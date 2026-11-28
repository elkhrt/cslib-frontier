module

public import CslibFrontier.Computability.Complexity.Classes.IP.TQBF.Verifier
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Data.ZMod.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Finite
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Length
import CslibFrontier.Foundations.Logic.Function.Iterate
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Finset.NatAntidiagonal

/-!
# Explicit-stack evaluator for `ArithQBF` over `ZMod p`

Supporting definitions and polynomial-time bounded-state stack evaluator for arithmetic QBF
evaluation and univariate restriction modulo `p`, used by
`CslibFrontier.Computability.Complexity.Classes.ArthurMerlin.PSPACE`
to place the Shamir–Shen honest prover in `EXP`.

## Main definitions

* `CslibFrontier.Complexity.posMod`: guarded positive modulus `p - 1 + 1`.
* `CslibFrontier.Complexity.PolyRep`: truncated polynomial representation modulo `p`.
* `CslibFrontier.Complexity.ArithFrame`, `CslibFrontier.Complexity.ArithState`,
  `CslibFrontier.Complexity.arithStep`: explicit-stack evaluator for `ArithQBF`.

## Main results

* `CslibFrontier.Complexity.exists_iterate_arithStep_call`: correctness of the stack evaluator.
* `CslibFrontier.Complexity.computableInPolyTime_runArith`: polynomial-time iterated evaluation.
-/

public section

namespace CslibFrontier.Complexity

open Cslib.Complexity Cslib.Logic.PL Polynomial Turing Turing.MultiTapeTM

/-! ### : Truncated polynomial arithmetic modulo `p` -/

/-- Guarded positive modulus matching `QBFProtocol.hornerMod`: equals `p` whenever `p ≠ 0`,
and `1` when `p = 0`. -/
def posMod (p : ℕ) : ℕ := p - 1 + 1

/-- The guarded modulus `posMod p` is always positive. -/
theorem posMod_pos (p : ℕ) : 0 < posMod p := Nat.succ_pos _

/-- For nonzero `p`, `posMod p = p`. -/
theorem posMod_eq (p : ℕ) [NeZero p] : posMod p = p :=
  Nat.sub_add_cancel NeZero.one_le

/-- The guarded modulus satisfies `posMod p ≤ p + 1`. -/
theorem posMod_le (p : ℕ) : posMod p ≤ p + 1 := by
  unfold posMod; omega

/-- Constant polynomial `C c` truncated to `D + 1` coefficients modulo `posMod p`. -/
private def polyConst (p D c : ℕ) : List ℕ :=
  (c % posMod p) :: List.replicate D 0

/-- Variable polynomial `X` truncated to `D + 1` coefficients modulo `posMod p`. -/
private def polyX (p D : ℕ) : List ℕ :=
  (List.range (D + 1)).map fun i => if i = 1 then 1 % posMod p else 0

/-- Coefficientwise addition of truncated polynomials modulo `posMod p`. -/
private def polyAdd (p D : ℕ) (a b : List ℕ) : List ℕ :=
  (List.range (D + 1)).map fun i => (a.getD i 0 + b.getD i 0) % posMod p

/-- Coefficientwise subtraction of truncated polynomials modulo `posMod p`. -/
private def polySub (p D : ℕ) (a b : List ℕ) : List ℕ :=
  (List.range (D + 1)).map fun i =>
    QBFProtocol.subMod (posMod p) (a.getD i 0) (b.getD i 0)

/-- `1 - a` truncated to `D + 1` coefficients modulo `posMod p`. -/
private def polyOneSub (p D : ℕ) (a : List ℕ) : List ℕ :=
  polySub p D (polyConst p D 1) a

/-- Degree-`k` coefficient of the product `a * b` modulo `posMod p`. -/
private def polyMulCoeff (p : ℕ) (a b : List ℕ) (k : ℕ) : ℕ :=
  (List.range (k + 1)).foldl
    (fun acc j => (acc + a.getD j 0 * b.getD (k - j) 0) % posMod p) 0

/-- Truncated polynomial multiplication modulo `posMod p`. -/
private def polyMul (p D : ℕ) (a b : List ℕ) : List ℕ :=
  (List.range (D + 1)).map (polyMulCoeff p a b)

/-- Truncated binary connective on polynomial coefficient lists. -/
private def polyConnective (p D : ℕ) : ArithQBF.Connective → List ℕ → List ℕ → List ℕ
  | .and, a, b => polyMul p D a b
  | .or, a, b => polyOneSub p D (polyMul p D (polyOneSub p D a) (polyOneSub p D b))

/-- Truncated operator on polynomial coefficient lists. -/
private def polyOperator (p D : ℕ) : ArithQBF.Operator → List ℕ → List ℕ → List ℕ → List ℕ
  | .ex, _, a, b => polyOneSub p D (polyMul p D (polyOneSub p D a) (polyOneSub p D b))
  | .all, _, a, b => polyMul p D a b
  | .lin, t, a, b => polyAdd p D (polyMul p D (polyOneSub p D t) a) (polyMul p D t b)

private theorem length_polyConst (p D c : ℕ) : (polyConst p D c).length = D + 1 := by
  simp [polyConst]

private theorem lt_posMod_polyConst (p D c : ℕ) : ∀ x ∈ polyConst p D c, x < posMod p := by
  intro x hx
  simp only [polyConst, List.mem_cons, List.mem_replicate] at hx
  rcases hx with rfl | ⟨_, rfl⟩
  · exact Nat.mod_lt _ (posMod_pos p)
  · exact posMod_pos p

private theorem length_polyX (p D : ℕ) : (polyX p D).length = D + 1 := by
  simp [polyX]

private theorem lt_posMod_polyX (p D : ℕ) : ∀ x ∈ polyX p D, x < posMod p := by
  intro x hx
  simp only [polyX, List.mem_map, List.mem_range] at hx
  rcases hx with ⟨i, _, rfl⟩
  split_ifs
  · exact Nat.mod_lt _ (posMod_pos p)
  · exact posMod_pos p

private theorem length_polyAdd (p D : ℕ) (a b : List ℕ) :
    (polyAdd p D a b).length = D + 1 := by
  simp [polyAdd]

private theorem lt_posMod_polyAdd (p D : ℕ) (a b : List ℕ) :
    ∀ x ∈ polyAdd p D a b, x < posMod p := by
  intro x hx
  simp only [polyAdd, List.mem_map, List.mem_range] at hx
  rcases hx with ⟨i, _, rfl⟩
  exact Nat.mod_lt _ (posMod_pos p)

private theorem length_polySub (p D : ℕ) (a b : List ℕ) :
    (polySub p D a b).length = D + 1 := by
  simp [polySub]

private theorem lt_posMod_polySub (p D : ℕ) (a b : List ℕ) :
    ∀ x ∈ polySub p D a b, x < posMod p := by
  intro x hx
  simp only [polySub, List.mem_map, List.mem_range] at hx
  rcases hx with ⟨i, _, rfl⟩
  exact Nat.mod_lt _ (posMod_pos p)

private theorem length_polyOneSub (p D : ℕ) (a : List ℕ) :
    (polyOneSub p D a).length = D + 1 := length_polySub p D _ a

private theorem lt_posMod_polyOneSub (p D : ℕ) (a : List ℕ) :
    ∀ x ∈ polyOneSub p D a, x < posMod p := lt_posMod_polySub p D _ a

private theorem foldl_polyMulCoeff_lt (p : ℕ) (a b : List ℕ) (k : ℕ) (l : List ℕ)
    {init : ℕ} (hinit : init < posMod p) :
    l.foldl (fun acc j => (acc + a.getD j 0 * b.getD (k - j) 0) % posMod p) init < posMod p := by
  induction l generalizing init with
  | nil => exact hinit
  | cons j l ih =>
    simp only [List.foldl_cons]
    exact ih (Nat.mod_lt _ (posMod_pos p))

private theorem polyMulCoeff_lt (p : ℕ) (a b : List ℕ) (k : ℕ) :
    polyMulCoeff p a b k < posMod p :=
  foldl_polyMulCoeff_lt p a b k _ (posMod_pos p)

private theorem length_polyMul (p D : ℕ) (a b : List ℕ) :
    (polyMul p D a b).length = D + 1 := by
  simp [polyMul]

private theorem lt_posMod_polyMul (p D : ℕ) (a b : List ℕ) :
    ∀ x ∈ polyMul p D a b, x < posMod p := by
  intro x hx
  simp only [polyMul, List.mem_map, List.mem_range] at hx
  rcases hx with ⟨k, _, rfl⟩
  exact polyMulCoeff_lt p a b k

private theorem length_polyConnective (p D : ℕ) (o : ArithQBF.Connective) (a b : List ℕ) :
    (polyConnective p D o a b).length = D + 1 := by
  cases o
  · exact length_polyMul p D a b
  · exact length_polyOneSub p D _

private theorem lt_posMod_polyConnective (p D : ℕ) (o : ArithQBF.Connective) (a b : List ℕ) :
    ∀ x ∈ polyConnective p D o a b, x < posMod p := by
  cases o
  · exact lt_posMod_polyMul p D a b
  · exact lt_posMod_polyOneSub p D _

private theorem length_polyOperator (p D : ℕ) (o : ArithQBF.Operator) (t a b : List ℕ) :
    (polyOperator p D o t a b).length = D + 1 := by
  cases o
  · exact length_polyOneSub p D _
  · exact length_polyMul p D a b
  · exact length_polyAdd p D _ _

private theorem lt_posMod_polyOperator (p D : ℕ) (o : ArithQBF.Operator) (t a b : List ℕ) :
    ∀ x ∈ polyOperator p D o t a b, x < posMod p := by
  cases o
  · exact lt_posMod_polyOneSub p D _
  · exact lt_posMod_polyMul p D a b
  · exact lt_posMod_polyAdd p D _ _

/-- Representation predicate: `a` holds the first `D + 1` coefficients of `P : (ZMod p)[X]`
as natural numbers below `p`. -/
def PolyRep (p D : ℕ) (a : List ℕ) (P : (ZMod p)[X]) : Prop :=
  a.length = D + 1 ∧ (∀ c ∈ a, c < p) ∧
    a.map (Nat.cast : ℕ → ZMod p) = P.coeffsBelow (D + 1)

/-- Extracting the `i`-th coefficient from a `PolyRep` recovers `P.coeff i` for `i ≤ D`. -/
theorem PolyRep.getD_cast {p D : ℕ} {a : List ℕ} {P : (ZMod p)[X]}
    (h : PolyRep p D a P) {i : ℕ} (hi : i ≤ D) :
    ((a.getD i 0 : ℕ) : ZMod p) = P.coeff i := by
  have hi' : i < a.length := by rw [h.1]; omega
  have hget : (a.map (Nat.cast : ℕ → ZMod p))[i]'(by simp [hi']) =
      (P.coeffsBelow (D + 1))[i]'(by simp; omega) := by
    simp [h.2.2]
  rw [List.getD_eq_getElem _ _ hi']
  simpa [Polynomial.coeffsBelow] using hget

private theorem polyRep_const {p : ℕ} [NeZero p] (D c : ℕ) :
    PolyRep p D (polyConst p D c) (Polynomial.C (c : ZMod p)) := by
  refine ⟨length_polyConst p D c, ?_, ?_⟩
  · simpa only [posMod_eq p] using lt_posMod_polyConst p D c
  · apply List.ext_getElem (by simp [polyConst, Polynomial.coeffsBelow])
    intro i hi₁ hi₂
    simp only [polyConst, List.length_map, List.length_cons, List.length_replicate] at hi₁
    simp only [polyConst, posMod_eq p, List.map_cons, List.map_replicate, Nat.cast_zero,
      Polynomial.coeffsBelow, List.getElem_map, List.getElem_range]
    cases i with
    | zero => simp [ZMod.natCast_mod]
    | succ i => simp

private theorem polyRep_X {p : ℕ} [NeZero p] (D : ℕ) :
    PolyRep p D (polyX p D) (Polynomial.X : (ZMod p)[X]) := by
  refine ⟨length_polyX p D, ?_, ?_⟩
  · simpa only [posMod_eq p] using lt_posMod_polyX p D
  · apply List.ext_getElem (by simp [polyX, Polynomial.coeffsBelow])
    intro i hi₁ hi₂
    simp only [polyX, List.length_map, List.length_range] at hi₁
    simp only [polyX, posMod_eq p, Polynomial.coeffsBelow, List.getElem_map, List.getElem_range,
      Polynomial.coeff_X]
    by_cases h : i = 1
    · subst h; simp [ZMod.natCast_mod]
    · have h' : 1 ≠ i := Ne.symm h
      simp [h, h']

private theorem polyRep_add {p : ℕ} [NeZero p] {D : ℕ} {a b : List ℕ} {P Q : (ZMod p)[X]}
    (ha : PolyRep p D a P) (hb : PolyRep p D b Q) :
    PolyRep p D (polyAdd p D a b) (P + Q) := by
  refine ⟨length_polyAdd p D a b, ?_, ?_⟩
  · simpa only [posMod_eq p] using lt_posMod_polyAdd p D a b
  · apply List.ext_getElem (by simp [polyAdd, Polynomial.coeffsBelow])
    intro i hi₁ hi₂
    simp only [polyAdd, List.length_map, List.length_range] at hi₁
    simp only [polyAdd, posMod_eq p, Polynomial.coeffsBelow, List.getElem_map, List.getElem_range,
      ZMod.natCast_mod, Nat.cast_add, Polynomial.coeff_add]
    rw [ha.getD_cast (by omega), hb.getD_cast (by omega)]

private theorem polyRep_sub {p : ℕ} [NeZero p] {D : ℕ} {a b : List ℕ} {P Q : (ZMod p)[X]}
    (ha : PolyRep p D a P) (hb : PolyRep p D b Q) :
    PolyRep p D (polySub p D a b) (P - Q) := by
  refine ⟨length_polySub p D a b, ?_, ?_⟩
  · simpa only [posMod_eq p] using lt_posMod_polySub p D a b
  · apply List.ext_getElem (by simp [polySub, Polynomial.coeffsBelow])
    intro i hi₁ hi₂
    simp only [polySub, List.length_map, List.length_range] at hi₁
    simp only [polySub, posMod_eq p, Polynomial.coeffsBelow, List.getElem_map, List.getElem_range,
      QBFProtocol.natCast_subMod, Polynomial.coeff_sub]
    rw [ha.getD_cast (by omega), hb.getD_cast (by omega)]

private theorem polyRep_oneSub {p : ℕ} [NeZero p] {D : ℕ} {a : List ℕ} {P : (ZMod p)[X]}
    (ha : PolyRep p D a P) :
    PolyRep p D (polyOneSub p D a) (1 - P) := by
  unfold polyOneSub
  simpa only [Nat.cast_one, map_one] using polyRep_sub (polyRep_const (p := p) D 1) ha

private theorem natCast_foldl_polyMulCoeff {p : ℕ} [NeZero p] (a b : List ℕ) (k n : ℕ) :
    (((List.range n).foldl
      (fun acc j => (acc + a.getD j 0 * b.getD (k - j) 0) % posMod p) 0 : ℕ) : ZMod p) =
      ∑ j ∈ Finset.range n, ((a.getD j 0 : ℕ) : ZMod p) * ((b.getD (k - j) 0 : ℕ) : ZMod p) := by
  have hmod : ∀ m : ℕ, ((m % posMod p : ℕ) : ZMod p) = (m : ZMod p) := fun m => by
    rw [posMod_eq p, ZMod.natCast_mod]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      hmod, Nat.cast_add, Nat.cast_mul, ih, Finset.sum_range_succ]

private theorem polyRep_mul {p : ℕ} [NeZero p] {D : ℕ} {a b : List ℕ} {P Q : (ZMod p)[X]}
    (ha : PolyRep p D a P) (hb : PolyRep p D b Q) :
    PolyRep p D (polyMul p D a b) (P * Q) := by
  refine ⟨length_polyMul p D a b, ?_, ?_⟩
  · simpa only [posMod_eq p] using lt_posMod_polyMul p D a b
  · apply List.ext_getElem (by simp [polyMul, Polynomial.coeffsBelow])
    intro k hk₁ hk₂
    simp only [polyMul, List.length_map, List.length_range] at hk₁
    simp only [polyMul, Polynomial.coeffsBelow, List.getElem_map, List.getElem_range]
    rw [polyMulCoeff, natCast_foldl_polyMulCoeff, Polynomial.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => P.coeff i * Q.coeff j)]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj_le : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    rw [ha.getD_cast (by omega), hb.getD_cast (by omega)]

private theorem polyRep_connective {p : ℕ} [NeZero p] {D : ℕ} (o : ArithQBF.Connective)
    {a b : List ℕ} {P Q : (ZMod p)[X]} (ha : PolyRep p D a P) (hb : PolyRep p D b Q) :
    PolyRep p D (polyConnective p D o a b) (o.apply P Q) := by
  cases o with
  | and => exact polyRep_mul ha hb
  | or => exact polyRep_oneSub (polyRep_mul (polyRep_oneSub ha) (polyRep_oneSub hb))

private theorem polyRep_operator {p : ℕ} [NeZero p] {D : ℕ} (o : ArithQBF.Operator)
    {t a b : List ℕ} {T P Q : (ZMod p)[X]}
    (ht : PolyRep p D t T) (ha : PolyRep p D a P) (hb : PolyRep p D b Q) :
    PolyRep p D (polyOperator p D o t a b) (o.apply T P Q) := by
  cases o with
  | ex => exact polyRep_oneSub (polyRep_mul (polyRep_oneSub ha) (polyRep_oneSub hb))
  | all => exact polyRep_mul ha hb
  | lin => exact polyRep_add (polyRep_mul (polyRep_oneSub ht) ha) (polyRep_mul ht hb)

section PolyArithPolyTime

open ComputableInPolyTime

variable {γ : Type} {encIn : γ ↪ List Bool}

/-- Computing the guarded positive modulus `posMod` in unary is polynomial-time. -/
theorem posMod_pt {p : γ → ℕ} (hp : ComputableInPolyTime p encIn encUnary) :
    ComputableInPolyTime (fun x => posMod (p x)) encIn encUnary := by
  unfold posMod; fun_prop

private lemma polyConst_pt {p D c : γ → ℕ}
    (hp : ComputableInPolyTime p encIn encUnary)
    (hD : ComputableInPolyTime D encIn encUnary)
    (hc : ComputableInPolyTime c encIn encUnary) :
    ComputableInPolyTime (fun x => polyConst (p x) (D x) (c x)) encIn (encList encUnary) := by
  have hpm := posMod_pt hp
  unfold polyConst
  fun_prop

private lemma polyX_pt {p D : γ → ℕ}
    (hp : ComputableInPolyTime p encIn encUnary)
    (hD : ComputableInPolyTime D encIn encUnary) :
    ComputableInPolyTime (fun x => polyX (p x) (D x)) encIn (encList encUnary) := by
  have hpm := posMod_pt hp
  unfold polyX
  refine mapWithInput (by fun_prop) ?_
  have hcond : ComputableInPolyTime (fun q : γ × ℕ => decide (q.2 = 1))
      (encPair encIn encUnary) encBool := decide_eq' (snd encIn encUnary) (const 1)
  have hthen : ComputableInPolyTime (fun q : γ × ℕ => 1 % posMod (p q.1))
      (encPair encIn encUnary) encUnary :=
    unary_mod' (const 1) (hpm.comp (.fst encIn encUnary))
  exact (ComputableInPolyTime.ite hcond hthen (const 0)).of_enc_eq fun q => by
    by_cases h : q.2 = 1 <;> simp [h]

private lemma polyAdd_pt {p D : γ → ℕ} {a b : γ → List ℕ}
    (hp : ComputableInPolyTime p encIn encUnary)
    (hD : ComputableInPolyTime D encIn encUnary)
    (ha : ComputableInPolyTime a encIn (encList encUnary))
    (hb : ComputableInPolyTime b encIn (encList encUnary)) :
    ComputableInPolyTime (fun x => polyAdd (p x) (D x) (a x) (b x)) encIn (encList encUnary) := by
  have hpm := posMod_pt hp
  unfold polyAdd
  refine mapWithInput (by fun_prop) ?_
  have h1 : ComputableInPolyTime (fun q : γ × ℕ => (a q.1).getD q.2 0)
      (encPair encIn encUnary) encUnary :=
    listGetDWithInput (ha.comp (.fst encIn encUnary)) (.snd encIn encUnary) 0
  have h2 : ComputableInPolyTime (fun q : γ × ℕ => (b q.1).getD q.2 0)
      (encPair encIn encUnary) encUnary :=
    listGetDWithInput (hb.comp (.fst encIn encUnary)) (.snd encIn encUnary) 0
  exact unary_mod' (unary_add' h1 h2) (hpm.comp (.fst encIn encUnary))

private lemma polySub_pt {p D : γ → ℕ} {a b : γ → List ℕ}
    (hp : ComputableInPolyTime p encIn encUnary)
    (hD : ComputableInPolyTime D encIn encUnary)
    (ha : ComputableInPolyTime a encIn (encList encUnary))
    (hb : ComputableInPolyTime b encIn (encList encUnary)) :
    ComputableInPolyTime (fun x => polySub (p x) (D x) (a x) (b x)) encIn (encList encUnary) := by
  have hpm := posMod_pt hp
  unfold polySub
  refine mapWithInput (by fun_prop) ?_
  have h1 : ComputableInPolyTime (fun q : γ × ℕ => (a q.1).getD q.2 0)
      (encPair encIn encUnary) encUnary :=
    listGetDWithInput (ha.comp (.fst encIn encUnary)) (.snd encIn encUnary) 0
  have h2 : ComputableInPolyTime (fun q : γ × ℕ => (b q.1).getD q.2 0)
      (encPair encIn encUnary) encUnary :=
    listGetDWithInput (hb.comp (.fst encIn encUnary)) (.snd encIn encUnary) 0
  exact QBFProtocol.computableInPolyTime_subMod (hpm.comp (.fst encIn encUnary)) h1 h2

private lemma polyOneSub_pt {p D : γ → ℕ} {a : γ → List ℕ}
    (hp : ComputableInPolyTime p encIn encUnary)
    (hD : ComputableInPolyTime D encIn encUnary)
    (ha : ComputableInPolyTime a encIn (encList encUnary)) :
    ComputableInPolyTime (fun x => polyOneSub (p x) (D x) (a x)) encIn (encList encUnary) :=
  polySub_pt hp hD (polyConst_pt hp hD (const 1)) ha

private lemma polyMulCoeff_pt :
    ComputableInPolyTime
      (fun x : (ℕ × List ℕ × List ℕ) × ℕ => polyMulCoeff x.1.1 x.1.2.1 x.1.2.2 x.2)
      (encPair (encPair encUnary (encPair (encList encUnary) (encList encUnary))) encUnary)
      encUnary := by
  let encX := encPair (encPair encUnary (encPair (encList encUnary) (encList encUnary))) encUnary
  unfold polyMulCoeff
  have hstep : ComputableInPolyTime
      (fun q : (((ℕ × List ℕ × List ℕ) × ℕ) × ℕ) × ℕ =>
        (q.1.2 + q.1.1.1.2.1.getD q.2 0 * q.1.1.1.2.2.getD (q.1.1.2 - q.2) 0) %
          posMod q.1.1.1.1)
      (encPair (encPair encX encUnary) encUnary) encUnary := by
    have hq1 : ComputableInPolyTime
        (fun q : (((ℕ × List ℕ × List ℕ) × ℕ) × ℕ) × ℕ => q.1.1)
        (encPair (encPair encX encUnary) encUnary) encX := (fst encX encUnary).comp (fst _ encUnary)
    have hacc : ComputableInPolyTime
        (fun q : (((ℕ × List ℕ × List ℕ) × ℕ) × ℕ) × ℕ => q.1.2)
        (encPair (encPair encX encUnary) encUnary) encUnary :=
      (snd encX encUnary).comp (fst _ encUnary)
    have hj : ComputableInPolyTime
        (fun q : (((ℕ × List ℕ × List ℕ) × ℕ) × ℕ) × ℕ => q.2)
        (encPair (encPair encX encUnary) encUnary) encUnary := snd _ encUnary
    have hp0 : ComputableInPolyTime
        (fun q : (((ℕ × List ℕ × List ℕ) × ℕ) × ℕ) × ℕ => q.1.1.1.1)
        (encPair (encPair encX encUnary) encUnary) encUnary := hq1.fst'.fst'
    have hpa : ComputableInPolyTime
        (fun q : (((ℕ × List ℕ × List ℕ) × ℕ) × ℕ) × ℕ => q.1.1.1.2.1)
        (encPair (encPair encX encUnary) encUnary) (encList encUnary) := hq1.fst'.snd'.fst'
    have hpb : ComputableInPolyTime
        (fun q : (((ℕ × List ℕ × List ℕ) × ℕ) × ℕ) × ℕ => q.1.1.1.2.2)
        (encPair (encPair encX encUnary) encUnary) (encList encUnary) := hq1.fst'.snd'.snd'
    have hk : ComputableInPolyTime
        (fun q : (((ℕ × List ℕ × List ℕ) × ℕ) × ℕ) × ℕ => q.1.1.2)
        (encPair (encPair encX encUnary) encUnary) encUnary := hq1.snd'
    have hpm := posMod_pt hp0
    have ha := listGetDWithInput hpa hj 0
    have hb := listGetDWithInput hpb (unary_sub' hk hj) 0
    exact unary_mod' (unary_add' hacc (unary_mul' ha hb)) hpm
  refine foldlWith (encIn := encX) (encP := encX) (encA := encUnary) (encB := encUnary)
    (encL := encList encUnary)
    (par := id) (list := fun x => List.range (x.2 + 1)) (init := fun _ => 0)
    (step := fun x acc j => (acc + x.1.2.1.getD j 0 * x.1.2.2.getD (x.2 - j) 0) % posMod x.1.1)
    id' (by fun_prop) (const 0) hstep
    (B := fun x => x.1.1 + 1) ?_ ?_
  · have hpx : ComputableInPolyTime (fun x : (ℕ × List ℕ × List ℕ) × ℕ => x.1.1 + 1)
        encX encUnary := by fun_prop
    exact hpx.polyBounded
  · intro x i _
    simp only [encUnary_apply, List.length_replicate, id_eq]
    have hlt := foldl_polyMulCoeff_lt x.1.1 x.1.2.1 x.1.2.2 x.2
      ((List.range (x.2 + 1)).take i) (posMod_pos x.1.1)
    have hle := posMod_le x.1.1
    omega

private lemma polyMul_pt {p D : γ → ℕ} {a b : γ → List ℕ}
    (hp : ComputableInPolyTime p encIn encUnary)
    (hD : ComputableInPolyTime D encIn encUnary)
    (ha : ComputableInPolyTime a encIn (encList encUnary))
    (hb : ComputableInPolyTime b encIn (encList encUnary)) :
    ComputableInPolyTime (fun x => polyMul (p x) (D x) (a x) (b x)) encIn (encList encUnary) := by
  unfold polyMul
  refine mapWithInput (by fun_prop) ?_
  exact polyMulCoeff_pt.comp
    ((((hp.comp (.fst encIn encUnary)).prod
      ((ha.comp (.fst encIn encUnary)).prod (hb.comp (.fst encIn encUnary)))).prod
      (.snd encIn encUnary)))

private lemma polyConnective_pt (o : ArithQBF.Connective) {p D : γ → ℕ} {a b : γ → List ℕ}
    (hp : ComputableInPolyTime p encIn encUnary)
    (hD : ComputableInPolyTime D encIn encUnary)
    (ha : ComputableInPolyTime a encIn (encList encUnary))
    (hb : ComputableInPolyTime b encIn (encList encUnary)) :
    ComputableInPolyTime (fun x => polyConnective (p x) (D x) o (a x) (b x)) encIn
      (encList encUnary) := by
  cases o with
  | and => exact polyMul_pt hp hD ha hb
  | or => exact polyOneSub_pt hp hD (polyMul_pt hp hD (polyOneSub_pt hp hD ha)
      (polyOneSub_pt hp hD hb))

private lemma polyOperator_pt (o : ArithQBF.Operator) {p D : γ → ℕ} {t a b : γ → List ℕ}
    (hp : ComputableInPolyTime p encIn encUnary)
    (hD : ComputableInPolyTime D encIn encUnary)
    (ht : ComputableInPolyTime t encIn (encList encUnary))
    (ha : ComputableInPolyTime a encIn (encList encUnary))
    (hb : ComputableInPolyTime b encIn (encList encUnary)) :
    ComputableInPolyTime (fun x => polyOperator (p x) (D x) o (t x) (a x) (b x)) encIn
      (encList encUnary) := by
  cases o with
  | ex => exact polyOneSub_pt hp hD (polyMul_pt hp hD (polyOneSub_pt hp hD ha)
      (polyOneSub_pt hp hD hb))
  | all => exact polyMul_pt hp hD ha hb
  | lin =>
    exact polyAdd_pt hp hD (polyMul_pt hp hD (polyOneSub_pt hp hD ht) ha)
      (polyMul_pt hp hD ht hb)

end PolyArithPolyTime

/-! ### : Explicit-stack evaluator for `ArithQBF` over `ZMod p` -/

/-- A call-stack frame of the arithmetic-formula evaluator. -/
structure ArithFrame where
  /-- Operator token currently being evaluated. -/
  token : ArithQBF.Kind × ℕ
  /-- Value returned from the first operand or pass, once available. -/
  first : Option (List ℕ)
  /-- Remaining token stream after the operator. -/
  rest : List (ArithQBF.Kind × ℕ)

/-- A state of the arithmetic-formula evaluator. -/
structure ArithState where
  /-- Remaining tokens to read. -/
  input : List (ArithQBF.Kind × ℕ)
  /-- Active call stack of operator frames. -/
  stack : List ArithFrame
  /-- Value currently being returned, or `none` when reading the next token. -/
  value : Option (List ℕ)

/-- Whether a stack frame is an operator (`∃`, `∀`, or `L`) binding variable `v`. -/
private def ArithFrame.binds (v : ℕ) (f : ArithFrame) : Bool :=
  (f.token.1 == .ex || f.token.1 == .all || f.token.1 == .lin) && f.token.2 == v

/-- Truncated polynomial value of variable `v` given base point `pt`, optional free variable
`xOpt`, and current call stack `stack`. -/
private def arithVarPoly (p D : ℕ) (pt : List (ℕ × ℕ)) (xOpt : Option ℕ)
    (stack : List ArithFrame) (v : ℕ) : List ℕ :=
  match stack.find? (ArithFrame.binds v) with
  | some f => polyConst p D (if f.first.isSome then 1 else 0)
  | none =>
    match xOpt with
    | some x => if v == x then polyX p D else polyConst p D (QBFProtocol.lookupPt pt v)
    | none => polyConst p D (QBFProtocol.lookupPt pt v)

/-- One step of the explicit-stack evaluator for `ArithQBF` modulo `posMod p`. -/
def arithStep (p D : ℕ) (pt : List (ℕ × ℕ)) (xOpt : Option ℕ) (s : ArithState) :
    ArithState :=
  match s.value with
  | none =>
    match s.input with
    | [] => ⟨[], s.stack, some (polyConst p D 0)⟩
    | (k, v) :: input =>
      match k with
      | .var => ⟨input, s.stack, some (arithVarPoly p D pt xOpt s.stack v)⟩
      | .top => ⟨input, s.stack, some (polyConst p D 1)⟩
      | .bot => ⟨input, s.stack, some (polyConst p D 0)⟩
      | .not | .and | .or | .ex | .all | .lin =>
        ⟨input, ⟨(k, v), none, input⟩ :: s.stack, none⟩
  | some b =>
    match s.stack with
    | [] => s
    | f :: stack =>
      match f.token.1, f.first with
      | .not, _ => ⟨s.input, stack, some (polyOneSub p D b)⟩
      | .and, none | .or, none =>
        ⟨s.input, { f with first := some b } :: stack, none⟩
      | .ex, none | .all, none | .lin, none =>
        ⟨f.rest, { f with first := some b } :: stack, none⟩
      | .and, some a => ⟨s.input, stack, some (polyConnective p D .and a b)⟩
      | .or, some a => ⟨s.input, stack, some (polyConnective p D .or a b)⟩
      | .ex, some a =>
        ⟨s.input, stack, some (polyOperator p D .ex
          (arithVarPoly p D pt xOpt stack f.token.2) a b)⟩
      | .all, some a =>
        ⟨s.input, stack, some (polyOperator p D .all
          (arithVarPoly p D pt xOpt stack f.token.2) a b)⟩
      | .lin, some a =>
        ⟨s.input, stack, some (polyOperator p D .lin
          (arithVarPoly p D pt xOpt stack f.token.2) a b)⟩
      | .var, _ | .top, _ | .bot, _ => ⟨s.input, stack, some b⟩

/-- Environment over `ZMod p` induced by base point `pt` and operator frames on `stack`. -/
def stackEnv (p : ℕ) (pt : List (ℕ × ℕ)) (stack : List ArithFrame) (v : ℕ) : ZMod p :=
  match stack.find? (ArithFrame.binds v) with
  | some f => if f.first.isSome then 1 else 0
  | none => (QBFProtocol.lookupPt pt v : ZMod p)

/-- On an empty stack, `stackEnv` reads directly from the point `pt`. -/
theorem stackEnv_nil (p : ℕ) (pt : List (ℕ × ℕ)) (v : ℕ) :
    stackEnv p pt [] v = (QBFProtocol.lookupPt pt v : ZMod p) := by
  unfold stackEnv; rfl

/-- Effective free variable for univariate restriction: becomes `none` once shadowed by an
operator frame on `stack`. -/
def effXOpt (xOpt : Option ℕ) (stack : List ArithFrame) : Option ℕ :=
  match xOpt with
  | none => none
  | some x => if (stack.find? (ArithFrame.binds x)).isSome then none else some x

/-- Target polynomial over `ZMod p`: `e.restrict` if `effXOpt` is `some x`, else constant
`C (e.eval)`. -/
noncomputable def targetPoly (p : ℕ) (pt : List (ℕ × ℕ)) (xOpt : Option ℕ)
    (stack : List ArithFrame) (e : ArithQBF ℕ) : (ZMod p)[X] :=
  match effXOpt xOpt stack with
  | some x => e.restrict (stackEnv p pt stack) x
  | none => Polynomial.C (e.eval (stackEnv p pt stack))

/-- On an empty stack with `xOpt = none`, `targetPoly` is the constant polynomial `C (e.eval)`. -/
theorem targetPoly_nil_none (p : ℕ) (pt : List (ℕ × ℕ)) (e : ArithQBF ℕ) :
    targetPoly p pt none [] e = Polynomial.C (e.eval (stackEnv p pt [])) := by
  unfold targetPoly effXOpt; rfl

/-- On an empty stack with `xOpt = some v`, `targetPoly` is the univariate restriction to `v`. -/
theorem targetPoly_nil_some (p : ℕ) (pt : List (ℕ × ℕ)) (v : ℕ) (e : ArithQBF ℕ) :
    targetPoly p pt (some v) [] e = e.restrict (stackEnv p pt []) v := by
  unfold targetPoly effXOpt; rfl

private theorem polyRep_arithVarPoly {p : ℕ} [NeZero p] (D : ℕ) (pt : List (ℕ × ℕ))
    (xOpt : Option ℕ) (stack : List ArithFrame) (v : ℕ) :
    PolyRep p D (arithVarPoly p D pt xOpt stack v)
      (match effXOpt xOpt stack with
       | some x => if v = x then Polynomial.X else Polynomial.C (stackEnv p pt stack v)
       | none => Polynomial.C (stackEnv p pt stack v)) := by
  unfold arithVarPoly stackEnv effXOpt
  rcases hfind : stack.find? (ArithFrame.binds v) with _ | f
  · rcases xOpt with _ | x
    · exact polyRep_const D _
    · by_cases hvx : v = x
      · subst hvx
        simp [hfind, polyRep_X]
      · dsimp only
        have hbeq : (v == x) = false := beq_false_of_ne hvx
        rw [hbeq]
        cases (stack.find? (ArithFrame.binds x)).isSome <;>
          simp only [Bool.false_eq_true, ↓reduceIte, hvx] <;> exact polyRep_const D _
  · have hcast : ((if f.first.isSome then 1 else 0 : ℕ) : ZMod p) =
        if f.first.isSome then 1 else 0 := by cases f.first <;> simp
    have hrep := polyRep_const (p := p) D (if f.first.isSome then 1 else 0)
    rw [hcast] at hrep
    rcases xOpt with _ | x
    · exact hrep
    · dsimp only
      rcases hx : (stack.find? (ArithFrame.binds x)).isSome with _ | _
      · have hvx : v ≠ x := by
          intro h; subst h; simp [hfind] at hx
        simpa only [Bool.false_eq_true, ↓reduceIte, hvx] using hrep
      · exact hrep

private theorem stackEnv_cons_nonbind {p : ℕ} (pt : List (ℕ × ℕ)) {f : ArithFrame}
    (hf : ∀ v, f.binds v = false) (stack : List ArithFrame) :
    stackEnv p pt (f :: stack) = stackEnv p pt stack := by
  funext v
  simp [stackEnv, hf v]

private theorem effXOpt_cons_nonbind (xOpt : Option ℕ) {f : ArithFrame}
    (hf : ∀ v, f.binds v = false) (stack : List ArithFrame) :
    effXOpt xOpt (f :: stack) = effXOpt xOpt stack := by
  cases xOpt with
  | none => rfl
  | some x => simp [effXOpt, hf x]

private theorem stackEnv_cons_op {p : ℕ} (pt : List (ℕ × ℕ)) {f : ArithFrame}
    {k : ArithQBF.Kind} {x : ℕ} (hk : k = .ex ∨ k = .all ∨ k = .lin) (hf : f.token = (k, x))
    (stack : List ArithFrame) :
    stackEnv p pt (f :: stack) =
      Function.update (stackEnv p pt stack) x (if f.first.isSome then 1 else 0) := by
  have hb (u : ℕ) : f.binds u = (u == x) := by
    rcases hk with rfl | rfl | rfl <;> simp [ArithFrame.binds, hf, Bool.beq_comm]
  funext v
  by_cases hv : v = x
  · subst hv; simp [stackEnv, hb]
  · simp [stackEnv, hb, hv, Function.update_of_ne]

private theorem effXOpt_cons_op_eq (xOpt : Option ℕ) {f : ArithFrame}
    {k : ArithQBF.Kind} {x : ℕ} (hk : k = .ex ∨ k = .all ∨ k = .lin) (hf : f.token = (k, x))
    (stack : List ArithFrame) :
    effXOpt xOpt (f :: stack) =
      match effXOpt xOpt stack with
      | some y => if x = y then none else some y
      | none => none := by
  have hb (u : ℕ) : f.binds u = (u == x) := by
    rcases hk with rfl | rfl | rfl <;> simp [ArithFrame.binds, hf, Bool.beq_comm]
  cases xOpt with
  | none => rfl
  | some y =>
    simp only [effXOpt, List.find?_cons, hb]
    by_cases hxy : x = y
    · subst hxy
      cases (stack.find? (ArithFrame.binds x)).isSome <;> simp
    · have hyx : (y == x) = false := beq_false_of_ne (Ne.symm hxy)
      cases h : (stack.find? (ArithFrame.binds y)).isSome <;> simp [hyx, hxy, h]

/-- Step budget for a call on an arithmetic formula. -/
def arithCallSteps : ArithQBF ℕ → ℕ
  | .var _ | .top | .bot => 1
  | .not e => arithCallSteps e + 2
  | .bin _ e₁ e₂ => arithCallSteps e₁ + arithCallSteps e₂ + 3
  | .op _ _ e => 2 * arithCallSteps e + 3

/-- Step budget of a binary connective formula dominates both operand budgets. -/
theorem arithCallSteps_bin_le (o : ArithQBF.Connective) (e₁ e₂ : ArithQBF ℕ) :
    arithCallSteps e₁ ≤ arithCallSteps (.bin o e₁ e₂) ∧
    arithCallSteps e₂ ≤ arithCallSteps (.bin o e₁ e₂) := by
  simp only [arithCallSteps]; omega

/-- Step budget of an operator formula dominates its body's budget. -/
theorem arithCallSteps_op_le (o : ArithQBF.Operator) (v : ℕ) (e : ArithQBF ℕ) :
    arithCallSteps e ≤ arithCallSteps (.op o v e) := by
  simp only [arithCallSteps]; omega

/-- The step budget of any arithmetic formula is strictly below `4 ^ e.tokens.length`. -/
theorem arithCallSteps_lt (e : ArithQBF ℕ) : arithCallSteps e < 4 ^ e.tokens.length := by
  induction e with
  | var _ | top | bot => simp [arithCallSteps, ArithQBF.tokens]
  | not e ih =>
    simp only [arithCallSteps, ArithQBF.tokens, List.length_cons, pow_succ]
    omega
  | bin o e₁ e₂ ih₁ ih₂ =>
    cases o <;>
    · simp only [arithCallSteps, ArithQBF.tokens, List.length_cons, List.length_append,
        pow_succ, pow_add]
      linarith [Nat.le_mul_of_pos_right (4 ^ e₁.tokens.length)
          (Nat.one_le_pow e₂.tokens.length 4 (by decide)),
        Nat.le_mul_of_pos_left (4 ^ e₂.tokens.length)
          (Nat.one_le_pow e₁.tokens.length 4 (by decide))]
  | op o _ e ih =>
    cases o <;>
    · simp only [arithCallSteps, ArithQBF.tokens, List.length_cons, pow_succ]
      omega

private theorem exists_iterate_arithStep_two {f : ArithState → ArithState} {B₁ B₂ : ℕ}
    {s₀ s₂ s₄ s₅ : ArithState}
    (h1 : ∃ T ≤ B₁, f^[T] (f s₀) = s₂)
    (h3 : ∃ T ≤ B₂, f^[T] (f s₂) = s₄)
    (h4 : f s₄ = s₅) :
    ∃ T ≤ B₁ + B₂ + 3, f^[T] s₀ = s₅ := by
  obtain ⟨T₁, hT₁, h₁⟩ := h1
  obtain ⟨T₂, hT₂, h₂⟩ := h3
  exact ⟨1 + (T₂ + (1 + (T₁ + 1))), by omega,
    Function.iterate_trans
      (Function.iterate_trans (Function.iterate_trans (Function.iterate_trans rfl h₁) rfl) h₂) h4⟩

/-- Every call on `e` returns a `PolyRep` of `targetPoly p pt xOpt stack e` within
`arithCallSteps e` steps, leaving the suffix `input` and `stack` intact. -/
theorem exists_iterate_arithStep_call {p : ℕ} [NeZero p] (D : ℕ) (pt : List (ℕ × ℕ))
    (xOpt : Option ℕ) (e : ArithQBF ℕ) (input : List (ArithQBF.Kind × ℕ))
    (stack : List ArithFrame) :
    ∃ T ≤ arithCallSteps e, ∃ res,
      PolyRep p D res (targetPoly p pt xOpt stack e) ∧
      (arithStep p D pt xOpt)^[T] ⟨e.tokens ++ input, stack, none⟩ =
        ⟨input, stack, some res⟩ := by
  induction e generalizing input stack with
  | var v =>
    refine ⟨1, le_rfl, arithVarPoly p D pt xOpt stack v, ?_, by simp [arithStep, ArithQBF.tokens]⟩
    have hrep := polyRep_arithVarPoly (p := p) D pt xOpt stack v
    unfold targetPoly
    cases h : effXOpt xOpt stack <;> rw [h] at hrep <;>
      simpa [ArithQBF.restrict, ArithQBF.eval] using hrep
  | top =>
    refine ⟨1, le_rfl, polyConst p D 1, ?_, by simp [arithStep, ArithQBF.tokens]⟩
    have hrep : PolyRep p D (polyConst p D 1) 1 := by
      simpa only [Nat.cast_one, map_one] using polyRep_const (p := p) D 1
    unfold targetPoly
    cases effXOpt xOpt stack <;> simpa [ArithQBF.restrict, ArithQBF.eval] using hrep
  | bot =>
    refine ⟨1, le_rfl, polyConst p D 0, ?_, by simp [arithStep, ArithQBF.tokens]⟩
    have hrep : PolyRep p D (polyConst p D 0) 0 := by
      simpa only [Nat.cast_zero, map_zero] using polyRep_const (p := p) D 0
    unfold targetPoly
    cases effXOpt xOpt stack <;> simpa [ArithQBF.restrict, ArithQBF.eval] using hrep
  | not e ih =>
    let fr : ArithFrame := ⟨(.not, 0), none, e.tokens ++ input⟩
    obtain ⟨T, hT, res, hrep, hrun⟩ := ih input (fr :: stack)
    have hnb : ∀ v, fr.binds v = false := fun _ => rfl
    have htp : targetPoly p pt xOpt (fr :: stack) e = targetPoly p pt xOpt stack e := by
      simp [targetPoly, stackEnv_cons_nonbind pt hnb, effXOpt_cons_nonbind xOpt hnb]
    rw [htp] at hrep
    refine ⟨1 + (T + 1), by simp only [arithCallSteps]; omega, polyOneSub p D res, ?_, ?_⟩
    · have hnot : targetPoly p pt xOpt stack e.not = 1 - targetPoly p pt xOpt stack e := by
        unfold targetPoly
        cases effXOpt xOpt stack <;> simp [ArithQBF.restrict, ArithQBF.eval]
      rw [hnot]
      exact polyRep_oneSub hrep
    · exact Function.iterate_trans
        (Function.iterate_trans (show arithStep p D pt xOpt ⟨e.not.tokens ++ input, stack, none⟩ =
          ⟨e.tokens ++ input, fr :: stack, none⟩ from rfl) hrun) rfl
  | bin o e₁ e₂ ih₁ ih₂ =>
    let k : ArithQBF.Kind := match o with | .and => .and | .or => .or
    let fr₁ : ArithFrame := ⟨(k, 0), none, e₁.tokens ++ (e₂.tokens ++ input)⟩
    have hnb₁ : ∀ v, fr₁.binds v = false := fun v => by cases o <;> rfl
    obtain ⟨T₁, hT₁, a, ha, hrun₁⟩ := ih₁ (e₂.tokens ++ input) (fr₁ :: stack)
    let fr₂ : ArithFrame := { fr₁ with first := some a }
    have hnb₂ : ∀ v, fr₂.binds v = false := fun v => by cases o <;> rfl
    obtain ⟨T₂, hT₂, b, hb, hrun₂⟩ := ih₂ input (fr₂ :: stack)
    have htp₁ : targetPoly p pt xOpt (fr₁ :: stack) e₁ = targetPoly p pt xOpt stack e₁ := by
      simp [targetPoly, stackEnv_cons_nonbind pt hnb₁, effXOpt_cons_nonbind xOpt hnb₁]
    have htp₂ : targetPoly p pt xOpt (fr₂ :: stack) e₂ = targetPoly p pt xOpt stack e₂ := by
      simp [targetPoly, stackEnv_cons_nonbind pt hnb₂, effXOpt_cons_nonbind xOpt hnb₂]
    rw [htp₁] at ha; rw [htp₂] at hb
    have hbin_tp : targetPoly p pt xOpt stack (.bin o e₁ e₂) =
        o.apply (targetPoly p pt xOpt stack e₁) (targetPoly p pt xOpt stack e₂) := by
      unfold targetPoly
      cases effXOpt xOpt stack with
      | some x => rfl
      | none =>
        simp only [ArithQBF.eval_bin, ArithQBF.Connective.map_apply]
    have hsteps : ∃ T ≤ arithCallSteps (.bin o e₁ e₂),
        (arithStep p D pt xOpt)^[T] ⟨(ArithQBF.bin o e₁ e₂).tokens ++ input, stack, none⟩ =
          ⟨input, stack, some (polyConnective p D o a b)⟩ := by
      have hs0 : arithStep p D pt xOpt ⟨(ArithQBF.bin o e₁ e₂).tokens ++ input, stack, none⟩ =
          ⟨e₁.tokens ++ (e₂.tokens ++ input), fr₁ :: stack, none⟩ := by
        cases o <;> simp [ArithQBF.tokens, arithStep, fr₁, k, List.append_assoc]
      have hs2 : arithStep p D pt xOpt ⟨e₂.tokens ++ input, fr₁ :: stack, some a⟩ =
          ⟨e₂.tokens ++ input, fr₂ :: stack, none⟩ := by
        cases o <;> rfl
      have hs4 : arithStep p D pt xOpt ⟨input, fr₂ :: stack, some b⟩ =
          ⟨input, stack, some (polyConnective p D o a b)⟩ := by
        cases o <;> rfl
      exact exists_iterate_arithStep_two ⟨T₁, hT₁, hs0.symm ▸ hrun₁⟩ ⟨T₂, hT₂, hs2.symm ▸ hrun₂⟩ hs4
    obtain ⟨T, hT, hrun⟩ := hsteps
    exact ⟨T, hT, polyConnective p D o a b, hbin_tp ▸ polyRep_connective o ha hb, hrun⟩
  | op o v e ih =>
    let k : ArithQBF.Kind := match o with | .ex => .ex | .all => .all | .lin => .lin
    have hk : k = .ex ∨ k = .all ∨ k = .lin := by cases o <;> simp [k]
    let fr₁ : ArithFrame := ⟨(k, v), none, e.tokens ++ input⟩
    obtain ⟨T₁, hT₁, a, ha, hrun₁⟩ := ih input (fr₁ :: stack)
    let fr₂ : ArithFrame := { fr₁ with first := some a }
    obtain ⟨T₂, hT₂, b, hb, hrun₂⟩ := ih input (fr₂ :: stack)
    have hsteps : ∃ T ≤ arithCallSteps (.op o v e),
        (arithStep p D pt xOpt)^[T] ⟨(ArithQBF.op o v e).tokens ++ input, stack, none⟩ =
          ⟨input, stack, some (polyOperator p D o
            (arithVarPoly p D pt xOpt stack v) a b)⟩ := by
      have hs0 : arithStep p D pt xOpt ⟨(ArithQBF.op o v e).tokens ++ input, stack, none⟩ =
          ⟨e.tokens ++ input, fr₁ :: stack, none⟩ := by
        cases o <;> rfl
      have hs2 : arithStep p D pt xOpt ⟨input, fr₁ :: stack, some a⟩ =
          ⟨e.tokens ++ input, fr₂ :: stack, none⟩ := by
        cases o <;> rfl
      have hs4 : arithStep p D pt xOpt ⟨input, fr₂ :: stack, some b⟩ =
          ⟨input, stack, some (polyOperator p D o (arithVarPoly p D pt xOpt stack v) a b)⟩ := by
        cases o <;> rfl
      rw [arithCallSteps, two_mul]
      exact exists_iterate_arithStep_two ⟨T₁, hT₁, hs0.symm ▸ hrun₁⟩ ⟨T₂, hT₂, hs2.symm ▸ hrun₂⟩ hs4
    obtain ⟨T, hT, hrun⟩ := hsteps
    refine ⟨T, hT, polyOperator p D o (arithVarPoly p D pt xOpt stack v) a b, ?_, hrun⟩
    have ht := polyRep_arithVarPoly (p := p) D pt xOpt stack v
    have hcomb := polyRep_operator o ht ha hb
    have henv₁ : stackEnv p pt (fr₁ :: stack) = Function.update (stackEnv p pt stack) v 0 := by
      have h := stackEnv_cons_op (p := p) pt hk (f := fr₁) rfl stack
      simpa [fr₁] using h
    have henv₂ : stackEnv p pt (fr₂ :: stack) = Function.update (stackEnv p pt stack) v 1 := by
      have h := stackEnv_cons_op (p := p) pt hk (f := fr₂) rfl stack
      simpa [fr₂] using h
    have heff₁ := effXOpt_cons_op_eq xOpt hk (f := fr₁) rfl stack
    have heff₂ := effXOpt_cons_op_eq xOpt hk (f := fr₂) rfl stack
    have htp : o.apply
        (match effXOpt xOpt stack with
         | some x => if v = x then Polynomial.X else Polynomial.C (stackEnv p pt stack v)
         | none => Polynomial.C (stackEnv p pt stack v))
        (targetPoly p pt xOpt (fr₁ :: stack) e)
        (targetPoly p pt xOpt (fr₂ :: stack) e) =
        targetPoly p pt xOpt stack (.op o v e) := by
      unfold targetPoly
      rw [henv₁, henv₂, heff₁, heff₂]
      cases effXOpt xOpt stack with
      | none =>
        simp only [ArithQBF.eval_op, ArithQBF.Operator.map_apply]
      | some x =>
        dsimp only
        by_cases hvx : v = x
        · subst hvx; simp [ArithQBF.restrict]
        · simp [hvx, ArithQBF.restrict]
    rwa [htp] at hcomb

/-- A state with empty stack and a returned value is a fixed point of `arithStep`. -/
theorem iterate_arithStep_done (p D : ℕ) (pt : List (ℕ × ℕ)) (xOpt : Option ℕ)
    (input : List (ArithQBF.Kind × ℕ)) (val : List ℕ) (n : ℕ) :
    (arithStep p D pt xOpt)^[n] ⟨input, [], some val⟩ = ⟨input, [], some val⟩ :=
  Function.iterate_fixed rfl n

/-! #### Invariant and polynomial-time computation of `arithStep` -/

private def ArithNested (n : ℕ) : ℕ → List ArithFrame → Prop
  | r, [] => r ≤ n
  | r, f :: stack => r ≤ f.rest.length ∧ ArithNested n (f.rest.length + 1) stack

private theorem ArithNested.mono {n : ℕ} : ∀ {r r' : ℕ} {stack : List ArithFrame},
    ArithNested n r stack → r' ≤ r → ArithNested n r' stack
  | _, _, [], h, hr => le_trans hr h
  | _, _, _ :: _, h, hr => ⟨le_trans hr h.1, h.2⟩

private theorem ArithNested.length_le {n : ℕ} : ∀ {r : ℕ} {stack : List ArithFrame},
    ArithNested n r stack → r + stack.length ≤ n
  | _, [], h => h
  | _, _ :: _, h => by simp only [List.length_cons]; linarith [h.1, h.2.length_le]

private def SmallPoly (p D : ℕ) (l : List ℕ) : Prop :=
  l.length ≤ D + 1 ∧ ∀ c ∈ l, c < posMod p

private structure GoodArith (p D : ℕ) (toks : List (ArithQBF.Kind × ℕ)) (s : ArithState) :
    Prop where
  input : s.input <:+ toks
  frames : ∀ f ∈ s.stack, f.token :: f.rest <:+ toks
  nested : ArithNested toks.length s.input.length s.stack
  frameFirst : ∀ f ∈ s.stack, ∀ l, f.first = some l → SmallPoly p D l
  valueSmall : ∀ l, s.value = some l → SmallPoly p D l

private theorem smallPoly_arithVarPoly (p D : ℕ) (pt : List (ℕ × ℕ)) (xOpt : Option ℕ)
    (stack : List ArithFrame) (v : ℕ) :
    SmallPoly p D (arithVarPoly p D pt xOpt stack v) := by
  unfold arithVarPoly
  rcases stack.find? (ArithFrame.binds v) with _ | f
  · rcases xOpt with _ | x
    · exact ⟨(length_polyConst p D _).le, lt_posMod_polyConst p D _⟩
    · dsimp only
      split_ifs
      · exact ⟨(length_polyX p D).le, lt_posMod_polyX p D⟩
      · exact ⟨(length_polyConst p D _).le, lt_posMod_polyConst p D _⟩
  · exact ⟨(length_polyConst p D _).le, lt_posMod_polyConst p D _⟩

private theorem goodArith_init (p D : ℕ) (toks : List (ArithQBF.Kind × ℕ)) :
    GoodArith p D toks ⟨toks, [], none⟩ :=
  ⟨List.suffix_refl _, fun _ hf => by simp at hf, le_refl _,
    fun _ hf => by simp at hf, fun _ h => by simp at h⟩

private theorem GoodArith.step {p D : ℕ} {toks : List (ArithQBF.Kind × ℕ)}
    {pt : List (ℕ × ℕ)} {xOpt : Option ℕ} {s : ArithState}
    (h : GoodArith p D toks s) : GoodArith p D toks (arithStep p D pt xOpt s) := by
  obtain ⟨input, stack, value⟩ := s
  obtain ⟨hin, hframes, hnest, hff, hval⟩ := h
  dsimp only at hin hframes hnest hff hval
  rcases value with _ | b
  · rcases input with _ | ⟨⟨k, v⟩, input⟩
    · refine ⟨hin, hframes, hnest, hff, ?_⟩
      rintro l ⟨⟩
      exact ⟨(length_polyConst p D 0).le, lt_posMod_polyConst p D 0⟩
    · have htail : input <:+ toks := (List.suffix_cons _ _).trans hin
      have hnest' : ArithNested toks.length input.length stack := hnest.mono (by simp)
      cases k with
      | var =>
        refine ⟨htail, hframes, hnest', hff, ?_⟩
        rintro l ⟨⟩
        exact smallPoly_arithVarPoly p D pt xOpt stack v
      | top =>
        refine ⟨htail, hframes, hnest', hff, ?_⟩
        rintro l ⟨⟩
        exact ⟨(length_polyConst p D 1).le, lt_posMod_polyConst p D 1⟩
      | bot =>
        refine ⟨htail, hframes, hnest', hff, ?_⟩
        rintro l ⟨⟩
        exact ⟨(length_polyConst p D 0).le, lt_posMod_polyConst p D 0⟩
      | not | and | or | ex | all | lin =>
        refine ⟨htail, fun f hf => ?_, ⟨le_refl _, hnest⟩, fun f hf l hl => ?_,
          fun _ h => by cases h⟩
        · rcases List.mem_cons.mp hf with rfl | hf
          · exact hin
          · exact hframes f hf
        · rcases List.mem_cons.mp hf with rfl | hf
          · cases hl
          · exact hff f hf l hl
  · have hb : SmallPoly p D b := hval b rfl
    rcases stack with _ | ⟨f, stack⟩
    · exact ⟨hin, hframes, hnest, hff, hval⟩
    · have hf := hframes f List.mem_cons_self
      have hrest : f.rest <:+ toks := (List.suffix_cons _ _).trans hf
      have hbelow : ∀ g ∈ stack, g.token :: g.rest <:+ toks := fun g hg =>
        hframes g (List.mem_cons_of_mem _ hg)
      have hff_below : ∀ g ∈ stack, ∀ l, g.first = some l → SmallPoly p D l := fun g hg =>
        hff g (List.mem_cons_of_mem _ hg)
      obtain ⟨hle, hnest₂⟩ := hnest
      have hpop : ArithNested toks.length input.length stack := hnest₂.mono (by omega)
      have hkeep : ∀ g ∈ { f with first := some b } :: stack, g.token :: g.rest <:+ toks :=
        fun g hg => (List.mem_cons.mp hg).elim (fun h => h ▸ hf) (hbelow g)
      have hff_keep : ∀ g ∈ { f with first := some b } :: stack, ∀ l,
          g.first = some l → SmallPoly p D l := by
        intro g hg l hl
        rcases List.mem_cons.mp hg with rfl | hg
        · cases hl; exact hb
        · exact hff_below g hg l hl
      obtain ⟨⟨k, x⟩, first, rest⟩ := f
      cases first with
      | none =>
        cases k with
        | var | top | bot => exact ⟨hin, hbelow, hpop, hff_below, by rintro l ⟨⟩; exact hb⟩
        | not => exact ⟨hin, hbelow, hpop, hff_below, by
            rintro l ⟨⟩; exact ⟨(length_polyOneSub p D b).le, lt_posMod_polyOneSub p D b⟩⟩
        | and | or => exact ⟨hin, hkeep, ⟨hle, hnest₂⟩, hff_keep, fun _ h => by cases h⟩
        | ex | all | lin =>
          exact ⟨hrest, hkeep, ⟨le_refl _, hnest₂⟩, hff_keep, fun _ h => by cases h⟩
      | some a =>
        cases k with
        | var | top | bot => exact ⟨hin, hbelow, hpop, hff_below, by rintro l ⟨⟩; exact hb⟩
        | not => exact ⟨hin, hbelow, hpop, hff_below, by
            rintro l ⟨⟩; exact ⟨(length_polyOneSub p D b).le, lt_posMod_polyOneSub p D b⟩⟩
        | and => exact ⟨hin, hbelow, hpop, hff_below, by
            rintro l ⟨⟩
            exact ⟨(length_polyConnective p D .and a b).le, lt_posMod_polyConnective p D .and a b⟩⟩
        | or => exact ⟨hin, hbelow, hpop, hff_below, by
            rintro l ⟨⟩
            exact ⟨(length_polyConnective p D .or a b).le, lt_posMod_polyConnective p D .or a b⟩⟩
        | ex => exact ⟨hin, hbelow, hpop, hff_below, by
            rintro l ⟨⟩
            exact ⟨(length_polyOperator p D .ex _ a b).le, lt_posMod_polyOperator p D .ex _ a b⟩⟩
        | all => exact ⟨hin, hbelow, hpop, hff_below, by
            rintro l ⟨⟩
            exact ⟨(length_polyOperator p D .all _ a b).le, lt_posMod_polyOperator p D .all _ a b⟩⟩
        | lin => exact ⟨hin, hbelow, hpop, hff_below, by
            rintro l ⟨⟩
            exact ⟨(length_polyOperator p D .lin _ a b).le, lt_posMod_polyOperator p D .lin _ a b⟩⟩

private theorem goodArith_iterate_step (p D : ℕ) (toks : List (ArithQBF.Kind × ℕ))
    (pt : List (ℕ × ℕ)) (xOpt : Option ℕ) (n : ℕ) :
    GoodArith p D toks ((arithStep p D pt xOpt)^[n] ⟨toks, [], none⟩) := by
  induction n with
  | zero => exact goodArith_init p D toks
  | succ n ih => rw [Function.iterate_succ_apply']; exact ih.step

/-! #### Encodings and polynomial-time step for the stack evaluator -/

open QBFProtocol.Machine (encArithToken)
open QBFProtocol (encPt)

private def ArithFrame.fields (f : ArithFrame) :
    (ArithQBF.Kind × ℕ) × Option (List ℕ) × List (ArithQBF.Kind × ℕ) :=
  (f.token, f.first, f.rest)

private abbrev encArithFrameFields :
    (ArithQBF.Kind × ℕ) × Option (List ℕ) × List (ArithQBF.Kind × ℕ) ↪ List Bool :=
  encPair encArithToken (encPair (encOption (encList encUnary)) (encList encArithToken))

private def encArithFrame : ArithFrame ↪ List Bool :=
  ⟨fun f => encArithFrameFields f.fields, fun f g h => by
    obtain ⟨⟩ := f; obtain ⟨⟩ := g
    simpa [ArithFrame.fields] using encArithFrameFields.injective h⟩

private def ArithState.fields (s : ArithState) :
    List (ArithQBF.Kind × ℕ) × List ArithFrame × Option (List ℕ) :=
  (s.input, s.stack, s.value)

private abbrev encArithStateFields :
    List (ArithQBF.Kind × ℕ) × List ArithFrame × Option (List ℕ) ↪ List Bool :=
  encPair (encList encArithToken) (encPair (encList encArithFrame) (encOption (encList encUnary)))

/-- Bitstring encoding of an arithmetic-evaluator state. -/
def encArithState : ArithState ↪ List Bool :=
  ⟨fun s => encArithStateFields s.fields, fun s t h => by
    obtain ⟨⟩ := s; obtain ⟨⟩ := t
    simpa [ArithState.fields] using encArithStateFields.injective h⟩

private theorem length_encSmallPoly {p D : ℕ} {l : List ℕ} (h : SmallPoly p D l) :
    (encList encUnary l).length ≤ (D + 1) * (2 * (p + 1) + 1) := by
  have hle := length_encList_le encUnary l (b := p + 1) fun c hc => by
    simp only [encUnary_apply, List.length_replicate]
    have := h.2 c hc
    have := posMod_le p
    omega
  exact hle.trans (Nat.mul_le_mul_right _ h.1)

private theorem length_encOption_smallPoly {p D : ℕ} {o : Option (List ℕ)}
    (ho : ∀ l, o = some l → SmallPoly p D l) :
    (encOption (encList encUnary) o).length ≤ (D + 1) * (2 * (p + 1) + 1) + 1 := by
  cases o with
  | none => simp [encOption]
  | some l =>
    have hlen : (encOption (encList encUnary) (some l)).length = (encList encUnary l).length + 1 :=
      by rfl
    have := length_encSmallPoly (ho l rfl)
    omega

private theorem length_encArithState_le {p D : ℕ} {toks : List (ArithQBF.Kind × ℕ)}
    {s : ArithState} (h : GoodArith p D toks s) :
    (encArithState s).length ≤
      8 * ((encList encArithToken toks).length + 1) *
        ((encList encArithToken toks).length + (D + 1) * (2 * (p + 1) + 1) + 5) +
      (D + 1) * (2 * (p + 1) + 1) + 6 := by
  set L := (encList encArithToken toks).length
  set P := (D + 1) * (2 * (p + 1) + 1)
  have hin : (encList encArithToken s.input).length ≤ L :=
    length_encList_sublist encArithToken h.input.sublist
  have hdepth : s.stack.length ≤ L := by
    have h1 : s.stack.length ≤ toks.length := by have := h.nested.length_le; omega
    exact h1.trans (length_le_length_encList encArithToken toks)
  have hframe : ∀ f ∈ s.stack, (encArithFrame f).length ≤ L + 2 * P + 4 := by
    intro f hf
    have hs := length_encList_sublist encArithToken (h.frames f hf).sublist
    have hfirst := length_encOption_smallPoly (h.frameFirst f hf)
    have hfl : (encArithFrame f).length =
        2 * (encArithToken f.token).length + 1 +
          (2 * (encOption (encList encUnary) f.first).length + 1 +
            (encList encArithToken f.rest).length) := by
      change (encArithFrameFields f.fields).length = _
      rw [ArithFrame.fields, encArithFrameFields,
        length_encPair (enc₁ := encArithToken),
        length_encPair (enc₁ := encOption (encList encUnary))]
    simp only [encList_cons, List.length_append, length_frame] at hs
    omega
  have hstack : (encList encArithFrame s.stack).length ≤
      L * (2 * (L + 2 * P + 4) + 1) :=
    (length_encList_le encArithFrame s.stack hframe).trans (Nat.mul_le_mul_right _ hdepth)
  have hval : (encOption (encList encUnary) s.value).length ≤ P + 1 :=
    length_encOption_smallPoly h.valueSmall
  have hsl : (encArithState s).length =
      2 * (encList encArithToken s.input).length + 1 +
        (2 * (encList encArithFrame s.stack).length + 1 +
          (encOption (encList encUnary) s.value).length) := by
    change (encArithStateFields s.fields).length = _
    rw [ArithState.fields, encArithStateFields,
      length_encPair (enc₁ := encList encArithToken),
      length_encPair (enc₁ := encList encArithFrame)]
  rw [hsl]
  nlinarith

section ArithStepPolyTime

open ComputableInPolyTime

attribute [local irreducible] ComputableInPolyTime

/-- Parameter tuple `((p, D), (pt, xOpt))` for the arithmetic-formula stack evaluator. -/
abbrev ArithPar := (ℕ × ℕ) × (List (ℕ × ℕ) × Option ℕ)

/-- Bitstring encoding of `ArithPar`. -/
abbrev encArithPar : ArithPar ↪ List Bool :=
  encPair (encPair encUnary encUnary) (encPair encPt (encOption encNat))

private abbrev ArithStepIn := ArithPar × ArithState

private abbrev encArithStepIn : ArithStepIn ↪ List Bool :=
  encPair encArithPar encArithState

private lemma arithFrame_fields_pt :
    ComputableInPolyTime ArithFrame.fields encArithFrame encArithFrameFields :=
  of_eq fun _ => rfl

private lemma arithFrame_mk_pt :
    ComputableInPolyTime
      (fun p : (ArithQBF.Kind × ℕ) × Option (List ℕ) × List (ArithQBF.Kind × ℕ) =>
        ArithFrame.mk p.1 p.2.1 p.2.2) encArithFrameFields encArithFrame :=
  of_eq fun _ => rfl

private lemma arithState_fields_pt :
    ComputableInPolyTime ArithState.fields encArithState encArithStateFields :=
  of_eq fun _ => rfl

private lemma arithState_mk_pt :
    ComputableInPolyTime
      (fun p : List (ArithQBF.Kind × ℕ) × List ArithFrame × Option (List ℕ) =>
        ArithState.mk p.1 p.2.1 p.2.2) encArithStateFields encArithState :=
  of_eq fun _ => rfl

private lemma arithFrame_token_pt :
    ComputableInPolyTime ArithFrame.token encArithFrame encArithToken :=
  (fst _ _).comp arithFrame_fields_pt

private lemma arithFrame_first_pt :
    ComputableInPolyTime ArithFrame.first encArithFrame (encOption (encList encUnary)) :=
  ((fst _ _).comp (snd _ _)).comp arithFrame_fields_pt

private lemma arithFrame_rest_pt :
    ComputableInPolyTime ArithFrame.rest encArithFrame (encList encArithToken) :=
  ((snd _ _).comp (snd _ _)).comp arithFrame_fields_pt

/-- Extracting the remaining token stream from an `ArithState` is polynomial-time. -/
theorem arithState_input_pt :
    ComputableInPolyTime ArithState.input encArithState (encList encArithToken) :=
  (fst _ _).comp arithState_fields_pt

private lemma arithState_stack_pt :
    ComputableInPolyTime ArithState.stack encArithState (encList encArithFrame) :=
  ((fst _ _).comp (snd _ _)).comp arithState_fields_pt

/-- Extracting the returned value option from an `ArithState` is polynomial-time. -/
theorem arithState_value_pt :
    ComputableInPolyTime ArithState.value encArithState (encOption (encList encUnary)) :=
  ((snd _ _).comp (snd _ _)).comp arithState_fields_pt

private lemma arithState_mk_comp_pt {γ : Type} {encIn : γ ↪ List Bool}
    {f₁ : γ → List (ArithQBF.Kind × ℕ)} {f₂ : γ → List ArithFrame}
    {f₃ : γ → Option (List ℕ)}
    (h₁ : ComputableInPolyTime f₁ encIn (encList encArithToken))
    (h₂ : ComputableInPolyTime f₂ encIn (encList encArithFrame))
    (h₃ : ComputableInPolyTime f₃ encIn (encOption (encList encUnary))) :
    ComputableInPolyTime (fun x => ArithState.mk (f₁ x) (f₂ x) (f₃ x)) encIn encArithState :=
  arithState_mk_pt.comp (h₁.prod (h₂.prod h₃))

private lemma arithFrame_mk_comp_pt {γ : Type} {encIn : γ ↪ List Bool}
    {f₁ : γ → ArithQBF.Kind × ℕ} {f₂ : γ → Option (List ℕ)}
    {f₃ : γ → List (ArithQBF.Kind × ℕ)}
    (h₁ : ComputableInPolyTime f₁ encIn encArithToken)
    (h₂ : ComputableInPolyTime f₂ encIn (encOption (encList encUnary)))
    (h₃ : ComputableInPolyTime f₃ encIn (encList encArithToken)) :
    ComputableInPolyTime (fun x => ArithFrame.mk (f₁ x) (f₂ x) (f₃ x)) encIn encArithFrame := by
  simpa only [Function.comp_def] using
    arithFrame_mk_pt.comp (h₁.prod (h₂.prod h₃))

private lemma arithFrame_binds_pt :
    ComputableInPolyTime (fun q : ℕ × ArithFrame => ArithFrame.binds q.1 q.2)
      (encPair encNat encArithFrame) encBool := by
  have hk : ComputableInPolyTime
      (fun k : ArithQBF.Kind => (k == .ex || k == .all || k == .lin))
      (encFinEnum ArithQBF.Kind) encBool := of_finite _
  have htok := arithFrame_token_pt.comp (.snd encNat encArithFrame)
  have h1 := hk.comp htok.fst'
  have h2 := beq htok.snd' (.fst encNat encArithFrame)
  exact (ite h1 h2 (const false)).of_enc_eq fun q => by
    unfold ArithFrame.binds
    simp only [Function.comp_apply]
    cases (q.2.token.1 == .ex || q.2.token.1 == .all || q.2.token.1 == .lin) <;> rfl

private lemma arithVarPoly_pt {γ : Type} {encIn : γ ↪ List Bool}
    {p D : γ → ℕ} {pt : γ → List (ℕ × ℕ)} {xOpt : γ → Option ℕ}
    {stack : γ → List ArithFrame} {v : γ → ℕ}
    (hp : ComputableInPolyTime p encIn encUnary)
    (hD : ComputableInPolyTime D encIn encUnary)
    (hpt : ComputableInPolyTime pt encIn encPt)
    (hxOpt : ComputableInPolyTime xOpt encIn (encOption encNat))
    (hstack : ComputableInPolyTime stack encIn (encList encArithFrame))
    (hv : ComputableInPolyTime v encIn encNat) :
    ComputableInPolyTime (fun q => arithVarPoly (p q) (D q) (pt q) (xOpt q) (stack q) (v q))
      encIn (encList encUnary) := by
  have hfind : ComputableInPolyTime
      (fun q => (stack q).find? (ArithFrame.binds (v q))) encIn (encOption encArithFrame) :=
    findWithInput hstack
      (arithFrame_binds_pt.comp ((hv.comp (.fst encIn encArithFrame)).prod
        (.snd encIn encArithFrame)))
  have hsome : ComputableInPolyTime
      (fun q : γ × ArithFrame => polyConst (p q.1) (D q.1) (if q.2.first.isSome then 1 else 0))
      (encPair encIn encArithFrame) (encList encUnary) :=
    polyConst_pt (hp.comp (.fst encIn encArithFrame)) (hD.comp (.fst encIn encArithFrame))
      (ite (optionIsSome (arithFrame_first_pt.comp (.snd encIn encArithFrame)))
        (const 1) (const 0))
  have hnone_none : ComputableInPolyTime
      (fun q : γ => polyConst (p q) (D q) (QBFProtocol.lookupPt (pt q) (v q)))
      encIn (encList encUnary) :=
    polyConst_pt hp hD (QBFProtocol.computableInPolyTime_lookupPt hpt hv)
  have hnone_some : ComputableInPolyTime
      (fun q : γ × ℕ => if v q.1 == q.2 then polyX (p q.1) (D q.1)
        else polyConst (p q.1) (D q.1) (QBFProtocol.lookupPt (pt q.1) (v q.1)))
      (encPair encIn encNat) (encList encUnary) :=
    ite (by fun_prop)
      (polyX_pt (hp.comp (.fst encIn encNat)) (hD.comp (.fst encIn encNat)))
      (hnone_none.comp (.fst encIn encNat))
  have hnone : ComputableInPolyTime
      (fun q : γ => (xOpt q).elim (polyConst (p q) (D q) (QBFProtocol.lookupPt (pt q) (v q)))
        (fun x => if v q == x then polyX (p q) (D q)
          else polyConst (p q) (D q) (QBFProtocol.lookupPt (pt q) (v q))))
      encIn (encList encUnary) :=
    optionElimWithInput
      (body := fun q x => if v q == x then polyX (p q) (D q)
        else polyConst (p q) (D q) (QBFProtocol.lookupPt (pt q) (v q)))
      hxOpt hnone_none hnone_some
  refine (optionElimWithInput
    (body := fun q f => polyConst (p q) (D q) (if f.first.isSome then 1 else 0))
    hfind hnone hsome).of_enc_eq fun q => ?_
  unfold arithVarPoly
  cases (stack q).find? (ArithFrame.binds (v q)) with
  | some f => rfl
  | none => cases xOpt q <;> rfl

private def arithHead (s : ArithState) : ArithQBF.Kind × ℕ :=
  s.input.headD (.top, 0)

private def arithTop (s : ArithState) : ArithFrame :=
  s.stack.headD ⟨(.top, 0), none, []⟩

private def arithRet (s : ArithState) : List ℕ :=
  s.value.getD []

private def arithReadStep (k : ArithQBF.Kind) (q : ArithStepIn) : ArithState :=
  match k with
  | .var => ⟨q.2.input.tail, q.2.stack,
      some (arithVarPoly q.1.1.1 q.1.1.2 q.1.2.1 q.1.2.2 q.2.stack (arithHead q.2).2)⟩
  | .top => ⟨q.2.input.tail, q.2.stack, some (polyConst q.1.1.1 q.1.1.2 1)⟩
  | .bot => ⟨q.2.input.tail, q.2.stack, some (polyConst q.1.1.1 q.1.1.2 0)⟩
  | .not | .and | .or | .ex | .all | .lin =>
    ⟨q.2.input.tail, ⟨arithHead q.2, none, q.2.input.tail⟩ :: q.2.stack, none⟩

private def arithRetStep (k : ArithQBF.Kind) (second : Bool) (q : ArithStepIn) : ArithState :=
  match k, second with
  | .not, _ => ⟨q.2.input, q.2.stack.tail, some (polyOneSub q.1.1.1 q.1.1.2 (arithRet q.2))⟩
  | .and, false | .or, false =>
    ⟨q.2.input, { arithTop q.2 with first := some (arithRet q.2) } :: q.2.stack.tail, none⟩
  | .ex, false | .all, false | .lin, false =>
    ⟨(arithTop q.2).rest,
      { arithTop q.2 with first := some (arithRet q.2) } :: q.2.stack.tail, none⟩
  | .and, true => ⟨q.2.input, q.2.stack.tail,
      some (polyConnective q.1.1.1 q.1.1.2 .and ((arithTop q.2).first.getD []) (arithRet q.2))⟩
  | .or, true => ⟨q.2.input, q.2.stack.tail,
      some (polyConnective q.1.1.1 q.1.1.2 .or ((arithTop q.2).first.getD []) (arithRet q.2))⟩
  | .ex, true => ⟨q.2.input, q.2.stack.tail, some (polyOperator q.1.1.1 q.1.1.2 .ex
      (arithVarPoly q.1.1.1 q.1.1.2 q.1.2.1 q.1.2.2 q.2.stack.tail (arithTop q.2).token.2)
      ((arithTop q.2).first.getD []) (arithRet q.2))⟩
  | .all, true => ⟨q.2.input, q.2.stack.tail, some (polyOperator q.1.1.1 q.1.1.2 .all
      (arithVarPoly q.1.1.1 q.1.1.2 q.1.2.1 q.1.2.2 q.2.stack.tail (arithTop q.2).token.2)
      ((arithTop q.2).first.getD []) (arithRet q.2))⟩
  | .lin, true => ⟨q.2.input, q.2.stack.tail, some (polyOperator q.1.1.1 q.1.1.2 .lin
      (arithVarPoly q.1.1.1 q.1.1.2 q.1.2.1 q.1.2.2 q.2.stack.tail (arithTop q.2).token.2)
      ((arithTop q.2).first.getD []) (arithRet q.2))⟩
  | .var, _ | .top, _ | .bot, _ => ⟨q.2.input, q.2.stack.tail, some (arithRet q.2)⟩

private theorem arithStep_eq (q : ArithStepIn) :
    arithStep q.1.1.1 q.1.1.2 q.1.2.1 q.1.2.2 q.2 =
      if q.2.value.isSome then
        if q.2.stack.isEmpty then q.2
        else arithRetStep (arithTop q.2).token.1 (arithTop q.2).first.isSome q
      else if q.2.input.isEmpty then
        ⟨q.2.input, q.2.stack, some (polyConst q.1.1.1 q.1.1.2 0)⟩
      else arithReadStep (arithHead q.2).1 q := by
  obtain ⟨⟨⟨p, D⟩, ⟨pt, xOpt⟩⟩, ⟨input, stack, value⟩⟩ := q
  rcases value with _ | b
  · rcases input with _ | ⟨⟨k, v⟩, input⟩
    · rfl
    · cases k <;> rfl
  · rcases stack with _ | ⟨⟨⟨k, x⟩, first, rest⟩, stack⟩
    · rfl
    · cases k <;> cases first <;> rfl

private lemma arithHead_pt :
    ComputableInPolyTime arithHead encArithState encArithToken :=
  ((headD (encA := encArithToken) (encL := encList encArithToken) (.top, 0)).comp
    arithState_input_pt).of_enc_eq fun _ => rfl

private lemma arithTop_pt :
    ComputableInPolyTime arithTop encArithState encArithFrame :=
  ((headD (encA := encArithFrame) (encL := encList encArithFrame)
    ⟨(.top, 0), none, []⟩).comp arithState_stack_pt).of_enc_eq fun _ => rfl

private lemma arithRet_pt :
    ComputableInPolyTime arithRet encArithState (encList encUnary) :=
  optionGetDWithInput arithState_value_pt (const [])

private lemma arithReadStep_pt (k : ArithQBF.Kind) :
    ComputableInPolyTime (arithReadStep k) encArithStepIn encArithState := by
  have hp := (fst encArithPar encArithState).fst'.fst'
  have hD := (fst encArithPar encArithState).fst'.snd'
  have hpt := (fst encArithPar encArithState).snd'.fst'
  have hxOpt := (fst encArithPar encArithState).snd'.snd'
  have hs := snd encArithPar encArithState
  have hin := arithState_input_pt.comp hs
  have hintail := (listTail encArithToken).comp hin
  have hstk := arithState_stack_pt.comp hs
  have hhd := arithHead_pt.comp hs
  have hpush := (cons encArithFrame).comp
    ((arithFrame_mk_comp_pt hhd (const none) hintail).prod hstk)
  have hsome := optionSome (encList encUnary)
  cases k with
  | var =>
    exact arithState_mk_comp_pt hintail hstk
      (hsome.comp (arithVarPoly_pt hp hD hpt hxOpt hstk hhd.snd'))
  | top => exact arithState_mk_comp_pt hintail hstk (hsome.comp (polyConst_pt hp hD (const 1)))
  | bot => exact arithState_mk_comp_pt hintail hstk (hsome.comp (polyConst_pt hp hD (const 0)))
  | not | and | or | ex | all | lin => exact arithState_mk_comp_pt hintail hpush (const none)

private lemma arithRetStep_pt (k : ArithQBF.Kind) (second : Bool) :
    ComputableInPolyTime (arithRetStep k second) encArithStepIn encArithState := by
  have hp := (fst encArithPar encArithState).fst'.fst'
  have hD := (fst encArithPar encArithState).fst'.snd'
  have hpt := (fst encArithPar encArithState).snd'.fst'
  have hxOpt := (fst encArithPar encArithState).snd'.snd'
  have hs := snd encArithPar encArithState
  have hin := arithState_input_pt.comp hs
  have hstk := arithState_stack_pt.comp hs
  have htail := (listTail encArithFrame).comp hstk
  have htop := arithTop_pt.comp hs
  have htok := arithFrame_token_pt.comp htop
  have hrest := arithFrame_rest_pt.comp htop
  have ha := optionGetDWithInput (arithFrame_first_pt.comp htop) (const [])
  have hb := arithRet_pt.comp hs
  have hsome := optionSome (encList encUnary)
  have hpush := (cons encArithFrame).comp
    ((arithFrame_mk_comp_pt htok (hsome.comp hb) hrest).prod htail)
  have ht := arithVarPoly_pt hp hD hpt hxOpt htail htok.snd'
  cases second with
  | false =>
    cases k with
    | not => exact arithState_mk_comp_pt hin htail (hsome.comp (polyOneSub_pt hp hD hb))
    | and | or => exact arithState_mk_comp_pt hin hpush (const none)
    | ex | all | lin => exact arithState_mk_comp_pt hrest hpush (const none)
    | var | top | bot => exact arithState_mk_comp_pt hin htail (hsome.comp hb)
  | true =>
    cases k with
    | not => exact arithState_mk_comp_pt hin htail (hsome.comp (polyOneSub_pt hp hD hb))
    | and => exact arithState_mk_comp_pt hin htail (hsome.comp (polyConnective_pt .and hp hD ha hb))
    | or => exact arithState_mk_comp_pt hin htail (hsome.comp (polyConnective_pt .or hp hD ha hb))
    | ex => exact arithState_mk_comp_pt hin htail (hsome.comp (polyOperator_pt .ex hp hD ht ha hb))
    | all =>
      exact arithState_mk_comp_pt hin htail (hsome.comp (polyOperator_pt .all hp hD ht ha hb))
    | lin =>
      exact arithState_mk_comp_pt hin htail (hsome.comp (polyOperator_pt .lin hp hD ht ha hb))
    | var | top | bot => exact arithState_mk_comp_pt hin htail (hsome.comp hb)

private theorem computableInPolyTime_arithStep :
    ComputableInPolyTime
      (fun q : ArithStepIn => arithStep q.1.1.1 q.1.1.2 q.1.2.1 q.1.2.2 q.2)
      encArithStepIn encArithState := by
  rw [show (fun q : ArithStepIn => arithStep q.1.1.1 q.1.1.2 q.1.2.1 q.1.2.2 q.2) = _ from
    funext arithStep_eq]
  have hs : ComputableInPolyTime (fun q : ArithStepIn => q.2) encArithStepIn encArithState :=
    snd encArithPar encArithState
  have hp : ComputableInPolyTime (fun q : ArithStepIn => q.1.1.1) encArithStepIn encUnary :=
    (fst encArithPar encArithState).fst'.fst'
  have hD : ComputableInPolyTime (fun q : ArithStepIn => q.1.1.2) encArithStepIn encUnary :=
    (fst encArithPar encArithState).fst'.snd'
  have hin : ComputableInPolyTime (fun q : ArithStepIn => q.2.input)
      encArithStepIn (encList encArithToken) := arithState_input_pt.comp hs
  have hstk : ComputableInPolyTime (fun q : ArithStepIn => q.2.stack)
      encArithStepIn (encList encArithFrame) := arithState_stack_pt.comp hs
  have hval : ComputableInPolyTime (fun q : ArithStepIn => q.2.value)
      encArithStepIn (encOption (encList encUnary)) := arithState_value_pt.comp hs
  have hzero : ComputableInPolyTime
      (fun q : ArithStepIn => ArithState.mk q.2.input q.2.stack
        (some (polyConst q.1.1.1 q.1.1.2 0))) encArithStepIn encArithState :=
    arithState_mk_comp_pt hin hstk
      ((optionSome (encList encUnary)).comp (polyConst_pt hp hD (const 0)))
  refine ite (optionIsSome hval)
    (ite ((listIsEmpty' encArithFrame).comp hstk) hs ?_)
    (ite ((listIsEmpty' encArithToken).comp hin) hzero ?_)
  · have htop := arithTop_pt.comp hs
    have htag : ComputableInPolyTime
        (fun q : ArithStepIn => ((arithTop q.2).token.1, (arithTop q.2).first.isSome))
        encArithStepIn (encPair (encFinEnum ArithQBF.Kind) encBool) :=
      (arithFrame_token_pt.comp htop).fst'.prod (optionIsSome (arithFrame_first_pt.comp htop))
    exact finite_cases (tagEncoding := encPair (encFinEnum ArithQBF.Kind) encBool)
      (tag := fun q : ArithStepIn => ((arithTop q.2).token.1, (arithTop q.2).first.isSome))
      (branch := fun tag => arithRetStep tag.1 tag.2) htag (fun t => arithRetStep_pt t.1 t.2)
  · have htag : ComputableInPolyTime (fun q : ArithStepIn => (arithHead q.2).1)
        encArithStepIn (encFinEnum ArithQBF.Kind) := (arithHead_pt.comp hs).fst'
    exact finite_cases (tagEncoding := encFinEnum ArithQBF.Kind)
      (tag := fun q : ArithStepIn => (arithHead q.2).1)
      (branch := arithReadStep) htag arithReadStep_pt

/-- Input tuple `((par, toks), fuel)` for running the arithmetic-formula stack evaluator. -/
abbrev RunArithIn := (ArithPar × List (ArithQBF.Kind × ℕ)) × ℕ

/-- Bitstring encoding of `RunArithIn`. -/
abbrev encRunArithIn : RunArithIn ↪ List Bool :=
  encPair (encPair encArithPar (encList encArithToken)) encUnary

/-- Running `arithStep` for `fuel` iterations from initial state `⟨toks, [], none⟩` is
polynomial-time in the encoded parameters, token list, and unary step count. -/
theorem computableInPolyTime_runArith :
    ComputableInPolyTime
      (fun x : RunArithIn =>
        (arithStep x.1.1.1.1 x.1.1.1.2 x.1.1.2.1 x.1.1.2.2)^[x.2] ⟨x.1.2, [], none⟩)
      encRunArithIn encArithState := by
  have hpar : ComputableInPolyTime (fun x : RunArithIn => x.1.1) encRunArithIn encArithPar :=
    (fst (encPair encArithPar (encList encArithToken)) encUnary).fst'
  have htoks : ComputableInPolyTime (fun x : RunArithIn => x.1.2)
      encRunArithIn (encList encArithToken) :=
    (fst (encPair encArithPar (encList encArithToken)) encUnary).snd'
  have hfuel : ComputableInPolyTime (fun x : RunArithIn => x.2) encRunArithIn encUnary :=
    snd (encPair encArithPar (encList encArithToken)) encUnary
  have hinit : ComputableInPolyTime (fun x : RunArithIn => ArithState.mk x.1.2 [] none)
      encRunArithIn encArithState :=
    arithState_mk_comp_pt htoks (const []) (const none)
  let B : RunArithIn → ℕ := fun x =>
    8 * ((encList encArithToken x.1.2).length + 1) *
      ((encList encArithToken x.1.2).length + (x.1.1.1.2 + 1) * (2 * (x.1.1.1.1 + 1) + 1) + 5) +
    (x.1.1.1.2 + 1) * (2 * (x.1.1.1.1 + 1) + 1) + 6
  have hB : PolyBounded (fun x : RunArithIn => (encRunArithIn x).length) B := by
    have hL : PolyBounded (fun x : RunArithIn => (encRunArithIn x).length)
        (fun x => (encList encArithToken x.1.2).length) := htoks.polyBounded_length
    have hp : PolyBounded (fun x : RunArithIn => (encRunArithIn x).length)
        (fun x => x.1.1.1.1) := hpar.fst'.fst'.polyBounded
    have hD : PolyBounded (fun x : RunArithIn => (encRunArithIn x).length)
        (fun x => x.1.1.1.2) := hpar.fst'.snd'.polyBounded
    have hP : PolyBounded (fun x : RunArithIn => (encRunArithIn x).length)
        (fun x => (x.1.1.1.2 + 1) * (2 * (x.1.1.1.1 + 1) + 1)) :=
      (hD.add (.const 1)).mul (((PolyBounded.const 2).mul (hp.add (.const 1))).add (.const 1))
    exact (((PolyBounded.const 8).mul (hL.add (.const 1))).mul
      ((hL.add hP).add (.const 5))).add (hP.add (.const 6)) |>.mono fun x => by dsimp [B]; omega
  exact iterateWith (encIn := encRunArithIn) (encPar := encArithPar) (encState := encArithState)
    (par := fun x => x.1.1) (count := fun x => x.2) (init := fun x => ⟨x.1.2, [], none⟩)
    (step := fun par s => arithStep par.1.1 par.1.2 par.2.1 par.2.2 s)
    hpar hfuel hinit computableInPolyTime_arithStep hB
    (fun x i _ => length_encArithState_le (goodArith_iterate_step _ _ _ _ _ i))

end ArithStepPolyTime


end CslibFrontier.Complexity
