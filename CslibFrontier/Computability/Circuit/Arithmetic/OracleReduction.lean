/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Papers Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.VNP
public import CslibFrontier.Computability.Circuit.Simulation
import CslibFrontier.Computability.Circuit.Arithmetic.Determinant
import CslibFrontier.Foundations.Data.Nat.PolynomialBound.Closure

/-!
# Polynomial oracle reductions ($c$-reductions) and `VNP`-completeness under oracle reductions

Bürgisser's *polynomial oracle reduction* ($c$-reduction, $f \le_c g$) between polynomial families
`f, g : PolynomialFamily K` equips arithmetic
circuits over `K` with oracle gates evaluating members `g.poly m` of `g` for indices `m` bounded by
a polynomially bounded function of `n`. Unlike Valiant's p-projections (`IsPProjection`), an oracle
circuit may invoke `g` multiple times and combine oracle outputs using ring additions and
multiplications, as in Lotz and Makowsky's `VNP`-completeness theorem for Traldi's dichromatic
polynomial.

Because unrestricted multiplications above an oracle gate can raise degree exponentially, the
relativized class `VPWithOracle g` (`\mathrm{VP}^g`) consists of *p-families* `f` (`f.IsPFamily`)
that reduce to `g` via polynomial-size oracle circuits.

## Main definitions

* `Cslib.Circuits.Arithmetic.ArithOracleOp`, `Cslib.Circuits.Arithmetic.arithOracleSignature`,
  `Cslib.Circuits.Arithmetic.arithOraclePolyInterp`: arithmetic circuit signature and formal
  polynomial interpretation with oracle gates for `g.poly m` (`m ≤ B`).
* `Cslib.Circuits.Arithmetic.PolynomialFamily.IsOracleReducible`: polynomial-size arithmetic oracle
  reducibility (`f ≤_c g`).
* `Cslib.Circuits.Arithmetic.VPWithOracle`: the relativized algebraic class `\mathrm{VP}^g`.
* `Cslib.Circuits.Arithmetic.IsVNPOracleHard`, `Cslib.Circuits.Arithmetic.IsVNPOracleComplete`:
  `VNP`-hardness and `VNP`-completeness under polynomial oracle reductions.

## Main results

* `Cslib.Circuits.Arithmetic.PolynomialFamily.IsOracleReducible.refl`,
  `Cslib.Circuits.Arithmetic.PolynomialFamily.IsOracleReducible.trans`: `≤_c` is a preorder on
  polynomial families.
* `Cslib.Circuits.Arithmetic.PolynomialFamily.IsPProjection.isOracleReducible`: every p-projection
  is a polynomial oracle reduction.
* `Cslib.Circuits.Arithmetic.VP.of_isOracleReducible`,
  `Cslib.Circuits.Arithmetic.VPWithOracle_eq_VP`: `VP` is closed under polynomial oracle reductions
  (`g ∈ VP K → VPWithOracle g = VP K`).
* `Cslib.Circuits.Arithmetic.IsVNPComplete.isVNPOracleComplete`,
  `Cslib.Circuits.Arithmetic.IsVNPOracleHard.VNP_subset_VP`: `VNP`-completeness under p-projections
  implies `VNP`-completeness under oracle reductions, and placing any `VNP`-oracle-hard family in
  `VP` collapses `VNP` to `VP`.
-/

@[expose] public section

namespace Cslib.Circuits.Arithmetic

open MvPolynomial Finset

universe u

section Signature

variable (K : Type u)

/-- Operations of an arithmetic oracle circuit with oracle index bound `B`: standard arithmetic
gates (`add`, `mul`, `const c`) together with `vars m`-ary oracle gates for `m : Fin (B + 1)`. -/
inductive ArithOracleOp (vars : ℕ → ℕ) (B : ℕ) : Type u
  /-- Standard addition, multiplication, or scalar constant gate. -/
  | arith (op : ArithOp K)
  /-- Oracle gate evaluating the `m`-th polynomial of the oracle family. -/
  | oracle (m : Fin (B + 1))

/-- Arity of an arithmetic-or-oracle operation. -/
abbrev ArithOracleOp.arity {vars : ℕ → ℕ} {B : ℕ} : ArithOracleOp K vars B → ℕ
  | .arith op => op.arity
  | .oracle m => vars m.1

/-- Arithmetic circuit signature augmented with oracle gates of arity `vars m` (`m ≤ B`). -/
abbrev arithOracleSignature (vars : ℕ → ℕ) (B : ℕ) : Signature.{u} where
  Op := ArithOracleOp K vars B
  Arity := ArithOracleOp.arity K

variable {K}

/-- Formal polynomial interpretation of `arithOracleSignature K g.vars B` inside
`MvPolynomial σ K`: arithmetic operations act on `MvPolynomial σ K`, and `.oracle m` substitutes
its argument polynomials into `g.poly m` via `MvPolynomial.aeval`. -/
noncomputable def arithOraclePolyInterp [CommSemiring K] (g : PolynomialFamily K) (B : ℕ)
    (σ : Type*) : Interpretation (arithOracleSignature K g.vars B) (MvPolynomial σ K)
  | .arith op, args => arithInterpretationWith K C op args
  | .oracle m, args => MvPolynomial.aeval args (g.poly m.1)

/-- Formal polynomial computed at output `j` by an arithmetic oracle circuit `c` relative to `g`. -/
noncomputable def oraclePolynomial [CommSemiring K] {g : PolynomialFamily K} {B n m : ℕ}
    (c : Circuit (arithOracleSignature K g.vars B) n m) (j : Fin m) :
    MvPolynomial (Fin n) K :=
  c.eval (arithOraclePolyInterp g B (Fin n)) X j

/-- Embedding a pure arithmetic operation into `arithOracleSignature`. -/
def embedArithCircuit {vars : ℕ → ℕ} {B n m : ℕ} (c : Circuit (arithSignature K) n m) :
    Circuit (arithOracleSignature K vars B) n m :=
  c.simulate fun op =>
    Circuit.oneGate (σ := arithOracleSignature K vars B) (.arith op) id

/-- `embedArithCircuit` preserves gate count. -/
@[simp]
theorem size_embedArithCircuit {vars : ℕ → ℕ} {B n m : ℕ} (c : Circuit (arithSignature K) n m) :
    (embedArithCircuit (vars := vars) (B := B) c).size = c.size := by
  rw [embedArithCircuit, Circuit.size_simulate]
  simp

/-- `embedArithCircuit` computes the same formal polynomial as `c.polynomial`. -/
theorem oraclePolynomial_embedArithCircuit [CommSemiring K] (g : PolynomialFamily K)
    {B n m : ℕ} (c : Circuit (arithSignature K) n m) (j : Fin m) :
    oraclePolynomial (g := g) (B := B) (embedArithCircuit c) j = c.polynomial j := by
  have hsim : (embedArithCircuit (vars := g.vars) (B := B) c).eval
      (arithOraclePolyInterp g B (Fin n)) =
      c.eval (arithInterpretationWith K C) := by
    refine Circuit.eval_simulate c _ fun op args => ?_
    funext k
    fin_cases k
    rfl
  exact congrFun (congrFun hsim X) j

/-- Evaluating an embedded pure arithmetic circuit at arbitrary `MvPolynomial σ K` inputs agrees
with `aeval` of `c.polynomial`. -/
theorem eval_embedArithCircuit_mvPolynomial [CommSemiring K] (g : PolynomialFamily K)
    {B n m : ℕ} {σ : Type*} (c : Circuit (arithSignature K) n m)
    (args : Fin n → MvPolynomial σ K) (j : Fin m) :
    (embedArithCircuit (vars := g.vars) (B := B) c).eval
        (arithOraclePolyInterp g B σ) args j =
      MvPolynomial.aeval args (c.polynomial j) := by
  have hsim : (embedArithCircuit (vars := g.vars) (B := B) c).eval
      (arithOraclePolyInterp g B σ) =
      c.eval (arithInterpretationWith K C) := by
    refine Circuit.eval_simulate c _ fun op x => ?_
    funext k
    fin_cases k
    rfl
  rw [congrFun (congrFun hsim args) j, Circuit.aeval_polynomial_mvPolynomial]

private theorem aeval_aeval_mvPolynomial [CommSemiring K] {ι τ σ : Type*}
    (args : τ → MvPolynomial σ K) (inputs : ι → MvPolynomial τ K) (P : MvPolynomial ι K) :
    MvPolynomial.aeval args (MvPolynomial.aeval inputs P) =
      MvPolynomial.aeval (fun i => MvPolynomial.aeval args (inputs i)) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [MvPolynomial.algebraMap_eq]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp => simp only [map_mul, aeval_X, hp]

/-- Evaluating an oracle circuit `c` on arbitrary `MvPolynomial σ K` inputs equals `aeval` of its
formal polynomial `oraclePolynomial c`. -/
theorem aeval_oraclePolynomial_mvPolynomial [CommSemiring K] {g : PolynomialFamily K}
    {B n m : ℕ} {σ : Type*} (c : Circuit (arithOracleSignature K g.vars B) n m)
    (args : Fin n → MvPolynomial σ K) (j : Fin m) :
    MvPolynomial.aeval args (oraclePolynomial c j) =
      c.eval (arithOraclePolyInterp g B σ) args j := by
  let hom : Homomorphism
      (arithOraclePolyInterp g B (Fin n))
      (arithOraclePolyInterp g B σ) :=
    ⟨MvPolynomial.aeval args, fun op inputs => by
      cases op with
      | arith aop =>
        cases aop <;> simp [arithOraclePolyInterp, arithInterpretationWith]
      | oracle idx =>
        exact aeval_aeval_mvPolynomial args inputs (g.poly idx.1)⟩
  simpa [hom, oraclePolynomial, Function.comp_def] using congrFun (c.map_eval hom X) j

end Signature

section Reductions

variable {K : Type u} [CommSemiring K]

/-- **Polynomial oracle reducibility (`f ≤_c g`)**:
there exist a polynomially bounded oracle-index bound `B : ℕ → ℕ` and a family of polynomial-size
arithmetic oracle circuits `c n` over `g` computing `f.poly n` as a formal polynomial.
-/
def PolynomialFamily.IsOracleReducible (f g : PolynomialFamily K) : Prop :=
  ∃ (B : ℕ → ℕ) (c : ∀ n, Circuit (arithOracleSignature K g.vars (B n)) (f.vars n) 1),
    PolynomiallyBounded B ∧
      PolynomiallyBounded (fun n => (c n).size) ∧
      ∀ n, oraclePolynomial (g := g) (c n) 0 = f.poly n

/-- Every polynomial family is oracle-reducible to itself (via a single top-level oracle gate). -/
theorem PolynomialFamily.IsOracleReducible.refl (f : PolynomialFamily K) :
    f.IsOracleReducible f := by
  refine ⟨id, fun n =>
      Circuit.oneGate (σ := arithOracleSignature K f.vars n)
        (.oracle ⟨n, Nat.lt_succ_self n⟩) id,
    PolynomiallyBounded.id, (PolynomiallyBounded.const 1).mono_of_le fun _ => le_rfl,
    fun n => ?_⟩
  change MvPolynomial.aeval X (f.poly n) = f.poly n
  exact MvPolynomial.aeval_X_left_apply (f.poly n)

private noncomputable def prefixMax (s : ℕ → ℕ) : ℕ → ℕ
  | 0 => s 0
  | n + 1 => max (prefixMax s n) (s (n + 1))

private theorem le_prefixMax (s : ℕ → ℕ) : ∀ {m B : ℕ}, m ≤ B → s m ≤ prefixMax s B := by
  intro m B
  induction B generalizing m with
  | zero =>
    intro hm
    obtain rfl := Nat.eq_zero_of_le_zero hm
    exact le_rfl
  | succ B ih =>
    intro hm
    rcases Nat.of_le_succ hm with hle | rfl
    · exact (ih hle).trans (le_max_left _ _)
    · exact le_max_right _ _

private theorem polynomiallyBounded_prefixMax {s : ℕ → ℕ} (hs : PolynomiallyBounded s) :
    PolynomiallyBounded (prefixMax s) := by
  obtain ⟨c, d, hs⟩ := polynomiallyBounded_iff_le.1 hs
  refine PolynomiallyBounded.of_forall_le c d fun B => ?_
  induction B with
  | zero => exact hs 0
  | succ B ih =>
    refine max_le (ih.trans ?_) (hs (B + 1))
    exact Nat.mul_le_mul_left c (Nat.pow_le_pow_left (by omega) d)

/-- Single-gate implementation widening the oracle index budget `B₁ ≤ B₂`. -/
def widenOracleImpl {vars : ℕ → ℕ} {B₁ B₂ : ℕ} (hB : B₁ ≤ B₂) :
    ∀ op : (arithOracleSignature K vars B₁).Op,
      Circuit (arithOracleSignature K vars B₂)
        ((arithOracleSignature K vars B₁).Arity op) 1
  | .arith op =>
    Circuit.oneGate (σ := arithOracleSignature K vars B₂) (.arith op) id
  | .oracle idx =>
    Circuit.oneGate (σ := arithOracleSignature K vars B₂)
      (.oracle ⟨idx.1, Nat.lt_succ_of_le ((Nat.le_of_lt_succ idx.2).trans hB)⟩) id

/-- Widening the oracle index budget `B₁ ≤ B₂` on an arithmetic oracle circuit preserves size and
formal polynomial semantics. -/
def widenOracleBound {vars : ℕ → ℕ} {B₁ B₂ n m : ℕ} (hB : B₁ ≤ B₂)
    (c : Circuit (arithOracleSignature K vars B₁) n m) :
    Circuit (arithOracleSignature K vars B₂) n m :=
  c.simulate (widenOracleImpl hB)

omit [CommSemiring K] in
@[simp]
theorem size_widenOracleBound {vars : ℕ → ℕ} {B₁ B₂ n m : ℕ} (hB : B₁ ≤ B₂)
    (c : Circuit (arithOracleSignature K vars B₁) n m) :
    (widenOracleBound hB c).size = c.size := by
  rw [widenOracleBound, Circuit.size_simulate]
  have h1 : (fun op : ArithOracleOp K vars B₁ => (widenOracleImpl hB op).size) = fun _ => 1 := by
    funext op
    cases op <;> rfl
  rw [h1, c.program.cost_const 1, one_mul]

theorem eval_widenOracleBound {g : PolynomialFamily K} {B₁ B₂ n m : ℕ} (hB : B₁ ≤ B₂)
    {σ : Type*} (c : Circuit (arithOracleSignature K g.vars B₁) n m) :
    (widenOracleBound hB c).eval (arithOraclePolyInterp g B₂ σ) =
      c.eval (arithOraclePolyInterp g B₁ σ) := by
  refine Circuit.eval_simulate c _ fun op args => ?_
  cases op with
  | arith a =>
    funext j
    fin_cases j
    rfl
  | oracle idx =>
    funext j
    fin_cases j
    rfl

/-- **Polynomial oracle reductions compose**. -/
theorem PolynomialFamily.IsOracleReducible.trans {f g h : PolynomialFamily K}
    (hfg : f.IsOracleReducible g) (hgh : g.IsOracleReducible h) :
    f.IsOracleReducible h := by
  obtain ⟨B₁, c₁, hB₁, hsize₁, hpoly₁⟩ := hfg
  obtain ⟨B₂, c₂, hB₂, hsize₂, hpoly₂⟩ := hgh
  let B : ℕ → ℕ := fun n => prefixMax B₂ (B₁ n)
  have hB : PolynomiallyBounded B := (polynomiallyBounded_prefixMax hB₂).comp hB₁
  let impl (n : ℕ) : ∀ op : (arithOracleSignature K g.vars (B₁ n)).Op,
      Circuit (arithOracleSignature K h.vars (B n))
        ((arithOracleSignature K g.vars (B₁ n)).Arity op) 1
    | .arith aop =>
      Circuit.oneGate (σ := arithOracleSignature K h.vars (B n)) (.arith aop) id
    | .oracle idx =>
      widenOracleBound (le_prefixMax B₂ (Nat.le_of_lt_succ idx.2)) (c₂ idx.1)
  let c : ∀ n, Circuit (arithOracleSignature K h.vars (B n)) (f.vars n) 1 :=
    fun n => (c₁ n).simulate (impl n)
  have hsize_bound : PolynomiallyBounded (fun n => (c n).size) := by
    have hmax : PolynomiallyBounded (fun n => max 1 (prefixMax (fun m => (c₂ m).size) (B₁ n))) :=
      ((PolynomiallyBounded.const 1).add
        ((polynomiallyBounded_prefixMax hsize₂).comp hB₁)).mono_of_le fun n =>
        max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _)
    refine (hmax.mul hsize₁).mono_of_le fun n => ?_
    rw [Circuit.size_simulate]
    refine (c₁ n).program.cost_le_mul fun op => ?_
    cases op with
    | arith _ => exact le_max_left _ _
    | oracle idx =>
      dsimp only [impl]
      rw [size_widenOracleBound]
      exact (le_prefixMax (fun m => (c₂ m).size) (Nat.le_of_lt_succ idx.2)).trans
        (le_max_right _ _)
  refine ⟨B, c, hB, hsize_bound, fun n => ?_⟩
  have hsim : (c n).eval (arithOraclePolyInterp h (B n) (Fin (f.vars n))) =
      (c₁ n).eval (arithOraclePolyInterp g (B₁ n) (Fin (f.vars n))) := by
    refine Circuit.eval_simulate (c₁ n) (impl n) fun op args => ?_
    cases op with
    | arith aop =>
      funext j
      fin_cases j
      rfl
    | oracle idx =>
      funext j
      rw [Subsingleton.elim j 0]
      dsimp only [impl, single]
      rw [congrFun (eval_widenOracleBound _ (c₂ idx.1)) args,
        ← aeval_oraclePolynomial_mvPolynomial, hpoly₂ idx.1]
      rfl
  exact (congrFun (congrFun hsim X) 0).trans (hpoly₁ n)

/-- **Every p-projection is a polynomial oracle reduction**:
apply `projectionCircuit` and feed its outputs into a single oracle gate.
-/
theorem PolynomialFamily.IsPProjection.isOracleReducible {f g : PolynomialFamily K}
    (hfg : f.IsPProjection g) (hgvars : PolynomiallyBounded g.vars) :
    f.IsOracleReducible g := by
  obtain ⟨t, ht, hproj⟩ := hfg
  choose ρ hρ using hproj
  let gate (n : ℕ) :
      Circuit (arithOracleSignature K g.vars (t n)) (g.vars (t n)) 1 :=
    Circuit.oneGate (σ := arithOracleSignature K g.vars (t n))
      (.oracle ⟨t n, Nat.lt_succ_self (t n)⟩) id
  let sub (n : ℕ) :
      Circuit (arithOracleSignature K g.vars (t n)) (f.vars n) (g.vars (t n)) :=
    embedArithCircuit (projectionCircuit (ρ n))
  refine ⟨t, fun n => (gate n).comp (sub n), ht,
    ((hgvars.comp ht).add (PolynomiallyBounded.const 1)).mono_of_le fun n => ?_, fun n => ?_⟩
  · rw [Circuit.size_comp, size_embedArithCircuit]
    exact Nat.add_le_add_right (size_projectionCircuit_le (ρ n)) 1
  · rw [oraclePolynomial, Circuit.eval_comp]
    dsimp only [gate, Circuit.eval_oneGate, arithOraclePolyInterp, id_eq]
    have hargs : (fun a : Fin (g.vars (t n)) =>
        (sub n).eval (arithOraclePolyInterp g (t n) (Fin (f.vars n))) X a) =
        fun a => Sum.elim X C (ρ n a) := by
      funext a
      dsimp only [sub]
      rw [eval_embedArithCircuit_mvPolynomial, MvPolynomial.aeval_X_left_apply]
      exact eval_projectionCircuit C (ρ n) X a
    rw [hargs, ← projection, hρ n]

/-- **Relativized algebraic complexity class `VP^g` (`VPWithOracle g`)**
: p-families that are polynomially oracle-reducible to
`g`.
-/
def VPWithOracle (g : PolynomialFamily K) : Set (PolynomialFamily K) :=
  {f | f.IsPFamily ∧ f.IsOracleReducible g}

/-- Every pure `VP` family belongs to `VPWithOracle g` for any polynomial family `g`. -/
theorem VP_subset_VPWithOracle (g : PolynomialFamily K) : VP K ⊆ VPWithOracle g := by
  rintro f ⟨hf, c, hsize, hpoly⟩
  refine ⟨hf, fun _ => 0, fun n => embedArithCircuit (c n), PolynomiallyBounded.const 0,
    hsize.mono_of_le fun n => by simp, fun n => ?_⟩
  rw [oraclePolynomial_embedArithCircuit, hpoly n]

/-- **`VP` is closed under polynomial oracle reductions**:
if `g ∈ VP K`, `f ≤_c g`, and `f` is a p-family, then `f ∈ VP K`.
-/
theorem VP.of_isOracleReducible {f g : PolynomialFamily K} (hg : g ∈ VP K)
    (hfg : f.IsOracleReducible g) (hf : f.IsPFamily) : f ∈ VP K := by
  obtain ⟨_, cg, hcg_size, hcg_poly⟩ := hg
  obtain ⟨B, c, hB, hc_size, hc_poly⟩ := hfg
  let impl (n : ℕ) : ∀ op : (arithOracleSignature K g.vars (B n)).Op,
      Circuit (arithSignature K) ((arithOracleSignature K g.vars (B n)).Arity op) 1
    | .arith aop => Circuit.oneGate (σ := arithSignature K) aop id
    | .oracle idx => cg idx.1
  let d : ∀ n, Circuit (arithSignature K) (f.vars n) 1 := fun n => (c n).simulate (impl n)
  have hd_size : PolynomiallyBounded (fun n => (d n).size) := by
    have hmax : PolynomiallyBounded (fun n => max 1 (prefixMax (fun m => (cg m).size) (B n))) :=
      ((PolynomiallyBounded.const 1).add
        ((polynomiallyBounded_prefixMax hcg_size).comp hB)).mono_of_le fun n =>
        max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _)
    refine (hmax.mul hc_size).mono_of_le fun n => ?_
    rw [Circuit.size_simulate]
    refine (c n).program.cost_le_mul fun op => ?_
    cases op with
    | arith _ => exact le_max_left _ _
    | oracle idx =>
      exact (le_prefixMax (fun m => (cg m).size) (Nat.le_of_lt_succ idx.2)).trans
        (le_max_right _ _)
  refine ⟨hf, d, hd_size, fun n => ?_⟩
  have hsim : (d n).eval (arithInterpretationWith K C) =
      (c n).eval (arithOraclePolyInterp g (B n) (Fin (f.vars n))) := by
    refine Circuit.eval_simulate (c n) (impl n) fun op args => ?_
    cases op with
    | arith aop =>
      funext j
      fin_cases j
      rfl
    | oracle idx =>
      funext j
      rw [Subsingleton.elim j 0]
      dsimp only [impl, single, arithOraclePolyInterp]
      rw [← Circuit.aeval_polynomial_mvPolynomial, hcg_poly idx.1]
  exact (congrFun (congrFun hsim X) 0).trans (hc_poly n)

/-- **`VP` relative to an oracle in `VP` equals `VP`** (`g ∈ VP K → VP^g = VP`). -/
theorem VPWithOracle_eq_VP {g : PolynomialFamily K} (hg : g ∈ VP K) :
    VPWithOracle g = VP K :=
  Set.Subset.antisymm (fun _ ⟨hf, hred⟩ => VP.of_isOracleReducible hg hred hf)
    (VP_subset_VPWithOracle g)

/-- **`VNP`-hardness under polynomial oracle reductions (`≤_c`)**: every family in `VNP K`
reduces to `g` by a polynomial oracle reduction. -/
def IsVNPOracleHard (g : PolynomialFamily K) : Prop :=
  ∀ ⦃f : PolynomialFamily K⦄, f ∈ VNP K → f.IsOracleReducible g

/-- **`VNP`-completeness under polynomial oracle reductions (`≤_c`)**: `g ∈ VNP K` and `g` is
`VNP`-hard under polynomial oracle reductions. -/
def IsVNPOracleComplete (g : PolynomialFamily K) : Prop :=
  g ∈ VNP K ∧ IsVNPOracleHard g

/-- `VNP`-completeness under p-projections implies `VNP`-completeness under polynomial oracle
reductions. -/
theorem IsVNPComplete.isVNPOracleComplete {g : PolynomialFamily K} (hg : IsVNPComplete g) :
    IsVNPOracleComplete g :=
  ⟨hg.1, fun f hf => (hg.2 f hf).isOracleReducible (VNP.isPFamily hg.1).1⟩

/-- `VNP`-oracle-hardness transfers along polynomial oracle reductions. -/
theorem IsVNPOracleHard.trans {g h : PolynomialFamily K} (hg : IsVNPOracleHard g)
    (hgh : g.IsOracleReducible h) : IsVNPOracleHard h :=
  fun _ hf => (hg hf).trans hgh

/-- **Collapse criterion**: if a `VNP`-oracle-hard family belongs to `VP K`, then `VNP K ⊆ VP K`
(and hence `VP K = VNP K`). -/
theorem IsVNPOracleHard.VNP_subset_VP {g : PolynomialFamily K} (hg : IsVNPOracleHard g)
    (hVP : g ∈ VP K) : VNP K ⊆ VP K :=
  fun _ hf => VP.of_isOracleReducible hVP (hg hf) (VNP.isPFamily hf)

/-- For a `VNP`-oracle-complete family `g`, `g ∈ VP K ↔ VNP K ⊆ VP K`. -/
theorem IsVNPOracleComplete.mem_VP_iff {g : PolynomialFamily K} (hg : IsVNPOracleComplete g) :
    g ∈ VP K ↔ VNP K ⊆ VP K :=
  ⟨IsVNPOracleHard.VNP_subset_VP hg.2, fun hsub => hsub hg.1⟩

-- Concrete non-vacuity and separation check: over any nontrivial commutative ring `R`, the
-- determinant family lies in `VPWithOracle (detFamily R)` whereas `powTwoPowFamily R` does not.
private theorem detFamily_mem_and_powTwoPowFamily_not_mem_VPWithOracle {R : Type u} [CommRing R]
    [Nontrivial R] :
    detFamily R ∈ VPWithOracle (detFamily R) ∧
      powTwoPowFamily R ∉ VPWithOracle (detFamily R) := by
  rw [VPWithOracle_eq_VP detFamily_mem_VP]
  exact ⟨detFamily_mem_VP, powTwoPowFamily_not_mem_VP⟩

end Reductions

end Cslib.Circuits.Arithmetic
