module

public import CslibFrontier.Computability.Complexity.Problems.ThreeSAT
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
public import CslibFrontier.Logics.Propositional.CNF.ModelCount
import CslibFrontier.Computability.Complexity.Classes.NP.Witness
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import CslibFrontier.Logics.Propositional.CNF.PolyTime

/-!
# Explicit Binary Covering Radius is NP-Complete

This module formalizes the explicit binary **Covering Radius** decision problem
: given a binary code `C ⊆ {0, 1}^n` (represented as an explicit list of length-`n` bit
strings) and an integer radius `r`, decide whether there exists `v ∈ {0, 1}^n` whose Hamming
distance to every codeword `c ∈ C` is strictly greater than `r`.

We prove native `NP`-completeness directly under standard Lean axioms by a polynomial-time
reduction from `ThreeSAT` (`Cslib.Complexity.ThreeSAT_npHard`) using complementary variable pairs
and two boost pairs.

## Main definitions

- `hammingDist`: Hamming distance between two bit strings (of equal length).
- `CoveringRadiusInstance`, `encCoveringRadius`: binary covering-radius instances and encoding.
- `CoveringRadius`: the explicit binary covering-radius language.

## Main results

- `CoveringRadius_mem_NP`: `CoveringRadius ∈ NP encCoveringRadius`.
- `CoveringRadius_npHard`: `NPHard encCoveringRadius CoveringRadius`.
- `CoveringRadius_npComplete`: `NPComplete encCoveringRadius CoveringRadius`.
-/

public section

namespace Cslib.Complexity

open Cslib.Logic.PL Turing.MultiTapeTM ComputableInPolyTime

/-- Hamming distance between two bit strings, computed over indices `0, ..., v.length - 1`. -/
@[expose]
def hammingDist (v c : List Bool) : ℕ :=
  (List.range v.length).countP fun i => v.getD i false != c.getD i false

/-- Hamming distance of equal-length strings is symmetric. -/
theorem hammingDist_comm {v c : List Bool} (h : v.length = c.length) :
    hammingDist v c = hammingDist c v := by
  simp only [hammingDist, h]
  exact List.countP_congr fun i _ => by cases v.getD i false <;> cases c.getD i false <;> rfl

/-- Helper: `l.getD i d = l[i]` for in-bounds indices. -/
private theorem getD_eq_getElem_of_lt {α : Type*} {l : List α} {i : ℕ} {d : α}
    (hi : i < l.length) : l.getD i d = l[i] := by
  simp [List.getD_eq_getElem?_getD, hi]

/-- Complementing the second string flips the Hamming distance to `v.length - hammingDist v c`. -/
theorem hammingDist_map_not {v c : List Bool} (h : v.length = c.length) :
    hammingDist v (c.map (!·)) = v.length - hammingDist v c := by
  have hle : hammingDist v c ≤ v.length := by
    simpa [hammingDist] using List.countP_le_length (l := List.range v.length)
  have hsum : hammingDist v (c.map (!·)) + hammingDist v c = v.length := by
    have hsplit := List.length_eq_countP_add_countP
      (fun i => (v.getD i false != c.getD i false) = true) (l := List.range v.length)
    rw [List.length_range] at hsplit
    have h1 : hammingDist v (c.map (!·)) =
        (List.range v.length).countP (fun i => !(v.getD i false != c.getD i false)) := by
      simp only [hammingDist]
      refine List.countP_congr fun i hi => ?_
      have hilt : i < c.length := by rw [← h]; exact List.mem_range.mp hi
      rw [getD_eq_getElem_of_lt (l := c.map (!·)) (by simpa using hilt), List.getElem_map,
        getD_eq_getElem_of_lt (l := c) hilt]
      cases v.getD i false <;> cases c[i] <;> rfl
    rw [h1]
    have h2 : (List.range v.length).countP (fun i => !(v.getD i false != c.getD i false)) =
        (List.range v.length).countP (fun i => ¬((v.getD i false != c.getD i false) = true)) :=
      List.countP_congr fun _ _ => by simp
    rw [h2, add_comm]
    exact hsplit.symm
  omega

/-- Hamming distance on `List Bool` of length `2 * m` decomposes as the sum of pair distances. -/
theorem hammingDist_eq_sum_pairs {v c : List Bool} {m : ℕ} (hv : v.length = 2 * m) :
    hammingDist v c = ∑ i ∈ Finset.range m,
      ((if v.getD (2 * i) false != c.getD (2 * i) false then 1 else 0) +
       (if v.getD (2 * i + 1) false != c.getD (2 * i + 1) false then 1 else 0)) := by
  have hgen : ∀ k, (List.range (2 * k)).countP (fun j => v.getD j false != c.getD j false) =
      ∑ i ∈ Finset.range k,
        ((if v.getD (2 * i) false != c.getD (2 * i) false then 1 else 0) +
         (if v.getD (2 * i + 1) false != c.getD (2 * i + 1) false then 1 else 0)) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [show 2 * (k + 1) = 2 * k + 1 + 1 by omega, List.range_succ, List.range_succ,
        List.countP_append, List.countP_append, ih, Finset.sum_range_succ]
      simp only [List.countP_cons, List.countP_nil]
      cases v.getD (2 * k) false != c.getD (2 * k) false <;>
        cases v.getD (2 * k + 1) false != c.getD (2 * k + 1) false <;> simp
  simpa [hammingDist, hv] using hgen m

/-- An instance of the explicit binary **Covering Radius** problem: length `len`, explicit list
of binary codewords `code`, and threshold radius `radius`. -/
@[ext]
structure CoveringRadiusInstance where
  /-- Common bit-length of all codewords. -/
  len : ℕ
  /-- Explicit list of binary codewords. -/
  code : List (List Bool)
  /-- Covering radius threshold. -/
  radius : ℕ
  deriving DecidableEq, Repr, Inhabited

/-- Encoding of `CoveringRadiusInstance`: unary `len`, framed list of bit strings `code`,
and binary `radius`. -/
enc_structure encCoveringRadius : CoveringRadiusInstance where
  len : encUnary,
  code : (encList encBits),
  radius : encNat

attribute [fun_prop] encCoveringRadius_len_polyTime encCoveringRadius_code_polyTime
  encCoveringRadius_radius_polyTime encCoveringRadius_mk_polyTime

/-- Well-formedness of a covering-radius instance: every codeword has length `len`. -/
@[expose]
def CoveringRadiusInstance.WellFormed (x : CoveringRadiusInstance) : Prop :=
  ∀ c ∈ x.code, c.length = x.len

/-- The explicit binary **Covering Radius** decision problem: is there a length-`len` binary
string at Hamming distance strictly greater than `radius` from every codeword in `code`? -/
@[expose]
def CoveringRadius : Set CoveringRadiusInstance :=
  {x | x.WellFormed ∧ ∃ v : List Bool, v.length = x.len ∧ ∀ c ∈ x.code, x.radius < hammingDist v c}

/-- Computing `hammingDist` on raw bit strings is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_hammingDist {γ : Type} {encIn : γ ↪ List Bool}
    {f g : γ → List Bool}
    (hf : ComputableInPolyTime f encIn encBits)
    (hg : ComputableInPolyTime g encIn encBits) :
    ComputableInPolyTime (fun x => hammingDist (f x) (g x)) encIn encUnary := by
  unfold hammingDist
  have hlen : ComputableInPolyTime (fun x => (f x).length) encIn encUnary := by fun_prop
  have hr : ComputableInPolyTime (fun x => List.range (f x).length) encIn (encList encUnary) :=
    range.comp hlen
  refine countPWithInput hr ?_
  have h1 : ComputableInPolyTime (fun p : γ × ℕ => (f p.1).getD p.2 false)
      (encPair encIn encUnary) encBool :=
    bitsGetDWithInput (hf.comp (fst encIn encUnary)) (snd encIn encUnary) false
  have h2 : ComputableInPolyTime (fun p : γ × ℕ => (g p.1).getD p.2 false)
      (encPair encIn encUnary) encBool :=
    bitsGetDWithInput (hg.comp (fst encIn encUnary)) (snd encIn encUnary) false
  fun_prop

namespace CoveringRadius

/-- Polynomial-time verifier for `CoveringRadius`: checks well-formedness and that the prefix of
length `x.len` of the certificate has Hamming distance `> x.radius` from every codeword. -/
@[expose]
def verifier (p : CoveringRadiusInstance × List Bool) : Bool :=
  p.1.code.all (fun c => decide (c.length = p.1.len)) &&
    p.1.code.all (fun c => decide (p.1.radius < hammingDist (p.2.take p.1.len) c))

/-- `CoveringRadius.verifier` is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_verifier :
    ComputableInPolyTime verifier (encPair encCoveringRadius encBits) encBool := by
  unfold verifier
  have htake : ComputableInPolyTime
      (fun p : CoveringRadiusInstance × List Bool => p.2.take p.1.len)
      (encPair encCoveringRadius encBits) encBits :=
    bitsTakeWithInput (snd encCoveringRadius encBits)
      (encCoveringRadius_len_polyTime (fst encCoveringRadius encBits))
  have h1 : ComputableInPolyTime
      (fun p : CoveringRadiusInstance × List Bool =>
        p.1.code.all (fun c => decide (c.length = p.1.len)))
      (encPair encCoveringRadius encBits) encBool := by
    refine allWithInput (encCoveringRadius_code_polyTime (fst encCoveringRadius encBits)) ?_
    have hcl : ComputableInPolyTime (fun q : (CoveringRadiusInstance × List Bool) × List Bool =>
        q.2.length) (encPair (encPair encCoveringRadius encBits) encBits) encUnary := by fun_prop
    have hxl : ComputableInPolyTime (fun q : (CoveringRadiusInstance × List Bool) × List Bool =>
        q.1.1.len) (encPair (encPair encCoveringRadius encBits) encBits) encUnary := by fun_prop
    fun_prop
  have h2 : ComputableInPolyTime
      (fun p : CoveringRadiusInstance × List Bool =>
        p.1.code.all (fun c => decide (p.1.radius < hammingDist (p.2.take p.1.len) c)))
      (encPair encCoveringRadius encBits) encBool := by
    refine allWithInput (encCoveringRadius_code_polyTime (fst encCoveringRadius encBits)) ?_
    have hrad : ComputableInPolyTime (fun q : (CoveringRadiusInstance × List Bool) × List Bool =>
        q.1.1.radius) (encPair (encPair encCoveringRadius encBits) encBits) encNat := by fun_prop
    have hdist : ComputableInPolyTime (fun q : (CoveringRadiusInstance × List Bool) × List Bool =>
        hammingDist (q.1.2.take q.1.1.len) q.2)
        (encPair (encPair encCoveringRadius encBits) encBits) encUnary :=
      computableInPolyTime_hammingDist (htake.comp (fst _ _)) (snd _ _)
    have hdistB : ComputableInPolyTime (fun q : (CoveringRadiusInstance × List Bool) × List Bool =>
        hammingDist (q.1.2.take q.1.1.len) q.2)
        (encPair (encPair encCoveringRadius encBits) encBits) encNat :=
      unary_to_binary.comp hdist
    fun_prop
  fun_prop

/-- `CoveringRadius.verifier` verifies `CoveringRadius` with certificates of length `|enc x|`. -/
theorem isVerifier :
    IsVerifier encCoveringRadius Polynomial.X verifier CoveringRadius := by
  have hlen_le (x : CoveringRadiusInstance) : x.len ≤ (encCoveringRadius x).length := by
    have h1 : (encUnary x.len).length ≤ (encCoveringRadius x).length := by
      rw [encCoveringRadius_apply, length_encPair, length_encPair]
      dsimp only
      omega
    simpa only [encUnary_apply, List.length_replicate] using h1
  refine IsVerifier.of_padding (fun x w hw h => ?_) fun x ⟨hWF, v, hv, hdist⟩ => ?_
  · simp only [verifier, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
    refine ⟨h.1, w.take x.len, ?_, h.2⟩
    have hle : x.len ≤ w.length := by
      rw [hw, Polynomial.eval_X]
      exact hlen_le x
    exact List.length_take_of_le hle
  · refine ⟨v, by simpa only [hv, Polynomial.eval_X] using hlen_le x, fun k => ?_⟩
    simp only [verifier, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
    rw [List.take_left' hv]
    exact ⟨hWF, hdist⟩

/-- `CoveringRadius` belongs to `NP`. -/
theorem mem_NP : CoveringRadius ∈ NP encCoveringRadius :=
  ⟨Polynomial.X, verifier, computableInPolyTime_verifier, isVerifier⟩

/-! ### Polynomial-time reduction from `ThreeSAT` -/

/-- Fixed NO-instance of `CoveringRadius`: code `{00, 11}` with radius `1` covers `{0,1}²`. -/
@[expose]
def noInstance : CoveringRadiusInstance :=
  ⟨2, [[false, false], [true, true]], 1⟩

/-- `noInstance` is not in `CoveringRadius`. -/
theorem noInstance_not_mem : noInstance ∉ CoveringRadius := by
  rintro ⟨_, v, hv, hdist⟩
  have h0 := hdist [false, false] (by simp [noInstance])
  have h1 := hdist [true, true] (by simp [noInstance])
  have hc : [true, true] = ([false, false] : List Bool).map (!·) := by decide
  rw [hc, hammingDist_map_not (by simp [noInstance, hv])] at h1
  rw [hv] at h1
  dsimp [noInstance] at h0 h1
  omega

/-- Test whether a clause is tautological (contains both `(v, true)` and `(v, false)`). -/
@[expose]
def isTautClause (c : Clause ℕ) : Bool :=
  c.any fun l => c.contains (l.1, !l.2)

/-- Build a binary codeword of length `m` from a per-coordinate Boolean predicate. -/
@[expose]
def mkBits (m : ℕ) (f : ℕ → Bool) : List Bool :=
  (List.range m).map f

private theorem length_mkBits (m : ℕ) (f : ℕ → Bool) : (mkBits m f).length = m := by
  simp [mkBits]

private theorem getD_mkBits {m j : ℕ} (f : ℕ → Bool) (hj : j < m) :
    (mkBits m f).getD j false = f j := by
  simp [mkBits, List.getD_eq_getElem?_getD, hj]

/-- Clause codeword for a non-empty, non-tautological clause `c` of length `≤ 3` over variables
`vars` of length `n`: total length `2 * (n + 2)`. -/
@[expose]
def clauseCodeword (vars : List ℕ) (c : Clause ℕ) : List Bool :=
  let c' := c.dedup
  let n := vars.length
  mkBits (2 * (n + 2)) fun j =>
    let i := j / 2
    let isOdd := decide (j % 2 = 1)
    if i < n then
      let v := vars.getD i 0
      if c'.contains (v, true) then isOdd
      else if c'.contains (v, false) then !isOdd
      else false
    else if i < n + (c'.length - 1) then isOdd
    else false

/-- Reduction from `ThreeSAT` to `CoveringRadius`. -/
@[expose]
def ofThreeSAT (φ : CNF ℕ) : CoveringRadiusInstance :=
  if φ.all (fun c => decide (c.length ≤ 3) && !c.isEmpty) then
    let vars := φ.distinctVars
    let n := vars.length
    let N := 2 * (n + 2)
    let base : List (List Bool) :=
      [mkBits N (fun _ => false), mkBits N (fun _ => true)] ++
      ((List.range (n + 2)).flatMap fun k =>
        [mkBits N (fun j => decide (j / 2 = k)),
         mkBits N (fun j => !(decide (j / 2 = k)))]) ++
      [mkBits N (fun j => decide (j = 2 * n + 1)),
       mkBits N (fun j => decide (j = 2 * (n + 1) + 1))]
    let cls : List (List Bool) :=
      (φ.filter fun c => !isTautClause c).map (clauseCodeword vars)
    ⟨N, base ++ cls, n + 1⟩
  else noInstance

/-- Helper: `mkBits` with a polynomial-time bit function is polynomial-time into `encBits`. -/
private theorem computableInPolyTime_mkBits {γ : Type} {encIn : γ ↪ List Bool}
    {m : γ → ℕ} {f : γ → ℕ → Bool}
    (hm : ComputableInPolyTime m encIn encUnary)
    (hf : ComputableInPolyTime (fun p : γ × ℕ => f p.1 p.2) (encPair encIn encUnary) encBool) :
    ComputableInPolyTime (fun x => mkBits (m x) (f x)) encIn encBits := by
  unfold mkBits
  exact mapToBitsWithInput (range.comp hm) hf

/-- Helper: `List.dedup` on clauses is computable in polynomial time. -/
private theorem computableInPolyTime_clause_dedup :
    ComputableInPolyTime (fun l : Clause ℕ => l.dedup)
      (encList (encPair encNat encBool)) (encList (encPair encNat encBool)) := by
  have hdedup_eq : ∀ l : List (Literal ℕ), l.dedup =
      (l.zipIdx.filter fun p => !(l.drop (p.2 + 1)).contains p.1).map Prod.fst := by
    intro l
    induction l with
    | nil => rfl
    | cons a t ih =>
      rw [List.dedup_cons, List.zipIdx_cons, List.filter_cons, Nat.zero_add,
        List.drop_succ_cons, List.drop_zero]
      have hshift : ∀ (xs : List (Literal ℕ)) (k : ℕ),
          ((xs.zipIdx (k + 1)).filter fun p => !(t.drop p.2).contains p.1).map Prod.fst =
          ((xs.zipIdx k).filter fun p => !(t.drop (p.2 + 1)).contains p.1).map Prod.fst := by
        intro xs k
        induction xs generalizing k with
        | nil => rfl
        | cons x ys ih2 =>
          simp only [List.zipIdx_cons, List.filter_cons]
          cases (t.drop (k + 1)).contains x
          · simp only [Bool.not_false, ↓reduceIte, List.map_cons, ih2 (k + 1)]
          · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, ih2 (k + 1)]
      have htail : ((t.zipIdx 1).filter fun p =>
            !((a :: t).drop (p.2 + 1)).contains p.1).map Prod.fst =
          ((t.zipIdx 0).filter fun p => !(t.drop (p.2 + 1)).contains p.1).map Prod.fst := by
        simpa [List.drop_succ_cons] using hshift t 0
      by_cases ha : a ∈ t
      · have hca : t.contains a = true := List.contains_iff_mem.mpr ha
        simp only [ha, ↓reduceIte, hca, Bool.not_true, Bool.false_eq_true, htail, ih]
      · have hca : t.contains a = false := by
          cases hc : t.contains a
          · rfl
          · exact absurd (List.contains_iff_mem.mp hc) ha
        simp only [ha, ↓reduceIte, hca, Bool.not_false, List.map_cons, htail, ih]
  have hpoly_dedup : ComputableInPolyTime (fun l : Clause ℕ =>
      (l.zipIdx.filter fun p => !(l.drop (p.2 + 1)).contains p.1).map Prod.fst)
      (encList (encPair encNat encBool)) (encList (encPair encNat encBool)) := by
    refine (map (fst (encPair encNat encBool) encUnary)).comp ?_
    refine filterWithInput (zipIdx (encPair encNat encBool)) ?_
    have hdrop : ComputableInPolyTime (fun q : Clause ℕ × (Literal ℕ × ℕ) =>
        q.1.drop (q.2.2 + 1))
        (encPair (encList (encPair encNat encBool)) (encPair (encPair encNat encBool) encUnary))
        (encList (encPair encNat encBool)) :=
      listDropWithInput (fst _ _) (by fun_prop)
    exact bool_not.comp (contains hdrop (by fun_prop))
  have heq : (fun l : Clause ℕ => l.dedup) =
      fun l : Clause ℕ => (l.zipIdx.filter fun p => !(l.drop (p.2 + 1)).contains p.1).map
        Prod.fst := funext hdedup_eq
  rw [heq]
  exact hpoly_dedup

/-- Helper: `clauseCodeword` is computable in polynomial time. -/
private theorem computableInPolyTime_clauseCodeword :
    ComputableInPolyTime (fun p : CNF ℕ × Clause ℕ => clauseCodeword p.1.distinctVars p.2)
      (encPair encCNF (encList (encPair encNat encBool))) encBits := by
  have hvars : ComputableInPolyTime (fun φ : CNF ℕ => φ.distinctVars) encCNF (encList encNat) :=
    CNF.computableInPolyTime_distinctVars encNat
  have hn : ComputableInPolyTime (fun φ : CNF ℕ => φ.distinctVars.length) encCNF encUnary := by
    fun_prop
  have hN : ComputableInPolyTime (fun φ : CNF ℕ => 2 * (φ.distinctVars.length + 2))
      encCNF encUnary := by fun_prop
  have hdedup : ComputableInPolyTime (fun p : CNF ℕ × Clause ℕ => p.2.dedup)
      (encPair encCNF (encList (encPair encNat encBool))) (encList (encPair encNat encBool)) :=
    computableInPolyTime_clause_dedup.comp (snd _ _)
  have hN' : ComputableInPolyTime (fun p : CNF ℕ × Clause ℕ =>
      2 * (p.1.distinctVars.length + 2)) (encPair encCNF (encList (encPair encNat encBool)))
      encUnary := hN.comp (fst _ _)
  have hbody : ComputableInPolyTime
      (fun q : (CNF ℕ × Clause ℕ) × ℕ =>
        if decide (q.2 / 2 < q.1.1.distinctVars.length) then
          if q.1.2.dedup.contains (q.1.1.distinctVars.getD (q.2 / 2) 0, true) then
            decide (q.2 % 2 = 1)
          else if q.1.2.dedup.contains (q.1.1.distinctVars.getD (q.2 / 2) 0, false) then
            !decide (q.2 % 2 = 1)
          else false
        else if decide (q.2 / 2 < q.1.1.distinctVars.length + (q.1.2.dedup.length - 1)) then
          decide (q.2 % 2 = 1)
        else false)
      (encPair (encPair encCNF (encList (encPair encNat encBool))) encUnary) encBool := by
    have hi : ComputableInPolyTime (fun q : (CNF ℕ × Clause ℕ) × ℕ => q.2 / 2)
        (encPair (encPair encCNF (encList (encPair encNat encBool))) encUnary) encUnary :=
      (unary_div_const 2).comp (snd _ _)
    have hmod : ComputableInPolyTime (fun q : (CNF ℕ × Clause ℕ) × ℕ => decide (q.2 % 2 = 1))
        (encPair (encPair encCNF (encList (encPair encNat encBool))) encUnary) encBool := by
      have hm2 : ComputableInPolyTime (fun q : (CNF ℕ × Clause ℕ) × ℕ => q.2 % 2)
          (encPair (encPair encCNF (encList (encPair encNat encBool))) encUnary) encUnary :=
        unary_mod.comp ((snd _ _).prod (const 2))
      fun_prop
    have hvars' : ComputableInPolyTime (fun q : (CNF ℕ × Clause ℕ) × ℕ => q.1.1.distinctVars)
        (encPair (encPair encCNF (encList (encPair encNat encBool))) encUnary)
        (encList encNat) :=
      hvars.comp ((fst _ _).comp (fst _ _))
    have hn' : ComputableInPolyTime (fun q : (CNF ℕ × Clause ℕ) × ℕ => q.1.1.distinctVars.length)
        (encPair (encPair encCNF (encList (encPair encNat encBool))) encUnary) encUnary :=
      hn.comp ((fst _ _).comp (fst _ _))
    have hc' : ComputableInPolyTime (fun q : (CNF ℕ × Clause ℕ) × ℕ => q.1.2.dedup)
        (encPair (encPair encCNF (encList (encPair encNat encBool))) encUnary)
        (encList (encPair encNat encBool)) :=
      hdedup.comp (fst _ _)
    have hv : ComputableInPolyTime (fun q : (CNF ℕ × Clause ℕ) × ℕ =>
        q.1.1.distinctVars.getD (q.2 / 2) 0)
        (encPair (encPair encCNF (encList (encPair encNat encBool))) encUnary) encNat :=
      listGetDWithInput hvars' hi 0
    have hct : ComputableInPolyTime (fun q : (CNF ℕ × Clause ℕ) × ℕ =>
        q.1.2.dedup.contains (q.1.1.distinctVars.getD (q.2 / 2) 0, true))
        (encPair (encPair encCNF (encList (encPair encNat encBool))) encUnary) encBool :=
      contains hc' (hv.prod (const true))
    have hcf : ComputableInPolyTime (fun q : (CNF ℕ × Clause ℕ) × ℕ =>
        q.1.2.dedup.contains (q.1.1.distinctVars.getD (q.2 / 2) 0, false))
        (encPair (encPair encCNF (encList (encPair encNat encBool))) encUnary) encBool :=
      contains hc' (hv.prod (const false))
    have hlt1 : ComputableInPolyTime (fun q : (CNF ℕ × Clause ℕ) × ℕ =>
        decide (q.2 / 2 < q.1.1.distinctVars.length))
        (encPair (encPair encCNF (encList (encPair encNat encBool))) encUnary) encBool := by
      fun_prop
    have hlt2 : ComputableInPolyTime (fun q : (CNF ℕ × Clause ℕ) × ℕ =>
        decide (q.2 / 2 < q.1.1.distinctVars.length + (q.1.2.dedup.length - 1)))
        (encPair (encPair encCNF (encList (encPair encNat encBool))) encUnary) encBool := by
      have hclen : ComputableInPolyTime (fun q : (CNF ℕ × Clause ℕ) × ℕ => q.1.2.dedup.length)
          (encPair (encPair encCNF (encList (encPair encNat encBool))) encUnary) encUnary :=
        (length_list _).comp hc'
      have hsub : ComputableInPolyTime (fun q : (CNF ℕ × Clause ℕ) × ℕ =>
          q.1.2.dedup.length - 1)
          (encPair (encPair encCNF (encList (encPair encNat encBool))) encUnary) encUnary :=
        unary_sub' hclen (const 1)
      have hadd : ComputableInPolyTime (fun q : (CNF ℕ × Clause ℕ) × ℕ =>
          q.1.1.distinctVars.length + (q.1.2.dedup.length - 1))
          (encPair (encPair encCNF (encList (encPair encNat encBool))) encUnary) encUnary :=
        unary_add' hn' hsub
      fun_prop
    exact hlt1.ite (hct.ite hmod (hcf.ite (bool_not.comp hmod) (const false)))
      (hlt2.ite hmod (const false))
  have hmk := computableInPolyTime_mkBits
    (f := fun (p : CNF ℕ × Clause ℕ) (j : ℕ) =>
      if decide (j / 2 < p.1.distinctVars.length) then
        if p.2.dedup.contains (p.1.distinctVars.getD (j / 2) 0, true) then
          decide (j % 2 = 1)
        else if p.2.dedup.contains (p.1.distinctVars.getD (j / 2) 0, false) then
          !decide (j % 2 = 1)
        else false
      else if decide (j / 2 < p.1.distinctVars.length + (p.2.dedup.length - 1)) then
        decide (j % 2 = 1)
      else false) hN' hbody
  have heq : (fun p : CNF ℕ × Clause ℕ => clauseCodeword p.1.distinctVars p.2) =
      (fun p : CNF ℕ × Clause ℕ =>
        mkBits (2 * (p.1.distinctVars.length + 2)) fun j =>
          if decide (j / 2 < p.1.distinctVars.length) then
            if p.2.dedup.contains (p.1.distinctVars.getD (j / 2) 0, true) then
              decide (j % 2 = 1)
            else if p.2.dedup.contains (p.1.distinctVars.getD (j / 2) 0, false) then
              !decide (j % 2 = 1)
            else false
          else if decide (j / 2 < p.1.distinctVars.length + (p.2.dedup.length - 1)) then
            decide (j % 2 = 1)
          else false) := by
    funext p
    simp [clauseCodeword]
  rw [heq]
  exact hmk

/-- Helper: forming a 2-element list `[f x, g x]` is polynomial-time. -/
private theorem computableInPolyTime_pair2 {γ β : Type} {encIn : γ ↪ List Bool}
    {encB : β ↪ List Bool} {f g : γ → β}
    (hf : ComputableInPolyTime f encIn encB) (hg : ComputableInPolyTime g encIn encB) :
    ComputableInPolyTime (fun x => [f x, g x]) encIn (encList encB) :=
  (cons encB).comp (hf.prod ((cons encB).comp (hg.prod (const ([] : List β)))))

/-- The reduction `ofThreeSAT` is computable in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_ofThreeSAT :
    ComputableInPolyTime ofThreeSAT encCNF encCoveringRadius := by
  have hguard : ComputableInPolyTime
      (fun φ : CNF ℕ => φ.all fun c => decide (c.length ≤ 3) && !c.isEmpty)
      encCNF encBool := by
    refine allWithInput id' ?_
    have hcl : ComputableInPolyTime (fun p : CNF ℕ × Clause ℕ => p.2.length)
        (encPair encCNF (encList (encPair encNat encBool))) encUnary := by fun_prop
    have hem : ComputableInPolyTime (fun p : CNF ℕ × Clause ℕ => p.2.isEmpty)
        (encPair encCNF (encList (encPair encNat encBool))) encBool :=
      (listIsEmpty' (encPair encNat encBool)).comp (snd _ _)
    fun_prop
  have hvars : ComputableInPolyTime (fun φ : CNF ℕ => φ.distinctVars) encCNF (encList encNat) :=
    CNF.computableInPolyTime_distinctVars encNat
  have hn : ComputableInPolyTime (fun φ : CNF ℕ => φ.distinctVars.length) encCNF encUnary :=
    (length_list encNat).comp hvars
  have hN : ComputableInPolyTime (fun φ : CNF ℕ => 2 * (φ.distinctVars.length + 2))
      encCNF encUnary :=
    unary_mul' (const 2) (unary_add' hn (const 2))
  have hallF : ComputableInPolyTime (fun φ : CNF ℕ => mkBits (2 * (φ.distinctVars.length + 2))
      (fun _ => false)) encCNF encBits :=
    computableInPolyTime_mkBits hN (const false)
  have hallT : ComputableInPolyTime (fun φ : CNF ℕ => mkBits (2 * (φ.distinctVars.length + 2))
      (fun _ => true)) encCNF encBits :=
    computableInPolyTime_mkBits hN (const true)
  have hpair : ComputableInPolyTime
      (fun φ : CNF ℕ => (List.range (φ.distinctVars.length + 2)).flatMap fun k =>
        [mkBits (2 * (φ.distinctVars.length + 2)) (fun j => decide (j / 2 = k)),
         mkBits (2 * (φ.distinctVars.length + 2)) (fun j => !(decide (j / 2 = k)))])
      encCNF (encList encBits) := by
    refine flatMapWithInput (range.comp (unary_add' hn (const 2))) ?_
    have hN' : ComputableInPolyTime (fun p : CNF ℕ × ℕ => 2 * (p.1.distinctVars.length + 2))
        (encPair encCNF encUnary) encUnary := hN.comp (fst _ _)
    have hp1 : ComputableInPolyTime
        (fun p : CNF ℕ × ℕ => mkBits (2 * (p.1.distinctVars.length + 2))
          (fun j => decide (j / 2 = p.2)))
        (encPair encCNF encUnary) encBits :=
      computableInPolyTime_mkBits (f := fun (p : CNF ℕ × ℕ) j => decide (j / 2 = p.2)) hN'
        (decide_eq' ((unary_div_const 2).comp (snd _ _)) ((snd _ _).comp (fst _ _)))
    have hp2 : ComputableInPolyTime
        (fun p : CNF ℕ × ℕ => mkBits (2 * (p.1.distinctVars.length + 2))
          (fun j => !(decide (j / 2 = p.2))))
        (encPair encCNF encUnary) encBits :=
      computableInPolyTime_mkBits (f := fun (p : CNF ℕ × ℕ) j => !(decide (j / 2 = p.2))) hN'
        (bool_not.comp (decide_eq' ((unary_div_const 2).comp (snd _ _))
          ((snd _ _).comp (fst _ _))))
    exact computableInPolyTime_pair2 hp1 hp2
  have hb1 : ComputableInPolyTime (fun φ : CNF ℕ => mkBits (2 * (φ.distinctVars.length + 2))
      (fun j => decide (j = 2 * φ.distinctVars.length + 1))) encCNF encBits :=
    computableInPolyTime_mkBits
      (f := fun (φ : CNF ℕ) j => decide (j = 2 * φ.distinctVars.length + 1)) hN
      (decide_eq' (snd _ _) (unary_add' (unary_mul' (const 2) (hn.comp (fst _ _))) (const 1)))
  have hb2 : ComputableInPolyTime (fun φ : CNF ℕ => mkBits (2 * (φ.distinctVars.length + 2))
      (fun j => decide (j = 2 * (φ.distinctVars.length + 1) + 1))) encCNF encBits :=
    computableInPolyTime_mkBits
      (f := fun (φ : CNF ℕ) j => decide (j = 2 * (φ.distinctVars.length + 1) + 1)) hN
      (decide_eq' (snd _ _)
        (unary_add' (unary_mul' (const 2) (unary_add' (hn.comp (fst _ _)) (const 1))) (const 1)))
  have htaut : ComputableInPolyTime isTautClause
      (encList (encPair encNat encBool)) encBool := by
    unfold isTautClause
    refine anyWithInput id' ?_
    have hlist : ComputableInPolyTime
        (fun p : Clause ℕ × Literal ℕ => p.1)
        (encPair (encList (encPair encNat encBool)) (encPair encNat encBool))
        (encList (encPair encNat encBool)) := by fun_prop
    have hlit : ComputableInPolyTime
        (fun p : Clause ℕ × Literal ℕ => (p.2.1, !p.2.2))
        (encPair (encList (encPair encNat encBool)) (encPair encNat encBool))
        (encPair encNat encBool) := by fun_prop
    exact contains hlist hlit
  have hcls : ComputableInPolyTime
      (fun φ : CNF ℕ => (φ.filter fun c => !isTautClause c).map (clauseCodeword φ.distinctVars))
      encCNF (encList encBits) := by
    have hfilt : ComputableInPolyTime (fun φ : CNF ℕ => φ.filter fun c => !isTautClause c)
        encCNF encCNF :=
      filterWithInput id' (bool_not.comp (htaut.comp (snd _ _)))
    exact mapWithInput hfilt computableInPolyTime_clauseCodeword
  have hcode : ComputableInPolyTime
      (fun φ : CNF ℕ =>
        (([mkBits (2 * (φ.distinctVars.length + 2)) (fun _ => false),
           mkBits (2 * (φ.distinctVars.length + 2)) (fun _ => true)] ++
          ((List.range (φ.distinctVars.length + 2)).flatMap fun k =>
            [mkBits (2 * (φ.distinctVars.length + 2)) (fun j => decide (j / 2 = k)),
             mkBits (2 * (φ.distinctVars.length + 2)) (fun j => !(decide (j / 2 = k)))]) ++
          [mkBits (2 * (φ.distinctVars.length + 2))
             (fun j => decide (j = 2 * φ.distinctVars.length + 1)),
           mkBits (2 * (φ.distinctVars.length + 2))
             (fun j => decide (j = 2 * (φ.distinctVars.length + 1) + 1))]) ++
         (φ.filter fun c => !isTautClause c).map (clauseCodeword φ.distinctVars)))
      encCNF (encList encBits) := by
    have h01 := computableInPolyTime_pair2 hallF hallT
    have hb12 := computableInPolyTime_pair2 hb1 hb2
    have hb := (listAppend encBits).comp (((listAppend encBits).comp (h01.prod hpair)).prod hb12)
    exact (listAppend encBits).comp (hb.prod hcls)
  have hrad : ComputableInPolyTime (fun φ : CNF ℕ => φ.distinctVars.length + 1) encCNF encNat :=
    unary_to_binary.comp (unary_add' hn (const 1))
  have hmain := hguard.ite (encCoveringRadius_mk_polyTime hN hcode hrad) (const noInstance)
  have heq : ofThreeSAT = fun φ =>
      if (φ.all fun c => decide (c.length ≤ 3) && !c.isEmpty) = true then
        ⟨2 * (φ.distinctVars.length + 2),
          (([mkBits (2 * (φ.distinctVars.length + 2)) (fun _ => false),
             mkBits (2 * (φ.distinctVars.length + 2)) (fun _ => true)] ++
            ((List.range (φ.distinctVars.length + 2)).flatMap fun k =>
              [mkBits (2 * (φ.distinctVars.length + 2)) (fun j => decide (j / 2 = k)),
               mkBits (2 * (φ.distinctVars.length + 2)) (fun j => !(decide (j / 2 = k)))]) ++
            [mkBits (2 * (φ.distinctVars.length + 2))
               (fun j => decide (j = 2 * φ.distinctVars.length + 1)),
             mkBits (2 * (φ.distinctVars.length + 2))
               (fun j => decide (j = 2 * (φ.distinctVars.length + 1) + 1))]) ++
           (φ.filter fun c => !isTautClause c).map (clauseCodeword φ.distinctVars)),
          φ.distinctVars.length + 1⟩
      else noInstance := by
    funext φ; rfl
  rw [heq]
  exact hmain

/-- Helper: exact Hamming distance from a consistent, boost-aligned `v` to
`clauseCodeword vars c`. -/
private theorem pair_dist_eq (φ : CNF ℕ)
    (hlen3 : ∀ c ∈ φ, c.length ≤ 3) (hne : ∀ c ∈ φ, c ≠ [])
    (v : List Bool) (hv : v.length = 2 * (φ.distinctVars.length + 2))
    (hcons : ∀ i < φ.distinctVars.length + 2,
      (if v.getD (2 * i) false then 1 else 0) +
      (if v.getD (2 * i + 1) false then 1 else 0) = 1)
    (hboost : ∀ b, φ.distinctVars.length ≤ b → b < φ.distinctVars.length + 2 →
      v.getD (2 * b) false = true ∧ v.getD (2 * b + 1) false = false)
    (c : Clause ℕ) (hc : c ∈ φ) (hnt : isTautClause c = false) :
    let vars := φ.distinctVars
    let n := vars.length
    let c' := c.dedup
    let satCount := (Finset.range n).filter (fun i =>
      (c'.contains (vars.getD i 0, true) && v.getD (2 * i) false) ||
      (c'.contains (vars.getD i 0, false) && !v.getD (2 * i) false))
    hammingDist v (clauseCodeword vars c) = n + 1 + 2 * satCount.card := by
  intro vars n c' satCount
  change ∀ i < n + 2, _ at hcons
  change ∀ b, n ≤ b → b < n + 2 → _ at hboost
  let N := 2 * (n + 2)
  rw [hammingDist_eq_sum_pairs (m := n + 2) hv]
  have hsplit : Finset.range (n + 2) = Finset.range n ∪ {n, n + 1} := by
    ext i; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_insert,
      Finset.mem_singleton]; omega
  have hdisj : Disjoint (Finset.range n) ({n, n + 1} : Finset ℕ) := by
    simp only [Finset.disjoint_iff_ne, Finset.mem_range, Finset.mem_insert,
      Finset.mem_singleton]
    rintro a ha b (rfl | rfl) <;> omega
  rw [hsplit, Finset.sum_union hdisj]
  have hnot_both : ∀ i < n,
      ¬(c'.contains (vars.getD i 0, true) = true ∧
        c'.contains (vars.getD i 0, false) = true) := by
    intro i _ ⟨h1, h2⟩
    have hm1 : (vars.getD i 0, true) ∈ c := List.mem_dedup.mp (List.contains_iff_mem.mp h1)
    have hm2 : (vars.getD i 0, false) ∈ c := List.mem_dedup.mp (List.contains_iff_mem.mp h2)
    have ht : isTautClause c = true := by
      rw [isTautClause, List.any_eq_true]
      exact ⟨(vars.getD i 0, true), hm1, List.contains_iff_mem.mpr hm2⟩
    rw [hnt] at ht; exact Bool.false_ne_true ht
  have hvars_nodup : vars.Nodup := CNF.nodup_distinctVars φ
  have hcl_card : ((Finset.range n).filter fun i =>
      c'.contains (vars.getD i 0, true) || c'.contains (vars.getD i 0, false)).card =
      c'.length := by
    let f : ℕ → Literal ℕ := fun i =>
      if c'.contains (vars.getD i 0, true) then (vars.getD i 0, true)
      else (vars.getD i 0, false)
    have hinj : Set.InjOn f ((Finset.range n).filter fun i =>
        c'.contains (vars.getD i 0, true) || c'.contains (vars.getD i 0, false)) := by
      intro i hi j hj hfeq
      have hi' := Finset.mem_filter.mp hi
      have hj' := Finset.mem_filter.mp hj
      have hv_eq : vars.getD i 0 = vars.getD j 0 := by
        have := congrArg Prod.fst hfeq
        dsimp only [f] at this
        split_ifs at this <;> exact this
      have hi_lt : i < vars.length := Finset.mem_range.mp hi'.1
      have hj_lt : j < vars.length := Finset.mem_range.mp hj'.1
      rw [getD_eq_getElem_of_lt hi_lt, getD_eq_getElem_of_lt hj_lt] at hv_eq
      exact (List.Nodup.getElem_inj_iff hvars_nodup).mp hv_eq
    have himg : ((Finset.range n).filter fun i =>
        c'.contains (vars.getD i 0, true) || c'.contains (vars.getD i 0, false)).image f =
        c'.toFinset := by
      ext l
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_range, Bool.or_eq_true,
        List.mem_toFinset]
      constructor
      · rintro ⟨i, ⟨_, hmem⟩, rfl⟩
        rcases hmem with h1 | h2
        · dsimp only [f]; rw [h1]; exact List.contains_iff_mem.mp h1
        · cases hct : c'.contains (vars.getD i 0, true)
          · dsimp only [f]; rw [hct]; exact List.contains_iff_mem.mp h2
          · dsimp only [f]; rw [hct]; exact List.contains_iff_mem.mp hct
      · intro hl
        have hl_c : l ∈ c := List.mem_dedup.mp hl
        have hlv : l.1 ∈ vars :=
          CNF.mem_distinctVars.mpr (by
            rw [CNF.vars, List.mem_map]
            exact ⟨l, List.mem_flatten.mpr ⟨c, hc, hl_c⟩, rfl⟩)
        obtain ⟨i, hi, hget⟩ := List.getElem_of_mem hlv
        refine ⟨i, ⟨hi, ?_⟩, ?_⟩
        · cases hlb : l.2
          · right; rw [List.contains_iff_mem, getD_eq_getElem_of_lt hi, hget, ← hlb]
            exact hl
          · left; rw [List.contains_iff_mem, getD_eq_getElem_of_lt hi, hget, ← hlb]
            exact hl
        · cases hlb : l.2
          · have hnt' : c'.contains (vars.getD i 0, true) = false := by
              by_contra htrue
              have htrue' : c'.contains (vars.getD i 0, true) = true := by
                cases h : c'.contains (vars.getD i 0, true) <;> simp_all
              have hfalse' : c'.contains (vars.getD i 0, false) = true := by
                rw [List.contains_iff_mem, getD_eq_getElem_of_lt hi, hget, ← hlb]; exact hl
              exact hnot_both i hi ⟨htrue', hfalse'⟩
            dsimp only [f]; rw [hnt', getD_eq_getElem_of_lt hi, hget]
            simp only [Bool.false_eq_true, ↓reduceIte]
            exact Prod.ext rfl hlb.symm
          · have htrue' : c'.contains (vars.getD i 0, true) = true := by
              rw [List.contains_iff_mem, getD_eq_getElem_of_lt hi, hget, ← hlb]; exact hl
            dsimp only [f]; rw [htrue', getD_eq_getElem_of_lt hi, hget]
            simp only [↓reduceIte]
            exact Prod.ext rfl hlb.symm
    rw [← Finset.card_image_of_injOn hinj, himg,
      List.toFinset_card_of_nodup (List.nodup_dedup c)]
  have hvar_sum : ∑ i ∈ Finset.range n,
      ((if v.getD (2 * i) false != (clauseCodeword vars c).getD (2 * i) false then 1 else 0) +
       (if v.getD (2 * i + 1) false != (clauseCodeword vars c).getD (2 * i +
         1) false then 1 else 0)) =
      n - c'.length + 2 * satCount.card := by
    have hpart : ∀ i ∈ Finset.range n,
        ((if v.getD (2 * i) false != (clauseCodeword vars c).getD (2 * i) false then 1 else 0) +
         (if v.getD (2 * i + 1) false != (clauseCodeword vars c).getD (2 * i +
           1) false then 1 else 0)) +
        (if c'.contains (vars.getD i 0, true) || c'.contains (vars.getD i 0,
          false) then 1 else 0) =
        1 + 2 * (if c'.contains (vars.getD i 0, true) && v.getD (2 * i) false ||
                    c'.contains (vars.getD i 0,
                      false) && !v.getD (2 * i) false then 1 else 0) := by
      intro i hi
      have hin : i < n := Finset.mem_range.mp hi
      have hci := hcons i (by omega)
      have hnb := hnot_both i hin
      have hlt0 : 2 * i < N := by omega
      have hlt1 : 2 * i + 1 < N := by omega
      have hc0 : (clauseCodeword vars c).getD (2 * i) false =
          if c'.contains (vars.getD i 0, true) then false
          else if c'.contains (vars.getD i 0, false) then true else false := by
        dsimp only [clauseCodeword]
        rw [getD_mkBits _ hlt0]
        simp [c', vars, n, hin, Nat.mul_div_right _ (by decide : 0 < 2)]
      have hc1 : (clauseCodeword vars c).getD (2 * i + 1) false =
          if c'.contains (vars.getD i 0, true) then true
          else if c'.contains (vars.getD i 0, false) then false else false := by
        have hd : (2 * i + 1) / 2 = i := by omega
        have hm : (2 * i + 1) % 2 = 1 := by omega
        dsimp only [clauseCodeword]
        rw [getD_mkBits _ hlt1]
        simp [c', vars, n, hd, hm, hin]
      rw [hc0, hc1]
      have h16 : ∀ v0 v1 ct cf : Bool,
          ((if v0 then 1 else 0) + (if v1 then 1 else 0) = 1) →
          ¬(ct = true ∧ cf = true) →
          ((if v0 != (if ct then false else if cf then true else false) then 1 else 0) +
           (if v1 != (if ct then true else if cf then false else false) then 1 else 0)) +
          (if ct || cf then 1 else 0) =
          1 + 2 * (if ct && v0 || cf && !v0 then 1 else 0) := by decide
      exact h16 _ _ _ _ hci hnb
    have hsum_eq := Finset.sum_congr rfl hpart
    rw [Finset.sum_add_distrib,
      Finset.sum_add_distrib (s := Finset.range n) (f := fun _ => 1),
      ← Finset.mul_sum] at hsum_eq
    simp only [Finset.sum_boole, Finset.sum_const, Finset.card_range, smul_eq_mul,
      mul_one] at hsum_eq
    have hle_c' : c'.length ≤ n := by
      rw [← hcl_card]
      exact Finset.card_filter_le _ _ |>.trans (by simp)
    rw [hcl_card] at hsum_eq
    change _ + c'.length = n + 2 * satCount.card at hsum_eq
    omega
  have hc'_pos : 1 ≤ c'.length := by
    obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil c (hne c hc)
    exact List.length_pos_of_ne_nil (List.ne_nil_of_mem (List.mem_dedup.mpr hx))
  have hc'_le3 : c'.length ≤ 3 :=
    (List.Sublist.length_le (List.dedup_sublist c)).trans (hlen3 c hc)
  have hboost_sum :
      ∑ i ∈ ({n, n + 1} : Finset ℕ),
        ((if v.getD (2 * i) false != (clauseCodeword vars c).getD (2 * i) false then 1 else 0) +
         (if v.getD (2 * i + 1) false != (clauseCodeword vars c).getD (2 * i +
           1) false then 1 else 0)) =
      c'.length + 1 := by
    have hne_nn1 : n ≠ n + 1 := by omega
    rw [Finset.sum_pair hne_nn1]
    obtain ⟨hbn0, hbn1⟩ := hboost n le_rfl (by omega)
    obtain ⟨hbn2, hbn3⟩ := hboost (n + 1) (by omega) (by omega)
    have ha : (clauseCodeword vars c).getD (2 * n) false = false := by
      dsimp only [clauseCodeword]; rw [getD_mkBits _ (by omega)]
      have hd : (2 * n) / 2 = n := by omega
      have hm : (2 * n) % 2 = 0 := by omega
      simp [n, hd, hm]
    have hb : (clauseCodeword vars c).getD (2 * n + 1) false =
        decide (n < n + (c'.length - 1)) := by
      dsimp only [clauseCodeword]; rw [getD_mkBits _ (by omega)]
      have hd : (2 * n + 1) / 2 = n := by omega
      have hm : (2 * n + 1) % 2 = 1 := by omega
      simp [c', vars, n, hd, hm]
    have hc'' : (clauseCodeword vars c).getD (2 * (n + 1)) false = false := by
      dsimp only [clauseCodeword]; rw [getD_mkBits _ (by omega)]
      have hd : (2 * (n + 1)) / 2 = n + 1 := by omega
      have hm : (2 * (n + 1)) % 2 = 0 := by omega
      simp [n, hd, hm]
    have hd : (clauseCodeword vars c).getD (2 * (n + 1) + 1) false =
        decide (n + 1 < n + (c'.length - 1)) := by
      dsimp only [clauseCodeword]; rw [getD_mkBits _ (by omega)]
      have hd' : (2 * (n + 1) + 1) / 2 = n + 1 := by omega
      have hm' : (2 * (n + 1) + 1) % 2 = 1 := by omega
      simp [c', vars, n, hd', hm']
    rw [ha, hb, hc'', hd, hbn0, hbn1, hbn2, hbn3]
    have hcases : c'.length = 1 ∨ c'.length = 2 ∨ c'.length = 3 := by omega
    rcases hcases with h1 | h2 | h3
    · simp [h1]
    · simp [h2]
    · simp [h3]
  rw [hvar_sum, hboost_sum]
  have hle_c' : c'.length ≤ n := by
    rw [← hcl_card]
    exact (Finset.card_filter_le _ _).trans (by simp)
  omega

/-- Correctness of `ofThreeSAT`: `ofThreeSAT φ ∈ CoveringRadius ↔ φ ∈ ThreeSAT`. -/
theorem ofThreeSAT_mem_iff (φ : CNF ℕ) : ofThreeSAT φ ∈ CoveringRadius ↔ φ ∈ ThreeSAT := by
  by_cases hvalid : (φ.all fun c => decide (c.length ≤ 3) && !c.isEmpty) = true
  · have hlen3 : ∀ c ∈ φ, c.length ≤ 3 := fun c hc => by
      have := List.all_eq_true.mp hvalid c hc
      simp only [Bool.and_eq_true, decide_eq_true_eq] at this
      exact this.1
    have hne : ∀ c ∈ φ, c ≠ [] := fun c hc => by
      have := List.all_eq_true.mp hvalid c hc
      simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff] at this
      exact this.2
    let vars := φ.distinctVars
    let n := vars.length
    let N := 2 * (n + 2)
    have hof : ofThreeSAT φ = ⟨N,
        ([mkBits N (fun _ => false), mkBits N (fun _ => true)] ++
          ((List.range (n + 2)).flatMap fun k =>
            [mkBits N (fun j => decide (j / 2 = k)),
             mkBits N (fun j => !(decide (j / 2 = k)))]) ++
          [mkBits N (fun j => decide (j = 2 * n + 1)),
           mkBits N (fun j => decide (j = 2 * (n + 1) + 1))]) ++
        (φ.filter fun c => !isTautClause c).map (clauseCodeword vars), n + 1⟩ := by
      simp [ofThreeSAT, hvalid, vars, n, N]
    have hWF : (ofThreeSAT φ).WellFormed := by
      rw [hof]
      intro w hw
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
        List.mem_flatMap, List.mem_range, List.mem_map, List.mem_filter] at hw
      rcases hw with (((rfl | rfl) | ⟨k, _, rfl | rfl⟩) | (rfl | rfl)) | ⟨c, _, rfl⟩
      all_goals simp [length_mkBits, clauseCodeword, N, n]
    rw [hof] at hWF ⊢
    -- Now prove both directions of `ofThreeSAT_mem_iff`.
    constructor
    · rintro ⟨_, v, hv, hdist⟩
      dsimp only at hv hdist
      -- Extract consistency `w_i = 1` for all `i < n + 2`.
      have hwt : (List.range N).countP (fun j => v.getD j false) = n + 2 := by
        have h0 := hdist (mkBits N (fun _ => false)) (by simp)
        have h1 := hdist (mkBits N (fun _ => true)) (by simp)
        have hcm : mkBits N (fun _ => true) = (mkBits N (fun _ => false)).map (!·) := by
          simp [mkBits]
        rw [hcm, hammingDist_map_not (by rw [hv, length_mkBits]), hv] at h1
        have hd0 : hammingDist v (mkBits N (fun _ => false)) =
            (List.range N).countP (fun j => v.getD j false) := by
          simp only [hammingDist, hv]
          refine List.countP_congr fun j hj => ?_
          rw [getD_mkBits _ (List.mem_range.mp hj)]
          cases v.getD j false <;> rfl
        rw [hd0] at h0 h1
        omega
      have hcons : ∀ k < n + 2,
          (if v.getD (2 * k) false then 1 else 0) +
          (if v.getD (2 * k + 1) false then 1 else 0) = 1 := by
        intro k hk
        have hpk := hdist (mkBits N (fun j => decide (j / 2 = k))) (by
          simp only [List.mem_append, List.mem_flatMap, List.mem_range, List.mem_cons]
          exact Or.inl (Or.inl (Or.inr ⟨k, hk, Or.inl rfl⟩)))
        have hpkc := hdist (mkBits N (fun j => !(decide (j / 2 = k)))) (by
          simp only [List.mem_append, List.mem_flatMap, List.mem_range, List.mem_cons]
          exact Or.inl (Or.inl (Or.inr ⟨k, hk, Or.inr (Or.inl rfl)⟩)))
        have hcm : mkBits N (fun j => !(decide (j / 2 = k))) =
            (mkBits N (fun j => decide (j / 2 = k))).map (!·) := by simp [mkBits]
        rw [hcm, hammingDist_map_not (by rw [hv, length_mkBits]), hv] at hpkc
        have hdk : hammingDist v (mkBits N (fun j => decide (j / 2 = k))) = n + 2 := by omega
        -- Relate `hdk` to `hwt` via pair sum!
        have hsum_k : hammingDist v (mkBits N (fun j => decide (j / 2 = k))) +
            2 * ((if v.getD (2 * k) false then 1 else 0) +
                 (if v.getD (2 * k + 1) false then 1 else 0)) =
            (List.range N).countP (fun j => v.getD j false) + 2 := by
          rw [hammingDist_eq_sum_pairs (m := n + 2) hv]
          have hwt_pairs : (List.range N).countP (fun j => v.getD j false) =
              ∑ i ∈ Finset.range (n + 2),
                ((if v.getD (2 * i) false then 1 else 0) +
                 (if v.getD (2 * i + 1) false then 1 else 0)) := by
            have := hammingDist_eq_sum_pairs (v := v) (c := mkBits N (fun _ => false)) (m :=
              n + 2) hv
            have h0 : hammingDist v (mkBits N (fun _ => false)) =
                (List.range N).countP (fun j => v.getD j false) := by
              simp only [hammingDist, hv]
              refine List.countP_congr fun j hj => ?_
              rw [getD_mkBits _ (List.mem_range.mp hj)]
              cases v.getD j false <;> rfl
            rw [← h0, this]
            refine Finset.sum_congr rfl fun i hi => ?_
            have hin : i < n + 2 := Finset.mem_range.mp hi
            rw [getD_mkBits _ (by omega), getD_mkBits _ (by omega)]
            cases v.getD (2 * i) false <;> cases v.getD (2 * i + 1) false <;> rfl
          rw [hwt_pairs]
          have hmem : k ∈ Finset.range (n + 2) := Finset.mem_range.mpr hk
          rw [← Finset.add_sum_erase _ _ hmem, ← Finset.add_sum_erase _ _ hmem]
          have hrest : ∑ i ∈ (Finset.range (n + 2)).erase k,
              ((if v.getD (2 * i) false != (mkBits N (fun j => decide (j / 2 =
                k))).getD (2 * i) false
                then 1 else 0) +
               (if v.getD (2 * i + 1) false !=
                  (mkBits N (fun j => decide (j / 2 = k))).getD (2 * i + 1) false
                then 1 else 0)) =
              ∑ i ∈ (Finset.range (n + 2)).erase k,
                ((if v.getD (2 * i) false then 1 else 0) +
                 (if v.getD (2 * i + 1) false then 1 else 0)) := by
            refine Finset.sum_congr rfl fun i hi => ?_
            have hik : i ≠ k := (Finset.mem_erase.mp hi).1
            have hin : i < n + 2 := Finset.mem_range.mp (Finset.mem_erase.mp hi).2
            rw [getD_mkBits _ (by omega), getD_mkBits _ (by omega)]
            have hd1 : (2 * i) / 2 = i := by omega
            have hd2 : (2 * i + 1) / 2 = i := by omega
            rw [hd1, hd2, decide_eq_false hik]
            cases v.getD (2 * i) false <;> cases v.getD (2 * i + 1) false <;> rfl
          rw [hrest, getD_mkBits _ (by omega), getD_mkBits _ (by omega)]
          have hd1 : (2 * k) / 2 = k := by omega
          have hd2 : (2 * k + 1) / 2 = k := by omega
          rw [hd1, hd2, decide_eq_true rfl]
          cases v.getD (2 * k) false <;> cases v.getD (2 * k + 1) false <;>
            simp only [Bool.false_bne, Bool.true_bne, Bool.not_true,
              ↓reduceIte, Bool.false_eq_true] <;> omega
        omega
      -- Extract boost values `v[2b] = true, v[2b+1] = false` for `b ∈ {n, n+1}`.
      have hboost : ∀ b, n ≤ b → b < n + 2 →
          v.getD (2 * b) false = true ∧ v.getD (2 * b + 1) false = false := by
        intro b hb1 hb2
        have hmem_b : mkBits N (fun j => decide (j = 2 * b + 1)) ∈
            ([mkBits N (fun _ => false), mkBits N (fun _ => true)] ++
              ((List.range (n + 2)).flatMap fun k =>
                [mkBits N (fun j => decide (j / 2 = k)),
                 mkBits N (fun j => !(decide (j / 2 = k)))]) ++
              [mkBits N (fun j => decide (j = 2 * n + 1)),
               mkBits N (fun j => decide (j = 2 * (n + 1) + 1))]) ++
            (φ.filter fun c => !isTautClause c).map (clauseCodeword vars) := by
          simp only [List.mem_append, List.mem_cons]
          have hb_eq : b = n ∨ b = n + 1 := by omega
          rcases hb_eq with rfl | rfl
          · exact Or.inl (Or.inr (Or.inl rfl))
          · exact Or.inl (Or.inr (Or.inr (Or.inl rfl)))
        have hdb := hdist _ hmem_b
        rw [hammingDist_eq_sum_pairs (m := n + 2) hv] at hdb
        have hbm : b ∈ Finset.range (n + 2) := Finset.mem_range.mpr hb2
        rw [← Finset.add_sum_erase _ _ hbm] at hdb
        have hrest : ∑ i ∈ (Finset.range (n + 2)).erase b,
            ((if v.getD (2 * i) false != (mkBits N (fun j => decide (j =
              2 * b + 1))).getD (2 * i) false
              then 1 else 0) +
             (if v.getD (2 * i + 1) false !=
                (mkBits N (fun j => decide (j = 2 * b + 1))).getD (2 * i + 1) false
              then 1 else 0)) = n + 1 := by
          have h1 : ∀ i ∈ (Finset.range (n + 2)).erase b,
              ((if v.getD (2 * i) false !=
                  (mkBits N (fun j => decide (j = 2 * b + 1))).getD (2 * i) false then 1 else 0) +
               (if v.getD (2 * i + 1) false !=
                  (mkBits N (fun j => decide (j =
                    2 * b + 1))).getD (2 * i + 1) false then 1 else 0)) = 1 := by
            intro i hi
            have hib : i ≠ b := (Finset.mem_erase.mp hi).1
            have hin : i < n + 2 := Finset.mem_range.mp (Finset.mem_erase.mp hi).2
            rw [getD_mkBits _ (by omega), getD_mkBits _ (by omega),
              decide_eq_false (by omega), decide_eq_false (by omega)]
            have hc := hcons i hin
            have h4 : ∀ a b : Bool,
                (if a then 1 else 0) + (if b then 1 else 0) = 1 →
                (if (a != false) then 1 else 0) + (if (b != false) then 1 else 0) = 1 := by decide
            exact h4 _ _ hc
          rw [Finset.sum_congr rfl h1, Finset.sum_const, Finset.card_erase_of_mem hbm,
            Finset.card_range]
          simp
        rw [hrest, getD_mkBits _ (by omega), getD_mkBits _ (by omega),
          decide_eq_false (by omega), decide_eq_true rfl] at hdb
        have hcb := hcons b hb2
        have h4 : ∀ a b : Bool,
            (if a then 1 else 0) + (if b then 1 else 0) = 1 →
            n + 1 < ((if (a != false) then 1 else 0) + (if (b != true) then 1 else 0)) + (n + 1) →
            a = true ∧ b = false := fun a b h1 h2 => by
          cases a <;> cases b <;> simp at h1 h2 ⊢
        exact h4 _ _ hcb hdb
      -- Build satisfying assignment `σ : ℕ → Bool`.
      refine ⟨hlen3, fun x => if h : x ∈ vars then v.getD (2 * vars.idxOf x) false else false, ?_⟩
      rw [CNF.eval_eq_true_iff]
      intro c hc
      by_cases ht : isTautClause c = true
      · rw [isTautClause, List.any_eq_true] at ht
        obtain ⟨l, hl, hl'⟩ := ht
        rw [Clause.eval_eq_true_iff]
        have hl'_mem := List.contains_iff_mem.mp hl'
        by_cases hval : (if h : l.1 ∈ vars then v.getD (2 * vars.idxOf l.1) false else false) = l.2
        · exact ⟨l, hl, hval⟩
        · refine ⟨(l.1, !l.2), hl'_mem, ?_⟩
          cases hlb : l.2 <;> simp_all
      · have hnt : isTautClause c = false := Bool.eq_false_iff.mpr ht
        have hmem_c : clauseCodeword vars c ∈
            ([mkBits N (fun _ => false), mkBits N (fun _ => true)] ++
              ((List.range (n + 2)).flatMap fun k =>
                [mkBits N (fun j => decide (j / 2 = k)),
                 mkBits N (fun j => !(decide (j / 2 = k)))]) ++
              [mkBits N (fun j => decide (j = 2 * n + 1)),
               mkBits N (fun j => decide (j = 2 * (n + 1) + 1))]) ++
            (φ.filter fun c => !isTautClause c).map (clauseCodeword vars) := by
          simp only [List.mem_append, List.mem_map, List.mem_filter, Bool.not_eq_true']
          exact Or.inr ⟨c, ⟨hc, hnt⟩, rfl⟩
        have hdc := hdist _ hmem_c
        rw [pair_dist_eq φ hlen3 hne v hv hcons hboost c hc hnt] at hdc
        have hpos : 0 < ((Finset.range n).filter fun i =>
            (c.dedup.contains (vars.getD i 0, true) && v.getD (2 * i) false) ||
            (c.dedup.contains (vars.getD i 0, false) && !v.getD (2 * i) false)).card := by
          dsimp only [vars, n] at hdc ⊢; omega
        obtain ⟨i, hi⟩ := Finset.card_pos.mp hpos
        obtain ⟨hin, hsat⟩ := Finset.mem_filter.mp hi
        have hi_lt : i < vars.length := Finset.mem_range.mp hin
        have hidx : vars.idxOf (vars.getD i 0) = i := by
          rw [getD_eq_getElem_of_lt hi_lt]
          exact List.Nodup.idxOf_getElem (CNF.nodup_distinctVars φ) i hi_lt
        have hmemv : vars.getD i 0 ∈ vars := by
          rw [getD_eq_getElem_of_lt hi_lt]; exact List.getElem_mem hi_lt
        rw [Clause.eval_eq_true_iff]
        simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at hsat
        rcases hsat with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact ⟨(vars.getD i 0, true), List.mem_dedup.mp (List.contains_iff_mem.mp h1), by
            rw [dite_eq_left hmemv, hidx]; exact h2⟩
        · exact ⟨(vars.getD i 0, false), List.mem_dedup.mp (List.contains_iff_mem.mp h1), by
            rw [dite_eq_left hmemv, hidx]; exact h2⟩
    · -- Forward direction: satisfying assignment `σ` yields `v`.
      rintro ⟨_, σ, hσ⟩
      let v : List Bool := mkBits N fun j =>
        let i := j / 2
        let isOdd := decide (j % 2 = 1)
        if i < n then
          if isOdd then !(σ (vars.getD i 0)) else σ (vars.getD i 0)
        else !isOdd
      have hv : v.length = N := length_mkBits N _
      have hcons : ∀ i < n + 2,
          (if v.getD (2 * i) false then 1 else 0) +
          (if v.getD (2 * i + 1) false then 1 else 0) = 1 := by
        intro i hi
        rw [getD_mkBits _ (by omega), getD_mkBits _ (by omega)]
        have hd1 : (2 * i) / 2 = i := by omega
        have hd2 : (2 * i + 1) / 2 = i := by omega
        have hm1 : (2 * i) % 2 = 0 := by omega
        have hm2 : (2 * i + 1) % 2 = 1 := by omega
        simp only [hd1, hd2, hm1, hm2]
        by_cases hin : i < n
        · simp only [hin, ↓reduceIte, decide_eq_false (by decide : (0 : ℕ) ≠ 1),
            Bool.false_eq_true]
          cases σ (vars.getD i 0) <;> rfl
        · simp only [hin, ↓reduceIte, decide_eq_false (by decide : (0 : ℕ) ≠ 1),
            Bool.not_false]
          rfl
      have hboost : ∀ b, n ≤ b → b < n + 2 →
          v.getD (2 * b) false = true ∧ v.getD (2 * b + 1) false = false := by
        intro b hb1 hb2
        rw [getD_mkBits _ (by omega), getD_mkBits _ (by omega)]
        have hd1 : (2 * b) / 2 = b := by omega
        have hd2 : (2 * b + 1) / 2 = b := by omega
        have hm1 : (2 * b) % 2 = 0 := by omega
        have hm2 : (2 * b + 1) % 2 = 1 := by omega
        have hnb : ¬(b < n) := by omega
        simp [hd1, hd2, hm1, hm2, hnb]
      have hpair_eq : ∀ a b d : Bool,
          (if a then 1 else 0) + (if b then 1 else 0) = 1 →
          (if (a != d) then 1 else 0) + (if (b != d) then 1 else 0) = 1 := by decide
      refine ⟨hWF, v, hv, fun w hw => ?_⟩
      dsimp only at hw ⊢
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
        List.mem_flatMap, List.mem_range, List.mem_map, List.mem_filter, Bool.not_eq_true'] at hw
      rcases hw with (((rfl | rfl) | ⟨k, hk, rfl | rfl⟩) | (rfl | rfl)) | ⟨c, ⟨hc, hnt⟩, rfl⟩
      · -- `allFalse`: distance is `n + 2`.
        rw [hammingDist_eq_sum_pairs (m := n + 2) hv]
        have h1 : ∀ i ∈ Finset.range (n + 2),
            ((if v.getD (2 * i) false !=
                (mkBits N (fun _ => false)).getD (2 * i) false then 1 else 0) +
             (if v.getD (2 * i + 1) false !=
                (mkBits N (fun _ => false)).getD (2 * i + 1) false then 1 else 0)) = 1 := by
          intro i hi; have hin := Finset.mem_range.mp hi
          rw [getD_mkBits (f := fun _ => false) (by omega),
            getD_mkBits (f := fun _ => false) (by omega)]
          exact hpair_eq _ _ _ (hcons i hin)
        rw [Finset.sum_congr rfl h1]; simp
      · -- `allTrue`: distance is `n + 2`.
        rw [hammingDist_eq_sum_pairs (m := n + 2) hv]
        have h1 : ∀ i ∈ Finset.range (n + 2),
            ((if v.getD (2 * i) false !=
                (mkBits N (fun _ => true)).getD (2 * i) false then 1 else 0) +
             (if v.getD (2 * i + 1) false !=
                (mkBits N (fun _ => true)).getD (2 * i + 1) false then 1 else 0)) = 1 := by
          intro i hi; have hin := Finset.mem_range.mp hi
          rw [getD_mkBits (f := fun _ => true) (by omega),
            getD_mkBits (f := fun _ => true) (by omega)]
          exact hpair_eq _ _ _ (hcons i hin)
        rw [Finset.sum_congr rfl h1]; simp
      · -- `pairWord k`: distance is `n + 2`.
        rw [hammingDist_eq_sum_pairs (m := n + 2) hv]
        have h1 : ∀ i ∈ Finset.range (n + 2),
            ((if v.getD (2 * i) false != (mkBits N (fun j => decide (j / 2 =
              k))).getD (2 * i) false then 1 else 0) +
             (if v.getD (2 * i + 1) false != (mkBits N (fun j => decide (j / 2 =
               k))).getD (2 * i + 1) false then 1 else 0)) = 1 := by
          intro i hi; have hin := Finset.mem_range.mp hi
          rw [getD_mkBits (f := fun j => decide (j / 2 = k)) (by omega),
            getD_mkBits (f := fun j => decide (j / 2 = k)) (by omega)]
          have hd1 : (2 * i) / 2 = i := by omega
          have hd2 : (2 * i + 1) / 2 = i := by omega
          rw [hd1, hd2]
          exact hpair_eq _ _ _ (hcons i hin)
        rw [Finset.sum_congr rfl h1]; simp
      · -- `pairWordCompl k`: distance is `n + 2`.
        rw [hammingDist_eq_sum_pairs (m := n + 2) hv]
        have h1 : ∀ i ∈ Finset.range (n + 2),
            ((if v.getD (2 * i) false != (mkBits N (fun j => !(decide (j / 2 =
              k)))).getD (2 * i) false then 1 else 0) +
             (if v.getD (2 * i + 1) false != (mkBits N (fun j => !(decide (j / 2 =
               k)))).getD (2 * i + 1) false then 1 else 0)) = 1 := by
          intro i hi; have hin := Finset.mem_range.mp hi
          rw [getD_mkBits (f := fun j => !(decide (j / 2 = k))) (by omega),
            getD_mkBits (f := fun j => !(decide (j / 2 = k))) (by omega)]
          have hd1 : (2 * i) / 2 = i := by omega
          have hd2 : (2 * i + 1) / 2 = i := by omega
          rw [hd1, hd2]
          exact hpair_eq _ _ _ (hcons i hin)
        rw [Finset.sum_congr rfl h1]; simp
      · -- `boostWord n`: distance is `n + 3`.
        rw [hammingDist_eq_sum_pairs (m := n + 2) hv]
        have hbm : n ∈ Finset.range (n + 2) := Finset.mem_range.mpr (by omega)
        rw [← Finset.add_sum_erase _ _ hbm]
        have h1 : ∀ i ∈ (Finset.range (n + 2)).erase n,
            ((if v.getD (2 * i) false != (mkBits N (fun j => decide (j =
              2 * n + 1))).getD (2 * i) false then 1 else 0) +
             (if v.getD (2 * i + 1) false != (mkBits N (fun j => decide (j =
               2 * n + 1))).getD (2 * i + 1) false then 1 else 0)) = 1 := by
          intro i hi; have hin := Finset.mem_range.mp (Finset.mem_erase.mp hi).2
          have hne' := (Finset.mem_erase.mp hi).1
          rw [getD_mkBits (f := fun j => decide (j = 2 * n + 1)) (by omega),
            getD_mkBits (f := fun j => decide (j = 2 * n + 1)) (by omega),
            decide_eq_false (by omega), decide_eq_false (by omega)]
          exact hpair_eq _ _ _ (hcons i hin)
        rw [Finset.sum_congr rfl h1, Finset.sum_const, Finset.card_erase_of_mem hbm,
          Finset.card_range,
          getD_mkBits (f := fun j => decide (j = 2 * n + 1)) (by omega),
          getD_mkBits (f := fun j => decide (j = 2 * n + 1)) (by omega),
          decide_eq_false (by omega), decide_eq_true rfl]
        obtain ⟨h0, h1'⟩ := hboost n le_rfl (by omega)
        rw [h0, h1']; simp only [Bool.true_bne, Bool.false_bne, ↓reduceIte, smul_eq_mul, mul_one]
        omega
      · -- `boostWord (n + 1)`: distance is `n + 3`.
        rw [hammingDist_eq_sum_pairs (m := n + 2) hv]
        have hbm : n + 1 ∈ Finset.range (n + 2) := Finset.mem_range.mpr (by omega)
        rw [← Finset.add_sum_erase _ _ hbm]
        have h1 : ∀ i ∈ (Finset.range (n + 2)).erase (n + 1),
            ((if v.getD (2 * i) false != (mkBits N (fun j => decide (j =
              2 * (n + 1) + 1))).getD (2 * i) false then 1 else 0) +
             (if v.getD (2 * i + 1) false != (mkBits N (fun j => decide (j =
               2 * (n + 1) + 1))).getD (2 * i + 1) false then 1 else 0)) = 1 := by
          intro i hi; have hin := Finset.mem_range.mp (Finset.mem_erase.mp hi).2
          have hne' := (Finset.mem_erase.mp hi).1
          rw [getD_mkBits (f := fun j => decide (j = 2 * (n + 1) + 1)) (by omega),
            getD_mkBits (f := fun j => decide (j = 2 * (n + 1) + 1)) (by omega),
            decide_eq_false (by omega), decide_eq_false (by omega)]
          exact hpair_eq _ _ _ (hcons i hin)
        rw [Finset.sum_congr rfl h1, Finset.sum_const, Finset.card_erase_of_mem hbm,
          Finset.card_range,
          getD_mkBits (f := fun j => decide (j = 2 * (n + 1) + 1)) (by omega),
          getD_mkBits (f := fun j => decide (j = 2 * (n + 1) + 1)) (by omega),
          decide_eq_false (by omega), decide_eq_true rfl]
        obtain ⟨h0, h1'⟩ := hboost (n + 1) (by omega) (by omega)
        rw [h0, h1']; simp only [Bool.true_bne, Bool.false_bne, ↓reduceIte, smul_eq_mul, mul_one]
        omega
      · -- `clauseCodeword vars c`: distance is `n + 1 + 2 * satCount.card ≥ n + 3`.
        rw [pair_dist_eq φ hlen3 hne v hv hcons hboost c hc hnt]
        obtain ⟨l, hl, hσl⟩ :=
          (Clause.eval_eq_true_iff _ _).mp ((CNF.eval_eq_true_iff _ _).mp hσ c hc)
        have hlv : l.1 ∈ vars :=
          CNF.mem_distinctVars.mpr (by
            rw [CNF.vars, List.mem_map]
            exact ⟨l, List.mem_flatten.mpr ⟨c, hc, hl⟩, rfl⟩)
        obtain ⟨i, hi, hget⟩ := List.getElem_of_mem hlv
        have hpos : 0 < ((Finset.range n).filter fun i =>
            (c.dedup.contains (vars.getD i 0, true) && v.getD (2 * i) false) ||
            (c.dedup.contains (vars.getD i 0, false) && !v.getD (2 * i) false)).card := by
          refine Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi, ?_⟩⟩
          have hv2i : v.getD (2 * i) false = σ l.1 := by
            rw [getD_mkBits _ (by omega)]
            have hd : (2 * i) / 2 = i := by omega
            have hm : (2 * i) % 2 = 0 := by omega
            simp [n, hd, hm, hi, hget]
          rw [hv2i, getD_eq_getElem_of_lt hi, hget]
          have hlt : (l.1, l.2) ∈ c := hl
          cases hlb : l.2
          · rw [hlb] at hσl hlt; simp [hσl, hlt]
          · rw [hlb] at hσl hlt; simp [hσl, hlt]
        exact Nat.lt_add_of_pos_right (Nat.mul_pos (by decide) hpos)
  · -- Malformed or empty-clause input maps to `noInstance`.
    have hof : ofThreeSAT φ = noInstance := by simp [ofThreeSAT, hvalid]
    rw [hof]
    refine ⟨fun h => (noInstance_not_mem h).elim, fun ⟨h3, σ, hσ⟩ => ?_⟩
    exfalso
    apply hvalid
    rw [List.all_eq_true]
    intro c hc
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', List.isEmpty_eq_false_iff]
    refine ⟨h3 c hc, fun hemp => ?_⟩
    have hsat := (CNF.eval_eq_true_iff _ _).mp hσ c hc
    simp [hemp, Clause.eval] at hsat

/-- `CoveringRadius` is `NP`-hard. -/
theorem npHard : NPHard encCoveringRadius CoveringRadius :=
  ThreeSAT_npHard.trans ⟨ofThreeSAT, computableInPolyTime_ofThreeSAT,
    fun φ => (ofThreeSAT_mem_iff φ).symm⟩

/-- **Explicit binary `CoveringRadius` is `NP`-complete.** -/
theorem npComplete : NPComplete encCoveringRadius CoveringRadius :=
  ⟨mem_NP, npHard⟩

end CoveringRadius

end Cslib.Complexity
