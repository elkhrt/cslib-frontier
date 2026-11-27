/-
Copyright (c) 2026 The CslibFrontier contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The CslibFrontier contributors
-/
module

public import Mathlib.Computability.Halting
public import CslibFrontier.Computability.Diophantine.Matiyasevich

import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring

/-!
# Undecidability of Quartic Diophantine Equations, Quadratic Systems, and the Degree Threshold

Combines the Matiyasevich–Robinson–Davis–Putnam theorem and universal quartic Diophantine equations
(`CslibFrontier.Computability.Diophantine.Matiyasevich`) with Skolem degree reduction
(`CslibFrontier.Computability.Diophantine.DegreeReduction`) to prove, under standard Lean axioms,
  that:

1. Single Diophantine equations of total degree `0` are computably decidable over `ℕ` and over `ℤ`,
   whereas single Diophantine equations of total degree at most `k` are undecidable for every
   `k ≥ 4` over both `ℕ` and `ℤ`.
2. Finite systems of Diophantine equations of total degree at most `k` are undecidable for every
   `k ≥ 2` (in particular quadratic systems at `k = 2` and cubic systems at `k = 3`) over both `ℕ`
   and `ℤ`.
3. Over both `ℕ` and `ℤ`, there exists a unique classical degree threshold `k ∈ {1, 2, 3, 4}` such
   that single-equation solvability is decidable for every degree `m < k` and undecidable for every
   degree `m ≥ k`.

## Main definitions

* `CslibFrontier.Computability.Diophantine.IntPoly`: concrete, `Primcodable` syntax for multivariate
  polynomials over
  `ℤ` with primitive recursive `totalDegree`, `evalInt`, `evalNat`, and `substVar0`.
* `CslibFrontier.Computability.Diophantine.IntPoly.toMvPoly` and
  `CslibFrontier.Computability.Diophantine.IntPoly.ofMvPoly`: semantic
  translation between `IntPoly` and canonical `MvPolynomial` carriers.
* `CslibFrontier.Computability.Diophantine.IntPoly.HasNatRoot` and
  `CslibFrontier.Computability.Diophantine.IntPoly.HasIntRoot`:
  natural-number and integer solvability of encoded integer polynomials.
* `CslibFrontier.Computability.Diophantine.IsDecidableDegreeNat` and
  `CslibFrontier.Computability.Diophantine.IsDecidableDegreeInt`:
  algorithmic decidability of single Diophantine equations of total degree at most `k` over `ℕ` and
  over `ℤ`.
* `CslibFrontier.Computability.Diophantine.IsDecidableSystemDegreeNat` and
  `CslibFrontier.Computability.Diophantine.IsDecidableSystemDegreeInt`: algorithmic decidability of
  finite systems of
  Diophantine equations of total degree at most `k` over `ℕ` and over `ℤ`.

## Main results

* `CslibFrontier.Computability.Diophantine.IntPoly.primrec_totalDegree`,
  `CslibFrontier.Computability.Diophantine.IntPoly.primrec_evalInt`,
  `CslibFrontier.Computability.Diophantine.IntPoly.primrec_evalNat`,
  `CslibFrontier.Computability.Diophantine.IntPoly.primrec_substVar0`, and
  `CslibFrontier.Computability.Diophantine.IntPoly.rePred_hasNatRoot`: effectiveness of polynomial
  syntax and
  recursive enumerability of natural-number solvability.
* `CslibFrontier.Computability.Diophantine.isDecidableDegreeNat_zero` and
  `CslibFrontier.Computability.Diophantine.isDecidableDegreeInt_zero`: decidability at total degree
  `0`.
* `CslibFrontier.Computability.Diophantine.not_isDecidableDegreeNat_of_four_le` and
  `CslibFrontier.Computability.Diophantine.not_isDecidableDegreeInt_of_four_le`: undecidability of
  single Diophantine
  equations of total degree at most `k` (`k ≥ 4`) over `ℕ` and over `ℤ`.
* `CslibFrontier.Computability.Diophantine.not_isDecidableSystemDegreeNat_of_two_le` and
  `CslibFrontier.Computability.Diophantine.not_isDecidableSystemDegreeInt_of_two_le`: undecidability
  of finite
  Diophantine systems of total degree at most `k` (`k ≥ 2`, including quadratic and cubic systems)
  over `ℕ` and over `ℤ`.
* `CslibFrontier.Computability.Diophantine.existsUnique_undecidable_degree_threshold_nat` and
  `CslibFrontier.Computability.Diophantine.existsUnique_undecidable_degree_threshold_int`: existence
  and uniqueness of
  the classical single-equation degree threshold `k ∈ {1, 2, 3, 4}` over `ℕ` and over `ℤ`.

## Tags

Hilbert's tenth problem, undecidability, quartic equations, cubic Diophantine systems, Skolem
-/

public section

namespace CslibFrontier.Computability.Diophantine

open MvPolynomial Dioph

/-! ### Computably encoded multivariate integer polynomials -/

/-- Explicit finite syntax for multivariate polynomials over `ℤ` in variables `x_0, x_1, ...`,
stored as a list of `(coefficient, variable-index list)` monomials so that evaluation, syntactic
total degree, specialization of constants, and Gödel encoding are primitive recursive. -/
public abbrev IntPoly : Type := List (ℤ × List ℕ)

/-- Total degree of an encoded polynomial `P : IntPoly` (maximum monomial factor-list length,
ignoring zero-coefficient terms). -/
public def IntPoly.totalDegree (P : IntPoly) : ℕ :=
  P.foldl (fun acc term ↦ if term.1 = 0 then acc else max acc term.2.length) 0

/-- Evaluates an encoded polynomial `P : IntPoly` at an integer assignment `x : List ℤ`
(with out-of-range variables defaulting to `0`). -/
public def IntPoly.evalInt (P : IntPoly) (x : List ℤ) : ℤ :=
  (P.map fun term ↦ term.1 * (term.2.map fun i ↦ x.getD i 0).prod).sum

/-- Evaluates an encoded polynomial `P : IntPoly` at a natural-number assignment `x : List ℕ`. -/
public def IntPoly.evalNat (P : IntPoly) (x : List ℕ) : ℤ :=
  P.evalInt (x.map Int.ofNat)

/-- Converts `P : IntPoly` into the canonical `MvPolynomial ℕ ℤ`. -/
public noncomputable def IntPoly.toMvPoly (P : IntPoly) : MvPolynomial ℕ ℤ :=
  (P.map fun term ↦ C term.1 * (term.2.map X).prod).sum

/-- The empty polynomial list has syntactic total degree `0`. -/
@[simp]
public theorem IntPoly.totalDegree_nil : IntPoly.totalDegree [] = 0 := by rfl

/-- Evaluating the empty polynomial list at any `x : List ℤ` yields `0`. -/
@[simp]
public theorem IntPoly.evalInt_nil (x : List ℤ) : IntPoly.evalInt [] x = 0 := by rfl

/-- Evaluating the empty polynomial list at any `x : List ℕ` yields `0`. -/
@[simp]
public theorem IntPoly.evalNat_nil (x : List ℕ) : IntPoly.evalNat [] x = 0 := by rfl

/-- The empty polynomial list converts to `0 : MvPolynomial ℕ ℤ`. -/
@[simp]
public theorem IntPoly.toMvPoly_nil : IntPoly.toMvPoly [] = 0 := by rfl

/-- Evaluates `P.toMvPoly` explicitly as the sum of monomial products along `P`. -/
public theorem IntPoly.eval_toMvPoly (P : IntPoly) (x : ℕ → ℤ) :
    eval x P.toMvPoly = (P.map fun term ↦ term.1 * (term.2.map x).prod).sum := by
  induction P with
  | nil => simp
  | cons t ts ih =>
    rw [IntPoly.toMvPoly, List.map_cons, List.sum_cons, map_add, map_mul, eval_C]
    change _ + eval x (IntPoly.toMvPoly ts) = _
    rw [ih, List.map_cons, List.sum_cons]
    congr 2
    induction t.2 with
    | nil => simp
    | cons i is ih2 => simp [ih2]

/-- The canonical `MvPolynomial.totalDegree` of `P.toMvPoly` is bounded by `P.totalDegree`. -/
public theorem IntPoly.totalDegree_toMvPoly_le (P : IntPoly) :
    P.toMvPoly.totalDegree ≤ P.totalDegree := by
  have hfold : ∀ (ts : IntPoly) (acc : ℕ),
      acc ≤ ts.foldl (fun a t ↦ if t.1 = 0 then a else max a t.2.length) acc ∧
      ∀ t ∈ ts, t.1 ≠ 0 → t.2.length ≤
        ts.foldl (fun a t ↦ if t.1 = 0 then a else max a t.2.length) acc := by
    intro ts
    induction ts with
    | nil => intro acc; exact ⟨le_rfl, fun _ h ↦ absurd h List.not_mem_nil⟩
    | cons t ts ih =>
      intro acc
      set acc' := if t.1 = 0 then acc else max acc t.2.length
      obtain ⟨h1, h2⟩ := ih acc'
      refine ⟨le_trans ?_ h1, ?_⟩
      · dsimp [acc']; split_ifs <;> omega
      · intro s hs hne
        rcases List.mem_cons.mp hs with rfl | hs
        · refine le_trans ?_ h1
          simp [acc', hne]
        · exact h2 s hs hne
  obtain ⟨_, hmem⟩ := hfold P 0
  have hsum : ∀ ts : IntPoly,
      (∀ t ∈ ts, t.1 ≠ 0 → t.2.length ≤ P.totalDegree) →
      ts.toMvPoly.totalDegree ≤ P.totalDegree := by
    intro ts
    induction ts with
    | nil => intro _; simp [IntPoly.toMvPoly]
    | cons t ts ih =>
      intro ht
      simp only [IntPoly.toMvPoly, List.map_cons, List.sum_cons]
      refine (totalDegree_add _ _).trans (max_le ?_
        (ih fun s hs ↦ ht s (List.mem_cons_of_mem t hs)))
      by_cases h0 : t.1 = 0
      · simp [h0]
      · refine (totalDegree_mul _ _).trans ?_
        rw [totalDegree_C, zero_add]
        refine le_trans ?_ (ht t List.mem_cons_self h0)
        clear ht ih h0
        induction t.2 with
        | nil => simp
        | cons i is ih2 =>
          simp only [List.map_cons, List.prod_cons, List.length_cons]
          refine (totalDegree_mul _ _).trans ?_
          rw [totalDegree_X]
          omega
  exact hsum P hmem

/-- `P : IntPoly` has a natural-number root (`∃ x : ℕ → ℕ, eval (x · : ℤ) P.toMvPoly = 0`). -/
public def IntPoly.HasNatRoot (P : IntPoly) : Prop :=
  ∃ x : ℕ → ℕ, eval (fun i ↦ (x i : ℤ)) P.toMvPoly = 0

/-- `P : IntPoly` has an integer root (`∃ x : ℕ → ℤ, eval x P.toMvPoly = 0`). -/
public def IntPoly.HasIntRoot (P : IntPoly) : Prop :=
  ∃ x : ℕ → ℤ, eval x P.toMvPoly = 0

private def IntPoly.maxVarPlusOne (P : IntPoly) : ℕ :=
  (P.map fun t ↦ (t.2.map Nat.succ).foldr max 0).foldr max 0

private theorem IntPoly.lt_maxVarPlusOne {P : IntPoly} {t : ℤ × List ℕ} (ht : t ∈ P)
    {i : ℕ} (hi : i ∈ t.2) : i < P.maxVarPlusOne := by
  have h1 : ∀ (l : List ℕ) (a : ℕ), a ∈ l → a ≤ l.foldr max 0 := by
    intro l a
    induction l with
    | nil => intro h; cases h
    | cons b bs ih =>
      intro h
      rcases List.mem_cons.mp h with rfl | h
      · exact le_max_left _ _
      · exact (ih h).trans (le_max_right _ _)
  have hi1 : i + 1 ≤ (t.2.map Nat.succ).foldr max 0 :=
    h1 _ _ (List.mem_map_of_mem (f := Nat.succ) hi)
  have ht1 : (t.2.map Nat.succ).foldr max 0 ≤ P.maxVarPlusOne :=
    h1 _ _ (List.mem_map_of_mem ht)
  omega

/-- `P.HasNatRoot` holds iff `P.evalNat l = 0` for some finite assignment `l : List ℕ`. -/
public theorem IntPoly.hasNatRoot_iff_exists_list (P : IntPoly) :
    P.HasNatRoot ↔ ∃ l : List ℕ, P.evalNat l = 0 := by
  constructor
  · rintro ⟨x, hx⟩
    let N := P.maxVarPlusOne
    refine ⟨List.ofFn fun i : Fin N ↦ x i.1, ?_⟩
    rw [IntPoly.evalNat, IntPoly.evalInt]
    rw [IntPoly.eval_toMvPoly] at hx
    rw [← hx]
    congr 1
    refine List.map_congr_left fun t ht ↦ ?_
    congr 2
    refine List.map_congr_left fun i hi ↦ ?_
    have hiN : i < N := P.lt_maxVarPlusOne ht hi
    simp [List.getD, hiN]
  · rintro ⟨l, hl⟩
    refine ⟨fun i ↦ l.getD i 0, ?_⟩
    rw [IntPoly.eval_toMvPoly]
    rw [IntPoly.evalNat, IntPoly.evalInt] at hl
    rw [← hl]
    congr 1
    refine List.map_congr_left fun t _ ↦ ?_
    congr 2
    refine List.map_congr_left fun i _ ↦ ?_
    by_cases hi : i < l.length <;> simp [List.getD, hi]

/-- `P.HasIntRoot` holds iff `P.evalInt l = 0` for some finite assignment `l : List ℤ`. -/
public theorem IntPoly.hasIntRoot_iff_exists_list (P : IntPoly) :
    P.HasIntRoot ↔ ∃ l : List ℤ, P.evalInt l = 0 := by
  constructor
  · rintro ⟨x, hx⟩
    let N := P.maxVarPlusOne
    refine ⟨List.ofFn fun i : Fin N ↦ x i.1, ?_⟩
    rw [IntPoly.evalInt]
    rw [IntPoly.eval_toMvPoly] at hx
    rw [← hx]
    congr 1
    refine List.map_congr_left fun t ht ↦ ?_
    congr 2
    refine List.map_congr_left fun i hi ↦ ?_
    have hiN : i < N := P.lt_maxVarPlusOne ht hi
    simp [List.getD, hiN]
  · rintro ⟨l, hl⟩
    exact ⟨fun i ↦ l.getD i 0, by rwa [IntPoly.eval_toMvPoly]⟩

/-- Encodes any `p : MvPolynomial (Fin n) ℤ` into an `IntPoly` preserving total degree and
evaluations over both `ℕ` and `ℤ`. -/
public noncomputable def IntPoly.ofMvPoly {n : ℕ} (p : MvPolynomial (Fin n) ℤ) : IntPoly := by
  classical
  exact p.support.toList.map fun s ↦
    (p.coeff s, (monomialToVarList s).map Fin.val)

/-- `(IntPoly.ofMvPoly p).totalDegree ≤ p.totalDegree`. -/
public theorem IntPoly.totalDegree_ofMvPoly_le {n : ℕ} (p : MvPolynomial (Fin n) ℤ) :
    (IntPoly.ofMvPoly p).totalDegree ≤ p.totalDegree := by
  classical
  have hfold : ∀ (ts : IntPoly) (acc : ℕ), acc ≤ p.totalDegree →
      (∀ t ∈ ts, t.2.length ≤ p.totalDegree) →
      ts.foldl (fun a t ↦ if t.1 = 0 then a else max a t.2.length) acc ≤ p.totalDegree := by
    intro ts
    induction ts with
    | nil => intro acc hacc _; exact hacc
    | cons t ts ih =>
      intro acc hacc ht
      refine ih _ ?_ fun s hs ↦ ht s (List.mem_cons_of_mem t hs)
      dsimp only
      split_ifs
      · exact hacc
      · exact max_le hacc (ht t List.mem_cons_self)
  refine hfold _ 0 (Nat.zero_le _) fun t ht ↦ ?_
  rcases List.mem_map.mp ht with ⟨s, hs, rfl⟩
  rw [List.length_map, length_monomialToVarList]
  exact le_totalDegree (Finset.mem_toList.mp hs)

/-- Evaluating `(IntPoly.ofMvPoly p).toMvPoly` at `x : ℕ → ℤ` agrees with
`eval (fun i : Fin n ↦ x i) p`. -/
public theorem IntPoly.eval_toMvPoly_ofMvPoly {n : ℕ} (p : MvPolynomial (Fin n) ℤ)
    (x : ℕ → ℤ) :
    eval x (IntPoly.ofMvPoly p).toMvPoly = eval (fun i : Fin n ↦ x i.1) p := by
  classical
  rw [IntPoly.eval_toMvPoly, IntPoly.ofMvPoly, List.map_map]
  have hfun : ((fun term : ℤ × List ℕ ↦ term.1 * (term.2.map x).prod) ∘
      fun s : Fin n →₀ ℕ ↦ (p.coeff s, (monomialToVarList s).map Fin.val)) =
      fun s ↦ eval (fun i : Fin n ↦ x i.1) (monomial s (p.coeff s)) := by
    ext s
    dsimp only [Function.comp_apply]
    rw [List.map_map, eval_monomial, ← prod_map_monomialToVarList]
    rfl
  rw [hfun, Finset.sum_map_toList]
  conv_rhs => rw [p.as_sum, map_sum]

/-- `(IntPoly.ofMvPoly p).HasNatRoot` holds iff `p` has a natural-number root. -/
public theorem IntPoly.hasNatRoot_ofMvPoly_iff {n : ℕ} (p : MvPolynomial (Fin n) ℤ) :
    (IntPoly.ofMvPoly p).HasNatRoot ↔ ∃ x : Fin n → ℕ, eval (fun i ↦ (x i : ℤ)) p = 0 := by
  constructor
  · rintro ⟨x, hx⟩
    rw [IntPoly.eval_toMvPoly_ofMvPoly] at hx
    exact ⟨fun i ↦ x i.1, hx⟩
  · rintro ⟨x, hx⟩
    refine ⟨fun k ↦ if hk : k < n then x ⟨k, hk⟩ else 0, ?_⟩
    rw [IntPoly.eval_toMvPoly_ofMvPoly]
    exact (congrArg (fun g ↦ eval g p) (funext fun i ↦ by simp [i.2])).trans hx

/-- `(IntPoly.ofMvPoly p).HasIntRoot` holds iff `p` has an integer root. -/
public theorem IntPoly.hasIntRoot_ofMvPoly_iff {n : ℕ} (p : MvPolynomial (Fin n) ℤ) :
    (IntPoly.ofMvPoly p).HasIntRoot ↔ ∃ x : Fin n → ℤ, eval x p = 0 := by
  constructor
  · rintro ⟨x, hx⟩
    rw [IntPoly.eval_toMvPoly_ofMvPoly] at hx
    exact ⟨fun i ↦ x i.1, hx⟩
  · rintro ⟨x, hx⟩
    refine ⟨fun k ↦ if hk : k < n then x ⟨k, hk⟩ else 0, ?_⟩
    rw [IntPoly.eval_toMvPoly_ofMvPoly]
    exact (congrArg (fun g ↦ eval g p) (funext fun i ↦ by simp [i.2])).trans hx

/-- Computable specialization of variable `x_0` to an integer constant `a` inside `P : IntPoly`,
never increasing `IntPoly.totalDegree`. -/
public def IntPoly.substVar0 (P : IntPoly) (a : ℤ) : IntPoly :=
  P.map fun term ↦
    let c0 := term.2.count 0
    (term.1 * a ^ c0, term.2.filter (· ≠ 0))

/-- Specializing `x_0 := a` in the empty polynomial list yields `[]`. -/
@[simp]
public theorem IntPoly.substVar0_nil (a : ℤ) : IntPoly.substVar0 [] a = [] := by rfl

/-- Specializing `x_0 := a` never increases `IntPoly.totalDegree`. -/
public theorem IntPoly.totalDegree_substVar0_le (P : IntPoly) (a : ℤ) :
    (P.substVar0 a).totalDegree ≤ P.totalDegree := by
  have hmono : ∀ (ts : IntPoly) (acc₁ acc₂ : ℕ), acc₁ ≤ acc₂ →
      (ts.substVar0 a).foldl (fun acc t ↦ if t.1 = 0 then acc else max acc t.2.length) acc₁ ≤
      ts.foldl (fun acc t ↦ if t.1 = 0 then acc else max acc t.2.length) acc₂ := by
    intro ts
    induction ts with
    | nil => intro _ _ h; exact h
    | cons t ts ih =>
      intro acc₁ acc₂ hacc
      refine ih _ _ ?_
      by_cases ht0 : t.1 = 0
      · simp [ht0, hacc]
      · simp only [ht0, ↓reduceIte]
        split_ifs
        · exact hacc.trans (le_max_left _ _)
        · exact max_le (hacc.trans (le_max_left _ _))
            ((List.length_filter_le _ _).trans (le_max_right _ _))
  exact hmono P 0 0 le_rfl

private theorem list_prod_subst0 (vs : List ℕ) (a : ℤ) (x : ℕ → ℤ) (hx0 : x 0 = a) :
    a ^ vs.count 0 * ((vs.filter (· ≠ 0)).map x).prod = (vs.map x).prod := by
  induction vs with
  | nil => simp
  | cons v vs ih =>
    by_cases hv : v = 0
    · subst hv
      have hf0 : List.filter (· ≠ 0) (0 :: vs) = List.filter (· ≠ 0) vs := by simp
      rw [List.count_cons_self, hf0, List.map_cons, List.prod_cons, hx0, pow_succ', mul_assoc, ih]
    · have hfv : List.filter (· ≠ 0) (v :: vs) = v :: List.filter (· ≠ 0) vs := by simp [hv]
      have hcv : List.count 0 (v :: vs) = List.count 0 vs := List.count_cons_of_ne hv
      rw [hcv, hfv, List.map_cons, List.prod_cons, List.map_cons, List.prod_cons, ← ih]
      ring

/-- Evaluating `(P.substVar0 a).toMvPoly` at `x` equals evaluating `P.toMvPoly` at `x` updated
with `0 ↦ a`. -/
public theorem IntPoly.eval_toMvPoly_substVar0 (P : IntPoly) (a : ℤ) (x : ℕ → ℤ) :
    eval x (P.substVar0 a).toMvPoly =
      eval (fun i ↦ if i = 0 then a else x i) P.toMvPoly := by
  rw [IntPoly.eval_toMvPoly, IntPoly.eval_toMvPoly, IntPoly.substVar0, List.map_map]
  congr 1
  refine List.map_congr_left fun t _ ↦ ?_
  have hflt : (t.2.filter (· ≠ 0)).map x =
      (t.2.filter (· ≠ 0)).map fun i ↦ if i = 0 then a else x i := by
    refine List.map_congr_left fun i hi ↦ ?_
    have hi0 : i ≠ 0 := by simpa using (List.mem_filter.mp hi).2
    simp [hi0]
  dsimp only [Function.comp_apply]
  rw [hflt, mul_assoc, list_prod_subst0 t.2 a (fun i ↦ if i = 0 then a else x i) (by simp)]

/-- `(P.substVar0 (n : ℤ)).HasNatRoot` holds iff `P.toMvPoly` has a natural-number root with
`x 0 = n`. -/
public theorem IntPoly.hasNatRoot_substVar0_iff (P : IntPoly) (n : ℕ) :
    (P.substVar0 (n : ℤ)).HasNatRoot ↔
      ∃ x : ℕ → ℕ, x 0 = n ∧ eval (fun i ↦ (x i : ℤ)) P.toMvPoly = 0 := by
  constructor
  · rintro ⟨x, hx⟩
    rw [IntPoly.eval_toMvPoly_substVar0] at hx
    refine ⟨fun i ↦ if i = 0 then n else x i, by simp, ?_⟩
    exact (congrArg (fun g ↦ eval g P.toMvPoly)
      (funext fun i ↦ by dsimp only; split_ifs <;> rfl)).trans hx
  · rintro ⟨x, rfl, hx⟩
    refine ⟨x, ?_⟩
    rw [IntPoly.eval_toMvPoly_substVar0]
    refine (congrArg (fun g ↦ eval g P.toMvPoly) (funext fun i ↦ ?_)).trans hx
    split_ifs with h
    · subst h; rfl
    · rfl

/-- `(P.substVar0 (n : ℤ)).HasIntRoot` holds iff `P.toMvPoly` has an integer root with
`x 0 = n`. -/
public theorem IntPoly.hasIntRoot_substVar0_iff (P : IntPoly) (n : ℕ) :
    (P.substVar0 (n : ℤ)).HasIntRoot ↔
      ∃ x : ℕ → ℤ, x 0 = (n : ℤ) ∧ eval x P.toMvPoly = 0 := by
  constructor
  · rintro ⟨x, hx⟩
    rw [IntPoly.eval_toMvPoly_substVar0] at hx
    exact ⟨fun i ↦ if i = 0 then (n : ℤ) else x i, by simp, hx⟩
  · rintro ⟨x, hx0, hx⟩
    refine ⟨x, ?_⟩
    rw [IntPoly.eval_toMvPoly_substVar0]
    refine (congrArg (fun g ↦ eval g P.toMvPoly) (funext fun i ↦ ?_)).trans hx
    split_ifs with h
    · subst h; exact hx0.symm
    · rfl

/-- `IntPoly.substVar0 P (n : ℤ)` is primitive recursive in `n` for every fixed `P`. -/
public theorem IntPoly.primrec_substVar0 (P : IntPoly) :
    Primrec fun n : ℕ ↦ P.substVar0 (n : ℤ) := by
  have hpow : ∀ c : ℕ, Primrec fun n : ℕ ↦ (n : ℤ) ^ c := by
    intro c
    induction c with
    | zero => exact Primrec.const 1
    | succ c ih =>
      simpa [pow_succ] using primrec_int_mul.comp ih primrec_int_ofNat
  unfold IntPoly.substVar0
  induction P with
  | nil => exact Primrec.const []
  | cons t ts ih =>
    refine Primrec.list_cons.comp ?_ ih
    refine Primrec.pair ?_ (Primrec.const (t.2.filter (· ≠ 0)))
    exact primrec_int_mul.comp (Primrec.const t.1) (hpow (t.2.count 0))

/-- `IntPoly.totalDegree` is primitive recursive. -/
public theorem IntPoly.primrec_totalDegree : Primrec IntPoly.totalDegree := by
  have hstep : Primrec fun q : IntPoly × (ℕ × (ℤ × List ℕ)) ↦
      if q.2.2.1 = 0 then q.2.1 else max q.2.1 q.2.2.2.length :=
    Primrec.ite
      (Primrec.eq.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)) (Primrec.const (0 : ℤ)))
      (Primrec.fst.comp Primrec.snd)
      (Primrec.nat_max.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.list_length.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
  exact (Primrec.list_foldl (Primrec.id (α := IntPoly)) (Primrec.const (0 : ℕ))
    (Primrec.to₂ hstep)).of_eq fun _ ↦ rfl

private theorem primrec_list_int_sum : Primrec (fun l : List ℤ ↦ l.sum) :=
  (Primrec.list_foldl Primrec.id (Primrec.const (0 : ℤ))
    (Primrec.to₂ (primrec_int_add.comp
      (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)))).of_eq
    fun l ↦ l.sum_eq_foldl.symm

private theorem primrec_list_int_prod : Primrec (fun l : List ℤ ↦ l.prod) := by
  refine (Primrec.list_foldl Primrec.id (Primrec.const (1 : ℤ))
    (Primrec.to₂ (primrec_int_mul.comp
      (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)))).of_eq fun l ↦ ?_
  have : ∀ (xs : List ℤ) (a : ℤ), xs.foldl (· * ·) a = a * xs.prod := by
    intro xs
    induction xs with
    | nil => intro a; simp
    | cons x xs ih => intro a; simp [ih, mul_assoc]
  simpa using (this l 1)

/-- `IntPoly.evalInt` is primitive recursive. -/
public theorem IntPoly.primrec_evalInt : Primrec (Function.uncurry IntPoly.evalInt) := by
  have hget : Primrec fun p : List ℤ × ℕ ↦ p.1.getD p.2 0 :=
    (Primrec.option_casesOn (Primrec.list_getElem?.comp Primrec.fst Primrec.snd)
      (Primrec.const (0 : ℤ)) (Primrec.to₂ Primrec.snd)).of_eq fun p ↦ by
        rw [List.getD_eq_getElem?_getD]; cases p.1[p.2]? <;> rfl
  have hterm : Primrec fun q : (IntPoly × List ℤ) × (ℤ × List ℕ) ↦
      q.2.1 * (q.2.2.map fun i ↦ q.1.2.getD i 0).prod :=
    primrec_int_mul.comp
      (Primrec.fst.comp Primrec.snd)
      (primrec_list_int_prod.comp
        (Primrec.list_map (Primrec.snd.comp Primrec.snd)
          (Primrec.to₂ (hget.comp
            (Primrec.pair (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd)))))
  exact primrec_list_int_sum.comp (Primrec.list_map Primrec.fst (Primrec.to₂ hterm))

/-- `IntPoly.evalNat` is primitive recursive. -/
public theorem IntPoly.primrec_evalNat : Primrec (Function.uncurry IntPoly.evalNat) :=
  IntPoly.primrec_evalInt.comp
    (Primrec.pair Primrec.fst
      (Primrec.list_map Primrec.snd (Primrec.to₂ (primrec_int_ofNat.comp Primrec.snd))))

/-- `IntPoly.HasNatRoot` is recursively enumerable (`REPred`). -/
public theorem IntPoly.rePred_hasNatRoot : REPred IntPoly.HasNatRoot := by
  have htest : Primrec fun q : IntPoly × ℕ ↦
      decide (q.1.evalNat (Denumerable.ofNat (List ℕ) q.2) = 0) :=
    ((Primrec.eq.comp Primrec.id (Primrec.const (0 : ℤ))).decide).comp
      (IntPoly.primrec_evalNat.comp
        (Primrec.pair Primrec.fst ((Primrec.ofNat (List ℕ)).comp Primrec.snd)))
  have hdom : Partrec fun P : IntPoly ↦
      Nat.rfind fun k ↦ Part.some
        (decide (P.evalNat (Denumerable.ofNat (List ℕ) k) = 0)) :=
    Partrec.rfind (Partrec.some.comp htest.to_comp.partrec)
  have hfun : (fun P : IntPoly ↦ (Nat.rfind fun k ↦ Part.some
      (decide (P.evalNat (Denumerable.ofNat (List ℕ) k) = 0))).Dom) = IntPoly.HasNatRoot :=
    funext fun P ↦ propext (Nat.rfind_dom.trans (by
      rw [IntPoly.hasNatRoot_iff_exists_list]
      exact ⟨fun ⟨k, hk⟩ ↦ ⟨Denumerable.ofNat (List ℕ) k, by simpa using hk⟩,
        fun ⟨l, hl⟩ ↦ ⟨Encodable.encode l, by simpa [Denumerable.ofNat_encode] using hl⟩⟩))
  exact hfun ▸ hdom.dom_re

/-! ### Degree-bounded decidability, undecidability, and the unique degree threshold -/

/-- Algorithmic decidability of the class `𝒟_k` of single Diophantine equations of total degree
at most `k` over `ℕ`: there exists a total computable decision function `f : IntPoly → Bool`
that returns `true` on every `P` with `P.totalDegree ≤ k` iff `P.HasNatRoot`. -/
@[expose]
public def IsDecidableDegreeNat (k : ℕ) : Prop :=
  ∃ f : IntPoly → Bool, Computable f ∧
    ∀ P : IntPoly, P.totalDegree ≤ k → (f P = true ↔ P.HasNatRoot)

/-- Algorithmic decidability of the class `𝒟_k` of single Diophantine equations of total degree
at most `k` over `ℤ`. -/
@[expose]
public def IsDecidableDegreeInt (k : ℕ) : Prop :=
  ∃ f : IntPoly → Bool, Computable f ∧
    ∀ P : IntPoly, P.totalDegree ≤ k → (f P = true ↔ P.HasIntRoot)

/-- Algorithmic decidability of finite systems of Diophantine equations each of total degree at
most `k` over `ℕ`. -/
@[expose]
public def IsDecidableSystemDegreeNat (k : ℕ) : Prop :=
  ∃ f : List IntPoly → Bool, Computable f ∧
    ∀ S : List IntPoly, (∀ P ∈ S, P.totalDegree ≤ k) →
      (f S = true ↔ ∃ x : ℕ → ℕ, ∀ P ∈ S, eval (fun i ↦ (x i : ℤ)) P.toMvPoly = 0)

/-- Algorithmic decidability of finite systems of Diophantine equations each of total degree at
most `k` over `ℤ`. -/
@[expose]
public def IsDecidableSystemDegreeInt (k : ℕ) : Prop :=
  ∃ f : List IntPoly → Bool, Computable f ∧
    ∀ S : List IntPoly, (∀ P ∈ S, P.totalDegree ≤ k) →
      (f S = true ↔ ∃ x : ℕ → ℤ, ∀ P ∈ S, eval x P.toMvPoly = 0)

/-- Monotonicity: if `𝒟_m` is decidable over `ℕ` and `k ≤ m`, then `𝒟_k` is decidable over `ℕ`. -/
public theorem IsDecidableDegreeNat.anti {k m : ℕ} (hkm : k ≤ m)
    (hm : IsDecidableDegreeNat m) : IsDecidableDegreeNat k := by
  rcases hm with ⟨f, hf, hspec⟩
  exact ⟨f, hf, fun P hP ↦ hspec P (hP.trans hkm)⟩

/-- Monotonicity: if `𝒟_m` is decidable over `ℤ` and `k ≤ m`, then `𝒟_k` is decidable over `ℤ`. -/
public theorem IsDecidableDegreeInt.anti {k m : ℕ} (hkm : k ≤ m)
    (hm : IsDecidableDegreeInt m) : IsDecidableDegreeInt k := by
  rcases hm with ⟨f, hf, hspec⟩
  exact ⟨f, hf, fun P hP ↦ hspec P (hP.trans hkm)⟩

private theorem eval_toMvPoly_eq_evalInt_nil_of_deg_zero {P : IntPoly}
    (hP : P.totalDegree ≤ 0) (x : ℕ → ℤ) :
    eval x P.toMvPoly = P.evalInt [] := by
  have hfold : ∀ (ts : IntPoly) (acc : ℕ),
      ts.foldl (fun a t ↦ if t.1 = 0 then a else max a t.2.length) acc = 0 →
      ∀ t ∈ ts, t.1 ≠ 0 → t.2 = [] := by
    intro ts
    induction ts with
    | nil => intro _ _ _ h; cases h
    | cons t ts ih =>
      intro acc h0 s hs hne
      have hge : ∀ (us : IntPoly) (b : ℕ),
          b ≤ us.foldl (fun a t ↦ if t.1 = 0 then a else max a t.2.length) b := by
        intro us
        induction us with
        | nil => intro _; exact le_rfl
        | cons r rs ihr =>
          intro b
          refine le_trans ?_ (ihr _)
          dsimp only; split_ifs <;> omega
      rcases List.mem_cons.mp hs with rfl | hs
      · have hge0 := hge ts (if s.1 = 0 then acc else max acc s.2.length)
        simp only [List.foldl_cons, hne, ↓reduceIte] at h0 hge0
        exact List.eq_nil_of_length_eq_zero (by omega)
      · exact ih _ h0 s hs hne
  have hterms := hfold P 0 (Nat.eq_zero_of_le_zero hP)
  rw [IntPoly.eval_toMvPoly, IntPoly.evalInt]
  congr 1
  refine List.map_congr_left fun t ht ↦ ?_
  by_cases h0 : t.1 = 0
  · simp [h0]
  · rw [hterms t ht h0]
    simp

private theorem primrec_decide_evalInt_nil :
    Computable fun P : IntPoly ↦ decide (P.evalInt [] = 0) :=
  (((Primrec.eq.comp Primrec.id (Primrec.const (0 : ℤ))).decide).comp
    (IntPoly.primrec_evalInt.comp (Primrec.pair Primrec.id (Primrec.const [])))).to_comp

/-- Degree-`0` Diophantine equations over `ℕ` are computably decidable. -/
public theorem isDecidableDegreeNat_zero : IsDecidableDegreeNat 0 := by
  refine ⟨fun P ↦ decide (P.evalInt [] = 0), primrec_decide_evalInt_nil, fun P hP ↦ ?_⟩
  rw [decide_eq_true_iff]
  exact ⟨fun h0 ↦ ⟨fun _ ↦ 0, (eval_toMvPoly_eq_evalInt_nil_of_deg_zero hP _).trans h0⟩,
    fun ⟨_, hx⟩ ↦ (eval_toMvPoly_eq_evalInt_nil_of_deg_zero hP _).symm.trans hx⟩

/-- Degree-`0` Diophantine equations over `ℤ` are computably decidable. -/
public theorem isDecidableDegreeInt_zero : IsDecidableDegreeInt 0 := by
  refine ⟨fun P ↦ decide (P.evalInt [] = 0), primrec_decide_evalInt_nil, fun P hP ↦ ?_⟩
  rw [decide_eq_true_iff]
  exact ⟨fun h0 ↦ ⟨fun _ ↦ 0, (eval_toMvPoly_eq_evalInt_nil_of_deg_zero hP _).trans h0⟩,
    fun ⟨_, hx⟩ ↦ (eval_toMvPoly_eq_evalInt_nil_of_deg_zero hP _).symm.trans hx⟩

/-- **Universal Quartic Diophantine Equation over `ℤ`**: every recursively enumerable predicate
`p : ℕ → Prop` is represented by a single polynomial of total degree at most `4` over `ℤ`. -/
public theorem rePred_exists_quartic_int {p : ℕ → Prop} (hp : REPred p) :
    ∃ (m : ℕ) (Q : MvPolynomial (Fin (1 + m)) ℤ),
      Q.totalDegree ≤ 4 ∧
      ∀ n : ℕ, p n ↔ ∃ z : Fin (1 + m) → ℤ, z 0 = (n : ℤ) ∧ eval z Q = 0 := by
  obtain ⟨m₀, P₀, hP₀⟩ := dioph_iff_exists_mvPoly.mp (rePred_iff_dioph.mp hp)
  let P₁ : MvPolynomial (Fin (1 + m₀)) ℤ := rename finSumFinEquiv P₀
  let Qraw := skolemQuarticInt P₁
  let k := (reduceToSystem 1 P₁).auxVars
  let Nnat := (1 + m₀) + k
  let eqvNat : QuarticNatVar P₁ ≃ Fin Nnat := finSumFinEquiv
  let eqvAll : QuarticIntVar P₁ ≃ Fin (Nnat + Nnat * 4) :=
    (Equiv.sumCongr eqvNat (eqvNat.prodCongr (Equiv.refl (Fin 4)) |>.trans finProdFinEquiv)).trans
      finSumFinEquiv
  have hM : Nnat + Nnat * 4 = 1 + ((m₀ + k) + Nnat * 4) := by dsimp [Nnat]; ring
  let eqvFinal : QuarticIntVar P₁ ≃ Fin (1 + ((m₀ + k) + Nnat * 4)) :=
    eqvAll.trans (finCongr hM)
  have hv0 : eqvFinal (Sum.inl (Sum.inl 0)) = 0 := by
    apply Fin.ext; simp [eqvFinal, eqvAll, eqvNat]; rfl
  let Q := rename eqvFinal Qraw
  refine ⟨(m₀ + k) + Nnat * 4, Q,
    (totalDegree_rename_le _ Qraw).trans (totalDegree_skolemQuarticInt_le P₁), fun n ↦ ?_⟩
  have h0 : p n ↔ ∃ y₀ : Fin m₀ → ℕ,
      eval (fun u ↦ ((Sum.elim ![n] y₀ u : ℕ) : ℤ)) P₀ = 0 := hP₀ ![n]
  rw [h0]
  constructor
  · rintro ⟨y₀, hy₀⟩
    let x₁ : Fin (1 + m₀) → ℕ := Sum.elim ![n] y₀ ∘ finSumFinEquiv.symm
    have hx₁ : eval (fun i ↦ (x₁ i : ℤ)) P₁ = 0 := by
      rw [show P₁ = rename finSumFinEquiv P₀ from rfl, eval_rename]
      exact (congrArg (fun g ↦ eval g P₀) (funext fun v ↦ by simp [x₁])).trans hy₀
    obtain ⟨y₁, hy₁⟩ := (exists_aux_eval_skolemQuarticNat_iff P₁ x₁).mpr hx₁
    let xNat : QuarticNatVar P₁ → ℕ := Sum.elim x₁ y₁
    have hf : ∀ v : QuarticNatVar P₁, ∃ f : Fin 4 → ℤ, (xNat v : ℤ) = ∑ j : Fin 4, f j ^ 2 :=
      fun _ ↦ int_nonneg_iff_exists_four_int_sq.mp (Nat.cast_nonneg _)
    choose f hf using hf
    let zRaw : QuarticIntVar P₁ → ℤ := Sum.elim (fun v ↦ (xNat v : ℤ)) (fun p ↦ f p.1 p.2)
    have hzRaw : eval zRaw Qraw = 0 := by
      rw [show Qraw = skolemQuarticInt P₁ from rfl, eval_skolemQuarticInt_eq_zero_iff,
        forall_eval_mem_intifySystem_iff]
      exact ⟨(eval_skolemQuarticNat_eq_zero_iff P₁ _).mp hy₁, fun v ↦ hf v⟩
    refine ⟨zRaw ∘ eqvFinal.symm, ?_, ?_⟩
    · rw [← hv0, Function.comp_apply, Equiv.symm_apply_apply]
      have : finSumFinEquiv.symm (0 : Fin (1 + m₀)) = Sum.inl 0 :=
        finSumFinEquiv.injective rfl
      simp [zRaw, xNat, x₁, this]
    · rw [show Q = rename eqvFinal Qraw from rfl, eval_rename]
      exact (congrArg (fun g ↦ eval g Qraw) (funext fun v ↦ by simp)).trans hzRaw
  · rintro ⟨z, hz0, hz⟩
    rw [show Q = rename eqvFinal Qraw from rfl, eval_rename] at hz
    let zRaw := z ∘ eqvFinal
    obtain ⟨hall, hsq⟩ := (forall_eval_mem_intifySystem_iff _ zRaw).mp
      ((eval_skolemQuarticInt_eq_zero_iff P₁ zRaw).mp hz)
    have hnonneg : ∀ v : QuarticNatVar P₁, 0 ≤ zRaw (Sum.inl v) := fun v ↦ by
      rw [hsq v]; exact Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
    let xNat : QuarticNatVar P₁ → ℕ := fun v ↦ (zRaw (Sum.inl v)).toNat
    have hxNat : eval (fun v ↦ (xNat v : ℤ)) (skolemQuarticNat P₁) = 0 := by
      rw [eval_skolemQuarticNat_eq_zero_iff]
      intro r hr
      exact (congrArg (fun g ↦ eval g r)
        (funext fun v ↦ Int.toNat_of_nonneg (hnonneg v))).trans (hall r hr)
    let x₁ : Fin (1 + m₀) → ℕ := xNat ∘ Sum.inl
    have hx₁ : eval (fun i ↦ (x₁ i : ℤ)) P₁ = 0 := by
      refine (exists_aux_eval_skolemQuarticNat_iff P₁ x₁).mp ⟨xNat ∘ Sum.inr, ?_⟩
      refine (congrArg (fun g ↦ eval g (skolemQuarticNat P₁)) (funext fun v ↦ ?_)).trans hxNat
      cases v <;> rfl
    have hx1_0 : x₁ 0 = n := by
      have : (x₁ 0 : ℤ) = (n : ℤ) := by
        change (((zRaw (Sum.inl (Sum.inl 0))).toNat : ℕ) : ℤ) = (n : ℤ)
        rw [Int.toNat_of_nonneg (hnonneg (Sum.inl 0))]
        change z (eqvFinal (Sum.inl (Sum.inl 0))) = (n : ℤ)
        rw [hv0, hz0]
      exact Int.ofNat.inj this
    rw [show P₁ = rename finSumFinEquiv P₀ from rfl, eval_rename] at hx₁
    refine ⟨fun j ↦ x₁ (finSumFinEquiv (Sum.inr j)), ?_⟩
    refine (congrArg (fun g ↦ eval g P₀) (funext fun w ↦ ?_)).trans hx₁
    rcases w with i | j
    · fin_cases i
      have h0 : finSumFinEquiv (Sum.inl (0 : Fin 1) : Fin 1 ⊕ Fin m₀) = 0 := rfl
      change (n : ℤ) = (x₁ (finSumFinEquiv (Sum.inl 0)) : ℤ)
      rw [h0, hx1_0]
    · rfl

private theorem rePred_univHaltZero :
    REPred fun e : ℕ ↦ ((Denumerable.ofNat Nat.Partrec.Code e).eval 0).Dom := by
  refine rePred_iff_dioph.mpr ?_
  let m2 : Fin 2 → Option (Fin 1)
    | 0 => some 0
    | 1 => none
  exact (inter (eq_dioph (proj_dioph none) (const_dioph 0))
    (universal_dom_dioph.reindex_dioph (Option (Fin 1)) m2)).ex1_dioph.ext fun _ ↦
      ⟨fun ⟨w, h0, h⟩ ↦ by change w = 0 at h0; subst h0; exact h, fun h ↦ ⟨0, rfl, h⟩⟩

private theorem primrec_map_substVar0 (S₀ : List IntPoly) :
    Primrec fun n : ℕ ↦ S₀.map fun P ↦ P.substVar0 (n : ℤ) := by
  induction S₀ with
  | nil => exact Primrec.const []
  | cons P _ ih => exact Primrec.list_cons.comp (IntPoly.primrec_substVar0 P) ih

/-- **Undecidability of Hilbert's Tenth Problem at Degree `≥ 4` over `ℕ`**: for every `k ≥ 4`,
no computable algorithm decides whether an integer polynomial of total degree at most `k` has a
root in `ℕ`. -/
public theorem not_isDecidableDegreeNat_of_four_le {k : ℕ} (hk : 4 ≤ k) :
    ¬ IsDecidableDegreeNat k := by
  rintro ⟨f, hf, hspec⟩
  obtain ⟨m, Q, hQdeg, hQ⟩ := rePred_exists_quartic_nat rePred_univHaltZero
  let Qfin : MvPolynomial (Fin (1 + m)) ℤ := rename finSumFinEquiv Q
  let P₀ : IntPoly := IntPoly.ofMvPoly Qfin
  have hP₀deg : P₀.totalDegree ≤ 4 :=
    (IntPoly.totalDegree_ofMvPoly_le Qfin).trans ((totalDegree_rename_le _ Q).trans hQdeg)
  have hdec : ComputablePred fun c : Nat.Partrec.Code ↦ (c.eval 0).Dom := by
    refine ComputablePred.computable_iff.mpr
      ⟨fun c ↦ f (P₀.substVar0 (Encodable.encode c : ℤ)),
        hf.comp ((IntPoly.primrec_substVar0 P₀).to_comp.comp (Primrec.to_comp Primrec.encode)),
        funext fun c ↦ propext (Iff.symm ?_)⟩
    dsimp only
    rw [hspec _ ((P₀.totalDegree_substVar0_le _).trans (hP₀deg.trans hk)),
      P₀.hasNatRoot_substVar0_iff]
    have hce : (c.eval 0).Dom ↔
        ∃ y : Fin m → ℕ, eval (fun v ↦ ((Sum.elim ![Encodable.encode c] y v : ℕ) : ℤ)) Q = 0 := by
      simpa [Denumerable.ofNat_encode] using hQ (Encodable.encode c)
    rw [hce]
    constructor
    · rintro ⟨x, hx0, hx⟩
      rw [IntPoly.eval_toMvPoly_ofMvPoly, show Qfin = rename finSumFinEquiv Q from rfl,
        eval_rename] at hx
      refine ⟨fun j ↦ x (finSumFinEquiv (Sum.inr j : Fin 1 ⊕ Fin m)).1, ?_⟩
      refine (congrArg (fun g ↦ eval g Q) (funext fun w ↦ ?_)).trans hx
      rcases w with i | j
      · fin_cases i; change (Encodable.encode c : ℤ) = (x 0 : ℤ); rw [hx0]
      · rfl
    · rintro ⟨y, hy⟩
      let xfin : Fin (1 + m) → ℕ := Sum.elim ![Encodable.encode c] y ∘ finSumFinEquiv.symm
      refine ⟨fun i ↦ if hi : i < 1 + m then xfin ⟨i, hi⟩ else 0, ?_, ?_⟩
      · have h0lt : 0 < 1 + m := by omega
        have hf0 : finSumFinEquiv.symm (⟨0, h0lt⟩ : Fin (1 + m)) = Sum.inl 0 :=
          finSumFinEquiv.injective rfl
        simp only [dite_eq_left h0lt, xfin, Function.comp_apply, hf0, Sum.elim_inl,
          Matrix.cons_val_zero]
      · rw [IntPoly.eval_toMvPoly_ofMvPoly, show Qfin = rename finSumFinEquiv Q from rfl,
          eval_rename]
        exact (congrArg (fun g ↦ eval g Q) (funext fun v ↦ by simp [xfin])).trans hy
  exact ComputablePred.halting_problem 0 hdec

/-- **Undecidability of Hilbert's Tenth Problem at Degree `≥ 4` over `ℤ`**: for every `k ≥ 4`,
no computable algorithm decides whether an integer polynomial of total degree at most `k` has a
root in `ℤ`. -/
public theorem not_isDecidableDegreeInt_of_four_le {k : ℕ} (hk : 4 ≤ k) :
    ¬ IsDecidableDegreeInt k := by
  rintro ⟨f, hf, hspec⟩
  obtain ⟨m, Q, hQdeg, hQ⟩ := rePred_exists_quartic_int rePred_univHaltZero
  let P₀ : IntPoly := IntPoly.ofMvPoly Q
  have hP₀deg : P₀.totalDegree ≤ 4 := (IntPoly.totalDegree_ofMvPoly_le Q).trans hQdeg
  have hdec : ComputablePred fun c : Nat.Partrec.Code ↦ (c.eval 0).Dom := by
    refine ComputablePred.computable_iff.mpr
      ⟨fun c ↦ f (P₀.substVar0 (Encodable.encode c : ℤ)),
        hf.comp ((IntPoly.primrec_substVar0 P₀).to_comp.comp (Primrec.to_comp Primrec.encode)),
        funext fun c ↦ propext (Iff.symm ?_)⟩
    dsimp only
    rw [hspec _ ((P₀.totalDegree_substVar0_le _).trans (hP₀deg.trans hk)),
      P₀.hasIntRoot_substVar0_iff]
    have hce : (c.eval 0).Dom ↔
        ∃ z : Fin (1 + m) → ℤ, z 0 = (Encodable.encode c : ℤ) ∧ eval z Q = 0 := by
      simpa [Denumerable.ofNat_encode] using hQ (Encodable.encode c)
    rw [hce]
    constructor
    · rintro ⟨x, hx0, hx⟩
      rw [IntPoly.eval_toMvPoly_ofMvPoly] at hx
      exact ⟨fun i ↦ x i.1, hx0, hx⟩
    · rintro ⟨z, hz0, hz⟩
      refine ⟨fun i ↦ if hi : i < 1 + m then z ⟨i, hi⟩ else 0, ?_, ?_⟩
      · have h0lt : 0 < 1 + m := by omega
        simpa [dite_eq_left h0lt] using hz0
      · rw [IntPoly.eval_toMvPoly_ofMvPoly]
        exact (congrArg (fun g ↦ eval g Q) (funext fun i ↦ by simp [i.2])).trans hz
  exact ComputablePred.halting_problem 0 hdec

/-- **Undecidability of Finite Quadratic and Cubic Diophantine Systems over `ℕ`**: for every
`k ≥ 2` (in particular quadratic systems `k = 2` and cubic systems `k = 3`), no computable
algorithm decides whether a finite system of integer polynomials of degree at most `k` has a
common root in `ℕ`. -/
public theorem not_isDecidableSystemDegreeNat_of_two_le {k : ℕ} (hk : 2 ≤ k) :
    ¬ IsDecidableSystemDegreeNat k := by
  rintro ⟨f, hf, hspec⟩
  obtain ⟨m₀, P₀, hP₀⟩ := dioph_iff_exists_mvPoly.mp (rePred_iff_dioph.mp rePred_univHaltZero)
  let P₁ : MvPolynomial (Fin (1 + m₀)) ℤ := rename finSumFinEquiv P₀
  let sys := reduceToSystem 1 P₁
  let eqv : Fin (1 + m₀) ⊕ Fin sys.auxVars ≃ Fin ((1 + m₀) + sys.auxVars) := finSumFinEquiv
  let S₀ : List IntPoly := sys.allPolys.map fun q ↦ IntPoly.ofMvPoly (rename eqv q)
  have hS₀deg : ∀ P ∈ S₀, P.totalDegree ≤ 2 := by
    intro P hP
    rcases List.mem_map.mp hP with ⟨q, hq, rfl⟩
    exact (IntPoly.totalDegree_ofMvPoly_le _).trans
      ((totalDegree_rename_le _ _).trans (totalDegree_mem_allPolys_reduceToSystem_le 1 P₁ hq))
  have hdec : ComputablePred fun c : Nat.Partrec.Code ↦ (c.eval 0).Dom := by
    refine ComputablePred.computable_iff.mpr
      ⟨fun c ↦ f (S₀.map fun P ↦ P.substVar0 (Encodable.encode c : ℤ)),
        hf.comp ((primrec_map_substVar0 S₀).to_comp.comp (Primrec.to_comp Primrec.encode)),
        funext fun c ↦ propext (Iff.symm ?_)⟩
    dsimp only
    let e := Encodable.encode c
    rw [hspec _ (fun Q hQ ↦ by
      rcases List.mem_map.mp hQ with ⟨P, hP, rfl⟩
      exact (P.totalDegree_substVar0_le _).trans ((hS₀deg P hP).trans hk))]
    have hce : (c.eval 0).Dom ↔
        ∃ y₀ : Fin m₀ → ℕ, eval (fun v ↦ ((Sum.elim ![e] y₀ v : ℕ) : ℤ)) P₀ = 0 := by
      simpa [e, Denumerable.ofNat_encode] using hP₀ ![e]
    rw [hce]
    constructor
    · rintro ⟨x, hx⟩
      let x' : ℕ → ℕ := fun i ↦ if i = 0 then e else x i
      let z : Fin (1 + m₀) ⊕ Fin sys.auxVars → ℕ := fun v ↦ x' (eqv v).1
      have hall : ∀ q ∈ sys.allPolys, eval (fun v ↦ (z v : ℤ)) q = 0 := by
        intro q hq
        have hP := hx ((IntPoly.ofMvPoly (rename eqv q)).substVar0 (e : ℤ))
          (List.mem_map_of_mem (List.mem_map_of_mem hq))
        rw [IntPoly.eval_toMvPoly_substVar0, IntPoly.eval_toMvPoly_ofMvPoly, eval_rename] at hP
        refine (congrArg (fun g ↦ eval g q) (funext fun v ↦ ?_)).trans hP
        simp only [z, x', Function.comp_apply]
        split_ifs <;> rfl
      have hx₁ : eval (fun i ↦ ((z ∘ Sum.inl) i : ℤ)) P₁ = 0 := by
        refine (exists_aux_eval_skolemQuarticNat_iff P₁ (z ∘ Sum.inl)).mp ⟨z ∘ Sum.inr, ?_⟩
        rw [eval_skolemQuarticNat_eq_zero_iff]
        intro q hq
        refine (congrArg (fun g ↦ eval g q) (funext fun v ↦ ?_)).trans (hall q hq)
        cases v <;> rfl
      rw [show P₁ = rename finSumFinEquiv P₀ from rfl, eval_rename] at hx₁
      refine ⟨fun j ↦ z (Sum.inl (finSumFinEquiv (Sum.inr j))), ?_⟩
      refine (congrArg (fun g ↦ eval g P₀) (funext fun w ↦ ?_)).trans hx₁
      rcases w with i | j
      · fin_cases i
        have : (eqv (Sum.inl (finSumFinEquiv (Sum.inl 0)))).1 = 0 := rfl
        change (e : ℤ) = (x' (eqv (Sum.inl (finSumFinEquiv (Sum.inl 0)))).1 : ℤ)
        rw [this]; simp [x']
      · rfl
    · rintro ⟨y₀, hy₀⟩
      let x₁ : Fin (1 + m₀) → ℕ := Sum.elim ![e] y₀ ∘ finSumFinEquiv.symm
      have hx₁ : eval (fun i ↦ (x₁ i : ℤ)) P₁ = 0 := by
        rw [show P₁ = rename finSumFinEquiv P₀ from rfl, eval_rename]
        exact (congrArg (fun g ↦ eval g P₀) (funext fun v ↦ by simp [x₁])).trans hy₀
      obtain ⟨y₁, hy₁⟩ := (exists_aux_eval_skolemQuarticNat_iff P₁ x₁).mpr hx₁
      have hall := (eval_skolemQuarticNat_eq_zero_iff P₁ _).mp hy₁
      let zfin : Fin ((1 + m₀) + sys.auxVars) → ℕ := Sum.elim x₁ y₁ ∘ eqv.symm
      let x : ℕ → ℕ := fun i ↦ if hi : i < (1 + m₀) + sys.auxVars then zfin ⟨i, hi⟩ else 0
      have hx0 : x 0 = e := by
        have h0lt : 0 < (1 + m₀) + sys.auxVars := by omega
        have he0 : eqv.symm ⟨0, h0lt⟩ = Sum.inl 0 := eqv.injective (by ext; simp [eqv])
        have hf0 : finSumFinEquiv.symm (0 : Fin (1 + m₀)) = Sum.inl 0 :=
          finSumFinEquiv.injective rfl
        simp only [x, dite_eq_left h0lt, zfin, Function.comp_apply, he0, Sum.elim_inl,
          x₁, hf0, Matrix.cons_val_zero]
      refine ⟨x, fun Q hQ ↦ ?_⟩
      rcases List.mem_map.mp hQ with ⟨P, hP, rfl⟩
      rcases List.mem_map.mp hP with ⟨q, hq, rfl⟩
      rw [IntPoly.eval_toMvPoly_substVar0, IntPoly.eval_toMvPoly_ofMvPoly, eval_rename]
      refine (congrArg (fun g ↦ eval g q) (funext fun v ↦ ?_)).trans (hall q hq)
      simp only [Function.comp_apply]
      split_ifs with h
      · have hxe : x (eqv v).1 = e := h ▸ hx0
        change (e : ℤ) = _
        rw [← hxe]; simp [x, zfin]
      · simp [x, zfin]
  exact ComputablePred.halting_problem 0 hdec

/-- **Undecidability of Finite Quadratic and Cubic Diophantine Systems over `ℤ`**: for every
`k ≥ 2` (in particular quadratic systems `k = 2` and cubic systems `k = 3`), no computable
algorithm decides whether a finite system of integer polynomials of degree at most `k` has a
common root in `ℤ`. -/
public theorem not_isDecidableSystemDegreeInt_of_two_le {k : ℕ} (hk : 2 ≤ k) :
    ¬ IsDecidableSystemDegreeInt k := by
  rintro ⟨f, hf, hspec⟩
  obtain ⟨m₀, P₀, hP₀⟩ := dioph_iff_exists_mvPoly.mp (rePred_iff_dioph.mp rePred_univHaltZero)
  let P₁ : MvPolynomial (Fin (1 + m₀)) ℤ := rename finSumFinEquiv P₀
  let sysInt := intifySystem (reduceToSystem 1 P₁).allPolys
  let Nnat := (1 + m₀) + (reduceToSystem 1 P₁).auxVars
  let eqvNat : QuarticNatVar P₁ ≃ Fin Nnat := finSumFinEquiv
  let eqvAll : QuarticIntVar P₁ ≃ Fin (Nnat + Nnat * 4) :=
    (Equiv.sumCongr eqvNat (eqvNat.prodCongr (Equiv.refl (Fin 4)) |>.trans finProdFinEquiv)).trans
      finSumFinEquiv
  let S₀ : List IntPoly := sysInt.map fun q ↦ IntPoly.ofMvPoly (rename eqvAll q)
  have hS₀deg : ∀ P ∈ S₀, P.totalDegree ≤ 2 := by
    intro P hP
    rcases List.mem_map.mp hP with ⟨q, hq, rfl⟩
    exact (IntPoly.totalDegree_ofMvPoly_le _).trans
      ((totalDegree_rename_le _ _).trans
        (totalDegree_mem_intifySystem_le
          (fun r hr ↦ totalDegree_mem_allPolys_reduceToSystem_le 1 P₁ hr) hq))
  have hdec : ComputablePred fun c : Nat.Partrec.Code ↦ (c.eval 0).Dom := by
    refine ComputablePred.computable_iff.mpr
      ⟨fun c ↦ f (S₀.map fun P ↦ P.substVar0 (Encodable.encode c : ℤ)),
        hf.comp ((primrec_map_substVar0 S₀).to_comp.comp (Primrec.to_comp Primrec.encode)),
        funext fun c ↦ propext (Iff.symm ?_)⟩
    dsimp only
    let e := Encodable.encode c
    rw [hspec _ (fun Q hQ ↦ by
      rcases List.mem_map.mp hQ with ⟨P, hP, rfl⟩
      exact (P.totalDegree_substVar0_le _).trans ((hS₀deg P hP).trans hk))]
    have hsys_eq_quartic :
        (∃ x : ℕ → ℤ, ∀ Q ∈ (S₀.map fun P ↦ P.substVar0 (e : ℤ)), eval x Q.toMvPoly = 0) ↔
        ∃ z : QuarticIntVar P₁ → ℤ,
          z (Sum.inl (Sum.inl 0)) = (e : ℤ) ∧ eval z (skolemQuarticInt P₁) = 0 := by
      simp_rw [eval_skolemQuarticInt_eq_zero_iff]
      have hv0 : (eqvAll (Sum.inl (Sum.inl 0))).1 = 0 := rfl
      constructor
      · rintro ⟨x, hx⟩
        let x' : ℕ → ℤ := fun i ↦ if i = 0 then (e : ℤ) else x i
        refine ⟨fun v ↦ x' (eqvAll v).1, by simp [x', hv0], fun q hq ↦ ?_⟩
        have h0 := hx ((IntPoly.ofMvPoly (rename eqvAll q)).substVar0 (e : ℤ))
          (List.mem_map_of_mem (List.mem_map_of_mem hq))
        rw [IntPoly.eval_toMvPoly_substVar0, IntPoly.eval_toMvPoly_ofMvPoly, eval_rename] at h0
        exact h0
      · rintro ⟨z, hz0, hz⟩
        let x : ℕ → ℤ := fun i ↦ if hi : i < Nnat + Nnat * 4 then z (eqvAll.symm ⟨i, hi⟩) else 0
        have hx0 : x 0 = (e : ℤ) := by
          have h0lt : 0 < Nnat + Nnat * 4 := by dsimp [Nnat]; omega
          have he0 : eqvAll.symm ⟨0, h0lt⟩ = Sum.inl (Sum.inl 0) :=
            eqvAll.injective (by ext; simp [hv0])
          simp only [x, dite_eq_left h0lt, he0, hz0]
        refine ⟨x, fun Q hQ ↦ ?_⟩
        rcases List.mem_map.mp hQ with ⟨P, hP, rfl⟩
        rcases List.mem_map.mp hP with ⟨q, hq, rfl⟩
        rw [IntPoly.eval_toMvPoly_substVar0, IntPoly.eval_toMvPoly_ofMvPoly, eval_rename]
        refine (congrArg (fun g ↦ eval g q) (funext fun v ↦ ?_)).trans (hz q hq)
        simp only [Function.comp_apply]
        split_ifs with h
        · rw [← hx0, ← h]; simp [x]
        · simp [x]
    rw [hsys_eq_quartic]
    have hce : (c.eval 0).Dom ↔
        ∃ y₀ : Fin m₀ → ℕ, eval (fun v ↦ ((Sum.elim ![e] y₀ v : ℕ) : ℤ)) P₀ = 0 := by
      simpa [e, Denumerable.ofNat_encode] using hP₀ ![e]
    rw [hce]
    constructor
    · rintro ⟨z, hz0, hz⟩
      obtain ⟨hall, hsq⟩ := (forall_eval_mem_intifySystem_iff _ z).mp
        ((eval_skolemQuarticInt_eq_zero_iff P₁ z).mp hz)
      have hnn : ∀ v : QuarticNatVar P₁, 0 ≤ z (Sum.inl v) := fun v ↦ by
        rw [hsq v]; exact Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
      let xNat : QuarticNatVar P₁ → ℕ := fun v ↦ (z (Sum.inl v)).toNat
      have hxNat : eval (fun v ↦ (xNat v : ℤ)) (skolemQuarticNat P₁) = 0 := by
        rw [eval_skolemQuarticNat_eq_zero_iff]
        intro r hr
        exact (congrArg (fun g ↦ eval g r)
          (funext fun v ↦ Int.toNat_of_nonneg (hnn v))).trans (hall r hr)
      have hx₁ : eval (fun i ↦ ((xNat ∘ Sum.inl) i : ℤ)) (rename finSumFinEquiv P₀) = 0 := by
        refine (exists_aux_eval_skolemQuarticNat_iff P₁ (xNat ∘ Sum.inl)).mp ⟨xNat ∘ Sum.inr, ?_⟩
        refine (congrArg (fun g ↦ eval g (skolemQuarticNat P₁)) (funext fun v ↦ ?_)).trans hxNat
        cases v <;> rfl
      rw [eval_rename] at hx₁
      have hx0 : xNat (Sum.inl 0) = e :=
        Int.ofNat.inj ((Int.toNat_of_nonneg (hnn (Sum.inl 0))).trans hz0)
      refine ⟨fun j ↦ xNat (Sum.inl (finSumFinEquiv (Sum.inr j))), ?_⟩
      refine (congrArg (fun g ↦ eval g P₀) (funext fun w ↦ ?_)).trans hx₁
      rcases w with i | j
      · fin_cases i
        have hf0 : finSumFinEquiv (Sum.inl (0 : Fin 1) : Fin 1 ⊕ Fin m₀) = 0 := rfl
        change (e : ℤ) = (xNat (Sum.inl (finSumFinEquiv (Sum.inl 0))) : ℤ)
        rw [hf0, hx0]
      · rfl
    · rintro ⟨y₀, hy₀⟩
      let x₁ : Fin (1 + m₀) → ℕ := Sum.elim ![e] y₀ ∘ finSumFinEquiv.symm
      have hx₁ : eval (fun i ↦ (x₁ i : ℤ)) P₁ = 0 := by
        rw [show P₁ = rename finSumFinEquiv P₀ from rfl, eval_rename]
        exact (congrArg (fun g ↦ eval g P₀) (funext fun v ↦ by simp [x₁])).trans hy₀
      obtain ⟨y₁, hy₁⟩ := (exists_aux_eval_skolemQuarticNat_iff P₁ x₁).mpr hx₁
      let xNat : QuarticNatVar P₁ → ℕ := Sum.elim x₁ y₁
      have hf : ∀ v, ∃ g : Fin 4 → ℤ, (xNat v : ℤ) = ∑ j : Fin 4, g j ^ 2 := fun _ ↦
        int_nonneg_iff_exists_four_int_sq.mp (Nat.cast_nonneg _)
      choose g hg using hf
      refine ⟨Sum.elim (fun v ↦ (xNat v : ℤ)) (fun p ↦ g p.1 p.2), ?_, ?_⟩
      · have hf0 : finSumFinEquiv.symm (0 : Fin (1 + m₀)) = Sum.inl 0 :=
          finSumFinEquiv.injective rfl
        simp [xNat, x₁, hf0]
      · rw [eval_skolemQuarticInt_eq_zero_iff, forall_eval_mem_intifySystem_iff]
        exact ⟨(eval_skolemQuarticNat_eq_zero_iff P₁ _).mp hy₁, fun v ↦ hg v⟩
  exact ComputablePred.halting_problem 0 hdec

/-- **Unique Classical Degree Threshold**: for any downward-closed predicate `D : ℕ → Prop` with
`D 0` and `¬ D 4`, there exists a unique `k : ℕ` (lying in `{1, 2, 3, 4}`) satisfying
`(∀ m < k, D m) ∧ (∀ m ≥ k, ¬ D m)`. -/
public theorem existsUnique_threshold_of_zero_of_not_four {D : ℕ → Prop}
    (h0 : D 0) (h4 : ¬ D 4) (hanti : ∀ ⦃k m⦄, k ≤ m → D m → D k) :
    ∃! k : ℕ, (∀ m < k, D m) ∧ (∀ m ≥ k, ¬ D m) := by
  have hex : ∃ k : ℕ, (∀ m < k, D m) ∧ ¬ D k := by
    by_cases h1 : D 1
    · by_cases h2 : D 2
      · by_cases h3 : D 3
        · refine ⟨4, fun m hm ↦ ?_, h4⟩
          interval_cases m <;> assumption
        · refine ⟨3, fun m hm ↦ ?_, h3⟩
          interval_cases m <;> assumption
      · refine ⟨2, fun m hm ↦ ?_, h2⟩
        interval_cases m <;> assumption
    · refine ⟨1, fun m hm ↦ ?_, h1⟩
      interval_cases m
      exact h0
  rcases hex with ⟨k, hlt, hnk⟩
  refine ⟨k, ⟨hlt, fun m hm hDm ↦ hnk (hanti hm hDm)⟩, ?_⟩
  rintro k' ⟨hlt', hge'⟩
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · exact hge' k' le_rfl (hlt k' h)
  · exact hnk (hlt' k h)

/-- There exists a unique degree threshold `k : ℕ` (`1 ≤ k ≤ 4`) such that `IsDecidableDegreeNat m`
holds for all `m < k` and fails for all `m ≥ k`. -/
public theorem existsUnique_undecidable_degree_threshold_nat :
    ∃! k : ℕ, (∀ m < k, IsDecidableDegreeNat m) ∧ (∀ m ≥ k, ¬ IsDecidableDegreeNat m) :=
  existsUnique_threshold_of_zero_of_not_four
    isDecidableDegreeNat_zero
    (not_isDecidableDegreeNat_of_four_le le_rfl)
    fun _ _ h ↦ IsDecidableDegreeNat.anti h

/-- There exists a unique degree threshold `k : ℕ` (`1 ≤ k ≤ 4`) such that `IsDecidableDegreeInt m`
holds for all `m < k` and fails for all `m ≥ k`. -/
public theorem existsUnique_undecidable_degree_threshold_int :
    ∃! k : ℕ, (∀ m < k, IsDecidableDegreeInt m) ∧ (∀ m ≥ k, ¬ IsDecidableDegreeInt m) :=
  existsUnique_threshold_of_zero_of_not_four
    isDecidableDegreeInt_zero
    (not_isDecidableDegreeInt_of_four_le le_rfl)
    fun _ _ h ↦ IsDecidableDegreeInt.anti h

/-- Non-vacuity witness: `IsDecidableDegreeNat 0` holds while `IsDecidableDegreeNat 4` and
`IsDecidableSystemDegreeNat 3` both fail. -/
private example :
    IsDecidableDegreeNat 0 ∧ ¬ IsDecidableDegreeNat 4 ∧ ¬ IsDecidableSystemDegreeNat 3 :=
  ⟨isDecidableDegreeNat_zero,
    not_isDecidableDegreeNat_of_four_le le_rfl,
    not_isDecidableSystemDegreeNat_of_two_le (by decide)⟩

end CslibFrontier.Computability.Diophantine
