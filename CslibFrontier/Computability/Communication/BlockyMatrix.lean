/-
Copyright (c) 2026 Google DeepMind. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Google DeepMind
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Communication.Rank
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Basic.Real.Basic
public import CslibFrontier.Computability.Communication.EqualityOracle
public import CslibFrontier.Computability.Communication.FactorizationNorm

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Blocky Matrices, Fractional Blocky Covers, and Equality-Oracle Lower Bounds

This module develops blocky Boolean matrices (`IsBlocky`), the `γ₂` factorization-norm lower bound
on deterministic `Equality`-oracle communication complexity, integral blocky cover numbers
(`blockyCoverNumber`), the monochromatic rectangle functional (`maxRect`), and fractional blocky
covers (`FractionalBlockyCover`, `fractionalBlockyCoverNumber`), including randomized rounding and
their quantitative equivalence with nondeterministic `Equality`-oracle complexity, under standard
Lean axioms.

## Main definitions

* `CslibFrontier.Communication.IsBlocky`: finite Boolean matrices arising from an identity matrix
via
  row/column duplication, permutation, and addition of all-zero rows/columns.
* `CslibFrontier.Communication.blockyCoverNumber`: integral blocky cover number `bc(M)`.
* `CslibFrontier.Communication.onesCount`, `CslibFrontier.Communication.IsMonoRect`,
  `CslibFrontier.Communication.maxMonoRectArea`, `CslibFrontier.Communication.maxRect`: the
  monochromatic
  rectangle ratio `maxrect(A) = α(A) / (|X| * √β(A))`.
* `CslibFrontier.Communication.FractionalBlockyCover`,
  `CslibFrontier.Communication.fractionalBlockyCoverNumber`: fractional blocky covers and `fbc(A)`.

## Main results

* `CslibFrontier.Communication.half_logb_gamma2Norm_le_eqOracleComplexity`:
  `(1 / 2) * log₂ γ₂(M) ≤ D^Eq(M)`.
* `CslibFrontier.Communication.exists_large_monoRect`: every nonzero `N × N` Boolean matrix `A`
contains
  a `1`-chromatic rectangle `U × V` with `min |U| |V| ≥ α(A) / (2 N bc(A))`.
* `CslibFrontier.Communication.maxRect_le_two_mul_blockyCoverNumber`:
  `maxrect(A) ≤ 2 * bc(A)`.
* `CslibFrontier.Communication.IsBlocky.fractionalBlockyCoverNumber_not_le_two`,
  `CslibFrontier.Communication.IsBlocky.fractionalBlockyCoverNumber_not_le_four`,
  `CslibFrontier.Communication.fractionalBlockyCoverNumber_and_le`,
  `CslibFrontier.Communication.fractionalBlockyCoverNumber_or_le`,
  `CslibFrontier.Communication.blockyCoverNumber_le_four_mul_fbc_mul_log`: complement, intersection,
  union, and randomized-rounding inequalities for `fbc`.
* `CslibFrontier.Communication.ndEqOracleComplexity_le_clog_blockyCoverNumber_add_one` and
  `CslibFrontier.Communication.logb_blockyCoverNumber_le_ndEq_add_log_log`: two-sided relationship
  between `ND^Eq(A)` and `log₂ bc(A)`.
-/

public section

open Finset Cslib Cslib.BitString Cslib.Communication
open scoped BigOperators

namespace CslibFrontier.Communication

section BlockyMatrices

variable {X Y X' Y' : Type*} [Fintype X] [Fintype Y]

/-- A finite Boolean matrix `B : X → Y → Bool` is *blocky* if it is obtained from an identity
matrix `I_{m,m}` with `m ≤ min (card X) (card Y)` by duplicating rows and columns, permuting rows
and columns, and adding all-zero rows and columns (represented by `none`). -/
@[expose]
def IsBlocky (B : X → Y → Bool) : Prop :=
  ∃ (m : ℕ) (_ : m ≤ min (Fintype.card X) (Fintype.card Y))
    (a : X → Option (Fin m)) (b : Y → Option (Fin m)),
    ∀ x y, B x y = true ↔ ∃ c : Fin m, a x = some c ∧ b y = some c

/-- Any Boolean matrix expressing equality `a x = b y` of two functions into an arbitrary type `α`
is blocky (with `m = |range a ∩ range b| ≤ min |X| |Y|`). -/
theorem IsBlocky.of_eq {α : Type*} {B : X → Y → Bool} (a : X → α) (b : Y → α)
    (h : ∀ x y, B x y = true ↔ a x = b y) : IsBlocky B := by
  classical
  let S : Finset α := Finset.univ.image a ∩ Finset.univ.image b
  have hSX : S.card ≤ Fintype.card X :=
    (Finset.card_le_card Finset.inter_subset_left).trans Finset.card_image_le
  have hSY : S.card ≤ Fintype.card Y :=
    (Finset.card_le_card Finset.inter_subset_right).trans Finset.card_image_le
  let e : { z : α // z ∈ S } ≃ Fin S.card := Fintype.equivFinOfCardEq (Fintype.card_coe S)
  refine ⟨S.card, le_min hSX hSY,
    fun x ↦ if hx : a x ∈ S then some (e ⟨a x, hx⟩) else none,
    fun y ↦ if hy : b y ∈ S then some (e ⟨b y, hy⟩) else none,
    fun x y ↦ ?_⟩
  rw [h]
  constructor
  · intro hxy
    have hx : a x ∈ S := Finset.mem_inter.mpr
      ⟨Finset.mem_image_of_mem a (Finset.mem_univ x),
       hxy ▸ Finset.mem_image_of_mem b (Finset.mem_univ y)⟩
    have hy : b y ∈ S := hxy ▸ hx
    refine ⟨e ⟨a x, hx⟩, ?_, ?_⟩
    · simp only [hx, ↓reduceDIte]
    · simp only [hy, ↓reduceDIte]
      exact congr_arg (fun z ↦ some (e z)) (Subtype.ext hxy.symm)
  · rintro ⟨c, hx, hy⟩
    by_cases hxs : a x ∈ S
    · simp only [hxs, ↓reduceDIte] at hx
      by_cases hys : b y ∈ S
      · simp only [hys, ↓reduceDIte] at hy
        have hsub : (⟨a x, hxs⟩ : { z : α // z ∈ S }) = ⟨b y, hys⟩ :=
          e.injective ((Option.some.inj hx).trans (Option.some.inj hy).symm)
        exact congr_arg Subtype.val hsub
      · simp only [hys, ↓reduceDIte] at hy
        cases hy
    · simp only [hxs, ↓reduceDIte] at hx
      cases hx

/-- The all-`false` Boolean matrix is blocky. -/
theorem IsBlocky.const_false : IsBlocky (fun (_ : X) (_ : Y) ↦ false) :=
  ⟨0, Nat.zero_le _, fun _ ↦ none, fun _ ↦ none, fun _ _ ↦ by simp⟩

/-- The all-`true` Boolean matrix is blocky. -/
theorem IsBlocky.const_true : IsBlocky (fun (_ : X) (_ : Y) ↦ true) :=
  IsBlocky.of_eq (fun _ : X ↦ ()) (fun _ : Y ↦ ()) (fun _ _ ↦ by simp)

/-- Every combinatorial rectangle `U × V` is a blocky matrix. -/
theorem IsBlocky.rect (U : X → Bool) (V : Y → Bool) :
    IsBlocky (fun x y ↦ U x && V y) :=
  IsBlocky.of_eq
    (fun x ↦ if U x then (0 : Fin 3) else 1)
    (fun y ↦ if V y then (0 : Fin 3) else 2)
    (fun x y ↦ by cases U x <;> cases V y <;> decide)

/-- Every symmetric bipartition `(S × Sᶜ) ⊔ (Sᶜ × S)` is a blocky matrix. -/
theorem IsBlocky.bipartition (p : X → Bool) (q : Y → Bool) :
    IsBlocky (fun x y ↦ p x != q y) :=
  IsBlocky.of_eq p (fun y ↦ !q y) (fun x y ↦ by cases p x <;> cases q y <;> simp)

/-- The identity (`equality`) Boolean matrix on `X` is blocky. -/
theorem IsBlocky.equality [DecidableEq X] : IsBlocky (equality : X → X → Bool) :=
  IsBlocky.of_eq id id (fun _ _ ↦ by simp [Cslib.Communication.equality])

/-- Pulling back a blocky matrix along arbitrary maps `f : X' → X` and `g : Y' → Y` (covering
submatrices, permutations, and row/column duplications) yields a blocky matrix. -/
theorem IsBlocky.comap [Fintype X'] [Fintype Y'] {B : X → Y → Bool} (hB : IsBlocky B)
    (f : X' → X) (g : Y' → Y) : IsBlocky (fun x y ↦ B (f x) (g y)) := by
  obtain ⟨m, _, a, b, hab⟩ := hB
  let fa : X' → Fin m ⊕ Bool := fun x ↦ Option.rec (Sum.inr false) Sum.inl (a (f x))
  let fb : Y' → Fin m ⊕ Bool := fun y ↦ Option.rec (Sum.inr true) Sum.inl (b (g y))
  refine IsBlocky.of_eq fa fb (fun x y ↦ ?_)
  rw [hab]
  cases ha : a (f x) <;> cases hb : b (g y) <;> simp [fa, fb, ha, hb, eq_comm]

/-- The entrywise conjunction (Hadamard product) of two blocky matrices is blocky. -/
theorem IsBlocky.and {B₁ B₂ : X → Y → Bool} (h₁ : IsBlocky B₁) (h₂ : IsBlocky B₂) :
    IsBlocky (fun x y ↦ B₁ x y && B₂ x y) := by
  obtain ⟨m₁, _, a₁, b₁, hab₁⟩ := h₁
  obtain ⟨m₂, _, a₂, b₂, hab₂⟩ := h₂
  let fa : X → (Fin m₁ × Fin m₂) ⊕ Bool := fun x ↦
    Option.rec (Sum.inr false) (fun c₁ ↦ Option.rec (Sum.inr false) (fun c₂ ↦ Sum.inl (c₁, c₂))
      (a₂ x)) (a₁ x)
  let fb : Y → (Fin m₁ × Fin m₂) ⊕ Bool := fun y ↦
    Option.rec (Sum.inr true) (fun c₁ ↦ Option.rec (Sum.inr true) (fun c₂ ↦ Sum.inl (c₁, c₂))
      (b₂ y)) (b₁ y)
  refine IsBlocky.of_eq fa fb (fun x y ↦ ?_)
  rw [Bool.and_eq_true_iff, hab₁, hab₂]
  cases h1x : a₁ x <;> cases h2x : a₂ x <;> cases h1y : b₁ y <;> cases h2y : b₂ y <;>
    simp [fa, fb, h1x, h2x, h1y, h2y, eq_comm]

/-- Every blocky matrix decomposes into pairwise row- and column-disjoint `1`-chromatic
combinatorial rectangles. -/
theorem IsBlocky.disjoint_rectangles {B : X → Y → Bool} (hB : IsBlocky B) :
    ∃ (m : ℕ) (U : Fin m → Finset X) (V : Fin m → Finset Y),
      (∀ i j, i ≠ j → Disjoint (U i) (U j)) ∧
      (∀ i j, i ≠ j → Disjoint (V i) (V j)) ∧
      (∑ i, (U i).card ≤ Fintype.card X) ∧
      (∑ i, (V i).card ≤ Fintype.card Y) ∧
      (∀ x y, B x y = true ↔ ∃ i, x ∈ U i ∧ y ∈ V i) := by
  classical
  obtain ⟨m, _, a, b, hab⟩ := hB
  let U : Fin m → Finset X := fun i ↦ Finset.univ.filter (fun x ↦ a x = some i)
  let V : Fin m → Finset Y := fun i ↦ Finset.univ.filter (fun y ↦ b y = some i)
  have hdU : ∀ i j, i ≠ j → Disjoint (U i) (U j) := by
    intro i j hij
    rw [Finset.disjoint_left]
    intro x hxi hxj
    simp only [U, Finset.mem_filter] at hxi hxj
    exact hij (Option.some.inj (hxi.2.symm.trans hxj.2))
  have hdV : ∀ i j, i ≠ j → Disjoint (V i) (V j) := by
    intro i j hij
    rw [Finset.disjoint_left]
    intro y hyi hyj
    simp only [V, Finset.mem_filter] at hyi hyj
    exact hij (Option.some.inj (hyi.2.symm.trans hyj.2))
  have hsumU : ∑ i : Fin m, (U i).card ≤ Fintype.card X := by
    rw [← Finset.card_biUnion (fun i _ j _ hij ↦ hdU i j hij)]
    exact Finset.card_le_univ _
  have hsumV : ∑ i : Fin m, (V i).card ≤ Fintype.card Y := by
    rw [← Finset.card_biUnion (fun i _ j _ hij ↦ hdV i j hij)]
    exact Finset.card_le_univ _
  refine ⟨m, U, V, hdU, hdV, hsumU, hsumV, fun x y ↦ ?_⟩
  rw [hab]
  simp [U, V]

/-- Every blocky matrix can be computed with at most `1` `Equality`-oracle query. -/
theorem IsBlocky.eqOracleComplexity_le_one {B : X → Y → Bool} (hB : IsBlocky B) :
    eqOracleComplexity B ≤ 1 := by
  classical
  obtain ⟨m, _, a, b, hab⟩ := hB
  let alice : X → Fin m ⊕ Bool := fun x ↦ Option.rec (Sum.inr false) Sum.inl (a x)
  let bob : Y → Fin m ⊕ Bool := fun y ↦ Option.rec (Sum.inr true) Sum.inl (b y)
  let p : OracleProtocol eqOracle X Y Bool := eqQuery alice bob (.output false) (.output true)
  have hev : p.eval = B := by
    ext x y
    rw [eval_eqQuery (α := Fin m ⊕ Bool)]
    have hiff : alice x = bob y ↔ B x y = true := by
      rw [hab]
      cases ha : a x <;> cases hb : b y <;> simp [alice, bob, ha, hb, eq_comm]
    have hdec : @decide (alice x = bob y) (instDecidableEqSum (alice x) (bob y)) = B x y := by
      rw [Bool.eq_iff_iff, @decide_eq_true_eq _ (instDecidableEqSum (alice x) (bob y))]
      exact hiff
    change cond (@decide (alice x = bob y) (instDecidableEqSum (alice x) (bob y)))
      ((OracleProtocol.output true : OracleProtocol eqOracle X Y Bool).eval x y)
      ((OracleProtocol.output false : OracleProtocol eqOracle X Y Bool).eval x y) = B x y
    rw [hdec]
    cases B x y <;> simp
  exact (eqOracleComplexity_le_depth hev).trans (by simp [p])

/-- Every blocky matrix has `γ₂` factorization norm at most `1`. -/
theorem IsBlocky.gamma2Norm_le_one {B : X → Y → Bool} (hB : IsBlocky B) :
    CslibFrontier.Matrix.gamma2Norm (communicationMatrix ℝ B) ≤ 1 := by
  obtain ⟨m, _, a, b, hab⟩ := hB
  let U : Matrix X (Fin m) ℝ := _root_.Matrix.of fun x c ↦ if a x = some c then 1 else 0
  let V : Matrix (Fin m) Y ℝ := _root_.Matrix.of fun c y ↦ if b y = some c then 1 else 0
  have hUV : U * V = communicationMatrix ℝ B := by
    ext x y
    simp only [_root_.Matrix.mul_apply, U, V, _root_.Matrix.of_apply, communicationMatrix_apply]
    cases hxy : B x y
    · change _ = (0 : ℝ)
      refine Finset.sum_eq_zero (fun c _ ↦ ?_)
      by_cases hax : a x = some c
      · have hby : b y ≠ some c := fun h ↦ by
          have ht := (hab x y).mpr ⟨c, hax, h⟩
          rw [hxy] at ht; cases ht
        simp [hax, hby]
      · simp [hax]
    · obtain ⟨c, hax, hby⟩ := (hab x y).mp hxy
      rw [Finset.sum_eq_single c]
      · simp [hax, hby]
      · intro c' _ hne
        have hne' : a x ≠ some c' := by rw [hax]; exact fun h ↦ hne (Option.some.inj h).symm
        simp only [hne', ↓reduceIte, zero_mul]
      · intro hc; exact absurd (Finset.mem_univ c) hc
  have hU : CslibFrontier.Matrix.rowL2Norm U ≤ 1 := by
    refine CslibFrontier.Matrix.rowL2Norm_le_of_sq zero_le_one (fun x ↦ ?_)
    cases hax : a x with
    | none => simp [U, hax]
    | some c =>
      rw [Finset.sum_eq_single c (fun c' _ hne ↦ by simp [U, hax, hne.symm])
        (fun hc ↦ absurd (Finset.mem_univ c) hc)]
      simp [U, hax]
  have hV : CslibFrontier.Matrix.colL2Norm V ≤ 1 := by
    refine CslibFrontier.Matrix.colL2Norm_le_of_sq zero_le_one (fun y ↦ ?_)
    cases hby : b y with
    | none => simp [V, hby]
    | some c =>
      rw [Finset.sum_eq_single c (fun c' _ hne ↦ by simp [V, hby, hne.symm])
        (fun hc ↦ absurd (Finset.mem_univ c) hc)]
      simp [V, hby]
  calc CslibFrontier.Matrix.gamma2Norm (communicationMatrix ℝ B)
      ≤ CslibFrontier.Matrix.rowL2Norm U * CslibFrontier.Matrix.colL2Norm V :=
        CslibFrontier.Matrix.gamma2Norm_le_of_factorization U V hUV
    _ ≤ 1 * 1 := mul_le_mul hU hV (CslibFrontier.Matrix.colL2Norm_nonneg V) zero_le_one
    _ = 1 := mul_one 1

/-- Every deterministic `Equality`-oracle protocol `p` satisfies
`gamma2Norm (communicationMatrix ℝ p.eval) ≤ 3 ^ p.depth`. -/
theorem gamma2Norm_le_three_pow_eqProtocol (p : OracleProtocol eqOracle X Y Bool) :
    CslibFrontier.Matrix.gamma2Norm (communicationMatrix ℝ p.eval) ≤ (3 : ℝ) ^ p.depth := by
  induction p with
  | output z =>
    cases z
    · have hz : communicationMatrix ℝ
          (OracleProtocol.output false : OracleProtocol eqOracle X Y Bool).eval = 0 := by
        ext x y; simp [communicationMatrix_apply]
      rw [hz, OracleProtocol.depth_output, pow_zero, CslibFrontier.Matrix.gamma2Norm_zero]
      exact zero_le_one
    · have ht : communicationMatrix ℝ
          (OracleProtocol.output true : OracleProtocol eqOracle X Y Bool).eval =
          _root_.Matrix.of fun _ _ ↦ (1 : ℝ) := by
        ext x y; simp [communicationMatrix_apply]
      rw [ht, OracleProtocol.depth_output, pow_zero]
      exact CslibFrontier.Matrix.gamma2Norm_ones_le
  | query m a b p₀ p₁ ih₀ ih₁ =>
    let B : X → Y → Bool := fun x y ↦ eqOracle m (a x) (b y)
    have hB : IsBlocky B := IsBlocky.of_eq a b (fun _ _ ↦ by simp [B, equality])
    let J : Matrix X Y ℝ := _root_.Matrix.of fun _ _ ↦ 1
    let MB : Matrix X Y ℝ := communicationMatrix ℝ B
    have hdecomp : communicationMatrix ℝ (OracleProtocol.query m a b p₀ p₁).eval =
        _root_.Matrix.hadamard MB (communicationMatrix ℝ p₁.eval) +
          _root_.Matrix.hadamard (J - MB) (communicationMatrix ℝ p₀.eval) := by
      ext x y
      simp only [OracleProtocol.eval_query, communicationMatrix_apply, _root_.Matrix.add_apply,
        _root_.Matrix.hadamard_apply, _root_.Matrix.sub_apply, J, MB, _root_.Matrix.of_apply]
      change bitVal ℝ (cond (B x y) (p₁.eval x y) (p₀.eval x y)) = _
      cases B x y <;> cases p₁.eval x y <;> cases p₀.eval x y <;> simp
    rw [hdecomp, OracleProtocol.depth_query]
    set d := max p₀.depth p₁.depth
    have h₀ : CslibFrontier.Matrix.gamma2Norm (communicationMatrix ℝ p₀.eval) ≤ (3 : ℝ) ^ d :=
      ih₀.trans (pow_le_pow_right₀ (a := (3 : ℝ)) (by norm_num) (le_max_left _ _))
    have h₁ : CslibFrontier.Matrix.gamma2Norm (communicationMatrix ℝ p₁.eval) ≤ (3 : ℝ) ^ d :=
      ih₁.trans (pow_le_pow_right₀ (a := (3 : ℝ)) (by norm_num) (le_max_right _ _))
    have hMB : CslibFrontier.Matrix.gamma2Norm MB ≤ 1 := hB.gamma2Norm_le_one
    have hJMB : CslibFrontier.Matrix.gamma2Norm (J - MB) ≤ 2 := by
      calc CslibFrontier.Matrix.gamma2Norm (J - MB)
          ≤ CslibFrontier.Matrix.gamma2Norm J + CslibFrontier.Matrix.gamma2Norm MB :=
            CslibFrontier.Matrix.gamma2Norm_sub_le J MB
        _ ≤ 1 + 1 := add_le_add CslibFrontier.Matrix.gamma2Norm_ones_le hMB
        _ = 2 := by norm_num
    calc CslibFrontier.Matrix.gamma2Norm
          (_root_.Matrix.hadamard MB (communicationMatrix ℝ p₁.eval) +
            _root_.Matrix.hadamard (J - MB) (communicationMatrix ℝ p₀.eval))
        ≤ CslibFrontier.Matrix.gamma2Norm (_root_.Matrix.hadamard MB (communicationMatrix ℝ
        p₁.eval)) +
            CslibFrontier.Matrix.gamma2Norm
              (_root_.Matrix.hadamard (J - MB) (communicationMatrix ℝ p₀.eval)) :=
          CslibFrontier.Matrix.gamma2Norm_add_le _ _
      _ ≤ CslibFrontier.Matrix.gamma2Norm MB *
            CslibFrontier.Matrix.gamma2Norm (communicationMatrix ℝ p₁.eval) +
          CslibFrontier.Matrix.gamma2Norm (J - MB) *
            CslibFrontier.Matrix.gamma2Norm (communicationMatrix ℝ p₀.eval) :=
          add_le_add (CslibFrontier.Matrix.gamma2Norm_hadamard_le _ _)
            (CslibFrontier.Matrix.gamma2Norm_hadamard_le _ _)
      _ ≤ 1 * (3 : ℝ) ^ d + 2 * (3 : ℝ) ^ d :=
          add_le_add
            (mul_le_mul hMB h₁ (CslibFrontier.Matrix.gamma2Norm_nonneg _) zero_le_one)
            (mul_le_mul hJMB h₀ (CslibFrontier.Matrix.gamma2Norm_nonneg _) (by norm_num))
      _ = (3 : ℝ) ^ (d + 1) := by rw [pow_succ]; ring

/-- For every finite Boolean matrix `f : X → Y → Bool`,
`gamma2Norm (communicationMatrix ℝ f) ≤ 3 ^ D^Eq(f)` (and hence `≤ 4 ^ D^Eq(f)`). -/
theorem gamma2Norm_le_three_pow_eqOracleComplexity (f : X → Y → Bool) :
    CslibFrontier.Matrix.gamma2Norm (communicationMatrix ℝ f) ≤ (3 : ℝ) ^ eqOracleComplexity f := by
  obtain ⟨p, hp, hd⟩ := exists_eval_depth_le_eqOracleComplexity f
  have h1 : CslibFrontier.Matrix.gamma2Norm (communicationMatrix ℝ f) ≤ (3 : ℝ) ^ p.depth := by
    rw [← hp]; exact gamma2Norm_le_three_pow_eqProtocol p
  exact h1.trans (pow_le_pow_right₀ (a := (3 : ℝ)) (by norm_num) hd)

/-- **`γ₂`-norm lower bound on deterministic `Equality`-oracle complexity**
: for every finite Boolean matrix `f : X → Y → Bool`,
`(1 / 2) * log₂ (gamma2Norm (communicationMatrix ℝ f)) ≤ D^Eq(f)`.
-/
theorem half_logb_gamma2Norm_le_eqOracleComplexity (f : X → Y → Bool) :
    (1 / 2 : ℝ) * Real.logb 2 (CslibFrontier.Matrix.gamma2Norm (communicationMatrix ℝ f)) ≤
      eqOracleComplexity f := by
  set g := CslibFrontier.Matrix.gamma2Norm (communicationMatrix ℝ f)
  set d := eqOracleComplexity f
  by_cases hg : g = 0
  · simp [hg]
  · have hpos : 0 < g := (CslibFrontier.Matrix.gamma2Norm_nonneg _).lt_of_ne' hg
    have h4 : g ≤ (2 : ℝ) ^ (2 * d) := by
      calc g ≤ (3 : ℝ) ^ d := gamma2Norm_le_three_pow_eqOracleComplexity f
        _ ≤ (4 : ℝ) ^ d := pow_le_pow_left₀ (by norm_num) (by norm_num) d
        _ = (2 : ℝ) ^ (2 * d) := by rw [pow_mul]; norm_num
    have hlog : Real.logb 2 g ≤ ((2 * d : ℕ) : ℝ) := by
      calc Real.logb 2 g ≤ Real.logb 2 ((2 : ℝ) ^ (2 * d)) :=
            Real.logb_le_logb_of_le (by norm_num) hpos h4
        _ = ((2 * d : ℕ) : ℝ) := by
            rw [← Real.rpow_natCast, Real.logb_rpow (by norm_num) (by norm_num)]
    push_cast at hlog
    linarith

/-- Blocky cover number `bc(M)` of a finite Boolean matrix `M : X → Y → Bool`: the minimum `r : ℕ`
such that `M` is the entrywise OR of `r` blocky matrices `B₁, …, B_r`. -/
noncomputable def blockyCoverNumber (M : X → Y → Bool) : ℕ :=
  sInf { r : ℕ | ∃ B : Fin r → X → Y → Bool,
    (∀ i, IsBlocky (B i)) ∧ (∀ x y, M x y = true ↔ ∃ i, B i x y = true) }

/-- Every finite Boolean matrix admits a blocky cover of size at most `Fintype.card X` (one
rectangle per row). -/
theorem exists_blockyCover_card (M : X → Y → Bool) :
    ∃ B : Fin (Fintype.card X) → X → Y → Bool,
      (∀ i, IsBlocky (B i)) ∧ (∀ x y, M x y = true ↔ ∃ i, B i x y = true) := by
  classical
  let e : Fin (Fintype.card X) ≃ X := (Fintype.equivFin X).symm
  refine ⟨fun i x y ↦ decide (x = e i) && M (e i) y,
    fun i ↦ IsBlocky.rect (fun x ↦ decide (x = e i)) (fun y ↦ M (e i) y),
    fun x y ↦ ?_⟩
  constructor
  · intro hxy
    refine ⟨e.symm x, ?_⟩
    simp [hxy]
  · rintro ⟨i, hi⟩
    rw [Bool.and_eq_true_iff, decide_eq_true_eq] at hi
    rw [hi.1]
    exact hi.2

/-- Any blocky cover of size `r` gives `blockyCoverNumber M ≤ r`. -/
theorem blockyCoverNumber_le {M : X → Y → Bool} {r : ℕ} (B : Fin r → X → Y → Bool)
    (hB : ∀ i, IsBlocky (B i)) (hcov : ∀ x y, M x y = true ↔ ∃ i, B i x y = true) :
    blockyCoverNumber M ≤ r :=
  Nat.sInf_le ⟨B, hB, hcov⟩

/-- There exists an optimal blocky cover of `M` using `blockyCoverNumber M` blocky matrices. -/
theorem exists_blockyCover (M : X → Y → Bool) :
    ∃ B : Fin (blockyCoverNumber M) → X → Y → Bool,
      (∀ i, IsBlocky (B i)) ∧ (∀ x y, M x y = true ↔ ∃ i, B i x y = true) := by
  have hne : { r : ℕ | ∃ B : Fin r → X → Y → Bool,
      (∀ i, IsBlocky (B i)) ∧ (∀ x y, M x y = true ↔ ∃ i, B i x y = true) }.Nonempty :=
    ⟨Fintype.card X, exists_blockyCover_card M⟩
  exact Nat.sInf_mem hne

/-- `bc(M) = 0` iff `M` is the all-`false` matrix. -/
theorem blockyCoverNumber_eq_zero_iff {M : X → Y → Bool} :
    blockyCoverNumber M = 0 ↔ ∀ x y, M x y = false := by
  constructor
  · intro h0 x y
    obtain ⟨B, _, hcov⟩ := exists_blockyCover M
    cases hM : M x y
    · rfl
    · obtain ⟨i, _⟩ := (hcov x y).mp hM
      exact Fin.elim0 (h0 ▸ i)
  · intro hf
    exact Nat.eq_zero_of_le_zero
      (blockyCoverNumber_le (r := 0) Fin.elim0 (fun i ↦ i.elim0)
        (fun x y ↦ by rw [hf x y]; simp))

/-- Every blocky matrix has blocky cover number at most `1`. -/
theorem IsBlocky.blockyCoverNumber_le_one {B : X → Y → Bool} (hB : IsBlocky B) :
    blockyCoverNumber B ≤ 1 :=
  blockyCoverNumber_le (fun _ : Fin 1 ↦ B) (fun _ ↦ hB)
    (fun _ _ ↦ ⟨fun h ↦ ⟨0, h⟩, fun ⟨_, h⟩ ↦ h⟩)

/-- Every nonzero blocky matrix has blocky cover number equal to `1`. -/
theorem IsBlocky.blockyCoverNumber_eq_one {B : X → Y → Bool} (hB : IsBlocky B)
    (hne : ∃ x y, B x y = true) : blockyCoverNumber B = 1 := by
  have hle := hB.blockyCoverNumber_le_one
  have hne0 : blockyCoverNumber B ≠ 0 := by
    intro h0
    obtain ⟨x, y, hxy⟩ := hne
    rw [blockyCoverNumber_eq_zero_iff.mp h0 x y] at hxy
    cases hxy
  omega

/-- Taking any submatrix (or duplicating/permuting rows and columns) does not increase `bc(M)`. -/
theorem blockyCoverNumber_comap_le [Fintype X'] [Fintype Y'] (M : X → Y → Bool)
    (f : X' → X) (g : Y' → Y) :
    blockyCoverNumber (fun x y ↦ M (f x) (g y)) ≤ blockyCoverNumber M := by
  obtain ⟨B, hB, hcov⟩ := exists_blockyCover M
  exact blockyCoverNumber_le (fun i x y ↦ B i (f x) (g y))
    (fun i ↦ (hB i).comap f g) (fun x y ↦ hcov (f x) (g y))

/-- Nondeterministic `Equality`-oracle complexity is at most `⌈log₂ bc(A)⌉ + 1` (selecting one of
`bc(A) ≤ 2 ^ ⌈log₂ bc(A)⌉` blocky matrices nondeterministically and verifying it with one
`Equality` query). -/
theorem ndEqOracleComplexity_le_clog_blockyCoverNumber_add_one (A : X → Y → Bool) :
    ndEqOracleComplexity A ≤ Nat.clog 2 (blockyCoverNumber A) + 1 := by
  set r := blockyCoverNumber A
  set m := Nat.clog 2 r
  have hr : r ≤ 2 ^ m := Nat.le_pow_clog (by norm_num) r
  obtain ⟨B, hB, hcov⟩ := exists_blockyCover A
  let M : Fin (2 ^ m) → X → Y → Bool := fun i ↦
    if h : i.1 < r then B ⟨i.1, h⟩ else fun _ _ ↦ false
  refine ndEqOracleComplexity_le (m := m) (d := 1)
    (hasNdEqCover_iff.mpr ⟨M, fun i ↦ ?_, fun x y ↦ ?_⟩)
  · dsimp only [M]
    by_cases h : i.1 < r
    · simp only [h, ↓reduceDIte]
      exact (hB ⟨i.1, h⟩).eqOracleComplexity_le_one
    · simp only [h, ↓reduceDIte]
      exact IsBlocky.const_false.eqOracleComplexity_le_one
  · rw [hcov]
    constructor
    · rintro ⟨j, hj⟩
      refine ⟨⟨j.1, j.2.trans_le hr⟩, ?_⟩
      dsimp only [M]
      have hjr : j.1 < r := j.2
      simp only [hjr, ↓reduceDIte]
      exact hj
    · rintro ⟨i, hi⟩
      dsimp only [M] at hi
      by_cases h : i.1 < r
      · simp only [h, ↓reduceDIte] at hi
        exact ⟨⟨i.1, h⟩, hi⟩
      · simp only [h, ↓reduceDIte] at hi
        cases hi

/-- Number `α(A)` of `1`-valued entries of a finite Boolean matrix `A : X → Y → Bool`. -/
@[expose]
def onesCount (A : X → Y → Bool) : ℕ :=
  (Finset.univ.filter fun p : X × Y ↦ A p.1 p.2 = true).card

/-- A combinatorial rectangle `U × V` is `1`-chromatic in `A` if `A x y = true` on `U × V`. -/
@[expose]
def IsMonoRect (A : X → Y → Bool) (U : Finset X) (V : Finset Y) : Prop :=
  ∀ x ∈ U, ∀ y ∈ V, A x y = true

/-- Maximum area `β(A) = max { |U| * |V| | U × V is 1-chromatic in A }`. -/
noncomputable def maxMonoRectArea (A : X → Y → Bool) : ℕ := by
  classical
  exact (Finset.univ : Finset (Finset X × Finset Y)).sup
    (fun p ↦ if IsMonoRect A p.1 p.2 then p.1.card * p.2.card else 0)

/-- Every `1`-chromatic rectangle `U × V` of `A` has area `|U| * |V| ≤ maxMonoRectArea A`. -/
theorem card_mul_card_le_maxMonoRectArea {A : X → Y → Bool} {U : Finset X} {V : Finset Y}
    (h : IsMonoRect A U V) : U.card * V.card ≤ maxMonoRectArea A := by
  classical
  have hle := Finset.le_sup
    (f := fun p : Finset X × Finset Y ↦ if IsMonoRect A p.1 p.2 then p.1.card * p.2.card else 0)
    (Finset.mem_univ (U, V))
  simpa [maxMonoRectArea, h] using hle

/-- Bounding every `1`-chromatic rectangle's area by `b` yields `maxMonoRectArea A ≤ b`. -/
theorem maxMonoRectArea_le {A : X → Y → Bool} {b : ℕ}
    (h : ∀ U V, IsMonoRect A U V → U.card * V.card ≤ b) :
    maxMonoRectArea A ≤ b := by
  classical
  refine Finset.sup_le (fun p _ ↦ ?_)
  split_ifs with hp
  · exact h p.1 p.2 hp
  · exact Nat.zero_le b

/-- The Pitassi–Shirley–Shraibman rectangle ratio `maxrect(A) = α(A) / (|X| * √β(A))` of a square
Boolean matrix `A : X → X → Bool`. -/
@[expose]
noncomputable def maxRect (A : X → X → Bool) : ℝ :=
  (onesCount A : ℝ) / ((Fintype.card X : ℝ) * √(maxMonoRectArea A : ℝ))

private theorem onesCount_eq_sum_disjoint_rects {B : X → Y → Bool} {m : ℕ}
    (U : Fin m → Finset X) (V : Fin m → Finset Y)
    (hdU : ∀ i j, i ≠ j → Disjoint (U i) (U j))
    (hB : ∀ x y, B x y = true ↔ ∃ j, x ∈ U j ∧ y ∈ V j) :
    onesCount B = ∑ j : Fin m, (U j).card * (V j).card := by
  classical
  have heq : Finset.univ.filter (fun p : X × Y ↦ B p.1 p.2 = true) =
      Finset.univ.biUnion (fun j : Fin m ↦ U j ×ˢ V j) := by
    ext ⟨x, y⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
      Finset.mem_product]
    exact hB x y
  rw [onesCount, heq, Finset.card_biUnion (fun j₁ _ j₂ _ hne ↦ by
    change Disjoint (U j₁ ×ˢ V j₁) (U j₂ ×ˢ V j₂)
    rw [Finset.disjoint_left]
    intro ⟨x, y⟩ h₁ h₂
    simp only [Finset.mem_product] at h₁ h₂
    exact Finset.disjoint_left.mp (hdU j₁ j₂ hne) h₁.1 h₂.1)]
  exact Finset.sum_congr rfl (fun j _ ↦ Finset.card_product _ _)

/-- Short-vs.-narrow rectangle counting bound for any blocky cover: if every `1`-chromatic
rectangle `U × V` of `A` satisfies `|U| ≤ s ∨ |V| ≤ s` (with `s ≥ 0`), then
`onesCount A ≤ (card X + card Y) * blockyCoverNumber A * s`. -/
theorem onesCount_le_sum_card_mul_bc_of_monoRect_bound {A : X → Y → Bool} {s : ℝ} (hs : 0 ≤ s)
    (hrect : ∀ U V, IsMonoRect A U V → (U.card : ℝ) ≤ s ∨ (V.card : ℝ) ≤ s) :
    (onesCount A : ℝ) ≤
      ((Fintype.card X : ℝ) + Fintype.card Y) * (blockyCoverNumber A : ℝ) * s := by
  classical
  set K := blockyCoverNumber A
  obtain ⟨B, hB, hcov⟩ := exists_blockyCover A
  have hB_bound : ∀ i : Fin K,
      (onesCount (B i) : ℝ) ≤ ((Fintype.card X : ℝ) + Fintype.card Y) * s := by
    intro i
    obtain ⟨m, U, V, hdU, _, hsumU, hsumV, hBi⟩ := (hB i).disjoint_rectangles
    have hmono : ∀ j : Fin m, IsMonoRect A (U j) (V j) :=
      fun j x hx y hy ↦ (hcov x y).mpr ⟨i, (hBi x y).mpr ⟨j, hx, hy⟩⟩
    have hones : onesCount (B i) = ∑ j : Fin m, (U j).card * (V j).card :=
      onesCount_eq_sum_disjoint_rects U V hdU hBi
    rw [hones, Nat.cast_sum]
    calc ∑ j : Fin m, (((U j).card * (V j).card : ℕ) : ℝ)
        ≤ ∑ j : Fin m, (s * ((V j).card : ℝ) + ((U j).card : ℝ) * s) := by
          refine Finset.sum_le_sum (fun j _ ↦ ?_)
          rw [Nat.cast_mul]
          rcases hrect (U j) (V j) (hmono j) with hU | hV
          · have h1 : ((U j).card : ℝ) * (V j).card ≤ s * (V j).card :=
              mul_le_mul_of_nonneg_right hU (Nat.cast_nonneg _)
            linarith [mul_nonneg (Nat.cast_nonneg (U j).card) hs]
          · have h2 : ((U j).card : ℝ) * (V j).card ≤ (U j).card * s :=
              mul_le_mul_of_nonneg_left hV (Nat.cast_nonneg _)
            linarith [mul_nonneg hs (Nat.cast_nonneg (V j).card)]
      _ = ((∑ j : Fin m, ((V j).card : ℝ)) + ∑ j : Fin m, ((U j).card : ℝ)) * s := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]; ring
      _ ≤ ((Fintype.card Y : ℝ) + Fintype.card X) * s := by
          refine mul_le_mul_of_nonneg_right (add_le_add ?_ ?_) hs
          · exact_mod_cast hsumV
          · exact_mod_cast hsumU
      _ = ((Fintype.card X : ℝ) + Fintype.card Y) * s := by ring
  have hcover_card : onesCount A ≤ ∑ i : Fin K, onesCount (B i) := by
    have hsub : Finset.univ.filter (fun p : X × Y ↦ A p.1 p.2 = true) ⊆
        Finset.univ.biUnion (fun i : Fin K ↦
          Finset.univ.filter fun p : X × Y ↦ B i p.1 p.2 = true) := by
      intro ⟨x, y⟩ hxy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion] at hxy ⊢
      exact (hcov x y).mp hxy
    exact (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  calc (onesCount A : ℝ)
      ≤ ∑ i : Fin K, (onesCount (B i) : ℝ) := by exact_mod_cast hcover_card
    _ ≤ ∑ _i : Fin K, ((Fintype.card X : ℝ) + Fintype.card Y) * s :=
        Finset.sum_le_sum (fun i _ ↦ hB_bound i)
    _ = ((Fintype.card X : ℝ) + Fintype.card Y) * (K : ℝ) * s := by simp; ring

/-- Strict short-vs.-narrow existence lemma: every nonzero square Boolean matrix `A : X → X → Bool`
contains a `1`-chromatic rectangle `U × V` with both `|U|` and `|V|` at least
`onesCount A / (2 * card X * blockyCoverNumber A)`. -/
theorem exists_large_monoRect (A : X → X → Bool) (hne : ∃ x y, A x y = true) :
    ∃ U V : Finset X, IsMonoRect A U V ∧
      (onesCount A : ℝ) / (2 * Fintype.card X * blockyCoverNumber A) ≤ U.card ∧
      (onesCount A : ℝ) / (2 * Fintype.card X * blockyCoverNumber A) ≤ V.card := by
  classical
  by_contra hno
  push Not at hno
  set K := blockyCoverNumber A
  set N := Fintype.card X
  set t : ℝ := (onesCount A : ℝ) / (2 * (N : ℝ) * (K : ℝ))
  obtain ⟨x₀, y₀, hx₀⟩ := hne
  have hN : 0 < N := Fintype.card_pos_iff.mpr ⟨x₀⟩
  have hK : 0 < K := Nat.pos_of_ne_zero (fun h0 ↦ by
    rw [blockyCoverNumber_eq_zero_iff.mp h0 x₀ y₀] at hx₀; cases hx₀)
  have hones_pos : 0 < onesCount A :=
    Finset.card_pos.mpr ⟨(x₀, y₀), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx₀⟩⟩
  have ht_pos : 0 < t := by positivity
  obtain ⟨B, hB, hcov⟩ := exists_blockyCover A
  have hB_lt : ∀ i : Fin K, (onesCount (B i) : ℝ) ≤ 2 * (N : ℝ) * t ∧
      (0 < onesCount (B i) → (onesCount (B i) : ℝ) < 2 * (N : ℝ) * t) := by
    intro i
    obtain ⟨m, U, V, hdU, _, hsumU, hsumV, hBi⟩ := (hB i).disjoint_rectangles
    have hmono : ∀ j : Fin m, IsMonoRect A (U j) (V j) :=
      fun j x hx y hy ↦ (hcov x y).mpr ⟨i, (hBi x y).mpr ⟨j, hx, hy⟩⟩
    have hones : onesCount (B i) = ∑ j : Fin m, (U j).card * (V j).card :=
      onesCount_eq_sum_disjoint_rects U V hdU hBi
    have hterm_le : ∀ j : Fin m,
        ((U j).card : ℝ) * (V j).card ≤ t * (V j).card + (U j).card * t := by
      intro j
      by_cases hU : t ≤ (U j).card
      · have hV : ((V j).card : ℝ) < t := hno (U j) (V j) (hmono j) hU
        nlinarith [Nat.cast_nonneg (α := ℝ) (U j).card, Nat.cast_nonneg (α := ℝ) (V j).card]
      · push Not at hU
        nlinarith [Nat.cast_nonneg (α := ℝ) (U j).card, Nat.cast_nonneg (α := ℝ) (V j).card]
    have hterm_lt : ∀ j : Fin m, 0 < (U j).card * (V j).card →
        ((U j).card : ℝ) * (V j).card < t * (V j).card + (U j).card * t := by
      intro j hj
      have hUp : 0 < ((U j).card : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_mul_pos_right hj)
      have hVp : 0 < ((V j).card : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_mul_pos_left hj)
      by_cases hU : t ≤ (U j).card
      · have hV : ((V j).card : ℝ) < t := hno (U j) (V j) (hmono j) hU
        nlinarith
      · push Not at hU
        nlinarith
    have hrhs : ∑ j : Fin m, (t * ((V j).card : ℝ) + ((U j).card : ℝ) * t) ≤
        2 * (N : ℝ) * t := by
      calc ∑ j : Fin m, (t * ((V j).card : ℝ) + ((U j).card : ℝ) * t)
          = ((∑ j : Fin m, ((V j).card : ℝ)) + ∑ j : Fin m, ((U j).card : ℝ)) * t := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]; ring
        _ ≤ ((N : ℝ) + N) * t :=
            mul_le_mul_of_nonneg_right (add_le_add (by exact_mod_cast hsumV)
              (by exact_mod_cast hsumU)) ht_pos.le
        _ = 2 * (N : ℝ) * t := by ring
    refine ⟨?_, fun hpos ↦ ?_⟩
    · rw [hones, Nat.cast_sum]
      exact (Finset.sum_le_sum fun j _ ↦ by rw [Nat.cast_mul]; exact hterm_le j).trans hrhs
    · have hexj : ∃ j ∈ (Finset.univ : Finset (Fin m)), 0 < (U j).card * (V j).card := by
        by_contra hall
        push Not at hall
        have : onesCount (B i) = 0 := by
          rw [hones]
          exact Finset.sum_eq_zero (fun j hj ↦ Nat.eq_zero_of_le_zero (hall j hj))
        omega
      obtain ⟨j₀, hj₀, hjp⟩ := hexj
      rw [hones, Nat.cast_sum]
      have hstrict : ∑ j : Fin m, (((U j).card * (V j).card : ℕ) : ℝ) <
          ∑ j : Fin m, (t * ((V j).card : ℝ) + ((U j).card : ℝ) * t) :=
        Finset.sum_lt_sum (fun j _ ↦ by rw [Nat.cast_mul]; exact hterm_le j)
          ⟨j₀, hj₀, by rw [Nat.cast_mul]; exact hterm_lt j₀ hjp⟩
      exact hstrict.trans_le hrhs
  obtain ⟨i₀, hi₀⟩ := (hcov x₀ y₀).mp hx₀
  have hi₀_pos : 0 < onesCount (B i₀) :=
    Finset.card_pos.mpr ⟨(x₀, y₀), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi₀⟩⟩
  have hcover_card : onesCount A ≤ ∑ i : Fin K, onesCount (B i) := by
    have hsub : Finset.univ.filter (fun p : X × X ↦ A p.1 p.2 = true) ⊆
        Finset.univ.biUnion (fun i : Fin K ↦
          Finset.univ.filter fun p : X × X ↦ B i p.1 p.2 = true) := by
      intro ⟨x, y⟩ hxy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion] at hxy ⊢
      exact (hcov x y).mp hxy
    exact (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  have hlt : (onesCount A : ℝ) < (onesCount A : ℝ) := by
    calc (onesCount A : ℝ)
        ≤ ∑ i : Fin K, (onesCount (B i) : ℝ) := by exact_mod_cast hcover_card
      _ < ∑ _i : Fin K, 2 * (N : ℝ) * t :=
          Finset.sum_lt_sum (fun i _ ↦ (hB_lt i).1)
            ⟨i₀, Finset.mem_univ i₀, (hB_lt i₀).2 hi₀_pos⟩
      _ = (K : ℝ) * (2 * (N : ℝ) * t) := by simp
      _ = onesCount A := by
          have hNK : (2 * (N : ℝ) * (K : ℝ)) ≠ 0 := by positivity
          dsimp [t]; field_simp [hNK]
  exact lt_irrefl _ hlt

/-- **Rectangle lower bound on blocky cover number**:
for every finite square Boolean matrix `A : X → X → Bool`,
`maxRect A ≤ 2 * blockyCoverNumber A`.
-/
theorem maxRect_le_two_mul_blockyCoverNumber (A : X → X → Bool) :
    maxRect A ≤ 2 * (blockyCoverNumber A : ℝ) := by
  set β : ℝ := (maxMonoRectArea A : ℝ)
  set N : ℝ := (Fintype.card X : ℝ)
  have hdenom : 0 ≤ N * √β := mul_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _)
  rcases hdenom.eq_or_lt with h0 | hpos
  · rw [maxRect, ← h0, div_zero]
    positivity
  · rw [maxRect, div_le_iff₀ hpos]
    have hrect : ∀ U V : Finset X, IsMonoRect A U V →
        (U.card : ℝ) ≤ √β ∨ (V.card : ℝ) ≤ √β := by
      intro U V hUV
      by_contra h
      push Not at h
      have hmul : β < (U.card : ℝ) * V.card := by
        calc β = √β * √β := (Real.mul_self_sqrt (Nat.cast_nonneg _)).symm
          _ < (U.card : ℝ) * V.card :=
              mul_lt_mul'' h.1 h.2 (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      have hle : (U.card : ℝ) * V.card ≤ β := by
        have hnat : ((U.card * V.card : ℕ) : ℝ) ≤ β :=
          Nat.cast_le.mpr (card_mul_card_le_maxMonoRectArea hUV)
        rwa [Nat.cast_mul] at hnat
      linarith
    calc (onesCount A : ℝ)
        ≤ (N + N) * (blockyCoverNumber A : ℝ) * √β :=
          onesCount_le_sum_card_mul_bc_of_monoRect_bound (Real.sqrt_nonneg _) hrect
      _ = 2 * (blockyCoverNumber A : ℝ) * (N * √β) := by ring

end BlockyMatrices

section FractionalBlockyCover

variable {X Y X' Y' : Type*} [Fintype X] [Fintype Y]

/-- A fractional blocky cover of a finite Boolean matrix `A : X → Y → Bool`: nonnegative weights
`weight i ≥ 0` on blocky matrices `mat i` whose weighted sum vanishes where `A x y = false` and is
at least `1` where `A x y = true`. -/
structure FractionalBlockyCover (A : X → Y → Bool) where
  /-- Number of blocky matrices in the cover. -/
  size : ℕ
  /-- Nonnegative weight attached to each blocky matrix. -/
  weight : Fin size → ℝ
  /-- Indexed family of blocky matrices. -/
  mat : Fin size → X → Y → Bool
  /-- Every weight is nonnegative. -/
  weight_nonneg : ∀ i, 0 ≤ weight i
  /-- Every matrix in the family is blocky. -/
  mat_blocky : ∀ i, IsBlocky (mat i)
  /-- Zero-entries of `A` receive weighted sum `0`. -/
  sum_eq_zero_of_false : ∀ x y, A x y = false →
    ∑ i, weight i * (if mat i x y = true then (1 : ℝ) else 0) = 0
  /-- One-entries of `A` receive weighted sum at least `1`. -/
  one_le_sum_of_true : ∀ x y, A x y = true →
    1 ≤ ∑ i, weight i * (if mat i x y = true then (1 : ℝ) else 0)

namespace FractionalBlockyCover

/-- Total weight `∑ i, weight i` of a fractional blocky cover. -/
def totalWeight {A : X → Y → Bool} (C : FractionalBlockyCover A) : ℝ :=
  ∑ i, C.weight i

/-- Total weight is nonnegative. -/
theorem totalWeight_nonneg {A : X → Y → Bool} (C : FractionalBlockyCover A) :
    0 ≤ C.totalWeight :=
  Finset.sum_nonneg (fun i _ ↦ C.weight_nonneg i)

/-- Every matrix with a strictly positive weight in `C` is false on every `0`-entry of `A`. -/
theorem mat_eq_false_of_weight_pos {A : X → Y → Bool} (C : FractionalBlockyCover A)
    {i : Fin C.size} (hi : 0 < C.weight i) {x : X} {y : Y} (hxy : A x y = false) :
    C.mat i x y = false := by
  have h0 := C.sum_eq_zero_of_false x y hxy
  rw [Finset.sum_eq_zero_iff_of_nonneg
    (fun j _ ↦ mul_nonneg (C.weight_nonneg j) (by cases C.mat j x y <;> norm_num))] at h0
  have hterm := h0 i (Finset.mem_univ i)
  cases hm : C.mat i x y
  · rfl
  · simp [hm, hi.ne'] at hterm

/-- Any integral blocky cover yields a fractional blocky cover with unit weights. -/
def ofIntegral {A : X → Y → Bool} {r : ℕ} (B : Fin r → X → Y → Bool)
    (hB : ∀ i, IsBlocky (B i)) (hcov : ∀ x y, A x y = true ↔ ∃ i, B i x y = true) :
    FractionalBlockyCover A where
  size := r
  weight := fun _ ↦ 1
  mat := B
  weight_nonneg := fun _ ↦ zero_le_one
  mat_blocky := hB
  sum_eq_zero_of_false := fun x y hxy ↦ by
    refine Finset.sum_eq_zero (fun i _ ↦ ?_)
    have hf : B i x y = false :=
      Bool.eq_false_iff.mpr (fun h ↦ by rw [(hcov x y).mpr ⟨i, h⟩] at hxy; cases hxy)
    simp [hf]
  one_le_sum_of_true := fun x y hxy ↦ by
    obtain ⟨i₀, hi₀⟩ := (hcov x y).mp hxy
    have hterm : ∀ j : Fin r, 0 ≤ (1 : ℝ) * (if B j x y = true then (1 : ℝ) else 0) :=
      fun j ↦ by cases B j x y <;> norm_num
    calc (1 : ℝ) = (1 : ℝ) * (if B i₀ x y = true then (1 : ℝ) else 0) := by simp [hi₀]
      _ ≤ ∑ i : Fin r, (1 : ℝ) * (if B i x y = true then (1 : ℝ) else 0) :=
          Finset.single_le_sum (fun j _ ↦ hterm j) (Finset.mem_univ i₀)

@[simp]
theorem totalWeight_ofIntegral {A : X → Y → Bool} {r : ℕ} (B : Fin r → X → Y → Bool)
    (hB : ∀ i, IsBlocky (B i)) (hcov : ∀ x y, A x y = true ↔ ∃ i, B i x y = true) :
    (ofIntegral B hB hcov).totalWeight = r := by
  unfold totalWeight ofIntegral
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  exact congr_arg (Nat.cast (R := ℝ)) (Fintype.card_fin r)

/-- Reindex a fractional blocky cover constructed over an arbitrary finite index type `κ`. -/
noncomputable def ofFintype {κ : Type*} [Fintype κ] {A : X → Y → Bool}
    (w : κ → ℝ) (B : κ → X → Y → Bool) (hw : ∀ k, 0 ≤ w k) (hB : ∀ k, IsBlocky (B k))
    (h0 : ∀ x y, A x y = false → ∑ k, w k * (if B k x y = true then (1 : ℝ) else 0) = 0)
    (h1 : ∀ x y, A x y = true → 1 ≤ ∑ k, w k * (if B k x y = true then (1 : ℝ) else 0)) :
    FractionalBlockyCover A :=
  let e : Fin (Fintype.card κ) ≃ κ := (Fintype.equivFin κ).symm
  { size := Fintype.card κ
    weight := fun i ↦ w (e i)
    mat := fun i ↦ B (e i)
    weight_nonneg := fun i ↦ hw (e i)
    mat_blocky := fun i ↦ hB (e i)
    sum_eq_zero_of_false := fun x y hxy ↦ by
      rw [Equiv.sum_comp e (fun k ↦ w k * if B k x y = true then (1 : ℝ) else 0)]
      exact h0 x y hxy
    one_le_sum_of_true := fun x y hxy ↦ by
      rw [Equiv.sum_comp e (fun k ↦ w k * if B k x y = true then (1 : ℝ) else 0)]
      exact h1 x y hxy }

@[simp]
theorem totalWeight_ofFintype {κ : Type*} [Fintype κ] {A : X → Y → Bool}
    (w : κ → ℝ) (B : κ → X → Y → Bool) (hw : ∀ k, 0 ≤ w k) (hB : ∀ k, IsBlocky (B k))
    (h0 : ∀ x y, A x y = false → ∑ k, w k * (if B k x y = true then (1 : ℝ) else 0) = 0)
    (h1 : ∀ x y, A x y = true → 1 ≤ ∑ k, w k * (if B k x y = true then (1 : ℝ) else 0)) :
    (ofFintype w B hw hB h0 h1).totalWeight = ∑ k, w k :=
  Equiv.sum_comp (Fintype.equivFin κ).symm w

/-- Pull back a fractional blocky cover along local maps `f : X' → X` and `g : Y' → Y`. -/
def comap [Fintype X'] [Fintype Y'] {A : X → Y → Bool} (C : FractionalBlockyCover A)
    (f : X' → X) (g : Y' → Y) : FractionalBlockyCover (fun x y ↦ A (f x) (g y)) where
  size := C.size
  weight := C.weight
  mat := fun i x y ↦ C.mat i (f x) (g y)
  weight_nonneg := C.weight_nonneg
  mat_blocky := fun i ↦ (C.mat_blocky i).comap f g
  sum_eq_zero_of_false := fun x y hxy ↦ C.sum_eq_zero_of_false (f x) (g y) hxy
  one_le_sum_of_true := fun x y hxy ↦ C.one_le_sum_of_true (f x) (g y) hxy

end FractionalBlockyCover

/-- Fractional blocky cover number `fbc(A)`: infimum of `C.totalWeight` over all fractional blocky
covers `C` of `A`. -/
noncomputable def fractionalBlockyCoverNumber (A : X → Y → Bool) : ℝ :=
  sInf { c : ℝ | ∃ C : FractionalBlockyCover A, C.totalWeight = c }

private theorem fbc_bddBelow (A : X → Y → Bool) :
    BddBelow { c : ℝ | ∃ C : FractionalBlockyCover A, C.totalWeight = c } :=
  ⟨0, fun _ ⟨C, hC⟩ ↦ hC ▸ C.totalWeight_nonneg⟩

private theorem fbc_nonempty (A : X → Y → Bool) :
    { c : ℝ | ∃ C : FractionalBlockyCover A, C.totalWeight = c }.Nonempty := by
  obtain ⟨B, hB, hcov⟩ := exists_blockyCover A
  exact ⟨_, FractionalBlockyCover.ofIntegral B hB hcov, rfl⟩

/-- Any fractional blocky cover `C` of `A` bounds `fbc(A) ≤ C.totalWeight`. -/
theorem fractionalBlockyCoverNumber_le {A : X → Y → Bool} (C : FractionalBlockyCover A) :
    fractionalBlockyCoverNumber A ≤ C.totalWeight :=
  csInf_le (fbc_bddBelow A) ⟨C, rfl⟩

/-- Lower-bound principle for `fractionalBlockyCoverNumber A`. -/
theorem le_fractionalBlockyCoverNumber_iff {A : X → Y → Bool} {b : ℝ} :
    b ≤ fractionalBlockyCoverNumber A ↔ ∀ C : FractionalBlockyCover A, b ≤ C.totalWeight := by
  rw [fractionalBlockyCoverNumber, le_csInf_iff (fbc_bddBelow A) (fbc_nonempty A)]
  exact ⟨fun h C ↦ h _ ⟨C, rfl⟩, fun h _ ⟨C, hC⟩ ↦ hC ▸ h C⟩

/-- For every `ε > 0`, there is a fractional blocky cover of total weight `< fbc(A) + ε`. -/
theorem exists_fractionalBlockyCover_lt_add {A : X → Y → Bool} {ε : ℝ} (hε : 0 < ε) :
    ∃ C : FractionalBlockyCover A, C.totalWeight < fractionalBlockyCoverNumber A + ε := by
  obtain ⟨_, ⟨C, rfl⟩, hlt⟩ :=
    exists_lt_of_csInf_lt (fbc_nonempty A) (lt_add_of_pos_right _ hε)
  exact ⟨C, hlt⟩

/-- `fbc(A)` is always nonnegative. -/
theorem fractionalBlockyCoverNumber_nonneg (A : X → Y → Bool) :
    0 ≤ fractionalBlockyCoverNumber A :=
  le_fractionalBlockyCoverNumber_iff.mpr FractionalBlockyCover.totalWeight_nonneg

/-- `fbc(A) ≤ bc(A)` for every finite Boolean matrix `A`. -/
theorem fractionalBlockyCoverNumber_le_blockyCoverNumber (A : X → Y → Bool) :
    fractionalBlockyCoverNumber A ≤ blockyCoverNumber A := by
  obtain ⟨B, hB, hcov⟩ := exists_blockyCover A
  simpa using fractionalBlockyCoverNumber_le (FractionalBlockyCover.ofIntegral B hB hcov)

/-- `fbc` of the all-`false` matrix is `0`. -/
@[simp]
theorem fractionalBlockyCoverNumber_false :
    fractionalBlockyCoverNumber (fun (_ : X) (_ : Y) ↦ false) = 0 := by
  apply le_antisymm _ (fractionalBlockyCoverNumber_nonneg _)
  exact (fractionalBlockyCoverNumber_le_blockyCoverNumber _).trans
    (by simp [blockyCoverNumber_eq_zero_iff.mpr fun _ _ ↦ rfl])

/-- If `A` has at least one `true` entry, then `1 ≤ fbc(A)`. -/
theorem one_le_fractionalBlockyCoverNumber {A : X → Y → Bool} (h : ∃ x y, A x y = true) :
    1 ≤ fractionalBlockyCoverNumber A := by
  obtain ⟨x, y, hxy⟩ := h
  refine le_fractionalBlockyCoverNumber_iff.mpr (fun C ↦ ?_)
  calc (1 : ℝ) ≤ ∑ i, C.weight i * (if C.mat i x y = true then 1 else 0) :=
        C.one_le_sum_of_true x y hxy
    _ ≤ ∑ i, C.weight i := Finset.sum_le_sum (fun i _ ↦ by
        cases C.mat i x y <;> simp [C.weight_nonneg i])
    _ = C.totalWeight := rfl

/-- Every blocky matrix has `fbc(B) ≤ 1`. -/
theorem IsBlocky.fractionalBlockyCoverNumber_le_one {B : X → Y → Bool} (hB : IsBlocky B) :
    fractionalBlockyCoverNumber B ≤ 1 :=
  (fractionalBlockyCoverNumber_le_blockyCoverNumber B).trans
    (by exact_mod_cast hB.blockyCoverNumber_le_one)

/-- Pulling back rows and columns does not increase `fbc(A)`. -/
theorem fractionalBlockyCoverNumber_comap_le [Fintype X'] [Fintype Y'] (A : X → Y → Bool)
    (f : X' → X) (g : Y' → Y) :
    fractionalBlockyCoverNumber (fun x y ↦ A (f x) (g y)) ≤ fractionalBlockyCoverNumber A :=
  le_fractionalBlockyCoverNumber_iff.mpr (fun C ↦ fractionalBlockyCoverNumber_le (C.comap f g))

/-- **Complement property of fractional blocky covers (sharp constant `2`)**: for every blocky
matrix `B : X → Y → Bool`, `fbc(J - B) ≤ 2` (sampling uniform Boolean colourings `s` and forming
symmetric bipartitions `s(fa x) != s(fb y)`, which cover every non-equal pair with probability
`1/2`). -/
theorem IsBlocky.fractionalBlockyCoverNumber_not_le_two {B : X → Y → Bool} (hB : IsBlocky B) :
    fractionalBlockyCoverNumber (fun x y ↦ !B x y) ≤ 2 := by
  classical
  obtain ⟨m, _, a, b, hab⟩ := hB
  let fa : X → Fin m ⊕ Bool := fun x ↦ Option.rec (Sum.inr false) Sum.inl (a x)
  let fb : Y → Fin m ⊕ Bool := fun y ↦ Option.rec (Sum.inr true) Sum.inl (b y)
  have hne_iff : ∀ x y, (!B x y) = true ↔ fa x ≠ fb y := by
    intro x y
    cases hBxy : B x y
    · simp only [Bool.not_false, true_iff]
      intro heq
      have htrue : B x y = true := by
        rw [hab]
        cases ha : a x <;> cases hb : b y <;> simp_all [fa, fb]
      rw [hBxy] at htrue; cases htrue
    · obtain ⟨c, hax, hby⟩ := (hab x y).mp hBxy
      simp [fa, fb, hax, hby]
  let K : ℝ := (Fintype.card (Fin m ⊕ Bool → Bool) : ℝ)
  have hK : 0 < K := Nat.cast_pos.mpr Fintype.card_pos
  let w : (Fin m ⊕ Bool → Bool) → ℝ := fun _ ↦ 2 / K
  let M : (Fin m ⊕ Bool → Bool) → X → Y → Bool := fun s x y ↦ s (fa x) != s (fb y)
  let C := FractionalBlockyCover.ofFintype (A := fun x y ↦ !B x y) w M (fun _ ↦ by positivity)
    (fun s ↦ IsBlocky.bipartition (fun x ↦ s (fa x)) (fun y ↦ s (fb y)))
    (fun x y hxy ↦ by
      have heq : fa x = fb y := by
        by_contra hne
        have ht := (hne_iff x y).mpr hne
        rw [hxy] at ht; cases ht
      exact Finset.sum_eq_zero (fun s _ ↦ by simp [M, heq]))
    (fun x y hxy ↦ by
      have hne : fa x ≠ fb y := (hne_iff x y).mp hxy
      let flip : (Fin m ⊕ Bool → Bool) → (Fin m ⊕ Bool → Bool) :=
        fun s ↦ Function.update s (fa x) (!s (fa x))
      let good := (Finset.univ : Finset (Fin m ⊕ Bool → Bool)).filter
        (fun s ↦ M s x y = true)
      let bad := (Finset.univ : Finset (Fin m ⊕ Bool → Bool)).filter
        (fun s ↦ M s x y = false)
      have hcard_eq : good.card = bad.card := by
        refine Finset.card_bij (fun s _ ↦ flip s) (fun s hs ↦ ?_) (fun s₁ _ s₂ _ h ↦ ?_)
          (fun s hs ↦ ⟨flip s, ?_, ?_⟩)
        · simp only [good, bad, Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
          simp only [M, flip, Function.update_self, Function.update_of_ne hne.symm] at hs ⊢
          cases h1 : s (fa x) <;> cases h2 : s (fb y) <;> simp_all
        · have hinv : ∀ t, flip (flip t) = t := fun t ↦ by
            ext u; by_cases hu : u = fa x <;> simp [flip, hu]
          simpa [hinv] using congr_arg flip h
        · simp only [good, bad, Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
          simp only [M, flip, Function.update_self, Function.update_of_ne hne.symm] at hs ⊢
          cases h1 : s (fa x) <;> cases h2 : s (fb y) <;> simp_all
        · ext u; by_cases hu : u = fa x <;> simp [flip, hu]
      have htotal : good.card + bad.card = Fintype.card (Fin m ⊕ Bool → Bool) := by
        have hdisj : Disjoint good bad :=
          Finset.disjoint_filter.mpr (fun _ _ h₁ h₂ ↦ by rw [h₁] at h₂; cases h₂)
        have hunion : good ∪ bad = Finset.univ := by
          ext s
          simp only [good, bad, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
          cases M s x y <;> simp
        rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_univ]
      have hgood : (2 : ℝ) * (good.card : ℝ) = K := by
        have h2 : ((2 * good.card : ℕ) : ℝ) = K :=
          congr_arg (Nat.cast (R := ℝ)) (by omega : 2 * good.card = Fintype.card _)
        simpa [Nat.cast_mul] using h2
      have hsum : ∑ s : Fin m ⊕ Bool → Bool, w s * (if M s x y = true then (1 : ℝ) else 0) =
          (2 / K) * (good.card : ℝ) := by
        simp only [w, ← Finset.mul_sum]
        congr 1
        rw [Finset.sum_boole]
      rw [hsum]
      refine le_of_eq ?_
      field_simp [hK.ne']
      linarith)
  calc fractionalBlockyCoverNumber (fun x y ↦ !B x y)
      ≤ C.totalWeight := fractionalBlockyCoverNumber_le C
    _ = ∑ _s : Fin m ⊕ Bool → Bool, (2 / K) := FractionalBlockyCover.totalWeight_ofFintype ..
    _ = K * (2 / K) := by simp [K]
    _ = 2 := mul_div_cancel₀ 2 hK.ne'

/-- **Complement property of fractional blocky covers**: for every blocky matrix `B`,
`fbc(J - B) ≤ 4`. -/
theorem IsBlocky.fractionalBlockyCoverNumber_not_le_four {B : X → Y → Bool} (hB : IsBlocky B) :
    fractionalBlockyCoverNumber (fun x y ↦ !B x y) ≤ 4 :=
  hB.fractionalBlockyCoverNumber_not_le_two.trans (by norm_num)

/-- **Submultiplicativity of `fbc` under entrywise AND**:
`fbc(P ∧ Q) ≤ fbc(P) * fbc(Q)`. -/
theorem fractionalBlockyCoverNumber_and_le (P Q : X → Y → Bool) :
    fractionalBlockyCoverNumber (fun x y ↦ P x y && Q x y) ≤
      fractionalBlockyCoverNumber P * fractionalBlockyCoverNumber Q := by
  have hprod : ∀ (C₁ : FractionalBlockyCover P) (C₂ : FractionalBlockyCover Q),
      fractionalBlockyCoverNumber (fun x y ↦ P x y && Q x y) ≤
        C₁.totalWeight * C₂.totalWeight := by
    intro C₁ C₂
    let C := FractionalBlockyCover.ofFintype
      (fun p : Fin C₁.size × Fin C₂.size ↦ C₁.weight p.1 * C₂.weight p.2)
      (fun p x y ↦ C₁.mat p.1 x y && C₂.mat p.2 x y)
      (fun p ↦ mul_nonneg (C₁.weight_nonneg p.1) (C₂.weight_nonneg p.2))
      (fun p ↦ (C₁.mat_blocky p.1).and (C₂.mat_blocky p.2))
      (fun x y hxy ↦ by
        have hfac : ∑ p : Fin C₁.size × Fin C₂.size,
            C₁.weight p.1 * C₂.weight p.2 *
              (if (C₁.mat p.1 x y && C₂.mat p.2 x y) = true then (1 : ℝ) else 0) =
            (∑ i, C₁.weight i * if C₁.mat i x y = true then (1 : ℝ) else 0) *
              (∑ j, C₂.weight j * if C₂.mat j x y = true then (1 : ℝ) else 0) := by
          rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
          refine Finset.sum_congr rfl (fun i _ ↦ Finset.sum_congr rfl (fun j _ ↦ ?_))
          cases C₁.mat i x y <;> cases C₂.mat j x y <;> simp
        rw [hfac]
        rcases Bool.and_eq_false_iff.mp hxy with hP | hQ
        · rw [C₁.sum_eq_zero_of_false x y hP, zero_mul]
        · rw [C₂.sum_eq_zero_of_false x y hQ, mul_zero])
      (fun x y hxy ↦ by
        have hfac : ∑ p : Fin C₁.size × Fin C₂.size,
            C₁.weight p.1 * C₂.weight p.2 *
              (if (C₁.mat p.1 x y && C₂.mat p.2 x y) = true then (1 : ℝ) else 0) =
            (∑ i, C₁.weight i * if C₁.mat i x y = true then (1 : ℝ) else 0) *
              (∑ j, C₂.weight j * if C₂.mat j x y = true then (1 : ℝ) else 0) := by
          rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
          refine Finset.sum_congr rfl (fun i _ ↦ Finset.sum_congr rfl (fun j _ ↦ ?_))
          cases C₁.mat i x y <;> cases C₂.mat j x y <;> simp
        rw [hfac]
        obtain ⟨hP, hQ⟩ := Bool.and_eq_true_iff.mp hxy
        simpa using mul_le_mul (C₁.one_le_sum_of_true x y hP) (C₂.one_le_sum_of_true x y hQ)
          zero_le_one (zero_le_one.trans (C₁.one_le_sum_of_true x y hP)))
    calc fractionalBlockyCoverNumber (fun x y ↦ P x y && Q x y)
        ≤ C.totalWeight := fractionalBlockyCoverNumber_le C
      _ = ∑ p : Fin C₁.size × Fin C₂.size, C₁.weight p.1 * C₂.weight p.2 :=
          FractionalBlockyCover.totalWeight_ofFintype ..
      _ = C₁.totalWeight * C₂.totalWeight := by
          rw [Fintype.sum_prod_type, FractionalBlockyCover.totalWeight,
            FractionalBlockyCover.totalWeight, Finset.sum_mul_sum]
  by_cases hQ0 : ∀ x y, Q x y = false
  · have hPQ : (fun x y ↦ P x y && Q x y) = fun _ _ ↦ false := by ext x y; simp [hQ0 x y]
    have hQ : Q = fun _ _ ↦ false := by ext x y; exact hQ0 x y
    rw [hPQ, hQ, fractionalBlockyCoverNumber_false, mul_zero]
  · push Not at hQ0
    have hQpos : 0 < fractionalBlockyCoverNumber Q :=
      zero_lt_one.trans_le (one_le_fractionalBlockyCoverNumber
        (let ⟨x, y, h⟩ := hQ0; ⟨x, y, Bool.eq_true_of_not_eq_false h⟩))
    by_cases hP0 : ∀ x y, P x y = false
    · have hPQ : (fun x y ↦ P x y && Q x y) = fun _ _ ↦ false := by ext x y; simp [hP0 x y]
      have hP : P = fun _ _ ↦ false := by ext x y; exact hP0 x y
      rw [hPQ, hP, fractionalBlockyCoverNumber_false, zero_mul]
    · push Not at hP0
      have hPpos : 0 < fractionalBlockyCoverNumber P :=
        zero_lt_one.trans_le (one_le_fractionalBlockyCoverNumber
          (let ⟨x, y, h⟩ := hP0; ⟨x, y, Bool.eq_true_of_not_eq_false h⟩))
      rw [← div_le_iff₀' hPpos]
      refine le_fractionalBlockyCoverNumber_iff.mpr (fun C₂ ↦ ?_)
      have hC₂ : 0 < C₂.totalWeight := hQpos.trans_le (fractionalBlockyCoverNumber_le C₂)
      rw [div_le_iff₀' hPpos, ← div_le_iff₀ hC₂]
      refine le_fractionalBlockyCoverNumber_iff.mpr (fun C₁ ↦ ?_)
      rw [div_le_iff₀ hC₂]
      exact hprod C₁ C₂

/-- **Subadditivity of `fbc` under entrywise OR**: `fbc(P ∨ Q) ≤ fbc(P) + fbc(Q)`. -/
theorem fractionalBlockyCoverNumber_or_le (P Q : X → Y → Bool) :
    fractionalBlockyCoverNumber (fun x y ↦ P x y || Q x y) ≤
      fractionalBlockyCoverNumber P + fractionalBlockyCoverNumber Q := by
  refine le_of_forall_pos_lt_add (fun ε hε ↦ ?_)
  obtain ⟨C₁, hC₁⟩ := exists_fractionalBlockyCover_lt_add (A := P) (half_pos hε)
  obtain ⟨C₂, hC₂⟩ := exists_fractionalBlockyCover_lt_add (A := Q) (half_pos hε)
  let C := FractionalBlockyCover.ofFintype
    (Sum.elim C₁.weight C₂.weight)
    (Sum.elim C₁.mat C₂.mat)
    (fun s : Fin C₁.size ⊕ Fin C₂.size ↦ Sum.casesOn s C₁.weight_nonneg C₂.weight_nonneg)
    (fun s : Fin C₁.size ⊕ Fin C₂.size ↦ Sum.casesOn s C₁.mat_blocky C₂.mat_blocky)
    (fun x y hxy ↦ by
      obtain ⟨hP, hQ⟩ := Bool.or_eq_false_iff.mp hxy
      rw [Fintype.sum_sum_type]
      have h1 := C₁.sum_eq_zero_of_false x y hP
      have h2 := C₂.sum_eq_zero_of_false x y hQ
      change (∑ i, C₁.weight i * if C₁.mat i x y = true then (1 : ℝ) else 0) +
        (∑ j, C₂.weight j * if C₂.mat j x y = true then (1 : ℝ) else 0) = 0
      rw [h1, h2, add_zero])
    (fun x y hxy ↦ by
      rw [Fintype.sum_sum_type]
      change 1 ≤ (∑ i, C₁.weight i * if C₁.mat i x y = true then (1 : ℝ) else 0) +
        (∑ j, C₂.weight j * if C₂.mat j x y = true then (1 : ℝ) else 0)
      have hnn₁ : 0 ≤ ∑ i, C₁.weight i * if C₁.mat i x y = true then (1 : ℝ) else 0 :=
        Finset.sum_nonneg (fun i _ ↦ mul_nonneg (C₁.weight_nonneg i)
          (by cases C₁.mat i x y <;> norm_num))
      have hnn₂ : 0 ≤ ∑ j, C₂.weight j * if C₂.mat j x y = true then (1 : ℝ) else 0 :=
        Finset.sum_nonneg (fun j _ ↦ mul_nonneg (C₂.weight_nonneg j)
          (by cases C₂.mat j x y <;> norm_num))
      rcases Bool.or_eq_true_iff.mp hxy with hP | hQ
      · linarith [C₁.one_le_sum_of_true x y hP]
      · linarith [C₂.one_le_sum_of_true x y hQ])
  have htot : C.totalWeight = C₁.totalWeight + C₂.totalWeight := by
    rw [FractionalBlockyCover.totalWeight_ofFintype, Fintype.sum_sum_type]
    rfl
  calc fractionalBlockyCoverNumber (fun x y ↦ P x y || Q x y)
      ≤ C.totalWeight := fractionalBlockyCoverNumber_le C
    _ = C₁.totalWeight + C₂.totalWeight := htot
    _ < fractionalBlockyCoverNumber P + fractionalBlockyCoverNumber Q + ε := by linarith

/-- Finite-disjunction subadditivity for `fractionalBlockyCoverNumber`. -/
theorem fractionalBlockyCoverNumber_finsetOr_le {ι : Type*} (s : Finset ι)
    (M : ι → X → Y → Bool) :
    fractionalBlockyCoverNumber (fun x y ↦ decide (∃ i ∈ s, M i x y = true)) ≤
      ∑ i ∈ s, fractionalBlockyCoverNumber (M i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have hrew : (fun x y ↦ decide (∃ i ∈ insert a s, M i x y = true)) =
        fun x y ↦ M a x y || decide (∃ i ∈ s, M i x y = true) := by
      ext x y
      by_cases hMa : M a x y = true <;> simp [hMa]
    rw [hrew, Finset.sum_insert ha]
    exact (fractionalBlockyCoverNumber_or_le _ _).trans (add_le_add le_rfl ih)

/-- **Randomized rounding from fractional to integral blocky covers**: for every square Boolean
matrix `P : X → X → Bool` with `2 ≤ Fintype.card X`,
`(bc(P) : ℝ) ≤ 4 * fbc(P) * ln |X|`. -/
theorem blockyCoverNumber_le_four_mul_fbc_mul_log (P : X → X → Bool)
    (hX : 2 ≤ Fintype.card X) :
    (blockyCoverNumber P : ℝ) ≤
      4 * fractionalBlockyCoverNumber P * Real.log (Fintype.card X : ℝ) := by
  classical
  by_cases hP0 : ∀ x y, P x y = false
  · have hP : P = fun _ _ ↦ false := by ext x y; exact hP0 x y
    rw [blockyCoverNumber_eq_zero_iff.mpr hP0, hP, fractionalBlockyCoverNumber_false]
    simp
  · push Not at hP0
    obtain ⟨x₀, y₀, hx₀'⟩ := hP0
    have hx₀ : P x₀ y₀ = true := Bool.eq_true_of_not_eq_false hx₀'
    have hfbc_ge : 1 ≤ fractionalBlockyCoverNumber P :=
      one_le_fractionalBlockyCoverNumber ⟨x₀, y₀, hx₀⟩
    set N := Fintype.card X
    have hN_pos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    have hlog_pos : 0 < Real.log (N : ℝ) :=
      Real.log_pos (by exact_mod_cast (by omega : 1 < N))
    have hε : 0 < fractionalBlockyCoverNumber P / 4 := by linarith
    obtain ⟨C, hCW⟩ := exists_fractionalBlockyCover_lt_add (A := P) hε
    set W := C.totalWeight
    have hW_ge : 1 ≤ W := hfbc_ge.trans (fractionalBlockyCoverNumber_le C)
    have hW_pos : 0 < W := zero_lt_one.trans_le hW_ge
    let t : ℕ := Nat.floor (2 * W * Real.log (N : ℝ)) + 1
    have ht_gt : 2 * W * Real.log (N : ℝ) < (t : ℝ) := by
      dsimp [t]
      exact_mod_cast Nat.lt_floor_add_one (2 * W * Real.log (N : ℝ))
    let p : Fin C.size → ℝ := fun i ↦ C.weight i / W
    have hp_nn : ∀ i, 0 ≤ p i := fun i ↦ div_nonneg (C.weight_nonneg i) hW_pos.le
    have hp_sum : ∑ i : Fin C.size, p i = 1 := by
      simp only [p, ← Finset.sum_div]
      exact div_self hW_pos.ne'
    let prob : (Fin t → Fin C.size) → ℝ := fun ω ↦ ∏ r : Fin t, p (ω r)
    have hprob_nn : ∀ ω, 0 ≤ prob ω := fun ω ↦ Finset.prod_nonneg (fun r _ ↦ hp_nn (ω r))
    have hprob_sum : ∑ ω : Fin t → Fin C.size, prob ω = 1 := by
      have hpi := (Fintype.sum_pow p t).symm
      rw [hp_sum, one_pow] at hpi
      exact hpi
    let ones := (Finset.univ : Finset (X × X)).filter (fun q ↦ P q.1 q.2 = true)
    have hmiss : ∀ q ∈ ones,
        ∑ ω : Fin t → Fin C.size,
          (if ∀ r : Fin t, C.mat (ω r) q.1 q.2 = false then prob ω else 0) ≤
        Real.exp (-(t : ℝ) / W) := by
      intro ⟨x, y⟩ hq
      have hxy : P x y = true := (Finset.mem_filter.mp hq).2
      let qvec : Fin C.size → ℝ := fun i ↦ if C.mat i x y = false then p i else 0
      have hprod_eq : ∀ ω : Fin t → Fin C.size,
          (if ∀ r : Fin t, C.mat (ω r) x y = false then prob ω else 0) =
            ∏ r : Fin t, qvec (ω r) := by
        intro ω
        split_ifs with hall
        · exact Finset.prod_congr rfl (fun r _ ↦ by simp [qvec, hall r])
        · push Not at hall
          obtain ⟨r₀, hr₀⟩ := hall
          symm
          exact Finset.prod_eq_zero (Finset.mem_univ r₀) (by simp [qvec, hr₀])
      simp_rw [hprod_eq]
      rw [← Fintype.sum_pow qvec t]
      have hq_nn : 0 ≤ ∑ i, qvec i :=
        Finset.sum_nonneg (fun i _ ↦ by dsimp [qvec]; cases C.mat i x y <;> simp [hp_nn i])
      have hhit : 1 / W ≤ ∑ i : Fin C.size, p i * (if C.mat i x y = true then (1 : ℝ) else 0) := by
        simp only [p, div_mul_eq_mul_div, ← Finset.sum_div]
        exact div_le_div_of_nonneg_right (C.one_le_sum_of_true x y hxy) hW_pos.le
      have hsplit : ∑ i, qvec i +
          ∑ i, p i * (if C.mat i x y = true then (1 : ℝ) else 0) = 1 := by
        rw [← Finset.sum_add_distrib]
        conv_rhs => rw [← hp_sum]
        refine Finset.sum_congr rfl (fun i _ ↦ ?_)
        cases hm : C.mat i x y <;> simp [qvec, hm]
      have hq_le : ∑ i, qvec i ≤ Real.exp (-(1 / W)) := by
        have h1 : ∑ i, qvec i ≤ 1 - 1 / W := by linarith
        linarith [Real.add_one_le_exp (-(1 / W))]
      calc (∑ i, qvec i) ^ t
          ≤ Real.exp (-(1 / W)) ^ t := pow_le_pow_left₀ hq_nn hq_le t
        _ = Real.exp (-(t : ℝ) / W) := by
            rw [← Real.exp_nat_mul]
            congr 1
            ring
    have hexp_lt : (N : ℝ) ^ 2 * Real.exp (-(t : ℝ) / W) < 1 := by
      have hlt : -(t : ℝ) / W < -2 * Real.log (N : ℝ) := by
        rw [div_lt_iff₀ hW_pos]
        linarith
      calc (N : ℝ) ^ 2 * Real.exp (-(t : ℝ) / W)
          < (N : ℝ) ^ 2 * Real.exp (-2 * Real.log (N : ℝ)) :=
            mul_lt_mul_of_pos_left (Real.exp_lt_exp.mpr hlt) (sq_pos_of_pos hN_pos)
        _ = (N : ℝ) ^ 2 * ((N : ℝ) ^ 2)⁻¹ := by
            congr 1
            rw [show -2 * Real.log (N : ℝ) = -Real.log ((N : ℝ) ^ 2) by
              rw [Real.log_pow]; push_cast; ring, Real.exp_neg,
              Real.exp_log (sq_pos_of_pos hN_pos)]
        _ = 1 := mul_inv_cancel₀ (sq_pos_of_pos hN_pos).ne'
    let bad : (Fin t → Fin C.size) → Prop :=
      fun ω ↦ ∃ q ∈ ones, ∀ r : Fin t, C.mat (ω r) q.1 q.2 = false
    have hbad_lt : ∑ ω : Fin t → Fin C.size, (if bad ω then prob ω else 0) < 1 := by
      have hpt : ∀ ω, (if bad ω then prob ω else 0) ≤
          ∑ q ∈ ones, (if ∀ r, C.mat (ω r) q.1 q.2 = false then prob ω else 0) := by
        intro ω
        have hterm_nn : ∀ q : X × X,
            0 ≤ (if ∀ r, C.mat (ω r) q.1 q.2 = false then prob ω else 0) := fun q ↦ by
          by_cases h : ∀ r, C.mat (ω r) q.1 q.2 = false <;> simp [h, hprob_nn ω]
        by_cases hb : bad ω
        · simp only [hb, ↓reduceIte]
          obtain ⟨q₀, hq₀, hall⟩ := hb
          calc prob ω = (if ∀ r, C.mat (ω r) q₀.1 q₀.2 = false then prob ω else 0) := by
                split_ifs
                exact rfl
            _ ≤ _ := Finset.single_le_sum (fun q _ ↦ hterm_nn q) hq₀
        · simp only [hb, ↓reduceIte]
          exact Finset.sum_nonneg (fun q _ ↦ hterm_nn q)
      have hcard_le : (ones.card : ℝ) ≤ (N : ℝ) ^ 2 := by
        have : ones.card ≤ N * N :=
          (Finset.card_le_univ ones).trans (by simp [Fintype.card_prod, N])
        simpa [sq] using (Nat.cast_le (α := ℝ).mpr this)
      calc ∑ ω, (if bad ω then prob ω else 0)
          ≤ ∑ ω, ∑ q ∈ ones, (if ∀ r, C.mat (ω r) q.1 q.2 = false then prob ω else 0) :=
            Finset.sum_le_sum (fun ω _ ↦ hpt ω)
        _ = ∑ q ∈ ones, ∑ ω, (if ∀ r, C.mat (ω r) q.1 q.2 = false then prob ω else 0) :=
            Finset.sum_comm
        _ ≤ ∑ _q ∈ ones, Real.exp (-(t : ℝ) / W) := Finset.sum_le_sum hmiss
        _ = (ones.card : ℝ) * Real.exp (-(t : ℝ) / W) := by simp
        _ ≤ (N : ℝ) ^ 2 * Real.exp (-(t : ℝ) / W) :=
            mul_le_mul_of_nonneg_right hcard_le (Real.exp_nonneg _)
        _ < 1 := hexp_lt
    have hex_good : ∃ ω : Fin t → Fin C.size, 0 < prob ω ∧ ¬bad ω := by
      by_contra hnone
      push Not at hnone
      have heq : ∑ ω, (if bad ω then prob ω else 0) = ∑ ω, prob ω := by
        refine Finset.sum_congr rfl (fun ω _ ↦ ?_)
        by_cases hp0 : 0 < prob ω
        · have hbω : bad ω := hnone ω hp0
          simp only [hbω, ↓reduceIte]
        · have hz : prob ω = 0 := le_antisymm (not_lt.mp hp0) (hprob_nn ω)
          simp [hz]
      linarith [hprob_sum]
    obtain ⟨ω, hω_pos, hω_good⟩ := hex_good
    have hbc_le : blockyCoverNumber P ≤ t := by
      refine blockyCoverNumber_le (fun r ↦ C.mat (ω r)) (fun r ↦ C.mat_blocky (ω r)) (fun x y ↦ ?_)
      constructor
      · intro hxy
        have hnot : ¬∀ r : Fin t, C.mat (ω r) x y = false := fun hall ↦
          hω_good ⟨(x, y), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxy⟩, hall⟩
        push Not at hnot
        obtain ⟨r, hr⟩ := hnot
        exact ⟨r, Bool.eq_true_of_not_eq_false hr⟩
      · rintro ⟨r, hr⟩
        by_contra hne_t
        have hf : P x y = false := Bool.eq_false_iff.mpr hne_t
        have hpr : p (ω r) ≠ 0 := by
          intro hz
          have : prob ω = 0 := Finset.prod_eq_zero (Finset.mem_univ r) hz
          linarith
        have hwr : 0 < C.weight (ω r) := by
          refine (C.weight_nonneg (ω r)).lt_of_ne' (fun hz ↦ hpr ?_)
          simp [p, hz]
        rw [C.mat_eq_false_of_weight_pos hwr hf] at hr
        cases hr
    have hlog2 : (1 / 2 : ℝ) < Real.log (N : ℝ) := by
      have hln2 : (1 / 2 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
      exact hln2.trans_le (Real.log_le_log (by norm_num) (by exact_mod_cast hX))
    have ht_le : (t : ℝ) ≤ 2 * W * Real.log (N : ℝ) + 1 := by
      dsimp [t]
      rw [Nat.cast_add, Nat.cast_one]
      linarith [Nat.floor_le (show 0 ≤ 2 * W * Real.log (N : ℝ) by positivity)]
    calc (blockyCoverNumber P : ℝ)
        ≤ t := by exact_mod_cast hbc_le
      _ ≤ 2 * W * Real.log (N : ℝ) + 1 := ht_le
      _ ≤ 2 * ((5 / 4 : ℝ) * fractionalBlockyCoverNumber P) * Real.log (N : ℝ) +
            (3 / 2 : ℝ) * fractionalBlockyCoverNumber P * Real.log (N : ℝ) := by
          have h1 : W ≤ (5 / 4 : ℝ) * fractionalBlockyCoverNumber P := by linarith
          have hlog3 : (1 : ℝ) ≤ (3 / 2 : ℝ) * Real.log (N : ℝ) := by
            have hln2 : (2 / 3 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
            have : (2 / 3 : ℝ) < Real.log (N : ℝ) :=
              hln2.trans_le (Real.log_le_log (by norm_num) (by exact_mod_cast hX))
            linarith
          have h2 :
              (1 : ℝ) ≤ (3 / 2 : ℝ) * fractionalBlockyCoverNumber P * Real.log (N : ℝ) := by
            calc (1 : ℝ) ≤ 1 * ((3 / 2 : ℝ) * Real.log (N : ℝ)) := by linarith
              _ ≤ fractionalBlockyCoverNumber P * ((3 / 2 : ℝ) * Real.log (N : ℝ)) :=
                  mul_le_mul_of_nonneg_right hfbc_ge (by positivity)
              _ = (3 / 2 : ℝ) * fractionalBlockyCoverNumber P * Real.log (N : ℝ) := by ring
          have h3 : 2 * W * Real.log (N : ℝ) ≤
              2 * ((5 / 4 : ℝ) * fractionalBlockyCoverNumber P) * Real.log (N : ℝ) :=
            mul_le_mul_of_nonneg_right (by linarith) hlog_pos.le
          linarith
      _ = 4 * fractionalBlockyCoverNumber P * Real.log (N : ℝ) := by ring

/-- Base-`2` logarithm version of `blockyCoverNumber_le_four_mul_fbc_mul_log`: for `2 ≤ card X`,
`(bc(P) : ℝ) ≤ 4 * fbc(P) * log₂ |X|`. -/
theorem blockyCoverNumber_le_four_mul_fbc_mul_logb (P : X → X → Bool)
    (hX : 2 ≤ Fintype.card X) :
    (blockyCoverNumber P : ℝ) ≤
      4 * fractionalBlockyCoverNumber P * Real.logb 2 (Fintype.card X : ℝ) := by
  have hlog_le : Real.log (Fintype.card X : ℝ) ≤ Real.logb 2 (Fintype.card X : ℝ) := by
    rw [Real.logb]
    have hln2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hln2_le : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
    have hlnN_nn : 0 ≤ Real.log (Fintype.card X : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ Fintype.card X))
    rw [le_div_iff₀ hln2_pos]
    nlinarith
  exact (blockyCoverNumber_le_four_mul_fbc_mul_log P hX).trans
    (mul_le_mul_of_nonneg_left hlog_le
      (mul_nonneg (by norm_num) (fractionalBlockyCoverNumber_nonneg P)))

/-- Every deterministic `Equality`-oracle protocol `p` satisfies `fbc(p.eval) ≤ 3 ^ p.depth`
(and hence `≤ 5 ^ p.depth`). -/
theorem fractionalBlockyCoverNumber_le_three_pow_eqProtocol (p : OracleProtocol eqOracle X Y Bool) :
    fractionalBlockyCoverNumber p.eval ≤ (3 : ℝ) ^ p.depth := by
  induction p with
  | output z =>
    cases z
    · have hf : (OracleProtocol.output false : OracleProtocol eqOracle X Y Bool).eval =
          fun _ _ ↦ false := by ext; simp
      rw [hf, OracleProtocol.depth_output, pow_zero, fractionalBlockyCoverNumber_false]
      exact zero_le_one
    · have ht : (OracleProtocol.output true : OracleProtocol eqOracle X Y Bool).eval =
          fun _ _ ↦ true := by ext; simp
      rw [ht, OracleProtocol.depth_output, pow_zero]
      exact (IsBlocky.const_true (X := X) (Y := Y)).fractionalBlockyCoverNumber_le_one
  | query m a b p₀ p₁ ih₀ ih₁ =>
    let B : X → Y → Bool := fun x y ↦ eqOracle m (a x) (b y)
    have hB : IsBlocky B := IsBlocky.of_eq a b (fun _ _ ↦ by simp [B, equality])
    have hrew : (OracleProtocol.query m a b p₀ p₁).eval =
        fun x y ↦ (B x y && p₁.eval x y) || ((!B x y) && p₀.eval x y) := by
      ext x y
      simp only [OracleProtocol.eval_query]
      change cond (B x y) (p₁.eval x y) (p₀.eval x y) = _
      cases B x y <;> simp
    set d := max p₀.depth p₁.depth
    have h₀ : fractionalBlockyCoverNumber p₀.eval ≤ (3 : ℝ) ^ d :=
      ih₀.trans (pow_le_pow_right₀ (a := (3 : ℝ)) (by norm_num) (le_max_left _ _))
    have h₁ : fractionalBlockyCoverNumber p₁.eval ≤ (3 : ℝ) ^ d :=
      ih₁.trans (pow_le_pow_right₀ (a := (3 : ℝ)) (by norm_num) (le_max_right _ _))
    rw [hrew, OracleProtocol.depth_query]
    calc fractionalBlockyCoverNumber
          (fun x y ↦ (B x y && p₁.eval x y) || ((!B x y) && p₀.eval x y))
        ≤ fractionalBlockyCoverNumber (fun x y ↦ B x y && p₁.eval x y) +
            fractionalBlockyCoverNumber (fun x y ↦ (!B x y) && p₀.eval x y) :=
          fractionalBlockyCoverNumber_or_le _ _
      _ ≤ fractionalBlockyCoverNumber B * fractionalBlockyCoverNumber p₁.eval +
            fractionalBlockyCoverNumber (fun x y ↦ !B x y) *
              fractionalBlockyCoverNumber p₀.eval :=
          add_le_add (fractionalBlockyCoverNumber_and_le _ _)
            (fractionalBlockyCoverNumber_and_le _ _)
      _ ≤ 1 * (3 : ℝ) ^ d + 2 * (3 : ℝ) ^ d :=
          add_le_add
            (mul_le_mul hB.fractionalBlockyCoverNumber_le_one h₁
              (fractionalBlockyCoverNumber_nonneg _) zero_le_one)
            (mul_le_mul hB.fractionalBlockyCoverNumber_not_le_two h₀
              (fractionalBlockyCoverNumber_nonneg _) (by norm_num))
      _ = (3 : ℝ) ^ (d + 1) := by rw [pow_succ]; ring

/-- For every finite Boolean matrix `A : X → Y → Bool`, `fbc(A) ≤ 3 ^ ND^Eq(A)`. -/
theorem fractionalBlockyCoverNumber_le_three_pow_ndEq (A : X → Y → Bool) :
    fractionalBlockyCoverNumber A ≤ (3 : ℝ) ^ ndEqOracleComplexity A := by
  classical
  obtain ⟨m, d, hmd, hcov'⟩ := exists_hasNdEqCover_eq A
  obtain ⟨M, hMd, hcov⟩ := hasNdEqCover_iff.mp hcov'
  have hrew : A = fun x y ↦
      decide (∃ i ∈ (Finset.univ : Finset (Fin (2 ^ m))), M i x y = true) := by
    ext x y
    by_cases hxy : A x y = true
    · obtain ⟨i, hi⟩ := (hcov x y).mp hxy
      have hex : ∃ j ∈ (Finset.univ : Finset (Fin (2 ^ m))), M j x y = true :=
        ⟨i, Finset.mem_univ i, hi⟩
      rw [hxy, decide_eq_true hex]
    · have hf : A x y = false := Bool.eq_false_iff.mpr hxy
      have hnex : ¬∃ j ∈ (Finset.univ : Finset (Fin (2 ^ m))), M j x y = true := by
        rintro ⟨j, -, hj⟩
        exact hxy ((hcov x y).mpr ⟨j, hj⟩)
      rw [hf, decide_eq_false hnex]
  have hMi : ∀ i : Fin (2 ^ m), fractionalBlockyCoverNumber (M i) ≤ (3 : ℝ) ^ d := by
    intro i
    obtain ⟨p, hp, hpd⟩ := eqOracleComplexity_le_iff.mp (hMd i)
    rw [← hp]
    exact (fractionalBlockyCoverNumber_le_three_pow_eqProtocol p).trans
      (pow_le_pow_right₀ (a := (3 : ℝ)) (by norm_num) hpd)
  have hsub := fractionalBlockyCoverNumber_finsetOr_le (Finset.univ : Finset (Fin (2 ^ m))) M
  calc fractionalBlockyCoverNumber A
      ≤ ∑ i : Fin (2 ^ m), fractionalBlockyCoverNumber (M i) := by
        convert hsub using 2; ext x y; rw [hrew]; simp
    _ ≤ ∑ _i : Fin (2 ^ m), (3 : ℝ) ^ d := Finset.sum_le_sum (fun i _ ↦ hMi i)
    _ = (2 : ℝ) ^ m * (3 : ℝ) ^ d := by simp
    _ ≤ (3 : ℝ) ^ m * (3 : ℝ) ^ d :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) (by norm_num) m) (by positivity)
    _ = (3 : ℝ) ^ ndEqOracleComplexity A := by rw [← pow_add, hmd]

/-- Corollary of `fractionalBlockyCoverNumber_le_three_pow_ndEq` with base `5` (obtained when using
`fbc(J - B) ≤ 4`): `fbc(A) ≤ 5 ^ ND^Eq(A)`. -/
theorem fractionalBlockyCoverNumber_le_five_pow_ndEq (A : X → Y → Bool) :
    fractionalBlockyCoverNumber A ≤ (5 : ℝ) ^ ndEqOracleComplexity A :=
  (fractionalBlockyCoverNumber_le_three_pow_ndEq A).trans
    (pow_le_pow_left₀ (by norm_num) (by norm_num) _)

/-- **Upper bound on `log₂ bc(A)` in terms of `ND^Eq(A)` and `log₂ log₂ |X|`**: for every finite
square Boolean matrix `A : X → X → Bool` with `2 ≤ Fintype.card X`,
`log₂ bc(A) ≤ log₂ 3 * ND^Eq(A) + log₂ (log₂ |X|) + 2`. -/
theorem logb_blockyCoverNumber_le_ndEq_add_log_log (A : X → X → Bool)
    (hX : 2 ≤ Fintype.card X) :
    Real.logb 2 (blockyCoverNumber A : ℝ) ≤
      Real.logb 2 3 * (ndEqOracleComplexity A : ℝ) +
        Real.logb 2 (Real.logb 2 (Fintype.card X : ℝ)) + 2 := by
  have hlogN : 1 ≤ Real.logb 2 (Fintype.card X : ℝ) := by
    calc (1 : ℝ) = Real.logb 2 2 := (Real.logb_self_eq_one (by norm_num)).symm
      _ ≤ Real.logb 2 (Fintype.card X : ℝ) :=
          Real.logb_le_logb_of_le (by norm_num) (by norm_num) (by exact_mod_cast hX)
  have hll_nn : 0 ≤ Real.logb 2 (Real.logb 2 (Fintype.card X : ℝ)) :=
    Real.logb_nonneg (by norm_num) hlogN
  have hlog3_nn : 0 ≤ Real.logb 2 3 := Real.logb_nonneg (by norm_num) (by norm_num)
  by_cases hbc0 : blockyCoverNumber A = 0
  · rw [hbc0, Nat.cast_zero, Real.logb_zero]
    positivity
  · have hbc_pos : (0 : ℝ) < blockyCoverNumber A := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hbc0)
    have hprod : (blockyCoverNumber A : ℝ) ≤
        4 * (3 : ℝ) ^ ndEqOracleComplexity A * Real.logb 2 (Fintype.card X : ℝ) := by
      calc (blockyCoverNumber A : ℝ)
          ≤ 4 * fractionalBlockyCoverNumber A * Real.logb 2 (Fintype.card X : ℝ) :=
            blockyCoverNumber_le_four_mul_fbc_mul_logb A hX
        _ ≤ 4 * (3 : ℝ) ^ ndEqOracleComplexity A * Real.logb 2 (Fintype.card X : ℝ) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left (fractionalBlockyCoverNumber_le_three_pow_ndEq A)
                (by norm_num))
              (zero_le_one.trans hlogN)
    have hlog4 : Real.logb 2 (4 : ℝ) = 2 := by
      rw [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) by norm_num, Real.logb_pow,
        Real.logb_self_eq_one (by norm_num)]
      norm_num
    calc Real.logb 2 (blockyCoverNumber A : ℝ)
        ≤ Real.logb 2
            (4 * (3 : ℝ) ^ ndEqOracleComplexity A * Real.logb 2 (Fintype.card X : ℝ)) :=
          Real.logb_le_logb_of_le (by norm_num) hbc_pos hprod
      _ = Real.logb 2 4 + Real.logb 2 ((3 : ℝ) ^ ndEqOracleComplexity A) +
            Real.logb 2 (Real.logb 2 (Fintype.card X : ℝ)) := by
          rw [Real.logb_mul (by positivity) (zero_lt_one.trans_le hlogN).ne',
            Real.logb_mul (by norm_num) (by positivity)]
      _ = Real.logb 2 3 * (ndEqOracleComplexity A : ℝ) +
            Real.logb 2 (Real.logb 2 (Fintype.card X : ℝ)) + 2 := by
          rw [hlog4, Real.logb_pow]
          ring

-- Non-vacuity check: `bc(I_3) = 1` and `fbc(J_3 - I_3) ≤ 2`.
example : blockyCoverNumber (equality : Fin 3 → Fin 3 → Bool) = 1 ∧
    fractionalBlockyCoverNumber (fun x y : Fin 3 ↦ !equality x y) ≤ 2 :=
  ⟨IsBlocky.equality.blockyCoverNumber_eq_one ⟨0, 0, rfl⟩,
   IsBlocky.equality.fractionalBlockyCoverNumber_not_le_two⟩

end FractionalBlockyCover

end CslibFrontier.Communication
