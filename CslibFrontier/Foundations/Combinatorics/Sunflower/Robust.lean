/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FormalPapers Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Combinatorics.BiasedSetMeasure
public import CslibFrontier.Foundations.Combinatorics.Sunflower
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Robust Sunflowers and Spread Set Systems

This module develops set-system kernels, links, `(α, β)`-robust sunflowers, weighted and unweighted
spread set systems, linear-spread satisfyingness, and maximal violating-kernel extraction.

A set system `F` is an `(α, β)`-robust sunflower when its common intersection (kernel) `K` does not
belong to `F` and the link `{S \ K : S ∈ F, K ⊆ S}` is `(α, β)`-satisfying. Every `(1 / r, 1 / r)`-
robust sunflower (`r ≥ 2`) contains an `r`-petal sunflower (`Cslib.ContainsSunflower`).
Combining Janson's exponential tail inequality with rational-weight multiset padding shows that
weighted `w`-set systems with spread at least `max (4 * log (1 / β)) 2 * w / α` are
`(α, β)`-satisfying, and maximal violating-kernel extraction produces `(α, β)`-robust sunflowers in
large `w`-uniform set systems.

## Main definitions

* `CslibFrontier.IsWSetSystem`, `CslibFrontier.IsWUniform`: bounded-width and uniform set systems.
* `CslibFrontier.setSystemKernel`, `CslibFrontier.setLink`: common intersection and link of a finite
  set system.
* `CslibFrontier.IsRobustSunflower`, `CslibFrontier.ContainsRobustSunflower`: `(α, β)`-robust
  sunflowers.
* `CslibFrontier.WeightProfile`, `CslibFrontier.kappaProfile`, `CslibFrontier.IsSpreadWeighted`,
  `CslibFrontier.IsSpread`, `CslibFrontier.IsUniformKappaSpread`,
  `CslibFrontier.IsSatisfyingProfile`: spread weight profiles, spread set systems, and satisfying
  profiles.

## Main results

* `CslibFrontier.IsRobustSunflower.containsSunflower`,
  `CslibFrontier.ContainsRobustSunflower.containsSunflower`: every `(1 / r, 1 / r)`-robust sunflower
  (`r ≥ 2`) contains an `r`-petal sunflower.
* `CslibFrontier.isSatisfying_of_isSpreadWeighted_linear`,
  `CslibFrontier.isSatisfyingProfile_kappaProfile_linear`: weighted `w`-set systems with spread at
  least `max (4 * log (1 / β)) 2 * w / α` are `(α, β)`-satisfying.
* `CslibFrontier.containsRobustSunflower_of_isSatisfyingProfile`,
  `CslibFrontier.containsRobustSunflower_of_card_gt_linear_pow`: kernel-extraction criteria for
  `(α, β)`-robust sunflowers in `w`-uniform set systems.
-/

public section

namespace CslibFrontier

open Finset

/-! ### Bounded-width set systems, kernels, links, and robust sunflowers -/

/-- A `w`-set system is a finite family of finite sets each of cardinality at most `w`. -/
public def IsWSetSystem {α : Type*} (w : ℕ) (F : Finset (Finset α)) : Prop :=
  ∀ S ∈ F, S.card ≤ w

/-- Characterization of `IsWSetSystem`. -/
public theorem isWSetSystem_iff {α : Type*} {w : ℕ} {F : Finset (Finset α)} :
    IsWSetSystem w F ↔ ∀ S ∈ F, S.card ≤ w :=
  Iff.rfl

/-- A `w`-uniform set system is a finite family of finite sets each of cardinality `w`. -/
public def IsWUniform {α : Type*} (w : ℕ) (F : Finset (Finset α)) : Prop :=
  ∀ S ∈ F, S.card = w

/-- Characterization of `IsWUniform`. -/
public theorem isWUniform_iff {α : Type*} {w : ℕ} {F : Finset (Finset α)} :
    IsWUniform w F ↔ ∀ S ∈ F, S.card = w :=
  Iff.rfl

/-- Every `w`-uniform set system is a `w`-set system. -/
public theorem IsWUniform.isWSetSystem {α : Type*} {w : ℕ} {F : Finset (Finset α)}
    (h : IsWUniform w F) : IsWSetSystem w F :=
  fun S hS ↦ (h S hS).le

/-- The common intersection (kernel) of a nonempty finite set system `F`, defaulting to `∅` when
`F = ∅`. -/
public def setSystemKernel {α : Type*} [DecidableEq α] (F : Finset (Finset α)) : Finset α :=
  (F.biUnion id).filter fun x ↦ ∀ S ∈ F, x ∈ S

/-- Membership in `setSystemKernel F` for nonempty `F` is membership in every member of `F`. -/
@[simp]
public theorem mem_setSystemKernel_iff {α : Type*} [DecidableEq α]
    {F : Finset (Finset α)} (hF : F.Nonempty) {x : α} :
    x ∈ setSystemKernel F ↔ ∀ S ∈ F, x ∈ S := by
  obtain ⟨S₀, hS₀⟩ := hF
  simp only [setSystemKernel, mem_filter, mem_biUnion, id_eq]
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨⟨S₀, hS₀, h S₀ hS₀⟩, h⟩⟩

/-- The kernel of `F` is contained in every member of `F`. -/
public theorem setSystemKernel_subset {α : Type*} [DecidableEq α]
    {F : Finset (Finset α)} {S : Finset α} (hS : S ∈ F) :
    setSystemKernel F ⊆ S := by
  intro x hx
  exact (mem_setSystemKernel_iff ⟨S, hS⟩).1 hx S hS

/-- Any set contained in every member of a nonempty family `F` lies in `setSystemKernel F`. -/
public theorem subset_setSystemKernel {α : Type*} [DecidableEq α]
    {F : Finset (Finset α)} (hF : F.Nonempty) {T : Finset α} (hT : ∀ S ∈ F, T ⊆ S) :
    T ⊆ setSystemKernel F := by
  intro x hx
  exact (mem_setSystemKernel_iff hF).2 fun S hS ↦ hT S hS hx

/-- The link `{S \ T : S ∈ F, T ⊆ S}` of a set system `F` at `T`. -/
public def setLink {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (T : Finset α) : Finset (Finset α) :=
  (F.filter (T ⊆ ·)).image (· \ T)

/-- Membership characterization for `setLink F T`. -/
@[simp]
public theorem mem_setLink_iff {α : Type*} [DecidableEq α]
    {F : Finset (Finset α)} {T P : Finset α} :
    P ∈ setLink F T ↔ Disjoint P T ∧ P ∪ T ∈ F := by
  simp only [setLink, mem_image, mem_filter]
  constructor
  · rintro ⟨S, ⟨hSF, hTS⟩, rfl⟩
    exact ⟨sdiff_disjoint, (sdiff_union_of_subset hTS).symm ▸ hSF⟩
  · rintro ⟨hdisj, hmem⟩
    exact ⟨P ∪ T, ⟨hmem, subset_union_right⟩, union_sdiff_cancel_right hdisj⟩

/-- Cardinality of `setLink F T` equals the number of members of `F` containing `T`. -/
public theorem card_setLink {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (T : Finset α) :
    (setLink F T).card = (F.filter (T ⊆ ·)).card := by
  refine card_image_of_injOn fun S₁ hS₁ S₂ hS₂ heq ↦ ?_
  rw [← sdiff_union_of_subset (mem_filter.1 hS₁).2,
    ← sdiff_union_of_subset (mem_filter.1 hS₂).2, heq]

/-- Iterated link identity `setLink (setLink F K) T = setLink F (K ∪ T)` when `Disjoint K T`. -/
public theorem setLink_setLink {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) {K T : Finset α} (hKT : Disjoint K T) :
    setLink (setLink F K) T = setLink F (K ∪ T) := by
  ext P
  simp only [mem_setLink_iff]
  constructor
  · rintro ⟨hPT, hPK, hPTK⟩
    refine ⟨disjoint_union_right.2 ⟨disjoint_of_subset_left subset_union_left hPK, hPT⟩, ?_⟩
    rwa [union_assoc, union_comm T K] at hPTK
  · rintro ⟨hPKT, hmem⟩
    obtain ⟨hPK, hPT⟩ := disjoint_union_right.1 hPKT
    refine ⟨hPT, disjoint_union_left.2 ⟨hPK, hKT.symm⟩, ?_⟩
    rwa [union_assoc, union_comm T K]

/-- A set system `F` is an `(α, β)`-robust sunflower when its kernel `K = setSystemKernel F` does
not belong to `F` and the link `setLink F K` is `(α, β)`-satisfying. -/
public def IsRobustSunflower {α : Type*} [DecidableEq α]
    (α_prob β_err : ℝ) (F : Finset (Finset α)) : Prop :=
  setSystemKernel F ∉ F ∧ IsSatisfying α_prob β_err (setLink F (setSystemKernel F))

/-- Characterization of `IsRobustSunflower`. -/
public theorem isRobustSunflower_iff {α : Type*} [DecidableEq α]
    {α_prob β_err : ℝ} {F : Finset (Finset α)} :
    IsRobustSunflower α_prob β_err F ↔
      setSystemKernel F ∉ F ∧ IsSatisfying α_prob β_err (setLink F (setSystemKernel F)) :=
  Iff.rfl

/-- A set system `F` contains an `(α, β)`-robust sunflower if some subfamily `G ⊆ F` is an
`(α, β)`-robust sunflower. -/
public def ContainsRobustSunflower {α : Type*} [DecidableEq α]
    (α_prob β_err : ℝ) (F : Finset (Finset α)) : Prop :=
  ∃ G ⊆ F, IsRobustSunflower α_prob β_err G

/-- Characterization of `ContainsRobustSunflower`. -/
public theorem containsRobustSunflower_iff {α : Type*} [DecidableEq α]
    {α_prob β_err : ℝ} {F : Finset (Finset α)} :
    ContainsRobustSunflower α_prob β_err F ↔ ∃ G ⊆ F, IsRobustSunflower α_prob β_err G :=
  Iff.rfl

/-- Monotonicity of `ContainsRobustSunflower` with respect to set-system inclusion. -/
public theorem ContainsRobustSunflower.mono {α : Type*} [DecidableEq α]
    {α_prob β_err : ℝ} {F H : Finset (Finset α)}
    (hFH : F ⊆ H) (h : ContainsRobustSunflower α_prob β_err F) :
    ContainsRobustSunflower α_prob β_err H := by
  obtain ⟨G, hGF, hG⟩ := h
  exact ⟨G, hGF.trans hFH, hG⟩

/-- Every `(1 / r, 1 / r)`-robust sunflower (`r ≥ 2`) contains a combinatorial `r`-petal
sunflower. -/
public theorem IsRobustSunflower.containsSunflower {α : Type*} [DecidableEq α]
    {r : ℕ} (hr : 2 ≤ r) {F : Finset (Finset α)}
    (hrob : IsRobustSunflower (1 / (r : ℝ)) (1 / (r : ℝ)) F) :
    Cslib.ContainsSunflower r F := by
  obtain ⟨hKnot, hsat⟩ := isRobustSunflower_iff.1 hrob
  set K := setSystemKernel F
  have hempty : ∅ ∉ setLink F K := by
    rw [mem_setLink_iff, empty_union]
    exact fun h ↦ hKnot h.2
  obtain ⟨D, hDF, hDcard, hDdisj⟩ :=
    exists_pairwise_disjoint_of_isSatisfying (by omega : 1 ≤ r) hsat hempty
  let S := D.image (· ∪ K)
  have hinj : Set.InjOn (fun P : Finset α ↦ P ∪ K) D := by
    intro P₁ hP₁ P₂ hP₂ heq
    dsimp only at heq
    have hd₁ : Disjoint P₁ K := (mem_setLink_iff.1 (hDF hP₁)).1
    have hd₂ : Disjoint P₂ K := (mem_setLink_iff.1 (hDF hP₂)).1
    rw [← union_sdiff_cancel_right hd₁, ← union_sdiff_cancel_right hd₂, heq]
  refine ⟨S, ?_, ?_, K, ?_, ?_⟩
  · intro A hA
    obtain ⟨P, hPD, rfl⟩ := mem_image.1 hA
    exact (mem_setLink_iff.1 (hDF hPD)).2
  · rw [card_image_of_injOn hinj, hDcard]
  · intro A hA
    obtain ⟨P, -, rfl⟩ := mem_image.1 hA
    exact subset_union_right
  · intro A hA B hB hAB
    obtain ⟨P₁, hP₁, rfl⟩ := mem_image.1 hA
    obtain ⟨P₂, hP₂, rfl⟩ := mem_image.1 hB
    have hne : P₁ ≠ P₂ := fun h ↦ hAB (congrArg (· ∪ K) h)
    have hdisj := disjoint_left.1 (hDdisj hP₁ hP₂ hne)
    ext x
    simp only [mem_inter, mem_union]
    exact ⟨fun ⟨h1, h2⟩ ↦
      h1.elim (fun hxP₁ ↦ h2.elim (fun hxP₂ ↦ False.elim (hdisj hxP₁ hxP₂)) id) id,
      fun hxK ↦ ⟨Or.inr hxK, Or.inr hxK⟩⟩

/-- If `F` contains a `(1 / r, 1 / r)`-robust sunflower (`r ≥ 2`), then `F` contains an `r`-petal
sunflower. -/
public theorem ContainsRobustSunflower.containsSunflower {α : Type*} [DecidableEq α]
    {r : ℕ} (hr : 2 ≤ r) {F : Finset (Finset α)}
    (h : ContainsRobustSunflower (1 / (r : ℝ)) (1 / (r : ℝ)) F) :
    Cslib.ContainsSunflower r F := by
  obtain ⟨G, hGF, hG⟩ := containsRobustSunflower_iff.1 h
  obtain ⟨S, hSG, hcard, K, hSK⟩ := hG.containsSunflower hr
  exact ⟨S, hSG.trans hGF, hcard, K, hSK⟩

/-! ### Spread weight profiles, linear-spread satisfyingness, and kernel extraction -/

/-- An unweighted `w`-set system `F` is `κ`-spread when `|F| ≥ κ ^ w` and
`|setLink F T| ≤ κ ^ (-|T|) * |F|` for every nonempty `T`. -/
public def IsUniformKappaSpread {α : Type*} [DecidableEq α]
    (w : ℕ) (κ : ℝ) (F : Finset (Finset α)) : Prop :=
  IsWSetSystem w F ∧ κ ^ w ≤ (F.card : ℝ) ∧
    ∀ T : Finset α, T.Nonempty → ((setLink F T).card : ℝ) ≤ κ⁻¹ ^ T.card * (F.card : ℝ)

/-- Characterization of `IsUniformKappaSpread`. -/
public theorem isUniformKappaSpread_iff {α : Type*} [DecidableEq α]
    {w : ℕ} {κ : ℝ} {F : Finset (Finset α)} :
    IsUniformKappaSpread w κ F ↔
      IsWSetSystem w F ∧ κ ^ w ≤ (F.card : ℝ) ∧
        ∀ T : Finset α, T.Nonempty → ((setLink F T).card : ℝ) ≤ κ⁻¹ ^ T.card * (F.card : ℝ) :=
  Iff.rfl

/-- A spread weight profile of width `w`: an antitone sequence `s_0 ≥ s_1 ≥ ... ≥ 0` with
`s_0 > 0` and `s_i = 0` for all `i > w`. -/
@[ext]
public structure WeightProfile (w : ℕ) where
  /-- Entry `s_i` of the profile, vanishing for `i > w`. -/
  val : ℕ → ℝ
  /-- Strict positivity at `0`. -/
  zero_pos : 0 < val 0
  /-- Antitone order `s_0 ≥ s_1 ≥ ...`. -/
  antitone : Antitone val
  /-- Nonnegativity of all entries. -/
  nonneg : ∀ i, 0 ≤ val i
  /-- Vanishing beyond width `w`. -/
  eq_zero_of_gt : ∀ i, w < i → val i = 0

/-- Geometric `κ`-spread weight profile `(1; κ⁻¹, ..., κ⁻w)` for `κ ≥ 1`. -/
public noncomputable def kappaProfile (κ : ℝ) (hκ : 1 ≤ κ) (w : ℕ) : WeightProfile w where
  val i := if i ≤ w then κ⁻¹ ^ i else 0
  zero_pos := by simp
  antitone := by
    intro i j hij
    by_cases hj : j ≤ w
    · have hi : i ≤ w := hij.trans hj
      simp only [hi, hj, ↓reduceIte]
      exact pow_le_pow_of_le_one (inv_nonneg.2 (zero_le_one.trans hκ))
        (inv_le_one_of_one_le₀ hκ) hij
    · by_cases hi : i ≤ w
      · simp only [hi, hj, ↓reduceIte]
        exact pow_nonneg (inv_nonneg.2 (zero_le_one.trans hκ)) i
      · simp [hi, hj]
  nonneg i := by
    by_cases hi : i ≤ w
    · simp only [hi, ↓reduceIte]
      exact pow_nonneg (inv_nonneg.2 (zero_le_one.trans hκ)) i
    · simp [hi]
  eq_zero_of_gt i hi := by
    have : ¬ i ≤ w := not_le.2 hi
    simp [this]

/-- Value of `kappaProfile` at `0` is `1`. -/
@[simp]
public theorem kappaProfile_val_zero (κ : ℝ) (hκ : 1 ≤ κ) (w : ℕ) :
    (kappaProfile κ hκ w).val 0 = 1 := by
  simp [kappaProfile]

/-- Value of `kappaProfile` at `i ≤ w` is `κ⁻¹ ^ i`. -/
public theorem kappaProfile_val_of_le (κ : ℝ) (hκ : 1 ≤ κ) {w i : ℕ} (hi : i ≤ w) :
    (kappaProfile κ hκ w).val i = κ⁻¹ ^ i := by
  simp [kappaProfile, hi]

/-- Total rational weight `∑_{S ∈ F'} σ(S)` cast to `ℝ`. -/
public def subWeight {α : Type*} (σ : Finset α → ℚ) (F' : Finset (Finset α)) : ℝ :=
  ∑ S ∈ F', (σ S : ℝ)

/-- Explicit sum representation of `subWeight`. -/
public theorem subWeight_eq_sum {α : Type*} (σ : Finset α → ℚ) (F' : Finset (Finset α)) :
    subWeight σ F' = ∑ S ∈ F', (σ S : ℝ) := by
  rfl

/-- `subWeight` of the empty family is `0`. -/
@[simp]
public theorem subWeight_empty {α : Type*} (σ : Finset α → ℚ) :
    subWeight σ (∅ : Finset (Finset α)) = 0 := by
  simp [subWeight]

/-- Total rational weight of sets in `F` containing `T`. -/
public def linkWeight {α : Type*} [DecidableEq α]
    (σ : Finset α → ℚ) (F : Finset (Finset α)) (T : Finset α) : ℝ :=
  ∑ S ∈ F with T ⊆ S, (σ S : ℝ)

/-- Explicit sum representation of `linkWeight`. -/
public theorem linkWeight_eq_sum {α : Type*} [DecidableEq α]
    (σ : Finset α → ℚ) (F : Finset (Finset α)) (T : Finset α) :
    linkWeight σ F T = ∑ S ∈ F with T ⊆ S, (σ S : ℝ) := by
  rfl

/-- A weighted `w`-set system `(F, σ)` (`σ : Finset α → ℚ`) is `s`-spread when `σ ≥ 0` on `F`,
`subWeight σ F ≥ s_0`, and `linkWeight σ F T ≤ s_{|T|}` for every nonempty `T`. -/
public def IsSpreadWeighted {α : Type*} [DecidableEq α]
    {w : ℕ} (s : WeightProfile w) (F : Finset (Finset α)) (σ : Finset α → ℚ) : Prop :=
  IsWSetSystem w F ∧ (∀ S ∈ F, 0 ≤ σ S) ∧
    s.val 0 ≤ subWeight σ F ∧
    ∀ T : Finset α, T.Nonempty → linkWeight σ F T ≤ s.val T.card

/-- Characterization of `IsSpreadWeighted`. -/
public theorem isSpreadWeighted_iff {α : Type*} [DecidableEq α]
    {w : ℕ} {s : WeightProfile w} {F : Finset (Finset α)} {σ : Finset α → ℚ} :
    IsSpreadWeighted s F σ ↔
      IsWSetSystem w F ∧ (∀ S ∈ F, 0 ≤ σ S) ∧
        s.val 0 ≤ subWeight σ F ∧
        ∀ T : Finset α, T.Nonempty → linkWeight σ F T ≤ s.val T.card :=
  Iff.rfl

/-- A set system `F` is `s`-spread if `(F, σ)` is `s`-spread for some nonnegative rational weight
assignment `σ`. -/
public def IsSpread {α : Type*} [DecidableEq α]
    {w : ℕ} (s : WeightProfile w) (F : Finset (Finset α)) : Prop :=
  ∃ σ : Finset α → ℚ, IsSpreadWeighted s F σ

/-- Characterization of `IsSpread`. -/
public theorem isSpread_iff {α : Type*} [DecidableEq α]
    {w : ℕ} {s : WeightProfile w} {F : Finset (Finset α)} :
    IsSpread s F ↔ ∃ σ : Finset α → ℚ, IsSpreadWeighted s F σ :=
  Iff.rfl

/-- Weighted `κ`-spreadness with respect to `kappaProfile κ hκ w`. -/
public def IsKappaSpread {α : Type*} [DecidableEq α]
    (w : ℕ) (κ : ℝ) (hκ : 1 ≤ κ) (F : Finset (Finset α)) : Prop :=
  IsSpread (kappaProfile κ hκ w) F

/-- Characterization of `IsKappaSpread`. -/
public theorem isKappaSpread_iff {α : Type*} [DecidableEq α]
    {w : ℕ} {κ : ℝ} {hκ : 1 ≤ κ} {F : Finset (Finset α)} :
    IsKappaSpread w κ hκ F ↔ IsSpread (kappaProfile κ hκ w) F :=
  Iff.rfl

/-- Every unweighted `κ`-spread `w`-set system (`κ ≥ 1`) is weighted `κ`-spread via uniform weights
`1 / |F|`. -/
public theorem IsUniformKappaSpread.isKappaSpread {α : Type*} [DecidableEq α]
    {w : ℕ} {κ : ℝ} (hκ : 1 ≤ κ) {F : Finset (Finset α)}
    (hF : IsUniformKappaSpread w κ F) :
    IsKappaSpread w κ hκ F := by
  obtain ⟨hw, hcard_ge, hlink⟩ := hF
  have hcard_pos : (0 : ℝ) < F.card := lt_of_lt_of_le (pow_pos (by linarith) w) hcard_ge
  refine ⟨fun _ ↦ (F.card : ℚ)⁻¹, hw, fun _ _ ↦ by positivity, ?_, ?_⟩
  · simp only [kappaProfile, zero_le, ↓reduceIte, pow_zero, subWeight, Rat.cast_inv,
      Rat.cast_natCast, sum_const, nsmul_eq_mul]
    rw [mul_inv_cancel₀ hcard_pos.ne']
  · intro T hT
    by_cases hTw : T.card ≤ w
    · simp only [kappaProfile, hTw, ↓reduceIte, linkWeight, Rat.cast_inv, Rat.cast_natCast,
        sum_const, nsmul_eq_mul]
      rw [← card_setLink]
      exact (div_le_iff₀ hcard_pos).2 (hlink T hT)
    · have hemp : F.filter (T ⊆ ·) = ∅ := by
        rw [filter_eq_empty_iff]
        intro S hS hTS
        exact hTw ((card_le_card hTS).trans (hw S hS))
      simp [kappaProfile, hTw, linkWeight, hemp]

/-- Width monotonicity of `IsKappaSpread`: an `ℓ`-width `κ`-spread family is `w`-width `κ`-spread
whenever `ℓ ≤ w`. -/
public theorem IsKappaSpread.mono_width {α : Type*} [DecidableEq α]
    {ℓ w : ℕ} (hℓw : ℓ ≤ w) {κ : ℝ} (hκ : 1 ≤ κ) {F : Finset (Finset α)}
    (hF : IsKappaSpread ℓ κ hκ F) :
    IsKappaSpread w κ hκ F := by
  obtain ⟨σ, hℓ, hσ0, htot, hlink⟩ := hF
  refine ⟨σ, fun S hS ↦ (hℓ S hS).trans hℓw, hσ0, ?_, ?_⟩
  · simpa [kappaProfile] using htot
  · intro T hT
    by_cases hTℓ : T.card ≤ ℓ
    · have hTw : T.card ≤ w := hTℓ.trans hℓw
      have h1 := hlink T hT
      simpa [kappaProfile, hTℓ, hTw] using h1
    · have hemp : F.filter (T ⊆ ·) = ∅ := by
        rw [filter_eq_empty_iff]
        intro S hS hTS
        exact hTℓ ((card_le_card hTS).trans (hℓ S hS))
      have h0 : linkWeight σ F T = 0 := by simp [linkWeight, hemp]
      rw [h0]
      exact (kappaProfile κ hκ w).nonneg T.card

/-- A weight profile `s` is `(α, β)`-satisfying when every `s`-spread set system on a finite ground
set is `(α, β)`-satisfying. -/
public def IsSatisfyingProfile {w : ℕ} (α_prob β_err : ℝ) (s : WeightProfile w) : Prop :=
  ∀ (n : ℕ) (F : Finset (Finset (Fin n))), IsSpread s F → IsSatisfying α_prob β_err F

/-- Characterization of `IsSatisfyingProfile`. -/
public theorem isSatisfyingProfile_iff {w : ℕ} {α_prob β_err : ℝ} {s : WeightProfile w} :
    IsSatisfyingProfile α_prob β_err s ↔
      ∀ (n : ℕ) (F : Finset (Finset (Fin n))), IsSpread s F → IsSatisfying α_prob β_err F :=
  Iff.rfl

/-- Universe-polymorphic instantiation of `IsSatisfyingProfile` on an arbitrary ground type `α`. -/
public theorem IsSatisfyingProfile.apply_univ {w : ℕ} {α_prob β_err : ℝ} {s : WeightProfile w}
    (hsat : IsSatisfyingProfile α_prob β_err s)
    {α : Type*} [DecidableEq α] {F : Finset (Finset α)} (hF : IsSpread s F) :
    IsSatisfying α_prob β_err F := by
  classical
  obtain ⟨σ, hspread⟩ := isSpread_iff.1 hF
  obtain ⟨hw_sys, hσnonneg, hσtot, hσlink⟩ := isSpreadWeighted_iff.1 hspread
  have hw := isWSetSystem_iff.1 hw_sys
  have hsat_fn := isSatisfyingProfile_iff.1 hsat
  let U := F.biUnion id
  by_cases hU : U.card = 0
  · have hFsub : F ⊆ {∅} := by
      intro S hS
      rw [mem_singleton, ← subset_empty]
      have hSU : S ⊆ U := subset_biUnion_of_mem id hS
      rwa [card_eq_zero.1 hU] at hSU
    have hFne : F.Nonempty := by
      by_contra hnot
      rw [not_nonempty_iff_eq_empty] at hnot
      subst hnot
      have h0 := s.zero_pos
      rw [subWeight_empty] at hσtot
      linarith
    have hFeq : F = {∅} := Subset.antisymm hFsub (singleton_subset_iff.2 (by
      obtain ⟨S, hS⟩ := hFne
      exact (mem_singleton.1 (hFsub hS)) ▸ hS))
    let F₀ : Finset (Finset (Fin 0)) := {∅}
    have hF₀spread : IsSpread s F₀ := by
      refine isSpread_iff.2 ⟨fun _ ↦ σ ∅, isSpreadWeighted_iff.2 ⟨isWSetSystem_iff.2 ?_, ?_, ?_,
        ?_⟩⟩
      · intro S hS
        simp [mem_singleton.1 hS]
      · intro S hS
        simpa [mem_singleton.1 hS] using hσnonneg ∅ (hFeq ▸ mem_singleton_self ∅)
      · simpa [F₀, subWeight_eq_sum, hFeq] using hσtot
      · intro T hT
        obtain ⟨x, -⟩ := hT
        exact Fin.elim0 x
    have h₀ := isSatisfying_iff.1 (hsat_fn 0 F₀ hF₀spread)
    rw [isSatisfying_iff, hFeq]
    simpa [F₀] using h₀
  · let e : ↥U ≃ Fin U.card := U.equivFin
    let toFin : α → Fin U.card := fun x ↦
      if hx : x ∈ U then e ⟨x, hx⟩ else ⟨0, Nat.pos_of_ne_zero hU⟩
    have hinjOn : ∀ S ∈ F, Set.InjOn toFin S := by
      intro S hS x hx y hy hxy
      have hxU : x ∈ U := subset_biUnion_of_mem id hS hx
      have hyU : y ∈ U := subset_biUnion_of_mem id hS hy
      simp only [toFin, hxU, hyU, ↓reduceDIte] at hxy
      exact congrArg Subtype.val (e.injective hxy)
    have hFinj : Set.InjOn (fun S : Finset α ↦ S.image toFin) F := by
      intro S₁ hS₁ S₂ hS₂ h12
      dsimp only at h12
      ext x
      constructor
      · intro hx
        have hmem : toFin x ∈ S₂.image toFin := by
          rw [← h12]
          exact mem_image_of_mem toFin hx
        obtain ⟨y, hy, hyx⟩ := mem_image.1 hmem
        have hxU : x ∈ U := subset_biUnion_of_mem id hS₁ hx
        have hyU : y ∈ U := subset_biUnion_of_mem id hS₂ hy
        simp only [toFin, hxU, hyU, ↓reduceDIte] at hyx
        have : x = y := (congrArg Subtype.val (e.injective hyx)).symm
        rwa [this]
      · intro hx
        have hmem : toFin x ∈ S₁.image toFin := by
          rw [h12]
          exact mem_image_of_mem toFin hx
        obtain ⟨y, hy, hyx⟩ := mem_image.1 hmem
        have hxU : x ∈ U := subset_biUnion_of_mem id hS₂ hx
        have hyU : y ∈ U := subset_biUnion_of_mem id hS₁ hy
        simp only [toFin, hxU, hyU, ↓reduceDIte] at hyx
        have : x = y := (congrArg Subtype.val (e.injective hyx)).symm
        rwa [this]
    let fromFin : Fin U.card → α := fun i ↦ (e.symm i).1
    have hleft : ∀ x ∈ U, fromFin (toFin x) = x := by
      intro x hxU
      simp [fromFin, toFin, hxU]
    have hright : ∀ i : Fin U.card, toFin (fromFin i) = i := by
      intro i
      have hxU : fromFin i ∈ U := (e.symm i).2
      simp [fromFin, toFin, hxU]
    let F' : Finset (Finset (Fin U.card)) := F.image fun S ↦ S.image toFin
    let σ' : Finset (Fin U.card) → ℚ := fun A ↦ σ (A.image fromFin)
    have hretract : ∀ S ∈ F, (S.image toFin).image fromFin = S := by
      intro S hS
      ext x
      simp only [mem_image]
      constructor
      · rintro ⟨i, ⟨y, hyS, rfl⟩, rfl⟩
        rwa [hleft y (subset_biUnion_of_mem id hS hyS)]
      · intro hxS
        exact ⟨toFin x, ⟨x, hxS, rfl⟩, hleft x (subset_biUnion_of_mem id hS hxS)⟩
    have hF'spread : IsSpread s F' := by
      refine isSpread_iff.2 ⟨σ', isSpreadWeighted_iff.2 ⟨isWSetSystem_iff.2 ?_, ?_, ?_, ?_⟩⟩
      · intro A hA
        obtain ⟨S, hS, rfl⟩ := mem_image.1 hA
        rw [card_image_of_injOn (hinjOn S hS)]
        exact hw S hS
      · intro A hA
        obtain ⟨S, hS, rfl⟩ := mem_image.1 hA
        simp only [σ', hretract S hS]
        exact hσnonneg S hS
      · simp only [subWeight_eq_sum, F', sum_image hFinj, σ']
        rw [sum_congr rfl fun S hS ↦ by rw [hretract S hS], ← subWeight_eq_sum]
        exact hσtot
      · intro T hT
        have hfromInj : Function.Injective fromFin :=
          Function.LeftInverse.injective hright
        let T₀ : Finset α := T.image fromFin
        have hT₀card : T₀.card = T.card := card_image_of_injective T hfromInj
        have hT₀ne : T₀.Nonempty := hT.image fromFin
        have hfilter : linkWeight σ' F' T = linkWeight σ F T₀ := by
          simp only [linkWeight_eq_sum, F', filter_image,
            sum_image (hFinj.mono (filter_subset _ _)), σ']
          have hsub_iff : ∀ S ∈ F, T ⊆ S.image toFin ↔ T₀ ⊆ S := by
            intro S hS
            constructor
            · intro hTS x hxT₀
              obtain ⟨i, hiT, rfl⟩ := mem_image.1 hxT₀
              obtain ⟨y, hyS, hyi⟩ := mem_image.1 (hTS hiT)
              have : fromFin i = y := by
                have hyU : y ∈ U := subset_biUnion_of_mem id hS hyS
                rw [← hyi, hleft y hyU]
              rwa [this]
            · intro hT₀S i hiT
              have hxS : fromFin i ∈ S := hT₀S (mem_image_of_mem fromFin hiT)
              exact hright i ▸ mem_image_of_mem toFin hxS
          rw [filter_congr hsub_iff]
          exact sum_congr rfl fun S hS ↦ by rw [hretract S (mem_filter.1 hS).1]
        rw [hfilter, ← hT₀card]
        exact hσlink T₀ hT₀ne
    have hsatF' := isSatisfying_iff.1 (hsat_fn U.card F' hF'spread)
    rw [isSatisfying_iff]
    have hprob_eq : satProb α_prob F' = satProb α_prob F := by
      have hF'U : ∀ A ∈ F', A ⊆ univ := fun _ _ ↦ subset_univ _
      have hFU : ∀ S ∈ F, S ⊆ U := fun S hS ↦ subset_biUnion_of_mem id hS
      rw [← biasedEventProb_exists_subset_eq_satProb hF'U,
        ← biasedEventProb_exists_subset_eq_satProb hFU]
      have hfromInj : Function.Injective fromFin := Function.LeftInverse.injective hright
      rw [biasedEventProb_eq_sum_filter, biasedEventProb_eq_sum_filter]
      let φ : Finset (Fin U.card) ↪ Finset α :=
        ⟨fun R ↦ R.image fromFin, fun R₁ R₂ h ↦ by
          dsimp only at h
          ext i
          constructor
          · intro hi
            obtain ⟨j, hj, hij⟩ := mem_image.1 (h ▸ mem_image_of_mem fromFin hi)
            exact hfromInj hij ▸ hj
          · intro hi
            obtain ⟨j, hj, hij⟩ := mem_image.1 (h.symm ▸ mem_image_of_mem fromFin hi)
            exact hfromInj hij ▸ hj⟩
      have himg : (univ.powerset.filter fun R : Finset (Fin U.card) ↦ ∃ A ∈ F', A ⊆ R).map φ =
          U.powerset.filter fun R : Finset α ↦ ∃ S ∈ F, S ⊆ R := by
        ext R
        simp only [mem_map, mem_filter, mem_powerset, subset_univ, true_and, φ]
        constructor
        · rintro ⟨R', ⟨A, hAF', hAR'⟩, rfl⟩
          obtain ⟨S, hSF, rfl⟩ := mem_image.1 hAF'
          refine ⟨?_, S, hSF, ?_⟩
          · intro x hx
            obtain ⟨i, -, rfl⟩ := mem_image.1 hx
            exact (e.symm i).2
          · rw [← hretract S hSF]
            exact image_subset_image hAR'
        · rintro ⟨hRU, S, hSF, hSR⟩
          refine ⟨R.image toFin, ⟨S.image toFin, mem_image_of_mem _ hSF, image_subset_image hSR⟩,
            ?_⟩
          ext x
          change x ∈ (R.image toFin).image fromFin ↔ x ∈ R
          simp only [mem_image]
          constructor
          · rintro ⟨i, ⟨y, hyR, rfl⟩, rfl⟩
            rwa [hleft y (hRU hyR)]
          · intro hxR
            exact ⟨toFin x, ⟨x, hxR, rfl⟩, hleft x (hRU hxR)⟩
      rw [← himg, sum_map]
      refine sum_congr rfl fun R _ ↦ ?_
      change biasedWeight univ α_prob R = biasedWeight U α_prob (R.image fromFin)
      rw [biasedWeight_eq_mul_pow, biasedWeight_eq_mul_pow,
        card_image_of_injective R hfromInj, card_univ, Fintype.card_fin]
    rwa [← hprob_eq]

private lemma choose_le_pow (w ℓ : ℕ) : w.choose ℓ ≤ w ^ ℓ := by
  induction ℓ with
  | zero => simp
  | succ ℓ ih =>
    by_cases hw0 : w = 0
    · simp [hw0]
    · have hrec := Nat.choose_succ_right_eq w ℓ
      have h1 : w.choose (ℓ + 1) ≤ w.choose ℓ * w := by
        have hle : w.choose ℓ * (w - ℓ) ≤ w.choose ℓ * w :=
          Nat.mul_le_mul_left _ (Nat.sub_le w ℓ)
        have h2 : w.choose (ℓ + 1) * 1 ≤ w.choose (ℓ + 1) * (ℓ + 1) :=
          Nat.mul_le_mul_left _ (by omega)
        omega
      calc w.choose (ℓ + 1)
          ≤ w.choose ℓ * w := h1
        _ ≤ w ^ ℓ * w := Nat.mul_le_mul_right w ih
        _ = w ^ (ℓ + 1) := (pow_succ w ℓ).symm

private lemma geom_sum_Icc_lt_two_div {q : ℝ} (hq : 2 ≤ q) {w : ℕ} (hw : 1 ≤ w) :
    ∑ ℓ ∈ Icc 1 w, (1 / q) ^ ℓ < 2 / q := by
  have hq_pos : 0 < q := by linarith
  have h1q_pos : 0 < 1 / q := div_pos zero_lt_one hq_pos
  have hsub_ge : 1 / 2 ≤ 1 - 1 / q := by
    have : 1 / q ≤ 1 / 2 := one_div_le_one_div_of_le zero_lt_two hq
    linarith
  have hsub_pos : 0 < 1 - 1 / q := by linarith
  have htel : (1 - 1 / q) * ∑ ℓ ∈ Icc 1 w, (1 / q) ^ ℓ = 1 / q - (1 / q) ^ (w + 1) := by
    have hIcc : Icc 1 w = (range w).image (· + 1) := by
      ext m
      simp only [mem_Icc, mem_image, mem_range]
      exact ⟨fun ⟨h1, hm⟩ ↦ ⟨m - 1, by omega, by omega⟩,
        fun ⟨k, hk, hkm⟩ ↦ ⟨by omega, by omega⟩⟩
    rw [hIcc, sum_image (fun a _ b _ h ↦ by omega)]
    clear hIcc hw
    induction w with
    | zero => simp
    | succ k ih =>
      rw [sum_range_succ, mul_add, ih]
      simp only [pow_succ]
      ring
  have hpow_pos : 0 < (1 / q) ^ (w + 1) := pow_pos h1q_pos (w + 1)
  have hlt1 : (1 - 1 / q) * ∑ ℓ ∈ Icc 1 w, (1 / q) ^ ℓ < 1 / q := by linarith
  have hsum_pos : 0 < ∑ ℓ ∈ Icc 1 w, (1 / q) ^ ℓ := by
    refine sum_pos (fun ℓ _ ↦ pow_pos h1q_pos ℓ) ?_
    exact ⟨1, mem_Icc.2 ⟨le_rfl, hw⟩⟩
  have hle2 : (1 / 2 : ℝ) * ∑ ℓ ∈ Icc 1 w, (1 / q) ^ ℓ ≤
      (1 - 1 / q) * ∑ ℓ ∈ Icc 1 w, (1 / q) ^ ℓ :=
    mul_le_mul_of_nonneg_right hsub_ge hsum_pos.le
  have h2q : 2 / q = 2 * (1 / q) := by ring
  linarith

private lemma uniform_multiset_fail_lt {β ι : Type*} [DecidableEq β] [Fintype ι]
    {α_prob β_err : ℝ} (hα₀ : 0 < α_prob) (hα₁ : α_prob < 1)
    (hβ₀ : 0 < β_err) (_hβ₁ : β_err < 1) {w : ℕ} (hw : 2 ≤ w)
    (Xpad : Finset β) (Spad : ι → Finset β)
    (hSpad_sub : ∀ i : ι, Spad i ⊆ Xpad)
    (hSpad_card : ∀ i : ι, (Spad i).card = w)
    (hN_pos : (0 : ℝ) < (Fintype.card ι : ℝ))
    (hSpad_link : ∀ (i : ι) (R : Finset β),
      R ⊆ Spad i → R.Nonempty →
        (((univ : Finset ι).filter fun j ↦ R ⊆ Spad j).card : ℝ) ≤
          (max (4 * Real.log (1 / β_err)) 2 * (w : ℝ) / α_prob)⁻¹ ^ R.card *
            (Fintype.card ι : ℝ)) :
    biasedEventProb Xpad α_prob (fun R' ↦ ∀ i : ι, ¬ Spad i ⊆ R') < β_err := by
  classical
  let q : ℝ := max (4 * Real.log (1 / β_err)) 2
  have hq_ge2 : 2 ≤ q := le_max_right _ _
  have hq_pos : 0 < q := by linarith
  let κ : ℝ := q * (w : ℝ) / α_prob
  have hκ_pos : 0 < κ := div_pos (mul_pos hq_pos (Nat.cast_pos.2 (by omega))) hα₀
  let N : ℕ := Fintype.card ι
  let μ : ℝ := ∑ i : ι, α_prob ^ (Spad i).card
  let Δ : ℝ := ∑ i : ι, ∑ j ∈ (univ : Finset ι) with ¬ Disjoint (Spad i) (Spad j),
    α_prob ^ (Spad i ∪ Spad j).card
  have hμ_eq : μ = (N : ℝ) * α_prob ^ w := by
    simp only [μ, hSpad_card, sum_const, card_univ, N, nsmul_eq_mul]
  have hμ_pos : 0 < μ := by
    rw [hμ_eq]
    exact mul_pos hN_pos (pow_pos hα₀ w)
  have hμ_le_Δ : μ ≤ Δ := by
    refine sum_le_sum fun i _ ↦ ?_
    have hne_i : (Spad i).Nonempty := card_pos.1 (by rw [hSpad_card i]; omega)
    have hmem_i : i ∈ (univ : Finset ι).filter (fun j ↦ ¬ Disjoint (Spad i) (Spad j)) := by
      refine mem_filter.2 ⟨mem_univ i, ?_⟩
      rw [disjoint_self]
      exact hne_i.ne_empty
    have hle := single_le_sum (f := fun j ↦ α_prob ^ (Spad i ∪ Spad j).card)
      (fun j _ ↦ pow_nonneg hα₀.le _) hmem_i
    simpa [union_idempotent] using hle
  have hΔ_lt : Δ < 2 * μ ^ 2 / q := by
    have hrow_le : ∀ i : ι,
        (∑ j ∈ (univ : Finset ι) with ¬ Disjoint (Spad i) (Spad j),
            α_prob ^ (Spad i ∪ Spad j).card) ≤
          ∑ ℓ ∈ Icc 1 w, (w : ℝ) ^ ℓ * (κ⁻¹ ^ ℓ * (N : ℝ)) * α_prob ^ (2 * w - ℓ) := by
      intro i
      let NonempR := (Spad i).powerset.filter Finset.Nonempty
      have hmapsR : ∀ j ∈ (univ : Finset ι).filter (fun j ↦ ¬ Disjoint (Spad i) (Spad j)),
          Spad i ∩ Spad j ∈ NonempR := by
        intro j hj
        have hnd : ¬ Disjoint (Spad i) (Spad j) := (mem_filter.1 hj).2
        exact mem_filter.2 ⟨mem_powerset.2 inter_subset_left,
          not_disjoint_iff_nonempty_inter.1 hnd⟩
      rw [← sum_fiberwise_of_maps_to hmapsR]
      have hfibR : ∀ R ∈ NonempR,
          (∑ j ∈ ((univ : Finset ι).filter fun j ↦ ¬ Disjoint (Spad i) (Spad j)) with
              Spad i ∩ Spad j = R, α_prob ^ (Spad i ∪ Spad j).card) ≤
            (κ⁻¹ ^ R.card * (N : ℝ)) * α_prob ^ (2 * w - R.card) := by
        intro R hR
        obtain ⟨hRpow, hRne⟩ := mem_filter.1 hR
        have hRsub : R ⊆ Spad i := mem_powerset.1 hRpow
        have hun_card :
            ∀ j ∈ (((univ : Finset ι).filter fun j ↦ ¬ Disjoint (Spad i) (Spad j)).filter
                fun j ↦ Spad i ∩ Spad j = R),
              (Spad i ∪ Spad j).card = 2 * w - R.card := by
          intro j hj
          have hinter : Spad i ∩ Spad j = R := (mem_filter.1 hj).2
          have hadd := card_inter_add_card_union (Spad i) (Spad j)
          rw [hinter, hSpad_card i, hSpad_card j] at hadd
          omega
        rw [sum_congr rfl fun j hj ↦ by rw [hun_card j hj], sum_const, nsmul_eq_mul]
        refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg hα₀.le _)
        have hsub_j :
            (((univ : Finset ι).filter fun j ↦ ¬ Disjoint (Spad i) (Spad j)).filter
                fun j ↦ Spad i ∩ Spad j = R) ⊆
              (univ : Finset ι).filter fun j ↦ R ⊆ Spad j := by
          intro j hj
          have hinter : Spad i ∩ Spad j = R := (mem_filter.1 hj).2
          exact mem_filter.2 ⟨mem_univ j, hinter ▸ inter_subset_right⟩
        exact (Nat.cast_le.2 (card_le_card hsub_j)).trans (hSpad_link i R hRsub hRne)
      have hmaps_card : ∀ R ∈ NonempR, R.card ∈ Icc 1 w := by
        intro R hR
        obtain ⟨hRpow, hRne⟩ := mem_filter.1 hR
        exact mem_Icc.2 ⟨hRne.card_pos,
          (card_le_card (mem_powerset.1 hRpow)).trans_eq (hSpad_card i)⟩
      calc ∑ R ∈ NonempR,
              ∑ j ∈ ((univ : Finset ι).filter fun j ↦ ¬ Disjoint (Spad i) (Spad j)) with
                Spad i ∩ Spad j = R, α_prob ^ (Spad i ∪ Spad j).card
          ≤ ∑ R ∈ NonempR, (κ⁻¹ ^ R.card * (N : ℝ)) * α_prob ^ (2 * w - R.card) :=
            sum_le_sum hfibR
        _ = ∑ ℓ ∈ Icc 1 w, ∑ R ∈ NonempR with R.card = ℓ,
              (κ⁻¹ ^ R.card * (N : ℝ)) * α_prob ^ (2 * w - R.card) :=
            (sum_fiberwise_of_maps_to hmaps_card _).symm
        _ ≤ ∑ ℓ ∈ Icc 1 w, (w : ℝ) ^ ℓ * (κ⁻¹ ^ ℓ * (N : ℝ)) * α_prob ^ (2 * w - ℓ) := by
            refine sum_le_sum fun ℓ _ ↦ ?_
            rw [sum_congr rfl fun R hR ↦ by rw [(mem_filter.1 hR).2], sum_const, nsmul_eq_mul,
              ← mul_assoc]
            refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg hα₀.le _)
            refine mul_le_mul_of_nonneg_right ?_
              (mul_nonneg (pow_nonneg (inv_nonneg.2 hκ_pos.le) ℓ) hN_pos.le)
            have hsub_pow : (NonempR.filter fun R ↦ R.card = ℓ) ⊆ (Spad i).powersetCard ℓ := by
              intro R hR
              obtain ⟨hRN, hc⟩ := mem_filter.1 hR
              exact mem_powersetCard.2 ⟨mem_powerset.1 (mem_filter.1 hRN).1, hc⟩
            have hcard_le : (NonempR.filter fun R ↦ R.card = ℓ).card ≤ w ^ ℓ := by
              calc (NonempR.filter fun R ↦ R.card = ℓ).card
                  ≤ ((Spad i).powersetCard ℓ).card := card_le_card hsub_pow
                _ = w.choose ℓ := by rw [card_powersetCard, hSpad_card i]
                _ ≤ w ^ ℓ := choose_le_pow w ℓ
            exact_mod_cast hcard_le
    have hΔ_le_geom : Δ ≤ μ ^ 2 * ∑ ℓ ∈ Icc 1 w, (1 / q) ^ ℓ := by
      calc Δ
          ≤ ∑ _i : ι,
              ∑ ℓ ∈ Icc 1 w, (w : ℝ) ^ ℓ * (κ⁻¹ ^ ℓ * (N : ℝ)) * α_prob ^ (2 * w - ℓ) :=
            sum_le_sum fun i _ ↦ hrow_le i
        _ = (N : ℝ) *
              ∑ ℓ ∈ Icc 1 w, (w : ℝ) ^ ℓ * (κ⁻¹ ^ ℓ * (N : ℝ)) * α_prob ^ (2 * w - ℓ) := by
            rw [sum_const, card_univ, nsmul_eq_mul]
        _ = μ ^ 2 * ∑ ℓ ∈ Icc 1 w, (1 / q) ^ ℓ := by
            rw [hμ_eq, mul_sum, mul_sum]
            refine sum_congr rfl fun ℓ hℓ ↦ ?_
            obtain ⟨_, hℓw⟩ := mem_Icc.1 hℓ
            have hw_pos : (0 : ℝ) < w := Nat.cast_pos.2 (by omega)
            have hα_split : α_prob ^ (2 * w - ℓ) = (α_prob ^ w) ^ 2 * α_prob⁻¹ ^ ℓ := by
              calc α_prob ^ (2 * w - ℓ)
                  = α_prob ^ (2 * w - ℓ) * (α_prob ^ ℓ * α_prob⁻¹ ^ ℓ) := by
                    rw [← mul_pow, mul_inv_cancel₀ hα₀.ne', one_pow, mul_one]
                _ = α_prob ^ (2 * w) * α_prob⁻¹ ^ ℓ := by
                    rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel (by omega : ℓ ≤ 2 * w)]
                _ = (α_prob ^ w) ^ 2 * α_prob⁻¹ ^ ℓ := by
                    rw [mul_comm 2 w, pow_mul]
            have hratio : (w : ℝ) * κ⁻¹ * α_prob⁻¹ = 1 / q := by
              simp only [κ]
              field_simp [hq_pos.ne', hw_pos.ne', hα₀.ne']
            rw [hα_split]
            calc (N : ℝ) * ((w : ℝ) ^ ℓ * (κ⁻¹ ^ ℓ * (N : ℝ)) *
                    ((α_prob ^ w) ^ 2 * α_prob⁻¹ ^ ℓ))
                = ((N : ℝ) * α_prob ^ w) ^ 2 * ((w : ℝ) ^ ℓ * κ⁻¹ ^ ℓ * α_prob⁻¹ ^ ℓ) := by ring
              _ = ((N : ℝ) * α_prob ^ w) ^ 2 * ((w : ℝ) * κ⁻¹ * α_prob⁻¹) ^ ℓ := by
                  rw [← mul_pow, ← mul_pow]
              _ = ((N : ℝ) * α_prob ^ w) ^ 2 * (1 / q) ^ ℓ := by rw [hratio]
    have hgeom_lt := geom_sum_Icc_lt_two_div hq_ge2 (by omega : 1 ≤ w)
    calc Δ
        ≤ μ ^ 2 * ∑ ℓ ∈ Icc 1 w, (1 / q) ^ ℓ := hΔ_le_geom
      _ < μ ^ 2 * (2 / q) := mul_lt_mul_of_pos_left hgeom_lt (sq_pos_of_pos hμ_pos)
      _ = 2 * μ ^ 2 / q := by ring
  have hjanson := janson_inequality Xpad hα₀.le hα₁.le Spad hSpad_sub hμ_pos hμ_le_Δ
  have hΔ_pos : 0 < Δ := lt_of_lt_of_le hμ_pos hμ_le_Δ
  have hexp_lt : Real.exp (- (μ ^ 2 / (2 * Δ))) < β_err := by
    have hq4_lt : q / 4 < μ ^ 2 / (2 * Δ) := by
      rw [div_lt_div_iff₀ (by norm_num : (0 : ℝ) < 4) (mul_pos zero_lt_two hΔ_pos)]
      have h1 : Δ * q < 2 * μ ^ 2 := (lt_div_iff₀ hq_pos).1 hΔ_lt
      linarith
    have hq_ge_log : Real.log (1 / β_err) ≤ q / 4 := by
      have : 4 * Real.log (1 / β_err) ≤ q := le_max_left _ _
      linarith
    have hneg_log : - Real.log (1 / β_err) = Real.log β_err := by
      rw [one_div, Real.log_inv, neg_neg]
    calc Real.exp (- (μ ^ 2 / (2 * Δ)))
        < Real.exp (- (q / 4)) := Real.exp_lt_exp.2 (neg_lt_neg hq4_lt)
      _ ≤ Real.exp (- Real.log (1 / β_err)) := Real.exp_le_exp.2 (neg_le_neg hq_ge_log)
      _ = Real.exp (Real.log β_err) := by rw [hneg_log]
      _ = β_err := Real.exp_log hβ₀
  exact lt_of_le_of_lt hjanson hexp_lt

/-- Linear-spread satisfyingness: for `0 < α, β < 1`, `w ≥ 2`, and
`κ = max (4 * log (1 / β)) 2 * w / α`, every `s`-spread weighted `w`-set system satisfying
`s_i ≤ κ ^ (-i) * s_0` (`1 ≤ i ≤ w`) is `(α, β)`-satisfying. -/
public theorem isSatisfying_of_isSpreadWeighted_linear {α : Type*} [DecidableEq α]
    {α_prob β_err : ℝ} (hα₀ : 0 < α_prob) (hα₁ : α_prob < 1)
    (hβ₀ : 0 < β_err) (hβ₁ : β_err < 1) {w : ℕ} (hw : 2 ≤ w)
    {s : WeightProfile w} {F : Finset (Finset α)} {σ : Finset α → ℚ}
    (hspread : IsSpreadWeighted s F σ)
    (hs : ∀ i, 1 ≤ i → i ≤ w →
      s.val i ≤ (max (4 * Real.log (1 / β_err)) 2 * (w : ℝ) / α_prob)⁻¹ ^ i * s.val 0) :
    IsSatisfying α_prob β_err F := by
  classical
  by_cases hempty : ∅ ∈ F
  · rw [isSatisfying_iff, satProb_eq_biasedEventProb_biUnion]
    have h1 : biasedEventProb (F.biUnion id) α_prob (fun R ↦ ∃ S ∈ F, S ⊆ R) = 1 := by
      rw [biasedEventProb_eq_sum_filter]
      have hfilt : ((F.biUnion id).powerset.filter fun R ↦ ∃ S ∈ F, S ⊆ R) =
          (F.biUnion id).powerset := by
        ext R
        simp only [mem_filter, and_iff_left_iff_imp]
        exact fun _ ↦ ⟨∅, hempty, empty_subset R⟩
      rw [hfilt, sum_biasedWeight_powerset]
    linarith
  obtain ⟨hw_sys, hσ0, htot, hlink⟩ := isSpreadWeighted_iff.1 hspread
  rw [isWSetSystem_iff] at hw_sys
  let q : ℝ := max (4 * Real.log (1 / β_err)) 2
  have hq_ge2 : 2 ≤ q := le_max_right _ _
  have hq_pos : 0 < q := by linarith
  let κ : ℝ := q * (w : ℝ) / α_prob
  have hκ_ge1 : 1 ≤ κ := by
    have hw_ge2 : (2 : ℝ) ≤ w := by exact_mod_cast hw
    have hprod : 4 ≤ q * (w : ℝ) := by nlinarith
    exact (one_le_div hα₀).2 (by linarith)
  have hκ_pos : 0 < κ := by linarith
  let Fpos := F.filter fun S ↦ 0 < σ S
  have htot_pos_eq : subWeight σ Fpos = subWeight σ F := by
    rw [subWeight_eq_sum, subWeight_eq_sum]
    refine sum_subset (filter_subset _ F) fun S hSF hSnot ↦ ?_
    have hle : σ S ≤ 0 := not_lt.1 fun hgt ↦ hSnot (mem_filter.2 ⟨hSF, hgt⟩)
    have hge : 0 ≤ σ S := hσ0 S hSF
    have heq : σ S = 0 := le_antisymm hle hge
    simp [heq]
  have hFpos_ne : Fpos.Nonempty := by
    by_contra hnot
    rw [not_nonempty_iff_eq_empty] at hnot
    rw [hnot, subWeight_empty] at htot_pos_eq
    linarith [s.zero_pos, htot]
  let D : ℕ := ∏ S ∈ Fpos, (σ S).den
  have hD_pos_nat : 0 < D := prod_pos fun S _ ↦ (σ S).den_pos
  have hD_pos : (0 : ℝ) < D := Nat.cast_pos.2 hD_pos_nat
  let aNat : Finset α → ℕ := fun S ↦
    (σ S).num.toNat * ∏ T ∈ Fpos.erase S, (σ T).den
  have haNat_eq : ∀ S ∈ Fpos, (aNat S : ℝ) = (D : ℝ) * (σ S : ℝ) := by
    intro S hS
    have hσpos : 0 < σ S := (mem_filter.1 hS).2
    have hnum_nonneg : 0 ≤ (σ S).num := Rat.num_nonneg.2 hσpos.le
    have hnum_cast : (((σ S).num.toNat : ℕ) : ℚ) = ((σ S).num : ℚ) := by
      exact_mod_cast Int.toNat_of_nonneg hnum_nonneg
    have hD_split : D = (σ S).den * ∏ T ∈ Fpos.erase S, (σ T).den :=
      (mul_prod_erase Fpos (fun T ↦ (σ T).den) hS).symm
    have hrat : (aNat S : ℚ) = (D : ℚ) * σ S := by
      simp only [aNat, Nat.cast_mul, Nat.cast_prod, hnum_cast, hD_split,
        ← Rat.mul_den_eq_num (σ S)]
      ring
    exact_mod_cast hrat
  let L : ℕ := Nat.ceil (κ ^ w / ((D : ℝ) * s.val 0)) + 1
  have hL_pos_nat : 0 < L := Nat.succ_pos _
  have hL_pos : (0 : ℝ) < L := Nat.cast_pos.2 hL_pos_nat
  have hLD_s0_ge : κ ^ w ≤ (L : ℝ) * (D : ℝ) * s.val 0 := by
    have hDs0_pos : 0 < (D : ℝ) * s.val 0 := mul_pos hD_pos s.zero_pos
    have hceil : κ ^ w / ((D : ℝ) * s.val 0) ≤ (L : ℝ) := by
      calc κ ^ w / ((D : ℝ) * s.val 0)
          ≤ (Nat.ceil (κ ^ w / ((D : ℝ) * s.val 0)) : ℝ) := Nat.le_ceil _
        _ ≤ L := by exact_mod_cast Nat.le_succ _
    have := (div_le_iff₀ hDs0_pos).1 hceil
    linarith
  let mult : ↥Fpos → ℕ := fun S ↦ L * aNat S.1
  let ι := Σ S : ↥Fpos, Fin (mult S)
  let N : ℕ := Fintype.card ι
  have hN_eq_sum : (N : ℝ) = (L : ℝ) * (D : ℝ) * subWeight σ Fpos := by
    have hcard : N = ∑ S ∈ Fpos, L * aNat S := by
      simp only [N, ι, Fintype.card_sigma, Fintype.card_fin, mult]
      exact sum_attach Fpos fun S ↦ L * aNat S
    rw [hcard, Nat.cast_sum, subWeight_eq_sum, mul_sum]
    refine sum_congr rfl fun S hS ↦ ?_
    rw [Nat.cast_mul, haNat_eq S hS, mul_assoc]
  have hN_ge_s0 : (L : ℝ) * (D : ℝ) * s.val 0 ≤ (N : ℝ) := by
    rw [hN_eq_sum, htot_pos_eq]
    exact mul_le_mul_of_nonneg_left htot (mul_nonneg hL_pos.le hD_pos.le)
  have hN_ge_κw : κ ^ w ≤ (N : ℝ) := hLD_s0_ge.trans hN_ge_s0
  have hN_pos : (0 : ℝ) < (N : ℝ) := lt_of_lt_of_le (pow_pos hκ_pos w) hN_ge_κw
  let Dummy := ι × ℕ
  let X := F.biUnion id
  let Dset : Finset Dummy := (univ : Finset ι) ×ˢ range w
  let Xpad : Finset (α ⊕ Dummy) := X.image Sum.inl ∪ Dset.image Sum.inr
  let Spad : ι → Finset (α ⊕ Dummy) := fun i ↦
    i.1.1.image Sum.inl ∪
      ((range (w - i.1.1.card)).image (fun r ↦ (i, r))).image Sum.inr
  have hSpad_sub : ∀ i : ι, Spad i ⊆ Xpad := by
    intro i x hx
    rcases mem_union.1 hx with hxl | hxr
    · obtain ⟨a, haS, rfl⟩ := mem_image.1 hxl
      have hSF : i.1.1 ∈ F := (mem_filter.1 i.1.2).1
      exact mem_union_left _ (mem_image_of_mem Sum.inl (subset_biUnion_of_mem id hSF haS))
    · obtain ⟨d, hd, rfl⟩ := mem_image.1 hxr
      obtain ⟨r, hr, rfl⟩ := mem_image.1 hd
      have hrw : r < w := lt_of_lt_of_le (mem_range.1 hr) (Nat.sub_le w _)
      exact mem_union_right _ (mem_image_of_mem Sum.inr (mem_product.2 ⟨mem_univ i,
        mem_range.2 hrw⟩))
  have hSpad_card : ∀ i : ι, (Spad i).card = w := by
    intro i
    have hSF : i.1.1 ∈ F := (mem_filter.1 i.1.2).1
    have hSw : i.1.1.card ≤ w := hw_sys i.1.1 hSF
    have hd : Disjoint (i.1.1.image Sum.inl)
        (((range (w - i.1.1.card)).image (fun r ↦ (i, r))).image Sum.inr) := by
      refine disjoint_left.2 fun x h1 h2 ↦ ?_
      obtain ⟨a, -, rfl⟩ := mem_image.1 h1
      obtain ⟨d, -, hd_eq⟩ := mem_image.1 h2
      cases hd_eq
    rw [card_union_of_disjoint hd, card_image_of_injective _ Sum.inl_injective,
      card_image_of_injective _ Sum.inr_injective,
      card_image_of_injective _ (fun r₁ r₂ h ↦ (Prod.mk.inj h).2), card_range]
    omega
  have hSpad_link : ∀ (i : ι) (R : Finset (α ⊕ Dummy)),
      R ⊆ Spad i → R.Nonempty →
        (((univ : Finset ι).filter fun j ↦ R ⊆ Spad j).card : ℝ) ≤ κ⁻¹ ^ R.card * (N : ℝ) := by
    intro i R hRsub hRne
    have hRw : R.card ≤ w := (card_le_card hRsub).trans_eq (hSpad_card i)
    by_cases hhas_dummy : ∃ d : Dummy, Sum.inr d ∈ R
    · obtain ⟨d, hdR⟩ := hhas_dummy
      have hdi : d.1 = i := by
        rcases mem_union.1 (hRsub hdR) with h1 | h2
        · obtain ⟨a, -, ha⟩ := mem_image.1 h1
          cases ha
        · obtain ⟨d', hd', hd_eq⟩ := mem_image.1 h2
          obtain ⟨r, -, rfl⟩ := mem_image.1 hd'
          cases Sum.inr.inj hd_eq
          rfl
      have hsub_single : ((univ : Finset ι).filter fun j ↦ R ⊆ Spad j) ⊆ {i} := by
        intro j hj
        have hRj : R ⊆ Spad j := (mem_filter.1 hj).2
        rcases mem_union.1 (hRj hdR) with h1 | h2
        · obtain ⟨a, -, ha⟩ := mem_image.1 h1
          cases ha
        · obtain ⟨d', hd', hd_eq⟩ := mem_image.1 h2
          obtain ⟨r, -, rfl⟩ := mem_image.1 hd'
          have hdj : (j, r) = d := Sum.inr.inj hd_eq
          exact mem_singleton.2 ((congrArg Prod.fst hdj).trans hdi)
      have hcard_le1 : (((univ : Finset ι).filter fun j ↦ R ⊆ Spad j).card : ℝ) ≤ 1 := by
        have h1 : ((univ : Finset ι).filter fun j ↦ R ⊆ Spad j).card ≤ ({i} : Finset ι).card :=
          card_le_card hsub_single
        rw [card_singleton] at h1
        exact_mod_cast h1
      have h1_le : 1 ≤ κ⁻¹ ^ R.card * (N : ℝ) := by
        have hpow_le : κ ^ R.card ≤ (N : ℝ) := (pow_le_pow_right₀ hκ_ge1 hRw).trans hN_ge_κw
        have hpos : 0 < κ ^ R.card := pow_pos hκ_pos R.card
        rw [inv_pow, inv_mul_eq_div, one_le_div hpos]
        exact hpow_le
      exact hcard_le1.trans h1_le
    · push Not at hhas_dummy
      let T : Finset α := i.1.1.filter fun a ↦ Sum.inl a ∈ R
      have hR_eq : R = T.image Sum.inl := by
        ext x
        simp only [T, mem_image, mem_filter]
        constructor
        · intro hxR
          rcases mem_union.1 (hRsub hxR) with h1 | h2
          · obtain ⟨a, ha, rfl⟩ := mem_image.1 h1
            exact ⟨a, ⟨ha, hxR⟩, rfl⟩
          · obtain ⟨d, -, rfl⟩ := mem_image.1 h2
            exact absurd hxR (hhas_dummy d)
        · rintro ⟨a, ⟨-, hxR⟩, rfl⟩
          exact hxR
      have hTcard : T.card = R.card := by
        rw [hR_eq, card_image_of_injective _ Sum.inl_injective]
      have hTne : T.Nonempty := by
        obtain ⟨x, hx⟩ := hRne
        rw [hR_eq] at hx
        obtain ⟨a, ha, -⟩ := mem_image.1 hx
        exact ⟨a, ha⟩
      have hTw : T.card ≤ w := hTcard.trans_le hRw
      have hTge1 : 1 ≤ T.card := hTne.card_pos
      have hj_iff : ∀ j : ι, R ⊆ Spad j ↔ T ⊆ j.1.1 := by
        intro j
        rw [hR_eq]
        constructor
        · intro hsub a haT
          have hin : Sum.inl a ∈ Spad j := hsub (mem_image_of_mem Sum.inl haT)
          rcases mem_union.1 hin with h1 | h2
          · obtain ⟨b, hb, hab⟩ := mem_image.1 h1
            exact (Sum.inl.inj hab) ▸ hb
          · obtain ⟨d, -, hd_eq⟩ := mem_image.1 h2
            cases hd_eq
        · intro hsub x hx
          obtain ⟨a, haT, rfl⟩ := mem_image.1 hx
          exact mem_union_left _ (mem_image_of_mem Sum.inl (hsub haT))
      have hcount_eq :
          (((univ : Finset ι).filter fun j ↦ R ⊆ Spad j).card : ℝ) =
            (L : ℝ) * (D : ℝ) * linkWeight σ Fpos T := by
        have hfilt_eq : ((univ : Finset ι).filter fun j ↦ R ⊆ Spad j) =
            (Fpos.attach.filter fun S ↦ T ⊆ S.1).biUnion
              fun S ↦ (univ : Finset (Fin (mult S))).image fun m ↦ (⟨S, m⟩ : ι) := by
          ext ⟨S, m⟩
          simp only [mem_filter, mem_univ, true_and, hj_iff, mem_biUnion, mem_attach, mem_image]
          refine ⟨fun h ↦ ⟨S, h, m, rfl⟩, ?_⟩
          rintro ⟨S', hTS', m', heq⟩
          cases heq
          exact hTS'
        have hdisj :
            ((Fpos.attach.filter fun S ↦ T ⊆ S.1) : Set ↥Fpos).PairwiseDisjoint
              (fun S ↦ (univ : Finset (Fin (mult S))).image fun m ↦ (⟨S, m⟩ : ι)) := by
          intro S₁ _ S₂ _ hne
          refine disjoint_left.2 fun x hx₁ hx₂ ↦ hne ?_
          obtain ⟨m₁, -, rfl⟩ := mem_image.1 hx₁
          obtain ⟨m₂, -, heq⟩ := mem_image.1 hx₂
          exact (Sigma.mk.inj_iff.1 heq).1.symm
        rw [hfilt_eq, card_biUnion hdisj, Nat.cast_sum, linkWeight_eq_sum, mul_sum]
        have hsum_att :
            (∑ S ∈ Fpos.attach with T ⊆ S.1,
                (((univ : Finset (Fin (mult S))).image fun m ↦ (⟨S, m⟩ : ι)).card : ℝ)) =
              ∑ S ∈ Fpos.attach with T ⊆ S.1, (L * aNat S.1 : ℝ) := by
          refine sum_congr rfl fun S _ ↦ ?_
          rw [card_image_of_injective _ (fun m₁ m₂ h ↦ eq_of_heq (Sigma.mk.inj_iff.1 h).2),
            card_univ, Fintype.card_fin, Nat.cast_mul]
        rw [hsum_att, sum_filter,
          sum_attach Fpos (fun S ↦ if T ⊆ S then (L * aNat S : ℝ) else 0),
          ← sum_filter]
        refine sum_congr rfl fun S hS ↦ ?_
        rw [haNat_eq S (mem_filter.1 hS).1, mul_assoc]
      have hlink_pos_le : linkWeight σ Fpos T ≤ linkWeight σ F T := by
        rw [linkWeight_eq_sum, linkWeight_eq_sum]
        refine sum_le_sum_of_subset_of_nonneg ?_ ?_
        · intro S hS
          obtain ⟨hSFp, hTS⟩ := mem_filter.1 hS
          exact mem_filter.2 ⟨(mem_filter.1 hSFp).1, hTS⟩
        · intro S hS _
          exact_mod_cast hσ0 S (mem_filter.1 hS).1
      calc (((univ : Finset ι).filter fun j ↦ R ⊆ Spad j).card : ℝ)
          = (L : ℝ) * (D : ℝ) * linkWeight σ Fpos T := hcount_eq
        _ ≤ (L : ℝ) * (D : ℝ) * s.val T.card :=
            mul_le_mul_of_nonneg_left (hlink_pos_le.trans (hlink T hTne))
              (mul_nonneg hL_pos.le hD_pos.le)
        _ ≤ (L : ℝ) * (D : ℝ) * (κ⁻¹ ^ T.card * s.val 0) :=
            mul_le_mul_of_nonneg_left (hs T.card hTge1 hTw)
              (mul_nonneg hL_pos.le hD_pos.le)
        _ = κ⁻¹ ^ R.card * ((L : ℝ) * (D : ℝ) * s.val 0) := by
            rw [hTcard]
            ring
        _ ≤ κ⁻¹ ^ R.card * (N : ℝ) :=
            mul_le_mul_of_nonneg_left hN_ge_s0 (pow_nonneg (inv_nonneg.2 hκ_pos.le) _)
  have hfail_pad_lt :
      biasedEventProb Xpad α_prob (fun R' ↦ ∀ i : ι, ¬ Spad i ⊆ R') < β_err :=
    uniform_multiset_fail_lt hα₀ hα₁ hβ₀ hβ₁ hw Xpad Spad hSpad_sub hSpad_card hN_pos hSpad_link
  let Bset : Finset (α ⊕ Dummy) := Dset.image Sum.inr
  have hdisj_AB : Disjoint (X.image Sum.inl) Bset := by
    refine disjoint_left.2 fun x h1 h2 ↦ ?_
    obtain ⟨a, -, rfl⟩ := mem_image.1 h1
    obtain ⟨d, -, hd_eq⟩ := mem_image.1 h2
    cases hd_eq
  have hXpad_sdiff : Xpad \ Bset = X.image Sum.inl := union_sdiff_cancel_right hdisj_AB
  let Q : Finset (α ⊕ Dummy) → Prop := fun R' ↦ ¬ ∃ S ∈ F, S.image Sum.inl ⊆ R'
  have hQ_indep : biasedEventProb (X.image Sum.inl) α_prob Q = biasedEventProb Xpad α_prob Q := by
    rw [← hXpad_sdiff]
    refine biasedEventProb_sdiff_eq_of_indep subset_union_right α_prob fun R' _ ↦ ?_
    simp only [Q]
    refine not_congr (exists_congr fun S ↦ and_congr_right fun hSF ↦ ?_)
    constructor
    · intro hsub x hx
      refine mem_sdiff.2 ⟨hsub hx, ?_⟩
      have hxA : x ∈ X.image Sum.inl := by
        obtain ⟨a, haS, rfl⟩ := mem_image.1 hx
        exact mem_image_of_mem Sum.inl (subset_biUnion_of_mem id hSF haS)
      exact disjoint_left.1 hdisj_AB hxA
    · intro hsub
      exact hsub.trans sdiff_subset
  have hQ_le_pad :
      biasedEventProb Xpad α_prob Q ≤
        biasedEventProb Xpad α_prob (fun R' ↦ ∀ i : ι, ¬ Spad i ⊆ R') := by
    refine biasedEventProb_mono hα₀.le hα₁.le fun R' _ hQ i hsub ↦ hQ ?_
    exact ⟨i.1.1, (mem_filter.1 i.1.2).1, subset_union_left.trans hsub⟩
  have hQ_eq_X :
      biasedEventProb X α_prob (fun R ↦ ¬ ∃ S ∈ F, S ⊆ R) =
        biasedEventProb (X.image Sum.inl) α_prob Q := by
    rw [biasedEventProb_eq_sum_filter, biasedEventProb_eq_sum_filter]
    refine sum_nbij (fun R ↦ R.image Sum.inl) ?_ ?_ ?_ ?_
    · intro R hR
      obtain ⟨hRpow, hnot⟩ := mem_filter.1 hR
      refine mem_filter.2 ⟨mem_powerset.2 (image_subset_image (mem_powerset.1 hRpow)), ?_⟩
      rintro ⟨S, hSF, hSsub⟩
      refine hnot ⟨S, hSF, fun a ha ↦ ?_⟩
      obtain ⟨b, hbR, hab⟩ := mem_image.1 (hSsub (mem_image_of_mem Sum.inl ha))
      exact (Sum.inl.inj hab) ▸ hbR
    · intro R₁ _ R₂ _ heq
      dsimp only at heq
      ext a
      have h : Sum.inl (β := Dummy) a ∈ R₁.image Sum.inl ↔
          Sum.inl (β := Dummy) a ∈ R₂.image Sum.inl := by rw [heq]
      simpa [Sum.inl_injective.eq_iff] using h
    · intro R' hR'
      obtain ⟨hR'pow, hQ'⟩ := mem_filter.1 hR'
      let R : Finset α := X.filter fun a ↦ Sum.inl a ∈ R'
      have hR'_eq : R.image Sum.inl = R' := by
        ext x
        simp only [R, mem_image, mem_filter]
        constructor
        · rintro ⟨a, ⟨-, hx⟩, rfl⟩
          exact hx
        · intro hx
          obtain ⟨a, haX, rfl⟩ := mem_image.1 (mem_powerset.1 hR'pow hx)
          exact ⟨a, ⟨haX, hx⟩, rfl⟩
      refine ⟨R, mem_filter.2 ⟨mem_powerset.2 (filter_subset _ X), ?_⟩, hR'_eq⟩
      rintro ⟨S, hSF, hSR⟩
      exact hQ' ⟨S, hSF, hR'_eq ▸ image_subset_image hSR⟩
    · intro R _
      simp only [biasedWeight_eq_mul_pow, card_image_of_injective _ Sum.inl_injective]
  have hfail_X_lt : biasedEventProb X α_prob (fun R ↦ ¬ ∃ S ∈ F, S ⊆ R) < β_err := by
    rw [hQ_eq_X, hQ_indep]
    exact lt_of_le_of_lt hQ_le_pad hfail_pad_lt
  rw [isSatisfying_iff, satProb_eq_biasedEventProb_biUnion]
  have hcompl := biasedEventProb_add_compl X α_prob (fun R ↦ ∃ S ∈ F, S ⊆ R)
  linarith

/-- The geometric profile `kappaProfile κ` is `(α, β)`-satisfying whenever
`max (4 * log (1 / β)) 2 * w / α ≤ κ`. -/
public theorem isSatisfyingProfile_kappaProfile_linear
    {α_prob β_err : ℝ} (hα₀ : 0 < α_prob) (hα₁ : α_prob < 1)
    (hβ₀ : 0 < β_err) (hβ₁ : β_err < 1) {w : ℕ} (hw : 2 ≤ w)
    {κ : ℝ} (hκ_ge : max (4 * Real.log (1 / β_err)) 2 * (w : ℝ) / α_prob ≤ κ)
    (hκ : 1 ≤ κ) :
    IsSatisfyingProfile α_prob β_err (kappaProfile κ hκ w) := by
  rw [isSatisfyingProfile_iff]
  intro n F ⟨σ, hspread⟩
  refine isSatisfying_of_isSpreadWeighted_linear hα₀ hα₁ hβ₀ hβ₁ hw hspread fun i _ hiw ↦ ?_
  rw [kappaProfile_val_of_le κ hκ hiw, kappaProfile_val_zero, mul_one]
  have hbase_pos : 0 < max (4 * Real.log (1 / β_err)) 2 * (w : ℝ) / α_prob := by
    have hq_pos : 0 < max (4 * Real.log (1 / β_err)) 2 :=
      lt_of_lt_of_le zero_lt_two (le_max_right _ _)
    exact div_pos (mul_pos hq_pos (Nat.cast_pos.2 (by omega))) hα₀
  exact pow_le_pow_left₀ (inv_nonneg.2 (zero_le_one.trans hκ))
    (inv_anti₀ hbase_pos hκ_ge) i

/-- Maximal violating-kernel extraction: if `(1; κ⁻¹, ..., κ⁻w)` is `(α, β)`-satisfying (`κ > 1`),
every `w`-uniform set system of size strictly greater than `κ ^ w` contains an `(α, β)`-robust
sunflower. -/
public theorem containsRobustSunflower_of_isSatisfyingProfile {α : Type*} [DecidableEq α]
    {α_prob β_err : ℝ} (hα₀ : 0 < α_prob) (hα₁ : α_prob < 1)
    {w : ℕ} (hw : 2 ≤ w) {κ : ℝ} (hκ : 1 < κ)
    (hsat : IsSatisfyingProfile α_prob β_err (kappaProfile κ hκ.le w))
    {F : Finset (Finset α)} (hunif : IsWUniform w F) (hlarge : κ ^ w < (F.card : ℝ)) :
    ContainsRobustSunflower α_prob β_err F := by
  classical
  have hunif' := isWUniform_iff.1 hunif
  have hFcard_gt1 : (1 : ℝ) < F.card := lt_trans (one_lt_pow₀ hκ (by omega)) hlarge
  have hFcard_ge2 : 2 ≤ F.card := by
    have : 1 < F.card := by exact_mod_cast hFcard_gt1
    omega
  let U := F.biUnion id
  let Viol := U.powerset.filter fun K ↦
    K.Nonempty ∧ κ⁻¹ ^ K.card * (F.card : ℝ) < ((setLink F K).card : ℝ)
  by_cases hViol : Viol.Nonempty
  · obtain ⟨K, hKmem, hKmax⟩ := Viol.exists_maximalFor Finset.card hViol
    obtain ⟨hKpow, hKne, hKgt⟩ := mem_filter.1 hKmem
    have hKU : K ⊆ U := mem_powerset.1 hKpow
    have hKlt : K.card < w := by
      by_contra! hKge
      have hlink_le1 : (setLink F K).card ≤ 1 := by
        rw [card_setLink, card_le_one]
        intro S₁ hS₁ S₂ hS₂
        have heq₁ : K = S₁ := eq_of_subset_of_card_le (mem_filter.1 hS₁).2
          ((hunif' S₁ (mem_filter.1 hS₁).1) ▸ hKge)
        have heq₂ : K = S₂ := eq_of_subset_of_card_le (mem_filter.1 hS₂).2
          ((hunif' S₂ (mem_filter.1 hS₂).1) ▸ hKge)
        exact heq₁.symm.trans heq₂
      rcases eq_or_lt_of_le hKge with hKeq | hKw_gt
      · have hprod : 1 < κ⁻¹ ^ w * (F.card : ℝ) := by
          have hwpos : 0 < κ ^ w := pow_pos (by linarith) w
          have hmul : κ ^ w * (κ⁻¹ ^ w * (F.card : ℝ)) = (F.card : ℝ) := by
            rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ (by linarith), one_pow, one_mul]
          nlinarith
        rw [hKeq] at hprod
        have hlt1 : (1 : ℝ) < ((setLink F K).card : ℝ) := lt_trans hprod hKgt
        have : 1 < (setLink F K).card := by exact_mod_cast hlt1
        omega
      · have hemp : F.filter (K ⊆ ·) = ∅ := by
          rw [filter_eq_empty_iff]
          intro S hS hKS
          have := (card_le_card hKS).trans_eq (hunif' S hS)
          omega
        rw [card_setLink, hemp, card_empty, Nat.cast_zero] at hKgt
        have hnonneg : 0 ≤ κ⁻¹ ^ K.card * (F.card : ℝ) :=
          mul_nonneg (pow_nonneg (inv_nonneg.2 (by linarith)) K.card) (Nat.cast_nonneg F.card)
        linarith
    let G := F.filter (K ⊆ ·)
    have hGcard : (G.card : ℝ) = ((setLink F K).card : ℝ) := by rw [card_setLink]
    have hGlarge : κ ^ (w - K.card) < (G.card : ℝ) := by
      have hpos : 0 < κ⁻¹ ^ K.card := pow_pos (inv_pos.2 (by linarith)) K.card
      have h1 : κ ^ (w - K.card) = κ⁻¹ ^ K.card * κ ^ w := by
        have hκpos : 0 < κ ^ K.card := pow_pos (by linarith) K.card
        rw [inv_pow, inv_mul_eq_div, eq_div_iff hκpos.ne', ← pow_add, Nat.sub_add_cancel hKlt.le]
      rw [h1, hGcard]
      exact lt_trans (mul_lt_mul_of_pos_left hlarge hpos) hKgt
    have hGgt1 : (1 : ℝ) < G.card := lt_trans (one_lt_pow₀ hκ (by omega)) hGlarge
    have hGne : G.Nonempty := card_pos.1 (by
      have : 1 < G.card := by exact_mod_cast hGgt1
      omega)
    have hK_eq_ker : setSystemKernel G = K := by
      refine Subset.antisymm ?_ (subset_setSystemKernel hGne fun S hS ↦ (mem_filter.1 hS).2)
      by_contra hnot
      obtain ⟨x, hxker, hxK⟩ := not_subset.1 hnot
      let K' := insert x K
      have hxU : x ∈ U := by
        have hxG := (mem_setSystemKernel_iff hGne).1 hxker
        obtain ⟨S₀, hS₀⟩ := hGne
        exact subset_biUnion_of_mem id (mem_filter.1 hS₀).1 (hxG S₀ hS₀)
      have hK'U : K' ⊆ U := insert_subset hxU hKU
      have hfilt_eq : F.filter (K' ⊆ ·) = G := by
        ext S
        simp only [G, K', mem_filter, insert_subset_iff]
        refine ⟨fun h ↦ ⟨h.1, h.2.2⟩, fun h ↦ ⟨h.1, ?_, h.2⟩⟩
        exact (mem_setSystemKernel_iff hGne).1 hxker S (mem_filter.2 h)
      have hK'card_gt : K.card < K'.card := by
        rw [card_insert_of_notMem hxK]
        omega
      have hK'viol : K' ∈ Viol := by
        refine mem_filter.2 ⟨mem_powerset.2 hK'U, insert_nonempty x K, ?_⟩
        rw [card_setLink, hfilt_eq, hGcard]
        have hpow_lt : κ⁻¹ ^ K'.card < κ⁻¹ ^ K.card :=
          pow_lt_pow_right_of_lt_one₀ (inv_pos.2 (by linarith))
            (inv_lt_one_of_one_lt₀ hκ) hK'card_gt
        exact lt_trans (mul_lt_mul_of_pos_right hpow_lt (by linarith)) hKgt
      exact absurd (hKmax hK'viol hK'card_gt.le) (not_le.2 hK'card_gt)
    have hlinkG_eq : setLink G K = setLink F K := by
      ext P
      simp only [G, mem_setLink_iff, mem_filter]
      exact ⟨fun h ↦ ⟨h.1, h.2.1⟩, fun h ↦ ⟨h.1, h.2, subset_union_right⟩⟩
    have hFK_spread : IsUniformKappaSpread (w - K.card) κ (setLink F K) := by
      refine isUniformKappaSpread_iff.2 ⟨isWSetSystem_iff.2 ?_, hGcard ▸ hGlarge.le, ?_⟩
      · intro P hP
        obtain ⟨hPK, hPKF⟩ := mem_setLink_iff.1 hP
        have hcard_union := card_union_of_disjoint hPK
        have hPK_w := hunif' (P ∪ K) hPKF
        omega
      · intro T hT
        by_cases hTU : T ⊆ U \ K
        · have hKT : Disjoint K T := disjoint_of_subset_right hTU disjoint_sdiff_self_right
          rw [setLink_setLink F hKT]
          have hKTU : K ∪ T ⊆ U := union_subset hKU (hTU.trans sdiff_subset)
          have hKTcard : K.card < (K ∪ T).card := by
            rw [card_union_of_disjoint hKT]
            exact Nat.lt_add_of_pos_right hT.card_pos
          have hnotViol : K ∪ T ∉ Viol := fun hmem ↦
            absurd (hKmax hmem hKTcard.le) (not_le.2 hKTcard)
          have hle_KT : ((setLink F (K ∪ T)).card : ℝ) ≤
              κ⁻¹ ^ (K ∪ T).card * (F.card : ℝ) := by
            by_contra! hgt
            exact hnotViol (mem_filter.2 ⟨mem_powerset.2 hKTU, hKne.mono subset_union_left, hgt⟩)
          rw [card_union_of_disjoint hKT, pow_add] at hle_KT
          calc ((setLink F (K ∪ T)).card : ℝ)
              ≤ κ⁻¹ ^ T.card * (κ⁻¹ ^ K.card * (F.card : ℝ)) := by linarith
            _ ≤ κ⁻¹ ^ T.card * ((setLink F K).card : ℝ) :=
              mul_le_mul_of_nonneg_left hKgt.le (pow_nonneg (inv_nonneg.2 (by linarith)) _)
        · have hemp : (setLink F K).filter (T ⊆ ·) = ∅ := by
            rw [filter_eq_empty_iff]
            intro P hP hTP
            obtain ⟨hPK, hPKF⟩ := mem_setLink_iff.1 hP
            refine hTU fun x hxT ↦ mem_sdiff.2 ⟨?_, ?_⟩
            · exact subset_biUnion_of_mem id hPKF (mem_union_left K (hTP hxT))
            · exact disjoint_left.1 hPK (hTP hxT)
          rw [card_setLink, hemp, card_empty, Nat.cast_zero]
          exact mul_nonneg (pow_nonneg (inv_nonneg.2 (by linarith)) _) (Nat.cast_nonneg _)
    have hFK_sat : IsSatisfying α_prob β_err (setLink F K) :=
      hsat.apply_univ (isKappaSpread_iff.1
        ((hFK_spread.isKappaSpread hκ.le).mono_width (Nat.sub_le w K.card)))
    refine containsRobustSunflower_iff.2 ⟨G, filter_subset _ _, isRobustSunflower_iff.2 ⟨?_, ?_⟩⟩
    · rw [hK_eq_ker]
      intro hKG
      have := hunif' K (mem_filter.1 hKG).1
      omega
    · rwa [hK_eq_ker, hlinkG_eq]
  · rw [not_nonempty_iff_eq_empty, filter_eq_empty_iff] at hViol
    have hFspread : IsUniformKappaSpread w κ F := by
      refine isUniformKappaSpread_iff.2 ⟨hunif.isWSetSystem, hlarge.le, fun T hT ↦ ?_⟩
      by_cases hTU : T ⊆ U
      · by_contra! hgt
        exact hViol (mem_powerset.2 hTU) ⟨hT, hgt⟩
      · have hemp : F.filter (T ⊆ ·) = ∅ := by
          rw [filter_eq_empty_iff]
          intro S hS hTS
          exact hTU (hTS.trans (subset_biUnion_of_mem id hS))
        rw [card_setLink, hemp, card_empty, Nat.cast_zero]
        exact mul_nonneg (pow_nonneg (inv_nonneg.2 (by linarith)) _) (Nat.cast_nonneg _)
    have hFsat : IsSatisfying α_prob β_err F :=
      hsat.apply_univ (isKappaSpread_iff.1 (hFspread.isKappaSpread hκ.le))
    let K := setSystemKernel F
    have hKnot : K ∉ F := by
      intro hKF
      obtain ⟨S₁, hS₁, S₂, hS₂, hne⟩ := one_lt_card.1 (by omega : 1 < F.card)
      have hKS₁ : K = S₁ := eq_of_subset_of_card_le (setSystemKernel_subset hS₁)
        (by rw [hunif' K hKF, hunif' S₁ hS₁])
      have hKS₂ : K = S₂ := eq_of_subset_of_card_le (setSystemKernel_subset hS₂)
        (by rw [hunif' K hKF, hunif' S₂ hS₂])
      exact hne (hKS₁.symm.trans hKS₂)
    refine containsRobustSunflower_iff.2 ⟨F, Subset.rfl, isRobustSunflower_iff.2 ⟨hKnot, ?_⟩⟩
    rw [isSatisfying_iff] at hFsat ⊢
    refine lt_of_lt_of_le hFsat ?_
    have hFU : ∀ S ∈ F, S ⊆ U := fun S hS ↦ subset_biUnion_of_mem id hS
    have hFKU : ∀ P ∈ setLink F K, P ⊆ U := by
      intro P hP
      obtain ⟨-, hPKF⟩ := mem_setLink_iff.1 hP
      exact subset_union_left.trans (subset_biUnion_of_mem id hPKF)
    rw [← biasedEventProb_exists_subset_eq_satProb hFU,
      ← biasedEventProb_exists_subset_eq_satProb hFKU]
    refine biasedEventProb_mono hα₀.le hα₁.le fun R _ ↦ ?_
    rintro ⟨S, hSF, hSR⟩
    refine ⟨S \ K, mem_setLink_iff.2 ⟨sdiff_disjoint, ?_⟩, sdiff_subset.trans hSR⟩
    rwa [sdiff_union_of_subset (setSystemKernel_subset hSF)]

/-- Direct linear-spread robust-sunflower bound: for `0 < α, β < 1` and `w ≥ 2`, every `w`-uniform
set system of size strictly greater than `(max (4 * log (1 / β)) 2 * w / α) ^ w` contains an
`(α, β)`-robust sunflower. -/
public theorem containsRobustSunflower_of_card_gt_linear_pow {α : Type*} [DecidableEq α]
    {α_prob β_err : ℝ} (hα₀ : 0 < α_prob) (hα₁ : α_prob < 1)
    (hβ₀ : 0 < β_err) (hβ₁ : β_err < 1) {w : ℕ} (hw : 2 ≤ w)
    {F : Finset (Finset α)} (hunif : IsWUniform w F)
    (hlarge : (max (4 * Real.log (1 / β_err)) 2 * (w : ℝ) / α_prob) ^ w < (F.card : ℝ)) :
    ContainsRobustSunflower α_prob β_err F := by
  let κ : ℝ := max (4 * Real.log (1 / β_err)) 2 * (w : ℝ) / α_prob
  have hκ_gt1 : 1 < κ := by
    have hq_ge2 : (2 : ℝ) ≤ max (4 * Real.log (1 / β_err)) 2 := le_max_right _ _
    have hw_ge2 : (2 : ℝ) ≤ w := by exact_mod_cast hw
    have hprod : 4 ≤ max (4 * Real.log (1 / β_err)) 2 * (w : ℝ) := by nlinarith
    exact (one_lt_div hα₀).2 (by linarith)
  exact containsRobustSunflower_of_isSatisfyingProfile hα₀ hα₁ hw hκ_gt1
    (isSatisfyingProfile_kappaProfile_linear hα₀ hα₁ hβ₀ hβ₁ hw le_rfl hκ_gt1.le)
    hunif hlarge

end CslibFrontier
