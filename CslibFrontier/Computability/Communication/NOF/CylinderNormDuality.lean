/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Communication.NOF.CylinderNorm
import CslibFrontier.Foundations.LinearAlgebra.Matrix.Farkas
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Strong Linear-Programming Duality and Generalized Discrepancy for NOF Norms

This module develops the dual cylinder intersection norm `muDual` (`μ*`), establishes strong linear
programming duality for the approximate norms `muAlpha` and `muInfty` using Farkas's lemma and
compactness of the dual unit ball, proves `μ^∞(A) = 1 / disc(A)` with attainment, and derives the
generalized discrepancy lower bound for public-coin randomized NOF protocols.

## Main definitions

* `muDual`: dual cylinder intersection norm `μ*(Q) = max_Z |⟨Q, χ_Z⟩|`.
* `nofDiscrepancy`, `minDiscrepancy`: multiparty tensor discrepancy and minimum discrepancy over
  probability distributions.

## Main results

* `nofDiscrepancy_eq_cslib_discrepancy`: exact equality with `Cslib.Communication.NOF.discrepancy`.
* `muAlpha_eq_dual`, `muInfty_eq_dual`: strong LP duality for `μ^α(A)` and `μ^∞(A)`.
* `muInfty_eq_inv_minDiscrepancy`: `μ^∞(A) = 1 / disc(A)` with an attaining distribution.
* `randProtocol_generalized_discrepancy_bound`: generalized discrepancy bound for public-coin
  randomized NOF protocols.
-/

public section

open scoped BigOperators
open Cslib.BitString Cslib.Communication.NOF

namespace CslibFrontier.Computability.Communication.NOF

section DualityAndDiscrepancy

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {X : ι → Type*} [∀ i, Fintype (X i)]

/-- **Dual cylinder intersection norm `μ*(Q)`**):
`μ*(Q) = max_{Z cylinder intersection} |⟨Q, χ(Z)⟩|`. -/
noncomputable def muDual (Q : Tensor X) : ℝ :=
  ⨆ Z : CylInter X, |tensorInner Q (charTensor Z.1)|

/-- Every cylinder intersection satisfies `|⟨Q, χ(Z)⟩| ≤ μ*(Q)`. -/
theorem abs_tensorInner_charTensor_le_muDual (Q : Tensor X) {Z : Set (∀ i, X i)}
    (hZ : IsCylinderIntersection Z) :
    |tensorInner Q (charTensor Z)| ≤ muDual Q := by
  unfold muDual
  exact le_ciSup (Set.finite_range (fun S : CylInter X ↦ |tensorInner Q (charTensor S.1)|)).bddAbove
    (⟨Z, hZ⟩ : CylInter X)

/-- `μ*(Q)` is nonnegative. -/
theorem muDual_nonneg (Q : Tensor X) : 0 ≤ muDual Q :=
  (abs_nonneg _).trans (abs_tensorInner_charTensor_le_muDual Q isCylinderIntersection_univ)

/-- `μ*(Q)` is attained on some cylinder intersection `Z`. -/
theorem exists_cylInter_eq_muDual (Q : Tensor X) :
    ∃ Z : Set (∀ i, X i), IsCylinderIntersection Z ∧
      |tensorInner Q (charTensor Z)| = muDual Q := by
  have : Nonempty (CylInter X) := ⟨⟨Set.univ, isCylinderIntersection_univ⟩⟩
  obtain ⟨⟨Z, hZ⟩, hmax⟩ := exists_eq_ciSup_of_finite
    (f := fun S : CylInter X ↦ |tensorInner Q (charTensor S.1)|)
  exact ⟨Z, hZ, hmax⟩

/-- Upper bound criterion for `μ*(Q)`. -/
theorem muDual_le_iff (Q : Tensor X) {B : ℝ} :
    muDual Q ≤ B ↔ ∀ Z : Set (∀ i, X i), IsCylinderIntersection Z →
      |tensorInner Q (charTensor Z)| ≤ B := by
  have : Nonempty (CylInter X) := ⟨⟨Set.univ, isCylinderIntersection_univ⟩⟩
  constructor
  · intro h Z hZ
    exact (abs_tensorInner_charTensor_le_muDual Q hZ).trans h
  · intro h
    exact ciSup_le fun ⟨Z, hZ⟩ ↦ h Z hZ

/-- `μ*(Q) ≤ ‖Q‖₁`. -/
theorem muDual_le_tensorL1 (Q : Tensor X) : muDual Q ≤ tensorL1 Q := by
  rw [muDual_le_iff]
  intro Z _
  simp only [tensorInner_eq_sum, tensorL1_eq_sum]
  calc |∑ x : ∀ i, X i, Q x * charTensor Z x|
      ≤ ∑ x : ∀ i, X i, |Q x * charTensor Z x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x : ∀ i, X i, |Q x| := Finset.sum_le_sum fun x _ ↦ by
        by_cases hx : x ∈ Z
        · rw [charTensor_of_mem hx, mul_one]
        · rw [charTensor_of_notMem hx, mul_zero, abs_zero]; exact abs_nonneg _

/-- Positive homogeneity of `μ*`: `μ*(c · Q) = |c| · μ*(Q)`. -/
theorem muDual_smul (c : ℝ) (Q : Tensor X) :
    muDual (fun x ↦ c * Q x) = |c| * muDual Q := by
  have hinner : ∀ Z : Set (∀ i, X i),
      |tensorInner (fun x ↦ c * Q x) (charTensor Z)| = |c| * |tensorInner Q (charTensor Z)| := by
    intro Z
    have hsum : tensorInner (fun x ↦ c * Q x) (charTensor Z) =
        c * tensorInner Q (charTensor Z) := by
      simp only [tensorInner_eq_sum]
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ ↦ by ring
    rw [hsum, abs_mul]
  refine le_antisymm ?_ ?_
  · rw [muDual_le_iff]
    intro Z hZ
    rw [hinner Z]
    exact mul_le_mul_of_nonneg_left (abs_tensorInner_charTensor_le_muDual Q hZ) (abs_nonneg c)
  · obtain ⟨Z, hZ, hmax⟩ := exists_cylInter_eq_muDual Q
    rw [← hmax, ← hinner Z]
    exact abs_tensorInner_charTensor_le_muDual _ hZ

/-- On at least two players, `|Q x| ≤ μ*(Q)` for every entry `x`. -/
theorem abs_entry_le_muDual [Nontrivial ι] (Q : Tensor X) (x : ∀ i, X i) :
    |Q x| ≤ muDual Q := by
  have hsing : tensorInner Q (charTensor ({x} : Set (∀ i, X i))) = Q x := by
    simp only [tensorInner_eq_sum]
    rw [Finset.sum_eq_single x]
    · rw [charTensor_of_mem (Set.mem_singleton x), mul_one]
    · intro y _ hne
      rw [charTensor_of_notMem (Set.notMem_singleton_iff.mpr hne), mul_zero]
    · intro h; exact (h (Finset.mem_univ _)).elim
  rw [← hsing]
  exact abs_tensorInner_charTensor_le_muDual Q (isCylinderIntersection_singleton x)

/-- On at least two players, `μ*(Q) = 0 ↔ Q = 0`. -/
theorem muDual_eq_zero_iff [Nontrivial ι] (Q : Tensor X) : muDual Q = 0 ↔ Q = 0 := by
  constructor
  · intro h
    funext x
    have := abs_entry_le_muDual Q x
    rw [h] at this
    exact abs_nonpos_iff.mp this
  · rintro rfl
    refine le_antisymm ((muDual_le_iff _).mpr fun Z _ ↦ by simp [tensorInner_eq_sum])
      (muDual_nonneg _)

/-- Primal-dual bilinear inequality: `|⟨B, Q⟩| ≤ μ(B) · μ*(Q)`. -/
theorem abs_tensorInner_le_mu_mul_muDual [Nontrivial ι] (B Q : Tensor X) :
    |tensorInner B Q| ≤ mu B * muDual Q := by
  by_cases hQ0 : muDual Q = 0
  · have hQ : Q = 0 := (muDual_eq_zero_iff Q).mp hQ0
    subst hQ
    rw [hQ0, mul_zero]
    simp [tensorInner_eq_sum]
  · have hQpos : 0 < muDual Q := lt_of_le_of_ne (muDual_nonneg Q) (Ne.symm hQ0)
    rw [← div_le_iff₀ hQpos]
    refine le_mu_of_forall_decomp fun n α Z hZ hB ↦ ?_
    rw [div_le_iff₀ hQpos]
    have hinner : tensorInner B Q = ∑ r : Fin n, α r * tensorInner Q (charTensor (Z r)) := by
      simp only [tensorInner_eq_sum]
      calc ∑ x, B x * Q x
          = ∑ x, (∑ r, α r * charTensor (Z r) x) * Q x :=
            Finset.sum_congr rfl fun x _ ↦ by rw [hB x]
        _ = ∑ x, ∑ r, α r * (Q x * charTensor (Z r) x) :=
            Finset.sum_congr rfl fun x _ ↦ by
              rw [Finset.sum_mul]
              exact Finset.sum_congr rfl fun r _ ↦ by ring
        _ = ∑ r, ∑ x, α r * (Q x * charTensor (Z r) x) := Finset.sum_comm
        _ = ∑ r, α r * ∑ x, Q x * charTensor (Z r) x :=
            Finset.sum_congr rfl fun r _ ↦ (Finset.mul_sum _ _ _).symm
    rw [hinner]
    calc |∑ r, α r * tensorInner Q (charTensor (Z r))|
        ≤ ∑ r, |α r * tensorInner Q (charTensor (Z r))| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ r, |α r| * muDual Q := Finset.sum_le_sum fun r _ ↦ by
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (abs_tensorInner_charTensor_le_muDual Q (hZ r))
            (abs_nonneg _)
      _ = (∑ r, |α r|) * muDual Q := (Finset.sum_mul _ _ _).symm

/-- Equivalence of the dual-norm definition `μ*(Q) = max_{μ(B) ≤ 1} |⟨B, Q⟩|` with
`max_Z |⟨Q, χ(Z)⟩|`. -/
theorem muDual_eq_sSup_unit_ball [Nontrivial ι] (Q : Tensor X) :
    muDual Q = sSup {v : ℝ | ∃ B : Tensor X, mu B ≤ 1 ∧ v = |tensorInner B Q|} := by
  refine le_antisymm ?_ ?_
  · obtain ⟨Z, hZ, hmax⟩ := exists_cylInter_eq_muDual Q
    rw [← hmax, tensorInner_comm]
    refine le_csSup ?_ ⟨charTensor Z, ?_, rfl⟩
    · refine ⟨muDual Q, ?_⟩
      rintro v ⟨B, hB, rfl⟩
      calc |tensorInner B Q| ≤ mu B * muDual Q := abs_tensorInner_le_mu_mul_muDual B Q
        _ ≤ 1 * muDual Q := mul_le_mul_of_nonneg_right hB (muDual_nonneg Q)
        _ = muDual Q := one_mul _
    · have h1 := mu_le_of_decomp (B := charTensor Z) (n := 1) (fun _ ↦ 1) (fun _ ↦ Z)
        (fun _ ↦ hZ) (fun x ↦ by simp)
      simpa using h1
  · refine csSup_le ?_ ?_
    · have hmu0 : mu (0 : Tensor X) ≤ 1 := by
        have h0 := mu_le_of_decomp (B := (0 : Tensor X)) (n := 0) Fin.elim0 Fin.elim0
          (fun r ↦ r.elim0) (fun _ ↦ by simp)
        simpa using h0.trans zero_le_one
      exact ⟨0, 0, hmu0, by simp [tensorInner_eq_sum]⟩
    · rintro v ⟨B, hB, rfl⟩
      calc |tensorInner B Q| ≤ mu B * muDual Q := abs_tensorInner_le_mu_mul_muDual B Q
        _ ≤ 1 * muDual Q := mul_le_mul_of_nonneg_right hB (muDual_nonneg Q)
        _ = muDual Q := one_mul _

/-- **the definition — Discrepancy `disc_P(A) = μ*(A ∘ P)`**.
-/
noncomputable def nofDiscrepancy (A P : Tensor X) : ℝ :=
  muDual (hadamardTensor A P)

/-- Exact bridge between `nofDiscrepancy` and `Cslib.Communication.NOF.discrepancy`. -/
theorem nofDiscrepancy_eq_cslib_discrepancy (ν : PMF (∀ i, X i)) (f : (∀ i, X i) → Bool) :
    nofDiscrepancy (signTensor f) (fun x ↦ (ν x).toReal) =
      Cslib.Communication.NOF.discrepancy ν f := by
  have hsum_eq : ∀ φ : ∀ i, View X i → Bool,
      tensorInner (hadamardTensor (signTensor f) (fun x ↦ (ν x).toReal))
        (charTensor (cylinderIntersection φ)) =
      ∑ x with x ∈ cylinderIntersection φ, (ν x).toReal * signVal (f x) := by
    intro φ
    simp only [tensorInner_eq_sum, hadamardTensor_apply, signTensor_apply]
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    by_cases hx : x ∈ cylinderIntersection φ
    · rw [charTensor_of_mem hx, ite_eq_left hx]; ring
    · rw [charTensor_of_notMem hx, ite_eq_right hx]; ring
  refine le_antisymm ?_ ?_
  · rw [nofDiscrepancy, muDual_le_iff]
    intro Z hZ
    rcases isCylinderIntersection_iff.mp hZ with ⟨φ, rfl⟩
    rw [hsum_eq φ]
    exact abs_sum_le_discrepancy ν f φ
  · obtain ⟨φ, hφ⟩ := exists_abs_sum_eq_discrepancy ν f
    rw [← hφ, ← hsum_eq φ]
    exact abs_tensorInner_charTensor_le_muDual _ (isCylinderIntersection_iff.mpr ⟨φ, rfl⟩)

/-- Pointwise weak-duality kernel inequality:
for `a ∈ {-1, +1}` and `1 ≤ a * b ≤ α`, `((1 + α)(a * q) + (1 - α)|q|) / 2 ≤ b * q`. -/
theorem pointwise_approx_mu_dual_ineq {a b q α : ℝ} (ha : a = 1 ∨ a = -1)
    (hlo : 1 ≤ a * b) (hhi : a * b ≤ α) :
    ((1 + α) * (a * q) + (1 - α) * |q|) / 2 ≤ b * q := by
  have ha2 : a * a = 1 := by rcases ha with rfl | rfl <;> norm_num
  have hbq : b * q = (a * b) * (a * q) := by
    calc b * q = (a * a) * b * q := by rw [ha2, one_mul]
      _ = (a * b) * (a * q) := by ring
  rw [hbq]
  have habs : |a * q| = |q| := by
    rw [abs_mul]
    rcases ha with rfl | rfl <;> simp
  rw [← habs]
  by_cases hnn : 0 ≤ a * q
  · rw [abs_of_nonneg hnn]; nlinarith
  · rw [abs_of_neg (lt_of_not_ge hnn)]; nlinarith

/-- Weak duality for `μ^α(A)`. -/
theorem weak_duality_muAlpha [Nontrivial ι] {A : Tensor X} (hA : IsSignTensor A) {α : ℝ}
    (hα : 1 ≤ α) (Q : Tensor X) :
    ((1 + α) * tensorInner A Q + (1 - α) * tensorL1 Q) / 2 ≤ muAlpha α A * muDual Q := by
  by_cases hQ0 : muDual Q = 0
  · have hQ : Q = 0 := (muDual_eq_zero_iff Q).mp hQ0
    subst hQ
    rw [hQ0, mul_zero]
    simp [tensorInner_eq_sum, tensorL1_eq_sum]
  · have hQpos : 0 < muDual Q := lt_of_le_of_ne (muDual_nonneg Q) (Ne.symm hQ0)
    rw [← div_le_iff₀ hQpos]
    refine le_muAlpha_of_forall hA hα fun B hB ↦ ?_
    rw [div_le_iff₀ hQpos]
    have hsum : ((1 + α) * tensorInner A Q + (1 - α) * tensorL1 Q) / 2 ≤ tensorInner B Q := by
      simp only [tensorInner_eq_sum, tensorL1_eq_sum]
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, div_eq_mul_inv, Finset.sum_mul]
      simp_rw [← div_eq_mul_inv]
      exact Finset.sum_le_sum fun x _ ↦ pointwise_approx_mu_dual_ineq (hA x) (hB x).1 (hB x).2
    exact hsum.trans ((le_abs_self _).trans (abs_tensorInner_le_mu_mul_muDual B Q))

/-- Weak duality for `μ^∞(A)`. -/
theorem weak_duality_muInfty [Nontrivial ι] {A : Tensor X} (hA : IsSignTensor A) {Q : Tensor X}
    (hAQ : ∀ x, 0 ≤ A x * Q x) :
    tensorInner A Q ≤ muInfty A * muDual Q := by
  by_cases hQ0 : muDual Q = 0
  · have hQ : Q = 0 := (muDual_eq_zero_iff Q).mp hQ0
    subst hQ
    rw [hQ0, mul_zero]
    simp [tensorInner_eq_sum]
  · have hQpos : 0 < muDual Q := lt_of_le_of_ne (muDual_nonneg Q) (Ne.symm hQ0)
    rw [← div_le_iff₀ hQpos]
    refine le_muInfty_of_forall hA fun B hB ↦ ?_
    rw [div_le_iff₀ hQpos]
    have hsum : tensorInner A Q ≤ tensorInner B Q := by
      simp only [tensorInner_eq_sum]
      refine Finset.sum_le_sum fun x _ ↦ ?_
      have hbq : B x * Q x = (A x * B x) * (A x * Q x) := by
        calc B x * Q x = (A x * A x) * B x * Q x := by rw [hA.mul_self x, one_mul]
          _ = (A x * B x) * (A x * Q x) := by ring
      rw [hbq]
      nlinarith [hB x, hAQ x]
    exact hsum.trans ((le_abs_self _).trans (abs_tensorInner_le_mu_mul_muDual B Q))

omit [Fintype ι] [∀ i, Fintype (X i)] in
/-- On nonempty finite domains, `1 ≤ μ^∞(A)` for every sign tensor `A`. -/
theorem one_le_muInfty [Finite ι] [∀ i, Finite (X i)] [Nontrivial ι] [∀ i, Nonempty (X i)]
    {A : Tensor X} (hA : IsSignTensor A) : 1 ≤ muInfty A := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  let _ : ∀ i, Fintype (X i) := fun i ↦ Fintype.ofFinite (X i)
  let x₀ : ∀ i, X i := fun i ↦ Classical.arbitrary (X i)
  let Q : Tensor X := fun x ↦ if x = x₀ then A x₀ else 0
  have hAQ : ∀ x, 0 ≤ A x * Q x := fun x ↦ by
    dsimp only [Q]
    split_ifs with hx
    · subst hx; rw [hA.mul_self x₀]; norm_num
    · rw [mul_zero]
  have hinner : tensorInner A Q = 1 := by
    simp only [tensorInner_eq_sum]
    rw [Finset.sum_eq_single x₀]
    · simp [Q, hA.mul_self x₀]
    · intro x _ hne; simp [Q, hne]
    · intro h; exact (h (Finset.mem_univ _)).elim
  have hmu : muDual Q ≤ 1 := by
    rw [muDual_le_iff]
    intro Z _
    simp only [tensorInner_eq_sum]
    rw [Finset.sum_eq_single x₀]
    · simp only [Q, ↓reduceIte, abs_mul, hA.abs_eq_one x₀, one_mul]
      by_cases hm : x₀ ∈ Z
      · rw [charTensor_of_mem hm, abs_one]
      · rw [charTensor_of_notMem hm, abs_zero]; norm_num
    · intro x _ hne; simp [Q, hne]
    · intro h; exact (h (Finset.mem_univ _)).elim
  have hwd := weak_duality_muInfty hA hAQ
  rw [hinner] at hwd
  exact hwd.trans (by nlinarith [muInfty_nonneg A])

omit [Fintype ι] [∀ i, Fintype (X i)] in
/-- On nonempty finite domains, `1 ≤ μ^α(A)` for every sign tensor `A` and `1 ≤ α`. -/
theorem one_le_muAlpha [Finite ι] [∀ i, Finite (X i)] [Nontrivial ι] [∀ i, Nonempty (X i)]
    {A : Tensor X} (hA : IsSignTensor A) {α : ℝ} (hα : 1 ≤ α) : 1 ≤ muAlpha α A :=
  (one_le_muInfty hA).trans (muInfty_le_muAlpha hA hα)

private theorem continuous_sum_finset {α β : Type*} [TopologicalSpace α]
    (s : Finset β) {f : β → α → ℝ} (hf : ∀ b ∈ s, Continuous (f b)) :
    Continuous (fun a ↦ ∑ b ∈ s, f b a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using continuous_const
  | insert b t hbt ih =>
    simp_rw [Finset.sum_insert hbt]
    exact (hf b (Finset.mem_insert_self b t)).add
      (ih fun c hc ↦ hf c (Finset.mem_insert_of_mem hc))

/-- Compactness of the unit ball `{Q | μ*(Q) ≤ 1}` on finite domains with `≥ 2` players. -/
private theorem isCompact_muDual_unitBall [Nontrivial ι] :
    IsCompact {Q : Tensor X | muDual Q ≤ 1} := by
  have hclosed : IsClosed {Q : Tensor X | muDual Q ≤ 1} := by
    have heq : {Q : Tensor X | muDual Q ≤ 1} =
        ⋂ Z : CylInter X, {Q : Tensor X | |tensorInner Q (charTensor Z.1)| ≤ 1} := by
      ext Q
      simp only [Set.mem_ofPred_eq, Set.mem_iInter, muDual_le_iff]
      exact ⟨fun h ⟨Z, hZ⟩ ↦ h Z hZ, fun h Z hZ ↦ h ⟨Z, hZ⟩⟩
    rw [heq]
    refine isClosed_iInter fun Z ↦ isClosed_le ?_ continuous_const
    refine continuous_abs.comp ?_
    simp only [tensorInner_eq_sum]
    exact continuous_sum_finset _ fun x _ ↦ (continuous_apply x).mul continuous_const
  have hbdd : Bornology.IsBounded {Q : Tensor X | muDual Q ≤ 1} := by
    refine Metric.isBounded_iff_subset_closedBall 0 |>.mpr ⟨1, fun Q hQ ↦ ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
    intro x
    exact (abs_entry_le_muDual Q x).trans hQ
  exact Metric.isCompact_of_isClosed_isBounded hclosed hbdd

/-- **Farkas strong-duality step for `μ^α(A)`**: for any `t < μ^α(A)`, there exists `Q` with
`μ*(Q) ≤ 1` and `((1 + α) ⟨A, Q⟩ + (1 - α) ‖Q‖₁) / 2 > t`. -/
private theorem exists_dual_gt_of_lt_muAlpha [Nontrivial ι]
    {A : Tensor X} (hA : IsSignTensor A) {α t : ℝ} (hα : 1 ≤ α) (ht : t < muAlpha α A) :
    ∃ Q : Tensor X, muDual Q ≤ 1 ∧
      t < ((1 + α) * tensorInner A Q + (1 - α) * tensorL1 Q) / 2 := by
  classical
  let _ : Fintype (CylInter X) := Fintype.ofFinite (CylInter X)
  let I := ∀ i, X i
  let J := CylInter X
  let M : Matrix ((J ⊕ J) ⊕ (I ⊕ I) ⊕ Unit) (J ⊕ J) ℝ :=
    Matrix.of fun r c ↦
      match r, c with
      | .inl (.inl Z), .inl Z' => if Z = Z' then -1 else 0
      | .inl (.inl _), .inr _ => 0
      | .inl (.inr _), .inl _ => 0
      | .inl (.inr Z), .inr Z' => if Z = Z' then -1 else 0
      | .inr (.inl (.inl x)), .inl Z => -(A x * charTensor Z.1 x)
      | .inr (.inl (.inl x)), .inr Z => A x * charTensor Z.1 x
      | .inr (.inl (.inr x)), .inl Z => A x * charTensor Z.1 x
      | .inr (.inl (.inr x)), .inr Z => -(A x * charTensor Z.1 x)
      | .inr (.inr ()), _ => 1
  let b : ((J ⊕ J) ⊕ (I ⊕ I) ⊕ Unit) → ℝ := fun r ↦
    match r with
    | .inl _ => 0
    | .inr (.inl (.inl _)) => -1
    | .inr (.inl (.inr _)) => α
    | .inr (.inr ()) => t
  have hinfeas : ¬∃ v : J ⊕ J → ℝ, M.mulVec v ≤ b := by
    rintro ⟨v, hv⟩
    let p : J → ℝ := fun Z ↦ v (.inl Z)
    let q : J → ℝ := fun Z ↦ v (.inr Z)
    have hp : ∀ Z, 0 ≤ p Z := fun Z ↦ by
      have h := hv (.inl (.inl Z))
      simp only [M, b, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.of_apply,
        zero_mul, Finset.sum_const_zero, add_zero, ite_mul, neg_mul, one_mul, Finset.sum_ite_eq,
        Finset.mem_univ, ↓reduceIte] at h
      linarith
    have hq : ∀ Z, 0 ≤ q Z := fun Z ↦ by
      have h := hv (.inl (.inr Z))
      simp only [M, b, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.of_apply,
        zero_mul, Finset.sum_const_zero, zero_add, ite_mul, neg_mul, one_mul, Finset.sum_ite_eq,
        Finset.mem_univ, ↓reduceIte] at h
      linarith
    let B : Tensor X := fun x ↦ ∑ Z : J, (p Z - q Z) * charTensor Z.1 x
    have hlo : ∀ x, 1 ≤ A x * B x := fun x ↦ by
      have h := hv (.inr (.inl (.inl x)))
      simp only [M, b, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.of_apply] at h
      have heq : -(A x * B x) =
          ∑ Z : J, -(A x * charTensor Z.1 x) * p Z + ∑ Z : J, A x * charTensor Z.1 x * q Z := by
        dsimp only [B]
        rw [Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun Z _ ↦ by ring
      linarith
    have hhi : ∀ x, A x * B x ≤ α := fun x ↦ by
      have h := hv (.inr (.inl (.inr x)))
      simp only [M, b, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.of_apply] at h
      have heq : A x * B x =
          ∑ Z : J, A x * charTensor Z.1 x * p Z + ∑ Z : J, -(A x * charTensor Z.1 x) * q Z := by
        dsimp only [B]
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun Z _ ↦ by ring
      linarith
    have hsum_t : ∑ Z : J, (p Z + q Z) ≤ t := by
      have h := hv (.inr (.inr ()))
      simp only [M, b, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.of_apply,
        one_mul] at h
      rwa [Finset.sum_add_distrib]
    let e : Fin (Fintype.card J) ≃ J := (Fintype.equivFin J).symm
    have hmuB : mu B ≤ ∑ Z : J, |p Z - q Z| := by
      have hle := mu_le_of_decomp (B := B) (n := Fintype.card J)
        (fun r ↦ p (e r) - q (e r)) (fun r ↦ (e r).1) (fun r ↦ (e r).2)
        (fun x ↦ (e.sum_comp (fun Z : J ↦ (p Z - q Z) * charTensor Z.1 x)).symm)
      exact hle.trans (le_of_eq (e.sum_comp (fun Z : J ↦ |p Z - q Z|)))
    have habs_le : ∑ Z : J, |p Z - q Z| ≤ ∑ Z : J, (p Z + q Z) :=
      Finset.sum_le_sum fun Z _ ↦ by
        calc |p Z - q Z| = |p Z + -q Z| := by rw [sub_eq_add_neg]
          _ ≤ |p Z| + |-q Z| := abs_add_le _ _
          _ = p Z + q Z := by rw [abs_neg, abs_of_nonneg (hp Z), abs_of_nonneg (hq Z)]
    have hcontr : muAlpha α A ≤ t :=
      (muAlpha_le_mu fun x ↦ ⟨hlo x, hhi x⟩).trans (hmuB.trans (habs_le.trans hsum_t))
    linarith
  obtain ⟨y, hy0, hyM, hyb⟩ := (Matrix.not_exists_mulVec_le_iff M b).mp hinfeas
  let sp : J → ℝ := fun Z ↦ y (.inl (.inl Z))
  let sq_ : J → ℝ := fun Z ↦ y (.inl (.inr Z))
  let u : I → ℝ := fun x ↦ y (.inr (.inl (.inl x)))
  let w : I → ℝ := fun x ↦ y (.inr (.inl (.inr x)))
  let lam : ℝ := y (.inr (.inr ()))
  have hsp : ∀ Z, 0 ≤ sp Z := fun Z ↦ hy0 (.inl (.inl Z))
  have hsq : ∀ Z, 0 ≤ sq_ Z := fun Z ↦ hy0 (.inl (.inr Z))
  have hu : ∀ x, 0 ≤ u x := fun x ↦ hy0 (.inr (.inl (.inl x)))
  have hw : ∀ x, 0 ≤ w x := fun x ↦ hy0 (.inr (.inl (.inr x)))
  have hlam : 0 ≤ lam := hy0 (.inr (.inr ()))
  let Q : Tensor X := fun x ↦ (u x - w x) * A x
  have hQ_bound : muDual Q ≤ lam := by
    rw [muDual_le_iff]
    intro Z hZ
    let Z' : J := ⟨Z, hZ⟩
    have hc1 := congrFun hyM (.inl Z')
    have hc2 := congrFun hyM (.inr Z')
    simp only [Matrix.vecMul, dotProduct, Fintype.sum_sum_type, Fintype.sum_unique,
      Pi.zero_apply, M, Matrix.of_apply, mul_ite, mul_neg, mul_one, mul_zero,
      Finset.sum_const_zero, add_zero, zero_add, Finset.sum_ite_eq', Finset.mem_univ,
      ↓reduceIte] at hc1 hc2
    have hinner : tensorInner Q (charTensor Z) =
        ∑ x : I, u x * (A x * charTensor Z x) - ∑ x : I, w x * (A x * charTensor Z x) := by
      simp only [tensorInner_eq_sum]
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun x _ ↦ by dsimp only [Q]; ring
    have h1 : tensorInner Q (charTensor Z) ≤ lam := by
      rw [hinner]
      have hspZ := hsp Z'
      rw [Finset.sum_neg_distrib] at hc1
      have hc1' : -sp Z' + (-(∑ x : I, u x * (A x * charTensor Z x)) +
          ∑ x : I, w x * (A x * charTensor Z x) + lam) = 0 := hc1
      linarith
    have h2 : -tensorInner Q (charTensor Z) ≤ lam := by
      rw [hinner]
      have hsqZ := hsq Z'
      rw [Finset.sum_neg_distrib] at hc2
      have hc2' : -sq_ Z' + (∑ x : I, u x * (A x * charTensor Z x) +
          -(∑ x : I, w x * (A x * charTensor Z x)) + lam) = 0 := hc2
      linarith
    exact abs_le.mpr ⟨by linarith, h1⟩
  have hdot : lam * t < ∑ x : I, (u x - α * w x) := by
    simp only [dotProduct, Fintype.sum_sum_type, Fintype.sum_unique, b, mul_zero,
      Finset.sum_const_zero, zero_add, mul_neg, mul_one, Finset.sum_neg_distrib] at hyb
    have hsub : ∑ x : I, (u x - α * w x) = ∑ x : I, u x - ∑ x : I, w x * α := by
      rw [Finset.sum_sub_distrib]
      congr 1; exact Finset.sum_congr rfl fun _ _ ↦ mul_comm _ _
    have hyb' : -(∑ x : I, u x) + ∑ x : I, w x * α + lam * t < 0 := hyb
    linarith
  have hlam_pos : 0 < lam := by
    by_contra hle
    have hlam0 : lam = 0 := le_antisymm (not_lt.mp hle) hlam
    rw [hlam0] at hQ_bound hdot
    have hQ0 : Q = 0 := (muDual_eq_zero_iff Q).mp (le_antisymm hQ_bound (muDual_nonneg Q))
    have huw : ∀ x, u x = w x := fun x ↦ by
      have hx : (u x - w x) * A x = 0 := congrFun hQ0 x
      have hAne : A x ≠ 0 := by rcases hA x with h | h <;> rw [h] <;> norm_num
      linarith [(mul_eq_zero.mp hx).resolve_right hAne]
    have hnonpos : ∑ x : I, (u x - α * w x) ≤ 0 :=
      Finset.sum_nonpos fun x _ ↦ by rw [huw x]; nlinarith [hw x]
    linarith
  let Q' : Tensor X := fun x ↦ lam⁻¹ * Q x
  have hQ'_ball : muDual Q' ≤ 1 := by
    rw [muDual_smul, abs_inv, abs_of_pos hlam_pos]
    calc lam⁻¹ * muDual Q ≤ lam⁻¹ * lam :=
          mul_le_mul_of_nonneg_left hQ_bound (inv_nonneg.mpr hlam_pos.le)
      _ = 1 := inv_mul_cancel₀ hlam_pos.ne'
  have hnum_Q : ∑ x : I, (u x - α * w x) ≤
      ((1 + α) * tensorInner A Q + (1 - α) * tensorL1 Q) / 2 := by
    have hAQ : tensorInner A Q = ∑ x : I, (u x - w x) := by
      simp only [tensorInner_eq_sum]
      refine Finset.sum_congr rfl fun x _ ↦ ?_
      dsimp only [Q]
      rw [mul_comm (u x - w x), ← mul_assoc, hA.mul_self x, one_mul]
    have hL1 : tensorL1 Q ≤ ∑ x : I, (u x + w x) := by
      simp only [tensorL1_eq_sum]
      refine Finset.sum_le_sum fun x _ ↦ ?_
      dsimp only [Q]
      rw [abs_mul, hA.abs_eq_one x, mul_one]
      calc |u x - w x| = |u x + -w x| := by rw [sub_eq_add_neg]
        _ ≤ |u x| + |-w x| := abs_add_le _ _
        _ = u x + w x := by rw [abs_neg, abs_of_nonneg (hu x), abs_of_nonneg (hw x)]
    have hle1 : (1 - α) * (∑ x : I, (u x + w x)) ≤ (1 - α) * tensorL1 Q :=
      mul_le_mul_of_nonpos_left hL1 (by linarith)
    rw [hAQ]
    have hident : ((1 + α) * ∑ x : I, (u x - w x) + (1 - α) * ∑ x : I, (u x + w x)) / 2 =
        ∑ x : I, (u x - α * w x) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, div_eq_mul_inv, Finset.sum_mul]
      exact Finset.sum_congr rfl fun x _ ↦ by ring
    linarith
  have hscale : ((1 + α) * tensorInner A Q' + (1 - α) * tensorL1 Q') / 2 =
      lam⁻¹ * (((1 + α) * tensorInner A Q + (1 - α) * tensorL1 Q) / 2) := by
    have h1 : tensorInner A Q' = lam⁻¹ * tensorInner A Q := by
      simp only [tensorInner_eq_sum]
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ ↦ by dsimp only [Q']; ring
    have h2 : tensorL1 Q' = lam⁻¹ * tensorL1 Q := by
      simp only [tensorL1_eq_sum]
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ ↦ by
        dsimp only [Q']; rw [abs_mul, abs_inv, abs_of_pos hlam_pos]
    rw [h1, h2]; ring
  refine ⟨Q', hQ'_ball, ?_⟩
  rw [hscale]
  have hgt := lt_of_lt_of_le hdot hnum_Q
  have := mul_lt_mul_of_pos_left hgt (inv_pos.mpr hlam_pos)
  rwa [← mul_assoc, inv_mul_cancel₀ hlam_pos.ne', one_mul] at this

/-- **Farkas strong-duality step for `μ^∞(A)`**: for any `t < μ^∞(A)`, there exists `Q` with
`A ∘ Q ≥ 0`, `μ*(Q) ≤ 1`, and `⟨A, Q⟩ > t`. -/
private theorem exists_dual_gt_of_lt_muInfty [Nontrivial ι]
    {A : Tensor X} (hA : IsSignTensor A) {t : ℝ} (ht : t < muInfty A) :
    ∃ Q : Tensor X, (∀ x, 0 ≤ A x * Q x) ∧ muDual Q ≤ 1 ∧ t < tensorInner A Q := by
  classical
  let _ : Fintype (CylInter X) := Fintype.ofFinite (CylInter X)
  let I := ∀ i, X i
  let J := CylInter X
  let M : Matrix ((J ⊕ J) ⊕ I ⊕ Unit) (J ⊕ J) ℝ :=
    Matrix.of fun r c ↦
      match r, c with
      | .inl (.inl Z), .inl Z' => if Z = Z' then -1 else 0
      | .inl (.inl _), .inr _ => 0
      | .inl (.inr _), .inl _ => 0
      | .inl (.inr Z), .inr Z' => if Z = Z' then -1 else 0
      | .inr (.inl x), .inl Z => -(A x * charTensor Z.1 x)
      | .inr (.inl x), .inr Z => A x * charTensor Z.1 x
      | .inr (.inr ()), _ => 1
  let b : ((J ⊕ J) ⊕ I ⊕ Unit) → ℝ := fun r ↦
    match r with
    | .inl _ => 0
    | .inr (.inl _) => -1
    | .inr (.inr ()) => t
  have hinfeas : ¬∃ v : J ⊕ J → ℝ, M.mulVec v ≤ b := by
    rintro ⟨v, hv⟩
    let p : J → ℝ := fun Z ↦ v (.inl Z)
    let q : J → ℝ := fun Z ↦ v (.inr Z)
    have hp : ∀ Z, 0 ≤ p Z := fun Z ↦ by
      have h := hv (.inl (.inl Z))
      simp only [M, b, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.of_apply,
        zero_mul, Finset.sum_const_zero, add_zero, ite_mul, neg_mul, one_mul, Finset.sum_ite_eq,
        Finset.mem_univ, ↓reduceIte] at h
      linarith
    have hq : ∀ Z, 0 ≤ q Z := fun Z ↦ by
      have h := hv (.inl (.inr Z))
      simp only [M, b, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.of_apply,
        zero_mul, Finset.sum_const_zero, zero_add, ite_mul, neg_mul, one_mul, Finset.sum_ite_eq,
        Finset.mem_univ, ↓reduceIte] at h
      linarith
    let B : Tensor X := fun x ↦ ∑ Z : J, (p Z - q Z) * charTensor Z.1 x
    have hlo : ∀ x, 1 ≤ A x * B x := fun x ↦ by
      have h := hv (.inr (.inl x))
      simp only [M, b, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.of_apply] at h
      have heq : -(A x * B x) =
          ∑ Z : J, -(A x * charTensor Z.1 x) * p Z + ∑ Z : J, A x * charTensor Z.1 x * q Z := by
        dsimp only [B]
        rw [Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun Z _ ↦ by ring
      linarith
    have hsum_t : ∑ Z : J, (p Z + q Z) ≤ t := by
      have h := hv (.inr (.inr ()))
      simp only [M, b, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.of_apply,
        one_mul] at h
      rwa [Finset.sum_add_distrib]
    let e : Fin (Fintype.card J) ≃ J := (Fintype.equivFin J).symm
    have hmuB : mu B ≤ ∑ Z : J, |p Z - q Z| := by
      have hle := mu_le_of_decomp (B := B) (n := Fintype.card J)
        (fun r ↦ p (e r) - q (e r)) (fun r ↦ (e r).1) (fun r ↦ (e r).2)
        (fun x ↦ (e.sum_comp (fun Z : J ↦ (p Z - q Z) * charTensor Z.1 x)).symm)
      exact hle.trans (le_of_eq (e.sum_comp (fun Z : J ↦ |p Z - q Z|)))
    have habs_le : ∑ Z : J, |p Z - q Z| ≤ ∑ Z : J, (p Z + q Z) :=
      Finset.sum_le_sum fun Z _ ↦ by
        calc |p Z - q Z| = |p Z + -q Z| := by rw [sub_eq_add_neg]
          _ ≤ |p Z| + |-q Z| := abs_add_le _ _
          _ = p Z + q Z := by rw [abs_neg, abs_of_nonneg (hp Z), abs_of_nonneg (hq Z)]
    have hcontr : muInfty A ≤ t :=
      (muInfty_le_mu hlo).trans (hmuB.trans (habs_le.trans hsum_t))
    linarith
  obtain ⟨y, hy0, hyM, hyb⟩ := (Matrix.not_exists_mulVec_le_iff M b).mp hinfeas
  let sp : J → ℝ := fun Z ↦ y (.inl (.inl Z))
  let sq_ : J → ℝ := fun Z ↦ y (.inl (.inr Z))
  let u : I → ℝ := fun x ↦ y (.inr (.inl x))
  let lam : ℝ := y (.inr (.inr ()))
  have hsp : ∀ Z, 0 ≤ sp Z := fun Z ↦ hy0 (.inl (.inl Z))
  have hsq : ∀ Z, 0 ≤ sq_ Z := fun Z ↦ hy0 (.inl (.inr Z))
  have hu : ∀ x, 0 ≤ u x := fun x ↦ hy0 (.inr (.inl x))
  have hlam : 0 ≤ lam := hy0 (.inr (.inr ()))
  let Q : Tensor X := fun x ↦ u x * A x
  have hAQ : ∀ x, 0 ≤ A x * Q x := fun x ↦ by
    dsimp only [Q]
    rw [mul_comm (u x), ← mul_assoc, hA.mul_self x, one_mul]
    exact hu x
  have hQ_bound : muDual Q ≤ lam := by
    rw [muDual_le_iff]
    intro Z hZ
    let Z' : J := ⟨Z, hZ⟩
    have hc1 := congrFun hyM (.inl Z')
    have hc2 := congrFun hyM (.inr Z')
    simp only [Matrix.vecMul, dotProduct, Fintype.sum_sum_type, Fintype.sum_unique,
      Pi.zero_apply, M, Matrix.of_apply, mul_ite, mul_neg, mul_one, mul_zero,
      Finset.sum_const_zero, add_zero, zero_add, Finset.sum_ite_eq', Finset.mem_univ,
      ↓reduceIte] at hc1 hc2
    have hinner : tensorInner Q (charTensor Z) = ∑ x : I, u x * (A x * charTensor Z x) := by
      simp only [tensorInner_eq_sum]
      exact Finset.sum_congr rfl fun x _ ↦ by dsimp only [Q]; ring
    have h1 : tensorInner Q (charTensor Z) ≤ lam := by
      rw [hinner]
      have hspZ := hsp Z'
      rw [Finset.sum_neg_distrib] at hc1
      have hc1' : -sp Z' + (-(∑ x : I, u x * (A x * charTensor Z x)) + lam) = 0 := hc1
      linarith
    have h2 : -tensorInner Q (charTensor Z) ≤ lam := by
      rw [hinner]
      have hsqZ := hsq Z'
      have hc2' : -sq_ Z' + (∑ x : I, u x * (A x * charTensor Z x) + lam) = 0 := hc2
      linarith
    exact abs_le.mpr ⟨by linarith, h1⟩
  have hinner_AQ : tensorInner A Q = ∑ x : I, u x := by
    simp only [tensorInner_eq_sum]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    dsimp only [Q]
    rw [mul_comm (u x), ← mul_assoc, hA.mul_self x, one_mul]
  have hdot : lam * t < tensorInner A Q := by
    simp only [dotProduct, Fintype.sum_sum_type, Fintype.sum_unique, b, mul_zero,
      Finset.sum_const_zero, zero_add, mul_neg, mul_one, Finset.sum_neg_distrib] at hyb
    rw [hinner_AQ]
    have hyb' : -(∑ x : I, u x) + lam * t < 0 := hyb
    linarith
  have hlam_pos : 0 < lam := by
    by_contra hle
    have hlam0 : lam = 0 := le_antisymm (not_lt.mp hle) hlam
    rw [hlam0] at hQ_bound hdot
    have hQ0 : Q = 0 := (muDual_eq_zero_iff Q).mp (le_antisymm hQ_bound (muDual_nonneg Q))
    rw [hQ0] at hdot
    simp [tensorInner_eq_sum] at hdot
  let Q' : Tensor X := fun x ↦ lam⁻¹ * Q x
  refine ⟨Q',
    fun x ↦ by dsimp only [Q']; rw [mul_left_comm]; exact mul_nonneg (by positivity) (hAQ x),
    ?_, ?_⟩
  · rw [muDual_smul, abs_inv, abs_of_pos hlam_pos]
    calc lam⁻¹ * muDual Q ≤ lam⁻¹ * lam :=
          mul_le_mul_of_nonneg_left hQ_bound (inv_nonneg.mpr hlam_pos.le)
      _ = 1 := inv_mul_cancel₀ hlam_pos.ne'
  · have hscale : tensorInner A Q' = lam⁻¹ * tensorInner A Q := by
      simp only [tensorInner_eq_sum]
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ ↦ by dsimp only [Q']; ring
    rw [hscale]
    have := mul_lt_mul_of_pos_left hdot (inv_pos.mpr hlam_pos)
    rwa [← mul_assoc, inv_mul_cancel₀ hlam_pos.ne', one_mul] at this

/-- **the lifting theorem — Strong LP Duality for `μ^α(A)`**:
For any sign tensor `A` on `≥ 2` players with nonempty finite domains and `1 ≤ α`,
`μ^α(A) = max_{Q ≠ 0} ((1 + α) ⟨A, Q⟩ + (1 - α) ‖Q‖₁) / (2 μ*(Q))`, with the maximum attained. -/
theorem muAlpha_eq_dual [Nontrivial ι] [∀ i, Nonempty (X i)] {A : Tensor X} (hA : IsSignTensor A)
    {α : ℝ} (hα : 1 ≤ α) :
    (∀ Q : Tensor X, muDual Q ≠ 0 →
      ((1 + α) * tensorInner A Q + (1 - α) * tensorL1 Q) / (2 * muDual Q) ≤ muAlpha α A) ∧
    (∃ Q : Tensor X, muDual Q ≠ 0 ∧
      ((1 + α) * tensorInner A Q + (1 - α) * tensorL1 Q) / (2 * muDual Q) = muAlpha α A) := by
  have hle : ∀ Q : Tensor X, muDual Q ≠ 0 →
      ((1 + α) * tensorInner A Q + (1 - α) * tensorL1 Q) / (2 * muDual Q) ≤ muAlpha α A := by
    intro Q hQ
    have hQpos : 0 < muDual Q := lt_of_le_of_ne (muDual_nonneg Q) (Ne.symm hQ)
    rw [div_le_iff₀ (by positivity)]
    have hwd := weak_duality_muAlpha hA hα Q
    linarith
  refine ⟨hle, ?_⟩
  let obj : Tensor X → ℝ := fun Q ↦ ((1 + α) * tensorInner A Q + (1 - α) * tensorL1 Q) / 2
  have hcont : Continuous obj := by
    refine Continuous.div_const ?_ 2
    refine Continuous.add ?_ ?_
    · refine continuous_const.mul ?_
      change Continuous (fun Q : Tensor X ↦ tensorInner A Q)
      simp only [tensorInner_eq_sum]
      exact continuous_sum_finset _ fun x _ ↦ continuous_const.mul (continuous_apply x)
    · refine continuous_const.mul ?_
      change Continuous (fun Q : Tensor X ↦ tensorL1 Q)
      simp only [tensorL1_eq_sum]
      exact continuous_sum_finset _ fun x _ ↦ continuous_abs.comp (continuous_apply x)
  have hne : ({Q : Tensor X | muDual Q ≤ 1}).Nonempty :=
    ⟨0, by simp [(muDual_eq_zero_iff (0 : Tensor X)).mpr rfl]⟩
  obtain ⟨Q₀, hQ₀_mem, hQ₀_max⟩ := isCompact_muDual_unitBall.exists_isMaxOn hne hcont.continuousOn
  have hobj_ge : muAlpha α A ≤ obj Q₀ := by
    by_contra hlt
    push Not at hlt
    obtain ⟨Q₁, hQ₁_mem, hQ₁_gt⟩ := exists_dual_gt_of_lt_muAlpha hA hα hlt
    exact absurd (hQ₀_max hQ₁_mem) (not_le.mpr hQ₁_gt)
  have hmu_ge1 : 1 ≤ muAlpha α A := one_le_muAlpha hA hα
  have hQ₀_ne : muDual Q₀ ≠ 0 := by
    intro h0
    have hQ0 : Q₀ = 0 := (muDual_eq_zero_iff Q₀).mp h0
    have : obj Q₀ = 0 := by simp [obj, hQ0, tensorInner_eq_sum, tensorL1_eq_sum]
    linarith
  have hobj_le : obj Q₀ ≤ muAlpha α A := by
    have h1 := weak_duality_muAlpha hA hα Q₀
    have h2 : muAlpha α A * muDual Q₀ ≤ muAlpha α A := by
      nlinarith [muAlpha_nonneg α A, show muDual Q₀ ≤ 1 from hQ₀_mem]
    exact h1.trans h2
  have hobj_eq : obj Q₀ = muAlpha α A := le_antisymm hobj_le hobj_ge
  have hmuQ₀_eq : muDual Q₀ = 1 := by
    have h1 := weak_duality_muAlpha hA hα Q₀
    rw [show ((1 + α) * tensorInner A Q₀ + (1 - α) * tensorL1 Q₀) / 2 = obj Q₀ from rfl,
      hobj_eq] at h1
    have hge : 1 ≤ muDual Q₀ := by nlinarith
    exact le_antisymm hQ₀_mem hge
  refine ⟨Q₀, hQ₀_ne, ?_⟩
  rw [hmuQ₀_eq, mul_one]
  exact hobj_eq

/-- **the lifting theorem — Strong LP Duality for `μ^∞(A)`**:
For any sign tensor `A` on `≥ 2` players with nonempty finite domains,
`μ^∞(A) = max_{Q ≠ 0, A ∘ Q ≥ 0} ⟨A, Q⟩ / μ*(Q)`, with the maximum attained. -/
theorem muInfty_eq_dual [Nontrivial ι] [∀ i, Nonempty (X i)] {A : Tensor X} (hA : IsSignTensor A) :
    (∀ Q : Tensor X, (∀ x, 0 ≤ A x * Q x) → muDual Q ≠ 0 →
      tensorInner A Q / muDual Q ≤ muInfty A) ∧
    (∃ Q : Tensor X, (∀ x, 0 ≤ A x * Q x) ∧ muDual Q ≠ 0 ∧
      tensorInner A Q / muDual Q = muInfty A) := by
  have hle : ∀ Q : Tensor X, (∀ x, 0 ≤ A x * Q x) → muDual Q ≠ 0 →
      tensorInner A Q / muDual Q ≤ muInfty A := by
    intro Q hAQ hQ
    have hQpos : 0 < muDual Q := lt_of_le_of_ne (muDual_nonneg Q) (Ne.symm hQ)
    rw [div_le_iff₀ hQpos]
    exact weak_duality_muInfty hA hAQ
  refine ⟨hle, ?_⟩
  let S : Set (Tensor X) := {Q : Tensor X | muDual Q ≤ 1} ∩ {Q : Tensor X | ∀ x, 0 ≤ A x * Q x}
  have hclosed2 : IsClosed {Q : Tensor X | ∀ x, 0 ≤ A x * Q x} := by
    have heq : {Q : Tensor X | ∀ x, 0 ≤ A x * Q x} = ⋂ x, {Q : Tensor X | 0 ≤ A x * Q x} := by
      ext Q; simp
    rw [heq]
    exact isClosed_iInter fun x ↦
      isClosed_le continuous_const (continuous_const.mul (continuous_apply x))
  have hcomp : IsCompact S := isCompact_muDual_unitBall.inter_right hclosed2
  have hne : S.Nonempty :=
    ⟨0, by simp [(muDual_eq_zero_iff (0 : Tensor X)).mpr rfl], fun _ ↦ by simp⟩
  have hcont : Continuous (fun Q : Tensor X ↦ tensorInner A Q) := by
    simp only [tensorInner_eq_sum]
    exact continuous_sum_finset _ fun x _ ↦ continuous_const.mul (continuous_apply x)
  obtain ⟨Q₀, hQ₀_mem, hQ₀_max⟩ := hcomp.exists_isMaxOn hne hcont.continuousOn
  have hge : muInfty A ≤ tensorInner A Q₀ := by
    by_contra hlt
    push Not at hlt
    obtain ⟨Q₁, hAQ₁, hball₁, hgt₁⟩ := exists_dual_gt_of_lt_muInfty hA hlt
    exact absurd (hQ₀_max ⟨hball₁, hAQ₁⟩) (not_le.mpr hgt₁)
  have hmu_ge1 : 1 ≤ muInfty A := one_le_muInfty hA
  have hQ₀_ne : muDual Q₀ ≠ 0 := by
    intro h0
    have hQ0 : Q₀ = 0 := (muDual_eq_zero_iff Q₀).mp h0
    have : tensorInner A Q₀ = 0 := by simp [hQ0, tensorInner_eq_sum]
    linarith
  have hle_Q₀ : tensorInner A Q₀ ≤ muInfty A := by
    have h1 := weak_duality_muInfty hA hQ₀_mem.2
    have h2 : muInfty A * muDual Q₀ ≤ muInfty A := by
      nlinarith [muInfty_nonneg A, show muDual Q₀ ≤ 1 from hQ₀_mem.1]
    exact h1.trans h2
  have heq_Q₀ : tensorInner A Q₀ = muInfty A := le_antisymm hle_Q₀ hge
  have hmuQ₀_eq : muDual Q₀ = 1 := by
    have h1 := weak_duality_muInfty hA hQ₀_mem.2
    rw [heq_Q₀] at h1
    exact le_antisymm hQ₀_mem.1 (by nlinarith)
  refine ⟨Q₀, hQ₀_mem.2, hQ₀_ne, ?_⟩
  rw [hmuQ₀_eq, div_one, heq_Q₀]

/-- Minimum discrepancy `disc(A) = inf_P disc_P(A)` over probability distributions `P`. -/
noncomputable def minDiscrepancy (A : Tensor X) : ℝ :=
  sInf {d : ℝ | ∃ P : Tensor X, (∀ x, 0 ≤ P x) ∧ (∑ x, P x = 1) ∧ d = nofDiscrepancy A P}

/-- **Multiparty Communication Lower Bound**:
For every sign tensor `A` on `≥ 2` players with nonempty finite domains,
`μ^∞(A) = 1 / disc(A)`, and the minimum discrepancy is attained by a probability distribution. -/
theorem muInfty_eq_inv_minDiscrepancy [Nontrivial ι] [∀ i, Nonempty (X i)] {A : Tensor X}
    (hA : IsSignTensor A) :
    muInfty A = 1 / minDiscrepancy A ∧
      ∃ P : Tensor X, (∀ x, 0 ≤ P x) ∧ (∑ x, P x = 1) ∧
        nofDiscrepancy A P = minDiscrepancy A := by
  have hmu_pos : 0 < muInfty A := lt_of_lt_of_le zero_lt_one (one_le_muInfty hA)
  have hlb : ∀ P : Tensor X, (∀ x, 0 ≤ P x) → (∑ x, P x = 1) →
      1 / muInfty A ≤ nofDiscrepancy A P := by
    intro P hP0 hP1
    let Q := hadamardTensor A P
    have hAQ : ∀ x, 0 ≤ A x * Q x := fun x ↦ by
      simp only [Q, hadamardTensor_apply]
      rw [← mul_assoc, hA.mul_self x, one_mul]
      exact hP0 x
    have hinner : tensorInner A Q = 1 := by
      simp only [tensorInner_eq_sum]
      calc ∑ x, A x * Q x = ∑ x, P x := Finset.sum_congr rfl fun x _ ↦ by
            simp only [Q, hadamardTensor_apply]
            rw [← mul_assoc, hA.mul_self x, one_mul]
        _ = 1 := hP1
    have hwd := weak_duality_muInfty hA hAQ
    rw [hinner] at hwd
    rw [div_le_iff₀ hmu_pos, mul_comm]
    exact hwd
  obtain ⟨Q₀, hAQ₀, hQ₀_ne, hQ₀_eq⟩ := (muInfty_eq_dual hA).2
  have hQ₀_pos : 0 < muDual Q₀ := lt_of_le_of_ne (muDual_nonneg Q₀) (Ne.symm hQ₀_ne)
  have hinner_pos : 0 < tensorInner A Q₀ := by
    have : tensorInner A Q₀ = muInfty A * muDual Q₀ := (div_eq_iff hQ₀_ne).mp hQ₀_eq
    rw [this]; positivity
  let P₀ : Tensor X := fun x ↦ (A x * Q₀ x) / tensorInner A Q₀
  have hP₀_nn : ∀ x, 0 ≤ P₀ x := fun x ↦ div_nonneg (hAQ₀ x) hinner_pos.le
  have hP₀_sum : ∑ x, P₀ x = 1 := by
    dsimp only [P₀]
    rw [← Finset.sum_div]
    exact div_self hinner_pos.ne'
  have hP₀_disc : nofDiscrepancy A P₀ = 1 / muInfty A := by
    have hhad : hadamardTensor A P₀ = fun x ↦ (tensorInner A Q₀)⁻¹ * Q₀ x := by
      funext x
      simp only [hadamardTensor_apply, P₀]
      rw [mul_div_assoc', ← mul_assoc, hA.mul_self x, one_mul, div_eq_inv_mul]
    rw [nofDiscrepancy, hhad, muDual_smul, abs_inv, abs_of_pos hinner_pos, ← hQ₀_eq]
    field_simp [hQ₀_pos.ne', hinner_pos.ne']
  have hmin_eq : minDiscrepancy A = 1 / muInfty A := by
    let DSet : Set ℝ :=
      {d : ℝ | ∃ P : Tensor X, (∀ x, 0 ≤ P x) ∧ (∑ x, P x = 1) ∧ d = nofDiscrepancy A P}
    have hbdd : BddBelow DSet := ⟨0, fun _ ⟨_, _, _, hw⟩ ↦ hw ▸ muDual_nonneg _⟩
    have hmem : nofDiscrepancy A P₀ ∈ DSet := ⟨P₀, hP₀_nn, hP₀_sum, rfl⟩
    change sInf DSet = 1 / muInfty A
    refine le_antisymm ?_ ?_
    · exact (csInf_le hbdd hmem).trans (le_of_eq hP₀_disc)
    · refine le_csInf ⟨nofDiscrepancy A P₀, hmem⟩ ?_
      rintro d ⟨P, hP0, hP1, rfl⟩
      exact hlb P hP0 hP1
  refine ⟨?_, P₀, hP₀_nn, hP₀_sum, hP₀_disc.trans hmin_eq.symm⟩
  rw [hmin_eq, one_div_one_div]

/-- **Chattopadhyay–Ada Generalized Discrepancy Bound**):
If `R^k_ε(f) ≤ c`, then for every witness tensor `Q`,
`|⟨A_f, Q⟩| - 2ε ‖Q‖₁ ≤ 2^c · μ*(Q)`. -/
theorem randProtocol_generalized_discrepancy_bound [Nontrivial ι] {f : (∀ i, X i) → Bool}
    {ε : ℝ} {c : ℕ} (hε : 0 ≤ ε) (h : PublicCoin.ecomplexityFun ε f ≤ c) (Q : Tensor X) :
    |tensorInner (signTensor f) Q| - 2 * ε * tensorL1 Q ≤ (2 : ℝ) ^ c * muDual Q := by
  obtain ⟨l, p, g, hp0, hp1, hg, hinf⟩ := (publicCoin_decomposition_iff hε).mp h
  let E : Tensor X := fun x ↦ ∑ r : Fin l, p r * signTensor (g r) x
  have herr_inner : |tensorInner (signTensor f) Q - tensorInner E Q| ≤ 2 * ε * tensorL1 Q := by
    simp only [tensorInner_eq_sum, tensorL1_eq_sum]
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    calc |∑ x, (signTensor f x * Q x - E x * Q x)|
        ≤ ∑ x, |signTensor f x * Q x - E x * Q x| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ x, |signTensor f x - E x| * |Q x| :=
          Finset.sum_congr rfl fun x _ ↦ by rw [← sub_mul, abs_mul]
      _ ≤ ∑ x, (2 * ε) * |Q x| := Finset.sum_le_sum fun x _ ↦
          mul_le_mul_of_nonneg_right
            ((tensorLInfty_le_iff _ (by linarith)).mp hinf x) (abs_nonneg _)
  have hmuE : mu E ≤ (2 : ℝ) ^ c := by
    calc mu E ≤ ∑ r, mu (fun x ↦ p r * signTensor (g r) x) := mu_finset_sum_le Finset.univ _
      _ = ∑ r, p r * mu (signTensor (g r)) :=
          Finset.sum_congr rfl fun r _ ↦ by rw [mu_smul, abs_of_nonneg (hp0 r)]
      _ ≤ ∑ r, p r * (2 : ℝ) ^ c := Finset.sum_le_sum fun r _ ↦
          mul_le_mul_of_nonneg_left (mu_le_two_pow_of_ecomplexityFun_le (hg r)) (hp0 r)
      _ = (2 : ℝ) ^ c := by rw [← Finset.sum_mul, hp1, one_mul]
  have hE_le : |tensorInner E Q| ≤ (2 : ℝ) ^ c * muDual Q :=
    (abs_tensorInner_le_mu_mul_muDual E Q).trans
      (mul_le_mul_of_nonneg_right hmuE (muDual_nonneg Q))
  have htri : |tensorInner (signTensor f) Q| - |tensorInner E Q| ≤
      |tensorInner (signTensor f) Q - tensorInner E Q| :=
    abs_sub_abs_le_abs_sub _ _
  linarith

end DualityAndDiscrepancy

end CslibFrontier.Computability.Communication.NOF
