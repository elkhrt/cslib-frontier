module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Rat.Defs

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Int.Interval
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The Steinitz Lemma and Column-Independent Small Integer Solutions

Proves the finite-dimensional Steinitz lemma over `ℚ` in the `ℓ∞` norm via the
Grinberg–Sevastyanov linear-algebraic backward induction, and derives a
column-independent upper bound on the `ℓ₁` norm of minimal nonnegative integer solutions
of `A *ᵥ x = b`.

## Main results

* `CslibFrontier.Foundations.LinearAlgebra.steinitz_lemma`: any zero-sum family of vectors
  in `Fin m → ℚ` bounded by `B` in `ℓ∞` admits an ordering whose partial sums are bounded
  by `m * B`.
* `CslibFrontier.Foundations.LinearAlgebra.exists_nonneg_int_mulVec_eq_sum_le`: if
  `A *ᵥ x₀ = b` has a nonnegative integer solution for an `m × n` integer matrix `A` with
  entries and RHS bounded in absolute value by `B`, then it has a nonnegative integer
  solution `x` with `∑ j, x j ≤ (2 * (m + 1) * B + 1) ^ m` (independent of `n`).
-/

public section

namespace CslibFrontier.Foundations.LinearAlgebra

open Finset Matrix

/-- Helper: given `S : Finset (Fin L)` with `m < S.card` and weights `α : Fin L → ℚ`
in `[0, 1]` satisfying `∑ i ∈ S, α i • v i = 0` and `∑ i ∈ S, α i = S.card - m - 1`,
there exists a weight vector `β` on `S` with the same equations and some `i₀ ∈ S`
having `β i₀ = 0`. -/
private lemma exists_zero_weight {L m : ℕ} (v : Fin L → Fin m → ℚ)
    (S : Finset (Fin L)) (_hm : m < S.card)
    (α : Fin L → ℚ) (h0 : ∀ i ∈ S, 0 ≤ α i) (h1 : ∀ i ∈ S, α i ≤ 1)
    (hsum_v : ∀ r : Fin m, ∑ i ∈ S, α i * v i r = 0)
    (hsum_one : ∑ i ∈ S, α i = (S.card : ℚ) - m - 1) :
    ∃ β : Fin L → ℚ, (∀ i ∈ S, 0 ≤ β i) ∧ (∀ i ∈ S, β i ≤ 1) ∧
      (∀ r : Fin m, ∑ i ∈ S, β i * v i r = 0) ∧
      (∑ i ∈ S, β i = (S.card : ℚ) - m - 1) ∧
      ∃ i₀ ∈ S, β i₀ = 0 := by
  classical
  -- Induct on the number of strictly interior coordinates `i ∈ S` with `0 < α i < 1`.
  suffices h : ∀ k : ℕ, ∀ β : Fin L → ℚ,
      (S.filter fun i ↦ 0 < β i ∧ β i < 1).card ≤ k →
      (∀ i ∈ S, 0 ≤ β i) → (∀ i ∈ S, β i ≤ 1) →
      (∀ r : Fin m, ∑ i ∈ S, β i * v i r = 0) →
      (∑ i ∈ S, β i = (S.card : ℚ) - m - 1) →
      ∃ γ : Fin L → ℚ, (∀ i ∈ S, 0 ≤ γ i) ∧ (∀ i ∈ S, γ i ≤ 1) ∧
        (∀ r : Fin m, ∑ i ∈ S, γ i * v i r = 0) ∧
        (∑ i ∈ S, γ i = (S.card : ℚ) - m - 1) ∧
        ∃ i₀ ∈ S, γ i₀ = 0 by
    exact h S.card α (card_filter_le _ _) h0 h1 hsum_v hsum_one
  intro k
  induction k with
  | zero =>
    intro β hcard hβ0 hβ1 hβv hβone
    refine ⟨β, hβ0, hβ1, hβv, hβone, ?_⟩
    by_contra hno
    push Not at hno
    have hall1 : ∀ i ∈ S, β i = 1 := by
      intro i hi
      have hpos : 0 < β i := lt_of_le_of_ne (hβ0 i hi) (Ne.symm (hno i hi))
      have hnotlt : ¬β i < 1 := by
        intro hlt
        have hmem : i ∈ S.filter (fun j ↦ 0 < β j ∧ β j < 1) :=
          mem_filter.mpr ⟨hi, hpos, hlt⟩
        have := card_pos.mpr ⟨i, hmem⟩
        omega
      linarith [hβ1 i hi]
    have hsum_eq : ∑ i ∈ S, β i = (S.card : ℚ) := by
      rw [Finset.sum_congr rfl hall1, Finset.sum_const, nsmul_eq_mul, mul_one]
    linarith
  | succ k ih =>
    intro β hcard hβ0 hβ1 hβv hβone
    let F := S.filter (fun i ↦ 0 < β i ∧ β i < 1)
    by_cases hF : F.card ≤ m + 1
    · -- At most `m + 1` interior coordinates; some coordinate in `S` must be `0`.
      refine ⟨β, hβ0, hβ1, hβv, hβone, ?_⟩
      by_contra hno
      push Not at hno
      have hsub : S \ F ⊆ S := sdiff_subset
      have hall1 : ∀ i ∈ S \ F, β i = 1 := by
        intro i hi
        have hiS : i ∈ S := (mem_sdiff.mp hi).1
        have hniF : i ∉ F := (mem_sdiff.mp hi).2
        have hpos : 0 < β i := lt_of_le_of_ne (hβ0 i hiS) (Ne.symm (hno i hiS))
        have hnotlt : ¬β i < 1 := fun hlt ↦ hniF (mem_filter.mpr ⟨hiS, hpos, hlt⟩)
        linarith [hβ1 i hiS]
      have hsum_split : ∑ i ∈ S, β i = ∑ i ∈ S \ F, β i + ∑ i ∈ F, β i := by
        rw [← Finset.sum_union disjoint_sdiff_self_left, sdiff_union_of_subset (filter_subset _ _)]
      have hF_nonneg : 0 ≤ ∑ i ∈ F, β i :=
        Finset.sum_nonneg fun i hi ↦ hβ0 i (mem_filter.mp hi).1
      have hS_sdiff : ∑ i ∈ S \ F, β i = ((S \ F).card : ℚ) := by
        rw [Finset.sum_congr rfl hall1, Finset.sum_const, nsmul_eq_mul, mul_one]
      have hcard_sdiff : (S \ F).card + F.card = S.card :=
        card_sdiff_add_card_eq_card (filter_subset _ _)
      have hF_pos : F.Nonempty → 0 < ∑ i ∈ F, β i := fun hne ↦
        Finset.sum_pos (fun i hi ↦ (mem_filter.mp hi).2.1) hne
      by_cases hFne : F.Nonempty
      · have hpos := hF_pos hFne
        have hq : ((S \ F).card : ℚ) + (F.card : ℚ) = (S.card : ℚ) := by exact_mod_cast hcard_sdiff
        have hFq : (F.card : ℚ) ≤ (m : ℚ) + 1 := by exact_mod_cast hF
        linarith
      · rw [not_nonempty_iff_eq_empty] at hFne
        have hFq : F.card = 0 := by simp [hFne]
        have hq : ((S \ F).card : ℚ) = (S.card : ℚ) := by
          have : (S \ F).card = S.card := by omega
          exact_mod_cast this
        linarith
    · -- More than `m + 1` interior coordinates: find a nonzero kernel vector on `F`.
      have hFgt : m + 1 < F.card := by omega
      let M : Matrix (Fin (m + 1)) F ℚ := Matrix.of fun r j ↦
        if hr : r.val < m then v j.1 ⟨r.val, hr⟩ else 1
      have hrank : Module.finrank ℚ (Fin (m + 1) → ℚ) < Module.finrank ℚ (F → ℚ) := by
        simp only [Module.finrank_pi, Fintype.card_fin, Fintype.card_coe]
        exact hFgt
      have hnotinj : ¬Function.Injective M.mulVecLin := by
        intro hinj
        have := LinearMap.finrank_le_finrank_of_injective hinj
        omega
      have hker : ∃ dF : F → ℚ, dF ≠ 0 ∧ M *ᵥ dF = 0 := by
        by_contra hall
        apply hnotinj
        rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
        intro dF hdF
        by_contra hne
        exact hall ⟨dF, hne, hdF⟩
      obtain ⟨dF, hdF_ne, hdF_ker⟩ := hker
      let d : Fin L → ℚ := fun i ↦ if hi : i ∈ F then dF ⟨i, hi⟩ else 0
      have hd_zero : ∀ i, i ∉ F → d i = 0 := fun i hi ↦ by simp [d, hi]
      have hd_ne : ∃ i ∈ F, d i ≠ 0 := by
        by_contra h
        push Not at h
        apply hdF_ne
        funext ⟨i, hi⟩
        simpa [d, hi] using h i hi
      have hFS : F ⊆ S := filter_subset _ S
      have hd_v : ∀ r : Fin m, ∑ i ∈ S, d i * v i r = 0 := by
        intro r
        have hr0 := congrFun hdF_ker ⟨r.val, by omega⟩
        simp only [mulVec, dotProduct, M, Matrix.of_apply, r.isLt, dite_true,
          Pi.zero_apply] at hr0
        rw [← Finset.sum_subset hFS (fun i _ hi ↦ by simp [d, hi])]
        rw [← Finset.sum_coe_sort F (fun i ↦ d i * v i r)]
        convert hr0 using 1
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        simp [d, j.2, mul_comm]
      have hd_one : ∑ i ∈ S, d i = 0 := by
        have hm0 := congrFun hdF_ker ⟨m, by omega⟩
        simp only [mulVec, dotProduct, M, Matrix.of_apply, lt_irrefl, dite_false, one_mul,
          Pi.zero_apply] at hm0
        rw [← Finset.sum_subset hFS (fun i _ hi ↦ by simp [d, hi])]
        rw [← Finset.sum_coe_sort F d]
        convert hm0 using 1
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        simp [d, j.2]
      -- Pick `t > 0` moving `β` along `d` (or `-d`) until an interior coord hits `0`/`1`.
      obtain ⟨i₁, hi₁, hdi₁⟩ := hd_ne
      -- Normalize sign so some `i ∈ F` has `d i > 0` (replacing `d` by `-d` if needed).
      have ⟨d', hd'_zero, hd'_v, hd'_one, hd'_pos⟩ :
          ∃ d' : Fin L → ℚ, (∀ i, i ∉ F → d' i = 0) ∧
            (∀ r : Fin m, ∑ i ∈ S, d' i * v i r = 0) ∧
            (∑ i ∈ S, d' i = 0) ∧ (∃ i ∈ F, 0 < d' i) := by
        rcases lt_or_gt_of_ne hdi₁ with hlt | hgt
        · refine ⟨-d, fun i hi ↦ by simp [hd_zero i hi], fun r ↦ ?_, ?_,
            ⟨i₁, hi₁, by simp; linarith⟩⟩
          · simp [Pi.neg_apply, neg_mul, Finset.sum_neg_distrib, hd_v r]
          · simp [Pi.neg_apply, Finset.sum_neg_distrib, hd_one]
        · exact ⟨d, hd_zero, hd_v, hd_one, ⟨i₁, hi₁, hgt⟩⟩
      -- For each `i ∈ F` with `d' i > 0`, `β i / d' i > 0` and `(1 - β i) / d' i > 0`;
      -- for each `i ∈ F` with `d' i < 0`, `β i / (-d' i) > 0`.
      -- Move `β' := β - t * d'` with `t` the minimum of `β i / d' i` (for `d' i > 0`)
      -- and `(1 - β i) / (-d' i)` (for `d' i < 0`).
      let candidates : Finset ℚ :=
        (F.filter (fun i ↦ 0 < d' i)).image (fun i ↦ β i / d' i) ∪
        (F.filter (fun i ↦ d' i < 0)).image (fun i ↦ (1 - β i) / (-d' i))
      have hcand_ne : candidates.Nonempty := by
        obtain ⟨i, hi, hpos⟩ := hd'_pos
        exact ⟨β i / d' i, mem_union_left _ (mem_image.mpr ⟨i, mem_filter.mpr ⟨hi, hpos⟩, rfl⟩)⟩
      set t : ℚ := candidates.min' hcand_ne with ht
      have ht_pos : 0 < t := by
        have ht_mem := min'_mem candidates hcand_ne
        rcases mem_union.mp ht_mem with h1 | h2
        · obtain ⟨i, hi, hti⟩ := mem_image.mp h1
          have hiF := (mem_filter.mp hi).1
          have hdi := (mem_filter.mp hi).2
          rw [ht, ← hti]
          exact div_pos (mem_filter.mp hiF).2.1 hdi
        · obtain ⟨i, hi, hti⟩ := mem_image.mp h2
          have hiF := (mem_filter.mp hi).1
          have hdi := (mem_filter.mp hi).2
          rw [ht, ← hti]
          exact div_pos (sub_pos.mpr (mem_filter.mp hiF).2.2) (neg_pos.mpr hdi)
      let β' : Fin L → ℚ := fun i ↦ β i - t * d' i
      have hβ'_0 : ∀ i ∈ S, 0 ≤ β' i := by
        intro i hi
        by_cases hiF : i ∈ F
        · rcases lt_trichotomy (d' i) 0 with hneg | hzero | hpos
          · have : 0 ≤ -t * d' i := by nlinarith
            dsimp only [β']
            linarith [hβ0 i hi]
          · simp [β', hzero, hβ0 i hi]
          · have hle : t ≤ β i / d' i :=
              min'_le _ _ (mem_union_left _ (mem_image.mpr ⟨i, mem_filter.mpr ⟨hiF, hpos⟩, rfl⟩))
            have hmul : t * d' i ≤ β i := (le_div_iff₀ hpos).mp hle
            dsimp only [β']
            linarith
        · simp [β', hd'_zero i hiF, hβ0 i hi]
      have hβ'_1 : ∀ i ∈ S, β' i ≤ 1 := by
        intro i hi
        by_cases hiF : i ∈ F
        · rcases lt_trichotomy (d' i) 0 with hneg | hzero | hpos
          · have hle : t ≤ (1 - β i) / (-d' i) :=
              min'_le _ _ (mem_union_right _ (mem_image.mpr ⟨i, mem_filter.mpr ⟨hiF, hneg⟩, rfl⟩))
            have hmul : t * (-d' i) ≤ 1 - β i := (le_div_iff₀ (neg_pos.mpr hneg)).mp hle
            dsimp only [β']
            linarith
          · simp [β', hzero, hβ1 i hi]
          · dsimp only [β']
            nlinarith [hβ1 i hi]
        · simp [β', hd'_zero i hiF, hβ1 i hi]
      have hβ'_v : ∀ r : Fin m, ∑ i ∈ S, β' i * v i r = 0 := by
        intro r
        have : ∑ i ∈ S, β' i * v i r =
            (∑ i ∈ S, β i * v i r) - t * (∑ i ∈ S, d' i * v i r) := by
          simp only [β', sub_mul, Finset.sum_sub_distrib, Finset.mul_sum, mul_assoc]
        rw [this, hβv r, hd'_v r, mul_zero, sub_zero]
      have hβ'_one : ∑ i ∈ S, β' i = (S.card : ℚ) - m - 1 := by
        have : ∑ i ∈ S, β' i = (∑ i ∈ S, β i) - t * (∑ i ∈ S, d' i) := by
          simp only [β', Finset.sum_sub_distrib, Finset.mul_sum]
        rw [this, hβone, hd'_one, mul_zero, sub_zero]
      -- At least one coordinate in `F` hits `0` or `1`, so the interior set strictly shrinks.
      have hshrink : (S.filter fun i ↦ 0 < β' i ∧ β' i < 1).card ≤ k := by
        have hsub : S.filter (fun i ↦ 0 < β' i ∧ β' i < 1) ⊂ F := by
          rw [Finset.ssubset_iff_subset_ne]
          refine ⟨fun i hi ↦ ?_, fun heq ↦ ?_⟩
          · have hiS := (mem_filter.mp hi).1
            by_cases hiF : i ∈ F
            · exact hiF
            · exfalso
              have hsame : β' i = β i := by simp [β', hd'_zero i hiF]
              have hβi := (mem_filter.mp hi).2
              rw [hsame] at hβi
              exact hiF (mem_filter.mpr ⟨hiS, hβi⟩)
          · have ht_mem := min'_mem candidates hcand_ne
            rcases mem_union.mp ht_mem with h1 | h2
            · obtain ⟨i, hi, hti⟩ := mem_image.mp h1
              have hiF := (mem_filter.mp hi).1
              have hdi := (mem_filter.mp hi).2
              have hzero : β' i = 0 := by
                dsimp only [β']
                rw [ht, ← hti, div_mul_cancel₀ _ (ne_of_gt hdi), sub_self]
              rw [← heq] at hiF
              linarith [(mem_filter.mp hiF).2.1]
            · obtain ⟨i, hi, hti⟩ := mem_image.mp h2
              have hiF := (mem_filter.mp hi).1
              have hdi := (mem_filter.mp hi).2
              have hone : β' i = 1 := by
                dsimp only [β']
                have hne : -d' i ≠ 0 := ne_of_gt (neg_pos.mpr hdi)
                have hmul : t * (-d' i) = 1 - β i := by
                  rw [ht, ← hti, div_mul_cancel₀ _ hne]
                linarith
              rw [← heq] at hiF
              linarith [(mem_filter.mp hiF).2.2]
        have hlt := card_lt_card hsub
        have hFcard : F.card ≤ k + 1 := hcard
        omega
      exact ih β' hshrink hβ'_0 hβ'_1 hβ'_v hβ'_one

/-- **Steinitz lemma** in `ℓ∞` norm over `ℚ`:
given `L` vectors `v : Fin L → Fin m → ℚ` with `∑ i, v i = 0` and `|v i r| ≤ B` for all `i, r`,
there exists a permutation `σ` of `Fin L` such that every partial sum
`∑ j ∈ Finset.univ.filter (·.val < t), v (σ j) r` has absolute value at most `m * B`.
-/
theorem steinitz_lemma {L m : ℕ} {v : Fin L → Fin m → ℚ} {B : ℚ}
    (hB : 0 ≤ B) (hnorm : ∀ i r, |v i r| ≤ B) (hzero : ∀ r, ∑ i : Fin L, v i r = 0) :
    ∃ σ : Equiv.Perm (Fin L), ∀ (t : ℕ) (r : Fin m),
      |∑ j ∈ Finset.univ.filter (fun j : Fin L ↦ j.val < t), v (σ j) r| ≤ (m : ℚ) * B := by
  classical
  -- Build a decreasing chain `S L ⊃ S (L-1) ⊃ ... ⊃ S m` (when `m ≤ L`).
  by_cases hLm : L ≤ m
  · refine ⟨Equiv.refl (Fin L), fun t r ↦ ?_⟩
    calc |∑ j ∈ Finset.univ.filter (fun j : Fin L ↦ j.val < t), v j r|
        ≤ ∑ j ∈ Finset.univ.filter (fun j : Fin L ↦ j.val < t), |v j r| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j ∈ Finset.univ.filter (fun j : Fin L ↦ j.val < t), B :=
          sum_le_sum fun j _ ↦ hnorm j r
      _ = ((Finset.univ.filter (fun j : Fin L ↦ j.val < t)).card : ℚ) * B := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ (m : ℚ) * B := by
          apply mul_le_mul_of_nonneg_right _ hB
          have : (Finset.univ.filter (fun j : Fin L ↦ j.val < t)).card ≤ L :=
            (card_filter_le _ _).trans (by simp)
          exact_mod_cast this.trans hLm
  · push Not at hLm
    -- By backward induction from `k = L` down to `k = m`, build subsets `S k` of card `k`
    -- with weights `α` in `[0,1]` summing to `k - m` and `∑ i ∈ S k, α i * v i r = 0`,
    -- plus a bijection `f` ordering `Fin L` so that `{f j | j < k} = S k` for all `k ≥ m`.
    suffices hchain : ∀ d : ℕ, d ≤ L - m →
        ∃ (S : Finset (Fin L)) (α : Fin L → ℚ) (tail : List (Fin L)),
          S.card = L - d ∧ tail.length = d ∧ tail.Nodup ∧
          (∀ x ∈ tail, x ∉ S) ∧
          (∀ i ∈ S, 0 ≤ α i) ∧ (∀ i ∈ S, α i ≤ 1) ∧
          (∀ r, ∑ i ∈ S, α i * v i r = 0) ∧
          (∑ i ∈ S, α i = ((L - d : ℕ) : ℚ) - m) ∧
          (∀ j ≤ d, ∀ r, |∑ i ∈ S ∪ (tail.take j).toFinset, v i r| ≤ (m : ℚ) * B) by
      obtain ⟨S, α, tail, hScard, hlen, hnodup, hdisj, _, _, _, _, hbound⟩ :=
        hchain (L - m) le_rfl
      -- Concatenate `S.toList` (length `m`) and `tail` (length `L - m`) to get a permutation.
      let full : List (Fin L) := S.toList ++ tail
      have hfull_len : full.length = L := by
        simp only [full, List.length_append, Finset.length_toList, hScard, hlen]
        omega
      have hfull_nodup : full.Nodup := by
        rw [List.nodup_append]
        refine ⟨S.nodup_toList, hnodup, fun a ha b hb hab ↦ ?_⟩
        subst hab
        exact hdisj a hb (Finset.mem_toList.mp ha)
      have hfull_mem : ∀ x : Fin L, x ∈ full := by
        intro x
        have hcard : full.toFinset.card = L := by
          rw [List.toFinset_card_of_nodup hfull_nodup, hfull_len]
        have heq : full.toFinset = Finset.univ :=
          Finset.eq_univ_of_card _ (by simpa using hcard)
        exact List.mem_toFinset.mp (heq ▸ Finset.mem_univ x)
      let σFun : Fin L → Fin L := fun j ↦ full[j.val]'(by omega)
      have hσ_inj : Function.Injective σFun := by
        intro a b hab
        have := (List.Nodup.getElem_inj_iff hfull_nodup).mp hab
        exact Fin.ext this
      let σ : Equiv.Perm (Fin L) :=
        Equiv.ofBijective σFun (Finite.injective_iff_bijective.mp hσ_inj)
      refine ⟨σ, fun t r ↦ ?_⟩
      by_cases htm : t ≤ m
      · calc |∑ j ∈ Finset.univ.filter (fun j : Fin L ↦ j.val < t), v (σ j) r|
            ≤ ∑ j ∈ Finset.univ.filter (fun j : Fin L ↦ j.val < t), |v (σ j) r| :=
              abs_sum_le_sum_abs _ _
          _ ≤ ∑ _j ∈ Finset.univ.filter (fun j : Fin L ↦ j.val < t), B :=
              sum_le_sum fun j _ ↦ hnorm _ r
          _ = ((Finset.univ.filter (fun j : Fin L ↦ j.val < t)).card : ℚ) * B := by
              rw [sum_const, nsmul_eq_mul]
          _ ≤ (m : ℚ) * B := by
              apply mul_le_mul_of_nonneg_right _ hB
              have hcard_le : (Finset.univ.filter (fun j : Fin L ↦ j.val < t)).card ≤ t := by
                calc (Finset.univ.filter (fun j : Fin L ↦ j.val < t)).card
                    ≤ (Finset.range t).card := by
                      refine Finset.card_le_card_of_injOn Fin.val (fun j hj ↦ ?_)
                        (fun a _ b _ h ↦ Fin.ext h)
                      exact mem_range.mpr (mem_filter.mp hj).2
                  _ = t := card_range t
              exact_mod_cast hcard_le.trans htm
      · have hle_d : min (t - m) (L - m) ≤ L - m := Nat.min_le_right _ _
        have hset_eq : (Finset.univ.filter (fun j : Fin L ↦ j.val < t)).image σ =
            S ∪ (tail.take (min (t - m) (L - m))).toFinset := by
          ext x
          simp only [mem_image, mem_filter, mem_univ, true_and, mem_union, List.mem_toFinset]
          constructor
          · rintro ⟨j, hjt, rfl⟩
            change full[j.val] ∈ S ∨ full[j.val] ∈ tail.take (min (t - m) (L - m))
            by_cases hjm : j.val < S.toList.length
            · left
              rw [List.getElem_append_left hjm]
              exact Finset.mem_toList.mp (List.getElem_mem hjm)
            · right
              have hjm' : S.toList.length ≤ j.val := by omega
              rw [List.getElem_append_right hjm']
              have hidx : j.val - S.toList.length < min (t - m) (L - m) := by
                have hSlen : S.toList.length = m := by rw [Finset.length_toList, hScard]; omega
                omega
              have htake : (tail.take (min (t - m) (L - m)))[j.val - S.toList.length]'(by
                  rw [List.length_take]; omega) = tail[j.val - S.toList.length]'(by omega) :=
                List.getElem_take
              rw [← htake]
              exact List.getElem_mem _
          · intro hx
            rcases hx with hxS | hxt
            · obtain ⟨k, hk, hkx⟩ := List.getElem_of_mem (Finset.mem_toList.mpr hxS)
              have hkL : k < L := by rw [Finset.length_toList, hScard] at hk; omega
              refine ⟨⟨k, hkL⟩, ?_, ?_⟩
              · dsimp only
                rw [Finset.length_toList, hScard] at hk
                omega
              · change full[k] = x
                rw [List.getElem_append_left hk, hkx]
            · obtain ⟨k, hk, hkx⟩ := List.getElem_of_mem hxt
              rw [List.length_take] at hk
              have hk' : k < min (t - m) (L - m) := by omega
              have hktail : k < tail.length := by omega
              have hSlen : S.toList.length = m := by rw [Finset.length_toList, hScard]; omega
              have hmkL : m + k < L := by omega
              refine ⟨⟨m + k, hmkL⟩, by dsimp only; omega, ?_⟩
              change full[m + k] = x
              have hge : S.toList.length ≤ m + k := by omega
              rw [List.getElem_append_right hge]
              simpa only [hSlen, Nat.add_sub_cancel_left, List.getElem_take] using hkx
        have hinj_on : Set.InjOn σ
            (Finset.univ.filter (fun j : Fin L ↦ j.val < t) : Set (Fin L)) :=
          fun _ _ _ _ h ↦ σ.injective h
        rw [← Finset.sum_image (f := fun i ↦ v i r) hinj_on, hset_eq]
        exact hbound (min (t - m) (L - m)) hle_d r
    -- Prove `hchain` by induction on `d`.
    intro d
    induction d with
    | zero =>
      intro _
      refine ⟨Finset.univ, fun _ ↦ ((L : ℚ) - m) / L, [], by simp, rfl, List.nodup_nil,
        fun _ h ↦ absurd h (List.not_mem_nil), fun _ _ ↦ ?_, fun _ _ ↦ ?_, fun r ↦ ?_, ?_, ?_⟩
      · have : (0 : ℚ) ≤ (L : ℚ) - m := by
          have : (m : ℚ) ≤ L := by exact_mod_cast hLm.le
          linarith
        exact div_nonneg this (by positivity)
      · have hLpos : (0 : ℚ) < L := by exact_mod_cast (by omega : 0 < L)
        rw [div_le_one hLpos]
        have : (0 : ℚ) ≤ m := by positivity
        linarith
      · rw [← Finset.mul_sum, hzero r, mul_zero]
      · rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        have hLne : (L : ℚ) ≠ 0 := by exact_mod_cast (by omega : L ≠ 0)
        simp [mul_div_cancel₀ _ hLne]
      · intro j hj r
        have hj0 : j = 0 := by omega
        subst hj0
        simp only [List.take_zero, List.toFinset_nil, union_empty, hzero r, abs_zero]
        exact mul_nonneg (Nat.cast_nonneg m) hB
    | succ d ih =>
      intro hd
      obtain ⟨S, α, tail, hScard, hlen, hnodup, hdisj, hα0, hα1, hαv, hαone, hbound⟩ :=
        ih (by omega)
      have hmS : m < S.card := by omega
      -- Scale `α` by `((S.card - m - 1) / (S.card - m))` to feed into `exists_zero_weight`.
      have hSm_pos : (0 : ℚ) < (S.card : ℚ) - m := by
        have : (m : ℚ) < S.card := by exact_mod_cast hmS
        linarith
      let c : ℚ := ((S.card : ℚ) - m - 1) / ((S.card : ℚ) - m)
      have hc0 : 0 ≤ c := by
        apply div_nonneg _ (le_of_lt hSm_pos)
        have : (m + 1 : ℚ) ≤ S.card := by exact_mod_cast hmS
        linarith
      have hc1 : c ≤ 1 := by
        rw [div_le_one hSm_pos]
        linarith
      let α' : Fin L → ℚ := fun i ↦ c * α i
      have hα'0 : ∀ i ∈ S, 0 ≤ α' i := fun i hi ↦ mul_nonneg hc0 (hα0 i hi)
      have hα'1 : ∀ i ∈ S, α' i ≤ 1 := fun i hi ↦
        (mul_le_mul_of_nonneg_right hc1 (hα0 i hi)).trans (by simpa using hα1 i hi)
      have hα'v : ∀ r, ∑ i ∈ S, α' i * v i r = 0 := fun r ↦ by
        simp only [α', mul_assoc, ← Finset.mul_sum, hαv r, mul_zero]
      have hα'one : ∑ i ∈ S, α' i = (S.card : ℚ) - m - 1 := by
        have hne : (S.card : ℚ) - m ≠ 0 := ne_of_gt hSm_pos
        have hS_eq : ((L - d : ℕ) : ℚ) = (S.card : ℚ) := by exact_mod_cast hScard.symm
        rw [show ∑ i ∈ S, α' i = c * ∑ i ∈ S, α i from (Finset.mul_sum S α c).symm,
          hαone, hS_eq]
        dsimp only [c]
        exact div_mul_cancel₀ _ hne
      obtain ⟨β, hβ0, hβ1, hβv, hβone, i₀, hi₀S, hβi₀⟩ :=
        exists_zero_weight v S hmS α' hα'0 hα'1 hα'v hα'one
      let S' := S.erase i₀
      let tail' := i₀ :: tail
      have hS'card : S'.card = L - (d + 1) := by
        rw [card_erase_of_mem hi₀S, hScard]; omega
      have htail'_len : tail'.length = d + 1 := by simp [tail', hlen]
      have htail'_nodup : tail'.Nodup :=
        List.nodup_cons.mpr ⟨fun h ↦ hdisj i₀ h hi₀S, hnodup⟩
      have hdisj' : ∀ x ∈ tail', x ∉ S' := by
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hxt
        · exact Finset.notMem_erase _ _
        · exact fun h ↦ hdisj x hxt (mem_of_mem_erase h)
      have hβ_sum_S' : ∑ i ∈ S', β i = ((L - (d + 1) : ℕ) : ℚ) - m := by
        have h1 := Finset.add_sum_erase S β hi₀S
        rw [hβi₀, zero_add] at h1
        rw [h1, hβone, hScard]
        have hLd : (1 : ℚ) ≤ ((L - d : ℕ) : ℚ) := by exact_mod_cast (by omega : 1 ≤ L - d)
        have hsub : ((L - (d + 1) : ℕ) : ℚ) = ((L - d : ℕ) : ℚ) - 1 := by
          have : L - (d + 1) + 1 = L - d := by omega
          have hq : ((L - (d + 1) : ℕ) : ℚ) + 1 = ((L - d : ℕ) : ℚ) := by exact_mod_cast this
          linarith
        linarith
      have hβ_v_S' : ∀ r, ∑ i ∈ S', β i * v i r = 0 := by
        intro r
        have h1 := Finset.add_sum_erase S (fun i ↦ β i * v i r) hi₀S
        rw [hβi₀, zero_mul, zero_add] at h1
        exact h1.trans (hβv r)
      refine ⟨S', β, tail', hS'card, htail'_len, htail'_nodup, hdisj',
        fun i hi ↦ hβ0 i (mem_of_mem_erase hi),
        fun i hi ↦ hβ1 i (mem_of_mem_erase hi),
        hβ_v_S', hβ_sum_S', fun j hj r ↦ ?_⟩
      rcases j with _ | j
      · -- `j = 0`: bound `|∑ i ∈ S', v i r| ≤ m * B` using `β`.
        have hdiff : ∑ i ∈ S', v i r = ∑ i ∈ S', (1 - β i) * v i r := by
          simp only [sub_mul, one_mul, Finset.sum_sub_distrib, hβ_v_S' r, sub_zero]
        rw [List.take_zero, List.toFinset_nil, union_empty, hdiff]
        calc |∑ i ∈ S', (1 - β i) * v i r|
            ≤ ∑ i ∈ S', |(1 - β i) * v i r| := abs_sum_le_sum_abs _ _
          _ ≤ ∑ i ∈ S', (1 - β i) * B := by
              refine sum_le_sum fun i hi ↦ ?_
              have h1m : 0 ≤ 1 - β i := sub_nonneg.mpr (hβ1 i (mem_of_mem_erase hi))
              rw [abs_mul, abs_of_nonneg h1m]
              exact mul_le_mul_of_nonneg_left (hnorm i r) h1m
          _ = (∑ i ∈ S', (1 - β i)) * B := by rw [Finset.sum_mul]
          _ = (m : ℚ) * B := by
              congr 1
              rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one,
                hS'card, hβ_sum_S']
              ring
      · -- `j + 1`: `S' ∪ (i₀ :: tail.take j).toFinset = S ∪ (tail.take j).toFinset`.
        have heq_set : S' ∪ (tail'.take (j + 1)).toFinset = S ∪ (tail.take j).toFinset := by
          simp only [tail', List.take_succ_cons, List.toFinset_cons, S']
          ext x
          simp only [mem_union, mem_erase, mem_insert]
          by_cases hx : x = i₀
          · subst hx; simp [hi₀S]
          · simp [hx]
        rw [heq_set]
        exact hbound j (by omega) r

/-- **Column-independent small `ℓ₁`-norm integer solution bound**:
if `A *ᵥ x₀ = b` has a nonnegative integer solution `x₀ : Fin n → ℕ`, where `A` is an `m × n`
integer matrix with `|A i j| ≤ B` and `|b i| ≤ B`, then there exists a nonnegative integer
solution `x : Fin n → ℕ` with `∑ j, x j ≤ (2 * (m + 1) * B + 1) ^ m`.
Crucially, the bound depends only on `m` and `B` — never on the column count `n`. -/
theorem exists_nonneg_int_mulVec_eq_sum_le {m n B : ℕ}
    {A : Matrix (Fin m) (Fin n) ℤ} {b : Fin m → ℤ}
    (hA : ∀ i j, |A i j| ≤ (B : ℤ)) (hb : ∀ i, |b i| ≤ (B : ℤ))
    {x₀ : Fin n → ℕ} (hAx₀ : A *ᵥ (fun j ↦ (x₀ j : ℤ)) = b) :
    ∃ x : Fin n → ℕ, A *ᵥ (fun j ↦ (x j : ℤ)) = b ∧
      ∑ j : Fin n, x j ≤ (2 * (m + 1) * B + 1) ^ m := by
  classical
  -- Choose a solution minimizing the total `ℓ₁` norm `∑ j, x j`.
  let Sol : Set (Fin n → ℕ) := {x | A *ᵥ (fun j ↦ (x j : ℤ)) = b}
  have hSol : Sol.Nonempty := ⟨x₀, hAx₀⟩
  let x : Fin n → ℕ := Function.argminOn (fun y ↦ ∑ j : Fin n, y j) Sol hSol
  have hx_mem : A *ᵥ (fun j ↦ (x j : ℤ)) = b := Function.argminOn_mem _ Sol hSol
  have hx_min : ∀ y : Fin n → ℕ, A *ᵥ (fun j ↦ (y j : ℤ)) = b →
      ∑ j : Fin n, x j ≤ ∑ j : Fin n, y j :=
    fun y hy ↦ Function.argminOn_le _ Sol hy
  refine ⟨x, hx_mem, ?_⟩
  set L : ℕ := ∑ j : Fin n, x j
  by_contra hgt
  push Not at hgt
  -- Build a list of `L` column indices where column `j` appears `x j` times.
  let cols : List (Fin n) := (Finset.univ : Finset (Fin n)).toList.flatMap fun j ↦
    List.replicate (x j) j
  have hcols_len : cols.length = L := by
    have h1 : cols.length = ((Finset.univ : Finset (Fin n)).toList.map x).sum := by
      simp [cols, List.length_flatMap]
    rw [h1]
    exact Finset.sum_map_toList (Finset.univ : Finset (Fin n)) x
  have hcols_count : ∀ j : Fin n, cols.count j = x j := by
    intro j
    rw [List.count_flatMap]
    have hsum_eq :
        ((Finset.univ : Finset (Fin n)).toList.map
          (fun a ↦ (List.replicate (x a) a).count j)).sum =
        ∑ a ∈ (Finset.univ : Finset (Fin n)), (List.replicate (x a) a).count j :=
      Finset.sum_map_toList (Finset.univ : Finset (Fin n)) _
    change ((Finset.univ : Finset (Fin n)).toList.map
      (fun a ↦ (List.replicate (x a) a).count j)).sum = x j
    rw [hsum_eq]
    trans ∑ a : Fin n, if a = j then x a else 0
    · refine Finset.sum_congr rfl fun a _ ↦ ?_
      rw [List.count_replicate]
      by_cases h : a = j <;> simp [h]
    · simp
  -- Define the `L + 1` vectors in `Fin m → ℚ`: the `L` columns of `A` plus `-b`.
  let v : Fin (L + 1) → Fin m → ℚ := fun k r ↦
    if hk : k.val < L then
      (A r (cols[k.val]'(by omega)) : ℚ)
    else
      -(b r : ℚ)
  have hB0 : (0 : ℚ) ≤ (B : ℚ) := Nat.cast_nonneg B
  have hv_norm : ∀ k r, |v k r| ≤ (B : ℚ) := by
    intro k r
    dsimp only [v]
    split_ifs with hk
    · exact_mod_cast hA r (cols[k.val]'(by omega))
    · rw [abs_neg]; exact_mod_cast hb r
  have hv_zero : ∀ r, ∑ k : Fin (L + 1), v k r = 0 := by
    intro r
    rw [Fin.sum_univ_castSucc]
    have hlast : v (Fin.last L) r = -(b r : ℚ) := by simp [v]
    rw [hlast]
    have hfirst : ∑ k : Fin L, v k.castSucc r = (∑ j : Fin n, A r j * (x j : ℤ) : ℤ) := by
      have hcast : ∀ k : Fin L, v k.castSucc r = ((A r (cols[k.val]'(by omega)) : ℤ) : ℚ) := by
        intro k; simp [v, k.isLt]
      simp_rw [hcast, ← Int.cast_sum]
      congr 1
      have hlist : ∑ k : Fin L, A r (cols[k.val]'(by omega)) =
          (cols.map (fun j ↦ A r j)).sum := by
        rw [← List.sum_ofFn]
        congr 1
        refine List.ext_getElem (by simp [hcols_len]) fun i hi _ ↦ ?_
        simp
      rw [hlist]
      have hflat : ∀ l : List (Fin n),
          ((l.flatMap fun j ↦ List.replicate (x j) j).map fun j ↦ A r j).sum =
            (l.map fun j ↦ A r j * (x j : ℤ)).sum := by
        intro l
        induction l with
        | nil => simp
        | cons a tl ih =>
          simp only [List.flatMap_cons, List.map_append, List.sum_append, List.map_replicate,
            List.sum_replicate, List.map_cons, List.sum_cons, ih]
          ring
      rw [hflat]
      exact Finset.sum_map_toList (Finset.univ : Finset (Fin n)) (fun j ↦ A r j * (x j : ℤ))
    rw [hfirst]
    have hr := congrFun hx_mem r
    simp only [mulVec, dotProduct] at hr
    rw [hr]
    ring
  -- Apply `steinitz_lemma` to `v` and drop the single element `Fin.last L`.
  obtain ⟨σ, hσ⟩ := steinitz_lemma hB0 hv_norm hv_zero
  -- Define the `L + 1` strictly increasing prefix sets of the `L` column indices
  -- obtained by deleting `pPos := σ⁻¹ (Fin.last L)` from `0, 1, ..., L`.
  let pPos : Fin (L + 1) := σ.symm (Fin.last L)
  let cut (t : Fin (L + 1)) : ℕ := if t.val ≤ pPos.val then t.val else t.val + 1
  let dropIdx (t : Fin (L + 1)) : Finset (Fin (L + 1)) :=
    (Finset.univ.filter (fun j : Fin (L + 1) ↦ j.val < cut t)).erase pPos
  -- Every `dropIdx t` avoids `pPos`, and its image under `σ` avoids `Fin.last L`.
  -- Its partial sum `sInt t` is an integer vector in `[-(m+1)*B, (m+1)*B]^m`.
  let sInt (t : Fin (L + 1)) (r : Fin m) : ℤ :=
    ∑ j ∈ dropIdx t, if hj : (σ j).val < L then A r (cols[(σ j).val]'(by omega)) else 0
  have hsInt_cast : ∀ (t : Fin (L + 1)) (r : Fin m),
      (sInt t r : ℚ) = ∑ j ∈ dropIdx t, v (σ j) r := by
    intro t r
    simp only [sInt, Int.cast_sum]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    have hne : σ j ≠ Fin.last L := fun h ↦ by
      have : j = pPos := (Equiv.eq_symm_apply σ).mpr h
      exact (mem_erase.mp hj).1 this
    have hlt : (σ j).val < L := by
      have := (σ j).isLt
      have : (σ j).val ≠ L := fun h ↦ hne (Fin.ext h)
      omega
    simp [v, hlt]
  have hsInt_bound : ∀ (t : Fin (L + 1)) (r : Fin m),
      |sInt t r| ≤ ((m + 1) * B : ℕ) := by
    intro t r
    have hq : |(sInt t r : ℚ)| ≤ (((m + 1) * B : ℕ) : ℚ) := by
      rw [hsInt_cast]
      have hfull := hσ (cut t) r
      by_cases hp : pPos ∈ Finset.univ.filter (fun j : Fin (L + 1) ↦ j.val < cut t)
      · have hsplit := Finset.add_sum_erase
          (Finset.univ.filter (fun j : Fin (L + 1) ↦ j.val < cut t)) (fun j ↦ v (σ j) r) hp
        have hsum_eq : ∑ j ∈ dropIdx t, v (σ j) r =
            (∑ j ∈ Finset.univ.filter (fun j : Fin (L + 1) ↦ j.val < cut t), v (σ j) r) -
            v (σ pPos) r := by
          dsimp only [dropIdx]; linarith
        rw [hsum_eq]
        calc |(∑ j ∈ Finset.univ.filter (fun j : Fin (L + 1) ↦ j.val < cut t), v (σ j) r) -
                v (σ pPos) r|
            ≤ |∑ j ∈ Finset.univ.filter (fun j : Fin (L + 1) ↦ j.val < cut t), v (σ j) r| +
              |v (σ pPos) r| := abs_sub _ _
          _ ≤ (m : ℚ) * B + B := add_le_add hfull (hv_norm _ r)
          _ = (((m + 1) * B : ℕ) : ℚ) := by push_cast; ring
      · have hsame : dropIdx t = Finset.univ.filter (fun j : Fin (L + 1) ↦ j.val < cut t) :=
          erase_eq_of_notMem hp
        rw [hsame]
        calc |∑ j ∈ Finset.univ.filter (fun j : Fin (L + 1) ↦ j.val < cut t), v (σ j) r|
            ≤ (m : ℚ) * B := hfull
          _ ≤ (((m + 1) * B : ℕ) : ℚ) := by
              push_cast
              nlinarith
    exact_mod_cast hq
  -- Pigeonhole on the `L + 1` vectors `sInt t : Fin m → Finset.Icc (-(M:ℤ)) M`.
  let M : ℤ := ((m + 1) * B : ℕ)
  let box : Finset (Fin m → ℤ) := Fintype.piFinset fun _ ↦ Finset.Icc (-M) M
  have hbox_card : box.card = (2 * (m + 1) * B + 1) ^ m := by
    simp only [box, Fintype.card_piFinset, Int.card_Icc, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
    congr 1
    have h2M : M + 1 - -M = ((2 * (m + 1) * B + 1 : ℕ) : ℤ) := by
      dsimp only [M]; push_cast; ring
    rw [h2M, Int.toNat_natCast]
  have hs_mem : ∀ t : Fin (L + 1), sInt t ∈ box := by
    intro t
    rw [Fintype.mem_piFinset]
    intro r
    rw [Finset.mem_Icc]
    exact abs_le.mp (hsInt_bound t r)
  have hcard_lt : box.card < (Finset.univ : Finset (Fin (L + 1))).card := by
    rw [hbox_card, Finset.card_univ, Fintype.card_fin]; omega
  obtain ⟨t₁, ht1, t₂, ht2, hne, heq⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (f := sInt) hcard_lt (fun t _ ↦ hs_mem t)
  clear ht1 ht2
  -- Assume `t₁ < t₂` (by symmetry).
  wlog hlt : t₁.val < t₂.val generalizing t₁ t₂
  · exact this t₂ t₁ hne.symm heq.symm (by
      have : t₁.val ≠ t₂.val := fun h ↦ hne (Fin.ext h)
      omega)
  -- The nonempty set `D := dropIdx t₂ \ dropIdx t₁` has zero column sum!
  let D : Finset (Fin (L + 1)) := dropIdx t₂ \ dropIdx t₁
  have hcut_lt : cut t₁ < cut t₂ := by
    dsimp only [cut]
    split_ifs <;> omega
  have hsub : dropIdx t₁ ⊆ dropIdx t₂ := by
    intro j hj
    exact mem_erase.mpr ⟨(mem_erase.mp hj).1,
      mem_filter.mpr ⟨mem_univ _, ((mem_filter.mp (mem_erase.mp hj).2).2).trans hcut_lt⟩⟩
  have hD_ne : D.Nonempty := by
    by_cases h1 : t₁.val < pPos.val
    · refine ⟨t₁, mem_sdiff.mpr ⟨mem_erase.mpr ⟨fun h ↦ by omega, mem_filter.mpr ⟨mem_univ _, ?_⟩⟩,
        fun h ↦ by
          have := (mem_filter.mp (mem_erase.mp h).2).2
          dsimp only [cut] at this
          split_ifs at this <;> omega⟩⟩
      dsimp only [cut]
      split_ifs <;> omega
    · have h2 : pPos.val < cut t₂ := by
        dsimp only [cut]
        split_ifs <;> omega
      have ht1_lt : t₁.val + 1 < L + 1 := by omega
      let j₀ : Fin (L + 1) := ⟨t₁.val + 1, ht1_lt⟩
      refine ⟨j₀, mem_sdiff.mpr ⟨mem_erase.mpr ⟨fun h ↦ ?_, mem_filter.mpr ⟨mem_univ _, ?_⟩⟩,
        fun h ↦ ?_⟩⟩
      · have : t₁.val + 1 = pPos.val := congrArg Fin.val h
        omega
      · dsimp only [j₀, cut]
        split_ifs <;> omega
      · have := (mem_filter.mp (mem_erase.mp h).2).2
        dsimp only [j₀, cut] at this
        split_ifs at this <;> omega
  -- Every `j ∈ D` satisfies `(σ j).val < L`.
  have hD_lt : ∀ j ∈ D, (σ j).val < L := by
    intro j hj
    have hne' : σ j ≠ Fin.last L := fun h ↦ by
      have : j = pPos := (Equiv.eq_symm_apply σ).mpr h
      exact (mem_erase.mp (mem_sdiff.mp hj).1).1 this
    have := (σ j).isLt
    have : (σ j).val ≠ L := fun h ↦ hne' (Fin.ext h)
    omega
  -- Sum of columns over `D` is `sInt t₂ - sInt t₁ = 0`.
  have hD_sum : ∀ r : Fin m,
      ∑ j ∈ D, (if hj : (σ j).val < L then A r (cols[(σ j).val]'(by omega)) else 0) = 0 := by
    intro r
    have hsplit : ∑ j ∈ dropIdx t₂,
          (if hj : (σ j).val < L then A r (cols[(σ j).val]'(by omega)) else 0) =
        ∑ j ∈ dropIdx t₁,
          (if hj : (σ j).val < L then A r (cols[(σ j).val]'(by omega)) else 0) +
        ∑ j ∈ D,
          (if hj : (σ j).val < L then A r (cols[(σ j).val]'(by omega)) else 0) := by
      rw [← Finset.sum_union disjoint_sdiff_self_right, union_sdiff_of_subset hsub]
    have hs_eq : sInt t₁ r = sInt t₂ r := congrFun heq r
    dsimp only [sInt] at hs_eq
    linarith
  -- Subtract the columns indexed by `D` from `x` to get a strictly smaller solution `y`.
  let colOf (i : Fin L) : Fin n := cols[i.val]'(by omega)
  have hcolOf_count : ∀ j : Fin n,
      (Finset.univ.filter fun i : Fin L ↦ colOf i = j).card = x j := by
    intro j
    rw [← hcols_count j, Finset.card_filter]
    have hmap : ∑ i : Fin L, (if colOf i = j then 1 else 0) =
        (cols.map fun a ↦ if a = j then 1 else 0).sum := by
      rw [← List.sum_ofFn]
      congr 1
      refine List.ext_getElem (by simp [hcols_len]) fun i hi _ ↦ ?_
      simp [colOf]
    rw [hmap]
    have hsum_count : ∀ l : List (Fin n),
        (l.map fun a ↦ if a = j then 1 else 0).sum = l.count j := by
      intro l
      induction l with
      | nil => simp
      | cons a tl ih =>
        rw [List.map_cons, List.sum_cons, List.count_cons, ih]
        by_cases h : a = j <;> simp [h, beq_iff_eq, Nat.add_comm]
    exact hsum_count cols
  let idxOf (k : Fin (L + 1)) (hk : k ∈ D) : Fin L := ⟨(σ k).val, hD_lt k hk⟩
  let D' : Finset (Fin L) := D.attach.image fun ⟨k, hk⟩ ↦ idxOf k hk
  have hD'_card : D'.card = D.card := by
    rw [Finset.card_image_of_injective]
    · exact Finset.card_attach
    · rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
      simp only [idxOf, Fin.mk.injEq] at hab
      exact Subtype.ext (σ.injective (Fin.ext hab))
  let dCount (j : Fin n) : ℕ := (D'.filter fun i ↦ colOf i = j).card
  have hdCount_le : ∀ j : Fin n, dCount j ≤ x j := fun j ↦ by
    rw [← hcolOf_count j]
    exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ _))
  have hdCount_sum : ∑ j : Fin n, dCount j = D'.card := by
    simpa only [dCount] using
      (Finset.sum_card_fiberwise_eq_card_filter D' (Finset.univ : Finset (Fin n)) colOf).trans
        (by simp)
  have hdCount_A : ∀ r : Fin m, ∑ j : Fin n, A r j * (dCount j : ℤ) = 0 := by
    intro r
    have hfib : ∑ j : Fin n, (dCount j : ℤ) * A r j = ∑ i ∈ D', A r (colOf i) := by
      have h := Finset.sum_fiberwise_of_maps_to (s := D') (t := (Finset.univ : Finset (Fin n)))
        (g := colOf) (f := fun i ↦ A r (colOf i)) (fun _ _ ↦ Finset.mem_univ _)
      rw [← h]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [Finset.sum_congr rfl (fun i hi ↦ by rw [(mem_filter.mp hi).2]),
        Finset.sum_const, nsmul_eq_mul]
    have hmul_comm : ∑ j : Fin n, A r j * (dCount j : ℤ) = ∑ j : Fin n, (dCount j : ℤ) * A r j :=
      Finset.sum_congr rfl fun _ _ ↦ mul_comm _ _
    rw [hmul_comm, hfib]
    have himg : ∑ i ∈ D', A r (colOf i) =
        ∑ k ∈ D.attach, A r (colOf (idxOf k.1 k.2)) := by
      dsimp only [D']
      rw [Finset.sum_image]
      rintro ⟨a, ha⟩ _ ⟨b, hb⟩ _ hab
      simp only [idxOf, Fin.mk.injEq] at hab
      exact Subtype.ext (σ.injective (Fin.ext hab))
    rw [himg, ← hD_sum r]
    rw [← Finset.sum_attach D]
    refine Finset.sum_congr rfl fun ⟨k, hk⟩ _ ↦ ?_
    simp [colOf, idxOf, hD_lt k hk]
  let y : Fin n → ℕ := fun j ↦ x j - dCount j
  have hy_sol : A *ᵥ (fun j ↦ (y j : ℤ)) = b := by
    ext r
    have hr := congrFun hx_mem r
    simp only [mulVec, dotProduct] at hr ⊢
    have hsub_cast : ∀ j : Fin n, (y j : ℤ) = (x j : ℤ) - (dCount j : ℤ) := fun j ↦
      Nat.cast_sub (hdCount_le j)
    simp_rw [hsub_cast, mul_sub, Finset.sum_sub_distrib, hr, hdCount_A r, sub_zero]
  have hy_sum : ∑ j : Fin n, y j + D'.card = L := by
    have h1 : ∑ j : Fin n, (y j + dCount j) = L := by
      refine (Finset.sum_congr rfl fun j _ ↦ Nat.sub_add_cancel (hdCount_le j)).trans rfl
    rw [Finset.sum_add_distrib, hdCount_sum] at h1
    exact h1
  have hmin := hx_min y hy_sol
  have hDpos : 0 < D'.card := by rw [hD'_card]; exact Finset.card_pos.mpr hD_ne
  omega

end CslibFrontier.Foundations.LinearAlgebra
