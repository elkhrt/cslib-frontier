module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Balanced Bicolored Matrices and Union-Generated Sequences

Combinatorial tools for propositional proof-complexity lower bounds:

* Every balanced two-coloring of an `n × n` matrix contains either `⌊c n⌋` rows each having
  entries of both colors in `2 ⌊c n⌋` distinct columns, or the transposed column configuration,
  where `c = 1 / 2 - √2 / 4 > 1 / 7`.
* Every union-generated sequence of finite sets reaching a target set `C` passes through an
  intermediate set whose intersection with a subset `C' ⊆ C` has cardinality in
  `[a * |C'|, 2 * a * |C'|)`.

## Main results

* `CslibFrontier.Logic.PL.OBDD.matrixConst`: the constant `1 / 2 - √2 / 4`.
* `CslibFrontier.Logic.PL.OBDD.balanced_matrix_bicolored_matching`: bicolored row or column
  matching in any balanced Boolean square matrix.
* `CslibFrontier.Logic.PL.OBDD.exists_intermediate_union_card`: intermediate-cardinality step in
  any union-generated sequence of finite sets.
-/

public section

namespace CslibFrontier.Logic.PL.OBDD

open Finset

/-! ### Balanced bicolored matrices -/

/-- The constant `c = 1 / 2 - √2 / 4` governing balanced matrix matchings. -/
noncomputable def matrixConst : ℝ :=
  1 / 2 - Real.sqrt 2 / 4

/-- `matrixConst` is strictly positive. -/
theorem matrixConst_pos : 0 < matrixConst := by
  unfold matrixConst
  have hsq : Real.sqrt 2 < 2 := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  linarith

/-- Lower bound `1 / 7 < matrixConst` (equivalently `100 > 98`), matching the paper's threshold
`n > 34`. -/
theorem one_div_seven_lt_matrixConst : (1 : ℝ) / 7 < matrixConst := by
  unfold matrixConst
  have hsq : Real.sqrt 2 < 10 / 7 := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  linarith

/-- Key quadratic inequality for `m = ⌊matrixConst * n⌋`: `n ^ 2 ≤ 2 * (n - 2 * m) ^ 2`. -/
private theorem sq_le_two_mul_sub_two_mul_floor (n : ℕ) :
    (n : ℝ) ^ 2 ≤ 2 * ((n : ℝ) - 2 * (Nat.floor (matrixConst * n) : ℝ)) ^ 2 := by
  have hm : (Nat.floor (matrixConst * n) : ℝ) ≤ matrixConst * n :=
    Nat.floor_le (mul_nonneg matrixConst_pos.le (Nat.cast_nonneg n))
  have hdiff : Real.sqrt 2 / 2 * (n : ℝ) ≤ (n : ℝ) - 2 * (Nat.floor (matrixConst * n) : ℝ) := by
    unfold matrixConst at hm ⊢
    linarith
  have hnn : 0 ≤ Real.sqrt 2 / 2 * (n : ℝ) := by positivity
  have hsq := mul_self_le_mul_self hnn hdiff
  have hsqrt2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  nlinarith

/-- For `m = ⌊matrixConst * n⌋` and `1 ≤ m`, we have `2 * m < n` and
`n ^ 2 + 1 < 2 * (n - 2 * m) * (n - 2 * k)` whenever `k < m`. -/
private theorem sub_two_mul_gt_half_sq {n k : ℕ}
    (hk : k < Nat.floor (matrixConst * n)) :
    2 * Nat.floor (matrixConst * n) < n ∧
      n ^ 2 + 1 < 2 * (n - 2 * Nat.floor (matrixConst * n)) * (n - 2 * k) := by
  set m := Nat.floor (matrixConst * n)
  have hm_pos : 1 ≤ m := Nat.succ_le_of_lt (Nat.lt_of_le_of_lt (Nat.zero_le k) hk)
  have hm_le : (m : ℝ) ≤ matrixConst * n :=
    Nat.floor_le (mul_nonneg matrixConst_pos.le (Nat.cast_nonneg n))
  have hsqrt_gt : (1 : ℝ) < Real.sqrt 2 := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  have h2m_lt_r : (2 * m : ℝ) < n := by
    have hn_pos : (0 : ℝ) < n := by
      by_contra h0
      have : (n : ℝ) = 0 := le_antisymm (not_lt.1 h0) (Nat.cast_nonneg n)
      have : (m : ℝ) ≤ 0 := by simpa [this] using hm_le
      have : (1 : ℝ) ≤ m := by exact_mod_cast hm_pos
      linarith
    unfold matrixConst at hm_le
    nlinarith
  have h2m_lt : 2 * m < n := by exact_mod_cast h2m_lt_r
  refine ⟨h2m_lt, ?_⟩
  have hsq_r := sq_le_two_mul_sub_two_mul_floor n
  have hdiff_ge : (1 : ℝ) ≤ (n : ℝ) - 2 * (m : ℝ) := by
    have : 1 ≤ n - 2 * m := by omega
    have hcast : ((n - 2 * m : ℕ) : ℝ) = (n : ℝ) - 2 * (m : ℝ) := by
      rw [Nat.cast_sub h2m_lt.le, Nat.cast_mul, Nat.cast_ofNat]
    linarith [show (1 : ℝ) ≤ ((n - 2 * m : ℕ) : ℝ) by exact_mod_cast this]
  have hk_le : k + 1 ≤ m := hk
  have h2k_le : 2 * k + 2 ≤ 2 * m := by omega
  have hnk_ge : ((n - 2 * m : ℕ) : ℝ) + 2 ≤ ((n - 2 * k : ℕ) : ℝ) := by
    have hnat : (n - 2 * m) + 2 ≤ n - 2 * k := by omega
    exact_mod_cast hnat
  have hcast_m : ((n - 2 * m : ℕ) : ℝ) = (n : ℝ) - 2 * (m : ℝ) := by
    rw [Nat.cast_sub h2m_lt.le, Nat.cast_mul, Nat.cast_ofNat]
  have hprod_r : (n : ℝ) ^ 2 + 1 <
      2 * ((n - 2 * m : ℕ) : ℝ) * ((n - 2 * k : ℕ) : ℝ) := by
    nlinarith
  exact_mod_cast hprod_r

/-- Greedy extraction of rows containing both a `true` and a `false` entry in disjoint columns. -/
private theorem greedy_bicolored_rows {n : ℕ} (M : Fin n → Fin n → Bool) :
    ∀ t : ℕ, ∃ (k : ℕ) (rows : Fin k ↪ Fin n) (cT cF : Fin k ↪ Fin n),
      (∀ a b, cT a ≠ cF b) ∧
      (∀ a, M (rows a) (cT a) = true ∧ M (rows a) (cF a) = false) ∧
      (k = t ∨
        ∀ i : Fin n, (∀ a, rows a ≠ i) →
          ∀ j₁ j₂ : Fin n,
            (∀ a, cT a ≠ j₁ ∧ cF a ≠ j₁) →
            (∀ a, cT a ≠ j₂ ∧ cF a ≠ j₂) →
            M i j₁ = M i j₂) := by
  intro t
  induction t with
  | zero =>
    refine ⟨0, ⟨Fin.elim0, fun a => a.elim0⟩, ⟨Fin.elim0, fun a => a.elim0⟩,
      ⟨Fin.elim0, fun a => a.elim0⟩, fun a => a.elim0, fun a => a.elim0, Or.inl rfl⟩
  | succ t ih =>
    obtain ⟨k, rows, cT, cF, hdisj, hcol, hstop⟩ := ih
    rcases hstop with rfl | hmono
    · by_cases hex : ∃ i : Fin n, (∀ a, rows a ≠ i) ∧
          ∃ j₁ j₂ : Fin n,
            (∀ a, cT a ≠ j₁ ∧ cF a ≠ j₁) ∧
            (∀ a, cT a ≠ j₂ ∧ cF a ≠ j₂) ∧
            M i j₁ = true ∧ M i j₂ = false
      · obtain ⟨i₀, hi₀, j₁, j₂, hj₁, hj₂, hM₁, hM₂⟩ := hex
        have hjne : j₁ ≠ j₂ := by
          intro h; rw [h, hM₂] at hM₁; exact Bool.false_ne_true hM₁
        let rows' : Fin (k + 1) ↪ Fin n :=
          ⟨Fin.snoc rows i₀, fun a b hab => by
            induction a using Fin.lastCases with
            | last =>
              induction b using Fin.lastCases with
              | last => rfl
              | cast b =>
                simp only [Fin.snoc_last, Fin.snoc_castSucc] at hab
                exact absurd hab.symm (hi₀ b)
            | cast a =>
              induction b using Fin.lastCases with
              | last =>
                simp only [Fin.snoc_last, Fin.snoc_castSucc] at hab
                exact absurd hab (hi₀ a)
              | cast b =>
                simp only [Fin.snoc_castSucc] at hab
                exact congrArg Fin.castSucc (rows.injective hab)⟩
        let cT' : Fin (k + 1) ↪ Fin n :=
          ⟨Fin.snoc cT j₁, fun a b hab => by
            induction a using Fin.lastCases with
            | last =>
              induction b using Fin.lastCases with
              | last => rfl
              | cast b =>
                simp only [Fin.snoc_last, Fin.snoc_castSucc] at hab
                exact absurd hab.symm (hj₁ b).1
            | cast a =>
              induction b using Fin.lastCases with
              | last =>
                simp only [Fin.snoc_last, Fin.snoc_castSucc] at hab
                exact absurd hab (hj₁ a).1
              | cast b =>
                simp only [Fin.snoc_castSucc] at hab
                exact congrArg Fin.castSucc (cT.injective hab)⟩
        let cF' : Fin (k + 1) ↪ Fin n :=
          ⟨Fin.snoc cF j₂, fun a b hab => by
            induction a using Fin.lastCases with
            | last =>
              induction b using Fin.lastCases with
              | last => rfl
              | cast b =>
                simp only [Fin.snoc_last, Fin.snoc_castSucc] at hab
                exact absurd hab.symm (hj₂ b).2
            | cast a =>
              induction b using Fin.lastCases with
              | last =>
                simp only [Fin.snoc_last, Fin.snoc_castSucc] at hab
                exact absurd hab (hj₂ a).2
              | cast b =>
                simp only [Fin.snoc_castSucc] at hab
                exact congrArg Fin.castSucc (cF.injective hab)⟩
        have hr_last : rows' (Fin.last k) = i₀ := Fin.snoc_last (α := fun _ => Fin n) i₀ (⇑rows)
        have hr_cast : ∀ a : Fin k, rows' a.castSucc = rows a :=
          fun a => Fin.snoc_castSucc (α := fun _ => Fin n) i₀ (⇑rows) a
        have hcT_last : cT' (Fin.last k) = j₁ := Fin.snoc_last (α := fun _ => Fin n) j₁ (⇑cT)
        have hcT_cast : ∀ a : Fin k, cT' a.castSucc = cT a :=
          fun a => Fin.snoc_castSucc (α := fun _ => Fin n) j₁ (⇑cT) a
        have hcF_last : cF' (Fin.last k) = j₂ := Fin.snoc_last (α := fun _ => Fin n) j₂ (⇑cF)
        have hcF_cast : ∀ a : Fin k, cF' a.castSucc = cF a :=
          fun a => Fin.snoc_castSucc (α := fun _ => Fin n) j₂ (⇑cF) a
        refine ⟨k + 1, rows', cT', cF', ?_, ?_, Or.inl rfl⟩
        · intro a b
          induction a using Fin.lastCases with
          | last =>
            induction b using Fin.lastCases with
            | last => rw [hcT_last, hcF_last]; exact hjne
            | cast b => rw [hcT_last, hcF_cast]; exact (hj₁ b).2.symm
          | cast a =>
            induction b using Fin.lastCases with
            | last => rw [hcT_cast, hcF_last]; exact (hj₂ a).1
            | cast b => rw [hcT_cast, hcF_cast]; exact hdisj a b
        · intro a
          induction a using Fin.lastCases with
          | last => rw [hr_last, hcT_last, hcF_last]; exact ⟨hM₁, hM₂⟩
          | cast a => rw [hr_cast, hcT_cast, hcF_cast]; exact hcol a
      · refine ⟨k, rows, cT, cF, hdisj, hcol, Or.inr fun i hi j₁ j₂ hj₁ hj₂ => ?_⟩
        by_contra hne
        cases h₁ : M i j₁ <;> cases h₂ : M i j₂
        · exact hne (h₁.trans h₂.symm)
        · exact hex ⟨i, hi, j₂, j₁, hj₂, hj₁, h₂, h₁⟩
        · exact hex ⟨i, hi, j₁, j₂, hj₁, hj₂, h₁, h₂⟩
        · exact hne (h₁.trans h₂.symm)
    · exact ⟨k, rows, cT, cF, hdisj, hcol, Or.inr hmono⟩

/-- **Balanced bicolored matrix matching**:
In any `n × n` Boolean matrix whose `true` and `false` entry counts differ by at most `1`, with
`m = ⌊(1/2 - √2/4) n⌋`, at least one of the following holds:
1. There are `m` distinct rows each containing a `true` and a `false` entry such that all `2m`
   chosen entries lie in pairwise distinct columns.
2. There are `m` distinct columns each containing a `true` and a `false` entry such that all `2m`
   chosen entries lie in pairwise distinct rows. -/
theorem balanced_matrix_bicolored_matching {n : ℕ} (M : Fin n → Fin n → Bool)
    (hbal :
      let w := (Finset.univ.filter (fun p : Fin n × Fin n => M p.1 p.2 = true)).card
      let b := (Finset.univ.filter (fun p : Fin n × Fin n => M p.1 p.2 = false)).card
      w ≤ b + 1 ∧ b ≤ w + 1) :
    let m := Nat.floor (matrixConst * n)
    (∃ (rows cT cF : Fin m ↪ Fin n),
        (∀ a b, cT a ≠ cF b) ∧
        ∀ a, M (rows a) (cT a) = true ∧ M (rows a) (cF a) = false) ∨
    (∃ (cols rT rF : Fin m ↪ Fin n),
        (∀ a b, rT a ≠ rF b) ∧
        ∀ a, M (rT a) (cols a) = true ∧ M (rF a) (cols a) = false) := by
  classical
  dsimp only at hbal ⊢
  set m := Nat.floor (matrixConst * n)
  obtain ⟨k, rows, cT, cF, hdisj, hcol, hstop⟩ := greedy_bicolored_rows M m
  rcases hstop with rfl | hmono
  · exact Or.inl ⟨rows, cT, cF, hdisj, hcol⟩
  · by_cases hkm : m ≤ k
    · let inc : Fin m ↪ Fin k := Fin.castLEEmb hkm
      exact Or.inl ⟨inc.trans rows, inc.trans cT, inc.trans cF,
        fun a b => hdisj (inc a) (inc b), fun a => hcol (inc a)⟩
    · right
      have hk_lt : k < m := Nat.lt_of_not_le hkm
      obtain ⟨h2m_lt, hprod_gt⟩ := sub_two_mul_gt_half_sq hk_lt
      let usedRows : Finset (Fin n) := Finset.univ.image rows
      let usedCols : Finset (Fin n) := Finset.univ.image cT ∪ Finset.univ.image cF
      let remRows : Finset (Fin n) := Finset.univ \ usedRows
      let remCols : Finset (Fin n) := Finset.univ \ usedCols
      have hcard_uR : usedRows.card = k := by
        rw [Finset.card_image_of_injective _ rows.injective, Finset.card_fin]
      have hdisj_c : Disjoint (Finset.univ.image cT) (Finset.univ.image cF) := by
        rw [Finset.disjoint_left]
        rintro j hjT hjF
        obtain ⟨a, _, rfl⟩ := Finset.mem_image.1 hjT
        obtain ⟨b, _, hba⟩ := Finset.mem_image.1 hjF
        exact hdisj a b hba.symm
      have hcard_uC : usedCols.card = 2 * k := by
        rw [Finset.card_union_of_disjoint hdisj_c,
          Finset.card_image_of_injective _ cT.injective,
          Finset.card_image_of_injective _ cF.injective, Finset.card_fin]
        omega
      have hcard_rR : remRows.card = n - k := by
        rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin, hcard_uR]
      have hcard_rC : remCols.card = n - 2 * k := by
        rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin, hcard_uC]
      have hrC_pos : 0 < remCols.card := by omega
      obtain ⟨j₀, hj₀⟩ := Finset.card_pos.1 hrC_pos
      have hmem_rR : ∀ i ∈ remRows, ∀ a, rows a ≠ i := by
        intro i hi a heq
        have : i ∈ usedRows := Finset.mem_image.2 ⟨a, Finset.mem_univ _, heq⟩
        exact (Finset.mem_sdiff.1 hi).2 this
      have hmem_rC : ∀ j ∈ remCols, ∀ a, cT a ≠ j ∧ cF a ≠ j := by
        intro j hj a
        have hnu : j ∉ usedCols := (Finset.mem_sdiff.1 hj).2
        refine ⟨fun h => hnu (Finset.mem_union_left _ (Finset.mem_image.2 ⟨a, by simp, h⟩)),
          fun h => hnu (Finset.mem_union_right _ (Finset.mem_image.2 ⟨a, by simp, h⟩))⟩
      let tRows : Finset (Fin n) := remRows.filter (fun i => M i j₀ = true)
      let fRows : Finset (Fin n) := remRows.filter (fun i => M i j₀ = false)
      have hpart : tRows.card + fRows.card = remRows.card := by
        have hdisj_tf : Disjoint tRows fRows := by
          rw [Finset.disjoint_left]
          intro i ht hf
          have h1 := (Finset.mem_filter.1 ht).2
          have h2 := (Finset.mem_filter.1 hf).2
          rw [h1] at h2; cases h2
        have hunion : tRows ∪ fRows = remRows := by
          ext i
          simp only [tRows, fRows, Finset.mem_union, Finset.mem_filter]
          cases M i j₀ <;> simp
        rw [← Finset.card_union_of_disjoint hdisj_tf, hunion]
      set w := (Finset.univ.filter (fun p : Fin n × Fin n => M p.1 p.2 = true)).card
      set b := (Finset.univ.filter (fun p : Fin n × Fin n => M p.1 p.2 = false)).card
      have hwb : w + b = n ^ 2 := by
        have hdisj_wb : Disjoint
            (Finset.univ.filter (fun p : Fin n × Fin n => M p.1 p.2 = true))
            (Finset.univ.filter (fun p : Fin n × Fin n => M p.1 p.2 = false)) := by
          rw [Finset.disjoint_left]
          intro p h1 h2
          have h1' := (Finset.mem_filter.1 h1).2
          have h2' := (Finset.mem_filter.1 h2).2
          rw [h1'] at h2'; cases h2'
        have hunion :
            Finset.univ.filter (fun p : Fin n × Fin n => M p.1 p.2 = true) ∪
              Finset.univ.filter (fun p : Fin n × Fin n => M p.1 p.2 = false) =
              Finset.univ := by
          ext p; cases M p.1 p.2 <;> simp
        have hsum : w + b = (Finset.univ : Finset (Fin n × Fin n)).card := by
          rw [← Finset.card_union_of_disjoint hdisj_wb, hunion]
        simpa [Fintype.card_prod, Nat.pow_two] using hsum
      have hw_le : 2 * w ≤ n ^ 2 + 1 := by omega
      have hb_le : 2 * b ≤ n ^ 2 + 1 := by omega
      have ht_all : ∀ i ∈ tRows, ∀ j ∈ remCols, M i j = true := by
        intro i hi j hj
        have ⟨hi_r, hi_j0⟩ := Finset.mem_filter.1 hi
        have heq := hmono i (hmem_rR i hi_r) j j₀ (hmem_rC j hj) (hmem_rC j₀ hj₀)
        exact heq.trans hi_j0
      have hf_all : ∀ i ∈ fRows, ∀ j ∈ remCols, M i j = false := by
        intro i hi j hj
        have ⟨hi_r, hi_j0⟩ := Finset.mem_filter.1 hi
        have heq := hmono i (hmem_rR i hi_r) j j₀ (hmem_rC j hj) (hmem_rC j₀ hj₀)
        exact heq.trans hi_j0
      have ht_bound : tRows.card * remCols.card ≤ w := by
        calc tRows.card * remCols.card = (tRows ×ˢ remCols).card := (Finset.card_product _ _).symm
          _ ≤ w := Finset.card_le_card (fun p hp => by
              rw [Finset.mem_product] at hp
              exact Finset.mem_filter.2 ⟨Finset.mem_univ _, ht_all p.1 hp.1 p.2 hp.2⟩)
      have hf_bound : fRows.card * remCols.card ≤ b := by
        calc fRows.card * remCols.card = (fRows ×ˢ remCols).card := (Finset.card_product _ _).symm
          _ ≤ b := Finset.card_le_card (fun p hp => by
              rw [Finset.mem_product] at hp
              exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hf_all p.1 hp.1 p.2 hp.2⟩)
      have ht_lt : tRows.card < n - 2 * m := by
        by_contra hge
        have hge' : n - 2 * m ≤ tRows.card := Nat.le_of_not_lt hge
        have hmul : (n - 2 * m) * (n - 2 * k) ≤ tRows.card * remCols.card := by
          rw [hcard_rC]; exact Nat.mul_le_mul_right _ hge'
        have hmul2 : 2 * (n - 2 * m) * (n - 2 * k) ≤ 2 * w := by
          rw [Nat.mul_assoc]
          exact Nat.mul_le_mul_left 2 (hmul.trans ht_bound)
        have hlt_w : n ^ 2 + 1 < 2 * w := lt_of_lt_of_le hprod_gt hmul2
        omega
      have hf_lt : fRows.card < n - 2 * m := by
        by_contra hge
        have hge' : n - 2 * m ≤ fRows.card := Nat.le_of_not_lt hge
        have hmul : (n - 2 * m) * (n - 2 * k) ≤ fRows.card * remCols.card := by
          rw [hcard_rC]; exact Nat.mul_le_mul_right _ hge'
        have hmul2 : 2 * (n - 2 * m) * (n - 2 * k) ≤ 2 * b := by
          rw [Nat.mul_assoc]
          exact Nat.mul_le_mul_left 2 (hmul.trans hf_bound)
        have hlt_b : n ^ 2 + 1 < 2 * b := lt_of_lt_of_le hprod_gt hmul2
        omega
      have ht_ge : m ≤ tRows.card := by omega
      have hf_ge : m ≤ fRows.card := by omega
      have hremC_ge : m ≤ remCols.card := by
        have hm_le : (m : ℝ) ≤ matrixConst * n :=
          Nat.floor_le (mul_nonneg matrixConst_pos.le (Nat.cast_nonneg n))
        have h3m : (3 * m : ℝ) < n := by
          have hsqrt_gt : (1 : ℝ) < Real.sqrt 2 := by
            rw [Real.lt_sqrt (by norm_num)]; norm_num
          have hn_pos : (0 : ℝ) < n := by
            have : 0 < n := by omega
            exact_mod_cast this
          unfold matrixConst at hm_le
          nlinarith
        have h3m_nat : 3 * m < n := by exact_mod_cast h3m
        omega
      obtain ⟨colsSet, hcolsSub, hcolsCard⟩ := Finset.exists_subset_card_eq hremC_ge
      obtain ⟨rTSet, hrTSub, hrTCard⟩ := Finset.exists_subset_card_eq ht_ge
      obtain ⟨rFSet, hrFSub, hrFCard⟩ := Finset.exists_subset_card_eq hf_ge
      let cols : Fin m ↪ Fin n :=
        (colsSet.equivFinOfCardEq hcolsCard).symm.toEmbedding.trans (Function.Embedding.subtype _)
      let rT : Fin m ↪ Fin n :=
        (rTSet.equivFinOfCardEq hrTCard).symm.toEmbedding.trans (Function.Embedding.subtype _)
      let rF : Fin m ↪ Fin n :=
        (rFSet.equivFinOfCardEq hrFCard).symm.toEmbedding.trans (Function.Embedding.subtype _)
      refine ⟨cols, rT, rF, ?_, ?_⟩
      · intro a b heq
        have ha : rT a ∈ tRows := hrTSub ((rTSet.equivFinOfCardEq hrTCard).symm a).2
        have hb : rF b ∈ fRows := hrFSub ((rFSet.equivFinOfCardEq hrFCard).symm b).2
        rw [heq] at ha
        have h1 := (Finset.mem_filter.1 ha).2
        have h2 := (Finset.mem_filter.1 hb).2
        rw [h1] at h2; cases h2
      · intro a
        have hc : cols a ∈ remCols := hcolsSub ((colsSet.equivFinOfCardEq hcolsCard).symm a).2
        have ha : rT a ∈ tRows := hrTSub ((rTSet.equivFinOfCardEq hrTCard).symm a).2
        have hb : rF a ∈ fRows := hrFSub ((rFSet.equivFinOfCardEq hrFCard).symm a).2
        exact ⟨ht_all _ ha _ hc, hf_all _ hb _ hc⟩

/-! ### Intermediate sets in union-generated sequences -/

/-- **Intermediate cardinality in union-generated sequences**:
Let `C` be a finite set, `R ⊆ C` with `2 ≤ |R|`, and `B : Fin l → Finset α` (`0 < l`) a sequence
of subsets of `C` ending at `B (l - 1) = C` such that each `B i` is empty, a singleton `{c}`, or
the union `B j ∪ B k` of two earlier sets (`j, k < i`). Then for every `a : ℝ` with
`1 / |R| < a ≤ 1 / 2`, there exists `j < l - 1` with `a |R| ≤ |B j ∩ R| < 2 a |R|`. -/
theorem exists_intermediate_union_card {α : Type*} [DecidableEq α] {l : ℕ} (hl : 0 < l)
    (C R : Finset α) (hRC : R ⊆ C) (hR : 2 ≤ R.card)
    (B : Fin l → Finset α)
    (hlast : B ⟨l - 1, Nat.sub_lt hl Nat.zero_lt_one⟩ = C)
    (hstep : ∀ i : Fin l,
      B i = ∅ ∨ (∃ c ∈ C, B i = {c}) ∨ ∃ j k : Fin l, j < i ∧ k < i ∧ B i = B j ∪ B k)
    {a : ℝ} (ha_lo : (1 : ℝ) / R.card < a) (ha_hi : a ≤ 1 / 2) :
    ∃ j : Fin l, j.val + 1 < l ∧
      a * R.card ≤ ((B j ∩ R).card : ℝ) ∧ ((B j ∩ R).card : ℝ) < 2 * a * R.card := by
  have hR_pos : (0 : ℝ) < R.card := by exact_mod_cast (show 0 < R.card by omega)
  have ha_mul_gt_one : (1 : ℝ) < a * R.card := by
    have := (div_lt_iff₀ hR_pos).1 ha_lo
    linarith
  have htwo_a_le : 2 * a * R.card ≤ R.card := by nlinarith
  by_contra hnone
  push Not at hnone
  have hdichot : ∀ i : Fin l,
      ((B i ∩ R).card : ℝ) < a * R.card ∨ 2 * a * R.card ≤ ((B i ∩ R).card : ℝ) := by
    intro i
    by_cases hlt : i.val + 1 < l
    · by_cases h1 : a * R.card ≤ ((B i ∩ R).card : ℝ)
      · exact Or.inr (hnone i hlt h1)
      · exact Or.inl (lt_of_not_ge h1)
    · have hi : i = ⟨l - 1, Nat.sub_lt hl Nat.zero_lt_one⟩ :=
        Fin.ext (by dsimp only; omega)
      rw [hi, hlast, Finset.inter_eq_right.2 hRC]
      exact Or.inr htwo_a_le
  have hex : ∃ n : ℕ, ∃ hn : n < l, 2 * a * R.card ≤ ((B ⟨n, hn⟩ ∩ R).card : ℝ) := by
    refine ⟨l - 1, Nat.sub_lt hl Nat.zero_lt_one, ?_⟩
    rw [hlast, Finset.inter_eq_right.2 hRC]
    exact htwo_a_le
  classical
  let k := Nat.find hex
  obtain ⟨hk_lt, hk_ge⟩ := Nat.find_spec hex
  let ki : Fin l := ⟨k, hk_lt⟩
  have hk_min : ∀ j : Fin l, j < ki → ((B j ∩ R).card : ℝ) < a * R.card := by
    intro j hj
    rcases hdichot j with hlt | hge
    · exact hlt
    · exfalso
      exact Nat.find_min hex hj ⟨j.isLt, hge⟩
  rcases hstep ki with hempty | ⟨c, -, hsing⟩ | ⟨j₁, j₂, hj₁, hj₂, hunion⟩
  · have hzero : ((B ki ∩ R).card : ℝ) = 0 := by simp [hempty]
    linarith
  · have hle_one : ((B ki ∩ R).card : ℝ) ≤ 1 := by
      have : (B ki ∩ R).card ≤ 1 := by
        rw [hsing]
        exact (Finset.card_le_card Finset.inter_subset_left).trans (by simp)
      exact_mod_cast this
    linarith
  · have h1 := hk_min j₁ hj₁
    have h2 := hk_min j₂ hj₂
    have hcard : (B ki ∩ R).card ≤ (B j₁ ∩ R).card + (B j₂ ∩ R).card := by
      rw [hunion, Finset.union_inter_distrib_right]
      exact Finset.card_union_le _ _
    have hcard_r : ((B ki ∩ R).card : ℝ) ≤ ((B j₁ ∩ R).card : ℝ) + ((B j₂ ∩ R).card : ℝ) := by
      exact_mod_cast hcard
    linarith

end CslibFrontier.Logic.PL.OBDD
