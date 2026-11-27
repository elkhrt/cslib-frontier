/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Communication.Disjointness
public import CslibFrontier.Computability.Communication.Functions
import CslibFrontier.Computability.Communication.Amplification
import CslibFrontier.Computability.Communication.Corruption
import CslibFrontier.Foundations.Combinatorics.PowersetTail
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.ToReal
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Randomized Communication Lower Bound for Unique-Intersection Functions and `RNE`

Generalizes `Cslib.Communication.Disjointness` to prove an `Ω(n)` public-coin randomized
communication complexity lower bound for any Boolean function on `(2m + 1)`-bit strings that
agrees with disjointness (or its negation) on all pairs `(x, y)` with `|x ∩ y| ≤ 1`, and applies
it to the iterated 3-bit not-all-equal intersection function `RNE_{3^d}`.

## Main results

* `Cslib.Communication.PublicCoin.le_mul_ecomplexityFun_of_unique_disjoint`:
  `Ω(n)` public-coin lower bound for any function agreeing with `!disjointness` on unique
  intersections (`|x ∩ y| ≤ 1`).
* `Cslib.Communication.PublicCoin.le_mul_ecomplexityFun_rne`:
  `3^d ≤ 2^16 * R^{cc}_{1/3}(RNE_{3^d}) + 2^12`.
-/

public section

namespace Cslib.Communication

open Finset

/-- The iterated 3-bit not-all-equal function `NE^d : {0, 1}^{3^d} → {0, 1}`. -/
def iteratedNotAllEqual : (d : ℕ) → (Fin (3 ^ d) → Bool) → Bool
  | 0, x => x ⟨0, by norm_num⟩
  | d + 1, x =>
    let split (k : Fin 3) : Fin (3 ^ d) → Bool := fun j =>
      x ⟨k.1 * 3 ^ d + j.1, by
        have hk := k.isLt; have hj := j.isLt
        have h1 : k.1 * 3 ^ d + j.1 < (k.1 + 1) * 3 ^ d := by rw [add_mul, one_mul]; omega
        have h2 : (k.1 + 1) * 3 ^ d ≤ 3 * 3 ^ d := Nat.mul_le_mul_right _ (by omega)
        have hpow : 3 ^ (d + 1) = 3 * 3 ^ d := by rw [pow_succ, mul_comm]
        omega⟩
    let a := iteratedNotAllEqual d (split 0)
    let b := iteratedNotAllEqual d (split 1)
    let c := iteratedNotAllEqual d (split 2)
    decide (¬(a = b ∧ b = c))

/-- Exposed unique-intersection partition family for Razborov's hard distribution. -/
private def uParts (U : Type*) [DecidableEq U] [Fintype U] (m : ℕ) :
    Finset (Disjointness.Partition U) :=
  {T | T.point ∉ T.left ∧ T.point ∉ T.right ∧ Disjoint T.left T.right ∧
    #T.left = m ∧ #T.right = m}

private theorem mem_uParts {U : Type*} [DecidableEq U] [Fintype U] {m : ℕ}
    {T : Disjointness.Partition U} :
    T ∈ uParts U m ↔ T.point ∉ T.left ∧ T.point ∉ T.right ∧ Disjoint T.left T.right ∧
      #T.left = m ∧ #T.right = m := by
  simp only [uParts, mem_filter, mem_univ, true_and]

private theorem uCompl_insert {U : Type*} [DecidableEq U] [Fintype U] {m : ℕ}
    (hU : Fintype.card U = 2 * m + 1) {T : Disjointness.Partition U} (hT : T ∈ uParts U m) :
    (insert T.point T.right)ᶜ = T.left := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := mem_uParts.mp hT
  symm
  refine eq_of_subset_of_card_le (fun a ha => ?_) ?_
  · rw [mem_compl, mem_insert, not_or]
    exact ⟨fun h => h1 (h ▸ ha), fun h => disjoint_left.mp h3 ha h⟩
  · rw [card_compl, card_insert_of_notMem h2, hU, h4, h5]; omega

private theorem uSum_parts {U : Type*} [DecidableEq U] [Fintype U] {m : ℕ}
    (hU : Fintype.card U = 2 * m + 1) {M : Type*} [AddCommMonoid M]
    (F : Disjointness.Partition U → M) :
    ∑ T ∈ uParts U m, F T =
      ∑ Ty ∈ powersetCard m univ, ∑ i ∈ Tyᶜ, F ⟨i, (insert i Ty)ᶜ, Ty⟩ := by
  rw [sum_sigma']
  refine sum_nbij' (fun T => ⟨T.right, T.point⟩) (fun x => ⟨x.2, (insert x.2 x.1)ᶜ, x.1⟩)
    ?_ ?_ ?_ (fun _ _ => rfl) ?_
  · exact fun T hT =>
      let ⟨_, h2, _, _, h5⟩ := mem_uParts.mp hT
      mem_sigma.mpr ⟨mem_powersetCard.mpr ⟨subset_univ _, h5⟩, mem_compl.mpr h2⟩
  · rintro ⟨Ty, i⟩ hx
    have hTy := (mem_powersetCard.mp (mem_sigma.mp hx).1).2
    have hi := mem_compl.mp (mem_sigma.mp hx).2
    refine mem_uParts.mpr ⟨by simp, hi,
      disjoint_left.mpr fun _ ha haTy => mem_compl.mp ha (mem_insert_of_mem haTy), ?_, hTy⟩
    rw [card_compl, card_insert_of_notMem hi, hU, hTy]; omega
  · intro T hT; ext <;> simp only [uCompl_insert hU hT]
  · intro T hT; simp only [uCompl_insert hU hT]

private theorem uSum_parts_swap {U : Type*} [DecidableEq U] [Fintype U] {m : ℕ}
    {M : Type*} [AddCommMonoid M] (F : Disjointness.Partition U → M) :
    ∑ T ∈ uParts U m, F T = ∑ T ∈ uParts U m, F ⟨T.point, T.right, T.left⟩ := by
  refine sum_nbij' (fun T => ⟨T.point, T.right, T.left⟩) (fun T => ⟨T.point, T.right, T.left⟩)
    ?_ ?_ (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) <;>
  · intro T hT
    obtain ⟨h1, h2, h3, h4, h5⟩ := mem_uParts.mp hT
    exact mem_uParts.mpr ⟨h2, h1, h3.symm, h5, h4⟩

private theorem uCard_parts {U : Type*} [DecidableEq U] [Fintype U] {m : ℕ}
    (hU : Fintype.card U = 2 * m + 1) :
    #(uParts U m) = #(powersetCard m (univ : Finset U)) * (m + 1) := by
  rw [card_eq_sum_ones, uSum_parts hU]
  simp only [sum_const, smul_eq_mul, mul_one]
  rw [sum_congr rfl fun Ty hTy => by rw [card_compl, hU, (mem_powersetCard.mp hTy).2],
    sum_const, smul_eq_mul]
  exact congrArg (_ * ·) (by omega)

private theorem uCard_parts_pos {U : Type*} [DecidableEq U] [Fintype U] {m : ℕ}
    (hU : Fintype.card U = 2 * m + 1) : 0 < #(uParts U m) := by
  rw [uCard_parts hU, card_powersetCard, card_univ, hU]
  exact Nat.mul_pos (Nat.choose_pos (by omega)) (Nat.succ_pos m)

private noncomputable def uHardWeight {U : Type*} [DecidableEq U] [Fintype U] (m : ℕ) :
    Finset U × Finset U → ℝ
  | (x, y) =>
    (∑ T ∈ uParts U m,
      ((if x ⊆ T.left then 1 else 0) * (if y ⊆ T.right then 1 else 0) +
        (if T.point ∈ x ∧ x ⊆ T.rightᶜ then 1 else 0) *
          (if T.point ∈ y ∧ y ⊆ T.leftᶜ then 1 else 0))) /
      (2 * #(uParts U m) * 4 ^ m)

private theorem uHardWeight_nonneg {U : Type*} [DecidableEq U] [Fintype U] {m : ℕ}
    (q : Finset U × Finset U) : 0 ≤ uHardWeight m q := by
  rcases q with ⟨x, y⟩
  unfold uHardWeight
  refine div_nonneg (sum_nonneg fun _ _ => ?_) (by positivity)
  split_ifs <;> norm_num

private theorem uSum_hardWeight_split {U : Type*} [DecidableEq U] [Fintype U] {m : ℕ}
    (hU : Fintype.card U = 2 * m + 1) :
    (∑ x : Finset U, ∑ y : Finset U,
      (if decide (Disjoint x y) = true then uHardWeight m (x, y) else 0)) = 1 / 2 ∧
    (∑ x : Finset U, ∑ y : Finset U,
      (if decide (Disjoint x y) = true then 0 else uHardWeight m (x, y))) = 1 / 2 ∧
    ∀ (A B : Finset (Finset U)) {r : ℕ}, 48 * r ≤ m + 1 →
      (1 / 18 : ℝ) * (∑ x ∈ A, ∑ y ∈ B,
          (if decide (Disjoint x y) = true then uHardWeight m (x, y) else 0)) ≤
        (∑ x ∈ A, ∑ y ∈ B,
          (if decide (Disjoint x y) = true then 0 else uHardWeight m (x, y))) +
        (27 / 32 : ℝ) ^ r / 2 := by
  let low (A : Finset (Finset U)) (s : Finset U) : ℕ := #{x ∈ A | x ⊆ s}
  let high (A : Finset (Finset U)) (i : U) (s : Finset U) : ℕ := #{x ∈ A | i ∈ x ∧ x ⊆ sᶜ}
  have hite : ∀ x y : Finset U,
      (if decide (Disjoint x y) = true then uHardWeight m (x, y) else 0) =
        (∑ T ∈ uParts U m,
          (if x ⊆ T.left then (1 : ℝ) else 0) * (if y ⊆ T.right then 1 else 0)) /
          (2 * #(uParts U m) * 4 ^ m) ∧
      (if decide (Disjoint x y) = true then 0 else uHardWeight m (x, y)) =
        (∑ T ∈ uParts U m,
          (if T.point ∈ x ∧ x ⊆ T.rightᶜ then (1 : ℝ) else 0) *
            (if T.point ∈ y ∧ y ⊆ T.leftᶜ then 1 else 0)) /
          (2 * #(uParts U m) * 4 ^ m) := by
    intro x y; unfold uHardWeight
    by_cases h : Disjoint x y
    · have hz (T : Disjointness.Partition U) :
          (if T.point ∈ x ∧ x ⊆ T.rightᶜ then (1 : ℝ) else 0) *
            (if T.point ∈ y ∧ y ⊆ T.leftᶜ then 1 else 0) = 0 := by
        split_ifs with h1 h2
        · exact absurd h2.1 (disjoint_left.mp h h1.1)
        all_goals norm_num
      simp only [h, decide_true, ↓reduceIte, hz, add_zero, sum_const_zero, zero_div, and_self]
    · have hz {T : Disjointness.Partition U} (hT : T ∈ uParts U m) :
          (if x ⊆ T.left then (1 : ℝ) else 0) * (if y ⊆ T.right then 1 else 0) = 0 := by
        split_ifs with h1 h2
        · exact absurd ((mem_uParts.mp hT).2.2.1.mono h1 h2) h
        all_goals norm_num
      simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte]
      exact ⟨(div_eq_zero_iff.mpr (.inl (sum_eq_zero fun T hT => hz hT))).symm,
        congrArg (· / _) (sum_congr rfl fun T hT => by rw [hz hT, zero_add])⟩
  have hrect : ∀ (A B : Finset (Finset U)) (p q : Disjointness.Partition U → Finset U → Prop)
      [∀ T x, Decidable (p T x)] [∀ T y, Decidable (q T y)] (D : ℝ),
      ∑ x ∈ A, ∑ y ∈ B, (∑ T ∈ uParts U m,
          (if p T x then (1 : ℝ) else 0) * (if q T y then 1 else 0)) / D =
        (∑ T ∈ uParts U m, (#{x ∈ A | p T x} : ℝ) * #{y ∈ B | q T y}) / D := by
    intro A B p q _ _ D
    simp only [← sum_div]; congr 1
    calc ∑ x ∈ A, ∑ y ∈ B, ∑ T ∈ uParts U m,
          (if p T x then (1 : ℝ) else 0) * (if q T y then 1 else 0)
        = ∑ x ∈ A, ∑ T ∈ uParts U m, ∑ y ∈ B,
            (if p T x then (1 : ℝ) else 0) * (if q T y then 1 else 0) :=
          sum_congr rfl fun _ _ => sum_comm
      _ = ∑ T ∈ uParts U m, ∑ x ∈ A, ∑ y ∈ B,
            (if p T x then (1 : ℝ) else 0) * (if q T y then 1 else 0) := sum_comm
      _ = _ := sum_congr rfl fun T _ => by rw [← sum_mul_sum, sum_boole, sum_boole]
  have hsum1 : ∀ A B : Finset (Finset U),
      ∑ x ∈ A, ∑ y ∈ B, (if decide (Disjoint x y) = true then uHardWeight m (x, y) else 0) =
        (∑ T ∈ uParts U m, ((low A T.left : ℝ) * low B T.right)) /
          (2 * #(uParts U m) * 4 ^ m) := fun A B => by
    simp only [fun x y => (hite x y).1]; exact hrect A B _ _ _
  have hsum2 : ∀ A B : Finset (Finset U),
      ∑ x ∈ A, ∑ y ∈ B, (if decide (Disjoint x y) = true then 0 else uHardWeight m (x, y)) =
        (∑ T ∈ uParts U m, ((high A T.point T.right : ℝ) * high B T.point T.left)) /
          (2 * #(uParts U m) * 4 ^ m) := fun A B => by
    simp only [fun x y => (hite x y).2]; exact hrect A B _ _ _
  have hP : (0 : ℝ) < #(uParts U m) := by exact_mod_cast uCard_parts_pos hU
  have h4m : (2 ^ m : ℝ) * 2 ^ m = 4 ^ m := by rw [← mul_pow]; norm_num
  have hlow_univ : ∀ s : Finset U, low univ s = 2 ^ #s := fun s => by
    change #{x ∈ (univ : Finset (Finset U)) | x ⊆ s} = 2 ^ #s
    rw [← card_powerset]
    exact congrArg card (ext fun _ => by simp only [mem_filter, mem_univ, true_and, mem_powerset])
  have hhigh_univ : ∀ {i : U} {s : Finset U}, i ∉ s → high univ i s = 2 ^ (#sᶜ - 1) := by
    intro i s hi
    change #{x ∈ (univ : Finset (Finset U)) | i ∈ x ∧ x ⊆ sᶜ} = 2 ^ (#sᶜ - 1)
    have hi' : i ∈ sᶜ := mem_compl.mpr hi
    have h1 : #{x ∈ (univ : Finset (Finset U)) | i ∈ x ∧ x ⊆ sᶜ} = #{x ∈ sᶜ.powerset | i ∈ x} :=
      congrArg card (ext fun _ => by simp only [mem_filter, mem_univ, true_and, mem_powerset,
        and_comm])
    have h2 : {x ∈ sᶜ.powerset | i ∉ x} = (sᶜ.erase i).powerset :=
      ext fun _ => by simp only [mem_filter, mem_powerset, subset_erase]
    have h3 := (card_filter_add_card_filter_not (s := sᶜ.powerset) fun x => i ∈ x).trans
      (card_powerset sᶜ)
    have h5 : 2 ^ #sᶜ = 2 ^ (#sᶜ - 1) * 2 := by
      rw [← pow_succ, Nat.sub_add_cancel (card_pos.mpr ⟨i, hi'⟩)]
    rw [h2, card_powerset, card_erase_of_mem hi', h5] at h3
    rw [h1]; omega
  have hcompl : ∀ {s : Finset U}, #s = m → #sᶜ - 1 = m := fun {s} h => by
    simp only [card_compl, hU, h]; omega
  refine ⟨?_, ?_, ?_⟩
  · rw [hsum1, sum_congr rfl fun T hT => by
      rw [hlow_univ, hlow_univ, (mem_uParts.mp hT).2.2.2.1, (mem_uParts.mp hT).2.2.2.2,
        Nat.cast_pow, Nat.cast_ofNat, h4m], sum_const, nsmul_eq_mul]
    field_simp
  · rw [hsum2, sum_congr rfl fun T hT => by
      obtain ⟨h1, h2, -, h4, h5⟩ := mem_uParts.mp hT
      rw [hhigh_univ h2, hhigh_univ h1, hcompl h4, hcompl h5, Nat.cast_pow, Nat.cast_ofNat, h4m],
      sum_const, nsmul_eq_mul]
    field_simp
  · intro A B r hr
    have hside : ∀ (X Y : Finset (Finset U)),
        4 * ∑ T ∈ uParts U m with 3 * high X T.point T.right < low X T.left,
            ((low X T.left : ℝ) * low Y T.right) ≤
          ∑ T ∈ uParts U m, ((low X T.left : ℝ) * low Y T.right) +
            18 * #(uParts U m) * 4 ^ m * (27 / 32) ^ r := by
      intro X Y
      rw [sum_filter, uSum_parts hU, uSum_parts hU, uCard_parts hU, mul_sum]
      have hconst : (18 : ℝ) * ((#(powersetCard m (univ : Finset U)) * (m + 1) : ℕ) : ℝ) *
          4 ^ m * (27 / 32) ^ r = ∑ _Ty ∈ powersetCard m (univ : Finset U),
            18 * ((m : ℝ) + 1) * 4 ^ m * (27 / 32) ^ r := by
        rw [sum_const, nsmul_eq_mul]; push_cast; ring
      rw [hconst, ← sum_add_distrib]
      refine sum_le_sum fun Ty hTy => ?_
      have hTy : #Ty = m := (mem_powersetCard.mp hTy).2
      have hS : #Tyᶜ = m + 1 := by simp only [card_compl, hU, hTy]; omega
      have hb : (low Y Ty : ℝ) ≤ 2 ^ m := by
        have hle : low Y Ty ≤ 2 ^ #Ty := by
          rw [← card_powerset]
          exact card_le_card fun x hx => mem_powerset.mpr (mem_filter.mp hx).2
        exact_mod_cast hTy ▸ hle
      have hKL := four_mul_sum_card_filter_notMem_le X Tyᶜ (r := r) (j := 12 * r) (by omega)
      rw [hS] at hKL
      push_cast at hKL
      have hlow_ci : ∀ i : U, low X (insert i Ty)ᶜ = #{x ∈ X | x ⊆ Tyᶜ ∧ i ∉ x} := fun i => by
        dsimp only [low]; congr 1; refine filter_congr fun x _ => ?_
        simp only [subset_iff, mem_compl, mem_insert, not_or]
        exact ⟨fun h => ⟨fun a ha => (h ha).2, fun hi => (h hi).1 rfl⟩,
          fun h a ha => ⟨fun hai => h.2 (hai ▸ ha), h.1 ha⟩⟩
      simp only [hlow_ci, high]
      rw [← sum_filter, ← sum_mul, ← sum_mul]
      have hb0 : (0 : ℝ) ≤ low Y Ty := Nat.cast_nonneg _
      have hsl : 8 * ((m : ℝ) + 1) * (27 / 32 : ℝ) ^ r +
          (12 * (r : ℝ) + 1) * 2 ^ (12 * r) * (3 / 4) ^ (m + 1) ≤
          9 * ((m : ℝ) + 1) * (27 / 32) ^ r := by
        have h1 : (12 * (r : ℝ) + 1) ≤ (m : ℝ) + 1 := by
          exact_mod_cast (by omega : 12 * r + 1 ≤ m + 1)
        have h2 : (3 / 4 : ℝ) ^ (m + 1) ≤ (3 / 4) ^ (48 * r) :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) hr
        have h3 : (2 : ℝ) ^ (12 * r) * (3 / 4) ^ (48 * r) ≤ (27 / 32) ^ r := by
          rw [pow_mul, pow_mul, ← mul_pow]
          exact pow_le_pow_left₀ (by positivity) (by norm_num) r
        have h4 : (12 * (r : ℝ) + 1) * 2 ^ (12 * r) * (3 / 4) ^ (m + 1) ≤
            ((m : ℝ) + 1) * (27 / 32) ^ r :=
          calc (12 * (r : ℝ) + 1) * 2 ^ (12 * r) * (3 / 4) ^ (m + 1)
              ≤ ((m : ℝ) + 1) * (2 ^ (12 * r) * (3 / 4) ^ (48 * r)) := by rw [mul_assoc]; gcongr
            _ ≤ ((m : ℝ) + 1) * (27 / 32) ^ r := mul_le_mul_of_nonneg_left h3 (by positivity)
        linarith
      have hsc : (2 : ℝ) ^ (m + 1) * (8 * ((m : ℝ) + 1) * (27 / 32) ^ r +
          (12 * (r : ℝ) + 1) * 2 ^ (12 * r) * (3 / 4) ^ (m + 1)) * (low Y Ty : ℝ) ≤
          18 * ((m : ℝ) + 1) * 4 ^ m * (27 / 32) ^ r := by
        have hrhs : 18 * ((m : ℝ) + 1) * 4 ^ m * (27 / 32) ^ r =
            2 ^ (m + 1) * (9 * ((m : ℝ) + 1) * (27 / 32) ^ r) * 2 ^ m := by
          rw [pow_succ, ← h4m]; ring
        rw [hrhs]; gcongr
      linarith [mul_le_mul_of_nonneg_right hKL hb0]
    have hX := hside A B
    have hY := hside B A
    rw [sum_filter] at hX hY
    rw [uSum_parts_swap, uSum_parts_swap (fun T => (low B T.left : ℝ) * low A T.right)] at hY
    have hpt : ∀ T ∈ uParts U m, (low A T.left : ℝ) * low B T.right ≤
        9 * ((high A T.point T.right : ℝ) * high B T.point T.left) +
          ((if 3 * high A T.point T.right < low A T.left then (low A T.left : ℝ) * low B T.right
            else 0) +
           (if 3 * high B T.point T.left < low B T.right then (low B T.right : ℝ) * low A T.left
            else 0)) := by
      intro T _
      have h0 : (0 : ℝ) ≤ (low A T.left : ℝ) * low B T.right := by positivity
      have h0' : (0 : ℝ) ≤ (high A T.point T.right : ℝ) * high B T.point T.left := by positivity
      by_cases hx : 3 * high A T.point T.right < low A T.left <;>
        by_cases hy : 3 * high B T.point T.left < low B T.right <;>
        simp only [hx, hy, ↓reduceIte, add_zero]
      · nlinarith
      · linarith
      · nlinarith
      · push Not at hx hy
        have hx' : (low A T.left : ℝ) ≤ 3 * high A T.point T.right := by exact_mod_cast hx
        have hy' : (low B T.right : ℝ) ≤ 3 * high B T.point T.left := by exact_mod_cast hy
        have := mul_le_mul hx' hy' (Nat.cast_nonneg _) (by positivity)
        linarith
    have htot := sum_le_sum hpt
    rw [sum_add_distrib, sum_add_distrib, ← mul_sum] at htot
    rw [sum_congr rfl fun _ _ => mul_comm _ _] at hY
    have hcomb : ∑ T ∈ uParts U m, ((low A T.left : ℝ) * low B T.right) ≤
        18 * ∑ T ∈ uParts U m, ((high A T.point T.right : ℝ) * high B T.point T.left) +
          18 * #(uParts U m) * 4 ^ m * (27 / 32) ^ r := by linarith
    rw [hsum1, hsum2]
    have hdiv := div_le_div_of_nonneg_right hcomb
      (by positivity : (0 : ℝ) ≤ 2 * #(uParts U m) * 4 ^ m)
    have hcancel : (18 * #(uParts U m) * 4 ^ m * (27 / 32) ^ r : ℝ) /
        (2 * #(uParts U m) * 4 ^ m) = 9 * (27 / 32) ^ r := by field_simp; ring
    rw [add_div, mul_div_assoc, hcancel] at hdiv
    linarith

private noncomputable def uHardDist {U : Type*} [DecidableEq U] [Fintype U] (m : ℕ)
    (hU : Fintype.card U = 2 * m + 1) : PMF (Finset U × Finset U) :=
  PMF.ofFintype (fun q => ENNReal.ofReal (uHardWeight m q)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg fun q _ => uHardWeight_nonneg q, Fintype.sum_prod_type]
    obtain ⟨h1, h2, -⟩ := uSum_hardWeight_split hU
    have hsum : ∑ x : Finset U, ∑ y : Finset U, uHardWeight m (x, y) = 1 := by
      calc ∑ x : Finset U, ∑ y : Finset U, uHardWeight m (x, y)
          = ∑ x : Finset U, ∑ y : Finset U,
              ((if decide (Disjoint x y) = true then uHardWeight m (x, y) else 0) +
               (if decide (Disjoint x y) = true then 0 else uHardWeight m (x, y))) :=
            sum_congr rfl fun x _ => sum_congr rfl fun y _ => by split_ifs <;> simp
        _ = 1 := by simp only [sum_add_distrib, h1, h2]; norm_num
    rw [hsum, ENNReal.ofReal_one])

/-- Public-coin communication lower bound for any function `f` on `2m + 1` bits that agrees with
`!disjointness` on all pairs `(x, y)` with `|x ∩ y| ≤ 1` (i.e. `x ∩ y = ∅` or `x ∩ y = {i}`). -/
theorem PublicCoin.le_mul_ecomplexityFun_of_unique_disjoint {m : ℕ}
    (f : BitString (2 * m + 1) → BitString (2 * m + 1) → Bool)
    (hzero : ∀ x y : BitString (2 * m + 1), (∀ i, (x i && y i) = false) → f x y = false)
    (hone : ∀ (x y : BitString (2 * m + 1)) (i₀ : Fin (2 * m + 1)),
      (∀ i, (x i && y i) = decide (i = i₀)) → f x y = true) :
    ((2 * m + 1 : ℕ) : ℕ∞) ≤ 2 ^ 16 * PublicCoin.ecomplexityFun (1 / 3) f + 2 ^ 12 := by
  have hU : Fintype.card (Fin (2 * m + 1)) = 2 * m + 1 := Fintype.card_fin (2 * m + 1)
  let ind : Finset (Fin (2 * m + 1)) → BitString (2 * m + 1) := fun s i => decide (i ∈ s)
  have hagree : ∀ (x y : Finset (Fin (2 * m + 1))),
      uHardWeight m (x, y) ≠ 0 →
      ((!f (ind x) (ind y)) = true ↔ Disjoint x y) := by
    intro x y hne
    by_cases hdisj : Disjoint x y
    · have hz : ∀ i, (ind x i && ind y i) = false := fun i => by
        simp only [ind, Bool.and_eq_false_iff, decide_eq_false_iff_not]
        by_cases hi : i ∈ x
        · exact Or.inr (Finset.disjoint_left.mp hdisj hi)
        · exact Or.inl hi
      simp [hzero (ind x) (ind y) hz, hdisj]
    · have hex : ∃ T ∈ uParts (Fin (2 * m + 1)) m,
          T.point ∈ x ∧ x ⊆ T.rightᶜ ∧ T.point ∈ y ∧ y ⊆ T.leftᶜ := by
        by_contra hall; push Not at hall; apply hne
        unfold uHardWeight
        refine div_eq_zero_iff.mpr (Or.inl (Finset.sum_eq_zero fun T hT => ?_))
        have h1 : (if x ⊆ T.left then (1 : ℝ) else 0) * (if y ⊆ T.right then 1 else 0) = 0 := by
          split_ifs with hx hy
          · exact absurd ((mem_uParts.mp hT).2.2.1.mono hx hy) hdisj
          all_goals norm_num
        have h2 : (if T.point ∈ x ∧ x ⊆ T.rightᶜ then (1 : ℝ) else 0) *
            (if T.point ∈ y ∧ y ⊆ T.leftᶜ then 1 else 0) = 0 := by
          split_ifs with hx hy
          · exact absurd hy.2 (hall T hT hx.1 hx.2 hy.1)
          all_goals norm_num
        linarith
      obtain ⟨T, hT, hpx, hxsub, hpy, hysub⟩ := hex
      have hcompl := uCompl_insert hU hT
      have hu : ∀ i, (ind x i && ind y i) = decide (i = T.point) := fun i => by
        dsimp only [ind]
        rw [← Bool.decide_and, decide_eq_decide]
        constructor
        · rintro ⟨hix, hiy⟩
          have hnr : i ∉ T.right := Finset.mem_compl.mp (hxsub hix)
          have hnl : i ∉ T.left := Finset.mem_compl.mp (hysub hiy)
          rw [← hcompl, Finset.mem_compl, not_not, Finset.mem_insert] at hnl
          exact hnl.resolve_right hnr
        · intro heq; subst heq; exact ⟨hpx, hpy⟩
      simp [hone (ind x) (ind y) T.point hu, hdisj]
  obtain ⟨hsplit1, -, hsplit3⟩ := uSum_hardWeight_split hU
  have hwt : ∀ q, (uHardDist m hU q).toReal = uHardWeight m q := fun q => by
    rw [uHardDist, PMF.ofFintype_apply, ENNReal.toReal_ofReal (uHardWeight_nonneg q)]
  -- Transfer corruption and mass from `uHardDist`.
  have h164 : (((m + 1) / 48 : ℕ) : ℕ∞) ≤
      5 * PublicCoin.ecomplexityFun (1 / 64) (fun x y => !f (ind x) (ind y)) + 29 := by
    cases h : PublicCoin.ecomplexityFun (1 / 64) (fun x y => !f (ind x) (ind y))
      using ENat.recTopCoe with
    | top => simp
    | coe c =>
      set r := (m + 1) / 48
      have hr : 48 * r ≤ m + 1 := Nat.mul_div_le (m + 1) 48
      have hcorr : Corrupted (uHardDist m hU) (fun x y => !f (ind x) (ind y))
          true (1 / 18) ((27 / 32) ^ r / 2) := by
        intro A B
        have hc := hsplit3 A B hr
        have h1 : ∑ x ∈ A, ∑ y ∈ B,
              (if (!f (ind x) (ind y)) = true then (uHardDist m hU (x, y)).toReal else 0) =
            ∑ x ∈ A, ∑ y ∈ B,
              (if decide (Disjoint x y) = true then uHardWeight m (x, y) else 0) :=
          Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by
            rw [hwt]
            by_cases h0 : uHardWeight m (x, y) = 0
            · simp [h0]
            · by_cases hd : Disjoint x y <;> simp [hagree x y h0, hd]
        have h2 : ∑ x ∈ A, ∑ y ∈ B,
              (if (!f (ind x) (ind y)) = true then 0 else (uHardDist m hU (x, y)).toReal) =
            ∑ x ∈ A, ∑ y ∈ B,
              (if decide (Disjoint x y) = true then 0 else uHardWeight m (x, y)) :=
          Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by
            rw [hwt]
            by_cases h0 : uHardWeight m (x, y) = 0
            · simp [h0]
            · by_cases hd : Disjoint x y <;> simp [hagree x y h0, hd]
        rw [h1, h2]; exact hc
      have hmass : ((uHardDist m hU).toOuterMeasure
          {q | (!f (ind q.1) (ind q.2)) = true}).toReal = 1 / 2 := by
        rw [Cslib.Probability.PMF.toOuterMeasure_apply_toReal, Fintype.sum_prod_type, ← hsplit1]
        refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
        rw [Set.mem_ofPred_eq, hwt]
        by_cases h0 : uHardWeight m (x, y) = 0
        · simp [h0]
        · by_cases hd : Disjoint x y <;> simp [hagree x y h0, hd]
      have hbound := hcorr.mul_sub_le_of_ecomplexityFun_le (by norm_num) h.le
      rw [hmass] at hbound
      have hreal : (13 : ℝ) * 32 ^ r ≤ 576 * 2 ^ c * 27 ^ r := by
        have h13 : (13 : ℝ) / 1152 ≤ 2 ^ c * ((27 / 32) ^ r / 2) := by linarith
        rw [div_pow, ← mul_div_assoc, ← mul_div_assoc, div_div,
          le_div_iff₀ (by positivity)] at h13
        linarith
      have hnat : 13 * 32 ^ r ≤ 576 * 2 ^ c * 27 ^ r := by exact_mod_cast hreal
      set q := r / 5; set t := r % 5
      have hr5 : r = 5 * q + t := (Nat.div_add_mod r 5).symm
      have h1 : 2 ^ q * 27 ^ (5 * q) ≤ 32 ^ (5 * q) := by
        rw [pow_mul, pow_mul, ← mul_pow]; exact Nat.pow_le_pow_left (by norm_num) q
      have h2 : 27 ^ t ≤ 32 ^ t := Nat.pow_le_pow_left (by norm_num) t
      have h3 : 13 * 2 ^ q * 27 ^ r ≤ 576 * 2 ^ c * 27 ^ r :=
        calc 13 * 2 ^ q * 27 ^ r = 13 * (2 ^ q * 27 ^ (5 * q)) * 27 ^ t := by
              rw [hr5, pow_add]; ring
          _ ≤ 13 * 32 ^ (5 * q) * 32 ^ t := by gcongr
          _ = 13 * 32 ^ r := by rw [hr5, pow_add]; ring
          _ ≤ 576 * 2 ^ c * 27 ^ r := hnat
      have h4 : 13 * 2 ^ q ≤ 576 * 2 ^ c := Nat.le_of_mul_le_mul_right h3 (by positivity)
      have h5 : q < c + 6 := by
        by_contra hq
        have h6 : 2 ^ c * 2 ^ 6 ≤ 2 ^ q := by
          rw [← pow_add]; exact Nat.pow_le_pow_right two_pos (by omega)
        have : 0 < 2 ^ c := by positivity
        omega
      exact_mod_cast (by omega : r ≤ 5 * c + 29)
  have hneg : PublicCoin.ecomplexityFun (1 / 3) (fun x y => !f x y) ≤
      PublicCoin.ecomplexityFun (1 / 3) f := by
    simp only [PublicCoin.ecomplexityFun, PublicCoin.ecomplexity, le_iInf_iff]
    rintro ⟨μ, hμ⟩
    let μ' : PublicCoin (BitString (2 * m + 1)) (BitString (2 * m + 1)) Bool :=
      μ.map (Protocol.map Bool.not)
    have hsol' : μ'.Solves (1 / 3) (fun x y z => (!f x y) = z) Set.univ Set.univ := by
      intro x _ y _
      have h1 := hμ x (Set.mem_univ _) y (Set.mem_univ _)
      simp only [PublicCoin.errorProb, Cslib.Probability.PMF.errorProb, μ',
        PMF.toOuterMeasure_map_apply] at h1 ⊢
      have heq : Protocol.map Bool.not ⁻¹' {p | ¬(!f x y) = p.run x y} =
          {p | ¬f x y = p.run x y} := by
        ext p
        simp only [Set.mem_preimage, Set.mem_ofPred_eq, Protocol.run_map]
        cases f x y <;> cases p.run x y <;> decide
      rw [heq]; exact h1
    have hd' : μ'.depth ≤ μ.depth := by
      rw [PublicCoin.depth_le_iff]; intro p hp
      simp only [μ', PMF.mem_support_map_iff] at hp
      obtain ⟨q, hq, rfl⟩ := hp
      simpa [Protocol.depth_map] using PublicCoin.depth_le_iff.mp le_rfl q hq
    exact (PublicCoin.ecomplexity_le_depth hsol').trans (by exact_mod_cast hd')
  have hcomap : PublicCoin.ecomplexityFun (1 / 64) (fun x y => !f (ind x) (ind y)) ≤
      PublicCoin.ecomplexityFun (1 / 64) (fun x y => !f x y) :=
    PublicCoin.ecomplexityFun_comap_le (fun x y => !f x y) ind ind
  have hanti : PublicCoin.ecomplexityFun (1 / 64) (fun x y => !f x y) ≤
      PublicCoin.ecomplexityFun ((8 / 9 : ℝ) ^ 36) (fun x y => !f x y) :=
    PublicCoin.ecomplexity_anti (by
      have h6 : (8 / 9 : ℝ) ^ 6 ≤ 1 / 2 := by norm_num
      calc (8 / 9 : ℝ) ^ 36 = ((8 / 9 : ℝ) ^ 6) ^ 6 := by rw [← pow_mul]
        _ ≤ (1 / 2 : ℝ) ^ 6 := pow_le_pow_left₀ (by positivity) h6 6
        _ = 1 / 64 := by norm_num)
  have hamp : PublicCoin.ecomplexityFun ((8 / 9 : ℝ) ^ 36) (fun x y => !f x y) ≤
      2 * (36 : ℕ) * PublicCoin.ecomplexityFun (1 / 3) (fun x y => !f x y) :=
    PublicCoin.ecomplexityFun_le_two_mul_mul_one_third 36
  have h13 : PublicCoin.ecomplexityFun (1 / 64) (fun x y => !f (ind x) (ind y)) ≤
      2 * (36 : ℕ) * PublicCoin.ecomplexityFun (1 / 3) f :=
    calc PublicCoin.ecomplexityFun (1 / 64) (fun x y => !f (ind x) (ind y))
        ≤ 2 * (36 : ℕ) * PublicCoin.ecomplexityFun (1 / 3) (fun x y => !f x y) :=
          le_trans hcomap (le_trans hanti hamp)
      _ ≤ 2 * (36 : ℕ) * PublicCoin.ecomplexityFun (1 / 3) f := by gcongr
  have hchain : (((m + 1) / 48 : ℕ) : ℕ∞) ≤
      5 * (2 * (36 : ℕ) * PublicCoin.ecomplexityFun (1 / 3) f) + 29 :=
    calc (((m + 1) / 48 : ℕ) : ℕ∞)
        ≤ 5 * PublicCoin.ecomplexityFun (1 / 64) (fun x y => !f (ind x) (ind y)) + 29 := h164
      _ ≤ 5 * (2 * (36 : ℕ) * PublicCoin.ecomplexityFun (1 / 3) f) + 29 := by gcongr
  generalize hR : PublicCoin.ecomplexityFun (1 / 3) f = R at hchain ⊢
  induction R using ENat.recTopCoe with
  | top =>
    have h216 : (2 ^ 16 : ℕ∞) ≠ 0 := pow_ne_zero 16 (by norm_num)
    rw [ENat.mul_top h216, _root_.top_add]
    exact le_top
  | coe c =>
    have hcast_rhs : (5 : ℕ∞) * (2 * (36 : ℕ) * (c : ℕ∞)) + 29 =
        ((5 * (2 * 36 * c) + 29 : ℕ) : ℕ∞) := by
      simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    rw [hcast_rhs] at hchain
    have hnat : (m + 1) / 48 ≤ 5 * (2 * 36 * c) + 29 := Nat.cast_le (α := ℕ∞).mp hchain
    have hdiv : 48 * ((m + 1) / 48) + (m + 1) % 48 = m + 1 := Nat.div_add_mod (m + 1) 48
    have hmod : (m + 1) % 48 < 48 := Nat.mod_lt (m + 1) (by norm_num)
    have hstep : 2 * m + 1 ≤ 2 ^ 16 * c + 2 ^ 12 := by
      have hm1 : m + 1 ≤ 48 * (5 * (2 * 36 * c) + 29) + 47 := by linarith
      linarith
    have hcast : ((2 * m + 1 : ℕ) : ℕ∞) ≤ ((2 ^ 16 * c + 2 ^ 12 : ℕ) : ℕ∞) := Nat.cast_le.mpr hstep
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using hcast

/-- Public-coin communication lower bound for `RNE_{3^d}`:
`3^d ≤ 2^16 * R^{cc}_{1/3}(RNE_{3^d}) + 2^12`. -/
theorem PublicCoin.le_mul_ecomplexityFun_rne (d : ℕ) :
    ((3 ^ d : ℕ) : ℕ∞) ≤
      2 ^ 16 * PublicCoin.ecomplexityFun (1 / 3)
        (fun x y : BitString (3 ^ d) => iteratedNotAllEqual d (fun i => x i && y i)) + 2 ^ 12 := by
  have hodd : Odd (3 ^ d) := Odd.pow ⟨1, rfl⟩
  set m := (3 ^ d - 1) / 2
  have h2m1 : 2 * m + 1 = 3 ^ d := by obtain ⟨k, hk⟩ := hodd; omega
  have hzero : ∀ d', iteratedNotAllEqual d' (fun _ => false) = false := by
    intro d'; induction d' with
    | zero => rfl
    | succ d' ih => simp [iteratedNotAllEqual, ih]
  have hmarked : ∀ (d' : ℕ) (i₀ : Fin (3 ^ d')),
      iteratedNotAllEqual d' (fun i => decide (i = i₀)) = true := by
    intro d'; induction d' with
    | zero =>
      intro i₀
      have h0 : i₀ = ⟨0, by norm_num⟩ := by ext; omega
      subst h0; simp [iteratedNotAllEqual]
    | succ d' ih =>
      intro i₀
      have hpow : 0 < 3 ^ d' := by positivity
      set q := i₀.1 / 3 ^ d'; set r := i₀.1 % 3 ^ d'
      have hq : q < 3 := by
        have hi : i₀.1 < 3 ^ d' * 3 := by simpa [pow_succ] using i₀.isLt
        exact Nat.div_lt_of_lt_mul hi
      have hr : r < 3 ^ d' := Nat.mod_lt _ hpow
      have hi_eq : i₀.1 = q * 3 ^ d' + r := by
        have := (Nat.div_add_mod i₀.1 (3 ^ d')).symm
        rw [mul_comm] at this; exact this
      simp only [iteratedNotAllEqual, decide_eq_true_eq]
      have hbl : ∀ k : Fin 3,
          (fun j : Fin (3 ^ d') => decide ((⟨k.1 * 3 ^ d' + j.1, by
            have hk := k.isLt; have hj := j.isLt
            have h1 : k.1 * 3 ^ d' + j.1 < (k.1 + 1) * 3 ^ d' := by rw [add_mul, one_mul]; omega
            have h2 : (k.1 + 1) * 3 ^ d' ≤ 3 * 3 ^ d' := Nat.mul_le_mul_right _ (by omega)
            have hp : 3 ^ (d' + 1) = 3 * 3 ^ d' := by rw [pow_succ, mul_comm]
            omega⟩ : Fin (3 ^ (d' + 1))) = i₀)) =
          if k.1 = q then (fun j => decide (j = ⟨r, hr⟩)) else (fun _ => false) := by
        intro k; split_ifs with hk
        · funext j; simp only [Fin.ext_iff, decide_eq_decide]
          rw [hk, hi_eq]; constructor <;> intro h <;> omega
        · funext j; simp only [Fin.ext_iff, decide_eq_false_iff_not]; intro h
          have hdiv : (k.1 * 3 ^ d' + j.1) / 3 ^ d' = k.1 := by
            rw [Nat.add_comm, Nat.add_mul_div_right _ _ hpow, Nat.div_eq_of_lt j.isLt, zero_add]
          exact hk (by rw [← hdiv, h])
      rw [hbl 0, hbl 1, hbl 2]
      match q, hq with
      | 0, _ => simp [ih, hzero]
      | 1, _ => simp [ih, hzero]
      | 2, _ => simp [ih, hzero]
  let f : BitString (2 * m + 1) → BitString (2 * m + 1) → Bool :=
    fun x y => iteratedNotAllEqual d (fun i => x ⟨i.1, by omega⟩ && y ⟨i.1, by omega⟩)
  have hlow := PublicCoin.le_mul_ecomplexityFun_of_unique_disjoint f
    (fun x y hz => by
      have : (fun i : Fin (3 ^ d) => x ⟨i.1, by omega⟩ && y ⟨i.1, by omega⟩) =
          fun _ => false := by
        funext i; exact hz ⟨i.1, by omega⟩
      simp [f, this, hzero])
    (fun x y i₀ hu => by
      have : (fun i : Fin (3 ^ d) => x ⟨i.1, by omega⟩ && y ⟨i.1, by omega⟩) =
          fun i => decide (i = ⟨i₀.1, by omega⟩) := by
        funext i
        rw [hu ⟨i.1, by omega⟩]
        simp [Fin.ext_iff]
      simp [f, this, hmarked])
  have hcomap : PublicCoin.ecomplexityFun (1 / 3) f ≤
      PublicCoin.ecomplexityFun (1 / 3)
        (fun x y : BitString (3 ^ d) => iteratedNotAllEqual d (fun i => x i && y i)) :=
    PublicCoin.ecomplexityFun_comap_le
      (fun x y : BitString (3 ^ d) => iteratedNotAllEqual d (fun i => x i && y i))
      (fun (x : BitString (2 * m + 1)) (j : Fin (3 ^ d)) => x ⟨j.1, by omega⟩)
      (fun (y : BitString (2 * m + 1)) (j : Fin (3 ^ d)) => y ⟨j.1, by omega⟩)
  have h2m1' : ((2 * m + 1 : ℕ) : ℕ∞) = ((3 ^ d : ℕ) : ℕ∞) := by exact_mod_cast h2m1
  rw [h2m1'] at hlow
  exact hlow.trans (by gcongr)

end Cslib.Communication
