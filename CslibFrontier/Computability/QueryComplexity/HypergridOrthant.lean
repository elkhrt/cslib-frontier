/-
Copyright (c) 2026 Google DeepMind. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Google DeepMind
-/
module
-- upstream: candidate

public import Cslib.Init
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Find

/-!
# Discrete Balanced-Orthant Bisection on Finite Hypergrids

This module proves a discrete simultaneous median and balanced-orthant partitioning theorem on
finite `k`-dimensional hypergrids `Fin k → Fin n`: for any finite subset `S ⊆ [n]^k`, any free
coordinate subset `F ⊆ Fin k`, and any boundary template `z₀`, there exist a grid point `q`
agreeing with `z₀` outside `F` and an orthant orientation `φ : Fin k → OrthantSign` such that both
opposite closed `F`-orthants centered at `q` contain at least `|S| / 2^{|F|}` points of `S`.

## Main definitions

* `CslibFrontier.Computability.QueryComplexity.OrthantSign`: two-valued orthant direction
  `{-1, +1}`.
* `CslibFrontier.Computability.QueryComplexity.orthantLe`: closed coordinatewise orthant comparison.
* `CslibFrontier.Computability.QueryComplexity.hypergridOrthant`: subset of `S` lying in the
  `φ`-orthant around `q` over free coordinates `F`.

## Main results

* `CslibFrontier.Computability.QueryComplexity.exists_joint_median_split`: 1D simultaneous median
  threshold splitting two finite subsets into opposite half-lines of size at least half of each.
* `CslibFrontier.Computability.QueryComplexity.exists_balanced_orthant_hypergrid`: inductive
  `2^{-|F|}` balanced opposite-orthant theorem on finite hypergrids.
-/

public section

namespace CslibFrontier.Computability.QueryComplexity

/-- Two-valued orthant sign `{-1, +1}`. -/
inductive OrthantSign : Type
  /-- Lower half-line direction `x_i ≤ q_i`. -/
  | neg
  /-- Upper half-line direction `q_i ≤ x_i`. -/
  | pos
  deriving DecidableEq, Repr

namespace OrthantSign

/-- Opposite orthant sign involution. -/
@[expose] def dual : OrthantSign → OrthantSign
  | .neg => .pos
  | .pos => .neg

@[simp]
theorem dual_dual (s : OrthantSign) : s.dual.dual = s := by
  cases s <;> rfl

end OrthantSign

/-- Closed coordinatewise comparison along `b : OrthantSign`. -/
@[expose] def orthantLe {α : Type*} [LE α] (b : OrthantSign) (u v : α) : Prop :=
  match b with
  | .pos => v ≤ u
  | .neg => u ≤ v

instance instDecidableOrthantLe {α : Type*} [LE α] [DecidableRel (α := α) (· ≤ ·)]
    (b : OrthantSign) (u v : α) : Decidable (orthantLe b u v) := by
  cases b <;> dsimp only [orthantLe] <;> infer_instance

/-- Subset of `S ⊆ (Fin k → Fin n)` lying in the `φ`-orthant around `q` on coordinates `F`. -/
def hypergridOrthant {n k : ℕ} (S : Finset (Fin k → Fin n)) (q : Fin k → Fin n)
    (F : Finset (Fin k)) (φ : Fin k → OrthantSign) : Finset (Fin k → Fin n) :=
  S.filter fun x ↦ ∀ i ∈ F, orthantLe (φ i) (x i) (q i)

/-- Simultaneous 1D median threshold: for any two finite subsets `A, B ⊆ (Fin k → Fin n)` and
coordinate `i`, there exist `t : Fin n` and `b : OrthantSign` such that at least half of `A` lies
in the `b`-ray from `t` and at least half of `B` lies in the opposite `b.dual`-ray from `t`. -/
theorem exists_joint_median_split {n k : ℕ} [NeZero n]
    (A B : Finset (Fin k → Fin n)) (i : Fin k) :
    ∃ (t : Fin n) (b : OrthantSign),
      2 * (A.filter fun x ↦ orthantLe b (x i) t).card ≥ A.card ∧
      2 * (B.filter fun x ↦ orthantLe b.dual (x i) t).card ≥ B.card := by
  let fA (m : ℕ) : ℕ := (A.filter fun x ↦ (x i).val ≤ m).card
  let fB (m : ℕ) : ℕ := (B.filter fun x ↦ (x i).val ≤ m).card
  let good (m : ℕ) : Prop := m ≤ n - 1 ∧ (2 * fA m ≥ A.card ∨ 2 * fB m ≥ B.card)
  have hex : ∃ m, good m := by
    refine ⟨n - 1, le_rfl, Or.inl ?_⟩
    have hA_eq : (A.filter fun x ↦ (x i).val ≤ n - 1) = A := by
      ext x
      simp only [Finset.mem_filter, and_iff_left_iff_imp]
      intro _; have := (x i).isLt; omega
    dsimp only [fA]; rw [hA_eq]; omega
  classical
  let m₀ := Nat.find hex
  obtain ⟨hm₀_le, hm₀_or⟩ := Nat.find_spec hex
  let t : Fin n := ⟨m₀, by have := Nat.pos_of_ne_zero (NeZero.ne n); omega⟩
  have hge_count : ∀ C : Finset (Fin k → Fin n),
      (m₀ > 0 → 2 * (C.filter fun x ↦ (x i).val ≤ m₀ - 1).card < C.card) →
      2 * (C.filter fun x ↦ t ≤ x i).card ≥ C.card := by
    intro C hprev
    by_cases hm0 : m₀ = 0
    · have hC_eq : (C.filter fun x ↦ t ≤ x i) = C := by
        ext x
        simp only [Finset.mem_filter, and_iff_left_iff_imp]
        intro _; change m₀ ≤ (x i).val; omega
      rw [hC_eq]; omega
    · have hlt_prev := hprev (Nat.pos_of_ne_zero hm0)
      let C₁ := C.filter fun x ↦ (x i).val ≤ m₀ - 1
      let C₂ := C.filter fun x ↦ t ≤ x i
      change 2 * C₁.card < C.card at hlt_prev
      change 2 * C₂.card ≥ C.card
      have hdisj : Disjoint C₁ C₂ := by
        rw [Finset.disjoint_left]
        intro x hx1 hx2
        have h1 : (x i).val ≤ m₀ - 1 := (Finset.mem_filter.mp hx1).2
        have h2 : m₀ ≤ (x i).val := (Finset.mem_filter.mp hx2).2
        omega
      have hunion : C₁ ∪ C₂ = C := by
        ext x
        simp only [C₁, C₂, Finset.mem_union, Finset.mem_filter]
        refine ⟨fun hx ↦ hx.elim And.left And.left, fun hx ↦ ?_⟩
        change (_ ∧ _) ∨ (_ ∧ m₀ ≤ (x i).val)
        by_cases hle : (x i).val ≤ m₀ - 1
        · exact Or.inl ⟨hx, hle⟩
        · exact Or.inr ⟨hx, by omega⟩
      have hsum : C₁.card + C₂.card = C.card := by
        rw [← Finset.card_union_of_disjoint hdisj, hunion]
      omega
  rcases hm₀_or with hA_ge | hB_ge
  · refine ⟨t, .neg, hA_ge, hge_count B fun hpos ↦ ?_⟩
    have hnot := Nat.find_min hex (Nat.sub_lt hpos Nat.one_pos)
    have hnot_or : ¬ (2 * fA (m₀ - 1) ≥ A.card ∨ 2 * fB (m₀ - 1) ≥ B.card) :=
      fun hor ↦ hnot ⟨by omega, hor⟩
    exact not_le.mp (not_or.mp hnot_or).2
  · refine ⟨t, .pos, hge_count A fun hpos ↦ ?_, hB_ge⟩
    have hnot := Nat.find_min hex (Nat.sub_lt hpos Nat.one_pos)
    have hnot_or : ¬ (2 * fA (m₀ - 1) ≥ A.card ∨ 2 * fB (m₀ - 1) ≥ B.card) :=
      fun hor ↦ hnot ⟨by omega, hor⟩
    exact not_le.mp (not_or.mp hnot_or).1

/-- Discrete hypergrid balanced-orthant theorem: for every finite subset `S ⊆ (Fin k → Fin n)`,
coordinate subset `F`, and template `z₀`, there exist a grid point `q` agreeing with `z₀` outside
`F` and an orientation `φ` such that both opposite `F`-orthants at `q` contain at least
`|S| / 2^{|F|}` elements of `S`. -/
theorem exists_balanced_orthant_hypergrid {n k : ℕ} [NeZero n]
    (S : Finset (Fin k → Fin n)) (F : Finset (Fin k)) (z₀ : Fin k → Fin n) :
    ∃ (q : Fin k → Fin n) (φ : Fin k → OrthantSign),
      (∀ j ∉ F, q j = z₀ j) ∧
      2 ^ F.card * (hypergridOrthant S q F φ).card ≥ S.card ∧
      2 ^ F.card * (hypergridOrthant S q F (fun i ↦ (φ i).dual)).card ≥ S.card := by
  classical
  induction F using Finset.cons_induction with
  | empty =>
    refine ⟨z₀, fun _ ↦ .pos, fun _ _ ↦ rfl, ?_, ?_⟩ <;>
      simp [hypergridOrthant]
  | cons i I' hi_not ih =>
    obtain ⟨q', φ', hq'_out, hA_bound, hB_bound⟩ := ih
    let A := hypergridOrthant S q' I' φ'
    let B := hypergridOrthant S q' I' (fun j ↦ (φ' j).dual)
    obtain ⟨t, b, hA_split, hB_split⟩ := exists_joint_median_split A B i
    let q := Function.update q' i t
    let φ := Function.update φ' i b
    have hA_eq : hypergridOrthant S q (Finset.cons i I' hi_not) φ =
        A.filter fun x ↦ orthantLe b (x i) t := by
      ext x
      simp only [A, hypergridOrthant, Finset.mem_filter, Finset.mem_cons]
      constructor
      · rintro ⟨hxS, hall⟩
        refine ⟨⟨hxS, fun j hj ↦ ?_⟩, by simpa [q, φ] using hall i (Or.inl rfl)⟩
        have hji : j ≠ i := fun heq ↦ hi_not (heq ▸ hj)
        simpa [q, φ, Function.update_of_ne hji] using hall j (Or.inr hj)
      · rintro ⟨⟨hxS, hall⟩, hxi⟩
        refine ⟨hxS, fun j hj ↦ ?_⟩
        rcases hj with rfl | hj'
        · simpa [q, φ] using hxi
        · have hji : j ≠ i := fun heq ↦ hi_not (heq ▸ hj')
          simpa [q, φ, Function.update_of_ne hji] using hall j hj'
    have hB_eq : hypergridOrthant S q (Finset.cons i I' hi_not) (fun j ↦ (φ j).dual) =
        B.filter fun x ↦ orthantLe b.dual (x i) t := by
      ext x
      simp only [B, hypergridOrthant, Finset.mem_filter, Finset.mem_cons]
      constructor
      · rintro ⟨hxS, hall⟩
        refine ⟨⟨hxS, fun j hj ↦ ?_⟩, by simpa [q, φ] using hall i (Or.inl rfl)⟩
        have hji : j ≠ i := fun heq ↦ hi_not (heq ▸ hj)
        simpa [q, φ, Function.update_of_ne hji] using hall j (Or.inr hj)
      · rintro ⟨⟨hxS, hall⟩, hxi⟩
        refine ⟨hxS, fun j hj ↦ ?_⟩
        rcases hj with rfl | hj'
        · simpa [q, φ] using hxi
        · have hji : j ≠ i := fun heq ↦ hi_not (heq ▸ hj')
          simpa [q, φ, Function.update_of_ne hji] using hall j hj'
    refine ⟨q, φ, fun j hj ↦ ?_, ?_, ?_⟩
    · rw [Finset.mem_cons, not_or] at hj
      simpa [q, Function.update_of_ne hj.1] using hq'_out j hj.2
    · rw [Finset.card_cons, Nat.pow_succ', hA_eq]
      calc 2 * 2 ^ I'.card * (A.filter fun x ↦ orthantLe b (x i) t).card
          = 2 ^ I'.card * (2 * (A.filter fun x ↦ orthantLe b (x i) t).card) := by
            rw [Nat.mul_assoc, Nat.mul_left_comm]
        _ ≥ 2 ^ I'.card * A.card := Nat.mul_le_mul_left _ hA_split
        _ ≥ S.card := hA_bound
    · rw [Finset.card_cons, Nat.pow_succ', hB_eq]
      calc 2 * 2 ^ I'.card * (B.filter fun x ↦ orthantLe b.dual (x i) t).card
          = 2 ^ I'.card * (2 * (B.filter fun x ↦ orthantLe b.dual (x i) t).card) := by
            rw [Nat.mul_assoc, Nat.mul_left_comm]
        _ ≥ 2 ^ I'.card * B.card := Nat.mul_le_mul_left _ hB_split
        _ ≥ S.card := hB_bound

end CslibFrontier.Computability.QueryComplexity
