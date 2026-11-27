module

public import CslibFrontier.Algorithms.Lean.TSP.HeldKarp
public import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.List.Permutation
import Mathlib.Order.Bounds.Basic

/-!
# Cost-Scaling, Off-Diagonal Agreement, and Reversal Symmetry for TSP

General properties of `Cslib.Algorithms.Lean.TSP.walkCost` and `Cslib.Algorithms.Lean.TSP.heldKarp`:
* exact off-diagonal agreement (`heldKarp_congr_offDiag`),
* positive scalar cost-scaling invariance (`walkCost_const_mul`, `heldKarp_const_mul`),
* tour-reversal invariance for symmetric cost matrices (`walkCost_reverse`).
-/

public section

namespace CslibFrontier.Algorithms.Lean.TSP

open Cslib.Algorithms.Lean.TSP

/-- Reversing the interior vertices of a walk in a symmetric cost matrix reverses the endpoints
while preserving total cost. -/
theorem walkCost_reverse {α W : Type*} [AddCommMonoid W] {d : α → α → W}
    (hd : ∀ i j, d i j = d j i) :
    ∀ (L : List α) (a b : α), walkCost d a L.reverse b = walkCost d b L a
  | [], a, b => by simp [walkCost, hd a b]
  | x :: xs, a, b => by
      rw [List.reverse_cons, walkCost_append_singleton, walkCost_reverse hd xs a x]
      simp only [walkCost, hd x b, add_comm]

/-- `walkCost` scales linearly by a constant factor over any semiring. -/
theorem walkCost_const_mul {α R : Type*} [Semiring R] (d : α → α → R) (c : R) (a b : α) :
    ∀ L : List α, walkCost (fun i j => c * d i j) a L b = c * walkCost d a L b
  | [] => rfl
  | x :: xs => by
      simp only [walkCost, walkCost_const_mul d c x b xs, mul_add]

/-- `heldKarp` scales linearly by any nonnegative constant `c ≥ 0` over a linearly ordered
semiring `R`. -/
theorem heldKarp_const_mul {n : ℕ} {R : Type*} [Semiring R] [LinearOrder R] [IsStrictOrderedRing R]
    (d : Fin (n + 1) → Fin (n + 1) → R) {c : R} (hc : 0 ≤ c) :
    heldKarp (fun i j => c * d i j) = c * heldKarp d := by
  have h1 := isLeast_heldKarp_permutations (fun i j => c * d i j)
  have h2 := isLeast_heldKarp_permutations d
  refine IsLeast.unique h1 ⟨?_, ?_⟩
  · rcases h2.1 with ⟨L, hL, hval⟩
    exact ⟨L, hL, by rw [walkCost_const_mul, hval]⟩
  · rintro y ⟨L, hL, rfl⟩
    rw [walkCost_const_mul]
    exact mul_le_mul_of_nonneg_left (h2.2 ⟨L, hL, rfl⟩) hc

/-- Adjacent vertices along `0, L.map Fin.succ, 0` are distinct whenever `L` is a nodup list of
`Fin n` with `L ≠ []`. -/
private theorem walkCost_congr_offDiag_aux {n : ℕ} {W : Type*} [AddCommMonoid W]
    {d₁ d₂ : Fin (n + 1) → Fin (n + 1) → W}
    (h : ∀ i j, i ≠ j → d₁ i j = d₂ i j) :
    ∀ (a : Fin (n + 1)) (L : List (Fin n)),
      L.Nodup → (∀ x ∈ L, a ≠ x.succ) → (L = [] → a ≠ 0) →
        walkCost d₁ a (L.map Fin.succ) 0 = walkCost d₂ a (L.map Fin.succ) 0
  | a, [], _, _, ha0 => by
      simp only [List.map_nil, walkCost]
      exact h a 0 (ha0 rfl)
  | a, x :: xs, hnd, ha, _ => by
      have hne : a ≠ x.succ := ha x List.mem_cons_self
      have hnd_xs : xs.Nodup := (List.nodup_cons.1 hnd).2
      have hx_notin : x ∉ xs := (List.nodup_cons.1 hnd).1
      have hne_xs : ∀ y ∈ xs, x.succ ≠ y.succ := fun y hy heq =>
        hx_notin (Fin.succ_injective _ heq ▸ hy)
      simp only [List.map_cons, walkCost, h a x.succ hne,
        walkCost_congr_offDiag_aux h x.succ xs hnd_xs hne_xs (fun _ => Fin.succ_ne_zero x)]

/-- Two cost functions agreeing on all off-diagonal pairs `(i, j)` (`i ≠ j`) produce identical
`heldKarp` optimal tour costs whenever `1 ≤ n`. -/
theorem heldKarp_congr_offDiag {n : ℕ} (hn : 1 ≤ n) {W : Type*}
    [AddCommMonoid W] [LinearOrder W] [IsOrderedAddMonoid W]
    {d₁ d₂ : Fin (n + 1) → Fin (n + 1) → W}
    (h : ∀ i j, i ≠ j → d₁ i j = d₂ i j) :
    heldKarp d₁ = heldKarp d₂ := by
  have h1 := isLeast_heldKarp_permutations d₁
  have h2 := isLeast_heldKarp_permutations d₂
  have hwalk : ∀ L ∈ (List.finRange n).permutations,
      walkCost d₁ 0 (L.map Fin.succ) 0 = walkCost d₂ 0 (L.map Fin.succ) 0 := by
    intro L hL
    have hperm : L.Perm (List.finRange n) := List.mem_permutations.1 hL
    have hnd : L.Nodup := hperm.nodup_iff.2 (List.nodup_finRange n)
    have hne_nil : L = [] → (0 : Fin (n + 1)) ≠ 0 := by
      intro hnil
      have := hperm.length_eq
      simp [hnil] at this
      omega
    exact walkCost_congr_offDiag_aux h 0 L hnd (fun x _ => (Fin.succ_ne_zero x).symm) hne_nil
  have hset :
      {c | ∃ L ∈ (List.finRange n).permutations, walkCost d₁ 0 (L.map Fin.succ) 0 = c} =
      {c | ∃ L ∈ (List.finRange n).permutations, walkCost d₂ 0 (L.map Fin.succ) 0 = c} := by
    ext c
    simp only [Set.mem_ofPred_eq]
    exact exists_congr fun L => and_congr_right fun hL => by rw [hwalk L hL]
  rw [hset] at h1
  exact IsLeast.unique h1 h2

end CslibFrontier.Algorithms.Lean.TSP
