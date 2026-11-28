module

public import CslibFrontier.Computability.Communication.DirectProduct.IntersectionDist
public import CslibFrontier.Computability.Communication.DirectProduct.IntersectionSampling
public import CslibFrontier.Computability.Communication.Rectangle
import CslibFrontier.Probability.PMF.Event
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Linear Programming and Smooth Rectangle Bounds for Intersection Search

Linear programming relaxations for two-party communication protocols solving `k`-subset
intersection search `SEARCH_{C(N,k)}` and single-instance Nondisjointness:

* Valid `k`-intersection rectangles `IsValidSearchRect` and primal/dual LPs (`RectWeights`,
  `DualSolution`, `IsPrimalFeasible`, `IsDualFeasible`) with ambiguity parameter `T ≥ 1`.
* Weak LP duality (`weak_duality_search`, `det_protocol_dual_bound`, `publicCoin_dual_bound`) and
  explicit feasible dual construction (`searchChooseDual`, `searchChooseDual_feasible`,
  `searchChooseDual_obj`).
* `searchChoose_sdpt`: exponential success-probability upper bound for public-coin protocols
  solving `SEARCH_{C(N,k)}` in `o(N)` communication.
* Lovász LP and Smooth Rectangle Bound LP (`IsLovaszPrimal`, `IsLovaszDual`,
  `IsSmoothRectPrimal`, `IsSmoothRectDual`) together with an explicit linear dual lower bound
  `smooth_rect_ndisj_bound` for single-instance `NDISJ_n`.
-/

public section

namespace CslibFrontier.Computability.Communication

open Cslib Finset Cslib.Communication

/-! ### Valid `k`-intersection rectangles and the Search LP -/

/-- The family `R_v`: a rectangle `A × B ⊆ {0,1}^N × {0,1}^N` is valid for
`k`-intersection search if there exists a `k`-element subset `I ⊆ Fin N` contained in `x ∩ y` for
every `(x, y) ∈ A × B`. -/
@[expose] def IsValidSearchRect (N k : ℕ) (A B : Finset (BitString N)) : Prop :=
  ∃ I : Finset (Fin N), I.card = k ∧ (∀ x ∈ A, I ⊆ supportSet x) ∧ (∀ y ∈ B, I ⊆ supportSet y)

/-- A finite weighted family of combinatorial rectangles on `BitString N × BitString N`. -/
@[ext] structure RectWeights (N : ℕ) where
  /-- Number of rectangles in the family. -/
  size : ℕ
  /-- Alice's side of each rectangle. -/
  alice : Fin size → Finset (BitString N)
  /-- Bob's side of each rectangle. -/
  bob : Fin size → Finset (BitString N)
  /-- Real weight assigned to each rectangle. -/
  weight : Fin size → ℝ

/-- Total weight `∑_R w_R` of a rectangle weighting (objective of primal LP (1)). -/
@[expose] def RectWeights.cost {N : ℕ} (W : RectWeights N) : ℝ :=
  ∑ r : Fin W.size, W.weight r

/-- Total weight `∑_{R : (x, y) ∈ R} w_R` covering input pair `(x, y)`. -/
@[expose] def RectWeights.cover {N : ℕ} (W : RectWeights N) (x y : BitString N) : ℝ :=
  ∑ r : Fin W.size, if x ∈ W.alice r ∧ y ∈ W.bob r then W.weight r else 0

/-- Feasibility for the restricted-rectangle primal LP with upper
multiplicity / ambiguity bound `T` (taking `T = 1` for randomized protocols and `T = 2^(ε k)` for
limited-ambiguity AM protocols). -/
@[expose] def IsPrimalFeasible (N k : ℕ) (σ T : ℝ) (W : RectWeights N) : Prop :=
  (∀ r, 0 ≤ W.weight r) ∧
  (∀ r, IsValidSearchRect N k (W.alice r) (W.bob r)) ∧
  (∀ x y : BitString N, (interSet x y).card = k → σ ≤ W.cover x y) ∧
  (∀ x y : BitString N, W.cover x y ≤ T)

/-- Restricting to `R_v` automatically makes primal constraint (2) hold: inputs with `|x ∩ y| < k`
receive zero total weight. -/
theorem IsPrimalFeasible.cover_eq_zero_of_lt {N k : ℕ} {σ T : ℝ} {W : RectWeights N}
    (hW : IsPrimalFeasible N k σ T W) {x y : BitString N} (hlt : (interSet x y).card < k) :
    W.cover x y = 0 := by
  unfold RectWeights.cover
  refine sum_eq_zero fun r _ => ?_
  split_ifs with hmem
  · obtain ⟨I, hI, hA, hB⟩ := hW.2.1 r
    have hsub : I ⊆ interSet x y := by
      rw [interSet_eq_inter]
      exact subset_inter (hA x hmem.1) (hB y hmem.2)
    have hle : k ≤ (interSet x y).card := hI ▸ card_le_card hsub
    omega
  · rfl

/-- A candidate dual solution `(φ, ψ)` for the search dual LP. -/
@[ext] structure DualSolution (N : ℕ) where
  /-- Positive weights `φ_{x,y}` supported on `T_{k,N}`. -/
  phi : BitString N → BitString N → ℝ
  /-- Nonpositive weights `ψ_{x,y}`. -/
  psi : BitString N → BitString N → ℝ

/-- Feasibility for the search dual LP. -/
@[expose] def IsDualFeasible (N k : ℕ) (D : DualSolution N) : Prop :=
  (∀ x y, 0 ≤ D.phi x y) ∧
  (∀ x y, D.psi x y ≤ 0) ∧
  (∀ x y, (interSet x y).card ≠ k → D.phi x y = 0) ∧
  (∀ A B : Finset (BitString N), IsValidSearchRect N k A B →
    ∑ x ∈ A, ∑ y ∈ B, (D.phi x y + D.psi x y) ≤ 1)

/-- Dual objective value `∑_{x,y} (σ * φ_{x,y} + T * ψ_{x,y})` for ambiguity bound `T`. -/
@[expose] def DualSolution.obj {N : ℕ} (D : DualSolution N) (σ T : ℝ) : ℝ :=
  ∑ x : BitString N, ∑ y : BitString N, (σ * D.phi x y + T * D.psi x y)

/-- Double-sum characterization of `DualSolution.obj`. -/
theorem DualSolution.obj_eq_sum {N : ℕ} (D : DualSolution N) (σ T : ℝ) :
    D.obj σ T = ∑ x : BitString N, ∑ y : BitString N, (σ * D.phi x y + T * D.psi x y) := rfl

/-- Helper collapsing a full-space double sum restricted to a rectangle `A × B`. -/
private theorem sum_ite_mem_rect {N : ℕ} (A B : Finset (BitString N))
    (f : BitString N → BitString N → ℝ) :
    ∑ x : BitString N, ∑ y : BitString N, (if x ∈ A ∧ y ∈ B then f x y else 0) =
      ∑ x ∈ A, ∑ y ∈ B, f x y := by
  calc
    ∑ x : BitString N, ∑ y : BitString N, (if x ∈ A ∧ y ∈ B then f x y else 0)
      = ∑ x : BitString N,
          if x ∈ A then ∑ y : BitString N, if y ∈ B then f x y else 0 else 0 := by
        refine sum_congr rfl fun x _ => ?_
        by_cases hx : x ∈ A
        · simp only [hx, true_and, ↓reduceIte]
        · simp only [hx, false_and, ↓reduceIte, sum_const_zero]
    _ = ∑ x ∈ A, ∑ y ∈ B, f x y := by
        rw [← sum_filter]
        have hA : (univ.filter fun x => x ∈ A) = A := by ext x; simp
        rw [hA]
        refine sum_congr rfl fun x _ => ?_
        rw [← sum_filter]
        have hB : (univ.filter fun y => y ∈ B) = B := by ext y; simp
        rw [hB]

/-- Weak LP duality for the search LP, generalized to ambiguity `T`:
every dual feasible solution lower-bounds the cost of every primal feasible solution. -/
theorem weak_duality_search {N k : ℕ} {σ T : ℝ} {W : RectWeights N} {D : DualSolution N}
    (hW : IsPrimalFeasible N k σ T W) (hD : IsDualFeasible N k D) :
    D.obj σ T ≤ W.cost := by
  obtain ⟨hWnn, hWrect, hWlo, hWhi⟩ := hW
  obtain ⟨hDphi, hDpsi, hDsupp, hDrect⟩ := hD
  have h1 : D.obj σ T ≤
      ∑ x : BitString N, ∑ y : BitString N,
        W.cover x y * (D.phi x y + D.psi x y) := by
    unfold DualSolution.obj
    refine sum_le_sum fun x _ => sum_le_sum fun y _ => ?_
    have hphi_le : σ * D.phi x y ≤ W.cover x y * D.phi x y := by
      by_cases hk : (interSet x y).card = k
      · exact mul_le_mul_of_nonneg_right (hWlo x y hk) (hDphi x y)
      · rw [hDsupp x y hk, mul_zero, mul_zero]
    have hpsi_le : T * D.psi x y ≤ W.cover x y * D.psi x y :=
      mul_le_mul_of_nonpos_right (hWhi x y) (hDpsi x y)
    linarith
  have h2 : ∑ x : BitString N, ∑ y : BitString N,
        W.cover x y * (D.phi x y + D.psi x y) =
      ∑ r : Fin W.size, W.weight r *
        ∑ x ∈ W.alice r, ∑ y ∈ W.bob r, (D.phi x y + D.psi x y) := by
    have hterm : ∀ x y : BitString N,
        W.cover x y * (D.phi x y + D.psi x y) =
          ∑ r : Fin W.size,
            if x ∈ W.alice r ∧ y ∈ W.bob r then
              W.weight r * (D.phi x y + D.psi x y)
            else 0 := by
      intro x y
      unfold RectWeights.cover
      rw [sum_mul]
      refine sum_congr rfl fun r _ => by split_ifs <;> ring
    simp_rw [hterm]
    rw [sum_congr rfl fun x _ => sum_comm]
    rw [sum_comm]
    refine sum_congr rfl fun r _ => ?_
    rw [sum_ite_mem_rect, mul_sum]
    refine sum_congr rfl fun x _ => by rw [mul_sum]
  have h3 : ∑ r : Fin W.size, W.weight r *
        ∑ x ∈ W.alice r, ∑ y ∈ W.bob r, (D.phi x y + D.psi x y) ≤ W.cost := by
    unfold RectWeights.cost
    refine sum_le_sum fun r _ => ?_
    have hle := hDrect (W.alice r) (W.bob r) (hWrect r)
    nlinarith [hWnn r]
  linarith

/-! ### Explicit Dual Solution and Feasibility -/

/-- Exact binomial identity for dual feasibility:
`C(n, k) * C(n + k, k) = C(2k, k) * C(n + k, 2k)` for `k ≤ n`. -/
private theorem choose_mul_add_choose_eq {n k : ℕ} (hkn : k ≤ n) :
    n.choose k * (n + k).choose k = (2 * k).choose k * (n + k).choose (2 * k) := by
  have h1 := Nat.choose_mul_factorial_mul_factorial hkn
  have h2 := Nat.choose_mul_factorial_mul_factorial (show k ≤ n + k by omega)
  have h3 := Nat.choose_mul_factorial_mul_factorial (show k ≤ 2 * k by omega)
  have h4 := Nat.choose_mul_factorial_mul_factorial (show 2 * k ≤ n + k by omega)
  have hsub1 : n + k - k = n := by omega
  have hsub2 : 2 * k - k = k := by omega
  have hsub3 : n + k - 2 * k = n - k := by omega
  rw [hsub1] at h2
  rw [hsub2] at h3
  rw [hsub3] at h4
  have hmul : (n.choose k * (n + k).choose k) *
      (k.factorial * k.factorial * (2 * k).factorial * (n - k).factorial * n.factorial) =
      ((2 * k).choose k * (n + k).choose (2 * k)) *
      (k.factorial * k.factorial * (2 * k).factorial * (n - k).factorial * n.factorial) := by
    calc
      (n.choose k * (n + k).choose k) *
          (k.factorial * k.factorial * (2 * k).factorial * (n - k).factorial * n.factorial)
        = (n.choose k * k.factorial * (n - k).factorial) *
          ((n + k).choose k * k.factorial * n.factorial) * (2 * k).factorial := by ring
      _ = n.factorial * (n + k).factorial * (2 * k).factorial := by rw [h1, h2]
      _ = ((2 * k).choose k * k.factorial * k.factorial) *
          ((n + k).choose (2 * k) * (2 * k).factorial * (n - k).factorial) * n.factorial := by
          rw [h3, h4]; ring
      _ = ((2 * k).choose k * (n + k).choose (2 * k)) *
          (k.factorial * k.factorial * (2 * k).factorial * (n - k).factorial * n.factorial) := by
          ring
  have hpos : 0 < k.factorial * k.factorial * (2 * k).factorial * (n - k).factorial *
      n.factorial := by positivity
  exact Nat.eq_of_mul_eq_mul_right hpos hmul

/-- Elementary inductive bound replacing Stirling's approximation uniformly for all `k ≥ 1`:
`(3 / 2) ^ k ≤ C(2k, k) * (3 / 4) ^ k`. -/
private theorem three_halves_pow_le_centralBinom_mul {k : ℕ} :
    (3 / 2 : ℝ) ^ k ≤ ((2 * k).choose k : ℝ) * (3 / 4 : ℝ) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hstep : (k + 1) * (2 * (k + 1)).choose (k + 1) = 2 * (2 * k + 1) * (2 * k).choose k := by
      have h1 := Nat.choose_mul_factorial_mul_factorial (show k ≤ 2 * k by omega)
      have h2 := Nat.choose_mul_factorial_mul_factorial (show k + 1 ≤ 2 * (k + 1) by omega)
      rw [show 2 * k - k = k by omega] at h1
      rw [show 2 * (k + 1) - (k + 1) = k + 1 by omega] at h2
      have hfac1 : (k + 1).factorial = (k + 1) * k.factorial := Nat.factorial_succ k
      have hfac2 : (2 * (k + 1)).factorial =
          (2 * k + 2) * (2 * k + 1) * (2 * k).factorial := by
        rw [show 2 * (k + 1) = (2 * k + 1) + 1 by omega, Nat.factorial_succ, Nat.factorial_succ]
        ring
      have hmul : ((k + 1) * (2 * (k + 1)).choose (k + 1)) * (k.factorial * k.factorial) =
          (2 * (2 * k + 1) * (2 * k).choose k) * (k.factorial * k.factorial) := by
        have h2' : (2 * (k + 1)).choose (k + 1) * ((k + 1) * k.factorial) *
            ((k + 1) * k.factorial) = (2 * k + 2) * (2 * k + 1) * (2 * k).factorial := by
          rwa [hfac1, hfac2] at h2
        have hl : (k + 1) * ((k + 1) * (2 * (k + 1)).choose (k + 1) *
            (k.factorial * k.factorial)) =
            (k + 1) * (2 * (2 * k + 1) * (2 * k).choose k * (k.factorial * k.factorial)) := by
          calc
            (k + 1) * ((k + 1) * (2 * (k + 1)).choose (k + 1) * (k.factorial * k.factorial))
              = (2 * (k + 1)).choose (k + 1) * ((k + 1) * k.factorial) *
                  ((k + 1) * k.factorial) := by ring
            _ = (2 * k + 2) * (2 * k + 1) * (2 * k).factorial := h2'
            _ = (2 * k + 2) * (2 * k + 1) * ((2 * k).choose k * k.factorial * k.factorial) := by
                rw [h1]
            _ = (k + 1) * (2 * (2 * k + 1) * (2 * k).choose k *
                  (k.factorial * k.factorial)) := by ring
        exact Nat.eq_of_mul_eq_mul_left (Nat.succ_pos k) hl
      exact Nat.eq_of_mul_eq_mul_right (by positivity) hmul
    have hstepR : ((k + 1 : ℕ) : ℝ) * ((2 * (k + 1)).choose (k + 1) : ℝ) =
        2 * (2 * (k : ℝ) + 1) * ((2 * k).choose k : ℝ) := by
      exact_mod_cast hstep
    have hratio : (2 : ℝ) * ((2 * k).choose k : ℝ) ≤ ((2 * (k + 1)).choose (k + 1) : ℝ) := by
      have hpos : (0 : ℝ) < (k + 1 : ℕ) := Nat.cast_pos.mpr (Nat.succ_pos k)
      have hmul : ((k + 1 : ℕ) : ℝ) * (2 * ((2 * k).choose k : ℝ)) ≤
          ((k + 1 : ℕ) : ℝ) * ((2 * (k + 1)).choose (k + 1) : ℝ) := by
        rw [hstepR]
        have hnn : (0 : ℝ) ≤ ((2 * k).choose k : ℝ) := Nat.cast_nonneg _
        push_cast
        nlinarith
      exact le_of_mul_le_mul_left hmul hpos
    rw [pow_succ, pow_succ]
    calc
      (3 / 2 : ℝ) ^ k * (3 / 2)
        ≤ ((2 * k).choose k : ℝ) * (3 / 4 : ℝ) ^ k * (3 / 2) := by gcongr
      _ = (2 * ((2 * k).choose k : ℝ)) * (3 / 4 : ℝ) ^ k * (3 / 4) := by ring
      _ ≤ ((2 * (k + 1)).choose (k + 1) : ℝ) * (3 / 4 : ℝ) ^ k * (3 / 4) := by gcongr
      _ = ((2 * (k + 1)).choose (k + 1) : ℝ) * ((3 / 4 : ℝ) ^ k * (3 / 4)) := by ring

/-- Explicit feasible dual solution on `N = n + k` coordinates with `m = n / 4`,
positive weights on `T_{k, n+k}`, and negative weights on `T_{2k, n+k}` scaled by `(2 / 3) ^ k`. -/
noncomputable def searchChooseDual (n k : ℕ) : DualSolution (n + k) where
  phi x y := (2 : ℝ) ^ (gammaISL * (n : ℝ)) * muWeight k (n + k) (n / 4 + k) x y
  psi x y := -(2 : ℝ) ^ (gammaISL * (n : ℝ)) * (2 / 3 : ℝ) ^ k *
    muWeight (2 * k) (n + k) (n / 4 + k) x y

/-- Feasibility of `searchChooseDual n k` whenever `k ≤ gammaISL * n / 2`. -/
theorem searchChooseDual_feasible {n k : ℕ} (hk : (k : ℝ) ≤ gammaISL * (n : ℝ) / 2) :
    IsDualFeasible (n + k) k (searchChooseDual n k) := by
  have hγ_le : gammaISL ≤ 1 := gammaISL_le_one
  have hkn : k ≤ n := by
    have : (k : ℝ) ≤ (n : ℝ) := by nlinarith [gammaISL_pos]
    exact_mod_cast this
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x y
    unfold searchChooseDual
    have := muWeight_nonneg k (n + k) (n / 4 + k) x y
    positivity
  · intro x y
    unfold searchChooseDual
    have := muWeight_nonneg (2 * k) (n + k) (n / 4 + k) x y
    have hpos : 0 ≤ (2 : ℝ) ^ (gammaISL * (n : ℝ)) * (2 / 3 : ℝ) ^ k := by positivity
    nlinarith
  · intro x y hne
    dsimp only [searchChooseDual]
    have hnot : (x, y) ∉ weightPairs k (n + k) (n / 4 + k) := fun h =>
      hne (mem_weightPairs.mp h).2.2
    rw [muWeight_eq_zero_of_notMem hnot, mul_zero]
  · intro A B hrect
    set m := n / 4
    have hsum_eq :
        ∑ x ∈ A, ∑ y ∈ B, ((searchChooseDual n k).phi x y + (searchChooseDual n k).psi x y) =
        (2 : ℝ) ^ (gammaISL * (n : ℝ)) *
          (muRect k (n + k) (m + k) A B -
            (2 / 3 : ℝ) ^ k * muRect (2 * k) (n + k) (m + k) A B) := by
      dsimp only [searchChooseDual]
      simp_rw [muRect_eq_sum]
      simp_rw [sum_add_distrib, ← mul_sum]
      ring
    rw [hsum_eq]
    by_cases hsmall : muRect k (n + k) (m + k) A B ≤ (2 : ℝ) ^ (-gammaISL * (n : ℝ))
    · have hnn : 0 ≤ (2 / 3 : ℝ) ^ k * muRect (2 * k) (n + k) (m + k) A B :=
        mul_nonneg (by positivity) (muRect_nonneg _ _ _ _ _)
      calc
        (2 : ℝ) ^ (gammaISL * (n : ℝ)) *
            (muRect k (n + k) (m + k) A B -
              (2 / 3 : ℝ) ^ k * muRect (2 * k) (n + k) (m + k) A B)
          ≤ (2 : ℝ) ^ (gammaISL * (n : ℝ)) * muRect k (n + k) (m + k) A B := by
            have h2pos : 0 ≤ (2 : ℝ) ^ (gammaISL * (n : ℝ)) := by positivity
            nlinarith
        _ ≤ (2 : ℝ) ^ (gammaISL * (n : ℝ)) * (2 : ℝ) ^ (-gammaISL * (n : ℝ)) := by gcongr
        _ = 1 := by
            rw [← Real.rpow_add two_pos]
            norm_num
    · push Not at hsmall
      obtain ⟨I, hI, hA, hB⟩ := hrect
      set A' := restrictSideAdd I hI A
      set B' := restrictSideAdd I hI B
      have hadd1 := muRect_add (m := m) hI hA hB
      have hadd2 := muRect_two_mul_add (m := m) hkn hI hA hB
      have hch_pos : (0 : ℝ) < (n + k).choose k := Nat.cast_pos.mpr (Nat.choose_pos (by omega))
      have hch_ge1 : (1 : ℝ) ≤ (n + k).choose k := by
        exact_mod_cast Nat.choose_pos (show k ≤ n + k by omega)
      have h0_eq : muRect 0 n m A' B' = ((n + k).choose k : ℝ) * muRect k (n + k) (m + k) A B := by
        rw [hadd1, ← mul_assoc, mul_inv_cancel₀ hch_pos.ne', one_mul]
      have hbig' : (2 : ℝ) ^ (-gammaISL * (n : ℝ)) ≤ muRect 0 n m A' B' := by
        rw [h0_eq]
        nlinarith [show (0 : ℝ) ≤ (2 : ℝ) ^ (-gammaISL * (n : ℝ)) by positivity]
      have hisl := intersection_sampling_three_fourths hk A' B' hbig'
      have hch2_pos : (0 : ℝ) < (n + k).choose (2 * k) :=
        Nat.cast_pos.mpr (Nat.choose_pos (by omega))
      have hratio_eq : ((n.choose k : ℝ) / ((n + k).choose (2 * k) : ℝ)) *
          ((n + k).choose k : ℝ) = ((2 * k).choose k : ℝ) := by
        have hnat : (n.choose k : ℝ) * ((n + k).choose k : ℝ) =
            ((2 * k).choose k : ℝ) * ((n + k).choose (2 * k) : ℝ) := by
          exact_mod_cast choose_mul_add_choose_eq hkn
        field_simp
        linarith
      have h2k_ge : (3 / 2 : ℝ) ^ k * muRect k (n + k) (m + k) A B ≤
          muRect (2 * k) (n + k) (m + k) A B := by
        calc
          (3 / 2 : ℝ) ^ k * muRect k (n + k) (m + k) A B
            ≤ ((2 * k).choose k : ℝ) * (3 / 4 : ℝ) ^ k * muRect k (n + k) (m + k) A B := by
              exact mul_le_mul_of_nonneg_right three_halves_pow_le_centralBinom_mul
                (muRect_nonneg _ _ _ _ _)
          _ = ((n.choose k : ℝ) / ((n + k).choose (2 * k) : ℝ)) *
                ((3 / 4 : ℝ) ^ k * (((n + k).choose k : ℝ) * muRect k (n + k) (m + k) A B)) := by
              rw [← hratio_eq]; ring
          _ = ((n.choose k : ℝ) / ((n + k).choose (2 * k) : ℝ)) *
                ((3 / 4 : ℝ) ^ k * muRect 0 n m A' B') := by rw [← h0_eq]
          _ ≤ ((n.choose k : ℝ) / ((n + k).choose (2 * k) : ℝ)) * muRect k n m A' B' := by
              gcongr
          _ = muRect (2 * k) (n + k) (m + k) A B := hadd2.symm
      have hcancel : (2 / 3 : ℝ) ^ k * ((3 / 2 : ℝ) ^ k * muRect k (n + k) (m + k) A B) =
          muRect k (n + k) (m + k) A B := by
        rw [← mul_assoc, ← mul_pow]
        norm_num
      have hnonpos : muRect k (n + k) (m + k) A B -
          (2 / 3 : ℝ) ^ k * muRect (2 * k) (n + k) (m + k) A B ≤ 0 := by
        have hmul := mul_le_mul_of_nonneg_left h2k_ge (by positivity : (0 : ℝ) ≤ (2 / 3 : ℝ) ^ k)
        linarith
      have h2pos : 0 ≤ (2 : ℝ) ^ (gammaISL * (n : ℝ)) := by positivity
      nlinarith

/-- Exact objective value of `searchChooseDual n k`:
`obj σ T = 2 ^ (gammaISL * n) * (σ - T * (2 / 3) ^ k)` whenever `k ≤ n / 4`. -/
theorem searchChooseDual_obj {n k : ℕ} (hkn : k ≤ n / 4) (σ T : ℝ) :
    (searchChooseDual n k).obj σ T =
      (2 : ℝ) ^ (gammaISL * (n : ℝ)) * (σ - T * (2 / 3 : ℝ) ^ k) := by
  unfold DualSolution.obj searchChooseDual
  have hsum1 : ∑ x : BitString (n + k), ∑ y : BitString (n + k),
      muWeight k (n + k) (n / 4 + k) x y = 1 := sum_muWeight (by omega) (by omega)
  have hsum2 : ∑ x : BitString (n + k), ∑ y : BitString (n + k),
      muWeight (2 * k) (n + k) (n / 4 + k) x y = 1 := sum_muWeight (by omega) (by omega)
  simp_rw [sum_add_distrib]
  have h1 : ∑ x : BitString (n + k), ∑ y : BitString (n + k),
      σ * ((2 : ℝ) ^ (gammaISL * (n : ℝ)) * muWeight k (n + k) (n / 4 + k) x y) =
      σ * (2 : ℝ) ^ (gammaISL * (n : ℝ)) := by
    simp_rw [← mul_assoc, ← mul_sum, hsum1, mul_one]
  have h2 : ∑ x : BitString (n + k), ∑ y : BitString (n + k),
      T * (-(2 : ℝ) ^ (gammaISL * (n : ℝ)) * (2 / 3 : ℝ) ^ k *
        muWeight (2 * k) (n + k) (n / 4 + k) x y) =
      -(T * ((2 : ℝ) ^ (gammaISL * (n : ℝ)) * (2 / 3 : ℝ) ^ k)) := by
    have hpt : ∀ x y : BitString (n + k),
        T * (-(2 : ℝ) ^ (gammaISL * (n : ℝ)) * (2 / 3 : ℝ) ^ k *
          muWeight (2 * k) (n + k) (n / 4 + k) x y) =
        (-(T * ((2 : ℝ) ^ (gammaISL * (n : ℝ)) * (2 / 3 : ℝ) ^ k))) *
          muWeight (2 * k) (n + k) (n / 4 + k) x y := fun _ _ => by ring
    simp_rw [hpt, ← mul_sum, hsum2, mul_one]
  rw [h1, h2]
  ring

/-! ### Explicit constants and master LP lower bound -/

/-- Explicit universal success-decay constant for `SEARCH_{C(N,k)}`. -/
@[expose] noncomputable def alphaMain : ℝ := 1 / 8

/-- Numeric value of `alphaMain`. -/
theorem alphaMain_val : alphaMain = 1 / 8 := rfl

/-- Explicit communication-rate constant for `SEARCH_{C(N,k)}`. -/
@[expose] noncomputable def betaMain : ℝ := gammaISL / 4

/-- Formula expressing `betaMain` in terms of `gammaISL`. -/
theorem betaMain_eq_div : betaMain = gammaISL / 4 := rfl

/-- Explicit `k / N` threshold constant for `SEARCH_{C(N,k)}`. -/
@[expose] noncomputable def gammaMain : ℝ := gammaISL / 12

/-- Formula expressing `gammaMain` in terms of `gammaISL`. -/
theorem gammaMain_eq_div : gammaMain = gammaISL / 12 := rfl

/-- `alphaMain ∈ (0, 1]`. -/
theorem alphaMain_mem : 0 < alphaMain ∧ alphaMain ≤ 1 := by
  unfold alphaMain; norm_num

/-- `betaMain ∈ (0, 1]`. -/
theorem betaMain_mem : 0 < betaMain ∧ betaMain ≤ 1 := by
  rw [betaMain_eq_div, gammaISL_eq_div, deltaRaz_eq_zpow]
  norm_num

/-- `gammaMain ∈ (0, 1]`. -/
theorem gammaMain_mem : 0 < gammaMain ∧ gammaMain ≤ 1 := by
  rw [gammaMain_eq_div, gammaISL_eq_div, deltaRaz_eq_zpow]
  norm_num

/-- Elementary inequality `a ^ k + b ^ k ≤ (a + b) ^ k` for `a, b ≥ 0` and `k ≥ 1`. -/
private theorem pow_add_pow_le_add_pow {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) {k : ℕ} (hk : 1 ≤ k) :
    a ^ k + b ^ k ≤ (a + b) ^ k := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
  induction m with
  | zero => simp
  | succ m ih =>
    have h1 : a ^ (1 + m) ≤ (a + b) ^ (1 + m) := pow_le_pow_left₀ ha (by linarith) _
    have h2 : b ^ (1 + m) ≤ (a + b) ^ (1 + m) := pow_le_pow_left₀ hb (by linarith) _
    rw [show 1 + (m + 1) = (1 + m) + 1 by omega, pow_succ, pow_succ, pow_succ]
    nlinarith

/-- Master arithmetic step for the dual LP bound: given `n = N - k`, `1 ≤ k`,
`k ≤ gammaMain * N`, ambiguity `T ≤ (9 / 8) ^ k`, and cost `C ≤ 2 ^ (betaMain * N)`,
the inequality `2 ^ (gammaISL * n) * (σ - T * (2 / 3) ^ k) ≤ C` forces `σ ≤ 2 ^ (-alphaMain * k)`.
-/
theorem success_le_of_dual_bound {N k : ℕ} {σ T C : ℝ} (hk1 : 1 ≤ k)
    (hk : (k : ℝ) ≤ gammaMain * (N : ℝ)) (hT : T ≤ (9 / 8 : ℝ) ^ k)
    (hC : C ≤ (2 : ℝ) ^ (betaMain * (N : ℝ)))
    (hdual : (2 : ℝ) ^ (gammaISL * ((N - k : ℕ) : ℝ)) * (σ - T * (2 / 3 : ℝ) ^ k) ≤ C) :
    σ ≤ (2 : ℝ) ^ (-alphaMain * (k : ℝ)) := by
  have hkN : k ≤ N := by
    have : (k : ℝ) ≤ (N : ℝ) := by nlinarith [gammaMain_mem.2]
    exact_mod_cast this
  have h2pos : (0 : ℝ) < (2 : ℝ) ^ (gammaISL * ((N - k : ℕ) : ℝ)) := by positivity
  have hdiv : σ - T * (2 / 3 : ℝ) ^ k ≤ C * (2 : ℝ) ^ (-(gammaISL * ((N - k : ℕ) : ℝ))) := by
    have hmul := mul_le_mul_of_nonneg_right hdual
      (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ (-(gammaISL * ((N - k : ℕ) : ℝ))))
    rw [mul_comm, ← mul_assoc, ← Real.rpow_add two_pos, neg_add_cancel, Real.rpow_zero, one_mul]
      at hmul
    exact hmul
  have hexp : betaMain * (N : ℝ) + -(gammaISL * ((N - k : ℕ) : ℝ)) ≤ -8 * (k : ℝ) := by
    rw [Nat.cast_sub hkN]
    unfold betaMain gammaMain at *
    have hγ1 : gammaISL ≤ 1 := gammaISL_le_one
    nlinarith [gammaISL_pos]
  have hrem : C * (2 : ℝ) ^ (-(gammaISL * ((N - k : ℕ) : ℝ))) ≤ (1 / 256 : ℝ) ^ k := by
    calc
      C * (2 : ℝ) ^ (-(gammaISL * ((N - k : ℕ) : ℝ)))
        ≤ (2 : ℝ) ^ (betaMain * (N : ℝ)) * (2 : ℝ) ^ (-(gammaISL * ((N - k : ℕ) : ℝ))) := by
          gcongr
      _ = (2 : ℝ) ^ (betaMain * (N : ℝ) + -(gammaISL * ((N - k : ℕ) : ℝ))) :=
          (Real.rpow_add two_pos _ _).symm
      _ ≤ (2 : ℝ) ^ (-8 * (k : ℝ)) := Real.rpow_le_rpow_of_exponent_le one_le_two hexp
      _ = (1 / 256 : ℝ) ^ k := by
          rw [show (-8 : ℝ) * (k : ℝ) = (-8 : ℝ) * ((k : ℕ) : ℝ) by rfl, Real.rpow_mul zero_le_two,
            Real.rpow_natCast, show (-8 : ℝ) = ((-8 : ℤ) : ℝ) by norm_num, Real.rpow_intCast]
          norm_num
  have hT23 : T * (2 / 3 : ℝ) ^ k ≤ (3 / 4 : ℝ) ^ k := by
    calc
      T * (2 / 3 : ℝ) ^ k ≤ (9 / 8 : ℝ) ^ k * (2 / 3 : ℝ) ^ k := by gcongr
      _ = (3 / 4 : ℝ) ^ k := by rw [← mul_pow]; norm_num
  have h78_le : (7 / 8 : ℝ) ^ k ≤ (2 : ℝ) ^ (-alphaMain * (k : ℝ)) := by
    have hbase : (7 / 8 : ℝ) ≤ (2 : ℝ) ^ (-alphaMain) := by
      have hpow : (7 / 8 : ℝ) ^ (8 : ℕ) ≤ ((2 : ℝ) ^ (-alphaMain)) ^ (8 : ℕ) := by
        rw [← Real.rpow_natCast ((2 : ℝ) ^ _), ← Real.rpow_mul zero_le_two]
        unfold alphaMain
        norm_num
      have hnn : 0 ≤ (2 : ℝ) ^ (-alphaMain) := by positivity
      by_contra hlt
      push Not at hlt
      have : ((2 : ℝ) ^ (-alphaMain)) ^ (8 : ℕ) < (7 / 8 : ℝ) ^ (8 : ℕ) :=
        pow_lt_pow_left₀ hlt hnn (by norm_num)
      linarith
    calc
      (7 / 8 : ℝ) ^ k ≤ ((2 : ℝ) ^ (-alphaMain)) ^ k := pow_le_pow_left₀ (by norm_num) hbase k
      _ = (2 : ℝ) ^ (-alphaMain * (k : ℝ)) := by
          rw [← Real.rpow_natCast ((2 : ℝ) ^ _), ← Real.rpow_mul zero_le_two]
  have hsum_pow : (3 / 4 : ℝ) ^ k + (1 / 256 : ℝ) ^ k ≤ (7 / 8 : ℝ) ^ k := by
    calc
      (3 / 4 : ℝ) ^ k + (1 / 256 : ℝ) ^ k
        ≤ (3 / 4 + 1 / 256 : ℝ) ^ k := pow_add_pow_le_add_pow (by norm_num) (by norm_num) hk1
      _ ≤ (7 / 8 : ℝ) ^ k := pow_le_pow_left₀ (by norm_num) (by norm_num) k
  linarith

/-- **LP lower bound for `SEARCH_{C(N,k)}`**: any primal feasible rectangle weighting of ambiguity
`T ≤ (9 / 8) ^ k` and total cost at most `2 ^ (betaMain * N)` has success probability
`σ ≤ 2 ^ (-alphaMain * k)` whenever `k ≤ gammaMain * N`. -/
theorem lp_search_lower_bound {N k : ℕ} {σ T : ℝ} {W : RectWeights N}
    (hk : (k : ℝ) ≤ gammaMain * (N : ℝ)) (hT : T ≤ (9 / 8 : ℝ) ^ k)
    (hcost : W.cost ≤ (2 : ℝ) ^ (betaMain * (N : ℝ)))
    (hW : IsPrimalFeasible N k σ T W) :
    σ ≤ (2 : ℝ) ^ (-alphaMain * (k : ℝ)) := by
  rcases Nat.eq_zero_or_pos k with rfl | hkpos
  · simp only [Nat.cast_zero, mul_zero, Real.rpow_zero]
    have h0 := hW.2.2.1 (fun _ => false) (fun _ => false) (by
      rw [card_eq_zero]; ext i; simp)
    have h1 := hW.2.2.2 (fun _ => false) (fun _ => false)
    simp only [pow_zero] at hT
    linarith
  have hkN : k ≤ N := by
    have : (k : ℝ) ≤ (N : ℝ) := by nlinarith [gammaMain_mem.2]
    exact_mod_cast this
  set n := N - k
  have hNk : n + k = N := Nat.sub_add_cancel hkN
  have hγ_le : gammaMain ≤ gammaISL / 12 := le_rfl
  have hk_isl : (k : ℝ) ≤ gammaISL * (n : ℝ) / 2 := by
    have hN : (N : ℝ) = (n : ℝ) + (k : ℝ) := by exact_mod_cast hNk.symm
    have hγ1 : gammaISL ≤ 1 := gammaISL_le_one
    unfold gammaMain at hk
    nlinarith [gammaISL_pos]
  have hkn4 : k ≤ n / 4 := by
    have hγ4 : gammaISL / 2 ≤ 1 / 8 := gammaISL_div_two_le
    have h4 : (4 * k : ℝ) ≤ (n : ℝ) := by nlinarith
    have h4nat : 4 * k ≤ n := by exact_mod_cast h4
    omega
  clear_value n
  subst hNk
  have hdual_feas := searchChooseDual_feasible hk_isl
  have hwd := weak_duality_search hW hdual_feas
  rw [searchChooseDual_obj hkn4 σ T] at hwd
  have hsub : n + k - k = n := Nat.add_sub_cancel n k
  exact success_le_of_dual_bound hkpos hk hT hcost (by simpa [hsub] using hwd)

/-! ### Deterministic protocol duality and `SEARCH_{C(N,k)}` lower bound -/

/-- Pointwise dual-weight bound for a single deterministic protocol `p` on `SearchChooseRel N k`:
if `D` is dual feasible, then the sum over all `(x, y)` of `1_{p succeeds} * φ + ψ` is at most
`p.leafCount`. Proved by restricting each accepting leaf rectangle to pairs intersecting on its
declared `k`-subset `I`. -/
private theorem det_protocol_dual_bound {N k : ℕ}
    (p : Protocol (BitString N) (BitString N) (Option (Finset (Fin N))))
    {D : DualSolution N} (hD : IsDualFeasible N k D) :
    ∑ x : BitString N, ∑ y : BitString N,
        (({q : Protocol (BitString N) (BitString N) (Option (Finset (Fin N))) |
            SearchChooseRel N k x y (q.run x y)}.indicator (fun _ => D.phi x y) p) + D.psi x y) ≤
      (p.leafCount : ℝ) := by
  classical
  simp only [Set.indicator_apply, Set.mem_ofPred_eq]
  obtain ⟨hDphi, hDpsi, hDsupp, hDrect⟩ := hD
  -- For each leaf `i`, if `p.leafOutput i = some I` with `I.card = k`, define the refined valid
  -- search rectangle `A_i × B_i ⊆ leafAlice i × leafBob i`.
  let goodLeaf (i : Fin p.leafCount) : Prop :=
    match p.leafOutput i with
    | none => False
    | some I => I.card = k
  let leafA (i : Fin p.leafCount) : Finset (BitString N) :=
    match p.leafOutput i with
    | none => ∅
    | some I => univ.filter fun x => x ∈ p.leafAlice i ∧ I ⊆ supportSet x
  let leafB (i : Fin p.leafCount) : Finset (BitString N) :=
    match p.leafOutput i with
    | none => ∅
    | some I => univ.filter fun y => y ∈ p.leafBob i ∧ I ⊆ supportSet y
  have hgood_le : ∀ i : Fin p.leafCount, goodLeaf i →
      ∑ x ∈ leafA i, ∑ y ∈ leafB i, (D.phi x y + D.psi x y) ≤ 1 := by
    intro i hi
    cases ho : p.leafOutput i with
    | none => simp [goodLeaf, ho] at hi
    | some I =>
      simp only [goodLeaf, ho] at hi
      apply hDrect
      refine ⟨I, hi, ?_, ?_⟩
      · intro x hx; simp only [leafA, ho, mem_filter, mem_univ, true_and] at hx; exact hx.2
      · intro y hy; simp only [leafB, ho, mem_filter, mem_univ, true_and] at hy; exact hy.2
  have hsum_leaves :
      ∑ i : Fin p.leafCount with goodLeaf i,
        ∑ x ∈ leafA i, ∑ y ∈ leafB i, (D.phi x y + D.psi x y) ≤ (p.leafCount : ℝ) := by
    calc
      ∑ i : Fin p.leafCount with goodLeaf i,
          ∑ x ∈ leafA i, ∑ y ∈ leafB i, (D.phi x y + D.psi x y)
        ≤ ∑ i : Fin p.leafCount with goodLeaf i, (1 : ℝ) :=
          sum_le_sum fun i hi => hgood_le i (mem_filter.mp hi).2
      _ = (#{i : Fin p.leafCount | goodLeaf i} : ℝ) := by rw [sum_const, nsmul_eq_mul, mul_one]
      _ ≤ (p.leafCount : ℝ) := by
          exact_mod_cast (card_le_univ _).trans_eq (Fintype.card_fin p.leafCount)
  -- Each `(x, y)` lies in `leafA i × leafB i` for at most one `i` (namely `i = p.leaf x y`),
  -- and whenever `|x ∩ y| = k` and `p` succeeds on `(x, y)`, it lies in `leafA (p.leaf x y) × ...`.
  have hswap :
      ∑ i : Fin p.leafCount with goodLeaf i,
        ∑ x ∈ leafA i, ∑ y ∈ leafB i, (D.phi x y + D.psi x y) =
      ∑ x : BitString N, ∑ y : BitString N,
        if goodLeaf (p.leaf x y) ∧ x ∈ leafA (p.leaf x y) ∧ y ∈ leafB (p.leaf x y) then
          D.phi x y + D.psi x y
        else 0 := by
    have h1 : ∀ i : Fin p.leafCount,
        (if goodLeaf i then ∑ x ∈ leafA i, ∑ y ∈ leafB i, (D.phi x y + D.psi x y) else 0) =
        ∑ x : BitString N, ∑ y : BitString N,
          if goodLeaf i ∧ x ∈ leafA i ∧ y ∈ leafB i then D.phi x y + D.psi x y else 0 := by
      intro i
      by_cases hi : goodLeaf i
      · simp only [hi, ↓reduceIte, true_and]
        exact (sum_ite_mem_rect (leafA i) (leafB i) (fun x y => D.phi x y + D.psi x y)).symm
      · simp [hi]
    rw [sum_filter, sum_congr rfl fun i _ => h1 i]
    rw [sum_comm]
    rw [sum_congr rfl fun x _ => sum_comm]
    refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => ?_
    have huniq : ∀ i : Fin p.leafCount,
        goodLeaf i ∧ x ∈ leafA i ∧ y ∈ leafB i → i = p.leaf x y := by
      rintro i ⟨hi, hx, hy⟩
      cases ho : p.leafOutput i with
      | none => simp [goodLeaf, ho] at hi
      | some I =>
        simp only [leafA, leafB, ho, mem_filter, mem_univ, true_and] at hx hy
        exact (Protocol.leaf_eq_iff.mpr ⟨hx.1, hy.1⟩).symm
    have hite : ∀ i : Fin p.leafCount,
        (if goodLeaf i ∧ x ∈ leafA i ∧ y ∈ leafB i then D.phi x y + D.psi x y else 0) =
        (if i = p.leaf x y then
          if goodLeaf (p.leaf x y) ∧ x ∈ leafA (p.leaf x y) ∧ y ∈ leafB (p.leaf x y) then
            D.phi x y + D.psi x y
          else 0
        else 0) := by
      intro i
      by_cases heq : i = p.leaf x y
      · subst heq; simp
      · have hnot : ¬(goodLeaf i ∧ x ∈ leafA i ∧ y ∈ leafB i) := fun h => heq (huniq i h)
        simp [heq, hnot]
    rw [sum_congr rfl fun i _ => hite i, sum_ite_eq' univ (p.leaf x y), ite_eq_left (mem_univ _)]
  rw [hswap] at hsum_leaves
  refine le_trans ?_ hsum_leaves
  refine sum_le_sum fun x _ => sum_le_sum fun y _ => ?_
  by_cases hcond : goodLeaf (p.leaf x y) ∧ x ∈ leafA (p.leaf x y) ∧ y ∈ leafB (p.leaf x y)
  · rw [ite_eq_left hcond]
    split_ifs
    · linarith
    · linarith [hDphi x y]
  · rw [ite_eq_right hcond]
    by_cases hsucc : SearchChooseRel N k x y (p.run x y)
    · simp only [hsucc, ↓reduceIte]
      by_cases hcard : (interSet x y).card = k
      · exfalso
        have hrun := (searchChooseRel_eq_card_iff hcard).mp hsucc
        rw [Protocol.run_eq_leafOutput_leaf] at hrun
        apply hcond
        refine ⟨?_, ?_, ?_⟩
        · simp [goodLeaf, hrun, hcard]
        · simp only [leafA, hrun, mem_filter, mem_univ, true_and]
          exact ⟨Protocol.mem_leafAlice_leaf, by rw [interSet_eq_inter]; exact inter_subset_left⟩
        · simp only [leafB, hrun, mem_filter, mem_univ, true_and]
          exact ⟨Protocol.mem_leafBob_leaf, by rw [interSet_eq_inter]; exact inter_subset_right⟩
      · rw [hDsupp x y hcard, zero_add]
        exact hDpsi x y
    · simp only [hsucc, ↓reduceIte, zero_add]
      exact hDpsi x y

/-- Averaging `det_protocol_dual_bound` over any public-coin distribution `μ` (without requiring
finite support of `μ`). -/
theorem publicCoin_dual_bound {N k c : ℕ}
    {μ : PublicCoin (BitString N) (BitString N) (Option (Finset (Fin N)))}
    (hdepth : μ.depth ≤ c) {σ : ℝ} (hsolves : SolvesWithSuccess μ σ (SearchChooseRel N k))
    {D : DualSolution N} (hD : IsDualFeasible N k D) :
    D.obj σ 1 ≤ (2 : ℝ) ^ c := by
  classical
  have hμ_sum : ∑' p, (μ p).toReal = 1 := by
    have h := μ.tsum_coe
    have hsumm : Summable fun p => (μ p).toReal :=
      ENNReal.summable_toReal (by rw [h]; exact ENNReal.one_ne_top)
    rw [← ENNReal.tsum_toReal_eq (fun p => μ.apply_ne_top p), h, ENNReal.toReal_one]
  have hsumm_μ : Summable fun p => (μ p).toReal :=
    ENNReal.summable_toReal (by rw [μ.tsum_coe]; exact ENNReal.one_ne_top)
  have hpt : ∀ p, (μ p).toReal *
      (∑ x : BitString N, ∑ y : BitString N,
        ((if SearchChooseRel N k x y (p.run x y) then D.phi x y else 0) + D.psi x y)) ≤
      (μ p).toReal * (2 : ℝ) ^ c := by
    intro p
    by_cases hp : p ∈ μ.support
    · have hd : p.depth ≤ c := Nat.cast_le (α :=
      ℕ∞).mp ((PublicCoin.depth_le_depth hp).trans hdepth)
      have hlc : (p.leafCount : ℝ) ≤ (2 : ℝ) ^ c := by
        exact_mod_cast p.leafCount_le_two_pow_depth.trans (Nat.pow_le_pow_right two_pos hd)
      have hdet := det_protocol_dual_bound p hD
      simp only [Set.indicator_apply, Set.mem_ofPred_eq] at hdet
      exact mul_le_mul_of_nonneg_left (hdet.trans hlc) ENNReal.toReal_nonneg
    · have h0 : μ p = 0 := by simpa [PMF.mem_support_iff] using hp
      simp [h0]
  have hsumm_term : ∀ x y : BitString N,
      Summable fun p => (μ p).toReal *
        ((if SearchChooseRel N k x y (p.run x y) then D.phi x y else 0) + D.psi x y) := by
    intro x y
    refine Summable.of_norm_bounded (g := fun p => (μ p).toReal * (|D.phi x y| + |D.psi x y|))
      (hsumm_μ.mul_right _) fun p => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
    refine mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
    calc
      |(if SearchChooseRel N k x y (p.run x y) then D.phi x y else 0) + D.psi x y|
        ≤ |if SearchChooseRel N k x y (p.run x y) then D.phi x y else 0| + |D.psi x y| :=
          abs_add_le _ _
      _ ≤ |D.phi x y| + |D.psi x y| := by split_ifs <;> simp [abs_nonneg]
  have htsum_le :
      ∑' p, (μ p).toReal *
        (∑ x : BitString N, ∑ y : BitString N,
          ((if SearchChooseRel N k x y (p.run x y) then D.phi x y else 0) + D.psi x y)) ≤
      (2 : ℝ) ^ c := by
    have hsumm_lhs : Summable fun p => (μ p).toReal *
        (∑ x : BitString N, ∑ y : BitString N,
          ((if SearchChooseRel N k x y (p.run x y) then D.phi x y else 0) + D.psi x y)) := by
      simp_rw [mul_sum]
      exact summable_sum fun x _ => summable_sum fun y _ => hsumm_term x y
    calc
      _ ≤ ∑' p, (μ p).toReal * (2 : ℝ) ^ c :=
          hsumm_lhs.tsum_le_tsum hpt (hsumm_μ.mul_right _)
      _ = (∑' p, (μ p).toReal) * (2 : ℝ) ^ c := tsum_mul_right
      _ = (2 : ℝ) ^ c := by rw [hμ_sum, one_mul]
  have hswap :
      ∑' p, (μ p).toReal *
        (∑ x : BitString N, ∑ y : BitString N,
          ((if SearchChooseRel N k x y (p.run x y) then D.phi x y else 0) + D.psi x y)) =
      ∑ x : BitString N, ∑ y : BitString N,
        (successProb μ (SearchChooseRel N k) x y * D.phi x y + D.psi x y) := by
    simp_rw [mul_sum]
    rw [Summable.tsum_finsetSum fun x _ => summable_sum fun y _ => hsumm_term x y]
    refine sum_congr rfl fun x _ => ?_
    rw [Summable.tsum_finsetSum fun y _ => hsumm_term x y]
    refine sum_congr rfl fun y _ => ?_
    have hsumm1 : Summable fun p => (μ p).toReal *
        (if SearchChooseRel N k x y (p.run x y) then D.phi x y else 0) := by
      refine Summable.of_norm_bounded (g := fun p => (μ p).toReal * |D.phi x y|)
        (hsumm_μ.mul_right _) fun p => ?_
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
      refine mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
      split_ifs <;> simp [abs_nonneg]
    have hsumm2 : Summable fun p => (μ p).toReal * D.psi x y := hsumm_μ.mul_right _
    simp_rw [mul_add]
    rw [hsumm1.tsum_add hsumm2, tsum_mul_right, hμ_sum, one_mul]
    congr 1
    have hpt1 : ∀ p, (μ p).toReal *
        (if SearchChooseRel N k x y (p.run x y) then D.phi x y else 0) =
        (if SearchChooseRel N k x y (p.run x y) then (μ p).toReal else 0) * D.phi x y := by
      intro p; split_ifs <;> ring
    simp_rw [hpt1, tsum_mul_right]
    congr 1
    rw [successProb_eq_toOuterMeasure, PMF.toOuterMeasure_apply]
    have hne : ∀ p, ({q : Protocol (BitString N) (BitString N) (Option (Finset (Fin N))) |
        SearchChooseRel N k x y (q.run x y)}.indicator (⇑μ) p) ≠ ⊤ := fun p => by
      by_cases hp : SearchChooseRel N k x y (p.run x y) <;> simp [hp, PMF.apply_ne_top]
    rw [ENNReal.tsum_toReal_eq hne]
    refine tsum_congr fun p => ?_
    by_cases hp : SearchChooseRel N k x y (p.run x y) <;> simp [hp]
  rw [hswap] at htsum_le
  refine le_trans ?_ htsum_le
  unfold DualSolution.obj
  refine sum_le_sum fun x _ => sum_le_sum fun y _ => ?_
  rw [one_mul]
  have := mul_le_mul_of_nonneg_right (hsolves x y) (hD.1 x y)
  linarith

/-- Explicit-constant strong direct product bound for `SEARCH_{C(N,k)}`:
every public-coin randomized protocol of communication `c ≤ betaMain * N` for `SEARCH_{C(N,k)}`
with `k ≤ gammaMain * N` has worst-case success probability `σ ≤ 2 ^ (-alphaMain * k)`. -/
theorem main_search_choose_bound {N k c : ℕ} (hk : (k : ℝ) ≤ gammaMain * (N : ℝ))
    (hc : (c : ℝ) ≤ betaMain * (N : ℝ))
    {μ : PublicCoin (BitString N) (BitString N) (Option (Finset (Fin N)))}
    (hdepth : μ.depth ≤ c) {σ : ℝ} (hsolves : SolvesWithSuccess μ σ (SearchChooseRel N k)) :
    σ ≤ (2 : ℝ) ^ (-alphaMain * (k : ℝ)) := by
  rcases Nat.eq_zero_or_pos k with rfl | hkpos
  · simp only [Nat.cast_zero, mul_zero, Real.rpow_zero]
    exact solvesWithSuccess_le_one hsolves
  have hkN : k ≤ N := by
    have : (k : ℝ) ≤ (N : ℝ) := by nlinarith [gammaMain_mem.2]
    exact_mod_cast this
  set n := N - k
  have hNk : n + k = N := Nat.sub_add_cancel hkN
  have hk_isl : (k : ℝ) ≤ gammaISL * (n : ℝ) / 2 := by
    have hN : (N : ℝ) = (n : ℝ) + (k : ℝ) := by exact_mod_cast hNk.symm
    have hγ1 : gammaISL ≤ 1 := gammaISL_le_one
    unfold gammaMain at hk
    nlinarith [gammaISL_pos]
  have hkn4 : k ≤ n / 4 := by
    have hγ4 : gammaISL / 2 ≤ 1 / 8 := gammaISL_div_two_le
    have h4 : (4 * k : ℝ) ≤ (n : ℝ) := by nlinarith
    have h4nat : 4 * k ≤ n := by exact_mod_cast h4
    omega
  clear_value n
  subst hNk
  have hdual := publicCoin_dual_bound hdepth hsolves (searchChooseDual_feasible hk_isl)
  rw [searchChooseDual_obj hkn4 σ 1] at hdual
  have hsub : n + k - k = n := Nat.add_sub_cancel n k
  have hC : ((2 : ℝ) ^ c) ≤ (2 : ℝ) ^ (betaMain * ((n + k : ℕ) : ℝ)) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le one_le_two hc
  exact success_le_of_dual_bound (T := 1) hkpos hk (one_le_pow₀ (by norm_num)) hC
    (by rw [hsub]; exact hdual)

/-- Strong direct product bound for public-coin protocols solving `SEARCH_{C(N,k)}`:
There are constants `0 < α, β, γ ≤ 1` such that every randomized public-coin protocol with
communication at most `β N` for `SEARCH_{C(N,k)}` with `k ≤ γ N` has worst-case success
probability at most `2 ^ (-α k)`. -/
theorem searchChoose_sdpt :
    ∃ α β γ : ℝ, (0 < α ∧ α ≤ 1) ∧ (0 < β ∧ β ≤ 1) ∧ (0 < γ ∧ γ ≤ 1) ∧
      ∀ (N k c : ℕ), (k : ℝ) ≤ γ * (N : ℝ) → (c : ℝ) ≤ β * (N : ℝ) →
        ∀ (μ : PublicCoin (BitString N) (BitString N) (Option (Finset (Fin N)))),
          μ.depth ≤ c → ∀ σ : ℝ, SolvesWithSuccess μ σ (SearchChooseRel N k) →
            σ ≤ (2 : ℝ) ^ (-α * (k : ℝ)) :=
  ⟨alphaMain, betaMain, gammaMain, alphaMain_mem, betaMain_mem, gammaMain_mem,
    fun _ _ _ hk hc _ hdepth _ hsolves => main_search_choose_bound hk hc hdepth hsolves⟩

/-! ### Lovász LP and Smooth Rectangle Bound LP -/

/-- Primal feasibility for Lovász's LP for a Boolean function `f`
with error `ε`. -/
@[expose] def IsLovaszPrimalFeasible {N : ℕ} (f : BitString N → BitString N → Bool) (ε : ℝ)
    (W : RectWeights N) : Prop :=
  (∀ r, 0 ≤ W.weight r) ∧
  (∀ x y, f x y = true → 1 - ε ≤ W.cover x y) ∧
  (∀ x y, f x y = false → W.cover x y ≤ ε)

/-- Dual feasibility for Lovász's LP. -/
@[expose] def IsLovaszDualFeasible {N : ℕ} (f : BitString N → BitString N → Bool)
    (phi : BitString N → BitString N → ℝ) : Prop :=
  (∀ x y, f x y = true → 0 ≤ phi x y) ∧
  (∀ x y, f x y = false → phi x y ≤ 0) ∧
  (∀ A B : Finset (BitString N), ∑ x ∈ A, ∑ y ∈ B, phi x y ≤ 1)

/-- Weak duality for Lovász's LP. -/
theorem weak_duality_lovasz {N : ℕ} {f : BitString N → BitString N → Bool} {ε : ℝ}
    {W : RectWeights N} {phi : BitString N → BitString N → ℝ}
    (hW : IsLovaszPrimalFeasible f ε W) (hD : IsLovaszDualFeasible f phi) :
    (∑ x : BitString N, ∑ y : BitString N,
        if f x y = true then (1 - ε) * phi x y else ε * phi x y) ≤ W.cost := by
  obtain ⟨hWnn, hW1, hW0⟩ := hW
  obtain ⟨hD1, hD0, hDrect⟩ := hD
  have h1 : (∑ x : BitString N, ∑ y : BitString N,
        if f x y = true then (1 - ε) * phi x y else ε * phi x y) ≤
      ∑ x : BitString N, ∑ y : BitString N, W.cover x y * phi x y := by
    refine sum_le_sum fun x _ => sum_le_sum fun y _ => ?_
    cases hxy : f x y
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact mul_le_mul_of_nonpos_right (hW0 x y hxy) (hD0 x y hxy)
    · simp only [↓reduceIte]
      exact mul_le_mul_of_nonneg_right (hW1 x y hxy) (hD1 x y hxy)
  have h2 : ∑ x : BitString N, ∑ y : BitString N, W.cover x y * phi x y =
      ∑ r : Fin W.size, W.weight r * ∑ x ∈ W.alice r, ∑ y ∈ W.bob r, phi x y := by
    have hterm : ∀ x y : BitString N, W.cover x y * phi x y =
        ∑ r : Fin W.size, if x ∈ W.alice r ∧ y ∈ W.bob r then W.weight r * phi x y else 0 := by
      intro x y; unfold RectWeights.cover; rw [sum_mul]
      exact sum_congr rfl fun r _ => by split_ifs <;> ring
    simp_rw [hterm]
    rw [sum_congr rfl fun x _ => sum_comm, sum_comm]
    refine sum_congr rfl fun r _ => ?_
    rw [sum_ite_mem_rect, mul_sum]
    refine sum_congr rfl fun x _ => by rw [mul_sum]
  have h3 : ∑ r : Fin W.size, W.weight r * ∑ x ∈ W.alice r, ∑ y ∈ W.bob r, phi x y ≤ W.cost :=
    sum_le_sum fun r _ => by nlinarith [hWnn r, hDrect (W.alice r) (W.bob r)]
  linarith

/-- Primal feasibility for the Smooth Rectangle Bound LP: Lovász's LP
augmented with the partition upper bound `∑_{R ∋ (x,y)} w_R ≤ 1` on `1`-inputs (Eq. (32)). -/
@[expose] def IsSmoothRectPrimalFeasible {N : ℕ} (f : BitString N → BitString N → Bool) (ε : ℝ)
    (W : RectWeights N) : Prop :=
  IsLovaszPrimalFeasible f ε W ∧ ∀ x y, f x y = true → W.cover x y ≤ 1

/-- Dual feasibility for the Smooth Rectangle Bound LP. -/
@[expose] def IsSmoothRectDualFeasible {N : ℕ} (f : BitString N → BitString N → Bool)
    (D : DualSolution N) : Prop :=
  (∀ x y, f x y = true → 0 ≤ D.phi x y ∧ D.psi x y ≤ 0) ∧
  (∀ x y, f x y = false → D.phi x y ≤ 0 ∧ D.psi x y = 0) ∧
  (∀ A B : Finset (BitString N), ∑ x ∈ A, ∑ y ∈ B, (D.phi x y + D.psi x y) ≤ 1)

/-- Weak duality for the Smooth Rectangle Bound LP. -/
theorem weak_duality_smooth_rect {N : ℕ} {f : BitString N → BitString N → Bool} {ε : ℝ}
    {W : RectWeights N} {D : DualSolution N}
    (hW : IsSmoothRectPrimalFeasible f ε W) (hD : IsSmoothRectDualFeasible f D) :
    (∑ x : BitString N, ∑ y : BitString N,
        (if f x y = true then (1 - ε) * D.phi x y + D.psi x y else ε * D.phi x y)) ≤ W.cost := by
  obtain ⟨⟨hWnn, hW1, hW0⟩, hWle1⟩ := hW
  obtain ⟨hD1, hD0, hDrect⟩ := hD
  have h1 : (∑ x : BitString N, ∑ y : BitString N,
        (if f x y = true then (1 - ε) * D.phi x y + D.psi x y else ε * D.phi x y)) ≤
      ∑ x : BitString N, ∑ y : BitString N, W.cover x y * (D.phi x y + D.psi x y) := by
    refine sum_le_sum fun x _ => sum_le_sum fun y _ => ?_
    cases hxy : f x y
    · simp only [Bool.false_eq_true, ↓reduceIte, (hD0 x y hxy).2, add_zero]
      exact mul_le_mul_of_nonpos_right (hW0 x y hxy) (hD0 x y hxy).1
    · simp only [↓reduceIte]
      have hphi := mul_le_mul_of_nonneg_right (hW1 x y hxy) (hD1 x y hxy).1
      have hpsi := mul_le_mul_of_nonpos_right (hWle1 x y hxy) (hD1 x y hxy).2
      linarith
  have h2 : ∑ x : BitString N, ∑ y : BitString N, W.cover x y * (D.phi x y + D.psi x y) =
      ∑ r : Fin W.size, W.weight r *
        ∑ x ∈ W.alice r, ∑ y ∈ W.bob r, (D.phi x y + D.psi x y) := by
    have hterm : ∀ x y : BitString N, W.cover x y * (D.phi x y + D.psi x y) =
        ∑ r : Fin W.size,
          if x ∈ W.alice r ∧ y ∈ W.bob r then
            W.weight r * (D.phi x y + D.psi x y)
          else 0 := by
      intro x y; unfold RectWeights.cover; rw [sum_mul]
      exact sum_congr rfl fun r _ => by split_ifs <;> ring
    simp_rw [hterm]
    rw [sum_congr rfl fun x _ => sum_comm, sum_comm]
    refine sum_congr rfl fun r _ => ?_
    rw [sum_ite_mem_rect, mul_sum]
    refine sum_congr rfl fun x _ => by rw [mul_sum]
  have h3 : ∑ r : Fin W.size, W.weight r *
        ∑ x ∈ W.alice r, ∑ y ∈ W.bob r, (D.phi x y + D.psi x y) ≤ W.cost :=
    sum_le_sum fun r _ => by nlinarith [hWnn r, hDrect (W.alice r) (W.bob r)]
  linarith

/-- Explicit smooth-rectangle dual bound for single-instance `NDISJ_n`:
for any `n ≥ 8`, any valid 1-intersection rectangle family `W` with `cover ≥ 1 - ε` on `T_{1,n}`
and `cover ≤ 1` everywhere satisfies `2 ^ ((deltaRaz / 64) * n) * ((1 - ε) - 3 / 4) ≤ W.cost`. -/
theorem smooth_rect_ndisj_bound {n : ℕ} (hn : 8 ≤ n) {ε : ℝ} {W : RectWeights n}
    (hW : IsPrimalFeasible n 1 (1 - ε) 1 W) :
    (2 : ℝ) ^ ((deltaRaz / 64) * (n : ℝ)) * ((1 - ε) - 3 / 4) ≤ W.cost := by
  set m := n / 4
  set β : ℝ := deltaRaz / 64
  have hδ_val : deltaRaz = 1 / (2 : ℝ) ^ (42 : ℕ) := by
    rw [deltaRaz_eq_zpow]; norm_num
  let D : DualSolution n := {
    phi := fun x y => (2 : ℝ) ^ (β * (n : ℝ)) * muWeight 1 n m x y
    psi := fun x y => -(3 / 4 : ℝ) * (2 : ℝ) ^ (β * (n : ℝ)) * muWeight 2 n m x y
  }
  have hD : IsDualFeasible n 1 D := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro x y; dsimp [D]; have := muWeight_nonneg 1 n m x y; positivity
    · intro x y; dsimp [D]
      have := muWeight_nonneg 2 n m x y
      have hpos : 0 ≤ (3 / 4 : ℝ) * (2 : ℝ) ^ (β * (n : ℝ)) := by positivity
      nlinarith
    · intro x y hne; dsimp [D]
      have hnot : (x, y) ∉ weightPairs 1 n m := fun h => hne (mem_weightPairs.mp h).2.2
      rw [muWeight_eq_zero_of_notMem hnot, mul_zero]
    · intro A B hrect
      have hsum_eq : ∑ x ∈ A, ∑ y ∈ B, (D.phi x y + D.psi x y) =
          (2 : ℝ) ^ (β * (n : ℝ)) * (muRect 1 n m A B - (3 / 4 : ℝ) * muRect 2 n m A B) := by
        dsimp only [D]; simp_rw [muRect_eq_sum]
        simp_rw [sum_add_distrib, ← mul_sum]
        ring
      rw [hsum_eq]
      by_cases hsmall : muRect 1 n m A B ≤ (2 : ℝ) ^ (-β * (n : ℝ))
      · have hnn : 0 ≤ (3 / 4 : ℝ) * muRect 2 n m A B :=
          mul_nonneg (by norm_num) (muRect_nonneg _ _ _ _ _)
        calc
          (2 : ℝ) ^ (β * (n : ℝ)) * (muRect 1 n m A B - (3 / 4 : ℝ) * muRect 2 n m A B)
            ≤ (2 : ℝ) ^ (β * (n : ℝ)) * muRect 1 n m A B := by
              have h2pos : 0 ≤ (2 : ℝ) ^ (β * (n : ℝ)) := by positivity
              nlinarith
          _ ≤ (2 : ℝ) ^ (β * (n : ℝ)) * (2 : ℝ) ^ (-β * (n : ℝ)) := by gcongr
          _ = 1 := by rw [← Real.rpow_add two_pos]; norm_num
      · push Not at hsmall
        obtain ⟨I, hI, hA, hB⟩ := hrect
        have hAs : sliceSide I A = A := filter_true_of_mem hA
        have hBs : sliceSide I B = B := filter_true_of_mem hB
        set A' := restrictSide I hI A
        set B' := restrictSide I hI B
        have h1eq : muRect 1 n m A B = (n : ℝ)⁻¹ * muRect 0 (n - 1) (m - 1) A' B' := by
          have h := muRect_slice_sub (k := 1) (n := n) (m := m) (by omega) (by omega) hI A B
          rw [hAs, hBs, Nat.choose_one_right] at h
          exact h
        have h2eq : muRect 2 n m A B =
            (((n - 1 : ℕ) : ℝ) / (n.choose 2 : ℝ)) * muRect 1 (n - 1) (m - 1) A' B' := by
          have h := muRect_slice_succ_sub (k := 1) (n := n) (m := m) (by omega) (by omega) hI A B
          rw [hAs, hBs] at h
          exact h
        have hn0 : (0 : ℝ) < n := by positivity
        have h0eq : muRect 0 (n - 1) (m - 1) A' B' = (n : ℝ) * muRect 1 n m A B := by
          rw [h1eq, ← mul_assoc, mul_inv_cancel₀ hn0.ne', one_mul]
        -- Since `μ_{0, n-1, m-1}(A' × B') ≤ 1`, `μ_{1, n, m}(A × B) ≤ 1 / n ≤ 1 / 8`, which
        -- forces `2 ^ (-β n) < 1 / 8`, hence `β n > 3` and `n > 2 ^ 46`.
        have hmu1_le_inv : muRect 1 n m A B ≤ 1 / 8 := by
          have h0le1 : muRect 0 (n - 1) (m - 1) A' B' ≤ 1 :=
            muRect_le_one (Nat.zero_le _) (by omega) A' B'
          have hn8 : (8 : ℝ) ≤ n := by exact_mod_cast hn
          nlinarith [muRect_nonneg 1 n m A B]
        have hn_large : (2 : ℝ) ^ (46 : ℕ) < (n : ℝ) := by
          by_contra hle
          push Not at hle
          have hexp : (-1 : ℝ) ≤ -β * (n : ℝ) := by
            dsimp only [β]; rw [hδ_val]
            nlinarith [show (1 / (2 : ℝ) ^ (42 : ℕ) / 64) * (2 : ℝ) ^ (46 : ℕ) = 1 / 4 by norm_num]
          have hhalf : (1 / 2 : ℝ) ≤ (2 : ℝ) ^ (-β * (n : ℝ)) := by
            calc (1 / 2 : ℝ) = (2 : ℝ) ^ (-1 : ℝ) := by
                  rw [show (-1 : ℝ) = ((-1 : ℤ) : ℝ) by norm_num, Real.rpow_intCast]; norm_num
              _ ≤ (2 : ℝ) ^ (-β * (n : ℝ)) := Real.rpow_le_rpow_of_exponent_le one_le_two hexp
          linarith
        have h0_big : (2 : ℝ) ^ (-deltaRaz * ((n - 1 : ℕ) : ℝ)) ≤
            muRect 0 (n - 1) (m - 1) A' B' := by
          rw [h0eq]
          have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
          have hexp : -deltaRaz * ((n - 1 : ℕ) : ℝ) ≤ -β * (n : ℝ) := by
            rw [Nat.cast_sub (show 1 ≤ n by omega), Nat.cast_one]
            dsimp only [β]
            have : (8 : ℝ) ≤ n := by exact_mod_cast hn
            nlinarith [deltaRaz_pos]
          calc
            (2 : ℝ) ^ (-deltaRaz * ((n - 1 : ℕ) : ℝ))
              ≤ (2 : ℝ) ^ (-β * (n : ℝ)) := Real.rpow_le_rpow_of_exponent_le one_le_two hexp
            _ ≤ 1 * muRect 1 n m A B := by linarith
            _ ≤ (n : ℝ) * muRect 1 n m A B := by
                exact mul_le_mul_of_nonneg_right hn1 (muRect_nonneg _ _ _ _ _)
        have hm_hi' : ((m - 1 : ℕ) : ℝ) ≤ ((n - 1 : ℕ) : ℝ) / 4 := by
          have : 4 * (m - 1) ≤ n - 1 := by omega
          have : (4 * (m - 1 : ℕ) : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by exact_mod_cast this
          linarith
        have hm_lo' : ((n - 1 : ℕ) : ℝ) / 4 - deltaRaz * ((n - 1 : ℕ) : ℝ) ≤
            ((m - 1 : ℕ) : ℝ) := by
          have h4m : n ≤ 4 * m + 3 := by omega
          have h4mR : (n : ℝ) - 3 ≤ 4 * (m : ℝ) := by
            have : (n : ℝ) ≤ 4 * (m : ℝ) + 3 := by exact_mod_cast h4m
            linarith
          rw [Nat.cast_sub (show 1 ≤ m by omega), Nat.cast_sub (show 1 ≤ n by omega),
            Nat.cast_one]
          have hbig_dn : (8 : ℝ) ≤ deltaRaz * ((n : ℝ) - 1) := by
            rw [hδ_val]
            nlinarith [show (1 / (2 : ℝ) ^ (42 : ℕ)) * ((2 : ℝ) ^ (46 : ℕ) - 1) > 8 by norm_num]
          linarith
        have hraz := razborov_main_four_fifths (n := n - 1) (m := m - 1) (by omega)
          hm_lo' hm_hi' A' B' h0_big
        have hch2 : 2 * n.choose 2 = n * (n - 1) := by
          rw [Nat.choose_two_right]; exact Nat.mul_div_cancel' (Nat.even_mul_pred_self n).two_dvd
        have hch2R : 2 * (n.choose 2 : ℝ) = (n : ℝ) * ((n - 1 : ℕ) : ℝ) := by
          exact_mod_cast hch2
        have hch_pos : (0 : ℝ) < n.choose 2 := Nat.cast_pos.mpr (Nat.choose_pos (by omega))
        have hscale : (((n - 1 : ℕ) : ℝ) / (n.choose 2 : ℝ)) * (n : ℝ) = 2 := by
          field_simp; linarith
        have hratio43 : (4 / 3 : ℝ) * muRect 1 n m A B ≤ muRect 2 n m A B := by
          rw [h2eq]
          calc
            (4 / 3 : ℝ) * muRect 1 n m A B
              ≤ (8 / 5 : ℝ) * muRect 1 n m A B := by linarith [muRect_nonneg 1 n m A B]
            _ = (((n - 1 : ℕ) : ℝ) / (n.choose 2 : ℝ)) *
                  ((4 / 5 : ℝ) * ((n : ℝ) * muRect 1 n m A B)) := by
                rw [show (((n - 1 : ℕ) : ℝ) / (n.choose 2 : ℝ)) *
                    ((4 / 5 : ℝ) * ((n : ℝ) * muRect 1 n m A B)) =
                    (4 / 5 : ℝ) * ((((n - 1 : ℕ) : ℝ) / (n.choose 2 : ℝ)) * (n : ℝ)) *
                      muRect 1 n m A B by ring, hscale]
                ring
            _ = (((n - 1 : ℕ) : ℝ) / (n.choose 2 : ℝ)) *
                  ((4 / 5 : ℝ) * muRect 0 (n - 1) (m - 1) A' B') := by rw [← h0eq]
            _ ≤ (((n - 1 : ℕ) : ℝ) / (n.choose 2 : ℝ)) * muRect 1 (n - 1) (m - 1) A' B' := by
                gcongr
        have h2pos : 0 ≤ (2 : ℝ) ^ (β * (n : ℝ)) := by positivity
        nlinarith
  have hwd := weak_duality_search hW hD
  have hobj : D.obj (1 - ε) 1 = (2 : ℝ) ^ (β * (n : ℝ)) * ((1 - ε) - 3 / 4) := by
    unfold DualSolution.obj
    dsimp only [D]
    have hsum1 : ∑ x : BitString n, ∑ y : BitString n, muWeight 1 n m x y = 1 :=
      sum_muWeight (by omega) (by omega)
    have hsum2 : ∑ x : BitString n, ∑ y : BitString n, muWeight 2 n m x y = 1 :=
      sum_muWeight (by omega) (by omega)
    simp_rw [sum_add_distrib, one_mul]
    have h1 : ∑ x : BitString n, ∑ y : BitString n,
        (1 - ε) * ((2 : ℝ) ^ (β * (n : ℝ)) * muWeight 1 n m x y) =
        (1 - ε) * (2 : ℝ) ^ (β * (n : ℝ)) := by
      simp_rw [← mul_assoc, ← mul_sum, hsum1, mul_one]
    have h2 : ∑ x : BitString n, ∑ y : BitString n,
        (-(3 / 4 : ℝ) * (2 : ℝ) ^ (β * (n : ℝ)) * muWeight 2 n m x y) =
        -(3 / 4 : ℝ) * (2 : ℝ) ^ (β * (n : ℝ)) := by
      simp_rw [← mul_sum, hsum2, mul_one]
    rw [h1, h2]; ring
  rwa [hobj] at hwd

end CslibFrontier.Computability.Communication
