/-
Copyright (c) 2026 The PanMath contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The PanMath contributors
-/
module

public import CslibFrontier.Computability.Complexity.Classes.P
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Pair
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Rat
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Unary
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Probability.Distributions.Gaussian.Real

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Sqrt
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Rat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.Bits
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeLoops
import CslibFrontier.Foundations.Data.Nat.BinarySize
import CslibFrontier.Foundations.Data.Rat.Basic
import CslibFrontier.Foundations.Probability.Gaussian.Real
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.List.GetD
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Exact Rational Orthogonal Projections and Gaussian Distribution Bounds

This module provides polynomial-time exact rational linear algebra and elementary Gaussian
measure inequalities used to reduce high-dimensional Gaussian halfspace conjunctions to
fixed-dimensional rational grid quadrature:

* Exact rational vector sums, inner products, Euclidean embeddings, square-root upper
  approximations, alternating Taylor polynomials for `exp(-t)`, and bounded square-root-free
  rational Gram–Schmidt orthogonalization, each paired with a `ComputableInPolyTime` certificate.
* 1D Gaussian diagonal-scaling TV bound `|(N(0, 1))(S) - (N(0, σ²))(S)| ≤ σ - 1`, product-measure
  TV telescoping, exponential 1D Gaussian tail `Pr[R ≤ |X|] ≤ 2^{-R}`, and product `ℓ¹`
  telescoping for discrete probability weights.

## Main definitions

* `CslibFrontier.Foundations.Probability.Gaussian.ratVecToEuclidean`: embeds a rational list `v :
  List ℚ` into
  `EuclideanSpace ℝ (Fin n)`.
* `CslibFrontier.Foundations.Probability.Gaussian.ratSum`,
  `CslibFrontier.Foundations.Probability.Gaussian.ratDot`: exact rational list sum and inner
  product.
* `CslibFrontier.Foundations.Probability.Gaussian.ratSqrtUpper`: polynomial-time rational upper
  approximation to `√q`.
* `CslibFrontier.Foundations.Probability.Gaussian.ratExpNeg`: common-denominator alternating Taylor
  sum for `exp(-t)`.
* `CslibFrontier.Foundations.Probability.Gaussian.ratProjectStep`,
  `CslibFrontier.Foundations.Probability.Gaussian.ratOrthogonalize`,
  `CslibFrontier.Foundations.Probability.Gaussian.ratGramSchmidtBounded`: exact rational
  Gram–Schmidt orthogonalization of at
  most `d` vectors without square roots.

## Main results

* `CslibFrontier.Foundations.Probability.Gaussian.computableInPolyTime_ratSum`,
  `CslibFrontier.Foundations.Probability.Gaussian.computableInPolyTime_ratDot`,
  `CslibFrontier.Foundations.Probability.Gaussian.computableInPolyTime_ratSqrtUpper`,
  `CslibFrontier.Foundations.Probability.Gaussian.computableInPolyTime_ratExpNeg`,
  `CslibFrontier.Foundations.Probability.Gaussian.computableInPolyTime_ratGramSchmidtBounded`:
  polynomial-time certificates.
* `CslibFrontier.Foundations.Probability.Gaussian.ratSqrtUpper_spec`,
  `CslibFrontier.Foundations.Probability.Gaussian.abs_ratExpNeg_sub_exp_le`,
  `CslibFrontier.Foundations.Probability.Gaussian.ratGramSchmidtBounded_spec`: accuracy and
  orthogonality invariants.
* `CslibFrontier.Foundations.Probability.Gaussian.abs_gaussianReal_sub_scaled_le`,
  `CslibFrontier.Foundations.Probability.Gaussian.abs_pi_measureReal_sub_le`,
  `CslibFrontier.Foundations.Probability.Gaussian.gaussianReal_abs_ge_le_two_pow`,
  `CslibFrontier.Foundations.Probability.Gaussian.sum_abs_prod_sub_le`: Gaussian scaling, tail, and
  product bounds.
-/

public section

open MeasureTheory ProbabilityTheory Real Set Finset BigOperators Turing.MultiTapeTM
open scoped NNReal ENNReal RealInnerProductSpace

namespace CslibFrontier.Foundations.Probability.Gaussian

/-! ### Rational vector embedding, sums, and inner products -/

/-- Embed a rational list `v : List ℚ` into `EuclideanSpace ℝ (Fin n)` by reading coordinates with
zero padding beyond `v.length`. -/
@[expose] noncomputable def ratVecToEuclidean (n : ℕ) (v : List ℚ) :
    EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 fun j : Fin n => ((v.getD j.1 0 : ℚ) : ℝ)

@[simp]
theorem ratVecToEuclidean_apply (n : ℕ) (v : List ℚ) (j : Fin n) :
    (ratVecToEuclidean n v).ofLp j = ((v.getD j.1 0 : ℚ) : ℝ) := rfl

@[simp]
theorem ratVecToEuclidean_nil (n : ℕ) : ratVecToEuclidean n [] = 0 := by
  ext j
  simp [ratVecToEuclidean]

@[simp]
theorem ratVecToEuclidean_zero (v : List ℚ) : ratVecToEuclidean 0 v = 0 := by
  ext j
  exact Fin.elim0 j

/-- Exact rational sum of a list of rationals via a left fold. -/
@[expose] def ratSum (l : List ℚ) : ℚ :=
  l.foldl (· + ·) 0

@[simp]
theorem ratSum_nil : ratSum [] = 0 := rfl

theorem ratSum_eq_sum (l : List ℚ) : ratSum l = l.sum := by
  rw [ratSum, ← List.sum_eq_foldl]

@[simp]
theorem ratSum_cons (a : ℚ) (l : List ℚ) : ratSum (a :: l) = a + ratSum l := by
  simp [ratSum_eq_sum]

/-- Exact rational inner product of two rational vectors `a, b : List ℚ`. -/
@[expose] def ratDot (a b : List ℚ) : ℚ :=
  ratSum ((a.zip b).map fun p => p.1 * p.2)

@[simp]
theorem ratDot_nil_left (b : List ℚ) : ratDot [] b = 0 := rfl

@[simp]
theorem ratDot_nil_right (a : List ℚ) : ratDot a [] = 0 := by
  simp [ratDot]

@[simp]
theorem ratDot_cons (x y : ℚ) (a b : List ℚ) :
    ratDot (x :: a) (y :: b) = x * y + ratDot a b := by
  simp [ratDot]

theorem ratDot_eq_sum_fin {n : ℕ} {a b : List ℚ} (ha : a.length = n) (hb : b.length = n) :
    ratDot a b = ∑ j : Fin n, a.getD j.1 0 * b.getD j.1 0 := by
  induction n generalizing a b with
  | zero =>
    have ha0 : a = [] := List.eq_nil_of_length_eq_zero ha
    have hb0 : b = [] := List.eq_nil_of_length_eq_zero hb
    simp [ha0, hb0]
  | succ n ih =>
    cases a with
    | nil => simp at ha
    | cons x xs =>
      cases b with
      | nil => simp at hb
      | cons y ys =>
        simp only [List.length_cons, Nat.succ.injEq] at ha hb
        rw [ratDot_cons, Fin.sum_univ_succ, ih ha hb]
        simp

theorem ratDot_comm (a b : List ℚ) : ratDot a b = ratDot b a := by
  induction a generalizing b with
  | nil => simp
  | cons x xs ih =>
    cases b with
    | nil => simp
    | cons y ys =>
      rw [ratDot_cons, ratDot_cons, mul_comm, ih]

theorem inner_ratVecToEuclidean_eq_ratDot {n : ℕ} {a b : List ℚ}
    (ha : a.length = n) (hb : b.length = n) :
    ⟪ratVecToEuclidean n a, ratVecToEuclidean n b⟫ = (ratDot a b : ℝ) := by
  rw [PiLp.inner_apply, ratDot_eq_sum_fin ha hb, Rat.cast_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [ratVecToEuclidean_apply, RCLike.inner_apply, conj_trivial, Rat.cast_mul]
  ring

theorem norm_sq_ratVecToEuclidean_eq_ratDot {n : ℕ} {a : List ℚ} (ha : a.length = n) :
    ‖ratVecToEuclidean n a‖ ^ 2 = (ratDot a a : ℝ) := by
  rw [← real_inner_self_eq_norm_sq, inner_ratVecToEuclidean_eq_ratDot ha ha]

theorem ratVecToEuclidean_eq_zero_iff_ratDot {n : ℕ} {a : List ℚ} (ha : a.length = n) :
    ratVecToEuclidean n a = 0 ↔ ratDot a a = 0 := by
  rw [← norm_eq_zero, ← sq_eq_zero_iff (a := ‖ratVecToEuclidean n a‖),
    norm_sq_ratVecToEuclidean_eq_ratDot ha]
  exact_mod_cast Iff.rfl

theorem ratDot_self_nonneg (a : List ℚ) : 0 ≤ ratDot a a := by
  induction a with
  | nil => simp
  | cons x xs ih =>
    rw [ratDot_cons]
    exact add_nonneg (mul_self_nonneg x) ih

private theorem nat_size_add_le_max (a b : ℕ) : (a + b).size ≤ max a.size b.size + 1 := by
  rw [Nat.size_le]
  have ha : a < 2 ^ max a.size b.size :=
    (Nat.lt_size_self a).trans_le (Nat.pow_le_pow_right (by omega) (le_max_left _ _))
  have hb : b < 2 ^ max a.size b.size :=
    (Nat.lt_size_self b).trans_le (Nat.pow_le_pow_right (by omega) (le_max_right _ _))
  rw [pow_succ]
  omega

private theorem ratSize_add_le (a b : ℚ) :
    max (a + b).num.natAbs.size (a + b).den.size ≤
      max a.num.natAbs.size a.den.size + (encRat b).length := by
  have hnum : (a + b).num.natAbs.size ≤
      max a.num.natAbs.size a.den.size + max b.num.natAbs.size b.den.size + 1 := by
    have h1 : (a + b).num.natAbs.size ≤
        max (a.num.natAbs * b.den).size (b.num.natAbs * a.den).size + 1 :=
      (Nat.size_le_size (Rat.natAbs_num_add_le a b)).trans (nat_size_add_le_max _ _)
    have h2 : (a.num.natAbs * b.den).size ≤ a.num.natAbs.size + b.den.size := Nat.size_mul_le _ _
    have h3 : (b.num.natAbs * a.den).size ≤ b.num.natAbs.size + a.den.size := Nat.size_mul_le _ _
    omega
  have hden : (a + b).den.size ≤ a.den.size + b.den.size :=
    (Nat.size_le_size (Rat.den_add_le a b)).trans (Nat.size_mul_le _ _)
  have hb_len := length_encRat b
  omega

private theorem length_encRat_le_of_mem {l : List ℚ} {q : ℚ} (hq : q ∈ l) :
    (encRat q).length ≤ (encList encRat l).length := by
  induction l with
  | nil => simp at hq
  | cons a t ih =>
    simp only [encList_cons, List.length_append, length_frame]
    rcases List.mem_cons.mp hq with rfl | ht
    · omega
    · have := ih ht; omega

/-- Summing a list of rationals is computable in polynomial time. -/
theorem computableInPolyTime_ratSum :
    ComputableInPolyTime ratSum (encList encRat) encRat := by
  let inv : List ℚ → List ℚ → ℚ → Prop := fun l consumed acc =>
    max acc.num.natAbs.size acc.den.size ≤ 1 + consumed.length * (encList encRat l).length
  have hpoly : PolyBounded (fun l : List ℚ => (encList encRat l).length)
      (fun l : List ℚ => 3 * (1 + (encList encRat l).length * (encList encRat l).length) + 3) := by
    refine (PolyBounded.const 3).mul
      ((PolyBounded.const 1).add (PolyBounded.self.mul PolyBounded.self)) |>.add
      (PolyBounded.const 3)
  refine (ComputableInPolyTime.foldl_spec (encIn := encList encRat) (encA := encRat)
    (encB := encRat) (encL := encList encRat)
    (list := id) (init := fun _ => (0 : ℚ)) (step := (· + ·))
    .id' (.const 0) ComputableInPolyTime.rat_add inv ?_ ?_ hpoly ?_).1
  · intro l; simp [inv]
  · intro l consumed acc q hpref hinv
    have hq_mem : q ∈ l := hpref.subset (by simp)
    have hq_len := length_encRat_le_of_mem hq_mem
    have hstep := ratSize_add_le acc q
    simp only [inv, List.length_append, List.length_singleton, Nat.add_mul, Nat.one_mul] at hinv ⊢
    omega
  · intro l consumed acc hpref hinv
    have hlen : consumed.length ≤ (encList encRat l).length :=
      hpref.length_le.trans (SizedListEncoding.length_le (encA := encRat) (encL :=
        encList encRat) l)
    have hmul : consumed.length * (encList encRat l).length ≤
        (encList encRat l).length * (encList encRat l).length := Nat.mul_le_mul_right _ hlen
    rw [length_encRat]; simp only [inv] at hinv; omega

/-- Exact rational inner product is computable in polynomial time. -/
theorem computableInPolyTime_ratDot :
    ComputableInPolyTime (fun p : List ℚ × List ℚ => ratDot p.1 p.2)
      (encPair (encList encRat) (encList encRat)) encRat :=
  (computableInPolyTime_ratSum.comp
    ((ComputableInPolyTime.map ComputableInPolyTime.rat_mul).comp
      (ComputableInPolyTime.zip encRat encRat))).of_enc_eq fun _ => rfl

/-! ### Rational square-root upper approximation -/

/-- Rational upper approximation to `√q` (for `q > 0`, `M ≥ 1`): returns
`(Nat.sqrt (q.num.toNat * q.den * (2 * M)^2) + 1) / (2 * M * q.den)`. -/
@[expose] def ratSqrtUpper (q : ℚ) (M : ℕ) : ℚ :=
  let s : ℕ := Nat.sqrt (q.num.toNat * q.den * (2 * M) ^ 2) + 1
  Rat.divInt (s : ℤ) ((2 * M * q.den : ℕ) : ℤ)

theorem ratSqrtUpper_spec {q : ℚ} (hq : 0 < q) {M : ℕ} (hM : 1 ≤ M) :
    Real.sqrt (q : ℝ) < (ratSqrtUpper q M : ℝ) ∧
      (ratSqrtUpper q M : ℝ) ≤ (1 + 1 / (M : ℝ)) * Real.sqrt (q : ℝ) := by
  have hnum_pos : 0 < q.num := Rat.num_pos.mpr hq
  have hden_pos : 0 < q.den := q.den_pos
  have hp_pos : 0 < q.num.toNat := by omega
  have hp_cast : ((q.num.toNat : ℕ) : ℝ) = (q.num : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hnum_pos.le
  set p : ℕ := q.num.toNat
  set t : ℕ := q.den
  set N : ℕ := p * t * (2 * M) ^ 2
  set s : ℕ := Nat.sqrt N + 1
  have hN_lt : N < s ^ 2 := by
    have := Nat.lt_succ_sqrt N
    simpa [s, sq] using this
  have hsq_le : (Nat.sqrt N) ^ 2 ≤ N := Nat.sqrt_le' N
  have hM_pos : (0 : ℝ) < (M : ℝ) := Nat.cast_pos.mpr hM
  have ht_pos : (0 : ℝ) < (t : ℝ) := Nat.cast_pos.mpr hden_pos
  have hq_rpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hq_eq : (q : ℝ) = (p : ℝ) / (t : ℝ) := by
    rw [Rat.cast_def, ← hp_cast]
  have hden_ne : (2 * (M : ℝ) * (t : ℝ)) ≠ 0 := by positivity
  have hr_eq : (ratSqrtUpper q M : ℝ) = (s : ℝ) / (2 * (M : ℝ) * (t : ℝ)) := by
    unfold ratSqrtUpper
    rw [Rat.cast_divInt]
    push_cast [s, N, p, t]
    ring
  have hsqrt_eq : Real.sqrt (q : ℝ) = Real.sqrt (N : ℝ) / (2 * (M : ℝ) * (t : ℝ)) := by
    have hN_eq : (N : ℝ) = (q : ℝ) * (2 * (M : ℝ) * (t : ℝ)) ^ 2 := by
      rw [hq_eq]
      push_cast [N]
      field_simp [ht_pos.ne']
    rw [hN_eq, Real.sqrt_mul hq_rpos.le, Real.sqrt_sq (by positivity),
      mul_div_cancel_right₀ _ hden_ne]
  constructor
  · rw [hr_eq, hsqrt_eq, div_lt_div_iff_of_pos_right (by positivity)]
    have hN_lt_r : (N : ℝ) < (s : ℝ) ^ 2 := by exact_mod_cast hN_lt
    calc Real.sqrt (N : ℝ) < Real.sqrt ((s : ℝ) ^ 2) :=
          Real.sqrt_lt_sqrt (by positivity) hN_lt_r
      _ = (s : ℝ) := Real.sqrt_sq (by positivity)
  · rw [hr_eq, hsqrt_eq]
    have hsqrt_le : ((Nat.sqrt N : ℕ) : ℝ) ≤ Real.sqrt (N : ℝ) := by
      calc ((Nat.sqrt N : ℕ) : ℝ) = Real.sqrt (((Nat.sqrt N : ℕ) : ℝ) ^ 2) :=
            (Real.sqrt_sq (by positivity)).symm
        _ ≤ Real.sqrt (N : ℝ) := Real.sqrt_le_sqrt (by exact_mod_cast hsq_le)
    have h2M_le : 2 * (M : ℝ) ≤ Real.sqrt (N : ℝ) := by
      have h1 : (2 * (M : ℝ)) ^ 2 ≤ (N : ℝ) := by
        have hpt : (1 : ℝ) ≤ (p : ℝ) * (t : ℝ) := by
          have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp_pos
          have ht1 : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast hden_pos
          nlinarith
        have hN_cast : (N : ℝ) = (p : ℝ) * (t : ℝ) * (2 * (M : ℝ)) ^ 2 := by
          push_cast [N]; ring
        rw [hN_cast]
        nlinarith
      calc 2 * (M : ℝ) = Real.sqrt ((2 * (M : ℝ)) ^ 2) := (Real.sqrt_sq (by positivity)).symm
        _ ≤ Real.sqrt (N : ℝ) := Real.sqrt_le_sqrt h1
    have hM_le_sqrt : (M : ℝ) ≤ Real.sqrt (N : ℝ) := by linarith
    have h1_div : (1 : ℝ) / (2 * (M : ℝ) * (t : ℝ)) ≤
        (1 / (M : ℝ)) * (Real.sqrt (N : ℝ) / (2 * (M : ℝ) * (t : ℝ))) := by
      calc (1 : ℝ) / (2 * (M : ℝ) * (t : ℝ))
          = (1 / (M : ℝ)) * ((M : ℝ) / (2 * (M : ℝ) * (t : ℝ))) := by
            field_simp [hM_pos.ne', ht_pos.ne']
        _ ≤ (1 / (M : ℝ)) * (Real.sqrt (N : ℝ) / (2 * (M : ℝ) * (t : ℝ))) := by
            gcongr
    have hs_cast : (s : ℝ) = ((Nat.sqrt N : ℕ) : ℝ) + 1 := by
      push_cast [s]; ring
    rw [hs_cast, add_div]
    have hfirst : ((Nat.sqrt N : ℕ) : ℝ) / (2 * (M : ℝ) * (t : ℝ)) ≤
        Real.sqrt (N : ℝ) / (2 * (M : ℝ) * (t : ℝ)) := by gcongr
    linarith

/-- `ratSqrtUpper` is computable in polynomial time (with `M` in unary). -/
theorem computableInPolyTime_ratSqrtUpper :
    ComputableInPolyTime (fun p : ℚ × ℕ => ratSqrtUpper p.1 p.2)
      (encPair encRat encUnary) encRat := by
  have hq := ComputableInPolyTime.fst encRat encUnary
  have hM := ComputableInPolyTime.snd encRat encUnary
  have hp : ComputableInPolyTime (fun p : ℚ × ℕ => p.1.num.toNat)
      (encPair encRat encUnary) encNat :=
    ComputableInPolyTime.intBin_toNat.comp (ComputableInPolyTime.rat_num.comp hq)
  have ht : ComputableInPolyTime (fun p : ℚ × ℕ => p.1.den)
      (encPair encRat encUnary) encNat :=
    ComputableInPolyTime.rat_den.comp hq
  have h2M : ComputableInPolyTime (fun p : ℚ × ℕ => 2 * p.2)
      (encPair encRat encUnary) encNat :=
    ComputableInPolyTime.unary_to_binary.comp
      (ComputableInPolyTime.unary_mul' (ComputableInPolyTime.const 2) hM)
  have h2M_sq : ComputableInPolyTime (fun p : ℚ × ℕ => (2 * p.2) ^ 2)
      (encPair encRat encUnary) encNat :=
    ComputableInPolyTime.binary_pow' h2M (ComputableInPolyTime.const 2)
  have hN : ComputableInPolyTime (fun p : ℚ × ℕ => p.1.num.toNat * p.1.den * (2 * p.2) ^ 2)
      (encPair encRat encUnary) encNat :=
    ComputableInPolyTime.binary_mul.comp
      ((ComputableInPolyTime.binary_mul.comp (hp.prod ht)).prod h2M_sq)
  have hs : ComputableInPolyTime
      (fun p : ℚ × ℕ => ((Nat.sqrt (p.1.num.toNat * p.1.den * (2 * p.2) ^ 2) + 1 : ℕ) : ℤ))
      (encPair encRat encUnary) encIntBin :=
    ComputableInPolyTime.intBin_natCast.comp
      (ComputableInPolyTime.binary_add' (ComputableInPolyTime.binary_sqrt' hN)
        (ComputableInPolyTime.const 1))
  have hden : ComputableInPolyTime (fun p : ℚ × ℕ => ((2 * p.2 * p.1.den : ℕ) : ℤ))
      (encPair encRat encUnary) encIntBin :=
    ComputableInPolyTime.intBin_natCast.comp
      (ComputableInPolyTime.binary_mul.comp (h2M.prod ht))
  exact (ComputableInPolyTime.rat_divInt' hs hden).of_enc_eq fun _ => rfl

/-! ### Exact alternating Taylor polynomial for `exp(-t)` -/

/-- Exact common-denominator alternating Taylor sum `∑_{j=0}^K (-t)^j / j!` for `exp(-t)`. -/
@[expose] def ratExpNeg (t : ℚ) (K : ℕ) : ℚ :=
  let D : ℤ := (t.den : ℤ) ^ K * ∏ i ∈ Finset.range K, ((i : ℤ) + 1)
  let N : ℤ := ((List.range (K + 1)).map fun j =>
    (-t.num) ^ j * (t.den : ℤ) ^ (K - j) *
      ∏ i ∈ Finset.range (K - j), ((j : ℤ) + (i : ℤ) + 1)).sum
  Rat.divInt N D

private theorem list_sum_map_range_eq (k : ℕ) (f : ℕ → ℝ) :
    ((List.range k).map f).sum = ∑ i ∈ Finset.range k, f i := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.map_append, List.sum_append, List.map_singleton,
      List.sum_singleton, ih, Finset.sum_range_succ]

private theorem prod_range_add_one_eq_factorial (k : ℕ) :
    (∏ i ∈ Finset.range k, ((i : ℝ) + 1)) = (k.factorial : ℝ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.prod_range_succ, ih, Nat.factorial_succ]
    push_cast
    ring

private theorem factorial_mul_prod_shift (j K : ℕ) (hj : j ≤ K) :
    (j.factorial : ℝ) * (∏ i ∈ Finset.range (K - j), ((j : ℝ) + (i : ℝ) + 1)) =
      (K.factorial : ℝ) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hj
  rw [Nat.add_sub_cancel_left]
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.prod_range_succ, ← mul_assoc, ih (by omega),
      show j + (m + 1) = (j + m).succ by omega, Nat.factorial_succ]
    push_cast
    ring

theorem ratExpNeg_eq_sum (t : ℚ) (K : ℕ) :
    (ratExpNeg t K : ℝ) =
      ∑ j ∈ Finset.range (K + 1), (-(t : ℝ)) ^ j / (j.factorial : ℝ) := by
  unfold ratExpNeg
  rw [Rat.cast_divInt]
  push_cast
  have hD_fac : (∏ i ∈ Finset.range K, ((i : ℝ) + 1)) = (K.factorial : ℝ) :=
    prod_range_add_one_eq_factorial K
  have hden_ne : (t.den : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr t.den_nz
  have hKfac_ne : (K.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero K)
  rw [hD_fac, List.map_map, list_sum_map_range_eq, Finset.sum_div]
  refine Finset.sum_congr rfl fun j hj => ?_
  simp only [Function.comp_apply, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_natCast,
    Int.cast_prod, Int.cast_add, Int.cast_one]
  have hjK : j ≤ K := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have hjfac_ne : (j.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j)
  have hshift := factorial_mul_prod_shift j K hjK
  have hpow : (t.den : ℝ) ^ j * (t.den : ℝ) ^ (K - j) = (t.den : ℝ) ^ K := by
    rw [← pow_add, Nat.add_sub_of_le hjK]
  rw [Rat.cast_def]
  field_simp [hden_ne, hjfac_ne, hKfac_ne]
  have h1 : (-(t.num : ℝ)) ^ j * (t.den : ℝ) ^ (K - j) *
      (∏ i ∈ Finset.range (K - j), ((j : ℝ) + (i : ℝ) + 1)) * (j.factorial : ℝ) =
      (-(t.num : ℝ)) ^ j * (t.den : ℝ) ^ (K - j) *
        ((j.factorial : ℝ) * ∏ i ∈ Finset.range (K - j), ((j : ℝ) + (i : ℝ) + 1)) := by ring
  rw [h1, hshift, ← hpow]
  field_simp [hden_ne]
  have hcancel : (t.den : ℝ) ^ j * (t.den : ℝ)⁻¹ ^ j = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hden_ne, one_pow]
  linear_combination -((t.num : ℝ) ^ j * (-1 : ℝ) ^ j) * hcancel

theorem abs_ratExpNeg_sub_exp_le {t : ℚ} {T B K : ℕ}
    (ht0 : (0 : ℝ) ≤ (t : ℝ)) (htT : (t : ℝ) ≤ (T : ℝ))
    (hK : 3 * T + 2 * B + 2 ≤ K) :
    |(ratExpNeg t K : ℝ) - Real.exp (-(t : ℝ))| ≤ (1 / 4 : ℝ) ^ B := by
  rw [ratExpNeg_eq_sum, abs_sub_comm]
  set n : ℕ := K + 1
  have hcomplex : ‖Complex.exp ((-(t : ℝ) : ℂ)) -
      ∑ j ∈ Finset.range n, ((-(t : ℝ) : ℂ)) ^ j / (j.factorial : ℂ)‖ ≤
      ‖((-(t : ℝ) : ℂ))‖ ^ n / (n.factorial : ℝ) * 2 := by
    refine Complex.exp_bound' ?_
    rw [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0,
      div_le_iff₀ (by positivity)]
    have hn_succ : (2 : ℝ) * (T : ℝ) ≤ (n.succ : ℝ) := by
      have : 2 * T ≤ n.succ := by omega
      exact_mod_cast this
    linarith
  have hreal : |Real.exp (-(t : ℝ)) -
      ∑ j ∈ Finset.range n, (-(t : ℝ)) ^ j / (j.factorial : ℝ)| ≤
      (t : ℝ) ^ n / (n.factorial : ℝ) * 2 := by
    have hcast : Complex.exp ((-(t : ℝ) : ℂ)) -
        ∑ j ∈ Finset.range n, ((-(t : ℝ) : ℂ)) ^ j / (j.factorial : ℂ) =
        (((Real.exp (-(t : ℝ)) -
          ∑ j ∈ Finset.range n, (-(t : ℝ)) ^ j / (j.factorial : ℝ)) : ℝ) : ℂ) := by
      simp [Complex.ofReal_exp]
    rw [hcast, Complex.norm_real, Real.norm_eq_abs] at hcomplex
    simpa [norm_neg, abs_of_nonneg ht0] using hcomplex
  have hsum_le : (2 * (t : ℝ)) ^ n / (n.factorial : ℝ) ≤ Real.exp (2 * (t : ℝ)) := by
    have h := Real.sum_le_exp_of_nonneg (show 0 ≤ 2 * (t : ℝ) by positivity) (n + 1)
    exact (Finset.single_le_sum (f := fun i => (2 * (t : ℝ)) ^ i / (i.factorial : ℝ))
      (fun i _ => by positivity) (Finset.mem_range.mpr (Nat.lt_succ_self n))).trans h
  have hpow_le : (t : ℝ) ^ n / (n.factorial : ℝ) ≤ Real.exp (2 * (t : ℝ)) / (2 : ℝ) ^ n := by
    rw [le_div_iff₀ (by positivity)]
    have : (t : ℝ) ^ n / (n.factorial : ℝ) * (2 : ℝ) ^ n =
        (2 * (t : ℝ)) ^ n / (n.factorial : ℝ) := by rw [mul_pow]; ring
    rw [this]; exact hsum_le
  have hexp2 : Real.exp (2 : ℝ) ≤ (8 : ℝ) := by
    have h1 := Real.exp_one_lt_d9
    have hpos := Real.exp_pos (1 : ℝ)
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    nlinarith
  have hexp2t : Real.exp (2 * (t : ℝ)) ≤ (2 : ℝ) ^ (3 * T) := by
    calc Real.exp (2 * (t : ℝ)) ≤ Real.exp (2 * (T : ℝ)) := Real.exp_le_exp.mpr (by linarith)
      _ = Real.exp ((T : ℕ) * (2 : ℝ)) := by ring_nf
      _ = (Real.exp 2) ^ T := Real.exp_nat_mul 2 T
      _ ≤ (8 : ℝ) ^ T := pow_le_pow_left₀ (Real.exp_pos _).le hexp2 T
      _ = (2 : ℝ) ^ (3 * T) := by rw [show (8 : ℝ) = (2 : ℝ) ^ 3 by norm_num, ← pow_mul]
  have hfinal : (t : ℝ) ^ n / (n.factorial : ℝ) * 2 ≤ (1 / 4 : ℝ) ^ B := by
    have hpow_split : (2 : ℝ) ^ (3 * T + 2 * B + 1) =
        (2 : ℝ) ^ (3 * T + 1) * (2 : ℝ) ^ (2 * B) := by
      rw [← pow_add]; congr 1; omega
    calc (t : ℝ) ^ n / (n.factorial : ℝ) * 2
        ≤ (Real.exp (2 * (t : ℝ)) / (2 : ℝ) ^ n) * 2 := by gcongr
      _ ≤ ((2 : ℝ) ^ (3 * T) / (2 : ℝ) ^ n) * 2 := by gcongr
      _ = (2 : ℝ) ^ (3 * T + 1) / (2 : ℝ) ^ n := by rw [pow_succ]; ring
      _ ≤ (2 : ℝ) ^ (3 * T + 1) / (2 : ℝ) ^ (3 * T + 2 * B + 1) := by
          gcongr
          · norm_num
          · omega
      _ = (1 / 4 : ℝ) ^ B := by
          rw [hpow_split, div_mul_eq_div_div, div_self (by positivity), one_div,
            show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, one_div, inv_pow, ← pow_mul]
  exact hreal.trans hfinal

private theorem computableInPolyTime_ratExpNegTerm :
    ComputableInPolyTime
      (fun x : (ℚ × ℕ) × ℕ =>
        (-x.1.1.num) ^ x.2 * (x.1.1.den : ℤ) ^ (x.1.2 - x.2) *
          ∏ i ∈ Finset.range (x.1.2 - x.2), ((x.2 : ℤ) + (i : ℤ) + 1))
      (encPair (encPair encRat encUnary) encUnary) encIntBin := by
  let eIn := encPair encRat encUnary
  let e2 := encPair eIn encUnary
  have hx1 := ComputableInPolyTime.fst eIn encUnary
  have hj := ComputableInPolyTime.snd eIn encUnary
  have ht := (ComputableInPolyTime.fst encRat encUnary).comp hx1
  have hK := (ComputableInPolyTime.snd encRat encUnary).comp hx1
  have hsub := ComputableInPolyTime.unary_sub' hK hj
  have hnegnum := ComputableInPolyTime.intBin_neg.comp (ComputableInPolyTime.rat_num.comp ht)
  have htden := ComputableInPolyTime.intBin_natCast.comp (ComputableInPolyTime.rat_den.comp ht)
  have hpow1 := ComputableInPolyTime.intBin_pow' hnegnum hj
  have hpow2 := ComputableInPolyTime.intBin_pow' htden hsub
  have hshift_fn : ComputableInPolyTime
      (fun y : ((ℚ × ℕ) × ℕ) × ℕ => ((y.1.2 : ℤ) + (y.2 : ℤ) + 1))
      (encPair e2 encUnary) encIntBin :=
    (ComputableInPolyTime.intBin_add'
      (ComputableInPolyTime.intBin_add'
        (ComputableInPolyTime.intBin_natCast_unary.comp
          (hj.comp (ComputableInPolyTime.fst e2 encUnary)))
        (ComputableInPolyTime.intBin_natCast_unary.comp
          (ComputableInPolyTime.snd e2 encUnary)))
      (ComputableInPolyTime.const 1)).of_enc_eq fun _ => rfl
  have hprod := ComputableInPolyTime.intBin_prod_range hshift_fn hsub
  exact (ComputableInPolyTime.intBin_mul'
    (ComputableInPolyTime.intBin_mul' hpow1 hpow2) hprod).of_enc_eq fun _ => rfl

/-- `ratExpNeg` is computable in polynomial time (with `K` in unary). -/
theorem computableInPolyTime_ratExpNeg :
    ComputableInPolyTime (fun p : ℚ × ℕ => ratExpNeg p.1 p.2)
      (encPair encRat encUnary) encRat := by
  let eIn := encPair encRat encUnary
  have ht := ComputableInPolyTime.fst encRat encUnary
  have hK := ComputableInPolyTime.snd encRat encUnary
  have htden := ComputableInPolyTime.intBin_natCast.comp (ComputableInPolyTime.rat_den.comp ht)
  have hDfac := ComputableInPolyTime.intBin_prod_range
    ((ComputableInPolyTime.intBin_add'
      (ComputableInPolyTime.intBin_natCast_unary.comp (ComputableInPolyTime.snd eIn encUnary))
      (ComputableInPolyTime.const 1)).of_enc_eq fun _ => rfl)
    hK
  have hD := ComputableInPolyTime.intBin_mul' (ComputableInPolyTime.intBin_pow' htden hK) hDfac
  have hrange := ComputableInPolyTime.range.comp
    (ComputableInPolyTime.unary_add' hK (ComputableInPolyTime.const 1))
  have hN := ComputableInPolyTime.intBin_sum.comp
    (ComputableInPolyTime.mapWithInput (f := fun p j =>
        (-p.1.num) ^ j * (p.1.den : ℤ) ^ (p.2 - j) *
          ∏ i ∈ Finset.range (p.2 - j), ((j : ℤ) + (i : ℤ) + 1))
      hrange computableInPolyTime_ratExpNegTerm)
  exact (ComputableInPolyTime.rat_divInt' hN hD).of_enc_eq fun _ => rfl

/-! ### Exact rational Gram–Schmidt orthogonalization -/

/-- Single projection step removing the component of `v` along `e`:
`v - (ratDot v e / ratDot e e) • e` (leaving `v` unchanged if `ratDot e e = 0`). -/
@[expose] def ratProjectStep (v e : List ℚ) : List ℚ :=
  let denom := ratDot e e
  if denom = 0 then v
  else
    let coeff := ratDot v e / denom
    (v.zip e).map fun p => p.1 - coeff * p.2

/-- Apply `ratProjectStep` against the first `k` vectors in `basis`. -/
@[expose] def ratOrthogonalize : ℕ → List (List ℚ) → List ℚ → List ℚ
  | 0, _, v => v
  | _ + 1, [], v => v
  | k + 1, e :: es, v => ratOrthogonalize k es (ratProjectStep v e)

/-- Exact rational Gram–Schmidt orthogonalization of the first `d` vectors of `vecs`,
producing a list of at most `d` pairwise orthogonal nonzero rational vectors with the same span. -/
@[expose] def ratGramSchmidtBounded : ℕ → List (List ℚ) → List (List ℚ)
  | 0, _ => []
  | _ + 1, [] => []
  | d + 1, v :: vs =>
    let basis := ratGramSchmidtBounded d vs
    let u := ratOrthogonalize d basis v
    if ratDot u u = 0 then basis else u :: basis

@[simp]
theorem ratGramSchmidtBounded_zero (vecs : List (List ℚ)) :
    ratGramSchmidtBounded 0 vecs = [] := rfl

@[simp]
theorem ratGramSchmidtBounded_nil (d : ℕ) :
    ratGramSchmidtBounded d [] = [] := by
  cases d <;> rfl

theorem ratGramSchmidtBounded_length_le (d : ℕ) (vecs : List (List ℚ)) :
    (ratGramSchmidtBounded d vecs).length ≤ d := by
  induction d generalizing vecs with
  | zero => simp
  | succ d ih =>
    cases vecs with
    | nil => simp
    | cons v vs =>
      simp only [ratGramSchmidtBounded]
      split_ifs
      · exact (ih vs).trans (Nat.le_succ d)
      · exact Nat.succ_le_succ (ih vs)

private theorem ratProjectStep_length {N : ℕ} {v e : List ℚ}
    (hv : v.length = N) (he : e.length = N) :
    (ratProjectStep v e).length = N := by
  unfold ratProjectStep
  dsimp only
  split_ifs
  · exact hv
  · simp [hv, he]

private theorem ratProjectStep_vec {N : ℕ} {v e : List ℚ}
    (hv : v.length = N) (he : e.length = N) :
    ratVecToEuclidean N (ratProjectStep v e) =
      if ratDot e e = 0 then ratVecToEuclidean N v
      else ratVecToEuclidean N v -
        ((ratDot v e / ratDot e e : ℚ) : ℝ) • ratVecToEuclidean N e := by
  unfold ratProjectStep
  dsimp only
  split_ifs with h0
  · rfl
  · ext j
    simp only [ratVecToEuclidean_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
    have hj : j.1 < (v.zip e).length := by simp [hv, he]
    have hget : ((v.zip e).map fun p => p.1 - ratDot v e / ratDot e e * p.2).getD j.1 0 =
        v.getD j.1 0 - ratDot v e / ratDot e e * e.getD j.1 0 := by
      rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map, List.getElem_zip,
        ← List.getD_eq_getElem _ 0 (hv ▸ j.2), ← List.getD_eq_getElem _ 0 (he ▸ j.2)]
    rw [hget]
    push_cast
    rfl

private theorem ratOrthogonalize_spec {N : ℕ} (k : ℕ) (basis : List (List ℚ))
    (hk : basis.length ≤ k) (hlen : ∀ e ∈ basis, e.length = N)
    (hne : ∀ e ∈ basis, ratDot e e ≠ 0)
    (horth : basis.Pairwise fun e₁ e₂ => ⟪ratVecToEuclidean N e₁, ratVecToEuclidean N e₂⟫ = 0)
    (v : List ℚ) (hv : v.length = N) :
    (ratOrthogonalize k basis v).length = N ∧
    (∀ e ∈ basis, ⟪ratVecToEuclidean N (ratOrthogonalize k basis v),
        ratVecToEuclidean N e⟫ = 0) ∧
    ratVecToEuclidean N v - ratVecToEuclidean N (ratOrthogonalize k basis v) ∈
      Submodule.span ℝ (Set.range fun i : Fin basis.length =>
        ratVecToEuclidean N basis[i]) := by
  induction k generalizing basis v with
  | zero =>
    have hb : basis = [] := List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero hk)
    subst hb
    exact ⟨hv, by simp [ratOrthogonalize], by simp [ratOrthogonalize]⟩
  | succ k ih =>
    cases basis with
    | nil => exact ⟨hv, by simp [ratOrthogonalize], by simp [ratOrthogonalize]⟩
    | cons e₀ es =>
      simp only [List.length_cons, Nat.succ_le_succ_iff] at hk
      simp only [List.pairwise_cons] at horth
      have he_len : e₀.length = N := hlen e₀ List.mem_cons_self
      have he_ne : ratDot e₀ e₀ ≠ 0 := hne e₀ List.mem_cons_self
      have hv'_len : (ratProjectStep v e₀).length = N := ratProjectStep_length hv he_len
      obtain ⟨hulen, huorth, huspan⟩ := ih es hk
        (fun x hx => hlen x (List.mem_cons_of_mem e₀ hx))
        (fun x hx => hne x (List.mem_cons_of_mem e₀ hx))
        horth.2 (ratProjectStep v e₀) hv'_len
      simp only [ratOrthogonalize]
      refine ⟨hulen, ?_, ?_⟩
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hxes
        · have hstep_orth : ⟪ratVecToEuclidean N (ratProjectStep v x),
              ratVecToEuclidean N x⟫ = 0 := by
            rw [ratProjectStep_vec hv he_len]
            simp only [he_ne, ↓reduceIte]
            rw [inner_sub_left, inner_smul_left,
              inner_ratVecToEuclidean_eq_ratDot hv he_len,
              inner_ratVecToEuclidean_eq_ratDot he_len he_len]
            have hne_r : (ratDot x x : ℝ) ≠ 0 := by exact_mod_cast he_ne
            simp only [RCLike.conj_to_real]
            push_cast
            field_simp [hne_r]
            ring
          have hdiff_orth :
              ⟪ratVecToEuclidean N (ratProjectStep v x) -
                  ratVecToEuclidean N (ratOrthogonalize k es (ratProjectStep v x)),
                ratVecToEuclidean N x⟫ = 0 := by
            refine Submodule.span_induction (p := fun w _ => ⟪w, ratVecToEuclidean N x⟫ = 0)
              ?_ (by simp) (fun a b _ _ ha hb => by rw [inner_add_left, ha, hb, add_zero])
              (fun r a _ ha => by rw [inner_smul_left, ha, mul_zero]) huspan
            rintro _ ⟨i, rfl⟩
            rw [real_inner_comm]
            exact horth.1 _ (List.getElem_mem _)
          have hsub0 : ⟪ratVecToEuclidean N (ratProjectStep v x), ratVecToEuclidean N x⟫ -
              ⟪ratVecToEuclidean N (ratOrthogonalize k es (ratProjectStep v x)),
                ratVecToEuclidean N x⟫ = 0 := by
            rw [← inner_sub_left, hdiff_orth]
          linarith
        · exact huorth x hxes
      · have hspan_mono : Submodule.span ℝ (Set.range fun i : Fin es.length =>
            ratVecToEuclidean N es[i]) ≤
            Submodule.span ℝ (Set.range fun i : Fin (e₀ :: es).length =>
              ratVecToEuclidean N (e₀ :: es)[i]) := by
          refine Submodule.span_mono ?_
          rintro _ ⟨i, rfl⟩
          exact ⟨i.succ, rfl⟩
        have hstep_mem : ratVecToEuclidean N v - ratVecToEuclidean N (ratProjectStep v e₀) ∈
            Submodule.span ℝ (Set.range fun i : Fin (e₀ :: es).length =>
              ratVecToEuclidean N (e₀ :: es)[i]) := by
          rw [ratProjectStep_vec hv he_len]
          simp only [he_ne, ↓reduceIte, sub_sub_cancel]
          exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨0, Nat.succ_pos _⟩, rfl⟩)
        have hsum := Submodule.add_mem _ hstep_mem (hspan_mono huspan)
        simpa only [sub_add_sub_cancel] using hsum

/-- Full invariant of `ratGramSchmidtBounded d vecs`: length `≤ d`, pairwise orthogonal nonzero
rational basis vectors of length `N`,
  and exact orthogonal projection formula for every `v ∈ vecs`. -/
theorem ratGramSchmidtBounded_spec {N d : ℕ} {vecs : List (List ℚ)}
    (hlen_vecs : vecs.length ≤ d) (hv_len : ∀ v ∈ vecs, v.length = N) :
    let basis := ratGramSchmidtBounded d vecs
    basis.length ≤ d ∧
    (∀ e ∈ basis, e.length = N ∧ ratDot e e ≠ 0) ∧
    (basis.Pairwise fun e₁ e₂ => ⟪ratVecToEuclidean N e₁, ratVecToEuclidean N e₂⟫ = 0) ∧
    ∀ v ∈ vecs, ratVecToEuclidean N v =
      ∑ s : Fin basis.length,
        ((ratDot v basis[s] / ratDot basis[s] basis[s] : ℚ) : ℝ) •
          ratVecToEuclidean N basis[s] := by
  have hmain : ∀ (d : ℕ) (vecs : List (List ℚ)),
      vecs.length ≤ d → (∀ v ∈ vecs, v.length = N) →
      (ratGramSchmidtBounded d vecs).length ≤ d ∧
      (∀ e ∈ ratGramSchmidtBounded d vecs, e.length = N ∧ ratDot e e ≠ 0) ∧
      ((ratGramSchmidtBounded d vecs).Pairwise fun e₁ e₂ =>
        ⟪ratVecToEuclidean N e₁, ratVecToEuclidean N e₂⟫ = 0) ∧
      ∀ v ∈ vecs, ratVecToEuclidean N v ∈
        Submodule.span ℝ (Set.range fun i : Fin (ratGramSchmidtBounded d vecs).length =>
          ratVecToEuclidean N (ratGramSchmidtBounded d vecs)[i]) := by
    intro d
    induction d with
    | zero =>
      intro vecs hlen _
      have hnil : vecs = [] := List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero hlen)
      subst hnil
      exact ⟨le_rfl, by simp, by simp, by simp⟩
    | succ d ih =>
      intro vecs hlen hv
      cases vecs with
      | nil => exact ⟨Nat.zero_le _, by simp, by simp, by simp⟩
      | cons v vs =>
        simp only [List.length_cons, Nat.succ_le_succ_iff] at hlen
        obtain ⟨hb_len, hb_info, hb_orth, hb_span⟩ :=
          ih vs hlen (fun x hx => hv x (List.mem_cons_of_mem v hx))
        set basis := ratGramSchmidtBounded d vs
        set u := ratOrthogonalize d basis v
        obtain ⟨hu_len, hu_orth, hu_span⟩ := ratOrthogonalize_spec d basis hb_len
          (fun e he => (hb_info e he).1) (fun e he => (hb_info e he).2) hb_orth v
          (hv v List.mem_cons_self)
        let P : List (List ℚ) → Prop := fun res =>
          res.length ≤ d + 1 ∧
          (∀ e ∈ res, e.length = N ∧ ratDot e e ≠ 0) ∧
          (res.Pairwise fun e₁ e₂ => ⟪ratVecToEuclidean N e₁, ratVecToEuclidean N e₂⟫ = 0) ∧
          ∀ x ∈ v :: vs, ratVecToEuclidean N x ∈
            Submodule.span ℝ (Set.range fun i : Fin res.length => ratVecToEuclidean N res[i])
        change P (ratGramSchmidtBounded (d + 1) (v :: vs))
        have hdef : ratGramSchmidtBounded (d + 1) (v :: vs) =
            if ratDot u u = 0 then basis else u :: basis := rfl
        by_cases hu0 : ratDot u u = 0
        · simp only [hu0, ↓reduceIte] at hdef
          rw [hdef]
          refine ⟨hb_len.trans (Nat.le_succ d), hb_info, hb_orth, fun x hx => ?_⟩
          rcases List.mem_cons.mp hx with rfl | hxvs
          · have hu_zero : ratVecToEuclidean N u = 0 :=
              (ratVecToEuclidean_eq_zero_iff_ratDot hu_len).mpr hu0
            rw [hu_zero, sub_zero] at hu_span
            exact hu_span
          · exact hb_span x hxvs
        · simp only [hu0, ↓reduceIte] at hdef
          rw [hdef]
          refine ⟨Nat.succ_le_succ hb_len, ?_, ?_, fun x hx => ?_⟩
          · intro e he
            rcases List.mem_cons.mp he with rfl | heb
            · exact ⟨hu_len, hu0⟩
            · exact hb_info e heb
          · exact List.pairwise_cons.mpr ⟨hu_orth, hb_orth⟩
          · have hmono : Submodule.span ℝ (Set.range fun i : Fin basis.length =>
                ratVecToEuclidean N basis[i]) ≤
                Submodule.span ℝ (Set.range fun i : Fin (u :: basis).length =>
                  ratVecToEuclidean N (u :: basis)[i]) := by
              refine Submodule.span_mono ?_
              rintro _ ⟨i, rfl⟩
              exact ⟨i.succ, rfl⟩
            rcases List.mem_cons.mp hx with rfl | hxvs
            · have hu_mem : ratVecToEuclidean N u ∈
                  Submodule.span ℝ (Set.range fun i : Fin (u :: basis).length =>
                    ratVecToEuclidean N (u :: basis)[i]) :=
                Submodule.subset_span ⟨⟨0, Nat.succ_pos _⟩, rfl⟩
              have hsum := Submodule.add_mem _ (hmono hu_span) hu_mem
              simpa only [u, sub_add_cancel] using hsum
            · exact hmono (hb_span x hxvs)
  obtain ⟨hb_len, hb_info, hb_orth, hb_span⟩ := hmain d vecs hlen_vecs hv_len
  refine ⟨hb_len, hb_info, hb_orth, fun v hv => ?_⟩
  set basis := ratGramSchmidtBounded d vecs
  have hmem := hb_span v hv
  have hpairwise : Pairwise fun i j : Fin basis.length =>
      ⟪ratVecToEuclidean N basis[i], ratVecToEuclidean N basis[j]⟫ = 0 := by
    intro i j hij
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · exact List.pairwise_iff_getElem.mp hb_orth i.1 j.1 i.2 j.2 hlt
    · rw [real_inner_comm]
      exact List.pairwise_iff_getElem.mp hb_orth j.1 i.1 j.2 i.2 hgt
  rw [Submodule.mem_span_range_iff_exists_fun] at hmem
  obtain ⟨c, hc⟩ := hmem
  rw [← hc]
  refine Finset.sum_congr rfl fun s _ => ?_
  congr 1
  have hs_info := hb_info basis[s] (List.getElem_mem s.2)
  have hinner : ⟪∑ i : Fin basis.length, c i • ratVecToEuclidean N basis[i],
      ratVecToEuclidean N basis[s]⟫ = c s * (ratDot basis[s] basis[s] : ℝ) := by
    rw [sum_inner]
    rw [Finset.sum_eq_single s]
    · rw [real_inner_smul_left, inner_ratVecToEuclidean_eq_ratDot hs_info.1 hs_info.1]
    · intro i _ his
      rw [real_inner_smul_left, hpairwise his, mul_zero]
    · intro hs'; exact absurd (Finset.mem_univ s) hs'
  have hdot_eq : (ratDot v basis[s] : ℝ) = c s * (ratDot basis[s] basis[s] : ℝ) := by
    rw [← inner_ratVecToEuclidean_eq_ratDot (hv_len v hv) hs_info.1, ← hc, hinner]
  have hne_r : (ratDot basis[s] basis[s] : ℝ) ≠ 0 := by exact_mod_cast hs_info.2
  push_cast
  rw [hdot_eq, mul_div_cancel_right₀ _ hne_r]

private theorem computableInPolyTime_ratProjectStep :
    ComputableInPolyTime (fun p : List ℚ × List ℚ => ratProjectStep p.1 p.2)
      (encPair (encList encRat) (encList encRat)) (encList encRat) := by
  have hv := ComputableInPolyTime.fst (encList encRat) (encList encRat)
  have he := ComputableInPolyTime.snd (encList encRat) (encList encRat)
  have hdenom := computableInPolyTime_ratDot.comp (he.prod he)
  have hcond := ComputableInPolyTime.rat_eq' hdenom (ComputableInPolyTime.const (0 : ℚ))
  have hcoeff :=
    ComputableInPolyTime.rat_div' (computableInPolyTime_ratDot.comp (hv.prod he)) hdenom
  have hzip := (ComputableInPolyTime.zip encRat encRat).comp (hv.prod he)
  have hmap := ComputableInPolyTime.mapWith
    (ComputableInPolyTime.rat_sub'
      ((ComputableInPolyTime.fst encRat encRat).comp (ComputableInPolyTime.snd encRat _))
      (ComputableInPolyTime.rat_mul'
        (ComputableInPolyTime.fst encRat (encPair encRat encRat))
        ((ComputableInPolyTime.snd encRat encRat).comp (ComputableInPolyTime.snd encRat _))))
    hcoeff hzip
  exact (hcond.ite' hv hmap).of_enc_eq fun p => congrArg (encList encRat) (by
    simp only [ratProjectStep, Function.comp_apply, decide_eq_true_eq])

private theorem computableInPolyTime_ratOrthogonalize (k : ℕ) :
    ComputableInPolyTime (fun p : List (List ℚ) × List ℚ => ratOrthogonalize k p.1 p.2)
      (encPair (encList (encList encRat)) (encList encRat)) (encList encRat) := by
  induction k with
  | zero =>
    exact (ComputableInPolyTime.snd (encList (encList encRat)) (encList encRat)).of_enc_eq
      fun _ => rfl
  | succ k ih =>
    have hb := ComputableInPolyTime.fst (encList (encList encRat)) (encList encRat)
    have hv := ComputableInPolyTime.snd (encList (encList encRat)) (encList encRat)
    have hempty := (ComputableInPolyTime.listIsEmpty' (encList encRat)).comp hb
    have hhead := (ComputableInPolyTime.headD (encA := encList encRat)
      (encL := encList (encList encRat)) []).comp hb
    have htail := (ComputableInPolyTime.listTail (encList encRat)).comp hb
    have hstep := computableInPolyTime_ratProjectStep.comp (hv.prod hhead)
    have hrec := ih.comp (htail.prod hstep)
    refine (hempty.ite' hv hrec).of_enc_eq fun p => congrArg (encList encRat) ?_
    rcases p with ⟨b, v⟩
    cases b <;> simp [ratOrthogonalize]

/-- `ratGramSchmidtBounded d` is computable in polynomial time for every fixed constant `d`. -/
theorem computableInPolyTime_ratGramSchmidtBounded (d : ℕ) :
    ComputableInPolyTime (ratGramSchmidtBounded d)
      (encList (encList encRat)) (encList (encList encRat)) := by
  induction d with
  | zero => exact (ComputableInPolyTime.const []).of_enc_eq fun _ => rfl
  | succ d ih =>
    have hempty := ComputableInPolyTime.listIsEmpty' (encList encRat)
    have hv := ComputableInPolyTime.headD (encA := encList encRat)
      (encL := encList (encList encRat)) []
    have hvs := ComputableInPolyTime.listTail (encList encRat)
    have hbasis := ih.comp hvs
    have hu := (computableInPolyTime_ratOrthogonalize d).comp (hbasis.prod hv)
    have hcond := ComputableInPolyTime.rat_eq'
      (computableInPolyTime_ratDot.comp (hu.prod hu)) (ComputableInPolyTime.const (0 : ℚ))
    have hcons := (ComputableInPolyTime.cons (encList encRat)).comp (hu.prod hbasis)
    refine (hempty.ite' (ComputableInPolyTime.const []) (hcond.ite' hbasis hcons)).of_enc_eq
      fun vecs => congrArg (encList (encList encRat)) ?_
    cases vecs <;> simp [ratGramSchmidtBounded]

/-! ### Gaussian diagonal-scaling TV bound, product telescoping, and exponential tail -/

/-- **1D Gaussian diagonal-scaling TV bound**: for `σ ≥ 1`, `N(0, 1)` and `N(0, σ²)` differ on
every measurable set by at most `1 - 1 / σ ≤ σ - 1`. -/
theorem abs_gaussianReal_sub_scaled_le {σ : ℝ} (hσ : 1 ≤ σ) {S : Set ℝ} (hS : MeasurableSet S) :
    |(gaussianReal 0 1).real S -
      (gaussianReal 0 ⟨σ ^ 2, sq_nonneg σ⟩).real S| ≤ σ - 1 := by
  have hσ_pos : 0 < σ := by linarith
  set v : ℝ≥0 := ⟨σ ^ 2, sq_nonneg σ⟩
  have hv_ne : v ≠ 0 := by
    intro h
    have : σ ^ 2 = 0 := congrArg NNReal.toReal h
    nlinarith
  have hpdf_le : ∀ x : ℝ, gaussianPDFReal 0 1 x - gaussianPDFReal 0 v x ≤
      (1 - σ⁻¹) * gaussianPDFReal 0 1 x := by
    intro x
    have h1 : σ⁻¹ * gaussianPDFReal 0 1 x ≤ gaussianPDFReal 0 v x := by
      simp only [gaussianPDFReal_def, sub_zero, NNReal.coe_one, mul_one]
      have hv_coe : (v : ℝ) = σ ^ 2 := rfl
      rw [hv_coe, Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2 * Real.pi), Real.sqrt_sq hσ_pos.le,
        mul_inv_rev, ← mul_assoc]
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
      rw [neg_div, neg_div, neg_le_neg_iff]
      have hsq : (1 : ℝ) ≤ σ ^ 2 := by nlinarith
      have : x ^ 2 / (2 * σ ^ 2) ≤ x ^ 2 / 2 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith [sq_nonneg x]
      simpa [mul_comm] using this
    linarith
  have hone_side : ∀ {T : Set ℝ}, MeasurableSet T →
      (gaussianReal 0 1).real T - (gaussianReal 0 v).real T ≤ 1 - σ⁻¹ := fun {T} hT => by
    rw [Measure.real_def, Measure.real_def,
      gaussianReal_apply_eq_integral 0 one_ne_zero,
      gaussianReal_apply_eq_integral 0 hv_ne,
      ENNReal.toReal_ofReal (integral_nonneg fun x => gaussianPDFReal_nonneg _ _ x),
      ENNReal.toReal_ofReal (integral_nonneg fun x => gaussianPDFReal_nonneg _ _ x),
      ← integral_sub (integrable_gaussianPDFReal 0 1).integrableOn
        (integrable_gaussianPDFReal 0 v).integrableOn]
    calc ∫ x in T, (gaussianPDFReal 0 1 x - gaussianPDFReal 0 v x)
        ≤ ∫ x in T, (1 - σ⁻¹) * gaussianPDFReal 0 1 x :=
          setIntegral_mono_on
            ((integrable_gaussianPDFReal 0 1).sub (integrable_gaussianPDFReal 0 v)).integrableOn
            ((integrable_gaussianPDFReal 0 1).const_mul (1 - σ⁻¹)).integrableOn hT
            (fun x _ => hpdf_le x)
      _ = (1 - σ⁻¹) * ∫ x in T, gaussianPDFReal 0 1 x := integral_const_mul _ _
      _ ≤ (1 - σ⁻¹) * ∫ x, gaussianPDFReal 0 1 x := by
          refine mul_le_mul_of_nonneg_left ?_ (sub_nonneg.mpr (inv_le_one_of_one_le₀ hσ))
          exact setIntegral_le_integral (integrable_gaussianPDFReal 0 1)
            (ae_of_all _ fun x => gaussianPDFReal_nonneg _ _ x)
      _ = 1 - σ⁻¹ := by rw [integral_gaussianPDFReal_eq_one 0 one_ne_zero, mul_one]
  have hcompl : (gaussianReal 0 v).real S - (gaussianReal 0 1).real S =
      (gaussianReal 0 1).real Sᶜ - (gaussianReal 0 v).real Sᶜ := by
    have h1 := measureReal_compl (μ := gaussianReal 0 1) hS
    have h2 := measureReal_compl (μ := gaussianReal 0 v) hS
    simp only [Measure.real_def, measure_univ, ENNReal.toReal_one] at h1 h2
    rw [Measure.real_def, Measure.real_def, Measure.real_def, Measure.real_def]
    linarith
  have h1m : 1 - σ⁻¹ ≤ σ - 1 := by
    have : 0 ≤ (σ - 1) ^ 2 / σ := by positivity
    have hdiff : (σ - 1) - (1 - σ⁻¹) = (σ - 1) ^ 2 / σ := by field_simp [hσ_pos.ne']
    linarith
  rw [abs_le]
  exact ⟨by linarith [hone_side hS.compl], (hone_side hS).trans h1m⟩

/-- Product-measure total-variation telescoping bound: if `|μ_s.real S - ν_s.real S| ≤ τ` for all
measurable `S ⊆ ℝ` and all `s : Fin k`, then `|(Measure.pi μ).real A - (Measure.pi ν).real A| ≤`
`k * τ` for all measurable `A ⊆ Fin k → ℝ`. -/
theorem abs_pi_measureReal_sub_le : ∀ {k : ℕ} {μ ν : Fin k → Measure ℝ}
    [∀ s, IsProbabilityMeasure (μ s)] [∀ s, IsProbabilityMeasure (ν s)]
    {τ : ℝ}, 0 ≤ τ →
    (∀ (s : Fin k) {S : Set ℝ}, MeasurableSet S → |(μ s).real S - (ν s).real S| ≤ τ) →
    ∀ {A : Set (Fin k → ℝ)}, MeasurableSet A →
    |(Measure.pi μ).real A - (Measure.pi ν).real A| ≤ (k : ℝ) * τ := by
  intro k
  induction k with
  | zero =>
    intro μ ν _ _ τ _ _ A _
    classical
    have hμ : (Measure.pi μ).real A = if Fin.elim0 ∈ A then 1 else 0 := by
      split_ifs with h
      · have hA_eq : A = Set.univ := Set.eq_univ_of_forall fun f =>
          Subsingleton.elim f Fin.elim0 ▸ h
        simp [hA_eq]
      · have hA_eq : A = ∅ := Set.eq_empty_of_forall_notMem fun f hf =>
          h (Subsingleton.elim f Fin.elim0 ▸ hf)
        simp [hA_eq]
    have hν : (Measure.pi ν).real A = if Fin.elim0 ∈ A then 1 else 0 := by
      split_ifs with h
      · have hA_eq : A = Set.univ := Set.eq_univ_of_forall fun f =>
          Subsingleton.elim f Fin.elim0 ▸ h
        simp [hA_eq]
      · have hA_eq : A = ∅ := Set.eq_empty_of_forall_notMem fun f hf =>
          h (Subsingleton.elim f Fin.elim0 ▸ hf)
        simp [hA_eq]
    simp [hμ, hν]
  | succ k ih =>
    intro μ ν _ _ τ hτ hstep A hA
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => ℝ) 0
    let μ' : Fin k → Measure ℝ := fun j => μ (Fin.succAbove 0 j)
    let ν' : Fin k → Measure ℝ := fun j => ν (Fin.succAbove 0 j)
    have hmp_μ := MeasureTheory.measurePreserving_piFinSuccAbove μ 0
    have hmp_ν := MeasureTheory.measurePreserving_piFinSuccAbove ν 0
    let B : Set (ℝ × (Fin k → ℝ)) := e.symm ⁻¹' A
    have hB : MeasurableSet B := e.symm.measurable hA
    have hA_μ : (Measure.pi μ).real A = ((μ 0).prod (Measure.pi μ')).real B := by
      rw [← hmp_μ.measureReal_preimage hB.nullMeasurableSet]
      congr 1
      ext x
      simp [B, e]
    have hA_ν : (Measure.pi ν).real A = ((ν 0).prod (Measure.pi ν')).real B := by
      rw [← hmp_ν.measureReal_preimage hB.nullMeasurableSet]
      congr 1
      ext x
      simp [B, e]
    have hprod_int : ∀ (m₁ : Measure ℝ) (m₂ : Measure (Fin k → ℝ))
        [IsProbabilityMeasure m₁] [IsProbabilityMeasure m₂],
        (m₁.prod m₂).real B = ∫ x, m₂.real (Prod.mk x ⁻¹' B) ∂m₁ := fun m₁ m₂ _ _ => by
      have hm : Measurable fun x => m₂ (Prod.mk x ⁻¹' B) := measurable_measure_prodMk_left hB
      have hreal_m : Measurable fun x => m₂.real (Prod.mk x ⁻¹' B) := hm.ennreal_toReal
      rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun _ => measureReal_nonneg)
        hreal_m.aestronglyMeasurable, Measure.real_def, Measure.prod_apply hB]
      congr 1
      refine lintegral_congr fun x => ?_
      rw [Measure.real_def, ENNReal.ofReal_toReal (measure_ne_top m₂ _)]
    have hterm1 : |((μ 0).prod (Measure.pi μ')).real B -
        ((μ 0).prod (Measure.pi ν')).real B| ≤ (k : ℝ) * τ := by
      rw [hprod_int, hprod_int, ← integral_sub]
      · calc |∫ x, ((Measure.pi μ').real (Prod.mk x ⁻¹' B) -
              (Measure.pi ν').real (Prod.mk x ⁻¹' B)) ∂(μ 0)|
            ≤ ∫ x, |(Measure.pi μ').real (Prod.mk x ⁻¹' B) -
                (Measure.pi ν').real (Prod.mk x ⁻¹' B)| ∂(μ 0) :=
              abs_integral_le_integral_abs
          _ ≤ ∫ _ : ℝ, (k : ℝ) * τ ∂(μ 0) := by
              refine integral_mono_of_nonneg (ae_of_all _ fun _ => abs_nonneg _)
                (integrable_const _) (ae_of_all _ fun x => ?_)
              exact ih hτ (fun j S hS => hstep (Fin.succAbove 0 j) hS) (measurable_prodMk_left hB)
          _ = (k : ℝ) * τ := by simp
      · exact Integrable.of_bound
          (measurable_measure_prodMk_left hB).ennreal_toReal.aestronglyMeasurable
          1 (ae_of_all _ fun x => by
            rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]; exact measureReal_le_one)
      · exact Integrable.of_bound
          (measurable_measure_prodMk_left hB).ennreal_toReal.aestronglyMeasurable
          1 (ae_of_all _ fun x => by
            rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]; exact measureReal_le_one)
    have hprod_symm : ∀ (m₁ : Measure ℝ) (m₂ : Measure (Fin k → ℝ))
        [IsProbabilityMeasure m₁] [IsProbabilityMeasure m₂],
        (m₁.prod m₂).real B = ∫ y, m₁.real ((fun x => (x, y)) ⁻¹' B) ∂m₂ := fun m₁ m₂ _ _ => by
      have hm : Measurable fun y => m₁ ((fun x => (x, y)) ⁻¹' B) :=
        measurable_measure_prodMk_right hB
      have hreal_m : Measurable fun y => m₁.real ((fun x => (x, y)) ⁻¹' B) := hm.ennreal_toReal
      rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun _ => measureReal_nonneg)
        hreal_m.aestronglyMeasurable, Measure.real_def, Measure.prod_apply_symm hB]
      congr 1
      refine lintegral_congr fun y => ?_
      rw [Measure.real_def, ENNReal.ofReal_toReal (measure_ne_top m₁ _)]
    have hterm2 : |((μ 0).prod (Measure.pi ν')).real B -
        ((ν 0).prod (Measure.pi ν')).real B| ≤ τ := by
      rw [hprod_symm, hprod_symm, ← integral_sub]
      · calc |∫ y, ((μ 0).real ((fun x => (x, y)) ⁻¹' B) -
              (ν 0).real ((fun x => (x, y)) ⁻¹' B)) ∂(Measure.pi ν')|
            ≤ ∫ y, |(μ 0).real ((fun x => (x, y)) ⁻¹' B) -
                (ν 0).real ((fun x => (x, y)) ⁻¹' B)| ∂(Measure.pi ν') :=
              abs_integral_le_integral_abs
          _ ≤ ∫ _ : Fin k → ℝ, τ ∂(Measure.pi ν') := by
              refine integral_mono_of_nonneg (ae_of_all _ fun _ => abs_nonneg _)
                (integrable_const _) (ae_of_all _ fun y => ?_)
              exact hstep 0 (measurable_prodMk_right hB)
          _ = τ := by simp
      · exact Integrable.of_bound
          (measurable_measure_prodMk_right hB).ennreal_toReal.aestronglyMeasurable
          1 (ae_of_all _ fun y => by
            rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]; exact measureReal_le_one)
      · exact Integrable.of_bound
          (measurable_measure_prodMk_right hB).ennreal_toReal.aestronglyMeasurable
          1 (ae_of_all _ fun y => by
            rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]; exact measureReal_le_one)
    rw [hA_μ, hA_ν, Nat.cast_succ, add_mul, one_mul]
    calc |((μ 0).prod (Measure.pi μ')).real B - ((ν 0).prod (Measure.pi ν')).real B|
        ≤ |((μ 0).prod (Measure.pi μ')).real B - ((μ 0).prod (Measure.pi ν')).real B| +
          |((μ 0).prod (Measure.pi ν')).real B - ((ν 0).prod (Measure.pi ν')).real B| :=
          abs_sub_le _ _ _
      _ ≤ (k : ℝ) * τ + τ := add_le_add hterm1 hterm2

/-- Exponential 1D standard Gaussian tail: for `R ≥ 2`, `Pr_{X ~ N(0,1)}[R ≤ |X|] ≤ 2^{-R}`. -/
theorem gaussianReal_abs_ge_le_two_pow {R : ℕ} (hR : 2 ≤ R) :
    (gaussianReal 0 1).real {x : ℝ | (R : ℝ) ≤ |x|} ≤ 1 / (2 : ℝ) ^ R := by
  have hderiv : ∀ x : ℝ, HasDerivAt (fun t : ℝ => -((1 / 2 : ℝ) * Real.exp (2 - 2 * t)))
      (Real.exp (2 - 2 * x)) x := fun x => by
    have hd1 : HasDerivAt (fun t : ℝ => (2 : ℝ) - 2 * t) (-2) x := by
      have h0 : HasDerivAt (fun t : ℝ => (2 : ℝ) + (-2) * t) (0 + (-2) * 1) x :=
        (hasDerivAt_const x (2 : ℝ)).add ((hasDerivAt_id x).const_mul (-2 : ℝ))
      convert h0 using 1
      · funext t; ring
      · ring
    convert ((hd1.exp.const_mul (1 / 2 : ℝ)).neg) using 1
    ring
  have htend : Filter.Tendsto (fun x : ℝ => -((1 / 2 : ℝ) * Real.exp (2 - 2 * x)))
      Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun x : ℝ => 2 - 2 * x) Filter.atTop Filter.atBot :=
      Filter.tendsto_atBot.mpr fun b =>
        Filter.eventually_atTop.mpr ⟨(2 - b) / 2, fun x hx => by linarith⟩
    have h2 := (Real.tendsto_exp_atBot.comp h1).const_mul (1 / 2 : ℝ)
    simpa using h2.neg
  have hright : (gaussianReal 0 1).real (Ioi (R : ℝ)) ≤ (1 / 2 : ℝ) * (1 / (2 : ℝ) ^ R) := by
    rw [Measure.real_def, gaussianReal_apply_eq_integral 0 one_ne_zero,
      ENNReal.toReal_ofReal (integral_nonneg fun x => gaussianPDFReal_nonneg _ _ x)]
    have hdom : ∀ x ∈ Ioi (R : ℝ), gaussianPDFReal 0 1 x ≤ Real.exp (2 - 2 * x) := fun x _ => by
      simp only [gaussianPDFReal_def, sub_zero, NNReal.coe_one, mul_one]
      have hsqrt_ge : (1 : ℝ) ≤ Real.sqrt (2 * Real.pi) := by
        have : (1 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
        simpa using Real.sqrt_le_sqrt this
      have hinv_le : (Real.sqrt (2 * Real.pi))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hsqrt_ge
      have hexp_le : Real.exp (-(x ^ 2) / 2) ≤ Real.exp (2 - 2 * x) :=
        Real.exp_le_exp.mpr (by nlinarith [sq_nonneg (x - 2)])
      calc (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(x ^ 2) / 2)
          ≤ 1 * Real.exp (2 - 2 * x) :=
            mul_le_mul hinv_le hexp_le (Real.exp_pos _).le (by positivity)
        _ = Real.exp (2 - 2 * x) := one_mul _
    have hint_exp : ∫ x in Ioi (R : ℝ), Real.exp (2 - 2 * x) =
        (1 / 2 : ℝ) * Real.exp (2 - 2 * (R : ℝ)) := by
      have hg := MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg
        (a := (R : ℝ)) (l := 0) (g := fun x => -((1 / 2 : ℝ) * Real.exp (2 - 2 * x)))
        (g' := fun x => Real.exp (2 - 2 * x))
        (by fun_prop) (fun x _ => hderiv x) (fun x _ => (Real.exp_pos _).le) htend
      simpa using hg
    have hint_on : IntegrableOn (fun x => Real.exp (2 - 2 * x)) (Ioi (R : ℝ)) :=
      integrableOn_Ioi_deriv_of_nonneg (a := (R : ℝ)) (l := 0)
        (g := fun x => -((1 / 2 : ℝ) * Real.exp (2 - 2 * x)))
        (g' := fun x => Real.exp (2 - 2 * x))
        (by fun_prop) (fun x _ => hderiv x) (fun x _ => (Real.exp_pos _).le) htend
    calc ∫ x in Ioi (R : ℝ), gaussianPDFReal 0 1 x
        ≤ ∫ x in Ioi (R : ℝ), Real.exp (2 - 2 * x) :=
          setIntegral_mono_on (integrable_gaussianPDFReal 0 1).integrableOn hint_on
            measurableSet_Ioi hdom
      _ = (1 / 2 : ℝ) * Real.exp (2 - 2 * (R : ℝ)) := hint_exp
      _ ≤ (1 / 2 : ℝ) * Real.exp (-(R : ℝ)) := by
          gcongr
          have : (2 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
          linarith
      _ ≤ (1 / 2 : ℝ) * (1 / (2 : ℝ) ^ R) := by
          gcongr
          rw [Real.exp_neg, one_div]
          refine inv_anti₀ (by positivity) ?_
          have h2e : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
          calc (2 : ℝ) ^ R ≤ (Real.exp 1) ^ R := pow_le_pow_left₀ (by norm_num) h2e R
            _ = Real.exp ((R : ℕ) * (1 : ℝ)) := (Real.exp_nat_mul 1 R).symm
            _ = Real.exp (R : ℝ) := by ring_nf
  have hsingle : (gaussianReal 0 1).real {x : ℝ | (R : ℝ) ≤ x} =
      (gaussianReal 0 1).real (Ioi (R : ℝ)) := by
    have hdiff : {x : ℝ | (R : ℝ) ≤ x} = Ioi (R : ℝ) ∪ {(R : ℝ)} := by
      ext x; simp [le_iff_lt_or_eq, or_comm, eq_comm]
    have hpt0 : (gaussianReal 0 1).real {(R : ℝ)} = 0 := by
      simp [Measure.real_def, gaussianReal_apply_eq_integral 0 one_ne_zero]
    rw [hdiff, measureReal_union (by simp) (measurableSet_singleton _), hpt0, add_zero]
  have hneg : (gaussianReal 0 1).real {x : ℝ | (R : ℝ) ≤ -x} =
      (gaussianReal 0 1).real {x : ℝ | (R : ℝ) ≤ x} := by
    have hsym := gaussianReal_zero_map_neg (1 : ℝ≥0)
    have hpre : (fun x : ℝ => -x) ⁻¹' Set.Ici (R : ℝ) = {x : ℝ | (R : ℝ) ≤ -x} := rfl
    have hici : Set.Ici (R : ℝ) = {x : ℝ | (R : ℝ) ≤ x} := rfl
    rw [Measure.real_def, Measure.real_def, ← hpre, ← hici,
      ← Measure.map_apply measurable_neg measurableSet_Ici, hsym]
  have hsub : {x : ℝ | (R : ℝ) ≤ |x|} ⊆ {x : ℝ | (R : ℝ) ≤ x} ∪ {x : ℝ | (R : ℝ) ≤ -x} := by
    intro x hx
    rcases le_or_gt 0 x with h0 | h0
    · left; simpa [abs_of_nonneg h0] using hx
    · right; simpa [abs_of_neg h0] using hx
  calc (gaussianReal 0 1).real {x : ℝ | (R : ℝ) ≤ |x|}
      ≤ (gaussianReal 0 1).real ({x : ℝ | (R : ℝ) ≤ x} ∪ {x : ℝ | (R : ℝ) ≤ -x}) :=
        measureReal_mono hsub
    _ ≤ (gaussianReal 0 1).real {x : ℝ | (R : ℝ) ≤ x} +
        (gaussianReal 0 1).real {x : ℝ | (R : ℝ) ≤ -x} := measureReal_union_le _ _
    _ = 2 * (gaussianReal 0 1).real (Ioi (R : ℝ)) := by rw [hneg, hsingle]; ring
    _ ≤ 2 * ((1 / 2 : ℝ) * (1 / (2 : ℝ) ^ R)) := by gcongr
    _ = 1 / (2 : ℝ) ^ R := by ring

/-- Product `ℓ¹` telescoping: for nonnegative weight functions `p, q : Fin G → ℝ` summing to at
most `1`, the `k`-fold product weights satisfy `∑_z |∏ p(z_s) - ∏ q(z_s)| ≤ k * ∑_m |p m - q m|`. -/
theorem sum_abs_prod_sub_le {G : ℕ} : ∀ (k : ℕ) {p q : Fin G → ℝ},
    (∀ m, 0 ≤ p m) → (∀ m, 0 ≤ q m) →
    (∑ m, p m ≤ 1) → (∑ m, q m ≤ 1) →
    (∑ z : Fin k → Fin G, |∏ s : Fin k, p (z s) - ∏ s : Fin k, q (z s)|) ≤
      (k : ℝ) * ∑ m : Fin G, |p m - q m| := by
  intro k
  induction k with
  | zero => intro p q _ _ _ _; simp
  | succ k ih =>
    intro p q hp hq hp1 hq1
    let e := (Fin.consEquiv (fun _ : Fin (k + 1) => Fin G)).symm
    rw [← Equiv.sum_comp e.symm]
    have hsplit : ∀ x : Fin G × (Fin k → Fin G),
        |∏ s : Fin (k + 1), p (e.symm x s) - ∏ s : Fin (k + 1), q (e.symm x s)| ≤
          |p x.1 - q x.1| * (∏ s : Fin k, p (x.2 s)) +
          q x.1 * |∏ s : Fin k, p (x.2 s) - ∏ s : Fin k, q (x.2 s)| := fun ⟨m, z⟩ => by
      simp only [e, Equiv.symm_symm, Fin.prod_univ_succ, Fin.consEquiv_apply, Fin.cons_zero,
        Fin.cons_succ]
      have hrewrite : p m * ∏ s, p (z s) - q m * ∏ s, q (z s) =
          (p m - q m) * ∏ s, p (z s) + q m * (∏ s, p (z s) - ∏ s, q (z s)) := by ring
      rw [hrewrite]
      calc |(p m - q m) * ∏ s, p (z s) + q m * (∏ s, p (z s) - ∏ s, q (z s))|
          ≤ |(p m - q m) * ∏ s, p (z s)| + |q m * (∏ s, p (z s) - ∏ s, q (z s))| :=
            abs_add_le _ _
        _ = |p m - q m| * ∏ s, p (z s) + q m * |∏ s, p (z s) - ∏ s, q (z s)| := by
            rw [abs_mul, abs_mul, abs_of_nonneg (Finset.prod_nonneg fun _ _ => hp _),
              abs_of_nonneg (hq m)]
    calc ∑ x : Fin G × (Fin k → Fin G),
            |∏ s : Fin (k + 1), p (e.symm x s) - ∏ s : Fin (k + 1), q (e.symm x s)|
        ≤ ∑ x : Fin G × (Fin k → Fin G),
            (|p x.1 - q x.1| * ∏ s : Fin k, p (x.2 s) +
              q x.1 * |∏ s : Fin k, p (x.2 s) - ∏ s : Fin k, q (x.2 s)|) :=
          Finset.sum_le_sum fun x _ => hsplit x
      _ = (∑ m : Fin G, |p m - q m|) * (∑ z : Fin k → Fin G, ∏ s : Fin k, p (z s)) +
          (∑ m : Fin G, q m) *
            (∑ z : Fin k → Fin G, |∏ s : Fin k, p (z s) - ∏ s : Fin k, q (z s)|) := by
          rw [Finset.sum_add_distrib, Fintype.sum_prod_type, Fintype.sum_prod_type]
          congr 1
          · rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun m _ => by dsimp only; exact (Finset.mul_sum _ _ _).symm
          · rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun m _ => by dsimp only; exact (Finset.mul_sum _ _ _).symm
      _ ≤ (∑ m : Fin G, |p m - q m|) * 1 + 1 * ((k : ℝ) * ∑ m : Fin G, |p m - q m|) := by
          have hprod_p : ∑ z : Fin k → Fin G, ∏ s : Fin k, p (z s) = (∑ m : Fin G, p m) ^ k :=
            (Fintype.sum_pow (fun m => p m) k).symm
          have hprod_le1 : ∑ z : Fin k → Fin G, ∏ s : Fin k, p (z s) ≤ 1 := by
            rw [hprod_p]
            exact pow_le_one₀ (Finset.sum_nonneg fun m _ => hp m) hp1
          have hsum_abs_nn : 0 ≤ ∑ m : Fin G, |p m - q m| :=
            Finset.sum_nonneg fun m _ => abs_nonneg _
          have hih := ih hp hq hp1 hq1
          have hprod_diff_nn : 0 ≤ ∑ z : Fin k → Fin G, |∏ s, p (z s) - ∏ s, q (z s)| :=
            Finset.sum_nonneg fun _ _ => abs_nonneg _
          gcongr
      _ = ((k + 1 : ℕ) : ℝ) * ∑ m : Fin G, |p m - q m| := by push_cast; ring

end CslibFrontier.Foundations.Probability.Gaussian
