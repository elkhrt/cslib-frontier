module

public import CslibFrontier.Foundations.Data.Code.FiniteFieldFourier
public import CslibFrontier.Foundations.Combinatorics.Expander.AffineFamily
public import CslibFrontier.Foundations.Combinatorics.Expander.Walk
public import CslibFrontier.Foundations.Data.Code.Justesen
public import CslibFrontier.Foundations.FieldTheory.Finite.BinaryField
public import CslibFrontier.Foundations.FieldTheory.Finite.Coordinates
public import Mathlib.Data.Finset.Card
public import Mathlib.LinearAlgebra.Matrix.ToLin

import CslibFrontier.Foundations.Combinatorics.Expander.Mixing
import CslibFrontier.Foundations.Data.Finset.Expect
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Expander-Walk Parity Sampling and Explicit Small-Bias Binary Linear Codes

This module formalizes three reusable components of explicit small-bias coding theory and
derandomization:

1. **Expander-walk parity sampling**: for any `D`-regular rotation map `G` with spectral
   expansion `λ` and any `±1` function `s : V → ℝ` with `|𝔼 s| ≤ 1 - δ`, the two-step signed walk
   operator `T f = G.walk (s * G.walk f)` contracts the second moment by at most
   `(1 - δ)² + 2 λ²`, yielding
   `|𝔼_{walk of length 2t} ∏_{j < t} s(v_{2j+1})| ≤ ((1 - δ)² + 2 λ²)^{t/2}`.
2. **Explicit linear-length `η`-biased binary linear codes**:
   composing zero-padded Justesen codes (`Cslib.Code.justesenCode`) with parity sampling along
   walks on a constant power of `Cslib.RotationMap.arithmeticExpander` yields an explicit
   binary linear code of dimension `k`, length `m = O(k · η^{-C})`, and bias at most `η`, together
   with a uniform polynomial-time row evaluator.
3. **Combinatorial unranking of `n`-subsets**: a computable bijection `unrankSubset m n` from
   `Fin (m.choose n)` to `n`-subsets of `Fin m`, certified `ComputableInPolyTime`, paired with an
   `IsPPTOn` approximate uniform `n`-subset sampler using `⌈log₂ C(m, n)⌉ + n` fair bits with
   total-variation error at most `2⁻ⁿ`.

All results are proved under standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`).

## Main definitions

* `CslibFrontier.Foundations.Data.Code.walkSignStep`: the signed two-step walk operator
  `f ↦ G.walk (s * G.walk f)`.
* `CslibFrontier.Foundations.Data.Code.justesenScale`,
  `CslibFrontier.Foundations.Data.Code.paddedJustesenLen`,
  `CslibFrontier.Foundations.Data.Code.paddedJustesenMap`: zero-padded explicit binary Justesen code
  of dimension `k` and length `O(k)` with relative weights in `[1/256, 1/2]`.
* `CslibFrontier.Foundations.Data.Code.abnnrExpanderPow`,
  `CslibFrontier.Foundations.Data.Code.abnnrLen`,
  `CslibFrontier.Foundations.Data.Code.abnnrGenMap`: explicit `η`-biased binary linear code.
* `CslibFrontier.Foundations.Data.Code.unrankSubset`,
  `CslibFrontier.Foundations.Data.Code.unrankSubsetEquiv`,
  `CslibFrontier.Foundations.Data.Code.sampleSubsetProgram`: combinatorial unranking and PPT
  sampling of `n`-subsets of `Fin m`.
* `CslibFrontier.Foundations.Data.Code.abnnrRowEval`: polynomial-time executable row evaluator for
  the generator matrix.

## Main results

* `CslibFrontier.Foundations.Data.Code.expect_walkSignStep_sq_le`
* `CslibFrontier.Foundations.Data.Code.abs_expect_walk_parity_le`
* `CslibFrontier.Foundations.Data.Code.isVectorBiased_abnnrGenMap`
* `CslibFrontier.Foundations.Data.Code.abnnrLen_le`
* `CslibFrontier.Foundations.Data.Code.computableInPolyTime_unrankSubset`
* `CslibFrontier.Foundations.Data.Code.isPPTOn_sampleSubsetProgram`
* `CslibFrontier.Foundations.Data.Code.dist_eval_sampleSubsetProgram_le`
* `CslibFrontier.Foundations.Data.Code.computableInPolyTime_abnnrRowEval`

## Tags

small-bias space, expander walk, ABNNR, Justesen code, combinatorial unranking, derandomization
-/

public section

namespace CslibFrontier.Foundations.Data.Code

open Finset Cslib.Probability
open scoped BigOperators

/-! ### Part 1: Expander-walk parity sampling -/

section ExpanderParity

variable {V D : Type*} [Fintype V] [Fintype D]

/-- The signed two-step walk operator `f ↦ G.walk (fun v ↦ s v * G.walk f v)`. -/
noncomputable def walkSignStep (G : Cslib.RotationMap V D) (s : V → ℝ) :
    (V → ℝ) →ₗ[ℝ] (V → ℝ) where
  toFun f := G.walk (fun v ↦ s v * G.walk f v)
  map_add' f g := by
    have hmul : (fun v ↦ s v * G.walk (f + g) v) =
        (fun v ↦ s v * G.walk f v) + (fun v ↦ s v * G.walk g v) := by
      ext v; simp [map_add, mul_add]
    rw [hmul, map_add]
  map_smul' c f := by
    have hmul : (fun v ↦ s v * G.walk (c • f) v) =
        c • (fun v ↦ s v * G.walk f v) := by
      ext v; simp [map_smul, smul_eq_mul]; ring
    rw [hmul, map_smul]; rfl

omit [Fintype V] in
theorem walkSignStep_apply (G : Cslib.RotationMap V D) (s : V → ℝ) (f : V → ℝ) (v : V) :
    walkSignStep G s f v = G.walk (fun w ↦ s w * G.walk f w) v := by rfl

private lemma expect_sub_mean_sq [Nonempty V] (h : V → ℝ) :
    𝔼 v, (h v - 𝔼 w, h w) ^ 2 = (𝔼 v, h v ^ 2) - (𝔼 w, h w) ^ 2 := by
  have h1 : 𝔼 v, (h v - 𝔼 w, h w) ^ 2 =
      (𝔼 v, h v ^ 2) - 2 * (𝔼 w, h w) * (𝔼 v, h v) + (𝔼 w, h w) ^ 2 := by
    have hexp : (fun v ↦ (h v - 𝔼 w, h w) ^ 2) =
        fun v ↦ h v ^ 2 - 2 * (𝔼 w, h w) * h v + (𝔼 w, h w) ^ 2 := by
      ext v; ring
    rw [hexp, expect_add_distrib, expect_sub_distrib, Fintype.expect_const, ← mul_expect]
  linarith

/-- Second-moment contraction of the signed two-step walk operator `walkSignStep`. -/
theorem expect_walkSignStep_sq_le [Nonempty V] [Nonempty D]
    (G : Cslib.RotationMap V D) {s : V → ℝ} (hs : ∀ v, s v ^ 2 = 1)
    {δ : ℝ} (_hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hmean : |𝔼 v, s v| ≤ 1 - δ) (f : V → ℝ) :
    𝔼 v, walkSignStep G s f v ^ 2 ≤
      ((1 - δ) ^ 2 + 2 * G.spectralExpansion ^ 2) * 𝔼 v, f v ^ 2 := by
  set lam := G.spectralExpansion
  have hlam0 : 0 ≤ lam := G.spectralExpansion_nonneg
  have hlam1 : lam ≤ 1 := G.spectralExpansion_le_one
  set g : V → ℝ := G.walk f
  set h : V → ℝ := fun v ↦ s v * g v
  set d : ℝ := 𝔼 v, h v
  have hwalk_h : 𝔼 v, G.walk h v = d := G.expect_walk h
  have hvar := G.expect_walk_pow_sub_expect_sq_le 1 h
  simp only [pow_one, mul_one] at hvar
  have hL : 𝔼 v, (G.walk h v - d) ^ 2 = (𝔼 v, G.walk h v ^ 2) - d ^ 2 := by
    have := expect_sub_mean_sq (G.walk h)
    rwa [hwalk_h] at this
  have hR : 𝔼 v, (h v - d) ^ 2 = (𝔼 v, h v ^ 2) - d ^ 2 := expect_sub_mean_sq h
  rw [hL, hR] at hvar
  have hsq_h : 𝔼 v, h v ^ 2 = 𝔼 v, g v ^ 2 := by
    refine expect_congr rfl fun v _ ↦ ?_
    simp only [h, mul_pow, hs v, one_mul]
  have hsq_g : 𝔼 v, g v ^ 2 ≤ 𝔼 v, f v ^ 2 := G.expect_walk_sq_le f
  have hstep1 : 𝔼 v, G.walk h v ^ 2 ≤ (1 - lam ^ 2) * d ^ 2 + lam ^ 2 * 𝔼 v, f v ^ 2 := by
    have h1 : 𝔼 v, G.walk h v ^ 2 ≤ (1 - lam ^ 2) * d ^ 2 + lam ^ 2 * 𝔼 v, h v ^ 2 := by
      linarith
    rw [hsq_h] at h1
    nlinarith [sq_nonneg lam]
  have hmix := G.sq_expect_mul_walk_pow_sub_le 1 s f
  simp only [pow_one, mul_one] at hmix
  have hEs2 : 𝔼 v, s v ^ 2 = 1 := by simp only [hs, Fintype.expect_const]
  rw [hEs2] at hmix
  set a := 𝔼 v, s v
  set b := 𝔼 v, f v
  set E := 𝔼 v, f v ^ 2
  have hE_nonneg : 0 ≤ E := expect_nonneg fun v _ ↦ sq_nonneg (f v)
  have hb_le_E : b ^ 2 ≤ E := by
    have := expect_sub_mean_sq f
    have hnn : 0 ≤ 𝔼 v, (f v - b) ^ 2 := expect_nonneg fun v _ ↦ sq_nonneg _
    linarith
  have ha_sq : a ^ 2 ≤ (1 - δ) ^ 2 :=
    sq_le_sq.mpr (by rwa [abs_of_nonneg (by linarith : 0 ≤ 1 - δ)])
  have h1a : 1 - a ^ 2 ≤ 1 := by linarith [sq_nonneg a]
  have hmix' : (d - a * b) ^ 2 ≤ lam ^ 2 * (E - b ^ 2) := by
    have hnn1 : 0 ≤ E - b ^ 2 := sub_nonneg.mpr hb_le_E
    have hle : lam ^ 2 * (1 - a ^ 2) * (E - b ^ 2) ≤ lam ^ 2 * 1 * (E - b ^ 2) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1a (sq_nonneg lam)) hnn1
    linarith
  have hd_sq : d ^ 2 ≤ ((1 - δ) ^ 2 + lam ^ 2) * E := by
    set r := Real.sqrt (E - b ^ 2)
    have hr_sq : r ^ 2 = E - b ^ 2 := Real.sq_sqrt (sub_nonneg.mpr hb_le_E)
    have hr_nn : 0 ≤ r := Real.sqrt_nonneg _
    have hdiff_abs : |d - a * b| ≤ lam * r := by
      have hsq_r : (d - a * b) ^ 2 ≤ (lam * r) ^ 2 := by rw [mul_pow, hr_sq]; exact hmix'
      have := sq_le_sq.mp hsq_r
      rwa [abs_of_nonneg (mul_nonneg hlam0 hr_nn)] at this
    have hd_abs : |d| ≤ |a| * |b| + lam * r := by
      calc |d| = |(d - a * b) + a * b| := by ring_nf
        _ ≤ |d - a * b| + |a * b| := abs_add_le _ _
        _ = |a| * |b| + |d - a * b| := by rw [abs_mul, add_comm]
        _ ≤ |a| * |b| + lam * r := by linarith
    have hcs : d ^ 2 ≤ (a ^ 2 + lam ^ 2) * E := by
      have hd2 : d ^ 2 ≤ (|a| * |b| + lam * r) ^ 2 := by
        have h1 : |d| ^ 2 ≤ (|a| * |b| + lam * r) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg d) hd_abs 2
        rwa [sq_abs] at h1
      have hlag : (|a| * |b| + lam * r) ^ 2 ≤ (a ^ 2 + lam ^ 2) * (b ^ 2 + r ^ 2) := by
        nlinarith [sq_nonneg (|a| * r - lam * |b|), sq_abs a, sq_abs b]
      rw [hr_sq] at hlag
      have hbr : b ^ 2 + (E - b ^ 2) = E := by ring
      rw [hbr] at hlag
      exact hd2.trans hlag
    exact hcs.trans (mul_le_mul_of_nonneg_right (by linarith) hE_nonneg)
  have h1lam_le1 : 1 - lam ^ 2 ≤ 1 := by linarith [sq_nonneg lam]
  have hstep2 : (1 - lam ^ 2) * d ^ 2 ≤ ((1 - δ) ^ 2 + lam ^ 2) * E := by
    calc (1 - lam ^ 2) * d ^ 2
        ≤ 1 * d ^ 2 := mul_le_mul_of_nonneg_right h1lam_le1 (sq_nonneg d)
      _ = d ^ 2 := one_mul _
      _ ≤ ((1 - δ) ^ 2 + lam ^ 2) * E := hd_sq
  change 𝔼 v, G.walk h v ^ 2 ≤ ((1 - δ) ^ 2 + 2 * lam ^ 2) * E
  linarith

/-- Iterated second-moment bound for `walkSignStep` starting from the constant `1` function. -/
theorem expect_walkSignStep_pow_one_sq_le [Nonempty V] [Nonempty D]
    (G : Cslib.RotationMap V D) {s : V → ℝ} (hs : ∀ v, s v ^ 2 = 1)
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hmean : |𝔼 v, s v| ≤ 1 - δ) (t : ℕ) :
    𝔼 v, ((walkSignStep G s) ^ t) (fun _ ↦ 1) v ^ 2 ≤
      ((1 - δ) ^ 2 + 2 * G.spectralExpansion ^ 2) ^ t := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [pow_succ', mul_apply_eq_comp]
    have hstep := expect_walkSignStep_sq_le G hs hδ0 hδ1 hmean
      (((walkSignStep G s) ^ t) (fun _ ↦ 1))
    have hc : 0 ≤ (1 - δ) ^ 2 + 2 * G.spectralExpansion ^ 2 := by positivity
    calc 𝔼 v, walkSignStep G s (((walkSignStep G s) ^ t) (fun _ ↦ 1)) v ^ 2
        ≤ ((1 - δ) ^ 2 + 2 * G.spectralExpansion ^ 2) *
            𝔼 v, ((walkSignStep G s) ^ t) (fun _ ↦ 1) v ^ 2 := hstep
      _ ≤ ((1 - δ) ^ 2 + 2 * G.spectralExpansion ^ 2) *
            ((1 - δ) ^ 2 + 2 * G.spectralExpansion ^ 2) ^ t :=
          mul_le_mul_of_nonneg_left ih hc
      _ = ((1 - δ) ^ 2 + 2 * G.spectralExpansion ^ 2) ^ (t + 1) := (pow_succ' _ t).symm

omit [Fintype V] in
/-- Explicit random-walk representation of `((walkSignStep G s) ^ t) 1`. -/
theorem walkSignStep_pow_one_eq_expect (G : Cslib.RotationMap V D) (s : V → ℝ) (t : ℕ) (v : V) :
    ((walkSignStep G s) ^ t) (fun _ ↦ 1) v =
      𝔼 k : Fin (2 * t) → D, ∏ j : Fin t, s (G.walkAt (v, k) (2 * j.val + 1)) := by
  induction t generalizing v with
  | zero => simp
  | succ t ih =>
    rw [pow_succ', mul_apply_eq_comp, walkSignStep_apply, G.walk_apply]
    simp_rw [G.walk_apply, ih]
    let hsplit : (Fin (2 * (t + 1)) → D) ≃ D × (D × (Fin (2 * t) → D)) :=
      (Equiv.arrowCongr (finCongr (show 2 * (t + 1) = (2 * t + 1) + 1 by omega))
        (Equiv.refl D)).trans
        ((Fin.consEquiv fun _ : Fin ((2 * t + 1) + 1) ↦ D).symm.trans
          (Equiv.prodCongr (Equiv.refl D) (Fin.consEquiv fun _ : Fin (2 * t + 1) ↦ D).symm))
    have hwalk_cast : ∀ {L₁ L₂ : ℕ} (hL : L₁ = L₂) (u : V) (f : Fin L₂ → D) (m : ℕ),
        G.walkAt (u, fun i : Fin L₁ ↦ f (finCongr hL i)) m = G.walkAt (u, f) m := by
      rintro L₁ _ rfl u f m; rfl
    rw [← Fintype.expect_equiv hsplit.symm
      (fun p ↦ ∏ j : Fin (t + 1), s (G.walkAt (v, hsplit.symm p) (2 * j.val + 1)))
      (fun k' ↦ ∏ j : Fin (t + 1), s (G.walkAt (v, k') (2 * j.val + 1)))
      (fun _ ↦ rfl)]
    rw [Fintype.expect_prod_type]
    refine expect_congr rfl fun i0 _ ↦ ?_
    rw [mul_expect, Fintype.expect_prod_type]
    refine expect_congr rfl fun i1 _ ↦ ?_
    rw [mul_expect]
    refine expect_congr rfl fun k _ ↦ ?_
    rw [Fin.prod_univ_succ]
    have hv1 : G.walkAt (v, hsplit.symm (i0, i1, k)) 1 = G.neighbor v i0 := by
      have h0 : hsplit.symm (i0, i1, k) 0 = i0 := by simp [hsplit, finCongr]
      rw [G.walkAt_succ_of_lt _ (by omega), G.walkAt_zero]
      exact congrArg (G.neighbor v) h0
    have hrest : ∀ j : Fin t,
        G.walkAt (v, hsplit.symm (i0, i1, k)) (2 * j.succ.val + 1) =
          G.walkAt (G.neighbor (G.neighbor v i0) i1, k) (2 * j.val + 1) := by
      intro j
      have hcons1 : ∀ m, G.walkAt (v, hsplit.symm (i0, i1, k)) (m + 1) =
          G.walkAt (G.neighbor v i0, Fin.cons i1 k) m := by
        intro m
        have h1 : G.walkAt (v, hsplit.symm (i0, i1, k)) (m + 1) =
            G.walkAt (v, Fin.cons i0 (Fin.cons i1 k)) (m + 1) :=
          hwalk_cast (show 2 * (t + 1) = (2 * t + 1) + 1 by omega) v (Fin.cons i0 (Fin.cons i1 k))
            (m + 1)
        rw [h1, G.walkAt_cons_succ]
      have h2 := hcons1 (2 * j.val + 2)
      have h3 := G.walkAt_cons_succ (G.neighbor v i0) i1 k (2 * j.val + 1)
      have hidx : 2 * j.succ.val + 1 = (2 * j.val + 2) + 1 := by simp [Fin.val_succ]; ring
      rw [hidx, h2, h3]
    simp only [Fin.val_zero, mul_zero, zero_add]
    rw [hv1]
    simp_rw [hrest]

/-- Expander-walk parity-sampling bias bound: averaging `∏_{j < t} s(v_{2j+1})` over all
walks of length `2 t` in `G` has absolute value at most `((1 - δ)² + 2 λ²)^{t/2}`. -/
theorem abs_expect_walk_parity_le [Nonempty V] [Nonempty D]
    (G : Cslib.RotationMap V D) {s : V → ℝ} (hs : ∀ v, s v ^ 2 = 1)
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hmean : |𝔼 v, s v| ≤ 1 - δ) (t : ℕ) :
    |𝔼 p : V × (Fin (2 * t) → D), ∏ j : Fin t, s (G.walkAt p (2 * j.val + 1))| ≤
      (Real.sqrt ((1 - δ) ^ 2 + 2 * G.spectralExpansion ^ 2)) ^ t := by
  have hrew : (𝔼 p : V × (Fin (2 * t) → D), ∏ j : Fin t, s (G.walkAt p (2 * j.val + 1))) =
      𝔼 v : V, ((walkSignStep G s) ^ t) (fun _ ↦ 1) v := by
    rw [Fintype.expect_prod_type]
    refine expect_congr rfl fun v _ ↦ (walkSignStep_pow_one_eq_expect G s t v).symm
  rw [hrew]
  set f : V → ℝ := ((walkSignStep G s) ^ t) (fun _ ↦ 1)
  have hcs : (𝔼 v, f v) ^ 2 ≤ 𝔼 v, f v ^ 2 := by
    have := expect_sub_mean_sq f
    have hnn : 0 ≤ 𝔼 v, (f v - 𝔼 w, f w) ^ 2 := expect_nonneg fun v _ ↦ sq_nonneg _
    linarith
  have hpow := expect_walkSignStep_pow_one_sq_le G hs hδ0 hδ1 hmean t
  have hsq : (𝔼 v, f v) ^ 2 ≤
      ((Real.sqrt ((1 - δ) ^ 2 + 2 * G.spectralExpansion ^ 2)) ^ t) ^ 2 := by
    rw [← pow_mul, mul_comm t 2, pow_mul, Real.sq_sqrt (by positivity)]
    exact hcs.trans hpow
  have hpos : 0 ≤ (Real.sqrt ((1 - δ) ^ 2 + 2 * G.spectralExpansion ^ 2)) ^ t := by positivity
  have := sq_le_sq.mp hsq
  rwa [abs_of_nonneg hpos] at this

private lemma canonicalAddChar_zmod_two_sum {ι : Type*} (S : Finset ι) (g : ι → ZMod 2) :
    canonicalAddChar (ZMod 2) (∑ j ∈ S, g j) =
      ((∏ j ∈ S, (if g j = 0 then (1 : ℝ) else -1) : ℝ) : ℂ) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha, canonicalAddChar_add, ih,
      canonicalAddChar_zmod_two, Complex.ofReal_mul]
    congr 1
    split_ifs <;> simp

/-- Translating `abs_expect_walk_parity_le` into `IsVectorBiased` for binary vectors whose
normalized Hamming weight lies in `[1/256, 1/2]` on an expander with `λ(G) ≤ 1/256`. -/
theorem isVectorBiased_walkParity [Nonempty V] [Nonempty D]
    (G : Cslib.RotationMap V D) (hG : G.spectralExpansion ≤ 1 / 256)
    (x : V → ZMod 2) (hlo : (1 / 256 : ℝ) ≤ normalizedHammingWeight x)
    (hhi : normalizedHammingWeight x ≤ 1 / 2) (t : ℕ) :
    IsVectorBiased ((255 / 256 : ℝ) ^ t)
      (fun p : V × (Fin (2 * t) → D) ↦ ∑ j : Fin t, x (G.walkAt p (2 * j.val + 1))) := by
  classical
  rw [isVectorBiased_iff]
  intro a ha
  have hz2 : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  have ha1 : a = 1 := (hz2 a).resolve_left ha
  subst ha1
  simp only [one_mul]
  let s : V → ℝ := fun v ↦ if x v = 0 then 1 else -1
  have hs : ∀ v, s v ^ 2 = 1 := fun v ↦ by dsimp [s]; split_ifs <;> norm_num
  have hmean_eq : 𝔼 v, s v = 1 - 2 * normalizedHammingWeight x := by
    rw [Fintype.expect_eq_sum_div_card, normalizedHammingWeight_eq_div]
    have hsum : ∑ v : V, s v = (Fintype.card V : ℝ) - 2 * (hammingNorm x : ℝ) := by
      have hcard : (Finset.univ.filter fun v : V ↦ x v = 0).card + hammingNorm x =
          Fintype.card V := by
        rw [hammingNorm]
        simpa [Finset.card_univ] using
          Finset.card_filter_add_card_filter_not (s := Finset.univ) (p := fun v : V ↦ x v = 0)
      have hcast : ((Finset.univ.filter fun v : V ↦ x v = 0).card : ℝ) +
          (hammingNorm x : ℝ) = (Fintype.card V : ℝ) := by exact_mod_cast hcard
      have hs_split : ∑ v : V, s v =
          ((Finset.univ.filter fun v : V ↦ x v = 0).card : ℝ) - (hammingNorm x : ℝ) := by
        have h1 := Finset.sum_filter_add_sum_filter_not (s := Finset.univ)
          (p := fun v : V ↦ x v = 0) (f := s)
        rw [← h1]
        have hA : ∑ v ∈ Finset.univ.filter (fun v : V ↦ x v = 0), s v =
            ((Finset.univ.filter fun v : V ↦ x v = 0).card : ℝ) := by
          trans ∑ _v ∈ Finset.univ.filter (fun v : V ↦ x v = 0), (1 : ℝ)
          · exact Finset.sum_congr rfl fun v hv ↦ by simp [s, (Finset.mem_filter.mp hv).2]
          · simp
        have hB : ∑ v ∈ Finset.univ.filter (fun v : V ↦ ¬x v = 0), s v =
            -(hammingNorm x : ℝ) := by
          trans ∑ _v ∈ Finset.univ.filter (fun v : V ↦ x v ≠ 0), (-1 : ℝ)
          · exact Finset.sum_congr rfl fun v hv ↦ by simp [s, (Finset.mem_filter.mp hv).2]
          · simp [hammingNorm]
        rw [hA, hB]; ring
      linarith
    have hV : (Fintype.card V : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    rw [hsum]; field_simp [hV]
  have hmean : |𝔼 v, s v| ≤ 1 - (1 / 128 : ℝ) := by
    rw [hmean_eq, abs_le]; constructor <;> linarith
  have hbound := abs_expect_walk_parity_le G hs (by norm_num : (0 : ℝ) ≤ 1 / 128)
    (by norm_num : (1 / 128 : ℝ) ≤ 1) hmean t
  have hbase : Real.sqrt ((1 - 1 / 128 : ℝ) ^ 2 + 2 * G.spectralExpansion ^ 2) ≤ 255 / 256 := by
    refine Real.sqrt_le_iff.mpr ⟨by norm_num, ?_⟩
    have hlam_sq : G.spectralExpansion ^ 2 ≤ (1 / 256 : ℝ) ^ 2 := by
      have := G.spectralExpansion_nonneg; nlinarith
    nlinarith
  have hsum_eq :
      ∑ p : V × (Fin (2 * t) → D),
          canonicalAddChar (ZMod 2) (∑ j : Fin t, x (G.walkAt p (2 * j.val + 1))) =
        (((Fintype.card (V × (Fin (2 * t) → D)) : ℝ) *
          𝔼 p : V × (Fin (2 * t) → D),
            ∏ j : Fin t, s (G.walkAt p (2 * j.val + 1)) : ℝ) : ℂ) := by
    simp_rw [canonicalAddChar_zmod_two_sum]
    rw [← Complex.ofReal_sum, Fintype.expect_eq_sum_div_card]
    have hcard : (Fintype.card (V × (Fin (2 * t) → D)) : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    congr 1; dsimp only [s]; field_simp [hcard]
  rw [hsum_eq, Complex.norm_real, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (Nat.cast_nonneg _)]
  calc (Fintype.card (V × (Fin (2 * t) → D)) : ℝ) *
        |𝔼 p : V × (Fin (2 * t) → D), ∏ j : Fin t, s (G.walkAt p (2 * j.val + 1))|
      ≤ (Fintype.card (V × (Fin (2 * t) → D)) : ℝ) *
          (Real.sqrt ((1 - 1 / 128 : ℝ) ^ 2 + 2 * G.spectralExpansion ^ 2)) ^ t :=
        mul_le_mul_of_nonneg_left hbound (Nat.cast_nonneg _)
    _ ≤ (Fintype.card (V × (Fin (2 * t) → D)) : ℝ) * (255 / 256 : ℝ) ^ t := by gcongr

end ExpanderParity

/-! ### Part 2: Explicit linear-length `η`-biased binary linear codes -/

section ABNNR

/-- Smallest positive integer `s` such that `k ≤ 8 * s * 2 ^ (16 * s)`. -/
def justesenScale (k : ℕ) : ℕ :=
  ((List.range (Nat.log 2 k + 2)).find? fun s ↦
    decide (1 ≤ s ∧ k ≤ 8 * s * 2 ^ (16 * s))).getD (Nat.log 2 k + 1)

theorem justesenScale_eq (k : ℕ) :
    justesenScale k =
      ((List.range (Nat.log 2 k + 2)).find? fun s ↦
        decide (1 ≤ s ∧ k ≤ 8 * s * 2 ^ (16 * s))).getD (Nat.log 2 k + 1) := by rfl

theorem justesenScale_pos (k : ℕ) : 1 ≤ justesenScale k := by
  unfold justesenScale
  cases h : (List.range (Nat.log 2 k + 2)).find?
      (fun s ↦ decide (1 ≤ s ∧ k ≤ 8 * s * 2 ^ (16 * s))) with
  | none => simp
  | some s =>
    have hs := List.find?_some h
    simp only [decide_eq_true_eq] at hs
    simpa using hs.1

theorem le_dim_justesenScale (k : ℕ) :
    k ≤ 8 * justesenScale k * 2 ^ (16 * justesenScale k) := by
  unfold justesenScale
  cases h : (List.range (Nat.log 2 k + 2)).find?
      (fun s ↦ decide (1 ≤ s ∧ k ≤ 8 * s * 2 ^ (16 * s))) with
  | none =>
    simp only [Option.getD_none]
    set s := Nat.log 2 k + 1
    have hpow : k < 2 ^ s := Nat.lt_pow_succ_log_self (by decide) k
    have hpow2 : 2 ^ s ≤ 2 ^ (16 * s) := Nat.pow_le_pow_right (by decide) (by omega)
    have hmul : 1 ≤ 8 * s := by omega
    nlinarith
  | some s =>
    have hs := List.find?_some h
    simp only [decide_eq_true_eq] at hs
    simpa using hs.2

theorem justesenScale_minimal (k : ℕ) :
    justesenScale k = 1 ∨
      8 * (justesenScale k - 1) * 2 ^ (16 * (justesenScale k - 1)) < k := by
  have hpos := justesenScale_pos k
  by_cases h1 : justesenScale k = 1
  · exact Or.inl h1
  · right
    have hge2 : 2 ≤ justesenScale k := by omega
    unfold justesenScale at h1 hge2 ⊢
    cases h : (List.range (Nat.log 2 k + 2)).find?
        (fun s ↦ decide (1 ≤ s ∧ k ≤ 8 * s * 2 ^ (16 * s))) with
    | none =>
      exfalso
      have hmem : Nat.log 2 k + 1 ∈ List.range (Nat.log 2 k + 2) := by
        simp
      have hfalse := List.find?_eq_none.mp h _ hmem
      simp only [decide_eq_true_eq, not_and, not_le] at hfalse
      set s := Nat.log 2 k + 1
      have hpow : k < 2 ^ s := Nat.lt_pow_succ_log_self (by decide) k
      have hpow2 : 2 ^ s ≤ 2 ^ (16 * s) := Nat.pow_le_pow_right (by decide) (by omega)
      have hlt := hfalse (by omega)
      have hmul : 1 ≤ 8 * s := by omega
      nlinarith
    | some s =>
      simp only [h, Option.getD_some] at h1 hge2 ⊢
      have hmem := List.mem_of_find?_eq_some h
      have hlt_range : s < Nat.log 2 k + 2 := List.mem_range.mp hmem
      have hprev_mem : s - 1 ∈ List.range (Nat.log 2 k + 2) :=
        List.mem_range.mpr (by omega)
      have hprev := List.find?_eq_some_iff_append.mp h
      obtain ⟨hpred, xs, ys, hsplit, hnone⟩ := hprev
      have hs_ge2 : 2 ≤ s := hge2
      have hsm1_in_xs : s - 1 ∈ xs := by
        have hidx : (xs ++ s :: ys)[s - 1]? = some (s - 1) := by
          rw [← hsplit, List.getElem?_range (by omega)]
        have hlen_xs : xs.length = s := by
          have := congrArg (fun l ↦ l[xs.length]?) hsplit
          rw [List.getElem?_append_right (le_refl _), Nat.sub_self, List.getElem?_cons_zero] at this
          have hlt_len : xs.length < Nat.log 2 k + 2 := by
            have := congrArg List.length hsplit
            simp only [List.length_range, List.length_append, List.length_cons] at this
            omega
          rw [List.getElem?_range hlt_len] at this
          exact Option.some.inj this
        have hlt_xs : s - 1 < xs.length := by omega
        have := List.getElem?_eq_some_iff.mp
          (by rw [List.getElem?_append_left hlt_xs] at hidx; exact hidx)
        obtain ⟨_, heq⟩ := this
        rw [← heq]
        exact List.getElem_mem hlt_xs
      have hno := hnone (s - 1) hsm1_in_xs
      by_contra hle
      have hle' : k ≤ 8 * (s - 1) * 2 ^ (16 * (s - 1)) := by omega
      have htrue : decide (1 ≤ s - 1 ∧ k ≤ 8 * (s - 1) * 2 ^ (16 * (s - 1))) = true :=
        decide_eq_true ⟨by omega, hle'⟩
      simp [htrue] at hno

/-- Block length of the base Justesen code for dimension `k`. -/
def justesenLen (k : ℕ) : ℕ :=
  32 * justesenScale k * (2 ^ (16 * justesenScale k) - 1)

theorem justesenLen_eq (k : ℕ) :
    justesenLen k = 32 * justesenScale k * (2 ^ (16 * justesenScale k) - 1) := by rfl

/-- Length of the zero-padded Justesen code for dimension `k`: `2 * justesenLen k`. -/
def paddedJustesenLen (k : ℕ) : ℕ := 2 * justesenLen k

theorem paddedJustesenLen_eq (k : ℕ) : paddedJustesenLen k = 2 * justesenLen k := by rfl

theorem justesenLen_pos (k : ℕ) : 0 < justesenLen k := by
  unfold justesenLen
  have hs := justesenScale_pos k
  have h2 : 1 < 2 ^ (16 * justesenScale k) := Nat.one_lt_pow (by omega) (by decide)
  have h1 : 0 < 2 ^ (16 * justesenScale k) - 1 := by omega
  positivity

theorem paddedJustesenLen_pos (k : ℕ) : 0 < paddedJustesenLen k := by
  unfold paddedJustesenLen; have := justesenLen_pos k; omega

theorem justesenLen_le (k : ℕ) : justesenLen k ≤ 2 ^ 21 * max 1 k := by
  unfold justesenLen
  set s := justesenScale k
  have hle1 : 32 * s * (2 ^ (16 * s) - 1) ≤ 4 * (8 * s * 2 ^ (16 * s)) := by
    have : 2 ^ (16 * s) - 1 ≤ 2 ^ (16 * s) := Nat.sub_le _ _
    nlinarith
  by_cases hs1 : s = 1
  · have hval : 4 * (8 * s * 2 ^ (16 * s)) = 2 ^ 21 := by
      rw [hs1]; norm_num
    have hmax : 1 ≤ max 1 k := le_max_left 1 k
    nlinarith
  · have hs2 : 2 ≤ s := by have := justesenScale_pos k; omega
    have hmin : 8 * (s - 1) * 2 ^ (16 * (s - 1)) < k :=
      (justesenScale_minimal k).resolve_left hs1
    have hratio : 8 * s * 2 ^ (16 * s) ≤ 2 ^ 17 * (8 * (s - 1) * 2 ^ (16 * (s - 1))) := by
      have hpow : 2 ^ (16 * s) = 2 ^ 16 * 2 ^ (16 * (s - 1)) := by
        rw [← pow_add]; congr 1; omega
      have hs_le : s ≤ 2 * (s - 1) := by omega
      rw [hpow]
      calc 8 * s * (2 ^ 16 * 2 ^ (16 * (s - 1)))
          ≤ 8 * (2 * (s - 1)) * (2 ^ 16 * 2 ^ (16 * (s - 1))) := by gcongr
        _ = 2 ^ 17 * (8 * (s - 1) * 2 ^ (16 * (s - 1))) := by ring
    have hk_le : k ≤ max 1 k := le_max_right 1 k
    calc 32 * s * (2 ^ (16 * s) - 1)
        ≤ 4 * (8 * s * 2 ^ (16 * s)) := hle1
      _ ≤ 4 * (2 ^ 17 * (8 * (s - 1) * 2 ^ (16 * (s - 1)))) := Nat.mul_le_mul_left 4 hratio
      _ ≤ 4 * (2 ^ 17 * k) := Nat.mul_le_mul_left 4 (Nat.mul_le_mul_left _ hmin.le)
      _ = 2 ^ 19 * k := by ring
      _ ≤ 2 ^ 21 * max 1 k := by
          have : 2 ^ 19 * k ≤ 2 ^ 21 * k := Nat.mul_le_mul_right k (by norm_num)
          exact this.trans (Nat.mul_le_mul_left _ hk_le)

theorem two_pow_sixteen_justesenScale_le (k : ℕ) :
    2 ^ (16 * justesenScale k) ≤ 2 ^ 16 * max 1 k := by
  set s := justesenScale k
  by_cases hs1 : s = 1
  · rw [hs1]
    calc 2 ^ (16 * 1) = 2 ^ 16 * 1 := by ring
      _ ≤ 2 ^ 16 * max 1 k := Nat.mul_le_mul_left _ (le_max_left 1 k)
  · have hs2 : 2 ≤ s := by have := justesenScale_pos k; omega
    have hmin : 8 * (s - 1) * 2 ^ (16 * (s - 1)) < k :=
      (justesenScale_minimal k).resolve_left hs1
    have hpow : 2 ^ (16 * s) = 2 ^ 16 * 2 ^ (16 * (s - 1)) := by
      rw [← pow_add]; congr 1; omega
    have h1 : 2 ^ (16 * (s - 1)) ≤ 8 * (s - 1) * 2 ^ (16 * (s - 1)) :=
      Nat.le_mul_of_pos_left _ (by omega : 0 < 8 * (s - 1))
    have h2 : 2 ^ (16 * (s - 1)) ≤ k := h1.trans hmin.le
    rw [hpow]
    exact Nat.mul_le_mul_left _ (h2.trans (le_max_right 1 k))

/-- Fixed `w`-bit list of `m`'s binary digits `m.testBit 0, ..., m.testBit (w - 1)`. -/
def bitsOfNat (w m : ℕ) : List Bool :=
  (List.range w).map m.testBit

theorem bitsOfNat_eq (w m : ℕ) : bitsOfNat w m = (List.range w).map m.testBit := by rfl

@[simp]
theorem length_bitsOfNat (w m : ℕ) : (bitsOfNat w m).length = w := by
  simp [bitsOfNat]

theorem getD_bitsOfNat {w m i : ℕ} (hi : i < w) :
    (bitsOfNat w m).getD i false = m.testBit i := by
  simp [bitsOfNat, List.getD_eq_getElem?_getD, hi]

private lemma bitsOfNat_inj {w : ℕ} {a b : ℕ} (ha : a < 2 ^ w) (hb : b < 2 ^ w)
    (h : ∀ i : Fin w, a.testBit i.val = b.testBit i.val) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < w
  · exact h ⟨i, hi⟩
  · have hwi : w ≤ i := by omega
    have h1 := Nat.testBit_lt_two_pow (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by decide) hwi))
    have h2 := Nat.testBit_lt_two_pow (lt_of_lt_of_le hb (Nat.pow_le_pow_right (by decide) hwi))
    rw [h1, h2]

private lemma fieldOfBits_bitsOfNat_ne_zero {w : ℕ} (hw : w ≠ 0) {m : ℕ}
    (hm1 : 1 ≤ m) (hm2 : m < 2 ^ w) :
    Cslib.BinaryField.fieldOfBits (Cslib.BinaryField.basis hw) (bitsOfNat w m) ≠ 0 := by
  intro h0
  have htb : ∀ i : Fin w, m.testBit i.val = false := by
    intro i
    have h1 := congrFun (congrArg (Cslib.BinaryField.equivBits hw) h0) i
    rw [Cslib.BinaryField.equivBits_apply, Cslib.BinaryField.repr_fieldOfBits,
      RingEquiv.apply_symm_apply, map_zero, Pi.zero_apply, getD_bitsOfNat i.isLt] at h1
    exact h1
  have hm0 : m = 0 := bitsOfNat_inj hm2 (by positivity) fun i ↦ by
    rw [htb i, Nat.zero_testBit]
  omega

/-- Explicit bijection between `Fin (2 ^ w - 1)` and nonzero elements of `BinaryField w`. -/
noncomputable def binaryFieldUnitsEquiv {w : ℕ} (hw : w ≠ 0) :
    Fin (2 ^ w - 1) ≃ (Cslib.BinaryField w)ˣ := by
  have hcard : Fintype.card (Fin (2 ^ w - 1)) =
      Fintype.card (Cslib.BinaryField w)ˣ := by
    rw [Fintype.card_fin, Fintype.card_units, Cslib.BinaryField.card hw]
  refine Equiv.ofBijective
    (fun u : Fin (2 ^ w - 1) ↦
      Units.mk0 (Cslib.BinaryField.fieldOfBits (Cslib.BinaryField.basis hw)
        (bitsOfNat w (u.val + 1)))
        (fieldOfBits_bitsOfNat_ne_zero hw (by omega) (by
          have := u.isLt
          have hpos : 1 ≤ 2 ^ w := Nat.one_le_pow _ _ (by decide)
          omega))) ?_
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨fun u₁ u₂ heq ↦ ?_, hcard⟩
  have hval : Cslib.BinaryField.fieldOfBits (Cslib.BinaryField.basis hw)
        (bitsOfNat w (u₁.val + 1)) =
      Cslib.BinaryField.fieldOfBits (Cslib.BinaryField.basis hw)
        (bitsOfNat w (u₂.val + 1)) := congrArg Units.val heq
  have hbits : ∀ i : Fin w, (u₁.val + 1).testBit i.val = (u₂.val + 1).testBit i.val := by
    intro i
    have := congrFun (congrArg (Cslib.BinaryField.equivBits hw) hval) i
    rw [Cslib.BinaryField.equivBits_apply, Cslib.BinaryField.equivBits_apply,
      Cslib.BinaryField.repr_fieldOfBits, Cslib.BinaryField.repr_fieldOfBits,
      RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply,
      getD_bitsOfNat i.isLt, getD_bitsOfNat i.isLt] at this
    exact this
  have hpos : 1 ≤ 2 ^ w := Nat.one_le_pow _ _ (by decide)
  have hsum := bitsOfNat_inj (by have := u₁.isLt; omega) (by have := u₂.isLt; omega) hbits
  exact Fin.ext (by omega)

theorem binaryFieldUnitsEquiv_val {w : ℕ} (hw : w ≠ 0) (u : Fin (2 ^ w - 1)) :
    (binaryFieldUnitsEquiv hw u : Cslib.BinaryField w) =
      Cslib.BinaryField.fieldOfBits (Cslib.BinaryField.basis hw) (bitsOfNat w (u.val + 1)) := by
  rfl

/-- Explicit index bijection for `justesenLen k`. -/
noncomputable def justesenIndexEquiv (k : ℕ) :
    Fin (justesenLen k) ≃
      (Cslib.BinaryField (16 * justesenScale k))ˣ ×
        (Fin 2 × Fin (16 * justesenScale k)) :=
  have hw : 16 * justesenScale k ≠ 0 := by have := justesenScale_pos k; omega
  (finCongr (show justesenLen k = (2 ^ (16 * justesenScale k) - 1) * (2 * (16 * justesenScale k))
    by unfold justesenLen; ring)).trans
    (finProdFinEquiv.symm.trans
      (Equiv.prodCongr (binaryFieldUnitsEquiv hw) finProdFinEquiv.symm))

theorem justesenIndexEquiv_apply (k : ℕ) (v : Fin (justesenLen k)) :
    let w := 16 * justesenScale k
    let hw : w ≠ 0 := by have := justesenScale_pos k; omega
    justesenIndexEquiv k v =
      (binaryFieldUnitsEquiv hw ⟨v.val / (2 * w), by
          have h1 : v.val < (2 ^ w - 1) * (2 * w) := by
            have := v.isLt; unfold justesenLen at this; dsimp [w]; linarith
          exact Nat.div_lt_of_lt_mul (by rwa [mul_comm])⟩,
        (⟨(v.val % (2 * w)) / w, by
            have hrem : v.val % (2 * w) < 2 * w := Nat.mod_lt _ (by omega)
            exact Nat.div_lt_of_lt_mul (by simpa [mul_comm] using hrem)⟩,
          ⟨(v.val % (2 * w)) % w, Nat.mod_lt _ (by omega)⟩)) := by
  dsimp only [justesenIndexEquiv, Equiv.trans_apply, Equiv.prodCongr_apply, Prod.map_apply]
  refine Prod.ext rfl (Prod.ext ?_ ?_)
  · apply Fin.ext; rfl
  · apply Fin.ext
    change (v.val % (2 * (16 * justesenScale k))) % (16 * justesenScale k) = _
    rfl

/-- Outer Reed–Solomon evaluation map for a binary message `msg : Fin k → ZMod 2`. -/
noncomputable def justesenOuterPoly (k : ℕ) (msg : Fin k → ZMod 2) :
    Polynomial (Cslib.BinaryField (16 * justesenScale k)) :=
  let s := justesenScale k
  let w := 16 * s
  have hw : w ≠ 0 := by have := justesenScale_pos k; omega
  ∑ j : Fin (2 ^ (w - 1)),
    Polynomial.C (∑ d : Fin w,
      (if h : j.val * w + d.val < k then msg ⟨j.val * w + d.val, h⟩ else 0) •
        Cslib.BinaryField.basis hw d) *
      Polynomial.X ^ j.val

theorem justesenOuterPoly_eq (k : ℕ) (msg : Fin k → ZMod 2) :
    justesenOuterPoly k msg =
      ∑ j : Fin (2 ^ (16 * justesenScale k - 1)),
        Polynomial.C (∑ d : Fin (16 * justesenScale k),
          (if h : j.val * (16 * justesenScale k) + d.val < k then
            msg ⟨j.val * (16 * justesenScale k) + d.val, h⟩ else 0) •
            Cslib.BinaryField.basis (by have := justesenScale_pos k; omega) d) *
          Polynomial.X ^ j.val := by rfl

private lemma justesenOuterPoly_linear (k : ℕ) :
    ∀ (m₁ m₂ : Fin k → ZMod 2),
      justesenOuterPoly k (m₁ + m₂) = justesenOuterPoly k m₁ + justesenOuterPoly k m₂ := by
  intro m₁ m₂
  unfold justesenOuterPoly
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [← add_mul, ← map_add, ← Finset.sum_add_distrib]
  congr 2
  refine Finset.sum_congr rfl fun d _ ↦ ?_
  split_ifs with h
  · simp [Pi.add_apply, add_smul]
  · simp

private lemma justesenOuterPoly_degree_lt (k : ℕ) (msg : Fin k → ZMod 2) :
    (justesenOuterPoly k msg).degree < (2 ^ (16 * justesenScale k - 1) : ℕ) := by
  unfold justesenOuterPoly
  refine (Polynomial.degree_sum_le _ _).trans_lt ?_
  rw [Finset.sup_lt_iff (WithBot.bot_lt_coe _)]
  intro j _
  refine (Polynomial.degree_C_mul_X_pow_le _ _).trans_lt ?_
  exact_mod_cast j.isLt

/-- Zero-padded explicit binary Justesen linear code map of dimension `k` and length
`paddedJustesenLen k = O(k)`. Every nonzero codeword has normalized Hamming weight in
`[1/256, 1/2]`. -/
noncomputable def paddedJustesenMap (k : ℕ) :
    (Fin k → ZMod 2) →ₗ[ZMod 2] (Fin (paddedJustesenLen k) → ZMod 2) where
  toFun msg v :=
    if h : v.val < justesenLen k then
      let s := justesenScale k
      let w := 16 * s
      have hw : w ≠ 0 := by have := justesenScale_pos k; omega
      let c : (Cslib.BinaryField w)ˣ → Cslib.BinaryField w :=
        fun u ↦ (justesenOuterPoly k msg).eval (u : Cslib.BinaryField w)
      Cslib.BitString.bitEquiv.symm
        (Cslib.Code.justesen (Cslib.BinaryField.equivBits hw) c
          (justesenIndexEquiv k ⟨v.val, h⟩))
    else 0
  map_add' m₁ m₂ := by
    funext v
    dsimp only [Pi.add_apply]
    split_ifs with h
    · rw [← map_add]
      congr 1
      have hlin := justesenOuterPoly_linear k m₁ m₂
      change Cslib.Code.justesen _ _ _ = Cslib.Code.justesen _ _ _ + Cslib.Code.justesen _ _ _
      simp only [Cslib.Code.justesen, Cslib.Code.concat, Cslib.Code.wozencraft, hlin,
        Polynomial.eval_add]
      split_ifs <;> simp [map_add, mul_add]
    · simp
  map_smul' r msg := by
    have hz2 : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
    rcases hz2 r with rfl | rfl
    · funext v
      simp only [RingHom.id_apply, zero_smul, Pi.zero_apply]
      split_ifs with h
      · have hw : 16 * justesenScale k ≠ 0 := by have := justesenScale_pos k; omega
        have h0 : justesenOuterPoly k 0 = 0 := by
          unfold justesenOuterPoly
          refine Finset.sum_eq_zero fun j _ ↦ ?_
          have : ∑ d : Fin (16 * justesenScale k),
              (if h : j.val * (16 * justesenScale k) + d.val < k then (0 : ZMod 2) else 0) •
                Cslib.BinaryField.basis hw d = 0 := by simp
          simp
        simp [h0, Cslib.Code.justesen, Cslib.Code.concat, Cslib.Code.wozencraft]
      · rfl
    · simp

theorem paddedJustesenMap_apply (k : ℕ) (msg : Fin k → ZMod 2) (v : Fin (paddedJustesenLen k)) :
    paddedJustesenMap k msg v =
      if h : v.val < justesenLen k then
        let w := 16 * justesenScale k
        have hw : w ≠ 0 := by have := justesenScale_pos k; omega
        Cslib.BitString.bitEquiv.symm
          (Cslib.Code.justesen (Cslib.BinaryField.equivBits hw)
            (fun u ↦ (justesenOuterPoly k msg).eval (u : Cslib.BinaryField w))
            (justesenIndexEquiv k ⟨v.val, h⟩))
      else 0 := by rfl

theorem paddedJustesenMap_injective (k : ℕ) :
    Function.Injective (paddedJustesenMap k) := by
  rw [injective_iff_map_eq_zero]
  intro msg hmsg
  set s := justesenScale k
  set w := 16 * s
  have hw : w ≠ 0 := by have := justesenScale_pos k; omega
  have hjust0 : ∀ idx,
      Cslib.Code.justesen (Cslib.BinaryField.equivBits hw)
        (fun u ↦ (justesenOuterPoly k msg).eval (u : Cslib.BinaryField w)) idx =
          false := by
    intro idx
    set v : Fin (paddedJustesenLen k) :=
      ⟨((justesenIndexEquiv k).symm idx).val,
        by
          have := ((justesenIndexEquiv k).symm idx).isLt
          unfold paddedJustesenLen; omega⟩
    have hv := congrFun hmsg v
    have hlt : v.val < justesenLen k := ((justesenIndexEquiv k).symm idx).isLt
    simp only [paddedJustesenMap, LinearMap.coe_mk, AddHom.coe_mk, hlt, dite_true,
      Pi.zero_apply] at hv
    have hfin : (⟨v.val, hlt⟩ : Fin (justesenLen k)) = (justesenIndexEquiv k).symm idx :=
      Fin.ext rfl
    rw [hfin, Equiv.apply_symm_apply] at hv
    exact Cslib.BitString.bitEquiv.symm.injective (by simpa using hv)
  have heval0 : ∀ u : (Cslib.BinaryField w)ˣ,
      (justesenOuterPoly k msg).eval (u : Cslib.BinaryField w) = 0 := by
    have hinj := Cslib.Code.justesen_injective (Cslib.BinaryField.equivBits hw)
    intro u
    have h0 : Cslib.Code.justesen (Cslib.BinaryField.equivBits hw)
        (fun u ↦ (justesenOuterPoly k msg).eval (u : Cslib.BinaryField w)) =
        Cslib.Code.justesen (Cslib.BinaryField.equivBits hw) 0 := by
      funext idx
      rw [hjust0 idx]
      simp [Cslib.Code.justesen, Cslib.Code.concat, Cslib.Code.wozencraft]
      rfl
    exact congrFun (hinj h0) u
  have hpoly0 : justesenOuterPoly k msg = 0 := by
    by_contra hne
    have hdeg := justesenOuterPoly_degree_lt k msg
    have hnat : (justesenOuterPoly k msg).natDegree < 2 ^ (w - 1) :=
      (Polynomial.natDegree_lt_iff_degree_lt hne).mpr hdeg
    have hroots : Fintype.card (Cslib.BinaryField w)ˣ ≤
        (justesenOuterPoly k msg).natDegree := by
      have hcard_u : Fintype.card (Cslib.BinaryField w)ˣ =
          (Finset.univ.image (fun u : (Cslib.BinaryField w)ˣ ↦
            (u : Cslib.BinaryField w))).card := by
        rw [Finset.card_image_of_injective _ Units.val_injective, Finset.card_univ]
      rw [hcard_u]
      refine Polynomial.card_le_degree_of_subset_roots fun x hx ↦ ?_
      obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hx
      exact (Polynomial.mem_roots hne).mpr (heval0 u)
    rw [Fintype.card_units, Cslib.BinaryField.card hw] at hroots
    have hpow : 2 ^ w = 2 * 2 ^ (w - 1) := by rw [← pow_succ']; congr 1; omega
    have hpos : 0 < 2 ^ (w - 1) := by positivity
    omega
  funext r
  have hdim := le_dim_justesenScale k
  have hr_lt : r.val < w * 2 ^ (w - 1) := by
    have hpow : 2 ^ w = 2 * 2 ^ (w - 1) := by rw [← pow_succ']; congr 1; omega
    have heq : 8 * s * 2 ^ (16 * s) = w * 2 ^ (w - 1) := by
      change 8 * s * 2 ^ w = w * 2 ^ (w - 1)
      rw [hpow]; dsimp [w]; ring
    exact lt_of_lt_of_le r.isLt (hdim.trans_eq heq)
  set j : Fin (2 ^ (w - 1)) :=
    ⟨r.val / w, Nat.div_lt_of_lt_mul (by simpa [mul_comm] using hr_lt)⟩
  set d : Fin w := ⟨r.val % w, Nat.mod_lt _ (by omega)⟩
  have hcoeff := congrArg (fun p ↦ p.coeff j.val) hpoly0
  simp only [justesenOuterPoly, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_pow, Polynomial.coeff_zero, mul_ite, mul_one, mul_zero,
    Fin.val_inj, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte] at hcoeff
  have hrepr := congrArg (fun x ↦ (Cslib.BinaryField.basis hw).repr x d) hcoeff
  have hsum_apply : ∀ (s : Finset (Fin w)) (f : Fin w → Fin w →₀ ZMod 2),
      (∑ x ∈ s, f x) d = ∑ x ∈ s, f x d := fun s f ↦ by
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih => simp [Finset.sum_insert ha]
  simp only [map_sum, map_smul, Module.Basis.repr_self, map_zero, Finsupp.zero_apply] at hrepr
  rw [hsum_apply] at hrepr
  rw [Finset.sum_eq_single d (fun c _ hcd ↦ by
      rw [Finsupp.smul_apply, Finsupp.single_eq_of_ne hcd.symm, smul_zero])
    (fun hd ↦ (hd (Finset.mem_univ d)).elim)] at hrepr
  have hjd : j.val * w + d.val = r.val := by
    dsimp [j, d]; rw [mul_comm, Nat.div_add_mod]
  have hlt : j.val * (16 * justesenScale k) + d.val < k := by
    change j.val * w + d.val < k; rw [hjd]; exact r.isLt
  rw [dite_eq_left hlt, Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul, mul_one] at hrepr
  exact (congrArg msg (Fin.ext hjd)).symm.trans hrepr

/-- Normalized Hamming weight of every nonzero codeword of `paddedJustesenMap k` lies in
`[1/256, 1/2]`. -/
theorem normalizedHammingWeight_paddedJustesenMap_bounds (k : ℕ) {msg : Fin k → ZMod 2}
    (hmsg : msg ≠ 0) :
    (1 / 256 : ℝ) ≤ normalizedHammingWeight (paddedJustesenMap k msg) ∧
      normalizedHammingWeight (paddedJustesenMap k msg) ≤ 1 / 2 := by
  set s := justesenScale k
  set w := 16 * s
  have hw : w ≠ 0 := by have := justesenScale_pos k; omega
  have hN0_pos : 0 < justesenLen k := justesenLen_pos k
  let c : (Cslib.BinaryField w)ˣ → Cslib.BinaryField w :=
    fun u ↦ (justesenOuterPoly k msg).eval (u : Cslib.BinaryField w)
  let jw := Cslib.Code.justesen (Cslib.BinaryField.equivBits hw) c
  have hnorm_eq : hammingNorm (paddedJustesenMap k msg) = hammingNorm jw := by
    have h1 : (Finset.univ.filter fun v : Fin (paddedJustesenLen k) ↦
        paddedJustesenMap k msg v ≠ 0).card =
        (Finset.univ.filter fun u : Fin (justesenLen k) ↦
          jw (justesenIndexEquiv k u) ≠ false).card := by
      refine Finset.card_nbij'
        (fun v ↦ if h : v.val < justesenLen k then ⟨v.val, h⟩ else ⟨0, hN0_pos⟩)
        (fun u ↦ ⟨u.val, by unfold paddedJustesenLen; omega⟩)
        (fun v hv ↦ ?_) (fun u hu ↦ ?_) (fun v hv ↦ ?_) (fun u _ ↦ ?_)
      · have hne := (Finset.mem_filter.mp hv).2
        have hlt : v.val < justesenLen k := by
          by_contra hge
          apply hne; simp [paddedJustesenMap, hge]
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and, hlt, dite_true]
        intro hfalse
        apply hne
        rw [paddedJustesenMap_apply, dite_eq_left hlt]
        dsimp only
        dsimp only [jw, c] at hfalse
        rw [hfalse]
        simp
      · have hne := (Finset.mem_filter.mp hu).2
        have hlt : u.val < justesenLen k := u.isLt
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and,
          paddedJustesenMap, LinearMap.coe_mk, AddHom.coe_mk, hlt, dite_true]
        intro h0
        exact hne (Cslib.BitString.bitEquiv.symm.injective (by simpa using h0))
      · have hne := (Finset.mem_filter.mp hv).2
        have hlt : v.val < justesenLen k := by
          by_contra hge; apply hne; simp [paddedJustesenMap, hge]
        exact Fin.ext (by simp [hlt])
      · exact Fin.ext (by simp [u.isLt])
    rw [hammingNorm, h1]
    have h2 : (Finset.univ.filter fun u : Fin (justesenLen k) ↦
        jw (justesenIndexEquiv k u) ≠ false).card =
        (Finset.univ.filter fun idx ↦ jw idx ≠ false).card :=
      Finset.card_equiv (justesenIndexEquiv k) fun u ↦ by simp
    rw [h2]; rfl
  have hmem : jw ∈ Cslib.Code.justesenCode (Cslib.BinaryField.equivBits hw) (2 ^ (w - 1)) :=
    ⟨c, Cslib.Code.eval_mem_reedSolomon _ (justesenOuterPoly_degree_lt k msg), rfl⟩
  have h0mem : (0 : (Cslib.BinaryField w)ˣ × (Fin 2 × Fin w) → Bool) ∈
      Cslib.Code.justesenCode (Cslib.BinaryField.equivBits hw) (2 ^ (w - 1)) :=
    ⟨0, Submodule.zero_mem _, by
      funext idx; simp [Cslib.Code.justesen, Cslib.Code.concat, Cslib.Code.wozencraft]⟩
  have hjw_ne0 : jw ≠ 0 := by
    intro h0
    have hp0 : paddedJustesenMap k msg = 0 := by
      have : hammingNorm (paddedJustesenMap k msg) = 0 := by
        rw [hnorm_eq, h0]; simp
      exact hammingNorm_eq_zero.mp this
    exact hmsg (paddedJustesenMap_injective k (hp0.trans (map_zero _).symm))
  have hdist := Cslib.Code.card_le_mul_minDist_justesenCode (justesenScale_pos k)
    (Cslib.BinaryField.equivBits hw)
  have hmin_le : Cslib.Code.minDist
      (Cslib.Code.justesenCode (Cslib.BinaryField.equivBits hw) (2 ^ (w - 1))) ≤
        (hammingNorm jw : ℕ∞) := by
    have := Cslib.Code.minDist_le_hammingDist hmem h0mem hjw_ne0
    rwa [hammingDist_zero_right] at this
  have hcard_eq : Fintype.card ((Cslib.BinaryField w)ˣ × (Fin 2 × Fin w)) =
      justesenLen k := (Fintype.card_congr (justesenIndexEquiv k)).symm.trans (Fintype.card_fin _)
  have hN0_le : justesenLen k ≤ 128 * hammingNorm jw := by
    have hle : (Fintype.card ((Cslib.BinaryField w)ˣ × (Fin 2 × Fin w)) : ℕ∞) ≤
        128 * (hammingNorm jw : ℕ∞) := hdist.trans (by gcongr)
    rw [hcard_eq] at hle
    exact_mod_cast hle
  have hnorm_le : hammingNorm jw ≤ justesenLen k := by
    rw [← hcard_eq]
    exact hammingNorm_le_card_fintype
  have hN0_R : (0 : ℝ) < (justesenLen k : ℝ) := Nat.cast_pos.mpr hN0_pos
  rw [normalizedHammingWeight_eq_div, Fintype.card_fin, hnorm_eq, paddedJustesenLen]
  push_cast
  constructor
  · rw [le_div_iff₀ (by positivity)]
    have : (justesenLen k : ℝ) ≤ 128 * (hammingNorm jw : ℝ) := by exact_mod_cast hN0_le
    linarith
  · rw [div_le_iff₀ (by positivity)]
    have : (hammingNorm jw : ℝ) ≤ (justesenLen k : ℝ) := by exact_mod_cast hnorm_le
    linarith

/-- Constant expander power making `λ((arithmeticExpander n).pow abnnrExpanderPow) ≤ 1/256`. -/
def abnnrExpanderPow : ℕ := 400 * 257 ^ 16

theorem abnnrExpanderPow_eq : abnnrExpanderPow = 400 * 257 ^ 16 := by rfl

theorem abnnrExpanderPow_pos : 0 < abnnrExpanderPow := by
  unfold abnnrExpanderPow; positivity

theorem spectralExpansion_arithmeticExpander_pow_le (n : ℕ) :
    ((Cslib.RotationMap.arithmeticExpander n).pow abnnrExpanderPow).spectralExpansion ≤
      1 / 256 := by
  have h1 := (Cslib.RotationMap.arithmeticExpander n).spectralExpansion_pow_le abnnrExpanderPow
  have h2 := Cslib.RotationMap.spectralExpansion_arithmeticExpander_le n
  have hnn := (Cslib.RotationMap.arithmeticExpander n).spectralExpansion_nonneg
  have hexp : (1 - 9 / (400 * (257 : ℝ) ^ 16)) ^ abnnrExpanderPow ≤ Real.exp (-9) := by
    have hle : 1 - 9 / (400 * (257 : ℝ) ^ 16) ≤ Real.exp (-(9 / (400 * (257 : ℝ) ^ 16))) := by
      have := Real.add_one_le_exp (-(9 / (400 * (257 : ℝ) ^ 16)))
      linarith
    have hpos : 0 ≤ 1 - 9 / (400 * (257 : ℝ) ^ 16) := by norm_num
    calc (1 - 9 / (400 * (257 : ℝ) ^ 16)) ^ abnnrExpanderPow
        ≤ (Real.exp (-(9 / (400 * (257 : ℝ) ^ 16)))) ^ abnnrExpanderPow :=
          pow_le_pow_left₀ hpos hle _
      _ = Real.exp ((abnnrExpanderPow : ℝ) * (-(9 / (400 * (257 : ℝ) ^ 16)))) := by
          rw [← Real.exp_nat_mul]
      _ = Real.exp (-9) := by
          congr 1; unfold abnnrExpanderPow; push_cast; field_simp; ring
  have hexp9 : Real.exp (-9) ≤ 1 / 256 := by
    have he1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    have he9 : (256 : ℝ) ≤ Real.exp 9 := by
      have h9 : (Real.exp 1) ^ 9 = Real.exp 9 := by
        rw [← Real.exp_nat_mul]; norm_num
      have h29 : (256 : ℝ) ≤ (2 : ℝ) ^ 9 := by norm_num
      exact h29.trans (h9 ▸ pow_le_pow_left₀ (by norm_num) he1 9)
    rw [Real.exp_neg, inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) he9
  exact h1.trans ((pow_le_pow_left₀ hnn h2 _).trans (hexp.trans hexp9))

/-- Degree of `arithmeticExpander`. -/
def abnnrBaseDegree : ℕ := 2 * 257 ^ 12

theorem abnnrBaseDegree_eq : abnnrBaseDegree = 2 * 257 ^ 12 := by rfl

theorem abnnrBaseDegree_pos : 0 < abnnrBaseDegree := by
  unfold abnnrBaseDegree; positivity

/-- Length of the ABNNR92 binary linear code for dimension `k` and walk parameter `t`. -/
def abnnrLen (k t : ℕ) : ℕ :=
  paddedJustesenLen k * abnnrBaseDegree ^ (2 * abnnrExpanderPow * t)

theorem abnnrLen_eq (k t : ℕ) :
    abnnrLen k t = paddedJustesenLen k * abnnrBaseDegree ^ (2 * abnnrExpanderPow * t) := by rfl

theorem abnnrLen_pos (k t : ℕ) : 0 < abnnrLen k t := by
  unfold abnnrLen abnnrBaseDegree
  have := paddedJustesenLen_pos k
  positivity

theorem abnnrLen_le (k t : ℕ) :
    abnnrLen k t ≤ 2 ^ 22 * max 1 k * abnnrBaseDegree ^ (2 * abnnrExpanderPow * t) := by
  unfold abnnrLen paddedJustesenLen
  have h := justesenLen_le k
  have hmul : 2 * justesenLen k ≤ 2 ^ 22 * max 1 k := by
    calc 2 * justesenLen k ≤ 2 * (2 ^ 21 * max 1 k) := Nat.mul_le_mul_left 2 h
      _ = 2 ^ 22 * max 1 k := by ring
  exact Nat.mul_le_mul_right _ hmul

/-- Explicit base-`D` bijection between `Fin (D ^ L)` and `Fin L → Fin D`, mapping `x` to the
digit function `l ↦ (x / D ^ l) % D`. -/
def baseDEquiv (D : ℕ) (hD : 0 < D) : (L : ℕ) → Fin (D ^ L) ≃ (Fin L → Fin D)
  | 0 =>
    { toFun := fun _ i ↦ i.elim0
      invFun := fun _ ↦ ⟨0, by simp⟩
      left_inv := fun x ↦ Fin.ext (by dsimp; have := x.isLt; simp only [pow_zero] at this; omega)
      right_inv := fun f ↦ funext fun i ↦ i.elim0 }
  | L + 1 =>
    let eSplit : Fin (D ^ (L + 1)) ≃ Fin (D ^ L) × Fin D :=
      (finCongr (pow_succ D L)).trans finProdFinEquiv.symm
    let eRec : Fin (D ^ L) × Fin D ≃ (Fin L → Fin D) × Fin D :=
      Equiv.prodCongr (baseDEquiv D hD L) (Equiv.refl _)
    let eCons : (Fin L → Fin D) × Fin D ≃ (Fin (L + 1) → Fin D) :=
      (Equiv.prodComm _ _).trans (Fin.consEquiv fun _ ↦ Fin D)
    eSplit.trans (eRec.trans eCons)

theorem baseDEquiv_apply (D : ℕ) (hD : 0 < D) :
    ∀ (L : ℕ) (x : Fin (D ^ L)) (l : Fin L),
      (baseDEquiv D hD L x l).val = (x.val / D ^ l.val) % D
  | 0, _, l => l.elim0
  | L + 1, x, l => by
    refine Fin.cases ?_ ?_ l
    · simp only [baseDEquiv, Equiv.trans_apply, Equiv.prodCongr_apply,
        Equiv.prodComm_apply, Fin.consEquiv_apply, Fin.cons_zero, Fin.val_zero, pow_zero,
        Nat.div_one]
      rfl
    · intro j
      have hxlt : x.val / D < D ^ L := Nat.div_lt_of_lt_mul (by
        simpa [pow_succ, mul_comm] using x.isLt)
      have hrec := baseDEquiv_apply D hD L ⟨x.val / D, hxlt⟩ j
      change (baseDEquiv D hD L ⟨x.val / D, hxlt⟩ j).val = _
      rw [hrec, Nat.div_div_eq_div_mul]
      congr 2
      exact (pow_succ' D j.val).symm

/-- Explicit base-`D` index bijection between `Fin (abnnrLen k t)` and walks of length `2 * t` on
`(arithmeticExpander (paddedJustesenLen k)).pow abnnrExpanderPow`, matching `abnnrRowEval`. -/
noncomputable def abnnrWalkEquiv (k t : ℕ) :
    Fin (abnnrLen k t) ≃
      Fin (paddedJustesenLen k) ×
        (Fin (2 * t) → Fin abnnrExpanderPow →
          Cslib.RotationMap.AffinePlaneFamilyLabel (ZMod 257) 257) :=
  let D := abnnrBaseDegree
  let P := abnnrExpanderPow
  have hD : 0 < D := by unfold D abnnrBaseDegree; positivity
  let hdeg : Fintype.card (Cslib.RotationMap.AffinePlaneFamilyLabel (ZMod 257) 257) = D :=
    Cslib.RotationMap.card_affinePlaneFamilyLabel (ZMod.finEquiv 257).toEquiv.symm
  let lblEquiv : Cslib.RotationMap.AffinePlaneFamilyLabel (ZMod 257) 257 ≃ Fin D :=
    (Fintype.equivFin _).trans (finCongr hdeg)
  let e1 : Fin (abnnrLen k t) ≃ Fin (D ^ (2 * P * t)) × Fin (paddedJustesenLen k) :=
    (finCongr (mul_comm _ _)).trans finProdFinEquiv.symm
  let eFlat : Fin (D ^ (2 * P * t)) ≃ (Fin (2 * t) → Fin P → Fin D) :=
    (baseDEquiv D hD (2 * P * t)).trans
      ((Equiv.arrowCongr (finCongr (by ring : 2 * P * t = 2 * t * P)) (Equiv.refl _)).trans
        ((Equiv.arrowCongr finProdFinEquiv.symm (Equiv.refl _)).trans
          (Equiv.curry (Fin (2 * t)) (Fin P) (Fin D))))
  let eWalk : Fin (D ^ (2 * P * t)) ≃
      (Fin (2 * t) → Fin P → Cslib.RotationMap.AffinePlaneFamilyLabel (ZMod 257) 257) :=
    eFlat.trans (Equiv.arrowCongr (Equiv.refl _) (Equiv.arrowCongr (Equiv.refl _) lblEquiv.symm))
  e1.trans ((Equiv.prodComm _ _).trans (Equiv.prodCongr (Equiv.refl _) eWalk))

theorem abnnrWalkEquiv_fst (k t : ℕ) (i : Fin (abnnrLen k t)) :
    (abnnrWalkEquiv k t i).1.val = i.val % paddedJustesenLen k := by
  rfl

theorem abnnrWalkEquiv_snd (k t : ℕ) (i : Fin (abnnrLen k t)) (j : Fin (2 * t))
    (s : Fin abnnrExpanderPow) :
    (abnnrWalkEquiv k t i).2 j s =
      (Fintype.equivFin (Cslib.RotationMap.AffinePlaneFamilyLabel (ZMod 257) 257)).symm
        ⟨((i.val / paddedJustesenLen k) / abnnrBaseDegree ^ (j.val * abnnrExpanderPow + s.val)) %
            abnnrBaseDegree, by
          rw [Cslib.RotationMap.card_affinePlaneFamilyLabel (ZMod.finEquiv 257).toEquiv.symm]
          exact Nat.mod_lt _ (by unfold abnnrBaseDegree; positivity)⟩ := by
  have hD : 0 < abnnrBaseDegree := by unfold abnnrBaseDegree; positivity
  have hilt : i.val / paddedJustesenLen k < abnnrBaseDegree ^ (2 * abnnrExpanderPow * t) :=
    Nat.div_lt_of_lt_mul i.isLt
  have hjs : j.val * abnnrExpanderPow + s.val < 2 * abnnrExpanderPow * t := by
    have hj : j.val < 2 * t := j.isLt
    have hs : s.val < abnnrExpanderPow := s.isLt
    have h1 : j.val * abnnrExpanderPow + s.val < (j.val + 1) * abnnrExpanderPow := by
      rw [add_mul, one_mul]; omega
    have h2 : (j.val + 1) * abnnrExpanderPow ≤ (2 * t) * abnnrExpanderPow :=
      Nat.mul_le_mul_right _ hj
    calc j.val * abnnrExpanderPow + s.val < (2 * t) * abnnrExpanderPow := h1.trans_le h2
      _ = 2 * abnnrExpanderPow * t := by ring
  have h := baseDEquiv_apply abnnrBaseDegree hD (2 * abnnrExpanderPow * t)
    ⟨i.val / paddedJustesenLen k, hilt⟩ ⟨j.val * abnnrExpanderPow + s.val, hjs⟩
  let hdeg : Fintype.card (Cslib.RotationMap.AffinePlaneFamilyLabel (ZMod 257) 257) =
      abnnrBaseDegree :=
    Cslib.RotationMap.card_affinePlaneFamilyLabel (ZMod.finEquiv 257).toEquiv.symm
  have hwalk : (abnnrWalkEquiv k t i).2 j s =
      (Fintype.equivFin (Cslib.RotationMap.AffinePlaneFamilyLabel (ZMod 257) 257)).symm
        ((finCongr hdeg).symm
          (baseDEquiv abnnrBaseDegree hD (2 * abnnrExpanderPow * t)
            (finProdFinEquiv.symm (finCongr (mul_comm _ _) i)).1
            (finCongr (by ring : 2 * t * abnnrExpanderPow = 2 * abnnrExpanderPow * t)
              (finProdFinEquiv (j, s))))) := rfl
  rw [hwalk]
  refine congrArg
    (Fintype.equivFin (Cslib.RotationMap.AffinePlaneFamilyLabel (ZMod 257) 257)).symm
    (Fin.ext ?_)
  have h1 : (finProdFinEquiv.symm (finCongr (mul_comm _ _) i)).1 =
      ⟨i.val / paddedJustesenLen k, hilt⟩ := Fin.ext rfl
  have h2 : finCongr (by ring : 2 * t * abnnrExpanderPow = 2 * abnnrExpanderPow * t)
      (finProdFinEquiv (j, s)) = ⟨j.val * abnnrExpanderPow + s.val, hjs⟩ := by
    apply Fin.ext
    simp [finProdFinEquiv]; ring
  rw [h1, h2, finCongr_symm, finCongr_apply, Fin.val_cast]
  exact h

/-- Explicit ABNNR92 binary linear code map of dimension `k` and length `abnnrLen k t`. -/
noncomputable def abnnrGenMap (k t : ℕ) :
    (Fin k → ZMod 2) →ₗ[ZMod 2] (Fin (abnnrLen k t) → ZMod 2) where
  toFun msg i :=
    let G := (Cslib.RotationMap.arithmeticExpander (paddedJustesenLen k)).pow abnnrExpanderPow
    let p := abnnrWalkEquiv k t i
    ∑ j : Fin t, paddedJustesenMap k msg (G.walkAt p (2 * j.val + 1))
  map_add' m₁ m₂ := by
    funext i
    simp [map_add, Finset.sum_add_distrib]
  map_smul' r msg := by
    funext i
    simp [map_smul, Finset.mul_sum]

theorem abnnrGenMap_apply (k t : ℕ) (msg : Fin k → ZMod 2) (i : Fin (abnnrLen k t)) :
    abnnrGenMap k t msg i =
      ∑ j : Fin t, paddedJustesenMap k msg
        (((Cslib.RotationMap.arithmeticExpander (paddedJustesenLen k)).pow
          abnnrExpanderPow).walkAt (abnnrWalkEquiv k t i) (2 * j.val + 1)) := by rfl

/-- Every nonzero codeword of `abnnrGenMap k t` is `(255 / 256) ^ t`-biased. -/
theorem isVectorBiased_abnnrGenMap (k t : ℕ) {msg : Fin k → ZMod 2} (hmsg : msg ≠ 0) :
    IsVectorBiased ((255 / 256 : ℝ) ^ t) (abnnrGenMap k t msg) := by
  have : Nonempty (Fin (paddedJustesenLen k)) := ⟨⟨0, paddedJustesenLen_pos k⟩⟩
  have : Nonempty (Fin abnnrExpanderPow →
      Cslib.RotationMap.AffinePlaneFamilyLabel (ZMod 257) 257) :=
    ⟨fun _ ↦ Sum.inl (0, ((0, 0), (0, 0)))⟩
  have ⟨hlo, hhi⟩ := normalizedHammingWeight_paddedJustesenMap_bounds k hmsg
  have hwalk := isVectorBiased_walkParity
    ((Cslib.RotationMap.arithmeticExpander (paddedJustesenLen k)).pow abnnrExpanderPow)
    (spectralExpansion_arithmeticExpander_pow_le (paddedJustesenLen k))
    (paddedJustesenMap k msg) hlo hhi t
  rw [isVectorBiased_iff] at hwalk ⊢
  intro a ha
  have hcard : Fintype.card (Fin (abnnrLen k t)) =
      Fintype.card (Fin (paddedJustesenLen k) ×
        (Fin (2 * t) → Fin abnnrExpanderPow →
          Cslib.RotationMap.AffinePlaneFamilyLabel (ZMod 257) 257)) :=
    Fintype.card_congr (abnnrWalkEquiv k t)
  rw [hcard]
  have hsum :
      ∑ i : Fin (abnnrLen k t), canonicalAddChar (ZMod 2) (a * abnnrGenMap k t msg i) =
        ∑ p, canonicalAddChar (ZMod 2) (a * ∑ j : Fin t,
          paddedJustesenMap k msg
            (((Cslib.RotationMap.arithmeticExpander (paddedJustesenLen k)).pow
              abnnrExpanderPow).walkAt p (2 * j.val + 1))) :=
    Fintype.sum_equiv (abnnrWalkEquiv k t) _ _ fun _ ↦ rfl
  rw [hsum]
  exact hwalk a ha

/-- For `t ≥ 1`, `abnnrGenMap k t` is injective (hence has full dimension `k`). -/
theorem abnnrGenMap_injective (k : ℕ) {t : ℕ} (ht : 1 ≤ t) :
    Function.Injective (abnnrGenMap k t) := by
  rw [injective_iff_map_eq_zero]
  intro msg hmsg
  by_contra hne
  have : Nonempty (Fin (abnnrLen k t)) := ⟨⟨0, abnnrLen_pos k t⟩⟩
  have hbias := isVectorBiased_abnnrGenMap k t hne
  have ⟨hlo, _⟩ := normalizedHammingWeight_bounds_of_isVectorBiased hbias
  have hwt0 : normalizedHammingWeight (abnnrGenMap k t msg) = 0 := by
    rw [hmsg, normalizedHammingWeight_zero]
  have hlt1 : (255 / 256 : ℝ) ^ t < 1 :=
    pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
  have hpos : (0 : ℝ) < ((Fintype.card (ZMod 2) : ℝ) - 1) / (Fintype.card (ZMod 2) : ℝ) *
      (1 - (255 / 256 : ℝ) ^ t) := by
    rw [ZMod.card]; norm_num; linarith
  linarith

/-- Explicit ABNNR92 existence theorem: for every `k ≥ 1` and `0 < η ≤ 1`, choosing
`t = Nat.ceil (Real.log (1 / η) / Real.log (256 / 255))` yields an `η`-biased binary linear code
of dimension `k` and length `abnnrLen k t` (linear in `k`, polynomial in `1/η`). -/
theorem exists_abnnr_smallBias_linear (k : ℕ) {η : ℝ} (hη0 : 0 < η) (_hη1 : η ≤ 1) :
    ∃ (t : ℕ), 1 ≤ t ∧
      (255 / 256 : ℝ) ^ t ≤ η ∧
      Function.Injective (abnnrGenMap k t) ∧
      (∀ msg : Fin k → ZMod 2, msg ≠ 0 → IsVectorBiased η (abnnrGenMap k t msg)) := by
  set t := max 1 (Nat.ceil (Real.log (1 / η) / Real.log (256 / 255)))
  have ht1 : 1 ≤ t := le_max_left _ _
  have hpow : (255 / 256 : ℝ) ^ t ≤ η := by
    have hlog_pos : 0 < Real.log (256 / 255 : ℝ) := Real.log_pos (by norm_num)
    have ht_ge : Real.log (1 / η) / Real.log (256 / 255) ≤ (t : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast le_max_right 1 _)
    have hmul : Real.log (1 / η) ≤ (t : ℝ) * Real.log (256 / 255) :=
      (div_le_iff₀ hlog_pos).mp ht_ge
    have hexp := Real.exp_le_exp.mpr hmul
    rw [Real.exp_log (by positivity), ← Real.log_pow,
      Real.exp_log (by positivity)] at hexp
    have hinv : (255 / 256 : ℝ) ^ t = ((256 / 255 : ℝ) ^ t)⁻¹ := by
      rw [← inv_pow]; norm_num
    rw [hinv]
    rw [one_div] at hexp
    exact (inv_le_comm₀ (by positivity) hη0).mpr hexp
  refine ⟨t, ht1, hpow, abnnrGenMap_injective k ht1, fun msg hmsg ↦ ?_⟩
  rw [isVectorBiased_iff]
  intro a ha
  have hb := (isVectorBiased_iff.mp (isVectorBiased_abnnrGenMap k t hmsg)) a ha
  exact hb.trans (mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg _))

end ABNNR


end CslibFrontier.Foundations.Data.Code
