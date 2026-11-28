module

public import CslibFrontier.Computability.Circuit.Boolean.AC0
public import CslibFrontier.Computability.Circuit.Boolean.Unbounded
public import CslibFrontier.Foundations.Data.BitString.Basic
public import CslibFrontier.Foundations.Data.BitString.Weight
public import CslibFrontier.Probability.PMF
public import CslibFrontier.Probability.PMF.Uniform

import CslibFrontier.Computability.Circuit.Boolean.Majority
import CslibFrontier.Computability.Circuit.Boolean.ShallowSymmetric
import CslibFrontier.Computability.Circuit.CompositionDepth
import CslibFrontier.Computability.Circuit.Pi
import CslibFrontier.Foundations.Analysis.SpecialFunctions.ExpBounds
import CslibFrontier.Foundations.Analysis.SpecialFunctions.ExpLogQuadratic
import CslibFrontier.Foundations.Data.Nat.Log
import CslibFrontier.Foundations.Data.Nat.PolynomialBound.Closure
import CslibFrontier.Probability.Chernoff
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.Product
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Constant-Depth AC⁰ Relative-Threshold Approximate Counting

This module formalizes non-uniform constant-depth polynomial-size approximate Hamming-weight
counting circuits for fixed relative accuracy `ε > 0`, together with the sharp quantifier
necessity showing that no single constant-depth polynomial-size family works uniformly for all
`ε > 0` simultaneously.

## Main results

* `CslibFrontier.Computability.Circuit.Boolean.ApproximateCount.approxCount_unquantified_eps_false`:
  no single AC⁰ family resolves relative Hamming-weight thresholds uniformly for all `ε > 0`.
* `CslibFrontier.Computability.Circuit.Boolean.ApproximateCount.exists_approxCount_circuit`:
  for every fixed `ε > 0`, depth-7 polynomial-size unbounded fan-in circuits distinguish
  Hamming weight `≤ (1 - ε) * a` from `≥ (1 + ε) * a`.
-/

public section

namespace CslibFrontier.Computability.Circuit.Boolean.ApproximateCount

open Cslib Cslib.BitString Cslib.Circuits Cslib.Circuits.Boolean Cslib.Circuits.Boolean.Unbounded
open Cslib.Probability.PMF Finset

/-! ### Part 1: Impossibility of Uniform Relative-Error AC⁰ Counting Across All `ε > 0` -/

/-- Duplicating each input bit twice as a zero-gate wiring circuit `Fin n → Fin (2 * n)`. -/
private def dupWiring (n : ℕ) : Circuit Unbounded.signature n (2 * n) :=
  Circuit.wiring Unbounded.signature fun i : Fin (2 * n) => ⟨i.1 / 2, by omega⟩

private lemma weight_eval_dupWiring (n : ℕ) (x : BitString n) :
    BitString.weight ((dupWiring n).eval Unbounded.interpretation x) = 2 * BitString.weight x := by
  have h1 : ∀ i : Fin (2 * n), (dupWiring n).eval Unbounded.interpretation x i =
      x ⟨i.1 / 2, by omega⟩ := fun _ => rfl
  simp only [BitString.weight, h1]
  have hbij :
      (Finset.univ.filter fun i : Fin (2 * n) => x ⟨i.1 / 2, by omega⟩ = true).card =
        ((Finset.univ.filter fun j : Fin n => x j = true) ×ˢ
          (Finset.univ : Finset (Fin 2))).card := by
    refine Finset.card_bij
      (fun i _ => (⟨i.1 / 2, by omega⟩, ⟨i.1 % 2, Nat.mod_lt _ (by omega)⟩))
      (fun i hi => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
        simp [hi])
      (fun i₁ _ i₂ _ h => by
        simp only [Prod.mk.injEq, Fin.ext_iff] at h
        exact Fin.ext (by omega))
      (fun p hp => by
        simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and] at hp
        refine ⟨⟨2 * p.1.1 + p.2.1, by omega⟩, ?_, ?_⟩
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          have hdiv : (2 * p.1.1 + p.2.1) / 2 = p.1.1 := by omega
          simpa [hdiv] using hp.1
        · ext <;> dsimp <;> omega)
  rw [hbij, Finset.card_product, Finset.card_univ, Fintype.card_fin, mul_comm]

/-- No single constant-depth polynomial-size AC⁰ family can approximate Hamming weight within
relative error `1 ± ε` simultaneously for all `ε > 0`, even for integer thresholds `1 ≤ a < m`.
Taking `m = 2n`, `a = 2⌈n/2⌉ - 1`, and `ε = 1 / (2a + 1)` on bit-duplicated inputs computes exact
`majority`, contradicting `majority_notMem_AC0`. -/
theorem approxCount_unquantified_eps_false :
    ¬ ∃ (d : ℕ) (s : ℕ → ℕ), PolynomiallyBounded s ∧
      ∀ (m a : ℕ) (ε : ℝ), 1 ≤ a → a < m → 0 < ε →
        ∃ C : Circuit Unbounded.signature m 1,
          C.depth ≤ d ∧ C.size ≤ s m ∧
          (∀ x : BitString m, (BitString.weight x : ℝ) ≤ (1 - ε) * a →
            C.eval Unbounded.interpretation x 0 = true) ∧
          (∀ x : BitString m, (1 + ε) * a ≤ (BitString.weight x : ℝ) →
            C.eval Unbounded.interpretation x 0 = false) := by
  rintro ⟨d, s, hs, hfam⟩
  apply majority_notMem_AC0
  rw [AC0, ConstDepth.mem_iff]
  refine ⟨d + 1, fun n => s (2 * n) + 2, ?_, fun n => ?_⟩
  · have hcomp : PolynomiallyBounded fun n => s (2 * n) := hs.comp (by fun_prop)
    fun_prop
  · rw [Language.slice_ofSlices]
    by_cases hn2 : n < 2
    · interval_cases n
      · refine ⟨constCircuit (.id _) true, fun x => funext fun j => ?_, ?_, ?_⟩
        · fin_cases j
          simp [majority, threshold, BitString.weight]
        · exact (depth_constCircuit_le (φ := .id _) true).trans (by omega)
        · simp
      · refine ⟨Circuit.wiring Unbounded.signature (fun _ => (0 : Fin 1)),
          fun x => funext fun j => ?_, ?_, ?_⟩
        · fin_cases j
          simp only [Circuit.eval_wiring, single_apply, majority, threshold, BitString.weight,
            Finset.univ_unique, Fin.default_eq_zero]
          cases hx : x 0 <;> simp [Finset.filter_singleton, hx]
        · simp
        · simp
    · push Not at hn2
      let a : ℕ := 2 * ((n + 1) / 2) - 1
      have ha1 : 1 ≤ a := by omega
      have ham : a < 2 * n := by omega
      let ε : ℝ := 1 / (2 * (a : ℝ) + 1)
      have hε : 0 < ε := by positivity
      obtain ⟨C, hCd, hCs, hlo, hhi⟩ := hfam (2 * n) a ε ha1 ham hε
      let D : Circuit Unbounded.signature n 1 :=
        notCircuit (.id _) (C.comp (dupWiring n))
      refine ⟨D, fun x => funext fun j => ?_, ?_, ?_⟩
      · fin_cases j
        simp only [D, eval_notCircuit, Circuit.eval_comp, single_apply, majority, threshold]
        have hw := weight_eval_dupWiring n x
        have hεa : ε * (a : ℝ) < 1 / 2 := by
          dsimp only [ε]
          rw [one_div_mul_eq_div, div_lt_div_iff₀ (by positivity) (by norm_num)]
          linarith
        by_cases hmaj : (n + 1) / 2 ≤ BitString.weight x
        · have hge : (1 + ε) * (a : ℝ) ≤
              (BitString.weight ((dupWiring n).eval Unbounded.interpretation x) : ℝ) := by
            rw [hw]
            have hnat : a + 1 ≤ 2 * BitString.weight x := by omega
            have hreal : (a : ℝ) + 1 ≤ (2 * BitString.weight x : ℕ) := by exact_mod_cast hnat
            nlinarith
          rw [hhi _ hge]
          simp [hmaj]
        · have hle : (BitString.weight ((dupWiring n).eval Unbounded.interpretation x) : ℝ) ≤
              (1 - ε) * (a : ℝ) := by
            rw [hw]
            have hnat : 2 * BitString.weight x + 1 ≤ a := by omega
            have hreal : ((2 * BitString.weight x : ℕ) : ℝ) + 1 ≤ (a : ℝ) := by
              exact_mod_cast hnat
            nlinarith
          rw [hlo _ hle]
          simp [hmaj]
      · calc D.depth ≤ (C.comp (dupWiring n)).depth + 1 := depth_notCircuit_le _
          _ ≤ (C.depth + (dupWiring n).depth) + 1 :=
              Nat.add_le_add_right (Circuit.depth_comp_le _ _) 1
          _ ≤ d + 1 := by simp [dupWiring]; omega
      · simp [D, dupWiring]
        omega

/-! ### Part 2: Probabilistic & Circuit Helpers for Approximate Counting -/

/-- Uniform distribution on functions `ι → α` equals the independent product `PMF.pi` of
uniform distributions on `α`. -/
private theorem uniformOfFintype_pi_eq {ι α : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype α] [Nonempty α] :
    uniformOfFintype (ι → α) =
      pi (fun _ : ι => uniformOfFintype α) := by
  ext f
  simp only [uniformOfFintype_apply, pi_apply, Fintype.card_fun, Finset.prod_const,
    Finset.card_univ, Nat.cast_pow, ENNReal.inv_pow]

/-- Bernoulli's inequality for `t ≤ 1`: `1 - k * t ≤ (1 - t) ^ k`. -/
private theorem one_sub_mul_le_pow {t : ℝ} (ht1 : t ≤ 1) (k : ℕ) :
    1 - (k : ℝ) * t ≤ (1 - t) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    push_cast
    rw [pow_succ]
    have hmul : (1 - (k : ℝ) * t) * (1 - t) ≤ (1 - t) ^ k * (1 - t) :=
      mul_le_mul_of_nonneg_right ih (by linarith)
    nlinarith [mul_nonneg (Nat.cast_nonneg k) (sq_nonneg t)]

/-- Additive Hoeffding-style upper tail derived from `pi_sum_ge_le_exp` and
`Real.exp_neg_le_one_sub_add_sq`: if independent scores in `[0, 1]` over `Fin r` have mean `≤ μ`,
then `Pr[∑ score ≥ μ + r * γ] ≤ exp(-(r * γ^2 / 4))` for every `0 ≤ γ ≤ 1`. -/
private theorem pi_sum_ge_add_le_exp {r : ℕ} {α : Fin r → Type*}
    [∀ i, Fintype (α i)] (p : ∀ i, PMF (α i)) (score : ∀ i, α i → ℝ)
    (hscore : ∀ i a, a ∈ (p i).support → score i a ∈ Set.Icc 0 1)
    {μ γ : ℝ} (hμ : ∑ i, ∑ a, (p i a).toReal * score i a ≤ μ)
    (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) :
    ((pi p).toOuterMeasure {outcome | μ + r * γ ≤ ∑ i, score i (outcome i)}).toReal ≤
      Real.exp (-(r * γ ^ 2 / 4)) := by
  let t : ℝ := γ / 2
  have ht0 : 0 ≤ t := by positivity
  have ht1 : t ≤ 1 := by dsimp [t]; linarith
  have hexp : Real.exp t - 1 ≤ t + t ^ 2 := by
    have h := Real.exp_neg_le_one_sub_add_sq (y := -t) (by linarith)
    rw [neg_neg, sub_neg_eq_add, neg_sq] at h
    linarith
  have hmean_le_r : ∑ i, ∑ a, (p i a).toReal * score i a ≤ (r : ℝ) := by
    calc ∑ i, ∑ a, (p i a).toReal * score i a
        ≤ ∑ i : Fin r, ∑ a : α i, (p i a).toReal := by
          refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun a _ => ?_
          by_cases ha : a ∈ (p i).support
          · have h1 := (hscore i a ha).2
            nlinarith [ENNReal.toReal_nonneg (a := p i a)]
          · rw [PMF.mem_support_iff, not_not] at ha
            simp [ha]
      _ = ∑ _i : Fin r, (1 : ℝ) := Finset.sum_congr rfl fun i _ => by
          have hsum : ∑ a : α i, p i a = 1 := by simpa [tsum_fintype] using (p i).tsum_coe
          rw [← ENNReal.toReal_sum (fun a _ => PMF.apply_ne_top _ _), hsum, ENNReal.toReal_one]
      _ = (r : ℝ) := by simp
  have hmean_nonneg : 0 ≤ ∑ i, ∑ a, (p i a).toReal * score i a := by
    refine Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun a _ => ?_
    by_cases ha : a ∈ (p i).support
    · exact mul_nonneg ENNReal.toReal_nonneg (hscore i a ha).1
    · rw [PMF.mem_support_iff, not_not] at ha; simp [ha]
  refine (pi_sum_ge_le_exp p score hscore ht0 (μ + r * γ)).trans (Real.exp_le_exp.mpr ?_)
  set m := ∑ i, ∑ a, (p i a).toReal * score i a
  have h1 : m * (Real.exp t - 1) ≤ m * (t + t ^ 2) := mul_le_mul_of_nonneg_left hexp hmean_nonneg
  have h2 : m * t ^ 2 ≤ (r : ℝ) * t ^ 2 := mul_le_mul_of_nonneg_right hmean_le_r (sq_nonneg t)
  have h3 : m * t ≤ μ * t := mul_le_mul_of_nonneg_right hμ ht0
  have h4 : (r : ℝ) * t ^ 2 - t * ((r : ℝ) * γ) = -(r * γ ^ 2 / 4) := by dsimp [t]; ring
  nlinarith

/-- Symmetric threshold `weight y < T` on `r` bits. -/
private def ltThreshold (r T : ℕ) : BooleanFunction r :=
  fun y => decide (BitString.weight y < T)

private lemma isSymmetric_ltThreshold (r T : ℕ) :
    BooleanFunction.IsSymmetric (ltThreshold r T) := by
  intro x y hxy
  simp [ltThreshold, hxy]

/-- Exact counting formula for the probability of a set under `uniformOfFintype`. -/
private lemma uniformOfFintype_toOuterMeasure_toReal {β : Type*} [Fintype β] [Nonempty β]
    (S : Set β) [DecidablePred (· ∈ S)] :
    ((uniformOfFintype β).toOuterMeasure S).toReal =
      ((Finset.univ.filter fun a : β => a ∈ S).card : ℝ) / (Fintype.card β : ℝ) := by
  rw [toOuterMeasure_apply_toReal]
  trans (∑ a ∈ Finset.univ.filter (fun a : β => a ∈ S), (uniformOfFintype β a).toReal)
  · rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun a _ => ?_
    by_cases ha : a ∈ S <;> simp [ha]
  · simp only [uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast,
      Finset.sum_const, nsmul_eq_mul, ← div_eq_mul_inv]

/-- The exact probability that the OR of `k` i.i.d. uniform coordinates of `x : BitString m`
evaluates to `true` is `1 - (1 - weight x / m) ^ k`. -/
private lemma prob_orSample_eq {m k : ℕ} (hm : 0 < m) [Nonempty (Fin m)] (x : BitString m) :
    ((uniformOfFintype (Fin k → Fin m)).toOuterMeasure
      {idx | (∃ t : Fin k, x (idx t) = true)}).toReal =
      1 - (1 - (BitString.weight x : ℝ) / m) ^ k := by
  classical
  rw [toOuterMeasure_toReal_add_compl (uniformOfFintype (Fin k → Fin m)) _ |> fun h =>
    show ((uniformOfFintype (Fin k → Fin m)).toOuterMeasure _).toReal =
      1 - ((uniformOfFintype (Fin k → Fin m)).toOuterMeasure _ᶜ).toReal by linarith]
  congr 1
  rw [uniformOfFintype_toOuterMeasure_toReal]
  have hfilt : (Finset.univ.filter fun idx : Fin k → Fin m =>
      idx ∈ {idx : Fin k → Fin m | ∃ t : Fin k, x (idx t) = true}ᶜ) =
      Finset.univ.filter fun idx : Fin k → Fin m => ∀ t : Fin k, x (idx t) = false := by
    ext idx; simp
  rw [hfilt]
  simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
  let Z : Finset (Fin m) := Finset.univ.filter fun i : Fin m => x i = false
  have hcard_eq :
      (Finset.univ.filter fun idx : Fin k → Fin m => ∀ t : Fin k, x (idx t) = false).card =
        Z.card ^ k := by
    have hbij :
        (Finset.univ.filter fun idx : Fin k → Fin m => ∀ t : Fin k, x (idx t) = false).card =
          Fintype.card (Fin k → {i : Fin m // i ∈ Z}) := by
      rw [← Finset.card_univ]
      refine Finset.card_bij
        (fun idx hidx t => ⟨idx t, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          (Finset.mem_filter.mp hidx).2 t⟩⟩)
        (fun _ _ => Finset.mem_univ _)
        (fun idx₁ _ idx₂ _ h => funext fun t => congrArg Subtype.val (congrFun h t))
        (fun f _ => ⟨fun t => (f t).1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun t =>
          (Finset.mem_filter.mp (f t).2).2⟩, rfl⟩)
    rw [hbij, Fintype.card_fun, Fintype.card_coe, Fintype.card_fin]
  have hZcard : Z.card + BitString.weight x = m := by
    have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin m)))
      (fun i => x i = false)
    simpa [Z, BitString.weight] using h
  have hZreal : (Z.card : ℝ) / m = 1 - (BitString.weight x : ℝ) / m := by
    have hm0 : (m : ℝ) ≠ 0 := by positivity
    have hZr : (Z.card : ℝ) + (BitString.weight x : ℝ) = m := by exact_mod_cast hZcard
    field_simp
    linarith
  rw [hcard_eq, Nat.cast_pow, ← div_pow, hZreal]

/-- Single-sample OR probability separation for `0 < ε' ≤ 1/2`, `1 ≤ a`, `(1 + ε') * a ≤ m`:
there exist `k ≥ 1` (`k ≤ m`) and `θ ∈ [0, 1]` such that `weight x ≤ (1 - ε') * a` implies
`p_k(x) ≤ θ - ε'^2 / 16` and `weight x ≥ (1 + ε') * a` implies `p_k(x) ≥ θ + ε'^2 / 16`. -/
private theorem exists_orSample_params {m : ℕ} {a ε' : ℝ}
    (hε0 : 0 < ε') (hε1 : ε' ≤ 1 / 2) (ha1 : 1 ≤ a) (ham : (1 + ε') * a ≤ m) :
    ∃ (k : ℕ) (θ : ℝ), 1 ≤ k ∧ k ≤ m ∧ 0 ≤ θ ∧ θ ≤ 1 ∧
      (∀ x : BitString m, (BitString.weight x : ℝ) ≤ (1 - ε') * a →
        1 - (1 - (BitString.weight x : ℝ) / m) ^ k ≤ θ - ε' ^ 2 / 16) ∧
      (∀ x : BitString m, (1 + ε') * a ≤ (BitString.weight x : ℝ) →
        θ + ε' ^ 2 / 16 ≤ 1 - (1 - (BitString.weight x : ℝ) / m) ^ k) := by
  have hm_pos : (0 : ℝ) < m := by nlinarith
  by_cases hreg : ε' * (m : ℝ) / (4 * a) < 1
  · -- Regime 1: `k = 1`, direct coordinate sampling
    refine ⟨1, a / m, le_rfl, by
        have : (1 : ℝ) ≤ m := by nlinarith
        exact_mod_cast this,
      by positivity, by
        rw [div_le_one hm_pos]; nlinarith, ?_, ?_⟩
    · intro x hx
      simp only [pow_one, sub_sub_cancel]
      have hgap : ε' ^ 2 / 16 ≤ ε' * a / m := by
        rw [div_le_div_iff₀ (by norm_num) hm_pos]
        have h1 : ε' * (m : ℝ) < 4 * a := (div_lt_one (by positivity)).mp hreg
        nlinarith
      have h1 : (BitString.weight x : ℝ) / m ≤ (1 - ε') * a / m :=
        div_le_div_of_nonneg_right hx hm_pos.le
      have h2 : (1 - ε') * a / m = a / m - ε' * a / m := by ring
      linarith
    · intro x hx
      simp only [pow_one, sub_sub_cancel]
      have hgap : ε' ^ 2 / 16 ≤ ε' * a / m := by
        rw [div_le_div_iff₀ (by norm_num) hm_pos]
        have h1 : ε' * (m : ℝ) < 4 * a := (div_lt_one (by positivity)).mp hreg
        nlinarith
      have h1 : (1 + ε') * a / m ≤ (BitString.weight x : ℝ) / m :=
        div_le_div_of_nonneg_right hx hm_pos.le
      have h2 : (1 + ε') * a / m = a / m + ε' * a / m := by ring
      linarith
  · -- Regime 2: `k = ⌊ε' * m / (4 * a)⌋ ≥ 1`, OR-sampling
    push Not at hreg
    let k : ℕ := Nat.floor (ε' * (m : ℝ) / (4 * a))
    have hk1 : 1 ≤ k := Nat.le_floor (by exact_mod_cast hreg : ((1 : ℕ) : ℝ) ≤ _)
    have hk_le_real : (k : ℝ) ≤ ε' * (m : ℝ) / (4 * a) := Nat.floor_le (by positivity)
    have hk_le_m : k ≤ m := by
      have h1 : (k : ℝ) ≤ m := by
        calc (k : ℝ) ≤ ε' * (m : ℝ) / (4 * a) := hk_le_real
          _ ≤ (1 / 2) * (m : ℝ) / (4 * 1) := by gcongr
          _ ≤ m := by linarith
      exact_mod_cast h1
    have hlt_k : ε' * (m : ℝ) / (4 * a) < (k : ℝ) + 1 := Nat.lt_floor_add_one _
    have hk_ge_half : ε' * (m : ℝ) / (8 * a) ≤ (k : ℝ) := by
      have hk1' : (1 : ℝ) ≤ k := by exact_mod_cast hk1
      have hdiv : ε' * (m : ℝ) / (8 * a) = (ε' * (m : ℝ) / (4 * a)) / 2 := by ring
      linarith
    let u : ℝ := (k : ℝ) * a / m
    have hu_lo : ε' / 8 ≤ u := by
      dsimp only [u]
      rw [div_le_div_iff₀ (by norm_num) hm_pos]
      have h1 := mul_le_mul_of_nonneg_right hk_ge_half (show (0 : ℝ) ≤ 8 * a by positivity)
      rw [div_mul_cancel₀ _ (by positivity)] at h1
      linarith
    have hu_hi : u ≤ ε' / 4 := by
      dsimp only [u]
      rw [div_le_div_iff₀ hm_pos (by norm_num)]
      have h1 := mul_le_mul_of_nonneg_right hk_le_real (show (0 : ℝ) ≤ 4 * a by positivity)
      rw [div_mul_cancel₀ _ (by positivity)] at h1
      linarith
    let θ : ℝ := (1 - ε' / 4) * u
    refine ⟨k, θ, hk1, hk_le_m, by dsimp [θ]; nlinarith, by dsimp [θ]; nlinarith, ?_, ?_⟩
    · intro x hx
      have ht1 : (BitString.weight x : ℝ) / m ≤ 1 := by
        rw [div_le_one hm_pos]; exact_mod_cast BitString.weight_le_length x
      have hbern := one_sub_mul_le_pow ht1 k
      have hkm : (k : ℝ) * ((BitString.weight x : ℝ) / m) ≤ (1 - ε') * u := by
        calc (k : ℝ) * ((BitString.weight x : ℝ) / m)
            ≤ (k : ℝ) * (((1 - ε') * a) / m) := by gcongr
          _ = (1 - ε') * u := by dsimp [u]; ring
      have hgap : (1 - ε') * u ≤ θ - ε' ^ 2 / 16 := by
        dsimp [θ]
        nlinarith [hu_lo]
      linarith
    · intro x hx
      have hw_le_m : (BitString.weight x : ℝ) ≤ m := by exact_mod_cast BitString.weight_le_length x
      have ht_ge : (1 + ε') * a / m ≤ (BitString.weight x : ℝ) / m :=
        div_le_div_of_nonneg_right hx hm_pos.le
      have hpow_le : (1 - (BitString.weight x : ℝ) / m) ^ k ≤
          Real.exp (-((1 + ε') * u)) := by
        have h1 : 1 - (BitString.weight x : ℝ) / m ≤ 1 - (1 + ε') * a / m := by linarith
        have h2 : 0 ≤ 1 - (BitString.weight x : ℝ) / m := by
          rw [sub_nonneg, div_le_one hm_pos]; exact hw_le_m
        calc (1 - (BitString.weight x : ℝ) / m) ^ k
            ≤ (1 - (1 + ε') * a / m) ^ k := pow_le_pow_left₀ h2 h1 k
          _ ≤ Real.exp (-((1 + ε') * u)) :=
              Real.one_sub_pow_le_exp ((div_le_one hm_pos).mpr ham)
                (by dsimp [u]; ring_nf; rfl)
      have hexp := Real.exp_neg_le_one_sub_add_sq_div_two (x := (1 + ε') * u) (by nlinarith)
      have hquad : θ + ε' ^ 2 / 16 ≤ (1 + ε') * u - ((1 + ε') * u) ^ 2 / 2 := by
        dsimp [θ]
        have hz_le : (1 + ε') * u ≤ 3 * ε' / 8 := by nlinarith
        have hsq : ((1 + ε') * u) ^ 2 / 2 ≤ (3 * ε' / 16) * ((1 + ε') * u) := by
          have := mul_le_mul_of_nonneg_right hz_le (show 0 ≤ (1 + ε') * u by nlinarith)
          linarith
        nlinarith [hu_lo, sq_nonneg ε']
      linarith

/-- For a fixed `r`-sample threshold circuit built from `k`-OR gates, the single-block error
probability is at most `exp (-(r * γ^2 / 4))`. -/
private theorem block_error_prob_le {m k r : ℕ} (hm : 0 < m) [Nonempty (Fin m)]
    {θ γ : ℝ} (hθ0 : 0 ≤ θ) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (x : BitString m) :
    let T : ℕ := Nat.floor (r * θ) + 1
    let p : ℝ := 1 - (1 - (BitString.weight x : ℝ) / m) ^ k
    let blockEval (b : Fin r → Fin k → Fin m) : Bool :=
      ltThreshold r T (fun l => decide (∃ t : Fin k, x (b l t) = true))
    (p ≤ θ - γ →
      ((uniformOfFintype (Fin r → Fin k → Fin m)).toOuterMeasure
        {b | blockEval b = false}).toReal ≤ Real.exp (-(r * γ ^ 2 / 4))) ∧
    (θ + γ ≤ p →
      ((uniformOfFintype (Fin r → Fin k → Fin m)).toOuterMeasure
        {b | blockEval b = true}).toReal ≤ Real.exp (-(r * γ ^ 2 / 4))) := by
  intro T p blockEval
  let q : _root_.PMF (Fin k → Fin m) := uniformOfFintype (Fin k → Fin m)
  have hpi : uniformOfFintype (Fin r → Fin k → Fin m) =
      pi (fun _ : Fin r => q) :=
    uniformOfFintype_pi_eq (ι := Fin r) (α := Fin k → Fin m)
  rw [hpi]
  let ind (s : Fin k → Fin m) : ℝ := if (∃ t : Fin k, x (s t) = true) then 1 else 0
  have hind_mean : ∑ s : Fin k → Fin m, (q s).toReal * ind s = p := by
    have h1 := prob_orSample_eq (k := k) hm x
    rw [toOuterMeasure_toReal_eq_sum_ite] at h1
    simpa [q, ind, p] using h1
  have hsum_weight (b : Fin r → Fin k → Fin m) :
      (∑ l : Fin r, ind (b l)) =
        (BitString.weight (fun l : Fin r => decide (∃ t : Fin k, x (b l t) = true)) : ℝ) := by
    simp only [ind, BitString.weight, decide_eq_true_eq, Finset.sum_boole]
  constructor
  · intro hp
    have hsub : {b : Fin r → Fin k → Fin m | blockEval b = false} ⊆
        {b | (r : ℝ) * (θ - γ) + (r : ℝ) * γ ≤ ∑ l : Fin r, ind (b l)} := by
      intro b hb
      simp only [Set.mem_ofPred_eq, blockEval, ltThreshold, decide_eq_false_iff_not, not_lt] at hb
      simp only [Set.mem_ofPred_eq, hsum_weight]
      have hT : (r : ℝ) * θ < (T : ℝ) := by
        dsimp [T]; push_cast; exact Nat.lt_floor_add_one _
      have hb' : (T : ℝ) ≤
          (BitString.weight (fun l : Fin r => decide (∃ t : Fin k, x (b l t) = true)) : ℝ) := by
        exact_mod_cast hb
      linarith
    refine (ENNReal.toReal_mono (toOuterMeasure_ne_top _ _)
      (MeasureTheory.measure_mono hsub)).trans ?_
    refine pi_sum_ge_add_le_exp (fun _ : Fin r => q) (fun _ => ind)
      (fun _ s _ => by dsimp [ind]; split_ifs <;> norm_num) ?_ hγ0 hγ1
    simp only [hind_mean, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg r)
  · intro hp
    let ind' (s : Fin k → Fin m) : ℝ := 1 - ind s
    have hind'_mean : ∑ s : Fin k → Fin m, (q s).toReal * ind' s = 1 - p := by
      have hq1 : ∑ s : Fin k → Fin m, (q s).toReal = 1 := by
        have hsum : ∑ s : Fin k → Fin m, q s = 1 := by simpa [tsum_fintype] using q.tsum_coe
        rw [← ENNReal.toReal_sum (fun _ _ => PMF.apply_ne_top _ _), hsum, ENNReal.toReal_one]
      calc ∑ s, (q s).toReal * (1 - ind s)
          = ∑ s, (q s).toReal - ∑ s, (q s).toReal * ind s := by
              rw [← Finset.sum_sub_distrib]; congr 1; ext s; ring
        _ = 1 - p := by rw [hq1, hind_mean]
    have hsub : {b : Fin r → Fin k → Fin m | blockEval b = true} ⊆
        {b | (r : ℝ) * (1 - θ - γ) + (r : ℝ) * γ ≤ ∑ l : Fin r, ind' (b l)} := by
      intro b hb
      simp only [Set.mem_ofPred_eq, blockEval, ltThreshold, decide_eq_true_eq] at hb
      simp only [Set.mem_ofPred_eq, ind', Finset.sum_sub_distrib, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, hsum_weight]
      have hle : BitString.weight (fun l : Fin r => decide (∃ t : Fin k, x (b l t) = true)) ≤
          Nat.floor (r * θ) := by dsimp [T] at hb; omega
      have hle' : (BitString.weight (fun l : Fin r =>
          decide (∃ t : Fin k, x (b l t) = true)) : ℝ) ≤ (r : ℝ) * θ :=
        (Nat.cast_le.mpr hle).trans (Nat.floor_le (mul_nonneg (Nat.cast_nonneg r) hθ0))
      linarith
    refine (ENNReal.toReal_mono (toOuterMeasure_ne_top _ _)
      (MeasureTheory.measure_mono hsub)).trans ?_
    refine pi_sum_ge_add_le_exp (fun _ : Fin r => q) (fun _ => ind')
      (fun _ s _ => by dsimp [ind', ind]; split_ifs <;> norm_num) ?_ hγ0 hγ1
    simp only [hind'_mean, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg r)

/-- Exact product formula for `∀ i, P (f i)` under `PMF.uniformOfFintype (Fin m → α)`. -/
private theorem uniformOfFintype_forall_prob {m : ℕ} {α : Type*} [Fintype α] [Nonempty α]
    (E : Set α) :
    ((uniformOfFintype (Fin m → α)).toOuterMeasure {f | ∀ i : Fin m, f i ∈ E}).toReal =
      (((uniformOfFintype α).toOuterMeasure E).toReal) ^ m := by
  classical
  rw [uniformOfFintype_toOuterMeasure_toReal, uniformOfFintype_toOuterMeasure_toReal,
    Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, div_pow]
  congr 1
  have hfilt : (Finset.univ.filter fun f : Fin m → α =>
      f ∈ {f : Fin m → α | ∀ i : Fin m, f i ∈ E}) =
      Finset.univ.filter fun f : Fin m → α => ∀ i : Fin m, f i ∈ E := by
    ext f; rfl
  rw [hfilt]
  have hcard : (Finset.univ.filter fun f : Fin m → α => ∀ i, f i ∈ E).card =
      (Finset.univ.filter fun a : α => a ∈ E).card ^ m := by
    let S : Finset α := Finset.univ.filter fun a => a ∈ E
    have hbij : (Finset.univ.filter fun f : Fin m → α => ∀ i, f i ∈ E).card =
        Fintype.card (Fin m → {a : α // a ∈ S}) := by
      rw [← Finset.card_univ]
      refine Finset.card_bij
        (fun f hf i => ⟨f i, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          (Finset.mem_filter.mp hf).2 i⟩⟩)
        (fun _ _ => Finset.mem_univ _)
        (fun f₁ _ f₂ _ h => funext fun i => congrArg Subtype.val (congrFun h i))
        (fun g _ => ⟨fun i => (g i).1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun i =>
          (Finset.mem_filter.mp (g i).2).2⟩, rfl⟩)
    rw [hbij, Fintype.card_fun, Fintype.card_coe, Fintype.card_fin]
  rw [hcard, Nat.cast_pow]

/-- Union bound for `∃ i, f i ∈ E` under `uniformOfFintype (Fin m → α)`. -/
private theorem uniformOfFintype_exists_prob_le {m : ℕ} {α : Type*} [Fintype α] [Nonempty α]
    (E : Set α) :
    ((uniformOfFintype (Fin m → α)).toOuterMeasure {f | ∃ i : Fin m, f i ∈ E}).toReal ≤
      m * ((uniformOfFintype α).toOuterMeasure E).toReal := by
  classical
  have hsub : {f : Fin m → α | ∃ i : Fin m, f i ∈ E} =
      ⋃ i : Fin m, {f : Fin m → α | f i ∈ E} := by ext f; simp
  rw [hsub]
  have hle : (uniformOfFintype (Fin m → α)).toOuterMeasure
      (⋃ i : Fin m, {f : Fin m → α | f i ∈ E}) ≤
      ∑ i : Fin m, (uniformOfFintype (Fin m → α)).toOuterMeasure {f | f i ∈ E} :=
    MeasureTheory.measure_iUnion_fintype_le _ _
  refine (ENNReal.toReal_mono
    (ENNReal.sum_ne_top.mpr fun _ _ => toOuterMeasure_ne_top _ _) hle).trans ?_
  rw [ENNReal.toReal_sum (fun _ _ => toOuterMeasure_ne_top _ _)]
  have heach (i : Fin m) :
      ((uniformOfFintype (Fin m → α)).toOuterMeasure {f | f i ∈ E}).toReal =
        ((uniformOfFintype α).toOuterMeasure E).toReal := by
    have hmap : (uniformOfFintype (Fin m → α)).map (fun f => f i) =
        uniformOfFintype α := by
      rw [uniformOfFintype_pi_eq (ι := Fin m) (α := α), pi_map_eval]
    have hev : (uniformOfFintype (Fin m → α)).toOuterMeasure {f | f i ∈ E} =
        ((uniformOfFintype (Fin m → α)).map (fun f => f i)).toOuterMeasure E := by
      rw [PMF.toOuterMeasure_map_apply]
      rfl
    rw [hev, hmap]
  simp only [heach, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  exact le_rfl

/-- **Non-uniform AC⁰ relative-threshold approximate counting:**
for every fixed `ε > 0`, there exists a polynomially bounded size function `s` such that for
every input length `m` and every real threshold `a > 0`, there is an unbounded fan-in circuit
`C` of depth at most `7` and size at most `s m` that outputs `true` whenever
`weight x ≤ (1 - ε) * a` and `false` whenever `weight x ≥ (1 + ε) * a`. -/
theorem exists_approxCount_circuit {ε : ℝ} (hε : 0 < ε) :
    ∃ s : ℕ → ℕ, PolynomiallyBounded s ∧
      ∀ (m : ℕ) (a : ℝ), 0 < a →
        ∃ C : Circuit Unbounded.signature m 1,
          C.depth ≤ 7 ∧ C.size ≤ s m ∧
          (∀ x : BitString m, (BitString.weight x : ℝ) ≤ (1 - ε) * a →
            C.eval Unbounded.interpretation x 0 = true) ∧
          (∀ x : BitString m, (1 + ε) * a ≤ (BitString.weight x : ℝ) →
            C.eval Unbounded.interpretation x 0 = false) := by
  let ε' : ℝ := min ε (1 / 2)
  have hε'0 : 0 < ε' := lt_min hε (by norm_num)
  have hε'1 : ε' ≤ 1 / 2 := min_le_right _ _
  have hε'_le : ε' ≤ ε := min_le_left _ _
  let γ : ℝ := ε' ^ 2 / 16
  have hγ0 : 0 < γ := by positivity
  have hγ1 : γ ≤ 1 := by dsimp [γ]; nlinarith
  obtain ⟨Csym, hCsym0, hsym⟩ := Unbounded.exists_circuit_of_isSymmetric (d := 3) (by omega)
  let K : ℕ := Nat.ceil (4 / γ ^ 2) + 1
  have hK1 : 1 ≤ K := by omega
  let A : ℕ := Nat.ceil ((2 : ℝ) ^ (Csym ^ 2 * (K : ℝ) / 4)) + 1
  let s : ℕ → ℕ := fun m =>
    1 + m * (1 + m * (A * (8 * (m + 2)) + 2 * (K * (Nat.clog 2 (m + 2) + 2)))) + 2
  refine ⟨s, ?_, fun m a ha => ?_⟩
  · have hclog : PolynomiallyBounded fun m => Nat.clog 2 (m + 2) := by
      refine ⟨1, Filter.eventually_atTop.mpr ⟨2, fun m hm => ?_⟩⟩
      simp only [pow_one]
      have h2 : m + 2 ≤ 2 ^ m := by
        induction m, hm using Nat.le_induction with
        | base => norm_num
        | succ k hk ih => rw [pow_succ]; omega
      exact Nat.clog_le_of_le_pow h2
    dsimp only [s]
    fun_prop
  · -- Reduce trivial regimes first: `m = 0`, `(1 + ε') * a > m`, or `(1 - ε') * a < 1`.
    by_cases hm0 : m = 0
    · subst hm0
      refine ⟨constCircuit (.id _) true,
        (depth_constCircuit_le (φ := .id _) true).trans (by omega),
        by simp [s], fun x _ => by simp, fun x hx => ?_⟩
      exfalso
      have hw0 : BitString.weight x = 0 := by simp [BitString.weight]
      rw [hw0, Nat.cast_zero] at hx
      nlinarith
    have hm_pos : 0 < m := Nat.pos_of_ne_zero hm0
    have : Nonempty (Fin m) := ⟨⟨0, hm_pos⟩⟩
    by_cases hbig : (m : ℝ) < (1 + ε') * a
    · refine ⟨constCircuit (.id _) true,
        (depth_constCircuit_le (φ := .id _) true).trans (by omega),
        by simp [s], fun x _ => by simp, fun x hx => ?_⟩
      exfalso
      have hwm : (BitString.weight x : ℝ) ≤ m := by exact_mod_cast BitString.weight_le_length x
      nlinarith
    push Not at hbig
    by_cases hsmall : a < 1
    · -- `(1 - ε') * a < 1`, so `weight x ≤ (1 - ε') * a` forces `weight x = 0`,
      -- while `weight x ≥ (1 + ε') * a > 0` forces `weight x ≥ 1`.
      -- A negated `m`-ary OR gate decides `weight x = 0` in depth 2, size 2.
      let C : Circuit Unbounded.signature m 1 :=
        notCircuit (.id _) (Circuit.oneGate (σ := Unbounded.signature) (.or m) id)
      refine ⟨C, ?_, ?_, fun x hx => ?_, fun x hx => ?_⟩
      · calc C.depth ≤ (Circuit.oneGate (σ := Unbounded.signature) (.or m) id).depth + 1 :=
              depth_notCircuit_le _
          _ = 2 := by simp
          _ ≤ 7 := by omega
      · simp [C, s]
      · simp only [C, eval_notCircuit, Circuit.eval_oneGate, interpretation_or, id_eq]
        have hw0 : BitString.weight x = 0 := by
          by_contra hne
          have h1 : (1 : ℝ) ≤ BitString.weight x := by exact_mod_cast Nat.pos_of_ne_zero hne
          nlinarith
        have hall : ∀ i : Fin m, x i = false := by
          intro i
          by_contra h
          have hi : x i = true := by cases hx' : x i <;> simp_all
          have hpos : 0 < BitString.weight x := by
            rw [BitString.weight]
            exact Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
          omega
        simp [hall]
      · simp only [C, eval_notCircuit, Circuit.eval_oneGate, interpretation_or, id_eq]
        have hw_pos : 0 < BitString.weight x := by
          by_contra h0
          have hw0 : BitString.weight x = 0 := by omega
          rw [hw0, Nat.cast_zero] at hx
          nlinarith
        obtain ⟨i, hi⟩ := Finset.card_pos.mp hw_pos
        have hex : ∃ j : Fin m, x j = true := ⟨i, (Finset.mem_filter.mp hi).2⟩
        simp [hex]
    push Not at hsmall
    -- Main regime: `m ≥ 1`, `a ≥ 1`, `(1 + ε') * a ≤ m`.
    obtain ⟨k, θ, hk1, hkm, hθ0, hθ1, hlo_p, hhi_p⟩ :=
      exists_orSample_params hε'0 hε'1 hsmall hbig
    let r : ℕ := K * (Nat.clog 2 (m + 2) + 2)
    have hr1 : 1 ≤ r := Nat.mul_pos (by omega) (by omega)
    let T : ℕ := Nat.floor (r * θ) + 1
    -- Single-block error probability bound `≤ 1 / (4 * (m + 2))`.
    have herr_block_val : Real.exp (-(r * γ ^ 2 / 4)) ≤ 1 / (4 * ((m : ℝ) + 2)) := by
      have hK_ge : 4 / γ ^ 2 ≤ (K : ℝ) := by
        dsimp [K]; push_cast; linarith [Nat.le_ceil (4 / γ ^ 2)]
      have hrg : ((Nat.clog 2 (m + 2) + 2 : ℕ) : ℝ) ≤ r * γ ^ 2 / 4 := by
        dsimp [r]
        push_cast
        have h1 : 4 ≤ (K : ℝ) * γ ^ 2 := by
          have := mul_le_mul_of_nonneg_right hK_ge (sq_nonneg γ)
          rwa [div_mul_cancel₀ _ (by positivity)] at this
        have h2 : 1 ≤ (K : ℝ) * γ ^ 2 / 4 := by linarith
        nlinarith [show (0 : ℝ) ≤ (Nat.clog 2 (m + 2) : ℝ) + 2 by positivity]
      calc Real.exp (-(r * γ ^ 2 / 4))
          ≤ (1 / 2 : ℝ) ^ (Nat.clog 2 (m + 2) + 2) := Real.exp_le_half_pow _ (by linarith)
        _ = 1 / (4 * (2 : ℝ) ^ Nat.clog 2 (m + 2)) := by
            rw [pow_add, one_div_pow, one_div_pow]
            norm_num
        _ ≤ 1 / (4 * ((m : ℝ) + 2)) := by
            gcongr
            exact_mod_cast Nat.le_pow_clog (by norm_num) (m + 2)
    -- Probabilistic existence of an `m × m` grid of `r`-block samplers succeeding on ALL `x`.
    let Block := Fin r → Fin k → Fin m
    let Row := Fin m → Block
    let Grid := Fin m → Row
    let blockEval (b : Block) (x : BitString m) : Bool :=
      ltThreshold r T (fun l => decide (∃ t : Fin k, x (b l t) = true))
    let rowEval (row : Row) (x : BitString m) : Bool :=
      decide (∀ j : Fin m, blockEval (row j) x = true)
    let gridEval (g : Grid) (x : BitString m) : Bool :=
      decide (∃ i : Fin m, rowEval (g i) x = true)
    let badFor (x : BitString m) : Set Grid :=
      if (BitString.weight x : ℝ) ≤ (1 - ε') * a then {g | gridEval g x = false}
      else if (1 + ε') * a ≤ (BitString.weight x : ℝ) then {g | gridEval g x = true}
      else ∅
    have hbad_le (x : BitString m) :
        ((uniformOfFintype Grid).toOuterMeasure (badFor x)).toReal ≤
          (1 / 4 : ℝ) ^ m := by
      have hblk := block_error_prob_le (k := k) (r := r) hm_pos hθ0 hγ0.le hγ1 x
      dsimp only [badFor]
      split_ifs with h1 h2
      · -- YES input: each row fails with prob `≤ m / (4(m+2)) ≤ 1/4`; all rows fail `≤ (1/4)^m`.
        have hb : ((uniformOfFintype Block).toOuterMeasure
            {b | blockEval b x = false}).toReal ≤ 1 / (4 * ((m : ℝ) + 2)) :=
          (hblk.1 (hlo_p x h1)).trans herr_block_val
        have hrow_eq : {row : Row | rowEval row x = false} =
            {row : Row | ∃ j : Fin m, blockEval (row j) x = false} := by
          ext row; simp [rowEval]
        have hrow_le : ((uniformOfFintype Row).toOuterMeasure
            {row | rowEval row x = false}).toReal ≤ 1 / 4 := by
          rw [hrow_eq]
          refine (uniformOfFintype_exists_prob_le {b | blockEval b x = false}).trans ?_
          calc (m : ℝ) * ((uniformOfFintype Block).toOuterMeasure
                {b | blockEval b x = false}).toReal
              ≤ (m : ℝ) * (1 / (4 * ((m : ℝ) + 2))) :=
                mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg m)
            _ ≤ 1 / 4 := by
                rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
                linarith
        have hgrid_eq : {g : Grid | gridEval g x = false} =
            {g : Fin m → Row | ∀ i : Fin m, g i ∈ {row : Row | rowEval row x = false}} :=
          Set.ext fun g => by
            change gridEval g x = false ↔ ∀ i : Fin m, rowEval (g i) x = false
            simp [gridEval]
        rw [hgrid_eq]
        change ((uniformOfFintype (Fin m → Row)).toOuterMeasure
            {g : Fin m → Row | ∀ i : Fin m, g i ∈ {row : Row | rowEval row x = false}}).toReal ≤ _
        rw [uniformOfFintype_forall_prob (α := Row) {row : Row | rowEval row x = false}]
        exact pow_le_pow_left₀ ENNReal.toReal_nonneg hrow_le m
      · -- NO input: each row accepts with prob `≤ (1/(4(m+2)))^m`; union over `m` rows `≤ (1/4)^m`.
        have hb : ((uniformOfFintype Block).toOuterMeasure
            {b | blockEval b x = true}).toReal ≤ 1 / (4 * ((m : ℝ) + 2)) :=
          (hblk.2 (hhi_p x h2)).trans herr_block_val
        have hrow_eq : {row : Row | rowEval row x = true} =
            {row : Fin m → Block | ∀ j : Fin m, row j ∈ {b : Block | blockEval b x = true}} :=
          Set.ext fun row => by
            change rowEval row x = true ↔ ∀ j : Fin m, blockEval (row j) x = true
            simp [rowEval]
        have hrow_le : ((uniformOfFintype Row).toOuterMeasure
            {row | rowEval row x = true}).toReal ≤ (1 / (4 * ((m : ℝ) + 2))) ^ m := by
          rw [hrow_eq]
          change ((uniformOfFintype (Fin m → Block)).toOuterMeasure
              {row : Fin m → Block | ∀ j : Fin m,
                row j ∈ {b : Block | blockEval b x = true}}).toReal ≤ _
          rw [uniformOfFintype_forall_prob (α := Block) {b : Block | blockEval b x = true}]
          exact pow_le_pow_left₀ ENNReal.toReal_nonneg hb m
        have hgrid_eq : {g : Grid | gridEval g x = true} =
            {g : Grid | ∃ i : Fin m, rowEval (g i) x = true} := by
          ext g; simp [gridEval]
        rw [hgrid_eq]
        refine (uniformOfFintype_exists_prob_le {row | rowEval row x = true}).trans ?_
        calc (m : ℝ) * ((uniformOfFintype Row).toOuterMeasure
              {row | rowEval row x = true}).toReal
            ≤ (m : ℝ) * (1 / (4 * ((m : ℝ) + 2))) ^ m :=
              mul_le_mul_of_nonneg_left hrow_le (Nat.cast_nonneg m)
          _ = (m : ℝ) * (1 / ((m : ℝ) + 2)) ^ m * (1 / 4 : ℝ) ^ m := by
              rw [show (1 / (4 * ((m : ℝ) + 2))) = (1 / ((m : ℝ) + 2)) * (1 / 4) by field_simp,
                mul_pow]; ring
          _ ≤ 1 * (1 / 4 : ℝ) ^ m := by
              refine mul_le_mul_of_nonneg_right ?_ (by positivity)
              have hpow : (1 / ((m : ℝ) + 2)) ^ m ≤ 1 / ((m : ℝ) + 2) := by
                have hle1 : (1 / ((m : ℝ) + 2)) ≤ 1 := by
                  rw [div_le_one (by positivity)]; linarith
                have h0 : 0 ≤ (1 / ((m : ℝ) + 2)) := by positivity
                calc (1 / ((m : ℝ) + 2)) ^ m
                    ≤ (1 / ((m : ℝ) + 2)) ^ 1 := pow_le_pow_of_le_one h0 hle1 hm_pos
                  _ = 1 / ((m : ℝ) + 2) := pow_one _
              calc (m : ℝ) * (1 / ((m : ℝ) + 2)) ^ m
                  ≤ (m : ℝ) * (1 / ((m : ℝ) + 2)) :=
                    mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg m)
                _ ≤ 1 := by rw [mul_one_div, div_le_one (by positivity)]; linarith
          _ = (1 / 4 : ℝ) ^ m := one_mul _
      · simp
    -- Union bound over all `2^m` inputs `x : BitString m`.
    have hunion_lt : ((uniformOfFintype Grid).toOuterMeasure
        (⋃ x : BitString m, badFor x)).toReal < 1 := by
      have hle : (uniformOfFintype Grid).toOuterMeasure (⋃ x : BitString m, badFor x) ≤
          ∑ x : BitString m, (uniformOfFintype Grid).toOuterMeasure (badFor x) :=
        MeasureTheory.measure_iUnion_fintype_le _ _
      have h1 := (ENNReal.toReal_mono
        (ENNReal.sum_ne_top.mpr fun _ _ => toOuterMeasure_ne_top _ _) hle).trans_eq
        (ENNReal.toReal_sum (fun _ _ => toOuterMeasure_ne_top _ _))
      have h2 : ∑ x : BitString m,
          ((uniformOfFintype Grid).toOuterMeasure (badFor x)).toReal ≤
          (1 / 2 : ℝ) ^ m := by
        calc ∑ x : BitString m,
              ((uniformOfFintype Grid).toOuterMeasure (badFor x)).toReal
            ≤ ∑ _x : BitString m, (1 / 4 : ℝ) ^ m := Finset.sum_le_sum fun x _ => hbad_le x
          _ = (2 : ℝ) ^ m * (1 / 4 : ℝ) ^ m := by
              simp [nsmul_eq_mul]
          _ = (1 / 2 : ℝ) ^ m := by rw [← mul_pow]; norm_num
      have h3 : (1 / 2 : ℝ) ^ m < 1 :=
        pow_lt_one₀ (by norm_num) (by norm_num) hm_pos.ne'
      linarith
    have hex_good : ∃ g : Grid, g ∉ ⋃ x : BitString m, badFor x := by
      by_contra hall
      push Not at hall
      have huniv : (⋃ x : BitString m, badFor x) = Set.univ := Set.eq_univ_iff_forall.mpr hall
      rw [huniv] at hunion_lt
      have h1 : (uniformOfFintype Grid).toOuterMeasure Set.univ = 1 := by
        rw [_root_.PMF.toOuterMeasure_apply_fintype]
        simpa [tsum_fintype] using (uniformOfFintype Grid).tsum_coe
      rw [h1, ENNReal.toReal_one] at hunion_lt
      exact lt_irrefl _ hunion_lt
    obtain ⟨g, hg⟩ := hex_good
    -- Instantiate the depth-4 symmetric threshold circuit on `r` bits from `ShallowSymmetric`.
    obtain ⟨S, hScomp, -, hSdepth, hSsize⟩ := hsym r hr1 (ltThreshold r T)
      (isSymmetric_ltThreshold r T)
    -- Bound `S.size ≤ A * (8 * (m + 2)) + r` using AM-GM `Csym * √r ≤ Csym^2 * K / 4 + L + 2`.
    have hSsize_nat : S.size ≤ A * (8 * (m + 2)) + r := by
      have hpow_r : (r : ℝ) ^ ((3 - 1 : ℕ) : ℝ)⁻¹ = Real.sqrt (r : ℝ) := by
        rw [Real.sqrt_eq_rpow]; norm_num
      rw [hpow_r] at hSsize
      set L := Nat.clog 2 (m + 2) + 2
      have hsqrt_le : Csym * Real.sqrt (r : ℝ) ≤ Csym ^ 2 * (K : ℝ) / 4 + (L : ℝ) := by
        have hsq : 0 ≤ (Csym * Real.sqrt (K : ℝ) / 2 - Real.sqrt (L : ℝ)) ^ 2 := sq_nonneg _
        have hr_eq : Real.sqrt (r : ℝ) = Real.sqrt (K : ℝ) * Real.sqrt (L : ℝ) := by
          dsimp [r, L]; push_cast; exact Real.sqrt_mul (Nat.cast_nonneg K) _
        have hK0 : (Real.sqrt (K : ℝ)) ^ 2 = (K : ℝ) := Real.sq_sqrt (Nat.cast_nonneg K)
        have hL0 : (Real.sqrt (L : ℝ)) ^ 2 = (L : ℝ) := Real.sq_sqrt (Nat.cast_nonneg L)
        rw [hr_eq]
        nlinarith
      have h2pow : (2 : ℝ) ^ (Csym * Real.sqrt (r : ℝ)) ≤ (A : ℝ) * (8 * ((m : ℝ) + 2)) := by
        calc (2 : ℝ) ^ (Csym * Real.sqrt (r : ℝ))
            ≤ (2 : ℝ) ^ (Csym ^ 2 * (K : ℝ) / 4 + (L : ℝ)) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) hsqrt_le
          _ = (2 : ℝ) ^ (Csym ^ 2 * (K : ℝ) / 4) * (2 : ℝ) ^ (L : ℝ) :=
              Real.rpow_add (by norm_num) _ _
          _ ≤ (A : ℝ) * ((2 : ℝ) ^ L) := by
              rw [Real.rpow_natCast]
              refine mul_le_mul_of_nonneg_right ?_ (by positivity)
              dsimp [A]; push_cast; linarith [Nat.le_ceil ((2 : ℝ) ^ (Csym ^ 2 * (K : ℝ) / 4))]
          _ ≤ (A : ℝ) * (8 * ((m : ℝ) + 2)) := by
              refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg A)
              have hcl : 2 ^ Nat.clog 2 (m + 2) ≤ 2 * (m + 2) :=
                Nat.pow_clog_le_mul (by norm_num) (by omega)
              have hL_le : 2 ^ L ≤ 8 * (m + 2) := by
                dsimp [L]; rw [pow_add]; omega
              exact_mod_cast hL_le
      have htot : (S.size : ℝ) ≤ ((A * (8 * (m + 2)) + r : ℕ) : ℝ) := by
        push_cast; linarith
      exact_mod_cast htot
    -- Assemble the depth-7 unbounded fan-in circuit from `g` and `S`.
    let blockCirc (i j : Fin m) : Circuit Unbounded.signature m 1 :=
      S.comp (Circuit.pi fun l : Fin r =>
        Circuit.oneGate (σ := Unbounded.signature) (.or k) fun t => g i j l t)
    let rowCirc (i : Fin m) : Circuit Unbounded.signature m 1 :=
      (Circuit.oneGate (σ := Unbounded.signature) (.and m) id).comp
        (Circuit.pi fun j : Fin m => blockCirc i j)
    let C : Circuit Unbounded.signature m 1 :=
      (Circuit.oneGate (σ := Unbounded.signature) (.or m) id).comp
        (Circuit.pi fun i : Fin m => rowCirc i)
    have hCeval (x : BitString m) : C.eval Unbounded.interpretation x 0 = gridEval g x := by
      have hblk_eval (i j : Fin m) :
          (blockCirc i j).eval Unbounded.interpretation x 0 = blockEval (g i j) x := by
        simp only [blockCirc, Circuit.eval_comp, Circuit.eval_pi, Circuit.eval_oneGate,
          interpretation_or]
        have hcomp := congrFun
          (hScomp fun l : Fin r => decide (∃ t : Fin k, x (g i j l t) = true)) 0
        simpa [single_apply, blockEval] using hcomp
      have hrow_eval (i : Fin m) :
          (rowCirc i).eval Unbounded.interpretation x 0 = rowEval (g i) x := by
        simp only [rowCirc, Circuit.eval_comp, Circuit.eval_pi, Circuit.eval_oneGate,
          interpretation_and, id_eq, hblk_eval, rowEval]
      simp only [C, Circuit.eval_comp, Circuit.eval_pi, Circuit.eval_oneGate,
        interpretation_or, id_eq, hrow_eval, gridEval]
    refine ⟨C, ?_, ?_, fun x hx => ?_, fun x hx => ?_⟩
    · have hblk_d (i j : Fin m) : (blockCirc i j).depth ≤ 5 := by
        refine (Circuit.depth_comp_le _ _).trans ?_
        have hpi_d : (Circuit.pi fun l : Fin r =>
            Circuit.oneGate (σ := Unbounded.signature) (.or k) fun t => g i j l t).depth ≤ 1 :=
          Circuit.depth_pi_le _ fun _ => by simp
        omega
      have hrow_d (i : Fin m) : (rowCirc i).depth ≤ 6 := by
        refine (Circuit.depth_comp_le _ _).trans ?_
        have hpi_d := Circuit.depth_pi_le (fun j => blockCirc i j) (hblk_d i)
        simp only [Circuit.depth_oneGate]
        omega
      refine (Circuit.depth_comp_le _ _).trans ?_
      have hpi_d := Circuit.depth_pi_le (fun i => rowCirc i) hrow_d
      simp only [Circuit.depth_oneGate]
      omega
    · have hblk_s (i j : Fin m) : (blockCirc i j).size ≤ A * (8 * (m + 2)) + 2 * r := by
        simp only [blockCirc, Circuit.size_comp, Circuit.size_pi, Circuit.size_oneGate,
          Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
        omega
      have hrow_s (i : Fin m) : (rowCirc i).size ≤ 1 + m * (A * (8 * (m + 2)) + 2 * r) := by
        simp only [rowCirc, Circuit.size_comp, Circuit.size_pi, Circuit.size_oneGate]
        calc (∑ j : Fin m, (blockCirc i j).size) + 1
            ≤ (∑ _j : Fin m, (A * (8 * (m + 2)) + 2 * r)) + 1 :=
              Nat.add_le_add_right (Finset.sum_le_sum fun j _ => hblk_s i j) 1
          _ = 1 + m * (A * (8 * (m + 2)) + 2 * r) := by simp [Nat.add_comm]
      simp only [C, Circuit.size_comp, Circuit.size_pi, Circuit.size_oneGate]
      calc (∑ i : Fin m, (rowCirc i).size) + 1
          ≤ (∑ _i : Fin m, (1 + m * (A * (8 * (m + 2)) + 2 * r))) + 1 :=
            Nat.add_le_add_right (Finset.sum_le_sum fun i _ => hrow_s i) 1
        _ ≤ s m := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, s, r]
            omega
    · rw [hCeval]
      have hx' : (BitString.weight x : ℝ) ≤ (1 - ε') * a := by nlinarith
      have hnot : g ∉ badFor x := fun hmem => hg (Set.mem_iUnion.mpr ⟨x, hmem⟩)
      simp only [badFor, hx', ↓reduceIte, Set.mem_ofPred_eq, Bool.not_eq_false] at hnot
      exact hnot
    · rw [hCeval]
      have hx' : (1 + ε') * a ≤ (BitString.weight x : ℝ) := by nlinarith
      have hnot_lo : ¬ (BitString.weight x : ℝ) ≤ (1 - ε') * a := by nlinarith
      have hnot : g ∉ badFor x := fun hmem => hg (Set.mem_iUnion.mpr ⟨x, hmem⟩)
      simp only [badFor, hnot_lo, hx', ↓reduceIte, Set.mem_ofPred_eq, Bool.not_eq_true] at hnot
      exact hnot


end CslibFrontier.Computability.Circuit.Boolean.ApproximateCount
