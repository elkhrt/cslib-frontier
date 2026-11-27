/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FormalPapers Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.QueryComplexity.Quantum.NayakWuConsequences
public import CslibFrontier.Computability.QueryComplexity.Quantum.UnknownSearch
public import CslibFrontier.Foundations.Data.BitString.Basic

import CslibFrontier.Probability.PMF
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Quantum Binary-Prefix Minimum Search and QRAM Query Complexity

Generalizes Grover's known-count search bound (`Cslib.Quantum.grover_success`) to arbitrary nonzero
marked multiplicity `1 ≤ t ≤ N` (`grover_of_weight_success`), formalizes unsigned MSB-prefix dyadic
interval bisection (`msbPrefix`, `quantumMinWordPMF_minWord_ge`) using amplified one-sided BBHT
quantum `OR` stages (`quantumOrAmpPMF`), and establishes the matching `Ω(√N)` quantum QRAM query
lower bound (`qram_minimum_query_lower_bound`) from
`Cslib.Quantum.kthSmallest_involution_lower_bound`.

## Main definitions

* `CslibFrontier.Quantum.groverOptIter`: optimal Grover iteration count
  `⌊π / (4 * searchAngle N t)⌋₊`.
* `CslibFrontier.Quantum.msbPrefix`, `CslibFrontier.Quantum.minWord`: `k`-bit MSB prefix and
  unsigned minimum word of a nonempty finite table.
* `CslibFrontier.Quantum.quantumOrOncePMF`, `CslibFrontier.Quantum.quantumOrAmpPMF`: single-stage
  and `R`-fold amplified one-sided quantum `OR` distributions.
* `CslibFrontier.Quantum.quantumPrefixRefinePMF`, `CslibFrontier.Quantum.quantumMinWordPMF`:
  adaptive binary-prefix quantum minimum-finding distributions.
* `CslibFrontier.Quantum.IsMinUnsignedValue`: decidable predicate characterizing the unsigned
  minimum of a `BitString m` table.

## Main results

* `CslibFrontier.Quantum.run_grover_false`: zero-target stationarity of Grover's iteration.
* `CslibFrontier.Quantum.grover_of_weight_success`: `O(√(N / t))` query bound with `≥ 1 - t / N`
  and universal `≥ 1 / 2` success probability for every `1 ≤ t ≤ N`.
* `CslibFrontier.Quantum.val_equivFin_msbPrefix`, `CslibFrontier.Quantum.msbPrefix_eq_iff_interval`:
  quotient and dyadic-interval characterizations of `msbPrefix`.
* `CslibFrontier.Quantum.quantumMinWordPMF_minWord_ge`: `(1 - (9 / 16) ^ R) ^ b` success lower
  bound for `b`-stage quantum binary-prefix minimum search.
* `CslibFrontier.Quantum.qram_minimum_query_lower_bound`: `√|ι| + √(|ι| - 1) ≤ 288 * T` lower bound
  for bounded-error QRAM minimum finding.
-/

public section

namespace CslibFrontier.Quantum

open Finset Real Cslib Cslib.BitString Cslib.Quantum

/-- Optimal deterministic Grover iteration count `⌊π / (4 * searchAngle N t)⌋₊` for `t` marked
items among `N`. -/
noncomputable def groverOptIter (N t : ℕ) : ℕ :=
  ⌊Real.pi / (4 * searchAngle N t)⌋₊

/-- On the all-false input `fun _ ↦ false`, Grover's algorithm leaves `uniform N` invariant. -/
theorem run_grover_false {N : ℕ} (hN : 0 < N) (k : ℕ) :
    run (grover N) (uniform N) (fun _ ↦ false) k = uniform N := by
  have hw : weight (fun _ : Fin N ↦ false) = 0 := by simp [weight]
  ext p
  rw [run_grover_of_weight hN (fun _ ↦ false) k p, hw, searchAngle_zero, mul_zero, Real.cos_zero]
  simp [uniform, one_div]

/-- For `1 ≤ t ≤ N`, `groverOptIter N t ≤ π * √(N / t) / 4`. -/
theorem groverOptIter_le {N t : ℕ} (ht : 1 ≤ t) (htN : t ≤ N) :
    (groverOptIter N t : ℝ) ≤ Real.pi * Real.sqrt ((N : ℝ) / t) / 4 := by
  have ht0 : (0 : ℝ) < t := Nat.cast_pos.mpr ht
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.mpr (lt_of_lt_of_le ht htN)
  set θ := searchAngle N t
  have hs : Real.sin θ = Real.sqrt ((t : ℝ) / N) := sin_searchAngle htN
  have hsin_pos : 0 < Real.sin θ := by rw [hs]; exact Real.sqrt_pos.mpr (div_pos ht0 hN0)
  have hθ_pos : 0 < θ := Real.arcsin_pos.mpr (by rw [← hs]; exact hsin_pos)
  have hsin_le : Real.sin θ ≤ θ := Real.sin_le hθ_pos.le
  calc
    (groverOptIter N t : ℝ) ≤ Real.pi / (4 * θ) := Nat.floor_le (by positivity)
    _ ≤ Real.pi / (4 * Real.sin θ) := by gcongr
    _ = Real.pi * Real.sqrt ((N : ℝ) / t) / 4 := by
      rw [hs, Real.sqrt_div ht0.le, Real.sqrt_div hN0.le]
      field_simp [Real.sqrt_ne_zero'.mpr ht0, Real.sqrt_ne_zero'.mpr hN0]

/-- When `N < 2 * t` and `t ≤ N`, `groverOptIter N t = 0`. -/
theorem groverOptIter_eq_zero_of_lt_two_mul {N t : ℕ} (h2t : N < 2 * t) (htN : t ≤ N) :
    groverOptIter N t = 0 := by
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
  have hhalf : (1 / 2 : ℝ) < (t : ℝ) / N := by
    rw [div_lt_div_iff₀ zero_lt_two hN0]
    exact_mod_cast (by omega : 1 * N < (t * 2 : ℕ))
  have hpi4 : Real.pi / 4 < searchAngle N t := by
    have hlt_sin : Real.sin (Real.pi / 4) < Real.sin (searchAngle N t) := by
      rw [Real.sin_pi_div_four, sin_searchAngle htN]
      have hsq : (Real.sqrt 2 / 2) ^ 2 < (Real.sqrt ((t : ℝ) / N)) ^ 2 := by
        rw [div_pow, Real.sq_sqrt zero_le_two, Real.sq_sqrt (by positivity)]
        linarith
      exact lt_of_pow_lt_pow_left₀ 2 (Real.sqrt_nonneg _) hsq
    by_contra hle
    push Not at hle
    have hmono := Real.sin_le_sin_of_le_of_le_pi_div_two
      (by linarith [searchAngle_nonneg N t, Real.pi_pos]) (by linarith [Real.pi_pos]) hle
    linarith
  rw [groverOptIter, Nat.floor_eq_zero, div_lt_one (by linarith [Real.pi_pos])]
  linarith

/-- **Multi-target Grover amplification**: for any `x : Fin N → Bool` with `weight x ≥ 1`,
`groverOptIter N (weight x) ≤ (π / 4) * √(N / weight x)` queries measure a marked index with
probability at least `1 - weight x / N` and at least `1 / 2`. -/
theorem grover_of_weight_success {N : ℕ} (hN : 0 < N) (x : Fin N → Bool)
    (hx : ∃ i, x i = true) :
    1 - (weight x : ℝ) / N ≤
        (∑ i with x i = true, regProb (run (grover N) (uniform N) x
          (groverOptIter N (weight x))) i) ∧
      1 / 2 ≤
        (∑ i with x i = true, regProb (run (grover N) (uniform N) x
          (groverOptIter N (weight x))) i) ∧
      (groverOptIter N (weight x) : ℝ) ≤
        Real.pi * Real.sqrt ((N : ℝ) / weight x) / 4 := by
  obtain ⟨i₀, hi₀⟩ := hx
  set t := weight x
  have ht1 : 1 ≤ t := card_pos.mpr ⟨i₀, by simp [hi₀]⟩
  have htN : t ≤ N := weight_le_length x
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have ht0 : (0 : ℝ) < t := Nat.cast_pos.mpr ht1
  set θ := searchAngle N t
  have hs : Real.sin θ = Real.sqrt ((t : ℝ) / N) := sin_searchAngle htN
  have hθ0 : 0 < θ := Real.arcsin_pos.mpr (Real.sqrt_pos.mpr (div_pos ht0 hN0))
  have hθpi : θ ≤ Real.pi / 2 := Real.arcsin_le_pi_div_two _
  set T := groverOptIter N t
  have hT1 : (T : ℝ) ≤ Real.pi / (4 * θ) := Nat.floor_le (by positivity)
  have hT2 : Real.pi / (4 * θ) < T + 1 := Nat.lt_floor_add_one _
  have hprob : ∑ i with x i = true, regProb (run (grover N) (uniform N) x T) i =
      Real.sin ((2 * T + 1) * θ) ^ 2 :=
    sum_regProb_run_grover hN x T
  have hmain : 1 - (t : ℝ) / N ≤ Real.sin ((2 * T + 1) * θ) ^ 2 := by
    set y := (2 * (T : ℝ) + 1) * θ
    have hy1 : y ≤ Real.pi / 2 + θ := by
      nlinarith [(le_div_iff₀ (by positivity)).mp hT1, show y = (2 * (T : ℝ) + 1) * θ from rfl]
    have hy2 : Real.pi / 2 - θ < y := by
      nlinarith [(div_lt_iff₀ (by positivity)).mp hT2, show y = (2 * (T : ℝ) + 1) * θ from rfl]
    have hcos : Real.cos y ^ 2 ≤ Real.sin θ ^ 2 := by
      rw [← Real.sin_pi_div_two_sub]
      have h1 : Real.sin (Real.pi / 2 - y) ≤ Real.sin θ :=
        Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) hθpi (by linarith)
      have h2 : -Real.sin θ ≤ Real.sin (Real.pi / 2 - y) := by
        rw [← Real.sin_neg]
        exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith) (by linarith)
      nlinarith
    rw [hs, Real.sq_sqrt (div_nonneg ht0.le hN0.le)] at hcos
    nlinarith [Real.sin_sq_add_cos_sq y]
  refine ⟨hprob ▸ hmain, ?_, groverOptIter_le ht1 htN⟩
  rw [hprob]
  by_cases h2t : 2 * t ≤ N
  · have hle_half : (t : ℝ) / N ≤ 1 / 2 := by
      rw [div_le_div_iff₀ hN0 zero_lt_two]
      exact_mod_cast (by omega : t * 2 ≤ 1 * N)
    linarith
  · push Not at h2t
    have hT0 : T = 0 := groverOptIter_eq_zero_of_lt_two_mul h2t htN
    rw [hT0]
    simp only [Nat.cast_zero, mul_zero, zero_add, one_mul, hs,
      Real.sq_sqrt (div_nonneg ht0.le hN0.le)]
    rw [div_le_div_iff₀ zero_lt_two hN0]
    exact_mod_cast (by omega : 1 * N ≤ t * 2)

/-- The `k` most significant bits of `w : BitString m` (`k ≤ m`). -/
@[expose] def msbPrefix {m : ℕ} (k : ℕ) (hk : k ≤ m) (w : BitString m) : BitString k :=
  fun i ↦ w ⟨m - k + i.val, by omega⟩

@[simp]
theorem msbPrefix_self {m : ℕ} (w : BitString m) :
    msbPrefix m le_rfl w = w := by
  funext i
  simp [msbPrefix]

/-- Extending `msbPrefix` by one bit prepends bit `m - 1 - k` via `Fin.cons`. -/
theorem msbPrefix_succ_eq_cons {m k : ℕ} (hk : k + 1 ≤ m) (w : BitString m) :
    msbPrefix (k + 1) hk w =
      Fin.cons (w ⟨m - 1 - k, by omega⟩) (msbPrefix k (by omega) w) := by
  funext i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · exact congrArg w (Fin.ext (by simp; omega))
  · exact congrArg w (Fin.ext (by simp; omega))

/-- Quotient characterization of `msbPrefix`. -/
theorem val_equivFin_msbPrefix {m k : ℕ} (hk : k ≤ m) (w : BitString m) :
    (BitString.equivFin k (msbPrefix k hk w) : ℕ) =
      (BitString.equivFin m w : ℕ) / 2 ^ (m - k) := by
  induction m with
  | zero =>
    obtain rfl : k = 0 := by omega
    simp
  | succ m ih =>
    rcases hk.eq_or_lt with rfl | hlt
    · simp
    · have hk' : k ≤ m := by omega
      have htail : msbPrefix k hk w = msbPrefix k hk' (Fin.tail w) := by
        funext i
        exact congrArg w (Fin.ext (by simp; omega))
      have hcons : w = Fin.cons (w 0) (Fin.tail w) := (Fin.cons_self_tail w).symm
      have hval : (BitString.equivFin (m + 1) w : ℕ) =
          (w 0).toNat + 2 * (BitString.equivFin m (Fin.tail w) : ℕ) := by
        conv_lhs => rw [hcons]
        exact val_equivFin_cons (w 0) (Fin.tail w)
      have hsub : m + 1 - k = (m - k) + 1 := by omega
      have hdiv2 : ((w 0).toNat + 2 * (BitString.equivFin m (Fin.tail w) : ℕ)) / 2 =
          (BitString.equivFin m (Fin.tail w) : ℕ) := by
        have hb : (w 0).toNat < 2 := by cases w 0 <;> decide
        omega
      rw [htail, ih hk', hval, hsub, pow_succ', ← Nat.div_div_eq_div_mul, hdiv2]

/-- Dyadic interval characterization of `msbPrefix`. -/
theorem msbPrefix_eq_iff_interval {m k : ℕ} (hk : k ≤ m) (w : BitString m) (p : BitString k) :
    msbPrefix k hk w = p ↔
      (BitString.equivFin k p : ℕ) * 2 ^ (m - k) ≤ (BitString.equivFin m w : ℕ) ∧
        (BitString.equivFin m w : ℕ) < ((BitString.equivFin k p : ℕ) + 1) * 2 ^ (m - k) := by
  have hpow : 0 < 2 ^ (m - k) := pow_pos zero_lt_two _
  have heq : msbPrefix k hk w = p ↔
      (BitString.equivFin k (msbPrefix k hk w) : ℕ) = (BitString.equivFin k p : ℕ) :=
    ⟨fun h ↦ h ▸ rfl, fun h ↦ (BitString.equivFin k).injective (Fin.ext h)⟩
  rw [heq, val_equivFin_msbPrefix hk]
  constructor
  · intro h
    rw [← h]
    exact ⟨Nat.div_mul_le_self _ _, by rw [add_one_mul]; exact Nat.lt_div_mul_add hpow⟩
  · rintro ⟨hlo, hhi⟩
    exact le_antisymm
      (Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul hpow).mpr hhi))
      ((Nat.le_div_iff_mul_le hpow).mpr hlo)

/-- Minimum `BitString m` attained by a nonempty finite table `y : ι → BitString m`. -/
noncomputable def minWord {ι : Type*} [Fintype ι] [Nonempty ι] {m : ℕ}
    (y : ι → BitString m) : BitString m :=
  y (((Set.univ : Set ι).exists_min_image (fun i ↦ BitString.equivFin m (y i))
    Set.finite_univ Set.univ_nonempty).choose)

/-- `minWord y` is attained in `y`. -/
theorem exists_eq_minWord {ι : Type*} [Fintype ι] [Nonempty ι] {m : ℕ}
    (y : ι → BitString m) : ∃ i : ι, y i = minWord y := by
  exact ⟨_, rfl⟩

/-- `minWord y` bounds every `y i` from below. -/
theorem equivFin_minWord_le {ι : Type*} [Fintype ι] [Nonempty ι] {m : ℕ}
    (y : ι → BitString m) (i : ι) :
    BitString.equivFin m (minWord y) ≤ BitString.equivFin m (y i) :=
  ((Set.univ : Set ι).exists_min_image (fun j ↦ BitString.equivFin m (y j))
    Set.finite_univ Set.univ_nonempty).choose_spec.2 i (Set.mem_univ i)

private theorem msbPrefix_succ_minWord_iff {ι : Type*} [Fintype ι] [Nonempty ι] {m k : ℕ}
    (hk : k + 1 ≤ m) (y : ι → BitString m) {p : BitString k}
    (hp : msbPrefix k (by omega) (minWord y) = p) :
    ((∃ i : ι, msbPrefix (k + 1) hk (y i) = Fin.cons false p) →
        msbPrefix (k + 1) hk (minWord y) = Fin.cons false p) ∧
      ((∀ i : ι, msbPrefix (k + 1) hk (y i) ≠ Fin.cons false p) →
        msbPrefix (k + 1) hk (minWord y) = Fin.cons true p) := by
  have hstep := msbPrefix_succ_eq_cons hk (minWord y)
  rw [hp] at hstep
  set bit := minWord y ⟨m - 1 - k, by omega⟩
  constructor
  · rintro ⟨i, hi⟩
    cases hbit : bit
    · rw [hstep, hbit]
    · exfalso
      rw [hbit] at hstep
      have hmin_int := (msbPrefix_eq_iff_interval hk (minWord y) (Fin.cons true p)).mp hstep
      have hi_int := (msbPrefix_eq_iff_interval hk (y i) (Fin.cons false p)).mp hi
      rw [val_equivFin_cons, Bool.toNat_true] at hmin_int
      rw [val_equivFin_cons, Bool.toNat_false, zero_add] at hi_int
      have hle : (BitString.equivFin m (minWord y) : ℕ) ≤ (BitString.equivFin m (y i) : ℕ) :=
        Fin.le_iff_val_le_val.mp (equivFin_minWord_le y i)
      have heq_mul :
          (1 + 2 * (BitString.equivFin k p : ℕ)) * 2 ^ (m - (k + 1)) =
            (2 * (BitString.equivFin k p : ℕ) + 1) * 2 ^ (m - (k + 1)) := by ring
      omega
  · intro hall
    cases hbit : bit
    · exfalso
      obtain ⟨i, hi⟩ := exists_eq_minWord y
      exact hall i (by rw [hi, hstep, hbit])
    · rw [hstep, hbit]

/-- Single-stage one-sided quantum `OR` distribution. -/
noncomputable def quantumOrOncePMF {N : ℕ} (hN : 0 < N) (x : Fin N → Bool) : PMF Bool :=
  (measure (run (orStage N) (randomGroverInit N (orRange N)) x (orRange N))
    (by rw [norm_run]; exact norm_randomGroverInit hN (Nat.mul_pos (by decide) (Nat.succ_pos _)))
  ).map fun p ↦ p.2.1

/-- `R`-fold amplified one-sided quantum `OR` distribution. -/
noncomputable def quantumOrAmpPMF {N : ℕ} (hN : 0 < N) (x : Fin N → Bool) : ℕ → PMF Bool
  | 0 => PMF.pure false
  | r + 1 => (quantumOrOncePMF hN x).bind fun b ↦
      if b then PMF.pure true else quantumOrAmpPMF hN x r

private def reindexBitString {a b : ℕ} (h : a = b) (v : BitString a) : BitString b :=
  fun i ↦ v ⟨i.val, by omega⟩

/-- Adaptive `s`-stage MSB-prefix refinement distribution. -/
noncomputable def quantumPrefixRefinePMF {N m : ℕ} (hN : 0 < N) (y : Fin N → BitString m)
    (R : ℕ) : ∀ (s : ℕ), s ≤ m → BitString (m - s) → PMF (BitString m)
  | 0, _, p => PMF.pure (reindexBitString (Nat.sub_zero m) p)
  | s + 1, _, p =>
    (quantumOrAmpPMF hN
      (fun i ↦ decide (msbPrefix (m - (s + 1) + 1) (by omega) (y i) = Fin.cons false p)) R).bind
      fun hasZero ↦
        quantumPrefixRefinePMF hN y R s (by omega)
          (reindexBitString (by omega) (Fin.cons (!hasZero) p))

/-- Adaptive `b`-stage quantum binary-prefix minimum search distribution. -/
noncomputable def quantumMinWordPMF {N m : ℕ} (hN : 0 < N) (y : Fin N → BitString m)
    (b : ℕ) (hb : b ≤ m) (R : ℕ) : PMF (BitString m) :=
  quantumPrefixRefinePMF hN y R b hb (fun _ ↦ false)

private theorem quantumOrOncePMF_true_toReal {N : ℕ} (hN : 0 < N) (x : Fin N → Bool) :
    (quantumOrOncePMF hN x true).toReal =
      ∑ i with x i = true,
        regProb (run (randomGrover N (orRange N)) (randomGroverInit N (orRange N)) x
          (orRange N - 1)) i := by
  have hnorm : ‖run (orStage N) (randomGroverInit N (orRange N)) x (orRange N)‖ = 1 := by
    rw [norm_run]
    exact norm_randomGroverInit hN (Nat.mul_pos (by decide) (Nat.succ_pos _))
  let ψ := run (orStage N) (randomGroverInit N (orRange N)) x (orRange N)
  let S : Finset (Fin N × Bool × (Unit × Fin (orRange N))) :=
    univ.filter fun p ↦ p.2.1 = true
  have hmap : quantumOrOncePMF hN x true = (measure ψ hnorm).toOuterMeasure (S : Set _) := by
    rw [quantumOrOncePMF, PMF.map_apply, tsum_fintype, PMF.toOuterMeasure_apply_fintype]
    refine Finset.sum_congr rfl fun p _ ↦ ?_
    by_cases hp : p.2.1 = true <;> simp [S, Set.indicator, hp, ψ]
  rw [hmap, measure_toOuterMeasure_apply,
    ENNReal.toReal_ofReal (measureProb_nonneg ψ S), measureProb_run_orStage hN]

private theorem pmf_bool_add_toReal (μ : PMF Bool) :
    (μ true).toReal + (μ false).toReal = 1 := by
  have htsum := μ.tsum_coe
  rw [tsum_fintype, Fintype.sum_bool] at htsum
  simpa [ENNReal.toReal_add (μ.apply_ne_top true) (μ.apply_ne_top false)] using
    congrArg ENNReal.toReal htsum

private theorem quantumOrAmpPMF_false_of_forall_false {N : ℕ} (hN : 0 < N) {x : Fin N → Bool}
    (hx : ∀ i, x i = false) (R : ℕ) :
    (quantumOrAmpPMF hN x R false).toReal = 1 := by
  have honce_t : (quantumOrOncePMF hN x true).toReal = 0 := by
    rw [quantumOrOncePMF_true_toReal hN]
    exact Finset.sum_eq_zero fun i hi ↦ by simp [hx i] at hi
  have honce_f : (quantumOrOncePMF hN x false).toReal = 1 := by
    linarith [pmf_bool_add_toReal (quantumOrOncePMF hN x)]
  induction R with
  | zero => simp [quantumOrAmpPMF]
  | succ r ih =>
    rw [quantumOrAmpPMF, Cslib.Probability.PMF.bind_apply_toReal, Fintype.sum_bool]
    simp [honce_t, honce_f, ih]

private theorem quantumOrAmpPMF_true_ge {N : ℕ} (hN : 0 < N) {x : Fin N → Bool}
    (hx : ∃ i, x i = true) (R : ℕ) :
    1 - (9 / 16 : ℝ) ^ R ≤ (quantumOrAmpPMF hN x R true).toReal := by
  have honce_f : (quantumOrOncePMF hN x false).toReal ≤ 9 / 16 := by
    have h7 : (7 / 16 : ℝ) ≤ (quantumOrOncePMF hN x true).toReal := by
      rw [quantumOrOncePMF_true_toReal hN]
      refine (by norm_num : (7 / 16 : ℝ) ≤ 1 / 2 - 1 / (4 * 4)).trans ?_
      exact le_sum_regProb_run_randomGrover hN (m := orRange N) (by norm_num)
        (by
          have h' : (N : ℝ) ≤ ((Nat.sqrt N + 1 : ℕ) : ℝ) ^ 2 := by
            exact_mod_cast (Nat.lt_succ_sqrt' N).le
          calc (4 : ℝ) ^ 2 * N ≤ 4 ^ 2 * ((Nat.sqrt N + 1 : ℕ) : ℝ) ^ 2 := by gcongr
            _ = (orRange N : ℝ) ^ 2 := by
              simp only [orRange, Nat.cast_mul, Nat.cast_ofNat]; ring)
        x hx
    linarith [pmf_bool_add_toReal (quantumOrOncePMF hN x)]
  suffices hfalse : (quantumOrAmpPMF hN x R false).toReal ≤ (9 / 16 : ℝ) ^ R by
    linarith [pmf_bool_add_toReal (quantumOrAmpPMF hN x R)]
  induction R with
  | zero => simp [quantumOrAmpPMF]
  | succ r ih =>
    rw [quantumOrAmpPMF, Cslib.Probability.PMF.bind_apply_toReal, Fintype.sum_bool]
    simp only [↓reduceIte, Bool.false_eq_true, PMF.pure_apply, ENNReal.toReal_zero,
      mul_zero, zero_add]
    calc
      (quantumOrOncePMF hN x false).toReal * (quantumOrAmpPMF hN x r false).toReal
          ≤ (9 / 16 : ℝ) * (9 / 16 : ℝ) ^ r :=
        mul_le_mul honce_f ih ENNReal.toReal_nonneg (by norm_num)
      _ = (9 / 16 : ℝ) ^ (r + 1) := by ring

private theorem quantumPrefixRefinePMF_spec {N m : ℕ} [NeZero N] (y : Fin N → BitString m)
    (R : ℕ) (s : ℕ) :
    ∀ (hs : s ≤ m) (p : BitString (m - s)),
      msbPrefix (m - s) (Nat.sub_le m s) (minWord y) = p →
        (1 - (9 / 16 : ℝ) ^ R) ^ s ≤
          (quantumPrefixRefinePMF (NeZero.pos N) y R s hs p (minWord y)).toReal := by
  induction s with
  | zero =>
    intro hs p hp
    have hpeq : reindexBitString (Nat.sub_zero m) p = minWord y := by
      funext i
      have hi := congrFun hp ⟨i.val, by omega⟩
      simpa [reindexBitString, msbPrefix] using hi.symm
    simp [quantumPrefixRefinePMF, hpeq]
  | succ s ih =>
    intro hs p hp
    have hN : 0 < N := NeZero.pos N
    have hpow_nonneg : 0 ≤ 1 - (9 / 16 : ℝ) ^ R := by
      have h9 : (9 / 16 : ℝ) ^ R ≤ (1 : ℝ) ^ R := pow_le_pow_left₀ (by norm_num) (by norm_num) R
      have h1 : (1 : ℝ) ^ R = 1 := one_pow R
      linarith
    let pred : Fin N → Bool :=
      fun i ↦ decide (msbPrefix (m - (s + 1) + 1) (by omega) (y i) = Fin.cons false p)
    have hexpand :
        (quantumPrefixRefinePMF (NeZero.pos N) y R (s + 1) hs p (minWord y)).toReal =
          (quantumOrAmpPMF hN pred R true).toReal *
            (quantumPrefixRefinePMF hN y R s (by omega)
              (reindexBitString (by omega) (Fin.cons false p)) (minWord y)).toReal +
          (quantumOrAmpPMF hN pred R false).toReal *
            (quantumPrefixRefinePMF hN y R s (by omega)
              (reindexBitString (by omega) (Fin.cons true p)) (minWord y)).toReal := by
      rw [quantumPrefixRefinePMF, Cslib.Probability.PMF.bind_apply_toReal, Fintype.sum_bool]
      simp only [Bool.not_true, Bool.not_false]
      rfl
    rw [hexpand]
    have hchar := msbPrefix_succ_minWord_iff (by omega : (m - (s + 1)) + 1 ≤ m) y hp
    have hreind : ∀ q : BitString (m - (s + 1) + 1),
        msbPrefix (m - (s + 1) + 1) (by omega) (minWord y) = q →
        msbPrefix (m - s) (Nat.sub_le m s) (minWord y) =
          reindexBitString (by omega) q := by
      intro q hq
      funext i
      have hi := congrFun hq ⟨i.val, by omega⟩
      simpa [reindexBitString, msbPrefix,
        show m - (m - (s + 1) + 1) + i.val = m - (m - s) + i.val by omega] using hi
    by_cases hex : ∃ i : Fin N, msbPrefix (m - (s + 1) + 1) (by omega) (y i) = Fin.cons false p
    · obtain ⟨i₀, hi₀⟩ := hex
      have hp1 := hreind (Fin.cons false p) (hchar.1 ⟨i₀, hi₀⟩)
      have hih := ih (by omega) _ hp1
      have hamp := quantumOrAmpPMF_true_ge hN (x := pred) ⟨i₀, decide_eq_true hi₀⟩ R
      have hnonneg_f : 0 ≤ (quantumOrAmpPMF hN pred R false).toReal *
          (quantumPrefixRefinePMF hN y R s (by omega)
            (reindexBitString (by omega) (Fin.cons true p)) (minWord y)).toReal :=
        mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
      calc
        (1 - (9 / 16 : ℝ) ^ R) ^ (s + 1)
            = (1 - (9 / 16 : ℝ) ^ R) * (1 - (9 / 16 : ℝ) ^ R) ^ s := pow_succ' _ _
        _ ≤ (quantumOrAmpPMF hN pred R true).toReal *
              (quantumPrefixRefinePMF hN y R s (by omega)
                (reindexBitString (by omega) (Fin.cons false p)) (minWord y)).toReal :=
          mul_le_mul hamp hih (pow_nonneg hpow_nonneg s) ENNReal.toReal_nonneg
        _ ≤ _ := by linarith
    · push Not at hex
      have hall_pred : ∀ i : Fin N, pred i = false := fun i ↦ decide_eq_false (hex i)
      have hp1 := hreind (Fin.cons true p) (hchar.2 hex)
      have hih := ih (by omega) _ hp1
      have hamp := quantumOrAmpPMF_false_of_forall_false hN hall_pred R
      have hnonneg_t : 0 ≤ (quantumOrAmpPMF hN pred R true).toReal *
          (quantumPrefixRefinePMF hN y R s (by omega)
            (reindexBitString (by omega) (Fin.cons false p)) (minWord y)).toReal :=
        mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
      rw [hamp, one_mul]
      calc
        (1 - (9 / 16 : ℝ) ^ R) ^ (s + 1)
            = (1 - (9 / 16 : ℝ) ^ R) * (1 - (9 / 16 : ℝ) ^ R) ^ s := pow_succ' _ _
        _ ≤ 1 * (1 - (9 / 16 : ℝ) ^ R) ^ s :=
          mul_le_mul_of_nonneg_right
            (by linarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 9 / 16) R])
            (pow_nonneg hpow_nonneg s)
        _ ≤ _ := by linarith

/-- **Adaptive `b`-stage quantum binary-prefix minimum search guarantee**: outputs `minWord y` with
probability at least `(1 - (9 / 16) ^ R) ^ b` whenever some `y i₀` satisfies `val(y i₀) < 2 ^ b`. -/
theorem quantumMinWordPMF_minWord_ge {N m b : ℕ} [NeZero N] (hb : b ≤ m)
    (y : Fin N → BitString m) {i₀ : Fin N} (hi₀ : (BitString.equivFin m (y i₀) : ℕ) < 2 ^ b)
    (R : ℕ) :
    (1 - (9 / 16 : ℝ) ^ R) ^ b ≤
      (quantumMinWordPMF (NeZero.pos N) y b hb R (minWord y)).toReal := by
  have hinit : msbPrefix (m - b) (Nat.sub_le m b) (minWord y) = fun _ ↦ false := by
    rw [msbPrefix_eq_iff_interval]
    have hle : (BitString.equivFin m (minWord y) : ℕ) ≤ (BitString.equivFin m (y i₀) : ℕ) :=
      Fin.le_iff_val_le_val.mp (equivFin_minWord_le y i₀)
    have hsub : m - (m - b) = b := by omega
    rw [val_equivFin_false, zero_mul, zero_add, one_mul, hsub]
    exact ⟨Nat.zero_le _, lt_of_le_of_lt hle hi₀⟩
  exact quantumPrefixRefinePMF_spec y R b hb (fun _ ↦ false) hinit

/-- Predicate asserting that `v : Fin (2 ^ m)` is the unsigned minimum value of `y`. -/
@[expose] def IsMinUnsignedValue {ι : Type*} {m : ℕ} (y : ι → BitString m)
    (v : Fin (2 ^ m)) : Prop :=
  (∃ i, BitString.equivFin m (y i) = v) ∧ ∀ i, v ≤ BitString.equivFin m (y i)

instance instDecidableIsMinUnsignedValue {ι : Type*} [Fintype ι] {m : ℕ}
    (y : ι → BitString m) (v : Fin (2 ^ m)) : Decidable (IsMinUnsignedValue y v) := by
  unfold IsMinUnsignedValue
  infer_instance

private theorem isKthSmallest_one_iff_min {ι α : Type*} [Fintype ι] [LinearOrder α]
    (X : ι → α) (y₀ : α) :
    IsKthSmallest X 1 y₀ ↔ (∃ i, X i = y₀) ∧ ∀ i, y₀ ≤ X i := by
  rw [IsKthSmallest, Nat.lt_one_iff, card_eq_zero, filter_eq_empty_iff]
  constructor
  · rintro ⟨hnone, hpos⟩
    have hge : ∀ i, y₀ ≤ X i := fun i ↦ not_lt.mp (hnone (mem_univ i))
    obtain ⟨i, hi⟩ := card_pos.mp hpos
    exact ⟨⟨i, le_antisymm (mem_filter.mp hi).2 (hge i)⟩, hge⟩
  · rintro ⟨⟨i, rfl⟩, hge⟩
    refine ⟨fun j _ ↦ not_lt.mpr (hge j), card_pos.mpr ⟨i, mem_filter.mpr ⟨mem_univ i, le_rfl⟩⟩⟩

private theorem isApproxKthSmallest_one_one_iff {ι α : Type*} [Fintype ι] [LinearOrder α]
    [Nonempty ι] (X : ι → α) (y₀ : α) :
    IsApproxKthSmallest X 1 1 y₀ ↔ IsKthSmallest X 1 y₀ := by
  rw [IsApproxKthSmallest]
  constructor
  · rintro ⟨j, hj1, _, _, hjlt, hk⟩
    norm_num at hjlt
    have hj_le1 : j ≤ 1 := by exact_mod_cast hjlt
    obtain rfl : j = 1 := le_antisymm hj_le1 hj1
    exact hk
  · intro hk
    exact ⟨1, le_rfl, Fintype.card_pos, by norm_num, by norm_num, hk⟩

/-- **`Ω(√N)` QRAM minimum-finding query lower bound**. -/
theorem qram_minimum_query_lower_bound {ι W : Type*} [Fintype ι] [Fintype W] {m : ℕ}
    (hm : 1 ≤ m) (hcard : 4 ≤ Fintype.card ι)
    (U : ℕ → ValueState ι (BitString m) W →ₗᵢ[ℂ] ValueState ι (BitString m) W)
    {ψ₀ : ValueState ι (BitString m) W} (hψ₀ : ‖ψ₀‖ = 1)
    (T : ℕ) (out : ι × BitString m × W → Fin (2 ^ m))
    (hsucc : ∀ y : ι → BitString m, 2 / 3 ≤
      measureProb (runValue addStep U ψ₀ y T)
        (univ.filter fun p ↦ IsMinUnsignedValue y (out p))) :
    Real.sqrt (Fintype.card ι) + Real.sqrt (Fintype.card ι - 1) ≤ 288 * T := by
  classical
  have hne : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  let stepFin : Fin (2 ^ m) →
      (EuclideanSpace ℂ (BitString m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (BitString m)) :=
    fun v ↦ addStep ((BitString.equivFin m).symm v)
  have hpow : 2 ≤ 2 ^ m := by
    calc 2 = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ m := Nat.pow_le_pow_right zero_lt_two hm
  let a₀ : Fin (2 ^ m) := ⟨0, by omega⟩
  let a₁ : Fin (2 ^ m) := ⟨1, by omega⟩
  have ha : a₀ < a₁ := Fin.mk_lt_mk.mpr zero_lt_one
  have hR : ∀ φ, ((stepFin a₀).symm.trans (stepFin a₁))
      (((stepFin a₀).symm.trans (stepFin a₁)) φ) = φ :=
    addStep_rel_involutive BitString.add_self _ _
  have hbound := kthSmallest_involution_lower_bound stepFin U hψ₀ T out a₀ a₁ ha hR
    (k := 1) (Δ := 1) le_rfl (by omega) le_rfl (by exact_mod_cast hcard)
    (fun X _ ↦ by
      let y : ι → BitString m := fun i ↦ (BitString.equivFin m).symm (X i)
      have hrun : ∀ t, runValue stepFin U ψ₀ X t = runValue addStep U ψ₀ y t := by
        intro t
        induction t with
        | zero => rfl
        | succ t ih =>
          rw [runValue, runValue, ih]
          congr 1
          ext ⟨i, v, w⟩
          simp [stepFin, y]
      have hset : (univ.filter fun p ↦ IsApproxKthSmallest X 1 1 (out p)) =
          univ.filter fun p ↦ IsMinUnsignedValue y (out p) := by
        ext p
        simp only [mem_filter, mem_univ, true_and, @isApproxKthSmallest_one_one_iff _ _ _ _ hne,
          isKthSmallest_one_iff_min, IsMinUnsignedValue, y, Equiv.apply_symm_apply]
      rw [hrun T, hset]
      simpa only [show (1 : ℝ) - 1 / 3 = 2 / 3 by norm_num] using hsucc y)
  simpa using hbound

end CslibFrontier.Quantum
