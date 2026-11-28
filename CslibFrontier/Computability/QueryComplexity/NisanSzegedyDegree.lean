module

public import Cslib.Computability.QueryComplexity.Measures
public import CslibFrontier.Computability.QueryComplexity.Degree
public import CslibFrontier.Foundations.BooleanAnalysis.Fourier
public import CslibFrontier.Foundations.BooleanAnalysis.Influence
public import CslibFrontier.Foundations.BooleanAnalysis.MaximalSupport
public import CslibFrontier.Foundations.BooleanAnalysis.Symmetrization
public import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.Bertrand

/-!
# Polynomial Degree Lower Bounds for Coordinate-Dependent and Symmetric Boolean Functions

This module establishes general lower bounds on the real multilinear polynomial degree `degree f` of
Boolean functions `f : {0, 1}^N → Bool`:

* **Logarithmic degree lower bound for coordinate-dependent functions**: every Boolean function `f`
  that depends on all `N` coordinates satisfies `N ≤ degree f * 2 ^ (degree f - 1)` and, for
  `2 ≤ N`, `log₂ N - log₂ (log₂ N) ≤ degree f`. The proof combines total-influence upper bounds from
  Fourier support degree with coordinatewise influence lower bounds from maximal Fourier support on
  subcubes.
* **Prime-gap degree lower bounds for non-constant symmetric functions**: for every non-constant
  symmetric Boolean function `f` on `N` bits and every prime `p ≤ N + 1`, `p - 1 ≤ degree f`. In
  particular, `degree f = N` whenever `N + 1` is prime, and `(N + 1) / 2 ≤ degree f` unconditionally
  for all `N` by Bertrand's postulate.

## Main definitions

* `CslibFrontier.Computability.QueryComplexity.DependsOnAll`: predicate asserting that a Boolean
  function is sensitive to every coordinate at some input.
* `CslibFrontier.Computability.QueryComplexity.symValue`: value of a symmetric Boolean function on
  the Hamming layer of weight `k`.

## Main results

* `CslibFrontier.Computability.QueryComplexity.nisan_szegedy_degree_mul_two_pow`:
  `N ≤ degree f * 2 ^ (degree f - 1)` when `f` depends on all `N` coordinates.
* `CslibFrontier.Computability.QueryComplexity.nisan_szegedy_degree_log`:
  `log₂ N - log₂ (log₂ N) ≤ degree f` for `2 ≤ N` when `f` depends on all `N` coordinates.
* `CslibFrontier.Computability.QueryComplexity.degree_eq_of_isSymmetric_of_prime`:
  `degree f = N` for non-constant symmetric `f` when `N + 1` is prime.
* `CslibFrontier.Computability.QueryComplexity.prime_sub_one_le_degree_of_isSymmetric`:
  `p - 1 ≤ degree f` for non-constant symmetric `f` and prime `p ≤ N + 1`.
* `CslibFrontier.Computability.QueryComplexity.degree_ge_half_of_isSymmetric`:
  `(N + 1) / 2 ≤ degree f` for every non-constant symmetric `f`.
-/

public section

open Finset Polynomial Cslib Cslib.BitString Cslib.QueryComplexity

namespace CslibFrontier.Computability.QueryComplexity

/-- A Boolean function `f` on `N` bits depends on all `N` coordinates when every coordinate admits
an input at which flipping that coordinate changes the output of `f`. -/
@[expose] public def DependsOnAll {N : ℕ} (f : BooleanFunction N) : Prop :=
  ∀ i : Fin N, ∃ x : BitString N, IsSensitiveCoord f x i

/-- Nonzero functions on `{0, 1}^N` whose Fourier coefficients vanish above degree `D` are nonzero
on at least `2 ^ (N - D)` inputs. -/
private theorem card_ne_zero_ge_of_fourier_degree {N D : ℕ} {g : BitString N → ℝ}
    (hD : ∀ T : Finset (Fin N), D < #T → fourierCoeff g T = 0)
    (hne : ∃ x, g x ≠ 0) :
    2 ^ (N - D) ≤ #{x : BitString N | g x ≠ 0} := by
  classical
  have hnonempty : (univ.filter fun S : Finset (Fin N) => fourierCoeff g S ≠ 0).Nonempty := by
    by_contra hempty
    rw [not_nonempty_iff_eq_empty] at hempty
    obtain ⟨x, hx⟩ := hne
    apply hx
    rw [← sum_fourierCoeff_mul_chi g x]
    refine sum_eq_zero fun S _ => ?_
    have h0 : fourierCoeff g S = 0 := by
      by_contra hS
      have : S ∈ (univ.filter fun T : Finset (Fin N) => fourierCoeff g T ≠ 0) :=
        mem_filter.2 ⟨mem_univ _, hS⟩
      rw [hempty] at this
      exact notMem_empty S this
    rw [h0, zero_mul]
  obtain ⟨S, hSmem, hSmax⟩ := exists_max_image _ Finset.card hnonempty
  have hS : fourierCoeff g S ≠ 0 := (mem_filter.1 hSmem).2
  have hSdeg : #S ≤ D := by
    by_contra hgt
    exact hS (hD S (lt_of_not_ge hgt))
  have hmax : ∀ T : Finset (Fin N), S ⊂ T → fourierCoeff g T = 0 := by
    intro T hST
    by_contra hT
    have hle := hSmax T (mem_filter.2 ⟨mem_univ _, hT⟩)
    exact (card_lt_card hST).not_ge hle
  have hpick : ∀ a : ({i : Fin N // i ∉ S} → Bool),
      ∃ y : BitString N, (∀ i (hi : i ∉ S), y i = a ⟨i, hi⟩) ∧ g y ≠ 0 := by
    intro a
    let x : BitString N := fun i => if hi : i ∈ S then false else a ⟨i, hi⟩
    obtain ⟨y, hy, hgy⟩ := exists_ne_zero_on_face_of_fourierCoeff_maximal S g hS hmax x
    exact ⟨y, fun i hi => by simpa [x, hi] using hy i hi, hgy⟩
  choose φ hφeq hφne using hpick
  have hinj : Function.Injective φ := by
    intro a₁ a₂ h
    funext ⟨i, hi⟩
    rw [← hφeq a₁ i hi, ← hφeq a₂ i hi, h]
  have hsub : univ.image φ ⊆ ({y : BitString N | g y ≠ 0} : Finset (BitString N)) := by
    intro y hy
    obtain ⟨a, -, rfl⟩ := mem_image.1 hy
    exact mem_filter.2 ⟨mem_univ _, hφne a⟩
  calc 2 ^ (N - D)
      ≤ 2 ^ (N - #S) := Nat.pow_le_pow_right (by norm_num) (Nat.sub_le_sub_left hSdeg N)
    _ = Fintype.card ({i : Fin N // i ∉ S} → Bool) := by
        rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_subtype_compl, Fintype.card_fin,
          Fintype.card_coe]
    _ = #(univ.image φ) := by
        rw [card_image_of_injective _ hinj, card_univ]
    _ ≤ #{x : BitString N | g x ≠ 0} := card_le_card hsub

/-- Every Boolean function `f` on `N` bits that depends on all `N` coordinates satisfies
`N ≤ degree f * 2 ^ (degree f - 1)`. -/
public theorem nisan_szegedy_degree_mul_two_pow {N : ℕ} {f : BooleanFunction N}
    (hdep : DependsOnAll f) :
    N ≤ degree f * 2 ^ (degree f - 1) := by
  classical
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · exact Nat.zero_le _
  set d := degree f
  have hd_pos : 0 < d := by
    by_contra hd0
    have hd : d = 0 := Nat.eq_zero_of_not_pos hd0
    obtain ⟨x, hx⟩ := hdep ⟨0, hN⟩
    have hzero : ∀ S : Finset (Fin N), 0 < #S →
        fourierCoeff (fun y => signVal (f y)) S = 0 := by
      intro S hS
      have htd : totalDegree (fun y => signVal (f y)) ≤ 0 := by
        rw [← degree_eq_totalDegree_signVal]
        exact hd.le
      exact (totalDegree_le_iff_fourierCoeff_eq_zero.1 htd) S hS
    have hconst : ∀ y, signVal (f y) = fourierCoeff (fun z => signVal (f z)) ∅ := by
      intro y
      rw [← sum_fourierCoeff_mul_chi (fun z => signVal (f z)) y,
        sum_eq_single ∅ (fun S _ hS => by
          rw [hzero S (card_pos.2 (nonempty_iff_ne_empty.2 hS)), zero_mul]) (by simp)]
      simp
    have hEq := (hconst x).trans (hconst (Function.update x ⟨0, hN⟩ (!x ⟨0, hN⟩))).symm
    have : f (Function.update x ⟨0, hN⟩ (!x ⟨0, hN⟩)) = f x := by
      cases h1 : f x <;> cases h2 : f (Function.update x ⟨0, hN⟩ (!x ⟨0, hN⟩))
      · rfl
      · rw [h1, h2] at hEq; norm_num [signVal] at hEq
      · rw [h1, h2] at hEq; norm_num [signVal] at hEq
      · rfl
    exact hx this
  have htot : totalInfluence (fun x => signVal (f x)) ≤ (d : ℝ) := by
    rw [totalInfluence_eq_sum_card_mul_fourierCoeff_sq]
    have hle : ∀ S : Finset (Fin N),
        (#S : ℝ) * fourierCoeff (fun x => signVal (f x)) S ^ 2 ≤
          (d : ℝ) * fourierCoeff (fun x => signVal (f x)) S ^ 2 := by
      intro S
      by_cases hS : #S ≤ d
      · exact mul_le_mul_of_nonneg_right (by exact_mod_cast hS) (sq_nonneg _)
      · have h0 : fourierCoeff (fun x => signVal (f x)) S = 0 := by
          have htd : totalDegree (fun x => signVal (f x)) ≤ d := by
            rw [← degree_eq_totalDegree_signVal]
          exact (totalDegree_le_iff_fourierCoeff_eq_zero.1 htd) S (lt_of_not_ge hS)
        simp [h0]
    calc ∑ S : Finset (Fin N), (#S : ℝ) * fourierCoeff (fun x => signVal (f x)) S ^ 2
        ≤ ∑ S : Finset (Fin N), (d : ℝ) * fourierCoeff (fun x => signVal (f x)) S ^ 2 :=
          sum_le_sum fun S _ => hle S
      _ = (d : ℝ) * ∑ S : Finset (Fin N), fourierCoeff (fun x => signVal (f x)) S ^ 2 := by
          rw [← mul_sum]
      _ = (d : ℝ) := by rw [sum_fourierCoeff_sq_signVal, mul_one]
  have hinf : ∀ i : Fin N, ((2 : ℝ) ^ (d - 1))⁻¹ ≤ influence i (fun x => signVal (f x)) := by
    intro i
    obtain ⟨x, hx⟩ := hdep i
    have hdeg_deriv : ∀ T : Finset (Fin N), d - 1 < #T →
        fourierCoeff (BitString.derivative i (fun y => signVal (f y))) T = 0 := by
      intro T hT
      rw [fourierCoeff_derivative]
      split_ifs with hi
      · rfl
      · have hcard : d < #(insert i T) := by rw [card_insert_of_notMem hi]; omega
        have htd : totalDegree (fun y => signVal (f y)) ≤ d := by
          rw [← degree_eq_totalDegree_signVal]
        exact (totalDegree_le_iff_fourierCoeff_eq_zero.1 htd) (insert i T) hcard
    have hne : ∃ y, BitString.derivative i (fun z => signVal (f z)) y ≠ 0 :=
      ⟨x, (derivative_signVal_ne_zero_iff f i x).2 hx⟩
    have hcard := card_ne_zero_ge_of_fourier_degree hdeg_deriv hne
    rw [influence_signVal_eq_dens]
    have hdens :
        (dens {y : BitString N | BitString.derivative i (fun z => signVal (f z)) y ≠ 0} : ℝ) =
          (#{y : BitString N | BitString.derivative i (fun z => signVal (f z)) y ≠ 0} : ℝ) /
            (2 ^ N : ℝ) := by
      simp [dens, Fintype.card_bool, Fintype.card_fin]
    rw [hdens, le_div_iff₀ (by positivity)]
    have hpow : (2 : ℝ) ^ (N - (d - 1)) * (2 : ℝ) ^ (d - 1) = (2 : ℝ) ^ N := by
      rw [← pow_add, Nat.sub_add_cancel (by have := degree_le_card f; omega)]
    have hcardR : ((2 : ℝ) ^ (N - (d - 1))) ≤
        (#{y : BitString N | BitString.derivative i (fun z => signVal (f z)) y ≠ 0} : ℝ) := by
      exact_mod_cast hcard
    calc ((2 : ℝ) ^ (d - 1))⁻¹ * (2 : ℝ) ^ N
        = ((2 : ℝ) ^ (d - 1))⁻¹ * ((2 : ℝ) ^ (N - (d - 1)) * (2 : ℝ) ^ (d - 1)) := by rw [hpow]
      _ = (2 : ℝ) ^ (N - (d - 1)) := by field_simp
      _ ≤ _ := hcardR
  have hsum : (N : ℝ) * ((2 : ℝ) ^ (d - 1))⁻¹ ≤ totalInfluence (fun x => signVal (f x)) := by
    rw [totalInfluence]
    calc (N : ℝ) * ((2 : ℝ) ^ (d - 1))⁻¹
        = ∑ _i : Fin N, ((2 : ℝ) ^ (d - 1))⁻¹ := by
          rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ ≤ ∑ i : Fin N, influence i (fun x => signVal (f x)) :=
          sum_le_sum fun i _ => hinf i
  have hreal : (N : ℝ) ≤ (d : ℝ) * (2 : ℝ) ^ (d - 1) := by
    have h1 : (N : ℝ) * ((2 : ℝ) ^ (d - 1))⁻¹ ≤ (d : ℝ) := hsum.trans htot
    rwa [mul_inv_le_iff₀ (by positivity)] at h1
  exact_mod_cast hreal

/-- Logarithmic form of the polynomial degree lower bound: every Boolean function `f` on `N ≥ 2`
bits depending on all `N` coordinates satisfies `log₂ N - log₂ (log₂ N) ≤ degree f`. -/
public theorem nisan_szegedy_degree_log {N : ℕ} (hN : 2 ≤ N) {f : BooleanFunction N}
    (hdep : DependsOnAll f) :
    Real.logb 2 N - Real.logb 2 (Real.logb 2 N) ≤ (degree f : ℝ) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlog_ge_one : (1 : ℝ) ≤ Real.logb 2 N := by
    rw [← Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
    exact Real.logb_le_logb_of_le (by norm_num) (by norm_num) (by exact_mod_cast hN)
  have hloglog_nonneg : 0 ≤ Real.logb 2 (Real.logb 2 N) :=
    Real.logb_nonneg (by norm_num) hlog_ge_one
  by_cases hlt : Real.logb 2 N ≤ (degree f : ℝ)
  · linarith
  · push Not at hlt
    have hbound : (N : ℝ) ≤ (degree f : ℝ) * (2 : ℝ) ^ (degree f - 1) := by
      exact_mod_cast nisan_szegedy_degree_mul_two_pow hdep
    have hd_pos : 0 < degree f := by
      by_contra h0
      have hd0 : degree f = 0 := Nat.eq_zero_of_not_pos h0
      rw [hd0, Nat.cast_zero, zero_mul] at hbound
      linarith
    have hdR_pos : (0 : ℝ) < degree f := by exact_mod_cast hd_pos
    have h2pos : (0 : ℝ) < (2 : ℝ) ^ (degree f - 1) := by positivity
    have hlog := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hNpos hbound
    rw [Real.logb_mul hdR_pos.ne' h2pos.ne', Real.logb_pow,
      Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one] at hlog
    have hlogd : Real.logb 2 (degree f : ℝ) ≤ Real.logb 2 (Real.logb 2 N) :=
      Real.logb_le_logb_of_le (by norm_num) hdR_pos hlt.le
    have hsub : ((degree f - 1 : ℕ) : ℝ) = (degree f : ℝ) - 1 := by
      rw [Nat.cast_sub hd_pos, Nat.cast_one]
    rw [hsub] at hlog
    linarith

/-- The value `f_k` of a symmetric Boolean function `f` on inputs of Hamming weight `k`. -/
public noncomputable def symValue {N : ℕ} (f : BooleanFunction N) (k : ℕ) : Bool :=
  @decide (∃ x : BitString N, weight x = k ∧ f x = true) (Classical.propDecidable _)

/-- On inputs of Hamming weight `weight x`, `symValue f (weight x)` agrees with `f x`. -/
public theorem symValue_weight {N : ℕ} {f : BooleanFunction N} (hf : f.IsSymmetric)
    (x : BitString N) : symValue f (weight x) = f x := by
  classical
  unfold symValue
  rw [Bool.eq_iff_iff, @decide_eq_true_eq _ (Classical.propDecidable _)]
  exact ⟨fun ⟨y, hy, hfy⟩ => hf y x hy ▸ hfy, fun hx => ⟨x, rfl, hx⟩⟩

/-- Every non-constant symmetric Boolean function `f` on `N` bits admits a jump index `k < N` with
`symValue f k ≠ symValue f (k + 1)`. -/
private theorem exists_jump_of_isSymmetric {N : ℕ} {f : BooleanFunction N}
    (hsym : f.IsSymmetric) (hnc : ¬∀ x y, f x = f y) :
    ∃ k < N, symValue f k ≠ symValue f (k + 1) := by
  by_contra hno
  push Not at hno
  have hconst : ∀ k ≤ N, symValue f k = symValue f 0 := by
    intro k hk
    induction k with
    | zero => rfl
    | succ k ih => exact (hno k (by omega)).symm.trans (ih (by omega))
  apply hnc
  intro x y
  rw [← symValue_weight hsym x, ← symValue_weight hsym y,
    hconst (weight x) ((weight_le x).trans_eq (Fintype.card_fin N)),
    hconst (weight y) ((weight_le y).trans_eq (Fintype.card_fin N))]

/-- Absorption identity `(j + 1) * C(M + 1, j + 1) = (M + 1) * C(M, j)`. -/
private theorem succ_mul_choose_succ (M j : ℕ) :
    (j + 1) * (M + 1).choose (j + 1) = (M + 1) * M.choose j := by
  induction M generalizing j with
  | zero =>
    rcases j with _ | j
    · simp
    · rw [Nat.choose_eq_zero_of_lt (by omega : 1 < j + 2),
        Nat.choose_eq_zero_of_lt (by omega : 0 < j + 1), mul_zero, mul_zero]
  | succ M ih =>
    cases j with
    | zero => simp
    | succ j =>
      rw [Nat.choose_succ_succ (M + 1) (j + 1), mul_add]
      have h1 := ih j
      have h2 := ih (j + 1)
      have h3 : (j + 1 + 1) * (M + 1).choose (j + 1) =
          (j + 1) * (M + 1).choose (j + 1) + (M + 1).choose (j + 1) := by ring
      rw [h3, h1, h2, Nat.choose_succ_succ M j]
      ring

/-- If `q` is a real polynomial of degree strictly less than `N`, its `N`-th forward difference at
`0` vanishes: `∑_{k=0}^N (-1)^(N-k) C(N,k) q(k) = 0`. -/
private theorem sum_alt_choose_eval_eq_zero {N : ℕ} {q : ℝ[X]} (hq : q.natDegree < N) :
    ∑ k ∈ range (N + 1), (-1 : ℝ) ^ (N - k) * (N.choose k : ℝ) * q.eval (k : ℝ) = 0 := by
  have hpow : ∀ (M d : ℕ), d < M →
      ∑ k ∈ range (M + 1), (-1 : ℝ) ^ (M - k) * (M.choose k : ℝ) * (k : ℝ) ^ d = 0 := by
    intro M
    induction M with
    | zero => intro d hd; omega
    | succ M ih =>
      intro d hd
      cases d with
      | zero =>
        have h := add_pow (1 : ℝ) (-1 : ℝ) (M + 1)
        rw [add_neg_cancel, zero_pow (Nat.succ_ne_zero M)] at h
        exact (sum_congr rfl fun k _ => by simp).trans h.symm
      | succ d =>
        have hshift :
            ∑ k ∈ range (M + 2),
                (-1 : ℝ) ^ (M + 1 - k) * ((M + 1).choose k : ℝ) * (k : ℝ) ^ (d + 1) =
              ((M + 1 : ℕ) : ℝ) *
                ∑ j ∈ range (M + 1),
                  (-1 : ℝ) ^ (M - j) * (M.choose j : ℝ) * ((j : ℝ) + 1) ^ d := by
          rw [sum_range_succ']
          simp only [Nat.cast_zero, zero_pow (Nat.succ_ne_zero d), mul_zero, add_zero, mul_sum]
          refine sum_congr rfl fun j _ => ?_
          have hbin : ((M + 1).choose (j + 1) : ℝ) * ((j : ℝ) + 1) =
              ((M + 1 : ℕ) : ℝ) * (M.choose j : ℝ) := by
            have hnat := succ_mul_choose_succ M j
            have hcast : (((j + 1) * (M + 1).choose (j + 1) : ℕ) : ℝ) =
                (((M + 1) * M.choose j : ℕ) : ℝ) := congrArg Nat.cast hnat
            push_cast at hcast ⊢
            linear_combination hcast
          have hexp : M + 1 - (j + 1) = M - j := by omega
          rw [hexp, pow_succ]
          push_cast at hbin ⊢
          linear_combination ((-1 : ℝ) ^ (M - j) * ((j : ℝ) + 1) ^ d) * hbin
        rw [hshift]
        have hbin_sum :
            ∑ j ∈ range (M + 1), (-1 : ℝ) ^ (M - j) * (M.choose j : ℝ) * ((j : ℝ) + 1) ^ d =
              ∑ r ∈ range (d + 1), (d.choose r : ℝ) *
                ∑ j ∈ range (M + 1), (-1 : ℝ) ^ (M - j) * (M.choose j : ℝ) * (j : ℝ) ^ r := by
          trans ∑ j ∈ range (M + 1), ∑ r ∈ range (d + 1),
              (-1 : ℝ) ^ (M - j) * (M.choose j : ℝ) * ((d.choose r : ℝ) * (j : ℝ) ^ r)
          · refine sum_congr rfl fun j _ => ?_
            rw [add_pow, mul_sum]
            refine sum_congr rfl fun r _ => by ring
          · rw [sum_comm]
            refine sum_congr rfl fun r _ => ?_
            rw [mul_sum]
            refine sum_congr rfl fun j _ => by ring
        rw [hbin_sum, sum_eq_zero fun r hr => by
          rw [ih r (by have := mem_range.1 hr; omega), mul_zero], mul_zero]
  have hsum :
      ∑ k ∈ range (N + 1), (-1 : ℝ) ^ (N - k) * (N.choose k : ℝ) * q.eval (k : ℝ) =
        ∑ d ∈ range (q.natDegree + 1), q.coeff d *
          ∑ k ∈ range (N + 1), (-1 : ℝ) ^ (N - k) * (N.choose k : ℝ) * (k : ℝ) ^ d := by
    trans ∑ k ∈ range (N + 1), ∑ d ∈ range (q.natDegree + 1),
        (-1 : ℝ) ^ (N - k) * (N.choose k : ℝ) * (q.coeff d * (k : ℝ) ^ d)
    · refine sum_congr rfl fun k _ => ?_
      rw [eval_eq_sum_range, mul_sum]
    · rw [sum_comm]
      refine sum_congr rfl fun d _ => ?_
      rw [mul_sum]
      refine sum_congr rfl fun k _ => by ring
  rw [hsum]
  exact sum_eq_zero fun d hd => by
    rw [hpow N d (by have := mem_range.1 hd; omega), mul_zero]

/-- If `f` is a non-constant symmetric Boolean function on `{0, 1}^N` and `N + 1` is prime, then
`degree f = N`. -/
public theorem degree_eq_of_isSymmetric_of_prime {N : ℕ} {f : BooleanFunction N}
    (hsym : f.IsSymmetric) (hnc : ¬∀ x y, f x = f y) (hp : (N + 1).Prime) :
    degree f = N := by
  classical
  refine le_antisymm (degree_le_card f) ?_
  by_contra hlt
  push Not at hlt
  obtain ⟨q, hqdeg, hq⟩ :=
    exists_natDegree_le_eval_eq_layerAverage (degree_le_iff_mem_lowDegree.1 (le_refl (degree f)))
  have h0 := sum_alt_choose_eval_eq_zero (lt_of_le_of_lt hqdeg hlt)
  have hval : ∀ k ≤ N, q.eval (k : ℝ) = ((if symValue f k then (1 : ℤ) else 0) : ℝ) := by
    intro k hk
    rw [hq k (by rw [Fintype.card_fin]; exact hk), layerAverage, expect_eq_sum_div_card]
    have hcongr :
        ∑ x ∈ ({x : BitString N | weight x = k} : Finset (BitString N)), bitVal ℝ (f x) =
          ∑ _x ∈ ({x : BitString N | weight x = k} : Finset (BitString N)),
            ((if symValue f k then (1 : ℤ) else 0) : ℝ) :=
      sum_congr rfl fun x hx => by
        rw [← symValue_weight hsym x, (mem_filter.1 hx).2]
        cases symValue f k <;> simp [bitVal]
    rw [hcongr, sum_const, nsmul_eq_mul, mul_div_cancel_left₀]
    exact_mod_cast (weightLayer_nonempty hk).card_pos.ne'
  have hZ : ∑ k ∈ range (N + 1),
      (-1 : ℤ) ^ (N - k) * (N.choose k : ℤ) * (if symValue f k then (1 : ℤ) else 0) = 0 := by
    have hR : ((∑ k ∈ range (N + 1),
        (-1 : ℤ) ^ (N - k) * (N.choose k : ℤ) *
          (if symValue f k then (1 : ℤ) else 0) : ℤ) : ℝ) = 0 := by
      push_cast
      refine (sum_congr rfl fun k hk => ?_).trans h0
      have hkN : k ≤ N := Nat.lt_succ_iff.1 (mem_range.1 hk)
      rw [hval k hkN]
      cases symValue f k <;> simp
    exact_mod_cast hR
  let p := N + 1
  have hchoose_mod : ∀ k ≤ N, (N.choose k : ZMod p) = (-1 : ZMod p) ^ k := by
    intro k hk
    induction k with
    | zero => simp
    | succ k ih =>
      have hk' : k ≤ N := by omega
      have hdvd : p ∣ p.choose (k + 1) :=
        Nat.Prime.dvd_choose_self hp (Nat.succ_ne_zero k) (by omega)
      have hsum0 : ((p.choose (k + 1) : ℕ) : ZMod p) = 0 :=
        (ZMod.natCast_eq_zero_iff _ _).2 hdvd
      have hpas : p.choose (k + 1) = N.choose k + N.choose (k + 1) :=
        Nat.choose_succ_succ N k
      rw [hpas, Nat.cast_add, ih hk'] at hsum0
      have hneg : ((N.choose (k + 1) : ℕ) : ZMod p) = -((-1 : ZMod p) ^ k) :=
        eq_neg_of_add_eq_zero_right hsum0
      rw [hneg, pow_succ]
      ring
  have hmod :
      ((-1 : ZMod p) ^ N) *
        (∑ k ∈ range (N + 1), (if symValue f k then (1 : ZMod p) else 0)) = 0 := by
    have hcast : ((∑ k ∈ range (N + 1),
        (-1 : ℤ) ^ (N - k) * (N.choose k : ℤ) *
          (if symValue f k then (1 : ℤ) else 0) : ℤ) : ZMod p) = 0 := by
      rw [hZ, Int.cast_zero]
    rw [Int.cast_sum] at hcast
    rw [mul_sum]
    refine (sum_congr rfl fun k hk => ?_).trans hcast
    have hkN : k ≤ N := Nat.lt_succ_iff.1 (mem_range.1 hk)
    have hpow : (-1 : ZMod p) ^ (N - k) * (-1 : ZMod p) ^ k = (-1 : ZMod p) ^ N := by
      rw [← pow_add, Nat.sub_add_cancel hkN]
    cases symValue f k
    · simp
    · simp only [↓reduceIte, mul_one, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one,
        Int.cast_natCast, hchoose_mod k hkN, hpow]
  have hsum_mod : ((∑ k ∈ range (N + 1), if symValue f k then 1 else 0 : ℕ) : ZMod p) = 0 := by
    have hcast_sum :
        ((∑ k ∈ range (N + 1), if symValue f k then 1 else 0 : ℕ) : ZMod p) =
          ∑ k ∈ range (N + 1), (if symValue f k then (1 : ZMod p) else 0) := by
      rw [Nat.cast_sum]
      refine sum_congr rfl fun k _ => by cases symValue f k <;> simp
    rw [hcast_sum]
    calc ∑ k ∈ range (N + 1), (if symValue f k then (1 : ZMod p) else 0)
        = ((-1 : ZMod p) ^ N * (-1 : ZMod p) ^ N) *
            ∑ k ∈ range (N + 1), (if symValue f k then (1 : ZMod p) else 0) := by
          rw [← mul_pow, show (-1 : ZMod p) * -1 = 1 by ring, one_pow, one_mul]
      _ = (-1 : ZMod p) ^ N *
            ((-1 : ZMod p) ^ N *
              ∑ k ∈ range (N + 1), (if symValue f k then (1 : ZMod p) else 0)) := by ring
      _ = 0 := by rw [hmod, mul_zero]
  rw [ZMod.natCast_eq_zero_iff] at hsum_mod
  set S := ∑ k ∈ range (N + 1), (if symValue f k then 1 else 0)
  have hSle : S ≤ N + 1 := by
    calc S ≤ ∑ _k ∈ range (N + 1), 1 := sum_le_sum fun k _ => by cases symValue f k <;> simp
      _ = N + 1 := by simp
  have hS0_or : S = 0 ∨ S = N + 1 := by
    rcases Nat.eq_zero_or_pos S with h0 | hpos
    · left; exact h0
    · right; exact le_antisymm hSle (Nat.le_of_dvd hpos hsum_mod)
  apply hnc
  rcases hS0_or with h0 | hfull
  · have hall : ∀ k ∈ range (N + 1), symValue f k = false := by
      intro k hk
      have := (sum_eq_zero_iff.1 h0) k hk
      cases h : symValue f k <;> simp_all
    intro x y
    rw [← symValue_weight hsym x, ← symValue_weight hsym y,
      hall (weight x)
        (mem_range.2 (Nat.lt_succ_of_le ((weight_le x).trans_eq (Fintype.card_fin N)))),
      hall (weight y)
        (mem_range.2 (Nat.lt_succ_of_le ((weight_le y).trans_eq (Fintype.card_fin N))))]
  · have hall : ∀ k ∈ range (N + 1), symValue f k = true := by
      intro k hk
      by_contra hfk
      have hfk' : symValue f k = false := Bool.eq_false_iff.2 hfk
      have hlt' : S < N + 1 := by
        calc S < ∑ _j ∈ range (N + 1), 1 :=
              sum_lt_sum (fun j _ => by cases symValue f j <;> simp) ⟨k, hk, by simp [hfk']⟩
          _ = N + 1 := by simp
      omega
    intro x y
    rw [← symValue_weight hsym x, ← symValue_weight hsym y,
      hall (weight x)
        (mem_range.2 (Nat.lt_succ_of_le ((weight_le x).trans_eq (Fintype.card_fin N)))),
      hall (weight y)
        (mem_range.2 (Nat.lt_succ_of_le ((weight_le y).trans_eq (Fintype.card_fin N))))]

/-- For every non-constant symmetric Boolean function `f` on `{0, 1}^N` and every prime
`p ≤ N + 1`, `p - 1 ≤ degree f`. -/
public theorem prime_sub_one_le_degree_of_isSymmetric {N : ℕ} {f : BooleanFunction N}
    (hsym : f.IsSymmetric) (hnc : ¬∀ x y, f x = f y) {p : ℕ} (hp : p.Prime) (hpN : p ≤ N + 1) :
    p - 1 ≤ degree f := by
  classical
  obtain ⟨k, hkN, hjump⟩ := exists_jump_of_isSymmetric hsym hnc
  have hp2 : 2 ≤ p := hp.two_le
  let m := p - 1
  have hm_pos : 1 ≤ m := by omega
  have hmN : m ≤ N := by omega
  let a := min k (N - m)
  have ha_le_k : a ≤ k := min_le_left _ _
  have ha_le : a + m ≤ N := by omega
  have hk_lt : k + 1 ≤ a + m := by omega
  let pad : BitString m → BitString N := fun y i =>
    if hi : (i : ℕ) < m then y ⟨i, hi⟩
    else decide ((i : ℕ) < m + a)
  have hweight_pad : ∀ y : BitString m, weight (pad y) = weight y + a := by
    intro y
    rw [weight, weight]
    have hdisj :
        Disjoint (univ.filter fun i : Fin N => (i : ℕ) < m ∧ pad y i = true)
          (univ.filter fun i : Fin N => m ≤ (i : ℕ) ∧ pad y i = true) :=
      disjoint_filter.2 fun i _ h1 h2 => by omega
    have hunion :
        (univ.filter fun i : Fin N => (i : ℕ) < m ∧ pad y i = true) ∪
          (univ.filter fun i : Fin N => m ≤ (i : ℕ) ∧ pad y i = true) =
        univ.filter fun i : Fin N => pad y i = true := by
      ext i
      simp only [mem_union, mem_filter, mem_univ, true_and]
      exact ⟨fun h => h.elim And.right And.right,
        fun hy => if hlt : (i : ℕ) < m then Or.inl ⟨hlt, hy⟩ else Or.inr ⟨Nat.le_of_not_lt hlt, hy⟩⟩
    rw [← hunion, card_union_of_disjoint hdisj]
    have hleft :
        #(univ.filter fun i : Fin N => (i : ℕ) < m ∧ pad y i = true) =
          #(univ.filter fun j : Fin m => y j = true) := by
      refine card_nbij' (fun i => if hi : (i : ℕ) < m then ⟨i, hi⟩ else ⟨0, hm_pos⟩)
        (fun j => ⟨j, lt_of_lt_of_le j.2 hmN⟩) ?_ ?_ ?_ ?_
      · intro i hi
        obtain ⟨hlt, hy⟩ := (mem_filter.1 hi).2
        simpa [hlt, pad] using hy
      · intro j hj
        have hlt : (j : ℕ) < m := j.2
        simp [hlt, pad, (mem_filter.1 hj).2]
      · intro i hi
        obtain ⟨hlt, _⟩ := (mem_filter.1 hi).2
        ext; simp [hlt]
      · intro j _
        ext; simp [j.2]
    have hright :
        #(univ.filter fun i : Fin N => m ≤ (i : ℕ) ∧ pad y i = true) = a := by
      calc #(univ.filter fun i : Fin N => m ≤ (i : ℕ) ∧ pad y i = true)
          = #(range a) := by
            refine card_nbij' (fun i : Fin N => (i : ℕ) - m)
              (fun r : ℕ => if hr : m + r < N then ⟨m + r, hr⟩ else ⟨0, by omega⟩)
              ?_ ?_ ?_ ?_
            · intro i hi
              dsimp only
              obtain ⟨hge, hy⟩ := (mem_filter.1 hi).2
              have hnot : ¬ ((i : ℕ) < m) := by omega
              simp [pad, hnot] at hy
              exact mem_range.2 (by omega)
            · intro r hr
              have hlt : m + r < N := by have := mem_range.1 hr; omega
              have hnot : ¬ (m + r < m) := by omega
              simp [pad, hlt, hnot, mem_range.1 hr]
            · intro i hi
              dsimp only
              obtain ⟨hge, hy⟩ := (mem_filter.1 hi).2
              have hnot : ¬ ((i : ℕ) < m) := by omega
              simp [pad, hnot] at hy
              have hlt : m + ((i : ℕ) - m) < N := by omega
              ext; simp [hlt]; omega
            · intro r hr
              have hlt : m + r < N := by have := mem_range.1 hr; omega
              simp [hlt]
        _ = a := card_range a
    rw [hleft, hright]
  let g : BooleanFunction m := fun y => f (pad y)
  have hgsym : g.IsSymmetric := fun y₁ y₂ h => by
    simp only [g]
    exact hsym (pad y₁) (pad y₂) (by rw [hweight_pad, hweight_pad, h])
  have hgnc : ¬∀ y₁ y₂, g y₁ = g y₂ := by
    intro hconst
    obtain ⟨y₁, hy₁⟩ := weightLayer_nonempty (n := m) (k := k - a) (by omega)
    obtain ⟨y₂, hy₂⟩ := weightLayer_nonempty (n := m) (k := k + 1 - a) (by omega)
    have h1 : g y₁ = symValue f k := by
      simp only [g, ← symValue_weight hsym, hweight_pad, mem_weightLayer.1 hy₁,
        Nat.sub_add_cancel ha_le_k]
    have h2 : g y₂ = symValue f (k + 1) := by
      simp only [g, ← symValue_weight hsym, hweight_pad, mem_weightLayer.1 hy₂,
        Nat.sub_add_cancel (by omega : a ≤ k + 1)]
    exact hjump (h1.symm.trans ((hconst y₁ y₂).trans h2))
  have hm1 : m + 1 = p := Nat.sub_add_cancel hp.one_le
  have hdeg_g : degree g = m :=
    degree_eq_of_isSymmetric_of_prime hgsym hgnc (hm1.symm ▸ hp)
  have hdeg_le : degree g ≤ degree f := by
    rw [degree_le_iff_mem_lowDegree]
    have hf : (fun x => bitVal ℝ (f x)) ∈ lowDegree ℝ (Fin N) (degree f) :=
      mem_lowDegree_totalDegree _
    refine comp_mem_lowDegree (fun i => ?_) hf
    simp only [pad]
    split_ifs with hi
    · exact bitVal_mem_lowDegree (⟨(i : ℕ), hi⟩ : Fin m)
    · exact const_mem_lowDegree 1 _
  omega

/-- Every non-constant symmetric Boolean function `f` on `{0, 1}^N` satisfies
`(N + 1) / 2 ≤ degree f`. -/
public theorem degree_ge_half_of_isSymmetric {N : ℕ} {f : BooleanFunction N}
    (hsym : f.IsSymmetric) (hnc : ¬∀ x y, f x = f y) :
    (N + 1) / 2 ≤ degree f := by
  obtain ⟨k, hkN, -⟩ := exists_jump_of_isSymmetric hsym hnc
  obtain ⟨p, hp, hlo, hhi⟩ := Nat.exists_prime_lt_and_le_two_mul ((N + 1) / 2) (by omega)
  have hpN : p ≤ N + 1 := by omega
  have hdeg := prime_sub_one_le_degree_of_isSymmetric hsym hnc hp hpN
  omega

end CslibFrontier.Computability.QueryComplexity
