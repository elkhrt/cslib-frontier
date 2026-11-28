module

public import CslibFrontier.Computability.Circuit.Boolean.Oracle.HardnessAmplification
public import CslibFrontier.Computability.Complexity.Classes.EXP
public import CslibFrontier.Computability.Complexity.Classes.PH.Reduction
public import CslibFrontier.Computability.Complexity.Classes.Space
public import CslibFrontier.Computability.Complexity.Reduction
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime
public import CslibFrontier.Crypto.Primitives.PRG.NisanWigderson

import CslibFrontier.Computability.Circuit.Boolean.Lookup
import CslibFrontier.Computability.Circuit.Boolean.PPoly
import CslibFrontier.Computability.Circuit.Boolean.PolynomialTime
import CslibFrontier.Computability.Circuit.Boolean.Substitution
import CslibFrontier.Computability.Circuit.Complexity
import CslibFrontier.Computability.Complexity.Classes.BPP.Derandomization.Generator
import CslibFrontier.Computability.Complexity.HardnessEncoding.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log
import CslibFrontier.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial.Automation
import CslibFrontier.Crypto.Primitives.PRG.NisanWigderson.Derandomization
import CslibFrontier.Crypto.Primitives.PRG.NisanWigderson.Sampling
import CslibFrontier.Foundations.Data.BitString.WordCount
import CslibFrontier.Foundations.Data.Nat.PolynomialBound.Log
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Relativized Impagliazzo–Wigderson PRG and Oracle Circuits from Reductions

This module constructs a relativized Nisan–Wigderson pseudorandom generator fooling
polynomial-size `A`-oracle circuits from exponential worst-case `A`-oracle hardness in `E`
(Klivans–van Melkebeek), and proves that any language polynomial-time many-one reducible to `A`
(including `PSPACE` for `PSPACE`-complete `A` and `Π₃ᵖ` for `Σ₃ᵖ`-complete `A`) has
polynomial-size `A`-oracle circuits.

## Main results

* `abs_card_div_sub_card_div_lt_oracle`: Nisan–Wigderson fooling bound against `A`-oracle circuits.
* `exists_oraclePRG_of_hard`: explicit polynomial-time pseudorandom generator against
  polynomial-size `A`-oracle circuits from exponential worst-case `A`-oracle hardness in `E`.
* `polynomiallyBounded_oracleComplexity_of_polyTimeReducible`,
  `polynomiallyBounded_oracleComplexity_of_mem_PSPACE`,
  `polynomiallyBounded_oracleComplexity_of_mem_PiP3`:
  polynomial-size `A`-oracle circuits for languages reducing to `A` or its complement.
-/

public section

namespace CslibFrontier.Computability.Complexity.OraclePRG

open CslibFrontier.Computability.Circuit.Boolean.Oracle
open Cslib Cslib.BitString Cslib.Circuits Cslib.Circuits.Boolean Cslib.Complexity
open Cslib.Crypto.PRG Cslib.Crypto.PRG.NisanWigderson Cslib.HardnessEncoding
open Filter Finset _root_.Turing.MultiTapeTM

local instance instIsCompleteOracle' (A : Language Bool) :
    (oracleInterpretation A).IsComplete :=
  isComplete_oracleInterpretation A

/-! ### Part 1: Relativized Nisan–Wigderson & Klivans–van Melkebeek PRG -/

private theorem oracleComplexity_nextBitGuess_le (A : Language Bool) {n m : ℕ}
    (test : BooleanFunction m) (i : Fin m) (r : Bool) (u : Fin m → Bool)
    (bit : Fin i → BooleanFunction n) {B : ℕ} (hB : 1 ≤ B)
    (hbit : ∀ j, complexity (oracleInterpretation A) (single (bit j)) ≤ B) :
    complexity (oracleInterpretation A)
        (single fun x => nextBitGuess test i r u fun j => bit j x) ≤
      complexity (oracleInterpretation A) (single test) + m * B + 1 := by
  let q : Fin m → BooleanFunction n := fun j x =>
    if h : (j : ℕ) < i then bit ⟨j, h⟩ x else if j = i then r else u j
  have hq (j : Fin m) : complexity (oracleInterpretation A) (single (q j)) ≤ B := by
    by_cases h : (j : ℕ) < i
    · simpa only [q, dite_eq_left h] using hbit ⟨j, h⟩
    · simp only [q, dite_eq_right h]
      exact (oracleComplexity_const_le A _).trans hB
  have htest : complexity (oracleInterpretation A) (single fun x => test fun j => q j x) ≤
      complexity (oracleInterpretation A) (single test) + m * B := by
    calc _ ≤ complexity (oracleInterpretation A) (fun x j => q j x) +
          complexity (oracleInterpretation A) (single test) :=
            complexity_comp_le (I := oracleInterpretation A) _ (single test)
      _ ≤ m * B + complexity (oracleInterpretation A) (single test) := by
          gcongr
          refine (complexity_pi_le (I := oracleInterpretation A) q).trans ?_
          calc _ ≤ ∑ _j : Fin m, B := sum_le_sum fun j _ => hq j
            _ = m * B := by simp
      _ = _ := add_comm _ _
  cases r
  · have e : (fun x => nextBitGuess test i false u fun j => bit j x) =
        fun x => !test fun j => q j x := funext fun x => by
      simp only [nextBitGuess, q]; cases test _ <;> rfl
    rw [e]
    exact (oracleComplexity_not_le A _).trans (Nat.add_le_add_right htest 1)
  · have e : (fun x => nextBitGuess test i true u fun j => bit j x) =
        fun x => test fun j => q j x := funext fun x => by
      simp only [nextBitGuess, q]; cases test _ <;> rfl
    rw [e]
    exact htest.trans (Nat.le_succ _)

private theorem exists_oracleComplexity_le_half_add_div_le_card_eq (A : Language Bool)
    {ℓ n a m : ℕ} (D : Design ℓ n a m) (f : BooleanFunction n) (test : BooleanFunction m)
    (hm : 0 < m) {ε : ℝ}
    (hε : ε ≤ ((generator D f).realExperiment (fun y => PMF.pure (test y)) true).toReal -
      (Generator.idealExperiment (fun y => PMF.pure (test y)) true).toReal) :
    ∃ g : BooleanFunction n,
      complexity (oracleInterpretation A) (single g) ≤
        complexity (oracleInterpretation A) (single test) + m * (2 ^ a * (2 * a + 3) + 1) + 1 ∧
      1 / 2 + ε / m ≤ (#{x | g x = f x} : ℝ) / 2 ^ n := by
  obtain ⟨i, s, bit, r, u, hs, hbit, h⟩ :=
    exists_dependsOn_half_add_div_le_card_nextBitGuess_eq D f test hm hε
  refine ⟨_, oracleComplexity_nextBitGuess_le A test i r u bit (Nat.le_add_left 1 _) fun j => ?_, h⟩
  refine ((oracleComplexity_le_deMorgan A _).trans (complexity_le_of_dependsOn (hbit j))).trans ?_
  have := hs j
  gcongr

private theorem toReal_realExperiment_sub_toReal_idealExperiment_lt_oracle (A : Language Bool)
    {ℓ n a m : ℕ} (D : Design ℓ n a m) (f : BooleanFunction n) (hm : 0 < m) {ε : ℝ} {S : ℕ}
    (hf : ∀ g : BooleanFunction n,
      complexity (oracleInterpretation A) (single g) ≤ S + m * (2 ^ a * (2 * a + 3) + 1) + 1 →
        (#{x | g x = f x} : ℝ) / 2 ^ n < 1 / 2 + ε / m)
    (test : BooleanFunction m) (htest : complexity (oracleInterpretation A) (single test) ≤ S) :
    ((generator D f).realExperiment (fun y => PMF.pure (test y)) true).toReal -
      (Generator.idealExperiment (fun y => PMF.pure (test y)) true).toReal < ε := by
  by_contra hlt
  obtain ⟨g, hg, hfg⟩ :=
    exists_oracleComplexity_le_half_add_div_le_card_eq A D f test hm (not_lt.1 hlt)
  exact (hf g (by omega)).not_ge hfg

private theorem card_not_div' {X : Type*} [Fintype X] [Nonempty X] (p : X → Bool) :
    (#{x | (!p x) = true} : ℝ) / Fintype.card X =
      1 - (#{x | p x = true} : ℝ) / Fintype.card X := by
  have hpos : (0 : ℝ) < Fintype.card X := mod_cast Fintype.card_pos
  have hsum : #{x | p x = true} + #{x | (!p x) = true} = Fintype.card X := by
    simpa using card_filter_add_card_filter_not (s := univ) (fun x => p x = true)
  rw [eq_sub_iff_add_eq, ← add_div, div_eq_one_iff_eq hpos.ne']
  exact_mod_cast (add_comm _ _).trans hsum

/-- **Relativized Nisan–Wigderson fooling bound for `A`-oracle circuits.** -/
theorem abs_card_div_sub_card_div_lt_oracle (A : Language Bool) {ℓ n a m : ℕ}
    (D : Design ℓ n a m) {f : BooleanFunction n} {s S : ℕ} {ε : ℝ}
    (hf : IsOracleAverageCaseHard A f s)
    (hs : S + 1 + m * (2 ^ a * (2 * a + 3) + 1) + 1 ≤ s) (hm : (m : ℝ) < ε * s)
    (test : BooleanFunction m) (htest : complexity (oracleInterpretation A) (single test) ≤ S) :
    |(#{z | test (generator D f z) = true} : ℝ) / 2 ^ ℓ - #{r | test r = true} / 2 ^ m| < ε := by
  have hs0 : (0 : ℝ) < s := Nat.cast_pos.2
    (Nat.pos_of_ne_zero fun h => (Nat.cast_nonneg m).not_gt (hm.trans_eq (by simp [h])))
  have hε : 0 < ε := pos_of_mul_pos_left ((Nat.cast_nonneg m).trans_lt hm) hs0.le
  rcases Nat.eq_zero_or_pos m with rfl | hm0
  · have hr (r : Fin 0 → Bool) : test r = test Fin.elim0 := congrArg test (Subsingleton.elim _ _)
    rcases hb : test Fin.elim0 with _ | _ <;> simp [hr, hb, hε]
  have hslack : 1 / (s : ℝ) < ε / m := by
    rw [div_lt_div_iff₀ hs0 (by exact_mod_cast hm0)]; linarith
  have hhard (S' : ℕ) (hS' : S' ≤ S + 1) (g : BooleanFunction n)
      (hg : complexity (oracleInterpretation A) (single g) ≤
        S' + m * (2 ^ a * (2 * a + 3) + 1) + 1) :
      (#{x | g x = f x} : ℝ) / 2 ^ n < 1 / 2 + ε / m :=
    hf.div_lt hslack (hg.trans (by omega))
  have h₁ := toReal_realExperiment_sub_toReal_idealExperiment_lt_oracle A D f hm0
    (hhard S (by omega)) test htest
  have h₂ := toReal_realExperiment_sub_toReal_idealExperiment_lt_oracle A D f hm0
    (hhard (S + 1) le_rfl) (fun r => !test r) ((oracleComplexity_not_le A test).trans (by omega))
  simp only [Generator.toReal_realExperiment_pure, Generator.toReal_idealExperiment_pure,
    nnratCast_dens, card_not_div' (fun z => test (generator D f z)), card_not_div' test] at h₁ h₂
  simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool, Nat.cast_pow,
    Nat.cast_ofNat] at h₁ h₂
  exact abs_sub_lt_iff.2 ⟨by linarith, by linarith⟩

private theorem nw_oracle_design_and_size_bounds {c m S τ Nδ : ℕ} (hc : 0 < c) (hτ3 : 3 ≤ τ)
    (hNδ : 1 ≤ Nδ) (hBτ : 8 * (m + S + Nδ + 5) ≤ 2 ^ τ) :
    m ≤ (greedyMasks ((2 ^ (8 * c + 1) + 1) * τ) (c * (4 * τ)) (τ - 1)).length ∧
    S + 1 + m * (2 ^ (τ - 1) * (2 * (τ - 1) + 3) + 1) + 1 ≤ 2 ^ (4 * τ) ∧
    (Nδ : ℝ) * (m : ℝ) < ((2 ^ (4 * τ) : ℕ) : ℝ) := by
  set b := 2 ^ (8 * c + 1) with hb
  set P := 2 ^ τ with hP
  have hP8 : 8 ≤ P := (Nat.pow_le_pow_right two_pos hτ3).trans_eq' rfl
  have hc4 : c * 4 ≤ b + 1 := by
    have h₁ : c < 2 ^ c := Nat.lt_two_pow_self
    have h₂ : 2 ^ c * 4 ≤ b := by
      rw [hb, show 2 ^ c * 4 = 2 ^ (c + 2) by rw [pow_add]; rfl]
      exact Nat.pow_le_pow_right two_pos (by omega)
    omega
  have hlen : m ≤ (greedyMasks ((b + 1) * τ) (c * (4 * τ)) (τ - 1)).length := by
    refine le_length_greedyMasks (by omega) (by nlinarith) (by nlinarith) ?_
    calc 4 ^ (c * (4 * τ)) * m ≤ 4 ^ (c * (4 * τ)) * P := Nat.mul_le_mul_left _ (by omega)
      _ = b ^ τ := by
        rw [hb, hP, ← pow_mul, show (4 : ℕ) = 2 ^ 2 by rfl, ← pow_mul, ← pow_add]; ring_nf
  have hY : 2 ^ (τ - 1) * (2 * (τ - 1) + 3) + 1 ≤ P ^ 2 := by
    have hQ : 2 ^ (τ - 1) * 2 = P := by rw [hP, ← pow_succ, Nat.sub_add_cancel (by omega)]
    have := Nat.lt_two_pow_self (n := τ - 1); have := @Nat.one_le_two_pow (τ - 1)
    rw [← hQ]; nlinarith
  have h₂ : 8 * (m * P ^ 2) ≤ P ^ 3 :=
    calc 8 * (m * P ^ 2) = 8 * m * P ^ 2 := by ring
      _ ≤ P * P ^ 2 := Nat.mul_le_mul_right _ (by omega)
      _ = P ^ 3 := by ring
  have h₃ : 8 * P ^ 3 ≤ P ^ 4 := by
    rw [pow_succ P 3, mul_comm (P ^ 3)]; exact Nat.mul_le_mul_right _ hP8
  have h₄ : P ≤ P ^ 4 := Nat.le_self_pow (by norm_num) P
  have h₁ := Nat.mul_le_mul_left m hY
  have hNm : Nδ * m < 2 ^ (4 * τ) := by
    have hN : Nδ ≤ P := by omega
    have hmP : m ≤ P := by omega
    have hP2 : P * P ≤ P ^ 3 := by
      have : P * P * 1 ≤ P * P * P := Nat.mul_le_mul_left _ (by omega)
      nlinarith
    have : Nδ * m ≤ P * P := Nat.mul_le_mul hN hmP
    rw [mul_comm 4 τ, pow_mul, ← hP]
    omega
  refine ⟨hlen, by rw [mul_comm 4 τ, pow_mul, ← hP]; omega, by exact_mod_cast hNm⟩

/-- **Klivans–van Melkebeek relativized Impagliazzo–Wigderson PRG.**
If some language `L ∈ E` requires `A`-oracle circuits of size `2^(γ n)` for all sufficiently large
`n`, then for every polynomial circuit size bound `C * (m + 1)^d` and every `δ > 0`, there is a
constant `cSeed` and a polynomial-time generator `H : ℕ → List Bool → List Bool` stretching seeds
of length `cSeed * (Nat.log 2 m + 1)` to `m` bits that fools every `A`-oracle circuit of size
`≤ C * (m + 1)^d` within `δ`, for every `m ≥ 1`. -/
theorem exists_oraclePRG_of_hard (A : Language Bool) {L : Language Bool}
    (hL : (L : Set (List Bool)) ∈ E encBits) {γ : ℝ} (hγ : 0 < γ)
    (hHard : ∀ᶠ n : ℕ in atTop,
      (2 : ℝ) ^ (γ * (n : ℝ)) ≤ (oracleCircuitComplexity A L n : ℝ))
    (C d : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (cSeed : ℕ) (H : ℕ → List Bool → List Bool),
      ComputableInPolyTime (fun p : ℕ × List Bool => H p.1 p.2)
        (encPair encUnary encBits) encBits ∧
      (∀ m s, (H m s).length = m) ∧
      ∀ m ≥ 1, ∀ test : BooleanFunction m,
        complexity (oracleInterpretation A) (single test) ≤ C * (m + 1) ^ d →
        |((#{σ : BitString (cSeed * (Nat.log 2 m + 1)) |
            test (fun i => (H m (List.ofFn σ)).getD i.1 false) = true} : ℝ) /
            (2 : ℝ) ^ (cSeed * (Nat.log 2 m + 1))) -
          ((#{y : BitString m | test y = true} : ℝ) / (2 : ℝ) ^ m)| < δ := by
  have hHard' : ∀ᶠ n : ℕ in atTop,
      (2 : ℝ) ^ (γ * n) ≤ complexity (oracleInterpretation A) (single (L.slice n)) := by
    filter_upwards [hHard] with n hn
    rwa [oracleCircuitComplexity_eq] at hn
  set M := blockFactor γ
  set c := hardnessDivisor γ
  have hc : 0 < c := by dsimp [c, hardnessDivisor]; positivity
  set Lenc : Language Bool := encodedLanguage L M
  have hLencE : (Lenc : Set (List Bool)) ∈ E encBits := encodedLanguage_mem_E hL M
  have hAvg : ∀ᶠ n : ℕ in atTop, IsOracleAverageCaseHard A (Lenc.slice n) (2 ^ (n / c)) := by
    simpa only [Lenc, slice_encodedLanguage] using
      eventually_isOracleAverageCaseHard_encodedSlice hγ hHard'
  obtain ⟨kE, hkE⟩ := mem_E_iff.1 hLencE
  obtain ⟨g, hgL, hg⟩ := exists_computableInO_of_mem_DTIME hkE
  have hslice (n : ℕ) : (fun y : Fin n → Bool => g (List.ofFn y)) = Lenc.slice n := by
    funext y; rw [Bool.eq_iff_iff, Language.slice_eq_true_iff, ← hgL]; rfl
  set Nδ : ℕ := ⌈1 / δ⌉₊ + 1
  have hNδ1 : 1 ≤ Nδ := Nat.le_add_left 1 _
  have hNδ_inv : 1 / (Nδ : ℝ) < δ := by
    rw [div_lt_iff₀ (by positivity)]
    have h1 : 1 / δ < (Nδ : ℝ) := by
      dsimp [Nδ]; push_cast
      linarith [Nat.le_ceil (1 / δ)]
    have h2 := (div_lt_iff₀ hδ).mp h1
    linarith
  set B : ℕ → ℕ := fun m => m + C * (m + 1) ^ d + Nδ + 5
  have hBpoly : PolynomiallyBounded B := by dsimp [B]; fun_prop
  obtain ⟨e, he⟩ := hBpoly.exists_clog_le_mul_log
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 hAvg
  set t : ℕ → ℕ := fun m => n₀ + 3 + e * (Nat.log 2 m + 1)
  set b : ℕ := 2 ^ (8 * c + 1)
  set cSeed : ℕ := (b + 1) * (n₀ + 3 + e)
  let seedLen : ℕ → ℕ := fun m => (b + 1) * t m
  let blockLen : ℕ → ℕ := fun m => c * (4 * t m)
  let overlapLen : ℕ → ℕ := fun m => t m - 1
  let H : ℕ → List Bool → List Bool := fun m s =>
    listGenerator g (blockLen m) ((greedyMasks (seedLen m) (blockLen m) (overlapLen m)).take m) s
  have hH_poly : ComputableInPolyTime (fun p : ℕ × List Bool => H p.1 p.2)
      (encPair encUnary encBits) encBits := by
    have hlog2 : ComputableInPolyTime (fun m : ℕ => Nat.log 2 m) encUnary encUnary :=
      ComputableInPolyTime.unary_log_two
    have ht_poly : ComputableInPolyTime t encUnary encUnary := by dsimp [t]; fun_prop
    have hseed_poly : ComputableInPolyTime seedLen encUnary encUnary := by
      dsimp [seedLen]; fun_prop
    have hblock_poly : ComputableInPolyTime blockLen encUnary encUnary := by
      dsimp [blockLen]; fun_prop
    have hoverlap_poly : ComputableInPolyTime overlapLen encUnary encUnary := by
      dsimp [overlapLen]; fun_prop
    have hseedBudget : PolyBounded (fun m : ℕ => (encUnary m).length) (fun m => 2 ^ seedLen m) := by
      have h1 : PolyBounded (fun m : ℕ => (encUnary m).length)
          (fun m => 2 ^ ((b + 1) * (n₀ + 3 + e * (Nat.log 2 (encUnary m).length + 1)))) := by
        growth_poly
      exact h1.mono fun m => by simp [seedLen, t, encUnary_apply]
    have hblockBudget : PolyBounded (fun m : ℕ => (encUnary m).length)
        (fun m => 2 ^ (kE * blockLen m)) := by
      have h1 : PolyBounded (fun m : ℕ => (encUnary m).length)
          (fun m =>
            2 ^ (kE * (c * (4 * (n₀ + 3 + e * (Nat.log 2 (encUnary m).length + 1)))))) := by
        growth_poly
      exact h1.mono fun m => by simp [blockLen, t, encUnary_apply]
    exact computableInPolyTime_listGenerator_greedyMasks
      (fun _ _ h => Nat.pow_le_pow_right two_pos (Nat.mul_le_mul_left kE h))
      hg hseed_poly hblock_poly hoverlap_poly ComputableInPolyTime.id'
      hseedBudget hblockBudget
  have hBτ_all (m : ℕ) : 8 * B m ≤ 2 ^ (t m) := by
    dsimp [t]
    rw [pow_add]
    exact Nat.mul_le_mul
      (by rw [pow_add]; exact Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _))
      ((Nat.le_pow_clog one_lt_two _).trans (Nat.pow_le_pow_right two_pos (he m)))
  have hbounds (m : ℕ) :=
    nw_oracle_design_and_size_bounds (c := c) (m := m) (S := C * (m + 1) ^ d)
      (τ := t m) (Nδ := Nδ) hc (by dsimp [t]; omega) hNδ1 (hBτ_all m)
  have hH_len : ∀ m s, (H m s).length = m := by
    intro m s
    simp only [H, listGenerator, List.length_map, List.length_take]
    exact min_eq_left (hbounds m).1
  refine ⟨cSeed, H, hH_poly, hH_len, fun m hm test htest => ?_⟩
  have hseed_le : seedLen m ≤ cSeed * (Nat.log 2 m + 1) := by
    dsimp [seedLen, cSeed, t]
    have h1 : (b + 1) * (n₀ + 3) ≤ (b + 1) * (n₀ + 3) * (Nat.log 2 m + 1) :=
      Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
    linarith
  have hprefix :
      (#{σ : BitString (cSeed * (Nat.log 2 m + 1)) |
          test (fun i => (H m (List.ofFn σ)).getD i.1 false) = true} : ℝ) /
          (2 : ℝ) ^ (cSeed * (Nat.log 2 m + 1)) =
      (#{z : BitString (seedLen m) |
          test (fun i => (H m (List.ofFn z)).getD i.1 false) = true} : ℝ) /
          (2 : ℝ) ^ (seedLen m) := by
    have hH_take (w : List Bool) : H m w = H m (w.take (seedLen m)) := by
      dsimp only [H, listGenerator]
      refine List.map_congr_left fun mask hmask => ?_
      have hmask_len : mask.length = seedLen m :=
        length_of_mem_greedyMasks (List.mem_of_mem_take hmask)
      have hrm : restrictMask mask w = restrictMask mask (w.take (seedLen m)) := by
        unfold restrictMask
        refine List.map_congr_left fun idx hidx => ?_
        have hlt : idx < seedLen m := by
          have h1 := List.mem_range.mp (List.mem_of_mem_filter hidx)
          omega
        simp [List.getD_eq_getElem?_getD, hlt]
      rw [hrm]
    have hcard := BitString.card_filter_take hseed_le
      (fun w => test (fun i => (H m w).getD i.1 false) = true)
    have heq1 :
        #{σ : BitString (cSeed * (Nat.log 2 m + 1)) |
            test (fun i => (H m (List.ofFn σ)).getD i.1 false) = true} =
        #{σ : BitString (cSeed * (Nat.log 2 m + 1)) |
            test (fun i => (H m ((List.ofFn σ).take (seedLen m))).getD i.1 false) = true} :=
      congrArg Finset.card (filter_congr fun σ _ => by rw [← hH_take])
    rw [heq1, hcard, ← pow_sub_mul_pow 2 hseed_le]
    have hpos : ((2 : ℝ) ^ (cSeed * (Nat.log 2 m + 1) - seedLen m)) ≠ 0 := by positivity
    push_cast
    rw [mul_div_mul_left _ _ hpos]
  rw [hprefix]
  obtain ⟨hlen, hsz, hNm⟩ := hbounds m
  have hhard : IsOracleAverageCaseHard A (Lenc.slice (blockLen m)) (2 ^ (4 * t m)) := by
    have hbn : n₀ ≤ blockLen m := by
      calc n₀ ≤ 1 * (4 * t m) := by dsimp [t]; omega
        _ ≤ c * (4 * t m) := Nat.mul_le_mul_right _ hc
    have h := hn₀ (blockLen m) hbn
    rwa [show blockLen m / c = 4 * t m by dsimp [blockLen]; exact Nat.mul_div_cancel_left _ hc] at h
  have hεm : (m : ℝ) < δ * ((2 ^ (4 * t m) : ℕ) : ℝ) := by
    have h1 : (m : ℝ) < (1 / (Nδ : ℝ)) * ((2 ^ (4 * t m) : ℕ) : ℝ) := by
      rw [one_div_mul_eq_div, lt_div_iff₀ (by positivity), mul_comm]
      exact hNm
    have h2 : (1 / (Nδ : ℝ)) * ((2 ^ (4 * t m) : ℕ) : ℝ) ≤ δ * ((2 ^ (4 * t m) : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_right hNδ_inv.le (by positivity)
    linarith
  have hgap := abs_card_div_sub_card_div_lt_oracle A
    (Design.greedy (seedLen m) (blockLen m) (overlapLen m) m hlen) hhard hsz hεm test htest
  have hseeds :
      #{z : BitString (seedLen m) | test (fun i => (H m (List.ofFn z)).getD i.1 false) = true} =
      #{z : BitString (seedLen m) |
        test (generator (Design.greedy (seedLen m) (blockLen m) (overlapLen m) m hlen)
          (Lenc.slice (blockLen m)) z) = true} := by
    refine congrArg _ (filter_congr fun z _ => ?_)
    have hlg := listGenerator_take_greedyMasks (ℓ := seedLen m) (n := blockLen m)
      (a := overlapLen m) (m := m) hlen g z
    rw [show H m (List.ofFn z) = List.ofFn (generator
      (Design.greedy (seedLen m) (blockLen m) (overlapLen m) m hlen)
      (Lenc.slice (blockLen m)) z) by rw [← hslice]; exact hlg]
    have hfn : (fun i : Fin m => (List.ofFn (generator
        (Design.greedy (seedLen m) (blockLen m) (overlapLen m) m hlen)
        (Lenc.slice (blockLen m)) z)).getD i.1 false) =
        generator (Design.greedy (seedLen m) (blockLen m) (overlapLen m) m hlen)
          (Lenc.slice (blockLen m)) z := by
      funext i
      simp [List.getD_eq_getElem?_getD]
    rw [hfn]
  rw [hseeds]
  exact hgap

/-! ### Part 2: Polynomial-Size Oracle Circuits from Polynomial-Time Reductions -/

/-- Any language `L` polynomial-time many-one reducible to `A` has polynomial-size `A`-oracle
circuits. -/
theorem polynomiallyBounded_oracleComplexity_of_polyTimeReducible
    {L A : Language Bool} (hred : PolyTimeReducible encBits encBits (L : Set (List Bool)) A) :
    PolynomiallyBounded fun n =>
      complexity (oracleInterpretation A) (single (L.slice n)) := by
  obtain ⟨f, hf, hLA⟩ := hred
  obtain ⟨q, hq⟩ := hf.polyBounded_length.exists_polynomial
  have hlenEq_pt : ComputableInPolyTime
      (fun p : ℕ × List Bool => decide ((f p.2).length = p.1))
      (encPair encUnary encBits) encBool := by
    have h1 := ComputableInPolyTime.length_bits_comp
      (hf.comp (ComputableInPolyTime.snd encUnary encBits))
    have h2 := ComputableInPolyTime.fst encUnary encBits
    fun_prop
  have hbitAt_pt : ComputableInPolyTime
      (fun p : ℕ × List Bool => (f p.2).getD p.1 false)
      (encPair encUnary encBits) encBool :=
    ComputableInPolyTime.bitsGetDWithInput
      (hf.comp (ComputableInPolyTime.snd encUnary encBits))
      (ComputableInPolyTime.fst encUnary encBits) false
  obtain ⟨Llen, hLlen, hLlen_iff⟩ := PPoly.exists_of_polyTime hlenEq_pt
  obtain ⟨Lbit, hLbit, hLbit_iff⟩ := PPoly.exists_of_polyTime hbitAt_pt
  obtain ⟨c1, d1, hc1⟩ := polynomiallyBounded_iff_le.1 (mem_PPoly.1 hLlen)
  obtain ⟨c2, d2, hc2⟩ := polynomiallyBounded_iff_le.1 (mem_PPoly.1 hLbit)
  have hgLen_le (n r : ℕ) (hr : r ≤ q.eval n) :
      complexity (oracleInterpretation A)
        (single fun x : BitString n => decide ((f (List.ofFn x)).length = r)) ≤
        c1 * (2 * q.eval n + 1 + n + 1) ^ d1 + 2 := by
    have h1 := complexity_le_of_append_take Llen (frame (encUnary r)) (P := n) (Q := n) le_rfl
      (f := fun x : BitString n => decide ((f (List.ofFn x)).length = r)) fun x => by
        rw [List.take_of_length_le (by simp)]
        have h := hLlen_iff (r, List.ofFn x)
        simpa [encPair_apply, encBits_apply] using h
    have h2 : complexity (oracleInterpretation A)
        (single fun x : BitString n => decide ((f (List.ofFn x)).length = r)) ≤
        complexity interpretation (single (Llen.slice ((frame (encUnary r)).length + n))) + 2 :=
      (oracleComplexity_le_deMorgan A _).trans h1
    have hflen : (frame (encUnary r)).length + n = 2 * r + 1 + n := by
      simp [length_frame, encUnary_apply]
    rw [hflen] at h2
    have h3 := hc1 (2 * r + 1 + n)
    have h4 : (2 * r + 1 + n + 1) ^ d1 ≤ (2 * q.eval n + 1 + n + 1) ^ d1 :=
      Nat.pow_le_pow_left (by omega) d1
    have h5 := Nat.mul_le_mul_left c1 h4
    omega
  have hgBit_le (n j : ℕ) (hj : j ≤ q.eval n) :
      complexity (oracleInterpretation A)
        (single fun x : BitString n => (f (List.ofFn x)).getD j false) ≤
        c2 * (2 * q.eval n + 1 + n + 1) ^ d2 + 2 := by
    have h1 := complexity_le_of_append_take Lbit (frame (encUnary j)) (P := n) (Q := n) le_rfl
      (f := fun x : BitString n => (f (List.ofFn x)).getD j false) fun x => by
        rw [List.take_of_length_le (by simp)]
        have h := hLbit_iff (j, List.ofFn x)
        simpa [encPair_apply, encBits_apply] using h
    have h2 : complexity (oracleInterpretation A)
        (single fun x : BitString n => (f (List.ofFn x)).getD j false) ≤
        complexity interpretation (single (Lbit.slice ((frame (encUnary j)).length + n))) + 2 :=
      (oracleComplexity_le_deMorgan A _).trans h1
    have hflen : (frame (encUnary j)).length + n = 2 * j + 1 + n := by
      simp [length_frame, encUnary_apply]
    rw [hflen] at h2
    have h3 := hc2 (2 * j + 1 + n)
    have h4 : (2 * j + 1 + n + 1) ^ d2 ≤ (2 * q.eval n + 1 + n + 1) ^ d2 :=
      Nat.pow_le_pow_left (by omega) d2
    have h5 := Nat.mul_le_mul_left c2 h4
    omega
  let B1 (n : ℕ) : ℕ := c1 * (2 * q.eval n + 1 + n + 1) ^ d1 + 2
  let B2 (n : ℕ) : ℕ := c2 * (2 * q.eval n + 1 + n + 1) ^ d2 + 2
  let termBound (n : ℕ) : ℕ := B1 n + q.eval n * B2 n + 2
  have htotal (n : ℕ) :
      complexity (oracleInterpretation A) (single (L.slice n)) ≤
        (q.eval n + 1) * (termBound n + 1) + 1 := by
    let gLen (r : ℕ) : BooleanFunction n := fun x => decide ((f (List.ofFn x)).length = r)
    let gQuery (r : ℕ) : BooleanFunction n := fun x =>
      A.slice r (fun j : Fin r => (f (List.ofFn x)).getD j.1 false)
    let gTerm (r : ℕ) : BooleanFunction n := fun x => gLen r x && gQuery r x
    have hgQuery_le (r : ℕ) (hr : r ≤ q.eval n) :
        complexity (oracleInterpretation A) (single (gQuery r)) ≤ q.eval n * B2 n + 1 := by
      have hgate : complexity (oracleInterpretation A) (single (A.slice r)) ≤ 1 := by
        let cq : Circuit oracleSignature r 1 :=
          Circuit.oneGate (σ := oracleSignature) (.query r) id
        have hcomp : cq.Computes (oracleInterpretation A) (single (A.slice r)) := by
          intro y; funext j; fin_cases j
          simp [cq, Circuit.eval_oneGate]
        exact (complexity_le_of_computes cq hcomp).trans (by simp [cq])
      have hcomp := complexity_comp_le (I := oracleInterpretation A)
        (fun (x : BitString n) (j : Fin r) => (f (List.ofFn x)).getD j.1 false) (single (A.slice r))
      have hpi := complexity_pi_le (I := oracleInterpretation A)
        (fun (j : Fin r) (x : BitString n) => (f (List.ofFn x)).getD j.1 false)
      have hsum : ∑ j : Fin r, complexity (oracleInterpretation A)
          (single fun x : BitString n => (f (List.ofFn x)).getD j.1 false) ≤
          q.eval n * B2 n := by
        calc ∑ j : Fin r, _ ≤ ∑ _j : Fin r, B2 n :=
              Finset.sum_le_sum fun j _ => hgBit_le n j.1 (by omega)
          _ = r * B2 n := by simp
          _ ≤ q.eval n * B2 n := Nat.mul_le_mul_right _ hr
      have heq : (single (A.slice r)) ∘
          (fun (x : BitString n) (j : Fin r) => (f (List.ofFn x)).getD j.1 false) =
          single (gQuery r) := rfl
      rw [heq] at hcomp
      calc complexity (oracleInterpretation A) (single (gQuery r))
          ≤ complexity (oracleInterpretation A)
              (fun (x : BitString n) (j : Fin r) => (f (List.ofFn x)).getD j.1 false) +
            complexity (oracleInterpretation A) (single (A.slice r)) := hcomp
        _ ≤ (∑ j : Fin r, complexity (oracleInterpretation A)
              (single fun x : BitString n => (f (List.ofFn x)).getD j.1 false)) + 1 :=
            Nat.add_le_add hpi hgate
        _ ≤ q.eval n * B2 n + 1 := Nat.add_le_add_right hsum 1
    have hgTerm_le (r : ℕ) (hr : r ≤ q.eval n) :
        complexity (oracleInterpretation A) (single (gTerm r)) ≤ termBound n := by
      have h1 := oracleComplexity_and_le A (gLen r) (gQuery r)
      have h2 : complexity (oracleInterpretation A) (single (gLen r)) ≤ B1 n := hgLen_le n r hr
      have h3 : complexity (oracleInterpretation A) (single (gQuery r)) ≤ q.eval n * B2 n + 1 :=
        hgQuery_le r hr
      calc complexity (oracleInterpretation A) (single (gTerm r))
          ≤ complexity (oracleInterpretation A) (single (gLen r)) +
            complexity (oracleInterpretation A) (single (gQuery r)) + 1 := h1
        _ ≤ B1 n + (q.eval n * B2 n + 1) + 1 :=
            Nat.add_le_add_right (Nat.add_le_add h2 h3) 1
        _ = termBound n := by dsimp [termBound]; omega
    let foldOr (k : ℕ) : BooleanFunction n := fun x =>
      (List.range k).foldr (fun r acc => gTerm r x || acc) false
    have hfold_le : ∀ k ≤ q.eval n + 1,
        complexity (oracleInterpretation A) (single (foldOr k)) ≤
          k * (termBound n + 1) + 1 := by
      intro k hk
      induction k with
      | zero =>
        simpa [foldOr] using oracleComplexity_const_le A (n := n) false
      | succ k ih =>
        have hstep : foldOr (k + 1) = fun x => foldOr k x || gTerm k x := by
          funext x
          simp only [foldOr, List.range_succ, List.foldr_append, List.foldr_cons, List.foldr_nil,
            Bool.or_false]
          clear hk ih
          induction (List.range k) with
          | nil => simp
          | cons a l ihl => simp [ihl, Bool.or_assoc]
        rw [hstep]
        have h1 := oracleComplexity_or_le A (foldOr k) (gTerm k)
        have h2 := ih (by omega)
        have h3 := hgTerm_le k (by omega)
        nlinarith
    have hslice_eq : L.slice n = foldOr (q.eval n + 1) := by
      funext x
      rw [Bool.eq_iff_iff, Language.slice_eq_true_iff]
      have hfold_iff : ∀ k, foldOr k x = true ↔ ∃ r < k, gTerm r x = true := by
        intro k
        induction k with
        | zero => simp [foldOr]
        | succ k ih =>
          have hstep : foldOr (k + 1) x = (foldOr k x || gTerm k x) := by
            simp only [foldOr, List.range_succ, List.foldr_append, List.foldr_cons, List.foldr_nil,
              Bool.or_false]
            induction (List.range k) with
            | nil => simp
            | cons a l ihl => simp [ihl, Bool.or_assoc]
          rw [hstep, Bool.or_eq_true, ih]
          constructor
          · rintro (⟨r, hr, htr⟩ | hk)
            · exact ⟨r, by omega, htr⟩
            · exact ⟨k, by omega, hk⟩
          · rintro ⟨r, hr, htr⟩
            rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hr) with hlt | rfl
            · exact Or.inl ⟨r, hlt, htr⟩
            · exact Or.inr htr
      rw [hfold_iff]
      refine (hLA (List.ofFn x)).trans ?_
      constructor
      · intro hfx
        refine ⟨(f (List.ofFn x)).length, by
          have := hq (List.ofFn x); simp at this; omega, ?_⟩
        simp only [gTerm, gLen, gQuery, Bool.and_eq_true, decide_eq_true_eq, true_and,
          Language.slice_eq_true_iff]
        have hof : List.ofFn (fun j : Fin (f (List.ofFn x)).length =>
            (f (List.ofFn x)).getD j.1 false) = f (List.ofFn x) := by
          refine List.ext_getElem (by simp) fun i hi _ => ?_
          simp [List.getD_eq_getElem?_getD]
        rwa [hof]
      · rintro ⟨r, _, htr⟩
        simp only [gTerm, gLen, gQuery, Bool.and_eq_true, decide_eq_true_eq,
          Language.slice_eq_true_iff] at htr
        have hof : List.ofFn (fun j : Fin r => (f (List.ofFn x)).getD j.1 false) =
            f (List.ofFn x) := by
          refine List.ext_getElem (by simp [htr.1]) fun i hi _ => ?_
          have hi' : i < (f (List.ofFn x)).length := by omega
          simp [List.getD_eq_getElem?_getD, hi']
        rw [hof] at htr
        exact htr.2
    rw [hslice_eq]
    exact hfold_le (q.eval n + 1) le_rfl
  have hpoly : PolynomiallyBounded fun n => (q.eval n + 1) * (termBound n + 1) + 1 := by
    dsimp [termBound, B1, B2]; fun_prop
  exact hpoly.mono_of_le htotal

/-- Every language in `PSPACE` has polynomial-size `A`-oracle circuits for any `PSPACE`-complete
oracle `A`. -/
theorem polynomiallyBounded_oracleComplexity_of_mem_PSPACE {L A : Language Bool}
    (hA : PSPACEComplete encBits (A : Set (List Bool)))
    (hL : (L : Set (List Bool)) ∈ PSPACE encBits) :
    PolynomiallyBounded fun n =>
      complexity (oracleInterpretation A) (single (L.slice n)) :=
  polynomiallyBounded_oracleComplexity_of_polyTimeReducible (hA.2 encBits L hL)

/-- Every language in `Π₃ᵖ` has polynomial-size `A`-oracle circuits for any `Σ₃ᵖ`-complete
oracle `A`. -/
theorem polynomiallyBounded_oracleComplexity_of_mem_PiP3 {L A : Language Bool}
    (hA : SigmaPComplete 3 encBits (A : Set (List Bool)))
    (hL : (L : Set (List Bool)) ∈ PiP 3 encBits) :
    PolynomiallyBounded fun n =>
      complexity (oracleInterpretation A) (single (L.slice n)) := by
  have hLc : (Lᶜ : Set (List Bool)) ∈ SigmaP 3 encBits := compl_mem_SigmaP_of_mem_PiP hL
  have hpb := polynomiallyBounded_oracleComplexity_of_polyTimeReducible (L := Lᶜ) (A := A)
    (hA.2 encBits (Lᶜ : Set (List Bool)) hLc)
  refine (hpb.add (PolynomiallyBounded.const 1)).mono_of_le fun n => ?_
  have heq : L.slice n = fun x => !(Lᶜ : Language Bool).slice n x := funext fun x => by
    simp [Language.slice_compl]
  rw [heq]
  exact oracleComplexity_not_le A _


end CslibFrontier.Computability.Complexity.OraclePRG
