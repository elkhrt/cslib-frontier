module

public import CslibFrontier.Crypto.Computational.GoldreichLevin.HardCore
public import CslibFrontier.Crypto.Computational.OneWay
public import CslibFrontier.Crypto.Computational.PseudorandomGenerator
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import CslibFrontier.Crypto.Negligible.Basic
import CslibFrontier.Languages.Probabilistic.BitString
import CslibFrontier.Languages.Probabilistic.Norm
import CslibFrontier.Probability.BitString
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Map
import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.Tactic.PPT
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Pseudouniform Functions and Equivalence with Pseudorandom Generators

A length-preserving polynomial-time computable function `g` is *pseudouniform* if its output on a
uniform `n`-bit seed is computationally indistinguishable from the uniform distribution on `n`-bit
strings.

This module establishes the equivalence between pseudouniform one-way functions and pseudorandom
generators in the uniform Turing-machine model:
* Combining a pseudouniform one-way function with the Goldreich–Levin hard-core predicate yields a
  pseudorandom generator stretching `n` bits to `n + 1` bits (`prg_of_pseudouniform_oneWay`).
* Truncating any pseudorandom generator to its first `n` output bits yields a function that is both
  pseudouniform and one-way (`truncation_pseudouniform_and_oneWay`).

## Main definitions

* `CslibFrontier.Crypto.Computational.Pseudouniform`: length-preserving polynomial-time function
  whose output ensemble is computationally indistinguishable from uniform.
* `CslibFrontier.Crypto.Computational.truncPRG`: truncation of a bitstring function to the length
  of its input seed.

## Main results

* `CslibFrontier.Crypto.Computational.prg_of_pseudouniform_oneWay`: every pseudouniform one-way
  function yields a pseudorandom generator via the Goldreich–Levin construction.
* `CslibFrontier.Crypto.Computational.truncation_pseudouniform_and_oneWay`: truncating a
  pseudorandom generator to its input length produces a pseudouniform one-way function.
-/

public section

namespace CslibFrontier.Crypto.Computational

open Cslib Cslib.Crypto Cslib.BitString Cslib.Probability Turing.MultiTapeTM
open scoped NNReal

/-- A length-preserving polynomial-time computable function `g : List Bool → List Bool` is
pseudouniform if its output on a uniform `n`-bit seed is computationally indistinguishable from
the uniform distribution on `n`-bit strings. -/
structure Pseudouniform (g : List Bool → List Bool) : Prop where
  /-- Deterministic polynomial-time computability. -/
  polyTime : ComputableInPolyTime g encBits encBits
  /-- Length preservation `|g(v)| = |v|`. -/
  length_eq : ∀ v : List Bool, (g v).length = v.length
  /-- Computational indistinguishability from uniform. -/
  secure : ComputationallyIndistinguishable (generatorEnsemble g) BitString.uniformList

/-- Auxiliary distinguisher for the Goldreich–Levin reduction: given `u` of length `k`, samples `z`
of length `k + spare` and a fair bit `b`, and runs `adversary` on `u ++ z ++ [b]`. -/
private noncomputable def padDistinguisher (adversary : Distinguisher) (spare : ℕ) :
    Distinguisher :=
  fun k u => do
    let z ← BitString.sampleList (k + spare)
    let b ← BitString.sampleList 1
    adversary (2 * k + spare) (u ++ z ++ b)

@[program_certificate]
private theorem isPPT_padDistinguisher {adversary : Distinguisher}
    (ha : IsPPT encBool adversary) (spare : ℕ) :
    IsPPT encBool (padDistinguisher adversary spare) := by
  unfold padDistinguisher
  ppt

private theorem eval_distinguishing_padDistinguisher (g : List Bool → List Bool)
    (adversary : Distinguisher) (k spare : ℕ) (hspare : spare ≤ 1) :
    distinguishingGame (hardCoreIdeal (GoldreichLevin.paddedFunction g) (2 * k + spare))
        (adversary (2 * k + spare)) =
      distinguishingGame (generatorEnsemble g k) (padDistinguisher adversary spare k) ∧
    distinguishingGame (BitString.uniformList (2 * k + spare + 1))
        (adversary (2 * k + spare)) =
      distinguishingGame (BitString.uniformList k) (padDistinguisher adversary spare k) := by
  have hdiv : (2 * k + spare) / 2 = k := by omega
  have hsub : 2 * k + spare - k = k + spare := by omega
  have hbit : (BitString.uniformList 1) = (PMF.uniformOfFintype Bool).map (fun b => [b]) := by
    rw [BitString.uniformList_succ, BitString.uniformList_zero]
    simp [PMF.map, Function.comp_def]
  constructor
  · simp only [distinguishingGame_eq_bind, hardCoreIdeal, generatorEnsemble, padDistinguisher,
      ProbComp.eval_bind, BitString.eval_sampleList, hbit, PMF.monad_bind_eq_bind]
    rw [show 2 * k + spare = k + (k + spare) by omega, BitString.uniformList_add]
    simp only [PMF.bind_bind, PMF.bind_map, Function.comp_def]
    refine PMF.bind_congr_on_support _ _ _ fun v hv => ?_
    refine PMF.bind_congr_on_support _ _ _ fun z hz => ?_
    have hvl := BitString.length_of_mem_support_uniformList hv
    have hzl := BitString.length_of_mem_support_uniformList hz
    have hpad : GoldreichLevin.paddedFunction g (v ++ z) = g v ++ z := by
      simp only [GoldreichLevin.paddedFunction, List.length_append, hvl, hzl]
      rw [show (k + (k + spare)) / 2 = k by omega, List.take_left' hvl, List.drop_left' hvl]
    simp only [hpad]
  · simp only [distinguishingGame_eq_bind, padDistinguisher, ProbComp.eval_bind,
      BitString.eval_sampleList, hbit, PMF.monad_bind_eq_bind]
    rw [BitString.uniformList_snoc, show 2 * k + spare = k + (k + spare) by omega,
      BitString.uniformList_add]
    simp only [PMF.bind_bind, PMF.bind_map, Function.comp_def]

/-- If `g` is both pseudouniform and a one-way function, then the Goldreich–Levin construction
`h(v, z) = (g(v), z, ⊕_i v_i z_i)` (`GoldreichLevin.generator g`) is a pseudorandom generator
with one-bit stretch. -/
theorem prg_of_pseudouniform_oneWay {g : List Bool → List Bool}
    (hPU : Pseudouniform g) (hOW : OneWay g) :
    PseudorandomGenerator (GoldreichLevin.generator g) (fun n => n + 1) := by
  have hHC : HardCore (GoldreichLevin.paddedFunction g) GoldreichLevin.paddedPredicate :=
    GoldreichLevin.padded_hardCore hOW
  have h1 : ComputationallyIndistinguishable
      (generatorEnsemble (GoldreichLevin.generator g))
      (hardCoreIdeal (GoldreichLevin.paddedFunction g)) := hHC.indistinguishable
  have h2 : ComputationallyIndistinguishable
      (hardCoreIdeal (GoldreichLevin.paddedFunction g))
      (fun n => BitString.uniformList (n + 1)) := by
    intro adversary ha
    have hneg0 := hPU.secure (padDistinguisher adversary 0) (isPPT_padDistinguisher ha 0)
    have hneg1 := hPU.secure (padDistinguisher adversary 1) (isPPT_padDistinguisher ha 1)
    refine negligible_of_le ((hneg0.add hneg1).div_const two_pos) fun n => ?_
    obtain ⟨heqR, heqI⟩ :=
      eval_distinguishing_padDistinguisher g adversary (n / 2) (n % 2) (by omega)
    have hn : 2 * (n / 2) + n % 2 = n := by omega
    rw [hn] at heqR heqI
    dsimp only
    rw [heqR, heqI]
    rcases Nat.mod_two_eq_zero_or_one n with hmod | hmod
    · rw [hmod]
      exact le_add_of_nonneg_right zero_le
    · rw [hmod]
      exact le_add_of_nonneg_left zero_le
  have hpoly : ComputableInPolyTime (GoldreichLevin.generator g) encBits encBits := by
    unfold GoldreichLevin.generator
    have h1 := GoldreichLevin.polyTime_paddedFunction hPU.polyTime
    have h2 := GoldreichLevin.polyTime_paddedPredicate
    have h3 : ComputableInPolyTime (fun seed => [GoldreichLevin.paddedPredicate seed])
        encBits encBits :=
      ComputableInPolyTime.bitsCons h2 (ComputableInPolyTime.const [])
    exact ComputableInPolyTime.bitsAppend h1 h3
  have hlen : ∀ seed, (GoldreichLevin.generator g seed).length = seed.length + 1 := by
    intro seed
    simp [GoldreichLevin.generator, GoldreichLevin.paddedFunction_length hPU.length_eq]
  exact PseudorandomGenerator.of_indistinguishable hpoly hlen Nat.lt_succ_self (h1.trans h2)

/-- Truncation of a bitstring function `g` to the first `|v|` bits of its output. -/
def truncPRG (g : List Bool → List Bool) (v : List Bool) : List Bool :=
  (g v).take v.length

/-- Length preservation of `truncPRG` for an expanding generator. -/
theorem truncPRG_length {g : List Bool → List Bool} {length : ℕ → ℕ}
    (hlen : ∀ v, (g v).length = length v.length) (hstretch : ∀ n, n < length n)
    (v : List Bool) :
    (truncPRG g v).length = v.length := by
  simp only [truncPRG, List.length_take, hlen]
  exact Nat.min_eq_left (Nat.le_of_lt (hstretch v.length))

/-- Truncation is polynomial-time computable whenever `g` is. -/
theorem polyTime_truncPRG {g : List Bool → List Bool}
    (hg : ComputableInPolyTime g encBits encBits) :
    ComputableInPolyTime (truncPRG g) encBits encBits := by
  unfold truncPRG
  exact hg.bitsTakeWithInput ComputableInPolyTime.length_bits

/-- First distinguisher for the truncation one-wayness proof: runs inverter `A` on the first `n`
bits and checks whether `truncPRG g` maps the candidate back to those `n` bits. -/
private noncomputable def truncDistinguisher1 (g : List Bool → List Bool)
    (A : Inverter) : Distinguisher :=
  fun n w => do
    let cand ← A n (w.take n)
    return truncPRG g cand == w.take n

/-- Second distinguisher for the truncation one-wayness proof: runs inverter `A` on the first `n`
bits and checks whether the candidate has length `n` and its first `n + 1` output bits match `w`. -/
private noncomputable def truncDistinguisher2 (g : List Bool → List Bool)
    (A : Inverter) : Distinguisher :=
  fun n w => do
    let cand ← A n (w.take n)
    return decide (cand.length = n) && ((g cand).take (n + 1) == w.take (n + 1))

@[program_certificate]
private theorem isPPT_truncDistinguisher1 {g : List Bool → List Bool} {A : Inverter}
    (hg : ComputableInPolyTime g encBits encBits) (hA : IsPPT encBits A) :
    IsPPT encBool (truncDistinguisher1 g A) := by
  have htr : ComputableInPolyTime (truncPRG g) encBits encBits := polyTime_truncPRG hg
  unfold truncDistinguisher1
  ppt

@[program_certificate]
private theorem isPPT_truncDistinguisher2 {g : List Bool → List Bool} {A : Inverter}
    (hg : ComputableInPolyTime g encBits encBits) (hA : IsPPT encBits A) :
    IsPPT encBool (truncDistinguisher2 g A) := by
  unfold truncDistinguisher2
  ppt

/-- Exact probability bound linking `inversionGame (truncPRG g) A n` with the two distinguishers
`truncDistinguisher1` and `truncDistinguisher2`: `invProb ≤ adv(D₁) + 2 · adv(D₂)`. -/
private theorem invProb_le_adv_truncDistinguishers {g : List Bool → List Bool}
    {length : ℕ → ℕ} (hlen : ∀ v, (g v).length = length v.length)
    (hstretch : ∀ n, n < length n) (A : Inverter) (n : ℕ) :
    (Game.succProbability (ProbComp.eval (inversionGame (truncPRG g) A n)) : ℝ) ≤
      (Game.advantage (ProbComp.eval (prgRealGame g (truncDistinguisher1 g A) n))
        (ProbComp.eval (prgIdealGame length (truncDistinguisher1 g A) n)) : ℝ) +
      2 * (Game.advantage (ProbComp.eval (prgRealGame g (truncDistinguisher2 g A) n))
        (ProbComp.eval (prgIdealGame length (truncDistinguisher2 g A) n)) : ℝ) := by
  set invP : ℝ := (Game.succProbability (ProbComp.eval (inversionGame (truncPRG g) A n)) : ℝ)
  set r1 : ℝ :=
    (Game.succProbability (ProbComp.eval (prgRealGame g (truncDistinguisher1 g A) n)) : ℝ)
  set i1 : ℝ :=
    (Game.succProbability (ProbComp.eval (prgIdealGame length (truncDistinguisher1 g A) n)) : ℝ)
  set r2 : ℝ :=
    (Game.succProbability (ProbComp.eval (prgRealGame g (truncDistinguisher2 g A) n)) : ℝ)
  set i2 : ℝ :=
    (Game.succProbability (ProbComp.eval (prgIdealGame length (truncDistinguisher2 g A) n)) : ℝ)
  have hlen_n : n + 1 ≤ length n := hstretch n
  have hr1_eq : r1 = invP := by
    simp only [r1, invP, Game.coe_succProbability]
    congr 2
    simp only [prgRealGame, inversionGame, inversionExperiment, truncDistinguisher1,
      ProbComp.eval_bind, BitString.eval_sampleList, ProbComp.eval_pure]
    refine PMF.bind_congr_on_support _ _ _ fun v hv => ?_
    have hvl := BitString.length_of_mem_support_uniformList hv
    have htake : (g v).take n = truncPRG g v := by simp [truncPRG, hvl]
    rw [htake]
  have hi1_eq : i1 =
      (∑ y : BitString n,
        (((ProbComp.eval (A n (List.ofFn y))).map
          fun cand => truncPRG g cand == List.ofFn y) true).toReal) / (2 : ℝ) ^ n := by
    simp only [i1, Game.coe_succProbability, prgIdealGame, truncDistinguisher1,
      ProbComp.eval_bind, BitString.eval_sampleList, ProbComp.eval_pure]
    have htake_dist :
        (BitString.uniformList (length n)).bind (fun w =>
          (ProbComp.eval (A n (w.take n))).bind fun cand =>
            PMF.pure (truncPRG g cand == w.take n)) =
        (BitString.uniformList n).bind fun y =>
          (ProbComp.eval (A n y)).map fun cand => truncPRG g cand == y := by
      have h1 := BitString.uniformList_take (Nat.le_of_lt (hstretch n))
      rw [← h1, PMF.bind_map]
      rfl
    rw [htake_dist]
    rw [BitString.uniformList, PMF.bind_map, PMF.bind_apply, tsum_fintype,
      ENNReal.toReal_sum (fun _ _ => ENNReal.mul_ne_top (by simp) (PMF.apply_ne_top _ _))]
    simp_rw [ENNReal.toReal_mul, PMF.uniformOfFintype_apply, BitString.card,
      ENNReal.toReal_inv, ENNReal.toReal_natCast, Nat.cast_pow, Nat.cast_ofNat]
    rw [← Finset.mul_sum, inv_mul_eq_div]
    rfl
  have hi2_eq : i2 = i1 / 2 := by
    have htake2 :
        (BitString.uniformList (length n)).bind (fun w =>
          (ProbComp.eval (A n (w.take n))).bind fun cand =>
            PMF.pure (decide (cand.length = n) && ((g cand).take (n + 1) == w.take (n + 1)))) =
        (BitString.uniformList (n + 1)).bind (fun w =>
          (ProbComp.eval (A n (w.take n))).bind fun cand =>
            PMF.pure (decide (cand.length = n) && ((g cand).take (n + 1) == w))) := by
      rw [← BitString.uniformList_take hlen_n, PMF.bind_map]
      refine PMF.bind_congr_on_support _ _ _ fun w _ => ?_
      have ht : (w.take (n + 1)).take n = w.take n := by
        rw [List.take_take, Nat.min_eq_left (Nat.le_succ n)]
      simp only [Function.comp_def, ht]
    have hsplit :
        (BitString.uniformList (n + 1)).bind (fun w =>
          (ProbComp.eval (A n (w.take n))).bind fun cand =>
            PMF.pure (decide (cand.length = n) && ((g cand).take (n + 1) == w))) =
        (BitString.uniformList n).bind fun y =>
          (ProbComp.eval (A n y)).bind fun cand =>
            (PMF.uniformOfFintype Bool).map fun b =>
              decide (cand.length = n) && ((g cand).take (n + 1) == y ++ [b]) := by
      rw [BitString.uniformList_snoc]
      simp only [PMF.bind_bind, PMF.bind_map, Function.comp_def]
      refine PMF.bind_congr_on_support _ _ _ fun y hy => ?_
      have hyl := BitString.length_of_mem_support_uniformList hy
      have htake_y : ∀ b : Bool, (y ++ [b]).take n = y := fun b => List.take_left' hyl
      simp_rw [htake_y]
      rw [PMF.bind_comm]
      rfl
    have hbit_prob : ∀ (y : List Bool), y.length = n → ∀ (cand : List Bool),
        (((PMF.uniformOfFintype Bool).map fun b =>
          decide (cand.length = n) && ((g cand).take (n + 1) == y ++ [b])) true).toReal =
        (if truncPRG g cand = y then (1 : ℝ) else 0) / 2 := by
      intro y hyl cand
      rw [PMF.map_apply, tsum_fintype, Fintype.sum_bool,
        ENNReal.toReal_add (by split_ifs <;> simp) (by split_ifs <;> simp)]
      by_cases hcl : cand.length = n
      · have hglen : n + 1 ≤ (g cand).length := by
          rw [hlen, hcl]; exact hstretch n
        have hdecomp : (g cand).take (n + 1) = truncPRG g cand ++ [(g cand)[n]'(by omega)] := by
          simp only [truncPRG, hcl]
          rw [List.take_succ_eq_append_getElem (by omega)]
        by_cases htr : truncPRG g cand = y
        · simp only [htr, ↓reduceIte, hdecomp]
          cases hgbit : (g cand)[n]'(by omega) <;>
            simp [hcl, PMF.uniformOfFintype_apply]
        · simp only [htr, ↓reduceIte, hdecomp]
          simp [hcl, htr]
      · have hne : truncPRG g cand ≠ y := by
          intro heq
          have := congrArg List.length heq
          rw [truncPRG_length hlen hstretch, hyl] at this
          exact hcl this
        simp [hcl, hne]
    simp only [i2, Game.coe_succProbability, prgIdealGame, truncDistinguisher2,
      ProbComp.eval_bind, BitString.eval_sampleList, ProbComp.eval_pure]
    rw [htake2, hsplit, hi1_eq]
    rw [BitString.uniformList, PMF.bind_map, PMF.bind_apply, tsum_fintype,
      ENNReal.toReal_sum (fun _ _ => ENNReal.mul_ne_top (by simp) (PMF.apply_ne_top _ _))]
    simp_rw [ENNReal.toReal_mul, PMF.uniformOfFintype_apply, BitString.card,
      ENNReal.toReal_inv, ENNReal.toReal_natCast, Nat.cast_pow, Nat.cast_ofNat]
    rw [← Finset.mul_sum, inv_mul_eq_div, div_div, mul_comm ((2 : ℝ) ^ n) 2, ← div_div]
    congr 1
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun y _ => ?_
    simp only [Function.comp_apply]
    rw [PMF.bind_apply, PMF.map_apply]
    have hterm : ∀ cand : List Bool,
        (ProbComp.eval (A n (List.ofFn y)) cand *
          ((PMF.uniformOfFintype Bool).map fun b =>
            decide (cand.length = n) && ((g cand).take (n + 1) == List.ofFn y ++ [b])) true) =
        (if true = (truncPRG g cand == List.ofFn y) then
          ProbComp.eval (A n (List.ofFn y)) cand else 0) * (2 : ENNReal)⁻¹ := by
      intro cand
      have hreal := hbit_prob (List.ofFn y) (by simp) cand
      have hne_top : ((PMF.uniformOfFintype Bool).map fun b =>
          decide (cand.length = n) && ((g cand).take (n + 1) == List.ofFn y ++ [b])) true ≠ ⊤ :=
        PMF.apply_ne_top _ _
      have henn : ((PMF.uniformOfFintype Bool).map fun b =>
          decide (cand.length = n) && ((g cand).take (n + 1) == List.ofFn y ++ [b])) true =
          if truncPRG g cand = List.ofFn y then (2 : ENNReal)⁻¹ else 0 := by
        apply (ENNReal.toReal_eq_toReal_iff' hne_top (by split_ifs <;> simp)).mp
        rw [hreal]
        split_ifs <;> simp
      rw [henn]
      by_cases htr : truncPRG g cand = List.ofFn y
      · simp [htr]
      · simp [htr]
    simp_rw [hterm]
    rw [ENNReal.tsum_mul_right, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_ofNat,
      div_eq_mul_inv]
    congr 2
    refine tsum_congr fun cand => ?_
    by_cases htr : truncPRG g cand = List.ofFn y <;> simp [htr]
  have hi1_le_r2 : i1 ≤ r2 := by
    rw [hi1_eq]
    have hr2_eq : r2 =
        (∑ v : BitString n,
          (((ProbComp.eval (A n (truncPRG g (List.ofFn v)))).bind fun cand =>
            PMF.pure (decide (cand.length = n) &&
              ((g cand).take (n + 1) == (g (List.ofFn v)).take (n + 1)))) true).toReal) /
          (2 : ℝ) ^ n := by
      simp only [r2, Game.coe_succProbability, prgRealGame, truncDistinguisher2,
        ProbComp.eval_bind, BitString.eval_sampleList, ProbComp.eval_pure]
      rw [BitString.uniformList, PMF.bind_map, PMF.bind_apply, tsum_fintype,
        ENNReal.toReal_sum (fun _ _ => ENNReal.mul_ne_top (by simp) (PMF.apply_ne_top _ _))]
      simp_rw [ENNReal.toReal_mul, PMF.uniformOfFintype_apply, BitString.card,
        ENNReal.toReal_inv, ENNReal.toReal_natCast, Nat.cast_pow, Nat.cast_ofNat]
      rw [← Finset.mul_sum, inv_mul_eq_div]
      congr 1
      refine Finset.sum_congr rfl fun v _ => ?_
      have htake : (g (List.ofFn v)).take n = truncPRG g (List.ofFn v) := by
        simp [truncPRG]
      simp only [Function.comp_def, htake]
    rw [hr2_eq]
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    have hy_sum : ∀ y : BitString n,
        (((ProbComp.eval (A n (List.ofFn y))).map
          fun cand => truncPRG g cand == List.ofFn y) true).toReal =
        ∑ v : BitString n, if truncPRG g (List.ofFn v) = List.ofFn y then
          (ProbComp.eval (A n (List.ofFn y)) (List.ofFn v)).toReal else 0 := by
      intro y
      rw [PMF.map_apply]
      have hsupp : ∀ cand : List Bool,
          true = (truncPRG g cand == List.ofFn y) →
          cand ∈ (Finset.univ.image (List.ofFn : BitString n → List Bool)) := by
        intro cand htr'
        have htr : truncPRG g cand = List.ofFn y := by simpa using htr'.symm
        have hlen_c : cand.length = n := by
          have := congrArg List.length htr
          rw [truncPRG_length hlen hstretch, List.length_ofFn] at this
          exact this
        refine Finset.mem_image.mpr ⟨BitString.ofList n cand, Finset.mem_univ _, ?_⟩
        exact BitString.ofFn_ofList hlen_c
      rw [tsum_eq_sum (s := Finset.univ.image (List.ofFn : BitString n → List Bool))
        (fun cand hnot => by
          split_ifs with h
          · exact absurd (hsupp cand h) hnot
          · rfl)]
      rw [Finset.sum_image (fun a _ b _ h => List.ofFn_injective h),
        ENNReal.toReal_sum (fun _ _ => by split_ifs <;> simp [PMF.apply_ne_top])]
      refine Finset.sum_congr rfl fun v _ => ?_
      by_cases htr : truncPRG g (List.ofFn v) = List.ofFn y <;> simp [htr]
    simp_rw [hy_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum fun v _ => ?_
    let y₀ : BitString n := BitString.ofList n (truncPRG g (List.ofFn v))
    have hy₀ : List.ofFn y₀ = truncPRG g (List.ofFn v) := by
      apply BitString.ofFn_ofList
      rw [truncPRG_length hlen hstretch, List.length_ofFn]
    have hsingle :
        (∑ y : BitString n, if truncPRG g (List.ofFn v) = List.ofFn y then
          (ProbComp.eval (A n (List.ofFn y)) (List.ofFn v)).toReal else 0) =
        (ProbComp.eval (A n (truncPRG g (List.ofFn v))) (List.ofFn v)).toReal := by
      rw [Finset.sum_eq_single y₀]
      · simp [hy₀]
      · intro y _ hne
        have hne' : truncPRG g (List.ofFn v) ≠ List.ofFn y := by
          rw [← hy₀]
          intro h
          exact hne (List.ofFn_injective h).symm
        simp [hne']
      · intro h; exact absurd (Finset.mem_univ y₀) h
    rw [hsingle]
    have hle_enn : ProbComp.eval (A n (truncPRG g (List.ofFn v))) (List.ofFn v) ≤
        ((ProbComp.eval (A n (truncPRG g (List.ofFn v)))).bind fun cand =>
          PMF.pure (decide (cand.length = n) &&
            ((g cand).take (n + 1) == (g (List.ofFn v)).take (n + 1)))) true := by
      rw [PMF.bind_apply]
      have hterm_eq : ProbComp.eval (A n (truncPRG g (List.ofFn v))) (List.ofFn v) =
          ProbComp.eval (A n (truncPRG g (List.ofFn v))) (List.ofFn v) *
            PMF.pure (decide ((List.ofFn v).length = n) &&
              ((g (List.ofFn v)).take (n + 1) == (g (List.ofFn v)).take (n + 1))) true := by
        simp
      rw [hterm_eq]
      exact le_tsum (f := fun cand => ProbComp.eval (A n (truncPRG g (List.ofFn v))) cand *
        PMF.pure (decide (cand.length = n) &&
          ((g cand).take (n + 1) == (g (List.ofFn v)).take (n + 1))) true) (List.ofFn v)
    exact ENNReal.toReal_mono (PMF.apply_ne_top _ _) hle_enn
  rw [Game.coe_advantage, Game.coe_advantage]
  change invP ≤ |r1 - i1| + 2 * |r2 - i2|
  have h1 : invP - i1 ≤ |r1 - i1| := by rw [← hr1_eq]; exact le_abs_self _
  have h2 : i1 / 2 ≤ |r2 - i2| := by
    have : i1 / 2 ≤ r2 - i2 := by linarith
    exact this.trans (le_abs_self _)
  linarith

/-- If `g` is a pseudorandom generator with seed length `n` and output length `length n > n`, then
its truncation `truncPRG g` to the first `n` output bits is both pseudouniform and one-way. -/
theorem truncation_pseudouniform_and_oneWay {g : List Bool → List Bool} {length : ℕ → ℕ}
    (hPRG : PseudorandomGenerator g length) :
    Pseudouniform (truncPRG g) ∧ OneWay (truncPRG g) := by
  have hpoly : ComputableInPolyTime (truncPRG g) encBits encBits :=
    polyTime_truncPRG hPRG.polyTime
  have hlen : ∀ v, (truncPRG g v).length = v.length :=
    truncPRG_length hPRG.length_eq hPRG.stretch
  have hPU : Pseudouniform (truncPRG g) := by
    refine ⟨hpoly, hlen, ?_⟩
    have hmap : ComputationallyIndistinguishable
        (fun n => (generatorEnsemble g n).map (List.take n))
        (fun n => (BitString.uniformList (length n)).map (List.take n)) :=
      hPRG.indistinguishable.map (by fun_prop)
    have hL : (fun n => (generatorEnsemble g n).map (List.take n)) =
        generatorEnsemble (truncPRG g) := by
      funext n
      change (generatorEnsemble g n).map (List.take n) =
        generatorEnsemble (fun seed => (g seed).take seed.length) n
      exact (generatorEnsemble_postprocess g (fun k w => w.take k) n).symm
    have hR : (fun n => (BitString.uniformList (length n)).map (List.take n)) =
        BitString.uniformList := by
      funext n
      exact BitString.uniformList_take (Nat.le_of_lt (hPRG.stretch n))
    rwa [hL, hR] at hmap
  have hOW : OneWay (truncPRG g) := by
    refine OneWay.of_inversion_negligible hpoly fun A hA => ?_
    have hD1 : IsPPT encBool (truncDistinguisher1 g A) :=
      isPPT_truncDistinguisher1 hPRG.polyTime hA
    have hD2 : IsPPT encBool (truncDistinguisher2 g A) :=
      isPPT_truncDistinguisher2 hPRG.polyTime hA
    have hneg1 : Negligible fun n =>
        Game.advantage (ProbComp.eval (prgRealGame g (truncDistinguisher1 g A) n))
          (ProbComp.eval (prgIdealGame length (truncDistinguisher1 g A) n)) := by
      simpa only [eval_prgRealGame, eval_prgIdealGame] using
        hPRG.indistinguishable (truncDistinguisher1 g A) hD1
    have hneg2 : Negligible fun n =>
        Game.advantage (ProbComp.eval (prgRealGame g (truncDistinguisher2 g A) n))
          (ProbComp.eval (prgIdealGame length (truncDistinguisher2 g A) n)) := by
      simpa only [eval_prgRealGame, eval_prgIdealGame] using
        hPRG.indistinguishable (truncDistinguisher2 g A) hD2
    refine negligible_of_le (hneg1.add (hneg2.add hneg2)) fun n => ?_
    rw [← NNReal.coe_le_coe]
    have h := invProb_le_adv_truncDistinguishers hPRG.length_eq hPRG.stretch A n
    simp only [Pi.add_apply, NNReal.coe_add]
    linarith
  exact ⟨hPU, hOW⟩

end CslibFrontier.Crypto.Computational

end
