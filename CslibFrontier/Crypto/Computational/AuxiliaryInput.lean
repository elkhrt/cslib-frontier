/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Papers Contributors
-/
module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Pair
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Unary
public import CslibFrontier.Computability.Probabilistic.Oracle.Parameter
public import CslibFrontier.Computability.Probabilistic.PPT
public import CslibFrontier.Crypto.Computational.OneWay
public import CslibFrontier.Crypto.Computational.PseudorandomFunction
public import CslibFrontier.Crypto.Computational.PseudorandomGenerator
public import CslibFrontier.Probability.BitString
public import CslibFrontier.Probability.StatisticalDistance.CloseTo
import CslibFrontier.Computability.Complexity.Classes.Ladner.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Crypto.Game.Order
import CslibFrontier.Crypto.Negligible.Basic
import CslibFrontier.Foundations.Data.BitString.WordsOfLength
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.Map
import CslibFrontier.Probability.PMF.ToReal
import CslibFrontier.Tactic.PPT
import CslibFrontier.Tactic.PolyTime

/-!
# Auxiliary-Input and Infinitely-Often Cryptographic Primitives

This module defines auxiliary-input cryptographic primitives (`AuxInputFamily`, `IsAIOWF`,
`IsDistAIOWF`, `IsAIPRG`, `ExistsAIPRG`, `AuxInputPRFFamily`, `IsAIPRF`) and infinitely-often
cryptographic primitives (`IsIoOWF`, `IsIoPRG`, `IsIoPRF`), built directly on `CslibFrontier`'s
`ComputableInPolyTime`, `IsPPTOn`, `IsOraclePPTOn`, and `CloseTo` infrastructure.

## Main definitions

- `CslibFrontier.Crypto.AuxInputFamily`: polynomial-time auxiliary-input function family with
  polynomial-time input/output length maps.
- `CslibFrontier.Crypto.IsAIOWF`: auxiliary-input one-way function.
- `CslibFrontier.Crypto.IsDistAIOWF`: distributional auxiliary-input one-way function.
- `CslibFrontier.Crypto.IsAIPRG`, `CslibFrontier.Crypto.ExistsAIPRG`: auxiliary-input PRG and
  polynomial-stretch existence predicate.
- `CslibFrontier.Crypto.AuxInputPRFFamily`, `CslibFrontier.Crypto.IsAIPRF`: auxiliary-input
  pseudorandom function family.
- `CslibFrontier.Crypto.IsIoOWF`, `CslibFrontier.Crypto.IsIoPRG`, `CslibFrontier.Crypto.IsIoPRF`:
  infinitely-often one-way function, PRG, and PRF.

## Main results

- `CslibFrontier.Crypto.IsAIOWF.isDistAIOWF`: AIOWF implies distributional AIOWF.
- `CslibFrontier.Crypto.IsAIPRG.isAIOWF_of_sq_lt` and
  `CslibFrontier.Crypto.exists_aiOWF_of_exists_aiPRG`: polynomial-stretch auxiliary-input PRGs
  yield auxiliary-input one-way functions (combining inversion with bounded brute-force seed
  enumeration).
- `CslibFrontier.Crypto.OneWay.isIoOWF`, `CslibFrontier.Crypto.PseudorandomGenerator.isIoPRG`:
  standard uniform primitives are infinitely-often secure.
- `CslibFrontier.Crypto.IsIoOWF.exists_aiOWF`, `CslibFrontier.Crypto.IsIoPRG.exists_aiPRG`,
  `CslibFrontier.Crypto.IsIoPRF.exists_aiPRF`: infinitely-often uniform primitives yield
  auxiliary-input primitives.
-/

public section

namespace CslibFrontier.Crypto

open scoped ENNReal NNReal
open Cslib Cslib.BitString Cslib.Complexity Cslib.Crypto Cslib.Probability Turing.MultiTapeTM

/-- A polynomial-time computable **auxiliary-input function family**
`f = {f_z : {0,1}^{inputLen |z|} → {0,1}^{outputLen |z|}}`. Both length maps are computable in
polynomial time from unary `|z|`, ruling out superpolynomial length loopholes. -/
@[ext]
structure AuxInputFamily where
  /-- Input bit-length as a function of auxiliary-input length `|z|`. -/
  inputLen : ℕ → ℕ
  /-- Output bit-length as a function of auxiliary-input length `|z|`. -/
  outputLen : ℕ → ℕ
  /-- Family evaluation `f_z(x)`. -/
  eval : List Bool → List Bool → List Bool
  /-- `inputLen` is computable in polynomial time in unary. -/
  polyTime_inputLen : ComputableInPolyTime inputLen encUnary encUnary
  /-- `outputLen` is computable in polynomial time in unary. -/
  polyTime_outputLen : ComputableInPolyTime outputLen encUnary encUnary
  /-- `eval` is jointly computable in polynomial time on `(z, x)`. -/
  polyTime_eval : ComputableInPolyTime (fun p : List Bool × List Bool => eval p.1 p.2)
    (encPair encBits encBits) encBits
  /-- Exact output length on inputs of length `inputLen |z|`. -/
  length_eq : ∀ z x, x.length = inputLen z.length → (eval z x).length = outputLen z.length

/-- Inversion game for an auxiliary-input family `f` against adversary `A` on auxiliary string `z`.
The adversary wins when it outputs a preimage `x'` of exact length `f.inputLen z.length`. -/
noncomputable def aiInversionGame (f : AuxInputFamily)
    (A : List Bool → List Bool → ProbComp (List Bool)) (z : List Bool) : ProbComp Bool := do
  let x ← Cslib.BitString.sampleList (f.inputLen z.length)
  let y := f.eval z x
  let x' ← A z y
  return decide (x'.length = f.inputLen z.length ∧ f.eval z x' = y)

/-- **Auxiliary-input one-way function** (AIOWF): for every inverse polynomial `( |z| + 1 )^{-d}`
and every uniform PPT inverter `A`, there exist arbitrarily long auxiliary strings `z` on which
`A` inverts `f_z` with probability strictly less than `( |z| + 1 )^{-d}`. -/
def IsAIOWF (f : AuxInputFamily) : Prop :=
  ∀ (d : ℕ) (A : List Bool → List Bool → ProbComp (List Bool)),
    IsPPTOn (encPair encBits encBits) encBits (fun p => A p.1 p.2) →
    ∀ N : ℕ, ∃ z : List Bool, N ≤ z.length ∧
      (ProbComp.eval (aiInversionGame f A z) true).toReal <
        ((z.length + 1 : ℝ) ^ d)⁻¹

/-- True joint distribution `(x, f_z(x))` for `x ~ U_{f.inputLen |z|}`. -/
noncomputable def aiTrueJoint (f : AuxInputFamily) (z : List Bool) :
    PMF (List Bool × List Bool) :=
  (uniformList (f.inputLen z.length)).map fun x => (x, f.eval z x)

/-- Distributional-inverter joint distribution `(A(z, f_z(x)), f_z(x))` for
`x ~ U_{f.inputLen |z|}`. -/
noncomputable def aiDistInverterJoint (f : AuxInputFamily)
    (A : List Bool → List Bool → ProbComp (List Bool)) (z : List Bool) :
    PMF (List Bool × List Bool) :=
  (uniformList (f.inputLen z.length)).bind fun x =>
    (ProbComp.eval (A z (f.eval z x))).map fun x' => (x', f.eval z x)

/-- **Distributional auxiliary-input one-way function** (distAIOWF): there exists an inverse
polynomial `( |z| + 1 )^{-c}` such that for every uniform PPT `A`, there exist arbitrarily long
auxiliary strings `z` on which `(A(z, f_z(x)), f_z(x))` and `(x, f_z(x))` have total variation
distance strictly exceeding `( |z| + 1 )^{-c}`. -/
def IsDistAIOWF (f : AuxInputFamily) : Prop :=
  ∃ c : ℕ, ∀ (A : List Bool → List Bool → ProbComp (List Bool)),
    IsPPTOn (encPair encBits encBits) encBits (fun p => A p.1 p.2) →
    ∀ N : ℕ, ∃ z : List Bool, N ≤ z.length ∧
      ¬ CloseTo (aiDistInverterJoint f A z) (aiTrueJoint f z)
          (ENNReal.ofReal (((z.length + 1 : ℝ) ^ c)⁻¹))

/-- Real distinguishing game for an auxiliary-input PRG `G` on auxiliary string `z`. -/
noncomputable def aiPrgRealGame (G : AuxInputFamily)
    (A : List Bool → List Bool → ProbComp Bool) (z : List Bool) : ProbComp Bool := do
  let v ← Cslib.BitString.sampleList (G.inputLen z.length)
  A z (G.eval z v)

/-- Ideal (uniform) distinguishing game for an auxiliary-input PRG `G` on auxiliary string `z`. -/
noncomputable def aiPrgIdealGame (G : AuxInputFamily)
    (A : List Bool → List Bool → ProbComp Bool) (z : List Bool) : ProbComp Bool := do
  let u ← Cslib.BitString.sampleList (G.outputLen z.length)
  A z u

/-- **Auxiliary-input pseudorandom generator** (AIPRG): strictly stretches its seed and fools
every uniform PPT distinguisher up to every inverse polynomial on infinitely many `z`. -/
def IsAIPRG (G : AuxInputFamily) : Prop :=
  (∀ k, G.inputLen k < G.outputLen k) ∧
  ∀ (d : ℕ) (A : List Bool → List Bool → ProbComp Bool),
    IsPPTOn (encPair encBits encBits) encBool (fun p => A p.1 p.2) →
    ∀ N : ℕ, ∃ z : List Bool, N ≤ z.length ∧
      |(ProbComp.eval (aiPrgRealGame G A z) true).toReal -
        (ProbComp.eval (aiPrgIdealGame G A z) true).toReal| ≤
        ((z.length + 1 : ℝ) ^ d)⁻¹

/-- **Existence of polynomial-stretch AIPRGs** (`∃ AIPRG`): for every polynomial stretch degree `d`,
there exists an AIPRG `G` with `(G.inputLen k) ^ d < G.outputLen k` for all `k`. -/
def ExistsAIPRG : Prop :=
  ∀ d : ℕ, ∃ G : AuxInputFamily, IsAIPRG G ∧ ∀ k, (G.inputLen k) ^ d < G.outputLen k

/-- A polynomial-time computable **auxiliary-input PRF family**
`F = {F_z : {0,1}^{n(|z|)} × {0,1}^{n(|z|)} → Bool}`. -/
@[ext]
structure AuxInputPRFFamily where
  /-- Key and query length as a function of `|z|`. -/
  inputLen : ℕ → ℕ
  /-- Keyed Boolean evaluation `F_z(u, x)`. -/
  eval : List Bool → List Bool → List Bool → Bool
  /-- `inputLen` is computable in polynomial time in unary. -/
  polyTime_inputLen : ComputableInPolyTime inputLen encUnary encUnary
  /-- `eval` is jointly computable in polynomial time on `(z, (u, x))`. -/
  polyTime_eval : ComputableInPolyTime
    (fun p : List Bool × (List Bool × List Bool) => eval p.1 p.2.1 p.2.2)
    (encPair encBits (encPair encBits encBits)) encBool

/-- Real oracle game for an auxiliary-input PRF family `F` against oracle adversary `A`. -/
noncomputable def aiPrfRealGame (F : AuxInputPRFFamily)
    (A : List Bool → WordOracleComp Unit Bool) (z : List Bool) : ProbComp Bool := do
  let u ← Cslib.BitString.sampleList (F.inputLen z.length)
  (A z).run fun req =>
    pure (if req.2.length = F.inputLen z.length then [F.eval z u req.2] else [])

/-- Ideal random-function oracle game for an auxiliary-input PRF family `F`. -/
noncomputable def aiPrfIdealGame (F : AuxInputPRFFamily)
    (A : List Bool → WordOracleComp Unit Bool) (z : List Bool) : ProbComp Bool := do
  let table ← ProbComp.uniform (BitString (F.inputLen z.length) → BitString 1)
  (A z).run fun req =>
    pure (randomFunctionOracle (F.inputLen z.length) table req.2)

/-- **Auxiliary-input pseudorandom function** (AIPRF): for every inverse polynomial and every
uniform oracle PPT distinguisher `A`, there exist arbitrarily long `z` where `A` distinguishes
`F_z(u, ·)` from a uniform random function with advantage strictly below `( |z| + 1 )^{-d}`. -/
def IsAIPRF (F : AuxInputPRFFamily) : Prop :=
  ∀ (d : ℕ) (A : List Bool → WordOracleComp Unit Bool),
    IsOraclePPTOn encBits encBool A →
    ∀ N : ℕ, ∃ z : List Bool, N ≤ z.length ∧
      |(ProbComp.eval (aiPrfRealGame F A z) true).toReal -
        (ProbComp.eval (aiPrfIdealGame F A z) true).toReal| <
        ((z.length + 1 : ℝ) ^ d)⁻¹

/-- **Infinitely-often one-way function** (ioOWF): polynomial-time computable function `f` such
that every uniform PPT inverter fails (below `(n + 1)^{-d}`) on infinitely many input lengths `n`
when restricted to length-`n` preimages. -/
def IsIoOWF (f : List Bool → List Bool) : Prop :=
  ComputableInPolyTime f encBits encBits ∧
  ∀ (d : ℕ) (A : Inverter), IsPPT encBits A →
    ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      (ProbComp.eval
        (inversionGameOn f (fun m x' => decide (x'.length = m)) A n) true).toReal <
        ((n + 1 : ℝ) ^ d)⁻¹

/-- **Infinitely-often pseudorandom generator** (ioPRG): polynomial-time length-stretching
generator fooling every uniform PPT distinguisher on infinitely many seed lengths `n`. -/
def IsIoPRG (G : List Bool → List Bool) (len : ℕ → ℕ) : Prop :=
  ComputableInPolyTime G encBits encBits ∧
  (∀ x, (G x).length = len x.length) ∧
  (∀ n, n < len n) ∧
  ∀ (d : ℕ) (A : Distinguisher), IsPPT encBool A →
    ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      |(ProbComp.eval (prgRealGame G A n) true).toReal -
        (ProbComp.eval (prgIdealGame len A n) true).toReal| ≤
        ((n + 1 : ℝ) ^ d)⁻¹

/-- **Infinitely-often pseudorandom function** (ioPRF): polynomial-time keyed Boolean family
`f(u, x)` fooling every uniform oracle PPT distinguisher on infinitely many key lengths `n`. -/
def IsIoPRF (f : List Bool → List Bool → Bool) : Prop :=
  ComputableInPolyTime (fun p : List Bool × List Bool => f p.1 p.2)
    (encPair encBits encBits) encBool ∧
  ∀ (d : ℕ) (A : OracleDistinguisher), IsOraclePPT encBool A →
    ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      |(ProbComp.eval (prfRealGame id (fun u x => [f u x]) A n) true).toReal -
        (ProbComp.eval (prfIdealGame id (fun _ => 1) A n) true).toReal| <
        ((n + 1 : ℝ) ^ d)⁻¹

/-- The inversion probability in `aiInversionGame f A z` equals the probability of the valid
preimage event under `aiDistInverterJoint f A z`. -/
theorem eval_aiInversionGame_eq_toOuterMeasure (f : AuxInputFamily)
    (A : List Bool → List Bool → ProbComp (List Bool)) (z : List Bool) :
    ProbComp.eval (aiInversionGame f A z) true =
      (aiDistInverterJoint f A z).toOuterMeasure
        {p : List Bool × List Bool |
          p.1.length = f.inputLen z.length ∧ f.eval z p.1 = p.2} := by
  classical
  simp only [aiInversionGame, aiDistInverterJoint, ProbComp.eval_bind,
    ProbComp.eval_pure, BitString.eval_sampleList, PMF.bind_apply,
    PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_map_apply]
  refine tsum_congr fun x => ?_
  congr 1
  rw [PMF.toOuterMeasure_apply]
  refine tsum_congr fun x' => ?_
  by_cases h : x'.length = f.inputLen z.length ∧ f.eval z x' = f.eval z x <;> simp [h]

/-- The valid preimage event has probability `1` under `aiTrueJoint f z`. -/
theorem aiTrueJoint_preimage_event_eq_one (f : AuxInputFamily) (z : List Bool) :
    (aiTrueJoint f z).toOuterMeasure
        {p : List Bool × List Bool |
          p.1.length = f.inputLen z.length ∧ f.eval z p.1 = p.2} = 1 := by
  rw [aiTrueJoint, PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_apply_eq_one_iff]
  intro x hx
  exact ⟨length_of_mem_support_uniformList hx, rfl⟩

/-- **Every auxiliary-input one-way function is distributionally one-way.** -/
theorem IsAIOWF.isDistAIOWF {f : AuxInputFamily} (hf : IsAIOWF f) : IsDistAIOWF f := by
  refine ⟨1, fun A hA N => ?_⟩
  obtain ⟨z, hNz, hlt⟩ := hf 1 A hA (max N 2)
  refine ⟨z, (le_max_left N 2).trans hNz, fun hclose => ?_⟩
  let E : Set (List Bool × List Bool) :=
    {p | p.1.length = f.inputLen z.length ∧ f.eval z p.1 = p.2}
  have hbound := hclose.symm E
  rw [aiTrueJoint_preimage_event_eq_one, ← eval_aiInversionGame_eq_toOuterMeasure] at hbound
  have hreal : (1 : ℝ) ≤ (ProbComp.eval (aiInversionGame f A z) true).toReal +
      ((z.length + 1 : ℝ) ^ 1)⁻¹ := by
    have hfin1 : ProbComp.eval (aiInversionGame f A z) true ≠ ⊤ := PMF.apply_ne_top _ _
    have hfin2 : ENNReal.ofReal (((z.length + 1 : ℝ) ^ 1)⁻¹) ≠ ⊤ := ENNReal.ofReal_ne_top
    have hmono := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hfin1, hfin2⟩) hbound
    rw [ENNReal.toReal_one, ENNReal.toReal_add hfin1 hfin2,
      ENNReal.toReal_ofReal (by positivity)] at hmono
    exact hmono
  have hinv_gt : (1 : ℝ) - ((z.length + 1 : ℝ) ^ 1)⁻¹ ≤
      (ProbComp.eval (aiInversionGame f A z) true).toReal := by linarith
  have hsmall : ((z.length + 1 : ℝ) ^ 1)⁻¹ ≤ (1 / 3 : ℝ) := by
    have hz2 : (3 : ℝ) ≤ (z.length + 1 : ℝ) := by
      have : 2 ≤ z.length := (le_max_right N 2).trans hNz
      exact_mod_cast (show 3 ≤ z.length + 1 by omega)
    rw [pow_one, show (1 / 3 : ℝ) = (3 : ℝ)⁻¹ by norm_num]
    exact inv_anti₀ (by norm_num) hz2
  linarith

/-- **Every polynomial-stretch AIPRG is an AIOWF** (in fact, any AIPRG with
`(G.inputLen k) ^ 2 < G.outputLen k` is itself an AIOWF). -/
theorem IsAIPRG.isAIOWF_of_sq_lt {G : AuxInputFamily} (hG : IsAIPRG G)
    (hsq : ∀ k, (G.inputLen k) ^ 2 < G.outputLen k) : IsAIOWF G := by
  intro c A hA N
  by_contra hnot
  push Not at hnot
  let Ncap : List Bool → ℕ := fun z => 2 * (z.length + 1) ^ (c + 3)
  let bruteCheck : List Bool → List Bool → Bool := fun z y =>
    (List.range (Ncap z)).any fun j =>
      (Ladner.word j).length == G.inputLen z.length && (G.eval z (Ladner.word j) == y)
  let useBrute : List Bool → Bool := fun z =>
    Ladner.capPow 2 (G.inputLen z.length + 1) (Ncap z + 1) <= Ncap z
  let D : List Bool → List Bool → ProbComp Bool := fun z y =>
    if useBrute z then pure (bruteCheck z y)
    else do
      let x' ← A z y
      return (x'.length == G.inputLen z.length) && (G.eval z x' == y)
  have hNcap_poly : ComputableInPolyTime Ncap encBits encUnary := by
    have hlen : ComputableInPolyTime (fun z : List Bool => z.length) encBits encUnary :=
      ComputableInPolyTime.length_bits
    dsimp only [Ncap]; fun_prop
  have huseBrute_poly : ComputableInPolyTime useBrute encBits encBool := by
    have hin : ComputableInPolyTime (fun z : List Bool => G.inputLen z.length) encBits encUnary :=
      G.polyTime_inputLen.comp ComputableInPolyTime.length_bits
    dsimp only [useBrute]; fun_prop
  have hbrute_poly : ComputableInPolyTime (fun p : List Bool × List Bool => bruteCheck p.1 p.2)
      (encPair encBits encBits) encBool := by
    have h1 := G.polyTime_inputLen
    have h2 := G.polyTime_eval
    dsimp only [bruteCheck]; fun_prop
  have hD_ppt : IsPPTOn (encPair encBits encBits) encBool (fun p => D p.1 p.2) := by
    have h1 := G.polyTime_inputLen
    have h2 := G.polyTime_eval
    dsimp only [D]; ppt
  obtain ⟨z, hNz, hdist⟩ := hG.2 (c + 1) D hD_ppt (max N 2)
  have hNz_orig : N ≤ z.length := (le_max_left N 2).trans hNz
  have hz2 : 2 ≤ z.length := (le_max_right N 2).trans hNz
  have hinv_ge : ((z.length + 1 : ℝ) ^ c)⁻¹ ≤
      (ProbComp.eval (aiInversionGame G A z) true).toReal := hnot z hNz_orig
  have himg_prob : ((uniformList (G.outputLen z.length)).toOuterMeasure
      {y : List Bool | ∃ x : List Bool, x.length = G.inputLen z.length ∧ G.eval z x = y}).toReal ≤
      (2 : ℝ) ^ G.inputLen z.length / (2 : ℝ) ^ G.outputLen z.length := by
    have hsub : {y : List Bool | ∃ x : List Bool, x.length = G.inputLen z.length ∧ G.eval z x = y}
        ⊆ ↑((wordsOfLength (G.inputLen z.length)).image (G.eval z)) := by
      rintro y ⟨x, hx, rfl⟩
      exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨x, mem_wordsOfLength.mpr hx, rfl⟩)
    have h1 : ((uniformList (G.outputLen z.length)).toOuterMeasure
        {y : List Bool |
          ∃ x : List Bool, x.length = G.inputLen z.length ∧ G.eval z x = y}).toReal ≤
        ((uniformList (G.outputLen z.length)).toOuterMeasure
          ↑((wordsOfLength (G.inputLen z.length)).image (G.eval z))).toReal :=
      Cslib.Probability.PMF.toOuterMeasure_toReal_mono _ hsub
    have h2 := toOuterMeasure_uniformList_finset_le (G.outputLen z.length)
      ((wordsOfLength (G.inputLen z.length)).image (G.eval z))
    have hcard : (((wordsOfLength (G.inputLen z.length)).image (G.eval z)).card : ℝ) ≤
        (2 : ℝ) ^ G.inputLen z.length := by
      have hc := Finset.card_image_le (f := G.eval z) (s := wordsOfLength (G.inputLen z.length))
      rw [card_wordsOfLength] at hc
      exact_mod_cast hc
    have h2real : ((uniformList (G.outputLen z.length)).toOuterMeasure
        ↑((wordsOfLength (G.inputLen z.length)).image (G.eval z))).toReal ≤
        (((wordsOfLength (G.inputLen z.length)).image (G.eval z)).card : ℝ) *
          ((2 : ℝ) ^ G.outputLen z.length)⁻¹ := by
      have hfin : ((((wordsOfLength (G.inputLen z.length)).image (G.eval z)).card : ℝ≥0∞) *
          (1 / (2 : ℝ≥0∞) ^ G.outputLen z.length)) ≠ ⊤ := by
        apply ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
        rw [one_div]
        exact ENNReal.inv_ne_top.mpr (by positivity)
      have hm := ENNReal.toReal_mono hfin h2
      rw [one_div, ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_inv,
        ENNReal.toReal_pow, ENNReal.toReal_ofNat] at hm
      exact hm
    calc _ ≤ _ := h1.trans h2real
      _ ≤ (2 : ℝ) ^ G.inputLen z.length * ((2 : ℝ) ^ G.outputLen z.length)⁻¹ := by gcongr
      _ = (2 : ℝ) ^ G.inputLen z.length / (2 : ℝ) ^ G.outputLen z.length := by rw [div_eq_mul_inv]
  by_cases hbr : useBrute z = true
  · have hcap : 2 ^ (G.inputLen z.length + 1) ≤ Ncap z := by
      dsimp only [useBrute] at hbr
      rw [decide_eq_true_eq, Ladner.capPow] at hbr
      omega
    have hbrute_iff : ∀ y, bruteCheck z y = true ↔
        ∃ x : List Bool, x.length = G.inputLen z.length ∧ G.eval z x = y := by
      intro y
      simp only [bruteCheck, List.any_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq]
      refine ⟨fun ⟨j, _, h1, h2⟩ => ⟨Ladner.word j, h1, h2⟩, ?_⟩
      rintro ⟨x, hx, rfl⟩
      refine ⟨Ladner.index x, ?_, by simp [Ladner.word_index, hx], by simp [Ladner.word_index]⟩
      have := Ladner.index_add_two_le x
      rw [hx] at this; omega
    have hreal_one : (ProbComp.eval (aiPrgRealGame G D z) true).toReal = 1 := by
      have h1 : ProbComp.eval (aiPrgRealGame G D z) true = 1 := by
        simp only [aiPrgRealGame, D, hbr, ↓reduceIte, ProbComp.eval_bind, ProbComp.eval_pure,
          BitString.eval_sampleList, PMF.bind_apply]
        rw [← (uniformList (G.inputLen z.length)).tsum_coe]
        refine tsum_congr fun v => ?_
        by_cases hv : v ∈ (uniformList (G.inputLen z.length)).support
        · have hvlen := length_of_mem_support_uniformList hv
          simp [(hbrute_iff _).mpr ⟨v, hvlen, rfl⟩]
        · have hv0 : uniformList (G.inputLen z.length) v = 0 :=
            not_not.mp ((PMF.mem_support_iff _ _).not.mp hv)
          simp [hv0]
      rw [h1, ENNReal.toReal_one]
    have hideal_le : (ProbComp.eval (aiPrgIdealGame G D z) true).toReal ≤ 1 / 2 := by
      have heq : ProbComp.eval (aiPrgIdealGame G D z) true =
          (uniformList (G.outputLen z.length)).toOuterMeasure
            {y : List Bool |
              ∃ x : List Bool, x.length = G.inputLen z.length ∧ G.eval z x = y} := by
        simp only [aiPrgIdealGame, D, hbr, ↓reduceIte, ProbComp.eval_bind, ProbComp.eval_pure,
          BitString.eval_sampleList, PMF.bind_apply, PMF.toOuterMeasure_apply]
        refine tsum_congr fun u => ?_
        by_cases hu : bruteCheck z u = true
        · simp [hu, (hbrute_iff u).mp hu]
        · have hnot' : ¬ ∃ x, x.length = G.inputLen z.length ∧ G.eval z x = u :=
            fun h => hu ((hbrute_iff u).mpr h)
          simp [hu, hnot']
      rw [heq]
      have hhalf : (2 : ℝ) ^ G.inputLen z.length / (2 : ℝ) ^ G.outputLen z.length ≤ 1 / 2 := by
        have hlt := hG.1 z.length
        have hpow : (2 : ℝ) ^ (G.inputLen z.length + 1) ≤ (2 : ℝ) ^ G.outputLen z.length := by
          exact_mod_cast Nat.pow_le_pow_right (by norm_num) hlt
        rw [div_le_iff₀ (by positivity)]
        rw [pow_succ] at hpow
        linarith
      exact himg_prob.trans hhalf
    have hstep : (1 / 2 : ℝ) ≤
        |(ProbComp.eval (aiPrgRealGame G D z) true).toReal -
          (ProbComp.eval (aiPrgIdealGame G D z) true).toReal| := by
      rw [hreal_one]
      exact (by linarith : (1 / 2 : ℝ) ≤
        1 - (ProbComp.eval (aiPrgIdealGame G D z) true).toReal).trans (le_abs_self _)
    have hgt : ((z.length + 1 : ℝ) ^ (c + 1))⁻¹ < 1 / 2 := by
      have hstrict : (2 : ℝ) < (z.length + 1 : ℝ) ^ (c + 1) := by
        have h3 : (3 : ℝ) ≤ (z.length + 1 : ℝ) := by
          exact_mod_cast (show 3 ≤ z.length + 1 by omega)
        calc (2 : ℝ) < (3 : ℝ) := by norm_num
          _ = (3 : ℝ) ^ 1 := (pow_one _).symm
          _ ≤ (z.length + 1 : ℝ) ^ 1 := by simpa using h3
          _ ≤ (z.length + 1 : ℝ) ^ (c + 1) := pow_le_pow_right₀ (by linarith) (by omega)
      rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num]
      exact inv_strictAnti₀ (by norm_num) hstrict
    linarith
  · have hbrf : useBrute z = false := Bool.eq_false_iff.mpr hbr
    have hcap_lt : Ncap z < 2 ^ (G.inputLen z.length + 1) := by
      dsimp only [useBrute] at hbr
      rw [decide_eq_true_eq, Ladner.capPow] at hbr
      omega
    have hreal_eq : ProbComp.eval (aiPrgRealGame G D z) true =
        ProbComp.eval (aiInversionGame G A z) true := by
      simp only [aiPrgRealGame, aiInversionGame, D, hbrf, Bool.false_eq_true, ↓reduceIte,
        ProbComp.eval_bind, ProbComp.eval_pure, BitString.eval_sampleList, PMF.bind_apply]
      refine tsum_congr fun a => ?_
      congr 1
      refine tsum_congr fun a₁ => ?_
      congr 1
      simp only [Bool.beq_eq_decide_eq, Bool.decide_and]
    have hideal_le : (ProbComp.eval (aiPrgIdealGame G D z) true).toReal ≤
        (2 : ℝ) ^ G.inputLen z.length / (2 : ℝ) ^ G.outputLen z.length := by
      have hle : ProbComp.eval (aiPrgIdealGame G D z) true ≤
          (uniformList (G.outputLen z.length)).toOuterMeasure
            {y : List Bool |
              ∃ x : List Bool, x.length = G.inputLen z.length ∧ G.eval z x = y} := by
        simp only [aiPrgIdealGame, D, hbrf, Bool.false_eq_true, ↓reduceIte, ProbComp.eval_bind,
          ProbComp.eval_pure, BitString.eval_sampleList, PMF.bind_apply, PMF.toOuterMeasure_apply]
        refine tsum_le_tsum fun u => ?_
        by_cases hu : ∃ x : List Bool, x.length = G.inputLen z.length ∧ G.eval z x = u
        · rw [Set.indicator_of_mem (s := {y | ∃ x, x.length = G.inputLen z.length ∧
              G.eval z x = y}) hu, ← PMF.bind_apply]
          exact mul_le_of_le_one_right zero_le (PMF.coe_le_one _ _)
        · rw [Set.indicator_of_notMem (s := {y | ∃ x, x.length = G.inputLen z.length ∧
              G.eval z x = y}) hu, ← PMF.bind_apply]
          have h0 : ((ProbComp.eval (A z u)).bind fun x' =>
              PMF.pure ((x'.length == G.inputLen z.length) && (G.eval z x' == u))) true = 0 := by
            simp only [PMF.bind_apply, PMF.pure_apply]
            rw [tsum_eq_zero_iff]
            intro x'
            have hfalse : ¬ (x'.length = G.inputLen z.length ∧ G.eval z x' = u) :=
              fun hx' => hu ⟨x', hx'⟩
            simp [hfalse]
          rw [h0, mul_zero]
      exact (ENNReal.toReal_mono
        (Cslib.Probability.PMF.toOuterMeasure_ne_top _ _) hle).trans himg_prob
    have hn_ge2 : 2 ≤ G.inputLen z.length := by
      have h1 : (z.length + 1) ^ (c + 3) < 2 ^ G.inputLen z.length := by
        dsimp only [Ncap] at hcap_lt
        rw [pow_succ' 2] at hcap_lt; omega
      have h2 : 2 ^ 3 ≤ (z.length + 1) ^ (c + 3) := by
        calc 2 ^ 3 ≤ (z.length + 1) ^ 3 := Nat.pow_le_pow_left (by omega) 3
          _ ≤ (z.length + 1) ^ (c + 3) := Nat.pow_le_pow_right (by omega) (by omega)
      have h3 : 2 ^ 1 < 2 ^ G.inputLen z.length := by omega
      have h4 := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp h3
      omega
    have hgap : G.inputLen z.length + G.inputLen z.length < G.outputLen z.length := by
      have := hsq z.length; nlinarith
    have hpow_le : (2 : ℝ) ^ G.inputLen z.length / (2 : ℝ) ^ G.outputLen z.length ≤
        ((z.length + 1 : ℝ) ^ (c + 3))⁻¹ := by
      have h1 : (z.length + 1) ^ (c + 3) < 2 ^ G.inputLen z.length := by
        dsimp only [Ncap] at hcap_lt
        rw [pow_succ' 2] at hcap_lt; omega
      have h2 : (2 : ℝ) ^ (2 * G.inputLen z.length) ≤ (2 : ℝ) ^ G.outputLen z.length := by
        exact_mod_cast Nat.pow_le_pow_right (by norm_num)
          (by omega : 2 * G.inputLen z.length ≤ G.outputLen z.length)
      have h3 : (2 : ℝ) ^ G.inputLen z.length / (2 : ℝ) ^ G.outputLen z.length ≤
          ((2 : ℝ) ^ G.inputLen z.length)⁻¹ := by
        rw [div_le_iff₀ (by positivity)]
        rw [mul_comm, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
        have : (2 : ℝ) ^ G.inputLen z.length * (2 : ℝ) ^ G.inputLen z.length =
            (2 : ℝ) ^ (2 * G.inputLen z.length) := by rw [two_mul, pow_add]
        linarith
      have h4 : ((2 : ℝ) ^ G.inputLen z.length)⁻¹ ≤ ((z.length + 1 : ℝ) ^ (c + 3))⁻¹ := by
        apply inv_anti₀ (by positivity)
        exact_mod_cast h1.le
      exact h3.trans h4
    have hdiff : ((z.length + 1 : ℝ) ^ (c + 1))⁻¹ <
        ((z.length + 1 : ℝ) ^ c)⁻¹ - ((z.length + 1 : ℝ) ^ (c + 3))⁻¹ := by
      have hbase : (2 : ℝ) ≤ (z.length + 1 : ℝ) := by
        exact_mod_cast (show 2 ≤ z.length + 1 by omega)
      have hpos : (0 : ℝ) < (z.length + 1 : ℝ) ^ c := by positivity
      have hpos_inv : (0 : ℝ) < ((z.length + 1 : ℝ) ^ c)⁻¹ := inv_pos.mpr hpos
      have h3 : ((z.length + 1 : ℝ) ^ (c + 3))⁻¹ ≤ ((z.length + 1 : ℝ) ^ c)⁻¹ / 8 := by
        rw [pow_add, mul_inv, div_eq_mul_inv]; gcongr
        calc (8 : ℝ) = (2 : ℝ) ^ 3 := by norm_num
          _ ≤ (z.length + 1 : ℝ) ^ 3 := pow_le_pow_left₀ (by norm_num) hbase 3
      have h1 : ((z.length + 1 : ℝ) ^ (c + 1))⁻¹ ≤ ((z.length + 1 : ℝ) ^ c)⁻¹ / 2 := by
        rw [pow_add, pow_one, mul_inv, div_eq_mul_inv]; gcongr
      linarith
    have habs : (ProbComp.eval (aiInversionGame G A z) true).toReal -
        (ProbComp.eval (aiPrgIdealGame G D z) true).toReal ≤
        |(ProbComp.eval (aiPrgRealGame G D z) true).toReal -
          (ProbComp.eval (aiPrgIdealGame G D z) true).toReal| := by
      rw [hreal_eq]; exact le_abs_self _
    linarith

/-- **`ExistsAIPRG` implies the existence of an AIOWF.** -/
theorem exists_aiOWF_of_exists_aiPRG (h : ExistsAIPRG) : ∃ f : AuxInputFamily, IsAIOWF f := by
  obtain ⟨G, hG, hsq⟩ := h 2
  exact ⟨G, hG.isAIOWF_of_sq_lt hsq⟩

/-- **Standard uniform one-way functions are infinitely-often one-way.** -/
theorem OneWay.isIoOWF {f : List Bool → List Bool} (hf : OneWay f) : IsIoOWF f := by
  refine ⟨hf.polyTime, fun d A hA N => ?_⟩
  have hneg := (hf.oneWayOn (valid := fun m x' => decide (x'.length = m))).negligible A hA
  have hev := hneg.eventually_le_inv_polynomial
    (p := fun n => 2 * (n + 1) ^ d) (by fun_prop) (fun n => by positivity)
  rw [Filter.eventually_atTop] at hev
  obtain ⟨M, hM⟩ := hev
  refine ⟨max N M, le_max_left N M, ?_⟩
  have hle := hM (max N M) (le_max_right N M)
  have hlt : (1 : ℝ) / (2 * (max N M + 1 : ℕ) ^ d : ℕ) <
      (((max N M : ℕ) + 1 : ℝ) ^ d)⁻¹ := by
    rw [one_div]; push_cast
    apply inv_strictAnti₀ (by positivity)
    have hpos : (0 : ℝ) < ((max N M : ℝ) + 1) ^ d := by positivity
    linarith
  exact lt_of_le_of_lt (by simpa [Game.coe_succProbability] using hle) hlt

/-- **Standard uniform pseudorandom generators are infinitely-often pseudorandom.** -/
theorem PseudorandomGenerator.isIoPRG {G : List Bool → List Bool} {len : ℕ → ℕ}
    (hG : PseudorandomGenerator G len) : IsIoPRG G len := by
  refine ⟨hG.polyTime, hG.length_eq, hG.stretch, fun d A hA N => ?_⟩
  have hneg := hG.indistinguishable A hA
  have hev := hneg.eventually_le_inv_polynomial
    (p := fun n => (n + 1) ^ d) (by fun_prop) (fun n => by positivity)
  rw [Filter.eventually_atTop] at hev
  obtain ⟨M, hM⟩ := hev
  refine ⟨max N M, le_max_left N M, ?_⟩
  have hle := hM (max N M) (le_max_right N M)
  simpa only [eval_prgRealGame, eval_prgIdealGame, Game.coe_advantage,
    Game.coe_succProbability, one_div, Nat.cast_pow, Nat.cast_add, Nat.cast_one] using hle

/-- **Every infinitely-often one-way function with polynomial-time output length yields an AIOWF**
(by ignoring the auxiliary string `z` except for its length). -/
theorem IsIoOWF.exists_aiOWF {f : List Bool → List Bool} {len : ℕ → ℕ}
    (hf : IsIoOWF f) (hlen : ∀ x, (f x).length = len x.length)
    (hlen_poly : ComputableInPolyTime len encUnary encUnary) :
    ∃ F : AuxInputFamily, IsAIOWF F := by
  let F : AuxInputFamily :=
    { inputLen := id
      outputLen := len
      eval := fun _ x => f x
      polyTime_inputLen := ComputableInPolyTime.id'
      polyTime_outputLen := hlen_poly
      polyTime_eval := hf.1.comp (ComputableInPolyTime.snd encBits encBits)
      length_eq := fun z x hx => by simpa [hx] using hlen x }
  refine ⟨F, fun d A hA N => ?_⟩
  let A_unif : Inverter := fun n y => A (List.replicate n false) y
  have hA_unif : IsPPT encBits A_unif := by
    have hrep : ComputableInPolyTime (fun p : ℕ × List Bool => (List.replicate p.1 false, p.2))
        (encPair encUnary encBits) (encPair encBits encBits) :=
      ((ComputableInPolyTime.bitsReplicate false).comp
        (ComputableInPolyTime.fst encUnary encBits)).prod
        (ComputableInPolyTime.snd encUnary encBits)
    exact hA.preprocess hrep
  obtain ⟨n, hNn, hlt⟩ := hf.2 d A_unif hA_unif N
  refine ⟨List.replicate n false, by simpa using hNn, ?_⟩
  simpa [F, aiInversionGame, inversionGameOn, inversionExperiment, A_unif] using hlt

/-- **Every infinitely-often PRG yields an AIPRG** (by ignoring the auxiliary string `z` except
for its length). -/
theorem IsIoPRG.exists_aiPRG {G : List Bool → List Bool} {len : ℕ → ℕ}
    (hG : IsIoPRG G len) : ∃ F : AuxInputFamily, IsAIPRG F := by
  have hlen_poly : ComputableInPolyTime len encUnary encUnary :=
    PRG.polyTime_length hG.1 hG.2.1
  let F : AuxInputFamily :=
    { inputLen := id
      outputLen := len
      eval := fun _ x => G x
      polyTime_inputLen := ComputableInPolyTime.id'
      polyTime_outputLen := hlen_poly
      polyTime_eval := hG.1.comp (ComputableInPolyTime.snd encBits encBits)
      length_eq := fun z x hx => by simpa [hx] using hG.2.1 x }
  refine ⟨F, hG.2.2.1, fun d A hA N => ?_⟩
  let A_unif : Distinguisher := fun n y => A (List.replicate n false) y
  have hA_unif : IsPPT encBool A_unif := by
    have hrep : ComputableInPolyTime (fun p : ℕ × List Bool => (List.replicate p.1 false, p.2))
        (encPair encUnary encBits) (encPair encBits encBits) :=
      ((ComputableInPolyTime.bitsReplicate false).comp
        (ComputableInPolyTime.fst encUnary encBits)).prod
        (ComputableInPolyTime.snd encUnary encBits)
    exact hA.preprocess hrep
  obtain ⟨n, hNn, hle⟩ := hG.2.2.2 d A_unif hA_unif N
  refine ⟨List.replicate n false, by simpa using hNn, ?_⟩
  simpa [F, aiPrgRealGame, aiPrgIdealGame, prgRealGame, prgIdealGame, A_unif] using hle

/-- **Every infinitely-often PRF yields an AIPRF** (by ignoring the auxiliary string `z` except
for its length). -/
theorem IsIoPRF.exists_aiPRF {f : List Bool → List Bool → Bool} (hf : IsIoPRF f) :
    ∃ F : AuxInputPRFFamily, IsAIPRF F := by
  let F : AuxInputPRFFamily :=
    { inputLen := id
      eval := fun _ u x => f u x
      polyTime_inputLen := ComputableInPolyTime.id'
      polyTime_eval := hf.1.comp (ComputableInPolyTime.snd encBits (encPair encBits encBits)) }
  refine ⟨F, fun d A hA N => ?_⟩
  let A_unif : OracleDistinguisher := fun n _ => A (List.replicate n false)
  have hA_unif : IsOraclePPT encBool A_unif := by
    have hrep : ComputableInPolyTime (fun p : ℕ × List Bool => List.replicate p.1 false)
        (encPair encUnary encBits) encBits :=
      (ComputableInPolyTime.bitsReplicate false).comp (ComputableInPolyTime.fst encUnary encBits)
    exact hA.preprocess hrep
  obtain ⟨n, hNn, hlt⟩ := hf.2 d A_unif hA_unif N
  refine ⟨List.replicate n false, by simpa using hNn, ?_⟩
  have hrep_len : (List.replicate n false).length = n := List.length_replicate
  have hreal : aiPrfRealGame F A (List.replicate n false) =
      prfRealGame id (fun u x => [f u x]) A_unif n := by
    simp only [aiPrfRealGame, prfRealGame, prfOracle, F, A_unif, id_eq, hrep_len]
  have hideal : aiPrfIdealGame F A (List.replicate n false) =
      prfIdealGame id (fun _ => 1) A_unif n := by
    have hgen : ∀ (k : ℕ), k = n →
        (do
          let table ← ProbComp.uniform (BitString k → BitString 1)
          (A (List.replicate n false)).run fun req =>
            pure (randomFunctionOracle k table req.2)) =
        prfIdealGame id (fun _ => 1) A_unif n := by
      rintro k rfl; rfl
    exact hgen _ List.length_replicate
  rw [hreal, hideal, hrep_len]
  exact hlt

end CslibFrontier.Crypto
