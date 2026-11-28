/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FormalPapers Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Complexity.Classes.Oracle.PolyTime
public import CslibFrontier.Computability.Complexity.Reduction.CountingTuring
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.IntBinary.Decode
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Rat

import CslibFrontier.Computability.Complexity.Classes.Oracle.Closure
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Rat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Configuration
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.Words
import CslibFrontier.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial.Automation
import CslibFrontier.Computability.Probabilistic.Oracle.Composition
import CslibFrontier.Foundations.Data.Nat.Bits

/-!
# Transitivity of counting Turing reductions and encoded function oracles

Uniform oracle substitution for `Cslib.Complexity.PolyTimeOracleProgram` onto arbitrary decoded
output encodings, transitivity of `Cslib.Complexity.CountingTuringReducible` and
`Cslib.Complexity.CountingTuringHard`, total polynomial-time decoding for `encRat`, and
sentinel-terminated bit-graph Turing reductions (`AnswersEncodedBits`, `FunctionTuringReducible`,
`FunctionTuringHard`) to functions with arbitrary decoded output encodings (such as `ℚ`).
-/

public section

namespace Turing.MultiTapeTM

/-- Total polynomial-time decoding map `List Bool → ℚ` inverting `encRat`. -/
def decodeRat (w : List Bool) : ℚ :=
  let p := (Decoder.intBin.pair Decoder.nat).decode w
  Rat.divInt p.1 (p.2 : ℤ)

/-- `decodeRat` inverts `encRat` on every rational number `q : ℚ`. -/
theorem decodeRat_encRat (q : ℚ) : decodeRat (encRat q) = q := by
  simp only [decodeRat, encRat_apply, encRatData, (Decoder.intBin.pair Decoder.nat).decode_enc,
    Rat.num_divInt_den]

/-- `decodeRat` is computable in polynomial time from `encBits` to `encRat`. -/
@[fun_prop]
theorem computableInPolyTime_decodeRat :
    ComputableInPolyTime decodeRat encBits encRat := by
  have hp : ComputableInPolyTime (Decoder.intBin.pair Decoder.nat).decode
      encBits (encPair encIntBin encNat) :=
    (Decoder.intBin.pair Decoder.nat).computableInPolyTime
  have hcast : ComputableInPolyTime (fun p : ℤ × ℕ ↦ (p.1, (p.2 : ℤ)))
      (encPair encIntBin encNat) (encPair encIntBin encIntBin) :=
    (ComputableInPolyTime.fst encIntBin encNat).prod
      (ComputableInPolyTime.intBin_natCast.comp (ComputableInPolyTime.snd encIntBin encNat))
  exact (ComputableInPolyTime.rat_divInt.comp hcast).comp hp

/-- Total polynomial-time `Decoder` for `encRat`. -/
def Decoder.rat : Decoder encRat where
  decode := decodeRat
  decode_enc := decodeRat_encRat
  computable := computableInPolyTime_decodeRat.exists_degree

end Turing.MultiTapeTM

namespace Cslib.Complexity

open Probability Turing.MultiTapeTM

section UniformOracleSubstitution

private def simAnswerStep {k : ℕ} {Control : Type}
    (machine : Turing.MultiTapePTM k Bool Control Unit)
    (prog : List Bool → WordQueryComp Unit Bool)
    (cfg : Turing.MultiTapeMachine.FiniteConfig k Bool Control Unit) :
    WordQueryComp Unit (Turing.MultiTapeMachine.FiniteConfig k Bool Control Unit) :=
  if (machine.pendingQuery cfg).isSome then
    (fun b ↦ machine.receiveBit (cfg, b)) <$> prog (machine.pendingRequest cfg)
  else
    pure (machine.localStep cfg)

private theorem interpret_simAnswerStep {k : ℕ} {Control : Type}
    (machine : Turing.MultiTapePTM k Bool Control Unit)
    (prog : List Bool → WordQueryComp Unit Bool)
    (cfg : Turing.MultiTapeMachine.FiniteConfig k Bool Control Unit) :
    OracleComp.interpret ProbOracleComp.query (simAnswerStep machine prog cfg) =
      if (machine.pendingQuery cfg).isSome then
        (fun b ↦ machine.receiveBit (cfg, b)) <$>
          OracleComp.interpret ProbOracleComp.query (prog (machine.pendingRequest cfg))
      else
        pure (machine.localStep cfg) := by
  unfold simAnswerStep
  split <;> simp [OracleComp.interpret_map]

private theorem isOraclePPTOn_simAnswerStep {k : ℕ} {Control : Type} [Finite Control]
    (machine : Turing.MultiTapePTM k Bool Control Unit)
    {prog : List Bool → WordQueryComp Unit Bool}
    (hprog : IsOraclePPTOn encBits encBool
      (fun w ↦ OracleComp.interpret ProbOracleComp.query (prog w))) :
    IsOraclePPTOn encFiniteConfig encFiniteConfig
      (fun cfg ↦ OracleComp.interpret ProbOracleComp.query (simAnswerStep machine prog cfg)) := by
  simp only [interpret_simAnswerStep]
  exact IsOraclePPTOn.cond
    ((ComputableInPolyTime.of_finite Option.isSome).comp machine.pendingQuery_pt)
    ((hprog.preprocess machine.pendingRequest_pt).map_with
      (f := fun cfg b ↦ machine.receiveBit (cfg, b)) machine.receiveBit_pt)
    machine.localStep_pt.isOraclePPTOn

private theorem spaceBound_of_mem_support_simAnswerStep {k : ℕ} {Control : Type}
    (machine : Turing.MultiTapePTM k Bool Control Unit)
    (prog : List Bool → WordQueryComp Unit Bool)
    {inputSize steps : ℕ}
    {cfg next : Turing.MultiTapeMachine.FiniteConfig k Bool Control Unit}
    (hcfg : Turing.MultiTapeMachine.FiniteConfig.SpaceBound inputSize steps 1 cfg)
    (hnext : next ∈ OracleComp.support
      (OracleComp.interpret ProbOracleComp.query (simAnswerStep machine prog cfg))) :
    Turing.MultiTapeMachine.FiniteConfig.SpaceBound inputSize (steps + 1) 1 next := by
  rw [interpret_simAnswerStep] at hnext
  split_ifs at hnext with hq
  · obtain ⟨b, -, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hnext
    have hstep := machine.spaceBound_answerStep (fun _ ↦ b) hcfg
    rw [machine.answerStep_bit (fun _ ↦ b)] at hstep
    simpa [hq] using hstep
  · rw [OracleComp.eq_of_mem_supportWith_pure hnext]
    have hstep := machine.spaceBound_answerStep (fun _ ↦ false) hcfg
    rw [machine.answerStep_bit (fun _ ↦ false)] at hstep
    simpa [hq] using hstep

private theorem interpret_id_simAnswerStep {k : ℕ} {Control : Type}
    (machine : Turing.MultiTapePTM k Bool Control Unit)
    {prog : List Bool → WordQueryComp Unit Bool} {A : Set (List Bool)} {g : List Bool → Bool}
    (hg : ∀ w, OracleComp.interpret (m := Id) (languageOracle A) (prog w) = g w)
    (cfg : Turing.MultiTapeMachine.FiniteConfig k Bool Control Unit) :
    OracleComp.interpret (m := Id) (languageOracle A) (simAnswerStep machine prog cfg) =
      machine.answerStep (fun q ↦ [g q.2]) cfg := by
  rw [machine.answerStep_bit]
  unfold simAnswerStep
  split_ifs with hq
  · rw [OracleComp.interpret_map, hg]
    rfl
  · rfl

/-- Uniform oracle substitution for decoded outputs. -/
theorem PolyTimeOracleProgram.subst_of_decoder {α Y : Type} {encA : α ↪ List Bool}
    {encY : Y ↪ List Bool} (DY : Decoder encY) {O₁ : Set (List Bool)} {f : α → Y}
    (hf : ComputableInPolyTimeWithOracle O₁ f encA encY)
    {Admissible : Set (List Bool) → Prop}
    (hO₁ : PolyTimeOracleProgram encBits encBool Admissible
      (fun dec ↦ ∀ w, dec w = true ↔ w ∈ O₁)) :
    PolyTimeOracleProgram encA encY Admissible (· = f) := by
  classical
  obtain ⟨outerProg, houterCert, houterSpec⟩ := hf
  obtain ⟨k, m, machine, c, d, hrun⟩ := houterCert.exists_fin_run_pure_false
  obtain ⟨innerProg, hinnerCert, hinnerSpec⟩ := hO₁
  obtain ⟨cf, hcf⟩ := length_encFiniteConfig_le (k := k) (State := Fin m) (Oracle := Unit)
  have hcount : ComputableInPolyTime (fun a ↦ c * ((encA a).length + 1) ^ d) encA encUnary :=
    ((ComputableInPolyTime.unary_eval (Polynomial.C c * (Polynomial.X + 1) ^ d)).comp
      (ComputableInPolyTime.encoding_length encA)).of_enc_eq fun a ↦ by simp
  have hinit : ComputableInPolyTime
      (fun a ↦ Turing.MultiTapeMachine.FiniteConfig.init (k := k) (Oracle := Unit)
        machine.initial (encA a))
      encA encFiniteConfig := by
    refine (((ComputableInPolyTime.of_eq fun _ ↦ rfl :
        ComputableInPolyTime encA encA encBits).prod
      (ComputableInPolyTime.const (encOut :=
        encPair (encFinite (Option (Fin m)))
          (encPair encUnary (encPair (encPi (Index := Fin k) (encBiTape encBool)) encBits)))
        (some machine.initial, 1, fun _ ↦ Cslib.Turing.BiTape.nil, []))).prod
      (ComputableInPolyTime.const
        (encOut := encPi (Index := Unit) (encPair encBits (encBiTape encBool)))
        fun _ : Unit ↦ ([], Cslib.Turing.BiTape.nil))).of_enc_eq fun a ↦ ?_
    simp [Turing.MultiTapeMachine.FiniteConfig.init, Turing.FiniteCfg.init]
  have hbound : PolyBounded (fun a ↦ (encA a).length)
      (fun a ↦ cf * ((encA a).length + c * ((encA a).length + 1) ^ d + 1 + 1)) := by growth_poly
  have hit := (IsOraclePPTOn.iterate_spec hcount hinit
    (isOraclePPTOn_simAnswerStep machine hinnerCert)
    (fun a i cfg ↦ Turing.MultiTapeMachine.FiniteConfig.SpaceBound (encA a).length i 1 cfg)
    (fun _ ↦ Turing.MultiTapeMachine.FiniteConfig.spaceBound_init _ _ _)
    (fun _ _ _ _ hinv _ hnext ↦
      spaceBound_of_mem_support_simAnswerStep machine innerProg hinv hnext)
    hbound
    (fun _ _ _ hi hinv ↦ (hcf _ _ _ _ hinv).trans (Nat.mul_le_mul_left cf (by omega)))).1
  have hpost : ComputableInPolyTime
      (fun cfg : Turing.MultiTapeMachine.FiniteConfig k Bool (Fin m) Unit ↦
        DY.decode cfg.tapes.output)
      encFiniteConfig encY :=
    DY.computableInPolyTime.comp (by fun_prop)
  refine ⟨fun a ↦ (fun cfg ↦ DY.decode cfg.tapes.output) <$>
      OracleComp.iterate (c * ((encA a).length + 1) ^ d) (simAnswerStep machine innerProg)
        (Turing.MultiTapeMachine.FiniteConfig.init machine.initial (encA a)),
    ?_, fun A hA ↦ funext fun a ↦ ?_⟩
  · simp only [OracleComp.interpret_map, OracleComp.interpret_iterate]
    exact hit.map hpost
  · have hg : ∀ w, OracleComp.interpret (m := Id) (languageOracle A) (innerProg w) =
        decide (w ∈ O₁) := fun w ↦
      Bool.eq_iff_iff.mpr (by simpa only [decide_eq_true_eq] using hinnerSpec A hA w)
    rw [OracleComp.interpret_map, OracleComp.interpret_id_iterate]
    simp only [interpret_id_simAnswerStep machine hg]
    have hans : (fun q : Unit × List Bool ↦ [decide (q.2 ∈ O₁)]) = languageOracle O₁ := by
      funext q; simp [languageOracle]
    rw [hans]
    change DY.decode (((machine.answerStep (languageOracle O₁))^[c * ((encA a).length + 1) ^ d]
      (Turing.MultiTapeMachine.FiniteConfig.init machine.initial (encA a))).tapes.output) = f a
    rw [← machine.interpret_run_pure_false, hrun a (languageOracle O₁), houterSpec a]
    exact DY.decode_enc (f a)

end UniformOracleSubstitution

section CountingTuringClosure

variable {α β γ Z : Type}

/-- Uniformly deciding `bitGraph encB g` from any oracle program computing `g : β → ℕ`. -/
theorem bitGraph_polyTimeOracleProgram {encB : β ↪ List Bool} (DB : Decoder encB) {g : β → ℕ}
    {Admissible : Set (List Bool) → Prop}
    (hg : PolyTimeOracleProgram encB encNat Admissible (· = g)) :
    PolyTimeOracleProgram encBits encBool Admissible
      (fun dec ↦ ∀ w, dec w = true ↔ w ∈ bitGraph encB g) := by
  obtain ⟨gProg, hgCert, hgSpec⟩ := hg
  let D' := DB.pair Decoder.nat
  have hdec : ComputableInPolyTime D'.decode encBits (encPair encB encNat) :=
    D'.computableInPolyTime
  have hb : ComputableInPolyTime (fun w ↦ (D'.decode w).1) encBits encB :=
    (ComputableInPolyTime.fst _ _).comp hdec
  have hcheck : ComputableInPolyTime (fun w ↦ decide (encPair encB encNat (D'.decode w) = w))
      encBits encBool := by
    have henc : ComputableInPolyTime (fun w ↦ encPair encB encNat (D'.decode w)) encBits encBits :=
      (ComputableInPolyTime.id' (encIn := encPair encB encNat)).encoding_comp.comp hdec
    exact ComputableInPolyTime.decide_eq' henc ComputableInPolyTime.id'
  have hpost : ComputableInPolyTime
      (fun p : List Bool × ℕ ↦
        decide (encPair encB encNat (D'.decode p.1) = p.1) &&
          p.2.testBit (min p.2.size (D'.decode p.1).2))
      (encPair encBits encNat) encBool := by
    have hsize : ComputableInPolyTime (fun p : List Bool × ℕ ↦ p.2.size)
        (encPair encBits encNat) encUnary := by
      have hbits := (ComputableInPolyTime.of_eq (encIn := encNat) (encOut := encBits)
        (f := Nat.bits) fun _ ↦ rfl).comp (ComputableInPolyTime.snd encBits encNat)
      simpa only [Function.comp_def, Nat.size_eq_bits_len] using
        ComputableInPolyTime.length_bits_comp hbits
    have hidx : ComputableInPolyTime
        (fun p : List Bool × ℕ ↦ min p.2.size (D'.decode p.1).2)
        (encPair encBits encNat) encUnary :=
      ComputableInPolyTime.binary_min_unary' hsize
        (((ComputableInPolyTime.snd _ _).comp hdec).comp (ComputableInPolyTime.fst _ _))
    have htb := ComputableInPolyTime.binary_testBit (ComputableInPolyTime.snd encBits encNat) hidx
    exact ComputableInPolyTime.bool_and.comp
      ((hcheck.comp (ComputableInPolyTime.fst _ _)).prod htb)
  refine ⟨fun w ↦
      (fun val ↦ decide (encPair encB encNat (D'.decode w) = w) &&
        val.testBit (min val.size (D'.decode w).2)) <$> gProg (D'.decode w).1,
    ?_, fun A hA w ↦ ?_⟩
  · simp only [OracleComp.interpret_map]
    exact (hgCert.preprocess hb).map_with hpost
  · dsimp only
    rw [OracleComp.interpret_map]
    have hgw : OracleComp.interpret (m := Id) (languageOracle A) (gProg (D'.decode w).1) =
        g (D'.decode w).1 := congrFun (hgSpec A hA) (D'.decode w).1
    rw [hgw]
    have hmin (n i : ℕ) : n.testBit (min n.size i) = n.testBit i := by
      rcases le_total i n.size with h | h
      · rw [min_eq_right h]
      · rw [min_eq_left h, Nat.testBit_lt_two_pow (Nat.lt_size_self n),
          Nat.testBit_lt_two_pow ((Nat.lt_size_self n).trans_le
            (Nat.pow_le_pow_right two_pos h))]
    change (decide (encPair encB encNat (D'.decode w) = w) &&
      (g (D'.decode w).1).testBit (min (g (D'.decode w).1).size (D'.decode w).2)) = true ↔
      w ∈ bitGraph encB g
    rw [hmin, Bool.and_eq_true, decide_eq_true_eq]
    simp only [bitGraph, Set.mem_image]
    refine ⟨fun ⟨hw, hbit⟩ ↦ ⟨D'.decode w, hbit, hw⟩, ?_⟩
    rintro ⟨x, hx, rfl⟩
    rw [D'.decode_enc]
    exact ⟨rfl, hx⟩

/-- Transitivity of `CountingTuringReducible` through a decoded encoding `encB`. -/
theorem CountingTuringReducible.trans {encA : α ↪ List Bool} {encB : β ↪ List Bool}
    {encC : γ ↪ List Bool} (DB : Decoder encB) {f : α → ℕ} {g : β → ℕ} {h : γ → ℕ}
    (hfg : CountingTuringReducible encA encB f g)
    (hgh : CountingTuringReducible encB encC g h) :
    CountingTuringReducible encA encC f h := by
  obtain ⟨f', hf', rfl⟩ :=
    hfg.exists_computableInPolyTimeWithOracle (answersBits_bitGraph encB g)
  exact PolyTimeOracleProgram.subst_of_decoder Decoder.nat hf'
    (bitGraph_polyTimeOracleProgram DB hgh)

/-- Transfer of `CountingTuringHard` along a counting Turing reduction. -/
theorem CountingTuringHard.trans {encB : β ↪ List Bool} {encC : γ ↪ List Bool}
    (DB : Decoder encB) {g : β → ℕ} {h : γ → ℕ}
    (hg : CountingTuringHard encB g) (hgh : CountingTuringReducible encB encC g h) :
    CountingTuringHard encC h := fun _ encA f hf ↦
  (hg encA f hf).trans DB hgh

/-- Sentinel-terminated natural encoding `ofBits (encZ z ++ [true])`. -/
def encodeWordSentinelNat (encZ : Z ↪ List Bool) (z : Z) : ℕ :=
  ofBits (encZ z ++ [true])

/-- Recover the original bit word from `encodeWordSentinelNat`. -/
def decodeWordSentinelNat (n : ℕ) : List Bool :=
  n.bits.reverse.tail.reverse

@[simp]
theorem decodeWordSentinelNat_ofBits_append_true (w : List Bool) :
    decodeWordSentinelNat (ofBits (w ++ [true])) = w := by
  have hrdrop : (w ++ [true]).rdropWhile (!·) = w ++ [true] := by
    rw [List.rdropWhile_concat]
    simp
  simp [decodeWordSentinelNat, bits_ofBits, hrdrop]

@[simp]
theorem decode_decodeWordSentinelNat_encodeWordSentinelNat {encZ : Z ↪ List Bool}
    (DZ : Decoder encZ) (z : Z) :
    DZ.decode (decodeWordSentinelNat (encodeWordSentinelNat encZ z)) = z := by
  simp [encodeWordSentinelNat, DZ.decode_enc]

theorem size_encodeWordSentinelNat_le (encZ : Z ↪ List Bool) (z : Z) :
    (encodeWordSentinelNat encZ z).size ≤ (encZ z).length + 1 := by
  rw [← Nat.size_eq_bits_len, ← encNat_apply, encodeWordSentinelNat]
  exact (length_encNat_ofBits_le (encZ z ++ [true])).trans (by simp)

@[fun_prop]
theorem computableInPolyTime_decodeWordSentinelNat :
    ComputableInPolyTime decodeWordSentinelNat encNat encBits := by
  have hbits : ComputableInPolyTime Nat.bits encNat encBits :=
    ComputableInPolyTime.of_eq (encIn := encNat) (encOut := encBits) (f := Nat.bits) fun _ ↦ rfl
  exact ComputableInPolyTime.bitsReverse.comp
    (ComputableInPolyTime.bitsTail.comp (ComputableInPolyTime.bitsReverse.comp hbits))

theorem computableInPolyTime_encodeWordSentinelNat (encZ : Z ↪ List Bool) :
    ComputableInPolyTime (encodeWordSentinelNat encZ) encZ encNat := by
  have hw : ComputableInPolyTime (fun z : Z ↦ encZ z ++ [true]) encZ encBits :=
    ComputableInPolyTime.bitsAppend
      (ComputableInPolyTime.of_eq (encIn := encZ) (encOut := encBits) (f := encZ) fun _ ↦ rfl)
      (ComputableInPolyTime.const [true])
  exact ComputableInPolyTime.bitsToNat.comp hw

/-- Oracle language answering the sentinel-terminated bit-graph of `g : β → Z`. -/
def AnswersEncodedBits (encB : β ↪ List Bool) (encZ : Z ↪ List Bool) (g : β → Z)
    (A : Set (List Bool)) : Prop :=
  AnswersBits encB (encodeWordSentinelNat encZ ∘ g) A

/-- Polynomial-time Turing reduction to a function `g : β → Z` with output encoding `encZ`. -/
def FunctionTuringReducible {Y : Type} (encA : α ↪ List Bool) (encB : β ↪ List Bool)
    (encY : Y ↪ List Bool) (encZ : Z ↪ List Bool) (f : α → Y) (g : β → Z) : Prop :=
  PolyTimeOracleProgram encA encY (AnswersEncodedBits encB encZ g) (· = f)

/-- `#P`-hardness under polynomial-time Turing reductions for `g : β → Z`. -/
def FunctionTuringHard (encB : β ↪ List Bool) (encZ : Z ↪ List Bool) (g : β → Z) : Prop :=
  ∀ ⦃α : Type⦄ (encA : α ↪ List Bool) (f : α → ℕ),
    f ∈ SharpP encA → FunctionTuringReducible encA encB encNat encZ f g

/-- Batch non-adaptive constructor for `FunctionTuringReducible`. -/
theorem PolyTimeOracleProgram.of_batchEncodedBits {encA : α ↪ List Bool} {encB : β ↪ List Bool}
    {encZ : Z ↪ List Bool} (DZ : Decoder encZ) {f : α → ℕ} {g : β → Z}
    (queries : α → List β) (bound : α → ℕ) (combine : α × List Z → ℕ)
    (hqueries : ComputableInPolyTime queries encA (encList encB))
    (hbound : ComputableInPolyTime bound encA encUnary)
    (hcombine : ComputableInPolyTime combine (encPair encA (encList encZ)) encNat)
    (hlen : ∀ a, ∀ b ∈ queries a, (encZ (g b)).length + 1 ≤ bound a)
    (hspec : ∀ a, combine (a, (queries a).map g) = f a) :
    FunctionTuringReducible encA encB encNat encZ f g := by
  let decOne : ℕ → Z := fun n ↦ DZ.decode (decodeWordSentinelNat n)
  have hdecOne : ComputableInPolyTime decOne encNat encZ :=
    DZ.computableInPolyTime.comp computableInPolyTime_decodeWordSentinelNat
  let combineNat : α × List ℕ → ℕ := fun p ↦ combine (p.1, p.2.map decOne)
  have hcombineNat : ComputableInPolyTime combineNat (encPair encA (encList encNat)) encNat :=
    hcombine.comp ((ComputableInPolyTime.fst _ _).prod
      ((ComputableInPolyTime.map hdecOne).comp (ComputableInPolyTime.snd _ _)))
  exact PolyTimeOracleProgram.of_batchNatBits queries bound combineNat
    hqueries hbound hcombineNat
    (fun a b hb ↦ (size_encodeWordSentinelNat_le encZ (g b)).trans (hlen a b hb))
    (fun a ↦ by
      simp only [combineNat, List.map_map, Function.comp_def, decOne,
        decode_decodeWordSentinelNat_encodeWordSentinelNat DZ, hspec a])

/-- Transfer `CountingTuringHard` to an encoded function problem `h : γ → Z`. -/
theorem CountingTuringHard.trans_functionTuring {encB : β ↪ List Bool} {encC : γ ↪ List Bool}
    {encZ : Z ↪ List Bool} (DB : Decoder encB) {g : β → ℕ} {h : γ → Z}
    (hg : CountingTuringHard encB g)
    (hgh : FunctionTuringReducible encB encC encNat encZ g h) :
    FunctionTuringHard encC encZ h := by
  intro α encA f hf
  obtain ⟨f', hf', rfl⟩ :=
    (hg encA f hf).exists_computableInPolyTimeWithOracle (answersBits_bitGraph encB g)
  exact PolyTimeOracleProgram.subst_of_decoder Decoder.nat hf'
    (bitGraph_polyTimeOracleProgram DB hgh)

/-- Polynomial-time collapse for `FunctionTuringHard`. -/
theorem FunctionTuringHard.computableInPolyTime_collapse {encB : β ↪ List Bool}
    {encZ : Z ↪ List Bool} (DB : Decoder encB) {h : β → Z}
    (hhard : FunctionTuringHard encB encZ h)
    (hpoly : ComputableInPolyTime h encB encZ)
    {encA : α ↪ List Bool} {f : α → ℕ} (hf : f ∈ SharpP encA) :
    ComputableInPolyTime f encA encNat := by
  have hred : CountingTuringReducible encA encB f (encodeWordSentinelNat encZ ∘ h) :=
    hhard encA f hf
  exact hred.computableInPolyTime_of_decoder DB
    ((computableInPolyTime_encodeWordSentinelNat encZ).comp hpoly)

end CountingTuringClosure

end Cslib.Complexity
