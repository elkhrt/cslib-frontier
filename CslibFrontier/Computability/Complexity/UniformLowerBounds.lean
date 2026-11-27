module

public import CslibFrontier.Computability.Complexity.Classes.NP
public import CslibFrontier.Computability.Complexity.Classes.P
public import CslibFrontier.Computability.Complexity.Classes.Time
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat
public import CslibFrontier.Foundations.Data.BitString.List.Binary
public import Mathlib.Computability.Language
public import CslibFrontier.Computability.Circuit.NondeterministicCircuit
public import CslibFrontier.Computability.Complexity.NoComplementarySpeedup
import CslibFrontier.Computability.Circuit.Boolean.Encoding.Certificate
import CslibFrontier.Computability.Circuit.Encoding.Basic
import CslibFrontier.Computability.Circuit.Encoding.Layer
import CslibFrontier.Computability.Complexity.Classes.Constructible
import CslibFrontier.Computability.Complexity.Classes.Constructible.Log
import CslibFrontier.Computability.Complexity.Classes.Time.Verifier
import CslibFrontier.Computability.Complexity.Reduction
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Constructible
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Sqrt
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.OfBits
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.WordsRoundTrip
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.EqualityPrimitives
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeNatFrontends
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimePrimitives
import CslibFrontier.Foundations.Data.Nat.PolynomialBound.Exponential
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Padded Direct Connect Languages and Uniform Co-Nondeterministic Circuit Lower Bounds

This module defines padded direct connect languages (`pDCL`, `nDCL`) for `P`-uniform
nondeterministic circuit families and proves the unconditional uniform lower bound
`NP ⊈ P-uniform coNSIZE[O(n^k)]` following Santhanam–Williams.

## Main definitions

* `CslibFrontier.Computability.Complexity.padRoot`: iterated integer square root `⌊n^{1/2^r}⌋`.
* `CslibFrontier.Computability.Complexity.certEncode`: fixed-length certificate encoding of a
  `WitnessCircuit`.
* `CslibFrontier.Computability.Complexity.pDCL`, `CslibFrontier.Computability.Complexity.nDCL`:
  positive
  and negative padded direct connect languages.

## Main results

* `CslibFrontier.Computability.Complexity.pDCL_mem_P`,
  `CslibFrontier.Computability.Complexity.nDCL_mem_P`:
  padded direct connect languages of `P`-uniform circuit families lie in `P`.
* `CslibFrontier.Computability.Complexity.not_coNP_subset_PUniformNSIZE`,
  `CslibFrontier.Computability.Complexity.not_NP_subset_PUniformCoNSIZE`: for every `k ≥ 1`,
  `NP` is not contained in `P`-uniform `coNSIZE[O(n^k)]`.
-/

public section

namespace CslibFrontier.Computability.Complexity

open Cslib Cslib.Complexity Cslib.Circuits Cslib.Circuits.Boolean
open CslibFrontier.Computability.Circuit
open Turing Turing.MultiTapeTM Filter

/-! ### Part 2: Padded Direct Connect Languages (`pDCL`, `nDCL`) -/

/-- Iterated integer square root `⌊n^{1/2^r}⌋`, a constructive sublinear padding function. -/
@[expose] def padRoot (r n : ℕ) : ℕ := Nat.sqrt^[r] n

@[simp] theorem padRoot_zero (n : ℕ) : padRoot 0 n = n := rfl

@[simp] theorem padRoot_succ (r n : ℕ) : padRoot (r + 1) n = Nat.sqrt (padRoot r n) :=
  Function.iterate_succ_apply' Nat.sqrt r n

lemma padRoot_pow_le (r n : ℕ) : (padRoot r n) ^ (2 ^ r) ≤ n := by
  induction r generalizing n with
  | zero => simp [padRoot]
  | succ r ih =>
    simp only [padRoot, Function.iterate_succ_apply]
    calc (Nat.sqrt^[r] (Nat.sqrt n)) ^ 2 ^ (r + 1)
        = ((Nat.sqrt^[r] (Nat.sqrt n)) ^ 2 ^ r) ^ 2 := by rw [pow_succ, pow_mul]
      _ ≤ (Nat.sqrt n) ^ 2 := Nat.pow_le_pow_left (ih (Nat.sqrt n)) 2
      _ ≤ n := by simpa [sq] using Nat.sqrt_le n

lemma lt_padRoot_succ_pow (r n : ℕ) : n < (padRoot r n + 1) ^ (2 ^ r) := by
  induction r generalizing n with
  | zero => simp [padRoot]
  | succ r ih =>
    simp only [padRoot, Function.iterate_succ_apply]
    have h1 : Nat.sqrt n + 1 ≤ (Nat.sqrt^[r] (Nat.sqrt n) + 1) ^ 2 ^ r := ih (Nat.sqrt n)
    have h2 : n < (Nat.sqrt n + 1) ^ 2 := by simpa [sq] using Nat.lt_succ_sqrt n
    calc n < (Nat.sqrt n + 1) ^ 2 := h2
      _ ≤ ((Nat.sqrt^[r] (Nat.sqrt n) + 1) ^ 2 ^ r) ^ 2 := Nat.pow_le_pow_left h1 2
      _ = (Nat.sqrt^[r] (Nat.sqrt n) + 1) ^ 2 ^ (r + 1) := by rw [← pow_mul, pow_succ]

/-- Fixed-length certificate encoding of a witness circuit `c : WitnessCircuit n`. -/
def certEncode {n : ℕ} (c : WitnessCircuit n) : List Bool :=
  Boolean.certificate (n + c.witnessLen) c.size c.circuit.code.1 (c.circuit.outputs 0).toNat

/-- Positive `m`-padded direct connect language for a witness-circuit family `gen`. -/
def pDCL (gen : ℕ → Σ n, WitnessCircuit n) (m : ℕ → ℕ) : Language Bool :=
  {w | ∃ n i,
    w = encPair encNat encBits (n, BitString.lowBits (m n) i) ∧
    i < 2 ^ m n ∧
    i < (certEncode (gen n).2).length ∧
    (certEncode (gen n).2).getD i false = true}

/-- Negative `m`-padded direct connect language for a witness-circuit family `gen`. -/
def nDCL (gen : ℕ → Σ n, WitnessCircuit n) (m : ℕ → ℕ) : Language Bool :=
  {w | ∃ n i,
    w = encPair encNat encBits (n, BitString.lowBits (m n) i) ∧
    i < 2 ^ m n ∧
    i < (certEncode (gen n).2).length ∧
    (certEncode (gen n).2).getD i false = false}

private lemma padRoot_le (r n : ℕ) : padRoot r n ≤ n := by
  induction r generalizing n with
  | zero => simp [padRoot]
  | succ r ih =>
    simp only [padRoot, Function.iterate_succ_apply]
    exact (ih (Nat.sqrt n)).trans (Nat.sqrt_le_self n)

private lemma computableInPolyTime_padRoot (r : ℕ) :
    ComputableInPolyTime (padRoot r) encNat encNat := by
  induction r with
  | zero =>
    change ComputableInPolyTime (fun n => n) encNat encNat
    exact ComputableInPolyTime.id'
  | succ r ih =>
    have : padRoot (r + 1) = fun n => padRoot r (Nat.sqrt n) := by
      funext n; simp [padRoot, Function.iterate_succ_apply]
    rw [this]; exact ih.comp ComputableInPolyTime.binary_sqrt

private lemma computableInPolyTime_unaryField {α : Type} {enc : α ↪ List Bool}
    {w v : α → ℕ}
    (hw : ComputableInPolyTime w enc encUnary)
    (hv : ComputableInPolyTime v enc encUnary) :
    ComputableInPolyTime (fun a => Boolean.unaryField (w a) (v a)) enc encBits := by
  unfold Boolean.unaryField; exact ComputableInPolyTime.bitsAppend
    (ComputableInPolyTime.bitsReplicate true |>.comp hv)
    (ComputableInPolyTime.bitsReplicate false |>.comp (ComputableInPolyTime.unary_sub' hw hv))

private lemma computableInPolyTime_certEncode {α : Type} {enc : α ↪ List Bool}
    {gen : α → Σ n, WitnessCircuit n}
    (hgen : ComputableInPolyTime gen enc WitnessCircuit.encWitnessCircuit) :
    ComputableInPolyTime (fun a => certEncode (gen a).2) enc encBits := by
  let unpack : (Σ n, WitnessCircuit n) →
      ℕ × (ℕ × (List (Boolean.Op × List ℕ) × List ℕ)) :=
    fun p => (p.1, (p.1 + p.2.witnessLen, p.2.circuit.code))
  have hunpack : ComputableInPolyTime unpack WitnessCircuit.encWitnessCircuit
      (encPair encUnary (encPair encUnary (encPair (encList encGate) (encList encNat)))) :=
    (ComputableInPolyTime.id' (encIn := WitnessCircuit.encWitnessCircuit)).of_enc_eq fun p => by
      dsimp only [unpack]
      rw [WitnessCircuit.encWitnessCircuit_apply]
      simp only [encPair_apply, encCircuit_apply]
  have hcur := hunpack.comp hgen
  have h1 : ComputableInPolyTime (fun a => (gen a).1) enc encUnary :=
    (ComputableInPolyTime.fst _ _).comp hcur
  have h2 : ComputableInPolyTime (fun a => (gen a).1 + (gen a).2.witnessLen) enc encUnary :=
    (ComputableInPolyTime.fst _ _).comp ((ComputableInPolyTime.snd _ _).comp hcur)
  have hcode : ComputableInPolyTime (fun a => (gen a).2.circuit.code) enc
      (encPair (encList encGate) (encList encNat)) :=
    (ComputableInPolyTime.snd _ _).comp ((ComputableInPolyTime.snd _ _).comp hcur)
  have hgates : ComputableInPolyTime (fun a => (gen a).2.circuit.code.1) enc (encList encGate) :=
    (ComputableInPolyTime.fst _ _).comp hcode
  have houts : ComputableInPolyTime (fun a => (gen a).2.circuit.code.2) enc (encList encNat) :=
    (ComputableInPolyTime.snd _ _).comp hcode
  have hglen : ComputableInPolyTime (fun a => (gen a).2.circuit.code.1.length) enc encUnary :=
    (ComputableInPolyTime.length_list encGate).comp hgates
  have hwlen : ComputableInPolyTime (fun a => (gen a).2.witnessLen) enc encUnary := by
    have := ComputableInPolyTime.unary_sub' h2 h1
    simpa [Nat.add_sub_cancel_left] using this
  have hs : ComputableInPolyTime (fun a => (gen a).2.size) enc encUnary := by
    have hmax := ComputableInPolyTime.unary_max.comp (hglen.prod hwlen)
    convert hmax using 1
    funext a
    dsimp only [Function.comp_apply]; rw [WitnessCircuit.size_eq, Circuit.length_code_fst]
  have hwidth : ComputableInPolyTime (fun a => (gen a).1 + (gen a).2.witnessLen + (gen a).2.size)
      enc encUnary :=
    ComputableInPolyTime.unary_add' h2 hs
  have hout_nat :
    ComputableInPolyTime (fun a => ((gen a).2.circuit.outputs 0).toNat) enc encNat := by
    have hhd := (ComputableInPolyTime.headD (encA := encNat) (encL := encList encNat) 0).comp houts
    convert hhd using 1
    funext a
    simp [Circuit.code]
  have hout_u : ComputableInPolyTime (fun a => ((gen a).2.circuit.outputs 0).toNat) enc encUnary :=
    ComputableInPolyTime.binary_to_unary_bounded hout_nat hwidth fun a => by
      have := ((gen a).2.circuit.outputs 0).toNat_lt
      have : (gen a).2.circuit.size ≤ (gen a).2.size := le_max_left _ _
      omega
  have hgateRow : ComputableInPolyTime
      (fun p : α × (Boolean.Op × List ℕ) =>
        Boolean.gateRow ((gen p.1).1 + (gen p.1).2.witnessLen + (gen p.1).2.size)
          (p.2.1, [min (p.2.2.getD 0 0) ((gen p.1).1 + (gen p.1).2.witnessLen + (gen p.1).2.size),
                   min (p.2.2.getD 1 0) ((gen p.1).1 + (gen p.1).2.witnessLen + (gen p.1).2.size)]))
      (encPair enc encGate) encBits := by
    have hp1 : ComputableInPolyTime (fun p : α × (Boolean.Op × List ℕ) =>
        (gen p.1).1 + (gen p.1).2.witnessLen + (gen p.1).2.size) (encPair enc encGate) encUnary :=
      hwidth.comp (ComputableInPolyTime.fst _ _)
    have hop : ComputableInPolyTime (fun p : α × (Boolean.Op × List ℕ) => p.2.1.bits)
        (encPair enc encGate) encBits :=
      (ComputableInPolyTime.of_finite Boolean.Op.bits).comp
        ((ComputableInPolyTime.fst _ _).comp (ComputableInPolyTime.snd enc encGate))
    have hargs : ComputableInPolyTime (fun p : α × (Boolean.Op × List ℕ) => p.2.2)
        (encPair enc encGate) (encList encNat) :=
      (ComputableInPolyTime.snd _ _).comp (ComputableInPolyTime.snd enc encGate)
    have ha0_n : ComputableInPolyTime (fun p : α × (Boolean.Op × List ℕ) => p.2.2.getD 0 0)
        (encPair enc encGate) encNat := by
      have := (ComputableInPolyTime.headD (encA := encNat) (encL := encList encNat) 0).comp hargs
      convert this using 1; funext p; rcases p with ⟨a, op, args⟩; cases args <;> rfl
    have ha1_n : ComputableInPolyTime (fun p : α × (Boolean.Op × List ℕ) => p.2.2.getD 1 0)
        (encPair enc encGate) encNat := by
      have := (ComputableInPolyTime.headD (encA := encNat) (encL := encList encNat) 0).comp
        ((ComputableInPolyTime.listTail encNat).comp hargs)
      convert this using 1; funext p; rcases p with ⟨a, op, args⟩
      cases args with
      | nil => rfl
      | cons _ tl => cases tl <;> rfl
    have ha0 : ComputableInPolyTime (fun p : α × (Boolean.Op × List ℕ) =>
        min ((gen p.1).1 + (gen p.1).2.witnessLen + (gen p.1).2.size) (p.2.2.getD 0 0))
        (encPair enc encGate) encUnary :=
      ComputableInPolyTime.binary_min_unary' hp1 ha0_n
    have ha1 : ComputableInPolyTime (fun p : α × (Boolean.Op × List ℕ) =>
        min ((gen p.1).1 + (gen p.1).2.witnessLen + (gen p.1).2.size) (p.2.2.getD 1 0))
        (encPair enc encGate) encUnary :=
      ComputableInPolyTime.binary_min_unary' hp1 ha1_n
    have hrow : ComputableInPolyTime
        (fun p : α × (Boolean.Op × List ℕ) =>
          p.2.1.bits ++
            Boolean.unaryField ((gen p.1).1 + (gen p.1).2.witnessLen + (gen p.1).2.size)
              (min ((gen p.1).1 + (gen p.1).2.witnessLen + (gen p.1).2.size) (p.2.2.getD 0 0)) ++
            Boolean.unaryField ((gen p.1).1 + (gen p.1).2.witnessLen + (gen p.1).2.size)
              (min ((gen p.1).1 + (gen p.1).2.witnessLen + (gen p.1).2.size) (p.2.2.getD 1 0)))
        (encPair enc encGate) encBits :=
      ComputableInPolyTime.bitsAppend
        (ComputableInPolyTime.bitsAppend hop (computableInPolyTime_unaryField hp1 ha0))
        (computableInPolyTime_unaryField hp1 ha1)
    convert hrow using 1
    funext p
    simp [Boolean.gateRow, Nat.min_comm]
  have hflat : ComputableInPolyTime
      (fun a => ((gen a).2.circuit.code.1).flatMap
        (fun g => Boolean.gateRow ((gen a).1 + (gen a).2.witnessLen + (gen a).2.size) g))
      enc encBits := by
    let fRow : α → (Boolean.Op × List ℕ) → List Bool := fun a g =>
      Boolean.gateRow ((gen a).1 + (gen a).2.witnessLen + (gen a).2.size)
        (g.1, [min (g.2.getD 0 0) ((gen a).1 + (gen a).2.witnessLen + (gen a).2.size),
               min (g.2.getD 1 0) ((gen a).1 + (gen a).2.witnessLen + (gen a).2.size)])
    have hfm := ComputableInPolyTime.flatMapToBitsWithInput (f := fRow) hgates hgateRow
    convert hfm using 1
    funext a
    refine List.flatMap_congr fun g hg => ?_
    have hle : ∀ i ∈ g.2, i ≤ (gen a).1 + (gen a).2.witnessLen + (gen a).2.size := by
      intro i hi
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
      have hlt := (((gen a).2.circuit.isCodeFrom_code).getElem j hj).2 i hi
      have hj' : j < (gen a).2.circuit.size := Circuit.length_code_fst _ ▸ hj
      have hs' : (gen a).2.circuit.size ≤ (gen a).2.size := le_max_left _ _
      omega
    have hgetD : ∀ idx, g.2.getD idx 0 ≤ (gen a).1 + (gen a).2.witnessLen + (gen a).2.size := by
      intro idx; cases h : g.2[idx]? with
      | none => simp [List.getD, h]
      | some v =>
        simp only [List.getD, h, Option.getD_some]; exact hle v (List.mem_of_getElem? h)
    have h0 := hgetD 0
    have h1' := hgetD 1
    dsimp only [fRow]; rw [Nat.min_eq_left h0, Nat.min_eq_left h1']
    cases h : g.2 with
    | nil => simp [Boolean.gateRow, List.getD, h]
    | cons v0 tl =>
      cases tl with
      | nil => simp [Boolean.gateRow, List.getD, h]
      | cons v1 _ => simp [Boolean.gateRow, List.getD, h]
  have hpad_len : ComputableInPolyTime
      (fun a => ((gen a).2.size - (gen a).2.circuit.code.1.length) *
        (3 + 2 * ((gen a).1 + (gen a).2.witnessLen + (gen a).2.size))) enc encUnary :=
    ComputableInPolyTime.unary_mul'
      (ComputableInPolyTime.unary_sub' hs hglen)
      (ComputableInPolyTime.unary_add' (ComputableInPolyTime.const 3)
        (ComputableInPolyTime.unary_mul' (ComputableInPolyTime.const 2) hwidth))
  have hcert : ComputableInPolyTime
      (fun a => Boolean.unaryField (gen a).2.size (gen a).2.circuit.code.1.length ++
        Boolean.unaryField ((gen a).1 + (gen a).2.witnessLen + (gen a).2.size)
          ((gen a).2.circuit.outputs 0).toNat ++
        ((gen a).2.circuit.code.1).flatMap
          (Boolean.gateRow ((gen a).1 + (gen a).2.witnessLen + (gen a).2.size)) ++
        List.replicate (((gen a).2.size - (gen a).2.circuit.code.1.length) *
          (3 + 2 * ((gen a).1 + (gen a).2.witnessLen + (gen a).2.size))) false)
      enc encBits :=
    ComputableInPolyTime.bitsAppend
      (ComputableInPolyTime.bitsAppend
        (ComputableInPolyTime.bitsAppend
          (computableInPolyTime_unaryField hs hglen)
          (computableInPolyTime_unaryField hwidth hout_u))
        hflat)
      ((ComputableInPolyTime.bitsReplicate false).comp hpad_len)
  exact hcert

/-- Unified polynomial-time decision procedure for both `pDCL` (`bit = true`) and
`nDCL` (`bit = false`). -/
private lemma dcl_mem_P (gen : ℕ → Σ n, WitnessCircuit n)
    (hpoly : ComputableInPolyTime gen encUnary WitnessCircuit.encWitnessCircuit)
    (r : ℕ) (bit : Bool) :
    {w | ∃ n i,
      w = encPair encNat encBits (n, BitString.lowBits (padRoot r n) i) ∧
      i < 2 ^ padRoot r n ∧
      i < (certEncode (gen n).2).length ∧
      (certEncode (gen n).2).getD i false = bit} ∈ P encBits := by
  let u : List Bool → List Bool := dropFrame
  let cap : List Bool → ℕ := fun w => ((u w).length + 1) ^ (2 ^ r)
  let nCand : List Bool → ℕ := fun w => BitString.boundedBinaryValue (cap w) (unframe w).reverse
  let cert : List Bool → List Bool := fun w => certEncode (gen (nCand w)).2
  let iCand : List Bool → ℕ := fun w => BitString.boundedBinaryValue (cert w).length (u w).reverse
  let dec : List Bool → Bool := fun w =>
    (frame (encNat (nCand w)) ++ u w == w) &&
    ((u w).length == padRoot r (nCand w)) &&
    decide (iCand w < (cert w).length) &&
    ((cert w).getD (iCand w) false == bit)
  have hu_pt : ComputableInPolyTime u encBits encBits := ComputableInPolyTime.dropFrame
  have hulen : ComputableInPolyTime (fun w => (u w).length) encBits encUnary :=
    ComputableInPolyTime.length_bits.comp hu_pt
  have hcap : ComputableInPolyTime cap encBits encUnary :=
    (ComputableInPolyTime.unary_pow (2 ^ r)).comp
      (ComputableInPolyTime.unary_add' hulen (ComputableInPolyTime.const 1))
  have hnCand : ComputableInPolyTime nCand encBits encUnary :=
    ComputableInPolyTime.bitsBoundedBinaryValueWithInput hcap
      (ComputableInPolyTime.bitsReverse.comp ComputableInPolyTime.unframe)
  have hnCand_bin : ComputableInPolyTime nCand encBits encNat :=
    ComputableInPolyTime.unary_to_binary.comp hnCand
  have hframe_n : ComputableInPolyTime (fun w => frame (encNat (nCand w))) encBits encBits :=
    (ComputableInPolyTime.bitsFrame encNat).comp hnCand_bin
  have hcert_pt : ComputableInPolyTime cert encBits encBits :=
    (computableInPolyTime_certEncode hpoly).comp hnCand
  have hcert_len : ComputableInPolyTime (fun w => (cert w).length) encBits encUnary :=
    ComputableInPolyTime.length_bits.comp hcert_pt
  have hiCand : ComputableInPolyTime iCand encBits encUnary :=
    ComputableInPolyTime.bitsBoundedBinaryValueWithInput hcert_len
      (ComputableInPolyTime.bitsReverse.comp hu_pt)
  have hpad_u : ComputableInPolyTime (fun w => padRoot r (nCand w)) encBits encUnary :=
    ComputableInPolyTime.binary_to_unary_bounded
      ((computableInPolyTime_padRoot r).comp hnCand_bin) hnCand (fun w => padRoot_le r (nCand w))
  have hdec_pt : ComputableInPolyTime dec encBits encBool := by
    have hc1 :
      ComputableInPolyTime (fun w => frame (encNat (nCand w)) ++ u w == w) encBits encBool :=
      ComputableInPolyTime.beq
        (ComputableInPolyTime.bitsAppend hframe_n hu_pt) ComputableInPolyTime.id'
    have hc2 :
      ComputableInPolyTime (fun w => (u w).length == padRoot r (nCand w)) encBits encBool :=
      ComputableInPolyTime.unary_beq hulen hpad_u
    have hc3 : ComputableInPolyTime (fun w => decide (iCand w < (cert w).length)) encBits encBool :=
      ComputableInPolyTime.binary_lt'
        (ComputableInPolyTime.unary_to_binary.comp hiCand)
        (ComputableInPolyTime.unary_to_binary.comp hcert_len)
    have hc4 :
      ComputableInPolyTime (fun w => (cert w).getD (iCand w) false == bit) encBits encBool :=
      ComputableInPolyTime.beq
        (ComputableInPolyTime.bitsGetDWithInput hcert_pt hiCand false)
        (ComputableInPolyTime.const bit)
    have hAnd : ComputableInPolyTime (fun p : Bool × Bool => p.1 && p.2)
        (encPair encBool encBool) encBool := ComputableInPolyTime.of_finite _
    have h12 := hAnd.comp (hc1.prod hc2)
    have h123 := hAnd.comp (h12.prod hc3)
    exact hAnd.comp (h123.prod hc4)
  refine ⟨dec, hdec_pt, fun w => ?_⟩
  simp only [Set.mem_ofPred_eq, dec, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
  constructor
  · rintro ⟨n, i, rfl, hi_pow, hi_len, hbit⟩
    have hunf : unframe (encPair encNat encBits (n, BitString.lowBits (padRoot r n) i)) =
      encNat n := by
      rw [encPair_apply, unframe_frame_append]
    have hdrop : u (encPair encNat encBits (n, BitString.lowBits (padRoot r n) i)) =
        BitString.lowBits (padRoot r n) i := by
      dsimp only [u]; rw [encPair_apply, dropFrame_frame_append, encBits_apply]
    have hulen_eq : (u (encPair encNat encBits (n, BitString.lowBits (padRoot r n) i))).length =
        padRoot r n := by
      rw [hdrop, BitString.length_lowBits]
    have hn_lt : n < cap (encPair encNat encBits (n, BitString.lowBits (padRoot r n) i)) := by
      dsimp only [cap]; rw [hulen_eq]; exact lt_padRoot_succ_pow r n
    have hn_eq : nCand (encPair encNat encBits (n, BitString.lowBits (padRoot r n) i)) = n := by
      simp only [nCand, hunf, BitString.boundedBinaryValue_eq, encNat_apply,
        BitString.binaryValue_reverse_bits]
      exact Nat.min_eq_right hn_lt.le
    have hi_eq : iCand (encPair encNat encBits (n, BitString.lowBits (padRoot r n) i)) = i := by
      dsimp only [iCand, cert]
      rw [hn_eq, hdrop, BitString.boundedBinaryValue_eq, ← ofBits_reverse,
        List.reverse_reverse, ofBits_lowBits hi_pow]
      exact Nat.min_eq_right hi_len.le
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · rw [hn_eq, hdrop]; rfl
    · rw [hn_eq, hulen_eq]
    · dsimp only [cert]; rw [hn_eq, hi_eq]; exact hi_len
    · dsimp only [cert]; rw [hn_eq, hi_eq]; exact hbit
  · rintro ⟨⟨⟨hfw, hlen⟩, hilt⟩, hbit⟩
    have hi_eq : iCand w = ofBits (u w) ∧ ofBits (u w) < (cert w).length := by
      have h1 : iCand w = min (cert w).length (ofBits (u w)) := by
        simp only [iCand, BitString.boundedBinaryValue_eq, ← ofBits_reverse, List.reverse_reverse]
      rw [h1] at hilt ⊢
      have hlt' : ofBits (u w) < (cert w).length := by omega
      exact ⟨Nat.min_eq_right hlt'.le, hlt'⟩
    refine ⟨nCand w, iCand w, ?_, ?_, hilt, hbit⟩
    · have hlow : BitString.lowBits (padRoot r (nCand w)) (iCand w) = u w := by
        rw [← hlen, hi_eq.1, ofBits_eq_lsbValue, BitString.lowBits_lsbValue]
      rw [hlow]; exact hfw.symm
    · rw [← hlen, hi_eq.1]
      exact ofBits_lt_two_pow (u w)

/-- ** (Positive DCL in `P`)**: for any `P`-uniform witness-circuit family `gen`
and padding exponent `r`, `pDCL gen (padRoot r) ∈ P encBits`.
-/
theorem pDCL_mem_P (gen : ℕ → Σ n, WitnessCircuit n)
    (hpoly : ComputableInPolyTime gen encUnary WitnessCircuit.encWitnessCircuit) (r : ℕ) :
    pDCL gen (padRoot r) ∈ P encBits :=
  dcl_mem_P gen hpoly r true

/-- ** (Negative DCL in `P`)**: for any `P`-uniform witness-circuit family `gen`
and padding exponent `r`, `nDCL gen (padRoot r) ∈ P encBits`.
-/
theorem nDCL_mem_P (gen : ℕ → Σ n, WitnessCircuit n)
    (hpoly : ComputableInPolyTime gen encUnary WitnessCircuit.encWitnessCircuit) (r : ℕ) :
    nDCL gen (padRoot r) ∈ P encBits :=
  dcl_mem_P gen hpoly r false

/-! ### Part 3: Uniform Lower Bound `NP ⊈ P-uniform coNSIZE[O(n^k)]` -/

/-- Fixed universal polynomial-time verifier used in the Santhanam–Williams speedup step:
unpacks compressed nondeterministic DCL circuits `(D^p, D^n)` from advice `α`, unpacks a guessed
certificate `y` and witnesses from `W`, checks every bit of `y` against `(D^p, D^n)`, and
evaluates the reconstructed circuit on `(x, w_C)`. Because this verifier is completely independent
of `k`, `r`, and `b`, its polynomial time degree `d_V` is an absolute constant. -/
private def speedupVerifier (q : (List Bool × List Bool) × List Bool) : Bool :=
  let α := q.1.1
  let x := q.1.2
  let W := q.2
  let n := x.length
  let mPad := (unframe α).length
  let α1 := dropFrame α
  let wp := (unframe α1).length
  let α2 := dropFrame α1
  let sp := (unframe α2).length
  let α3 := dropFrame α2
  let wn := (unframe α3).length
  let α4 := dropFrame α3
  let sn := (unframe α4).length
  let α5 := dropFrame α4
  let certP := unframe α5
  let α6 := dropFrame α5
  let certN := unframe α6
  let α7 := dropFrame α6
  let bwC := unframe α7
  let bsC := dropFrame α7
  let wCu := (unframe W).length
  let W1 := dropFrame W
  let sCu := (unframe W1).length
  let W2 := dropFrame W1
  let y := unframe W2
  let W3 := dropFrame W2
  let wCbits := unframe W3
  let wsFlat := dropFrame W3
  let M := (encPair encNat encBits (n, List.replicate mPad false)).length
  let rcP := Boolean.readCertificate (M + wp) sp certP
  let rcN := Boolean.readCertificate (M + wn) sn certN
  let rcC := Boolean.readCertificate (n + wCu) sCu y
  let wMax := max wp wn
  (encNat wCu == bwC) &&
  (encNat sCu == bsC) &&
  (y.length == Boolean.certLength (n + wCu) sCu) &&
  (wCbits.length == wCu) &&
  ((List.range y.length).all fun i =>
    let ui := encPair encNat encBits (n, BitString.lowBits mPad i)
    let wi := BitString.listRow wMax i wsFlat
    if y.getD i false then
      Boolean.evalOutput (ui ++ wi.take wp) rcP.1 rcP.2
    else
      Boolean.evalOutput (ui ++ wi.take wn) rcN.1 rcN.2) &&
  Boolean.evalOutput (x ++ wCbits) rcC.1 rcC.2

private lemma computableInPolyTime_speedupVerifier :
    ComputableInPolyTime speedupVerifier
      (encPair (encPair encBits encBits) encBits) encBool := by
  let encQ := encPair (encPair encBits encBits) encBits
  have hα : ComputableInPolyTime (fun q => q.1.1) encQ encBits :=
    (ComputableInPolyTime.fst _ _).comp (ComputableInPolyTime.fst _ _)
  have hx : ComputableInPolyTime (fun q => q.1.2) encQ encBits :=
    (ComputableInPolyTime.snd _ _).comp (ComputableInPolyTime.fst _ _)
  have hW : ComputableInPolyTime (fun q => q.2) encQ encBits := ComputableInPolyTime.snd _ _
  have hn : ComputableInPolyTime (fun q => q.1.2.length) encQ encUnary :=
    ComputableInPolyTime.length_bits.comp hx
  have hn_bin : ComputableInPolyTime (fun q => q.1.2.length) encQ encNat :=
    ComputableInPolyTime.unary_to_binary.comp hn
  have hmPad : ComputableInPolyTime (fun q => (unframe q.1.1).length) encQ encUnary :=
    ComputableInPolyTime.length_bits.comp (ComputableInPolyTime.unframe.comp hα)
  have hα1 := ComputableInPolyTime.dropFrame.comp hα
  have hwp := ComputableInPolyTime.length_bits.comp (ComputableInPolyTime.unframe.comp hα1)
  have hα2 := ComputableInPolyTime.dropFrame.comp hα1
  have hsp := ComputableInPolyTime.length_bits.comp (ComputableInPolyTime.unframe.comp hα2)
  have hα3 := ComputableInPolyTime.dropFrame.comp hα2
  have hwn := ComputableInPolyTime.length_bits.comp (ComputableInPolyTime.unframe.comp hα3)
  have hα4 := ComputableInPolyTime.dropFrame.comp hα3
  have hsn := ComputableInPolyTime.length_bits.comp (ComputableInPolyTime.unframe.comp hα4)
  have hα5 := ComputableInPolyTime.dropFrame.comp hα4
  have hcertP := ComputableInPolyTime.unframe.comp hα5
  have hα6 := ComputableInPolyTime.dropFrame.comp hα5
  have hcertN := ComputableInPolyTime.unframe.comp hα6
  have hα7 := ComputableInPolyTime.dropFrame.comp hα6
  have hbwC := ComputableInPolyTime.unframe.comp hα7
  have hbsC := ComputableInPolyTime.dropFrame.comp hα7
  have hwCu := ComputableInPolyTime.length_bits.comp (ComputableInPolyTime.unframe.comp hW)
  have hW1 := ComputableInPolyTime.dropFrame.comp hW
  have hsCu := ComputableInPolyTime.length_bits.comp (ComputableInPolyTime.unframe.comp hW1)
  have hW2 := ComputableInPolyTime.dropFrame.comp hW1
  have hy := ComputableInPolyTime.unframe.comp hW2
  have hW3 := ComputableInPolyTime.dropFrame.comp hW2
  have hwCbits := ComputableInPolyTime.unframe.comp hW3
  have hwsFlat := ComputableInPolyTime.dropFrame.comp hW3
  have hM_bits : ComputableInPolyTime (fun q : (List Bool × List Bool) × List Bool =>
      encPair encNat encBits (q.1.2.length,
        List.replicate (unframe q.1.1).length false)) encQ encBits :=
    (ComputableInPolyTime.of_eq (f := encPair encNat encBits) (encOut := encBits) fun _ => rfl).comp
      (hn_bin.prod ((ComputableInPolyTime.bitsReplicate false).comp hmPad))
  have hM := ComputableInPolyTime.length_bits.comp hM_bits
  have hrcP := Boolean.computableInPolyTime_readCertificate
    (ComputableInPolyTime.unary_add' hM hwp) hsp hcertP
  have hrcN := Boolean.computableInPolyTime_readCertificate
    (ComputableInPolyTime.unary_add' hM hwn) hsn hcertN
  have hrcC := Boolean.computableInPolyTime_readCertificate
    (ComputableInPolyTime.unary_add' hn hwCu) hsCu hy
  have hwMax := ComputableInPolyTime.unary_max.comp (hwp.prod hwn)
  have hylen := ComputableInPolyTime.length_bits.comp hy
  have hcertLen : ComputableInPolyTime (fun q : (List Bool × List Bool) × List Bool =>
      Boolean.certLength (q.1.2.length + (unframe q.2).length) (unframe (dropFrame q.2)).length)
      encQ encUnary := by
    unfold Boolean.certLength
    have hns := ComputableInPolyTime.unary_add' (ComputableInPolyTime.unary_add' hn hwCu) hsCu
    exact ComputableInPolyTime.unary_add'
      (ComputableInPolyTime.unary_add' hsCu hns)
      (ComputableInPolyTime.unary_mul' hsCu
        (ComputableInPolyTime.unary_add' (ComputableInPolyTime.const 3)
          (ComputableInPolyTime.unary_mul' (ComputableInPolyTime.const 2) hns)))
  have hc1 := ComputableInPolyTime.beq
    ((ComputableInPolyTime.of_eq (f := encNat) (encOut := encBits) fun _ => rfl).comp
      (ComputableInPolyTime.unary_to_binary.comp hwCu)) hbwC
  have hc2 := ComputableInPolyTime.beq
    ((ComputableInPolyTime.of_eq (f := encNat) (encOut := encBits) fun _ => rfl).comp
      (ComputableInPolyTime.unary_to_binary.comp hsCu)) hbsC
  have hc3 := ComputableInPolyTime.unary_beq hylen hcertLen
  have hc4 := ComputableInPolyTime.unary_beq (ComputableInPolyTime.length_bits.comp hwCbits) hwCu
  have hrange : ComputableInPolyTime (fun q : (List Bool × List Bool) × List Bool =>
      List.range (unframe (dropFrame (dropFrame q.2))).length) encQ (encList encUnary) :=
    ComputableInPolyTime.range.comp hylen
  have htest : ComputableInPolyTime
      (fun p : ((List Bool × List Bool) × List Bool) × ℕ =>
        let q := p.1
        let i := p.2
        let mPad := (unframe q.1.1).length
        let wp := (unframe (dropFrame q.1.1)).length
        let sp := (unframe (dropFrame (dropFrame q.1.1))).length
        let wn := (unframe (dropFrame (dropFrame (dropFrame q.1.1)))).length
        let sn := (unframe (dropFrame (dropFrame (dropFrame (dropFrame q.1.1))))).length
        let certP := unframe (dropFrame (dropFrame (dropFrame (dropFrame (dropFrame q.1.1)))))
        let certN :=
          unframe (dropFrame (dropFrame (dropFrame (dropFrame (dropFrame (dropFrame q.1.1))))))
        let y := unframe (dropFrame (dropFrame q.2))
        let wsFlat := dropFrame (dropFrame (dropFrame (dropFrame q.2)))
        let M := (encPair encNat encBits (q.1.2.length, List.replicate mPad false)).length
        let rcP := Boolean.readCertificate (M + wp) sp certP
        let rcN := Boolean.readCertificate (M + wn) sn certN
        let ui := encPair encNat encBits (q.1.2.length, BitString.lowBits mPad i)
        let wi := BitString.listRow (max wp wn) i wsFlat
        if y.getD i false then
          Boolean.evalOutput (ui ++ wi.take wp) rcP.1 rcP.2
        else
          Boolean.evalOutput (ui ++ wi.take wn) rcN.1 rcN.2)
      (encPair encQ encUnary) encBool := by
    have hqf := ComputableInPolyTime.fst encQ encUnary
    have hi := ComputableInPolyTime.snd encQ encUnary
    have hui : ComputableInPolyTime (fun p : ((List Bool × List Bool) × List Bool) × ℕ =>
        encPair encNat encBits (p.1.1.2.length, BitString.lowBits (unframe p.1.1.1).length p.2))
        (encPair encQ encUnary) encBits :=
      (ComputableInPolyTime.of_eq (f := encPair encNat encBits) (encOut :=
        encBits) fun _ => rfl).comp
        ((hn_bin.comp hqf).prod
          (ComputableInPolyTime.bitsLow (hmPad.comp hqf)
            (ComputableInPolyTime.unary_to_binary.comp hi)))
    have hwi := ComputableInPolyTime.bitsRowWithInput (hwMax.comp hqf) hi (hwsFlat.comp hqf)
    have hyi := ComputableInPolyTime.bitsGetDWithInput (hy.comp hqf) hi false
    have hevP := Boolean.computableInPolyTime_evalOutput
      (ComputableInPolyTime.bitsAppend hui
        (ComputableInPolyTime.bitsTakeWithInput hwi (hwp.comp hqf)))
      ((ComputableInPolyTime.fst _ _).comp (hrcP.comp hqf))
      ((ComputableInPolyTime.snd _ _).comp (hrcP.comp hqf))
    have hevN := Boolean.computableInPolyTime_evalOutput
      (ComputableInPolyTime.bitsAppend hui
        (ComputableInPolyTime.bitsTakeWithInput hwi (hwn.comp hqf)))
      ((ComputableInPolyTime.fst _ _).comp (hrcN.comp hqf))
      ((ComputableInPolyTime.snd _ _).comp (hrcN.comp hqf))
    exact ComputableInPolyTime.ite' hyi hevP hevN
  have hc5 := ComputableInPolyTime.allWith htest ComputableInPolyTime.id' hrange
  have hc6 := Boolean.computableInPolyTime_evalOutput
    (ComputableInPolyTime.bitsAppend hx hwCbits)
    ((ComputableInPolyTime.fst _ _).comp hrcC)
    ((ComputableInPolyTime.snd _ _).comp hrcC)
  have hAnd : ComputableInPolyTime (fun p : Bool × Bool => p.1 && p.2)
      (encPair encBool encBool) encBool := ComputableInPolyTime.of_finite _
  have h12 := hAnd.comp (hc1.prod hc2)
  have h123 := hAnd.comp (h12.prod hc3)
  have h1234 := hAnd.comp (h123.prod hc4)
  have h12345 := hAnd.comp (h1234.prod hc5)
  exact hAnd.comp (h12345.prod hc6)

private lemma eventually_mul_size_le_padRoot (r C : ℕ) :
    ∀ᶠ n in atTop, C * (Nat.size (n + 1) + 1) ≤ padRoot r n := by
  have hpoly := PolynomiallyBounded.eventually_lt_two_pow
    (f := fun m => (C * (m + 3) + 1) ^ (2 ^ r)) (by fun_prop)
  rw [eventually_atTop] at hpoly ⊢
  obtain ⟨M₀, hM₀⟩ := hpoly
  refine ⟨2 ^ M₀ + 1, fun n hn => ?_⟩
  have hMle : M₀ ≤ Nat.log 2 (n + 1) :=
    Nat.le_log_of_pow_le (by norm_num) (by omega)
  have h1 := (hM₀ (Nat.log 2 (n + 1)) hMle).le
  have h2 : 2 ^ Nat.log 2 (n + 1) ≤ n + 1 := Nat.pow_log_le_self 2 (by omega)
  have hsz : Nat.size (n + 1) ≤ Nat.log 2 (n + 1) + 1 :=
    Nat.size_le.mpr (Nat.lt_pow_succ_log_self (by norm_num) (n + 1))
  have h3 : (C * (Nat.size (n + 1) + 1)) ^ (2 ^ r) < (padRoot r n + 1) ^ (2 ^ r) := by
    have hlt := lt_padRoot_succ_pow r n
    have hM0_pos : 1 ≤ 2 ^ M₀ := Nat.one_le_two_pow
    have h4' : (C * (Nat.size (n + 1) + 1) + 1) ^ (2 ^ r) ≤
        (C * (Nat.log 2 (n + 1) + 3) + 1) ^ (2 ^ r) :=
      Nat.pow_le_pow_left (by
        have := Nat.mul_le_mul_left C (show Nat.size (n + 1) + 1 ≤ Nat.log 2 (n + 1) + 2 by omega)
        have : C * (Nat.log 2 (n + 1) + 3) = C * (Nat.log 2 (n + 1) + 2) + C := by ring
        cases C with
        | zero => simp
        | succ C' => omega) _
    have hpos : 1 ≤ 2 ^ r := Nat.one_le_two_pow
    cases C with
    | zero =>
      simp only [zero_mul, zero_pow (by omega : 2 ^ r ≠ 0)]; exact Nat.pos_of_ne_zero (by omega)
    | succ C' =>
      have hlt1 : (C' + 1) * (Nat.size (n + 1) + 1) <
          (C' + 1) * (Nat.size (n + 1) + 1) + 1 := Nat.lt_succ_self _
      have hlt2 := Nat.pow_lt_pow_left hlt1 (by omega : 2 ^ r ≠ 0)
      have h6 := hlt2.trans_le ((h4'.trans h1).trans h2)
      have h7 : ((C' + 1) * (Nat.size (n + 1) + 1)) ^ (2 ^ r) ≤ n := Nat.lt_succ_iff.mp h6
      exact h7.trans_lt hlt
  by_contra hgt
  push Not at hgt
  have hle' : padRoot r n + 1 ≤ C * (Nat.size (n + 1) + 1) := by omega
  exact absurd (Nat.pow_le_pow_left hle' (2 ^ r)) (not_le_of_gt h3)

private lemma computableInO_length_lt (N₀ : ℕ) :
    ComputableInO (fun x : List Bool => decide (x.length < N₀)) encBits encBool
      (fun x => x.length) (fun x => x.length) := by
  have hlt : ComputableInPolyTime (fun n : ℕ => decide (n < N₀)) encNat encBool :=
    ComputableInPolyTime.binary_lt' ComputableInPolyTime.id' (ComputableInPolyTime.const N₀)
  have hlt_inO : ComputableInO (fun n : ℕ => decide (n < N₀)) encNat encBool
      (fun n => n) (fun n => n) := by
    obtain ⟨T, S, hT, hS, h⟩ := hlt.exists_computableInO
    obtain ⟨cT, dT, hcT⟩ := hT.exists_le
    obtain ⟨cS, dS, hcS⟩ := hS.exists_le
    obtain ⟨KT, hKT⟩ := PolynomiallyBounded.exists_le_mul_two_pow
      (p := fun m => cT * (m + 1) ^ dT) (by fun_prop)
    obtain ⟨KS, hKS⟩ := PolynomiallyBounded.exists_le_mul_two_pow
      (p := fun m => cS * (m + 1) ^ dS) (by fun_prop)
    have h2pow : ∀ n : ℕ, 2 ^ (encNat n).length ≤ 2 * (n + 1) := by
      intro n; rw [encNat_apply, Nat.size_eq_bits_len]
      cases n with
      | zero => simp
      | succ m =>
        have hsz : 1 ≤ Nat.size (m + 1) := Nat.size_pos.mpr (Nat.succ_pos m)
        have hlt2 : 2 ^ (Nat.size (m + 1) - 1) ≤ m + 1 := Nat.lt_size.mp (by omega)
        have hpow : 2 ^ Nat.size (m + 1) = 2 * 2 ^ (Nat.size (m + 1) - 1) := by
          conv_lhs => rw [← Nat.sub_add_cancel hsz, pow_succ, Nat.mul_comm]
        omega
    refine h.mono (2 * KT + 2 * KS + 2) (fun n => ?_) (fun n => ?_)
    · have h1 := (hcT n).trans (hKT (encNat n).length)
      have h3 : KT * 2 ^ (encNat n).length ≤ 2 * KT * (n + 1) := by
        have := Nat.mul_le_mul_left KT (h2pow n)
        have e : KT * (2 * (n + 1)) = 2 * KT * (n + 1) := by ring
        omega
      have e2 : (2 * KT + 2 * KS + 2) * (n + 1) =
          2 * KT * (n + 1) + 2 * KS * (n + 1) + 2 * (n + 1) := by ring
      omega
    · have h1 := (hcS n).trans (hKS (encNat n).length)
      have h3 : KS * 2 ^ (encNat n).length ≤ 2 * KS * (n + 1) := by
        have := Nat.mul_le_mul_left KS (h2pow n)
        have e : KS * (2 * (n + 1)) = 2 * KS * (n + 1) := by ring
        omega
      have e2 : (2 * KT + 2 * KS + 2) * (n + 1) =
          2 * KT * (n + 1) + 2 * KS * (n + 1) + 2 * (n + 1) := by ring
      omega
  exact (hlt_inO.comp ComputableInO.lengthNat).mono 2
    (fun x => by omega) (fun x => by omega)

private lemma timeConstructible_succ_pow_local (d : ℕ) (hd : 1 ≤ d) :
    TimeConstructible (fun n => (n + 1) ^ d) := by
  rcases eq_or_lt_of_le hd with rfl | h2
  · simpa only [pow_one] using timeConstructible_succ
  · exact timeConstructible_succ_pow (by omega)

private lemma computableInO_mem_const_list (small : List (List Bool)) :
    ComputableInO (fun x : List Bool => small.contains x) encBits encBool
      (fun x => x.length) (fun x => x.length) := by
  induction small with
  | nil =>
    exact (ComputableInO.const (encIn := encBits) (encMid := encBool) false).mono 1
      (fun _ => by simp [encBits_apply]) (fun _ => by simp [encBits_apply])
  | cons s tl ih =>
    have heq : ComputableInO (fun x : List Bool => decide (s = x)) encBits encBool
        (fun x => x.length) (fun x => x.length) := by
      have h := (ComputableInO.eq encBits).comp
        ((ComputableInO.const (encIn := encBits) (encMid := encBits) s).prod
          (ComputableInO.of_eq (f := id) fun _ => rfl))
      refine h.mono ((s.length + 2) ^ 2 + 4) (fun x => ?_) (fun x => ?_)
      · dsimp only [Function.comp_apply, encBits_apply, id_eq]
        have e1 : (s.length + 1) * (s.length + x.length + 1) =
            (s.length + 1) * x.length + (s.length + 1) ^ 2 := by ring
        have e2 : ((s.length + 2) ^ 2 + 4) * (x.length + 1) =
            (s.length + 2) ^ 2 * x.length + (s.length + 2) ^ 2 + 4 * x.length + 4 := by ring
        have h1 : (s.length + 1) * x.length ≤ (s.length + 2) ^ 2 * x.length :=
          Nat.mul_le_mul_right _ (by
            have : s.length + 1 ≤ s.length + 2 := Nat.le_succ _
            exact this.trans (Nat.le_self_pow (by norm_num) _))
        have h2 : (s.length + 1) ^ 2 ≤ (s.length + 2) ^ 2 := Nat.pow_le_pow_left (by omega) 2
        omega
      · dsimp only [Function.comp_apply, encBits_apply, id_eq]
        have hlen : (encPair encBits encBits (s, x)).length = 2 * s.length + 1 + x.length := by
          simp
        rw [hlen]
        have e2 : ((s.length + 2) ^ 2 + 4) * (x.length + 1) =
            (s.length + 2) ^ 2 * x.length + (s.length + 2) ^ 2 + 4 * x.length + 4 := by ring
        have hsq : 2 * s.length + 1 ≤ (s.length + 2) ^ 2 := by nlinarith
        omega
    have hor := (ComputableInDegree.of_finite (encIn := encPair encBool encBool) (encMid := encBool)
      (fun p : Bool × Bool => p.1 || p.2)).inO_one
    have hcomb : ComputableInO (fun x : List Bool => decide (s = x) || tl.contains x)
        encBits encBool (fun x => x.length) (fun x => x.length) :=
      (hor.comp (heq.prod ih)).mono 8
        (fun x => by simp; omega)
        (fun x => by simp; omega)
    refine hcomb.of_enc_eq fun x => ?_
    simp only [List.contains_cons]; rw [Bool.or_comm]
    congr 1
    by_cases h : x = s
    · subst h; simp
    · simp [h, Ne.symm h]

private lemma timeConstructible_mul_succ_pow (C d : ℕ) (hC : 1 ≤ C) (hd : 1 ≤ d) :
    TimeConstructible (fun n => C * (n + 1) ^ d) :=
  (timeConstructible_succ_pow_local d hd).comp_of_computableInPolyTime
    (g := fun m => C * m)
    (ComputableInPolyTime.binary_mul.comp
      ((ComputableInPolyTime.const C).prod ComputableInPolyTime.id'))
    (fun _ => Nat.le_mul_of_pos_left _ hC)

private lemma certEncode_length {m : ℕ} (c : WitnessCircuit m) :
    (certEncode c).length = Boolean.certLength (m + c.witnessLen) c.size :=
  Boolean.length_certificate_code c.circuit (le_max_left _ _)

private lemma certEncode_length_sq {m m' : ℕ} (c : WitnessCircuit m) (hm : m = m') :
    (certEncode c).length ≤ 3 * (m' + 2 * c.size + 1) ^ 2 := by
  subst hm; rw [certEncode_length c]
  refine (Boolean.certLength_le_three_mul_sq _ _).trans ?_
  have hw : c.witnessLen ≤ c.size := le_max_right _ _
  exact Nat.mul_le_mul_left 3 (Nat.pow_le_pow_left (by omega) 2)

private lemma readCertificate_certEncode {m m' : ℕ} (c : WitnessCircuit m) (hm : m = m') :
    Boolean.readCertificate (m' + c.witnessLen) c.size (certEncode c) =
      (c.circuit.code.1, (c.circuit.outputs 0).toNat) := by
  subst hm
  have h := Boolean.readCertificate_certificate_code_append c.circuit
    (le_max_left c.circuit.size c.witnessLen) []
  simpa [certEncode, WitnessCircuit.size_eq] using h

private lemma evalOutput_append_eq {m m' : ℕ} (c : WitnessCircuit m) (hm : m = m')
    (u w : List Bool) (hu : u.length = m') (hw : w.length = c.witnessLen) :
    Boolean.evalOutput (u ++ w) c.circuit.code.1 (c.circuit.outputs 0).toNat =
      c.circuit.eval Boolean.interpretation
        (Fin.append (BitString.ofList m' u ∘ Fin.cast hm)
          (BitString.ofList c.witnessLen w)) 0 := by
  subst hm; rw [Circuit.eval_eq_evalOutput]
  congr 1
  rw [List.ofFn_fin_append, show BitString.ofList m u ∘ Fin.cast rfl =
    BitString.ofList m u from rfl,
    BitString.ofFn_ofList hu, BitString.ofFn_ofList hw]

private lemma speedup_advice_sublinear {k r cH cP cN : ℕ} (hk : 1 ≤ k) (hr : 4 * k + 4 ≤ 2 ^ r)
    (genH : ℕ → Σ n, WitnessCircuit n) (hgenH_arity : ∀ n, (genH n).1 = n)
    (hgenH_size : ∀ n, (genH n).2.size ≤ cH * (n + 1) ^ k)
    (genP : ℕ → Σ n, WitnessCircuit n) (hgenP_arity : ∀ n, (genP n).1 = n)
    (hgenP_size : ∀ n, (genP n).2.size ≤ cP * (n + 1) ^ k)
    (genN : ℕ → Σ n, WitnessCircuit n) (hgenN_arity : ∀ n, (genN n).1 = n)
    (hgenN_size : ∀ n, (genN n).2.size ≤ cN * (n + 1) ^ k) :
    let Mfn : ℕ → ℕ := fun n =>
      (encPair encNat encBits (n, List.replicate (padRoot r n) false)).length
    let advice : ℕ → List Bool := fun n =>
      let C := (genH n).2
      let Dp := (genP (Mfn n)).2
      let Dn := (genN (Mfn n)).2
      frame (List.replicate (padRoot r n) true) ++
      frame (List.replicate Dp.witnessLen true) ++
      frame (List.replicate Dp.size true) ++
      frame (List.replicate Dn.witnessLen true) ++
      frame (List.replicate Dn.size true) ++
      frame (certEncode Dp) ++
      frame (certEncode Dn) ++
      frame (encNat C.witnessLen) ++
      encNat C.size
    (∀ c : ℕ, ∃ N : ℕ, ∀ n ≥ N, c * (advice n).length ≤ n) ∧
    (∀ᶠ n in atTop, (certEncode (genH n).2).length < 2 ^ padRoot r n) := by
  intro Mfn advice
  have hM_le : ∀ n, Mfn n ≤ 2 * (Nat.size (n + 1) + 1) + padRoot r n := by
    intro n
    have hsz : Nat.size n ≤ Nat.size (n + 1) := Nat.size_le_size (Nat.le_succ n)
    simp only [Mfn, length_encPair, encNat_apply, encBits_apply, List.length_replicate,
      Nat.size_eq_bits_len]
    omega
  let Kadv : ℕ := 16 * (cP + cN + cH + 4) ^ 2 * 16 + 100
  have hadv_len_le : ∀ n, (advice n).length ≤
      Kadv * (Mfn n + 1) ^ (2 * k) + 8 * (k + cH + 4) * (Nat.size (n + 1) + 1) := by
    intro n
    let C := (genH n).2
    let Dp := (genP (Mfn n)).2
    let Dn := (genN (Mfn n)).2
    have hDp_s : Dp.size ≤ cP * (Mfn n + 1) ^ k := hgenP_size (Mfn n)
    have hDn_s : Dn.size ≤ cN * (Mfn n + 1) ^ k := hgenN_size (Mfn n)
    have hDp_w : Dp.witnessLen ≤ Dp.size := le_max_right _ _
    have hDn_w : Dn.witnessLen ≤ Dn.size := le_max_right _ _
    have hC_s : C.size ≤ cH * (n + 1) ^ k := hgenH_size n
    have hC_w : C.witnessLen ≤ C.size := le_max_right _ _
    have hM2 : Mfn n + 1 ≤ (Mfn n + 1) ^ k := Nat.le_self_pow (by omega) (Mfn n + 1)
    have hcertP_le : (certEncode Dp).length ≤ 3 * ((2 * cP + 2) * (Mfn n + 1) ^ k) ^ 2 := by
      refine (certEncode_length_sq Dp (hgenP_arity (Mfn n))).trans
        (Nat.mul_le_mul_left 3 (Nat.pow_le_pow_left ?_ 2))
      have : (2 * cP + 2) * (Mfn n + 1) ^ k =
          2 * (cP * (Mfn n + 1) ^ k) + (Mfn n + 1) ^ k + (Mfn n + 1) ^ k := by ring
      omega
    have hcertN_le : (certEncode Dn).length ≤ 3 * ((2 * cN + 2) * (Mfn n + 1) ^ k) ^ 2 := by
      refine (certEncode_length_sq Dn (hgenN_arity (Mfn n))).trans
        (Nat.mul_le_mul_left 3 (Nat.pow_le_pow_left ?_ 2))
      have : (2 * cN + 2) * (Mfn n + 1) ^ k =
          2 * (cN * (Mfn n + 1) ^ k) + (Mfn n + 1) ^ k + (Mfn n + 1) ^ k := by ring
      omega
    have hszC : (encNat C.size).length ≤ (k + cH + 4) * (Nat.size (n + 1) + 1) := by
      rw [encNat_apply, Nat.size_eq_bits_len]
      have hpow1 : n + 1 < 2 ^ Nat.size (n + 1) := Nat.lt_size_self (n + 1)
      have hpow2 : (n + 1) ^ k ≤ 2 ^ (k * Nat.size (n + 1)) := by
        calc (n + 1) ^ k ≤ (2 ^ Nat.size (n + 1)) ^ k := Nat.pow_le_pow_left hpow1.le k
          _ = 2 ^ (k * Nat.size (n + 1)) := by rw [← pow_mul, Nat.mul_comm]
      have htot : C.size < 2 ^ (cH + k * Nat.size (n + 1)) := by
        rw [pow_add]; exact hC_s.trans_lt (by
          calc cH * (n + 1) ^ k ≤ cH * 2 ^ (k * Nat.size (n + 1)) :=
                Nat.mul_le_mul_left cH hpow2
            _ < 2 ^ cH * 2 ^ (k * Nat.size (n + 1)) :=
                Nat.mul_lt_mul_of_pos_right Nat.lt_two_pow_self Nat.one_le_two_pow)
      have hsz1 : Nat.size C.size ≤ cH + k * Nat.size (n + 1) := Nat.size_le.mpr htot
      have e : (k + cH + 4) * (Nat.size (n + 1) + 1) =
          k * Nat.size (n + 1) + cH * Nat.size (n + 1) + 4 * Nat.size (n + 1) + k + cH + 4 := by
        ring
      omega
    have hszCw : (encNat C.witnessLen).length ≤ (k + cH + 4) * (Nat.size (n + 1) + 1) := by
      have : (encNat C.witnessLen).length ≤ (encNat C.size).length := by
        simp only [encNat_apply, Nat.size_eq_bits_len]; exact Nat.size_le_size hC_w
      omega
    have hpow2k : ((Mfn n + 1) ^ k) ^ 2 = (Mfn n + 1) ^ (2 * k) := by
      rw [← pow_mul, Nat.mul_comm]
    have hM2k : (Mfn n + 1) ^ k ≤ (Mfn n + 1) ^ (2 * k) :=
      Nat.pow_le_pow_right (Nat.succ_pos _) (by omega)
    have hpr_le : padRoot r n ≤ Mfn n + 1 := by
      simp only [Mfn, length_encPair, encBits_apply, List.length_replicate]; omega
    simp only [advice, List.length_append, length_frame, List.length_replicate]
    have hcoeffP : (2 * cP + 2) ^ 2 ≤ (cP + cN + cH + 4) ^ 2 * 4 :=
      (Nat.pow_le_pow_left (show 2 * cP + 2 ≤ 2 * (cP + cN + cH + 4) by omega) 2).trans_eq (by ring)
    have hcoeffN : (2 * cN + 2) ^ 2 ≤ (cP + cN + cH + 4) ^ 2 * 4 :=
      (Nat.pow_le_pow_left (show 2 * cN + 2 ≤ 2 * (cP + cN + cH + 4) by omega) 2).trans_eq (by ring)
    set S := (cP + cN + cH + 4) ^ 2 * (Mfn n + 1) ^ (2 * k)
    have hP_fin : (certEncode Dp).length ≤ 12 * S := by
      calc (certEncode Dp).length ≤ 3 * ((2 * cP + 2) ^ 2 * (Mfn n + 1) ^ (2 * k)) := by
            simpa [mul_pow, hpow2k] using hcertP_le
        _ ≤ 3 * ((cP + cN + cH + 4) ^ 2 * 4 * (Mfn n + 1) ^ (2 * k)) :=
            Nat.mul_le_mul_left 3 (Nat.mul_le_mul_right _ hcoeffP)
        _ = 12 * S := by dsimp [S]; ring
    have hN_fin : (certEncode Dn).length ≤ 12 * S := by
      calc (certEncode Dn).length ≤ 3 * ((2 * cN + 2) ^ 2 * (Mfn n + 1) ^ (2 * k)) := by
            simpa [mul_pow, hpow2k] using hcertN_le
        _ ≤ 3 * ((cP + cN + cH + 4) ^ 2 * 4 * (Mfn n + 1) ^ (2 * k)) :=
            Nat.mul_le_mul_left 3 (Nat.mul_le_mul_right _ hcoeffN)
        _ = 12 * S := by dsimp [S]; ring
    have hcp1 : cP ≤ (cP + cN + cH + 4) ^ 2 :=
      (show cP ≤ cP + cN + cH + 4 by omega).trans (Nat.le_self_pow (by norm_num) _)
    have hcn1 : cN ≤ (cP + cN + cH + 4) ^ 2 :=
      (show cN ≤ cP + cN + cH + 4 by omega).trans (Nat.le_self_pow (by norm_num) _)
    have h1 : cP * (Mfn n + 1) ^ k ≤ S := Nat.mul_le_mul hcp1 hM2k
    have h2 : cN * (Mfn n + 1) ^ k ≤ S := Nat.mul_le_mul hcn1 hM2k
    have h3 : Mfn n + 1 ≤ (Mfn n + 1) ^ (2 * k) := hM2.trans hM2k
    have h4 : 1 ≤ (Mfn n + 1) ^ (2 * k) := Nat.pow_pos (Nat.succ_pos _)
    have h5 : Kadv * (Mfn n + 1) ^ (2 * k) = 256 * S + 100 * (Mfn n + 1) ^ (2 * k) := by
      dsimp [Kadv, S]; ring
    have h8 : 8 * (k + cH + 4) * (Nat.size (n + 1) + 1) =
        8 * ((k + cH + 4) * (Nat.size (n + 1) + 1)) := by ring
    dsimp only [Dp, Dn, C] at *
    omega
  constructor
  · intro c
    have hlog := (eventually_mul_size_le_padRoot r 2).and
      (eventually_mul_size_le_padRoot r (16 * (c + 1) * (k + cH + 4)))
    rw [eventually_atTop] at hlog
    obtain ⟨N₁, hN₁⟩ := hlog
    let B0 : ℕ := max 2 (2 * (c + 1) * Kadv * 4 ^ (2 * k))
    refine ⟨max N₁ (B0 ^ (2 ^ r)), fun n hn => ?_⟩
    have hn1 : N₁ ≤ n := (le_max_left _ _).trans hn
    have hn2 : B0 ^ (2 ^ r) ≤ n := (le_max_right _ _).trans hn
    obtain ⟨hlog2, hlogC⟩ := hN₁ n hn1
    have hpr_ge : B0 ≤ padRoot r n + 1 := by
      by_contra hlt; push Not at hlt
      have h1 : (padRoot r n + 1) ^ (2 ^ r) ≤ (B0 - 1) ^ (2 ^ r) :=
        Nat.pow_le_pow_left (by omega) _
      have h2 := lt_padRoot_succ_pow r n
      have h3 : (B0 - 1) ^ (2 ^ r) < B0 ^ (2 ^ r) :=
        Nat.pow_lt_pow_left (by omega) (by have := Nat.one_le_two_pow (n := r); omega)
      omega
    have hpr_pos : 1 ≤ padRoot r n := by have : 2 ≤ B0 := le_max_left _ _; omega
    have hM_4 : Mfn n + 1 ≤ 4 * padRoot r n := by have := hM_le n; omega
    have hterm1 : 2 * (c * (Kadv * (Mfn n + 1) ^ (2 * k))) ≤ n := by
      have h1 : (Mfn n + 1) ^ (2 * k) ≤ 4 ^ (2 * k) * (padRoot r n) ^ (2 * k) := by
        rw [← mul_pow]; exact Nat.pow_le_pow_left hM_4 _
      have h2 : 2 * (c * (Kadv * (4 ^ (2 * k) * (padRoot r n) ^ (2 * k)))) =
          (2 * c * Kadv * 4 ^ (2 * k)) * (padRoot r n) ^ (2 * k) := by ring
      have h3 : 2 * c * Kadv * 4 ^ (2 * k) ≤ B0 := by
        refine le_trans ?_ (le_max_right _ _)
        have e1 : 2 * c * Kadv * 4 ^ (2 * k) = (2 * c) * (Kadv * 4 ^ (2 * k)) := by ring
        have e2 : 2 * (c + 1) * Kadv * 4 ^ (2 * k) =
            (2 * (c + 1)) * (Kadv * 4 ^ (2 * k)) := by ring
        rw [e1, e2]; exact Nat.mul_le_mul_right _ (by omega)
      have hsq : 2 ≤ padRoot r n := by
        have hB200 : 200 ≤ B0 := le_trans (by
          have : 2 * 1 * 100 * 1 ≤ 2 * (c + 1) * Kadv * 4 ^ (2 * k) := by
            have h4 : 1 ≤ 4 ^ (2 * k) := Nat.one_le_pow (2 * k) 4 (by norm_num)
            have := Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left 2 (Nat.succ_pos c))
              (show 100 ≤ Kadv by dsimp [Kadv]; omega)) h4
            simpa using this
          omega) (le_max_right _ _)
        omega
      calc 2 * (c * (Kadv * (Mfn n + 1) ^ (2 * k)))
          ≤ 2 * (c * (Kadv * (4 ^ (2 * k) * (padRoot r n) ^ (2 * k)))) :=
            Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h1))
        _ = (2 * c * Kadv * 4 ^ (2 * k)) * (padRoot r n) ^ (2 * k) := h2
        _ ≤ (2 * padRoot r n) * (padRoot r n) ^ (2 * k) :=
            Nat.mul_le_mul_right _ (h3.trans (by omega))
        _ ≤ (padRoot r n * padRoot r n) * (padRoot r n) ^ (2 * k) :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hsq)
        _ = (padRoot r n) ^ (2 * k + 2) := by rw [pow_add, pow_two]; ring
        _ ≤ (padRoot r n) ^ (2 ^ r) := Nat.pow_le_pow_right hpr_pos (by omega)
        _ ≤ n := padRoot_pow_le r n
    have hterm2 : 2 * (c * (8 * (k + cH + 4) * (Nat.size (n + 1) + 1))) ≤ n := by
      have h1 : 2 * (c * (8 * (k + cH + 4) * (Nat.size (n + 1) + 1))) =
          (16 * c * (k + cH + 4)) * (Nat.size (n + 1) + 1) := by ring
      calc 2 * (c * (8 * (k + cH + 4) * (Nat.size (n + 1) + 1)))
          = (16 * c * (k + cH + 4)) * (Nat.size (n + 1) + 1) := h1
        _ ≤ (16 * (c + 1) * (k + cH + 4)) * (Nat.size (n + 1) + 1) :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega))
        _ ≤ padRoot r n := hlogC
        _ ≤ n := padRoot_le r n
    have hmul_sum := Nat.mul_le_mul_left c (hadv_len_le n)
    rw [Nat.mul_add] at hmul_sum; omega
  · have hlog := eventually_mul_size_le_padRoot r (2 * k + 16 + 4 * cH)
    rw [eventually_atTop] at hlog ⊢
    obtain ⟨M₁, hM₁⟩ := hlog
    refine ⟨max M₁ 2, fun n hn => ?_⟩
    have hpr := hM₁ n ((le_max_left _ _).trans hn)
    have hC_s : (genH n).2.size ≤ cH * (n + 1) ^ k := hgenH_size n
    have hbase : n + 2 * (genH n).2.size + 1 ≤ (2 * cH + 2) * (n + 1) ^ k := by
      have h1 : n + 1 ≤ (n + 1) ^ k := Nat.le_self_pow (by omega) (n + 1)
      have e : (2 * cH + 2) * (n + 1) ^ k =
          2 * (cH * (n + 1) ^ k) + (n + 1) ^ k + (n + 1) ^ k := by ring
      omega
    have hbound1 : (certEncode (genH n).2).length ≤ 3 * (2 * cH + 2) ^ 2 * (n + 1) ^ (2 * k) := by
      calc (certEncode (genH n).2).length
          ≤ 3 * (n + 2 * (genH n).2.size + 1) ^ 2 := certEncode_length_sq _ (hgenH_arity n)
        _ ≤ 3 * ((2 * cH + 2) * (n + 1) ^ k) ^ 2 :=
            Nat.mul_le_mul_left 3 (Nat.pow_le_pow_left hbase 2)
        _ = 3 * (2 * cH + 2) ^ 2 * (n + 1) ^ (2 * k) := by
            rw [mul_pow, ← pow_mul, Nat.mul_comm k 2]; ring
    have hpow2k : (n + 1) ^ (2 * k) ≤ 2 ^ (2 * k * Nat.size (n + 1)) := by
      calc (n + 1) ^ (2 * k) ≤ (2 ^ Nat.size (n + 1)) ^ (2 * k) :=
            Nat.pow_le_pow_left (Nat.lt_size_self (n + 1)).le _
        _ = 2 ^ (2 * k * Nat.size (n + 1)) := by rw [← pow_mul, Nat.mul_comm]
    have hconst : 3 * (2 * cH + 2) ^ 2 < 2 ^ (4 * cH + 12) := by
      have hc2 : (2 * cH + 2) ^ 2 < 2 ^ (4 * cH + 4) := by
        calc (2 * cH + 2) ^ 2 < (2 ^ (2 * cH + 2)) ^ 2 :=
              Nat.pow_lt_pow_left Nat.lt_two_pow_self (by norm_num)
          _ = 2 ^ (4 * cH + 4) := by rw [← pow_mul]; congr 1; ring
      have hc4 : 4 * 2 ^ (4 * cH + 4) = 2 ^ (4 * cH + 6) := by
        rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]; congr 1; omega
      have hc5 : 2 ^ (4 * cH + 6) ≤ 2 ^ (4 * cH + 12) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have htot_lt : (certEncode (genH n).2).length <
        2 ^ (4 * cH + 12 + 2 * k * Nat.size (n + 1)) := by
      rw [pow_add]; exact hbound1.trans_lt (lt_of_le_of_lt (Nat.mul_le_mul_left _ hpow2k)
        (Nat.mul_lt_mul_of_pos_right hconst Nat.one_le_two_pow))
    have hexp_le : 4 * cH + 12 + 2 * k * Nat.size (n + 1) ≤ padRoot r n := by
      have e : (2 * k + 16 + 4 * cH) * (Nat.size (n + 1) + 1) =
          2 * k * Nat.size (n + 1) + 16 * Nat.size (n + 1) + 4 * cH * Nat.size (n + 1) +
            2 * k + 16 + 4 * cH := by ring
      exact (by omega : 4 * cH + 12 + 2 * k * Nat.size (n + 1) ≤
        (2 * k + 16 + 4 * cH) * (Nat.size (n + 1) + 1)).trans hpr
    exact htot_lt.trans_le (Nat.pow_le_pow_right (by norm_num) hexp_le)

private lemma speedup_large_iff {k r cH cP cN b : ℕ} (hk : 1 ≤ k)
    (genH : ℕ → Σ n, WitnessCircuit n) (hgenH_arity : ∀ n, (genH n).1 = n)
    (hgenH_size : ∀ n, (genH n).2.size ≤ cH * (n + 1) ^ k)
    (hgenH_dec : ∀ n (x : Fin n → Bool),
      List.ofFn x ∈ hardLanguage b ↔ (genH n).2.NondetAccepts (x ∘ Fin.cast (hgenH_arity n)))
    (genP : ℕ → Σ n, WitnessCircuit n) (hgenP_arity : ∀ n, (genP n).1 = n)
    (hgenP_dec : ∀ n (x : Fin n → Bool),
      List.ofFn x ∈ pDCL genH (padRoot r) ↔
        (genP n).2.NondetAccepts (x ∘ Fin.cast (hgenP_arity n)))
    (genN : ℕ → Σ n, WitnessCircuit n) (hgenN_arity : ∀ n, (genN n).1 = n)
    (hgenN_dec : ∀ n (x : Fin n → Bool),
      List.ofFn x ∈ nDCL genH (padRoot r) ↔
        (genN n).2.NondetAccepts (x ∘ Fin.cast (hgenN_arity n)))
    (x : List Bool) (hcert_n : (certEncode (genH x.length).2).length < 2 ^ padRoot r x.length)
    (adv : List Bool)
    (hadv_eq : adv =
      let n := x.length
      let M := (encPair encNat encBits (n, List.replicate (padRoot r n) false)).length
      let C := (genH n).2; let Dp := (genP M).2; let Dn := (genN M).2
      frame (List.replicate (padRoot r n) true) ++ frame (List.replicate Dp.witnessLen true) ++
      frame (List.replicate Dp.size true) ++ frame (List.replicate Dn.witnessLen true) ++
      frame (List.replicate Dn.size true) ++ frame (certEncode Dp) ++ frame (certEncode Dn) ++
      frame (encNat C.witnessLen) ++ encNat C.size)
    (hadv_n : adv.length ≤ x.length) :
    x ∈ hardLanguage b ↔
      ∃ W : List Bool,
        W.length = (16 * (cH + cP + cN + 4) ^ 2 * 16 + 100) * (x.length + 1) ^ (2 * k + 2) ∧
        speedupVerifier ((adv, x), W) = true := by
  set n := x.length with hn_def
  set M := (encPair encNat encBits (n, List.replicate (padRoot r n) false)).length
  set CW := 16 * (cH + cP + cN + 4) ^ 2 * 16 + 100
  generalize hC_eq : (genH n).2 = C; generalize hDp_eq : (genP M).2 = Dp
  generalize hDn_eq : (genN M).2 = Dn
  have hC_ar : (genH n).1 = n := hgenH_arity n
  have hDp_ar : (genP M).1 = M := hgenP_arity M
  have hDn_ar : (genN M).1 = M := hgenN_arity M
  rw [hC_eq] at hcert_n
  have hC_size : C.size ≤ cH * (n + 1) ^ k := hC_eq ▸ hgenH_size n
  have hC_dec : x ∈ hardLanguage b ↔
      C.NondetAccepts (BitString.ofList n x ∘ Fin.cast hC_ar) := by
    have h1 := hgenH_dec n (BitString.ofList n x)
    rw [BitString.ofFn_ofList hn_def.symm] at h1; simpa [hC_eq] using h1
  have hP_dec : ∀ u : Fin M → Bool,
      List.ofFn u ∈ pDCL genH (padRoot r) ↔ Dp.NondetAccepts (u ∘ Fin.cast hDp_ar) :=
    fun u => by simpa [hDp_eq] using hgenP_dec M u
  have hN_dec : ∀ u : Fin M → Bool,
      List.ofFn u ∈ nDCL genH (padRoot r) ↔ Dn.NondetAccepts (u ∘ Fin.cast hDn_ar) :=
    fun u => by simpa [hDn_eq] using hgenN_dec M u
  dsimp only at hadv_eq
  rw [hC_eq, hDp_eq, hDn_eq] at hadv_eq
  have hunp_mPad : (unframe adv).length = padRoot r n := by
    simp only [hadv_eq, List.append_assoc, unframe_frame_append, List.length_replicate]
  have hunp_wp : (unframe (dropFrame adv)).length = Dp.witnessLen := by
    simp only [hadv_eq, List.append_assoc, dropFrame_frame_append, unframe_frame_append,
      List.length_replicate]
  have hunp_sp : (unframe (dropFrame (dropFrame adv))).length = Dp.size := by
    simp only [hadv_eq, List.append_assoc, dropFrame_frame_append, unframe_frame_append,
      List.length_replicate]
  have hunp_wn : (unframe (dropFrame (dropFrame (dropFrame adv)))).length = Dn.witnessLen := by
    simp only [hadv_eq, List.append_assoc, dropFrame_frame_append, unframe_frame_append,
      List.length_replicate]
  have hunp_sn : (unframe (dropFrame (dropFrame (dropFrame (dropFrame adv))))).length =
    Dn.size := by
    simp only [hadv_eq, List.append_assoc, dropFrame_frame_append, unframe_frame_append,
      List.length_replicate]
  have hunp_certP :
      unframe (dropFrame (dropFrame (dropFrame (dropFrame (dropFrame adv))))) = certEncode Dp := by
    simp only [hadv_eq, List.append_assoc, dropFrame_frame_append, unframe_frame_append]
  have hunp_certN :
      unframe (dropFrame (dropFrame (dropFrame (dropFrame (dropFrame (dropFrame adv)))))) =
        certEncode Dn := by
    simp only [hadv_eq, List.append_assoc, dropFrame_frame_append, unframe_frame_append]
  have hunp_bwC :
      unframe (dropFrame (dropFrame (dropFrame (dropFrame (dropFrame (dropFrame
        (dropFrame adv))))))) = encNat C.witnessLen := by
    simp only [hadv_eq, List.append_assoc, dropFrame_frame_append, unframe_frame_append]
  have hunp_bsC :
      dropFrame (dropFrame (dropFrame (dropFrame (dropFrame (dropFrame (dropFrame
        (dropFrame adv))))))) = encNat C.size := by
    simp only [hadv_eq, List.append_assoc, dropFrame_frame_append]
  have hrcP := readCertificate_certEncode Dp hDp_ar
  have hrcN := readCertificate_certEncode Dn hDn_ar
  have hrcC := readCertificate_certEncode C hC_ar
  have hM_eq : (encPair encNat encBits (n, List.replicate (padRoot r n) false)).length = M := rfl
  have h_ui_len : ∀ i, (encPair encNat encBits (n, BitString.lowBits (padRoot r n) i)).length = M :=
    fun i => by simp [M, BitString.length_lowBits]
  constructor
  · intro hx
    rw [hC_dec] at hx
    obtain ⟨yC, hyC⟩ := hx
    let wCbits : List Bool := List.ofFn yC
    let wMax : ℕ := max Dp.witnessLen Dn.witnessLen
    have hrow_ex : ∀ i < (certEncode C).length,
        ∃ wi : List Bool, wi.length = wMax ∧
          let ui := encPair encNat encBits (n, BitString.lowBits (padRoot r n) i)
          (if (certEncode C).getD i false then
            Boolean.evalOutput (ui ++ wi.take Dp.witnessLen) Dp.circuit.code.1
              (Dp.circuit.outputs 0).toNat
          else
            Boolean.evalOutput (ui ++ wi.take Dn.witnessLen) Dn.circuit.code.1
              (Dn.circuit.outputs 0).toNat) = true := by
      intro i hi
      have hipow : i < 2 ^ padRoot r n := hi.trans hcert_n
      set ui := encPair encNat encBits (n, BitString.lowBits (padRoot r n) i)
      have huilen : ui.length = M := h_ui_len i
      cases hbit : (certEncode C).getD i false
      · have hui_mem : ui ∈ nDCL genH (padRoot r) :=
          ⟨n, i, rfl, hipow, by simpa [hC_eq] using hi, by simpa [hC_eq] using hbit⟩
        have hacc := (hN_dec (BitString.ofList M ui)).mp (by rwa [BitString.ofFn_ofList huilen])
        obtain ⟨yn, hyn⟩ := hacc
        let wi := List.ofFn yn ++ List.replicate (wMax - Dn.witnessLen) false
        refine ⟨wi, by simp [wi, wMax], ?_⟩
        simp only [Bool.false_eq_true, ↓reduceIte]
        have htake : wi.take Dn.witnessLen = List.ofFn yn := by simp [wi]
        rw [htake, evalOutput_append_eq Dn hDn_ar ui (List.ofFn yn) huilen List.length_ofFn]
        simpa [BitString.ofList_ofFn] using hyn
      · have hui_mem : ui ∈ pDCL genH (padRoot r) :=
          ⟨n, i, rfl, hipow, by simpa [hC_eq] using hi, by simpa [hC_eq] using hbit⟩
        have hacc := (hP_dec (BitString.ofList M ui)).mp (by rwa [BitString.ofFn_ofList huilen])
        obtain ⟨yp, hyp⟩ := hacc
        let wi := List.ofFn yp ++ List.replicate (wMax - Dp.witnessLen) false
        refine ⟨wi, by simp [wi, wMax], ?_⟩
        simp only [↓reduceIte]
        have htake : wi.take Dp.witnessLen = List.ofFn yp := by simp [wi]
        rw [htake, evalOutput_append_eq Dp hDp_ar ui (List.ofFn yp) huilen List.length_ofFn]
        simpa [BitString.ofList_ofFn] using hyp
    let rowFn : ℕ → List Bool := fun i =>
      if hi : i < (certEncode C).length then (hrow_ex i hi).choose else List.replicate wMax false
    have hrow_len : ∀ i, (rowFn i).length = wMax := fun i => by
      dsimp only [rowFn]
      by_cases hi : i < (certEncode C).length
      · simp only [hi, ↓reduceDIte]; exact (hrow_ex i hi).choose_spec.1
      · simp only [hi, ↓reduceDIte, List.length_replicate]
    let wsFlat : List Bool := (List.range (certEncode C).length).flatMap rowFn
    let Wcore : List Bool :=
      frame (List.replicate C.witnessLen true) ++ frame (List.replicate C.size true) ++
      frame (certEncode C) ++ frame wCbits ++ wsFlat
    have hWcore_le : Wcore.length ≤ CW * (n + 1) ^ (2 * k + 2) := by
      have hwmax_le : wMax ≤ n := by
        have hwp_le : Dp.witnessLen ≤ adv.length := by
          simp only [hadv_eq, List.length_append, length_frame, List.length_replicate]; omega
        have hwn_le : Dn.witnessLen ≤ adv.length := by
          simp only [hadv_eq, List.length_append, length_frame, List.length_replicate]; omega
        dsimp only [wMax]; omega
      have hws_len : wsFlat.length = (certEncode C).length * wMax := by
        simp only [wsFlat, List.length_flatMap, hrow_len, List.map_const', List.sum_replicate,
          smul_eq_mul, List.length_range]
      have hCw : C.witnessLen ≤ C.size := le_max_right _ _
      have hCcert : (certEncode C).length ≤ 3 * ((2 * cH + 2) * (n + 1) ^ k) ^ 2 := by
        refine (certEncode_length_sq C hC_ar).trans
          (Nat.mul_le_mul_left 3 (Nat.pow_le_pow_left ?_ 2))
        have h2 : n + 1 ≤ (n + 1) ^ k := Nat.le_self_pow (by omega) (n + 1)
        have e : (2 * cH + 2) * (n + 1) ^ k =
            2 * (cH * (n + 1) ^ k) + (n + 1) ^ k + (n + 1) ^ k := by ring
        omega
      set SC := (cH + cP + cN + 4) ^ 2 * (n + 1) ^ (2 * k + 2)
      have hpow1 : (n + 1) ^ k ≤ (n + 1) ^ (2 * k + 2) :=
        Nat.pow_le_pow_right (Nat.succ_pos _) (by omega)
      have hpow2 : (n + 1) ^ (2 * k) ≤ (n + 1) ^ (2 * k + 2) :=
        Nat.pow_le_pow_right (Nat.succ_pos _) (by omega)
      have hCcert_2k : (certEncode C).length ≤ 12 * (cH + cP + cN + 4) ^ 2 * (n + 1) ^ (2 * k) := by
        have h1 : (2 * cH + 2) ^ 2 ≤ 4 * (cH + cP + cN + 4) ^ 2 :=
          (Nat.pow_le_pow_left (show 2 * cH + 2 ≤ 2 * (cH + cP + cN + 4) by omega) 2).trans_eq
            (by ring)
        calc (certEncode C).length ≤ 3 * ((2 * cH + 2) ^ 2 * (n + 1) ^ (2 * k)) := by
              simpa [mul_pow, ← pow_mul, Nat.mul_comm k 2] using hCcert
          _ ≤ 3 * (4 * (cH + cP + cN + 4) ^ 2 * (n + 1) ^ (2 * k)) :=
              Nat.mul_le_mul_left 3 (Nat.mul_le_mul_right _ h1)
          _ = 12 * (cH + cP + cN + 4) ^ 2 * (n + 1) ^ (2 * k) := by ring
      have hCcert2 : (certEncode C).length ≤ 12 * SC :=
        hCcert_2k.trans (by
          dsimp only [SC]; have h :=
            Nat.mul_le_mul_left (12 * (cH + cP + cN + 4) ^ 2) hpow2; linarith)
      have hws_le : wsFlat.length ≤ 12 * SC := by
        have hpow3 : (n + 1) ^ (2 * k) * n ≤ (n + 1) ^ (2 * k + 2) :=
          (Nat.mul_le_mul_left _ (Nat.le_succ n)).trans
            (by rw [← pow_succ]; exact Nat.pow_le_pow_right (Nat.succ_pos _) (by omega))
        rw [hws_len]
        calc (certEncode C).length * wMax
            ≤ (12 * (cH + cP + cN + 4) ^ 2 * (n + 1) ^ (2 * k)) * n :=
              Nat.mul_le_mul hCcert_2k hwmax_le
          _ = 12 * (cH + cP + cN + 4) ^ 2 * ((n + 1) ^ (2 * k) * n) := by ring
          _ ≤ 12 * (cH + cP + cN + 4) ^ 2 * (n + 1) ^ (2 * k + 2) := Nat.mul_le_mul_left _ hpow3
          _ = 12 * SC := by dsimp [SC]; ring
      have hcH_sq : cH ≤ (cH + cP + cN + 4) ^ 2 :=
        (show cH ≤ cH + cP + cN + 4 by omega).trans (Nat.le_self_pow (by norm_num) _)
      have h1 : cH * (n + 1) ^ k ≤ SC := Nat.mul_le_mul hcH_sq hpow1
      have h2 : 1 ≤ (n + 1) ^ (2 * k + 2) := Nat.pow_pos (Nat.succ_pos _)
      have hCW_exp : CW * (n + 1) ^ (2 * k + 2) = 256 * SC + 100 * (n + 1) ^ (2 * k + 2) := by
        dsimp [CW, SC]; ring
      simp only [Wcore, List.length_append, length_frame, List.length_replicate,
        wCbits, List.length_ofFn]
      omega
    let W : List Bool := Wcore ++ List.replicate (CW * (n + 1) ^ (2 * k + 2) - Wcore.length) false
    refine ⟨W, by simp [W]; omega, ?_⟩
    simp only [speedupVerifier, ← hn_def, hunp_mPad, hunp_wp, hunp_sp, hunp_wn, hunp_sn,
      hunp_certP, hunp_certN, hunp_bwC, hunp_bsC, hM_eq, hrcP, hrcN]
    have hW_u : (unframe W).length = C.witnessLen := by
      simp [W, Wcore, List.append_assoc, unframe_frame_append]
    have hW_s : (unframe (dropFrame W)).length = C.size := by
      simp [W, Wcore, List.append_assoc, dropFrame_frame_append, unframe_frame_append]
    have hW_y : unframe (dropFrame (dropFrame W)) = certEncode C := by
      simp [W, Wcore, List.append_assoc, dropFrame_frame_append, unframe_frame_append]
    have hW_wc : unframe (dropFrame (dropFrame (dropFrame W))) = wCbits := by
      simp [W, Wcore, List.append_assoc, dropFrame_frame_append, unframe_frame_append]
    have hW_ws : dropFrame (dropFrame (dropFrame (dropFrame W))) =
        wsFlat ++ List.replicate (CW * (n + 1) ^ (2 * k + 2) - Wcore.length) false := by
      simp [W, Wcore, List.append_assoc, dropFrame_frame_append]
    rw [hW_u, hW_s, hW_y, hW_wc, hW_ws, hrcC]
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range, true_and]
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · rw [certEncode_length C]; congr 2
    · simp [wCbits]
    · intro i hi
      have hrow_i : BitString.listRow wMax i
          (wsFlat ++ List.replicate (CW * (n + 1) ^ (2 * k + 2) - Wcore.length) false) =
          rowFn i := by
        have := BitString.listRow_flatMap_append rowFn (List.range (certEncode C).length)
          (fun j _ => hrow_len j)
          (List.replicate (CW * (n + 1) ^ (2 * k + 2) - Wcore.length) false) i (by simpa using hi)
        simpa [wsFlat] using this
      rw [hrow_i]
      simpa [rowFn, hi, wMax] using (hrow_ex i hi).choose_spec.2
    · rw [evalOutput_append_eq C hC_ar x (List.ofFn yC) hn_def.symm List.length_ofFn]
      simpa [BitString.ofList_ofFn] using hyC
  · rintro ⟨W, _, hV⟩
    simp only [speedupVerifier, ← hn_def, hunp_mPad, hunp_wp, hunp_sp, hunp_wn, hunp_sn,
      hunp_certP, hunp_certN, hunp_bwC, hunp_bsC, hM_eq, hrcP, hrcN,
      Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at hV
    rcases hV with ⟨⟨⟨⟨⟨hwC_eq, hsC_eq⟩, hy_len⟩, hwc_len⟩, hall_i⟩, hevalC⟩
    have hwC : (unframe W).length = C.witnessLen := encNat.injective hwC_eq
    have hsC : (unframe (dropFrame W)).length = C.size := encNat.injective hsC_eq
    set y := unframe (dropFrame (dropFrame W))
    set wCbits := unframe (dropFrame (dropFrame (dropFrame W)))
    set wsFlat := dropFrame (dropFrame (dropFrame (dropFrame W)))
    rw [hwC] at hy_len hwc_len hevalC; rw [hsC] at hy_len hevalC
    have hy_eq_len : y.length = (certEncode C).length := by
      rw [hy_len, certEncode_length C]; congr 2; exact hC_ar.symm
    have hy_eq : y = certEncode C := by
      refine List.ext_getElem hy_eq_len fun i hi hi' => ?_
      have hstep := hall_i i hi
      have hipow : i < 2 ^ padRoot r n := hi'.trans hcert_n
      set ui := encPair encNat encBits (n, BitString.lowBits (padRoot r n) i)
      have huilen : ui.length = M := h_ui_len i
      have hget : y.getD i false = y[i] := by simp [List.getD, hi]
      have hgetC : (certEncode C).getD i false = (certEncode C)[i] := by simp [List.getD, hi']
      rw [hget] at hstep; cases hyi : y[i]
      · rw [hyi] at hstep; simp only [Bool.false_eq_true, ↓reduceIte] at hstep
        have htake_len :
            ((BitString.listRow (max Dp.witnessLen Dn.witnessLen) i wsFlat).take
              Dn.witnessLen).length = Dn.witnessLen := by simp [BitString.length_listRow]
        rw [evalOutput_append_eq Dn hDn_ar ui _ huilen htake_len] at hstep
        have hui_mem := (hN_dec (BitString.ofList M ui)).mpr ⟨_, hstep⟩
        rw [BitString.ofFn_ofList huilen] at hui_mem
        rcases hui_mem with ⟨n', i', heq_ui, hi'pow, _, hbitC⟩
        have hpair := Prod.mk.inj ((encPair encNat encBits).injective heq_ui)
        have hn' : n' = n := hpair.1.symm; subst hn'
        have hi' : i' = i := by
          have h2 := congrArg ofBits hpair.2
          rw [ofBits_lowBits hi'pow, ofBits_lowBits hipow] at h2; exact h2.symm
        subst hi'; rw [hC_eq, hgetC] at hbitC; exact hbitC.symm
      · rw [hyi] at hstep; simp only [↓reduceIte] at hstep
        have htake_len :
            ((BitString.listRow (max Dp.witnessLen Dn.witnessLen) i wsFlat).take
              Dp.witnessLen).length = Dp.witnessLen := by simp [BitString.length_listRow]
        rw [evalOutput_append_eq Dp hDp_ar ui _ huilen htake_len] at hstep
        have hui_mem := (hP_dec (BitString.ofList M ui)).mpr ⟨_, hstep⟩
        rw [BitString.ofFn_ofList huilen] at hui_mem
        rcases hui_mem with ⟨n', i', heq_ui, hi'pow, _, hbitC⟩
        have hpair := Prod.mk.inj ((encPair encNat encBits).injective heq_ui)
        have hn' : n' = n := hpair.1.symm; subst hn'
        have hi' : i' = i := by
          have h2 := congrArg ofBits hpair.2
          rw [ofBits_lowBits hi'pow, ofBits_lowBits hipow] at h2; exact h2.symm
        subst hi'; rw [hC_eq, hgetC] at hbitC; exact hbitC.symm
    rw [hy_eq, hrcC] at hevalC
    rw [hC_dec, evalOutput_append_eq C hC_ar x wCbits hn_def.symm hwc_len] at *
    exact ⟨_, hevalC⟩

/-- ** (coNP side)**: for every `k ≥ 1`, `coNP` does not have `P`-uniform
nondeterministic circuits of size `O(n^k)`.
-/
theorem not_coNP_subset_PUniformNSIZE (k : ℕ) (hk : 1 ≤ k) :
    ¬ ∀ L ∈ coNP encBits, ∃ c : ℕ, L ∈ PUniformNSIZE (fun n => c * (n + 1) ^ k) := by
  intro hall
  obtain ⟨TV, SV, hTV, hSV, hV_inO⟩ := computableInPolyTime_speedupVerifier.exists_computableInO
  obtain ⟨CV, dV, hTV_le⟩ := hTV.exists_le
  obtain ⟨CS, dS, hSV_le⟩ := hSV.exists_le
  obtain ⟨r, hr⟩ : ∃ r : ℕ, 4 * k + 4 ≤ 2 ^ r :=
    ⟨4 * k + 4, (by omega : 4 * k + 4 ≤ 4 * k + 4).trans Nat.lt_two_pow_self.le⟩
  let dMax := max (max dV dS) 1
  have hdMax : 1 ≤ dMax := le_max_right _ _
  let b : ℕ := (2 * k + 2) * dMax + 1
  have hb : 1 ≤ b := by omega
  have hHb_coNTIME : hardLanguage b ∈ coNTIME encBits (fun n => (n + 1) ^ (b + 1)) :=
    hardLanguage_mem_coNTIME b hb
  have hHb_coNP : hardLanguage b ∈ coNP encBits := by
    rw [mem_coNP]
    refine (mem_NP_iff_exists_mem_NTIME (enc := encBits)).mpr ⟨b + 2, ?_⟩
    refine NTIME_mono_of_eventually_le ?_ (mem_coNTIME_iff.mp hHb_coNTIME)
    rw [eventually_atTop]
    refine ⟨2 ^ (b + 1), fun n hn => ?_⟩
    have hn1 : n + 1 ≤ 2 * n := by have := Nat.one_le_two_pow (n := b + 1); omega
    calc (n + 1) ^ (b + 1) ≤ (2 * n) ^ (b + 1) := Nat.pow_le_pow_left hn1 _
      _ = 2 ^ (b + 1) * n ^ (b + 1) := mul_pow 2 n (b + 1)
      _ ≤ n * n ^ (b + 1) := Nat.mul_le_mul_right _ hn
      _ = n ^ (b + 2) := by rw [← pow_succ']
  obtain ⟨cH, genH, hgenH_arity, hgenH_pt, hgenH_size, hgenH_dec⟩ := hall _ hHb_coNP
  have hpDCL_coNP : pDCL genH (padRoot r) ∈ coNP encBits :=
    P_subset_coNP (pDCL_mem_P genH hgenH_pt r)
  have hnDCL_coNP : nDCL genH (padRoot r) ∈ coNP encBits :=
    P_subset_coNP (nDCL_mem_P genH hgenH_pt r)
  obtain ⟨cP, genP, hgenP_arity, _, hgenP_size, hgenP_dec⟩ := hall _ hpDCL_coNP
  obtain ⟨cN, genN, hgenN_arity, _, hgenN_size, hgenN_dec⟩ := hall _ hnDCL_coNP
  let Mfn : ℕ → ℕ := fun n =>
    (encPair encNat encBits (n, List.replicate (padRoot r n) false)).length
  let advice : ℕ → List Bool := fun n =>
    let C := (genH n).2
    let Dp := (genP (Mfn n)).2
    let Dn := (genN (Mfn n)).2
    frame (List.replicate (padRoot r n) true) ++
    frame (List.replicate Dp.witnessLen true) ++
    frame (List.replicate Dp.size true) ++
    frame (List.replicate Dn.witnessLen true) ++
    frame (List.replicate Dn.size true) ++
    frame (certEncode Dp) ++
    frame (certEncode Dn) ++
    frame (encNat C.witnessLen) ++
    encNat C.size
  obtain ⟨hadv_sub, hcert_lt_pow⟩ := speedup_advice_sublinear hk hr
    genH hgenH_arity hgenH_size genP hgenP_arity hgenP_size genN hgenN_arity hgenN_size
  obtain ⟨N_adv, hN_adv⟩ := hadv_sub 1
  rw [eventually_atTop] at hcert_lt_pow
  obtain ⟨N_cert, hN_cert⟩ := hcert_lt_pow
  let N₀ := max N_adv N_cert
  let CW : ℕ := 16 * (cH + cP + cN + 4) ^ 2 * 16 + 100
  have hCW_pos : 1 ≤ CW := by dsimp [CW]; omega
  classical
  let small : List (List Bool) :=
    ((List.range N₀).flatMap BitString.enumList).filter (fun x => decide (x ∈ hardLanguage b))
  let Vfinal : (List Bool × List Bool) × List Bool → Bool := fun q =>
    if q.1.2.length < N₀ then small.contains q.1.2 else speedupVerifier q
  let LW : List Bool × List Bool → ℕ := fun p => CW * (p.2.length + 1) ^ (2 * k + 2)
  have hLW_inO : ComputableInO LW (encPair encBits encBits) encUnary
      (fun p => (encPair encBits encBits p).length + CW * (p.2.length + 1) ^ (2 * k + 2))
      (fun p => (encPair encBits encBits p).length + CW * (p.2.length + 1) ^ (2 * k + 2)) := by
    have htc := timeConstructible_mul_succ_pow CW (2 * k + 2) hCW_pos (by omega)
    have h1 := (ComputableInO.natToUnary.comp htc.computableInO).comp
      (ComputableInO.snd encBits encBits)
    refine h1.mono 4 (fun p => by omega) (fun p => by omega)
  have hVfinal_inO : ComputableInO Vfinal (encPair (encPair encBits encBits) encBits) encBool
      (fun q => ((encPair (encPair encBits encBits) encBits q).length + 1) ^ dMax)
      (fun q => ((encPair (encPair encBits encBits) encBits q).length + 1) ^ dMax) := by
    have hq_fst := ComputableInO.fst (encPair encBits encBits) encBits
    have hq_x := (ComputableInO.snd encBits encBits).comp hq_fst
    have h_lt := (computableInO_length_lt N₀).comp hq_x
    have h_sm := (computableInO_mem_const_list small).comp hq_x
    have hite := h_lt.ite h_sm hV_inO
    have haux : ∀ q : (List Bool × List Bool) × List Bool,
        let L := (encPair (encPair encBits encBits) encBits q).length
        let T := L + (encPair encBits encBits q.1).length + q.1.2.length
        T + (if decide (q.1.2.length < N₀) then T else TV q) ≤
          (CV + 12) * ((L + 1) ^ dMax + 1) ∧
        T + (if decide (q.1.2.length < N₀) then T else SV q) ≤
          (CS + 12) * ((L + 1) ^ dMax + 1) := by
      intro q L T
      have h1 : (encPair encBits encBits q.1).length ≤ L := by
        simp only [L, length_encPair]; omega
      have h2 : q.1.2.length ≤ (encPair encBits encBits q.1).length := by
        simp only [length_encPair, encBits_apply]; omega
      have hT_le : T ≤ 3 * L := by
        change L + (encPair encBits encBits q.1).length + q.1.2.length ≤ 3 * L
        omega
      have hLpow : L + 1 ≤ (L + 1) ^ dMax := Nat.le_self_pow (by omega) (L + 1)
      have hTVq : TV q ≤ CV * (L + 1) ^ dMax :=
        (hTV_le q).trans (Nat.mul_le_mul_left CV
          (Nat.pow_le_pow_right (Nat.succ_pos _) (le_trans (le_max_left _ _) (le_max_left _ _))))
      have hSVq : SV q ≤ CS * (L + 1) ^ dMax :=
        (hSV_le q).trans (Nat.mul_le_mul_left CS
          (Nat.pow_le_pow_right (Nat.succ_pos _) (le_trans (le_max_right _ _) (le_max_left _ _))))
      have eV : (CV + 12) * ((L + 1) ^ dMax + 1) =
          CV * (L + 1) ^ dMax + 12 * (L + 1) ^ dMax + CV + 12 := by ring
      have eS : (CS + 12) * ((L + 1) ^ dMax + 1) =
          CS * (L + 1) ^ dMax + 12 * (L + 1) ^ dMax + CS + 12 := by ring
      constructor <;> split_ifs <;> omega
    refine (hite.mono (CV + CS + 12) (fun q => ?_) (fun q => ?_)).of_enc_eq fun q => ?_
    · have h := (haux q).1; dsimp only [Function.comp_apply] at h ⊢
      have h1 := Nat.mul_le_mul_right (((encPair (encPair encBits encBits) encBits q).length + 1) ^
        dMax + 1) (show CV + 12 ≤ CV + CS + 12 by omega)
      omega
    · have h := (haux q).2; dsimp only [Function.comp_apply] at h ⊢
      have h1 := Nat.mul_le_mul_right (((encPair (encPair encBits encBits) encBits q).length + 1) ^
        dMax + 1) (show CS + 12 ≤ CV + CS + 12 by omega)
      omega
    · dsimp only [Vfinal, Function.comp_apply]
      by_cases h : q.1.2.length < N₀ <;> simp [h]
  let A : Set (List Bool × List Bool) :=
    {p | ∃ w : List Bool, w.length = LW p ∧ Vfinal (p, w) = true}
  have hA_mem : A ∈ NTIME (encPair encBits encBits) (fun m => (m + 1) ^ b) := by
    refine setOf_exists_mem_NTIME (C :=
      (CW + 4) ^ dMax + CW + 4) hLW_inO hVfinal_inO fun p w hw => ?_
    set m := (encPair encBits encBits p).length
    have hxle : p.2.length ≤ m := by simp only [m, length_encPair, encBits_apply]; omega
    have hpow_le : (p.2.length + 1) ^ (2 * k + 2) ≤ (m + 1) ^ (2 * k + 2) :=
      Nat.pow_le_pow_left (by omega) _
    have hq_len : (encPair (encPair encBits encBits) encBits (p, w)).length + 1 ≤
        (CW + 4) * (m + 1) ^ (2 * k + 2) := by
      have h1 : (encPair (encPair encBits encBits) encBits (p, w)).length =
        2 * m + 1 + w.length := by
        simp [m]
      have h2 : m + 1 ≤ (m + 1) ^ (2 * k + 2) := Nat.le_self_pow (by omega) (m + 1)
      have h3 : w.length ≤ CW * (m + 1) ^ (2 * k + 2) := by
        rw [hw]; exact Nat.mul_le_mul_left CW hpow_le
      have e : (CW + 4) * (m + 1) ^ (2 * k + 2) =
          CW * (m + 1) ^ (2 * k + 2) + 4 * (m + 1) ^ (2 * k + 2) := by ring
      omega
    have hq_pow : ((encPair (encPair encBits encBits) encBits (p, w)).length + 1) ^ dMax ≤
        (CW + 4) ^ dMax * (m + 1) ^ b := by
      calc ((encPair (encPair encBits encBits) encBits (p, w)).length + 1) ^ dMax
          ≤ ((CW + 4) * (m + 1) ^ (2 * k + 2)) ^ dMax := Nat.pow_le_pow_left hq_len dMax
        _ = (CW + 4) ^ dMax * (m + 1) ^ ((2 * k + 2) * dMax) := by rw [mul_pow, ← pow_mul]
        _ ≤ (CW + 4) ^ dMax * (m + 1) ^ b :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (Nat.succ_pos _) (by dsimp [b]; omega))
    have hm1 : m ≤ (m + 1) ^ b := (Nat.le_succ m).trans (Nat.le_self_pow (by omega) (m + 1))
    have hLWm : CW * (p.2.length + 1) ^ (2 * k + 2) ≤ CW * (m + 1) ^ b :=
      Nat.mul_le_mul_left CW (hpow_le.trans
        (Nat.pow_le_pow_right (Nat.succ_pos _) (by
          have : 2 * k + 2 ≤ (2 * k + 2) * dMax := Nat.le_mul_of_pos_right _ hdMax
          dsimp [b]; omega)))
    have e : ((CW + 4) ^ dMax + CW + 4) * (m + 1) ^ b =
        (CW + 4) ^ dMax * (m + 1) ^ b + CW * (m + 1) ^ b + 4 * (m + 1) ^ b := by ring
    omega
  have hA_iff : ∀ x : List Bool, x ∈ hardLanguage b ↔ (advice x.length, x) ∈ A := by
    intro x
    set n := x.length with hn_def
    by_cases hlt : n < N₀
    · have hsmall : small.contains x = true ↔ x ∈ hardLanguage b := by
        simp only [small, List.contains_eq_mem, List.mem_filter, List.mem_flatMap,
          List.mem_range, decide_eq_true_eq]
        exact ⟨fun h => h.2, fun hx => ⟨⟨n, hlt, BitString.mem_enumList.mpr hn_def.symm⟩, hx⟩⟩
      have hVf : ∀ w, Vfinal ((advice n, x), w) = small.contains x := fun w => by
        dsimp only [Vfinal]; rw [← hn_def]; simp [hlt]
      simp only [A, Set.mem_ofPred_eq, hVf, hsmall]
      exact ⟨fun hx => ⟨List.replicate (LW (advice n, x)) false, List.length_replicate, hx⟩,
        fun ⟨_, _, hx⟩ => hx⟩
    · have hge : N₀ ≤ n := Nat.le_of_not_lt hlt
      have hadv_n : (advice n).length ≤ x.length := by
        rw [hn_def]; simpa only [one_mul] using hN_adv n (le_trans (le_max_left _ _) hge)
      have hcert_n : (certEncode (genH x.length).2).length < 2 ^ padRoot r x.length :=
        hN_cert n (le_trans (le_max_right _ _) hge)
      have hVf : ∀ w, Vfinal ((advice n, x), w) = speedupVerifier ((advice n, x), w) :=
        fun w => by dsimp only [Vfinal]; rw [← hn_def]; simp [hlt]
      simp only [A, Set.mem_ofPred_eq, hVf, LW, CW, ← hn_def]
      exact speedup_large_iff hk genH hgenH_arity hgenH_size hgenH_dec
        genP hgenP_arity hgenP_dec genN hgenN_arity hgenN_dec x hcert_n
        (advice n) rfl hadv_n
  exact hardLanguage_notMem_NTIMEWithSublinearAdvice b hb
    ⟨fun n => (advice n).length, hadv_sub, advice, fun _ => rfl, A, hA_mem, hA_iff⟩

/-- ** (Uniform Lower Bound)**: for every `k ≥ 1`,
`NP ⊈ P-uniform coNSIZE[O(n^k)]`.
-/
theorem not_NP_subset_PUniformCoNSIZE (k : ℕ) (hk : 1 ≤ k) :
    ¬ ∀ L ∈ NP encBits, ∃ c : ℕ, L ∈ PUniformCoNSIZE (fun n => c * (n + 1) ^ k) := by
  intro hall
  refine not_coNP_subset_PUniformNSIZE k hk fun L hL => ?_
  have hLc : Lᶜ ∈ NP encBits := (mem_coNP (enc := encBits)).mp hL
  obtain ⟨c, hc⟩ := hall Lᶜ hLc
  refine ⟨c + 1, ?_⟩
  have h1 : Lᶜᶜ ∈ PUniformNSIZE (fun n => c * (n + 1) ^ k + 1) :=
    compl_mem_PUniformNSIZE_of_mem_PUniformCoNSIZE hc
  rw [compl_compl] at h1
  rcases h1 with ⟨gen, hgen, hpoly, hsize, hdec⟩
  refine ⟨gen, hgen, hpoly, fun n => (hsize n).trans ?_, hdec⟩
  dsimp only
  have hpos : 1 ≤ (n + 1) ^ k := Nat.pow_pos (Nat.succ_pos _)
  rw [Nat.add_mul, one_mul]; omega

end CslibFrontier.Computability.Complexity
