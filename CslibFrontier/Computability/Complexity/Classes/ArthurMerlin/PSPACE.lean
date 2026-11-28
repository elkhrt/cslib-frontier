module

public import CslibFrontier.Computability.Circuit.Boolean.PPoly
public import CslibFrontier.Computability.Complexity.Classes.ArthurMerlin
public import CslibFrontier.Computability.Complexity.Classes.EXP
public import CslibFrontier.Computability.Complexity.Classes.PH.Kannan
public import CslibFrontier.Computability.Complexity.Classes.Space
import CslibFrontier.Computability.Circuit.Boolean.Advice
import CslibFrontier.Computability.Complexity.Classes.IP.CoinFixing
import CslibFrontier.Computability.Complexity.Classes.IP.Simulation
import CslibFrontier.Computability.Complexity.Classes.IP.TQBF
import CslibFrontier.Computability.Complexity.Classes.Inclusions
import CslibFrontier.Computability.Complexity.Classes.Space.TQBF
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString.BinaryWord
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Configuration
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Finite
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Prime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Search
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Length
import CslibFrontier.Languages.Probabilistic.Oracle.InterpNorm
import Mathlib.Algebra.Field.ZMod
import CslibFrontier.Computability.Complexity.Classes.ArthurMerlin.PSPACEBase

/-!
# `EXP ⊆ P/poly → PSPACE ⊆ MA`

Babai–Fortnow–Nisan–Wigderson collapse of `PSPACE` into `MA` under `EXP ⊆ P/poly`:
the honest prover for the Shamir–Shen interactive proof of `TQBF` (`Cslib.Complexity.QBFProtocol`)
is computable in `EXP` via the explicit-stack polynomial evaluator in
`CslibFrontier.Computability.Complexity.Classes.ArthurMerlin.PSPACEBase`. Under
`EXP ⊆ P/poly`, polynomial-size circuits compute every bit of the honest prover's replies; Merlin
sends the circuit advice string, and Arthur simulates the fixed-coin verifier machine
deterministically against the advice-evaluated prover.

## Main results

* `CslibFrontier.Complexity.pspace_subset_MA_of_exp_subset_ppoly`:
  `EXP encBits ⊆ PPolyOn encBits → PSPACE enc ⊆ MA enc`.
* `CslibFrontier.Complexity.kannan_mem_MA_of_exp_subset_ppoly`:
  `EXP encBits ⊆ PPolyOn encBits → ∀ k, (Kannan.language k : Set (List Bool)) ∈ MA encBits`.
-/

public section

namespace CslibFrontier.Complexity

open Cslib Cslib.Complexity Cslib.Circuits.Boolean Cslib.Logic.PL Cslib.Probability
open Polynomial Turing Turing.MultiTapeTM
open QBFProtocol.Machine (encArithToken)
open QBFProtocol (encPt)
open scoped ENNReal

attribute [local irreducible] ComputableInPolyTime

/-! ### : The honest-prover bit language in `EXP` -/

/-- Query tuple `(p, D, msg, j)` encoded for the `EXP` honest-prover language. -/
private abbrev encHonestQuery : ℕ × ℕ × List Bool × ℕ ↪ List Bool :=
  encPair encUnary (encPair encUnary (encPair encBits encUnary))

private def decodeArithKind (w : List Bool) : ArithQBF.Kind :=
  if w.length = 0 then .var
  else if w.length = 1 then .top
  else if w.length = 2 then .bot
  else if w.length = 3 then .not
  else if w.length = 4 then .and
  else if w.length = 5 then .or
  else if w.length = 6 then .ex
  else if w.length = 7 then .all
  else .lin

private theorem decodeArithKind_enc (k : ArithQBF.Kind) :
    decodeArithKind (encFinEnum ArithQBF.Kind k) = k := by
  cases k <;> decide

private theorem computableInPolyTime_decodeArithKind :
    ComputableInPolyTime decodeArithKind encBits (encFinEnum ArithQBF.Kind) := by
  unfold decodeArithKind
  open ComputableInPolyTime in
  have eqk (n : ℕ) : ComputableInPolyTime (fun w : List Bool => decide (w.length = n))
      encBits encBool := decide_eq' length_bits (const n)
  exact ite_decide (eqk 0) (const ArithQBF.Kind.var)
    (ite_decide (eqk 1) (const ArithQBF.Kind.top)
      (ite_decide (eqk 2) (const ArithQBF.Kind.bot)
        (ite_decide (eqk 3) (const ArithQBF.Kind.not)
          (ite_decide (eqk 4) (const ArithQBF.Kind.and)
            (ite_decide (eqk 5) (const ArithQBF.Kind.or)
              (ite_decide (eqk 6) (const ArithQBF.Kind.ex)
                (ite_decide (eqk 7) (const ArithQBF.Kind.all)
                  (const ArithQBF.Kind.lin))))))))

private def arithKindDec : Decoder (encFinEnum ArithQBF.Kind) where
  decode := decodeArithKind
  decode_enc := decodeArithKind_enc
  computable := computableInPolyTime_decodeArithKind.exists_degree

private def msgDec : Decoder (encPair (encList encArithToken) encPt) :=
  Decoder.pair (Decoder.list (Decoder.pair arithKindDec Decoder.nat))
    (Decoder.list (Decoder.pair Decoder.nat Decoder.unary))

private def honestQueryDec : Decoder encHonestQuery :=
  Decoder.pair Decoder.unary (Decoder.pair Decoder.unary (Decoder.pair Decoder.bits Decoder.unary))

/-- Compute the `D + 1` honest reply residues (each `< posMod p`) for a message `(toks, pt)`
using `fuel` stack-evaluator steps. -/
private def evalHonestCoeffs (p D : ℕ) (toks : List (ArithQBF.Kind × ℕ)) (pt : List (ℕ × ℕ))
    (fuel : ℕ) : List ℕ :=
  match toks with
  | [] => List.replicate (D + 1) 0
  | (k, v) :: rest =>
    match k with
    | .and | .or =>
      let st₁ := (arithStep p D pt none)^[fuel] ⟨rest, [], none⟩
      let st₂ := (arithStep p D pt none)^[fuel] ⟨st₁.input, [], none⟩
      let v₁ := (st₁.value.getD []).getD 0 0 % posMod p
      let v₂ := (st₂.value.getD []).getD 0 0 % posMod p
      (List.range (D + 1)).map fun i => if i = 0 then v₁ else if i = 1 then v₂ else 0
    | .ex | .all | .lin =>
      let st := (arithStep p D pt (some v))^[fuel] ⟨rest, [], none⟩
      let l := st.value.getD []
      (List.range (D + 1)).map fun i => l.getD i 0 % posMod p
    | .var | .top | .bot | .not => List.replicate (D + 1) 0

private theorem length_evalHonestCoeffs (p D : ℕ) (toks : List (ArithQBF.Kind × ℕ))
    (pt : List (ℕ × ℕ)) (fuel : ℕ) :
    (evalHonestCoeffs p D toks pt fuel).length = D + 1 := by
  rcases toks with _ | ⟨⟨k, v⟩, rest⟩
  · simp [evalHonestCoeffs]
  · cases k <;> simp [evalHonestCoeffs]

private theorem lt_posMod_evalHonestCoeffs (p D : ℕ) (toks : List (ArithQBF.Kind × ℕ))
    (pt : List (ℕ × ℕ)) (fuel : ℕ) :
    ∀ a ∈ evalHonestCoeffs p D toks pt fuel, a < posMod p := by
  rcases toks with _ | ⟨⟨k, v⟩, rest⟩
  · intro a ha
    simp only [evalHonestCoeffs, List.mem_replicate] at ha
    rw [ha.2]; exact posMod_pos p
  · cases k <;> intro a ha <;> simp only [evalHonestCoeffs, List.mem_map, List.mem_range,
      List.mem_replicate] at ha
    · rw [ha.2]; exact posMod_pos p
    · rw [ha.2]; exact posMod_pos p
    · rw [ha.2]; exact posMod_pos p
    · rw [ha.2]; exact posMod_pos p
    · rcases ha with ⟨i, _, rfl⟩
      split_ifs <;> first | exact Nat.mod_lt _ (posMod_pos p) | exact posMod_pos p
    · rcases ha with ⟨i, _, rfl⟩
      split_ifs <;> first | exact Nat.mod_lt _ (posMod_pos p) | exact posMod_pos p
    · rcases ha with ⟨i, _, rfl⟩; exact Nat.mod_lt _ (posMod_pos p)
    · rcases ha with ⟨i, _, rfl⟩; exact Nat.mod_lt _ (posMod_pos p)
    · rcases ha with ⟨i, _, rfl⟩; exact Nat.mod_lt _ (posMod_pos p)

/-- Padded honest-prover bit decider: given query `y` and unary `fuel`, outputs the `j`-th bit
of the encoded honest reply. -/
private def honestBitStep (q : List Bool × ℕ) : Bool :=
  let (p, D, msg, j) := honestQueryDec.decode q.1
  let (toks, pt) := msgDec.decode msg
  let coeffs := evalHonestCoeffs p D toks pt q.2
  (QBFProtocol.encodeReply (posMod p) coeffs).getD j false

private theorem computableInPolyTime_encodeReply {γ : Type} {encIn : γ ↪ List Bool}
    {p : γ → ℕ} {l : γ → List ℕ}
    (hp : ComputableInPolyTime p encIn encUnary)
    (hl : ComputableInPolyTime l encIn (encList encUnary)) :
    ComputableInPolyTime (fun x => QBFProtocol.encodeReply (p x) (l x)) encIn encBits := by
  open ComputableInPolyTime in
  have hbw : ComputableInPolyTime
      (fun q : γ × ℕ => BitString.binaryWord (QBFProtocol.width (p q.1)) q.2)
      (encPair encIn encUnary) encBits :=
    binaryWord_polyTime (QBFProtocol.computableInPolyTime_width (hp.comp (.fst encIn encUnary)))
      (unary_to_binary.comp (.snd encIn encUnary))
  have hbwList : ComputableInPolyTime
      (fun q : γ × ℕ => BitString.binaryWord (QBFProtocol.width (p q.1)) q.2)
      (encPair encIn encUnary) (encList encBool) :=
    (bits_encList_polyTime encBool).1.comp hbw
  exact (bits_encList_polyTime encBool).2.comp (flatMapWithInput hl hbwList)

private theorem computableInPolyTime_honestBitStep :
    ComputableInPolyTime honestBitStep (encPair encBits encUnary) encBool := by
  open ComputableInPolyTime in
  let encQ := encPair encBits encUnary
  have hdec : ComputableInPolyTime (fun q : List Bool × ℕ => honestQueryDec.decode q.1)
      encQ encHonestQuery := honestQueryDec.computableInPolyTime.comp (.fst encBits encUnary)
  have hp : ComputableInPolyTime (fun q : List Bool × ℕ => (honestQueryDec.decode q.1).1)
      encQ encUnary := (fst _ _).comp hdec
  have hD : ComputableInPolyTime (fun q : List Bool × ℕ => (honestQueryDec.decode q.1).2.1)
      encQ encUnary := ((fst _ _).comp (snd _ _)).comp hdec
  have hmsg : ComputableInPolyTime (fun q : List Bool × ℕ => (honestQueryDec.decode q.1).2.2.1)
      encQ encBits := ((fst _ _).comp ((snd _ _).comp (snd _ _))).comp hdec
  have hj : ComputableInPolyTime (fun q : List Bool × ℕ => (honestQueryDec.decode q.1).2.2.2)
      encQ encUnary := ((snd _ _).comp ((snd _ _).comp (snd _ _))).comp hdec
  have hmp : ComputableInPolyTime
      (fun q : List Bool × ℕ => msgDec.decode (honestQueryDec.decode q.1).2.2.1)
      encQ (encPair (encList encArithToken) encPt) :=
    msgDec.computableInPolyTime.comp hmsg
  have htoks : ComputableInPolyTime
      (fun q : List Bool × ℕ => (msgDec.decode (honestQueryDec.decode q.1).2.2.1).1)
      encQ (encList encArithToken) := (fst _ _).comp hmp
  have hpt : ComputableInPolyTime
      (fun q : List Bool × ℕ => (msgDec.decode (honestQueryDec.decode q.1).2.2.1).2)
      encQ encPt := (snd _ _).comp hmp
  have hfuel : ComputableInPolyTime (fun q : List Bool × ℕ => q.2) encQ encUnary :=
    snd encBits encUnary
  have hpm := posMod_pt hp
  have hcoeffs : ComputableInPolyTime
      (fun q : List Bool × ℕ =>
        let (p, D, msg, _) := honestQueryDec.decode q.1
        let (toks, pt) := msgDec.decode msg
        evalHonestCoeffs p D toks pt q.2)
      encQ (encList encUnary) := by
    let branchBin : List Bool × ℕ → List ℕ := fun q =>
      let p := (honestQueryDec.decode q.1).1
      let D := (honestQueryDec.decode q.1).2.1
      let toks := (msgDec.decode (honestQueryDec.decode q.1).2.2.1).1
      let pt := (msgDec.decode (honestQueryDec.decode q.1).2.2.1).2
      let st₁ := (arithStep p D pt none)^[q.2] ⟨toks.tail, [], none⟩
      let st₂ := (arithStep p D pt none)^[q.2] ⟨st₁.input, [], none⟩
      let v₁ := (st₁.value.getD []).getD 0 0 % posMod p
      let v₂ := (st₂.value.getD []).getD 0 0 % posMod p
      (List.range (D + 1)).map fun i => if i = 0 then v₁ else if i = 1 then v₂ else 0
    have hbin_pt : ComputableInPolyTime branchBin encQ (encList encUnary) := by
      have hst₁ : ComputableInPolyTime
          (fun q : List Bool × ℕ =>
            let p := (honestQueryDec.decode q.1).1
            let D := (honestQueryDec.decode q.1).2.1
            let toks := (msgDec.decode (honestQueryDec.decode q.1).2.2.1).1
            let pt := (msgDec.decode (honestQueryDec.decode q.1).2.2.1).2
            (arithStep p D pt none)^[q.2] ⟨toks.tail, [], none⟩)
          encQ encArithState :=
        computableInPolyTime_runArith.comp
          ((((hp.prod hD).prod (hpt.prod (const none))).prod
            ((listTail encArithToken).comp htoks)).prod hfuel)
      have hst₂ : ComputableInPolyTime
          (fun q : List Bool × ℕ =>
            let p := (honestQueryDec.decode q.1).1
            let D := (honestQueryDec.decode q.1).2.1
            let toks := (msgDec.decode (honestQueryDec.decode q.1).2.2.1).1
            let pt := (msgDec.decode (honestQueryDec.decode q.1).2.2.1).2
            let st₁ := (arithStep p D pt none)^[q.2] ⟨toks.tail, [], none⟩
            (arithStep p D pt none)^[q.2] ⟨st₁.input, [], none⟩)
          encQ encArithState :=
        computableInPolyTime_runArith.comp
          ((((hp.prod hD).prod (hpt.prod (const none))).prod
            (arithState_input_pt.comp hst₁)).prod hfuel)
      have hv₁ : ComputableInPolyTime
          (fun q : List Bool × ℕ =>
            let p := (honestQueryDec.decode q.1).1
            let D := (honestQueryDec.decode q.1).2.1
            let toks := (msgDec.decode (honestQueryDec.decode q.1).2.2.1).1
            let pt := (msgDec.decode (honestQueryDec.decode q.1).2.2.1).2
            let st₁ := (arithStep p D pt none)^[q.2] ⟨toks.tail, [], none⟩
            (st₁.value.getD []).getD 0 0 % posMod p)
          encQ encUnary := by
        have hval := listGetDWithInput
          (optionGetDWithInput (arithState_value_pt.comp hst₁) (const [])) (const 0) 0
        exact unary_mod' hval hpm
      have hv₂ : ComputableInPolyTime
          (fun q : List Bool × ℕ =>
            let p := (honestQueryDec.decode q.1).1
            let D := (honestQueryDec.decode q.1).2.1
            let toks := (msgDec.decode (honestQueryDec.decode q.1).2.2.1).1
            let pt := (msgDec.decode (honestQueryDec.decode q.1).2.2.1).2
            let st₁ := (arithStep p D pt none)^[q.2] ⟨toks.tail, [], none⟩
            let st₂ := (arithStep p D pt none)^[q.2] ⟨st₁.input, [], none⟩
            (st₂.value.getD []).getD 0 0 % posMod p)
          encQ encUnary := by
        have hval := listGetDWithInput
          (optionGetDWithInput (arithState_value_pt.comp hst₂) (const [])) (const 0) 0
        exact unary_mod' hval hpm
      refine mapWithInput (unary_range' (unary_add' hD (const 1))) ?_
      have hbody : ComputableInPolyTime
          (fun z : (List Bool × ℕ) × ℕ =>
            if decide (z.2 = 0) then
              let p := (honestQueryDec.decode z.1.1).1
              let D := (honestQueryDec.decode z.1.1).2.1
              let toks := (msgDec.decode (honestQueryDec.decode z.1.1).2.2.1).1
              let pt := (msgDec.decode (honestQueryDec.decode z.1.1).2.2.1).2
              ((arithStep p D pt none)^[z.1.2] ⟨toks.tail, [], none⟩ |>.value.getD []).getD 0 0 %
                posMod p
            else if decide (z.2 = 1) then
              let p := (honestQueryDec.decode z.1.1).1
              let D := (honestQueryDec.decode z.1.1).2.1
              let toks := (msgDec.decode (honestQueryDec.decode z.1.1).2.2.1).1
              let pt := (msgDec.decode (honestQueryDec.decode z.1.1).2.2.1).2
              let st₁ := (arithStep p D pt none)^[z.1.2] ⟨toks.tail, [], none⟩
              ((arithStep p D pt none)^[z.1.2] ⟨st₁.input, [], none⟩ |>.value.getD []).getD 0 0 %
                posMod p
            else 0)
          (encPair encQ encUnary) encUnary :=
        ite (decide_eq' (snd encQ encUnary) (const 0)) (hv₁.comp (.fst encQ encUnary))
          (ite (decide_eq' (snd encQ encUnary) (const 1)) (hv₂.comp (.fst encQ encUnary)) (const 0))
      exact hbody.of_enc_eq fun z => by
        by_cases h0 : z.2 = 0
        · simp [h0]
        · by_cases h1 : z.2 = 1 <;> simp [h0, h1]
    let branchOp : List Bool × ℕ → List ℕ := fun q =>
      let p := (honestQueryDec.decode q.1).1
      let D := (honestQueryDec.decode q.1).2.1
      let toks := (msgDec.decode (honestQueryDec.decode q.1).2.2.1).1
      let pt := (msgDec.decode (honestQueryDec.decode q.1).2.2.1).2
      let v := (toks.headD (.top, 0)).2
      let st := (arithStep p D pt (some v))^[q.2] ⟨toks.tail, [], none⟩
      let l := st.value.getD []
      (List.range (D + 1)).map fun i => l.getD i 0 % posMod p
    have hhdTok : ComputableInPolyTime
        (fun q : List Bool × ℕ =>
          (msgDec.decode (honestQueryDec.decode q.1).2.2.1).1.headD (.top, 0))
        encQ encArithToken :=
      (headD (encA := encArithToken) (encL := encList encArithToken) (.top, 0)).comp htoks
    have hop_pt : ComputableInPolyTime branchOp encQ (encList encUnary) := by
      have hv : ComputableInPolyTime
          (fun q : List Bool × ℕ =>
            ((msgDec.decode (honestQueryDec.decode q.1).2.2.1).1.headD (.top, 0)).2)
          encQ encNat := hhdTok.snd'
      have hst : ComputableInPolyTime
          (fun q : List Bool × ℕ =>
            let p := (honestQueryDec.decode q.1).1
            let D := (honestQueryDec.decode q.1).2.1
            let toks := (msgDec.decode (honestQueryDec.decode q.1).2.2.1).1
            let pt := (msgDec.decode (honestQueryDec.decode q.1).2.2.1).2
            let v := (toks.headD (.top, 0)).2
            (arithStep p D pt (some v))^[q.2] ⟨toks.tail, [], none⟩)
          encQ encArithState :=
        computableInPolyTime_runArith.comp
          ((((hp.prod hD).prod (hpt.prod ((optionSome encNat).comp hv))).prod
            ((listTail encArithToken).comp htoks)).prod hfuel)
      have hl : ComputableInPolyTime
          (fun q : List Bool × ℕ =>
            let p := (honestQueryDec.decode q.1).1
            let D := (honestQueryDec.decode q.1).2.1
            let toks := (msgDec.decode (honestQueryDec.decode q.1).2.2.1).1
            let pt := (msgDec.decode (honestQueryDec.decode q.1).2.2.1).2
            let v := (toks.headD (.top, 0)).2
            ((arithStep p D pt (some v))^[q.2] ⟨toks.tail, [], none⟩).value.getD [])
          encQ (encList encUnary) :=
        optionGetDWithInput (arithState_value_pt.comp hst) (const [])
      refine mapWithInput (unary_range' (unary_add' hD (const 1))) ?_
      exact unary_mod' (listGetDWithInput (hl.comp (.fst encQ encUnary)) (.snd encQ encUnary) 0)
        (hpm.comp (.fst encQ encUnary))
    let branchNil : List Bool × ℕ → List ℕ := fun q =>
      List.replicate ((honestQueryDec.decode q.1).2.1 + 1) 0
    have hnil_pt : ComputableInPolyTime branchNil encQ (encList encUnary) :=
      (mapWithInput (f := fun (_ : List Bool × ℕ) (_ : ℕ) => (0 : ℕ))
        (unary_range' (unary_add' hD (const 1)))
        (const (encIn := encPair encQ encUnary) (encOut := encUnary) (0 : ℕ))).of_enc_eq fun q => by
        simp [branchNil]
    have hcases : ComputableInPolyTime
        (fun q : List Bool × ℕ =>
          if (msgDec.decode (honestQueryDec.decode q.1).2.2.1).1.isEmpty then branchNil q
          else
            match ((msgDec.decode (honestQueryDec.decode q.1).2.2.1).1.headD (.top, 0)).1 with
            | .and | .or => branchBin q
            | .ex | .all | .lin => branchOp q
            | .var | .top | .bot | .not => branchNil q)
        encQ (encList encUnary) := by
      refine ite ((listIsEmpty' encArithToken).comp htoks) hnil_pt ?_
      have hfin : ComputableInPolyTime
          (fun q : List Bool × ℕ =>
            (match ((msgDec.decode (honestQueryDec.decode q.1).2.2.1).1.headD (.top, 0)).1 with
              | .and | .or => branchBin
              | .ex | .all | .lin => branchOp
              | .var | .top | .bot | .not => branchNil) q)
          encQ (encList encUnary) := by
        refine finite_cases (tagEncoding := encFinEnum ArithQBF.Kind)
          (tag := fun q : List Bool × ℕ =>
            ((msgDec.decode (honestQueryDec.decode q.1).2.2.1).1.headD (.top, 0)).1)
          (branch := fun k => match k with
            | .and | .or => branchBin
            | .ex | .all | .lin => branchOp
            | .var | .top | .bot | .not => branchNil) hhdTok.fst' ?_
        intro k
        cases k <;> first | exact hbin_pt | exact hop_pt | exact hnil_pt
      exact hfin.of_enc_eq fun q => by
        cases ((msgDec.decode (honestQueryDec.decode q.1).2.2.1).1.headD (.top, 0)).1 <;> rfl
    exact hcases.of_enc_eq fun q => by
      dsimp only [branchNil, branchBin, branchOp]
      rcases h : (msgDec.decode (honestQueryDec.decode q.1).2.2.1).1 with _ | ⟨⟨k, v⟩, rest⟩
      · simp [evalHonestCoeffs]
      · cases k <;> simp [evalHonestCoeffs]
  have hrep : ComputableInPolyTime
      (fun q : List Bool × ℕ =>
        QBFProtocol.encodeReply (posMod (honestQueryDec.decode q.1).1)
          (let (p, D, msg, _) := honestQueryDec.decode q.1
           let (toks, pt) := msgDec.decode msg
           evalHonestCoeffs p D toks pt q.2))
      encQ encBits :=
    computableInPolyTime_encodeReply hpm hcoeffs
  exact (bitsGetDWithInput hrep hj false).of_enc_eq fun q => rfl

/-- The `EXP` bit language answering every query `(p, D, msg, j)` of the honest prover. -/
private def honestLang : Set (List Bool) :=
  {y : List Bool | honestBitStep (y, 2 ^ y.length) = true}

private theorem honestLang_mem_EXP : honestLang ∈ EXP encBits :=
  E_subset_EXP (setOf_mem_E_of_computableInPolyTime_pad computableInPolyTime_honestBitStep)

private theorem arithCallSteps_le_two_pow_query (p D : ℕ) (e : ArithQBF ℕ)
    (rest : List (ArithQBF.Kind × ℕ)) (pt : List (ℕ × ℕ)) (j : ℕ) :
    arithCallSteps e ≤
      2 ^ (encHonestQuery (p, D,
        encPair (encList encArithToken) encPt (e.tokens ++ rest, pt), j)).length := by
  have hlt := arithCallSteps_lt e
  have htok : e.tokens.length ≤ (encList encArithToken (e.tokens ++ rest)).length := by
    have h1 : e.tokens.length ≤ (e.tokens ++ rest).length := by simp
    exact h1.trans (length_le_length_encList encArithToken _)
  have hlen : 2 * e.tokens.length ≤
      (encHonestQuery (p, D,
        encPair (encList encArithToken) encPt (e.tokens ++ rest, pt), j)).length := by
    simp only [encHonestQuery, length_encPair, encBits_apply]
    omega
  have hpow : 4 ^ e.tokens.length ≤
      2 ^ (encHonestQuery (p, D,
        encPair (encList encArithToken) encPt (e.tokens ++ rest, pt), j)).length := by
    rw [show (4 : ℕ) = 2 ^ 2 by rfl, ← pow_mul]
    exact Nat.pow_le_pow_right two_pos hlen
  omega

/-- Reconstructed reply word of length `replyLimit p D` read bit-by-bit from `honestLang`. -/
private noncomputable def honestWordFromLang (p D : ℕ) (msg : List Bool) : List Bool :=
  (List.range (QBFProtocol.replyLimit p D)).map fun j =>
    honestBitStep (encHonestQuery (p, D, msg, j), 2 ^ (encHonestQuery (p, D, msg, j)).length)

private theorem length_encodeReply_eq {p : ℕ} {l : List ℕ} (hl : ∀ a ∈ l, a < p) :
    (QBFProtocol.encodeReply p l).length = l.length * QBFProtocol.width p := by
  unfold QBFProtocol.encodeReply
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons, Nat.succ_mul]
    have ha : a < 2 ^ QBFProtocol.width p :=
      (hl a (List.mem_cons_self ..)).trans (Nat.lt_pow_succ_log_self (by norm_num) p)
    rw [Cslib.BitString.length_binaryWord ha,
      ih fun b hb => hl b (List.mem_cons_of_mem _ hb), Nat.add_comm]

private theorem evalHonestCoeffs_eq_of_query {p : ℕ} [NeZero p] {D : ℕ} {xs : List ℕ}
    (e : ArithQBF ℕ) (rest : List (ArithQBF.Kind × ℕ)) (r : ℕ → ZMod p)
    (he : ∀ w ∈ e.vars, w ∈ xs) {fuel : ℕ} (hfuel : arithCallSteps e ≤ fuel) :
    let pt := QBFProtocol.canonPt xs r
    let coeffs := evalHonestCoeffs p D (e.tokens ++ rest) pt fuel
    coeffs.length = D + 1 ∧ (∀ a ∈ coeffs, a < p) ∧
    match e with
    | .bin _ e₁ e₂ =>
      (coeffs.getD 0 0 : ZMod p) = e₁.eval r ∧
      (1 ≤ D → (coeffs.getD 1 0 : ZMod p) = e₂.eval r)
    | .op _ v body =>
      coeffs.map (Nat.cast : ℕ → ZMod p) = (body.restrict r v).coeffsBelow (D + 1)
    | _ => True := by
  intro pt coeffs
  have hlen : coeffs.length = D + 1 := length_evalHonestCoeffs p D _ pt fuel
  have hlt : ∀ a ∈ coeffs, a < p := by
    simpa only [posMod_eq p] using lt_posMod_evalHonestCoeffs p D _ pt fuel
  refine ⟨hlen, hlt, ?_⟩
  have hstack_eq : ∀ w ∈ xs, stackEnv p pt [] w = r w := fun w hw => by
    rw [stackEnv_nil, QBFProtocol.lookupPt_canonPt r hw, ZMod.natCast_zmod_val]
  cases e with
  | var _ | top | bot | not _ => trivial
  | bin o e₁ e₂ =>
    have hT₁_le : arithCallSteps e₁ ≤ fuel := (arithCallSteps_bin_le o e₁ e₂).1.trans hfuel
    have hT₂_le : arithCallSteps e₂ ≤ fuel := (arithCallSteps_bin_le o e₁ e₂).2.trans hfuel
    obtain ⟨T₁, hT₁, res₁, hrep₁, hrun₁⟩ :=
      exists_iterate_arithStep_call (p := p) D pt none e₁ (e₂.tokens ++ rest) []
    obtain ⟨T₂, hT₂, res₂, hrep₂, hrun₂⟩ :=
      exists_iterate_arithStep_call (p := p) D pt none e₂ rest []
    have hst₁ : (arithStep p D pt none)^[fuel] ⟨e₁.tokens ++ (e₂.tokens ++ rest), [], none⟩ =
        ⟨e₂.tokens ++ rest, [], some res₁⟩ := by
      rw [show fuel = (fuel - T₁) + T₁ by omega, Function.iterate_add_apply, hrun₁,
        iterate_arithStep_done]
    have hst₂ : (arithStep p D pt none)^[fuel] ⟨e₂.tokens ++ rest, [], none⟩ =
        ⟨rest, [], some res₂⟩ := by
      rw [show fuel = (fuel - T₂) + T₂ by omega, Function.iterate_add_apply, hrun₂,
        iterate_arithStep_done]
    have heval₁ : ((res₁.getD 0 0 : ℕ) : ZMod p) = e₁.eval r := by
      have h0 := hrep₁.getD_cast (i := 0) (Nat.zero_le D)
      rw [targetPoly_nil_none, Polynomial.coeff_C_zero] at h0
      rw [h0]
      exact ArithQBF.eval_congr e₁ fun w hw => hstack_eq w (he w (List.mem_append_left _ hw))
    have heval₂ : ((res₂.getD 0 0 : ℕ) : ZMod p) = e₂.eval r := by
      have h0 := hrep₂.getD_cast (i := 0) (Nat.zero_le D)
      rw [targetPoly_nil_none, Polynomial.coeff_C_zero] at h0
      rw [h0]
      exact ArithQBF.eval_congr e₂ fun w hw => hstack_eq w (he w (List.mem_append_right _ hw))
    have htok_eq : ∀ o : ArithQBF.Connective,
        evalHonestCoeffs p D ((ArithQBF.bin o e₁ e₂).tokens ++ rest) pt fuel =
          (List.range (D + 1)).map fun i =>
            if i = 0 then res₁.getD 0 0 % p
            else if i = 1 then res₂.getD 0 0 % p
            else 0 := by
      intro o'
      cases o' <;>
        simp [ArithQBF.tokens, List.cons_append, List.append_assoc, evalHonestCoeffs,
          hst₁, hst₂, posMod_eq p]
    rw [show coeffs = _ from htok_eq o]
    constructor
    · rw [List.getD_eq_getElem _ _ (by simp)]
      simp only [List.getElem_map, List.getElem_range, ↓reduceIte, ZMod.natCast_mod]
      exact heval₁
    · intro hD1
      rw [List.getD_eq_getElem _ _ (by simp; omega)]
      simp only [List.getElem_map, List.getElem_range, Nat.one_ne_zero, ↓reduceIte,
        ZMod.natCast_mod]
      exact heval₂
  | op o v body =>
    have hT_le : arithCallSteps body ≤ fuel := (arithCallSteps_op_le o v body).trans hfuel
    obtain ⟨T, hT, res, hrep, hrun⟩ :=
      exists_iterate_arithStep_call (p := p) D pt (some v) body rest []
    have hst : (arithStep p D pt (some v))^[fuel] ⟨body.tokens ++ rest, [], none⟩ =
        ⟨rest, [], some res⟩ := by
      rw [show fuel = (fuel - T) + T by omega, Function.iterate_add_apply, hrun,
        iterate_arithStep_done]
    have htok_eq : ∀ o : ArithQBF.Operator,
        evalHonestCoeffs p D ((ArithQBF.op o v body).tokens ++ rest) pt fuel =
          (List.range (D + 1)).map fun i => res.getD i 0 % p := by
      intro o'
      cases o' <;>
        simp [ArithQBF.tokens, List.cons_append, evalHonestCoeffs, hst, posMod_eq p]
    rw [show coeffs = _ from htok_eq o]
    apply List.ext_getElem (by simp [Polynomial.coeffsBelow])
    intro i hi₁ hi₂
    simp only [List.length_map, List.length_range] at hi₁
    simp only [List.getElem_map, List.getElem_range, ZMod.natCast_mod, Polynomial.coeffsBelow]
    have hi_rep := hrep.getD_cast (i := i) (by omega)
    rw [targetPoly_nil_some] at hi_rep
    rw [hi_rep]
    exact congrArg (fun P => P.coeff i)
      (ArithQBF.restrict_congr body v fun w hw => hstack_eq w (he w (List.mem_cons_of_mem v hw)))

/-- Two runs of `evalHonestCoeffs` with sufficient fuel produce the exact same coefficient list. -/
private theorem evalHonestCoeffs_eq_of_ge {p : ℕ} [NeZero p] {D : ℕ} (hD1 : 1 ≤ D)
    {xs : List ℕ} (e : ArithQBF ℕ) (rest : List (ArithQBF.Kind × ℕ)) (r : ℕ → ZMod p)
    (he : ∀ w ∈ e.vars, w ∈ xs) {f₁ f₂ : ℕ}
    (hf₁ : arithCallSteps e ≤ f₁) (hf₂ : arithCallSteps e ≤ f₂) :
    evalHonestCoeffs p D (e.tokens ++ rest) (QBFProtocol.canonPt xs r) f₁ =
      evalHonestCoeffs p D (e.tokens ++ rest) (QBFProtocol.canonPt xs r) f₂ := by
  have hs₁ := evalHonestCoeffs_eq_of_query (p := p) (D := D) (xs := xs) e rest r he hf₁
  have hs₂ := evalHonestCoeffs_eq_of_query (p := p) (D := D) (xs := xs) e rest r he hf₂
  cases e with
  | var _ | top | bot | not _ =>
    simp [evalHonestCoeffs, ArithQBF.tokens]
  | bin o e₁ e₂ =>
    apply List.ext_getElem (hs₁.1.trans hs₂.1.symm)
    intro i hi₁ hi₂
    have hlt1 := hs₁.2.1 _ (List.getElem_mem hi₁)
    have hlt2 := hs₂.2.1 _ (List.getElem_mem hi₂)
    by_cases h0 : i = 0
    · subst h0
      have heq : ((evalHonestCoeffs p D ((ArithQBF.bin o e₁ e₂).tokens ++ rest)
          (QBFProtocol.canonPt xs r) f₁)[0] : ZMod p) =
          ((evalHonestCoeffs p D ((ArithQBF.bin o e₁ e₂).tokens ++ rest)
          (QBFProtocol.canonPt xs r) f₂)[0] : ZMod p) := by
        rw [← List.getD_eq_getElem _ _ hi₁, ← List.getD_eq_getElem _ _ hi₂]
        exact hs₁.2.2.1.trans hs₂.2.2.1.symm
      have hv := congrArg ZMod.val heq
      rwa [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt hlt1,
        Nat.mod_eq_of_lt hlt2] at hv
    · by_cases h1 : i = 1
      · subst h1
        have heq : ((evalHonestCoeffs p D ((ArithQBF.bin o e₁ e₂).tokens ++ rest)
            (QBFProtocol.canonPt xs r) f₁)[1] : ZMod p) =
            ((evalHonestCoeffs p D ((ArithQBF.bin o e₁ e₂).tokens ++ rest)
            (QBFProtocol.canonPt xs r) f₂)[1] : ZMod p) := by
          rw [← List.getD_eq_getElem _ _ hi₁, ← List.getD_eq_getElem _ _ hi₂]
          exact (hs₁.2.2.2 hD1).trans (hs₂.2.2.2 hD1).symm
        have hv := congrArg ZMod.val heq
        rwa [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt hlt1,
          Nat.mod_eq_of_lt hlt2] at hv
      · cases o <;> simp [evalHonestCoeffs, ArithQBF.tokens, h0, h1]
  | op o v body =>
    apply List.ext_getElem (hs₁.1.trans hs₂.1.symm)
    intro i hi₁ hi₂
    have hlt1 := hs₁.2.1 _ (List.getElem_mem hi₁)
    have hlt2 := hs₂.2.1 _ (List.getElem_mem hi₂)
    have hmap : (evalHonestCoeffs p D ((ArithQBF.op o v body).tokens ++ rest)
        (QBFProtocol.canonPt xs r) f₁).map (Nat.cast : ℕ → ZMod p) =
        (evalHonestCoeffs p D ((ArithQBF.op o v body).tokens ++ rest)
        (QBFProtocol.canonPt xs r) f₂).map (Nat.cast : ℕ → ZMod p) :=
      hs₁.2.2.trans hs₂.2.2.symm
    have heq : ((evalHonestCoeffs p D ((ArithQBF.op o v body).tokens ++ rest)
        (QBFProtocol.canonPt xs r) f₁)[i] : ZMod p) =
        ((evalHonestCoeffs p D ((ArithQBF.op o v body).tokens ++ rest)
        (QBFProtocol.canonPt xs r) f₂)[i] : ZMod p) := by
      have := congrArg (fun l => l[i]?) hmap
      simp only [List.getElem?_map, List.getElem?_eq_getElem hi₁,
        List.getElem?_eq_getElem hi₂, Option.map_some, Option.some.injEq] at this
      exact this
    have hv := congrArg ZMod.val heq
    rwa [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt hlt1,
      Nat.mod_eq_of_lt hlt2] at hv

private theorem honestBitStep_query {p : ℕ} [NeZero p] {D : ℕ} (hD1 : 1 ≤ D)
    {xs : List ℕ} (e : ArithQBF ℕ) (rest : List (ArithQBF.Kind × ℕ)) (r : ℕ → ZMod p)
    (he : ∀ w ∈ e.vars, w ∈ xs) (j : ℕ) :
    let msg := encPair (encList encArithToken) encPt (e.tokens ++ rest, QBFProtocol.canonPt xs r)
    honestBitStep (encHonestQuery (p, D, msg, j), 2 ^ (encHonestQuery (p, D, msg, j)).length) =
      (QBFProtocol.encodeReply p
        (evalHonestCoeffs p D (e.tokens ++ rest) (QBFProtocol.canonPt xs r)
          (arithCallSteps e))).getD j false := by
  intro msg
  unfold honestBitStep
  rw [honestQueryDec.decode_enc]
  change (QBFProtocol.encodeReply (posMod p)
    (evalHonestCoeffs p D (msgDec.decode msg).1 (msgDec.decode msg).2
      (2 ^ (encHonestQuery (p, D, msg, j)).length))).getD j false = _
  rw [show msg = encPair (encList encArithToken) encPt
      (e.tokens ++ rest, QBFProtocol.canonPt xs r) from rfl,
    msgDec.decode_enc, posMod_eq p]
  dsimp only
  rw [evalHonestCoeffs_eq_of_ge hD1 e rest r he
    (arithCallSteps_le_two_pow_query p D e rest (QBFProtocol.canonPt xs r) j) le_rfl]

private theorem agreesAt_honestWordFromLang_loop (I : QBFProtocol.Machine.LoopInput)
    (hD1 : 1 ≤ I.degree) (e : ArithQBF ℕ) (rest : List (ArithQBF.Kind × ℕ))
    (r : ℕ → ZMod I.modulus) (he : ∀ w ∈ e.vars, w ∈ I.xs) :
    QBFProtocol.AgreesAt I.degree
      (QBFProtocol.decodeTyped I
        (honestWordFromLang I.modulus I.degree
          (QBFProtocol.queryMessage I ⟨e, rest, r⟩)))
      e r := by
  have : NeZero I.modulus := ⟨Nat.succ_ne_zero _⟩
  let refCoeffs := evalHonestCoeffs I.modulus I.degree (e.tokens ++ rest)
    (QBFProtocol.canonPt I.xs r) (arithCallSteps e)
  have href := evalHonestCoeffs_eq_of_query (p := I.modulus) (D := I.degree) (xs := I.xs)
    e rest r he le_rfl
  have hword_eq : ∀ j, j < QBFProtocol.replyLimit I.modulus I.degree →
      honestBitStep (encHonestQuery
          (I.modulus, I.degree, QBFProtocol.queryMessage I ⟨e, rest, r⟩, j),
        2 ^ (encHonestQuery
          (I.modulus, I.degree, QBFProtocol.queryMessage I ⟨e, rest, r⟩, j)).length) =
        (QBFProtocol.encodeReply I.modulus refCoeffs).getD j false := fun j _ => by
    rw [QBFProtocol.queryMessage]
    exact honestBitStep_query hD1 e rest r he j
  have hlen_enc : (QBFProtocol.encodeReply I.modulus refCoeffs).length =
      QBFProtocol.replyLimit I.modulus I.degree := by
    rw [length_encodeReply_eq href.2.1, href.1, QBFProtocol.replyLimit]
  have hword_full :
      honestWordFromLang I.modulus I.degree (QBFProtocol.queryMessage I ⟨e, rest, r⟩) =
        QBFProtocol.encodeReply I.modulus refCoeffs := by
    apply List.ext_getElem (by simp [honestWordFromLang, hlen_enc])
    intro j hj₁ hj₂
    simp only [honestWordFromLang, List.length_map, List.length_range] at hj₁
    simp only [honestWordFromLang, List.getElem_map, List.getElem_range]
    rw [hword_eq j hj₁, List.getD_eq_getElem _ _ hj₂]
  have hdec :
      QBFProtocol.decodeTyped I
          (honestWordFromLang I.modulus I.degree (QBFProtocol.queryMessage I ⟨e, rest, r⟩)) =
        refCoeffs.map (Nat.cast : ℕ → ZMod I.modulus) := by
    rw [hword_full, QBFProtocol.decodeTyped,
      QBFProtocol.decodeReply_encodeReply href.2.1 href.1.le]
    congr 1
    apply List.ext_getElem (by simp only [List.length_map, List.length_range]; exact href.1.symm)
    intro i hi₁ hi₂
    simp only [List.length_map, List.length_range] at hi₁
    simp only [List.getElem_map, List.getElem_range]
    exact List.getD_eq_getElem refCoeffs 0 hi₂
  rw [hdec]
  cases e with
  | var _ | top | bot | not _ => trivial
  | bin o e₁ e₂ =>
    refine ⟨?_, ?_⟩
    · rw [← Nat.cast_zero (R := ZMod I.modulus), List.getD_map]
      exact href.2.2.1
    · rw [← Nat.cast_zero (R := ZMod I.modulus), List.getD_map]
      exact href.2.2.2 hD1
  | op o v body =>
    unfold QBFProtocol.AgreesAt
    rw [List.take_of_length_le (by rw [List.length_map, href.1])]
    exact href.2.2

/-- On every valid query of `QBFProtocol.verifier ψ`, reading `replyLimit p D` bits from
`honestLang` yields a reply agreeing with the honest prover. -/
private theorem agreesAt_honestWordFromLang (ψ : QBF ℕ) (e : ArithQBF ℕ)
    (rest : List (ArithQBF.Kind × ℕ)) (r : ℕ → ZMod (QBFProtocol.loopInput ψ).modulus)
    (he : ∀ w ∈ e.vars, w ∈ (QBFProtocol.loopInput ψ).xs) :
    QBFProtocol.AgreesAt (QBFProtocol.loopInput ψ).degree
      (QBFProtocol.decodeTyped (QBFProtocol.loopInput ψ)
        (honestWordFromLang (QBFProtocol.loopInput ψ).modulus (QBFProtocol.loopInput ψ).degree
          (QBFProtocol.queryMessage (QBFProtocol.loopInput ψ) ⟨e, rest, r⟩)))
      e r :=
  agreesAt_honestWordFromLang_loop (QBFProtocol.loopInput ψ) (by
    have hpos := List.length_pos_of_ne_nil (QBF.tokens_ne_nil ψ)
    change 1 ≤ 2 * ψ.tokens.length
    omega) e rest r he

/-! ### : Deterministic fixed-coin simulator and `TQBF ∈ MA` -/

/-- Stateless deterministic prover answering every query `m` with `f m`. -/
private noncomputable def detProver (f : List Bool → List Bool) : Prover Unit where
  State := Unit
  init := ()
  respond q s := PMF.pure (f q.2, s)

/-- One instruction of a verifier machine `M` with coin `b`, answering oracle queries via `f`
(truncated to `t` bits). -/
private def simStep {k : ℕ} {Control : Type} (M : MultiTapePTM k Bool Control Unit)
    (t : ℕ) (f : List Bool → List Bool)
    (cfg : MultiTapeMachine.FiniteConfig k Bool Control Unit) (b : Bool) :
    MultiTapeMachine.FiniteConfig k Bool Control Unit :=
  match Interaction.instruction M cfg b with
  | none => cfg
  | some (.step action symbol move) => cfg.step action symbol move
  | some (.query op next) => cfg.receive op next ((f (cfg.channels op).1).take t)

/-- Deterministic run of `M` on input `x` with coin string `r` against stateless prover `f`. -/
private def simRun {k : ℕ} {Control : Type} (M : MultiTapePTM k Bool Control Unit)
    (t : ℕ) (f : List Bool → List Bool) (x r : List Bool) :
    MultiTapeMachine.FiniteConfig k Bool Control Unit :=
  r.foldl (simStep M t f) (MultiTapeMachine.FiniteConfig.init M.initial x)

private theorem interpret_coinStep_detProver {k : ℕ} {Control : Type}
    (M : MultiTapePTM k Bool Control Unit) (t : ℕ) (f : List Bool → List Bool)
    (cfg : MultiTapeMachine.FiniteConfig k Bool Control Unit) (b : Bool) :
    (OracleComp.interpret (detProver f).respond (Interaction.coinStep M t cfg b)).run
        (detProver f).init =
      PMF.pure (simStep M t f cfg b, (detProver f).init) := by
  unfold Interaction.coinStep MultiTapeMachine.finiteStep simStep Interaction.instruction
  cases cfg.tapes.state with
  | none => rfl
  | some c =>
    simp only [Option.map_some, map_pure, pure_bind]
    cases M.tr c cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols cfg.answerSymbols b with
    | step => rfl
    | query op next =>
      simp only [bind_map_left, interp_norm]
      simp only [detProver, StateT.run, pmf_norm]

private theorem interpret_foldlM_coinStep_detProver {k : ℕ} {Control : Type}
    (M : MultiTapePTM k Bool Control Unit) (t : ℕ) (f : List Bool → List Bool)
    (r : List Bool) (cfg : MultiTapeMachine.FiniteConfig k Bool Control Unit) :
    (OracleComp.interpret (detProver f).respond (r.foldlM (Interaction.coinStep M t) cfg)).run
        (detProver f).init =
      PMF.pure (r.foldl (simStep M t f) cfg, (detProver f).init) := by
  induction r generalizing cfg with
  | nil => rfl
  | cons b r ih =>
    simp only [List.foldlM_cons, List.foldl_cons, interp_norm, interpret_coinStep_detProver,
      pmf_norm, ih]

private theorem acceptFrom_coinProgram_detProver {k : ℕ} {Control : Type}
    (M : MultiTapePTM k Bool Control Unit) (t : ℕ) (f : List Bool → List Bool) (x r : List Bool) :
    Interaction.acceptFrom (detProver f) (detProver f).init
        (some (Interaction.coinProgram M t x r)) =
      if (simRun M t f x r).tapes.output = [true] then 1 else 0 := by
  unfold Interaction.acceptFrom Interaction.coinProgram
  simp only [interp_norm, interpret_foldlM_coinStep_detProver, pmf_norm]
  dsimp only [simRun]
  by_cases h : (r.foldl (simStep M t f)
      (MultiTapeMachine.FiniteConfig.init M.initial x)).tapes.output = [true] <;> simp [h]

private theorem simStep_spaceBound {k : ℕ} {Control : Type}
    (M : MultiTapePTM k Bool Control Unit) (t : ℕ) (f : List Bool → List Bool)
    {n i : ℕ} {cfg : MultiTapeMachine.FiniteConfig k Bool Control Unit}
    (hs : MultiTapeMachine.FiniteConfig.SpaceBound n i t cfg) (b : Bool) :
    MultiTapeMachine.FiniteConfig.SpaceBound n (i + 1) t (simStep M t f cfg b) := by
  unfold simStep Interaction.instruction
  cases cfg.tapes.state with
  | none => exact hs.mono le_rfl (by omega) le_rfl
  | some c =>
    dsimp only [Option.map_some]
    cases M.tr c cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols cfg.answerSymbols b with
    | step action symbol move => exact hs.step action symbol move
    | query op next => exact hs.receive op next _ (List.length_take_le _ _)

private theorem foldl_simStep_congr {k : ℕ} {Control : Type}
    (M : MultiTapePTM k Bool Control Unit) (t : ℕ) (f₁ f₂ : List Bool → List Bool)
    {n i : ℕ} {cfg : MultiTapeMachine.FiniteConfig k Bool Control Unit}
    (hs : MultiTapeMachine.FiniteConfig.SpaceBound n i t cfg) (r : List Bool)
    (hf : ∀ m, m.length ≤ i + r.length → (f₁ m).take t = (f₂ m).take t) :
    r.foldl (simStep M t f₁) cfg = r.foldl (simStep M t f₂) cfg := by
  induction r generalizing i cfg with
  | nil => rfl
  | cons b r ih =>
    simp only [List.foldl_cons]
    have hstep : simStep M t f₁ cfg b = simStep M t f₂ cfg b := by
      unfold simStep Interaction.instruction
      cases cfg.tapes.state with
      | none => rfl
      | some c =>
        dsimp only [Option.map_some]
        cases M.tr c cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols cfg.answerSymbols b with
        | step => rfl
        | query op next =>
          dsimp only
          have hm : ((cfg.channels op).1).length ≤ i := hs.query op
          rw [hf _ (by simp only [List.length_cons]; omega)]
    rw [hstep]
    exact ih (simStep_spaceBound M t f₂ hs b) fun m hm =>
      hf m (by simp only [List.length_cons] at hm ⊢; omega)

private theorem simRun_congr {k : ℕ} {Control : Type}
    (M : MultiTapePTM k Bool Control Unit) (t : ℕ) (f₁ f₂ : List Bool → List Bool)
    (x r : List Bool) (hf : ∀ m, m.length ≤ r.length → (f₁ m).take t = (f₂ m).take t) :
    simRun M t f₁ x r = simRun M t f₂ x r :=
  foldl_simStep_congr M t f₁ f₂ (MultiTapeMachine.FiniteConfig.spaceBound_init M.initial x t) r
    (by simpa using hf)

private theorem acceptProb_verifier_detProver {k : ℕ} {Control : Type}
    (M : MultiTapePTM k Bool Control Unit) (t : ℕ) (ψ : QBF ℕ)
    (hV : ∀ (S : Type) (oracle : Unit × List Bool → StateT S PMF (List Bool)) s,
      ProbOracleComp.runWith oracle (encBool <$> QBFProtocol.verifier ψ) s =
      ProbOracleComp.runWith oracle (M.runOracle t (encQBF ψ)) s)
    (f : List Bool → List Bool) :
    acceptProb (QBFProtocol.verifier ψ) (detProver f) =
      (2 ^ t)⁻¹ * ((Finset.univ.filter fun r : Fin t → Bool =>
        decide ((simRun M t f (encQBF ψ) (List.ofFn r)).tapes.output = [true]) = true).card :
          ℝ≥0∞) := by
  have hV' : ∀ (S : Type) (oracle : Unit × List Bool → StateT S PMF (List Bool)) s,
      (OracleComp.interpret
        (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
          (encBool <$> QBFProtocol.verifier ψ)).run s =
      (OracleComp.interpret
        (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
          (M.runOracle t (encQBF ψ))).run s := by
    intro S oracle s
    simpa only [ProbOracleComp.runWith_eq_run_interpret] using hV S oracle s
  rw [Interaction.acceptProb_eq_sum M hV' (detProver f)]
  congr 1
  simp_rw [acceptFrom_coinProgram_detProver, decide_eq_true_eq]
  rw [Finset.sum_boole]

private theorem computableInPolyTime_simRun {k : ℕ} {Control : Type} [Finite Control]
    (M : MultiTapePTM k Bool Control Unit) {α : Type} {encA : α ↪ List Bool}
    (f : α → List Bool → List Bool)
    (hf : ComputableInPolyTime (fun p : α × List Bool => f p.1 p.2)
      (encPair encA encBits) encBits) :
    ComputableInPolyTime
      (fun p : (α × List Bool) × List Bool => simRun M p.2.length (f p.1.1) p.1.2 p.2)
      (encPair (encPair encA encBits) encBits)
      (encFiniteConfig (k := k) (State := Control) (Oracle := Unit)) := by
  open ComputableInPolyTime in
  let encIn := encPair (encPair encA encBits) encBits
  let encPar := encPair encA encUnary
  let encCfg := encFiniteConfig (k := k) (State := Control) (Oracle := Unit)
  obtain ⟨cf, hcf⟩ := length_encFiniteConfig_le (k := k) (State := Control) (Oracle := Unit)
  have hstep : ComputableInPolyTime
      (fun q : ((α × ℕ) × MultiTapeMachine.FiniteConfig k Bool Control Unit) × Bool =>
        simStep M q.1.1.2 (f q.1.1.1) q.1.2 q.2)
      (encPair (encPair encPar encCfg) encBool) encCfg := by
    refine finite_cases
      (tagEncoding := encFinite (Option (MultiTapeMachine.Action k Bool Control Unit)))
      (tag := fun q : ((α × ℕ) × MultiTapeMachine.FiniteConfig k Bool Control Unit) × Bool =>
        Interaction.instruction M q.1.2 q.2)
      (branch := fun tag q =>
        match tag with
        | none => q.1.2
        | some (.step action symbol move) => q.1.2.step action symbol move
        | some (.query op next) =>
          q.1.2.receive op next ((f q.1.1.1 (q.1.2.channels op).1).take q.1.1.2))
      ?_ ?_
    · exact (Interaction.computableInPolyTime_instruction M).comp
        ((((snd encPar encCfg).comp (fst _ encBool)).prod (snd _ encBool)))
    · intro tag
      have hq1 : ComputableInPolyTime
          (fun q : ((α × ℕ) × MultiTapeMachine.FiniteConfig k Bool Control Unit) × Bool => q.1)
          (encPair (encPair encPar encCfg) encBool) (encPair encPar encCfg) :=
        fst (encPair encPar encCfg) encBool
      have hcfg : ComputableInPolyTime
          (fun q : ((α × ℕ) × MultiTapeMachine.FiniteConfig k Bool Control Unit) × Bool => q.1.2)
          (encPair (encPair encPar encCfg) encBool) encCfg := hq1.snd'
      have ha : ComputableInPolyTime
          (fun q : ((α × ℕ) × MultiTapeMachine.FiniteConfig k Bool Control Unit) × Bool => q.1.1.1)
          (encPair (encPair encPar encCfg) encBool) encA := hq1.fst'.fst'
      have ht : ComputableInPolyTime
          (fun q : ((α × ℕ) × MultiTapeMachine.FiniteConfig k Bool Control Unit) × Bool => q.1.1.2)
          (encPair (encPair encPar encCfg) encBool) encUnary := hq1.fst'.snd'
      match tag with
      | none => exact hcfg
      | some (.step action symbol move) =>
        exact (finiteConfig_step action symbol move).comp hcfg
      | some (.query op next) =>
        have hch : ComputableInPolyTime
            (fun q : ((α × ℕ) × MultiTapeMachine.FiniteConfig k Bool Control Unit) × Bool =>
              (q.1.2.channels op).1)
            (encPair (encPair encPar encCfg) encBool) encBits :=
          ((pi_apply (encPair encBits (encBiTape encBool)) op).comp
            (finiteConfig_channels.comp hcfg)).fst'
        have hans : ComputableInPolyTime
            (fun q : ((α × ℕ) × MultiTapeMachine.FiniteConfig k Bool Control Unit) × Bool =>
              (f q.1.1.1 (q.1.2.channels op).1).take q.1.1.2)
            (encPair (encPair encPar encCfg) encBool) encBits :=
          bitsTakeWithInput (hf.comp (ha.prod hch)) ht
        exact finiteConfig_receive hcfg hans op next
  unfold simRun
  have hpar_pt : ComputableInPolyTime
      (fun p : (α × List Bool) × List Bool => (p.1.1, p.2.length)) encIn encPar :=
    (fst (encPair encA encBits) encBits).fst'.prod
      (length_bits.comp (snd (encPair encA encBits) encBits))
  have hlist_pt : ComputableInPolyTime (fun p : (α × List Bool) × List Bool => p.2)
      encIn encBits := snd (encPair encA encBits) encBits
  have hinit_pt : ComputableInPolyTime
      (fun p : (α × List Bool) × List Bool => MultiTapeMachine.FiniteConfig.init M.initial p.1.2)
      encIn encCfg :=
    finiteConfig_init (fst (encPair encA encBits) encBits).snd' M.initial
  have hsize_pb : PolyBounded (fun p : (α × List Bool) × List Bool => (encIn p).length)
      (fun p => cf * (3 * (encIn p).length + 1)) :=
    (PolyBounded.const cf).mul (((PolyBounded.const 3).mul PolyBounded.self).add (.const 1))
  refine (foldlWith_spec
    (encIn := encIn) (encP := encPar) (encA := encBool) (encB := encCfg) (encL := encBits)
    (par := fun p : (α × List Bool) × List Bool => (p.1.1, p.2.length))
    (list := fun p => p.2)
    (init := fun p => MultiTapeMachine.FiniteConfig.init M.initial p.1.2)
    (step := fun par cfg b => simStep M par.2 (f par.1) cfg b)
    hpar_pt hlist_pt hinit_pt hstep
    (fun p consumed cfg =>
      MultiTapeMachine.FiniteConfig.SpaceBound p.1.2.length consumed.length p.2.length cfg)
    (fun p => MultiTapeMachine.FiniteConfig.spaceBound_init _ _ _)
    (fun p consumed cfg b _ hs => by
      simpa using simStep_spaceBound M p.2.length (f p.1.1) hs b)
    (size := fun p => cf * (3 * (encIn p).length + 1))
    hsize_pb
    (fun p consumed cfg hprefix hs => ?_)).1
  have hcfg := hcf _ _ _ _ hs
  have hcons : consumed.length ≤ p.2.length := hprefix.length_le
  refine hcfg.trans (Nat.mul_le_mul_left cf ?_)
  simp only [encIn, length_encPair, encBits_apply]
  omega

/-- Prover reply computed from Merlin's advice string `w` on formula `ψ` and message `m`. -/
private def adviceProverReply (S W : Polynomial ℕ) (p : QBF ℕ × List Bool) (m : List Bool) :
    List Bool :=
  let ψ := p.1
  let w := p.2
  let modP := (QBFProtocol.loopInput ψ).modulus
  let degD := (QBFProtocol.loopInput ψ).degree
  (List.range (QBFProtocol.replyLimit modP degD)).map fun j =>
    evalAdvice (S.eval (encQBF ψ).length) (W.eval (encQBF ψ).length) w
      (encHonestQuery (modP, degD, m, j))

private theorem computableInPolyTime_modulus_qbf :
    ComputableInPolyTime QBFProtocol.modulus encQBF encUnary := by
  open ComputableInPolyTime in
  have htoks : ComputableInPolyTime (fun ψ : QBF ℕ => ψ.tokens)
      encQBF (encList TQBF.encToken) := of_eq fun _ => rfl
  have hlen : ComputableInPolyTime (fun ψ : QBF ℕ => ψ.tokens.length) encQBF encUnary :=
    (length_list TQBF.encToken).comp htoks
  have hbound : ComputableInPolyTime (fun ψ : QBF ℕ => 2 * QBFProtocol.primeBound ψ)
      encQBF encUnary := by
    unfold QBFProtocol.primeBound
    exact unary_mul' (const 2)
      (unary_mul' (unary_mul' (const 12) ((unary_pow 2).comp hlen)) (unary_add' hlen (const 1)))
  exact findGreatest hbound (unary_decide_prime.comp (.snd _ _))

private theorem computableInPolyTime_adviceProverReply (S W : Polynomial ℕ) :
    ComputableInPolyTime
      (fun q : (QBF ℕ × List Bool) × List Bool => adviceProverReply S W q.1 q.2)
      (encPair (encPair encQBF encBits) encBits) encBits := by
  open ComputableInPolyTime in
  let encQ := encPair (encPair encQBF encBits) encBits
  have hmod : ComputableInPolyTime
      (fun q : (QBF ℕ × List Bool) × List Bool => (QBFProtocol.loopInput q.1.1).modulus)
      encQ encUnary := by
    have hm := computableInPolyTime_modulus_qbf.comp ((fst encQBF encBits).comp (fst _ encBits))
    refine (unary_add' (unary_sub' hm (const 1)) (const 1)).of_enc_eq fun q => ?_
    rfl
  have hdeg : ComputableInPolyTime
      (fun q : (QBF ℕ × List Bool) × List Bool => (QBFProtocol.loopInput q.1.1).degree)
      encQ encUnary := by
    have htoks : ComputableInPolyTime (fun ψ : QBF ℕ => ψ.tokens)
        encQBF (encList TQBF.encToken) := of_eq fun _ => rfl
    have hlen : ComputableInPolyTime (fun q : (QBF ℕ × List Bool) × List Bool =>
        q.1.1.tokens.length) encQ encUnary :=
      (length_list TQBF.encToken).comp (htoks.comp ((fst encQBF encBits).comp (fst _ encBits)))
    exact unary_mul' (const 2) hlen
  have hlim : ComputableInPolyTime
      (fun q : (QBF ℕ × List Bool) × List Bool =>
        QBFProtocol.replyLimit (QBFProtocol.loopInput q.1.1).modulus
          (QBFProtocol.loopInput q.1.1).degree)
      encQ encUnary :=
    QBFProtocol.computableInPolyTime_replyLimit hmod hdeg
  have hlenψ : ComputableInPolyTime
      (fun q : ((QBF ℕ × List Bool) × List Bool) × ℕ => (encQBF q.1.1.1).length)
      (encPair encQ encUnary) encUnary :=
    (encoding_length encQBF).comp
      ((fst encQBF encBits).comp ((fst _ encBits).comp (fst encQ encUnary)))
  have hquery : ComputableInPolyTime
      (fun q : ((QBF ℕ × List Bool) × List Bool) × ℕ =>
        encHonestQuery ((QBFProtocol.loopInput q.1.1.1).modulus,
          (QBFProtocol.loopInput q.1.1.1).degree, q.1.2, q.2))
      (encPair encQ encUnary) encBits :=
    encoding_comp ((hmod.comp (fst encQ encUnary)).prod
      ((hdeg.comp (fst encQ encUnary)).prod
        (((snd _ encBits).comp (fst encQ encUnary)).prod (snd encQ encUnary))))
  have heval : ComputableInPolyTime
      (fun q : ((QBF ℕ × List Bool) × List Bool) × ℕ =>
        evalAdvice (S.eval (encQBF q.1.1.1).length) (W.eval (encQBF q.1.1.1).length) q.1.1.2
          (encHonestQuery ((QBFProtocol.loopInput q.1.1.1).modulus,
            (QBFProtocol.loopInput q.1.1.1).degree, q.1.2, q.2)))
      (encPair encQ encUnary) encBool :=
    computableInPolyTime_evalAdvice_eval S W hlenψ
      ((snd encQBF encBits).comp ((fst _ encBits).comp (fst encQ encUnary))) hquery
  have hmap : ComputableInPolyTime
      (fun q : (QBF ℕ × List Bool) × List Bool => adviceProverReply S W q.1 q.2)
      encQ (encList encBool) :=
    mapWithInput (unary_range' hlim) heval
  exact (bits_encList_polyTime encBool).2.comp hmap

/-- Under `EXP ⊆ P/poly`, `TQBF ∈ MA`. -/
private theorem TQBF_mem_MA_of_exp_subset_ppoly (hEXP : EXP encBits ⊆ PPolyOn encBits) :
    TQBF ∈ MA encQBF := by
  have hHonestPPoly : honestLang ∈ PPoly :=
    mem_PPolyOn_encBits_iff.mp (hEXP honestLang_mem_EXP)
  obtain ⟨_, k, Control, hfin, M, c_M, d_M, hM⟩ := QBFProtocol.isOraclePPTOn_verifier
  -- Polynomial bound on the query length `(encHonestQuery (p, D, m, j)).length`
  let p_coin : Polynomial ℕ := Polynomial.C c_M * (Polynomial.X + 1) ^ d_M
  let N_q : Polynomial ℕ :=
    Polynomial.C 4 * (Polynomial.C 24 * (Polynomial.X + 1) ^ 3 + Polynomial.C 2) +
    Polynomial.C 8 * (Polynomial.X + 1) +
    Polynomial.C 4 * p_coin +
    (Polynomial.C 2 * Polynomial.X + Polynomial.C 2) *
      (Polynomial.C 24 * (Polynomial.X + 1) ^ 3 + Polynomial.C 3) +
    Polynomial.C 20
  obtain ⟨S, W, P_adv, α, hα_len, _, hα_eval⟩ := PPoly.exists_evalAdvice hHonestPPoly N_q
  let V_MA : QBF ℕ × List Bool → Bool := fun z =>
    let w := z.2.take (P_adv.eval (encQBF z.1).length)
    let r := z.2.drop (P_adv.eval (encQBF z.1).length)
    decide ((simRun M r.length (adviceProverReply S W (z.1, w)) (encQBF z.1) r).tapes.output =
      [true])
  have hV_pt : ComputableInPolyTime V_MA (encPair encQBF encBits) encBool := by
    open ComputableInPolyTime in
    have hP : ComputableInPolyTime (fun z : QBF ℕ × List Bool => P_adv.eval (encQBF z.1).length)
        (encPair encQBF encBits) encUnary :=
      (unary_eval P_adv).comp ((encoding_length encQBF).comp (fst encQBF encBits))
    have hw : ComputableInPolyTime
        (fun z : QBF ℕ × List Bool => z.2.take (P_adv.eval (encQBF z.1).length))
        (encPair encQBF encBits) encBits :=
      bitsTakeWithInput (snd encQBF encBits) hP
    have hr : ComputableInPolyTime
        (fun z : QBF ℕ × List Bool => z.2.drop (P_adv.eval (encQBF z.1).length))
        (encPair encQBF encBits) encBits :=
      bitsDropWithInput (snd encQBF encBits) hP
    have hsim := (computableInPolyTime_simRun M (adviceProverReply S W)
      (computableInPolyTime_adviceProverReply S W)).comp
        ((((fst encQBF encBits).prod hw).prod
          ((of_eq (f := encQBF) (encOut := encBits) fun _ => rfl).comp (fst encQBF encBits))).prod
          hr)
    exact decide_eq' (finiteCfg_output.comp (finiteConfig_tapes.comp hsim)) (const [true])
  refine ⟨P_adv, p_coin, V_MA, hV_pt, fun ψ => ?_⟩
  set n := (encQBF ψ).length
  set t := p_coin.eval n
  have ht_eq : t = c_M * (n + 1) ^ d_M := by
    simp [t, p_coin, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add,
      Polynomial.eval_X, Polynomial.eval_one]
  have hV_split : ∀ (y : Fin (P_adv.eval n) → Bool) (r : Fin t → Bool),
      V_MA (ψ, List.ofFn y ++ List.ofFn r) =
        decide ((simRun M t (adviceProverReply S W (ψ, List.ofFn y))
          (encQBF ψ) (List.ofFn r)).tapes.output = [true]) := by
    intro y r
    have hly : (List.ofFn y).length = P_adv.eval n := List.length_ofFn
    have hlr : (List.ofFn r).length = t := List.length_ofFn
    dsimp only [V_MA]
    rw [show (encQBF ψ).length = n from rfl, List.take_left' hly, List.drop_left' hly, hlr]
  constructor
  · -- Completeness: ψ ∈ TQBF
    intro hψ
    let y : Fin (P_adv.eval n) → Bool := fun i => (α n)[i.val]'(by rw [hα_len n]; exact i.isLt)
    have hy_ofFn : List.ofFn y = α n := by
      apply List.ext_getElem (by simp [hα_len n])
      intro i hi₁ hi₂
      simp [y]
    refine ⟨y, ?_⟩
    dsimp only [BoundedErrorAt]
    simp_rw [hV_split y, hy_ofFn]
    set I := QBFProtocol.loopInput ψ
    set modP := I.modulus
    set degD := I.degree
    -- Show adviceProverReply agrees with honestWordFromLang on all messages of length ≤ t
    have htok_le : ψ.tokens.length ≤ n := by
      exact length_le_length_encList TQBF.encToken ψ.tokens
    have hmod_le : modP ≤ 24 * (n + 1) ^ 3 + 1 := by
      have hmod_eq : modP = QBFProtocol.modulus ψ :=
        Nat.sub_add_cancel (QBFProtocol.prime_modulus ψ).1.one_lt.le
      have hfg : QBFProtocol.modulus ψ ≤ 2 * QBFProtocol.primeBound ψ :=
        Nat.findGreatest_le _
      rw [hmod_eq]
      refine hfg.trans ?_
      unfold QBFProtocol.primeBound
      have h1 : ψ.tokens.length ^ 2 ≤ (n + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      have h2 : ψ.tokens.length + 1 ≤ n + 1 := by omega
      have h3 : ψ.tokens.length ^ 2 * (ψ.tokens.length + 1) ≤ (n + 1) ^ 2 * (n + 1) :=
        Nat.mul_le_mul h1 h2
      have h4 : (n + 1) ^ 2 * (n + 1) = (n + 1) ^ 3 := by ring
      have h5 : 12 * ψ.tokens.length ^ 2 * (ψ.tokens.length + 1) =
          12 * (ψ.tokens.length ^ 2 * (ψ.tokens.length + 1)) := by ring
      omega
    have hdeg_le : degD ≤ 2 * n := by
      change 2 * ψ.tokens.length ≤ 2 * n; omega
    have hwidth_le : QBFProtocol.width modP ≤ modP + 1 := by
      unfold QBFProtocol.width
      have := Nat.log_le_self 2 modP
      omega
    have hlim_le : QBFProtocol.replyLimit modP degD ≤ (2 * n + 1) * (24 * (n + 1) ^ 3 + 2) := by
      unfold QBFProtocol.replyLimit
      exact Nat.mul_le_mul (by omega) (hwidth_le.trans (by omega))
    have hagree : ∀ m, m.length ≤ t →
        (adviceProverReply S W (ψ, α n) m).take t = (honestWordFromLang modP degD m).take t := by
      intro m hm
      congr 1
      unfold adviceProverReply honestWordFromLang
      refine List.map_congr_left fun j hj => ?_
      have hj_lt : j < QBFProtocol.replyLimit modP degD := List.mem_range.mp hj
      have hq_le : (encHonestQuery (modP, degD, m, j)).length ≤ N_q.eval n := by
        simp only [encHonestQuery, length_encPair, encUnary_apply, List.length_replicate,
          encBits_apply]
        have hNq : N_q.eval n =
            4 * (24 * (n + 1) ^ 3 + 2) + 8 * (n + 1) + 4 * t +
            (2 * n + 2) * (24 * (n + 1) ^ 3 + 3) + 20 := by
          simp [N_q, t, Polynomial.eval_add, Polynomial.eval_mul,
            Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one]
        rw [hNq]
        have hj_le : j ≤ (2 * n + 2) * (24 * (n + 1) ^ 3 + 3) := by
          have : (2 * n + 1) * (24 * (n + 1) ^ 3 + 2) ≤ (2 * n + 2) * (24 * (n + 1) ^ 3 + 3) :=
            Nat.mul_le_mul (by omega) (by omega)
          omega
        omega
      have hev := hα_eval n (encHonestQuery (modP, degD, m, j)) hq_le
      rw [Bool.eq_iff_iff]
      exact hev
    have hsim_eq : ∀ r : Fin t → Bool,
        simRun M t (adviceProverReply S W (ψ, α n)) (encQBF ψ) (List.ofFn r) =
        simRun M t (honestWordFromLang modP degD) (encQBF ψ) (List.ofFn r) := fun r =>
      simRun_congr M t _ _ (encQBF ψ) (List.ofFn r) fun m hm =>
        hagree m (by simpa [List.length_ofFn] using hm)
    simp_rw [hsim_eq]
    have hprob := acceptProb_verifier_detProver M t ψ (ht_eq ▸ hM ψ) (honestWordFromLang modP degD)
    have hprob_one : acceptProb (QBFProtocol.verifier ψ)
        (detProver (honestWordFromLang modP degD)) = 1 := by
      rw [QBFProtocol.acceptProb_verifier_eq ψ hψ.1]
      set f : QBFProtocol.QueryAt (ZMod modP) → List (ZMod modP) := fun q =>
        QBFProtocol.decodeTyped I (honestWordFromLang modP degD (QBFProtocol.queryMessage I q))
      have htyped : QBFProtocol.typedRespond I (detProver (honestWordFromLang modP degD)).respond =
          fun q s => PMF.pure (f q, s) := funext₂ fun _ _ => PMF.pure_map _ _
      have heval : (QBFProtocol.arithOf ψ).eval 0 = (1 : ZMod modP) := by
        simp [QBFProtocol.arithOf, QBF.eval_arithmetize_zero _ hψ.1 (fun _ => false), hψ.2]
      have hlin : ∀ {φ : QBF ℕ} {v : ℕ}, v ∈ φ.vars → v ∈ QBFProtocol.linVars φ := by
        intro φ v hv
        unfold QBFProtocol.linVars
        induction φ with
        | var w => simp_all [QBF.vars, QBF.tokens]
        | top | bot => simp_all [QBF.vars]
        | not φ ih => exact List.mem_cons_of_mem _ (ih hv)
        | and φ χ ihφ ihχ | or φ χ ihφ ihχ =>
          simpa only [QBF.tokens, List.map_cons, List.map_append, List.mem_cons,
            List.mem_append] using Or.inr ((List.mem_append.1 hv).imp ihφ ihχ)
        | ex w φ ih | all w φ ih =>
          simpa only [QBF.tokens, List.map_cons, List.mem_cons] using
            (List.mem_cons.1 hv).imp id ih
      have hvars : ∀ w ∈ (QBFProtocol.arithOf ψ).vars, w ∈ I.xs := fun w hw =>
        (QBF.mem_vars_arithmetize hw).elim hlin id
      have hdegM : (QBFProtocol.arithOf ψ).maxRoundDegree ≤ degD :=
        (QBF.maxRoundDegree_arithmetize_le fun v hv => hlin hv).trans (by
          change 2 * ψ.size ≤ 2 * ψ.tokens.length
          rw [QBF.length_tokens])
      have hrun := QBFProtocol.run_verifyAt_of_agreesAt (QBFProtocol.samplerOf I) degD f I.xs
        (fun q hq => agreesAt_honestWordFromLang ψ q.formula q.rest q.point hq)
        (QBFProtocol.arithOf ψ) hvars hdegM [] 0 ()
      rw [htyped, ProbOracleComp.acceptProbWith]
      dsimp only [detProver]
      exact (congrArg (fun μ => PMF.map Prod.fst μ true) (heval ▸ hrun)).trans
        (by rw [PMF.pure_map, PMF.pure_apply_self])
    rw [hprob_one] at hprob
    have h2t_ne : ((2 : ℝ≥0∞) ^ t) ≠ 0 := by positivity
    have h2t_top : ((2 : ℝ≥0∞) ^ t) ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofNat_ne_top
    have hcard_enn : ((Finset.univ.filter fun r : Fin t → Bool =>
        decide ((simRun M t (honestWordFromLang modP degD)
          (encQBF ψ) (List.ofFn r)).tapes.output = [true]) = true).card : ℝ≥0∞) = (2 ^ t : ℕ) := by
      have h1 := congrArg (fun x : ℝ≥0∞ => (2 : ℝ≥0∞) ^ t * x) hprob.symm
      rw [mul_one, ← mul_assoc, ENNReal.mul_inv_cancel h2t_ne h2t_top, one_mul] at h1
      simpa using h1
    have hcard : (Finset.univ.filter fun r : Fin t → Bool =>
        decide ((simRun M t (honestWordFromLang modP degD)
          (encQBF ψ) (List.ofFn r)).tapes.output = [true]) = true).card = 2 ^ t := by
      exact_mod_cast hcard_enn
    change 2 * 2 ^ t ≤ 3 * (Finset.univ.filter fun r : Fin t → Bool =>
      decide ((simRun M t (honestWordFromLang modP degD)
        (encQBF ψ) (List.ofFn r)).tapes.output = [true]) = true).card
    rw [hcard]
    omega
  · -- Soundness: ψ ∉ TQBF
    intro hψ y
    dsimp only [BoundedErrorAt]
    simp_rw [hV_split y]
    set P_y := detProver (adviceProverReply S W (ψ, List.ofFn y))
    have hprob := acceptProb_verifier_detProver M t ψ (ht_eq ▸ hM ψ)
      (adviceProverReply S W (ψ, List.ofFn y))
    have hle : acceptProb (QBFProtocol.verifier ψ) P_y ≤ 1 / 3 :=
      QBFProtocol.acceptProb_verifier_le ψ hψ P_y
    rw [hprob] at hle
    set acc := (Finset.univ.filter fun r : Fin t → Bool =>
      decide ((simRun M t (adviceProverReply S W (ψ, List.ofFn y))
        (encQBF ψ) (List.ofFn r)).tapes.output = [true]) = true).card
    set rej := (Finset.univ.filter fun r : Fin t → Bool =>
      decide ((simRun M t (adviceProverReply S W (ψ, List.ofFn y))
        (encQBF ψ) (List.ofFn r)).tapes.output = [true]) = false).card
    have h3acc : 3 * acc ≤ 2 ^ t := by
      have hmul : (3 : ℝ≥0∞) * (2 : ℝ≥0∞) ^ t * ((2 : ℝ≥0∞) ^ t)⁻¹ * (acc : ℝ≥0∞) ≤
          (3 : ℝ≥0∞) * (2 : ℝ≥0∞) ^ t * (1 / 3 : ℝ≥0∞) := by
        rw [mul_assoc ((3 : ℝ≥0∞) * 2 ^ t)]
        gcongr
      have h2t_ne : ((2 : ℝ≥0∞) ^ t) ≠ 0 := by positivity
      have h2t_top : ((2 : ℝ≥0∞) ^ t) ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofNat_ne_top
      have hl : (3 : ℝ≥0∞) * (2 : ℝ≥0∞) ^ t * ((2 : ℝ≥0∞) ^ t)⁻¹ * (acc : ℝ≥0∞) =
          ((3 * acc : ℕ) : ℝ≥0∞) := by
        rw [mul_assoc (3 : ℝ≥0∞), ENNReal.mul_inv_cancel h2t_ne h2t_top, mul_one,
          Nat.cast_mul, Nat.cast_ofNat]
      have hr : (3 : ℝ≥0∞) * (2 : ℝ≥0∞) ^ t * (1 / 3 : ℝ≥0∞) = ((2 ^ t : ℕ) : ℝ≥0∞) := by
        rw [mul_comm (3 : ℝ≥0∞), mul_assoc, one_div,
          ENNReal.mul_inv_cancel (by norm_num) (by norm_num), mul_one, Nat.cast_pow, Nat.cast_ofNat]
      rw [hl, hr] at hmul
      exact_mod_cast hmul
    have hpart : acc + rej = 2 ^ t := by
      have huniv : (Finset.univ : Finset (Fin t → Bool)).card = 2 ^ t := by simp
      rw [← huniv]
      simpa only [acc, rej, Bool.not_eq_true] using
        Finset.card_filter_add_card_filter_not (s := Finset.univ)
          (fun r : Fin t → Bool =>
            decide ((simRun M t (adviceProverReply S W (ψ, List.ofFn y))
              (encQBF ψ) (List.ofFn r)).tapes.output = [true]) = true)
    change 2 * 2 ^ t ≤ 3 * rej
    omega

/-! ### : Public theorems (`PSPACE ⊆ MA` and Kannan's language in `MA`) -/

/-- **Babai–Fortnow–Nisan–Wigderson collapse**: if `EXP ⊆ P/poly`, then `PSPACE ⊆ MA`
for every instance encoding `enc`. -/
theorem pspace_subset_MA_of_exp_subset_ppoly {α : Type} {enc : α ↪ List Bool}
    (hEXP : EXP encBits ⊆ PPolyOn encBits) :
    PSPACE enc ⊆ MA enc := fun A hA =>
  (TQBF_pspaceHard enc A hA).mem_MA (TQBF_mem_MA_of_exp_subset_ppoly hEXP)

/-- Under `EXP ⊆ P/poly`, Kannan's language `Kannan.language k` lies in `MA` for every `k`. -/
theorem kannan_mem_MA_of_exp_subset_ppoly (hEXP : EXP encBits ⊆ PPolyOn encBits) (k : ℕ) :
    (Kannan.language k : Set (List Bool)) ∈ MA encBits :=
  pspace_subset_MA_of_exp_subset_ppoly hEXP
    (SigmaP_subset_PSPACE 3 (Kannan.language_mem_SigmaP_three k))

end CslibFrontier.Complexity
