module

public import CslibFrontier.Computability.Complexity.Problems.Graph
public import CslibFrontier.Computability.Complexity.Reduction.CountingTuring
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder

import CslibFrontier.Computability.Complexity.Classes.Oracle.Closure
import CslibFrontier.Computability.Complexity.Classes.Oracle.Counting
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Probabilistic.Oracle.Composition
import CslibFrontier.Computability.Probabilistic.Oracle.Substitution
import Mathlib.Data.Nat.Bitwise

/-!
# Transitivity of Polynomial-Time Counting Turing Reductions

This module proves transitivity of polynomial-time counting Turing reductions
(`CountingTuringReducible`) and `#P`-hardness under counting Turing reductions
(`CountingTuringHard`) via open stateless oracle substitution, together with a total
polynomial-time decoder for `Cslib.Complexity.encGraph`.

## Main definitions

* `Cslib.Complexity.graphDecoder`: a total polynomial-time decoder for
  `Cslib.Complexity.encGraph`.

## Main results

* `Cslib.Complexity.countingTuringReducible_self_of_size_bound`: reflexivity for
  polynomially size-bounded counting functions.
* `Cslib.Complexity.countingTuringReducible_trans`: transitivity of
  `CountingTuringReducible` across any intermediate encoding with a total polynomial-time
  `Decoder`.
* `Cslib.Complexity.countingTuringHard_trans`: `#P`-hardness under counting
  Turing reductions transfers across a counting Turing reduction.
-/

public section

namespace Cslib.Complexity

open Cslib Cslib.Complexity Cslib.Probability Turing.MultiTapeTM

/-- A total polynomial-time decoder for `Cslib.Complexity.encGraph`. -/
@[expose] def graphDecoder : Decoder encGraph :=
  ((Decoder.nat.list).pair ((Decoder.nat.pair Decoder.nat).list)).map
    (fun p => Graph.mk p.1 p.2)
    (fun G => (G.vertices, G.edges))
    (fun _ => rfl)
    (fun _ => rfl)

/-- Every counting function reduces to itself once its binary length is polynomially bounded
(for example, for every function in `#P`). -/
theorem countingTuringReducible_self_of_size_bound {α : Type} (encA : α ↪ List Bool)
    (f : α → ℕ) (bound : α → ℕ)
    (hbound : ComputableInPolyTime bound encA encUnary)
    (hsize : ∀ a, (f a).size ≤ bound a) :
    CountingTuringReducible encA encA f f :=
  PolyTimeOracleProgram.of_batchNatBits (fun a => [a]) bound (fun p => p.2.headD 0)
    (ComputableInPolyTime.cons' ComputableInPolyTime.id' (ComputableInPolyTime.const []))
    hbound
    ((ComputableInPolyTime.headD 0).comp (ComputableInPolyTime.snd _ _))
    (fun a b hb => by
      simp only [List.mem_singleton] at hb
      subst hb
      exact hsize b)
    (fun _ => rfl)

/-- **Transitivity of polynomial-time counting Turing reductions**: if `f ≤_T^#P h` and
`h ≤_T^#P g` and `encB` admits a total polynomial-time `Decoder`, then `f ≤_T^#P g`. -/
theorem countingTuringReducible_trans {α β γ : Type}
    {encA : α ↪ List Bool} {encB : β ↪ List Bool} {encC : γ ↪ List Bool}
    {f : α → ℕ} {h : β → ℕ} {g : γ → ℕ} (D : Decoder encB)
    (hfh : CountingTuringReducible encA encB f h)
    (hhg : CountingTuringReducible encB encC h g) :
    CountingTuringReducible encA encC f g := by
  classical
  obtain ⟨progF, hprogF, hspecF⟩ := hfh
  obtain ⟨progH, hprogH, hspecH⟩ := hhg
  let D' : Decoder (encPair encB encNat) := D.pair Decoder.nat
  have hdec : ComputableInPolyTime D'.decode encBits (encPair encB encNat) :=
    D'.computableInPolyTime
  let bitOfWord (w : List Bool) : WordQueryComp Unit (List Bool) :=
    (fun val =>
      let p := D'.decode w
      [decide (encPair encB encNat p = w) && val.testBit (min val.size p.2)]) <$>
      progH (D'.decode w).1
  let handler : Unit × List Bool → WordQueryComp Unit (List Bool) :=
    fun q => bitOfWord q.2
  have hbitOfWord_ppt :
      IsOraclePPTOn encBits encBits
        (fun w => OracleComp.interpret ProbOracleComp.query (bitOfWord w)) := by
    have hprogH' :
        IsOraclePPTOn encBits encNat
          (fun w => OracleComp.interpret ProbOracleComp.query (progH (D'.decode w).1)) :=
      hprogH.preprocess ((ComputableInPolyTime.fst encB encNat).comp hdec)
    have hpost :
        ComputableInPolyTime
          (fun p : List Bool × ℕ =>
            let d := D'.decode p.1
            [decide (encPair encB encNat d = p.1) && p.2.testBit (min p.2.size d.2)])
          (encPair encBits encNat) encBits := by
      have hd : ComputableInPolyTime (fun p : List Bool × ℕ => D'.decode p.1)
          (encPair encBits encNat) (encPair encB encNat) :=
        hdec.comp (ComputableInPolyTime.fst encBits encNat)
      have hval : ComputableInPolyTime (fun p : List Bool × ℕ => p.2)
          (encPair encBits encNat) encNat :=
        ComputableInPolyTime.snd encBits encNat
      have heqCheck :
          ComputableInPolyTime
            (fun p : List Bool × ℕ => decide (encPair encB encNat (D'.decode p.1) = p.1))
            (encPair encBits encNat) encBool :=
        (ComputableInPolyTime.encoding_comp hd).decide_eq'
          (ComputableInPolyTime.fst encBits encNat)
      have hsize : ComputableInPolyTime (fun p : List Bool × ℕ => p.2.size)
          (encPair encBits encNat) encUnary :=
        ComputableInPolyTime.binary_size.comp hval
      have hidx : ComputableInPolyTime
          (fun p : List Bool × ℕ => min p.2.size (D'.decode p.1).2)
          (encPair encBits encNat) encUnary :=
        ComputableInPolyTime.binary_min_unary' hsize
          ((ComputableInPolyTime.snd encB encNat).comp hd)
      have hbit : ComputableInPolyTime
          (fun p : List Bool × ℕ => p.2.testBit (min p.2.size (D'.decode p.1).2))
          (encPair encBits encNat) encBool :=
        ComputableInPolyTime.binary_testBit hval hidx
      exact ComputableInPolyTime.bitsCons (heqCheck.bool_and' hbit)
        (ComputableInPolyTime.const ([] : List Bool))
    simpa only [bitOfWord, OracleComp.interpret_map] using hprogH'.map_with hpost
  have hhandler_ppt :
      IsOraclePPTOn (encPair encA (encPair (encFinEnum Unit) encBits)) encBits
        (fun p : α × (Unit × List Bool) =>
          OracleComp.interpret ProbOracleComp.query (handler p.2)) :=
    hbitOfWord_ppt.preprocess
      ((ComputableInPolyTime.snd (encFinEnum Unit) encBits).comp
        (ComputableInPolyTime.snd encA (encPair (encFinEnum Unit) encBits)))
  have hsub_ppt :
      IsOraclePPTOn encA encNat
        (fun a => OracleComp.interpret ProbOracleComp.query
          (OracleComp.interpret handler (progF a))) := by
    have h := hprogF.interpret_preprocess_open'
      (operationEncoding := encFinEnum Unit)
      (handler := fun (_ : α) (q : Unit × List Bool) =>
        OracleComp.interpret ProbOracleComp.query (handler q))
      (prepare := id) (resources := fun _ _ => 1) ComputableInPolyTime.id'
      hhandler_ppt (ComputableInPolyTime.const 1)
      fun _ q reply hreply => by
        dsimp only [handler, bitOfWord] at hreply
        rw [OracleComp.interpret_map] at hreply
        obtain ⟨_, -, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hreply
        simp
    convert h using 2 with a
    simp only [id, OracleComp.interpret_interpret, ProbOracleComp.interpret_query]
  refine ⟨fun a => OracleComp.interpret handler (progF a), hsub_ppt, fun A hA => ?_⟩
  have hhandler_eq :
      (fun q => OracleComp.interpret (m := Id) (languageOracle A) (handler q)) =
        languageOracle (bitGraph encB h) := by
    funext ⟨_, w⟩
    simp only [handler, bitOfWord, OracleComp.interpret_map,
      congrFun (hspecH A hA) (D'.decode w).1, languageOracle_apply]
    have hmin (n i : ℕ) : n.testBit (min n.size i) = n.testBit i := by
      rcases le_total i n.size with hle | hle
      · rw [min_eq_right hle]
      · rw [min_eq_left hle, Nat.testBit_eq_false_of_lt (Nat.lt_size_self n),
          Nat.testBit_eq_false_of_lt ((Nat.lt_size_self n).trans_le
            (Nat.pow_le_pow_right two_pos hle))]
    dsimp only [Functor.map, Id.run]
    rw [hmin]
    have hmem : w ∈ bitGraph encB h ↔
        encPair encB encNat (D'.decode w) = w ∧
          (h (D'.decode w).1).testBit (D'.decode w).2 = true := by
      constructor
      · rintro ⟨x, hx, rfl⟩
        rw [D'.decode_enc]
        exact ⟨rfl, hx⟩
      · rintro ⟨hw, hb⟩
        exact ⟨D'.decode w, hb, hw⟩
    by_cases hw : w ∈ bitGraph encB h
    · have hpair := hmem.mp hw
      simp [hw, hpair.1, hpair.2]
    · have hnot : ¬ (encPair encB encNat (D'.decode w) = w ∧
          (h (D'.decode w).1).testBit (D'.decode w).2 = true) := fun hp => hw (hmem.mpr hp)
      have hfalse : (decide (encPair encB encNat (D'.decode w) = w) &&
          (h (D'.decode w).1).testBit (D'.decode w).2) = false := by
        rw [Bool.and_eq_false_iff, decide_eq_false_iff_not]
        by_cases he : encPair encB encNat (D'.decode w) = w
        · right; cases hb : (h (D'.decode w).1).testBit (D'.decode w).2
          · rfl
          · exact False.elim (hnot ⟨he, hb⟩)
        · exact Or.inl he
      rw [hfalse, decide_eq_false hw]
  rw [show (fun a => OracleComp.interpret (m := Id) (languageOracle A)
        (OracleComp.interpret handler (progF a))) =
      fun a => OracleComp.interpret (m := Id) (languageOracle (bitGraph encB h)) (progF a) from
    funext fun a => by rw [OracleComp.interpret_interpret, hhandler_eq]]
  exact hspecF (bitGraph encB h) (answersBits_bitGraph encB h)

/-- Transfer `#P`-hardness under counting Turing reductions across a counting Turing reduction
whose intermediate encoding admits a total polynomial-time `Decoder`. -/
theorem countingTuringHard_trans {β γ : Type}
    {encB : β ↪ List Bool} {encC : γ ↪ List Bool}
    {h : β → ℕ} {g : γ → ℕ} (D : Decoder encB)
    (hh : CountingTuringHard encB h)
    (hhg : CountingTuringReducible encB encC h g) :
    CountingTuringHard encC g :=
  fun _ encA f hf => countingTuringReducible_trans D (hh encA f hf) hhg

end Cslib.Complexity
