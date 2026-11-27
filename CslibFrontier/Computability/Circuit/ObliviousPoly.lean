module

public import CslibFrontier.Computability.Circuit.Boolean.Encoding
public import CslibFrontier.Computability.Circuit.ObliviousSimulation
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Length
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Eq
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Length
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List.Size
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.NatLength
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Pair
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListLookup
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListMap
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListPrimitives
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeLoops
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeNatFrontends
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimePrimitives
import CslibFrontier.Foundations.Data.Nat.BinarySize
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Polynomial-Time Combinators for Oblivious Circuit Gadgets

This module supplies binary encodings
  (`encGates`, `encLevelW`, `encHalfW`, `encTapeW`, `encStateW`),
encoding-length bounds, and `Turing.MultiTapeTM.ComputableInPolyTime` certificates for the
constant-size Pippenger–Fischer local gadgets (`emitShiftLevel0`, `emitCntRebalance`,
`emitCellRebalance`, `emitOutUpdate`) together with wire/gate growth bounds for level rebalancing.

## Main definitions

* `CslibFrontier.Computability.Circuit.Oblivious.encGates`, `encLevelW`, `encHalfW`, `encTapeW`,
  `encStateW`: binary encodings of the oblivious circuit-builder state types.

## Main results

* `poly_getD_const`: constant-index `List.getD` in polynomial time.

* `CslibFrontier.Computability.Circuit.Oblivious.poly_emitShiftLevel0`, `poly_emitCntRebalance`,
  `poly_emitCellRebalance`, `poly_emitOutUpdate`: polynomial-time computability of the
  constant-size oblivious circuit gadgets.
-/

public section

namespace CslibFrontier.Computability.Circuit.Oblivious

open Turing MultiTapeTM Cslib.Circuits Cslib.Circuits.Boolean

/-! ### Binary encodings of oblivious circuit-builder state -/

/-- Binary encoding of `Gates`: reversed gate list + binary next-wire counter. -/
@[expose] def encGates : Gates ↪ List Bool :=
  encPair (encList Boolean.encGate) encNat

/-- Binary encoding of `LevelW`: 6 count wires + list of 10-wire rows. -/
@[expose] def encLevelW : LevelW ↪ List Bool :=
  encPair (encList encNat) (encList (encList encNat))

/-- Binary encoding of `HalfW`: list of `LevelW`s. -/
@[expose] def encHalfW : HalfW ↪ List Bool :=
  encList encLevelW

/-- Binary encoding of `TapeW`: head pair + left/right half-tapes. -/
@[expose] def encTapeW : TapeW ↪ List Bool :=
  encPair (encPair encNat encNat) (encPair encHalfW encHalfW)

/-- Binary encoding of `StateW`: `(stateW, outW)` + `(inTape, workTapes)`. -/
@[expose] def encStateW : StateW ↪ List Bool :=
  encPair (encPair (encList encNat) (encList encNat)) (encPair encTapeW (encList encTapeW))

/-! ### Encoding-length upper and lower bounds -/

theorem length_encNat_le_of_le {a b : ℕ} (h : a ≤ b) :
    (encNat a).length ≤ (encNat b).length := by
  rw [encNat_apply, encNat_apply, Nat.size_eq_bits_len, Nat.size_eq_bits_len]
  exact Nat.size_le.mpr (lt_of_le_of_lt h (Nat.lt_size_self b))

theorem length_encNat_le_add {w a b : ℕ} (h : w ≤ a + b) :
    (encNat w).length ≤ (encNat a).length + b + 1 := by
  have h1 : w < 2 ^ (a.size + b.size + 1) := by
    have ha : a < 2 ^ a.size := Nat.lt_size_self a
    have hb : b < 2 ^ b.size := Nat.lt_size_self b
    have hpa : 2 ^ a.size ≤ 2 ^ (a.size + b.size) :=
      Nat.pow_le_pow_right (by norm_num) (Nat.le_add_right _ _)
    have hpb : 2 ^ b.size ≤ 2 ^ (a.size + b.size) :=
      Nat.pow_le_pow_right (by norm_num) (Nat.le_add_left _ _)
    rw [pow_succ]; omega
  have h2 : (encNat w).length ≤ a.size + b.size + 1 := length_encNat_le_of_lt_two_pow h1
  have ha_eq : (encNat a).length = a.size := by rw [encNat_apply, Nat.size_eq_bits_len]
  have hb_le : b.size ≤ b := Nat.size_le.mpr Nat.lt_two_pow_self
  rw [← ha_eq] at h2; omega

theorem length_encGate_le {gt : Boolean.Op × List ℕ} {W : ℕ}
    (hlen : gt.2.length ≤ 2) (hw : ∀ w ∈ gt.2, (encNat w).length ≤ W) :
    (Boolean.encGate gt).length ≤ 4 * W + 11 := by
  change (encPair Boolean.encOp (encList encNat) gt).length ≤ 4 * W + 11
  rw [length_encPair]; have hop : (Boolean.encOp gt.1).length ≤ 4 := by
    change (encUnary gt.1.toNat).length ≤ 4
    simp only [encUnary_apply, List.length_replicate]; cases gt.1 with
    | const b => cases b <;> decide
    | not => decide
    | and => decide
    | or => decide
  have hl : (encList encNat gt.2).length ≤ gt.2.length * (2 * W + 1) :=
    length_encList_le encNat gt.2 hw
  have hmul : gt.2.length * (2 * W + 1) ≤ 2 * (2 * W + 1) :=
    Nat.mul_le_mul_right _ hlen
  omega

theorem length_le_encList {α : Type} (enc : α ↪ List Bool) (l : List α) :
    l.length ≤ (encList enc l).length := by
  induction l with
  | nil => simp
  | cons a tl ih =>
    simp only [encList_cons, List.length_append, List.length_cons, length_frame]; omega

theorem length_encGates_le {g : Gates} {M G W : ℕ}
    (h1 : g.1.length ≤ M) (h2 : ∀ gt ∈ g.1, (Boolean.encGate gt).length ≤ G)
    (h3 : (encNat g.2).length ≤ W) :
    (encGates g).length ≤ 2 * (M * (2 * G + 1)) + 1 + W := by
  change (encPair (encList Boolean.encGate) encNat g).length ≤ _
  rw [length_encPair]; have hl : (encList Boolean.encGate g.1).length ≤ M * (2 * G + 1) :=
    (length_encList_le Boolean.encGate g.1 h2).trans (Nat.mul_le_mul_right _ h1)
  omega

theorem length_encLevelW_le {lv : LevelW} {MC MR RL W : ℕ}
    (h1 : lv.1.length ≤ MC) (h2 : ∀ w ∈ lv.1, (encNat w).length ≤ W)
    (h3 : lv.2.length ≤ MR)
    (h4 : ∀ r ∈ lv.2, r.length ≤ RL ∧ ∀ w ∈ r, (encNat w).length ≤ W) :
    (encLevelW lv).length ≤ 2 * (MC * (2 * W + 1)) + 1 + MR * (2 * (RL * (2 * W + 1)) + 1) := by
  change (encPair (encList encNat) (encList (encList encNat)) lv).length ≤ _
  rw [length_encPair]; have hc : (encList encNat lv.1).length ≤ MC * (2 * W + 1) :=
    (length_encList_le encNat lv.1 h2).trans (Nat.mul_le_mul_right _ h1)
  have hr : (encList (encList encNat) lv.2).length ≤ MR * (2 * (RL * (2 * W + 1)) + 1) := by
    refine (length_encList_le (encList encNat) lv.2 fun r hr => ?_).trans
      (Nat.mul_le_mul_right _ h3)
    exact (length_encList_le encNat r (h4 r hr).2).trans (Nat.mul_le_mul_right _ (h4 r hr).1)
  omega

theorem length_encRow_of_mem {lv : LevelW} {r : List ℕ} (h : r ∈ lv.2) :
    (encList encNat r).length ≤ (encLevelW lv).length := by
  have h1 : (encList encNat r).length ≤ (encList (encList encNat) lv.2).length :=
    length_le_encList_of_mem (encList encNat) h
  change _ ≤ (encPair (encList encNat) (encList (encList encNat)) lv).length
  rw [length_encPair]; omega

theorem length_encHalfW_sum_rows (hw : HalfW) :
    (hw.map fun lv => 1 + lv.2.length).sum ≤ (encHalfW hw).length := by
  induction hw with
  | nil => simp
  | cons lv tl ih =>
    have hcons : (encHalfW (lv :: tl)).length =
        2 * (encLevelW lv).length + 1 + (encHalfW tl).length := by
      change (encList encLevelW (lv :: tl)).length = _
      rw [encList_cons, List.length_append, length_frame]; rfl
    have hlv : lv.2.length ≤ (encLevelW lv).length := by
      have h1 := length_le_encList (encList encNat) lv.2
      change _ ≤ (encPair (encList encNat) (encList (encList encNat)) lv).length
      rw [length_encPair]; omega
    simp only [List.map_cons, List.sum_cons, hcons]; omega

theorem sum_getD_rows_le_encHalfW (hw : HalfW) :
    ((List.range hw.length).map fun i => 1 + (hw.getD i ([], [])).2.length).sum ≤
      (encHalfW hw).length := by
  have heq : (List.range hw.length).map (fun i => 1 + (hw.getD i ([], [])).2.length) =
      hw.map (fun lv => 1 + lv.2.length) := by
    apply List.ext_getElem (by simp)
    intro i hi _; simp only [List.length_map, List.length_range] at hi
    simp only [List.getElem_map, List.getElem_range, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hi, Option.getD_some]
  rw [heq]; exact length_encHalfW_sum_rows hw

/-! ### Core `ComputableInPolyTime` combinators -/

theorem poly_foldl_const {ι α β : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool}
    (l : List ι) (init : α → β) (step : α → β → ι → β)
    (hinit : ComputableInPolyTime init encA encB)
    (hstep : ∀ i ∈ l,
      ComputableInPolyTime (fun p : α × β => step p.1 p.2 i) (encPair encA encB) encB) :
    ComputableInPolyTime (fun a => l.foldl (step a) (init a)) encA encB := by
  induction l generalizing init with
  | nil => simpa using hinit
  | cons i tl ih =>
    simp only [List.foldl_cons]
    refine ih (fun a => step a (init a) i) ?_ (fun j hj => hstep j (List.mem_cons_of_mem i hj))
    exact @ComputableInPolyTime.comp' α (α × β) β encA (encPair encA encB) encB
      (fun p => step p.1 p.2 i) (fun a => (a, init a))
      (hstep i List.mem_cons_self) (ComputableInPolyTime.id'.prod hinit)

theorem poly_cons' {α γ : Type} {encIn : γ ↪ List Bool} {encA : α ↪ List Bool}
    {hd : γ → α} {tl : γ → List α}
    (hhd : ComputableInPolyTime hd encIn encA)
    (htl : ComputableInPolyTime tl encIn (encList encA)) :
    ComputableInPolyTime (fun x => hd x :: tl x) encIn (encList encA) :=
  @ComputableInPolyTime.comp' γ (α × List α) (List α) encIn (encPair encA (encList encA))
    (encList encA)
    (fun p => p.1 :: p.2) (fun x => (hd x, tl x)) (ComputableInPolyTime.cons encA) (hhd.prod htl)

theorem poly_append' {α γ : Type} {encIn : γ ↪ List Bool} {encA : α ↪ List Bool}
    {l₁ l₂ : γ → List α}
    (h₁ : ComputableInPolyTime l₁ encIn (encList encA))
    (h₂ : ComputableInPolyTime l₂ encIn (encList encA)) :
    ComputableInPolyTime (fun x => l₁ x ++ l₂ x) encIn (encList encA) :=
  @ComputableInPolyTime.comp' γ (List α × List α) (List α) encIn
    (encPair (encList encA) (encList encA)) (encList encA)
    (fun p => p.1 ++ p.2) (fun x => (l₁ x,
      l₂ x)) (ComputableInPolyTime.listAppend encA) (h₁.prod h₂)

@[fun_prop] theorem poly_getD_const {α γ : Type} {encIn : γ ↪ List Bool} {encA : α ↪ List Bool}
    {l : γ → List α} (hl : ComputableInPolyTime l encIn (encList encA)) (i : ℕ) (d : α) :
    ComputableInPolyTime (fun x => (l x).getD i d) encIn encA :=
  ComputableInPolyTime.listGetDWithInput hl (ComputableInPolyTime.const i) d

theorem poly_bool_and {γ : Type} {encIn : γ ↪ List Bool} {a b : γ → Bool}
    (ha : ComputableInPolyTime a encIn encBool)
    (hb : ComputableInPolyTime b encIn encBool) :
    ComputableInPolyTime (fun x => a x && b x) encIn encBool :=
  @ComputableInPolyTime.comp' γ (Bool × Bool) Bool encIn (encPair encBool encBool) encBool
    (fun p => p.1 && p.2) (fun x => (a x, b x))
    (ComputableInPolyTime.of_finite (fun p : Bool × Bool => p.1 && p.2)) (ha.prod hb)

theorem poly_binary_eq' {γ : Type} {encIn : γ ↪ List Bool} {a b : γ → ℕ}
    (ha : ComputableInPolyTime a encIn encNat)
    (hb : ComputableInPolyTime b encIn encNat) :
    ComputableInPolyTime (fun x => decide (a x = b x)) encIn encBool := by
  have h1 := ComputableInPolyTime.binary_lt' ha hb
  have h2 := ComputableInPolyTime.binary_lt' hb ha
  have h : ComputableInPolyTime (fun x => !(decide (a x < b x)) && !(decide (b x < a x)))
      encIn encBool :=
    @ComputableInPolyTime.comp' γ (Bool × Bool) Bool encIn (encPair encBool encBool) encBool
      (fun p => !p.1 && !p.2) (fun x => (decide (a x < b x), decide (b x < a x)))
      (ComputableInPolyTime.of_finite (fun p : Bool × Bool => !p.1 && !p.2)) (h1.prod h2)
  refine h.of_enc_eq fun x => congrArg encBool ?_
  by_cases hlt1 : a x < b x
  · have hne : a x ≠ b x := by omega
    simp [hlt1, hne]
  · by_cases hlt2 : b x < a x
    · have hne : a x ≠ b x := by omega
      simp [hlt1, hlt2, hne]
    · have heq : a x = b x := by omega
      simp [heq]

theorem poly_fst {α β₁ β₂ : Type} {encIn : α ↪ List Bool}
    {enc₁ : β₁ ↪ List Bool} {enc₂ : β₂ ↪ List Bool} {f : α → β₁ × β₂}
    (hf : ComputableInPolyTime f encIn (encPair enc₁ enc₂)) :
    ComputableInPolyTime (fun x => (f x).1) encIn enc₁ :=
  @ComputableInPolyTime.comp' α (β₁ × β₂) β₁ encIn (encPair enc₁ enc₂) enc₁
    (fun p => p.1) f (ComputableInPolyTime.fst enc₁ enc₂) hf

theorem poly_snd {α β₁ β₂ : Type} {encIn : α ↪ List Bool}
    {enc₁ : β₁ ↪ List Bool} {enc₂ : β₂ ↪ List Bool} {f : α → β₁ × β₂}
    (hf : ComputableInPolyTime f encIn (encPair enc₁ enc₂)) :
    ComputableInPolyTime (fun x => (f x).2) encIn enc₂ :=
  @ComputableInPolyTime.comp' α (β₁ × β₂) β₂ encIn (encPair enc₁ enc₂) enc₂
    (fun p => p.2) f (ComputableInPolyTime.snd enc₁ enc₂) hf

theorem poly_comp_fst {α β γ : Type} {enc₁ : α ↪ List Bool}
    {enc₂ : β ↪ List Bool} {encOut : γ ↪ List Bool} {f : α → γ}
    (hf : ComputableInPolyTime f enc₁ encOut) :
    ComputableInPolyTime (fun p : α × β => f p.1) (encPair enc₁ enc₂) encOut :=
  @ComputableInPolyTime.comp' (α × β) α γ (encPair enc₁ enc₂) enc₁ encOut
    f (fun p => p.1) hf (ComputableInPolyTime.fst enc₁ enc₂)

theorem poly_emitMap_const {ι γ : Type} {encIn : γ ↪ List Bool}
    (xs : List ι) (f : γ → Gates → ι → Gates × ℕ)
    (hf : ∀ i ∈ xs, ComputableInPolyTime (fun p : γ × Gates => f p.1 p.2 i)
      (encPair encIn encGates) (encPair encGates encNat)) :
    ComputableInPolyTime (fun p : γ × Gates => emitMap p.2 (f p.1) xs)
      (encPair encIn encGates) (encPair encGates (encList encNat)) := by
  simp only [emitMap_eq]
  have hfold : ComputableInPolyTime
      (fun p : γ × Gates => xs.foldl (fun (acc : Gates × List ℕ) (a : ι) =>
        let r := f p.1 acc.1 a; (r.1, r.2 :: acc.2)) (p.2, []))
      (encPair encIn encGates) (encPair encGates (encList encNat)) := by
    refine poly_foldl_const xs
      (fun p : γ × Gates => (p.2, ([] : List ℕ)))
      (fun (p : γ × Gates) (acc : Gates × List ℕ) (a : ι) =>
        let r := f p.1 acc.1 a; (r.1, r.2 :: acc.2))
      ((ComputableInPolyTime.snd encIn encGates).prod (ComputableInPolyTime.const []))
      (fun i hi => ?_)
    have hq1 : ComputableInPolyTime (fun q : (γ × Gates) × (Gates × List ℕ) => q.1.1)
        (encPair (encPair encIn encGates) (encPair encGates (encList encNat))) encIn :=
      poly_fst (ComputableInPolyTime.fst (encPair encIn encGates)
        (encPair encGates (encList encNat)))
    have hq2 : ComputableInPolyTime (fun q : (γ × Gates) × (Gates × List ℕ) => q.2.1)
        (encPair (encPair encIn encGates) (encPair encGates (encList encNat))) encGates :=
      poly_fst (ComputableInPolyTime.snd (encPair encIn encGates)
        (encPair encGates (encList encNat)))
    have hstep_f : ComputableInPolyTime
        (fun q : (γ × Gates) × (Gates × List ℕ) => f q.1.1 q.2.1 i)
        (encPair (encPair encIn encGates) (encPair encGates (encList encNat)))
        (encPair encGates encNat) :=
      @ComputableInPolyTime.comp' ((γ × Gates) × (Gates × List ℕ)) (γ × Gates) (Gates × ℕ)
        (encPair (encPair encIn encGates) (encPair encGates (encList encNat)))
        (encPair encIn encGates) (encPair encGates encNat)
        (fun p => f p.1 p.2 i) (fun q => (q.1.1, q.2.1))
        (hf i hi) (hq1.prod hq2)
    have hacc2 : ComputableInPolyTime
        (fun q : (γ × Gates) × (Gates × List ℕ) => q.2.2)
        (encPair (encPair encIn encGates) (encPair encGates (encList encNat)))
        (encList encNat) :=
      poly_snd (ComputableInPolyTime.snd (encPair encIn encGates)
        (encPair encGates (encList encNat)))
    exact ((poly_fst hstep_f).prod (poly_cons' (poly_snd hstep_f) hacc2)).of_enc_eq fun _ => rfl
  exact ((poly_fst hfold).prod (ComputableInPolyTime.listReverseWithInput
    (poly_snd hfold))).of_enc_eq
    fun _ => rfl

theorem poly_emitMap_mapConst {α γ : Type} {encIn : γ ↪ List Bool}
    (fs : List (γ → α)) (fg : γ → Gates) (step : γ → Gates → α → Gates × ℕ)
    (hg : ComputableInPolyTime fg encIn encGates)
    (hstep : ∀ f ∈ fs, ComputableInPolyTime (fun p : γ × Gates => step p.1 p.2 (f p.1))
      (encPair encIn encGates) (encPair encGates encNat)) :
    ComputableInPolyTime (fun x => emitMap (fg x) (step x) (fs.map fun f => f x))
      encIn (encPair encGates (encList encNat)) := by
  have h1 := @poly_emitMap_const (γ → α) γ encIn fs (fun x g₀ f => step x g₀ (f x)) hstep
  have h2 := @ComputableInPolyTime.comp' γ (γ × Gates) (Gates × List ℕ) encIn
    (encPair encIn encGates) (encPair encGates (encList encNat))
    _ (fun x => (x, fg x)) h1 (ComputableInPolyTime.id'.prod hg)
  exact h2.of_enc_eq fun x => congrArg (encPair encGates (encList encNat)) (by
    simp [emitMap_eq, List.foldl_map])

/-! ### `ComputableInPolyTime` for gate builders -/

theorem poly_gNot :
    ComputableInPolyTime (fun p : Gates × ℕ => Gates.gNot p.1 p.2)
      (encPair encGates encNat) (encPair encGates encNat) := by
  simp only [Gates.gNot_eq, Gates.emit_eq]
  have hg1 : ComputableInPolyTime (fun p : Gates × ℕ => p.1.1)
      (encPair encGates encNat) (encList Boolean.encGate) :=
    (ComputableInPolyTime.fst (encList Boolean.encGate) encNat).comp'
      (ComputableInPolyTime.fst encGates encNat)
  have hg2 : ComputableInPolyTime (fun p : Gates × ℕ => p.1.2)
      (encPair encGates encNat) encNat :=
    (ComputableInPolyTime.snd (encList Boolean.encGate) encNat).comp'
      (ComputableInPolyTime.fst encGates encNat)
  have hw := ComputableInPolyTime.snd encGates encNat
  have hgate : ComputableInPolyTime (fun p : Gates × ℕ => (Boolean.Op.not, [p.2]))
      (encPair encGates encNat) Boolean.encGate :=
    (ComputableInPolyTime.const Boolean.Op.not).prod
      (poly_cons' hw (ComputableInPolyTime.const []))
  exact ((poly_cons' hgate hg1).prod
      (ComputableInPolyTime.binary_add' hg2 (ComputableInPolyTime.const 1))).prod hg2

theorem poly_gAnd :
    ComputableInPolyTime (fun p : Gates × ℕ × ℕ => Gates.gAnd p.1 p.2.1 p.2.2)
      (encPair encGates (encPair encNat encNat)) (encPair encGates encNat) := by
  simp only [Gates.gAnd_eq, Gates.emit_eq]
  have hg1 : ComputableInPolyTime (fun p : Gates × ℕ × ℕ => p.1.1)
      (encPair encGates (encPair encNat encNat)) (encList Boolean.encGate) :=
    (ComputableInPolyTime.fst (encList Boolean.encGate) encNat).comp'
      (ComputableInPolyTime.fst encGates (encPair encNat encNat))
  have hg2 : ComputableInPolyTime (fun p : Gates × ℕ × ℕ => p.1.2)
      (encPair encGates (encPair encNat encNat)) encNat :=
    (ComputableInPolyTime.snd (encList Boolean.encGate) encNat).comp'
      (ComputableInPolyTime.fst encGates (encPair encNat encNat))
  have ha := (ComputableInPolyTime.fst encNat encNat).comp'
    (ComputableInPolyTime.snd encGates (encPair encNat encNat))
  have hb := (ComputableInPolyTime.snd encNat encNat).comp'
    (ComputableInPolyTime.snd encGates (encPair encNat encNat))
  have hgate : ComputableInPolyTime (fun p : Gates × ℕ × ℕ => (Boolean.Op.and, [p.2.1, p.2.2]))
      (encPair encGates (encPair encNat encNat)) Boolean.encGate :=
    (ComputableInPolyTime.const Boolean.Op.and).prod
      (poly_cons' ha (poly_cons' hb (ComputableInPolyTime.const [])))
  exact ((poly_cons' hgate hg1).prod
      (ComputableInPolyTime.binary_add' hg2 (ComputableInPolyTime.const 1))).prod hg2

theorem poly_gOr :
    ComputableInPolyTime (fun p : Gates × ℕ × ℕ => Gates.gOr p.1 p.2.1 p.2.2)
      (encPair encGates (encPair encNat encNat)) (encPair encGates encNat) := by
  simp only [Gates.gOr_eq, Gates.emit_eq]
  have hg1 : ComputableInPolyTime (fun p : Gates × ℕ × ℕ => p.1.1)
      (encPair encGates (encPair encNat encNat)) (encList Boolean.encGate) :=
    (ComputableInPolyTime.fst (encList Boolean.encGate) encNat).comp'
      (ComputableInPolyTime.fst encGates (encPair encNat encNat))
  have hg2 : ComputableInPolyTime (fun p : Gates × ℕ × ℕ => p.1.2)
      (encPair encGates (encPair encNat encNat)) encNat :=
    (ComputableInPolyTime.snd (encList Boolean.encGate) encNat).comp'
      (ComputableInPolyTime.fst encGates (encPair encNat encNat))
  have ha := (ComputableInPolyTime.fst encNat encNat).comp'
    (ComputableInPolyTime.snd encGates (encPair encNat encNat))
  have hb := (ComputableInPolyTime.snd encNat encNat).comp'
    (ComputableInPolyTime.snd encGates (encPair encNat encNat))
  have hgate : ComputableInPolyTime (fun p : Gates × ℕ × ℕ => (Boolean.Op.or, [p.2.1, p.2.2]))
      (encPair encGates (encPair encNat encNat)) Boolean.encGate :=
    (ComputableInPolyTime.const Boolean.Op.or).prod
      (poly_cons' ha (poly_cons' hb (ComputableInPolyTime.const [])))
  exact ((poly_cons' hgate hg1).prod
      (ComputableInPolyTime.binary_add' hg2 (ComputableInPolyTime.const 1))).prod hg2

theorem poly_gNot' {γ : Type} {encIn : γ ↪ List Bool}
    {fg : γ → Gates} {fw : γ → ℕ}
    (hg : ComputableInPolyTime fg encIn encGates)
    (hw : ComputableInPolyTime fw encIn encNat) :
    ComputableInPolyTime (fun x => Gates.gNot (fg x) (fw x)) encIn (encPair encGates encNat) :=
  @ComputableInPolyTime.comp' γ (Gates × ℕ) (Gates × ℕ) encIn (encPair encGates encNat)
    (encPair encGates encNat) (fun p => Gates.gNot p.1 p.2) (fun x => (fg x, fw x))
    poly_gNot (hg.prod hw)

theorem poly_gAnd' {γ : Type} {encIn : γ ↪ List Bool}
    {fg : γ → Gates} {fa fb : γ → ℕ}
    (hg : ComputableInPolyTime fg encIn encGates)
    (ha : ComputableInPolyTime fa encIn encNat)
    (hb : ComputableInPolyTime fb encIn encNat) :
    ComputableInPolyTime (fun x => Gates.gAnd (fg x) (fa x) (fb x)) encIn
      (encPair encGates encNat) :=
  @ComputableInPolyTime.comp' γ (Gates × ℕ × ℕ) (Gates × ℕ) encIn
    (encPair encGates (encPair encNat encNat)) (encPair encGates encNat)
    (fun p => Gates.gAnd p.1 p.2.1 p.2.2) (fun x => (fg x, (fa x, fb x)))
    poly_gAnd (hg.prod (ha.prod hb))

theorem poly_gOr' {γ : Type} {encIn : γ ↪ List Bool}
    {fg : γ → Gates} {fa fb : γ → ℕ}
    (hg : ComputableInPolyTime fg encIn encGates)
    (ha : ComputableInPolyTime fa encIn encNat)
    (hb : ComputableInPolyTime fb encIn encNat) :
    ComputableInPolyTime (fun x => Gates.gOr (fg x) (fa x) (fb x)) encIn
      (encPair encGates encNat) :=
  @ComputableInPolyTime.comp' γ (Gates × ℕ × ℕ) (Gates × ℕ) encIn
    (encPair encGates (encPair encNat encNat)) (encPair encGates encNat)
    (fun p => Gates.gOr p.1 p.2.1 p.2.2) (fun x => (fg x, (fa x, fb x)))
    poly_gOr (hg.prod (ha.prod hb))

theorem poly_gOr3' {γ : Type} {encIn : γ ↪ List Bool}
    {fg : γ → Gates} {fa fb fc : γ → ℕ}
    (hg : ComputableInPolyTime fg encIn encGates)
    (ha : ComputableInPolyTime fa encIn encNat)
    (hb : ComputableInPolyTime fb encIn encNat)
    (hc : ComputableInPolyTime fc encIn encNat) :
    ComputableInPolyTime (fun x => Gates.gOr3 (fg x) (fa x) (fb x) (fc x)) encIn
      (encPair encGates encNat) := by
  simp only [Gates.gOr3_eq]
  have hr1 := poly_gOr' hg ha hb
  exact poly_gOr' ((ComputableInPolyTime.fst encGates encNat).comp' hr1)
    ((ComputableInPolyTime.snd encGates encNat).comp' hr1) hc

theorem poly_gOr4' {γ : Type} {encIn : γ ↪ List Bool}
    {fg : γ → Gates} {fa fb fc fd : γ → ℕ}
    (hg : ComputableInPolyTime fg encIn encGates)
    (ha : ComputableInPolyTime fa encIn encNat)
    (hb : ComputableInPolyTime fb encIn encNat)
    (hc : ComputableInPolyTime fc encIn encNat)
    (hd : ComputableInPolyTime fd encIn encNat) :
    ComputableInPolyTime (fun x => Gates.gOr4 (fg x) (fa x) (fb x) (fc x) (fd x)) encIn
      (encPair encGates encNat) := by
  simp only [Gates.gOr4_eq]
  have hr1 := poly_gOr' hg ha hb
  have hr2 := poly_gOr' ((ComputableInPolyTime.fst encGates encNat).comp' hr1) hc hd
  exact poly_gOr' ((ComputableInPolyTime.fst encGates encNat).comp' hr2)
    ((ComputableInPolyTime.snd encGates encNat).comp' hr1)
    ((ComputableInPolyTime.snd encGates encNat).comp' hr2)

theorem poly_gMux3' {γ : Type} {encIn : γ ↪ List Bool}
    {fg : γ → Gates} {fs0 fv0 fs1 fv1 fs2 fv2 : γ → ℕ}
    (hg : ComputableInPolyTime fg encIn encGates)
    (hs0 : ComputableInPolyTime fs0 encIn encNat) (hv0 : ComputableInPolyTime fv0 encIn encNat)
    (hs1 : ComputableInPolyTime fs1 encIn encNat) (hv1 : ComputableInPolyTime fv1 encIn encNat)
    (hs2 : ComputableInPolyTime fs2 encIn encNat) (hv2 : ComputableInPolyTime fv2 encIn encNat) :
    ComputableInPolyTime
      (fun x => Gates.gMux3 (fg x) (fs0 x) (fv0 x) (fs1 x) (fv1 x) (fs2 x) (fv2 x))
      encIn (encPair encGates encNat) := by
  simp only [Gates.gMux3_eq]
  have r1 := poly_gAnd' hg hs0 hv0
  have r2 := poly_gAnd' ((ComputableInPolyTime.fst encGates encNat).comp' r1) hs1 hv1
  have r3 := poly_gAnd' ((ComputableInPolyTime.fst encGates encNat).comp' r2) hs2 hv2
  exact poly_gOr3' ((ComputableInPolyTime.fst encGates encNat).comp' r3)
    ((ComputableInPolyTime.snd encGates encNat).comp' r1)
    ((ComputableInPolyTime.snd encGates encNat).comp' r2)
    ((ComputableInPolyTime.snd encGates encNat).comp' r3)

theorem poly_gMux4' {γ : Type} {encIn : γ ↪ List Bool}
    {fg : γ → Gates} {fs0 fv0 fs1 fv1 fs2 fv2 fs3 fv3 : γ → ℕ}
    (hg : ComputableInPolyTime fg encIn encGates)
    (hs0 : ComputableInPolyTime fs0 encIn encNat) (hv0 : ComputableInPolyTime fv0 encIn encNat)
    (hs1 : ComputableInPolyTime fs1 encIn encNat) (hv1 : ComputableInPolyTime fv1 encIn encNat)
    (hs2 : ComputableInPolyTime fs2 encIn encNat) (hv2 : ComputableInPolyTime fv2 encIn encNat)
    (hs3 : ComputableInPolyTime fs3 encIn encNat) (hv3 : ComputableInPolyTime fv3 encIn encNat) :
    ComputableInPolyTime
      (fun x => Gates.gMux4 (fg x) (fs0 x) (fv0 x) (fs1 x) (fv1 x) (fs2 x) (fv2 x) (fs3 x) (fv3 x))
      encIn (encPair encGates encNat) := by
  simp only [Gates.gMux4_eq]
  have r1 := poly_gAnd' hg hs0 hv0
  have r2 := poly_gAnd' ((ComputableInPolyTime.fst encGates encNat).comp' r1) hs1 hv1
  have r3 := poly_gAnd' ((ComputableInPolyTime.fst encGates encNat).comp' r2) hs2 hv2
  have r4 := poly_gAnd' ((ComputableInPolyTime.fst encGates encNat).comp' r3) hs3 hv3
  exact poly_gOr4' ((ComputableInPolyTime.fst encGates encNat).comp' r4)
    ((ComputableInPolyTime.snd encGates encNat).comp' r1)
    ((ComputableInPolyTime.snd encGates encNat).comp' r2)
    ((ComputableInPolyTime.snd encGates encNat).comp' r3)
    ((ComputableInPolyTime.snd encGates encNat).comp' r4)

theorem poly_gOrList_const {ι γ : Type} {encIn : γ ↪ List Bool}
    (l : List ι) (fg : γ → Gates) (fbase : γ → ℕ) (fw : γ → ι → ℕ)
    (hg : ComputableInPolyTime fg encIn encGates)
    (hbase : ComputableInPolyTime fbase encIn encNat)
    (hw : ∀ i ∈ l, ComputableInPolyTime (fun x => fw x i) encIn encNat) :
    ComputableInPolyTime (fun x => Gates.gOrList (fg x) (fbase x) (l.map (fw x)))
      encIn (encPair encGates encNat) := by
  have heq : (fun x => Gates.gOrList (fg x) (fbase x) (l.map (fw x))) =
      fun x => l.foldl (fun acc i => Gates.gOr acc.1 acc.2 (fw x i)) (fg x, fbase x) := by
    funext x; simp [Gates.gOrList_eq, List.foldl_map]
  rw [heq]; exact poly_foldl_const l (fun x => (fg x, fbase x))
    (fun x acc i => Gates.gOr acc.1 acc.2 (fw x i)) (hg.prod hbase)
    (fun i hi => poly_gOr'
      ((ComputableInPolyTime.fst encGates encNat).comp'
        (ComputableInPolyTime.snd encIn (encPair encGates encNat)))
      ((ComputableInPolyTime.snd encGates encNat).comp'
        (ComputableInPolyTime.snd encIn (encPair encGates encNat)))
      ((hw i hi).comp' (ComputableInPolyTime.fst encIn (encPair encGates encNat))))

theorem poly_gAndList_const {ι γ : Type} {encIn : γ ↪ List Bool}
    (l : List ι) (fg : γ → Gates) (fbase : γ → ℕ) (fw : γ → ι → ℕ)
    (hg : ComputableInPolyTime fg encIn encGates)
    (hbase : ComputableInPolyTime fbase encIn encNat)
    (hw : ∀ i ∈ l, ComputableInPolyTime (fun x => fw x i) encIn encNat) :
    ComputableInPolyTime (fun x => Gates.gAndList (fg x) (fbase x) (l.map (fw x)))
      encIn (encPair encGates encNat) := by
  have heq : (fun x => Gates.gAndList (fg x) (fbase x) (l.map (fw x))) =
      fun x => l.foldl (fun acc i => Gates.gAnd acc.1 acc.2 (fw x i)) (fg x, fbase x) := by
    funext x; simp [Gates.gAndList_eq, List.foldl_map]
  rw [heq]; exact poly_foldl_const l (fun x => (fg x, fbase x))
    (fun x acc i => Gates.gAnd acc.1 acc.2 (fw x i)) (hg.prod hbase)
    (fun i hi => poly_gAnd'
      ((ComputableInPolyTime.fst encGates encNat).comp'
        (ComputableInPolyTime.snd encIn (encPair encGates encNat)))
      ((ComputableInPolyTime.snd encGates encNat).comp'
        (ComputableInPolyTime.snd encIn (encPair encGates encNat)))
      ((hw i hi).comp' (ComputableInPolyTime.fst encIn (encPair encGates encNat))))

/-! ### Wire/gate bounds for `emitCntRebalance` and `emitCellRebalance` -/

theorem emit_wire_bounds {g : Gates} {op : Boolean.Op} {args : List ℕ} {G W : ℕ}
    (hlen : args.length ≤ 2) (hargs : ∀ w ∈ args, (encNat w).length ≤ W)
    (hG : 4 * W + 11 ≤ G) (hg1 : ∀ gt ∈ g.1, (Boolean.encGate gt).length ≤ G)
    (hg2 : (encNat g.2).length ≤ W) :
    let r := g.emit op args
    r.1.1.length = g.1.length + 1 ∧ r.1.2 = g.2 + 1 ∧ (encNat r.2).length ≤ W ∧
    (∀ gt ∈ r.1.1, (Boolean.encGate gt).length ≤ G) := by
  refine ⟨rfl, rfl, hg2, fun gt hgt => ?_⟩
  simp only [Gates.emit_eq, List.mem_cons] at hgt
  rcases hgt with rfl | hgt
  · exact (length_encGate_le hlen hargs).trans hG
  · exact hg1 gt hgt

theorem emitMap_bounds {α : Type} {g : Gates} {f : Gates → α → Gates × ℕ}
    {xs : List α} {K G W : ℕ}
    (hf : ∀ g₀ a, a ∈ xs → (∀ gt ∈ g₀.1, (Boolean.encGate gt).length ≤ G) →
      (encNat g₀.2).length ≤ W → g₀.2 + K ≤ g.2 + K * xs.length →
      let r := f g₀ a
      r.1.1.length = g₀.1.length + K ∧ r.1.2 = g₀.2 + K ∧ (encNat r.2).length ≤ W ∧
      (∀ gt ∈ r.1.1, (Boolean.encGate gt).length ≤ G))
    (hg1 : ∀ gt ∈ g.1, (Boolean.encGate gt).length ≤ G)
    (hW : (encNat (g.2 + K * xs.length)).length ≤ W) :
    let r := emitMap g f xs
    r.1.1.length = g.1.length + K * xs.length ∧ r.1.2 = g.2 + K * xs.length ∧
    r.2.length = xs.length ∧ (∀ w ∈ r.2, (encNat w).length ≤ W) ∧
    (∀ gt ∈ r.1.1, (Boolean.encGate gt).length ≤ G) := by
  suffices h : ∀ (l : List α), (∀ a ∈ l, a ∈ xs) → ∀ (g₀ : Gates) (acc : List ℕ),
      (∀ gt ∈ g₀.1, (Boolean.encGate gt).length ≤ G) →
      (∀ w ∈ acc, (encNat w).length ≤ W) →
      g₀.2 + K * l.length ≤ g.2 + K * xs.length →
      let res := l.foldl (fun q a => let r := f q.1 a; (r.1, r.2 :: q.2)) (g₀, acc)
      res.1.1.length = g₀.1.length + K * l.length ∧ res.1.2 = g₀.2 + K * l.length ∧
      res.2.length = acc.length + l.length ∧ (∀ w ∈ res.2, (encNat w).length ≤ W) ∧
      (∀ gt ∈ res.1.1, (Boolean.encGate gt).length ≤ G) by
    have hr := h xs (fun _ ha => ha) g [] hg1 (by simp) le_rfl
    refine ⟨hr.1, hr.2.1, by simp [emitMap_eq, hr.2.2.1], fun w hw => ?_, hr.2.2.2.2⟩
    exact hr.2.2.2.1 w (List.mem_reverse.mp hw)
  intro l; induction l with
  | nil => intro _ g₀ acc hg₀ hacc _; exact ⟨by simp, by simp, by simp, hacc, hg₀⟩
  | cons a tl ih =>
    intro hsub g₀ acc hg₀ hacc hle
    have hge : g₀.2 + K ≤ g.2 + K * xs.length := by
      simp only [List.length_cons, Nat.mul_succ] at hle; omega
    have hs := hf g₀ a (hsub a List.mem_cons_self) hg₀
      ((length_encNat_le_of_le (by omega)).trans hW) hge
    have hih := ih (fun b hb => hsub b (List.mem_cons_of_mem a hb)) (f g₀ a).1
      ((f g₀ a).2 :: acc) hs.2.2.2 (fun w hw => by
        simp only [List.mem_cons] at hw
        rcases hw with rfl | hw
        · exact hs.2.2.1
        · exact hacc w hw)
      (by rw [hs.2.1]; simp only [List.length_cons, Nat.mul_succ] at hle; omega)
    refine ⟨?_, ?_, ?_, hih.2.2.2.1, hih.2.2.2.2⟩
    · simp only [List.foldl_cons, hih.1, hs.1, List.length_cons, Nat.mul_succ]; omega
    · simp only [List.foldl_cons, hih.2.1, hs.2.1, List.length_cons, Nat.mul_succ]; omega
    · simp only [List.foldl_cons, hih.2.2.1, List.length_cons]; omega

theorem gMux3_bounds {g : Gates} {s0 a0 s1 a1 s2 a2 G W : ℕ}
    (hs0 : (encNat s0).length ≤ W) (ha0 : (encNat a0).length ≤ W)
    (hs1 : (encNat s1).length ≤ W) (ha1 : (encNat a1).length ≤ W)
    (hs2 : (encNat s2).length ≤ W) (ha2 : (encNat a2).length ≤ W)
    (hG : 4 * W + 11 ≤ G) (hg1 : ∀ gt ∈ g.1, (Boolean.encGate gt).length ≤ G)
    (hW : (encNat (g.2 + 5)).length ≤ W) :
    let r := Gates.gMux3 g s0 a0 s1 a1 s2 a2
    r.1.1.length = g.1.length + 5 ∧ r.1.2 = g.2 + 5 ∧ (encNat r.2).length ≤ W ∧
    (∀ gt ∈ r.1.1, (Boolean.encGate gt).length ≤ G) := by
  have hle : ∀ (k : ℕ), k ≤ 5 → (encNat (g.2 + k)).length ≤ W := fun k hk =>
    (length_encNat_le_of_le (by omega)).trans hW
  simp only [Gates.gMux3_eq, Gates.gOr3_eq, Gates.gAnd_eq, Gates.gOr_eq]
  set r1 := g.emit .and [s0, a0]
  have b1 := emit_wire_bounds (g := g) (op := .and) (args := [s0, a0]) (by simp)
    (by intro w hw; simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl <;> assumption) hG hg1 (by simpa using hle 0 (by omega))
  set r2 := r1.1.emit .and [s1, a1]
  have b2 := emit_wire_bounds (g := r1.1) (op := .and) (args := [s1, a1]) (by simp)
    (by intro w hw; simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl <;> assumption) hG b1.2.2.2
    (by rw [b1.2.1]; exact hle 1 (by omega))
  set r3 := r2.1.emit .and [s2, a2]
  have b3 := emit_wire_bounds (g := r2.1) (op := .and) (args := [s2, a2]) (by simp)
    (by intro w hw; simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl <;> assumption) hG b2.2.2.2
    (by rw [b2.2.1, b1.2.1, Nat.add_assoc]; exact hle 2 (by omega))
  set r4 := r3.1.emit .or [r1.2, r2.2]
  have b4 := emit_wire_bounds (g := r3.1) (op := .or) (args := [r1.2, r2.2]) (by simp)
    (by intro w hw; simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl <;> first | exact b1.2.2.1 | exact b2.2.2.1)
    hG b3.2.2.2 (by rw [b3.2.1, b2.2.1, b1.2.1, Nat.add_assoc,
      Nat.add_assoc]; exact hle 3 (by omega))
  have b5 := emit_wire_bounds (g := r4.1) (op := .or) (args := [r4.2, r3.2]) (by simp)
    (by intro w hw; simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl <;> first | exact b4.2.2.1 | exact b3.2.2.1)
    hG b4.2.2.2
    (by rw [b4.2.1, b3.2.1, b2.2.1, b1.2.1, Nat.add_assoc, Nat.add_assoc,
      Nat.add_assoc]; exact hle 4 (by omega))
  exact ⟨by rw [b5.1, b4.1, b3.1, b2.1, b1.1],
    by rw [b5.2.1, b4.2.1, b3.2.1, b2.2.1, b1.2.1], b5.2.2.1, b5.2.2.2⟩

theorem gMux4_bounds {g : Gates} {s0 a0 s1 a1 s2 a2 s3 a3 G W : ℕ}
    (hs0 : (encNat s0).length ≤ W) (ha0 : (encNat a0).length ≤ W)
    (hs1 : (encNat s1).length ≤ W) (ha1 : (encNat a1).length ≤ W)
    (hs2 : (encNat s2).length ≤ W) (ha2 : (encNat a2).length ≤ W)
    (hs3 : (encNat s3).length ≤ W) (ha3 : (encNat a3).length ≤ W)
    (hG : 4 * W + 11 ≤ G) (hg1 : ∀ gt ∈ g.1, (Boolean.encGate gt).length ≤ G)
    (hW : (encNat (g.2 + 7)).length ≤ W) :
    let r := Gates.gMux4 g s0 a0 s1 a1 s2 a2 s3 a3
    r.1.1.length = g.1.length + 7 ∧ r.1.2 = g.2 + 7 ∧ (encNat r.2).length ≤ W ∧
    (∀ gt ∈ r.1.1, (Boolean.encGate gt).length ≤ G) := by
  have hle : ∀ (k : ℕ), k ≤ 7 → (encNat (g.2 + k)).length ≤ W := fun k hk =>
    (length_encNat_le_of_le (by omega)).trans hW
  simp only [Gates.gMux4_eq, Gates.gOr4_eq, Gates.gAnd_eq, Gates.gOr_eq]
  set r1 := g.emit .and [s0, a0]
  have b1 := emit_wire_bounds (g := g) (op := .and) (args := [s0, a0]) (by simp)
    (by intro w hw; simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl <;> assumption) hG hg1 (by simpa using hle 0 (by omega))
  set r2 := r1.1.emit .and [s1, a1]
  have b2 := emit_wire_bounds (g := r1.1) (op := .and) (args := [s1, a1]) (by simp)
    (by intro w hw; simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl <;> assumption) hG b1.2.2.2
    (by rw [b1.2.1]; exact hle 1 (by omega))
  set r3 := r2.1.emit .and [s2, a2]
  have b3 := emit_wire_bounds (g := r2.1) (op := .and) (args := [s2, a2]) (by simp)
    (by intro w hw; simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl <;> assumption) hG b2.2.2.2
    (by rw [b2.2.1, b1.2.1, Nat.add_assoc]; exact hle 2 (by omega))
  set r4 := r3.1.emit .and [s3, a3]
  have b4 := emit_wire_bounds (g := r3.1) (op := .and) (args := [s3, a3]) (by simp)
    (by intro w hw; simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl <;> assumption) hG b3.2.2.2
    (by rw [b3.2.1, b2.2.1, b1.2.1, Nat.add_assoc, Nat.add_assoc]; exact hle 3 (by omega))
  set r5 := r4.1.emit .or [r1.2, r2.2]
  have b5 := emit_wire_bounds (g := r4.1) (op := .or) (args := [r1.2, r2.2]) (by simp)
    (by intro w hw; simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl
        · exact b1.2.2.1
        · exact b2.2.2.1)
    hG b4.2.2.2
    (by rw [b4.2.1, b3.2.1, b2.2.1, b1.2.1, Nat.add_assoc, Nat.add_assoc,
      Nat.add_assoc]; exact hle 4 (by omega))
  set r6 := r5.1.emit .or [r3.2, r4.2]
  have b6 := emit_wire_bounds (g := r5.1) (op := .or) (args := [r3.2, r4.2]) (by simp)
    (by intro w hw; simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl
        · exact b3.2.2.1
        · exact b4.2.2.1)
    hG b5.2.2.2
    (by rw [b5.2.1, b4.2.1, b3.2.1, b2.2.1, b1.2.1, Nat.add_assoc, Nat.add_assoc, Nat.add_assoc,
            Nat.add_assoc]; exact hle 5 (by omega))
  have b7 := emit_wire_bounds (g := r6.1) (op := .or) (args := [r5.2, r6.2]) (by simp)
    (by intro w hw; simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl
        · exact b5.2.2.1
        · exact b6.2.2.1)
    hG b6.2.2.2
    (by rw [b6.2.1, b5.2.1, b4.2.1, b3.2.1, b2.2.1, b1.2.1, Nat.add_assoc, Nat.add_assoc,
            Nat.add_assoc, Nat.add_assoc, Nat.add_assoc]; exact hle 6 (by omega))
  exact ⟨by rw [b7.1, b6.1, b5.1, b4.1, b3.1, b2.1, b1.1],
    by rw [b7.2.1, b6.2.1, b5.2.1, b4.2.1, b3.2.1, b2.2.1, b1.2.1],
    b7.2.2.1, b7.2.2.2⟩

theorem emitCntRebalance_bounds {g : Gates} {fls : ℕ} {lo hi : List ℕ} {G W : ℕ}
    (hfls : (encNat fls).length ≤ W) (hlo : ∀ w ∈ lo, (encNat w).length ≤ W)
    (hhi : ∀ w ∈ hi, (encNat w).length ≤ W) (h0 : (encNat 0).length ≤ W)
    (hG : 4 * W + 11 ≤ G) (hg1 : ∀ gt ∈ g.1, (Boolean.encGate gt).length ≤ G)
    (hW : (encNat (g.2 + 37)).length ≤ W) :
    let r := emitCntRebalance g fls lo hi
    r.1.1.length = g.1.length + 37 ∧ r.1.2 = g.2 + 37 ∧
    (∀ gt ∈ r.1.1, (Boolean.encGate gt).length ≤ G) ∧
    (encNat r.2.1.1).length ≤ W ∧ (encNat r.2.1.2.1).length ≤ W ∧
    (encNat r.2.1.2.2).length ≤ W ∧
    (∀ w ∈ r.2.2.1, (encNat w).length ≤ W) ∧ (∀ w ∈ r.2.2.2, (encNat w).length ≤ W) := by
  have hget : ∀ (l : List ℕ) (k : ℕ), (∀ w ∈ l, (encNat w).length ≤ W) →
      (encNat (l.getD k 0)).length ≤ W := fun l k hl => by
    by_cases hk : k < l.length
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]; exact hl _ (List.getElem_mem hk)
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; exact h0
  have hle : ∀ (k : ℕ), k ≤ 37 → (encNat (g.2 + k)).length ≤ W := fun k hk =>
    (length_encNat_le_of_le (by omega)).trans hW
  dsimp only [emitCntRebalance_eq, Gates.gOr3_eq, Gates.gOr_eq]
  set r1 := g.emit .or [lo.getD 0 0, lo.getD 1 0]
  have b1 := emit_wire_bounds (g := g) (op := .or) (args := [lo.getD 0 0, lo.getD 1 0]) (by simp)
    (by intro w hw; simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl <;> exact hget _ _ hlo) hG hg1 (by simpa using hle 0 (by omega))
  set r2 := r1.1.emit .or [lo.getD 2 0, lo.getD 3 0]
  have b2 := emit_wire_bounds (g := r1.1) (op := .or) (args := [lo.getD 2 0, lo.getD 3 0]) (by simp)
    (by intro w hw; simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl <;> exact hget _ _ hlo) hG b1.2.2.2
          (by rw [b1.2.1]; exact hle 1 (by omega))
  set r3 := r2.1.emit .or [lo.getD 4 0, lo.getD 5 0]
  have b3 := emit_wire_bounds (g := r2.1) (op := .or) (args := [lo.getD 4 0, lo.getD 5 0]) (by simp)
    (by intro w hw; simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl <;> exact hget _ _ hlo) hG b2.2.2.2
    (by rw [b2.2.1, b1.2.1, Nat.add_assoc]; exact hle 2 (by omega))
  set r4 := r3.1.emit .or [lo.getD 0 0, lo.getD 2 0]
  have b4 := emit_wire_bounds (g := r3.1) (op := .or) (args := [lo.getD 0 0, lo.getD 2 0]) (by simp)
    (by intro w hw; simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl <;> exact hget _ _ hlo) hG b3.2.2.2
    (by rw [b3.2.1, b2.2.1, b1.2.1, Nat.add_assoc, Nat.add_assoc]; exact hle 3 (by omega))
  set r5 := r4.1.emit .or [r4.2, lo.getD 4 0]
  have b5 := emit_wire_bounds (g := r4.1) (op := .or) (args := [r4.2, lo.getD 4 0]) (by simp)
    (by intro w hw; simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl <;> first | exact b4.2.2.1 | exact hget _ _ hlo) hG b4.2.2.2
    (by rw [b4.2.1, b3.2.1, b2.2.1, b1.2.1, Nat.add_assoc, Nat.add_assoc,
      Nat.add_assoc]; exact hle 4 (by omega))
  set r6 := r5.1.emit .or [lo.getD 1 0, lo.getD 3 0]
  have b6 := emit_wire_bounds (g := r5.1) (op := .or) (args := [lo.getD 1 0, lo.getD 3 0]) (by simp)
    (by intro w hw; simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl <;> exact hget _ _ hlo) hG b5.2.2.2
    (by rw [b5.2.1, b4.2.1, b3.2.1, b2.2.1, b1.2.1, Nat.add_assoc, Nat.add_assoc, Nat.add_assoc,
            Nat.add_assoc]; exact hle 5 (by omega))
  set r7 := r6.1.emit .or [r6.2, lo.getD 5 0]
  have b7 := emit_wire_bounds (g := r6.1) (op := .or) (args := [r6.2, lo.getD 5 0]) (by simp)
    (by intro w hw; simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl <;> first | exact b6.2.2.1 | exact hget _ _ hlo) hG b6.2.2.2
    (by rw [b6.2.1, b5.2.1, b4.2.1, b3.2.1, b2.2.1, b1.2.1, Nat.add_assoc, Nat.add_assoc,
            Nat.add_assoc, Nat.add_assoc, Nat.add_assoc]; exact hle 6 (by omega))
  have hr7_2 : r7.1.2 = g.2 + 7 := by
    rw [b7.2.1, b6.2.1, b5.2.1, b4.2.1, b3.2.1, b2.2.1, b1.2.1]
  have hr7_1 : r7.1.1.length = g.1.length + 7 := by
    rw [b7.1, b6.1, b5.1, b4.1, b3.1, b2.1, b1.1]
  have hm := emitMap_bounds (g := r7.1) (K := 5) (G := G) (W := W)
    (f := fun g₀ t => Gates.gMux3 g₀ r1.2 t.1 r2.2 t.2.1 r3.2 t.2.2)
    (xs := [(hi.getD 1 0, hi.getD 0 0, fls), (hi.getD 2 0, hi.getD 1 0, hi.getD 0 0),
            (hi.getD 3 0, hi.getD 2 0, hi.getD 1 0), (hi.getD 4 0, hi.getD 3 0, hi.getD 2 0),
            (hi.getD 5 0, hi.getD 4 0, hi.getD 3 0), (fls, hi.getD 5 0, hi.getD 4 0)])
    (fun g₀ t ht hg₀ _ hge' => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact gMux3_bounds b1.2.2.1 (by first | exact hfls | exact hget _ _ hhi)
          b2.2.2.1 (hget _ _ hhi) b3.2.2.1 (by first | exact hfls | exact hget _ _ hhi)
          hG hg₀ ((length_encNat_le_of_le (by
            dsimp only [List.length_cons, List.length_nil] at hge'; omega)).trans hW))
    b7.2.2.2 ((length_encNat_le_of_le (by rw [hr7_2]; simp)).trans hW)
  refine ⟨by rw [hm.1, hr7_1]; simp, by rw [hm.2.1, hr7_2]; simp,
    hm.2.2.2.2, b1.2.2.1, b2.2.2.1, b3.2.2.1, fun w hw => ?_, hm.2.2.2.1⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl <;>
    first | exact hfls | exact b5.2.2.1 | exact b7.2.2.1

theorem emitCellRebalance_bounds {g : Gates} {c0 c1 c4 c5 borrow noop carry : ℕ}
    {L H0 H1 : List ℕ} {G W : ℕ}
    (hc0 : (encNat c0).length ≤ W) (hc1 : (encNat c1).length ≤ W)
    (hc4 : (encNat c4).length ≤ W) (hc5 : (encNat c5).length ≤ W)
    (hbr : (encNat borrow).length ≤ W) (hnp : (encNat noop).length ≤ W)
    (hcr : (encNat carry).length ≤ W)
    (hL : ∀ w ∈ L, (encNat w).length ≤ W) (hH0 : ∀ w ∈ H0, (encNat w).length ≤ W)
    (hH1 : ∀ w ∈ H1, (encNat w).length ≤ W) (h0 : (encNat 0).length ≤ W)
    (hG : 4 * W + 11 ≤ G) (hg1 : ∀ gt ∈ g.1, (Boolean.encGate gt).length ≤ G)
    (hW : (encNat (g.2 + 210)).length ≤ W) :
    let r := emitCellRebalance g c0 c1 c4 c5 borrow noop carry L H0 H1
    r.1.1.length = g.1.length + 210 ∧ r.1.2 = g.2 + 210 ∧
    r.2.1.length = 10 ∧ r.2.2.1.length = 10 ∧ r.2.2.2.length = 10 ∧
    (∀ w ∈ r.2.1, (encNat w).length ≤ W) ∧
    (∀ w ∈ r.2.2.1, (encNat w).length ≤ W) ∧
    (∀ w ∈ r.2.2.2, (encNat w).length ≤ W) ∧
    (∀ gt ∈ r.1.1, (Boolean.encGate gt).length ≤ G) := by
  have hget : ∀ (l : List ℕ) (k : ℕ), (∀ w ∈ l, (encNat w).length ≤ W) →
      (encNat (l.getD k 0)).length ≤ W := fun l k hl => by
    by_cases hk : k < l.length
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]; exact hl _ (List.getElem_mem hk)
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; exact h0
  dsimp only [emitCellRebalance_eq]
  let lSpec : List (ℕ × ℕ × ℕ × ℕ) :=
    [(H0.getD 0 0, L.getD 0 0, L.getD 0 0, L.getD 0 0),
     (H0.getD 1 0, L.getD 1 0, L.getD 1 0, L.getD 1 0),
     (H1.getD 0 0, H0.getD 0 0, L.getD 2 0, L.getD 2 0),
     (H1.getD 1 0, H0.getD 1 0, L.getD 3 0, L.getD 3 0),
     (L.getD 4 0, H1.getD 0 0, L.getD 4 0, L.getD 4 0),
     (L.getD 5 0, H1.getD 1 0, L.getD 5 0, L.getD 5 0),
     (L.getD 6 0, L.getD 6 0, L.getD 6 0, L.getD 6 0),
     (L.getD 7 0, L.getD 7 0, L.getD 7 0, L.getD 7 0),
     (L.getD 8 0, L.getD 8 0, L.getD 8 0, L.getD 8 0),
     (L.getD 9 0, L.getD 9 0, L.getD 9 0, L.getD 9 0)]
  let h0Spec : List (ℕ × ℕ × ℕ × ℕ) :=
    [(H0.getD 2 0, H0.getD 0 0, L.getD 4 0, L.getD 6 0),
     (H0.getD 3 0, H0.getD 1 0, L.getD 5 0, L.getD 7 0),
     (H0.getD 4 0, H0.getD 2 0, H0.getD 0 0, H0.getD 0 0),
     (H0.getD 5 0, H0.getD 3 0, H0.getD 1 0, H0.getD 1 0),
     (H0.getD 6 0, H0.getD 4 0, H0.getD 2 0, H0.getD 2 0),
     (H0.getD 7 0, H0.getD 5 0, H0.getD 3 0, H0.getD 3 0),
     (H0.getD 8 0, H0.getD 6 0, H0.getD 4 0, H0.getD 4 0),
     (H0.getD 9 0, H0.getD 7 0, H0.getD 5 0, H0.getD 5 0),
     (H0.getD 8 0, H0.getD 8 0, H0.getD 6 0, H0.getD 6 0),
     (H0.getD 9 0, H0.getD 9 0, H0.getD 7 0, H0.getD 7 0)]
  let h1Spec : List (ℕ × ℕ × ℕ × ℕ) :=
    [(H1.getD 2 0, H1.getD 0 0, L.getD 6 0, L.getD 8 0),
     (H1.getD 3 0, H1.getD 1 0, L.getD 7 0, L.getD 9 0),
     (H1.getD 4 0, H1.getD 2 0, H1.getD 0 0, H1.getD 0 0),
     (H1.getD 5 0, H1.getD 3 0, H1.getD 1 0, H1.getD 1 0),
     (H1.getD 6 0, H1.getD 4 0, H1.getD 2 0, H1.getD 2 0),
     (H1.getD 7 0, H1.getD 5 0, H1.getD 3 0, H1.getD 3 0),
     (H1.getD 8 0, H1.getD 6 0, H1.getD 4 0, H1.getD 4 0),
     (H1.getD 9 0, H1.getD 7 0, H1.getD 5 0, H1.getD 5 0),
     (H1.getD 8 0, H1.getD 8 0, H1.getD 6 0, H1.getD 6 0),
     (H1.getD 9 0, H1.getD 9 0, H1.getD 7 0, H1.getD 7 0)]
  have hm1 := emitMap_bounds (g := g) (K := 7) (G := G) (W := W)
    (f := fun g₀ t => Gates.gMux4 g₀ c0 t.1 c1 t.2.1 noop t.2.2.1 carry t.2.2.2)
    (xs := lSpec)
    (fun g₀ t ht hg₀ _ hge => by
      have htb : (encNat t.1).length ≤ W ∧ (encNat t.2.1).length ≤ W ∧
          (encNat t.2.2.1).length ≤ W ∧ (encNat t.2.2.2).length ≤ W := by
        simp only [lSpec, List.mem_cons, List.not_mem_nil, or_false] at ht
        rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          exact ⟨by first | exact hget _ _ hL | exact hget _ _ hH0 | exact hget _ _ hH1,
                 by first | exact hget _ _ hL | exact hget _ _ hH0 | exact hget _ _ hH1,
                 hget _ _ hL, hget _ _ hL⟩
      exact gMux4_bounds hc0 htb.1 hc1 htb.2.1 hnp htb.2.2.1 hcr htb.2.2.2 hG hg₀
        ((length_encNat_le_of_le (by
          dsimp only [lSpec, List.length_cons, List.length_nil] at hge; omega)).trans hW))
    hg1 ((length_encNat_le_of_le (by simp [lSpec])).trans hW)
  set r1 := emitMap g (fun g₀ t => Gates.gMux4 g₀ c0 t.1 c1 t.2.1 noop t.2.2.1 carry t.2.2.2) lSpec
  have hm2 := emitMap_bounds (g := r1.1) (K := 7) (G := G) (W := W)
    (f := fun g₀ t => Gates.gMux4 g₀ borrow t.1 noop t.2.1 c4 t.2.2.1 c5 t.2.2.2)
    (xs := h0Spec)
    (fun g₀ t ht hg₀ _ hge => by
      have htb : (encNat t.1).length ≤ W ∧ (encNat t.2.1).length ≤ W ∧
          (encNat t.2.2.1).length ≤ W ∧ (encNat t.2.2.2).length ≤ W := by
        simp only [h0Spec, List.mem_cons, List.not_mem_nil, or_false] at ht
        rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          exact ⟨hget _ _ hH0, hget _ _ hH0,
                 by first | exact hget _ _ hL | exact hget _ _ hH0,
                 by first | exact hget _ _ hL | exact hget _ _ hH0⟩
      exact gMux4_bounds hbr htb.1 hnp htb.2.1 hc4 htb.2.2.1 hc5 htb.2.2.2 hG hg₀
        ((length_encNat_le_of_le (by
          rw [hm1.2.1] at hge; dsimp only [lSpec, h0Spec, List.length_cons,
            List.length_nil] at hge; omega)).trans hW))
    hm1.2.2.2.2 ((length_encNat_le_of_le (by rw [hm1.2.1]; simp [lSpec, h0Spec])).trans hW)
  set r2 :=
    emitMap r1.1 (fun g₀ t => Gates.gMux4 g₀ borrow t.1 noop t.2.1 c4 t.2.2.1 c5 t.2.2.2) h0Spec
  have hm3 := emitMap_bounds (g := r2.1) (K := 7) (G := G) (W := W)
    (f := fun g₀ t => Gates.gMux4 g₀ borrow t.1 noop t.2.1 c4 t.2.2.1 c5 t.2.2.2)
    (xs := h1Spec)
    (fun g₀ t ht hg₀ _ hge => by
      have htb : (encNat t.1).length ≤ W ∧ (encNat t.2.1).length ≤ W ∧
          (encNat t.2.2.1).length ≤ W ∧ (encNat t.2.2.2).length ≤ W := by
        simp only [h1Spec, List.mem_cons, List.not_mem_nil, or_false] at ht
        rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          exact ⟨hget _ _ hH1, hget _ _ hH1,
                 by first | exact hget _ _ hL | exact hget _ _ hH1,
                 by first | exact hget _ _ hL | exact hget _ _ hH1⟩
      exact gMux4_bounds hbr htb.1 hnp htb.2.1 hc4 htb.2.2.1 hc5 htb.2.2.2 hG hg₀
        ((length_encNat_le_of_le (by
          rw [hm2.2.1, hm1.2.1] at hge; dsimp only [lSpec, h0Spec, h1Spec, List.length_cons,
            List.length_nil] at hge; omega)).trans hW))
    hm2.2.2.2.2 ((length_encNat_le_of_le (by rw [hm2.2.1, hm1.2.1]; simp [lSpec, h0Spec,
      h1Spec])).trans hW)
  refine ⟨?_, ?_, hm1.2.2.1, hm2.2.2.1, hm3.2.2.1, hm1.2.2.2.1, hm2.2.2.2.1, hm3.2.2.2.1,
    hm3.2.2.2.2⟩
  · rw [hm3.1, hm2.1, hm1.1]; simp [lSpec, h0Spec, h1Spec]
  · rw [hm3.2.1, hm2.2.1, hm1.2.1]; simp [lSpec, h0Spec, h1Spec]

theorem emitRebalanceLevel_row_lengths (g : Gates) (fls : ℕ) (low hi : LevelW) :
    let r := emitRebalanceLevel g fls low hi
    r.2.1.1.length = 6 ∧ r.2.2.1.length = 6 ∧
    r.2.1.2.length = low.2.length ∧ r.2.2.2.length = 2 * low.2.length ∧
    r.1.1.length = g.1.length + 37 + 210 * low.2.length ∧
    r.1.2 = g.2 + 37 + 210 * low.2.length := by
  dsimp only [emitRebalanceLevel_eq]
  have hcnt_len : (emitCntRebalance g fls low.1 hi.1).1.1.length = g.1.length + 37 ∧
      (emitCntRebalance g fls low.1 hi.1).1.2 = g.2 + 37 ∧
      (emitCntRebalance g fls low.1 hi.1).2.2.1.length = 6 ∧
      (emitCntRebalance g fls low.1 hi.1).2.2.2.length = 6 := by
    dsimp only [emitCntRebalance_eq, emitMap_eq, Gates.gOr3_eq, Gates.gMux3_eq, Gates.gAnd_eq,
      Gates.gOr_eq,
      Gates.emit_eq, List.foldl_cons, List.foldl_nil]
    refine ⟨by simp, by omega, by simp, by simp⟩
  have hfold : ∀ (l : List ℕ) (gc : Gates) (rL rH0 rH1 : List (List ℕ)),
      let res := l.foldl (fun (acc : Gates × (List (List ℕ) × List (List ℕ) × List (List ℕ))) j =>
        let r := emitCellRebalance acc.1 (low.1.getD 0 0) (low.1.getD 1 0) (low.1.getD 4 0)
          (low.1.getD 5 0) (emitCntRebalance g fls low.1 hi.1).2.1.1
          (emitCntRebalance g fls low.1 hi.1).2.1.2.1 (emitCntRebalance g fls low.1 hi.1).2.1.2.2
          (low.2.getD j []) (hi.2.getD j []) (hi.2.getD (low.2.length + j) [])
        (r.1, (r.2.1 :: acc.2.1, r.2.2.1 :: acc.2.2.1, r.2.2.2 :: acc.2.2.2))) (gc, (rL, rH0, rH1))
      res.1.1.length = gc.1.length + 210 * l.length ∧ res.1.2 = gc.2 + 210 * l.length ∧
      res.2.1.length = rL.length + l.length ∧ res.2.2.1.length = rH0.length + l.length ∧
      res.2.2.2.length = rH1.length + l.length := by
    intro l; induction l with
    | nil => intro gc rL rH0 rH1; simp
    | cons j tl ih =>
      intro gc rL rH0 rH1; simp only [List.foldl_cons]
      have hmap_len : ∀ {α : Type} (ga : Gates) (f : Gates → α → Gates × ℕ) (xs : List α) (K : ℕ)
          (hf : ∀ gb a, (f gb a).1.1.length = gb.1.length + K ∧ (f gb a).1.2 = gb.2 + K),
          (emitMap ga f xs).1.1.length = ga.1.length + K * xs.length ∧
          (emitMap ga f xs).1.2 = ga.2 + K * xs.length := by
        intro α ga f xs K hf
        suffices ∀ (acc : List ℕ),
            let r := xs.foldl (fun q a => let p := f q.1 a; (p.1, p.2 :: q.2)) (ga, acc)
            r.1.1.length = ga.1.length + K * xs.length ∧ r.1.2 = ga.2 + K * xs.length by
          exact this []
        intro acc; induction xs generalizing ga acc with
        | nil => simp
        | cons a tl' ih' =>
          simp only [List.foldl_cons, List.length_cons, Nat.mul_succ]
          have p1 := hf ga a; have p2 := ih' (f ga a).1 ((f ga a).2 :: acc)
          exact ⟨by rw [p2.1, p1.1]; omega, by rw [p2.2, p1.2]; omega⟩
      have hmux4_len : ∀ (ga : Gates) (a0 a1 a2 a3 a4 a5 a6 a7 : ℕ),
          (Gates.gMux4 ga a0 a1 a2 a3 a4 a5 a6 a7).1.1.length = ga.1.length + 7 ∧
          (Gates.gMux4 ga a0 a1 a2 a3 a4 a5 a6 a7).1.2 = ga.2 + 7 := fun _ _ _ _ _ _ _ _ _ => by
        dsimp only [Gates.gMux4_eq, Gates.gOr4_eq, Gates.gAnd_eq, Gates.gOr_eq, Gates.emit_eq]
        exact ⟨rfl,
          by omega⟩
      have hc : ∀ (ga : Gates) (c0 c1 c4 c5 br np cr : ℕ) (L H0 H1 : List ℕ),
          (emitCellRebalance ga c0 c1 c4 c5 br np cr L H0 H1).1.1.length = ga.1.length + 210 ∧
          (emitCellRebalance ga c0 c1 c4 c5 br np cr L H0 H1).1.2 = ga.2 + 210 := by
        intro ga c0 c1 c4 c5 br np cr L H0 H1; dsimp only [emitCellRebalance_eq]
        have p1 := hmap_len ga
          (fun gb (t : ℕ × ℕ × ℕ × ℕ) => Gates.gMux4 gb c0 t.1 c1 t.2.1 np t.2.2.1 cr t.2.2.2)
          [(H0.getD 0 0, L.getD 0 0, L.getD 0 0, L.getD 0 0),
           (H0.getD 1 0, L.getD 1 0, L.getD 1 0, L.getD 1 0),
           (H1.getD 0 0, H0.getD 0 0, L.getD 2 0, L.getD 2 0),
           (H1.getD 1 0, H0.getD 1 0, L.getD 3 0, L.getD 3 0),
           (L.getD 4 0, H1.getD 0 0, L.getD 4 0, L.getD 4 0),
           (L.getD 5 0, H1.getD 1 0, L.getD 5 0, L.getD 5 0),
           (L.getD 6 0, L.getD 6 0, L.getD 6 0, L.getD 6 0),
           (L.getD 7 0, L.getD 7 0, L.getD 7 0, L.getD 7 0),
           (L.getD 8 0, L.getD 8 0, L.getD 8 0, L.getD 8 0),
           (L.getD 9 0, L.getD 9 0, L.getD 9 0,
             L.getD 9 0)] 7 fun gb _ => hmux4_len gb _ _ _ _ _ _ _ _
        set m1 := emitMap ga
          (fun gb (t : ℕ × ℕ × ℕ × ℕ) => Gates.gMux4 gb c0 t.1 c1 t.2.1 np t.2.2.1 cr t.2.2.2)
          [(H0.getD 0 0, L.getD 0 0, L.getD 0 0, L.getD 0 0),
           (H0.getD 1 0, L.getD 1 0, L.getD 1 0, L.getD 1 0),
           (H1.getD 0 0, H0.getD 0 0, L.getD 2 0, L.getD 2 0),
           (H1.getD 1 0, H0.getD 1 0, L.getD 3 0, L.getD 3 0),
           (L.getD 4 0, H1.getD 0 0, L.getD 4 0, L.getD 4 0),
           (L.getD 5 0, H1.getD 1 0, L.getD 5 0, L.getD 5 0),
           (L.getD 6 0, L.getD 6 0, L.getD 6 0, L.getD 6 0),
           (L.getD 7 0, L.getD 7 0, L.getD 7 0, L.getD 7 0),
           (L.getD 8 0, L.getD 8 0, L.getD 8 0, L.getD 8 0),
           (L.getD 9 0, L.getD 9 0, L.getD 9 0, L.getD 9 0)]
        have p2 := hmap_len m1.1
          (fun gb (t : ℕ × ℕ × ℕ × ℕ) => Gates.gMux4 gb br t.1 np t.2.1 c4 t.2.2.1 c5 t.2.2.2)
          [(H0.getD 2 0, H0.getD 0 0, L.getD 4 0, L.getD 6 0),
           (H0.getD 3 0, H0.getD 1 0, L.getD 5 0, L.getD 7 0),
           (H0.getD 4 0, H0.getD 2 0, H0.getD 0 0, H0.getD 0 0),
           (H0.getD 5 0, H0.getD 3 0, H0.getD 1 0, H0.getD 1 0),
           (H0.getD 6 0, H0.getD 4 0, H0.getD 2 0, H0.getD 2 0),
           (H0.getD 7 0, H0.getD 5 0, H0.getD 3 0, H0.getD 3 0),
           (H0.getD 8 0, H0.getD 6 0, H0.getD 4 0, H0.getD 4 0),
           (H0.getD 9 0, H0.getD 7 0, H0.getD 5 0, H0.getD 5 0),
           (H0.getD 8 0, H0.getD 8 0, H0.getD 6 0, H0.getD 6 0),
           (H0.getD 9 0, H0.getD 9 0, H0.getD 7 0,
             H0.getD 7 0)] 7 fun gb _ => hmux4_len gb _ _ _ _ _ _ _ _
        set m2 := emitMap m1.1
          (fun gb (t : ℕ × ℕ × ℕ × ℕ) => Gates.gMux4 gb br t.1 np t.2.1 c4 t.2.2.1 c5 t.2.2.2)
          [(H0.getD 2 0, H0.getD 0 0, L.getD 4 0, L.getD 6 0),
           (H0.getD 3 0, H0.getD 1 0, L.getD 5 0, L.getD 7 0),
           (H0.getD 4 0, H0.getD 2 0, H0.getD 0 0, H0.getD 0 0),
           (H0.getD 5 0, H0.getD 3 0, H0.getD 1 0, H0.getD 1 0),
           (H0.getD 6 0, H0.getD 4 0, H0.getD 2 0, H0.getD 2 0),
           (H0.getD 7 0, H0.getD 5 0, H0.getD 3 0, H0.getD 3 0),
           (H0.getD 8 0, H0.getD 6 0, H0.getD 4 0, H0.getD 4 0),
           (H0.getD 9 0, H0.getD 7 0, H0.getD 5 0, H0.getD 5 0),
           (H0.getD 8 0, H0.getD 8 0, H0.getD 6 0, H0.getD 6 0),
           (H0.getD 9 0, H0.getD 9 0, H0.getD 7 0, H0.getD 7 0)]
        have p3 := hmap_len m2.1
          (fun gb (t : ℕ × ℕ × ℕ × ℕ) => Gates.gMux4 gb br t.1 np t.2.1 c4 t.2.2.1 c5 t.2.2.2)
          [(H1.getD 2 0, H1.getD 0 0, L.getD 6 0, L.getD 8 0),
           (H1.getD 3 0, H1.getD 1 0, L.getD 7 0, L.getD 9 0),
           (H1.getD 4 0, H1.getD 2 0, H1.getD 0 0, H1.getD 0 0),
           (H1.getD 5 0, H1.getD 3 0, H1.getD 1 0, H1.getD 1 0),
           (H1.getD 6 0, H1.getD 4 0, H1.getD 2 0, H1.getD 2 0),
           (H1.getD 7 0, H1.getD 5 0, H1.getD 3 0, H1.getD 3 0),
           (H1.getD 8 0, H1.getD 6 0, H1.getD 4 0, H1.getD 4 0),
           (H1.getD 9 0, H1.getD 7 0, H1.getD 5 0, H1.getD 5 0),
           (H1.getD 8 0, H1.getD 8 0, H1.getD 6 0, H1.getD 6 0),
           (H1.getD 9 0, H1.getD 9 0, H1.getD 7 0,
             H1.getD 7 0)] 7 fun gb _ => hmux4_len gb _ _ _ _ _ _ _ _
        exact ⟨by rw [p3.1, p2.1, p1.1]; simp, by rw [p3.2, p2.2, p1.2]; simp⟩
      set r := emitCellRebalance gc (low.1.getD 0 0) (low.1.getD 1 0) (low.1.getD 4 0)
        (low.1.getD 5 0)
        (emitCntRebalance g fls low.1 hi.1).2.1.1
        (emitCntRebalance g fls low.1 hi.1).2.1.2.1
        (emitCntRebalance g fls low.1 hi.1).2.1.2.2
        (low.2.getD j []) (hi.2.getD j []) (hi.2.getD (low.2.length + j) [])
      have h1 : r.1.1.length = gc.1.length + 210 ∧ r.1.2 = gc.2 + 210 :=
        hc gc (low.1.getD 0 0) (low.1.getD 1 0) (low.1.getD 4 0) (low.1.getD 5 0)
          (emitCntRebalance g fls low.1 hi.1).2.1.1
          (emitCntRebalance g fls low.1 hi.1).2.1.2.1
          (emitCntRebalance g fls low.1 hi.1).2.1.2.2
          (low.2.getD j []) (hi.2.getD j []) (hi.2.getD (low.2.length + j) [])
      have h2 := ih r.1 (r.2.1 :: rL) (r.2.2.1 :: rH0) (r.2.2.2 :: rH1)
      refine ⟨by rw [h2.1, h1.1, List.length_cons, Nat.mul_succ]; omega,
        by rw [h2.2.1, h1.2, List.length_cons, Nat.mul_succ]; omega,
        by rw [h2.2.2.1, List.length_cons, List.length_cons]; omega,
        by rw [h2.2.2.2.1, List.length_cons, List.length_cons]; omega,
        by rw [h2.2.2.2.2, List.length_cons, List.length_cons]; omega⟩
  have hf := hfold (List.range low.2.length) (emitCntRebalance g fls low.1 hi.1).1 [] [] []
  refine ⟨hcnt_len.2.2.1, hcnt_len.2.2.2, ?_, ?_, ?_, ?_⟩
  · rw [List.length_reverse, hf.2.2.1, List.length_nil, Nat.zero_add, List.length_range]
  · rw [List.length_append, List.length_reverse, List.length_reverse,
      hf.2.2.2.1, hf.2.2.2.2, List.length_nil, Nat.zero_add, List.length_range]; omega
  · rw [hf.1, hcnt_len.1, List.length_range]
  · rw [hf.2.1, hcnt_len.2.1, List.length_range]

/-! ### `ComputableInPolyTime` for constant-size local gadgets -/

theorem poly_emitShiftLevel0 :
    ComputableInPolyTime
      (fun p : (Gates × ℕ) × ((ℕ × ℕ × ℕ) × (ℕ × ℕ) × LevelW) =>
        emitShiftLevel0 p.1.1 p.1.2 p.2.1.1 p.2.1.2.1 p.2.1.2.2
          p.2.2.1.1 p.2.2.1.2 p.2.2.2)
      (encPair (encPair encGates encNat)
        (encPair (encPair encNat (encPair encNat encNat))
          (encPair (encPair encNat encNat) encLevelW)))
      (encPair encGates encLevelW) := by
  set P := (Gates × ℕ) × ((ℕ × ℕ × ℕ) × (ℕ × ℕ) × LevelW)
  set encP : P ↪ List Bool :=
    encPair (encPair encGates encNat)
      (encPair (encPair encNat (encPair encNat encNat)) (encPair (encPair encNat encNat) encLevelW))
  have hg : ComputableInPolyTime (fun p : P => p.1.1) encP encGates :=
    poly_fst (ComputableInPolyTime.fst _ _)
  simp only [emitShiftLevel0_eq]
  have hfls : ComputableInPolyTime (fun p : P => p.1.2) encP encNat :=
    poly_snd (ComputableInPolyTime.fst _ _)
  have hmP : ComputableInPolyTime (fun p : P => p.2.1.1) encP encNat :=
    poly_fst (poly_fst (ComputableInPolyTime.snd _ _))
  have hmZ : ComputableInPolyTime (fun p : P => p.2.1.2.1) encP encNat :=
    poly_fst (poly_snd (poly_fst (ComputableInPolyTime.snd _ _)))
  have hmS : ComputableInPolyTime (fun p : P => p.2.1.2.2) encP encNat :=
    poly_snd (poly_snd (poly_fst (ComputableInPolyTime.snd _ _)))
  have hw0 : ComputableInPolyTime (fun p : P => p.2.2.1.1) encP encNat :=
    poly_fst (poly_fst (poly_snd (ComputableInPolyTime.snd _ _)))
  have hw1 : ComputableInPolyTime (fun p : P => p.2.2.1.2) encP encNat :=
    poly_snd (poly_fst (poly_snd (ComputableInPolyTime.snd _ _)))
  have hlv : ComputableInPolyTime (fun p : P => p.2.2.2) encP encLevelW :=
    poly_snd (poly_snd (ComputableInPolyTime.snd _ _))
  have hc : ∀ k, ComputableInPolyTime (fun p : P => p.2.2.2.1.getD k 0) encP encNat :=
    fun k => poly_getD_const (poly_fst hlv) k 0
  have hr : ∀ k, ComputableInPolyTime (fun p : P => (p.2.2.2.2.getD 0 []).getD k 0) encP encNat :=
    fun k => poly_getD_const (poly_getD_const (poly_snd hlv) 0 []) k 0
  let cntFns : List (P → ℕ × ℕ × ℕ) :=
    [fun p => (p.2.2.2.1.getD 1 0, p.2.2.2.1.getD 0 0, p.1.2),
     fun p => (p.2.2.2.1.getD 2 0, p.2.2.2.1.getD 1 0, p.2.2.2.1.getD 0 0),
     fun p => (p.2.2.2.1.getD 3 0, p.2.2.2.1.getD 2 0, p.2.2.2.1.getD 1 0),
     fun p => (p.2.2.2.1.getD 4 0, p.2.2.2.1.getD 3 0, p.2.2.2.1.getD 2 0),
     fun p => (p.2.2.2.1.getD 5 0, p.2.2.2.1.getD 4 0, p.2.2.2.1.getD 3 0),
     fun p => (p.1.2, p.2.2.2.1.getD 5 0, p.2.2.2.1.getD 4 0)]
  let rowFns : List (P → ℕ × ℕ × ℕ) :=
    [fun p => ((p.2.2.2.2.getD 0 []).getD 2 0, (p.2.2.2.2.getD 0 []).getD 0 0, p.2.2.1.1),
     fun p => ((p.2.2.2.2.getD 0 []).getD 3 0, (p.2.2.2.2.getD 0 []).getD 1 0, p.2.2.1.2),
     fun p => ((p.2.2.2.2.getD 0 []).getD 4 0, (p.2.2.2.2.getD 0 []).getD 2 0,
       (p.2.2.2.2.getD 0 []).getD 0 0),
     fun p => ((p.2.2.2.2.getD 0 []).getD 5 0, (p.2.2.2.2.getD 0 []).getD 3 0,
       (p.2.2.2.2.getD 0 []).getD 1 0),
     fun p => ((p.2.2.2.2.getD 0 []).getD 6 0, (p.2.2.2.2.getD 0 []).getD 4 0,
       (p.2.2.2.2.getD 0 []).getD 2 0),
     fun p => ((p.2.2.2.2.getD 0 []).getD 7 0, (p.2.2.2.2.getD 0 []).getD 5 0,
       (p.2.2.2.2.getD 0 []).getD 3 0),
     fun p => ((p.2.2.2.2.getD 0 []).getD 8 0, (p.2.2.2.2.getD 0 []).getD 6 0,
       (p.2.2.2.2.getD 0 []).getD 4 0),
     fun p => ((p.2.2.2.2.getD 0 []).getD 9 0, (p.2.2.2.2.getD 0 []).getD 7 0,
       (p.2.2.2.2.getD 0 []).getD 5 0),
     fun p => ((p.2.2.2.2.getD 0 []).getD 8 0, (p.2.2.2.2.getD 0 []).getD 8 0,
       (p.2.2.2.2.getD 0 []).getD 6 0),
     fun p => ((p.2.2.2.2.getD 0 []).getD 9 0, (p.2.2.2.2.getD 0 []).getD 9 0,
       (p.2.2.2.2.getD 0 []).getD 7 0)]
  have hsnd := ComputableInPolyTime.snd encP encGates
  have h1 := poly_emitMap_mapConst cntFns (fun p => p.1.1)
    (fun p g₀ t => Gates.gMux3 g₀ p.2.1.1 t.1 p.2.1.2.1 t.2.1 p.2.1.2.2 t.2.2) hg (by
      intro f hf; simp only [cntFns, List.mem_cons, List.not_mem_nil, or_false] at hf
      rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
      · exact poly_gMux3' hsnd (poly_comp_fst hmP) (poly_comp_fst (hc 1)) (poly_comp_fst hmZ)
          (poly_comp_fst (hc 0)) (poly_comp_fst hmS) (poly_comp_fst hfls)
      · exact poly_gMux3' hsnd (poly_comp_fst hmP) (poly_comp_fst (hc 2)) (poly_comp_fst hmZ)
          (poly_comp_fst (hc 1)) (poly_comp_fst hmS) (poly_comp_fst (hc 0))
      · exact poly_gMux3' hsnd (poly_comp_fst hmP) (poly_comp_fst (hc 3)) (poly_comp_fst hmZ)
          (poly_comp_fst (hc 2)) (poly_comp_fst hmS) (poly_comp_fst (hc 1))
      · exact poly_gMux3' hsnd (poly_comp_fst hmP) (poly_comp_fst (hc 4)) (poly_comp_fst hmZ)
          (poly_comp_fst (hc 3)) (poly_comp_fst hmS) (poly_comp_fst (hc 2))
      · exact poly_gMux3' hsnd (poly_comp_fst hmP) (poly_comp_fst (hc 5)) (poly_comp_fst hmZ)
          (poly_comp_fst (hc 4)) (poly_comp_fst hmS) (poly_comp_fst (hc 3))
      · exact poly_gMux3' hsnd (poly_comp_fst hmP) (poly_comp_fst hfls) (poly_comp_fst hmZ)
          (poly_comp_fst (hc 5)) (poly_comp_fst hmS) (poly_comp_fst (hc 4)))
  have h2 := poly_emitMap_mapConst rowFns _
    (fun p g₀ t => Gates.gMux3 g₀ p.2.1.1 t.1 p.2.1.2.1 t.2.1 p.2.1.2.2 t.2.2)
    (poly_fst h1) (by
      intro f hf; simp only [rowFns, List.mem_cons, List.not_mem_nil, or_false] at hf
      rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact poly_gMux3' hsnd (poly_comp_fst hmP) (poly_comp_fst (hr 2)) (poly_comp_fst hmZ)
          (poly_comp_fst (hr 0)) (poly_comp_fst hmS) (poly_comp_fst hw0)
      · exact poly_gMux3' hsnd (poly_comp_fst hmP) (poly_comp_fst (hr 3)) (poly_comp_fst hmZ)
          (poly_comp_fst (hr 1)) (poly_comp_fst hmS) (poly_comp_fst hw1)
      · exact poly_gMux3' hsnd (poly_comp_fst hmP) (poly_comp_fst (hr 4)) (poly_comp_fst hmZ)
          (poly_comp_fst (hr 2)) (poly_comp_fst hmS) (poly_comp_fst (hr 0))
      · exact poly_gMux3' hsnd (poly_comp_fst hmP) (poly_comp_fst (hr 5)) (poly_comp_fst hmZ)
          (poly_comp_fst (hr 3)) (poly_comp_fst hmS) (poly_comp_fst (hr 1))
      · exact poly_gMux3' hsnd (poly_comp_fst hmP) (poly_comp_fst (hr 6)) (poly_comp_fst hmZ)
          (poly_comp_fst (hr 4)) (poly_comp_fst hmS) (poly_comp_fst (hr 2))
      · exact poly_gMux3' hsnd (poly_comp_fst hmP) (poly_comp_fst (hr 7)) (poly_comp_fst hmZ)
          (poly_comp_fst (hr 5)) (poly_comp_fst hmS) (poly_comp_fst (hr 3))
      · exact poly_gMux3' hsnd (poly_comp_fst hmP) (poly_comp_fst (hr 8)) (poly_comp_fst hmZ)
          (poly_comp_fst (hr 6)) (poly_comp_fst hmS) (poly_comp_fst (hr 4))
      · exact poly_gMux3' hsnd (poly_comp_fst hmP) (poly_comp_fst (hr 9)) (poly_comp_fst hmZ)
          (poly_comp_fst (hr 7)) (poly_comp_fst hmS) (poly_comp_fst (hr 5))
      · exact poly_gMux3' hsnd (poly_comp_fst hmP) (poly_comp_fst (hr 8)) (poly_comp_fst hmZ)
          (poly_comp_fst (hr 8)) (poly_comp_fst hmS) (poly_comp_fst (hr 6))
      · exact poly_gMux3' hsnd (poly_comp_fst hmP) (poly_comp_fst (hr 9)) (poly_comp_fst hmZ)
          (poly_comp_fst (hr 9)) (poly_comp_fst hmS) (poly_comp_fst (hr 7)))
  exact ((poly_fst h2).prod ((poly_snd h1).prod
    (poly_cons' (poly_snd h2) (ComputableInPolyTime.const [])))).of_enc_eq fun p => congrArg _ (by
    dsimp only [emitShiftLevel0_eq, cntFns, rowFns, List.map_cons, List.map_nil]; rfl)

theorem poly_emitCntRebalance :
    ComputableInPolyTime
      (fun p : (Gates × ℕ) × (List ℕ × List ℕ) => emitCntRebalance p.1.1 p.1.2 p.2.1 p.2.2)
      (encPair (encPair encGates encNat) (encPair (encList encNat) (encList encNat)))
      (encPair encGates
        (encPair (encPair encNat (encPair encNat encNat))
          (encPair (encList encNat) (encList encNat)))) := by
  set P := (Gates × ℕ) × (List ℕ × List ℕ)
  set encP : P ↪ List Bool :=
    encPair (encPair encGates encNat) (encPair (encList encNat) (encList encNat))
  have hg : ComputableInPolyTime (fun p : P => p.1.1) encP encGates :=
    (ComputableInPolyTime.fst encGates encNat).comp' (ComputableInPolyTime.fst _ _)
  simp only [emitCntRebalance_eq]
  have hfls : ComputableInPolyTime (fun p : P => p.1.2) encP encNat :=
    (ComputableInPolyTime.snd encGates encNat).comp' (ComputableInPolyTime.fst _ _)
  have hlo : ComputableInPolyTime (fun p : P => p.2.1) encP (encList encNat) :=
    (ComputableInPolyTime.fst (encList encNat)
      (encList encNat)).comp' (ComputableInPolyTime.snd _ _)
  have hhi : ComputableInPolyTime (fun p : P => p.2.2) encP (encList encNat) :=
    (ComputableInPolyTime.snd (encList encNat)
      (encList encNat)).comp' (ComputableInPolyTime.snd _ _)
  have hc : ∀ k, ComputableInPolyTime (fun p : P => p.2.1.getD k 0) encP encNat :=
    fun k => poly_getD_const hlo k 0
  have hh : ∀ k, ComputableInPolyTime (fun p : P => p.2.2.getD k 0) encP encNat :=
    fun k => poly_getD_const hhi k 0
  have r1 := poly_gOr' hg (hc 0) (hc 1)
  have hborrow := (ComputableInPolyTime.snd encGates encNat).comp' r1
  have r2 := poly_gOr' ((ComputableInPolyTime.fst encGates encNat).comp' r1) (hc 2) (hc 3)
  have hnoop := (ComputableInPolyTime.snd encGates encNat).comp' r2
  have r3 := poly_gOr' ((ComputableInPolyTime.fst encGates encNat).comp' r2) (hc 4) (hc 5)
  have hcarry := (ComputableInPolyTime.snd encGates encNat).comp' r3
  have r4 := poly_gOr3' ((ComputableInPolyTime.fst encGates encNat).comp' r3) (hc 0) (hc 2) (hc 4)
  have hlc2 := (ComputableInPolyTime.snd encGates encNat).comp' r4
  have r5 := poly_gOr3' ((ComputableInPolyTime.fst encGates encNat).comp' r4) (hc 1) (hc 3) (hc 5)
  have hlc3 := (ComputableInPolyTime.snd encGates encNat).comp' r5
  have hg5 := (ComputableInPolyTime.fst encGates encNat).comp' r5
  let hiFns : List (P → ℕ × ℕ × ℕ) :=
    [fun p => (p.2.2.getD 1 0, p.2.2.getD 0 0, p.1.2),
     fun p => (p.2.2.getD 2 0, p.2.2.getD 1 0, p.2.2.getD 0 0),
     fun p => (p.2.2.getD 3 0, p.2.2.getD 2 0, p.2.2.getD 1 0),
     fun p => (p.2.2.getD 4 0, p.2.2.getD 3 0, p.2.2.getD 2 0),
     fun p => (p.2.2.getD 5 0, p.2.2.getD 4 0, p.2.2.getD 3 0),
     fun p => (p.1.2, p.2.2.getD 5 0, p.2.2.getD 4 0)]
  have hfst := ComputableInPolyTime.fst encP encGates
  have hsnd := ComputableInPolyTime.snd encP encGates; have h6 := poly_emitMap_mapConst hiFns
    (fun p =>
      let s1 := Gates.gOr p.1.1 (p.2.1.getD 0 0) (p.2.1.getD 1 0)
      let s2 := Gates.gOr s1.1 (p.2.1.getD 2 0) (p.2.1.getD 3 0)
      let s3 := Gates.gOr s2.1 (p.2.1.getD 4 0) (p.2.1.getD 5 0)
      let s4 := Gates.gOr3 s3.1 (p.2.1.getD 0 0) (p.2.1.getD 2 0) (p.2.1.getD 4 0)
      (Gates.gOr3 s4.1 (p.2.1.getD 1 0) (p.2.1.getD 3 0) (p.2.1.getD 5 0)).1)
    (fun p g₀ t =>
      let s1 := Gates.gOr p.1.1 (p.2.1.getD 0 0) (p.2.1.getD 1 0)
      let s2 := Gates.gOr s1.1 (p.2.1.getD 2 0) (p.2.1.getD 3 0)
      let s3 := Gates.gOr s2.1 (p.2.1.getD 4 0) (p.2.1.getD 5 0)
      Gates.gMux3 g₀ s1.2 t.1 s2.2 t.2.1 s3.2 t.2.2)
    hg5 (by
      intro f hf; simp only [hiFns, List.mem_cons, List.not_mem_nil, or_false] at hf
      rcases hf with rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact poly_gMux3' hsnd (hborrow.comp' hfst)
          (by first | exact hfls.comp' hfst | exact (hh _).comp' hfst)
          (hnoop.comp' hfst) ((hh _).comp' hfst) (hcarry.comp' hfst)
          (by first | exact hfls.comp' hfst | exact (hh _).comp' hfst))
  have hlc := poly_cons' hfls (poly_cons' hfls (poly_cons' hlc2 (poly_cons' hlc3
    (poly_cons' hfls (poly_cons' hfls (ComputableInPolyTime.const []))))))
  exact ((ComputableInPolyTime.fst encGates (encList encNat)).comp' h6).prod
    ((hborrow.prod (hnoop.prod hcarry)).prod
      (hlc.prod ((ComputableInPolyTime.snd encGates (encList encNat)).comp' h6)))

theorem poly_emitCellRebalance :
    ComputableInPolyTime
      (fun p : (Gates × ((ℕ × ℕ) × (ℕ × ℕ)) × (ℕ × ℕ × ℕ)) × (List ℕ × List ℕ × List ℕ) =>
        emitCellRebalance p.1.1 p.1.2.1.1.1 p.1.2.1.1.2 p.1.2.1.2.1 p.1.2.1.2.2
          p.1.2.2.1 p.1.2.2.2.1 p.1.2.2.2.2 p.2.1 p.2.2.1 p.2.2.2)
      (encPair
        (encPair encGates
          (encPair (encPair (encPair encNat encNat) (encPair encNat encNat))
            (encPair encNat (encPair encNat encNat))))
        (encPair (encList encNat) (encPair (encList encNat) (encList encNat))))
      (encPair encGates (encPair (encList encNat) (encPair (encList encNat) (encList encNat))))
        := by
  set P := (Gates × ((ℕ × ℕ) × (ℕ × ℕ)) × (ℕ × ℕ × ℕ)) × (List ℕ × List ℕ × List ℕ)
  set encP : P ↪ List Bool :=
    encPair
      (encPair encGates
        (encPair (encPair (encPair encNat encNat) (encPair encNat encNat))
          (encPair encNat (encPair encNat encNat))))
      (encPair (encList encNat) (encPair (encList encNat) (encList encNat)))
  have hg : ComputableInPolyTime (fun p : P => p.1.1) encP encGates :=
    poly_fst (ComputableInPolyTime.fst _ _)
  have hsel : ComputableInPolyTime (fun p : P => p.1.2) encP
      (encPair (encPair (encPair encNat encNat) (encPair encNat encNat))
        (encPair encNat (encPair encNat encNat))) :=
    poly_snd (ComputableInPolyTime.fst _ _)
  have hc0 : ComputableInPolyTime (fun p : P => p.1.2.1.1.1) encP encNat :=
    poly_fst (poly_fst (poly_fst hsel))
  have hc1 : ComputableInPolyTime (fun p : P => p.1.2.1.1.2) encP encNat :=
    poly_snd (poly_fst (poly_fst hsel))
  have hc4 : ComputableInPolyTime (fun p : P => p.1.2.1.2.1) encP encNat :=
    poly_fst (poly_snd (poly_fst hsel))
  have hc5 : ComputableInPolyTime (fun p : P => p.1.2.1.2.2) encP encNat :=
    poly_snd (poly_snd (poly_fst hsel))
  have hbr : ComputableInPolyTime (fun p : P => p.1.2.2.1) encP encNat :=
    poly_fst (poly_snd hsel)
  have hnp : ComputableInPolyTime (fun p : P => p.1.2.2.2.1) encP encNat :=
    poly_fst (poly_snd (poly_snd hsel))
  have hcr : ComputableInPolyTime (fun p : P => p.1.2.2.2.2) encP encNat :=
    poly_snd (poly_snd (poly_snd hsel))
  have hL : ComputableInPolyTime (fun p : P => p.2.1) encP (encList encNat) :=
    poly_fst (ComputableInPolyTime.snd _ _)
  have hH0 : ComputableInPolyTime (fun p : P => p.2.2.1) encP (encList encNat) :=
    poly_fst (poly_snd (ComputableInPolyTime.snd _ _))
  have hH1 : ComputableInPolyTime (fun p : P => p.2.2.2) encP (encList encNat) :=
    poly_snd (poly_snd (ComputableInPolyTime.snd _ _))
  have hl : ∀ k, ComputableInPolyTime (fun p : P => p.2.1.getD k 0) encP encNat :=
    fun k => poly_getD_const hL k 0
  have ha : ∀ k, ComputableInPolyTime (fun p : P => p.2.2.1.getD k 0) encP encNat :=
    fun k => poly_getD_const hH0 k 0
  have hb : ∀ k, ComputableInPolyTime (fun p : P => p.2.2.2.getD k 0) encP encNat :=
    fun k => poly_getD_const hH1 k 0
  let lFns : List (P → ℕ × ℕ × ℕ × ℕ) :=
    [fun p => (p.2.2.1.getD 0 0, p.2.1.getD 0 0, p.2.1.getD 0 0, p.2.1.getD 0 0),
     fun p => (p.2.2.1.getD 1 0, p.2.1.getD 1 0, p.2.1.getD 1 0, p.2.1.getD 1 0),
     fun p => (p.2.2.2.getD 0 0, p.2.2.1.getD 0 0, p.2.1.getD 2 0, p.2.1.getD 2 0),
     fun p => (p.2.2.2.getD 1 0, p.2.2.1.getD 1 0, p.2.1.getD 3 0, p.2.1.getD 3 0),
     fun p => (p.2.1.getD 4 0, p.2.2.2.getD 0 0, p.2.1.getD 4 0, p.2.1.getD 4 0),
     fun p => (p.2.1.getD 5 0, p.2.2.2.getD 1 0, p.2.1.getD 5 0, p.2.1.getD 5 0),
     fun p => (p.2.1.getD 6 0, p.2.1.getD 6 0, p.2.1.getD 6 0, p.2.1.getD 6 0),
     fun p => (p.2.1.getD 7 0, p.2.1.getD 7 0, p.2.1.getD 7 0, p.2.1.getD 7 0),
     fun p => (p.2.1.getD 8 0, p.2.1.getD 8 0, p.2.1.getD 8 0, p.2.1.getD 8 0),
     fun p => (p.2.1.getD 9 0, p.2.1.getD 9 0, p.2.1.getD 9 0, p.2.1.getD 9 0)]
  let h0Fns : List (P → ℕ × ℕ × ℕ × ℕ) :=
    [fun p => (p.2.2.1.getD 2 0, p.2.2.1.getD 0 0, p.2.1.getD 4 0, p.2.1.getD 6 0),
     fun p => (p.2.2.1.getD 3 0, p.2.2.1.getD 1 0, p.2.1.getD 5 0, p.2.1.getD 7 0),
     fun p => (p.2.2.1.getD 4 0, p.2.2.1.getD 2 0, p.2.2.1.getD 0 0, p.2.2.1.getD 0 0),
     fun p => (p.2.2.1.getD 5 0, p.2.2.1.getD 3 0, p.2.2.1.getD 1 0, p.2.2.1.getD 1 0),
     fun p => (p.2.2.1.getD 6 0, p.2.2.1.getD 4 0, p.2.2.1.getD 2 0, p.2.2.1.getD 2 0),
     fun p => (p.2.2.1.getD 7 0, p.2.2.1.getD 5 0, p.2.2.1.getD 3 0, p.2.2.1.getD 3 0),
     fun p => (p.2.2.1.getD 8 0, p.2.2.1.getD 6 0, p.2.2.1.getD 4 0, p.2.2.1.getD 4 0),
     fun p => (p.2.2.1.getD 9 0, p.2.2.1.getD 7 0, p.2.2.1.getD 5 0, p.2.2.1.getD 5 0),
     fun p => (p.2.2.1.getD 8 0, p.2.2.1.getD 8 0, p.2.2.1.getD 6 0, p.2.2.1.getD 6 0),
     fun p => (p.2.2.1.getD 9 0, p.2.2.1.getD 9 0, p.2.2.1.getD 7 0, p.2.2.1.getD 7 0)]
  let h1Fns : List (P → ℕ × ℕ × ℕ × ℕ) :=
    [fun p => (p.2.2.2.getD 2 0, p.2.2.2.getD 0 0, p.2.1.getD 6 0, p.2.1.getD 8 0),
     fun p => (p.2.2.2.getD 3 0, p.2.2.2.getD 1 0, p.2.1.getD 7 0, p.2.1.getD 9 0),
     fun p => (p.2.2.2.getD 4 0, p.2.2.2.getD 2 0, p.2.2.2.getD 0 0, p.2.2.2.getD 0 0),
     fun p => (p.2.2.2.getD 5 0, p.2.2.2.getD 3 0, p.2.2.2.getD 1 0, p.2.2.2.getD 1 0),
     fun p => (p.2.2.2.getD 6 0, p.2.2.2.getD 4 0, p.2.2.2.getD 2 0, p.2.2.2.getD 2 0),
     fun p => (p.2.2.2.getD 7 0, p.2.2.2.getD 5 0, p.2.2.2.getD 3 0, p.2.2.2.getD 3 0),
     fun p => (p.2.2.2.getD 8 0, p.2.2.2.getD 6 0, p.2.2.2.getD 4 0, p.2.2.2.getD 4 0),
     fun p => (p.2.2.2.getD 9 0, p.2.2.2.getD 7 0, p.2.2.2.getD 5 0, p.2.2.2.getD 5 0),
     fun p => (p.2.2.2.getD 8 0, p.2.2.2.getD 8 0, p.2.2.2.getD 6 0, p.2.2.2.getD 6 0),
     fun p => (p.2.2.2.getD 9 0, p.2.2.2.getD 9 0, p.2.2.2.getD 7 0, p.2.2.2.getD 7 0)]
  have hsnd := ComputableInPolyTime.snd encP encGates
  have m1 := poly_emitMap_mapConst lFns (fun p => p.1.1)
    (fun p g₀ t => Gates.gMux4 g₀ p.1.2.1.1.1 t.1 p.1.2.1.1.2 t.2.1
      p.1.2.2.2.1 t.2.2.1 p.1.2.2.2.2 t.2.2.2) hg (by
      intro f hf; simp only [lFns, List.mem_cons, List.not_mem_nil, or_false] at hf
      rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact poly_gMux4' hsnd (poly_comp_fst hc0) (poly_comp_fst (ha 0)) (poly_comp_fst hc1)
          (poly_comp_fst (hl 0)) (poly_comp_fst hnp) (poly_comp_fst (hl 0)) (poly_comp_fst hcr)
          (poly_comp_fst (hl 0))
      · exact poly_gMux4' hsnd (poly_comp_fst hc0) (poly_comp_fst (ha 1)) (poly_comp_fst hc1)
          (poly_comp_fst (hl 1)) (poly_comp_fst hnp) (poly_comp_fst (hl 1)) (poly_comp_fst hcr)
          (poly_comp_fst (hl 1))
      · exact poly_gMux4' hsnd (poly_comp_fst hc0) (poly_comp_fst (hb 0)) (poly_comp_fst hc1)
          (poly_comp_fst (ha 0)) (poly_comp_fst hnp) (poly_comp_fst (hl 2)) (poly_comp_fst hcr)
          (poly_comp_fst (hl 2))
      · exact poly_gMux4' hsnd (poly_comp_fst hc0) (poly_comp_fst (hb 1)) (poly_comp_fst hc1)
          (poly_comp_fst (ha 1)) (poly_comp_fst hnp) (poly_comp_fst (hl 3)) (poly_comp_fst hcr)
          (poly_comp_fst (hl 3))
      · exact poly_gMux4' hsnd (poly_comp_fst hc0) (poly_comp_fst (hl 4)) (poly_comp_fst hc1)
          (poly_comp_fst (hb 0)) (poly_comp_fst hnp) (poly_comp_fst (hl 4)) (poly_comp_fst hcr)
          (poly_comp_fst (hl 4))
      · exact poly_gMux4' hsnd (poly_comp_fst hc0) (poly_comp_fst (hl 5)) (poly_comp_fst hc1)
          (poly_comp_fst (hb 1)) (poly_comp_fst hnp) (poly_comp_fst (hl 5)) (poly_comp_fst hcr)
          (poly_comp_fst (hl 5))
      · exact poly_gMux4' hsnd (poly_comp_fst hc0) (poly_comp_fst (hl 6)) (poly_comp_fst hc1)
          (poly_comp_fst (hl 6)) (poly_comp_fst hnp) (poly_comp_fst (hl 6)) (poly_comp_fst hcr)
          (poly_comp_fst (hl 6))
      · exact poly_gMux4' hsnd (poly_comp_fst hc0) (poly_comp_fst (hl 7)) (poly_comp_fst hc1)
          (poly_comp_fst (hl 7)) (poly_comp_fst hnp) (poly_comp_fst (hl 7)) (poly_comp_fst hcr)
          (poly_comp_fst (hl 7))
      · exact poly_gMux4' hsnd (poly_comp_fst hc0) (poly_comp_fst (hl 8)) (poly_comp_fst hc1)
          (poly_comp_fst (hl 8)) (poly_comp_fst hnp) (poly_comp_fst (hl 8)) (poly_comp_fst hcr)
          (poly_comp_fst (hl 8))
      · exact poly_gMux4' hsnd (poly_comp_fst hc0) (poly_comp_fst (hl 9)) (poly_comp_fst hc1)
          (poly_comp_fst (hl 9)) (poly_comp_fst hnp) (poly_comp_fst (hl 9)) (poly_comp_fst hcr)
          (poly_comp_fst (hl 9)))
  have m2 := poly_emitMap_mapConst h0Fns _
    (fun p g₀ t => Gates.gMux4 g₀ p.1.2.2.1 t.1 p.1.2.2.2.1 t.2.1
      p.1.2.1.2.1 t.2.2.1 p.1.2.1.2.2 t.2.2.2)
    (poly_fst m1) (by
      intro f hf; simp only [h0Fns, List.mem_cons, List.not_mem_nil, or_false] at hf
      rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact poly_gMux4' hsnd (poly_comp_fst hbr) (poly_comp_fst (ha 2)) (poly_comp_fst hnp)
          (poly_comp_fst (ha 0)) (poly_comp_fst hc4) (poly_comp_fst (hl 4)) (poly_comp_fst hc5)
          (poly_comp_fst (hl 6))
      · exact poly_gMux4' hsnd (poly_comp_fst hbr) (poly_comp_fst (ha 3)) (poly_comp_fst hnp)
          (poly_comp_fst (ha 1)) (poly_comp_fst hc4) (poly_comp_fst (hl 5)) (poly_comp_fst hc5)
          (poly_comp_fst (hl 7))
      · exact poly_gMux4' hsnd (poly_comp_fst hbr) (poly_comp_fst (ha 4)) (poly_comp_fst hnp)
          (poly_comp_fst (ha 2)) (poly_comp_fst hc4) (poly_comp_fst (ha 0)) (poly_comp_fst hc5)
          (poly_comp_fst (ha 0))
      · exact poly_gMux4' hsnd (poly_comp_fst hbr) (poly_comp_fst (ha 5)) (poly_comp_fst hnp)
          (poly_comp_fst (ha 3)) (poly_comp_fst hc4) (poly_comp_fst (ha 1)) (poly_comp_fst hc5)
          (poly_comp_fst (ha 1))
      · exact poly_gMux4' hsnd (poly_comp_fst hbr) (poly_comp_fst (ha 6)) (poly_comp_fst hnp)
          (poly_comp_fst (ha 4)) (poly_comp_fst hc4) (poly_comp_fst (ha 2)) (poly_comp_fst hc5)
          (poly_comp_fst (ha 2))
      · exact poly_gMux4' hsnd (poly_comp_fst hbr) (poly_comp_fst (ha 7)) (poly_comp_fst hnp)
          (poly_comp_fst (ha 5)) (poly_comp_fst hc4) (poly_comp_fst (ha 3)) (poly_comp_fst hc5)
          (poly_comp_fst (ha 3))
      · exact poly_gMux4' hsnd (poly_comp_fst hbr) (poly_comp_fst (ha 8)) (poly_comp_fst hnp)
          (poly_comp_fst (ha 6)) (poly_comp_fst hc4) (poly_comp_fst (ha 4)) (poly_comp_fst hc5)
          (poly_comp_fst (ha 4))
      · exact poly_gMux4' hsnd (poly_comp_fst hbr) (poly_comp_fst (ha 9)) (poly_comp_fst hnp)
          (poly_comp_fst (ha 7)) (poly_comp_fst hc4) (poly_comp_fst (ha 5)) (poly_comp_fst hc5)
          (poly_comp_fst (ha 5))
      · exact poly_gMux4' hsnd (poly_comp_fst hbr) (poly_comp_fst (ha 8)) (poly_comp_fst hnp)
          (poly_comp_fst (ha 8)) (poly_comp_fst hc4) (poly_comp_fst (ha 6)) (poly_comp_fst hc5)
          (poly_comp_fst (ha 6))
      · exact poly_gMux4' hsnd (poly_comp_fst hbr) (poly_comp_fst (ha 9)) (poly_comp_fst hnp)
          (poly_comp_fst (ha 9)) (poly_comp_fst hc4) (poly_comp_fst (ha 7)) (poly_comp_fst hc5)
          (poly_comp_fst (ha 7)))
  have m3 := poly_emitMap_mapConst h1Fns _
    (fun p g₀ t => Gates.gMux4 g₀ p.1.2.2.1 t.1 p.1.2.2.2.1 t.2.1
      p.1.2.1.2.1 t.2.2.1 p.1.2.1.2.2 t.2.2.2)
    (poly_fst m2) (by
      intro f hf; simp only [h1Fns, List.mem_cons, List.not_mem_nil, or_false] at hf
      rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact poly_gMux4' hsnd (poly_comp_fst hbr) (poly_comp_fst (hb 2)) (poly_comp_fst hnp)
          (poly_comp_fst (hb 0)) (poly_comp_fst hc4) (poly_comp_fst (hl 6)) (poly_comp_fst hc5)
          (poly_comp_fst (hl 8))
      · exact poly_gMux4' hsnd (poly_comp_fst hbr) (poly_comp_fst (hb 3)) (poly_comp_fst hnp)
          (poly_comp_fst (hb 1)) (poly_comp_fst hc4) (poly_comp_fst (hl 7)) (poly_comp_fst hc5)
          (poly_comp_fst (hl 9))
      · exact poly_gMux4' hsnd (poly_comp_fst hbr) (poly_comp_fst (hb 4)) (poly_comp_fst hnp)
          (poly_comp_fst (hb 2)) (poly_comp_fst hc4) (poly_comp_fst (hb 0)) (poly_comp_fst hc5)
          (poly_comp_fst (hb 0))
      · exact poly_gMux4' hsnd (poly_comp_fst hbr) (poly_comp_fst (hb 5)) (poly_comp_fst hnp)
          (poly_comp_fst (hb 3)) (poly_comp_fst hc4) (poly_comp_fst (hb 1)) (poly_comp_fst hc5)
          (poly_comp_fst (hb 1))
      · exact poly_gMux4' hsnd (poly_comp_fst hbr) (poly_comp_fst (hb 6)) (poly_comp_fst hnp)
          (poly_comp_fst (hb 4)) (poly_comp_fst hc4) (poly_comp_fst (hb 2)) (poly_comp_fst hc5)
          (poly_comp_fst (hb 2))
      · exact poly_gMux4' hsnd (poly_comp_fst hbr) (poly_comp_fst (hb 7)) (poly_comp_fst hnp)
          (poly_comp_fst (hb 5)) (poly_comp_fst hc4) (poly_comp_fst (hb 3)) (poly_comp_fst hc5)
          (poly_comp_fst (hb 3))
      · exact poly_gMux4' hsnd (poly_comp_fst hbr) (poly_comp_fst (hb 8)) (poly_comp_fst hnp)
          (poly_comp_fst (hb 6)) (poly_comp_fst hc4) (poly_comp_fst (hb 4)) (poly_comp_fst hc5)
          (poly_comp_fst (hb 4))
      · exact poly_gMux4' hsnd (poly_comp_fst hbr) (poly_comp_fst (hb 9)) (poly_comp_fst hnp)
          (poly_comp_fst (hb 7)) (poly_comp_fst hc4) (poly_comp_fst (hb 5)) (poly_comp_fst hc5)
          (poly_comp_fst (hb 5))
      · exact poly_gMux4' hsnd (poly_comp_fst hbr) (poly_comp_fst (hb 8)) (poly_comp_fst hnp)
          (poly_comp_fst (hb 8)) (poly_comp_fst hc4) (poly_comp_fst (hb 6)) (poly_comp_fst hc5)
          (poly_comp_fst (hb 6))
      · exact poly_gMux4' hsnd (poly_comp_fst hbr) (poly_comp_fst (hb 9)) (poly_comp_fst hnp)
          (poly_comp_fst (hb 9)) (poly_comp_fst hc4) (poly_comp_fst (hb 7)) (poly_comp_fst hc5)
          (poly_comp_fst (hb 7)))
  exact ((poly_fst m3).prod ((poly_snd m1).prod ((poly_snd m2).prod
    (poly_snd m3)))).of_enc_eq fun p =>
    congrArg _ (by
      dsimp only [emitCellRebalance_eq, lFns, h0Fns, h1Fns, List.map_cons, List.map_nil]; rfl)

theorem poly_emitOutUpdate :
    ComputableInPolyTime
      (fun p : (Gates × List ℕ) × ((ℕ × ℕ) × (ℕ × ℕ)) =>
        emitOutUpdate p.1.1 p.2.1.1 p.2.1.2 p.2.2.1 p.2.2.2 p.1.2)
      (encPair (encPair encGates (encList encNat))
        (encPair (encPair encNat encNat) (encPair encNat encNat)))
      (encPair encGates (encList encNat)) := by
  set P := (Gates × List ℕ) × ((ℕ × ℕ) × (ℕ × ℕ))
  set encP : P ↪ List Bool :=
    encPair (encPair encGates (encList encNat))
      (encPair (encPair encNat encNat) (encPair encNat encNat))
  have hg : ComputableInPolyTime (fun p : P => p.1.1) encP encGates :=
    poly_fst (ComputableInPolyTime.fst _ _)
  have hout : ComputableInPolyTime (fun p : P => p.1.2) encP (encList encNat) :=
    poly_snd (ComputableInPolyTime.fst _ _)
  have hsH : ComputableInPolyTime (fun p : P => p.2.1.1) encP encNat :=
    poly_fst (poly_fst (ComputableInPolyTime.snd _ _))
  have hoN : ComputableInPolyTime (fun p : P => p.2.1.2) encP encNat :=
    poly_snd (poly_fst (ComputableInPolyTime.snd _ _))
  have hoF : ComputableInPolyTime (fun p : P => p.2.2.1) encP encNat :=
    poly_fst (poly_snd (ComputableInPolyTime.snd _ _))
  have hoT : ComputableInPolyTime (fun p : P => p.2.2.2) encP encNat :=
    poly_snd (poly_snd (ComputableInPolyTime.snd _ _))
  have ho : ∀ k, ComputableInPolyTime (fun p : P => p.1.2.getD k 0) encP encNat :=
    fun k => poly_getD_const hout k 0
  have r1 := poly_gOr' hg hoF hoT; have r2 := poly_gOr3' (poly_fst r1) (ho 1) (ho 2) (ho 3)
  have hsnd := ComputableInPolyTime.snd encP encGates
  let andFns : List (P → ℕ × ℕ) :=
    [fun p => (p.2.1.1, p.1.2.getD 0 0), fun p => (p.2.1.1, p.1.2.getD 1 0),
     fun p => (p.2.1.1, p.1.2.getD 2 0), fun p => (p.2.1.1, p.1.2.getD 3 0),
     fun p => (p.2.1.2, p.1.2.getD 0 0), fun p => (p.2.1.2, p.1.2.getD 1 0),
     fun p => (p.2.1.2, p.1.2.getD 2 0), fun p => (p.2.1.2, p.1.2.getD 3 0),
     fun p => (p.2.2.1, p.1.2.getD 0 0), fun p => (p.2.2.2, p.1.2.getD 0 0),
     fun p => ((Gates.gOr p.1.1 p.2.2.1 p.2.2.2).2,
       (Gates.gOr3 (Gates.gOr p.1.1 p.2.2.1 p.2.2.2).1
         (p.1.2.getD 1 0) (p.1.2.getD 2 0) (p.1.2.getD 3 0)).2)]
  have m1 := poly_emitMap_mapConst andFns _
    (fun _ gc q => Gates.gAnd gc q.1 q.2) (poly_fst r2) (by
      intro f hf; simp only [andFns, List.mem_cons, List.not_mem_nil, or_false] at hf
      rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact poly_gAnd' hsnd (poly_comp_fst hsH) (poly_comp_fst (ho 0))
      · exact poly_gAnd' hsnd (poly_comp_fst hsH) (poly_comp_fst (ho 1))
      · exact poly_gAnd' hsnd (poly_comp_fst hsH) (poly_comp_fst (ho 2))
      · exact poly_gAnd' hsnd (poly_comp_fst hsH) (poly_comp_fst (ho 3))
      · exact poly_gAnd' hsnd (poly_comp_fst hoN) (poly_comp_fst (ho 0))
      · exact poly_gAnd' hsnd (poly_comp_fst hoN) (poly_comp_fst (ho 1))
      · exact poly_gAnd' hsnd (poly_comp_fst hoN) (poly_comp_fst (ho 2))
      · exact poly_gAnd' hsnd (poly_comp_fst hoN) (poly_comp_fst (ho 3))
      · exact poly_gAnd' hsnd (poly_comp_fst hoF) (poly_comp_fst (ho 0))
      · exact poly_gAnd' hsnd (poly_comp_fst hoT) (poly_comp_fst (ho 0))
      · exact poly_gAnd' hsnd (poly_comp_fst (poly_snd r1)) (poly_comp_fst (poly_snd r2)))
  have hps := poly_snd m1
  have ha : ∀ k, ComputableInPolyTime (fun p : P =>
      (emitMap (Gates.gOr3 (Gates.gOr p.1.1 p.2.2.1 p.2.2.2).1
        (p.1.2.getD 1 0) (p.1.2.getD 2 0) (p.1.2.getD 3 0)).1
        (fun gc q => Gates.gAnd gc q.1 q.2) (andFns.map fun f => f p)).2.getD k 0)
      encP encNat := fun k => poly_getD_const hps k 0
  let orFns : List (P → ℕ × ℕ × ℕ) :=
    [fun p => let ps := (emitMap (Gates.gOr3 (Gates.gOr p.1.1 p.2.2.1 p.2.2.2).1
       (p.1.2.getD 1 0) (p.1.2.getD 2 0) (p.1.2.getD 3 0)).1
       (fun gc q => Gates.gAnd gc q.1 q.2) (andFns.map fun f => f p)).2
       (ps.getD 0 0, ps.getD 4 0, ps.getD 4 0),
     fun p => let ps := (emitMap (Gates.gOr3 (Gates.gOr p.1.1 p.2.2.1 p.2.2.2).1
       (p.1.2.getD 1 0) (p.1.2.getD 2 0) (p.1.2.getD 3 0)).1
       (fun gc q => Gates.gAnd gc q.1 q.2) (andFns.map fun f => f p)).2
       (ps.getD 1 0, ps.getD 5 0, ps.getD 8 0),
     fun p => let ps := (emitMap (Gates.gOr3 (Gates.gOr p.1.1 p.2.2.1 p.2.2.2).1
       (p.1.2.getD 1 0) (p.1.2.getD 2 0) (p.1.2.getD 3 0)).1
       (fun gc q => Gates.gAnd gc q.1 q.2) (andFns.map fun f => f p)).2
       (ps.getD 2 0, ps.getD 6 0, ps.getD 9 0),
     fun p => let ps := (emitMap (Gates.gOr3 (Gates.gOr p.1.1 p.2.2.1 p.2.2.2).1
       (p.1.2.getD 1 0) (p.1.2.getD 2 0) (p.1.2.getD 3 0)).1
       (fun gc q => Gates.gAnd gc q.1 q.2) (andFns.map fun f => f p)).2
       (ps.getD 3 0, ps.getD 7 0, ps.getD 10 0)]
  exact (poly_emitMap_mapConst orFns _
    (fun _ gc t => Gates.gOr3 gc t.1 t.2.1 t.2.2) (poly_fst m1) (by
      intro f hf; simp only [orFns, List.mem_cons, List.not_mem_nil, or_false] at hf
      rcases hf with rfl | rfl | rfl | rfl
      · exact poly_gOr3' hsnd (poly_comp_fst (ha 0)) (poly_comp_fst (ha 4)) (poly_comp_fst (ha 4))
      · exact poly_gOr3' hsnd (poly_comp_fst (ha 1)) (poly_comp_fst (ha 5)) (poly_comp_fst (ha 8))
      · exact poly_gOr3' hsnd (poly_comp_fst (ha 2)) (poly_comp_fst (ha 6)) (poly_comp_fst (ha 9))
      · exact poly_gOr3' hsnd (poly_comp_fst (ha 3)) (poly_comp_fst (ha 7))
          (poly_comp_fst (ha 10)))).of_enc_eq
    fun p => congrArg _ (by
      dsimp only [emitOutUpdate_eq, andFns, orFns, List.map_cons, List.map_nil]; rfl)

end CslibFrontier.Computability.Circuit.Oblivious
