/-
Copyright (c) 2026 Formal Papers contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Papers contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.PolyTime
public import Mathlib.Computability.Partrec
import Mathlib.Data.Fintype.Basic

/-!
# Partial Recursive Simulation of Multi-Tape Turing Machines

Every function `f : α → β` between `Primcodable` types that is computable by a deterministic
multi-tape Turing machine with a binary alphabet and finitely many states
(`ComputableInTimeAndSpace`,
and in particular `ComputableInPolyTime`) relative to `Computable` binary encodings
`encIn : α ↪ List Bool` and `encOut : β ↪ List Bool` is `Computable` in Mathlib's partial-recursive
sense (`Mathlib.Computability.Partrec`).

The simulation represents machine states by indices in `ℕ`, shifts all work-tape head positions by
`T + 1` during a `T`-step bounded run so head coordinates remain positive natural numbers, stores
written work-tape cells in an association list queried via `List.lookup`, and applies unbounded
search (`Partrec.rfindOpt`) both to locate a halting horizon `T` and to invert `encOut`.

## Main results

* `Turing.MultiTapeTM.ComputableInTimeAndSpace.computable`: multi-tape TM computability implies
  Mathlib `Computable`.
* `Turing.MultiTapeTM.ComputableInPolyTime.computable`: polynomial-time multi-tape TM computability
  implies Mathlib `Computable`.
-/

public section

namespace Turing.MultiTapeTM

private abbrev SimKey : Type :=
  ℕ × Option Bool × List (Option Bool)

private abbrev SimAct : Type :=
  ℕ × List (Option (Option Bool) × ℕ) × Option Bool × Option ℕ

private abbrev SimCell : Type :=
  (ℕ × ℕ) × Option Bool

private abbrev SimCfg : Type :=
  Option ℕ × ℕ × List SimCell × List ℕ × List Bool

private def encodeSign : SignType → ℕ
  | .neg => 0
  | .zero => 1
  | .pos => 2

private lemma encodeSign_eq_cast_add_one (m : SignType) :
    (encodeSign m : ℤ) = (m.cast : ℤ) + 1 := by
  cases m <;> rfl

private lemma val_moveInputPos_eq_encodeSign {n : ℕ} (pos : Fin (n + 2)) (m : SignType) :
    (moveInputPos pos m).val = min (n + 1) (pos.val + encodeSign m - 1) := by
  have hval := val_moveInputPos_eq pos m
  have hlt := pos.isLt
  cases m <;> simp only [encodeSign, SignType.cast] at hval ⊢ <;> omega

private def defaultSimAct : SimAct :=
  (1, [], none, none)

private def simInputSym (input : List Bool) (inPos : ℕ) : Option Bool :=
  if inPos = 0 ∨ inPos = input.length + 1 then none else input[inPos - 1]?

private lemma primrec_simInputSym : Primrec₂ simInputSym := by
  have h : Primrec (fun p : List Bool × ℕ ↦ simInputSym p.1 p.2) := by
    unfold simInputSym
    refine Primrec.ite ?_ (Primrec.const (none : Option Bool)) ?_
    · exact PrimrecPred.or
        (Primrec.eq.comp Primrec.snd (Primrec.const 0))
        (Primrec.eq.comp Primrec.snd
          (Primrec.succ.comp (Primrec.list_length.comp Primrec.fst)))
    · exact Primrec.list_getElem?.comp Primrec.fst
        (Primrec.nat_sub.comp Primrec.snd (Primrec.const 1))
  exact Primrec.to₂ h

private lemma listLookup_decEq_eq {α β : Type*} [BEq α] [LawfulBEq α] [DecidableEq α]
    (a : α) (l : List (α × β)) :
    @List.lookup α β instBEqOfDecidableEq a l = l.lookup a := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨k, b⟩
    dsimp only [List.lookup]
    have hbeq : @BEq.beq α instBEqOfDecidableEq a k = (a == k) := by
      change decide (a = k) = (a == k)
      by_cases h : a = k
      · subst h; simp
      · simp [beq_false_of_ne h, h]
    rw [hbeq, ih]

private def simStep (k : ℕ) (table : List (SimKey × SimAct)) (input : List Bool)
    (c : SimCfg) : SimCfg :=
  match c.1 with
  | none => c
  | some qIdx =>
    let inPos := c.2.1
    let tapes := c.2.2.1
    let workPos := c.2.2.2.1
    let out := c.2.2.2.2
    let inSym := simInputSym input inPos
    let workSyms := (List.range k).map fun i ↦
      (tapes.lookup (i, workPos.getD i 0)).getD none
    let act := (table.lookup (qIdx, inSym, workSyms)).getD defaultSimAct
    let inMove := act.1
    let workActs := act.2.1
    let outSym := act.2.2.1
    let nextSt := act.2.2.2
    let inPos' := if input.length + 1 ≤ inPos + inMove - 1 then input.length + 1
      else inPos + inMove - 1
    let newCells := (List.range k).filterMap fun i ↦
      ((workActs.getD i (none, 1)).1).map fun s ↦ ((i, workPos.getD i 0), s)
    let tapes' := newCells ++ tapes
    let workPos' := (List.range k).map fun i ↦
      workPos.getD i 0 + (workActs.getD i (none, 1)).2 - 1
    let out' := out ++ outSym.toList
    (nextSt, inPos', tapes', workPos', out')

private lemma primrec_simStep (k : ℕ) (table : List (SimKey × SimAct)) :
    Primrec₂ (simStep k table) := by
  -- Express `simStep k table input c` via `Option.casesOn c.1`.
  have hst : Primrec fun p : List Bool × SimCfg ↦ p.2.1 := Primrec.fst.comp Primrec.snd
  have hc : Primrec fun p : List Bool × SimCfg ↦ p.2 := Primrec.snd
  -- Under `(p, qIdx) : (List Bool × SimCfg) × ℕ`:
  let inpF : (List Bool × SimCfg) × ℕ → List Bool := fun x ↦ x.1.1
  let inPosF : (List Bool × SimCfg) × ℕ → ℕ := fun x ↦ x.1.2.2.1
  let tapesF : (List Bool × SimCfg) × ℕ → List SimCell := fun x ↦ x.1.2.2.2.1
  let workPosF : (List Bool × SimCfg) × ℕ → List ℕ := fun x ↦ x.1.2.2.2.2.1
  let outF : (List Bool × SimCfg) × ℕ → List Bool := fun x ↦ x.1.2.2.2.2.2
  let qIdxF : (List Bool × SimCfg) × ℕ → ℕ := fun x ↦ x.2
  have hinp : Primrec inpF := Primrec.fst.comp Primrec.fst
  have hinPos : Primrec inPosF :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  have htapes : Primrec tapesF :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
  have hworkPos : Primrec workPosF :=
    Primrec.fst.comp
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))))
  have hout : Primrec outF :=
    Primrec.snd.comp
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))))
  have hqIdx : Primrec qIdxF := Primrec.snd
  have hinSym : Primrec fun x ↦ simInputSym (inpF x) (inPosF x) :=
    primrec_simInputSym.comp hinp hinPos
  have hworkSyms : Primrec fun x ↦
      (List.range k).map fun i ↦ ((tapesF x).lookup (i, (workPosF x).getD i 0)).getD none := by
    have hwStep : Primrec fun y : ((List Bool × SimCfg) × ℕ) × ℕ ↦
        ((tapesF y.1).lookup (y.2, (workPosF y.1).getD y.2 0)).getD none := by
      have hkey : Primrec fun y : ((List Bool × SimCfg) × ℕ) × ℕ ↦
          (y.2, (workPosF y.1).getD y.2 0) :=
        Primrec.pair Primrec.snd
          ((Primrec.list_getD 0).comp (hworkPos.comp Primrec.fst) Primrec.snd)
      have hlk : Primrec fun y : ((List Bool × SimCfg) × ℕ) × ℕ ↦
          (tapesF y.1).lookup (y.2, (workPosF y.1).getD y.2 0) :=
        (Primrec.listLookup.comp hkey (htapes.comp Primrec.fst)).of_eq fun _ ↦
          listLookup_decEq_eq _ _
      exact Primrec.option_getD.comp hlk (Primrec.const (none : Option Bool))
    exact Primrec.list_map (Primrec.const (List.range k)) (Primrec.to₂ hwStep)
  let actF : (List Bool × SimCfg) × ℕ → SimAct := fun x ↦
    (table.lookup (qIdxF x, simInputSym (inpF x) (inPosF x),
      (List.range k).map fun i ↦
        ((tapesF x).lookup (i, (workPosF x).getD i 0)).getD none)).getD defaultSimAct
  have hactLk : Primrec fun x : (List Bool × SimCfg) × ℕ ↦
      table.lookup (qIdxF x, simInputSym (inpF x) (inPosF x),
        (List.range k).map fun i ↦
          ((tapesF x).lookup (i, (workPosF x).getD i 0)).getD none) :=
    (Primrec.listLookup.comp (Primrec.pair hqIdx (Primrec.pair hinSym hworkSyms))
      (Primrec.const table)).of_eq fun _ ↦ listLookup_decEq_eq _ _
  have hact : Primrec actF :=
    Primrec.option_getD.comp hactLk (Primrec.const defaultSimAct)
  have hinMove : Primrec fun x ↦ (actF x).1 := Primrec.fst.comp hact
  have hworkActs : Primrec fun x ↦ (actF x).2.1 := Primrec.fst.comp (Primrec.snd.comp hact)
  have houtSym : Primrec fun x ↦ (actF x).2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp hact))
  have hnextSt : Primrec fun x ↦ (actF x).2.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hact))
  have hrawPos : Primrec fun x ↦ inPosF x + (actF x).1 - 1 :=
    Primrec.nat_sub.comp (Primrec.nat_add.comp hinPos hinMove) (Primrec.const 1)
  have hmaxPos : Primrec fun x ↦ (inpF x).length + 1 :=
    Primrec.succ.comp (Primrec.list_length.comp hinp)
  have hinPos' : Primrec fun x ↦
      if (inpF x).length + 1 ≤ inPosF x + (actF x).1 - 1 then (inpF x).length + 1
      else inPosF x + (actF x).1 - 1 :=
    Primrec.ite (Primrec.nat_le.comp hmaxPos hrawPos) hmaxPos hrawPos
  have hnewCells : Primrec fun x ↦
      (List.range k).filterMap fun i ↦
        (((actF x).2.1.getD i (none, 1)).1).map fun s ↦ ((i, (workPosF x).getD i 0), s) := by
    have hncStep : Primrec fun y : ((List Bool × SimCfg) × ℕ) × ℕ ↦
        (((actF y.1).2.1.getD y.2 (none, 1)).1).map fun s ↦
          ((y.2, (workPosF y.1).getD y.2 0), s) := by
      have hwOpt : Primrec fun y : ((List Bool × SimCfg) × ℕ) × ℕ ↦
          ((actF y.1).2.1.getD y.2 (none, 1)).1 :=
        Primrec.fst.comp
          ((Primrec.list_getD (none, 1)).comp (hworkActs.comp Primrec.fst) Primrec.snd)
      have hcellKey : Primrec fun y : (((List Bool × SimCfg) × ℕ) × ℕ) × Option Bool ↦
          (y.1.2, (workPosF y.1.1).getD y.1.2 0) :=
        Primrec.pair (Primrec.snd.comp Primrec.fst)
          ((Primrec.list_getD 0).comp (hworkPos.comp (Primrec.fst.comp Primrec.fst))
            (Primrec.snd.comp Primrec.fst))
      have hpairS : Primrec fun z : (((List Bool × SimCfg) × ℕ) × ℕ) × Option Bool ↦
          ((z.1.2, (workPosF z.1.1).getD z.1.2 0), z.2) :=
        Primrec.pair hcellKey Primrec.snd
      exact Primrec.option_map hwOpt (Primrec.to₂ hpairS)
    exact Primrec.listFilterMap (Primrec.const (List.range k)) (Primrec.to₂ hncStep)
  have htapes' : Primrec fun x ↦
      ((List.range k).filterMap fun i ↦
        (((actF x).2.1.getD i (none, 1)).1).map fun s ↦
          ((i, (workPosF x).getD i 0), s)) ++ tapesF x :=
    Primrec.list_append.comp hnewCells htapes
  have hworkPos' : Primrec fun x ↦
      (List.range k).map fun i ↦
        (workPosF x).getD i 0 + ((actF x).2.1.getD i (none, 1)).2 - 1 := by
    have hwpStep : Primrec fun y : ((List Bool × SimCfg) × ℕ) × ℕ ↦
        (workPosF y.1).getD y.2 0 + ((actF y.1).2.1.getD y.2 (none, 1)).2 - 1 := by
      have hp_i : Primrec fun y : ((List Bool × SimCfg) × ℕ) × ℕ ↦ (workPosF y.1).getD y.2 0 :=
        (Primrec.list_getD 0).comp (hworkPos.comp Primrec.fst) Primrec.snd
      have hm_i : Primrec fun y : ((List Bool × SimCfg) × ℕ) × ℕ ↦
          ((actF y.1).2.1.getD y.2 (none, 1)).2 :=
        Primrec.snd.comp
          ((Primrec.list_getD (none, 1)).comp (hworkActs.comp Primrec.fst) Primrec.snd)
      exact Primrec.nat_sub.comp (Primrec.nat_add.comp hp_i hm_i) (Primrec.const 1)
    exact Primrec.list_map (Primrec.const (List.range k)) (Primrec.to₂ hwpStep)
  have hout' : Primrec fun x ↦ outF x ++ (actF x).2.2.1.toList :=
    Primrec.list_append.comp hout (Primrec.optionToList.comp houtSym)
  have hsome : Primrec fun x : (List Bool × SimCfg) × ℕ ↦
      ((actF x).2.2.2,
        if (inpF x).length + 1 ≤ inPosF x + (actF x).1 - 1 then (inpF x).length + 1
        else inPosF x + (actF x).1 - 1,
        ((List.range k).filterMap fun i ↦
          (((actF x).2.1.getD i (none, 1)).1).map fun s ↦
            ((i, (workPosF x).getD i 0), s)) ++ tapesF x,
        (List.range k).map fun i ↦
          (workPosF x).getD i 0 + ((actF x).2.1.getD i (none, 1)).2 - 1,
        outF x ++ (actF x).2.2.1.toList) :=
    Primrec.pair hnextSt
      (Primrec.pair hinPos' (Primrec.pair htapes' (Primrec.pair hworkPos' hout')))
  have hstepUncurry : Primrec fun p : List Bool × SimCfg ↦ simStep k table p.1 p.2 := by
    refine (Primrec.option_casesOn hst hc (Primrec.to₂ hsome)).of_eq ?_
    rintro ⟨input, st, inPos, tapes, workPos, out⟩
    cases st <;> rfl
  exact Primrec.to₂ hstepUncurry

private def simInit (k q₀Idx : ℕ) (T : ℕ) : SimCfg :=
  (some q₀Idx, 1, [], (List.range k).map (fun _ ↦ T + 1), [])

private def simRun (k q₀Idx : ℕ) (table : List (SimKey × SimAct))
    (input : List Bool) (T : ℕ) : SimCfg :=
  (simStep k table input)^[T] (simInit k q₀Idx T)

private lemma primrec_simRun (k q₀Idx : ℕ) (table : List (SimKey × SimAct)) :
    Primrec₂ (simRun k q₀Idx table) := by
  have hinit : Primrec fun p : List Bool × ℕ ↦ simInit k q₀Idx p.2 := by
    unfold simInit
    refine Primrec.pair (Primrec.const (some q₀Idx))
      (Primrec.pair (Primrec.const 1)
        (Primrec.pair (Primrec.const [])
          (Primrec.pair ?_ (Primrec.const []))))
    exact Primrec.list_map (Primrec.const (List.range k))
      (Primrec.to₂ (Primrec.succ.comp (Primrec.snd.comp Primrec.fst)))
  have hstep : Primrec₂ fun (p : List Bool × ℕ) (c : SimCfg) ↦ simStep k table p.1 c :=
    (primrec_simStep k table).comp (Primrec.fst.comp Primrec.fst) Primrec.snd
  exact Primrec.to₂ (Primrec.nat_iterate Primrec.snd hinit hstep)

private lemma lookup_filterMap_range_cells (k : ℕ) (workPos : List ℕ)
    (workActs : List (Option (Option Bool) × ℕ)) (tapes : List SimCell)
    (i : ℕ) (hi : i < k) (p : ℕ) :
    ((((List.range k).filterMap fun j ↦
        ((workActs.getD j (none, 1)).1).map fun s ↦ ((j, workPos.getD j 0), s)) ++
        tapes).lookup (i, p)).getD none =
      match (workActs.getD i (none, 1)).1 with
      | none => (tapes.lookup (i, p)).getD none
      | some s => if p = workPos.getD i 0 then s else (tapes.lookup (i, p)).getD none := by
  rw [List.lookup_append]
  set g : ℕ → Option SimCell := fun j ↦
    ((workActs.getD j (none, 1)).1).map fun s ↦ ((j, workPos.getD j 0), s)
  have hlookup_in : ∀ (l : List ℕ), (∀ j ∈ l, j ≠ i) →
      ((l.filterMap g).lookup (i, p)) = none := by
    intro l hl
    induction l with
    | nil => rfl
    | cons j tl ih =>
      have hj : j ≠ i := hl j List.mem_cons_self
      have htl : ∀ j' ∈ tl, j' ≠ i := fun j' hj' ↦ hl j' (List.mem_cons_of_mem j hj')
      simp only [List.filterMap_cons, g]
      cases (workActs.getD j (none, 1)).1 with
      | none => exact ih htl
      | some s =>
        simp only [Option.map_some, List.lookup_cons]
        have hbeq : ((i, p) == (j, workPos.getD j 0)) = false :=
          beq_false_of_ne fun h ↦ hj (Prod.mk.inj h).1.symm
        rw [hbeq]
        exact ih htl
  have hsplit : List.range k =
    List.range i ++ (i :: (List.range (k - i - 1)).map (· + (i + 1))) := by
    apply List.ext_getElem
    · simp; omega
    · intro idx h1 h2
      rw [List.getElem_range]
      by_cases hlt : idx < i
      · rw [List.getElem_append_left (by simp [hlt]), List.getElem_range]
      · rw [List.getElem_append_right (by simp; omega)]
        simp only [List.length_range]
        rcases eq_or_lt_of_le (Nat.le_of_not_lt hlt) with rfl | hgt
        · simp
        · obtain ⟨d, hd⟩ := Nat.exists_eq_succ_of_ne_zero (show idx - i ≠ 0 by omega)
          simp [hd]; omega
  rw [hsplit, List.filterMap_append, List.lookup_append]
  have hleft_none : ((List.range i).filterMap g).lookup (i, p) = none :=
    hlookup_in _ fun j hj ↦ (List.mem_range.mp hj).ne
  have hright_none :
      (((List.range (k - i - 1)).map (· + (i + 1))).filterMap g).lookup (i, p) = none := by
    refine hlookup_in _ fun j hj ↦ ?_
    rcases List.mem_map.mp hj with ⟨d, _, rfl⟩
    omega
  rw [hleft_none, Option.none_or, List.filterMap_cons]
  have hgi : g i =
      ((workActs.getD i (none, 1)).1).map (fun s ↦ ((i, workPos.getD i 0), s)) := rfl
  rw [hgi]
  cases hact : (workActs.getD i (none, 1)).1 with
  | none =>
    rw [Option.map_none, hright_none]
    rfl
  | some s =>
    rw [Option.map_some, List.lookup_cons]
    dsimp only
    by_cases hp : p = workPos.getD i 0
    · subst hp; simp
    · have hbeq : ((i, p) == (i, workPos.getD i 0)) = false :=
        beq_false_of_ne fun h ↦ hp (Prod.mk.inj h).2
      rw [hbeq]
      dsimp only
      rw [hright_none, ite_eq_right hp]
      rfl

/-- Every function between `Primcodable` types computable in time and space on a deterministic
multi-tape Turing machine with finitely many states relative to `Computable` binary encodings is
`Computable` in Mathlib's partial-recursive sense. -/
theorem ComputableInTimeAndSpace.computable {α β : Type*} [Primcodable α] [Primcodable β]
    {f : α → β} {encIn : α ↪ List Bool} {encOut : β ↪ List Bool} {t s : α → ℕ}
    (h : ComputableInTimeAndSpace f encIn encOut t s)
    (hIn : _root_.Computable encIn) (hOut : _root_.Computable encOut) :
    _root_.Computable f := by
  classical
  obtain ⟨k, State, hfin, tm, htm⟩ := h
  let _ : Fintype State := Fintype.ofFinite State
  let eS : State ≃ Fin (Fintype.card State) := Fintype.equivFin State
  let q₀Idx : ℕ := (eS tm.q₀).val
  -- Build the finite transition lookup table `table : List (SimKey × SimAct)`.
  let domList : List (State × Option Bool × (Fin k → Option Bool)) := Finset.univ.toList
  let encodeKey (x : State × Option Bool × (Fin k → Option Bool)) : SimKey :=
    ((eS x.1).val, x.2.1, List.ofFn x.2.2)
  let encodeAct (act : Action k Bool State) : SimAct :=
    (encodeSign act.inputTape,
      List.ofFn (fun i : Fin k ↦ ((act.workTapes i).1, encodeSign (act.workTapes i).2)),
      act.output,
      act.state.map fun q ↦ (eS q).val)
  let table : List (SimKey × SimAct) :=
    domList.map fun x ↦ (encodeKey x, encodeAct (tm.tr x.1 x.2.1 x.2.2))
  have hencodeKey_inj : Function.Injective encodeKey := by
    rintro ⟨q₁, i₁, w₁⟩ ⟨q₂, i₂, w₂⟩ heq
    rcases Prod.mk.inj heq with ⟨hq, hiw⟩
    rcases Prod.mk.inj hiw with ⟨hi, hw⟩
    have hq_eq : q₁ = q₂ := eS.injective (Fin.ext hq)
    have hw_eq : w₁ = w₂ := List.ofFn_injective hw
    subst hq_eq hi hw_eq
    rfl
  have htable_lookup : ∀ (q : State) (inp : Option Bool) (work : Fin k → Option Bool),
      (table.lookup (encodeKey (q, inp, work))).getD defaultSimAct =
        encodeAct (tm.tr q inp work) := by
    intro q inp work
    have hmem : (q, inp, work) ∈ domList := Finset.mem_toList.mpr (Finset.mem_univ _)
    suffices ∀ l : List (State × Option Bool × (Fin k → Option Bool)),
        (q, inp, work) ∈ l →
        (l.map fun x ↦ (encodeKey x, encodeAct (tm.tr x.1 x.2.1 x.2.2))).lookup
          (encodeKey (q, inp, work)) = some (encodeAct (tm.tr q inp work)) by
      rw [this domList hmem]; rfl
    intro l hl
    induction l with
    | nil => simp at hl
    | cons hd tl ih =>
      simp only [List.map_cons, List.lookup_cons]
      by_cases hhd : encodeKey (q, inp, work) = encodeKey hd
      · have heq := hencodeKey_inj hhd
        subst heq
        simp
      · have hbeq : (encodeKey (q, inp, work) == encodeKey hd) = false := beq_false_of_ne hhd
        rw [hbeq]
        rcases List.mem_cons.mp hl with rfl | htl
        · exact absurd rfl hhd
        · exact ih htl
  -- Relate `tm.runFrom (tm.initCfg input) n` to `(simStep k table input)^[n] (simInit k q₀Idx T)`
  -- for every `n ≤ T`.
  let Rel (input : List Bool) (T : ℕ) (cfg : Cfg k Bool State input) (sc : SimCfg) : Prop :=
    sc.1 = cfg.state.map (fun q ↦ (eS q).val) ∧
    sc.2.1 = cfg.inputPos.val ∧
    (∀ (i : Fin k) (z : ℤ),
      1 ≤ z + ((T + 1 : ℕ) : ℤ) →
        (sc.2.2.1.lookup (i.val, (z + ((T + 1 : ℕ) : ℤ)).toNat)).getD none =
          cfg.workTapes i z) ∧
    (∀ i : Fin k, (cfg.workTapePos i).natAbs ≤ T ∧
      sc.2.2.2.1.getD i.val 0 = (cfg.workTapePos i + ((T + 1 : ℕ) : ℤ)).toNat) ∧
    sc.2.2.2.2 = cfg.output ∧
    sc.2.2.2.1.length = k
  have hRel_simRun : ∀ (input : List Bool) (T : ℕ),
      Rel input T (tm.runFrom (tm.initCfg input) T) (simRun k q₀Idx table input T) := by
    intro input T
    suffices ∀ n ≤ T,
        Rel input T (tm.runFrom (tm.initCfg input) n)
          ((simStep k table input)^[n] (simInit k q₀Idx T)) ∧
        ∀ i : Fin k, ((tm.runFrom (tm.initCfg input) n).workTapePos i).natAbs ≤ n from
      (this T le_rfl).1
    intro n hn
    induction n with
    | zero =>
      refine ⟨⟨rfl, rfl, ?_, ?_, rfl, by simp [simInit]⟩, fun _ ↦ by simp [runFrom,
        MultiTapeNTM.initCfg]⟩
      · intro i z _; rfl
      · intro i
        simp only [runFrom, Function.iterate_zero, id_eq, MultiTapeNTM.initCfg, Cfg.init,
          Int.natAbs_zero, Nat.zero_le, true_and, simInit]
        rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range i.isLt]
        simp
    | succ n ih =>
      obtain ⟨⟨hst, hinPos, htapes, hpos, hout, hlen_pos⟩, hbound_n⟩ := ih (Nat.le_of_succ_le hn)
      set cfg := tm.runFrom (tm.initCfg input) n
      set sc := (simStep k table input)^[n] (simInit k q₀Idx T)
      have hrun_succ : tm.runFrom (tm.initCfg input) (n + 1) = tm.step cfg :=
        Function.iterate_succ_apply' tm.step n (tm.initCfg input)
      have hsim_succ : (simStep k table input)^[n + 1] (simInit k q₀Idx T) =
          simStep k table input sc :=
        Function.iterate_succ_apply' (simStep k table input) n (simInit k q₀Idx T)
      rw [hrun_succ, hsim_succ]
      rcases hq : cfg.state with _ | q
      · -- Halted step
        have hsc1 : sc.1 = none := by rw [hst, hq]; rfl
        rw [step_of_halt hq]
        have hstep_sc : simStep k table input sc = sc := by
          rcases sc with ⟨st, a, b, c, d⟩
          dsimp at hsc1
          subst hsc1
          rfl
        rw [hstep_sc]
        exact ⟨⟨hst, hinPos, htapes, hpos, hout, hlen_pos⟩,
          fun i ↦ (hbound_n i).trans (Nat.le_succ n)⟩
      · -- Live step in state `q`
        have hsc1 : sc.1 = some (eS q).val := by rw [hst, hq]; rfl
        have hstep_cfg := tm.step_of_state hq
        rw [hstep_cfg]
        -- Verify input symbol and work symbols agree with `cfg.inputSymbol` and
        -- `cfg.workTapeSymbols`.
        have hinSym_eq : simInputSym input sc.2.1 = cfg.inputSymbol := by
          rw [hinPos]
          unfold simInputSym Cfg.inputSymbol
          by_cases h0 : cfg.inputPos = 0
          · simp [h0]
          · have hv0 : cfg.inputPos.val ≠ 0 := fun h ↦ h0 (Fin.ext h)
            by_cases h1 : cfg.inputPos.val = input.length + 1
            · simp [h0, h1]
            · have hlt_in : cfg.inputPos.val - 1 < input.length := by
                have := cfg.inputPos.isLt; omega
              simp [h0, hv0, h1, List.getElem?_eq_getElem hlt_in]
        have hworkSyms_eq :
            ((List.range k).map fun i ↦ (sc.2.2.1.lookup (i, sc.2.2.2.1.getD i 0)).getD none) =
              List.ofFn cfg.workTapeSymbols := by
          apply List.ext_getElem
          · simp
          · intro idx h1 h2
            simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn]
            let i : Fin k := ⟨idx, by simpa using h1⟩
            have hi_abs : (cfg.workTapePos i).natAbs ≤ n := hbound_n i
            have hi_ge1 : 1 ≤ cfg.workTapePos i + ((T + 1 : ℕ) : ℤ) := by omega
            rw [(hpos i).2]
            exact htapes i (cfg.workTapePos i) hi_ge1
        -- Unfold `simStep` on `sc` with `sc.1 = some (eS q).val`.
        rcases sc with ⟨_, inPos, tapes, workPos, out⟩
        dsimp at hsc1 hinPos htapes hpos hout hlen_pos hinSym_eq hworkSyms_eq
        subst hsc1
        simp only [simStep, hinSym_eq, hworkSyms_eq]
        have hact_eq : (table.lookup ((eS q).val, cfg.inputSymbol,
          List.ofFn cfg.workTapeSymbols)).getD
            defaultSimAct = encodeAct (tm.tr q cfg.inputSymbol cfg.workTapeSymbols) :=
          htable_lookup q cfg.inputSymbol cfg.workTapeSymbols
        rw [hact_eq]
        set act := tm.tr q cfg.inputSymbol cfg.workTapeSymbols
        have hworkActs_getD : ∀ i : Fin k,
            (List.ofFn
              (fun j : Fin k ↦ ((act.workTapes j).1, encodeSign (act.workTapes j).2))).getD
                i.val (none, 1) =
              ((act.workTapes i).1, encodeSign (act.workTapes i).2) := by
          intro i
          rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
          simp [i.isLt]
        have hbound_next : ∀ i : Fin k, ((act.apply cfg).workTapePos i).natAbs ≤ n + 1 := by
          intro i
          have hmove := abs_le.mp (Turing.workTapePos_apply_le act cfg i)
          have hprev := hbound_n i
          omega
        refine ⟨⟨rfl, ?_, ?_, ?_, ?_, by simp⟩, hbound_next⟩
        · -- Input head position
          rw [Action.apply_inputPos, val_moveInputPos_eq_encodeSign, hinPos]
          dsimp [encodeAct]
          by_cases hle : input.length + 1 ≤ cfg.inputPos.val + encodeSign act.inputTape - 1
          · rw [ite_eq_left hle]; omega
          · rw [ite_eq_right hle]; omega
        · -- Work tape contents
          intro i z hz1
          dsimp [encodeAct]
          rw [lookup_filterMap_range_cells k workPos _ tapes i.val i.isLt _, hworkActs_getD i]
          dsimp [Action.apply]
          have hcur_ge1 : 1 ≤ cfg.workTapePos i + ((T + 1 : ℕ) : ℤ) := by
            have := hbound_n i; omega
          have hpos_eq_iff :
              ((z + ((T : ℤ) + 1)).toNat = workPos.getD i.val 0) ↔ z = cfg.workTapePos i := by
            rw [(hpos i).2]
            omega
          cases hw : (act.workTapes i).1 with
          | none =>
            exact htapes i z hz1
          | some s =>
            dsimp only
            by_cases hzeq : z = cfg.workTapePos i
            · rw [ite_eq_left (hpos_eq_iff.mpr hzeq), hzeq, Function.update_self]
            · rw [ite_eq_right (mt hpos_eq_iff.mp hzeq), Function.update_of_ne hzeq]
              exact htapes i z hz1
        · -- Work tape head positions
          intro i
          refine ⟨(hbound_next i).trans hn, ?_⟩
          dsimp [encodeAct]
          rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range i.isLt]
          simp only [Option.map_some, Option.getD_some, (hpos i).2, hworkActs_getD i,
            Action.apply_workTapePos]
          have hcur_ge1 : 1 ≤ cfg.workTapePos i + ((T + 1 : ℕ) : ℤ) := by
            have := hbound_n i; omega
          have henc := encodeSign_eq_cast_add_one (act.workTapes i).2
          omega
        · -- Output tape
          simp [hout, encodeAct, Action.apply_output]
  -- Step 1: Compute `a ↦ encOut (f a)` via `Partrec.rfindOpt` on `T`.
  let findOutOpt (a : α) (T : ℕ) : Option (List Bool) :=
    let sc := simRun k q₀Idx table (encIn a) T
    match sc.1 with
    | none => some sc.2.2.2.2
    | some _ => none
  have hcomp_findOutOpt : _root_.Computable₂ findOutOpt := by
    have hsc : _root_.Computable fun p : α × ℕ ↦ simRun k q₀Idx table (encIn p.1) p.2 :=
      (primrec_simRun k q₀Idx table).to_comp.comp (hIn.comp _root_.Computable.fst)
        _root_.Computable.snd
    have hmain : _root_.Computable (fun p : α × ℕ ↦ findOutOpt p.1 p.2) := by
      refine (_root_.Computable.option_casesOn (_root_.Computable.fst.comp hsc)
        (_root_.Computable.option_some.comp
          (_root_.Computable.snd.comp (_root_.Computable.snd.comp
            (_root_.Computable.snd.comp (_root_.Computable.snd.comp hsc)))))
        (_root_.Computable.const none).to₂).of_eq fun ⟨a, T⟩ ↦ ?_
      dsimp [findOutOpt]
      cases (simRun k q₀Idx table (encIn a) T).1 <;> rfl
    exact _root_.Computable.to₂ hmain
  have hcomp_encOut_f : _root_.Computable (fun a : α ↦ encOut (f a)) := by
    refine (Partrec.rfindOpt hcomp_findOutOpt).of_eq_tot fun a ↦ ?_
    obtain ⟨⟨T₀, hhalt₀, hout₀⟩, -, -⟩ := htm a
    have hrel₀ := hRel_simRun (encIn a) T₀
    have hmem₀ : encOut (f a) ∈ findOutOpt a T₀ := by
      unfold findOutOpt
      dsimp only
      rw [hrel₀.1, hhalt₀, Option.map_none]
      dsimp only
      rw [hrel₀.2.2.2.2.1, hout₀]
      rfl
    have hdom : (Nat.rfindOpt (findOutOpt a)).Dom :=
      Nat.rfindOpt_dom.mpr ⟨T₀, encOut (f a), hmem₀⟩
    have hget_mem : (Nat.rfindOpt (findOutOpt a)).get hdom ∈ Nat.rfindOpt (findOutOpt a) :=
      Part.get_mem hdom
    obtain ⟨T₁, hT₁⟩ := Nat.rfindOpt_spec hget_mem
    have hrel₁ := hRel_simRun (encIn a) T₁
    dsimp [findOutOpt] at hT₁
    rcases hst₁ : (tm.runFrom (tm.initCfg (encIn a)) T₁).state with _ | q₁
    · rw [hrel₁.1, hst₁] at hT₁
      simp only [Option.map_none, Option.mem_def, Option.some.injEq] at hT₁
      have hhalt₁ : (tm.runFrom (tm.initCfg (encIn a)) T₁).Halted := hst₁
      have heq_run : tm.runFrom (tm.initCfg (encIn a)) T₁ =
          tm.runFrom (tm.initCfg (encIn a)) T₀ := by
        rcases le_total T₁ T₀ with hle | hle
        · exact (tm.runFrom_eq_of_halt _ hle hhalt₁).symm
        · exact tm.runFrom_eq_of_halt _ hle hhalt₀
      have hout_eq : (Nat.rfindOpt (findOutOpt a)).get hdom = encOut (f a) := by
        rw [← hT₁, hrel₁.2.2.2.2.1, heq_run, hout₀]
      rwa [← hout_eq]
    · rw [hrel₁.1, hst₁] at hT₁
      simp at hT₁
  -- Step 2: Invert `encOut : β ↪ List Bool` via `Partrec.rfindOpt` over `Encodable.decode (α :=
  -- β)`.
  let decodeOutOpt (a : α) (n : ℕ) : Option β :=
    match Encodable.decode (α := β) n with
    | none => none
    | some b => if encOut b = encOut (f a) then some b else none
  have hcomp_decodeOutOpt : _root_.Computable₂ decodeOutOpt := by
    have hdec : _root_.Computable fun p : α × ℕ ↦ Encodable.decode (α := β) p.2 :=
      _root_.Computable.decode.comp _root_.Computable.snd
    have hbranch : _root_.Computable₂ fun (p : α × ℕ) (b : β) ↦
        if encOut b = encOut (f p.1) then some b else none := by
      have heq_b : _root_.Computable fun x : (α × ℕ) × β ↦
          decide (Encodable.encode (encOut x.2) = Encodable.encode (encOut (f x.1.1))) :=
        ((Primrec.eq.comp Primrec.fst Primrec.snd).decide.to_comp).comp
          (_root_.Computable.pair
            (_root_.Computable.encode.comp (hOut.comp _root_.Computable.snd))
            (_root_.Computable.encode.comp
              (hcomp_encOut_f.comp (_root_.Computable.fst.comp _root_.Computable.fst))))
      have hbr_main : _root_.Computable (fun x : (α × ℕ) × β ↦
          if encOut x.2 = encOut (f x.1.1) then some x.2 else none) := by
        refine (_root_.Computable.cond heq_b
          (_root_.Computable.option_some.comp _root_.Computable.snd)
          (_root_.Computable.const none)).of_eq fun ⟨⟨a, _⟩, b⟩ ↦ ?_
        by_cases h : encOut b = encOut (f a) <;> simp [h, Encodable.encode_inj]
      exact _root_.Computable.to₂ hbr_main
    have hdec_main : _root_.Computable (fun p : α × ℕ ↦ decodeOutOpt p.1 p.2) := by
      refine (_root_.Computable.option_casesOn hdec (_root_.Computable.const none) hbranch).of_eq
        fun ⟨a, n⟩ ↦ ?_
      dsimp [decodeOutOpt]
      cases Encodable.decode (α := β) n <;> rfl
    exact _root_.Computable.to₂ hdec_main
  refine (Partrec.rfindOpt hcomp_decodeOutOpt).of_eq_tot fun a ↦ ?_
  have hmem_fa : f a ∈ decodeOutOpt a (Encodable.encode (f a)) := by
    simp [decodeOutOpt, Encodable.encodek]
  have hdom : (Nat.rfindOpt (decodeOutOpt a)).Dom :=
    Nat.rfindOpt_dom.mpr ⟨Encodable.encode (f a), f a, hmem_fa⟩
  have hget_mem : (Nat.rfindOpt (decodeOutOpt a)).get hdom ∈ Nat.rfindOpt (decodeOutOpt a) :=
    Part.get_mem hdom
  obtain ⟨n₁, hn₁⟩ := Nat.rfindOpt_spec hget_mem
  dsimp [decodeOutOpt] at hn₁
  rcases hdec₁ : Encodable.decode (α := β) n₁ with _ | b
  · rw [hdec₁] at hn₁; simp at hn₁
  · rw [hdec₁] at hn₁
    dsimp only at hn₁
    by_cases heq : encOut b = encOut (f a)
    · rw [ite_eq_left heq] at hn₁
      simp only [Option.mem_def, Option.some.injEq] at hn₁
      have hb_eq : b = f a := encOut.injective heq
      rwa [← hb_eq, hn₁]
    · rw [ite_eq_right heq] at hn₁; simp at hn₁

/-- Every polynomial-time multi-tape TM computable function between `Primcodable` types (relative to
`Computable` binary encodings) is `Computable` in Mathlib's partial-recursive sense. -/
theorem ComputableInPolyTime.computable {α β : Type*} [Primcodable α] [Primcodable β]
    {f : α → β} {encIn : α ↪ List Bool} {encOut : β ↪ List Bool}
    (h : ComputableInPolyTime f encIn encOut)
    (hIn : _root_.Computable encIn) (hOut : _root_.Computable encOut) :
    _root_.Computable f := by
  obtain ⟨t, s, -, -, hts⟩ := h
  exact hts.computable hIn hOut

end Turing.MultiTapeTM
