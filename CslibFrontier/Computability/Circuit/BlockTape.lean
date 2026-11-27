module

public import Cslib.Computability.Machines.Turing.MultiTape.Deterministic
public import CslibFrontier.Computability.Machines.Turing.MultiTape.OutView
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Nat.Log
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring

/-!
# Pippenger–Fischer Oblivious Block-Tape Simulation

This module formalizes the pure block-structured half-tape data structure of Pippenger and
Fischer and proves that it simulates any deterministic multi-tape
Turing machine (`Turing.MultiTapeTM`) for `T` steps using an oblivious rebalance schedule
where level `i` rebalances only at steps `t + 1` divisible by `2 ^ (i + 1)`.

## Main definitions

* `CslibFrontier.Computability.Circuit.BlockCell`: 2-bit tape cell (`Bool × Bool`) uniformly
  encoding work-tape symbols (`Option Bool`) and input-tape boundary markers.
* `CslibFrontier.Computability.Circuit.BlockLevel`: one level `i` of a half-tape holding
  `cnt ≤ 5` blocks of `2 ^ i` cells in five slots.
* `CslibFrontier.Computability.Circuit.BlockHalfTape`: `L` hierarchical levels with
  concatenation semantics `BlockHalfTape.toList`.
* `CslibFrontier.Computability.Circuit.BlockTape`: bidirectional tape `(headCell, left, right)`
  with oblivious push/pop and scheduled rebalance.
* `CslibFrontier.Computability.Circuit.ObliviousCfg`: full oblivious simulation state for a
  deterministic `Turing.MultiTapeTM`.

## Main results

* `CslibFrontier.Computability.Circuit.BlockHalfTape.toList_rebalanceStep`: scheduled
  rebalancing preserves the exact concatenated list of tape cells.
* `CslibFrontier.Computability.Circuit.BlockHalfTape.inv_rebalanceStep`: scheduled rebalancing
  maintains the level-count invariant (`2 ≤ cnt ≤ 3` at multiples of `2 ^ (i + 1)`).
* `CslibFrontier.Computability.Circuit.ObliviousCfg.run_agrees`: after `t ≤ T` steps, the
  oblivious simulation agrees with `tm.runFrom (tm.initCfg input) t` on state, output,
  input-head symbol, and all work-tape contents.
-/

public section

namespace CslibFrontier.Computability.Circuit

open Turing MultiTapeTM

/-- Uniform 2-bit tape cell: `(false, false)` is blank (or left input boundary),
`(false, true)` is the right input boundary, and `(true, b)` is `some b`. -/
abbrev BlockCell : Type := Bool × Bool

namespace BlockCell

/-- Decode a `BlockCell` to `Option Bool` (both boundary markers read as blank `none`). -/
@[expose] def toOption (c : BlockCell) : Option Bool :=
  if c.1 then some c.2 else none

/-- Encode an `Option Bool` as a work-tape `BlockCell`. -/
@[expose] def ofOption : Option Bool → BlockCell
  | none => (false, false)
  | some b => (true, b)

/-- Left input boundary marker. -/
@[expose] def leftEnd : BlockCell := (false, false)

/-- Right input boundary marker. -/
@[expose] def rightEnd : BlockCell := (false, true)

@[simp]
theorem toOption_ofOption (o : Option Bool) : (ofOption o).toOption = o := by
  cases o <;> rfl

@[simp]
theorem toOption_leftEnd : leftEnd.toOption = none := rfl

@[simp]
theorem toOption_rightEnd : rightEnd.toOption = none := rfl

/-- Input-tape cell at integer coordinate `z` for `input : List Bool`. -/
@[expose] def inputCell (input : List Bool) (z : ℤ) : BlockCell :=
  if z ≤ 0 then leftEnd
  else if h : z.toNat - 1 < input.length then (true, input[z.toNat - 1])
  else rightEnd

theorem toOption_inputCell_pos (input : List Bool) {p : ℕ} (hp : p < input.length) :
    (inputCell input (1 + p : ℕ)).toOption = some input[p] := by
  have h1 : ¬ (1 + (p : ℤ) ≤ 0) := by omega
  have h2 : (1 + (p : ℤ)).toNat - 1 = p := by omega
  simp [inputCell, h1, h2, hp, toOption]

theorem inputCell_zero (input : List Bool) : inputCell input 0 = leftEnd := by
  simp [inputCell]

theorem inputCell_end (input : List Bool) :
    inputCell input (input.length + 1 : ℕ) = rightEnd := by
  have h1 : ¬ ((input.length : ℤ) + 1 ≤ 0) := by omega
  simp [inputCell, h1]


theorem leftEnd_eq : leftEnd = (false, false) := rfl
theorem rightEnd_eq : rightEnd = (false, true) := rfl
theorem inputCell_eq (input : List Bool) (z : ℤ) :
    inputCell input z =
      if z ≤ 0 then leftEnd
      else if h : z.toNat - 1 < input.length then (true, input[z.toNat - 1])
      else rightEnd := rfl

end BlockCell

/-- One level `i` of a Pippenger–Fischer half-tape: up to `5` blocks of `2 ^ i` cells. -/
@[ext]
structure BlockLevel (i : ℕ) where
  /-- Number of active blocks in `slots` (maintained in `0..5`). -/
  cnt : ℕ
  /-- Five block slots, each storing `2 ^ i` cells (closest to head first). -/
  slots : Fin 5 → Fin (2 ^ i) → BlockCell

namespace BlockLevel

/-- Concatenated list of cells stored in the first `cnt` slots of `lvl`. -/
def toList {i : ℕ} (lvl : BlockLevel i) : List BlockCell :=
  ((List.finRange 5).take lvl.cnt).flatMap fun s => List.ofFn (lvl.slots s)

/-- Constant level filled with `c` in `2` active slots. -/
@[expose] def initConst (i : ℕ) (c : BlockCell) : BlockLevel i where
  cnt := 2
  slots _ _ := c

theorem toList_initConst (i : ℕ) (c : BlockCell) :
    (initConst i c).toList = List.replicate (2 * 2 ^ i) c := by
  simp only [toList, initConst, List.finRange_succ, List.map_cons, List.take_succ_cons,
    List.take_zero, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.ofFn_const]
  rw [← List.replicate_add]
  congr 1; omega

/-- Push one cell onto the front of level `0`. -/
@[expose] def push0 (c : BlockCell) (lvl : BlockLevel 0) : BlockLevel 0 where
  cnt := lvl.cnt + 1
  slots s j :=
    match s with
    | ⟨0, _⟩ => c
    | ⟨1, _⟩ => lvl.slots 0 j
    | ⟨2, _⟩ => lvl.slots 1 j
    | ⟨3, _⟩ => lvl.slots 2 j
    | ⟨4, _⟩ => lvl.slots 3 j

/-- Pop the front cell of level `0` (valid when `1 ≤ lvl.cnt`). -/
@[expose] def pop0 (lvl : BlockLevel 0) : BlockCell × BlockLevel 0 :=
  (lvl.slots 0 0,
    { cnt := lvl.cnt - 1
      slots := fun s j =>
        match s with
        | ⟨0, _⟩ => lvl.slots 1 j
        | ⟨1, _⟩ => lvl.slots 2 j
        | ⟨2, _⟩ => lvl.slots 3 j
        | ⟨3, _⟩ => lvl.slots 4 j
        | ⟨4, _⟩ => lvl.slots 4 j })

theorem toList_push0 (c : BlockCell) (lvl : BlockLevel 0) (h : lvl.cnt ≤ 4) :
    (push0 c lvl).toList = c :: lvl.toList := by
  rcases lvl with ⟨cnt, slots⟩
  dsimp only at h
  interval_cases cnt <;> simp [toList, push0, List.finRange_succ]

theorem toList_pop0 (lvl : BlockLevel 0) (h1 : 1 ≤ lvl.cnt) (h2 : lvl.cnt ≤ 5) :
    lvl.toList = (pop0 lvl).1 :: (pop0 lvl).2.toList := by
  rcases lvl with ⟨cnt, slots⟩
  dsimp only at h1 h2
  interval_cases cnt <;> simp [toList, pop0, List.finRange_succ]

/-- Split a block of size `2 ^ (i + 1)` into its first and second halves of size `2 ^ i`. -/
@[expose] def splitBlock {i : ℕ} (b : Fin (2 ^ (i + 1)) → BlockCell) :
    (Fin (2 ^ i) → BlockCell) × (Fin (2 ^ i) → BlockCell) :=
  (fun j => b ⟨j.val, by rw [pow_succ]; omega⟩,
   fun j => b ⟨2 ^ i + j.val, by rw [pow_succ]; omega⟩)

/-- Merge two blocks of size `2 ^ i` into one block of size `2 ^ (i + 1)`. -/
@[expose] def mergeBlock {i : ℕ} (b0 b1 : Fin (2 ^ i) → BlockCell) : Fin (2 ^ (i + 1)) →
  BlockCell :=
  fun j =>
    if h : j.val < 2 ^ i then b0 ⟨j.val, h⟩
    else b1 ⟨j.val - 2 ^ i, by rw [pow_succ] at j; omega⟩

theorem ofFn_splitBlock {i : ℕ} (b : Fin (2 ^ (i + 1)) → BlockCell) :
    List.ofFn (splitBlock b).1 ++ List.ofFn (splitBlock b).2 = List.ofFn b := by
  refine List.ext_getElem (by simp [pow_succ]; omega) fun k hk1 hk2 => ?_
  by_cases h : k < 2 ^ i
  · rw [List.getElem_append_left (by simpa using h)]
    simp [splitBlock]
  · rw [List.getElem_append_right (by simpa using Nat.le_of_not_lt h)]
    simp only [List.length_ofFn, List.getElem_ofFn, splitBlock]
    congr 1; apply Fin.ext; dsimp; omega

theorem ofFn_mergeBlock {i : ℕ} (b0 b1 : Fin (2 ^ i) → BlockCell) :
    List.ofFn (mergeBlock b0 b1) = List.ofFn b0 ++ List.ofFn b1 := by
  refine List.ext_getElem (by simp [pow_succ]; omega) fun k hk1 hk2 => ?_
  by_cases h : k < 2 ^ i
  · rw [List.getElem_append_left (by simpa using h)]
    simp [mergeBlock, h]
  · rw [List.getElem_append_right (by simpa using Nat.le_of_not_lt h)]
    simp [mergeBlock, h]

/-- Rebalance adjacent levels `low : BlockLevel i` and `hi : BlockLevel (i + 1)`:
- `cnt ∈ {0, 1}`: borrow block `0` of `hi` and split into 2 blocks appended to `low`.
- `cnt ∈ {2, 3}`: no-op.
- `cnt ∈ {4, 5}`: merge the furthest 2 blocks of `low` and prepend to `hi`. -/
@[expose] def rebalance {i : ℕ} (low : BlockLevel i) (hi : BlockLevel (i + 1)) :
    BlockLevel i × BlockLevel (i + 1) :=
  let (h0, h1) := splitBlock (hi.slots 0)
  match low.cnt with
  | 0 =>
    ({ cnt := 2
       slots := fun s => match s.val with
         | 0 => h0 | 1 => h1 | _ => low.slots s },
     { cnt := hi.cnt - 1
       slots := fun s => match s.val with
         | 0 => hi.slots 1 | 1 => hi.slots 2 | 2 => hi.slots 3
         | 3 => hi.slots 4 | _ => hi.slots 4 })
  | 1 =>
    ({ cnt := 3
       slots := fun s => match s.val with
         | 0 => low.slots 0 | 1 => h0 | 2 => h1 | _ => low.slots s },
     { cnt := hi.cnt - 1
       slots := fun s => match s.val with
         | 0 => hi.slots 1 | 1 => hi.slots 2 | 2 => hi.slots 3
         | 3 => hi.slots 4 | _ => hi.slots 4 })
  | 2 => (low, hi)
  | 3 => (low, hi)
  | 4 =>
    ({ cnt := 2, slots := low.slots },
     { cnt := hi.cnt + 1
       slots := fun s => match s.val with
         | 0 => mergeBlock (low.slots 2) (low.slots 3)
         | 1 => hi.slots 0 | 2 => hi.slots 1
         | 3 => hi.slots 2 | _ => hi.slots 3 })
  | _ =>
    ({ cnt := 3, slots := low.slots },
     { cnt := hi.cnt + 1
       slots := fun s => match s.val with
         | 0 => mergeBlock (low.slots 3) (low.slots 4)
         | 1 => hi.slots 0 | 2 => hi.slots 1
         | 3 => hi.slots 2 | _ => hi.slots 3 })

theorem toList_rebalance {i : ℕ} (low : BlockLevel i) (hi : BlockLevel (i + 1))
    (hlow : low.cnt ≤ 5) (hhi1 : 1 ≤ hi.cnt) (hhi2 : hi.cnt ≤ 4) :
    (rebalance low hi).1.toList ++ (rebalance low hi).2.toList =
      low.toList ++ hi.toList := by
  rcases low with ⟨cL, sL⟩
  rcases hi with ⟨cH, sH⟩
  dsimp only at hlow hhi1 hhi2
  have hsp := ofFn_splitBlock (sH 0)
  have hm23 := ofFn_mergeBlock (sL 2) (sL 3)
  have hm34 := ofFn_mergeBlock (sL 3) (sL 4)
  interval_cases cL <;> interval_cases cH <;>
    simp only [rebalance, toList, List.finRange_succ, List.map_cons, List.take_succ_cons,
      List.take_zero, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.nil_append,
      List.append_assoc, Fin.val_zero, Fin.val_succ] <;>
    simp [← hsp, hm23, hm34, List.append_assoc]

theorem rebalance_cnt_low {i : ℕ} (low : BlockLevel i) (hi : BlockLevel (i + 1))
    (hlow : low.cnt ≤ 5) :
    2 ≤ (rebalance low hi).1.cnt ∧ (rebalance low hi).1.cnt ≤ 3 := by
  rcases low with ⟨cL, sL⟩
  dsimp only at hlow
  interval_cases cL <;> simp [rebalance]

theorem rebalance_cnt_hi {i : ℕ} (low : BlockLevel i) (hi : BlockLevel (i + 1))
    (hlow : low.cnt ≤ 5) (_hhi1 : 1 ≤ hi.cnt) (_hhi2 : hi.cnt ≤ 4) :
    hi.cnt - 1 ≤ (rebalance low hi).2.cnt ∧ (rebalance low hi).2.cnt ≤ hi.cnt + 1 := by
  rcases low with ⟨cL, sL⟩
  dsimp only at hlow
  interval_cases cL <;> simp [rebalance] <;> omega


theorem initConst_eq (i : ℕ) (c : BlockCell) : initConst i c = ⟨2, fun _ _ => c⟩ := rfl

theorem push0_eq (c : BlockCell) (lvl : BlockLevel 0) :
    push0 c lvl = { cnt := lvl.cnt + 1, slots := fun s j => match s with
      | ⟨0, _⟩ => c | ⟨1, _⟩ => lvl.slots 0 j | ⟨2, _⟩ => lvl.slots 1 j
      | ⟨3, _⟩ => lvl.slots 2 j | ⟨4, _⟩ => lvl.slots 3 j } := rfl

theorem pop0_eq (lvl : BlockLevel 0) :
    pop0 lvl =
      (lvl.slots 0 0,
        { cnt := lvl.cnt - 1
          slots := fun s j =>
            match s with
            | ⟨0, _⟩ => lvl.slots 1 j
            | ⟨1, _⟩ => lvl.slots 2 j
            | ⟨2, _⟩ => lvl.slots 3 j
            | ⟨3, _⟩ => lvl.slots 4 j
            | ⟨4, _⟩ => lvl.slots 4 j }) := rfl

theorem splitBlock_eq {i : ℕ} (b : Fin (2 ^ (i + 1)) → BlockCell) :
    splitBlock b =
      (fun j => b ⟨j.val, by rw [pow_succ]; omega⟩,
       fun j => b ⟨2 ^ i + j.val, by rw [pow_succ]; omega⟩) := rfl

theorem mergeBlock_eq {i : ℕ} (b0 b1 : Fin (2 ^ i) → BlockCell) :
    mergeBlock b0 b1 =
      fun j =>
        if h : j.val < 2 ^ i then b0 ⟨j.val, h⟩
        else b1 ⟨j.val - 2 ^ i, by rw [pow_succ] at j; omega⟩ := rfl

theorem rebalance_eq {i : ℕ} (low : BlockLevel i) (hi : BlockLevel (i + 1)) :
    rebalance low hi =
      let (h0, h1) := splitBlock (hi.slots 0)
      match low.cnt with
      | 0 =>
        ({ cnt := 2
           slots := fun s => match s.val with
             | 0 => h0 | 1 => h1 | _ => low.slots s },
         { cnt := hi.cnt - 1
           slots := fun s => match s.val with
             | 0 => hi.slots 1 | 1 => hi.slots 2 | 2 => hi.slots 3
             | 3 => hi.slots 4 | _ => hi.slots 4 })
      | 1 =>
        ({ cnt := 3
           slots := fun s => match s.val with
             | 0 => low.slots 0 | 1 => h0 | 2 => h1 | _ => low.slots s },
         { cnt := hi.cnt - 1
           slots := fun s => match s.val with
             | 0 => hi.slots 1 | 1 => hi.slots 2 | 2 => hi.slots 3
             | 3 => hi.slots 4 | _ => hi.slots 4 })
      | 2 => (low, hi)
      | 3 => (low, hi)
      | 4 =>
        ({ cnt := 2, slots := low.slots },
         { cnt := hi.cnt + 1
           slots := fun s => match s.val with
             | 0 => mergeBlock (low.slots 2) (low.slots 3)
             | 1 => hi.slots 0 | 2 => hi.slots 1
             | 3 => hi.slots 2 | _ => hi.slots 3 })
      | _ =>
        ({ cnt := 3, slots := low.slots },
         { cnt := hi.cnt + 1
           slots := fun s => match s.val with
             | 0 => mergeBlock (low.slots 3) (low.slots 4)
             | 1 => hi.slots 0 | 2 => hi.slots 1
             | 3 => hi.slots 2 | _ => hi.slots 3 }) := rfl

end BlockLevel

/-- An `L`-level Pippenger–Fischer half-tape. -/
abbrev BlockHalfTape (L : ℕ) : Type := (i : Fin L) → BlockLevel i.val

namespace BlockHalfTape

/-- Concatenated list of all cells in `h`, from level `0` up to level `L - 1`. -/
def toList {L : ℕ} (h : BlockHalfTape L) : List BlockCell :=
  (List.finRange L).flatMap fun i => (h i).toList

/-- Constant half-tape initialized with `2` blocks of `c` at every level. -/
@[expose] def initConst (L : ℕ) (c : BlockCell) : BlockHalfTape L :=
  fun i => BlockLevel.initConst i.val c

/-- Level-count invariant at time `t`: between rebalances, level `i` stays in `[2, 3]` during
the first half of its `2 ^ (i + 1)` period and in `[1, 4]` during the second half. -/
@[expose] def Inv {L : ℕ} (t : ℕ) (h : BlockHalfTape L) : Prop :=
  ∀ i : Fin L,
    if t % 2 ^ (i.val + 1) < 2 ^ i.val then 2 ≤ (h i).cnt ∧ (h i).cnt ≤ 3
    else 1 ≤ (h i).cnt ∧ (h i).cnt ≤ 4

theorem inv_initConst (L : ℕ) (c : BlockCell) : Inv 0 (initConst L c) := by
  intro i
  simp [initConst, BlockLevel.initConst]

theorem cnt0_of_inv {L : ℕ} (hL : 0 < L) {t : ℕ} {h : BlockHalfTape L} (hinv : Inv t h) :
    1 ≤ (h ⟨0, hL⟩).cnt ∧ (h ⟨0, hL⟩).cnt ≤ 4 := by
  have hi := hinv ⟨0, hL⟩
  split_ifs at hi <;> omega

/-- Apply `push0` at level `0`. -/
@[expose] def push0 {L : ℕ} (_hL : 0 < L) (c : BlockCell) (h : BlockHalfTape L) : BlockHalfTape L :=
  fun i => if hi : i.val = 0 then hi ▸ BlockLevel.push0 c (hi.symm ▸ h i) else h i

/-- Apply `pop0` at level `0`. -/
@[expose] def pop0 {L : ℕ} (hL : 0 < L) (h : BlockHalfTape L) : BlockCell × BlockHalfTape L :=
  let (c, lvl0) := BlockLevel.pop0 (h ⟨0, hL⟩)
  (c, fun i => if hi : i.val = 0 then hi ▸ lvl0 else h i)

theorem toList_push0 {L : ℕ} (hL : 0 < L) (c : BlockCell) (h : BlockHalfTape L)
    (hc : (h ⟨0, hL⟩).cnt ≤ 4) :
    (push0 hL c h).toList = c :: h.toList := by
  cases L with
  | zero => omega
  | succ L' =>
    simp only [toList, List.finRange_succ, List.flatMap_cons, push0, Fin.val_zero, ↓reduceDIte]
    rw [BlockLevel.toList_push0 c (h 0) hc, List.cons_append]
    congr 1; congr 1
    refine List.flatMap_congr fun j hj => ?_
    obtain ⟨j', _, rfl⟩ := List.mem_map.mp hj
    simp

theorem toList_pop0 {L : ℕ} (hL : 0 < L) (h : BlockHalfTape L)
    (hc1 : 1 ≤ (h ⟨0, hL⟩).cnt) (hc2 : (h ⟨0, hL⟩).cnt ≤ 5) :
    h.toList = (pop0 hL h).1 :: (pop0 hL h).2.toList := by
  cases L with
  | zero => omega
  | succ L' =>
    simp only [toList, List.finRange_succ, List.flatMap_cons, pop0, Fin.val_zero, ↓reduceDIte]
    rw [BlockLevel.toList_pop0 (h 0) hc1 hc2, List.cons_append]
    congr 1; congr 1
    refine List.flatMap_congr fun j hj => ?_
    obtain ⟨j', _, rfl⟩ := List.mem_map.mp hj
    simp

/-- Rebalance level `j` with level `j + 1` inside `h`. -/
@[expose] def rebalanceAt {L : ℕ} (j : ℕ) (hj : j +
  1 < L) (h : BlockHalfTape L) : BlockHalfTape L :=
  let p := BlockLevel.rebalance (h ⟨j, Nat.lt_of_succ_lt hj⟩) (h ⟨j + 1, hj⟩)
  fun i =>
    if h1 : i.val = j then h1 ▸ p.1
    else if h2 : i.val = j + 1 then h2 ▸ p.2
    else h i

theorem toList_rebalanceAt {L : ℕ} (j : ℕ) (hj : j + 1 < L) (h : BlockHalfTape L)
    (hlow : (h ⟨j, by omega⟩).cnt ≤ 5)
    (hhi1 : 1 ≤ (h ⟨j + 1, hj⟩).cnt) (hhi2 : (h ⟨j + 1, hj⟩).cnt ≤ 4) :
    (rebalanceAt j hj h).toList = h.toList := by
  have htake : List.finRange L =
      (List.finRange L).take j ++ (⟨j, by omega⟩ :: ⟨j + 1, hj⟩ :: (List.finRange L).drop (j +
        2)) := by
    have hd1 : (List.finRange L).drop j = ⟨j, by omega⟩ :: (List.finRange L).drop (j + 1) := by
      rw [List.drop_eq_getElem_cons (by simp; omega)]; simp
    have hd2 : (List.finRange L).drop (j + 1) = ⟨j + 1, hj⟩ :: (List.finRange L).drop (j + 2) := by
      rw [List.drop_eq_getElem_cons (by simp; omega)]; simp
    calc List.finRange L = (List.finRange L).take j ++ (List.finRange L).drop j :=
          (List.take_append_drop j _).symm
      _ = (List.finRange L).take j ++ (⟨j, by omega⟩ :: ⟨j + 1, hj⟩ ::
            (List.finRange L).drop (j + 2)) := by rw [hd1, hd2]
  simp only [toList]
  conv_lhs => rw [htake]
  conv_rhs => rw [htake]
  simp only [List.flatMap_append, List.flatMap_cons]
  have hpref : ((List.finRange L).take j).flatMap (fun i => (rebalanceAt j hj h i).toList) =
      ((List.finRange L).take j).flatMap (fun i => (h i).toList) := by
    refine List.flatMap_congr fun i hi => ?_
    have hilt : i.val < j := by
      obtain ⟨idx, hidx, hval⟩ := List.mem_iff_getElem.mp hi
      simp only [List.getElem_take, List.getElem_finRange] at hval
      simp only [List.length_take, List.length_finRange] at hidx
      rw [← hval]; dsimp; omega
    simp [rebalanceAt, Nat.ne_of_lt hilt, Nat.ne_of_lt (by omega : i.val < j + 1)]
  have hsuff : ((List.finRange L).drop (j + 2)).flatMap (fun i => (rebalanceAt j hj h i).toList) =
      ((List.finRange L).drop (j + 2)).flatMap (fun i => (h i).toList) := by
    refine List.flatMap_congr fun i hi => ?_
    have higt : j + 2 ≤ i.val := by
      obtain ⟨idx, hidx, hval⟩ := List.mem_iff_getElem.mp hi
      simp only [List.getElem_drop, List.getElem_finRange] at hval
      rw [← hval]; dsimp; omega
    have h1 : i.val ≠ j := by omega
    have h2 : i.val ≠ j + 1 := by omega
    simp [rebalanceAt, h1, h2]
  have hmid : (rebalanceAt j hj h ⟨j, by omega⟩).toList ++
      (rebalanceAt j hj h ⟨j + 1, hj⟩).toList =
      (h ⟨j, by omega⟩).toList ++ (h ⟨j + 1, hj⟩).toList := by
    simp only [rebalanceAt, ↓reduceDIte, show j + 1 ≠ j by omega]
    exact BlockLevel.toList_rebalance _ _ hlow hhi1 hhi2
  rw [hpref, hsuff]
  congr 1
  rw [← List.append_assoc, hmid, List.append_assoc]

/-- Run all scheduled rebalances for step `t → t + 1` in order `j = 0, 1, ..., L - 2`. -/
@[expose] def rebalanceScheduleAux {L : ℕ} (t : ℕ) : (m : ℕ) → m ≤ L - 1 → BlockHalfTape L →
  BlockHalfTape L
  | 0, _, h => h
  | m + 1, hm, h =>
    let h' := rebalanceScheduleAux t m (by omega) h
    if (t + 1) % 2 ^ (m + 1) = 0 then rebalanceAt m (by omega) h' else h'

/-- Oblivious scheduled rebalance at the end of step `t` (moving to time `t + 1`). -/
@[expose] def rebalanceSchedule {L : ℕ} (t : ℕ) (h : BlockHalfTape L) : BlockHalfTape L :=
  rebalanceScheduleAux t (L - 1) le_rfl h

/-- Mid-step invariant after level-0 `±1` and rebalances `0 .. m - 1` at step `t → t + 1`. -/
private def MidInv {L : ℕ} (t m : ℕ) (h : BlockHalfTape L) : Prop :=
  ∀ i : Fin L,
    if i.val < m then
      if (t + 1) % 2 ^ (i.val + 1) < 2 ^ i.val then 2 ≤ (h i).cnt ∧ (h i).cnt ≤ 3
      else 1 ≤ (h i).cnt ∧ (h i).cnt ≤ 4
    else if i.val = m then
      if (t + 1) % 2 ^ m = 0 then
        if (t + 1) % 2 ^ (m + 1) = 0 then (h i).cnt ≤ 5
        else 1 ≤ (h i).cnt ∧ (h i).cnt ≤ 4
      else
        if (t + 1) % 2 ^ (m + 1) < 2 ^ m then 2 ≤ (h i).cnt ∧ (h i).cnt ≤ 3
        else 1 ≤ (h i).cnt ∧ (h i).cnt ≤ 4
    else
      if t % 2 ^ (i.val + 1) < 2 ^ i.val then 2 ≤ (h i).cnt ∧ (h i).cnt ≤ 3
      else 1 ≤ (h i).cnt ∧ (h i).cnt ≤ 4

private lemma mod_two_pow_succ_of_div {t m : ℕ} (hd : (t + 1) % 2 ^ m = 0) :
    (t + 1) % 2 ^ (m + 1) = 0 ∨ (t + 1) % 2 ^ (m + 1) = 2 ^ m := by
  have h1 : 2 ^ m ∣ t + 1 := Nat.dvd_of_mod_eq_zero hd
  rcases h1 with ⟨q, hq⟩
  rw [hq, pow_succ]
  rcases Nat.even_or_odd q with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · left
    have e : 2 ^ m * (k + k) = 2 ^ m * 2 * k := by ring
    rw [e]; exact Nat.mul_mod_right _ _
  · right
    have e : 2 ^ m * (2 * k + 1) = 2 ^ m * 2 * k + 2 ^ m := by ring
    rw [e, Nat.mul_add_mod]
    exact Nat.mod_eq_of_lt (by have := Nat.one_le_two_pow (n := m); omega)

private lemma mod_lt_iff_succ_of_not_div {t m : ℕ} (hnd : (t + 1) % 2 ^ m ≠ 0) :
    ((t + 1) % 2 ^ (m + 1) < 2 ^ m ↔ t % 2 ^ (m + 1) < 2 ^ m) ∧
    (t + 1) % 2 ^ (m + 1) ≠ 0 := by
  have hpos : 0 < 2 ^ m := Nat.one_le_two_pow
  have h2 : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [pow_succ, Nat.mul_comm]
  have hne : (t + 1) % 2 ^ (m + 1) ≠ 0 := by
    intro hz
    have hd : 2 ^ (m + 1) ∣ t + 1 := Nat.dvd_of_mod_eq_zero hz
    have hd' : 2 ^ m ∣ t + 1 := dvd_trans (by rw [h2]; exact dvd_mul_left _ _) hd
    exact hnd (Nat.mod_eq_zero_of_dvd hd')
  refine ⟨?_, hne⟩
  have hstep : (t + 1) % 2 ^ (m + 1) = t % 2 ^ (m + 1) + 1 := by
    have := Nat.mod_add_mod t (2 ^ (m + 1)) 1
    have hlt : t % 2 ^ (m + 1) + 1 < 2 ^ (m + 1) := by
      have hle : t % 2 ^ (m + 1) < 2 ^ (m + 1) := Nat.mod_lt _ (by omega)
      by_contra hge
      have heq : t % 2 ^ (m + 1) + 1 = 2 ^ (m + 1) := by omega
      have : (t + 1) % 2 ^ (m + 1) = 0 := by
        rw [Nat.add_mod, show (1 : ℕ) % 2 ^ (m + 1) = 1 from Nat.mod_eq_of_lt (by omega), heq,
          Nat.mod_self]
      exact hne this
    rw [Nat.add_mod, show (1 : ℕ) % 2 ^ (m + 1) = 1 from Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt hlt]
  have hnot_eq : t % 2 ^ (m + 1) + 1 ≠ 2 ^ m := by
    intro heq
    have hd : 2 ^ m ∣ t + 1 := by
      have hmod := Nat.div_add_mod t (2 ^ (m + 1))
      refine ⟨2 * (t / 2 ^ (m + 1)) + 1, ?_⟩
      have he : 2 ^ m * (2 * (t / 2 ^ (m + 1)) + 1) =
          2 ^ (m + 1) * (t / 2 ^ (m + 1)) + 2 ^ m := by rw [h2]; ring
      omega
    exact hnd (Nat.mod_eq_zero_of_dvd hd)
  omega

private lemma midInv_step {L t m : ℕ} (hm : m + 1 < L) {h : BlockHalfTape L}
    (hmid : MidInv t m h) :
    let h' := if (t + 1) % 2 ^ (m + 1) = 0 then rebalanceAt m hm h else h
    h'.toList = h.toList ∧ MidInv t (m + 1) h' := by
  dsimp only
  split_ifs with hd
  · have hdm : (t + 1) % 2 ^ m = 0 := by
      have hd1 : 2 ^ (m + 1) ∣ t + 1 := Nat.dvd_of_mod_eq_zero hd
      have hd2 : 2 ^ m ∣ t + 1 := dvd_trans (by rw [pow_succ]; exact dvd_mul_right _ _) hd1
      exact Nat.mod_eq_zero_of_dvd hd2
    have hlow : (h ⟨m, by omega⟩).cnt ≤ 5 := by
      have := hmid ⟨m, by omega⟩
      simpa [hdm, hd] using this
    have hhi_mid := hmid ⟨m + 1, hm⟩
    have hhi_t : 1 ≤ (h ⟨m + 1, hm⟩).cnt ∧ (h ⟨m + 1, hm⟩).cnt ≤ 4 := by
      have h1 : ¬ m + 1 < m := by omega
      have h2 : m + 1 ≠ m := by omega
      simp only [h1, h2, ↓reduceIte] at hhi_mid
      split_ifs at hhi_mid <;> omega
    have hlow_new := BlockLevel.rebalance_cnt_low (h ⟨m, by omega⟩) (h ⟨m + 1, hm⟩) hlow
    have hhi_new := BlockLevel.rebalance_cnt_hi (h ⟨m, by omega⟩) (h ⟨m + 1, hm⟩)
      hlow hhi_t.1 hhi_t.2
    refine ⟨toList_rebalanceAt m hm h hlow hhi_t.1 hhi_t.2, fun i => ?_⟩
    rcases i with ⟨iv, hiv⟩
    dsimp only
    by_cases hilt : iv < m
    · have hi1 : iv < m + 1 := by omega
      have hi_ne : iv ≠ m := by omega
      have hi_ne1 : iv ≠ m + 1 := by omega
      have hprev := hmid ⟨iv, hiv⟩
      simp only [hilt, ↓reduceIte] at hprev
      simp only [hi1, ↓reduceIte, rebalanceAt, hi_ne, hi_ne1]
      exact hprev
    · by_cases him : iv = m
      · subst him
        have hi1 : iv < iv + 1 := by omega
        have hpos : 0 < 2 ^ iv := Nat.one_le_two_pow
        simp only [hi1, ↓reduceIte, hd, hpos, rebalanceAt, ↓reduceDIte]
        exact hlow_new
      · by_cases him1 : iv = m + 1
        · subst him1
          have hnlt : ¬ m + 1 < m + 1 := by omega
          have hne : m + 1 ≠ m := by omega
          simp only [hnlt, ↓reduceIte, hd, rebalanceAt, hne, ↓reduceDIte]
          split_ifs with hd2
          · omega
          · have ht_lt : t % 2 ^ (m + 2) < 2 ^ (m + 1) := by
              have hdiv2 := mod_two_pow_succ_of_div hd
              rcases hdiv2 with h0 | hhalf
              · exact absurd h0 hd2
              · have hlt1 : 2 ^ (m + 1) < 2 ^ (m + 2) :=
                  Nat.pow_lt_pow_right (by omega) (by omega)
                have hpos2 : 0 < 2 ^ (m + 2) := Nat.one_le_two_pow
                have h1 : (t + 1) % 2 ^ (m + 2) = (t % 2 ^ (m + 2) + 1) % 2 ^ (m + 2) := by
                  rw [Nat.add_mod, Nat.mod_eq_of_lt (by omega : 1 < 2 ^ (m + 2))]
                have h2 : t % 2 ^ (m + 2) < 2 ^ (m + 2) := Nat.mod_lt _ hpos2
                by_cases hc : t % 2 ^ (m + 2) + 1 < 2 ^ (m + 2)
                · rw [Nat.mod_eq_of_lt hc, hhalf] at h1; omega
                · have : t % 2 ^ (m + 2) + 1 = 2 ^ (m + 2) := by omega
                  rw [this, Nat.mod_self, hhalf] at h1
                  have := Nat.one_le_two_pow (n := m + 1); omega
            have hhi_mid' := hmid ⟨m + 1, hm⟩
            have h1 : ¬ m + 1 < m := by omega
            have h2 : m + 1 ≠ m := by omega
            simp only [h1, h2, ↓reduceIte, ht_lt] at hhi_mid'
            omega
        · have hnlt : ¬ iv < m + 1 := by omega
          have hnlt0 : ¬ iv < m := by omega
          have hprev := hmid ⟨iv, hiv⟩
          simp only [hnlt0, him, ↓reduceIte] at hprev
          simp only [hnlt, him1, ↓reduceIte, rebalanceAt, him]
          exact hprev
  · refine ⟨rfl, fun i => ?_⟩
    rcases i with ⟨iv, hiv⟩
    dsimp only
    by_cases hilt : iv < m
    · have hi1 : iv < m + 1 := by omega
      have hprev := hmid ⟨iv, hiv⟩
      simp only [hilt, ↓reduceIte] at hprev
      simpa only [hi1, ↓reduceIte] using hprev
    · by_cases him : iv = m
      · subst him
        have hi1 : iv < iv + 1 := by omega
        have hprev := hmid ⟨iv, hiv⟩
        simp only [hilt, ↓reduceIte] at hprev
        simp only [hi1, ↓reduceIte]
        by_cases hdm : (t + 1) % 2 ^ iv = 0
        · have hdiv := mod_two_pow_succ_of_div hdm
          rcases hdiv with h0 | hhalf
          · exact absurd h0 hd
          · simp only [hdm, hd, ↓reduceIte] at hprev
            simp only [hhalf, lt_self_iff_false, ↓reduceIte]
            exact hprev
        · simp only [hdm, ↓reduceIte] at hprev
          exact hprev
      · by_cases him1 : iv = m + 1
        · subst him1
          have hnlt : ¬ m + 1 < m + 1 := by omega
          have hprev := hmid ⟨m + 1, hiv⟩
          simp only [hilt, him, ↓reduceIte] at hprev
          simp only [hnlt, ↓reduceIte, hd]
          have hiff := (mod_lt_iff_succ_of_not_div hd).1
          split_ifs at hprev ⊢ <;> omega
        · have hnlt : ¬ iv < m + 1 := by omega
          have hprev := hmid ⟨iv, hiv⟩
          simp only [hilt, him, ↓reduceIte] at hprev
          simpa only [hnlt, him1, ↓reduceIte] using hprev

theorem toList_and_inv_rebalanceSchedule {L t : ℕ} (hL : 0 < L)
    (ht : t + 1 < 2 ^ (L - 1)) {h : BlockHalfTape L}
    (hstep0 :
      (if (t + 1) % 2 = 0 then (h ⟨0, hL⟩).cnt ≤ 5
       else 1 ≤ (h ⟨0, hL⟩).cnt ∧ (h ⟨0, hL⟩).cnt ≤ 4) ∧
      ∀ i : Fin L, i.val ≠ 0 →
        if t % 2 ^ (i.val + 1) < 2 ^ i.val then 2 ≤ (h i).cnt ∧ (h i).cnt ≤ 3
        else 1 ≤ (h i).cnt ∧ (h i).cnt ≤ 4) :
    (rebalanceSchedule t h).toList = h.toList ∧ Inv (t + 1) (rebalanceSchedule t h) := by
  have hmid0 : MidInv t 0 h := by
    rintro ⟨iv, hiv⟩
    dsimp only
    have h0 : ¬ iv < 0 := by omega
    simp only [h0, ↓reduceIte]
    by_cases hi0 : iv = 0
    · subst hi0
      simp only [↓reduceIte, pow_zero, Nat.mod_one]
      exact hstep0.1
    · simp only [hi0, ↓reduceIte]
      exact hstep0.2 ⟨iv, hiv⟩ hi0
  have haux : ∀ m (hm : m ≤ L - 1),
      (rebalanceScheduleAux t m hm h).toList = h.toList ∧
      MidInv t m (rebalanceScheduleAux t m hm h) := by
    intro m
    induction m with
    | zero => intro _; exact ⟨rfl, hmid0⟩
    | succ m ih =>
      intro hm
      obtain ⟨hlist, hmid⟩ := ih (by omega)
      obtain ⟨hlist', hmid'⟩ := midInv_step (by omega : m + 1 < L) hmid
      exact ⟨hlist'.trans hlist, hmid'⟩
  obtain ⟨hlist, hmid⟩ := haux (L - 1) le_rfl
  refine ⟨hlist, fun i => ?_⟩
  change if (t + 1) % 2 ^ (i.val + 1) < 2 ^ i.val then
      2 ≤ (rebalanceScheduleAux t (L - 1) le_rfl h i).cnt ∧
        (rebalanceScheduleAux t (L - 1) le_rfl h i).cnt ≤ 3
    else 1 ≤ (rebalanceScheduleAux t (L - 1) le_rfl h i).cnt ∧
      (rebalanceScheduleAux t (L - 1) le_rfl h i).cnt ≤ 4
  have hfin := hmid i
  rcases i with ⟨iv, hiv⟩
  dsimp only at hfin ⊢
  by_cases hilt : iv < L - 1
  · simpa only [hilt, ↓reduceIte] using hfin
  · have hi_eq : iv = L - 1 := by omega
    subst hi_eq
    have hnd : (t + 1) % 2 ^ (L - 1) ≠ 0 := by rw [Nat.mod_eq_of_lt ht]; omega
    simp only [hilt, ↓reduceIte, hnd] at hfin
    exact hfin

theorem step0_of_inv {L t : ℕ} (hL : 0 < L) {h : BlockHalfTape L} (hinv : h.Inv t) :
    (∀ c : BlockCell,
      (if (t + 1) % 2 = 0 then (push0 hL c h ⟨0, hL⟩).cnt ≤ 5
       else 1 ≤ (push0 hL c h ⟨0, hL⟩).cnt ∧ (push0 hL c h ⟨0, hL⟩).cnt ≤ 4) ∧
      ∀ i : Fin L, i.val ≠ 0 →
        if t % 2 ^ (i.val + 1) < 2 ^ i.val then 2 ≤ (push0 hL c h i).cnt ∧ (push0 hL c h i).cnt ≤ 3
        else 1 ≤ (push0 hL c h i).cnt ∧ (push0 hL c h i).cnt ≤ 4) ∧
    ((if (t + 1) % 2 = 0 then ((pop0 hL h).2 ⟨0, hL⟩).cnt ≤ 5
      else 1 ≤ ((pop0 hL h).2 ⟨0, hL⟩).cnt ∧ ((pop0 hL h).2 ⟨0, hL⟩).cnt ≤ 4) ∧
     ∀ i : Fin L, i.val ≠ 0 →
       if t % 2 ^ (i.val + 1) < 2 ^ i.val then 2 ≤ ((pop0 hL h).2 i).cnt ∧ ((pop0 hL h).2 i).cnt ≤ 3
       else 1 ≤ ((pop0 hL h).2 i).cnt ∧ ((pop0 hL h).2 i).cnt ≤ 4) ∧
    ((if (t + 1) % 2 = 0 then (h ⟨0, hL⟩).cnt ≤ 5
      else 1 ≤ (h ⟨0, hL⟩).cnt ∧ (h ⟨0, hL⟩).cnt ≤ 4) ∧
     ∀ i : Fin L, i.val ≠ 0 →
       if t % 2 ^ (i.val + 1) < 2 ^ i.val then 2 ≤ (h i).cnt ∧ (h i).cnt ≤ 3
       else 1 ≤ (h i).cnt ∧ (h i).cnt ≤ 4) := by
  have h0 := hinv ⟨0, hL⟩
  dsimp only at h0
  have h0_eq : (t % 2 < 1 ↔ (t + 1) % 2 ≠ 0) := by omega
  refine ⟨fun c => ⟨?_, fun i hi => by simpa [push0, hi] using hinv i⟩,
    ⟨?_, fun i hi => by simpa [pop0, hi] using hinv i⟩,
    ⟨?_, fun i _ => hinv i⟩⟩
  · simp only [push0, ↓reduceDIte, BlockLevel.push0]
    split_ifs at h0 ⊢ <;> omega
  · simp only [pop0, ↓reduceDIte, BlockLevel.pop0]
    split_ifs at h0 ⊢ <;> omega
  · split_ifs at h0 ⊢ <;> omega

theorem rebalanceScheduleAux_cnt_bounds {L t : ℕ} (hL : 0 < L) {h : BlockHalfTape L}
    (hstep0 :
      (if (t + 1) % 2 = 0 then (h ⟨0, hL⟩).cnt ≤ 5
       else 1 ≤ (h ⟨0, hL⟩).cnt ∧ (h ⟨0, hL⟩).cnt ≤ 4) ∧
      ∀ i : Fin L, i.val ≠ 0 →
        if t % 2 ^ (i.val + 1) < 2 ^ i.val then 2 ≤ (h i).cnt ∧ (h i).cnt ≤ 3
        else 1 ≤ (h i).cnt ∧ (h i).cnt ≤ 4)
    {m : ℕ} (hm : m + 1 < L) (hdiv : (t + 1) % 2 ^ (m + 1) = 0) :
    let h' := rebalanceScheduleAux t m (by omega) h
    (h' ⟨m, Nat.lt_of_succ_lt hm⟩).cnt ≤ 5 ∧
    1 ≤ (h' ⟨m + 1, hm⟩).cnt ∧ (h' ⟨m + 1, hm⟩).cnt ≤ 4 := by
  have hmid0 : MidInv t 0 h := by
    rintro ⟨iv, hiv⟩; dsimp only
    simp only [Nat.not_lt_zero, ↓reduceIte]
    by_cases hi0 : iv = 0
    · subst hi0; simp only [↓reduceIte, pow_zero, Nat.mod_one]; exact hstep0.1
    · simp only [hi0, ↓reduceIte]; exact hstep0.2 ⟨iv, hiv⟩ hi0
  have hmidm : MidInv t m (rebalanceScheduleAux t m (by omega) h) := by
    have haux : ∀ k (hk : k ≤ L - 1), MidInv t k (rebalanceScheduleAux t k hk h) := by
      intro k
      induction k with
      | zero => intro _; exact hmid0
      | succ k ih => intro hk; exact (midInv_step (by omega) (ih (by omega))).2
    exact haux m (by omega)
  have h1 := hmidm ⟨m, Nat.lt_of_succ_lt hm⟩
  have h2 := hmidm ⟨m + 1, hm⟩
  dsimp only at h1 h2
  have hdm : (t + 1) % 2 ^ m = 0 := by
    have hdvd : 2 ^ m ∣ 2 ^ (m + 1) := ⟨2, by rw [pow_succ]⟩
    exact Nat.dvd_iff_mod_eq_zero.mp (hdvd.trans (Nat.dvd_of_mod_eq_zero hdiv))
  simp only [lt_irrefl, ↓reduceIte, hdm, hdiv] at h1
  simp only [show ¬ (m + 1 < m) by omega, show m + 1 ≠ m by omega, ↓reduceIte] at h2
  refine ⟨h1, ?_⟩
  split_ifs at h2 <;> omega

theorem inv_step0_of_change {L t : ℕ} (hL : 0 < L) {h h' : BlockHalfTape L}
    (hinv : Inv t h)
    (h0 : (h ⟨0, hL⟩).cnt - 1 ≤ (h' ⟨0, hL⟩).cnt ∧ (h' ⟨0, hL⟩).cnt ≤ (h ⟨0, hL⟩).cnt + 1)
    (hrest : ∀ i : Fin L, i.val ≠ 0 → h' i = h i) :
    (if (t + 1) % 2 = 0 then (h' ⟨0, hL⟩).cnt ≤ 5
     else 1 ≤ (h' ⟨0, hL⟩).cnt ∧ (h' ⟨0, hL⟩).cnt ≤ 4) ∧
    ∀ i : Fin L, i.val ≠ 0 →
      if t % 2 ^ (i.val + 1) < 2 ^ i.val then 2 ≤ (h' i).cnt ∧ (h' i).cnt ≤ 3
      else 1 ≤ (h' i).cnt ∧ (h' i).cnt ≤ 4 := by
  refine ⟨?_, fun i hi => by rw [hrest i hi]; exact hinv i⟩
  have hi0 := hinv ⟨0, hL⟩
  simp only [zero_add, pow_zero, pow_one] at hi0
  split_ifs with hmod
  · split_ifs at hi0 <;> omega
  · have ht0 : t % 2 < 1 := by omega
    simp only [ht0, ↓reduceIte] at hi0
    omega

/-- Initialize a right half-tape from a cell-valued function `f : ℕ → BlockCell` (closest first). -/
@[expose] def initFrom (L : ℕ) (f : ℕ → BlockCell) : BlockHalfTape L :=
  fun i =>
    { cnt := 2
      slots := fun s j =>
        f (2 * (2 ^ i.val - 1) + s.val * 2 ^ i.val + j.val) }

theorem inv_initFrom (L : ℕ) (f : ℕ → BlockCell) : Inv 0 (initFrom L f) := by
  intro i
  simp [initFrom]

private lemma toList_initFrom_aux (f : ℕ → BlockCell) :
    ∀ L : ℕ, (initFrom L f).toList = (List.range (2 * (2 ^ L - 1))).map f
  | 0 => by simp [toList, initFrom]
  | L + 1 => by
    have hsplit : List.finRange (L + 1) =
        (List.finRange L).map Fin.castSucc ++ [Fin.last L] := by
      refine List.ext_getElem (by simp) fun k hk1 hk2 => ?_
      by_cases h : k < L
      · rw [List.getElem_append_left (by simpa using h)]; simp
      · rw [List.getElem_append_right (by simp; omega)]
        have hk : k = L := by simp at hk1; omega
        subst hk; simp
        rfl
    simp only [toList, hsplit, List.flatMap_append, List.flatMap_map, List.flatMap_singleton]
    have hpref : (List.finRange L).flatMap (fun x : Fin L => (initFrom (L +
      1) f x.castSucc).toList) =
        (initFrom L f).toList := by
      refine List.flatMap_congr fun x _ => rfl
    rw [hpref, toList_initFrom_aux f L]
    have hlast : (initFrom (L + 1) f (Fin.last L)).toList =
        (List.range (2 * 2 ^ L)).map (fun k => f (2 * (2 ^ L - 1) + k)) := by
      have hsub : ∀ s : Fin 2,
          List.ofFn (fun j : Fin (2 ^ L) =>
            f (2 * (2 ^ L - 1) + s.val * 2 ^ L + j.val)) =
          (List.range (2 ^ L)).map (fun j => f (2 * (2 ^ L - 1) + s.val * 2 ^ L + j)) := by
        intro s
        refine List.ext_getElem (by simp) fun k hk1 hk2 => by simp
      simp only [BlockLevel.toList, initFrom, Fin.val_last, List.finRange_succ, List.map_cons,
        List.take_succ_cons, List.take_zero, List.flatMap_cons, List.flatMap_nil,
        List.append_nil, Fin.val_zero, Fin.val_succ, zero_mul, add_zero, zero_add, one_mul]
      have hs0 := hsub 0
      have hs1 := hsub 1
      simp only [Fin.val_zero, zero_mul, add_zero, Fin.val_one, one_mul] at hs0 hs1
      rw [hs0, hs1]
      have hrange : List.range (2 * 2 ^ L) =
          List.range (2 ^ L) ++ (List.range (2 ^ L)).map (fun j => 2 ^ L + j) := by
        refine List.ext_getElem (by simp; omega) fun k hk1 hk2 => ?_
        by_cases h : k < 2 ^ L
        · rw [List.getElem_append_left (by simpa using h)]; simp
        · rw [List.getElem_append_right (by simp; omega)]; simp; omega
      rw [hrange, List.map_append, List.map_map]
      congr 1
      refine List.map_congr_left fun j _ => ?_
      dsimp; congr 1; omega
    rw [hlast]
    have hpow : 2 * (2 ^ (L + 1) - 1) = 2 * (2 ^ L - 1) + 2 * 2 ^ L := by
      have := Nat.one_le_two_pow (n := L)
      rw [pow_succ]; omega
    rw [hpow, List.range_add, List.map_append, List.map_map]
    rfl

theorem getD_toList_initFrom (L : ℕ) (f : ℕ → BlockCell) (d : BlockCell)
    {k : ℕ} (hk : k < 2 * (2 ^ L - 1)) :
    (initFrom L f).toList.getD k d = f k := by
  rw [toList_initFrom_aux]
  simp [List.getD, hk]

theorem initConst_eq (L : ℕ) (c : BlockCell) :
    initConst L c = fun (i : Fin L) => BlockLevel.initConst i.val c := rfl

theorem push0_eq {L : ℕ} (_hL : 0 < L) (c : BlockCell) (h : BlockHalfTape L) :
    push0 _hL c h = fun i =>
      if hi : i.val = 0 then hi ▸ BlockLevel.push0 c (hi.symm ▸ h i) else h i := rfl

theorem pop0_eq {L : ℕ} (hL : 0 < L) (h : BlockHalfTape L) :
    pop0 hL h =
      let (c, lvl0) := BlockLevel.pop0 (h ⟨0, hL⟩)
      (c, fun i => if hi : i.val = 0 then hi ▸ lvl0 else h i) := rfl

theorem rebalanceAt_eq {L : ℕ} (j : ℕ) (hj : j +
  1 < L) (h : BlockHalfTape L) :
    rebalanceAt j hj h =
      let p := BlockLevel.rebalance (h ⟨j, Nat.lt_of_succ_lt hj⟩) (h ⟨j + 1, hj⟩)
      fun i =>
        if h1 : i.val = j then h1 ▸ p.1
        else if h2 : i.val = j + 1 then h2 ▸ p.2
        else h i := rfl

@[simp] theorem rebalanceScheduleAux_zero {L : ℕ} (t : ℕ) (h0 : 0 ≤ L - 1)
    (h : BlockHalfTape L) : rebalanceScheduleAux t 0 h0 h = h := rfl

@[simp] theorem rebalanceScheduleAux_succ {L : ℕ} (t m : ℕ) (hm : m + 1 ≤ L - 1)
    (h : BlockHalfTape L) :
    rebalanceScheduleAux t (m + 1) hm h =
      let h' := rebalanceScheduleAux t m (by omega) h
      if (t + 1) % 2 ^ (m + 1) = 0 then rebalanceAt m (by omega) h' else h' := rfl

theorem initFrom_eq (L : ℕ) (f : ℕ → BlockCell) :
    initFrom L f =
      fun i =>
        { cnt := 2
          slots := fun s j =>
            f (2 * (2 ^ i.val - 1) + s.val * 2 ^ i.val + j.val) } := rfl

end BlockHalfTape

/-- A bidirectional oblivious block tape: symbol under the head plus left and right half-tapes. -/
@[ext]
structure BlockTape (L : ℕ) where
  /-- Symbol currently under the tape head. -/
  head : BlockCell
  /-- Cells strictly to the left of the head (`pos - 1, pos - 2, ...`). -/
  left : BlockHalfTape L
  /-- Cells strictly to the right of the head (`pos + 1, pos + 2, ...`). -/
  right : BlockHalfTape L

namespace BlockTape

/-- Functional tape contents at integer coordinate `z`, centered at head position `pos`. -/
def toFun {L : ℕ} (bt : BlockTape L) (pos : ℤ) (dL dR : BlockCell) (z : ℤ) : BlockCell :=
  if z = pos then bt.head
  else if z > pos then bt.right.toList.getD (z - pos - 1).toNat dR
  else bt.left.toList.getD (pos - z - 1).toNat dL

/-- Move the tape head by `m : SignType`, writing `w` at the previous head position,
and run the scheduled rebalance for step `t → t + 1`. -/
@[expose] def step {L : ℕ} (hL : 0 < L) (t : ℕ) (w : BlockCell) (m : SignType)
    (bt : BlockTape L) : BlockTape L :=
  let bt' : BlockTape L :=
    match m with
    | .zero => { head := w, left := bt.left, right := bt.right }
    | .pos =>
      let (r0, r') := bt.right.pop0 hL
      { head := r0, left := bt.left.push0 hL w, right := r' }
    | .neg =>
      let (l0, l') := bt.left.pop0 hL
      { head := l0, left := l', right := bt.right.push0 hL w }
  { head := bt'.head
    left := bt'.left.rebalanceSchedule t
    right := bt'.right.rebalanceSchedule t }

/-- Both half-tapes satisfy the level-count invariant at time `t`. -/
@[expose] def Inv {L : ℕ} (t : ℕ) (bt : BlockTape L) : Prop :=
  bt.left.Inv t ∧ bt.right.Inv t

theorem step_correct {L t : ℕ} (hL : 0 < L) (ht : t + 1 < 2 ^ (L - 1))
    (bt : BlockTape L) (hdPos : ℤ) (dL dR w : BlockCell) (m : SignType)
    (hinv : bt.Inv t) :
    let bt' := bt.step hL t w m
    bt'.Inv (t + 1) ∧
    (∀ z : ℤ, bt'.toFun (hdPos + m) dL dR z =
      Function.update (bt.toFun hdPos dL dR) hdPos w z) := by
  have hL0 := BlockHalfTape.cnt0_of_inv hL hinv.1
  have hR0 := BlockHalfTape.cnt0_of_inv hL hinv.2
  cases m with
  | zero =>
    have hL' := BlockHalfTape.toList_and_inv_rebalanceSchedule hL ht
      (BlockHalfTape.inv_step0_of_change hL hinv.1 (by omega) fun _ _ => rfl)
    have hR' := BlockHalfTape.toList_and_inv_rebalanceSchedule hL ht
      (BlockHalfTape.inv_step0_of_change hL hinv.2 (by omega) fun _ _ => rfl)
    refine ⟨⟨hL'.2, hR'.2⟩, fun z => ?_⟩
    have hm0 : ((SignType.zero : SignType).cast : ℤ) = 0 := rfl
    simp only [step, toFun, hL'.1, hR'.1, hm0, add_zero]
    by_cases hz : z = hdPos
    · subst z; simp
    · simp [hz, toFun]
  | pos =>
    have hLstep :
        (if (t + 1) % 2 = 0 then ((bt.left.push0 hL w) ⟨0, hL⟩).cnt ≤ 5
         else 1 ≤ ((bt.left.push0 hL w) ⟨0, hL⟩).cnt ∧ ((bt.left.push0 hL w) ⟨0, hL⟩).cnt ≤ 4) ∧
        ∀ i : Fin L, i.val ≠ 0 → (bt.left.push0 hL w) i = bt.left i := by
      refine ⟨?_, fun i hi => by simp [BlockHalfTape.push0, hi]⟩
      have hcnt : ((bt.left.push0 hL w) ⟨0, hL⟩).cnt = (bt.left ⟨0, hL⟩).cnt + 1 := by
        simp [BlockHalfTape.push0, BlockLevel.push0]
      rw [hcnt]
      have hi0 := hinv.1 ⟨0, hL⟩; simp only [zero_add, pow_zero, pow_one] at hi0
      split_ifs with hmod
      · omega
      · have ht0 : t % 2 < 1 := by omega
        simp only [ht0, ↓reduceIte] at hi0; omega
    have hRstep :
        (if (t + 1) % 2 = 0 then ((bt.right.pop0 hL).2 ⟨0, hL⟩).cnt ≤ 5
         else 1 ≤ ((bt.right.pop0 hL).2 ⟨0, hL⟩).cnt ∧ ((bt.right.pop0 hL).2 ⟨0, hL⟩).cnt ≤ 4) ∧
        ∀ i : Fin L, i.val ≠ 0 → (bt.right.pop0 hL).2 i = bt.right i := by
      refine ⟨?_, fun i hi => by simp [BlockHalfTape.pop0, hi]⟩
      have hcnt : ((bt.right.pop0 hL).2 ⟨0, hL⟩).cnt = (bt.right ⟨0, hL⟩).cnt - 1 := by
        simp [BlockHalfTape.pop0, BlockLevel.pop0]
      rw [hcnt]
      have hi0 := hinv.2 ⟨0, hL⟩; simp only [zero_add, pow_zero, pow_one] at hi0
      split_ifs with hmod
      · omega
      · have ht0 : t % 2 < 1 := by omega
        simp only [ht0, ↓reduceIte] at hi0; omega
    have hL' := BlockHalfTape.toList_and_inv_rebalanceSchedule hL ht
      ⟨hLstep.1, fun i hi => by rw [hLstep.2 i hi]; exact hinv.1 i⟩
    have hR' := BlockHalfTape.toList_and_inv_rebalanceSchedule hL ht
      ⟨hRstep.1, fun i hi => by rw [hRstep.2 i hi]; exact hinv.2 i⟩
    have hLpush := BlockHalfTape.toList_push0 hL w bt.left hL0.2
    have hRpop := BlockHalfTape.toList_pop0 hL bt.right hR0.1 (by omega)
    refine ⟨⟨hL'.2, hR'.2⟩, fun z => ?_⟩
    have hmp : ((SignType.pos : SignType).cast : ℤ) = 1 := rfl
    simp only [step, toFun, hL'.1, hR'.1, hLpush, hmp]
    by_cases hz : z = hdPos
    · subst z
      have h1 : ¬ hdPos = hdPos + 1 := by omega
      have h2 : ¬ hdPos > hdPos + 1 := by omega
      simp [h1, h2]
    · by_cases hz1 : z = hdPos + 1
      · subst z
        simp only [↓reduceIte, Function.update_of_ne hz, toFun, show hdPos + 1 > hdPos by omega]
        rw [hRpop]
        simp
      · simp only [hz1, ↓reduceIte, Function.update_of_ne hz, toFun, hz]
        by_cases hgt : z > hdPos + 1
        · have hgt0 : z > hdPos := by omega
          simp only [hgt, hgt0, ↓reduceIte]
          rw [hRpop]
          have hidx : (z - hdPos - 1).toNat = (z - (hdPos + 1) - 1).toNat + 1 := by omega
          rw [hidx]; simp [List.getD]
        · have hlt0 : ¬ z > hdPos := by omega
          simp only [hgt, hlt0, ↓reduceIte]
          have hidx : (hdPos + 1 - z - 1).toNat = (hdPos - z - 1).toNat + 1 := by omega
          rw [hidx]; simp [List.getD]
  | neg =>
    have hLstep :
        (if (t + 1) % 2 = 0 then ((bt.left.pop0 hL).2 ⟨0, hL⟩).cnt ≤ 5
         else 1 ≤ ((bt.left.pop0 hL).2 ⟨0, hL⟩).cnt ∧ ((bt.left.pop0 hL).2 ⟨0, hL⟩).cnt ≤ 4) ∧
        ∀ i : Fin L, i.val ≠ 0 → (bt.left.pop0 hL).2 i = bt.left i := by
      refine ⟨?_, fun i hi => by simp [BlockHalfTape.pop0, hi]⟩
      have hcnt : ((bt.left.pop0 hL).2 ⟨0, hL⟩).cnt = (bt.left ⟨0, hL⟩).cnt - 1 := by
        simp [BlockHalfTape.pop0, BlockLevel.pop0]
      rw [hcnt]
      have hi0 := hinv.1 ⟨0, hL⟩; simp only [zero_add, pow_zero, pow_one] at hi0
      split_ifs with hmod
      · omega
      · have ht0 : t % 2 < 1 := by omega
        simp only [ht0, ↓reduceIte] at hi0; omega
    have hRstep :
        (if (t + 1) % 2 = 0 then ((bt.right.push0 hL w) ⟨0, hL⟩).cnt ≤ 5
         else 1 ≤ ((bt.right.push0 hL w) ⟨0, hL⟩).cnt ∧ ((bt.right.push0 hL w) ⟨0, hL⟩).cnt ≤ 4) ∧
        ∀ i : Fin L, i.val ≠ 0 → (bt.right.push0 hL w) i = bt.right i := by
      refine ⟨?_, fun i hi => by simp [BlockHalfTape.push0, hi]⟩
      have hcnt : ((bt.right.push0 hL w) ⟨0, hL⟩).cnt = (bt.right ⟨0, hL⟩).cnt + 1 := by
        simp [BlockHalfTape.push0, BlockLevel.push0]
      rw [hcnt]
      have hi0 := hinv.2 ⟨0, hL⟩; simp only [zero_add, pow_zero, pow_one] at hi0
      split_ifs with hmod
      · omega
      · have ht0 : t % 2 < 1 := by omega
        simp only [ht0, ↓reduceIte] at hi0; omega
    have hL' := BlockHalfTape.toList_and_inv_rebalanceSchedule hL ht
      ⟨hLstep.1, fun i hi => by rw [hLstep.2 i hi]; exact hinv.1 i⟩
    have hR' := BlockHalfTape.toList_and_inv_rebalanceSchedule hL ht
      ⟨hRstep.1, fun i hi => by rw [hRstep.2 i hi]; exact hinv.2 i⟩
    have hLpop := BlockHalfTape.toList_pop0 hL bt.left hL0.1 (by omega)
    have hRpush := BlockHalfTape.toList_push0 hL w bt.right hR0.2
    refine ⟨⟨hL'.2, hR'.2⟩, fun z => ?_⟩
    have hmn : ((SignType.neg : SignType).cast : ℤ) = -1 := rfl
    simp only [step, toFun, hL'.1, hR'.1, hRpush, hmn]
    by_cases hz : z = hdPos
    · subst z
      have h1 : ¬ hdPos = hdPos + -1 := by omega
      have h2 : hdPos > hdPos + -1 := by omega
      simp [h1, h2]
    · by_cases hz1 : z = hdPos + -1
      · subst z
        have hgt : ¬ hdPos + -1 > hdPos := by omega
        simp only [↓reduceIte, Function.update_of_ne hz, toFun, hgt]
        rw [hLpop]
        simp
      · simp only [hz1, ↓reduceIte, Function.update_of_ne hz, toFun, hz]
        by_cases hgt : z > hdPos + -1
        · have hgt0 : z > hdPos := by omega
          simp only [hgt, hgt0, ↓reduceIte]
          have hidx : (z - (hdPos + -1) - 1).toNat = (z - hdPos - 1).toNat + 1 := by omega
          rw [hidx]; simp [List.getD]
        · have hlt0 : ¬ z > hdPos := by omega
          simp only [hgt, hlt0, ↓reduceIte]
          rw [hLpop]
          have hidx : (hdPos - z - 1).toNat = (hdPos + -1 - z - 1).toNat + 1 := by omega
          rw [hidx]; simp [List.getD]

theorem step_eq {L : ℕ} (hL : 0 < L) (t : ℕ) (w : BlockCell) (m : SignType)
    (bt : BlockTape L) :
    step hL t w m bt =
      let bt' : BlockTape L :=
        match m with
        | .zero => { head := w, left := bt.left, right := bt.right }
        | .pos =>
          let (r0, r') := bt.right.pop0 hL
          { head := r0, left := bt.left.push0 hL w, right := r' }
        | .neg =>
          let (l0, l') := bt.left.pop0 hL
          { head := l0, left := l', right := bt.right.push0 hL w }
      { head := bt'.head
        left := bt'.left.rebalanceSchedule t
        right := bt'.right.rebalanceSchedule t } := rfl

end BlockTape

/-- Full oblivious simulation state for a deterministic `MultiTapeTM k Bool State`. -/
structure ObliviousCfg (k L : ℕ) (State : Type) where
  /-- Current control state (`none` when halted). -/
  state : Option State
  /-- First-symbol summary of the write-only output tape. -/
  outView : OutView
  /-- Read-only input tape stored as a `BlockTape` with boundary markers. -/
  inputTape : BlockTape L
  /-- `k` bidirectional work tapes stored as `BlockTape`s. -/
  workTapes : Fin k → BlockTape L

namespace ObliviousCfg

/-- Initial oblivious configuration for `tm` on `input : List Bool`. -/
@[expose] def init {k : ℕ} {State : Type} (L : ℕ) (tm : MultiTapeTM k Bool State)
  (input : List Bool) :
    ObliviousCfg k L State where
  state := some tm.q₀
  outView := .empty
  inputTape :=
    { head := BlockCell.inputCell input 1
      left := BlockHalfTape.initConst L BlockCell.leftEnd
      right := BlockHalfTape.initFrom L fun j => BlockCell.inputCell input (2 + j : ℕ) }
  workTapes := fun _ =>
    { head := (false, false)
      left := BlockHalfTape.initConst L (false, false)
      right := BlockHalfTape.initConst L (false, false) }

/-- Effective input-tape head move clamped at the boundary markers. -/
@[expose] def clampInputMove (head : BlockCell) (m : SignType) : SignType :=
  if head = BlockCell.leftEnd ∧ m = .neg then .zero
  else if head = BlockCell.rightEnd ∧ m = .pos then .zero
  else m

/-- One oblivious simulation step at time `t → t + 1`. -/
@[expose] noncomputable def step {k L : ℕ} {State : Type} (hL : 0 < L)
    (tm : MultiTapeTM k Bool State) (t : ℕ) (oc : ObliviousCfg k L State) :
    ObliviousCfg k L State :=
  match oc.state with
  | none =>
    { state := none
      outView := oc.outView
      inputTape := oc.inputTape.step hL t oc.inputTape.head .zero
      workTapes := fun i => (oc.workTapes i).step hL t (oc.workTapes i).head .zero }
  | some q =>
    let a := tm.tr q oc.inputTape.head.toOption (fun i => (oc.workTapes i).head.toOption)
    let mIn := clampInputMove oc.inputTape.head a.inputTape
    { state := a.state
      outView := oc.outView.push a.output
      inputTape := oc.inputTape.step hL t oc.inputTape.head mIn
      workTapes := fun i =>
        let w := match (a.workTapes i).1 with
          | none => (oc.workTapes i).head
          | some s => BlockCell.ofOption s
        (oc.workTapes i).step hL t w (a.workTapes i).2 }

/-- Agreement between an oblivious configuration and a genuine `Turing.Cfg` at time `t`. -/
@[expose] def Agrees {k L : ℕ} {State : Type} {input : List Bool} (t : ℕ)
    (oc : ObliviousCfg k L State) (cfg : Cfg k Bool State input) : Prop :=
  oc.state = cfg.state ∧
  oc.outView = OutView.ofList cfg.output ∧
  oc.inputTape.Inv t ∧
  (∀ z : ℤ, oc.inputTape.toFun cfg.inputPos.val BlockCell.leftEnd BlockCell.rightEnd z =
    BlockCell.inputCell input z) ∧
  (∀ i : Fin k, (oc.workTapes i).Inv t) ∧
  (∀ (i : Fin k) (z : ℤ),
    ((oc.workTapes i).toFun (cfg.workTapePos i) (false, false) (false, false) z).toOption =
      cfg.workTapes i z)

theorem init_agrees {k L : ℕ} {State : Type} (tm : MultiTapeTM k Bool State)
    (input : List Bool) (hLN : input.length + 2 < 2 * (2 ^ L - 1)) :
    Agrees 0 (init L tm input) (tm.initCfg input) := by
  refine ⟨rfl, rfl,
    ⟨BlockHalfTape.inv_initConst _ _, BlockHalfTape.inv_initFrom _ _⟩,
    fun z => ?_,
    fun _ => ⟨BlockHalfTape.inv_initConst _ _, BlockHalfTape.inv_initConst _ _⟩,
    fun i z => ?_⟩
  · have hpos1 : (1 : Fin (input.length + 2)).val = 1 := by simp
    simp only [init, BlockTape.toFun, MultiTapeNTM.initCfg, Cfg.init, hpos1, Nat.cast_one]
    by_cases hz1 : z = 1
    · subst z; simp
    · by_cases hgt : z > 1
      · simp only [hz1, hgt, ↓reduceIte]
        by_cases hlt : (z - 1 - 1).toNat < 2 * (2 ^ L - 1)
        · rw [BlockHalfTape.getD_toList_initFrom L _ _ hlt]
          congr 1; omega
        · have hbig : (input.length : ℤ) + 1 ≤ z := by omega
          have h1 : ¬ z ≤ 0 := by omega
          have h2 : ¬ z.toNat - 1 < input.length := by omega
          rw [BlockHalfTape.toList_initFrom_aux]
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]
          simp [BlockCell.inputCell, h1, h2]
      · simp only [hz1, hgt, ↓reduceIte]
        have hle0 : z ≤ 0 := by omega
        have hget : ∀ (m : ℕ), (List.replicate m BlockCell.leftEnd).getD (1 - z - 1).toNat
            BlockCell.leftEnd = BlockCell.leftEnd := fun m => by
          rw [List.getD_eq_getElem?_getD, List.getElem?_replicate]
          split_ifs <;> rfl
        have hcon : (BlockHalfTape.initConst L BlockCell.leftEnd).toList =
            List.replicate (2 * (2 ^ L - 1)) BlockCell.leftEnd := by
          have : (BlockHalfTape.initConst L BlockCell.leftEnd).toList =
              (BlockHalfTape.initFrom L fun _ => BlockCell.leftEnd).toList := rfl
          rw [this, BlockHalfTape.toList_initFrom_aux]
          simp
        rw [hcon, hget]; simp [BlockCell.inputCell, hle0]
  · simp only [init, BlockTape.toFun, MultiTapeNTM.initCfg, Cfg.init]
    have hcon : (BlockHalfTape.initConst L (false, false)).toList =
        List.replicate (2 * (2 ^ L - 1)) (false, false) := by
      have : (BlockHalfTape.initConst L (false, false)).toList =
          (BlockHalfTape.initFrom L fun _ => (false, false)).toList := rfl
      rw [this, BlockHalfTape.toList_initFrom_aux]
      simp
    rw [hcon]
    by_cases hz : z = 0
    · subst z; rfl
    · by_cases hgt : z > 0
      · simp only [hz, hgt, ↓reduceIte, List.getD_eq_getElem?_getD, List.getElem?_replicate]
        split_ifs <;> rfl
      · simp only [hz, hgt, ↓reduceIte, List.getD_eq_getElem?_getD, List.getElem?_replicate]
        split_ifs <;> rfl

private lemma clampInputMove_eq (input : List Bool) (pos : Fin (input.length + 2))
    (m : SignType) :
    ((pos.val : ℤ) + (clampInputMove (BlockCell.inputCell input pos.val) m).cast : ℤ) =
      (moveInputPos pos m).val := by
  rw [val_moveInputPos_eq]
  have hpos : (pos.val : ℤ) ≤ input.length + 1 := by omega
  have hmn : ((SignType.neg : SignType).cast : ℤ) = -1 := rfl
  have hmz : ((SignType.zero : SignType).cast : ℤ) = 0 := rfl
  have hmp : ((SignType.pos : SignType).cast : ℤ) = 1 := rfl
  cases m with
  | zero =>
    simp only [clampInputMove, show SignType.zero ≠ .neg by decide,
      show SignType.zero ≠ .pos by decide, and_false, ↓reduceIte, hmz]; omega
  | neg =>
    simp only [clampInputMove]
    by_cases h0 : pos.val = 0
    · have hc : BlockCell.inputCell input pos.val = BlockCell.leftEnd := by
        rw [h0, Nat.cast_zero]; exact BlockCell.inputCell_zero input
      rw [hc]
      simp only [true_and, ↓reduceIte, h0, Nat.cast_zero, hmz, hmn]; omega
    · have hc : BlockCell.inputCell input pos.val ≠ BlockCell.leftEnd := by
        have h1 : ¬ (pos.val : ℤ) ≤ 0 := by omega
        by_cases h2 : pos.val - 1 < input.length
        · simp [BlockCell.inputCell, h0, h2, BlockCell.leftEnd]
        · simp [BlockCell.inputCell, h0, h2, BlockCell.leftEnd, BlockCell.rightEnd]
      simp only [hc, false_and, ↓reduceIte, show SignType.neg ≠ .pos by decide, and_false, hmn]
      omega
  | pos =>
    simp only [clampInputMove, show SignType.pos ≠ .neg by decide, and_false, ↓reduceIte]
    by_cases he : pos.val = input.length + 1
    · have hc : BlockCell.inputCell input pos.val = BlockCell.rightEnd := by
        rw [he]; exact BlockCell.inputCell_end input
      rw [hc]
      simp only [true_and, ↓reduceIte, he, Nat.cast_add, Nat.cast_one, hmz, hmp]; omega
    · have hc : BlockCell.inputCell input pos.val ≠ BlockCell.rightEnd := by
        by_cases h0 : pos.val = 0
        · simp [h0, BlockCell.inputCell_zero, BlockCell.leftEnd, BlockCell.rightEnd]
        · have hlt : pos.val - 1 < input.length := by omega
          simp [BlockCell.inputCell, h0, hlt, BlockCell.rightEnd]
      simp only [hc, false_and, ↓reduceIte, hmp]; omega

theorem step_agrees {k L t : ℕ} {State : Type} {input : List Bool}
    (hL : 0 < L) (ht : t + 1 < 2 ^ (L - 1))
    (tm : MultiTapeTM k Bool State) {oc : ObliviousCfg k L State}
    {cfg : Cfg k Bool State input} (hag : Agrees t oc cfg) :
    Agrees (t + 1) (oc.step hL tm t) (tm.step cfg) := by
  rcases hag with ⟨hstate, hout, hin_inv, hin_fun, hwk_inv, hwk_fun⟩
  cases hcfg : cfg.state with
  | none =>
    have htm_s : tm.step cfg = cfg := MultiTapeTM.step_of_halt hcfg
    rw [htm_s]
    have hoc_s : oc.state = none := hstate.trans hcfg
    simp only [step, hoc_s]
    have hI := BlockTape.step_correct hL ht oc.inputTape cfg.inputPos.val
      BlockCell.leftEnd BlockCell.rightEnd oc.inputTape.head .zero hin_inv
    have hW := fun i => BlockTape.step_correct hL ht (oc.workTapes i) (cfg.workTapePos i)
      (false, false) (false, false) (oc.workTapes i).head .zero (hwk_inv i)
    have hmz : ((SignType.zero : SignType).cast : ℤ) = 0 := rfl
    refine ⟨hcfg.symm, hout, hI.1, fun z => ?_, fun i => (hW i).1, fun i z => ?_⟩
    · have := hI.2 z; simp only [hmz, add_zero] at this
      rw [this]
      by_cases hz : z = cfg.inputPos.val
      · subst z; rw [Function.update_self]; simpa [BlockTape.toFun] using hin_fun cfg.inputPos.val
      · rw [Function.update_of_ne hz]; exact hin_fun z
    · have := (hW i).2 z; simp only [hmz, add_zero] at this
      rw [this]
      by_cases hz : z = cfg.workTapePos i
      · subst z; rw [Function.update_self]
        simpa [BlockTape.toFun] using hwk_fun i (cfg.workTapePos i)
      · rw [Function.update_of_ne hz]; exact hwk_fun i z
  | some q =>
    have htm_s : tm.step cfg = (tm.tr q cfg.inputSymbol cfg.workTapeSymbols).apply cfg :=
      MultiTapeTM.step_of_state hcfg
    rw [htm_s]
    have hoc_s : oc.state = some q := hstate.trans hcfg
    have hhead_in : oc.inputTape.head = BlockCell.inputCell input cfg.inputPos.val := by
      simpa [BlockTape.toFun] using hin_fun cfg.inputPos.val
    have hsym_in : oc.inputTape.head.toOption = cfg.inputSymbol := by
      rw [hhead_in]
      by_cases h0 : cfg.inputPos.val = 0
      · rw [h0, Nat.cast_zero, BlockCell.inputCell_zero, BlockCell.toOption_leftEnd]
        exact (inputSymbol_eq_none_of_boundary (Or.inl h0)).symm
      · by_cases he : cfg.inputPos.val = input.length + 1
        · rw [he, BlockCell.inputCell_end, BlockCell.toOption_rightEnd]
          exact (inputSymbol_eq_none_of_boundary (Or.inr he)).symm
        · have hp : cfg.inputPos.val - 1 < input.length := by omega
          have h1 : cfg.inputPos.val = 1 + (cfg.inputPos.val - 1) := by omega
          rw [h1, BlockCell.toOption_inputCell_pos input hp,
            inputSymbolInner (cfg.inputPos.val - 1) h1 hp]
    have hsym_wk : (fun i => (oc.workTapes i).head.toOption) = cfg.workTapeSymbols := by
      funext i
      simpa [BlockTape.toFun, Cfg.workTapeSymbols] using hwk_fun i (cfg.workTapePos i)
    simp only [step, hoc_s, hsym_in, hsym_wk]
    set a := tm.tr q cfg.inputSymbol cfg.workTapeSymbols
    have hI := BlockTape.step_correct hL ht oc.inputTape cfg.inputPos.val
      BlockCell.leftEnd BlockCell.rightEnd oc.inputTape.head
      (clampInputMove oc.inputTape.head a.inputTape) hin_inv
    have hW := fun i => BlockTape.step_correct hL ht (oc.workTapes i) (cfg.workTapePos i)
      (false, false) (false, false)
      (match (a.workTapes i).1 with
        | none => (oc.workTapes i).head
        | some s => BlockCell.ofOption s)
      (a.workTapes i).2 (hwk_inv i)
    refine ⟨rfl, ?_, hI.1, fun z => ?_, fun i => (hW i).1, fun i z => ?_⟩
    · simp only [Action.apply, hout, OutView.ofList_append_toList]
    · simp only [Action.apply]
      rw [← clampInputMove_eq input cfg.inputPos a.inputTape, ← hhead_in]
      rw [hI.2 z]
      by_cases hz : z = cfg.inputPos.val
      · subst z; rw [Function.update_self, hhead_in]
      · rw [Function.update_of_ne hz]; exact hin_fun z
    · simp only [Action.apply]
      rw [(hW i).2 z]
      by_cases hz : z = cfg.workTapePos i
      · subst z; rw [Function.update_self]
        cases hwr : (a.workTapes i).1 with
        | none =>
          simpa [BlockTape.toFun] using hwk_fun i (cfg.workTapePos i)
        | some s =>
          simp [BlockCell.toOption_ofOption]
      · rw [Function.update_of_ne hz]
        cases (a.workTapes i).1 <;> simp [Function.update_of_ne hz, hwk_fun i z]

theorem run_agrees {k L T : ℕ} {State : Type} (tm : MultiTapeTM k Bool State)
    (input : List Bool) (hL : 0 < L) (hT : T < 2 ^ (L - 1))
    (hLN : input.length + 2 < 2 * (2 ^ L - 1)) :
    ∀ t ≤ T,
      Agrees t
        ((List.range t).foldl (fun oc s => oc.step hL tm s) (init L tm input))
        (tm.runFrom (tm.initCfg input) t) := by
  intro t ht
  induction t with
  | zero => exact init_agrees tm input hLN
  | succ t ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hrun : tm.runFrom (tm.initCfg input) (t + 1) =
        tm.step (tm.runFrom (tm.initCfg input) t) :=
      Function.iterate_succ_apply' tm.step t (tm.initCfg input)
    rw [hrun]
    exact step_agrees hL (by omega) tm (ih (by omega))

theorem init_eq {k : ℕ} {State : Type} (L : ℕ) (tm : MultiTapeTM k Bool State)
    (input : List Bool) :
    init L tm input = {
      state := some tm.q₀
      outView := .empty
      inputTape :=
        { head := BlockCell.inputCell input 1
          left := BlockHalfTape.initConst L BlockCell.leftEnd
          right := BlockHalfTape.initFrom L fun j => BlockCell.inputCell input (2 + j : ℕ) }
      workTapes := fun _ =>
        { head := (false, false)
          left := BlockHalfTape.initConst L (false, false)
          right := BlockHalfTape.initConst L (false, false) } } := rfl

theorem step_eq {k L : ℕ} {State : Type} (hL : 0 < L)
    (tm : MultiTapeTM k Bool State) (t : ℕ) (oc : ObliviousCfg k L State) :
    step hL tm t oc =
      match oc.state with
      | none =>
        { state := none
          outView := oc.outView
          inputTape := oc.inputTape.step hL t oc.inputTape.head .zero
          workTapes := fun i => (oc.workTapes i).step hL t (oc.workTapes i).head .zero }
      | some q =>
        let a := tm.tr q oc.inputTape.head.toOption (fun i => (oc.workTapes i).head.toOption)
        let mIn := clampInputMove oc.inputTape.head a.inputTape
        { state := a.state
          outView := oc.outView.push a.output
          inputTape := oc.inputTape.step hL t oc.inputTape.head mIn
          workTapes := fun i =>
            let w := match (a.workTapes i).1 with
              | none => (oc.workTapes i).head
              | some s => BlockCell.ofOption s
            (oc.workTapes i).step hL t w (a.workTapes i).2 } := rfl

end ObliviousCfg

end CslibFrontier.Computability.Circuit

