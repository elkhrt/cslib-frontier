module


public import CslibFrontier.Computability.Circuit.Boolean.MachineSimulation
import CslibFrontier.Computability.Machines.Turing.MultiTape.Run
import Mathlib.Data.Nat.Log

/-!
# Oblivious 5-slot block-buffer stack hierarchy for Pippenger–Fischer simulation

Implements the functional 5-slot oblivious block-buffer stack hierarchy (`LevelData`, `BlockStack`,
`ZipperTape`, `ObliviousCfg`) simulating any `MultiTapeTM k Bool State` with oblivious head-free
rebalancing schedule `2 ^ j ∣ t`, together with the exact simulation invariant `MatchesCfg` and
capped output-prefix summary `OutCap`.

## Main definitions

* `OutCap`: capped output-tape summary recording the first `m` output bits and length up to `m + 1`.
* `PippengerFischer.LevelData`, `PippengerFischer.BlockStack`, `PippengerFischer.ZipperTape`,
  `PippengerFischer.ObliviousCfg`: oblivious 5-slot hierarchical tape data structures.
* `PippengerFischer.runOblivious`: oblivious step-and-rebalance simulation of a `MultiTapeTM`.

## Main results

* `PippengerFischer.matchesCfg_runOblivious`: `runOblivious` agrees with `MultiTapeTM.runFrom` on
  control state, capped output prefix, and every reachable tape cell for all `t < 2 ^ (L - 1)`.
-/

public section

namespace CslibFrontier.Computability.Circuit.Boolean

open Cslib Cslib.Circuits Cslib.Circuits.Boolean Turing Turing.MultiTapeTM Finset

private theorem getD_eq_getElem' {α : Type*} (l : List α) (d : α) {i : ℕ} (hi : i < l.length) :
    l.getD i d = l[i] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]

private theorem getD_eq_default' {α : Type*} (l : List α) (d : α) {i : ℕ} (hi : l.length ≤ i) :
    l.getD i d = d := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi, Option.getD_none]

/-! ### Capped output summary -/

/-- Summary of an append-only output tape up to its first `m` bits. -/
@[ext]
structure OutCap (m : ℕ) where
  /-- Length of the output capped at `m + 1` (`m + 1` means strictly longer than `m`). -/
  len : Fin (m + 2)
  /-- First `m` emitted bits (defaulting to `false` beyond the actual length). -/
  bits : Fin m → Bool
  deriving DecidableEq

namespace OutCap

/-- Summarize a bit list into `OutCap m`. -/
@[expose] def ofList (m : ℕ) (l : List Bool) : OutCap m where
  len := ⟨min (m + 1) l.length, by omega⟩
  bits i := l.getD i.val false

/-- The capped length field of `OutCap.ofList m l`. -/
@[simp] theorem ofList_len (m : ℕ) (l : List Bool) :
    (ofList m l).len = ⟨min (m + 1) l.length, by omega⟩ := rfl

/-- The `i`-th bit field of `OutCap.ofList m l`. -/
@[simp] theorem ofList_bits (m : ℕ) (l : List Bool) (i : Fin m) :
    (ofList m l).bits i = l.getD i.val false := rfl

/-- Update `OutCap m` when emitting an optional bit. -/
@[expose] def push {m : ℕ} (o : OutCap m) : Option Bool → OutCap m
  | none => o
  | some b =>
    { len := ⟨min (m + 1) (o.len.val + 1), by omega⟩
      bits := fun i => if i.val = o.len.val then b else o.bits i }

/-- Summarizing the empty list gives length `0` and all `false` bits. -/
theorem ofList_nil (m : ℕ) : ofList m [] = ⟨⟨0, by omega⟩, fun _ => false⟩ := by
  ext <;> simp [ofList]

/-- Appending an optional emitted bit updates `OutCap.ofList` via `OutCap.push`. -/
theorem ofList_append_toList (m : ℕ) (l : List Bool) (b : Option Bool) :
    ofList m (l ++ b.toList) = (ofList m l).push b := by
  rcases b with _ | b
  · simp [push]
  · ext
    · simp only [ofList, push, Option.toList, List.length_append, List.length_singleton]
      omega
    · rename_i i
      simp only [ofList, push, Option.toList]
      by_cases hi : i.val < l.length
      · have hne : i.val ≠ min (m + 1) l.length := by have := i.isLt; omega
        simp only [hne, ↓reduceIte]
        rw [getD_eq_getElem' _ _ (by simp; omega),
          List.getElem_append_left hi, getD_eq_getElem' _ _ hi]
      · by_cases heq : i.val = l.length
        · have hmin : i.val = min (m + 1) l.length := by have := i.isLt; omega
          simp only [hmin, ↓reduceIte]
          rw [getD_eq_getElem' _ _ (by rw [List.length_append, List.length_singleton]; omega),
            List.getElem_append_right (by omega)]
          simp
        · have hne : i.val ≠ min (m + 1) l.length := by have := i.isLt; omega
          simp only [hne, ↓reduceIte]
          rw [getD_eq_default' _ _ (by simp; omega), getD_eq_default' _ _ (by omega)]

end OutCap

/-! ### Oblivious 5-slot block stack -/

namespace PippengerFischer

/-- Two-bit encoding of a tape cell (`(false, false)` is blank / left endmarker, `(false, true)` is
right endmarker on the input tape, and `(true, b)` is symbol `some b`). -/
abbrev Cell : Type := Bool × Bool

/-- Blank tape cell `(false, false)`. -/
abbrev blankCell : Cell := (false, false)

/-- One level `j` of a hierarchical stack: `cnt ∈ {0, ..., 5}` active blocks of length `2 ^ j`,
stored in `slots 0, ..., slots (cnt - 1)` from top to bottom. -/
structure LevelData (j : ℕ) where
  /-- Number of currently active blocks at level `j` (`0` through `5`). -/
  cnt : Fin 6
  /-- Five fixed slots, each holding a block of `2 ^ j` cells. -/
  slots : Fin 5 → Fin (2 ^ j) → Cell

/-- Flatten the active blocks of level `j` in order `0, ..., cnt - 1`. -/
def LevelData.toList {j : ℕ} (lv : LevelData j) : List Cell :=
  ((List.finRange 5).take lv.cnt.val).flatMap fun r => List.ofFn (lv.slots r)

/-- Split a block of size `2 ^ (j + 1)` into its lower and upper halves of size `2 ^ j`. -/
@[expose] def splitBlock {j : ℕ} (B : Fin (2 ^ (j + 1)) → Cell) :
    (Fin (2 ^ j) → Cell) × (Fin (2 ^ j) → Cell) :=
  (fun i => B ⟨i.val, by rw [pow_succ]; omega⟩,
   fun i => B ⟨2 ^ j + i.val, by rw [pow_succ]; omega⟩)

/-- Merge two blocks of size `2 ^ j` into a single block of size `2 ^ (j + 1)`. -/
@[expose] def mergeBlocks {j : ℕ} (A B : Fin (2 ^ j) → Cell) : Fin (2 ^ (j + 1)) → Cell :=
  fun i =>
    if h : i.val < 2 ^ j then A ⟨i.val, h⟩
    else B ⟨i.val - 2 ^ j, by
      have hi : i.val < 2 ^ j * 2 := by simpa [pow_succ] using i.isLt
      omega⟩

private theorem splitBlock_mergeBlocks {j : ℕ} (A B : Fin (2 ^ j) → Cell) :
    splitBlock (mergeBlocks A B) = (A, B) := by
  ext i <;> simp [splitBlock, mergeBlocks]

private theorem ofFn_splitBlock {j : ℕ} (B : Fin (2 ^ (j + 1)) → Cell) :
    List.ofFn B = List.ofFn (splitBlock B).1 ++ List.ofFn (splitBlock B).2 := by
  refine List.ext_getElem (by simp [pow_succ]; omega) fun k hk1 hk2 => ?_
  rw [List.length_ofFn] at hk1
  rw [List.getElem_ofFn]
  by_cases hk : k < 2 ^ j
  · rw [List.getElem_append_left (by simpa using hk), List.getElem_ofFn]; rfl
  · rw [List.getElem_append_right (by simp; omega), List.getElem_ofFn]
    simp only [splitBlock, List.length_ofFn]
    congr 1; apply Fin.ext; dsimp only; omega

/-- Top cell of level `0`. -/
@[expose] def LevelData.top0 (lv : LevelData 0) : Cell :=
  lv.slots 0 ⟨0, by norm_num⟩

/-- Push one cell onto level `0`, shifting slots `0..3` down to `1..4`. -/
@[expose] def LevelData.push0 (c : Cell) (lv : LevelData 0) : LevelData 0 where
  cnt := ⟨min 5 (lv.cnt.val + 1), by omega⟩
  slots r :=
    if r.val = 0 then fun _ => c
    else lv.slots ⟨r.val - 1, by omega⟩

/-- Pop the top cell from level `0`, shifting slots `1..4` up to `0..3`. -/
@[expose] def LevelData.pop0 (lv : LevelData 0) : LevelData 0 where
  cnt := ⟨lv.cnt.val - 1, by omega⟩
  slots r :=
    if h : r.val + 1 < 5 then lv.slots ⟨r.val + 1, h⟩
    else fun _ => blankCell

private theorem LevelData.toList_push0 (c : Cell) (lv : LevelData 0) (hc : lv.cnt.val ≤ 4) :
    (lv.push0 c).toList = c :: lv.toList := by
  rcases lv with ⟨⟨cnt, hlt⟩, slots⟩
  dsimp only at hc
  have h5 : cnt = 0 ∨ cnt = 1 ∨ cnt = 2 ∨ cnt = 3 ∨ cnt = 4 := by omega
  rcases h5 with rfl | rfl | rfl | rfl | rfl <;>
    simp [LevelData.toList, LevelData.push0, List.finRange_succ]

private theorem LevelData.toList_pop0 (lv : LevelData 0) (hc : 1 ≤ lv.cnt.val) :
    lv.toList = lv.top0 :: lv.pop0.toList := by
  rcases lv with ⟨⟨cnt, hlt⟩, slots⟩
  dsimp only at hc
  have h5 : cnt = 1 ∨ cnt = 2 ∨ cnt = 3 ∨ cnt = 4 ∨ cnt = 5 := by omega
  rcases h5 with rfl | rfl | rfl | rfl | rfl <;>
    simp [LevelData.toList, LevelData.pop0, LevelData.top0, List.finRange_succ]

/-- Rebalance level `j` against level `j + 1`:
- if `lv.cnt ≤ 1`, borrow the top block of `hi`, split into two blocks, append to `lv`;
- if `lv.cnt ≥ 4`, merge the bottom two blocks of `lv` and push onto top of `hi`;
- otherwise leave both levels unchanged. -/
@[expose] def rebalancePair {j : ℕ} (lv : LevelData j) (hi : LevelData (j + 1)) :
    LevelData j × LevelData (j + 1) :=
  let (A, B) := splitBlock (hi.slots 0)
  if hle1 : lv.cnt.val ≤ 1 then
    let lv' : LevelData j :=
      { cnt := ⟨lv.cnt.val + 2, by omega⟩
        slots := fun r =>
          if r.val = 0 then (if lv.cnt.val = 0 then A else lv.slots 0)
          else if r.val = 1 then (if lv.cnt.val = 0 then B else A)
          else if r.val = 2 then (if lv.cnt.val = 1 then B else lv.slots 2)
          else lv.slots r }
    let hi' : LevelData (j + 1) :=
      { cnt := ⟨hi.cnt.val - 1, by omega⟩
        slots := fun r =>
          if h : r.val + 1 < 5 then hi.slots ⟨r.val + 1, h⟩ else fun _ => blankCell }
    (lv', hi')
  else if hge4 : 4 ≤ lv.cnt.val then
    let M :=
      if lv.cnt.val = 4 then mergeBlocks (lv.slots 2) (lv.slots 3)
      else mergeBlocks (lv.slots 3) (lv.slots 4)
    let lv' : LevelData j :=
      { cnt := ⟨lv.cnt.val - 2, by omega⟩
        slots := lv.slots }
    let hi' : LevelData (j + 1) :=
      { cnt := ⟨min 5 (hi.cnt.val + 1), by omega⟩
        slots := fun r =>
          if r.val = 0 then M else hi.slots ⟨r.val - 1, by omega⟩ }
    (lv', hi')
  else
    (lv, hi)

/-- Pointwise formula for `(rebalancePair lv hi).2.slots 0 idx` when `idx < 2 ^ j`. -/
theorem rebalancePair_snd_slot0_lt {j : ℕ} (lv : LevelData j) (hi : LevelData (j + 1))
    (idx : Fin (2 ^ (j + 1))) (hidx : idx.val < 2 ^ j) :
    (rebalancePair lv hi).2.slots 0 idx =
      if lv.cnt.val ≤ 1 then hi.slots 1 idx
      else if 4 ≤ lv.cnt.val then
        if lv.cnt.val = 4 then lv.slots 2 ⟨idx.val, hidx⟩ else lv.slots 3 ⟨idx.val, hidx⟩
      else hi.slots 0 idx := by
  unfold rebalancePair
  by_cases h1 : lv.cnt.val ≤ 1
  · simp [h1]
  · by_cases h4 : 4 ≤ lv.cnt.val
    · by_cases heq4 : lv.cnt.val = 4 <;> simp [h1, h4, heq4, mergeBlocks, hidx]
    · simp [h1, h4]

/-- Pointwise formula for `(rebalancePair lv hi).2.slots 0 idx` when `idx ≥ 2 ^ j`. -/
theorem rebalancePair_snd_slot0_ge {j : ℕ} (lv : LevelData j) (hi : LevelData (j + 1))
    (idx : Fin (2 ^ (j + 1))) (hidx : ¬ idx.val < 2 ^ j)
    (hidx' : idx.val - 2 ^ j < 2 ^ j) :
    (rebalancePair lv hi).2.slots 0 idx =
      if lv.cnt.val ≤ 1 then hi.slots 1 idx
      else if 4 ≤ lv.cnt.val then
        if lv.cnt.val = 4 then lv.slots 3 ⟨idx.val - 2 ^ j, hidx'⟩
        else lv.slots 4 ⟨idx.val - 2 ^ j, hidx'⟩
      else hi.slots 0 idx := by
  unfold rebalancePair
  by_cases h1 : lv.cnt.val ≤ 1
  · simp [h1]
  · by_cases h4 : 4 ≤ lv.cnt.val
    · by_cases heq4 : lv.cnt.val = 4 <;> simp [h1, h4, heq4, mergeBlocks, hidx]
    · simp [h1, h4]

/-- Pointwise formula for `(rebalancePair lv hi).2.slots r idx` for `r = 1, 2, 3, 4`. -/
theorem rebalancePair_snd_slot_pos {j : ℕ} (lv : LevelData j) (hi : LevelData (j + 1))
    (r : Fin 5) (hr : 0 < r.val) (idx : Fin (2 ^ (j + 1))) :
    (rebalancePair lv hi).2.slots r idx =
      if lv.cnt.val ≤ 1 then
        if h : r.val + 1 < 5 then hi.slots ⟨r.val + 1, h⟩ idx else blankCell
      else if 4 ≤ lv.cnt.val then hi.slots ⟨r.val - 1, by omega⟩ idx
      else hi.slots r idx := by
  unfold rebalancePair
  by_cases h1 : lv.cnt.val ≤ 1
  · simp only [h1, ↓reduceDIte]
    split_ifs <;> rfl
  · by_cases h4 : 4 ≤ lv.cnt.val
    · have hr0 : r ≠ 0 := fun h => by rw [h] at hr; exact Nat.lt_irrefl 0 hr
      simp [h1, h4, hr0]
    · simp [h1, h4]

private theorem rebalancePair_toList {j : ℕ} (lv : LevelData j) (hi : LevelData (j + 1))
    (hlo : 1 ≤ hi.cnt.val) (hhi : hi.cnt.val ≤ 4) :
    (rebalancePair lv hi).1.toList ++ (rebalancePair lv hi).2.toList =
      lv.toList ++ hi.toList := by
  rcases lv with ⟨⟨c, hc⟩, sl⟩
  rcases hi with ⟨⟨d, hd⟩, sh⟩
  dsimp only at hlo hhi
  have hc6 : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 ∨ c = 5 := by omega
  have hd4 : d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 := by omega
  rcases hc6 with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hd4 with rfl | rfl | rfl | rfl <;>
    simp [rebalancePair, LevelData.toList, List.finRange_succ,
      ofFn_splitBlock, splitBlock_mergeBlocks, List.append_assoc]

private theorem rebalancePair_cnt {j : ℕ} (lv : LevelData j) (hi : LevelData (j + 1))
    (hlo : 1 ≤ hi.cnt.val) (hhi : hi.cnt.val ≤ 4) :
    (2 ≤ (rebalancePair lv hi).1.cnt.val ∧ (rebalancePair lv hi).1.cnt.val ≤ 3) ∧
      (hi.cnt.val - 1 ≤ (rebalancePair lv hi).2.cnt.val ∧
        (rebalancePair lv hi).2.cnt.val ≤ hi.cnt.val + 1) := by
  rcases lv with ⟨⟨c, hc⟩, sl⟩
  rcases hi with ⟨⟨d, hd⟩, sh⟩
  dsimp only at hlo hhi ⊢
  have hc6 : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 ∨ c = 5 := by omega
  rcases hc6 with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [rebalancePair] <;> omega

/-- A full `L`-level hierarchical block stack. -/
abbrev BlockStack (L : ℕ) : Type := (j : Fin L) → LevelData j.val

/-- Flatten all `L` levels of a block stack from level `0` to level `L - 1`. -/
def BlockStack.toList {L : ℕ} (s : BlockStack L) : List Cell :=
  (List.finRange L).flatMap fun j => (s j).toList

/-- Apply `rebalancePair` to adjacent levels `j` and `j + 1` of a block stack. -/
@[expose] def BlockStack.applyRebalance {L : ℕ} (s : BlockStack L) (j : ℕ) (hj : j + 1 < L) :
    BlockStack L :=
  let pair := rebalancePair (s ⟨j, by omega⟩) (s ⟨j + 1, hj⟩)
  fun i =>
    if h1 : i.val = j then h1 ▸ pair.1
    else if h2 : i.val = j + 1 then h2 ▸ pair.2
    else s i

private theorem levelData_eqRec_cnt {a b : ℕ} (h : a = b) (lv : LevelData a) :
    (h ▸ lv : LevelData b).cnt = lv.cnt := by
  subst h; rfl

private theorem BlockStack.toList_applyRebalance {L : ℕ} (s : BlockStack L) (j : ℕ)
    (hj : j + 1 < L) (hlo : 1 ≤ (s ⟨j + 1, hj⟩).cnt.val) (hhi : (s ⟨j + 1, hj⟩).cnt.val ≤ 4) :
    (s.applyRebalance j hj).toList = s.toList := by
  unfold BlockStack.toList
  have hsplit : List.finRange L =
      (List.finRange L).take j ++ [⟨j, by omega⟩, ⟨j + 1, hj⟩] ++
        (List.finRange L).drop (j + 2) := by
    refine List.ext_getElem (by simp; omega) fun k hk1 hk2 => ?_
    simp only [List.length_finRange] at hk1
    rw [List.getElem_finRange]
    by_cases h1 : k < j
    · rw [List.getElem_append_left (by simp; omega), List.getElem_append_left (by simp; omega),
        List.getElem_take, List.getElem_finRange]
    · by_cases h2 : k = j
      · subst h2
        rw [List.getElem_append_left (by simp; omega),
          List.getElem_append_right (by simp only [List.length_take, List.length_finRange]; omega)]
        simp [Nat.min_eq_left (by omega : k ≤ L)]
      · by_cases h3 : k = j + 1
        · subst h3
          rw [List.getElem_append_left (by simp; omega),
            List.getElem_append_right
              (by simp only [List.length_take, List.length_finRange]; omega)]
          simp [Nat.min_eq_left (by omega : j ≤ L)]
        · rw [List.getElem_append_right (by simp; omega), List.getElem_drop, List.getElem_finRange]
          apply Fin.ext
          simp only [Fin.val_cast, List.length_append, List.length_take, List.length_finRange,
            List.length_cons, List.length_nil, Nat.min_eq_left (by omega : j ≤ L)]
          omega
  rw [hsplit, List.flatMap_append, List.flatMap_append, List.flatMap_append, List.flatMap_append]
  congr 1
  · congr 1
    · refine List.flatMap_congr fun i hi => ?_
      have hilt : i.val < j := by
        obtain ⟨k, hk, hki⟩ := List.getElem_of_mem hi
        rw [List.getElem_take, List.getElem_finRange] at hki
        rw [List.length_take, List.length_finRange] at hk
        have : i.val = k := by simpa using congrArg Fin.val hki.symm
        omega
      simp [BlockStack.applyRebalance, show i.val ≠ j by omega, show i.val ≠ j + 1 by omega]
    · simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, BlockStack.applyRebalance,
        ↓reduceDIte, show ¬ (j + 1 = j) by omega]
      exact rebalancePair_toList (s ⟨j, by omega⟩) (s ⟨j + 1, hj⟩) hlo hhi
  · refine List.flatMap_congr fun i hi => ?_
    have higt : j + 2 ≤ i.val := by
      obtain ⟨k, hk, hki⟩ := List.getElem_of_mem hi
      rw [List.getElem_drop, List.getElem_finRange] at hki
      have : i.val = j + 2 + k := by simpa using congrArg Fin.val hki.symm
      omega
    simp [BlockStack.applyRebalance, show i.val ≠ j by omega, show i.val ≠ j + 1 by omega]

/-- Oblivious rebalancing loop at time `t` over levels `0, ..., m - 1`. -/
@[expose] def BlockStack.rebalanceLoop {L : ℕ} (t : ℕ) : ℕ → BlockStack L → BlockStack L
  | 0, s => s
  | j + 1, s =>
    let s' := rebalanceLoop t j s
    if h : j + 1 < L ∧ 2 ^ j ∣ t then s'.applyRebalance j h.1 else s'

/-- Update level `0` of a block stack by `f`. -/
@[expose] def BlockStack.update0 {L : ℕ} (hL : 0 < L) (f : LevelData 0 → LevelData 0)
    (s : BlockStack L) : BlockStack L :=
  fun i => if h : i.val = 0 then h ▸ f (s ⟨0, hL⟩) else s i

private theorem BlockStack.toList_update0 {L : ℕ} (hL : 0 < L) (f : LevelData 0 → LevelData 0)
    (s : BlockStack L) :
    (s.update0 hL f).toList = (f (s ⟨0, hL⟩)).toList ++ ((List.finRange L).tail.flatMap fun j =>
      (s j).toList) := by
  unfold BlockStack.toList
  rcases L with _ | L
  · omega
  · rw [List.finRange_succ, List.flatMap_cons, List.tail_cons]
    simp only [BlockStack.update0, Fin.val_zero, ↓reduceDIte]
    congr 1
    refine List.flatMap_congr fun i hi => ?_
    simp only [List.mem_map] at hi
    obtain ⟨r, -, rfl⟩ := hi
    simp

private theorem BlockStack.toList_eq_cons_tail {L : ℕ} (hL : 0 < L) (s : BlockStack L) :
    s.toList = (s ⟨0, hL⟩).toList ++ ((List.finRange L).tail.flatMap fun j => (s j).toList) := by
  have h1 := s.toList_update0 hL id
  have hid : s.update0 hL id = s := by
    funext i
    simp only [BlockStack.update0, id_eq]
    split_ifs with h
    · cases i with | mk val isLt => dsimp only at h; subst h; rfl
    · rfl
  rwa [hid] at h1

/-! ### Count invariant for oblivious rebalancing -/

/-- Valid block-count invariant after `t` steps: level `j` has `2 ≤ cnt ≤ 3` whenever fewer than
`2 ^ (j - 1)` steps have elapsed since the last multiple of `2 ^ j` (or `j = 0`), and `1 ≤ cnt ≤ 4`
otherwise. -/
def ValidCounts {L : ℕ} (t : ℕ) (s : BlockStack L) : Prop :=
  ∀ j : Fin L,
    if j.val = 0 ∨ t % 2 ^ j.val < 2 ^ (j.val - 1) then
      2 ≤ (s j).cnt.val ∧ (s j).cnt.val ≤ 3
    else
      1 ≤ (s j).cnt.val ∧ (s j).cnt.val ≤ 4

private theorem exists_two_pow_dvd_iff :
    ∀ m : ℕ, 0 < m → ∃ v : ℕ, (∀ j, 2 ^ j ∣ m ↔ j ≤ v) ∧ 2 ^ v ≤ m := by
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
    intro hm
    by_cases h2 : 2 ∣ m
    · obtain ⟨k, rfl⟩ := h2
      have hk : 0 < k := by omega
      obtain ⟨v, hv, hle⟩ := ih k (by omega) hk
      refine ⟨v + 1, fun j => ?_, by rw [pow_succ']; omega⟩
      cases j with
      | zero => simp
      | succ j =>
        rw [pow_succ', Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 2), hv j]
        omega
    · refine ⟨0, fun j => ?_, by omega⟩
      cases j with
      | zero => simp
      | succ j =>
        exact ⟨fun h => absurd ((dvd_pow_self 2 (Nat.succ_ne_zero j)).trans h) h2,
          fun h => by omega⟩

private theorem mod_two_pow_pred {t v j : ℕ} (hv : ∀ i, 2 ^ i ∣ (t + 1) ↔ i ≤ v) :
    (j ≤ v → 1 ≤ j → t % 2 ^ j = 2 ^ j - 1) ∧
    (j = v + 1 → t % 2 ^ j < 2 ^ (j - 1) ∧ (t + 1) % 2 ^ j = 2 ^ (j - 1)) ∧
    (v + 1 < j → ((t + 1) % 2 ^ j < 2 ^ (j - 1) ↔ t % 2 ^ j < 2 ^ (j - 1))) := by
  have hdvd (i : ℕ) (hi : i ≤ v) : (t + 1) % 2 ^ i = 0 := Nat.mod_eq_zero_of_dvd ((hv i).2 hi)
  have hndvd (i : ℕ) (hi : v < i) : (t + 1) % 2 ^ i ≠ 0 := fun h =>
    (Nat.not_le.2 hi) ((hv i).1 (Nat.dvd_of_mod_eq_zero h))
  refine ⟨fun hjv hj1 => ?_, fun hjv => ?_, fun hjv => ?_⟩
  · have h0 := hdvd j hjv
    have hpos : 0 < 2 ^ j := Nat.two_pow_pos j
    have hlt := Nat.mod_lt t hpos
    have hadd : (t % 2 ^ j + 1) % 2 ^ j = 0 := by simpa [Nat.add_mod] using h0
    by_contra hne
    have hsmall : t % 2 ^ j + 1 < 2 ^ j := by omega
    rw [Nat.mod_eq_of_lt hsmall] at hadd
    omega
  · subst hjv
    simp only [Nat.add_sub_cancel]
    have h0 : 2 ^ v ∣ (t + 1) := (hv v).2 le_rfl
    have h1 : ¬ 2 ^ (v + 1) ∣ (t + 1) := fun h => by have := (hv (v + 1)).1 h; omega
    obtain ⟨q, hq⟩ := h0
    have hqodd : q % 2 = 1 := by
      rcases Nat.mod_two_eq_zero_or_one q with h | h
      · exfalso; apply h1
        obtain ⟨r, rfl⟩ := Nat.dvd_of_mod_eq_zero h
        exact ⟨r, by rw [hq, pow_succ]; ring⟩
      · exact h
    have hmod1 : (t + 1) % 2 ^ (v + 1) = 2 ^ v := by
      rw [hq, pow_succ, Nat.mul_mod_mul_left, hqodd, mul_one]
    have hpos : 0 < 2 ^ v := Nat.two_pow_pos v
    have hmodt : t % 2 ^ (v + 1) = 2 ^ v - 1 := by
      have hpos2 : 0 < 2 ^ (v + 1) := Nat.two_pow_pos _
      have hlt := Nat.mod_lt t hpos2
      have hadd : (t % 2 ^ (v + 1) + 1) % 2 ^ (v + 1) = 2 ^ v := by
        simpa [Nat.add_mod] using hmod1
      by_cases hwrap : t % 2 ^ (v + 1) + 1 = 2 ^ (v + 1)
      · rw [hwrap, Nat.mod_self] at hadd; omega
      · rw [Nat.mod_eq_of_lt (by omega)] at hadd; omega
    omega
  · have hpos : 0 < 2 ^ j := Nat.two_pow_pos j
    have hpos' : 0 < 2 ^ (j - 1) := Nat.two_pow_pos (j - 1)
    have hpow : 2 ^ j = 2 * 2 ^ (j - 1) := by
      rw [← pow_succ', Nat.sub_add_cancel (by omega)]
    have hne1 : (t + 1) % 2 ^ j ≠ 0 := hndvd j (by omega)
    have hne2 : (t + 1) % 2 ^ (j - 1) ≠ 0 := hndvd (j - 1) (by omega)
    have hlt := Nat.mod_lt t hpos
    have hsucc : (t + 1) % 2 ^ j = t % 2 ^ j + 1 := by
      have hadd : (t + 1) % 2 ^ j = (t % 2 ^ j + 1) % 2 ^ j := by
        rw [Nat.add_mod, Nat.mod_eq_of_lt (by omega : 1 < 2 ^ j)]
      by_cases hwrap : t % 2 ^ j + 1 = 2 ^ j
      · rw [hwrap, Nat.mod_self] at hadd; exact absurd hadd hne1
      · rw [hadd, Nat.mod_eq_of_lt (by omega)]
    have hne_half : t % 2 ^ j + 1 ≠ 2 ^ (j - 1) := by
      intro heq
      apply hne2
      have hd : 2 ^ (j - 1) ∣ 2 ^ j := ⟨2, by rw [hpow, mul_comm]⟩
      rw [← Nat.mod_mod_of_dvd (t + 1) hd, hsucc, heq, Nat.mod_self]
    omega

private theorem validCounts_and_toList_rebalanceLoop {L t : ℕ} (hL : 2 ≤ L)
    (ht : t + 1 < 2 ^ (L - 1)) {s : BlockStack L}
    (hs0 : 1 ≤ (s ⟨0, by omega⟩).cnt.val ∧ (s ⟨0, by omega⟩).cnt.val ≤ 4)
    (hs_rest : ∀ j : Fin L, 0 < j.val →
      if t % 2 ^ j.val < 2 ^ (j.val - 1) then
        2 ≤ (s j).cnt.val ∧ (s j).cnt.val ≤ 3
      else
        1 ≤ (s j).cnt.val ∧ (s j).cnt.val ≤ 4) :
    ValidCounts (t + 1) (s.rebalanceLoop (t + 1) (L - 1)) ∧
      (s.rebalanceLoop (t + 1) (L - 1)).toList = s.toList := by
  obtain ⟨v, hv, hvle⟩ := exists_two_pow_dvd_iff (t + 1) (Nat.succ_pos t)
  have hvL : v + 1 < L := by
    by_contra h
    have hle : L - 1 ≤ v := by omega
    have := (Nat.pow_le_pow_right (by norm_num) hle).trans hvle
    omega
  have hmod := fun j => mod_two_pow_pred (j := j) hv
  let Inv (m : ℕ) (u : BlockStack L) : Prop :=
    u.toList = s.toList ∧
    (∀ j : Fin L,
      if j.val < min m (v + 1) then
        2 ≤ (u j).cnt.val ∧ (u j).cnt.val ≤ 3
      else if j.val = min m (v + 1) then
        if m = 0 then 1 ≤ (u j).cnt.val ∧ (u j).cnt.val ≤ 4
        else if m ≤ v then 0 ≤ (u j).cnt.val ∧ (u j).cnt.val ≤ 5
        else 1 ≤ (u j).cnt.val ∧ (u j).cnt.val ≤ 4
      else
        (u j).cnt.val = (s j).cnt.val)
  have hInv : ∀ m ≤ L - 1, Inv m (s.rebalanceLoop (t + 1) m) := by
    intro m
    induction m with
    | zero =>
      intro _
      simp only [BlockStack.rebalanceLoop]
      refine ⟨rfl, fun j => ?_⟩
      simp only [Nat.zero_min, Nat.not_lt_zero, ↓reduceIte]
      by_cases h0 : j.val = 0
      · simp only [h0, ↓reduceIte]
        have hj0 : j = ⟨0, by omega⟩ := Fin.ext h0
        rw [hj0]
        exact hs0
      · simp [h0]
    | succ m ih =>
      intro hm
      obtain ⟨hlist, hcnt⟩ := ih (by omega)
      simp only [BlockStack.rebalanceLoop]
      by_cases hmv : m ≤ v
      · have hdvd : 2 ^ m ∣ (t + 1) := (hv m).2 hmv
        have hltL : m + 1 < L := by omega
        rw [dite_eq_left ⟨hltL, hdvd⟩]
        set u := s.rebalanceLoop (t + 1) m
        have hu_next_eq : (u ⟨m + 1, hltL⟩).cnt.val = (s ⟨m + 1, hltL⟩).cnt.val := by
          have := hcnt ⟨m + 1, hltL⟩
          simp only [show min m (v + 1) = m by omega,
            show ¬ (m + 1 < m) by omega, show ¬ (m + 1 = m) by omega, ↓reduceIte] at this
          exact this
        have hu_next_bds :
            (if m + 1 ≤ v then 1 ≤ (u ⟨m + 1, hltL⟩).cnt.val ∧ (u ⟨m + 1, hltL⟩).cnt.val ≤ 4
             else 2 ≤ (u ⟨m + 1, hltL⟩).cnt.val ∧ (u ⟨m + 1, hltL⟩).cnt.val ≤ 3) := by
          rw [hu_next_eq]
          have hsr := hs_rest ⟨m + 1, hltL⟩ (by dsimp; omega)
          simp only [Nat.add_sub_cancel] at hsr
          split_ifs with hm1v
          · have hmeq := (hmod (m + 1)).1 hm1v (by omega)
            have hnotlt : ¬ t % 2 ^ (m + 1) < 2 ^ m := by
              rw [hmeq, pow_succ]
              have : 1 ≤ 2 ^ m := Nat.one_le_two_pow
              omega
            simpa [hnotlt] using hsr
          · have hm1eq : m + 1 = v + 1 := by omega
            have hlt := ((hmod (m + 1)).2.1 hm1eq).1
            simp only [Nat.add_sub_cancel] at hlt
            simpa [hlt] using hsr
        have hlo : 1 ≤ (u ⟨m + 1, hltL⟩).cnt.val := by split_ifs at hu_next_bds <;> omega
        have hhi : (u ⟨m + 1, hltL⟩).cnt.val ≤ 4 := by split_ifs at hu_next_bds <;> omega
        have hreb := rebalancePair_cnt (u ⟨m, by omega⟩) (u ⟨m + 1, hltL⟩) hlo hhi
        refine ⟨(u.toList_applyRebalance m hltL hlo hhi).trans hlist, fun j => ?_⟩
        simp only [show min (m + 1) (v + 1) = m + 1 by omega]
        by_cases h1 : j.val < m + 1
        · simp only [h1, ↓reduceIte]
          by_cases hjm : j.val = m
          · simp only [BlockStack.applyRebalance, dite_eq_left hjm, levelData_eqRec_cnt]
            exact hreb.1
          · simp only [BlockStack.applyRebalance, dite_eq_right hjm,
              dite_eq_right (show j.val ≠ m + 1 by omega)]
            have := hcnt j
            simp only [show min m (v + 1) = m by omega,
              show j.val < m by omega, ↓reduceIte] at this
            exact this
        · by_cases h2 : j.val = m + 1
          · rw [ite_eq_right h1, ite_eq_left h2]
            simp only [show ¬ (m + 1 = 0) by omega, ↓reduceIte, BlockStack.applyRebalance,
              dite_eq_right (show j.val ≠ m by omega), dite_eq_left h2, levelData_eqRec_cnt]
            have hlt6 := (rebalancePair (u ⟨m, by omega⟩) (u ⟨m + 1, hltL⟩)).2.cnt.isLt
            by_cases hm1v : m + 1 ≤ v
            · simp only [hm1v, ↓reduceIte] at hu_next_bds ⊢; omega
            · simp only [hm1v, ↓reduceIte] at hu_next_bds ⊢; omega
          · rw [ite_eq_right h1, ite_eq_right h2]
            simp only [BlockStack.applyRebalance, dite_eq_right (show j.val ≠ m by omega),
              dite_eq_right h2]
            have := hcnt j
            simp only [show min m (v + 1) = m by omega,
              show ¬ (j.val < m) by omega, show ¬ (j.val = m) by omega, ↓reduceIte] at this
            exact this
      · have hndvd : ¬ (m + 1 < L ∧ 2 ^ m ∣ (t + 1)) := fun h => hmv ((hv m).1 h.2)
        rw [dite_eq_right hndvd]
        refine ⟨hlist, fun j => ?_⟩
        have := hcnt j
        simp only [show min (m + 1) (v + 1) = v + 1 by omega,
          show min m (v + 1) = v + 1 by omega] at this ⊢
        split_ifs at this ⊢ <;> omega
  obtain ⟨hlist, hcnt⟩ := hInv (L - 1) le_rfl
  refine ⟨fun j => ?_, hlist⟩
  have hj := hcnt j
  simp only [show min (L - 1) (v + 1) = v + 1 by omega] at hj
  by_cases hj0 : j.val = 0
  · simp only [hj0, true_or, ↓reduceIte]
    simpa [hj0] using hj
  · by_cases hjv : j.val ≤ v
    · have h0 : (t + 1) % 2 ^ j.val = 0 := Nat.mod_eq_zero_of_dvd ((hv j.val).2 hjv)
      have hpos : 0 < 2 ^ (j.val - 1) := Nat.two_pow_pos _
      simp only [hj0, false_or, h0, hpos, ↓reduceIte]
      simpa [show j.val < v + 1 by omega] using hj
    · by_cases hjv1 : j.val = v + 1
      · have hm1 := ((hmod j.val).2.1 hjv1).2
        simp only [hj0, false_or, hm1, lt_self_iff_false, ↓reduceIte]
        simp only [hjv1, lt_self_iff_false, ↓reduceIte,
          show ¬ (L - 1 = 0) by omega, show ¬ (L - 1 ≤ v) by omega] at hj
        exact hj
      · have hgt : v + 1 < j.val := by omega
        have hiff := (hmod j.val).2.2 hgt
        have heq : (s.rebalanceLoop (t + 1) (L - 1) j).cnt.val = (s j).cnt.val := by
          simpa [show ¬ (j.val < v + 1) by omega, show ¬ (j.val = v + 1) by omega] using hj
        have hsr := hs_rest j (by omega)
        simp only [hj0, false_or, hiff, heq]
        exact hsr

/-! ### Zipper tapes and oblivious machine configurations -/

/-- A bidirectional tape represented as two oblivious block stacks around the head cell. -/
structure ZipperTape (L : ℕ) where
  /-- Cells strictly to the left of the head, nearest first. -/
  left : BlockStack L
  /-- Cell currently under the tape head. -/
  center : Cell
  /-- Cells strictly to the right of the head, nearest first. -/
  right : BlockStack L

/-- Interpret a zipper tape centered at head position `p : ℤ` as a tape function `ℤ → Cell`. -/
def ZipperTape.toFun {L : ℕ} (z : ZipperTape L) (p x : ℤ) : Cell :=
  if x = p then z.center
  else if p < x then z.right.toList.getD (x - p - 1).toNat blankCell
  else z.left.toList.getD (p - x - 1).toNat blankCell

/-- Perform one write-and-move step on a zipper tape (touching only `center` and level `0`). -/
@[expose] def ZipperTape.step {L : ℕ} (hL : 0 < L) (writeCell : Cell) (dir : SignType)
    (z : ZipperTape L) : ZipperTape L :=
  match dir with
  | .zero => { left := z.left, center := writeCell, right := z.right }
  | .pos =>
    { left := z.left.update0 hL (LevelData.push0 writeCell)
      center := (z.right ⟨0, hL⟩).top0
      right := z.right.update0 hL LevelData.pop0 }
  | .neg =>
    { left := z.left.update0 hL LevelData.pop0
      center := (z.left ⟨0, hL⟩).top0
      right := z.right.update0 hL (LevelData.push0 writeCell) }

/-- Apply oblivious rebalancing at step `t` to both stacks of a zipper tape. -/
@[expose] def ZipperTape.rebalance {L : ℕ} (t : ℕ) (z : ZipperTape L) : ZipperTape L where
  left := z.left.rebalanceLoop t (L - 1)
  center := z.center
  right := z.right.rebalanceLoop t (L - 1)

private theorem ZipperTape.toFun_step {L : ℕ} (hL : 0 < L) (writeCell : Cell) (dir : SignType)
    (z : ZipperTape L) (p x : ℤ)
    (hl1 : 1 ≤ (z.left ⟨0, hL⟩).cnt.val) (hl4 : (z.left ⟨0, hL⟩).cnt.val ≤ 4)
    (hr1 : 1 ≤ (z.right ⟨0, hL⟩).cnt.val) (hr4 : (z.right ⟨0, hL⟩).cnt.val ≤ 4) :
    (z.step hL writeCell dir).toFun (p + (dir.cast : ℤ)) x =
      if x = p then writeCell else z.toFun p x := by
  have hl_push : (z.left.update0 hL (LevelData.push0 writeCell)).toList =
      writeCell :: z.left.toList := by
    rw [BlockStack.toList_update0, LevelData.toList_push0 _ _ hl4, List.cons_append,
      ← BlockStack.toList_eq_cons_tail hL]
  have hr_push : (z.right.update0 hL (LevelData.push0 writeCell)).toList =
      writeCell :: z.right.toList := by
    rw [BlockStack.toList_update0, LevelData.toList_push0 _ _ hr4, List.cons_append,
      ← BlockStack.toList_eq_cons_tail hL]
  have hl_pop : z.left.toList =
      (z.left ⟨0, hL⟩).top0 :: (z.left.update0 hL LevelData.pop0).toList := by
    rw [BlockStack.toList_eq_cons_tail hL, LevelData.toList_pop0 _ hl1, List.cons_append,
      ← BlockStack.toList_update0 hL LevelData.pop0]
  have hr_pop : z.right.toList =
      (z.right ⟨0, hL⟩).top0 :: (z.right.update0 hL LevelData.pop0).toList := by
    rw [BlockStack.toList_eq_cons_tail hL, LevelData.toList_pop0 _ hr1, List.cons_append,
      ← BlockStack.toList_update0 hL LevelData.pop0]
  cases dir with
  | zero =>
    simp only [SignType.zero_eq_zero, SignType.coe_zero, add_zero, ZipperTape.step,
      ZipperTape.toFun]
    split_ifs <;> rfl
  | pos =>
    simp only [SignType.pos_eq_one, SignType.coe_one, ZipperTape.step, ZipperTape.toFun, hl_push]
    by_cases hxp : x = p
    · subst hxp
      rw [ite_eq_left rfl, ite_eq_right (by omega), ite_eq_right (by omega)]
      simp
    · by_cases hxp1 : x = p + 1
      · subst hxp1
        rw [ite_eq_left rfl, ite_eq_right (by omega), ite_eq_right (by omega),
          ite_eq_left (by omega), hr_pop]
        simp
      · by_cases hgt : p + 1 < x
        · rw [ite_eq_right hxp1, ite_eq_left hgt, ite_eq_right hxp, ite_eq_right hxp,
            ite_eq_left (by omega), hr_pop]
          have hsub : (x - p - 1).toNat = (x - (p + 1) - 1).toNat + 1 := by omega
          rw [hsub, List.getD_cons_succ]
        · have hlt : x < p := by omega
          rw [ite_eq_right hxp1, ite_eq_right (by omega), ite_eq_right hxp,
            ite_eq_right hxp, ite_eq_right (by omega)]
          have hsub : (p + 1 - x - 1).toNat = (p - x - 1).toNat + 1 := by omega
          rw [hsub, List.getD_cons_succ]
  | neg =>
    simp only [SignType.neg_eq_neg_one, SignType.coe_neg_one, ZipperTape.step, ZipperTape.toFun,
      hr_push]
    by_cases hxp : x = p
    · subst hxp
      rw [ite_eq_left rfl, ite_eq_right (by omega), ite_eq_left (by omega)]
      simp
    · by_cases hxp1 : x = p + -1
      · subst hxp1
        rw [ite_eq_left rfl, ite_eq_right (by omega), ite_eq_right (by omega),
          ite_eq_right (by omega), hl_pop]
        simp
      · by_cases hgt : p < x
        · rw [ite_eq_right hxp1, ite_eq_left (by omega), ite_eq_right hxp, ite_eq_right hxp,
            ite_eq_left hgt]
          have hsub : (x - (p + -1) - 1).toNat = (x - p - 1).toNat + 1 := by omega
          rw [hsub, List.getD_cons_succ]
        · have hlt : x < p + -1 := by omega
          rw [ite_eq_right hxp1, ite_eq_right (by omega), ite_eq_right hxp, ite_eq_right hxp,
            ite_eq_right (by omega), hl_pop]
          have hsub : (p - x - 1).toNat = (p + -1 - x - 1).toNat + 1 := by omega
          rw [hsub, List.getD_cons_succ]

/-- Encode an optional work-tape bit into a 2-bit `Cell`. -/
@[expose] def workEnc : Option Bool → Cell
  | none => (false, false)
  | some b => (true, b)

/-- Decode a 2-bit `Cell` into an optional tape bit (`false` first bit denotes blank/endmarker). -/
@[expose] def cellDec (c : Cell) : Option Bool :=
  if c.1 then some c.2 else none

private theorem cellDec_workEnc (s : Option Bool) : cellDec (workEnc s) = s := by
  cases s <;> rfl

/-- Initial block stack containing `f 0, f 1, ..., f (2 * (2 ^ L - 1) - 1)` in 2 active blocks per
level (`cnt j = 2` for all `j < L`). -/
@[expose] def initStack (L : ℕ) (f : ℕ → Cell) : BlockStack L :=
  fun j =>
    { cnt := ⟨2, by omega⟩
      slots := fun r i =>
        if r.val < 2 then f (2 * (2 ^ j.val - 1) + r.val * 2 ^ j.val + i.val)
        else blankCell }

private theorem validCounts_initStack (L : ℕ) (f : ℕ → Cell) :
    ValidCounts 0 (initStack L f) := by
  intro j
  simp [initStack]

private theorem toList_initStack (L : ℕ) (f : ℕ → Cell) :
    (initStack L f).toList = (List.range (2 * (2 ^ L - 1))).map f := by
  have hlevel (j : ℕ) (hj : j < L) :
      ((initStack L f) ⟨j, hj⟩).toList =
        ((List.range (2 * 2 ^ j)).map fun u => f (2 * (2 ^ j - 1) + u)) := by
    have hlv : ((initStack L f) ⟨j, hj⟩).toList =
        List.ofFn (fun i : Fin (2 ^ j) => f (2 * (2 ^ j - 1) + i.val)) ++
        List.ofFn (fun i : Fin (2 ^ j) => f (2 * (2 ^ j - 1) + 2 ^ j + i.val)) := by
      simp [initStack, LevelData.toList, List.finRange_succ]
    rw [hlv]
    refine List.ext_getElem (by simp; omega) fun k hk1 hk2 => ?_
    simp only [List.length_map, List.length_range] at hk2
    rw [List.getElem_map, List.getElem_range]
    by_cases hk : k < 2 ^ j
    · rw [List.getElem_append_left (by simpa using hk), List.getElem_ofFn]
    · rw [List.getElem_append_right (by simp; omega), List.getElem_ofFn]
      simp only [List.length_ofFn]
      congr 1; omega
  have hprefix : ∀ m ≤ L,
      ((List.finRange L).take m).flatMap (fun j => (initStack L f j).toList) =
        (List.range (2 * (2 ^ m - 1))).map f := by
    intro m
    induction m with
    | zero => intro _; simp
    | succ m ih =>
      intro hm
      have htake : (List.finRange L).take (m + 1) =
          (List.finRange L).take m ++ [⟨m, hm⟩] := by
        refine List.ext_getElem (by simp; omega) fun k hk1 hk2 => ?_
        rw [List.getElem_take, List.getElem_finRange]
        by_cases hkm : k < m
        · rw [List.getElem_append_left (by simp; omega), List.getElem_take, List.getElem_finRange]
        · have heq : k = m := by simp only [List.length_take, List.length_finRange] at hk1; omega
          subst heq
          rw [List.getElem_append_right
            (by simp only [List.length_take, List.length_finRange]; omega)]
          simp [Nat.min_eq_left (by omega : k ≤ L)]
      rw [htake, List.flatMap_append, ih (by omega), List.flatMap_cons, List.flatMap_nil,
        List.append_nil, hlevel m hm]
      have h1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
      have hsum : 2 * (2 ^ (m + 1) - 1) = 2 * (2 ^ m - 1) + 2 * 2 ^ m := by
        rw [pow_succ]; omega
      rw [hsum, List.range_add, List.map_append, List.map_map]
      rfl
  have hL := hprefix L le_rfl
  rw [List.take_of_length_le (by rw [List.length_finRange])] at hL
  exact hL

/-- Input-tape cell encoding at position `p : ℕ` for input `x : BitString n`:
`0 ↦ (false, false)` (left endmarker), `1 ≤ p ≤ n ↦ (true, x (p - 1))`, and
`p ≥ n + 1 ↦ (false, true)` (right endmarker). -/
@[expose] def inCell {n : ℕ} (x : BitString n) (p : ℕ) : Cell :=
  if p = 0 then (false, false)
  else if h : p - 1 < n then (true, x ⟨p - 1, h⟩)
  else (false, true)

private theorem cellDec_inCell {n : ℕ} (x : BitString n) (p : ℕ) :
    cellDec (inCell x p) = inputAt (List.ofFn x) p := by
  by_cases h0 : p = 0
  · simp [inCell, cellDec, inputAt, h0]
  · by_cases h1 : p - 1 < n
    · simp [inCell, cellDec, inputAt, h0, h1]
    · simp [inCell, cellDec, inputAt, h0, h1]

/-- Complete oblivious machine state with `L` stack levels and `m`-bit output prefix. -/
structure ObliviousCfg (k m : ℕ) (State : Type) (L : ℕ) where
  /-- Current control state (`none` when halted). -/
  state : Option State
  /-- Capped output-tape prefix of width `m`. -/
  out : OutCap m
  /-- Read-only input tape stored as a zipper of two `L`-level stacks. -/
  inTape : ZipperTape L
  /-- Work tapes `0, ..., k - 1`, each stored as a zipper of two `L`-level stacks. -/
  workTapes : Fin k → ZipperTape L

/-- Initial oblivious configuration for input `x : BitString n`. -/
@[expose] def initObliviousCfg {k m n : ℕ} {State : Type} (tm : MultiTapeTM k Bool State) (L : ℕ)
    (x : BitString n) : ObliviousCfg k m State L where
  state := some tm.q₀
  out := OutCap.ofList m []
  inTape :=
    { left := initStack L (fun _ => (false, false))
      center := inCell x 1
      right := initStack L (fun r => inCell x (r + 2)) }
  workTapes := fun _ =>
    { left := initStack L (fun _ => blankCell)
      center := blankCell
      right := initStack L (fun _ => blankCell) }

/-- Effective clamped input-head move from the current input cell (`(false, false)` = left end,
`(false, true)` = right end). -/
@[expose] def clampInMove (c : Cell) (d : SignType) : SignType :=
  if c = (false, false) ∧ d = .neg then .zero
  else if c = (false, true) ∧ d = .pos then .zero
  else d

/-- Local TM transition step on `ObliviousCfg` (before oblivious rebalancing). -/
@[expose] noncomputable def localStepOblivious {k m : ℕ} {State : Type}
    (tm : MultiTapeTM k Bool State) {L : ℕ} (hL : 0 < L)
    (oc : ObliviousCfg k m State L) : ObliviousCfg k m State L :=
  match oc.state with
  | none => oc
  | some q =>
    let act := tm.tr q (cellDec oc.inTape.center) (fun i => cellDec (oc.workTapes i).center)
    let inDir := clampInMove oc.inTape.center act.inputTape
    { state := act.state
      out := oc.out.push act.output
      inTape := oc.inTape.step hL oc.inTape.center inDir
      workTapes := fun i =>
        let wcell :=
          match (act.workTapes i).1 with
          | none => (oc.workTapes i).center
          | some sym => workEnc sym
        (oc.workTapes i).step hL wcell (act.workTapes i).2 }

/-- One step of `tm` on `ObliviousCfg`, followed by oblivious rebalancing for time `t + 1`. -/
@[expose] noncomputable def stepOblivious {k m : ℕ} {State : Type} (tm : MultiTapeTM k Bool State)
    {L : ℕ} (hL : 0 < L) (t : ℕ) (oc : ObliviousCfg k m State L) : ObliviousCfg k m State L :=
  let oc' := localStepOblivious tm hL oc
  { state := oc'.state
    out := oc'.out
    inTape := oc'.inTape.rebalance (t + 1)
    workTapes := fun i => (oc'.workTapes i).rebalance (t + 1) }

/-- Run `t` steps of the oblivious simulation starting from `initObliviousCfg tm L x`. -/
@[expose] noncomputable def runOblivious {k m n : ℕ} {State : Type} (tm : MultiTapeTM k Bool State)
    {L : ℕ} (hL : 0 < L) (x : BitString n) : ℕ → ObliviousCfg k m State L
  | 0 => initObliviousCfg tm L x
  | t + 1 => stepOblivious tm hL t (runOblivious tm hL x t)

/-- Correspondence invariant between `runOblivious` and `tm.runFrom` at time `t`. -/
@[expose] def MatchesCfg {k m n : ℕ} {State : Type} {L : ℕ} (x : BitString n) (t : ℕ)
    (oc : ObliviousCfg k m State L) (cfg : Cfg k Bool State (List.ofFn x)) : Prop :=
  oc.state = cfg.state ∧
  oc.out = OutCap.ofList m cfg.output ∧
  ValidCounts t oc.inTape.left ∧
  ValidCounts t oc.inTape.right ∧
  (∀ p : ℕ, p < n + 2 → oc.inTape.toFun (cfg.inputPos.val : ℤ) (p : ℤ) = inCell x p) ∧
  (∀ i : Fin k, ValidCounts t (oc.workTapes i).left ∧ ValidCounts t (oc.workTapes i).right ∧
    ∀ z : ℤ, cellDec ((oc.workTapes i).toFun (cfg.workTapePos i) z) = cfg.workTapes i z)

private theorem matchesCfg_init {k m n : ℕ} {State : Type} (tm : MultiTapeTM k Bool State)
    {L : ℕ} (hnL : n + 2 ≤ 2 * (2 ^ L - 1)) (x : BitString n) :
    MatchesCfg x 0 (initObliviousCfg (m := m) tm L x) (tm.initCfg (List.ofFn x)) := by
  have hinPos : (tm.initCfg (List.ofFn x)).inputPos.val = 1 := rfl
  have hwtPos (i : Fin k) : (tm.initCfg (List.ofFn x)).workTapePos i = 0 := rfl
  have hwt (i : Fin k) (z : ℤ) : (tm.initCfg (List.ofFn x)).workTapes i z = none := rfl
  refine ⟨rfl, rfl, validCounts_initStack _ _, validCounts_initStack _ _, fun p hp => ?_,
    fun i => ⟨validCounts_initStack _ _, validCounts_initStack _ _, fun z => ?_⟩⟩
  · simp only [initObliviousCfg, ZipperTape.toFun, hinPos, Nat.cast_one, toList_initStack]
    by_cases hp1 : (p : ℤ) = 1
    · have : p = 1 := by omega
      subst this; simp
    · by_cases hgt : (1 : ℤ) < p
      · rw [ite_eq_right hp1, ite_eq_left hgt]
        have hidx : ((p : ℤ) - 1 - 1).toNat < 2 * (2 ^ L - 1) := by omega
        rw [getD_eq_getElem' _ _ (by rw [List.length_map, List.length_range]; exact hidx),
          List.getElem_map, List.getElem_range]
        congr 1; omega
      · have hp0 : p = 0 := by omega
        subst hp0
        rw [ite_eq_right (by omega), ite_eq_right (by omega)]
        have hidx : 0 < 2 * (2 ^ L - 1) := by omega
        rw [getD_eq_getElem' _ _ (by rw [List.length_map, List.length_range]; exact hidx),
          List.getElem_map]
        rfl
  · simp only [initObliviousCfg, ZipperTape.toFun, hwtPos, hwt, toList_initStack]
    split_ifs
    · rfl
    · by_cases hlt : (z - 0 - 1).toNat < 2 * (2 ^ L - 1)
      · rw [getD_eq_getElem' _ _ (by rw [List.length_map, List.length_range]; exact hlt),
          List.getElem_map]; rfl
      · rw [getD_eq_default' _ _ (by rw [List.length_map, List.length_range]; omega)]; rfl
    · by_cases hlt : (0 - z - 1).toNat < 2 * (2 ^ L - 1)
      · rw [getD_eq_getElem' _ _ (by rw [List.length_map, List.length_range]; exact hlt),
          List.getElem_map]; rfl
      · rw [getD_eq_default' _ _ (by rw [List.length_map, List.length_range]; omega)]; rfl

private theorem validCounts_step_rebalance {L t : ℕ} (hL : 2 ≤ L) (ht : t + 1 < 2 ^ (L - 1))
    (z : ZipperTape L) (writeCell : Cell) (dir : SignType)
    (hl : ValidCounts t z.left) (hr : ValidCounts t z.right) :
    ValidCounts (t + 1) ((z.step (by omega) writeCell dir).rebalance (t + 1)).left ∧
    ValidCounts (t + 1) ((z.step (by omega) writeCell dir).rebalance (t + 1)).right ∧
    ((z.step (by omega) writeCell dir).rebalance (t + 1)).left.toList =
      (z.step (by omega) writeCell dir).left.toList ∧
    ((z.step (by omega) writeCell dir).rebalance (t + 1)).right.toList =
      (z.step (by omega) writeCell dir).right.toList := by
  have hl0 : 2 ≤ (z.left ⟨0, by omega⟩).cnt.val ∧ (z.left ⟨0, by omega⟩).cnt.val ≤ 3 := by
    simpa using hl ⟨0, by omega⟩
  have hr0 : 2 ≤ (z.right ⟨0, by omega⟩).cnt.val ∧ (z.right ⟨0, by omega⟩).cnt.val ≤ 3 := by
    simpa using hr ⟨0, by omega⟩
  have hstepL0 : 1 ≤ ((z.step (by omega) writeCell dir).left ⟨0, by omega⟩).cnt.val ∧
      ((z.step (by omega) writeCell dir).left ⟨0, by omega⟩).cnt.val ≤ 4 := by
    cases dir <;> simp [ZipperTape.step, BlockStack.update0, LevelData.push0, LevelData.pop0] <;>
      omega
  have hstepR0 : 1 ≤ ((z.step (by omega) writeCell dir).right ⟨0, by omega⟩).cnt.val ∧
      ((z.step (by omega) writeCell dir).right ⟨0, by omega⟩).cnt.val ≤ 4 := by
    cases dir <;> simp [ZipperTape.step, BlockStack.update0, LevelData.push0, LevelData.pop0] <;>
      omega
  have hstepL_rest : ∀ j : Fin L, 0 < j.val →
      if t % 2 ^ j.val < 2 ^ (j.val - 1) then
        2 ≤ ((z.step (by omega) writeCell dir).left j).cnt.val ∧
          ((z.step (by omega) writeCell dir).left j).cnt.val ≤ 3
      else
        1 ≤ ((z.step (by omega) writeCell dir).left j).cnt.val ∧
          ((z.step (by omega) writeCell dir).left j).cnt.val ≤ 4 := by
    intro j hj
    have hne : j.val ≠ 0 := by omega
    have hlj := hl j
    simp only [hne, false_or] at hlj
    cases dir <;> simpa [ZipperTape.step, BlockStack.update0, hne] using hlj
  have hstepR_rest : ∀ j : Fin L, 0 < j.val →
      if t % 2 ^ j.val < 2 ^ (j.val - 1) then
        2 ≤ ((z.step (by omega) writeCell dir).right j).cnt.val ∧
          ((z.step (by omega) writeCell dir).right j).cnt.val ≤ 3
      else
        1 ≤ ((z.step (by omega) writeCell dir).right j).cnt.val ∧
          ((z.step (by omega) writeCell dir).right j).cnt.val ≤ 4 := by
    intro j hj
    have hne : j.val ≠ 0 := by omega
    have hrj := hr j
    simp only [hne, false_or] at hrj
    cases dir <;> simpa [ZipperTape.step, BlockStack.update0, hne] using hrj
  obtain ⟨hvL, htoL⟩ := validCounts_and_toList_rebalanceLoop hL ht hstepL0 hstepL_rest
  obtain ⟨hvR, htoR⟩ := validCounts_and_toList_rebalanceLoop hL ht hstepR0 hstepR_rest
  exact ⟨hvL, hvR, htoL, htoR⟩

/-- Correctness of the oblivious simulation: for every `t < 2 ^ (L - 1)`, `runOblivious` satisfies
`MatchesCfg` with respect to `tm.runFrom (tm.initCfg (List.ofFn x)) t`. -/
theorem matchesCfg_runOblivious {k m n : ℕ} {State : Type} (tm : MultiTapeTM k Bool State)
    {L : ℕ} (hL : 2 ≤ L) (hnL : n + 2 ≤ 2 * (2 ^ L - 1)) (x : BitString n) :
    ∀ t < 2 ^ (L - 1),
      MatchesCfg x t (runOblivious (m := m) (L := L) tm (by omega) x t)
        (tm.runFrom (tm.initCfg (List.ofFn x)) t)
  | 0, _ => matchesCfg_init tm hnL x
  | t + 1, ht => by
    rw [runOblivious, runFrom_succ]
    obtain ⟨hst, hout, hinL, hinR, hinFun, hwork⟩ :=
      matchesCfg_runOblivious tm hL hnL x t (by omega)
    set oc := runOblivious (m := m) (L := L) tm (by omega) x t
    set cfg := tm.runFrom (tm.initCfg (List.ofFn x)) t
    rcases hq : cfg.state with _ | q
    · rw [MultiTapeTM.step_of_halt hq]
      have hoc_st : oc.state = none := hst.trans hq
      have hreb_in := validCounts_step_rebalance hL ht oc.inTape oc.inTape.center .zero hinL hinR
      have hreb_w (i : Fin k) := validCounts_step_rebalance hL ht (oc.workTapes i)
        (oc.workTapes i).center .zero (hwork i).1 (hwork i).2.1
      refine ⟨by simp [stepOblivious, localStepOblivious, hoc_st, hq],
        by simp [stepOblivious, localStepOblivious, hoc_st, hout],
        by simpa [stepOblivious, localStepOblivious, hoc_st, ZipperTape.step] using hreb_in.1,
        by simpa [stepOblivious, localStepOblivious, hoc_st, ZipperTape.step] using hreb_in.2.1,
        fun p hp => ?_,
        fun i => ⟨
          by simpa [stepOblivious, localStepOblivious, hoc_st, ZipperTape.step] using (hreb_w i).1,
          by simpa [stepOblivious, localStepOblivious, hoc_st, ZipperTape.step] using
            (hreb_w i).2.1,
          fun z => ?_⟩⟩
      · simp only [stepOblivious, localStepOblivious, hoc_st]
        have hL_eq : (oc.inTape.rebalance (t + 1)).left.toList = oc.inTape.left.toList := by
          simpa [ZipperTape.step] using hreb_in.2.2.1
        have hR_eq : (oc.inTape.rebalance (t + 1)).right.toList = oc.inTape.right.toList := by
          simpa [ZipperTape.step] using hreb_in.2.2.2
        have hto : (oc.inTape.rebalance (t + 1)).toFun (cfg.inputPos.val : ℤ) (p : ℤ) =
            oc.inTape.toFun (cfg.inputPos.val : ℤ) (p : ℤ) := by
          unfold ZipperTape.toFun
          rw [hL_eq, hR_eq]; rfl
        rw [hto]; exact hinFun p hp
      · simp only [stepOblivious, localStepOblivious, hoc_st]
        have hL_eq : ((oc.workTapes i).rebalance (t + 1)).left.toList =
            (oc.workTapes i).left.toList := by
          simpa [ZipperTape.step] using (hreb_w i).2.2.1
        have hR_eq : ((oc.workTapes i).rebalance (t + 1)).right.toList =
            (oc.workTapes i).right.toList := by
          simpa [ZipperTape.step] using (hreb_w i).2.2.2
        have hto : ((oc.workTapes i).rebalance (t + 1)).toFun (cfg.workTapePos i) z =
            (oc.workTapes i).toFun (cfg.workTapePos i) z := by
          unfold ZipperTape.toFun
          rw [hL_eq, hR_eq]; rfl
        rw [hto]; exact (hwork i).2.2 z
    · rw [MultiTapeTM.step_of_state hq]
      have hoc_st : oc.state = some q := hst.trans hq
      have hin_center : oc.inTape.center = inCell x cfg.inputPos.val := by
        have := hinFun cfg.inputPos.val (by simpa using cfg.inputPos.isLt)
        simpa [ZipperTape.toFun] using this
      have hin_sym : cellDec oc.inTape.center = cfg.inputSymbol := by
        rw [hin_center, cellDec_inCell, Cfg.inputSymbol_eq_inputAt]
      have hwork_sym : (fun i => cellDec (oc.workTapes i).center) = cfg.workTapeSymbols := by
        funext i
        have := (hwork i).2.2 (cfg.workTapePos i)
        simpa [ZipperTape.toFun, Cfg.workTapeSymbols] using this
      set act := tm.tr q cfg.inputSymbol cfg.workTapeSymbols
      set inDir := clampInMove oc.inTape.center act.inputTape
      have hin_move : ((act.apply cfg).inputPos.val : ℤ) =
          (cfg.inputPos.val : ℤ) + (inDir.cast : ℤ) := by
        rw [Action.apply_inputPos, val_moveInputPos_eq]
        have hlen : ((List.ofFn x).length : ℤ) = (n : ℤ) := by simp
        rw [hlen]
        have hpos_lt : cfg.inputPos.val < n + 2 := by simpa using cfg.inputPos.isLt
        have hc_left : oc.inTape.center = (false, false) ↔ cfg.inputPos.val = 0 := by
          rw [hin_center, inCell]
          by_cases h0 : cfg.inputPos.val = 0
          · simp [h0]
          · by_cases h1 : cfg.inputPos.val - 1 < n <;> simp [h0, h1]
        have hc_right : oc.inTape.center = (false, true) ↔ cfg.inputPos.val = n + 1 := by
          rw [hin_center, inCell]
          by_cases h0 : cfg.inputPos.val = 0
          · simp [h0]
          · by_cases h1 : cfg.inputPos.val - 1 < n
            · simp only [h0, h1, ↓reduceIte, ↓reduceDIte, Prod.mk.injEq, Bool.true_eq_false,
                false_and, false_iff]
              omega
            · simp only [h0, h1, ↓reduceIte, ↓reduceDIte, true_iff]
              omega
        simp only [inDir, clampInMove, hc_left, hc_right]
        cases act.inputTape with
        | zero =>
          simp only [reduceCtorEq, and_false, ↓reduceIte, SignType.cast, max_def, min_def]
          split_ifs <;> omega
        | neg =>
          simp only [and_true, reduceCtorEq, and_false, ↓reduceIte]
          by_cases h0 : cfg.inputPos.val = 0
          · simp only [h0, ↓reduceIte, SignType.cast, max_def, min_def]
            split_ifs <;> omega
          · simp only [h0, ↓reduceIte, SignType.cast, max_def, min_def]
            split_ifs <;> omega
        | pos =>
          simp only [and_true, reduceCtorEq, and_false, ↓reduceIte]
          by_cases hn1 : cfg.inputPos.val = n + 1
          · simp only [hn1, ↓reduceIte, SignType.cast, max_def, min_def]
            split_ifs <;> omega
          · simp only [hn1, ↓reduceIte, SignType.cast, max_def, min_def]
            split_ifs <;> omega
      have hreb_in := validCounts_step_rebalance hL ht oc.inTape oc.inTape.center inDir hinL hinR
      have hreb_w (i : Fin k) := validCounts_step_rebalance hL ht (oc.workTapes i)
        (match (act.workTapes i).1 with | none => (oc.workTapes i).center | some sym => workEnc sym)
        (act.workTapes i).2 (hwork i).1 (hwork i).2.1
      have hinL0 : 2 ≤ (oc.inTape.left ⟨0, by omega⟩).cnt.val ∧
          (oc.inTape.left ⟨0, by omega⟩).cnt.val ≤ 3 := by simpa using hinL ⟨0, by omega⟩
      have hinR0 : 2 ≤ (oc.inTape.right ⟨0, by omega⟩).cnt.val ∧
          (oc.inTape.right ⟨0, by omega⟩).cnt.val ≤ 3 := by simpa using hinR ⟨0, by omega⟩
      refine ⟨by simp [stepOblivious, localStepOblivious, hoc_st, hin_sym, hwork_sym, act],
        by simp [stepOblivious, localStepOblivious, hoc_st, hin_sym, hwork_sym, act, hout,
          OutCap.ofList_append_toList],
        by simpa [stepOblivious, localStepOblivious, hoc_st, hin_sym, hwork_sym, act, inDir] using
          hreb_in.1,
        by simpa [stepOblivious, localStepOblivious, hoc_st, hin_sym, hwork_sym, act, inDir] using
          hreb_in.2.1,
        fun p hp => ?_, fun i => ⟨
          by simpa [stepOblivious, localStepOblivious, hoc_st, hin_sym, hwork_sym, act] using
            (hreb_w i).1,
          by simpa [stepOblivious, localStepOblivious, hoc_st, hin_sym, hwork_sym, act] using
            (hreb_w i).2.1,
          fun z => ?_⟩⟩
      · simp only [stepOblivious, localStepOblivious, hoc_st, hin_sym, hwork_sym, hin_move]
        change ((oc.inTape.step (by omega) oc.inTape.center inDir).rebalance (t + 1)).toFun
          ((cfg.inputPos.val : ℤ) + (inDir.cast : ℤ)) (p : ℤ) = inCell x p
        have hto : ((oc.inTape.step (by omega) oc.inTape.center inDir).rebalance (t + 1)).toFun
            ((cfg.inputPos.val : ℤ) + (inDir.cast : ℤ)) (p : ℤ) =
            (oc.inTape.step (by omega) oc.inTape.center inDir).toFun
              ((cfg.inputPos.val : ℤ) + (inDir.cast : ℤ)) (p : ℤ) := by
          unfold ZipperTape.toFun
          rw [hreb_in.2.2.1, hreb_in.2.2.2]; rfl
        rw [hto, ZipperTape.toFun_step (by omega) _ _ _ _ _ (by omega) (by omega) (by omega)
          (by omega)]
        split_ifs with heq
        · rw [hin_center]; congr 1; omega
        · exact hinFun p hp
      · have hwL0 : 2 ≤ ((oc.workTapes i).left ⟨0, by omega⟩).cnt.val ∧
            ((oc.workTapes i).left ⟨0, by omega⟩).cnt.val ≤ 3 := by
          simpa using (hwork i).1 ⟨0, by omega⟩
        have hwR0 : 2 ≤ ((oc.workTapes i).right ⟨0, by omega⟩).cnt.val ∧
            ((oc.workTapes i).right ⟨0, by omega⟩).cnt.val ≤ 3 := by
          simpa using (hwork i).2.1 ⟨0, by omega⟩
        set wcell :=
          match (act.workTapes i).1 with
          | none => (oc.workTapes i).center
          | some sym => workEnc sym
        have hpos_eq : (act.apply cfg).workTapePos i =
            cfg.workTapePos i + (((act.workTapes i).2).cast : ℤ) := rfl
        simp only [stepOblivious, localStepOblivious, hoc_st, hin_sym, hwork_sym, hpos_eq]
        have hto : (((oc.workTapes i).step (by omega) wcell (act.workTapes i).2).rebalance
            (t + 1)).toFun (cfg.workTapePos i + (((act.workTapes i).2).cast : ℤ)) z =
            ((oc.workTapes i).step (by omega) wcell (act.workTapes i).2).toFun
              (cfg.workTapePos i + (((act.workTapes i).2).cast : ℤ)) z := by
          unfold ZipperTape.toFun
          rw [(hreb_w i).2.2.1, (hreb_w i).2.2.2]; rfl
        rw [hto, ZipperTape.toFun_step (by omega) _ _ _ _ _ (by omega) (by omega) (by omega)
          (by omega), Action.apply_workTapes_eq_ite]
        split_ifs with hz
        · subst hz
          cases hact : (act.workTapes i).1 with
          | none =>
            simp only [wcell, hact, Option.getD_none]
            have := (hwork i).2.2 (cfg.workTapePos i)
            simpa [ZipperTape.toFun] using this
          | some sym =>
            simp only [wcell, hact, Option.getD_some, cellDec_workEnc]
        · exact (hwork i).2.2 z

end PippengerFischer

end CslibFrontier.Computability.Circuit.Boolean
