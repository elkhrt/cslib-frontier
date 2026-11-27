/-
Copyright (c) 2026 Cslib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Papers contributors
-/

module

public import CslibFrontier.Computability.BusyBeaver.TuringMachine
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Nat.Log

import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Universal Alphabet Reduction for Bi-Infinite Turing Machines and Busy Beaver Bounds

Constructs a universal multi-sweep base-`b` block simulator (`b ≥ 2`) converting any halting
bi-infinite Turing machine with `n` states and `m ≥ 2` symbols into a halting `b`-symbol machine
with strictly fewer than `2 * (m + 1) * n * l` states (`l = Nat.clog b m`) without decreasing
blank-tape halting time, yielding
`busyBeaver n m ≤ busyBeaver (2 * (m + 1) * n * Nat.clog b m) b`.
-/

public section

namespace CslibFrontier.Computability.BusyBeaver

section BlockTape

private def BlockTapeWith {E : Type*} [Inhabited E] {b l : ℕ} [NeZero b]
    (enc : E → Fin l → Fin b) (T₁ : Turing.Tape E)
    (blk : Fin l → Fin b) (p : ℕ) (T₂ : Turing.Tape (Fin b)) : Prop :=
  ∀ (i : ℤ) (j : Fin l),
    T₂.nth (i * (l : ℤ) + (j.1 : ℤ) - (p : ℤ)) =
      if i = 0 then blk j else enc (T₁.nth i) j

private lemma tape_nth_default' {E : Type*} [Inhabited E] (i : ℤ) :
    (default : Turing.Tape E).nth i = default := by
  rcases i with (_ | n) | n
  · rfl
  · change (Turing.ListBlank.mk ([] : List E)).nth n = default; simp
  · change (Turing.ListBlank.mk ([] : List E)).nth n = default; simp

private lemma blockTapeWith_default {E : Type*} [Inhabited E] {b l : ℕ} [NeZero b]
    (enc : E → Fin l → Fin b) (henc : enc default = 0) :
    BlockTapeWith enc (default : Turing.Tape E) (enc default) 0
      (default : Turing.Tape (Fin b)) := by
  intro i j; rw [tape_nth_default', tape_nth_default']
  change (0 : Fin b) = if i = 0 then enc default j else enc default j; simp [henc]

private lemma blockTapeWith_head {E : Type*} [Inhabited E] {b l : ℕ} [NeZero b]
    {enc : E → Fin l → Fin b} {T₁ : Turing.Tape E} {blk : Fin l → Fin b}
    {p : ℕ} {T₂ : Turing.Tape (Fin b)} (hT : BlockTapeWith enc T₁ blk p T₂) (hp : p < l) :
    T₂.head = blk ⟨p, hp⟩ := by
  simpa using hT 0 ⟨p, hp⟩

private lemma block_coord_eq_zero_iff {l : ℕ} {i : ℤ} {j : Fin l} {p : ℕ} (hp : p < l) :
    i * (l : ℤ) + (j.1 : ℤ) - (p : ℤ) = 0 ↔ i = 0 ∧ j.1 = p := by
  refine ⟨fun h ↦ ?_, by rintro ⟨rfl, hjp⟩; omega⟩
  have hj : (j.1 : ℤ) < l := Int.ofNat_lt.mpr j.2
  have hpn : (p : ℤ) < l := Int.ofNat_lt.mpr hp
  have hi0 : i = 0 := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have : i ≤ -1 := (by omega); nlinarith
    · have : 1 ≤ i := (by omega); nlinarith
  subst hi0; exact ⟨rfl, by omega⟩

private lemma blockTapeWith_write {E : Type*} [Inhabited E] {b l : ℕ} [NeZero b]
    {enc : E → Fin l → Fin b} {T₁ : Turing.Tape E} {blk : Fin l → Fin b}
    {p : ℕ} {T₂ : Turing.Tape (Fin b)} (hT : BlockTapeWith enc T₁ blk p T₂) (hp : p < l)
    (d : Fin b) :
    BlockTapeWith enc T₁ (Function.update blk ⟨p, hp⟩ d) p (T₂.write d) := by
  intro i j; rw [Turing.Tape.write_nth]
  by_cases hz : i * (l : ℤ) + (j.1 : ℤ) - (p : ℤ) = 0
  · rw [ite_eq_left_iff.mpr (fun h ↦ absurd hz h)]
    obtain ⟨rfl, hjp⟩ := (block_coord_eq_zero_iff hp).mp hz
    have hj : j = ⟨p, hp⟩ := Fin.ext hjp
    simp [hj]
  · rw [ite_eq_right_iff.mpr (fun h ↦ absurd h hz), hT i j]
    by_cases hi : i = 0
    · subst hi
      have hne : j ≠ ⟨p, hp⟩ := fun h ↦ hz ((block_coord_eq_zero_iff hp).mpr ⟨rfl, by simp [h]⟩)
      simp [hne]
    · simp [hi]

private lemma blockTapeWith_move_right {E : Type*} [Inhabited E] {b l : ℕ} [NeZero b]
    {enc : E → Fin l → Fin b} {T₁ : Turing.Tape E} {blk : Fin l → Fin b}
    {p : ℕ} {T₂ : Turing.Tape (Fin b)} (hT : BlockTapeWith enc T₁ blk p T₂) :
    BlockTapeWith enc T₁ blk (p + 1) (T₂.move .right) := by
  intro i j; rw [Turing.Tape.move_right_nth]
  have heq : i * (l : ℤ) + (j.1 : ℤ) - ((p + 1 : ℕ) : ℤ) + 1 =
      i * (l : ℤ) + (j.1 : ℤ) - (p : ℤ) := by push_cast; ring
  rw [heq]; exact hT i j

private lemma blockTapeWith_move_left {E : Type*} [Inhabited E] {b l : ℕ} [NeZero b]
    {enc : E → Fin l → Fin b} {T₁ : Turing.Tape E} {blk : Fin l → Fin b}
    {p : ℕ} {T₂ : Turing.Tape (Fin b)} (hp : 1 ≤ p) (hT : BlockTapeWith enc T₁ blk p T₂) :
    BlockTapeWith enc T₁ blk (p - 1) (T₂.move .left) := by
  intro i j; rw [Turing.Tape.move_left_nth]
  have hpz : ((p - 1 : ℕ) : ℤ) = (p : ℤ) - 1 := by omega
  have heq : i * (l : ℤ) + (j.1 : ℤ) - ((p - 1 : ℕ) : ℤ) - 1 =
      i * (l : ℤ) + (j.1 : ℤ) - (p : ℤ) := by rw [hpz]; ring
  rw [heq]; exact hT i j

private lemma blockTapeWith_cross_right {E : Type*} [Inhabited E] {b l : ℕ} [NeZero b]
    (hl : 1 ≤ l) {enc : E → Fin l → Fin b} {T₁ : Turing.Tape E} {e' : E}
    {T₂ : Turing.Tape (Fin b)} (hT : BlockTapeWith enc T₁ (enc e') (l - 1) T₂) :
    BlockTapeWith enc ((T₁.write e').move .right)
      (enc ((T₁.write e').move .right).head) 0 (T₂.move .right) := by
  intro i j; rw [Turing.Tape.move_right_nth]
  have heq : i * (l : ℤ) + (j.1 : ℤ) - ((0 : ℕ) : ℤ) + 1 =
      (i + 1) * (l : ℤ) + (j.1 : ℤ) - ((l - 1 : ℕ) : ℤ) := by
    have : ((l - 1 : ℕ) : ℤ) = (l : ℤ) - 1 := by omega
    rw [this]; push_cast; ring
  rw [heq, hT (i + 1) j]
  have hhead : ((T₁.write e').move .right).head = T₁.nth 1 := by
    rw [← Turing.Tape.nth_zero, Turing.Tape.move_right_nth, Turing.Tape.write_nth]; simp
  by_cases hi : i = 0
  · subst hi; simp [hhead]
  · conv_rhs => rw [ite_eq_right_iff.mpr (fun h ↦ absurd h hi)]
    rw [Turing.Tape.move_right_nth, Turing.Tape.write_nth]
    by_cases hi1 : i + 1 = 0 <;> simp [hi1]

private lemma blockTapeWith_cross_left {E : Type*} [Inhabited E] {b l : ℕ} [NeZero b]
    (hl : 1 ≤ l) {enc : E → Fin l → Fin b} {T₁ : Turing.Tape E} {e' : E}
    {T₂ : Turing.Tape (Fin b)} (hT : BlockTapeWith enc T₁ (enc e') 0 T₂) :
    BlockTapeWith enc ((T₁.write e').move .left)
      (enc ((T₁.write e').move .left).head) (l - 1) (T₂.move .left) := by
  intro i j; rw [Turing.Tape.move_left_nth]
  have heq : i * (l : ℤ) + (j.1 : ℤ) - ((l - 1 : ℕ) : ℤ) - 1 =
      (i - 1) * (l : ℤ) + (j.1 : ℤ) - ((0 : ℕ) : ℤ) := by
    have : ((l - 1 : ℕ) : ℤ) = (l : ℤ) - 1 := by omega
    rw [this]; push_cast; ring
  rw [heq, hT (i - 1) j]
  have hhead : ((T₁.write e').move .left).head = T₁.nth (-1) := by
    rw [← Turing.Tape.nth_zero, Turing.Tape.move_left_nth, Turing.Tape.write_nth]; simp
  by_cases hi : i = 0
  · subst hi; simp [hhead]
  · conv_rhs => rw [ite_eq_right_iff.mpr (fun h ↦ absurd h hi)]
    rw [Turing.Tape.move_left_nth, Turing.Tape.write_nth]
    by_cases hi1 : i - 1 = 0 <;> simp [hi1]

end BlockTape

section GeneralBlockSimulator

/-- Control states for the base-`b` block simulator over base-`b` tuples of length
`l`, partitioning each simulated state `q : Q` into Sweep-0 (`Fin (l - 1)`), Sweep-1 prefix-tree
states (`Σ j : Fin l, Fin j.1 → Fin b`), and Sweep-2/3 states (`E × Bool × Fin (l - 1)`). -/
inductive BlockState (Q E : Type*) (b l : ℕ) : Type _
  | sweep0 (q : Q) (pos : Fin (l - 1))
  | sweep1 (q : Q) (j : Fin l) (pref : Fin j.1 → Fin b)
  | sweep23 (q : Q) (e : E) (isSweep3 : Bool) (pos : Fin (l - 1))

/-- Equivalence splitting `BlockState Q E b l` into its Sweep-0, Sweep-1, and Sweep-2/3
components. -/
def blockStateEquiv (Q E : Type*) (b l : ℕ) :
    BlockState Q E b l ≃
      (Q × Fin (l - 1)) ⊕
        ((Q × Σ j : Fin l, Fin j.1 → Fin b) ⊕ (Q × E × Bool × Fin (l - 1))) where
  toFun
    | .sweep0 q pos => Sum.inl (q, pos)
    | .sweep1 q j pref => Sum.inr (Sum.inl (q, ⟨j, pref⟩))
    | .sweep23 q e isSweep3 pos => Sum.inr (Sum.inr (q, e, isSweep3, pos))
  invFun
    | Sum.inl (q, pos) => .sweep0 q pos
    | Sum.inr (Sum.inl (q, ⟨j, pref⟩)) => .sweep1 q j pref
    | Sum.inr (Sum.inr (q, e, isSweep3, pos)) => .sweep23 q e isSweep3 pos
  left_inv x := by cases x <;> rfl
  right_inv x := by rcases x with ⟨q, pos⟩ | ⟨q, ⟨j, pref⟩⟩ | ⟨q, e, s3, pos⟩ <;> rfl

theorem blockStateEquiv_def (Q E : Type*) (b l : ℕ) :
    (blockStateEquiv Q E b l : BlockState Q E b l →
      (Q × Fin (l - 1)) ⊕
        ((Q × Σ j : Fin l, Fin j.1 → Fin b) ⊕ (Q × E × Bool × Fin (l - 1)))) =
      fun
        | .sweep0 q pos => Sum.inl (q, pos)
        | .sweep1 q j pref => Sum.inr (Sum.inl (q, ⟨j, pref⟩))
        | .sweep23 q e isSweep3 pos => Sum.inr (Sum.inr (q, e, isSweep3, pos)) := by
  funext x; cases x <;> rfl

@[simp] theorem blockStateEquiv_sweep0 {Q E : Type*} {b l : ℕ} (q : Q) (pos : Fin (l - 1)) :
    blockStateEquiv Q E b l (.sweep0 q pos) = Sum.inl (q, pos) := by rfl

@[simp] theorem blockStateEquiv_sweep1 {Q E : Type*} {b l : ℕ} (q : Q) (j : Fin l)
    (pref : Fin j.1 → Fin b) :
    blockStateEquiv Q E b l (.sweep1 q j pref) = Sum.inr (Sum.inl (q, ⟨j, pref⟩)) := by rfl

@[simp] theorem blockStateEquiv_sweep23 {Q E : Type*} {b l : ℕ} (q : Q) (e : E)
    (isSweep3 : Bool) (pos : Fin (l - 1)) :
    blockStateEquiv Q E b l (.sweep23 q e isSweep3 pos) =
      Sum.inr (Sum.inr (q, e, isSweep3, pos)) := by rfl

instance instFintypeBlockState {Q E : Type*} [Fintype Q] [Fintype E] (b l : ℕ) :
    Fintype (BlockState Q E b l) :=
  Fintype.ofEquiv _ (blockStateEquiv Q E b l).symm

/-- Exact cardinality of `BlockState Q E b l`. -/
@[simp] theorem card_blockState (Q E : Type*) [Fintype Q] [Fintype E] (b l : ℕ) :
    Fintype.card (BlockState Q E b l) =
      Fintype.card Q * ((l - 1) + ∑ j : Fin l, b ^ j.1 + 2 * Fintype.card E * (l - 1)) := by
  rw [Fintype.card_congr (blockStateEquiv Q E b l), Fintype.card_sum, Fintype.card_sum,
    Fintype.card_prod, Fintype.card_prod, Fintype.card_prod, Fintype.card_prod,
    Fintype.card_prod, Fintype.card_sigma, Fintype.card_bool, Fintype.card_fin]
  simp only [Fintype.card_pi, Fintype.card_fin, Finset.prod_const, Finset.card_fin]
  ring

/-- Existence of a blank-preserving injection `E ↪ (Fin l → Fin b)` when `2 ≤ b` and
`l = Nat.clog b (Fintype.card E)`. -/
theorem exists_block_enc (E : Type*) [Fintype E] [Inhabited E] {b : ℕ} [NeZero b]
    (hb : 2 ≤ b) :
    ∃ enc : E ↪ (Fin (Nat.clog b (Fintype.card E)) → Fin b), enc default = 0 := by
  classical
  let m := Fintype.card E; let l := Nat.clog b m
  have hm_le : m ≤ b ^ l := Nat.le_pow_clog (by omega) m
  have hm_pos : 0 < m := Fintype.card_pos
  have hpow_pos : 0 < b ^ l := pow_pos (by omega) l
  let eE₀ : E ≃ Fin m := Fintype.equivFin E
  let eE : E ≃ Fin m := eE₀.trans (Equiv.swap (eE₀ default) ⟨0, hm_pos⟩)
  have heE : eE default = ⟨0, hm_pos⟩ := Equiv.swap_apply_left _ _
  let eT₀ : (Fin l → Fin b) ≃ Fin (b ^ l) := Fintype.equivFinOfCardEq (by simp)
  let eT : (Fin l → Fin b) ≃ Fin (b ^ l) := eT₀.trans (Equiv.swap (eT₀ 0) ⟨0, hpow_pos⟩)
  have heT : eT.symm ⟨0, hpow_pos⟩ = 0 := eT.injective (by simp [eT])
  let fCast : Fin m ↪ Fin (b ^ l) := ⟨Fin.castLE hm_le, Fin.castLE_injective hm_le⟩
  refine ⟨eE.toEmbedding.trans (fCast.trans eT.symm.toEmbedding), ?_⟩
  simp only [Function.Embedding.trans_apply, Equiv.coe_toEmbedding, heE, fCast]
  exact heT

private def tupleSnoc {b j : ℕ} (pref : Fin j → Fin b) (d : Fin b) : Fin (j + 1) → Fin b :=
  fun i ↦ if h : i.1 < j then pref ⟨i.1, h⟩ else d

private lemma tupleSnoc_lt {b j : ℕ} (pref : Fin j → Fin b) (d : Fin b) (i : ℕ) (hi : i < j) :
    tupleSnoc pref d ⟨i, by omega⟩ = pref ⟨i, hi⟩ := by
  simp [tupleSnoc, hi]

private lemma tupleSnoc_eq {b j : ℕ} (pref : Fin j → Fin b) (d : Fin b) :
    tupleSnoc pref d ⟨j, Nat.lt_succ_self j⟩ = d := by
  simp [tupleSnoc]

private noncomputable def decodeBlock {E : Type*} {b l : ℕ}
    (enc : E ↪ (Fin l → Fin b)) (w : Fin l → Fin b) : Option E := by
  classical exact if h : ∃ e : E, enc e = w then some h.choose else none

private lemma decodeBlock_enc {E : Type*} {b l : ℕ} (enc : E ↪ (Fin l → Fin b)) (e : E) :
    decodeBlock enc (enc e) = some e := by
  classical
  have h : ∃ x : E, enc x = enc e := ⟨e, rfl⟩
  rw [decodeBlock, dite_eq_left h]; exact congrArg some (enc.injective h.choose_spec)

/-- Transition function for the base-`b` block simulator `blockSimTM`. -/
noncomputable def blockSimTrans {Q E : Type*} [Inhabited E] {b l : ℕ}
    (M : BiInfTM Q E) (hl : 1 ≤ l) (enc : E ↪ (Fin l → Fin b)) :
    BlockState Q E b l → Fin b → Option (BlockState Q E b l) × Fin b × Turing.Dir
  | .sweep0 q pos, d =>
    if _ : 0 < pos.1 then (some (.sweep0 q ⟨pos.1 - 1, by omega⟩), d, .left)
    else (some (.sweep1 q ⟨0, hl⟩ finZeroElim), d, .left)
  | .sweep1 q j pref, d =>
    let w := tupleSnoc pref d
    if hj : j.1 + 1 < l then
      (some (.sweep1 q ⟨j.1 + 1, hj⟩ w), d, .right)
    else
      let w' : Fin l → Fin b := fun i ↦ w ⟨i.1, by omega⟩
      match decodeBlock enc w' with
      | none => (none, d, .right)
      | some e =>
        match M.trans q e with
        | (none, _, _) => (none, d, .right)
        | (some q', e', dir) =>
          if _ : 2 ≤ l then
            (some (.sweep23 q e false ⟨l - 2, by omega⟩), enc e' ⟨l - 1, by omega⟩, .left)
          else
            (some (.sweep1 q' ⟨0, hl⟩ finZeroElim), enc e' ⟨0, hl⟩, dir)
  | .sweep23 q e false pos, d =>
    match M.trans q e with
    | (none, _, _) => (none, d, .right)
    | (some q', e', dir) =>
      let out := enc e' ⟨pos.1, by omega⟩
      if _ : 0 < pos.1 then
        (some (.sweep23 q e false ⟨pos.1 - 1, by omega⟩), out, .left)
      else
        match dir with
        | .left => (some (.sweep0 q' ⟨l - 2, by omega⟩), out, .left)
        | .right =>
          (some (.sweep23 q e true ⟨0, Nat.lt_of_le_of_lt (Nat.zero_le _) pos.2⟩), out, .right)
  | .sweep23 q e true pos, d =>
    match M.trans q e with
    | (none, _, _) => (none, d, .right)
    | (some q', _, _) =>
      if hpos : pos.1 + 1 < l - 1 then
        (some (.sweep23 q e true ⟨pos.1 + 1, hpos⟩), d, .right)
      else
        (some (.sweep1 q' ⟨0, hl⟩ finZeroElim), d, .right)

/-- General alphabet-reducing block simulator of `M : BiInfTM Q E` over `Fin b` with block
length `l ≥ 1`. -/
noncomputable def blockSimTM {Q E : Type*} [Inhabited E] {b l : ℕ} [NeZero b]
    (M : BiInfTM Q E) (hl : 1 ≤ l) (enc : E ↪ (Fin l → Fin b)) :
    BiInfTM (BlockState Q E b l) (Fin b) where
  initState := .sweep1 M.initState ⟨0, hl⟩ finZeroElim
  trans := blockSimTrans M hl enc

theorem blockSimTM_def {Q E : Type*} [Inhabited E] {b l : ℕ} [NeZero b]
    (M : BiInfTM Q E) (hl : 1 ≤ l) (enc : E ↪ (Fin l → Fin b)) :
    blockSimTM M hl enc =
      ⟨.sweep1 M.initState ⟨0, hl⟩ finZeroElim, blockSimTrans M hl enc⟩ := by rfl

@[simp] theorem blockSimTM_initState {Q E : Type*} [Inhabited E] {b l : ℕ} [NeZero b]
    (M : BiInfTM Q E) (hl : 1 ≤ l) (enc : E ↪ (Fin l → Fin b)) :
    (blockSimTM M hl enc).initState = .sweep1 M.initState ⟨0, hl⟩ finZeroElim := by rfl

@[simp] theorem blockSimTM_trans {Q E : Type*} [Inhabited E] {b l : ℕ} [NeZero b]
    (M : BiInfTM Q E) (hl : 1 ≤ l) (enc : E ↪ (Fin l → Fin b))
    (q : BlockState Q E b l) (d : Fin b) :
    (blockSimTM M hl enc).trans q d = blockSimTrans M hl enc q d := by rfl

private lemma blockSim_sweep1 {Q E : Type*} [Inhabited E] {b l : ℕ} [NeZero b]
    (M : BiInfTM Q E) (hl : 1 ≤ l) (enc : E ↪ (Fin l → Fin b))
    (q : Q) (T₁ : Turing.Tape E) :
    ∀ (k : ℕ) (hk : k < l) (T₂ : Turing.Tape (Fin b)),
      BlockTapeWith enc T₁ (enc T₁.head) 0 T₂ →
      ∃ T₂' : Turing.Tape (Fin b),
        (blockSimTM M hl enc).step^[k]
            ⟨some (.sweep1 q ⟨0, hl⟩ finZeroElim), T₂⟩ =
          ⟨some (.sweep1 q ⟨k, hk⟩ (fun i ↦ enc T₁.head ⟨i.1, by omega⟩)), T₂'⟩ ∧
        BlockTapeWith enc T₁ (enc T₁.head) k T₂' := by
  intro k; induction k with
  | zero =>
    intro hk T₂ hT; refine ⟨T₂, ?_, hT⟩
    simp only [Function.iterate_zero, id_eq, Cfg.mk.injEq, Option.some.injEq, and_true]
    congr 1; funext i; exact Fin.elim0 i
  | succ k ih =>
    intro hk T₂ hT
    obtain ⟨T₂', hiter, hT'⟩ := ih (by omega) T₂ hT
    refine ⟨T₂'.move .right, ?_, blockTapeWith_move_right hT'⟩
    rw [Function.iterate_succ_apply', hiter, BiInfTM.step_some]
    have hhead : T₂'.head = enc T₁.head ⟨k, by omega⟩ := blockTapeWith_head hT' (by omega)
    have hpref : tupleSnoc (fun i : Fin k ↦ enc T₁.head ⟨i.1, by omega⟩) T₂'.head =
        fun i : Fin (k + 1) ↦ enc T₁.head ⟨i.1, by omega⟩ := by
      funext i; rcases Nat.lt_or_ge i.1 k with hilt | hige
      · simpa using tupleSnoc_lt (fun j : Fin k ↦ enc T₁.head ⟨j.1, by omega⟩) T₂'.head i.1 hilt
      · have hieq : i.1 = k := by omega
        have hi' : i = ⟨k, Nat.lt_succ_self k⟩ := Fin.ext hieq
        rw [hi', tupleSnoc_eq, hhead]
    dsimp [blockSimTM, blockSimTrans]; rw [dite_eq_left hk, hpref, Turing.Tape.write_self]

private lemma blockSim_sweep2 {Q E : Type*} [Inhabited E] {b l : ℕ} [NeZero b]
    (M : BiInfTM Q E) (hl : 1 ≤ l) (enc : E ↪ (Fin l → Fin b))
    (q q' : Q) (e e' : E) (dir : Turing.Dir) (htr : M.trans q e = (some q', e', dir))
    (T₁ : Turing.Tape E) :
    ∀ (k : ℕ) (hk : k < l - 1) (T₂ : Turing.Tape (Fin b)) (blk : Fin l → Fin b),
      (∀ j : Fin l, k < j.1 → blk j = enc e' j) → BlockTapeWith enc T₁ blk k T₂ →
      ∃ (blk' : Fin l → Fin b) (T₂' : Turing.Tape (Fin b)),
        (blockSimTM M hl enc).step^[k] ⟨some (.sweep23 q e false ⟨k, hk⟩), T₂⟩ =
          ⟨some (.sweep23 q e false ⟨0, by omega⟩), T₂'⟩ ∧
        (∀ j : Fin l, 0 < j.1 → blk' j = enc e' j) ∧ BlockTapeWith enc T₁ blk' 0 T₂' := by
  intro k; induction k with
  | zero => intro hk T₂ blk hblk hT; exact ⟨blk, T₂, rfl, fun j hj ↦ hblk j hj, hT⟩
  | succ k ih =>
    intro hk T₂ blk hblk hT
    let blk₁ := Function.update blk ⟨k + 1, by omega⟩ (enc e' ⟨k + 1, by omega⟩)
    have hblk₁ : ∀ j : Fin l, k < j.1 → blk₁ j = enc e' j := by
      intro j hj; by_cases hjk : j.1 = k + 1
      · have hj' : j = ⟨k + 1, by omega⟩ := Fin.ext hjk
        simp [blk₁, hj']
      · have hne : j ≠ ⟨k + 1, by omega⟩ := fun h ↦ hjk (by simp [h])
        simp [blk₁, hne, hblk j (by omega)]
    obtain ⟨blk', T₂', hiter, hblk', hT'⟩ := ih (by omega) _ blk₁ hblk₁
      (blockTapeWith_move_left (by omega)
        (blockTapeWith_write hT (by omega) (enc e' ⟨k + 1, by omega⟩)))
    have hstep1 :
        (blockSimTM M hl enc).step ⟨some (.sweep23 q e false ⟨k + 1, hk⟩), T₂⟩ =
          ⟨some (.sweep23 q e false ⟨k, by omega⟩),
            (T₂.write (enc e' ⟨k + 1, by omega⟩)).move .left⟩ := by
      rw [BiInfTM.step_some]; dsimp [blockSimTM, blockSimTrans]; rw [htr]
    exact ⟨blk', T₂', by rw [Function.iterate_succ_apply, hstep1, hiter], hblk', hT'⟩

private lemma blockSim_sweep3 {Q E : Type*} [Inhabited E] {b l : ℕ} [NeZero b]
    (M : BiInfTM Q E) (hl : 1 ≤ l) (enc : E ↪ (Fin l → Fin b))
    (q q' : Q) (e e' : E) (dir : Turing.Dir) (htr : M.trans q e = (some q', e', dir))
    (T₁ : Turing.Tape E) (hl2 : 2 ≤ l) :
    ∀ (rem : ℕ), rem ≤ l - 2 → ∀ (T₂ : Turing.Tape (Fin b)),
      BlockTapeWith enc T₁ (enc e') (l - 1 - rem) T₂ →
      ∃ T₂' : Turing.Tape (Fin b),
        (blockSimTM M hl enc).step^[rem + 1]
            ⟨some (.sweep23 q e true ⟨l - 2 - rem, by omega⟩), T₂⟩ =
          ⟨some (.sweep1 q' ⟨0, hl⟩ finZeroElim), T₂'⟩ ∧
        BlockTapeWith enc ((T₁.write e').move .right)
          (enc ((T₁.write e').move .right).head) 0 T₂' := by
  intro rem; induction rem with
  | zero =>
    intro _ T₂ hT
    have hstep :
        (blockSimTM M hl enc).step ⟨some (.sweep23 q e true ⟨l - 2 - 0, by omega⟩), T₂⟩ =
          ⟨some (.sweep1 q' ⟨0, hl⟩ finZeroElim), T₂.move .right⟩ := by
      rw [BiInfTM.step_some]; dsimp [blockSimTM, blockSimTrans]; rw [htr]
      split_ifs with hpos
      · exfalso; omega
      · rw [Turing.Tape.write_self]
    exact ⟨T₂.move .right, by simpa using hstep, blockTapeWith_cross_right hl (by simpa using hT)⟩
  | succ rem ih =>
    intro _ T₂ hT
    have hstep1 :
        (blockSimTM M hl enc).step
            ⟨some (.sweep23 q e true ⟨l - 2 - (rem + 1), by omega⟩), T₂⟩ =
          ⟨some (.sweep23 q e true ⟨l - 2 - rem, by omega⟩), T₂.move .right⟩ := by
      rw [BiInfTM.step_some]; dsimp [blockSimTM, blockSimTrans]; rw [htr]
      split_ifs with hpos
      · have hidx : l - 2 - (rem + 1) + 1 = l - 2 - rem := by omega
        simp only [Turing.Tape.write_self, Cfg.mk.injEq, Option.some.injEq,
          BlockState.sweep23.injEq, true_and, and_true]; exact Fin.ext hidx
      · exfalso; omega
    obtain ⟨T₂', hiter, hT'⟩ := ih (by omega) (T₂.move .right)
      ((show l - 1 - (rem + 1) + 1 = l - 1 - rem by omega) ▸ blockTapeWith_move_right hT)
    exact ⟨T₂', by rw [Function.iterate_succ_apply, hstep1, hiter], hT'⟩

private lemma blockSim_sweep0 {Q E : Type*} [Inhabited E] {b l : ℕ} [NeZero b]
    (M : BiInfTM Q E) (hl : 1 ≤ l) (enc : E ↪ (Fin l → Fin b))
    (q' : Q) (T₁ : Turing.Tape E) :
    ∀ (k : ℕ) (hk : k < l - 1) (T₂ : Turing.Tape (Fin b)),
      BlockTapeWith enc T₁ (enc T₁.head) (k + 1) T₂ →
      ∃ T₂' : Turing.Tape (Fin b),
        (blockSimTM M hl enc).step^[k + 1] ⟨some (.sweep0 q' ⟨k, hk⟩), T₂⟩ =
          ⟨some (.sweep1 q' ⟨0, hl⟩ finZeroElim), T₂'⟩ ∧
        BlockTapeWith enc T₁ (enc T₁.head) 0 T₂' := by
  intro k; induction k with
  | zero =>
    intro hk T₂ hT
    have hstep :
        (blockSimTM M hl enc).step ⟨some (.sweep0 q' ⟨0, hk⟩), T₂⟩ =
          ⟨some (.sweep1 q' ⟨0, hl⟩ finZeroElim), T₂.move .left⟩ := by
      rw [BiInfTM.step_some]; dsimp [blockSimTM, blockSimTrans]; rw [Turing.Tape.write_self]
    exact ⟨T₂.move .left, by simpa using hstep,
      by simpa using blockTapeWith_move_left (by omega) hT⟩
  | succ k ih =>
    intro hk T₂ hT
    have hstep1 :
        (blockSimTM M hl enc).step ⟨some (.sweep0 q' ⟨k + 1, hk⟩), T₂⟩ =
          ⟨some (.sweep0 q' ⟨k, by omega⟩), T₂.move .left⟩ := by
      rw [BiInfTM.step_some]; dsimp [blockSimTM, blockSimTrans]; rw [Turing.Tape.write_self]
    obtain ⟨T₂', hiter, hT'⟩ := ih (by omega) (T₂.move .left)
      (by simpa using blockTapeWith_move_left (by omega) hT)
    exact ⟨T₂', by rw [Function.iterate_succ_apply, hstep1, hiter], hT'⟩

private lemma iterate_comp_five {α : Type*} (f : α → α) (a b c : ℕ) (x : α) :
    f^[c] (f (f^[b] (f (f^[a] x)))) = f^[a + 1 + b + 1 + c] x := by
  rw [← Function.iterate_succ_apply' f a, ← Function.iterate_add_apply f b (a + 1),
    ← Function.iterate_succ_apply' f (b + (a + 1)),
    ← Function.iterate_add_apply f c (b + (a + 1) + 1)]
  congr 1; omega

private def BlockSimRel {Q E : Type*} [Inhabited E] {b l : ℕ} [NeZero b]
    (enc : E ↪ (Fin l → Fin b)) (hl : 1 ≤ l)
    (c₁ : Cfg Q E) (c₂ : Cfg (BlockState Q E b l) (Fin b)) : Prop :=
  match c₁.state with
  | none => c₂.state = none
  | some q =>
    c₂.state = some (BlockState.sweep1 q ⟨0, hl⟩ finZeroElim) ∧
      BlockTapeWith enc c₁.tape (enc c₁.tape.head) 0 c₂.tape

/-- `blockSimTM M hl enc` preserves blank-tape halting and has halting time at least
`M.time`. -/
theorem blockSimTM_halts_and_time_le {Q E : Type*} [Inhabited E] {b l : ℕ} [NeZero b]
    (M : BiInfTM Q E) (hl : 1 ≤ l) (enc : E ↪ (Fin l → Fin b))
    (henc : enc default = 0) (hM : M.HaltsOnBlank) :
    (blockSimTM M hl enc).HaltsOnBlank ∧ M.time ≤ (blockSimTM M hl enc).time := by
  let M' := blockSimTM M hl enc
  refine haltsOnBlank_and_time_le_of_rel_sim (BlockSimRel enc hl)
    ⟨0, rfl, blockTapeWith_default enc henc⟩ ?_ ?_ hM
  · intro c₁ c₂ hrel hne
    rcases c₁ with ⟨_ | q, T₁⟩
    · exact absurd rfl hne
    · rcases c₂ with ⟨st₂, T₂⟩; rcases hrel with ⟨hst₂, hT⟩
      dsimp only at hst₂ hT; subst hst₂
      obtain ⟨T₂a, hsw1, hTa⟩ := blockSim_sweep1 M hl enc q T₁ (l - 1) (by omega) T₂ hT
      have hhead_a : T₂a.head = enc T₁.head ⟨l - 1, by omega⟩ :=
        blockTapeWith_head hTa (by omega)
      have hw_eq : (fun i : Fin l ↦
          tupleSnoc (fun j : Fin (l - 1) ↦ enc T₁.head ⟨j.1, by omega⟩) T₂a.head
            ⟨i.1, by omega⟩) = enc T₁.head := by
        funext i; rcases Nat.lt_or_ge i.1 (l - 1) with hi | hi
        · simp [tupleSnoc_lt _ _ i.1 hi]
        · have hil : i.1 = l - 1 := by omega
          rw [show (⟨i.1, by omega⟩ : Fin ((l - 1) + 1)) = ⟨l - 1, Nat.lt_succ_self _⟩ from
            Fin.ext hil, tupleSnoc_eq, hhead_a]
          exact congrArg (enc T₁.head) (Fin.ext hil.symm)
      rcases htr : M.trans q T₁.head with ⟨_ | q', e', dir⟩
      · refine ⟨l, hl, ?_⟩
        have hstep_halt :
            M'.step ⟨some (.sweep1 q ⟨l - 1, by omega⟩
                (fun i ↦ enc T₁.head ⟨i.1, by omega⟩)), T₂a⟩ =
              ⟨none, (T₂a.write T₂a.head).move .right⟩ := by
          rw [BiInfTM.step_some]; dsimp [M', blockSimTM, blockSimTrans]
          rw [dite_eq_right (by omega)]; simp only [hw_eq, decodeBlock_enc, htr]
        have hsplit : M'.step^[l] ⟨some (.sweep1 q ⟨0, hl⟩ finZeroElim), T₂⟩ =
            M'.step (M'.step^[l - 1] ⟨some (.sweep1 q ⟨0, hl⟩ finZeroElim), T₂⟩) := by
          rw [← Function.iterate_succ_apply' M'.step (l - 1)]
          exact congrFun (congrArg (Nat.iterate M'.step) (Nat.sub_add_cancel hl).symm) _
        rw [hsplit, hsw1, hstep_halt]; simp [BlockSimRel, htr]
      · by_cases hl2 : 2 ≤ l
        · have hstep_sw1_end :
              M'.step ⟨some (.sweep1 q ⟨l - 1, by omega⟩
                  (fun i ↦ enc T₁.head ⟨i.1, by omega⟩)), T₂a⟩ =
                ⟨some (.sweep23 q T₁.head false ⟨l - 2, by omega⟩),
                  (T₂a.write (enc e' ⟨l - 1, by omega⟩)).move .left⟩ := by
            rw [BiInfTM.step_some]; dsimp [M', blockSimTM, blockSimTrans]
            rw [dite_eq_right (by omega)]; simp only [hw_eq, decodeBlock_enc, htr, dite_eq_left hl2]
          let blk₁ := Function.update (enc T₁.head) ⟨l - 1, by omega⟩ (enc e' ⟨l - 1, by omega⟩)
          have hblk₁ : ∀ j : Fin l, l - 2 < j.1 → blk₁ j = enc e' j := by
            intro j hj; have hjlt := j.2
            have hjl : j = ⟨l - 1, by omega⟩ := Fin.ext (by dsimp only; omega)
            simp [blk₁, hjl]
          obtain ⟨blk', T₂b, hsw2, hblk', hTb⟩ :=
            blockSim_sweep2 M hl enc q q' T₁.head e' dir htr T₁ (l - 2) (by omega) _ blk₁ hblk₁
              ((show l - 1 - 1 = l - 2 by omega) ▸ blockTapeWith_move_left (by omega : 1 ≤ l - 1)
                (blockTapeWith_write hTa (by omega) (enc e' ⟨l - 1, by omega⟩)))
          have hTb_w : BlockTapeWith enc T₁ (enc e') 0 (T₂b.write (enc e' ⟨0, by omega⟩)) := by
            intro i j; rw [blockTapeWith_write hTb (by omega) (enc e' ⟨0, by omega⟩) i j]
            by_cases hi : i = 0
            · subst hi; simp only [ite_true]; by_cases hj0 : j = ⟨0, by omega⟩
              · simp [hj0]
              · simp [Function.update, hj0, hblk' j (Nat.pos_of_ne_zero fun h ↦ hj0 (Fin.ext h))]
            · simp [hi]
          have htot : 3 * l - 2 = (l - 1) + 1 + (l - 2) + 1 + ((l - 2) + 1) := by omega
          cases dir with
          | left =>
            have hstep_sw2_end :
                M'.step ⟨some (.sweep23 q T₁.head false ⟨0, by omega⟩), T₂b⟩ =
                  ⟨some (.sweep0 q' ⟨l - 2, by omega⟩),
                    (T₂b.write (enc e' ⟨0, by omega⟩)).move .left⟩ := by
              rw [BiInfTM.step_some]; dsimp [M', blockSimTM, blockSimTrans]; rw [htr]
            obtain ⟨T₂d, hsw0, hTd⟩ := blockSim_sweep0 M hl enc q' ((T₁.write e').move .left)
              (l - 2) (by omega) _ ((show l - 1 = (l - 2) + 1 by omega) ▸
                blockTapeWith_cross_left hl hTb_w)
            refine ⟨3 * l - 2, by omega, ?_⟩
            rw [htot, ← iterate_comp_five M'.step (l - 1) (l - 2) ((l - 2) + 1),
              hsw1, hstep_sw1_end, hsw2, hstep_sw2_end, hsw0]
            simp [BlockSimRel, htr, hTd]
          | right =>
            have hstep_sw2_end :
                M'.step ⟨some (.sweep23 q T₁.head false ⟨0, by omega⟩), T₂b⟩ =
                  ⟨some (.sweep23 q T₁.head true ⟨0, by omega⟩),
                    (T₂b.write (enc e' ⟨0, by omega⟩)).move .right⟩ := by
              rw [BiInfTM.step_some]; dsimp [M', blockSimTM, blockSimTrans]; rw [htr]
            obtain ⟨T₂d, hsw3, hTd⟩ := blockSim_sweep3 M hl enc q q' T₁.head e' .right htr T₁ hl2
              (l - 2) le_rfl _ ((show 0 + 1 = l - 1 - (l - 2) by omega) ▸
                blockTapeWith_move_right hTb_w)
            have hsw3' : M'.step^[(l - 2) + 1] ⟨some (.sweep23 q T₁.head true ⟨0, by omega⟩),
                (T₂b.write (enc e' ⟨0, by omega⟩)).move .right⟩ =
                ⟨some (.sweep1 q' ⟨0, hl⟩ finZeroElim), T₂d⟩ := by
              rwa [show (⟨0, by omega⟩ : Fin (l - 1)) = ⟨l - 2 - (l - 2), by omega⟩ from
                Fin.ext (by dsimp only; omega)]
            refine ⟨3 * l - 2, by omega, ?_⟩
            rw [htot, ← iterate_comp_five M'.step (l - 1) (l - 2) ((l - 2) + 1),
              hsw1, hstep_sw1_end, hsw2, hstep_sw2_end, hsw3']
            simp [BlockSimRel, htr, hTd]
        · have hl1 : l = 1 := by omega
          subst hl1; refine ⟨1, le_rfl, ?_⟩
          have hstep1 : M'.step ⟨some (.sweep1 q ⟨0, hl⟩ finZeroElim), T₂⟩ =
              ⟨some (.sweep1 q' ⟨0, hl⟩ finZeroElim), (T₂.write (enc e' ⟨0, hl⟩)).move dir⟩ := by
            rw [BiInfTM.step_some]; dsimp [M', blockSimTM, blockSimTrans]
            have hw1 : (fun i : Fin 1 ↦ tupleSnoc finZeroElim T₂.head i) = enc T₁.head := by
              funext i
              have hi0 : i = ⟨0, hl⟩ := Fin.ext (Fin.val_eq_zero i)
              rw [hi0]
              simpa [tupleSnoc] using blockTapeWith_head hT hl
            simp only [hw1, decodeBlock_enc, htr]
          rw [Function.iterate_one, hstep1]
          simp only [BiInfTM.step_some, htr, BlockSimRel, true_and]
          have hTw : BlockTapeWith enc T₁ (enc e') 0 (T₂.write (enc e' ⟨0, hl⟩)) := by
            intro i j; rw [blockTapeWith_write hT hl (enc e' ⟨0, hl⟩) i j]
            by_cases hi : i = 0
            · subst hi
              have hj0 : j = ⟨0, hl⟩ := Fin.ext (Fin.val_eq_zero j)
              simp [hj0]
            · simp [hi]
          cases dir with
          | left => simpa using blockTapeWith_cross_left hl hTw
          | right => simpa using blockTapeWith_cross_right hl hTw
  · intro c₁ c₂ hrel; rcases c₁ with ⟨_ | q, _⟩ <;> simp only [BlockSimRel] at hrel
    · simp [hrel]
    · simp [hrel.1]

private lemma geom_sum_mul_sub_one (b k : ℕ) (hb : 1 ≤ b) :
    (∑ j : Fin k, b ^ j.1) * (b - 1) + 1 = b ^ k := by
  rw [Fin.sum_univ_eq_sum_range (fun j ↦ b ^ j) k]
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, add_mul, pow_succ]
    have hpow : 1 ≤ b ^ k := Nat.one_le_pow k b hb
    have hmul : b ^ k * (b - 1) + b ^ k = b ^ k * b := by
      rw [← Nat.mul_add_one, Nat.sub_add_cancel hb]
    omega

/-- Strict block-simulator state-count bound: for `1 ≤ n`, `2 ≤ m`, `2 ≤ b`, and `l = Nat.clog b m`,
`Fintype.card (BlockState Q E b l) < 2 * (m + 1) * n * l`. -/
theorem card_blockState_lt (Q E : Type*) [Fintype Q] [Fintype E] {b : ℕ}
    (hn : 1 ≤ Fintype.card Q) (hm : 2 ≤ Fintype.card E) (hb : 2 ≤ b) :
    let l := Nat.clog b (Fintype.card E)
    Fintype.card (BlockState Q E b l) < 2 * (Fintype.card E + 1) * Fintype.card Q * l := by
  intro l; rw [card_blockState]
  set n := Fintype.card Q; set m := Fintype.card E
  have hl : 1 ≤ l := Nat.clog_pos hb hm
  have hpow_l : b ^ l < b * m := by
    have hpred : b ^ (l - 1) < m := by
      by_contra! hge
      have hle : l ≤ l - 1 := (Nat.clog_le_iff_le_pow (by omega)).mpr hge
      omega
    rw [← Nat.sub_add_cancel hl, pow_succ']
    exact Nat.mul_lt_mul_of_pos_left hpred (by omega)
  have hgeom : (∑ j : Fin l, b ^ j.1) * (b - 1) + 1 = b ^ l := geom_sum_mul_sub_one b l (by omega)
  have hbm_le : b * m ≤ 2 * m * (b - 1) := by
    calc b * m ≤ (2 * (b - 1)) * m := Nat.mul_le_mul_right m (by omega)
      _ = 2 * m * (b - 1) := by ring
  have hsum_mul_lt : (∑ j : Fin l, b ^ j.1) * (b - 1) < 2 * m * (b - 1) := by omega
  have hsum_lt : ∑ j : Fin l, b ^ j.1 < 2 * m := Nat.lt_of_mul_lt_mul_right hsum_mul_lt
  have h2m : 2 * m + 2 * m * (l - 1) = 2 * m * l := by
    calc 2 * m + 2 * m * (l - 1) = 2 * m * (1 + (l - 1)) := by ring
      _ = 2 * m * l := by rw [Nat.add_sub_of_le hl]
  have hinner : (l - 1) + ∑ j : Fin l, b ^ j.1 + 2 * m * (l - 1) < 2 * (m + 1) * l := by
    have : 2 * (m + 1) * l = 2 * m * l + 2 * l := by ring
    omega
  calc n * ((l - 1) + ∑ j : Fin l, b ^ j.1 + 2 * m * (l - 1))
      < n * (2 * (m + 1) * l) := Nat.mul_lt_mul_of_pos_left hinner hn
    _ = 2 * (m + 1) * n * l := by ring

/-- Existence of an alphabet-reduced machine over `Fin b`. -/
theorem exists_alphabetReduction_tm {Q E : Type*} [Fintype Q] [Fintype E] [Inhabited E]
    (M : BiInfTM Q E) {b : ℕ} [NeZero b] (hb : 2 ≤ b) (hm : 2 ≤ Fintype.card E)
    (hM : M.HaltsOnBlank) :
    let n := Fintype.card Q
    let m := Fintype.card E
    let l := Nat.clog b m
    let n' := n * ((l - 1) + ∑ j : Fin l, b ^ j.1 + 2 * m * (l - 1))
    n' < 2 * (m + 1) * n * l ∧
      ∃ M' : BiInfTM (Fin n') (Fin b), M'.HaltsOnBlank ∧ M.time ≤ M'.time := by
  classical
  dsimp only
  set n := Fintype.card Q; set m := Fintype.card E; set l := Nat.clog b m
  have hl : 1 ≤ l := Nat.clog_pos hb hm
  have hlt := card_blockState_lt Q E (Fintype.card_pos_iff.mpr ⟨M.initState⟩) hm hb
  dsimp only at hlt; rw [card_blockState] at hlt
  obtain ⟨enc, henc⟩ := exists_block_enc E hb
  obtain ⟨hh, hle⟩ := blockSimTM_halts_and_time_le M hl enc henc hM
  let eQ := Fintype.equivFinOfCardEq (card_blockState Q E b l)
  let M' := (blockSimTM M hl enc).mapEquiv eQ (Equiv.refl (Fin b))
  refine ⟨hlt, M', (BiInfTM.haltsOnBlank_mapEquiv_iff _ eQ (Equiv.refl (Fin b)) rfl).mpr hh, ?_⟩
  simpa [M', BiInfTM.time_mapEquiv _ eQ (Equiv.refl (Fin b)) rfl] using hle

/-- Busy Beaver bound from alphabet reduction: for `2 ≤ b`, `2 ≤ |E|`, and any
halting machine `M : BiInfTM Q E`, `M.time ≤ busyBeaver n' b ≤ busyBeaver (2 * (m + 1) * n * l) b`.
-/
theorem busyBeaver_alphabetReduction {Q E : Type*} [Fintype Q] [Fintype E] [Inhabited E]
    (M : BiInfTM Q E) {b : ℕ} (hb : 2 ≤ b) (hm : 2 ≤ Fintype.card E)
    (hM : M.HaltsOnBlank) :
    let l := Nat.clog b (Fintype.card E)
    let n' := Fintype.card Q * ((l - 1) + ∑ j : Fin l, b ^ j.1 + 2 * Fintype.card E * (l - 1))
    n' < 2 * (Fintype.card E + 1) * Fintype.card Q * l ∧
      M.time ≤ busyBeaver n' b ∧
      M.time ≤ busyBeaver (2 * (Fintype.card E + 1) * Fintype.card Q * l) b := by
  let _ : NeZero b := ⟨by omega⟩; dsimp only
  set l := Nat.clog b (Fintype.card E)
  set n' := Fintype.card Q * ((l - 1) + ∑ j : Fin l, b ^ j.1 + 2 * Fintype.card E * (l - 1))
  obtain ⟨hlt, M', _, hle⟩ := exists_alphabetReduction_tm M hb hm hM
  have hl : 1 ≤ l := Nat.clog_pos hb hm
  have hsum_pos : 1 ≤ ∑ j : Fin l, b ^ j.1 := by
    rw [← Nat.sub_add_cancel hl, Fin.sum_univ_succ]; simp
  have hn'1 : 1 ≤ n' := Nat.mul_pos (Fintype.card_pos_iff.mpr ⟨M.initState⟩) (by omega)
  let _ : NeZero n' := ⟨by omega⟩
  have hbb1 : M.time ≤ busyBeaver n' b := hle.trans (time_le_busyBeaver_fin M')
  exact ⟨hlt, hbb1, hbb1.trans (busyBeaver_mono hn'1 hlt.le (by omega) le_rfl)⟩

end GeneralBlockSimulator

/-- Generalized Busy Beaver alphabet-reduction inequality: for `1 ≤ n`, `2 ≤ m`, and `2 ≤ b`,
`busyBeaver n m ≤ busyBeaver (2 * (m + 1) * n * Nat.clog b m) b`. -/
theorem busyBeaver_le_alphabetReduction {n m b : ℕ} (hn : 1 ≤ n) (hm : 2 ≤ m) (hb : 2 ≤ b) :
    busyBeaver n m ≤ busyBeaver (2 * (m + 1) * n * Nat.clog b m) b := by
  let _ : NeZero n := ⟨by omega⟩
  let _ : NeZero m := ⟨by omega⟩
  obtain ⟨M, hM⟩ := exists_time_eq_busyBeaver n m
  by_cases hhalt : M.HaltsOnBlank
  · rw [← hM]
    simpa only [Fintype.card_fin] using
      (busyBeaver_alphabetReduction M hb (by simpa using hm) hhalt).2.2
  · rw [← hM, BiInfTM.time_of_not_haltsOnBlank hhalt]
    exact Nat.zero_le _

end CslibFrontier.Computability.BusyBeaver
