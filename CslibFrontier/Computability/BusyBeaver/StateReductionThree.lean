/-
Copyright (c) 2026 Cslib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Papers contributors
-/

module

public import CslibFrontier.Computability.BusyBeaver.TuringMachine
public import Mathlib.Data.Fintype.EquivFin

/-!
# Universal Three-State Reduction for Bi-Infinite Turing Machines

Simulates any blank-tape halting bi-infinite Turing machine with `n` states and `m` symbols on the
all-blank tape using `3` control states and `3 * (n + 1) * m` tape symbols without decreasing
halting time, yielding `busyBeaver n m ≤ busyBeaver 3 (3 * (n + 1) * m)` for all `n, m ≥ 1`.
-/

public section

namespace CslibFrontier.Computability.BusyBeaver

section Types

/-- Three-state control set `{qX, qL, qR}` for the 3-state simulator. -/
inductive State3 : Type
  | qX
  | qL
  | qR
  deriving DecidableEq, Inhabited

/-- Finite enumeration of the three control states in `State3`. -/
instance State3.instFintype : Fintype State3 where
  elems := {.qX, .qL, .qR}
  complete q := by cases q <;> simp

/-- There are `3` control states in `State3`. -/
@[simp] theorem card_state3 : Fintype.card State3 = 3 := rfl

/-- Transfer control state associated with a head movement direction. -/
def State3.ofDir : Turing.Dir → State3
  | .left => .qL
  | .right => .qR

theorem State3.ofDir_def :
    State3.ofDir = fun d ↦ match d with | .left => .qL | .right => .qR := by rfl

@[simp, grind =] theorem State3.ofDir_left : State3.ofDir .left = .qL := by rfl

@[simp, grind =] theorem State3.ofDir_right : State3.ofDir .right = .qR := by rfl

/-- Explicit equivalence between `State3` and `Fin 3`. -/
def State3.equivFin : State3 ≃ Fin 3 where
  toFun
    | .qX => 0
    | .qL => 1
    | .qR => 2
  invFun
    | ⟨0, _⟩ => .qX
    | ⟨1, _⟩ => .qL
    | ⟨2, _⟩ => .qR
  left_inv q := by cases q <;> rfl
  right_inv i := by
    rcases i with ⟨_ | _ | _ | _, hi⟩
    · rfl
    · rfl
    · rfl
    · omega

theorem State3.equivFin_def :
    State3.equivFin =
      { toFun := fun q ↦ match q with | .qX => 0 | .qL => 1 | .qR => 2
        invFun := fun i ↦ match i with | ⟨0, _⟩ => .qX | ⟨1, _⟩ => .qL | ⟨2, _⟩ => .qR
        left_inv := fun q ↦ by cases q <;> rfl
        right_inv := fun i ↦ by
          rcases i with ⟨_ | _ | _ | _, hi⟩
          · rfl
          · rfl
          · rfl
          · omega } := by rfl

@[simp, grind =] theorem State3.equivFin_qX : State3.equivFin .qX = 0 := by rfl

@[simp, grind =] theorem State3.equivFin_qL : State3.equivFin .qL = 1 := by rfl

@[simp, grind =] theorem State3.equivFin_qR : State3.equivFin .qR = 2 := by rfl

@[simp, grind =] theorem State3.equivFin_symm_zero : State3.equivFin.symm 0 = .qX := by rfl

@[simp, grind =] theorem State3.equivFin_symm_one : State3.equivFin.symm 1 = .qL := by rfl

@[simp, grind =] theorem State3.equivFin_symm_two : State3.equivFin.symm 2 = .qR := by rfl

/-- Expanded tape symbol for the 3-state simulator, encoding a unary state counter in
`Fin (n + 1)` (`0` when idle, `q.1 + 1` for state `q : Fin n`), an optional transfer direction
(`none` for idle `X`, `some d` for active transfer in direction `d`), and a symbol in `E`. -/
@[ext]
structure Sym3 (n : ℕ) (E : Type*) where
  /-- Unary state counter (`0` when idle or `q.1 + 1` for `q : Fin n`). -/
  count : Fin (n + 1)
  /-- Transfer direction (`none` for `X`, `some d` during unary transfer). -/
  dir : Option Turing.Dir
  /-- Underlying symbol from the original tape alphabet `E`. -/
  sym : E
  deriving DecidableEq

/-- Default blank symbol `⟨0, none, default⟩` on the simulator tape. -/
instance Sym3.instInhabited {n : ℕ} {E : Type*} [Inhabited E] : Inhabited (Sym3 n E) :=
  ⟨⟨0, none, default⟩⟩

@[simp, grind =] theorem Sym3.default_eq {n : ℕ} {E : Type*} [Inhabited E] :
    (default : Sym3 n E) = ⟨0, none, default⟩ := by rfl

/-- Equivalence between `Sym3 n E` and `Fin (n + 1) × Option Turing.Dir × E`. -/
def Sym3.equivProd (n : ℕ) (E : Type*) : Sym3 n E ≃ Fin (n + 1) × Option Turing.Dir × E where
  toFun s := (s.count, s.dir, s.sym)
  invFun p := ⟨p.1, p.2.1, p.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem Sym3.equivProd_def (n : ℕ) (E : Type*) :
    Sym3.equivProd n E =
      { toFun := fun s ↦ (s.count, s.dir, s.sym)
        invFun := fun p ↦ ⟨p.1, p.2.1, p.2.2⟩
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl } := by rfl

@[simp, grind =] theorem Sym3.equivProd_apply {n : ℕ} {E : Type*} (s : Sym3 n E) :
    Sym3.equivProd n E s = (s.count, s.dir, s.sym) := by rfl

@[simp, grind =] theorem Sym3.equivProd_symm_apply {n : ℕ} {E : Type*}
    (p : Fin (n + 1) × Option Turing.Dir × E) :
    (Sym3.equivProd n E).symm p = ⟨p.1, p.2.1, p.2.2⟩ := by rfl

/-- Finite enumeration of `Sym3 n E` whenever `E` is finite. -/
instance Sym3.instFintype {n : ℕ} {E : Type*} [Fintype E] : Fintype (Sym3 n E) :=
  Fintype.ofEquiv _ (Sym3.equivProd n E).symm

/-- Exact cardinality of the expanded simulator alphabet `Sym3 n E`. -/
@[simp] theorem card_sym3 (n : ℕ) (E : Type*) [Fintype E] :
    Fintype.card (Sym3 n E) = 3 * (n + 1) * Fintype.card E := by
  rw [Fintype.card_congr (Sym3.equivProd n E), Fintype.card_prod, Fintype.card_prod,
    Fintype.card_fin, Fintype.card_option, card_turingDir, show 2 + 1 = 3 from rfl,
    Nat.mul_left_comm, Nat.mul_assoc]

end Types

section Machine

private def simExpand {Q E : Type*} [Inhabited E] {n : ℕ}
    (eQ : Q ≃ Fin n) (M : BiInfTM Q E) (q : Q) (e : E) :
    Option State3 × Sym3 n E × Turing.Dir :=
  match M.trans q e with
  | (none, _, _) => (none, default, .right)
  | (some q', e', d') =>
    (some (State3.ofDir d'), ⟨(eQ q').castSucc, some d', e'⟩, d')

private def clampInc {n : ℕ} (c : Fin (n + 1)) : Fin (n + 1) :=
  if h : c.1 < n then ⟨c.1 + 1, Nat.succ_lt_succ h⟩ else c

/-- Transition function of the 3-state simulator relative to `eQ : Q ≃ Fin n`. -/
def stateThreeTrans {Q E : Type*} [Inhabited E] {n : ℕ}
    (eQ : Q ≃ Fin n) (M : BiInfTM Q E) :
    State3 → Sym3 n E → Option State3 × Sym3 n E × Turing.Dir
  | .qX, ⟨⟨0, _⟩, some d, e⟩ => (some .qX, ⟨0, none, e⟩, d)
  | .qX, ⟨⟨k + 1, hk⟩, some d, e⟩ =>
    (some (State3.ofDir d), ⟨⟨k, Nat.lt_of_succ_lt hk⟩, some d, e⟩, d)
  | .qX, ⟨⟨0, _⟩, none, e⟩ => simExpand eQ M M.initState e
  | .qX, ⟨⟨k + 1, hk⟩, none, e⟩ => simExpand eQ M (eQ.symm ⟨k, Nat.lt_of_succ_lt_succ hk⟩) e
  | .qL, ⟨c, none, e⟩ => (some .qX, ⟨clampInc c, none, e⟩, .right)
  | .qR, ⟨c, none, e⟩ => (some .qX, ⟨clampInc c, none, e⟩, .left)
  | .qL, ⟨_, some _, _⟩ => (none, default, .right)
  | .qR, ⟨_, some _, _⟩ => (none, default, .right)

theorem stateThreeTrans_def {Q E : Type*} [Inhabited E] {n : ℕ}
    (eQ : Q ≃ Fin n) (M : BiInfTM Q E) (st : State3) (s : Sym3 n E) :
    stateThreeTrans eQ M st s =
      match st, s with
      | .qX, ⟨⟨0, _⟩, some d, e⟩ => (some .qX, ⟨0, none, e⟩, d)
      | .qX, ⟨⟨k + 1, hk⟩, some d, e⟩ =>
        (some (State3.ofDir d), ⟨⟨k, Nat.lt_of_succ_lt hk⟩, some d, e⟩, d)
      | .qX, ⟨⟨0, _⟩, none, e⟩ =>
        match M.trans M.initState e with
        | (none, _, _) => (none, default, .right)
        | (some q', e', d') => (some (State3.ofDir d'), ⟨(eQ q').castSucc, some d', e'⟩, d')
      | .qX, ⟨⟨k + 1, hk⟩, none, e⟩ =>
        match M.trans (eQ.symm ⟨k, Nat.lt_of_succ_lt_succ hk⟩) e with
        | (none, _, _) => (none, default, .right)
        | (some q', e', d') => (some (State3.ofDir d'), ⟨(eQ q').castSucc, some d', e'⟩, d')
      | .qL, ⟨c, none, e⟩ =>
        (some .qX, ⟨if h : c.1 < n then ⟨c.1 + 1, Nat.succ_lt_succ h⟩ else c, none, e⟩, .right)
      | .qR, ⟨c, none, e⟩ =>
        (some .qX, ⟨if h : c.1 < n then ⟨c.1 + 1, Nat.succ_lt_succ h⟩ else c, none, e⟩, .left)
      | .qL, ⟨_, some _, _⟩ => (none, default, .right)
      | .qR, ⟨_, some _, _⟩ => (none, default, .right) := by
  cases st with
  | qX =>
    rcases s with ⟨⟨_ | k, hk⟩, _ | d, e⟩ <;> rfl
  | qL =>
    rcases s with ⟨c, _ | d, e⟩ <;> rfl
  | qR =>
    rcases s with ⟨c, _ | d, e⟩ <;> rfl

@[simp] theorem stateThreeTrans_qX_zero_some {Q E : Type*} [Inhabited E] {n : ℕ}
    (eQ : Q ≃ Fin n) (M : BiInfTM Q E) (d : Turing.Dir) (e : E) :
    stateThreeTrans eQ M .qX ⟨0, some d, e⟩ = (some .qX, ⟨0, none, e⟩, d) := by rfl

@[simp] theorem stateThreeTrans_qX_succ_some {Q E : Type*} [Inhabited E] {n : ℕ}
    (eQ : Q ≃ Fin n) (M : BiInfTM Q E) (k : Fin n) (d : Turing.Dir) (e : E) :
    stateThreeTrans eQ M .qX ⟨k.succ, some d, e⟩ =
      (some (State3.ofDir d), ⟨k.castSucc, some d, e⟩, d) := by rfl

@[simp] theorem stateThreeTrans_qX_zero_none {Q E : Type*} [Inhabited E] {n : ℕ}
    (eQ : Q ≃ Fin n) (M : BiInfTM Q E) (e : E) :
    stateThreeTrans eQ M .qX ⟨0, none, e⟩ =
      match M.trans M.initState e with
      | (none, _, _) => (none, default, .right)
      | (some q', e', d') => (some (State3.ofDir d'), ⟨(eQ q').castSucc, some d', e'⟩, d') := by
  rfl

@[simp] theorem stateThreeTrans_qX_succ_none {Q E : Type*} [Inhabited E] {n : ℕ}
    (eQ : Q ≃ Fin n) (M : BiInfTM Q E) (k : Fin n) (e : E) :
    stateThreeTrans eQ M .qX ⟨k.succ, none, e⟩ =
      match M.trans (eQ.symm k) e with
      | (none, _, _) => (none, default, .right)
      | (some q', e', d') => (some (State3.ofDir d'), ⟨(eQ q').castSucc, some d', e'⟩, d') := by
  rfl

@[simp] theorem stateThreeTrans_qL_none {Q E : Type*} [Inhabited E] {n : ℕ}
    (eQ : Q ≃ Fin n) (M : BiInfTM Q E) (c : Fin (n + 1)) (e : E) :
    stateThreeTrans eQ M .qL ⟨c, none, e⟩ =
      (some .qX, ⟨if h : c.1 < n then ⟨c.1 + 1, Nat.succ_lt_succ h⟩ else c, none, e⟩, .right) := by
  rfl

@[simp] theorem stateThreeTrans_qR_none {Q E : Type*} [Inhabited E] {n : ℕ}
    (eQ : Q ≃ Fin n) (M : BiInfTM Q E) (c : Fin (n + 1)) (e : E) :
    stateThreeTrans eQ M .qR ⟨c, none, e⟩ =
      (some .qX, ⟨if h : c.1 < n then ⟨c.1 + 1, Nat.succ_lt_succ h⟩ else c, none, e⟩, .left) := by
  rfl

@[simp] theorem stateThreeTrans_qL_some {Q E : Type*} [Inhabited E] {n : ℕ}
    (eQ : Q ≃ Fin n) (M : BiInfTM Q E) (c : Fin (n + 1)) (d : Turing.Dir) (e : E) :
    stateThreeTrans eQ M .qL ⟨c, some d, e⟩ = (none, default, .right) := by rfl

@[simp] theorem stateThreeTrans_qR_some {Q E : Type*} [Inhabited E] {n : ℕ}
    (eQ : Q ≃ Fin n) (M : BiInfTM Q E) (c : Fin (n + 1)) (d : Turing.Dir) (e : E) :
    stateThreeTrans eQ M .qR ⟨c, some d, e⟩ = (none, default, .right) := by rfl

/-- 3-state simulator of `M` parameterized by an explicit enumeration `eQ : Q ≃ Fin n`. -/
def stateThreeTMOfEquiv {Q E : Type*} [Inhabited E] {n : ℕ}
    (eQ : Q ≃ Fin n) (M : BiInfTM Q E) : BiInfTM State3 (Sym3 n E) where
  initState := .qX
  trans := stateThreeTrans eQ M

theorem stateThreeTMOfEquiv_def {Q E : Type*} [Inhabited E] {n : ℕ}
    (eQ : Q ≃ Fin n) (M : BiInfTM Q E) :
    stateThreeTMOfEquiv eQ M = ⟨.qX, stateThreeTrans eQ M⟩ := by rfl

@[simp, grind =] theorem stateThreeTMOfEquiv_initState {Q E : Type*} [Inhabited E] {n : ℕ}
    (eQ : Q ≃ Fin n) (M : BiInfTM Q E) :
    (stateThreeTMOfEquiv eQ M).initState = .qX := by rfl

@[simp, grind =] theorem stateThreeTMOfEquiv_trans {Q E : Type*} [Inhabited E] {n : ℕ}
    (eQ : Q ≃ Fin n) (M : BiInfTM Q E) (st : State3) (s : Sym3 n E) :
    (stateThreeTMOfEquiv eQ M).trans st s = stateThreeTrans eQ M st s := by rfl

/-- Canonical 3-state simulator `stateThreeTM M` of `M : BiInfTM Q E`. -/
noncomputable def stateThreeTM {Q E : Type*} [Fintype Q] [Inhabited E]
    (M : BiInfTM Q E) : BiInfTM State3 (Sym3 (Fintype.card Q) E) :=
  stateThreeTMOfEquiv (Fintype.equivFin Q) M

theorem stateThreeTM_def {Q E : Type*} [Fintype Q] [Inhabited E] (M : BiInfTM Q E) :
    stateThreeTM M = stateThreeTMOfEquiv (Fintype.equivFin Q) M := by rfl

@[simp, grind =] theorem stateThreeTM_initState {Q E : Type*} [Fintype Q] [Inhabited E]
    (M : BiInfTM Q E) : (stateThreeTM M).initState = .qX := by rfl

@[simp, grind =] theorem stateThreeTM_trans {Q E : Type*} [Fintype Q] [Inhabited E]
    (M : BiInfTM Q E) (st : State3) (s : Sym3 (Fintype.card Q) E) :
    (stateThreeTM M).trans st s = stateThreeTrans (Fintype.equivFin Q) M st s := by rfl

end Machine

section Simulation

private def dirStep : Turing.Dir → ℤ
  | .left => -1
  | .right => 1

private def oppDir : Turing.Dir → Turing.Dir
  | .left => .right
  | .right => .left

private lemma tape_move_nth {E : Type*} [Inhabited E] (T : Turing.Tape E) (d : Turing.Dir)
    (i : ℤ) : (T.move d).nth i = T.nth (i + dirStep d) := by
  cases d
  · simp [dirStep, sub_eq_add_neg]
  · simp [dirStep]

private lemma dirStep_ne_zero (d : Turing.Dir) : dirStep d ≠ 0 := by
  cases d <;> simp [dirStep]

private lemma dirStep_opp (d : Turing.Dir) : dirStep (oppDir d) = -dirStep d := by
  cases d <;> simp [dirStep, oppDir]

private def Sim3Rel {Q E : Type*} [Inhabited E] {n : ℕ}
    (eQ : Q ≃ Fin n) (M : BiInfTM Q E)
    (c₁ : Cfg Q E) (c₂ : Cfg State3 (Sym3 n E)) : Prop :=
  match c₁.state with
  | none => c₂.state = none
  | some q =>
      c₂.state = some .qX ∧
      (∀ i : ℤ, i ≠ 0 → c₂.tape.nth i = ⟨0, none, c₁.tape.nth i⟩) ∧
      (c₂.tape.nth 0 = ⟨(eQ q).succ, none, c₁.tape.head⟩ ∨
        (q = M.initState ∧ c₂.tape.nth 0 = ⟨0, none, c₁.tape.head⟩))

private lemma sim3_loop_step {Q E : Type*} [Inhabited E] {n : ℕ}
    (eQ : Q ≃ Fin n) (M : BiInfTM Q E) (d' : Turing.Dir) (e' : E)
    (T_orig : Turing.Tape E) :
    ∀ (a b : ℕ) (ha : a < n) (hb : b ≤ n) (hab : a + b ≤ n)
      (T₂ : Turing.Tape (Sym3 n E)),
      T₂.nth 0 = ⟨⟨a, Nat.lt_succ_of_lt ha⟩, some d', e'⟩ →
      T₂.nth (dirStep d') = ⟨⟨b, Nat.lt_succ_of_le hb⟩, none, T_orig.nth (dirStep d')⟩ →
      (∀ j : ℤ, j ≠ 0 → j ≠ dirStep d' → T₂.nth j = ⟨0, none, T_orig.nth j⟩) →
      ∃ T₂' : Turing.Tape (Sym3 n E),
        (stateThreeTMOfEquiv eQ M).step^[2 * a] ⟨some .qX, T₂⟩ = ⟨some .qX, T₂'⟩ ∧
        T₂'.nth 0 = ⟨0, some d', e'⟩ ∧
        T₂'.nth (dirStep d') =
          ⟨⟨a + b, Nat.lt_succ_of_le hab⟩, none, T_orig.nth (dirStep d')⟩ ∧
        (∀ j : ℤ, j ≠ 0 → j ≠ dirStep d' → T₂'.nth j = ⟨0, none, T_orig.nth j⟩) := by
  intro a
  induction a with
  | zero =>
    intro b _ _ _ T₂ h0 hnb hrest
    exact ⟨T₂, rfl, h0, by simpa using hnb, hrest⟩
  | succ a ih =>
    intro b ha hb hab T₂ h0 hnb hrest
    let aFin : Fin n := ⟨a, Nat.lt_of_succ_lt ha⟩
    have hsucc : (⟨a + 1, Nat.lt_succ_of_lt ha⟩ : Fin (n + 1)) = aFin.succ := rfl
    have hhead : T₂.head = ⟨aFin.succ, some d', e'⟩ := by
      rw [← Turing.Tape.nth_zero, h0, hsucc]
    have hstep1 :
        (stateThreeTMOfEquiv eQ M).step ⟨some .qX, T₂⟩ =
          ⟨some (State3.ofDir d'),
            (T₂.write ⟨aFin.castSucc, some d', e'⟩).move d'⟩ := by
      rw [BiInfTM.step_some, stateThreeTMOfEquiv_trans, hhead, stateThreeTrans_qX_succ_some]
    let T_mid := (T₂.write ⟨aFin.castSucc, some d', e'⟩).move d'
    have hmid_head : T_mid.head = ⟨⟨b, Nat.lt_succ_of_le hb⟩, none, T_orig.nth (dirStep d')⟩ := by
      rw [← Turing.Tape.nth_zero]
      change ((T₂.write ⟨aFin.castSucc, some d', e'⟩).move d').nth 0 = _
      rw [tape_move_nth, zero_add, Turing.Tape.write_nth,
        ite_eq_right_iff.mpr (fun h ↦ absurd h (dirStep_ne_zero d')), hnb]
    have hstep2 :
        (stateThreeTMOfEquiv eQ M).step ⟨some (State3.ofDir d'), T_mid⟩ =
          ⟨some .qX,
            (T_mid.write ⟨⟨b + 1, Nat.lt_succ_of_le (by omega)⟩, none,
              T_orig.nth (dirStep d')⟩).move (oppDir d')⟩ := by
      cases d'
      · rw [State3.ofDir_left, BiInfTM.step_some, stateThreeTMOfEquiv_trans, hmid_head,
          stateThreeTrans_qL_none]
        have hlt : b < n := by omega
        simp [hlt, oppDir]
      · rw [State3.ofDir_right, BiInfTM.step_some, stateThreeTMOfEquiv_trans, hmid_head,
          stateThreeTrans_qR_none]
        have hlt : b < n := by omega
        simp [hlt, oppDir]
    let T_next :=
      (T_mid.write ⟨⟨b + 1, Nat.lt_succ_of_le (by omega)⟩, none,
        T_orig.nth (dirStep d')⟩).move (oppDir d')
    have h_two :
        (stateThreeTMOfEquiv eQ M).step^[2] ⟨some .qX, T₂⟩ = ⟨some .qX, T_next⟩ := by
      rw [Function.iterate_succ_apply, Function.iterate_one, hstep1, hstep2]
    have hnext_nth : ∀ j : ℤ,
        T_next.nth j =
          if j = dirStep d' then
            ⟨⟨b + 1, Nat.lt_succ_of_le (by omega)⟩, none, T_orig.nth (dirStep d')⟩
          else if j = 0 then ⟨aFin.castSucc, some d', e'⟩
          else T₂.nth j := by
      intro j
      dsimp only [T_next, T_mid]
      rw [tape_move_nth, dirStep_opp, Turing.Tape.write_nth]
      by_cases hj1 : j + -dirStep d' = 0
      · have hj : j = dirStep d' := by omega
        rw [ite_eq_left_iff.mpr (fun h ↦ absurd hj1 h), ite_eq_left_iff.mpr (fun h ↦ absurd hj h)]
      · have hj : j ≠ dirStep d' := by omega
        rw [ite_eq_right_iff.mpr (fun h ↦ absurd h hj1), ite_eq_right_iff.mpr (fun h ↦ absurd h hj),
          tape_move_nth, Turing.Tape.write_nth, show j + -dirStep d' + dirStep d' = j by omega]
    have hnext_0 : T_next.nth 0 = ⟨⟨a, Nat.lt_succ_of_lt (Nat.lt_of_succ_lt ha)⟩, some d', e'⟩ := by
      rw [hnext_nth 0, ite_eq_right_iff.mpr (fun h ↦ absurd h (dirStep_ne_zero d').symm),
        ite_eq_left_iff.mpr (fun h ↦ absurd rfl h)]
      rfl
    have hnext_nb :
        T_next.nth (dirStep d') =
          ⟨⟨b + 1, Nat.lt_succ_of_le (by omega)⟩, none, T_orig.nth (dirStep d')⟩ := by
      rw [hnext_nth (dirStep d'), ite_eq_left_iff.mpr (fun h ↦ absurd rfl h)]
    have hnext_rest : ∀ j : ℤ, j ≠ 0 → j ≠ dirStep d' →
        T_next.nth j = ⟨0, none, T_orig.nth j⟩ := by
      intro j hj0 hjnb
      rw [hnext_nth j, ite_eq_right_iff.mpr (fun h ↦ absurd h hjnb),
        ite_eq_right_iff.mpr (fun h ↦ absurd h hj0), hrest j hj0 hjnb]
    obtain ⟨T₂', hiter, h0', hnb', hrest'⟩ :=
      ih (b + 1) (Nat.lt_of_succ_lt ha) (by omega) (by omega) T_next hnext_0 hnext_nb hnext_rest
    refine ⟨T₂', ?_, h0', ?_, hrest'⟩
    · rw [show 2 * (a + 1) = 2 * a + 2 by omega, Function.iterate_add_apply, h_two, hiter]
    · rw [hnb', Sym3.ext_iff]
      exact ⟨Fin.ext (by dsimp; omega), rfl, rfl⟩

private lemma sim3_step {Q E : Type*} [Inhabited E] {n : ℕ}
    (eQ : Q ≃ Fin n) (M : BiInfTM Q E) :
    ∀ c₁ c₂, Sim3Rel eQ M c₁ c₂ → c₁.state ≠ none →
      ∃ k ≥ 1, Sim3Rel eQ M (M.step c₁) ((stateThreeTMOfEquiv eQ M).step^[k] c₂) := by
  intro ⟨st₁, T₁⟩ ⟨st₂, T₂⟩ hrel hne
  rcases st₁ with _ | q
  · exact absurd rfl hne
  rcases hrel with ⟨rfl, hrest, hhead⟩
  have h1_step :
      ∀ q' e' d', M.trans q T₁.head = (some q', e', d') →
        (stateThreeTMOfEquiv eQ M).step ⟨some .qX, T₂⟩ =
          ⟨some (State3.ofDir d'), (T₂.write ⟨(eQ q').castSucc, some d', e'⟩).move d'⟩ := by
    intro q' e' d' htr
    rcases hhead with hq | ⟨rfl, h0⟩
    · have hhead2 : T₂.head = ⟨(eQ q).succ, none, T₁.head⟩ := by
        rw [← Turing.Tape.nth_zero, hq]
      rw [BiInfTM.step_some, stateThreeTMOfEquiv_trans, hhead2, stateThreeTrans_qX_succ_none]
      simp [htr]
    · have hhead2 : T₂.head = ⟨0, none, T₁.head⟩ := by
        rw [← Turing.Tape.nth_zero, h0]
      rw [BiInfTM.step_some, stateThreeTMOfEquiv_trans, hhead2, stateThreeTrans_qX_zero_none]
      simp [htr]
  rcases htr : M.trans q T₁.head with ⟨_ | q', e', d'⟩
  · refine ⟨1, le_rfl, ?_⟩
    rw [Function.iterate_one, BiInfTM.step_some, BiInfTM.step_some]
    rcases hhead with hq | ⟨rfl, h0⟩
    · have hhead2 : T₂.head = ⟨(eQ q).succ, none, T₁.head⟩ := by
        rw [← Turing.Tape.nth_zero, hq]
      rw [stateThreeTMOfEquiv_trans, hhead2, stateThreeTrans_qX_succ_none]
      simp [Sim3Rel, htr]
    · have hhead2 : T₂.head = ⟨0, none, T₁.head⟩ := by
        rw [← Turing.Tape.nth_zero, h0]
      rw [stateThreeTMOfEquiv_trans, hhead2, stateThreeTrans_qX_zero_none]
      simp [Sim3Rel, htr]
  · let i' := (eQ q').1
    have hi' : i' < n := (eQ q').2
    have hn_pos : 1 ≤ n := Nat.succ_le_of_lt (Nat.zero_lt_of_lt hi')
    have hstep1 := h1_step q' e' d' htr
    let T_a := (T₂.write ⟨(eQ q').castSucc, some d', e'⟩).move d'
    have ha_head : T_a.head = ⟨0, none, T₁.nth (dirStep d')⟩ := by
      rw [← Turing.Tape.nth_zero]
      dsimp only [T_a]
      rw [tape_move_nth, zero_add, Turing.Tape.write_nth,
        ite_eq_right_iff.mpr (fun h ↦ absurd h (dirStep_ne_zero d')),
        hrest (dirStep d') (dirStep_ne_zero d')]
    have hstep2 :
        (stateThreeTMOfEquiv eQ M).step ⟨some (State3.ofDir d'), T_a⟩ =
          ⟨some .qX, (T_a.write ⟨⟨1, Nat.succ_lt_succ hn_pos⟩, none, T₁.nth (dirStep d')⟩).move
            (oppDir d')⟩ := by
      cases d'
      · rw [State3.ofDir_left, BiInfTM.step_some, stateThreeTMOfEquiv_trans, ha_head,
          stateThreeTrans_qL_none]
        have h0n : (0 : ℕ) < n := hn_pos
        simp [h0n, oppDir]
      · rw [State3.ofDir_right, BiInfTM.step_some, stateThreeTMOfEquiv_trans, ha_head,
          stateThreeTrans_qR_none]
        have h0n : (0 : ℕ) < n := hn_pos
        simp [h0n, oppDir]
    let T_b := (T_a.write ⟨⟨1, Nat.succ_lt_succ hn_pos⟩, none, T₁.nth (dirStep d')⟩).move
      (oppDir d')
    have hb_nth : ∀ j : ℤ,
        T_b.nth j =
          if j = dirStep d' then
            ⟨⟨1, Nat.succ_lt_succ hn_pos⟩, none, T₁.nth (dirStep d')⟩
          else if j = 0 then ⟨(eQ q').castSucc, some d', e'⟩
          else T₂.nth j := by
      intro j
      dsimp only [T_b, T_a]
      rw [tape_move_nth, dirStep_opp, Turing.Tape.write_nth]
      by_cases hj1 : j + -dirStep d' = 0
      · have hj : j = dirStep d' := by omega
        rw [ite_eq_left_iff.mpr (fun h ↦ absurd hj1 h), ite_eq_left_iff.mpr (fun h ↦ absurd hj h)]
      · have hj : j ≠ dirStep d' := by omega
        rw [ite_eq_right_iff.mpr (fun h ↦ absurd h hj1), ite_eq_right_iff.mpr (fun h ↦ absurd h hj),
          tape_move_nth, Turing.Tape.write_nth, show j + -dirStep d' + dirStep d' = j by omega]
    have hb_0 : T_b.nth 0 = ⟨⟨i', Nat.lt_succ_of_lt hi'⟩, some d', e'⟩ := by
      rw [hb_nth 0, ite_eq_right_iff.mpr (fun h ↦ absurd h (dirStep_ne_zero d').symm),
        ite_eq_left_iff.mpr (fun h ↦ absurd rfl h)]
      rfl
    have hb_nb : T_b.nth (dirStep d') =
        ⟨⟨1, Nat.succ_lt_succ hn_pos⟩, none, T₁.nth (dirStep d')⟩ := by
      rw [hb_nth (dirStep d'), ite_eq_left_iff.mpr (fun h ↦ absurd rfl h)]
    have hb_rest : ∀ j : ℤ, j ≠ 0 → j ≠ dirStep d' → T_b.nth j = ⟨0, none, T₁.nth j⟩ := by
      intro j hj0 hjnb
      rw [hb_nth j, ite_eq_right_iff.mpr (fun h ↦ absurd h hjnb),
        ite_eq_right_iff.mpr (fun h ↦ absurd h hj0), hrest j hj0]
    obtain ⟨T_c, hloop, hc0, hcnb, hcrest⟩ :=
      sim3_loop_step eQ M d' e' T₁ i' 1 hi' hn_pos (by omega) T_b hb_0 hb_nb hb_rest
    have hc_head : T_c.head = ⟨0, some d', e'⟩ := by rw [← Turing.Tape.nth_zero, hc0]
    have hstep4 :
        (stateThreeTMOfEquiv eQ M).step ⟨some .qX, T_c⟩ =
          ⟨some .qX, (T_c.write ⟨0, none, e'⟩).move d'⟩ := by
      rw [BiInfTM.step_some, stateThreeTMOfEquiv_trans, hc_head, stateThreeTrans_qX_zero_some]
    let T_final := (T_c.write ⟨0, none, e'⟩).move d'
    refine ⟨2 * i' + 3, by omega, ?_⟩
    have hiter_all :
        (stateThreeTMOfEquiv eQ M).step^[2 * i' + 3] ⟨some .qX, T₂⟩ = ⟨some .qX, T_final⟩ := by
      rw [show 2 * i' + 3 = (2 * i' + 2) + 1 by omega, Function.iterate_succ_apply',
        show 2 * i' + 2 = 2 * i' + 2 by rfl, Function.iterate_add_apply,
        show (2 : ℕ) = 1 + 1 by rfl, Function.iterate_succ_apply', Function.iterate_one,
        hstep1, hstep2, hloop, hstep4]
    rw [hiter_all, BiInfTM.step_some]
    dsimp only [Sim3Rel]
    rw [htr]
    refine ⟨rfl, ?_, Or.inl ?_⟩
    · intro j hj0
      dsimp only [T_final]
      rw [tape_move_nth, Turing.Tape.write_nth, tape_move_nth, Turing.Tape.write_nth]
      by_cases hjneg : j + dirStep d' = 0
      · rw [ite_eq_left_iff.mpr (fun h ↦ absurd hjneg h),
          ite_eq_left_iff.mpr (fun h ↦ absurd hjneg h)]
      · rw [ite_eq_right_iff.mpr (fun h ↦ absurd h hjneg),
          ite_eq_right_iff.mpr (fun h ↦ absurd h hjneg),
          hcrest (j + dirStep d') hjneg (by omega)]
    · dsimp only [T_final]
      rw [tape_move_nth, zero_add, Turing.Tape.write_nth,
        ite_eq_right_iff.mpr (fun h ↦ absurd h (dirStep_ne_zero d')), hcnb]
      have hsucc_eq : (⟨i' + 1, Nat.lt_succ_of_le (by omega)⟩ : Fin (n + 1)) = (eQ q').succ := rfl
      rw [hsucc_eq]
      congr 1
      rw [← Turing.Tape.nth_zero, tape_move_nth, zero_add, Turing.Tape.write_nth,
        ite_eq_right_iff.mpr (fun h ↦ absurd h (dirStep_ne_zero d'))]

end Simulation

section Theorems

/-- Parameterized 3-state simulation theorem via `eQ : Q ≃ Fin n`. -/
theorem stateThreeTMOfEquiv_halts_and_time_le {Q E : Type*} [Inhabited E] {n : ℕ}
    (eQ : Q ≃ Fin n) (M : BiInfTM Q E) (h : M.HaltsOnBlank) :
    (stateThreeTMOfEquiv eQ M).HaltsOnBlank ∧ M.time ≤ (stateThreeTMOfEquiv eQ M).time := by
  refine haltsOnBlank_and_time_le_of_rel_sim (Sim3Rel eQ M) ⟨0, ?_⟩ (sim3_step eQ M) ?_ h
  · refine ⟨rfl, fun i _ ↦ ?_, Or.inr ⟨rfl, ?_⟩⟩
    · change (default : Turing.Tape (Sym3 n E)).nth i =
        ⟨0, none, (default : Turing.Tape E).nth i⟩
      cases i with
      | ofNat k =>
        cases k with
        | zero => rfl
        | succ k =>
          change (Turing.ListBlank.mk ([] : List (Sym3 n E))).nth k =
            ⟨0, none, (Turing.ListBlank.mk ([] : List E)).nth k⟩
          simp
      | negSucc k =>
        change (Turing.ListBlank.mk ([] : List (Sym3 n E))).nth k =
          ⟨0, none, (Turing.ListBlank.mk ([] : List E)).nth k⟩
        simp
    · rfl
  · intro c₁ c₂ hrel
    rcases c₁ with ⟨_ | q, _⟩
    · exact ⟨fun _ ↦ rfl, fun _ ↦ hrel⟩
    · exact ⟨fun h2 ↦ absurd (hrel.1.symm.trans h2) (Option.some_ne_none _),
        fun h1 ↦ absurd h1 (Option.some_ne_none _)⟩

/-- The canonical 3-state simulator `stateThreeTM M` preserves blank-tape halting with
`M.time ≤ (stateThreeTM M).time`. -/
theorem stateThreeTM_halts_and_time_le {Q E : Type*} [Fintype Q] [Inhabited E]
    (M : BiInfTM Q E) (h : M.HaltsOnBlank) :
    (stateThreeTM M).HaltsOnBlank ∧ M.time ≤ (stateThreeTM M).time :=
  stateThreeTMOfEquiv_halts_and_time_le (Fintype.equivFin Q) M h

/-- Every blank-tape halting machine `M : BiInfTM Q E` is simulated by a 3-state machine over
`Fin 3` and `Fin (3 * (Fintype.card Q + 1) * Fintype.card E)`. -/
theorem exists_stateThree_tm {Q E : Type*} [Fintype Q] [Fintype E] [Inhabited E]
    (M : BiInfTM Q E) (h : M.HaltsOnBlank) :
    ∃ M' : BiInfTM (Fin 3) (Fin (3 * (Fintype.card Q + 1) * Fintype.card E)),
      M'.HaltsOnBlank ∧ M.time ≤ M'.time := by
  classical
  have hm : 0 < Fintype.card E := Fintype.card_pos_iff.mpr ⟨default⟩
  let _ : NeZero (Fintype.card E) := ⟨hm.ne'⟩
  let eE₀ : Sym3 (Fintype.card Q) E ≃ Fin (3 * (Fintype.card Q + 1) * Fintype.card E) :=
    Fintype.equivFinOfCardEq (card_sym3 (Fintype.card Q) E)
  let eE : Sym3 (Fintype.card Q) E ≃ Fin (3 * (Fintype.card Q + 1) * Fintype.card E) :=
    eE₀.trans (Equiv.swap (eE₀ default) 0)
  have heE : eE default = default := Equiv.swap_apply_left (eE₀ default) 0
  let M' := (stateThreeTM M).mapEquiv State3.equivFin eE
  obtain ⟨hh, hle⟩ := stateThreeTM_halts_and_time_le M h
  refine ⟨M', (BiInfTM.haltsOnBlank_mapEquiv_iff _ _ _ heE).mpr hh, ?_⟩
  simpa [M', BiInfTM.time_mapEquiv _ _ _ heE] using hle

/-- Busy Beaver lower bound from 3-state reduction:
`M.time ≤ busyBeaver 3 (3 * (Fintype.card Q + 1) * Fintype.card E)`. -/
theorem busyBeaver_stateThree {Q E : Type*} [Fintype Q] [Fintype E] [Inhabited E]
    (M : BiInfTM Q E) (h : M.HaltsOnBlank) :
    M.time ≤ busyBeaver 3 (3 * (Fintype.card Q + 1) * Fintype.card E) := by
  obtain ⟨M', _, hle⟩ := exists_stateThree_tm M h
  have hm : 0 < Fintype.card E := Fintype.card_pos_iff.mpr ⟨default⟩
  let _ : NeZero (Fintype.card E) := ⟨hm.ne'⟩
  exact hle.trans (time_le_busyBeaver_fin M')

end Theorems

/-- Generalized Busy Beaver 3-state reduction inequality: for all `1 ≤ n` and `1 ≤ m`,
`busyBeaver n m ≤ busyBeaver 3 (3 * (n + 1) * m)`. -/
theorem busyBeaver_le_stateThree {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) :
    busyBeaver n m ≤ busyBeaver 3 (3 * (n + 1) * m) := by
  let _ : NeZero n := ⟨by omega⟩
  let _ : NeZero m := ⟨by omega⟩
  obtain ⟨M, hM⟩ := exists_time_eq_busyBeaver n m
  by_cases hhalt : M.HaltsOnBlank
  · rw [← hM]
    simpa only [Fintype.card_fin] using busyBeaver_stateThree M hhalt
  · rw [← hM, BiInfTM.time_of_not_haltsOnBlank hhalt]
    exact Nat.zero_le _

end CslibFrontier.Computability.BusyBeaver
