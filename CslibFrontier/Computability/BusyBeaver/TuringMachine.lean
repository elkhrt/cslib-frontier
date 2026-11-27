/-
Copyright (c) 2026 Cslib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Papers contributors
-/

module

public import Mathlib.Computability.TuringMachine.Tape
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Prod

import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pigeonhole

/-!
# Generalized Busy Beaver Shift Function for Bi-Infinite Turing Machines

Formalizes deterministic single-tape bi-infinite Turing machines over `Turing.Tape` and
`Turing.Dir`, blank-tape halting time, Radó's generalized two-parameter Busy Beaver shift
function `busyBeaver n m`, equivalence and embedding invariance, joint monotonicity, the exact
boundary values `busyBeaver 1 m = 1` and `busyBeaver n 1 = n`, and relational simulation
halting-time transfer under standard Lean axioms.
-/

public section

namespace CslibFrontier.Computability.BusyBeaver

section Machines

/-- Finite enumeration of the two head movement directions `Turing.Dir.left` and `.right`. -/
scoped instance instFintypeTuringDir : Fintype Turing.Dir where
  elems := {.left, .right}
  complete d := by cases d <;> simp

/-- There are `2` head movement directions in `Turing.Dir`. -/
@[scoped simp] theorem card_turingDir : Fintype.card Turing.Dir = 2 := rfl

/-- Bi-infinite deterministic Turing machine with state space `Q` and tape alphabet `E` (`default`
is the blank symbol). Returning `none` as the next state in `trans` represents `HALT`. -/
@[ext]
structure BiInfTM (Q E : Type*) [Inhabited E] where
  /-- Initial control state of the machine. -/
  initState : Q
  /-- Transition table `(q, e) ↦ (q', e', d)`, with `none` representing `HALT`. -/
  trans : Q → E → Option Q × E × Turing.Dir

namespace BiInfTM

/-- Default machine over `(Q, E)` halting immediately on every read. -/
instance instInhabited {Q E : Type*} [Inhabited Q] [Inhabited E] : Inhabited (BiInfTM Q E) :=
  ⟨⟨default, fun _ _ ↦ (none, default, .right)⟩⟩

/-- Equivalence between `BiInfTM Q E` and the pair `(M.initState, M.trans)`. -/
@[expose]
def equivProd (Q E : Type*) [Inhabited E] :
    BiInfTM Q E ≃ Q × (Q → E → Option Q × E × Turing.Dir) where
  toFun M := (M.initState, M.trans)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

lemma equivProd_def (Q E : Type*) [Inhabited E] :
    equivProd Q E =
      { toFun := fun M ↦ (M.initState, M.trans)
        invFun := fun p ↦ ⟨p.1, p.2⟩
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl } := rfl

@[simp, grind =] lemma equivProd_apply {Q E : Type*} [Inhabited E] (M : BiInfTM Q E) :
    equivProd Q E M = (M.initState, M.trans) := rfl

@[simp, grind =] lemma equivProd_symm_apply {Q E : Type*} [Inhabited E]
    (p : Q × (Q → E → Option Q × E × Turing.Dir)) : (equivProd Q E).symm p = ⟨p.1, p.2⟩ := rfl

/-- Finite enumeration of all bi-infinite Turing machines over finite `Q` and `E`. -/
instance instFintype {Q E : Type*} [Inhabited E] [Fintype Q] [Fintype E]
    [DecidableEq Q] [DecidableEq E] : Fintype (BiInfTM Q E) :=
  Fintype.ofEquiv _ (equivProd Q E).symm

end BiInfTM

/-- Instantaneous configuration of a bi-infinite Turing machine: optional state (`none` for `HALT`)
and a `Turing.Tape E`. -/
@[ext]
structure Cfg (Q E : Type*) [Inhabited E] where
  /-- Current control state, or `none` if halted. -/
  state : Option Q
  /-- Current bi-infinite tape centered at the head. -/
  tape : Turing.Tape E

/-- Default halted configuration on the blank tape. -/
instance Cfg.instInhabited {Q E : Type*} [Inhabited E] : Inhabited (Cfg Q E) := ⟨⟨none, default⟩⟩

end Machines

section Execution

variable {Q E : Type*} [Inhabited E]

namespace BiInfTM

/-- Single-step transition of `M : BiInfTM Q E` on `c : Cfg Q E`. -/
@[expose]
def step (M : BiInfTM Q E) (c : Cfg Q E) : Cfg Q E :=
  match c.state with
  | none => c
  | some q => let r := M.trans q c.tape.head; ⟨r.1, (c.tape.write r.2.1).move r.2.2⟩

lemma step_def (M : BiInfTM Q E) (c : Cfg Q E) :
    M.step c = match c.state with
      | none => c
      | some q => let r := M.trans q c.tape.head; ⟨r.1, (c.tape.write r.2.1).move r.2.2⟩ := rfl

@[simp, grind =] lemma step_none (M : BiInfTM Q E) (T : Turing.Tape E) :
    M.step ⟨none, T⟩ = ⟨none, T⟩ := rfl

@[simp] lemma step_of_state_eq_none (M : BiInfTM Q E) {c : Cfg Q E} (hc : c.state = none) :
    M.step c = c := by cases c with | mk state tape => dsimp at hc; subst hc; rfl

@[simp, grind =] lemma step_some (M : BiInfTM Q E) (q : Q) (T : Turing.Tape E) :
    M.step ⟨some q, T⟩ =
      ⟨(M.trans q T.head).1, (T.write (M.trans q T.head).2.1).move (M.trans q T.head).2.2⟩ :=
  rfl

/-- Initial configuration of `M` on tape `T` (defaulting to the all-blank tape). -/
@[expose]
def initConfig (M : BiInfTM Q E) (T : Turing.Tape E := default) : Cfg Q E := ⟨some M.initState, T⟩

lemma initConfig_def (M : BiInfTM Q E) (T : Turing.Tape E) :
    M.initConfig T = ⟨some M.initState, T⟩ := rfl

@[simp, grind =] lemma initConfig_state (M : BiInfTM Q E) (T : Turing.Tape E) :
    (M.initConfig T).state = some M.initState := rfl

@[simp, grind =] lemma initConfig_tape (M : BiInfTM Q E) (T : Turing.Tape E) :
    (M.initConfig T).tape = T := rfl

/-- Configuration of `M` after `k` steps starting from `M.initConfig T`. -/
@[expose]
def evalSteps (M : BiInfTM Q E) (k : ℕ) (T : Turing.Tape E := default) : Cfg Q E :=
  M.step^[k] (M.initConfig T)

lemma evalSteps_def (M : BiInfTM Q E) (k : ℕ) (T : Turing.Tape E) :
    M.evalSteps k T = M.step^[k] (M.initConfig T) := rfl

@[simp, grind =] lemma evalSteps_zero (M : BiInfTM Q E) (T : Turing.Tape E) :
    M.evalSteps 0 T = M.initConfig T := rfl

@[simp, grind =] lemma evalSteps_succ (M : BiInfTM Q E) (k : ℕ) (T : Turing.Tape E) :
    M.evalSteps (k + 1) T = M.step (M.evalSteps k T) :=
  Function.iterate_succ_apply' M.step k (M.initConfig T)

/-- Evaluating `k₁ + k₂` steps applies `M.step^[k₂]` to `M.evalSteps k₁ T`. -/
theorem evalSteps_add (M : BiInfTM Q E) (k₁ k₂ : ℕ) (T : Turing.Tape E) :
    M.evalSteps (k₁ + k₂) T = M.step^[k₂] (M.evalSteps k₁ T) := by
  rw [evalSteps_def, evalSteps_def, add_comm, Function.iterate_add_apply]

/-- Once `M` halts at step `k`, all subsequent configurations `k' ≥ k` coincide with step `k`. -/
theorem evalSteps_eq_of_halted (M : BiInfTM Q E) {T : Turing.Tape E} {k k' : ℕ}
    (hhalt : (M.evalSteps k T).state = none) (hle : k ≤ k') :
    M.evalSteps k' T = M.evalSteps k T := by
  induction k', hle using Nat.le_induction with
  | base => rfl
  | succ _ _ ih => rw [evalSteps_succ, ih, step_of_state_eq_none M hhalt]

/-- Predicate asserting that `M` is in `none` (`HALT`) after `k` steps on the blank tape. -/
@[expose]
def HaltsInStepsOnBlank (M : BiInfTM Q E) (k : ℕ) : Prop := (M.evalSteps k default).state = none

lemma haltsInStepsOnBlank_def (M : BiInfTM Q E) (k : ℕ) :
    M.HaltsInStepsOnBlank k = ((M.evalSteps k default).state = none) := rfl

@[simp, grind =] lemma haltsInStepsOnBlank_iff (M : BiInfTM Q E) (k : ℕ) :
    M.HaltsInStepsOnBlank k ↔ (M.evalSteps k default).state = none := Iff.rfl

/-- Decidability of `M.HaltsInStepsOnBlank k`. -/
instance instDecidableHaltsInStepsOnBlank (M : BiInfTM Q E) (k : ℕ) :
    Decidable (M.HaltsInStepsOnBlank k) :=
  match h : (M.evalSteps k default).state with
  | none => isTrue h
  | some _ => isFalse (by simp [HaltsInStepsOnBlank, h])

theorem not_haltsInStepsOnBlank_zero (M : BiInfTM Q E) : ¬ M.HaltsInStepsOnBlank 0 := by
  simp [HaltsInStepsOnBlank]

/-- Monotonicity of halting in step count on the blank tape. -/
theorem HaltsInStepsOnBlank.mono {M : BiInfTM Q E} {k k' : ℕ}
    (hk : M.HaltsInStepsOnBlank k) (hle : k ≤ k') : M.HaltsInStepsOnBlank k' := by
  rw [haltsInStepsOnBlank_iff] at hk ⊢; rw [M.evalSteps_eq_of_halted hk hle, hk]

/-- Predicate asserting that `M` eventually halts on the blank tape. -/
@[expose]
def HaltsOnBlank (M : BiInfTM Q E) : Prop := ∃ k : ℕ, M.HaltsInStepsOnBlank k

lemma haltsOnBlank_def (M : BiInfTM Q E) :
    M.HaltsOnBlank = (∃ k : ℕ, M.HaltsInStepsOnBlank k) := rfl

@[simp, grind =] lemma haltsOnBlank_iff (M : BiInfTM Q E) :
    M.HaltsOnBlank ↔ ∃ k : ℕ, M.HaltsInStepsOnBlank k := Iff.rfl

/-- Least blank-tape halting step of `M`, or `0` if `M` does not halt on the blank tape. -/
@[expose]
noncomputable def time (M : BiInfTM Q E) : ℕ := by
  classical exact if h : M.HaltsOnBlank then Nat.find h else 0

lemma time_def (M : BiInfTM Q E) :
    M.time = (by classical exact if h : M.HaltsOnBlank then Nat.find h else 0) := rfl

lemma time_of_haltsOnBlank {M : BiInfTM Q E} (h : M.HaltsOnBlank) : M.time = Nat.find h := by
  classical dsimp [time]; rw [dite_eq_left h]

lemma time_of_not_haltsOnBlank {M : BiInfTM Q E} (h : ¬ M.HaltsOnBlank) : M.time = 0 := by
  classical dsimp [time]; rw [dite_eq_right h]

/-- If `M` halts on the blank tape, it is halted at step `M.time`. -/
theorem haltsInStepsOnBlank_time {M : BiInfTM Q E} (h : M.HaltsOnBlank) :
    M.HaltsInStepsOnBlank M.time := by rw [time_of_haltsOnBlank h]; exact Nat.find_spec h

/-- Any halting step `k` on the blank tape upper-bounds `M.time`. -/
theorem time_le_of_haltsInStepsOnBlank {M : BiInfTM Q E} {k : ℕ}
    (hk : M.HaltsInStepsOnBlank k) : M.time ≤ k := by
  have h : M.HaltsOnBlank := ⟨k, hk⟩; rw [time_of_haltsOnBlank h]; exact Nat.find_min' h hk

/-- Every halting machine takes at least `1` step on the blank tape. -/
theorem one_le_time_of_haltsOnBlank {M : BiInfTM Q E} (h : M.HaltsOnBlank) : 1 ≤ M.time := by
  by_contra! hlt
  exact M.not_haltsInStepsOnBlank_zero (Nat.lt_one_iff.mp hlt ▸ M.haltsInStepsOnBlank_time h)

/-- At any halting step `k`, `M.evalSteps k default` equals `M.evalSteps M.time default`. -/
theorem evalSteps_eq_evalSteps_time_of_haltsInStepsOnBlank {M : BiInfTM Q E} {k : ℕ}
    (hk : M.HaltsInStepsOnBlank k) : M.evalSteps k default = M.evalSteps M.time default :=
  M.evalSteps_eq_of_halted (M.haltsInStepsOnBlank_time ⟨k, hk⟩)
    (M.time_le_of_haltsInStepsOnBlank hk)

/-- No step strictly preceding `M.time` is a halting step on the blank tape. -/
theorem not_haltsInStepsOnBlank_of_lt_time {M : BiInfTM Q E} {j : ℕ}
    (hj : j < M.time) : ¬ M.HaltsInStepsOnBlank j :=
  fun h ↦ Nat.not_le_of_lt hj (M.time_le_of_haltsInStepsOnBlank h)

/-- Uniqueness of the first halting step on the blank tape. -/
theorem time_eq_of_first_halt {M : BiInfTM Q E} {k : ℕ} (hk : M.HaltsInStepsOnBlank k)
    (hmin : ∀ j < k, ¬ M.HaltsInStepsOnBlank j) : M.time = k := by
  apply le_antisymm (M.time_le_of_haltsInStepsOnBlank hk)
  by_contra! hlt; exact hmin M.time hlt (M.haltsInStepsOnBlank_time ⟨k, hk⟩)

/-- Characterization of `M.time = k` given `M.HaltsInStepsOnBlank k`. -/
theorem time_eq_iff_of_haltsInStepsOnBlank {M : BiInfTM Q E} {k : ℕ}
    (hk : M.HaltsInStepsOnBlank k) : M.time = k ↔ ∀ j < k, ¬ M.HaltsInStepsOnBlank j :=
  ⟨fun heq _ hj ↦ M.not_haltsInStepsOnBlank_of_lt_time (heq ▸ hj), M.time_eq_of_first_halt hk⟩

end BiInfTM

end Execution

section Transport

private lemma tape_map_default {E E' : Type*} [Inhabited E] [Inhabited E']
    (f : Turing.PointedMap E E') : (default : Turing.Tape E).map f = default := by
  have hlb : (default : Turing.ListBlank E).map f = default := Turing.ListBlank.map_mk f []
  change Turing.Tape.mk (f default) ((default : Turing.ListBlank E).map f)
      ((default : Turing.ListBlank E).map f) = Turing.Tape.mk default default default
  rw [f.map_pt, hlb]

/-- Maps a configuration across a state map `fQ` and a pointed alphabet map `fE`. -/
@[expose]
def Cfg.map {Q Q' E E' : Type*} [Inhabited E] [Inhabited E']
    (fQ : Q → Q') (fE : Turing.PointedMap E E') (c : Cfg Q E) : Cfg Q' E' :=
  ⟨c.state.map fQ, c.tape.map fE⟩

@[simp, grind =] lemma cfg_map_state {Q Q' E E' : Type*} [Inhabited E] [Inhabited E']
    (fQ : Q → Q') (fE : Turing.PointedMap E E') (c : Cfg Q E) :
    (c.map fQ fE).state = c.state.map fQ := rfl

@[simp, grind =] lemma cfg_map_tape {Q Q' E E' : Type*} [Inhabited E] [Inhabited E']
    (fQ : Q → Q') (fE : Turing.PointedMap E E') (c : Cfg Q E) :
    (c.map fQ fE).tape = c.tape.map fE := rfl

namespace BiInfTM

section Hom

variable {Q Q' E E' : Type*} [Inhabited E] [Inhabited E']

private lemma evalSteps_eq_map_of_hom (M : BiInfTM Q E) (M' : BiInfTM Q' E')
    (fQ : Q → Q') (fE : Turing.PointedMap E E') (hinit : M'.initState = fQ M.initState)
    (htrans : ∀ q e, M'.trans (fQ q) (fE e) =
      let r := M.trans q e; (r.1.map fQ, fE r.2.1, r.2.2))
    (k : ℕ) (T : Turing.Tape E) :
    M'.evalSteps k (T.map fE) = (M.evalSteps k T).map fQ fE := by
  induction k with
  | zero => simp [initConfig, Cfg.map, hinit]
  | succ k ih =>
    rw [evalSteps_succ, evalSteps_succ, ih]
    rcases h : M.evalSteps k T with ⟨st, Tp⟩
    cases st with
    | none => rfl
    | some q =>
      simp only [Cfg.map, Option.map_some, step_some, Turing.Tape.map_fst, htrans,
        Turing.Tape.map_write, Turing.Tape.map_move]

private lemma haltsInStepsOnBlank_iff_of_hom (M : BiInfTM Q E) (M' : BiInfTM Q' E')
    (fQ : Q → Q') (fE : Turing.PointedMap E E') (hinit : M'.initState = fQ M.initState)
    (htrans : ∀ q e, M'.trans (fQ q) (fE e) =
      let r := M.trans q e; (r.1.map fQ, fE r.2.1, r.2.2)) (k : ℕ) :
    M'.HaltsInStepsOnBlank k ↔ M.HaltsInStepsOnBlank k := by
  rw [haltsInStepsOnBlank_iff, haltsInStepsOnBlank_iff, ← tape_map_default fE,
    evalSteps_eq_map_of_hom M M' fQ fE hinit htrans, cfg_map_state, Option.map_eq_none_iff]

private lemma time_eq_of_hom (M : BiInfTM Q E) (M' : BiInfTM Q' E')
    (fQ : Q → Q') (fE : Turing.PointedMap E E') (hinit : M'.initState = fQ M.initState)
    (htrans : ∀ q e, M'.trans (fQ q) (fE e) =
      let r := M.trans q e; (r.1.map fQ, fE r.2.1, r.2.2)) : M'.time = M.time := by
  have hiff := haltsInStepsOnBlank_iff_of_hom M M' fQ fE hinit htrans
  by_cases h : M.HaltsOnBlank
  · have h' : M'.HaltsOnBlank := let ⟨k, hk⟩ := h; ⟨k, (hiff k).mpr hk⟩
    rw [time_of_haltsOnBlank h, time_of_haltsOnBlank h']; exact Nat.find_congr' fun {k} ↦ hiff k
  · have h' : ¬ M'.HaltsOnBlank := fun ⟨k, hk⟩ ↦ h ⟨k, (hiff k).mp hk⟩
    rw [time_of_not_haltsOnBlank h, time_of_not_haltsOnBlank h']

end Hom

section MapEquiv

variable {Q Q' E E' : Type*} [Inhabited E] [Inhabited E']

/-- Transports a machine along equivalences `eQ : Q ≃ Q'` and `eE : E ≃ E'`. -/
@[expose]
def mapEquiv (M : BiInfTM Q E) (eQ : Q ≃ Q') (eE : E ≃ E') : BiInfTM Q' E' where
  initState := eQ M.initState
  trans q' e' := let r := M.trans (eQ.symm q') (eE.symm e'); (r.1.map eQ, eE r.2.1, r.2.2)

@[simp, grind =] lemma mapEquiv_initState (M : BiInfTM Q E) (eQ : Q ≃ Q') (eE : E ≃ E') :
    (M.mapEquiv eQ eE).initState = eQ M.initState := rfl

@[simp, grind =] lemma mapEquiv_trans (M : BiInfTM Q E) (eQ : Q ≃ Q') (eE : E ≃ E')
    (q' : Q') (e' : E') : (M.mapEquiv eQ eE).trans q' e' =
      let r := M.trans (eQ.symm q') (eE.symm e'); (r.1.map eQ, eE r.2.1, r.2.2) := rfl

/-- Equivalence transport preserves `k`-step trajectories when `eE` preserves `default`. -/
theorem evalSteps_mapEquiv (M : BiInfTM Q E) (eQ : Q ≃ Q') (eE : E ≃ E')
    (heE : eE default = default) (k : ℕ) (T : Turing.Tape E) :
    (M.mapEquiv eQ eE).evalSteps k (T.map ⟨eE, heE⟩) = (M.evalSteps k T).map eQ ⟨eE, heE⟩ :=
  evalSteps_eq_map_of_hom M (M.mapEquiv eQ eE) eQ ⟨eE, heE⟩ rfl (fun q e ↦ by simp) k T

/-- Equivalence transport preserves `k`-step blank-tape halting when `eE` preserves `default`. -/
@[grind =] theorem haltsInStepsOnBlank_mapEquiv_iff (M : BiInfTM Q E) (eQ : Q ≃ Q') (eE : E ≃ E')
    (heE : eE default = default) (k : ℕ) :
    (M.mapEquiv eQ eE).HaltsInStepsOnBlank k ↔ M.HaltsInStepsOnBlank k :=
  haltsInStepsOnBlank_iff_of_hom M (M.mapEquiv eQ eE) eQ ⟨eE, heE⟩ rfl (fun q e ↦ by simp) k

/-- Equivalence transport preserves eventual blank-tape halting when `eE` preserves `default`. -/
@[grind =] theorem haltsOnBlank_mapEquiv_iff (M : BiInfTM Q E) (eQ : Q ≃ Q') (eE : E ≃ E')
    (heE : eE default = default) : (M.mapEquiv eQ eE).HaltsOnBlank ↔ M.HaltsOnBlank := by
  simp only [haltsOnBlank_iff, haltsInStepsOnBlank_mapEquiv_iff M eQ eE heE]

/-- Equivalence transport preserves blank-tape halting time when `eE` preserves `default`. -/
@[simp] theorem time_mapEquiv (M : BiInfTM Q E) (eQ : Q ≃ Q') (eE : E ≃ E')
    (heE : eE default = default) : (M.mapEquiv eQ eE).time = M.time :=
  time_eq_of_hom M (M.mapEquiv eQ eE) eQ ⟨eE, heE⟩ rfl (fun q e ↦ by simp)

end MapEquiv

section Embed

variable {Q Q' E E' : Type*} [Inhabited E] [Inhabited E']

/-- Embeds `M : BiInfTM Q E` into `BiInfTM Q' E'` along injections `fQ : Q ↪ Q'` and
`fE : E ↪ E'`, halting immediately outside the embedded image. -/
@[expose]
noncomputable def embed (M : BiInfTM Q E) (fQ : Q ↪ Q') (fE : E ↪ E') : BiInfTM Q' E' where
  initState := fQ M.initState
  trans q' e' := by
    classical
    exact if hq : ∃ q, fQ q = q' then
      if he : ∃ e, fE e = e' then
        let r := M.trans hq.choose he.choose; (r.1.map fQ, fE r.2.1, r.2.2)
      else (none, default, .right)
    else (none, default, .right)

@[simp] lemma embed_initState (M : BiInfTM Q E) (fQ : Q ↪ Q') (fE : E ↪ E') :
    (M.embed fQ fE).initState = fQ M.initState := rfl

@[simp] lemma embed_trans_apply (M : BiInfTM Q E) (fQ : Q ↪ Q') (fE : E ↪ E') (q : Q) (e : E) :
    (M.embed fQ fE).trans (fQ q) (fE e) =
      let r := M.trans q e; (r.1.map fQ, fE r.2.1, r.2.2) := by
  classical
  have hq : ∃ q₀, fQ q₀ = fQ q := ⟨q, rfl⟩
  have he : ∃ e₀, fE e₀ = fE e := ⟨e, rfl⟩
  change (if hq' : ∃ q₀, fQ q₀ = fQ q then if he' : ∃ e₀, fE e₀ = fE e then
    let r := M.trans hq'.choose he'.choose; (r.1.map fQ, fE r.2.1, r.2.2)
    else (none, default, .right) else (none, default, .right)) = _
  rw [dite_eq_left hq, dite_eq_left he, fQ.injective hq.choose_spec, fE.injective he.choose_spec]

/-- Injective embedding preserves `k`-step trajectories when `fE` preserves `default`. -/
theorem evalSteps_embed (M : BiInfTM Q E) (fQ : Q ↪ Q') (fE : E ↪ E')
    (hfE : fE default = default) (k : ℕ) (T : Turing.Tape E) :
    (M.embed fQ fE).evalSteps k (T.map ⟨fE, hfE⟩) = (M.evalSteps k T).map fQ ⟨fE, hfE⟩ :=
  evalSteps_eq_map_of_hom M (M.embed fQ fE) fQ ⟨fE, hfE⟩ rfl
    (fun q e ↦ embed_trans_apply M fQ fE q e) k T

/-- Injective embedding preserves `k`-step blank-tape halting when `fE` preserves `default`. -/
@[grind =] theorem haltsInStepsOnBlank_embed_iff (M : BiInfTM Q E) (fQ : Q ↪ Q') (fE : E ↪ E')
    (hfE : fE default = default) (k : ℕ) :
    (M.embed fQ fE).HaltsInStepsOnBlank k ↔ M.HaltsInStepsOnBlank k :=
  haltsInStepsOnBlank_iff_of_hom M (M.embed fQ fE) fQ ⟨fE, hfE⟩ rfl
    (fun q e ↦ embed_trans_apply M fQ fE q e) k

/-- Injective embedding preserves eventual blank-tape halting when `fE` preserves `default`. -/
@[grind =] theorem haltsOnBlank_embed_iff (M : BiInfTM Q E) (fQ : Q ↪ Q') (fE : E ↪ E')
    (hfE : fE default = default) : (M.embed fQ fE).HaltsOnBlank ↔ M.HaltsOnBlank := by
  simp only [haltsOnBlank_iff, haltsInStepsOnBlank_embed_iff M fQ fE hfE]

/-- Injective embedding preserves blank-tape halting time when `fE` preserves `default`. -/
@[simp] theorem time_embed (M : BiInfTM Q E) (fQ : Q ↪ Q') (fE : E ↪ E')
    (hfE : fE default = default) : (M.embed fQ fE).time = M.time :=
  time_eq_of_hom M (M.embed fQ fE) fQ ⟨fE, hfE⟩ rfl (fun q e ↦ embed_trans_apply M fQ fE q e)

end Embed

end BiInfTM

end Transport

section BusyBeaver

/-- Generalized Busy Beaver function $\mathrm{BB}(n, m)$: maximum blank-tape halting time over
bi-infinite Turing machines with `n` states and `m` symbols (`0` when `n = 0` or `m = 0`). -/
@[expose]
noncomputable def busyBeaver : ℕ → ℕ → ℕ
  | 0, _ => 0
  | _, 0 => 0
  | n + 1, m + 1 => (Finset.univ : Finset (BiInfTM (Fin (n + 1)) (Fin (m + 1)))).sup BiInfTM.time

lemma busyBeaver_succ_succ (n m : ℕ) :
    busyBeaver (n + 1) (m + 1) =
      (Finset.univ : Finset (BiInfTM (Fin (n + 1)) (Fin (m + 1)))).sup BiInfTM.time := rfl

@[simp] lemma busyBeaver_zero_left (m : ℕ) : busyBeaver 0 m = 0 := rfl

@[simp] lemma busyBeaver_zero_right (n : ℕ) : busyBeaver n 0 = 0 := by cases n <;> rfl

/-- When `[NeZero n]` and `[NeZero m]`, `busyBeaver n m` equals the supremum of `BiInfTM.time`. -/
lemma busyBeaver_eq_sup (n m : ℕ) [NeZero n] [NeZero m] :
    busyBeaver n m = (Finset.univ : Finset (BiInfTM (Fin n) (Fin m))).sup BiInfTM.time := by
  rcases Nat.exists_eq_succ_of_ne_zero (NeZero.ne n) with ⟨_, rfl⟩
  rcases Nat.exists_eq_succ_of_ne_zero (NeZero.ne m) with ⟨_, rfl⟩
  rfl

/-- For `[NeZero n]` and `[NeZero m]`, some machine on `(Fin n, Fin m)` attains `busyBeaver n m`. -/
theorem exists_time_eq_busyBeaver (n m : ℕ) [NeZero n] [NeZero m] :
    ∃ M : BiInfTM (Fin n) (Fin m), M.time = busyBeaver n m := by
  rw [busyBeaver_eq_sup n m]
  obtain ⟨M, -, hM⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (BiInfTM (Fin n) (Fin m)))
    Finset.univ_nonempty BiInfTM.time
  exact ⟨M, hM.symm⟩

/-- Every machine on `(Fin n, Fin m)` has blank-tape halting time at most `busyBeaver n m`. -/
theorem time_le_busyBeaver_fin {n m : ℕ} [NeZero n] [NeZero m] (M : BiInfTM (Fin n) (Fin m)) :
    M.time ≤ busyBeaver n m := by
  rw [busyBeaver_eq_sup n m]; exact Finset.le_sup (Finset.mem_univ M)

private lemma time_le_busyBeaver_of_card_eq {Q E : Type*} [Fintype Q] [Fintype E] [Inhabited E]
    {n m : ℕ} [NeZero n] [NeZero m] (hn : Fintype.card Q = n) (hm : Fintype.card E = m)
    (M : BiInfTM Q E) : M.time ≤ busyBeaver n m := by
  classical
  rcases Fintype.truncEquivFin Q with ⟨eQ₀⟩
  rcases Fintype.truncEquivFin E with ⟨eE₀⟩
  let eQ : Q ≃ Fin n := eQ₀.trans (Equiv.cast (congrArg Fin hn))
  let eE₁ : E ≃ Fin m := eE₀.trans (Equiv.cast (congrArg Fin hm))
  let eE : E ≃ Fin m := eE₁.trans (Equiv.swap (eE₁ default) 0)
  have heE : eE default = default := Equiv.swap_apply_left (eE₁ default) (0 : Fin m)
  rw [← M.time_mapEquiv eQ eE heE]; exact time_le_busyBeaver_fin (M.mapEquiv eQ eE)

/-- Universality of `busyBeaver`: every machine over finite `(Q, E)` satisfies
`M.time ≤ busyBeaver (Fintype.card Q) (Fintype.card E)`. -/
theorem time_le_busyBeaver {Q E : Type*} [Fintype Q] [Fintype E] [Inhabited E]
    (M : BiInfTM Q E) : M.time ≤ busyBeaver (Fintype.card Q) (Fintype.card E) := by
  have hn : 0 < Fintype.card Q := Fintype.card_pos_iff.mpr ⟨M.initState⟩
  have hm : 0 < Fintype.card E := Fintype.card_pos_iff.mpr ⟨default⟩
  exact @time_le_busyBeaver_of_card_eq Q E _ _ _ (Fintype.card Q) (Fintype.card E)
    ⟨hn.ne'⟩ ⟨hm.ne'⟩ rfl rfl M

private lemma busyBeaver_mono_neZero {n₁ n₂ m₁ m₂ : ℕ} [NeZero n₁] [NeZero n₂]
    [NeZero m₁] [NeZero m₂] (hn : n₁ ≤ n₂) (hm : m₁ ≤ m₂) :
    busyBeaver n₁ m₁ ≤ busyBeaver n₂ m₂ := by
  obtain ⟨M, hM⟩ := exists_time_eq_busyBeaver n₁ m₁
  let fQ : Fin n₁ ↪ Fin n₂ := ⟨Fin.castLE hn, Fin.castLE_injective hn⟩
  let fE : Fin m₁ ↪ Fin m₂ := ⟨Fin.castLE hm, Fin.castLE_injective hm⟩
  rw [← hM, ← M.time_embed fQ fE (Fin.ext rfl)]; exact time_le_busyBeaver_fin (M.embed fQ fE)

/-- Monotonicity of `busyBeaver` in both arguments when `1 ≤ n₁ ≤ n₂` and `1 ≤ m₁ ≤ m₂`. -/
theorem busyBeaver_mono {n₁ n₂ m₁ m₂ : ℕ} (hn₁ : 1 ≤ n₁) (hn : n₁ ≤ n₂)
    (hm₁ : 1 ≤ m₁) (hm : m₁ ≤ m₂) : busyBeaver n₁ m₁ ≤ busyBeaver n₂ m₂ :=
  @busyBeaver_mono_neZero n₁ n₂ m₁ m₂ ⟨Nat.ne_of_gt hn₁⟩ ⟨Nat.ne_of_gt (hn₁.trans hn)⟩
    ⟨Nat.ne_of_gt hm₁⟩ ⟨Nat.ne_of_gt (hm₁.trans hm)⟩ hn hm

end BusyBeaver

section TrivialBounds

private lemma tape_nth_default {E : Type*} [Inhabited E] (i : ℤ) :
    (default : Turing.Tape E).nth i = default := by
  cases i with
  | ofNat n =>
    cases n with
    | zero => rfl
    | succ n => change (Turing.ListBlank.mk ([] : List E)).nth n = default; simp
  | negSucc n => change (Turing.ListBlank.mk ([] : List E)).nth n = default; simp

private lemma tape_eq_default_of_subsingleton {E : Type*} [Inhabited E] [Subsingleton E]
    (T : Turing.Tape E) : T = default := by
  rcases T with ⟨h, l, r⟩
  have hl : l = default := Turing.ListBlank.ext fun _ ↦ Subsingleton.elim _ _
  have hr : r = default := Turing.ListBlank.ext fun _ ↦ Subsingleton.elim _ _
  have hh : h = default := Subsingleton.elim _ _
  subst hl hr hh; rfl

private def haltOneTM (m : ℕ) [NeZero m] : BiInfTM (Fin 1) (Fin m) :=
  ⟨0, fun _ _ ↦ (none, 0, .right)⟩

private lemma haltOneTM_time (m : ℕ) [NeZero m] : (haltOneTM m).time = 1 :=
  BiInfTM.time_eq_of_first_halt rfl fun j hj ↦ by
    have hj0 : j = 0 := Nat.lt_one_iff.mp hj
    subst hj0; exact (haltOneTM m).not_haltsInStepsOnBlank_zero

private lemma subsingleton_state_loop_inv {Q E : Type*} [Subsingleton Q] [Inhabited E]
    (M : BiInfTM Q E) {q₁ : Q} (hr : (M.trans M.initState default).1 = some q₁) :
    ∀ k, (M.evalSteps k default).state = some M.initState := by
  have hq₁ : q₁ = M.initState := Subsingleton.elim _ _
  let idx : Turing.Dir → ℕ → ℤ | .right, i => (i : ℤ) | .left, i => -(i : ℤ)
  have inv : ∀ k, (M.evalSteps k default).state = some M.initState ∧
      ∀ i : ℕ, (M.evalSteps k default).tape.nth
        (idx (M.trans M.initState default).2.2 i) = default := by
    intro k; induction k with
    | zero => exact ⟨rfl, fun i ↦ tape_nth_default _⟩
    | succ k ih =>
      rcases ih with ⟨hst, hnth⟩
      have hhead : (M.evalSteps k default).tape.head = default := by
        have h0 := hnth 0
        cases hd : (M.trans M.initState default).2.2 <;> simpa [idx, hd] using h0
      rw [BiInfTM.evalSteps_succ]
      rcases hc : M.evalSteps k default with ⟨st, T⟩
      rw [hc] at hst hhead hnth; dsimp at hst hhead hnth; subst hst
      simp only [BiInfTM.step_some, hhead, hr, hq₁, true_and]
      intro i; cases hd : (M.trans M.initState default).2.2 with
      | left =>
        rw [Turing.Tape.move_left_nth, Turing.Tape.write_nth,
          ite_eq_right (by dsimp [idx]; omega)]
        simpa [idx, hd, show (-(i : ℤ) - 1) = -((i + 1 : ℕ) : ℤ) by omega] using hnth (i + 1)
      | right =>
        rw [Turing.Tape.move_right_nth, Turing.Tape.write_nth,
          ite_eq_right (by dsimp [idx]; omega)]
        simpa [idx, hd] using hnth (i + 1)
  exact fun k ↦ (inv k).1

private lemma time_le_one_of_subsingleton_state {Q E : Type*} [Subsingleton Q] [Inhabited E]
    (M : BiInfTM Q E) : M.time ≤ 1 := by
  rcases hr : (M.trans M.initState default).1 with _ | q₁
  · apply M.time_le_of_haltsInStepsOnBlank
    have hhead : (default : Turing.Tape E).head = default := rfl
    simpa [BiInfTM.HaltsInStepsOnBlank, BiInfTM.evalSteps_succ, BiInfTM.initConfig, hhead] using hr
  · have hnot : ¬ M.HaltsOnBlank := fun ⟨k, hk⟩ ↦ by
      rw [BiInfTM.haltsInStepsOnBlank_iff, subsingleton_state_loop_inv M hr k] at hk; nomatch hk
    rw [M.time_of_not_haltsOnBlank hnot]; exact Nat.zero_le 1

/-- Exact value of `busyBeaver 1 m = 1` for every `m ≥ 1`. -/
theorem busyBeaver_one_left {m : ℕ} (hm : 1 ≤ m) : busyBeaver 1 m = 1 := by
  have hnez : NeZero m := ⟨Nat.ne_of_gt hm⟩
  apply le_antisymm
  · rw [@busyBeaver_eq_sup 1 m _ hnez]
    exact Finset.sup_le fun M _ ↦ time_le_one_of_subsingleton_state M
  · exact (@haltOneTM_time m hnez).symm.trans_le (@time_le_busyBeaver_fin 1 m _ hnez (haltOneTM m))

private def chainTM (n : ℕ) [NeZero n] : BiInfTM (Fin n) (Fin 1) where
  initState := 0
  trans q _ := if h : q.1 + 1 < n then (some ⟨q.1 + 1, h⟩, 0, .right) else (none, 0, .right)

private lemma chainTM_evalSteps_of_lt (n : ℕ) [NeZero n] {k : ℕ} (hk : k < n) :
    (chainTM n).evalSteps k default = ⟨some ⟨k, hk⟩, default⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [BiInfTM.evalSteps_succ, ih (Nat.lt_of_succ_lt hk), BiInfTM.step_some]
    ext
    · simp [chainTM, hk]
    · exact tape_eq_default_of_subsingleton _

private lemma chainTM_time (n : ℕ) [NeZero n] : (chainTM n).time = n := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hhalt' : (chainTM n).HaltsInStepsOnBlank ((n - 1) + 1) := by
    rw [BiInfTM.haltsInStepsOnBlank_iff, BiInfTM.evalSteps_succ,
      chainTM_evalSteps_of_lt n (Nat.sub_lt hn Nat.zero_lt_one), BiInfTM.step_some]
    have hnotlt : ¬ ((n - 1) + 1 < n) := by omega
    simp [chainTM, hnotlt]
  refine BiInfTM.time_eq_of_first_halt (by rwa [Nat.sub_add_cancel hn] at hhalt') fun j hj ↦ ?_
  rw [BiInfTM.haltsInStepsOnBlank_iff, chainTM_evalSteps_of_lt n hj]; exact Option.some_ne_none _

/-- Any machine over a single-symbol alphabet (`Subsingleton E`) and finite state space `Q` has
blank-tape halting time at most `Fintype.card Q`. -/
theorem time_le_card_of_subsingleton {Q E : Type*} [Fintype Q] [Inhabited E] [Subsingleton E]
    (M : BiInfTM Q E) : M.time ≤ Fintype.card Q := by
  by_cases hhalt : M.HaltsOnBlank
  · by_contra! hlt
    let f : Fin (Fintype.card Q + 1) → Q := fun i ↦
      match (M.evalSteps i.1 default).state with | some q => q | none => M.initState
    obtain ⟨i₁, i₂, hne, heq⟩ :=
      Fintype.exists_ne_map_eq_of_card_lt f (by simp : Fintype.card Q < Fintype.card _)
    wlog hlt_i : i₁.1 < i₂.1 generalizing i₁ i₂
    · exact this i₂ i₁ hne.symm heq.symm
        (lt_of_le_of_ne (not_lt.mp hlt_i) (Fin.val_ne_of_ne hne.symm))
    rcases Option.ne_none_iff_exists'.mp
        (M.not_haltsInStepsOnBlank_of_lt_time (Nat.lt_of_lt_of_le i₁.2 hlt)) with ⟨q₁, hq₁⟩
    rcases Option.ne_none_iff_exists'.mp
        (M.not_haltsInStepsOnBlank_of_lt_time (Nat.lt_of_lt_of_le i₂.2 hlt)) with ⟨q₂, hq₂⟩
    have hq_eq : q₁ = q₂ := by
      have hf1 : f i₁ = q₁ := by dsimp [f]; rw [hq₁]
      have hf2 : f i₂ = q₂ := by dsimp [f]; rw [hq₂]
      rw [← hf1, ← hf2, heq]
    have hcfg : M.evalSteps i₁.1 default = M.evalSteps i₂.1 default := by
      ext
      · rw [hq₁, hq₂, hq_eq]
      · exact (tape_eq_default_of_subsingleton _).trans (tape_eq_default_of_subsingleton _).symm
    let d : ℕ := i₂.1 - i₁.1
    have hstep_d : M.step^[d] (M.evalSteps i₁.1 default) = M.evalSteps i₁.1 default := by
      rw [← M.evalSteps_add i₁.1 d default, Nat.add_sub_cancel' hlt_i.le, hcfg]
    have hloop : ∀ t : ℕ, M.evalSteps (i₁.1 + d * t) default = M.evalSteps i₁.1 default := by
      intro t; induction t with
      | zero => simp
      | succ t ih => rw [Nat.mul_succ, ← Nat.add_assoc, M.evalSteps_add, ih, hstep_d]
    have hhalted : M.HaltsInStepsOnBlank (i₁.1 + d * M.time) :=
      (M.haltsInStepsOnBlank_time hhalt).mono
        (le_trans (Nat.le_mul_of_pos_left M.time (Nat.sub_pos_of_lt hlt_i)) (Nat.le_add_left _ _))
    rw [BiInfTM.haltsInStepsOnBlank_iff, hloop M.time, hq₁] at hhalted
    exact Option.some_ne_none q₁ hhalted
  · rw [M.time_of_not_haltsOnBlank hhalt]; exact Nat.zero_le _

/-- Exact value of `busyBeaver n 1 = n` for every `n ≥ 1`. -/
theorem busyBeaver_one_right {n : ℕ} (hn : 1 ≤ n) : busyBeaver n 1 = n := by
  have hnez : NeZero n := ⟨Nat.ne_of_gt hn⟩
  apply le_antisymm
  · rw [@busyBeaver_eq_sup n 1 hnez _]
    refine Finset.sup_le fun M _ ↦ ?_; simpa using time_le_card_of_subsingleton M
  · exact (@chainTM_time n hnez).symm.trans_le (@time_le_busyBeaver_fin n 1 hnez _ (chainTM n))

end TrivialBounds

section Simulation

/-- Generic step-index simulation lemma: if `f : ℕ → ℕ` strictly advances whenever `M₁` has not
yet halted and preserves the blank-tape halting predicate at every `t`, then blank-tape halting of
`M₁` implies blank-tape halting of `M₂` with `M₁.time ≤ M₂.time`. -/
theorem haltsOnBlank_and_time_le_of_sim
    {Q₁ E₁ Q₂ E₂ : Type*} [Inhabited E₁] [Inhabited E₂]
    {M₁ : BiInfTM Q₁ E₁} {M₂ : BiInfTM Q₂ E₂} (f : ℕ → ℕ)
    (hstep : ∀ t, ¬ M₁.HaltsInStepsOnBlank t → f t + 1 ≤ f (t + 1))
    (hiff : ∀ t, M₂.HaltsInStepsOnBlank (f t) ↔ M₁.HaltsInStepsOnBlank t)
    (h₁ : M₁.HaltsOnBlank) : M₂.HaltsOnBlank ∧ M₁.time ≤ M₂.time := by
  have h₂ : M₂.HaltsOnBlank := ⟨f M₁.time, (hiff M₁.time).mpr (M₁.haltsInStepsOnBlank_time h₁)⟩
  refine ⟨h₂, ?_⟩
  have hle : ∀ t ≤ M₁.time, t ≤ f t := by
    intro t ht; induction t with
    | zero => exact Nat.zero_le _
    | succ t ih =>
      have ht_lt : t < M₁.time := Nat.lt_of_succ_le ht
      exact Nat.succ_le_of_lt
        (lt_of_le_of_lt (ih ht_lt.le) (hstep t (M₁.not_haltsInStepsOnBlank_of_lt_time ht_lt)))
  let t₀ : ℕ := M₁.time - 1
  have ht₀_lt : t₀ < M₁.time := Nat.sub_lt (M₁.one_le_time_of_haltsOnBlank h₁) Nat.zero_lt_one
  have hnot₂ : ¬ M₂.HaltsInStepsOnBlank (f t₀) :=
    mt (hiff t₀).mp (M₁.not_haltsInStepsOnBlank_of_lt_time ht₀_lt)
  have hlt_f : f t₀ < M₂.time := by
    by_contra! hge; exact hnot₂ ((M₂.haltsInStepsOnBlank_time h₂).mono hge)
  have ht₀_le : t₀ ≤ f t₀ := hle t₀ ht₀_lt.le
  omega

private noncomputable def relSimSeq
    {Q₁ E₁ Q₂ E₂ : Type*} [Inhabited E₁] [Inhabited E₂]
    (M₁ : BiInfTM Q₁ E₁) (M₂ : BiInfTM Q₂ E₂) (R : Cfg Q₁ E₁ → Cfg Q₂ E₂ → Prop)
    (hinit : ∃ k₀, R (M₁.initConfig default) (M₂.evalSteps k₀ default))
    (hstep : ∀ c₁ c₂, R c₁ c₂ → c₁.state ≠ none → ∃ k ≥ 1, R (M₁.step c₁) (M₂.step^[k] c₂)) :
    (t : ℕ) → { u : ℕ // R (M₁.evalSteps t default) (M₂.evalSteps u default) }
  | 0 => by classical exact ⟨Classical.choose hinit, Classical.choose_spec hinit⟩
  | t + 1 => by
    classical
    let prev := relSimSeq M₁ M₂ R hinit hstep t
    exact if hs : (M₁.evalSteps t default).state = none then
      ⟨prev.1, by rw [M₁.evalSteps_succ, M₁.step_of_state_eq_none hs]; exact prev.2⟩
    else
      let hex := hstep (M₁.evalSteps t default) (M₂.evalSteps prev.1 default) prev.2 hs
      ⟨prev.1 + Classical.choose hex, by
        rw [M₁.evalSteps_succ, M₂.evalSteps_add]; exact (Classical.choose_spec hex).2⟩

/-- Generic configuration-relation simulation lemma: if `R : Cfg Q₁ E₁ → Cfg Q₂ E₂ → Prop` holds
between `M₁.initConfig default` and some `M₂.evalSteps k₀ default`, advances by at least `1` step
of `M₂` for each active step of `M₁`, and preserves `state = none`, then blank-tape halting of
`M₁` implies blank-tape halting of `M₂` with `M₁.time ≤ M₂.time`. -/
theorem haltsOnBlank_and_time_le_of_rel_sim
    {Q₁ E₁ Q₂ E₂ : Type*} [Inhabited E₁] [Inhabited E₂]
    {M₁ : BiInfTM Q₁ E₁} {M₂ : BiInfTM Q₂ E₂} (R : Cfg Q₁ E₁ → Cfg Q₂ E₂ → Prop)
    (hinit : ∃ k₀, R (M₁.initConfig default) (M₂.evalSteps k₀ default))
    (hstep : ∀ c₁ c₂, R c₁ c₂ → c₁.state ≠ none → ∃ k ≥ 1, R (M₁.step c₁) (M₂.step^[k] c₂))
    (hhalt : ∀ c₁ c₂, R c₁ c₂ → (c₂.state = none ↔ c₁.state = none))
    (h₁ : M₁.HaltsOnBlank) : M₂.HaltsOnBlank ∧ M₁.time ≤ M₂.time := by
  classical
  let seq := relSimSeq M₁ M₂ R hinit hstep
  refine haltsOnBlank_and_time_le_of_sim (fun t ↦ (seq t).1) ?_ (fun t ↦ hhalt _ _ (seq t).2) h₁
  intro t hnot
  have hs : (M₁.evalSteps t default).state ≠ none := hnot
  change (seq t).1 + 1 ≤ (relSimSeq M₁ M₂ R hinit hstep (t + 1)).1
  dsimp [seq, relSimSeq]
  rw [dite_eq_right hs]
  dsimp only
  have hk := (Classical.choose_spec (hstep (M₁.evalSteps t default)
    (M₂.evalSteps (relSimSeq M₁ M₂ R hinit hstep t).1 default)
    (relSimSeq M₁ M₂ R hinit hstep t).2 hs)).1
  omega

end Simulation

end CslibFrontier.Computability.BusyBeaver
