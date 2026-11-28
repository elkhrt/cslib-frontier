module

public import CslibFrontier.Computability.Communication.DirectProduct.IntersectionDist
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.ToReal
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Bounded-Space Communicating Circuits and Matrix Product Models

Two-party bounded-space communicating circuits with oblivious communication schedules and
unconstrained communication and storage lower bounds for Boolean matrix products:

* `CommStepKind`, `CommSchedule`, `CommCircuit`, and `RandCommCircuit`: two-party circuits whose
  local registers have combined size at most `S` at every step and which exchange `C` total bits.
* `boolMatVec` and `boolMatMul`: `N × N` Boolean matrix-vector and matrix-matrix multiplication.
* `mv_unconstrained_bounds` and `mm_unconstrained_bounds`: baseline lower bounds (`S ≥ 1` and
  `C ≥ |Out| / 4`) for bounded-error randomized communicating circuits.
-/

open Cslib Cslib.Communication Cslib.Probability Finset

namespace CslibFrontier.Computability.Communication

public section

/-! ### Communicating Circuits -/

/-- The kind of operation performed at one step of a communicating circuit with output index
type `Out`. Crossing wires (`aliceToBob` and `bobToAlice`) count toward communication `C`;
local steps and output emissions occur locally using each player's current register and input. -/
inductive CommStepKind (Out : Type*) : Type _
  | localStep : CommStepKind Out
  | aliceToBob : CommStepKind Out
  | bobToAlice : CommStepKind Out
  | emitAlice (o : Out) : CommStepKind Out
  | emitBob (o : Out) : CommStepKind Out
  deriving DecidableEq

/-- Fixed topology, register widths, and predetermined output schedule of a pair of communicating
circuits computing outputs indexed by `Out` within total storage bound `S` bits. -/
structure CommSchedule (Out : Type*) (S : ℕ) where
  /-- Number of sequential circuit layers. -/
  steps : ℕ
  /-- Number of storage bits held by Alice at boundary `t`. -/
  spaceA : Fin (steps + 1) → ℕ
  /-- Number of storage bits held by Bob at boundary `t`. -/
  spaceB : Fin (steps + 1) → ℕ
  /-- Combined storage of Alice and Bob never exceeds `S` bits. -/
  space_bound : ∀ t, spaceA t + spaceB t ≤ S
  /-- Operation performed at step `t`. -/
  kind : Fin steps → CommStepKind Out
  /-- Predetermined step at which output `o` is emitted. -/
  emitStep : Out → Fin steps
  /-- At step `emitStep o`, either Alice or Bob emits output `o`. -/
  emitStep_spec : ∀ o, kind (emitStep o) = .emitAlice o ∨ kind (emitStep o) = .emitBob o

/-- Whether step `t` is a wire crossing between Alice and Bob. -/
@[expose] def CommSchedule.isCommStep {Out : Type*} {S : ℕ} (sch : CommSchedule Out S)
    (t : Fin sch.steps) : Bool :=
  match sch.kind t with
  | .aliceToBob | .bobToAlice => true
  | _ => false

/-- An `aliceToBob` step is a communication step. -/
theorem CommSchedule.isCommStep_of_aliceToBob {Out : Type*} {S : ℕ} {sch : CommSchedule Out S}
    {t : Fin sch.steps} (h : sch.kind t = .aliceToBob) : sch.isCommStep t = true := by
  simp [CommSchedule.isCommStep, h]

/-- A `bobToAlice` step is a communication step. -/
theorem CommSchedule.isCommStep_of_bobToAlice {Out : Type*} {S : ℕ} {sch : CommSchedule Out S}
    {t : Fin sch.steps} (h : sch.kind t = .bobToAlice) : sch.isCommStep t = true := by
  simp [CommSchedule.isCommStep, h]

/-- A `localStep` is not a communication step. -/
theorem CommSchedule.isCommStep_of_localStep {Out : Type*} {S : ℕ} {sch : CommSchedule Out S}
    {t : Fin sch.steps} (h : sch.kind t = .localStep) : sch.isCommStep t = false := by
  simp [CommSchedule.isCommStep, h]

/-- An `emitAlice` step is not a communication step. -/
theorem CommSchedule.isCommStep_of_emitAlice {Out : Type*} {S : ℕ} {sch : CommSchedule Out S}
    {t : Fin sch.steps} {o : Out} (h : sch.kind t = .emitAlice o) : sch.isCommStep t = false := by
  simp [CommSchedule.isCommStep, h]

/-- An `emitBob` step is not a communication step. -/
theorem CommSchedule.isCommStep_of_emitBob {Out : Type*} {S : ℕ} {sch : CommSchedule Out S}
    {t : Fin sch.steps} {o : Out} (h : sch.kind t = .emitBob o) : sch.isCommStep t = false := by
  simp [CommSchedule.isCommStep, h]

/-- Total number of crossing wires (communication `C`) in schedule `sch`. -/
@[expose] def CommSchedule.commCount {Out : Type*} {S : ℕ} (sch : CommSchedule Out S) : ℕ :=
  (Finset.univ.filter fun t : Fin sch.steps => sch.isCommStep t = true).card

/-- Output emission steps are distinct for distinct output indices. -/
theorem CommSchedule.emitStep_injective {Out : Type*} {S : ℕ} (sch : CommSchedule Out S) :
    Function.Injective sch.emitStep := by
  intro o₁ o₂ h
  have h1 := sch.emitStep_spec o₁
  have h2 := sch.emitStep_spec o₂
  rw [h] at h1
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact CommStepKind.emitAlice.inj (h1.symm.trans h2)
  · cases h1.symm.trans h2
  · cases h1.symm.trans h2
  · exact CommStepKind.emitBob.inj (h1.symm.trans h2)

/-- A deterministic communicating circuit following schedule `sch`, with arbitrary local gates
reading each player's private input and local storage register. -/
structure CommCircuit (X Y : Type*) {Out : Type*} {S : ℕ} (sch : CommSchedule Out S) where
  /-- Alice's initial register contents computed from her input `x`. -/
  initA : X → BitString (sch.spaceA 0)
  /-- Bob's initial register contents computed from his input `y`. -/
  initB : Y → BitString (sch.spaceB 0)
  /-- Bit sent by Alice across an `aliceToBob` wire at step `t`. -/
  sendA : (t : Fin sch.steps) → X → BitString (sch.spaceA t.castSucc) → Bool
  /-- Bit sent by Bob across a `bobToAlice` wire at step `t`. -/
  sendB : (t : Fin sch.steps) → Y → BitString (sch.spaceB t.castSucc) → Bool
  /-- Alice's local transition gate (the `Bool` argument is the bit from Bob at `bobToAlice`). -/
  nextA : (t : Fin sch.steps) → X → BitString (sch.spaceA t.castSucc) → Bool →
    BitString (sch.spaceA t.succ)
  /-- Bob's local transition gate (the `Bool` argument is the bit from Alice at `aliceToBob`). -/
  nextB : (t : Fin sch.steps) → Y → BitString (sch.spaceB t.castSucc) → Bool →
    BitString (sch.spaceB t.succ)
  /-- Output bit emitted by Alice at an `emitAlice` step. -/
  outA : (t : Fin sch.steps) → X → BitString (sch.spaceA t.castSucc) → Bool
  /-- Output bit emitted by Bob at an `emitBob` step. -/
  outB : (t : Fin sch.steps) → Y → BitString (sch.spaceB t.castSucc) → Bool

/-- Single-step register transition of a deterministic communicating circuit. -/
@[expose] def CommCircuit.stepState {X Y Out : Type*} {S : ℕ} {sch : CommSchedule Out S}
    (D : CommCircuit X Y sch) (x : X) (y : Y) (t : Fin sch.steps)
    (s : BitString (sch.spaceA t.castSucc) × BitString (sch.spaceB t.castSucc)) :
    BitString (sch.spaceA t.succ) × BitString (sch.spaceB t.succ) :=
  match sch.kind t with
  | .aliceToBob =>
    (D.nextA t x s.1 false, D.nextB t y s.2 (D.sendA t x s.1))
  | .bobToAlice =>
    (D.nextA t x s.1 (D.sendB t y s.2), D.nextB t y s.2 false)
  | _ =>
    (D.nextA t x s.1 false, D.nextB t y s.2 false)

/-- Single-step register transition at an `aliceToBob` step. -/
theorem CommCircuit.stepState_of_aliceToBob {X Y Out : Type*} {S : ℕ} {sch : CommSchedule Out S}
    (D : CommCircuit X Y sch) (x : X) (y : Y) {t : Fin sch.steps}
    (h : sch.kind t = .aliceToBob)
    (s : BitString (sch.spaceA t.castSucc) × BitString (sch.spaceB t.castSucc)) :
    D.stepState x y t s = (D.nextA t x s.1 false, D.nextB t y s.2 (D.sendA t x s.1)) := by
  simp [CommCircuit.stepState, h]

/-- Single-step register transition at a `bobToAlice` step. -/
theorem CommCircuit.stepState_of_bobToAlice {X Y Out : Type*} {S : ℕ} {sch : CommSchedule Out S}
    (D : CommCircuit X Y sch) (x : X) (y : Y) {t : Fin sch.steps}
    (h : sch.kind t = .bobToAlice)
    (s : BitString (sch.spaceA t.castSucc) × BitString (sch.spaceB t.castSucc)) :
    D.stepState x y t s = (D.nextA t x s.1 (D.sendB t y s.2), D.nextB t y s.2 false) := by
  simp [CommCircuit.stepState, h]

/-- Single-step register transition at a `localStep`. -/
theorem CommCircuit.stepState_of_localStep {X Y Out : Type*} {S : ℕ} {sch : CommSchedule Out S}
    (D : CommCircuit X Y sch) (x : X) (y : Y) {t : Fin sch.steps}
    (h : sch.kind t = .localStep)
    (s : BitString (sch.spaceA t.castSucc) × BitString (sch.spaceB t.castSucc)) :
    D.stepState x y t s = (D.nextA t x s.1 false, D.nextB t y s.2 false) := by
  simp [CommCircuit.stepState, h]

/-- Single-step register transition at an `emitAlice` step. -/
theorem CommCircuit.stepState_of_emitAlice {X Y Out : Type*} {S : ℕ} {sch : CommSchedule Out S}
    (D : CommCircuit X Y sch) (x : X) (y : Y) {t : Fin sch.steps} {o : Out}
    (h : sch.kind t = .emitAlice o)
    (s : BitString (sch.spaceA t.castSucc) × BitString (sch.spaceB t.castSucc)) :
    D.stepState x y t s = (D.nextA t x s.1 false, D.nextB t y s.2 false) := by
  simp [CommCircuit.stepState, h]

/-- Single-step register transition at an `emitBob` step. -/
theorem CommCircuit.stepState_of_emitBob {X Y Out : Type*} {S : ℕ} {sch : CommSchedule Out S}
    (D : CommCircuit X Y sch) (x : X) (y : Y) {t : Fin sch.steps} {o : Out}
    (h : sch.kind t = .emitBob o)
    (s : BitString (sch.spaceA t.castSucc) × BitString (sch.spaceB t.castSucc)) :
    D.stepState x y t s = (D.nextA t x s.1 false, D.nextB t y s.2 false) := by
  simp [CommCircuit.stepState, h]

/-- Register state `(sA, sB)` at boundary `k ≤ sch.steps`, defined by recursion on `k`. -/
@[expose] def CommCircuit.stateAtNat {X Y Out : Type*} {S : ℕ} {sch : CommSchedule Out S}
    (D : CommCircuit X Y sch) (x : X) (y : Y) :
    (k : ℕ) → (hk : k ≤ sch.steps) →
      BitString (sch.spaceA ⟨k, by omega⟩) × BitString (sch.spaceB ⟨k, by omega⟩)
  | 0, _ => (D.initA x, D.initB y)
  | k + 1, hk =>
    D.stepState x y ⟨k, by omega⟩ (D.stateAtNat x y k (by omega))

/-- Register state `(sA, sB)` at boundary `t : Fin (sch.steps + 1)`. -/
@[expose] def CommCircuit.stateAt {X Y Out : Type*} {S : ℕ} {sch : CommSchedule Out S}
    (D : CommCircuit X Y sch) (x : X) (y : Y) (t : Fin (sch.steps + 1)) :
    BitString (sch.spaceA t) × BitString (sch.spaceB t) :=
  D.stateAtNat x y t.val (Nat.lt_succ_iff.mp t.isLt)

/-- Relation between `CommCircuit.stateAt` and `CommCircuit.stateAtNat`. -/
theorem CommCircuit.stateAt_eq_stateAtNat {X Y Out : Type*} {S : ℕ} {sch : CommSchedule Out S}
    (D : CommCircuit X Y sch) (x : X) (y : Y) (t : Fin (sch.steps + 1)) :
    D.stateAt x y t = D.stateAtNat x y t.val (Nat.lt_succ_iff.mp t.isLt) := rfl

/-- Output vector computed by deterministic communicating circuit `D` on inputs `(x, y)`. -/
@[expose] def CommCircuit.eval {X Y Out : Type*} {S : ℕ} {sch : CommSchedule Out S}
    (D : CommCircuit X Y sch) (x : X) (y : Y) (o : Out) : Bool :=
  let t := sch.emitStep o
  let st := D.stateAt x y t.castSucc
  match sch.kind t with
  | .emitAlice _ => D.outA t x st.1
  | .emitBob _ => D.outB t y st.2
  | _ => false

/-- Output evaluation at an Alice-emitted output `o`. -/
theorem CommCircuit.eval_of_emitAlice {X Y Out : Type*} {S : ℕ} {sch : CommSchedule Out S}
    (D : CommCircuit X Y sch) (x : X) (y : Y) {o : Out} {o' : Out}
    (h : sch.kind (sch.emitStep o) = .emitAlice o') :
    D.eval x y o = D.outA (sch.emitStep o) x (D.stateAt x y (sch.emitStep o).castSucc).1 := by
  simp [CommCircuit.eval, h]

/-- Output evaluation at a Bob-emitted output `o`. -/
theorem CommCircuit.eval_of_emitBob {X Y Out : Type*} {S : ℕ} {sch : CommSchedule Out S}
    (D : CommCircuit X Y sch) (x : X) (y : Y) {o : Out} {o' : Out}
    (h : sch.kind (sch.emitStep o) = .emitBob o') :
    D.eval x y o = D.outB (sch.emitStep o) y (D.stateAt x y (sch.emitStep o).castSucc).2 := by
  simp [CommCircuit.eval, h]

/-- A randomized (public-coin) communicating circuit on a fixed schedule `sch` is a probability
distribution (`PMF`) over deterministic gate assignments following `sch`. -/
abbrev RandCommCircuit (X Y : Type*) {Out : Type*} {S : ℕ} (sch : CommSchedule Out S) : Type _ :=
  PMF (CommCircuit X Y sch)

/-- Error probability of a randomized communicating circuit `μ` computing `f` on input `(x, y)`. -/
@[expose] noncomputable def RandCommCircuit.errorProb {X Y Out : Type*} {S : ℕ}
  {sch : CommSchedule Out S}
    (μ : RandCommCircuit X Y sch) (f : X → Y → Out → Bool) (x : X) (y : Y) : ℝ :=
  (μ.toOuterMeasure {D | D.eval x y ≠ f x y}).toReal

/-- Success probability of a randomized communicating circuit `μ` computing `f` on `(x, y)`. -/
@[expose] noncomputable def RandCommCircuit.successProb {X Y Out : Type*} {S : ℕ}
  {sch : CommSchedule Out S}
    (μ : RandCommCircuit X Y sch) (f : X → Y → Out → Bool) (x : X) (y : Y) : ℝ :=
  (μ.toOuterMeasure {D | D.eval x y = f x y}).toReal

/-- A randomized communicating circuit `μ` computes `f` with worst-case error at most `ε`. -/
@[expose] def RandCommCircuit.Solves {X Y Out : Type*} {S : ℕ} {sch : CommSchedule Out S}
    (μ : RandCommCircuit X Y sch) (ε : ℝ) (f : X → Y → Out → Bool) : Prop :=
  ∀ x y, μ.errorProb f x y ≤ ε

/-- `successProb + errorProb = 1` for every input `(x, y)`. -/
theorem RandCommCircuit.successProb_add_errorProb {X Y Out : Type*} {S : ℕ}
    {sch : CommSchedule Out S} (μ : RandCommCircuit X Y sch) (f : X → Y → Out → Bool)
    (x : X) (y : Y) :
    μ.successProb f x y + μ.errorProb f x y = 1 := by
  classical
  have hcompl : {D : CommCircuit X Y sch | D.eval x y ≠ f x y} =
      {D : CommCircuit X Y sch | D.eval x y = f x y}ᶜ := by
    ext D; simp
  rw [RandCommCircuit.successProb, RandCommCircuit.errorProb, hcompl]
  exact Cslib.Probability.PMF.toOuterMeasure_toReal_add_compl μ
    {D : CommCircuit X Y sch | D.eval x y = f x y}

private theorem toOuterMeasure_toReal_add_le_one_of_disjoint {α : Type*} (μ : PMF α)
    {s t : Set α} (h : Disjoint s t) :
    (μ.toOuterMeasure s).toReal + (μ.toOuterMeasure t).toReal ≤ 1 := by
  have hsub : t ⊆ sᶜ := fun x hx hs => Set.disjoint_left.mp h hs hx
  have hmono := Cslib.Probability.PMF.toOuterMeasure_toReal_mono μ hsub
  linarith [Cslib.Probability.PMF.toOuterMeasure_toReal_add_compl μ s]

/-- If `μ` solves `f` with error at most `ε`, its success probability is at least `1 - ε`. -/
theorem RandCommCircuit.Solves.successProb_ge {X Y Out : Type*} {S : ℕ}
    {sch : CommSchedule Out S} {μ : RandCommCircuit X Y sch} {ε : ℝ} {f : X → Y → Out → Bool}
    (h : μ.Solves ε f) (x : X) (y : Y) :
    1 - ε ≤ μ.successProb f x y := by
  linarith [h x y, μ.successProb_add_errorProb f x y]

/-! ### Boolean Matrix-Vector and Matrix-Matrix Products -/

/-- Boolean matrix-vector multiplication `(A b)_i = ⋁_j (A_{i,j} ∧ b_j)`. -/
@[expose] def boolMatVec (N : ℕ) (A : Fin N → BitString N) (b : BitString N) : BitString N :=
  fun i => ndisj (A i) b

/-- Coordinate evaluation of `boolMatVec`. -/
theorem boolMatVec_apply (N : ℕ) (A : Fin N → BitString N) (b : BitString N) (i : Fin N) :
    boolMatVec N A b i = ndisj (A i) b := rfl

/-- Boolean matrix multiplication `(A B)_{i,j} = ⋁_l (A_{i,l} ∧ B_{l,j})`. -/
@[expose] def boolMatMul (N : ℕ) (A B : Fin N → BitString N) : Fin N × Fin N → Bool :=
  fun p => ndisj (A p.1) (fun l => B l p.2)

/-- Entry evaluation of `boolMatMul`. -/
theorem boolMatMul_apply (N : ℕ) (A B : Fin N → BitString N) (p : Fin N × Fin N) :
    boolMatMul N A B p = ndisj (A p.1) (fun l => B l p.2) := rfl

/-! ### Unconstrained Lower Bounds (`S ≥ 1` and `C ≥ |Out| / 4`) -/

private theorem stateAtNat_eq_of_zero_space {X Y Out : Type*} {sch : CommSchedule Out 0}
    (D : CommCircuit X Y sch) (x₁ x₂ : X) (y₁ y₂ : Y) (k : ℕ) (hk : k ≤ sch.steps) :
    D.stateAtNat x₁ y₁ k hk = D.stateAtNat x₂ y₂ k hk := by
  have hA : sch.spaceA ⟨k, by omega⟩ = 0 := by
    have := sch.space_bound ⟨k, by omega⟩; omega
  have hB : sch.spaceB ⟨k, by omega⟩ = 0 := by
    have := sch.space_bound ⟨k, by omega⟩; omega
  ext i
  · exact absurd i.isLt (by omega)
  · exact absurd i.isLt (by omega)

/-- Any bounded-error (`ε < 1 / 2`) communicating circuit computing a function that genuinely
depends on both `x` and `y` at some coordinate `o` must use space `S ≥ 1`. -/
theorem space_pos_of_depends_both {X Y Out : Type*} {S : ℕ} {sch : CommSchedule Out S}
    {μ : RandCommCircuit X Y sch} {ε : ℝ} {f : X → Y → Out → Bool}
    (hsolves : μ.Solves ε f) (hε : ε < 1 / 2)
    (o : Out) (hA : ∃ x y₁ y₂, f x y₁ o ≠ f x y₂ o)
    (hB : ∃ x₁ x₂ y, f x₁ y o ≠ f x₂ y o) :
    1 ≤ S := by
  classical
  by_contra hS
  have hS0 : S = 0 := by omega
  subst hS0
  rcases sch.emitStep_spec o with hAlice | hBob
  · obtain ⟨x, y₁, y₂, hne⟩ := hA
    have hdisj : Disjoint {D : CommCircuit X Y sch | D.eval x y₁ = f x y₁}
        {D : CommCircuit X Y sch | D.eval x y₂ = f x y₂} := by
      rw [Set.disjoint_left]
      intro D h1 h2
      have h1o := congrFun h1 o
      have h2o := congrFun h2 o
      have heq : D.eval x y₁ o = D.eval x y₂ o := by
        unfold CommCircuit.eval
        dsimp only
        rw [hAlice]
        have hst := stateAtNat_eq_of_zero_space D x x y₁ y₂ (sch.emitStep o).val
          (Nat.le_of_lt (sch.emitStep o).isLt)
        simp only [CommCircuit.stateAt, Fin.val_castSucc]
        rw [hst]
      exact hne (h1o.symm.trans (heq.trans h2o))
    have hsum : μ.successProb f x y₁ + μ.successProb f x y₂ ≤ 1 := by
      unfold RandCommCircuit.successProb
      exact toOuterMeasure_toReal_add_le_one_of_disjoint μ hdisj
    linarith [hsolves.successProb_ge x y₁, hsolves.successProb_ge x y₂]
  · obtain ⟨x₁, x₂, y, hne⟩ := hB
    have hdisj : Disjoint {D : CommCircuit X Y sch | D.eval x₁ y = f x₁ y}
        {D : CommCircuit X Y sch | D.eval x₂ y = f x₂ y} := by
      rw [Set.disjoint_left]
      intro D h1 h2
      have h1o := congrFun h1 o
      have h2o := congrFun h2 o
      have heq : D.eval x₁ y o = D.eval x₂ y o := by
        unfold CommCircuit.eval
        dsimp only
        rw [hBob]
        have hst := stateAtNat_eq_of_zero_space D x₁ x₂ y y (sch.emitStep o).val
          (Nat.le_of_lt (sch.emitStep o).isLt)
        simp only [CommCircuit.stateAt, Fin.val_castSucc]
        rw [hst]
      exact hne (h1o.symm.trans (heq.trans h2o))
    have hsum : μ.successProb f x₁ y + μ.successProb f x₂ y ≤ 1 := by
      unfold RandCommCircuit.successProb
      exact toOuterMeasure_toReal_add_le_one_of_disjoint μ hdisj
    linarith [hsolves.successProb_ge x₁ y, hsolves.successProb_ge x₂ y]

/-- Transcript of all bits sent at communication steps of `D` on `(x, y)`. -/
private def commTranscript {X Y Out : Type*} {S : ℕ} {sch : CommSchedule Out S}
    (D : CommCircuit X Y sch) (x : X) (y : Y)
    (t : {s : Fin sch.steps // sch.isCommStep s = true}) : Bool :=
  match sch.kind t.1 with
  | .aliceToBob => D.sendA t.1 x (D.stateAt x y t.1.castSucc).1
  | .bobToAlice => D.sendB t.1 y (D.stateAt x y t.1.castSucc).2
  | _ => false

/-- With `y` fixed, Bob's state at every step `k` is determined solely by `commTranscript D x y`. -/
private theorem stateB_eq_of_commTranscript_eq {X Y Out : Type*} {S : ℕ}
    {sch : CommSchedule Out S} (D : CommCircuit X Y sch) (x₁ x₂ : X) (y : Y)
    (htr : commTranscript D x₁ y = commTranscript D x₂ y) :
    ∀ (k : ℕ) (hk : k ≤ sch.steps),
      (D.stateAtNat x₁ y k hk).2 = (D.stateAtNat x₂ y k hk).2 := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro hk
    have hprev := ih (by omega)
    let t : Fin sch.steps := ⟨k, by omega⟩
    change (D.stepState x₁ y t (D.stateAtNat x₁ y k (by omega))).2 =
      (D.stepState x₂ y t (D.stateAtNat x₂ y k (by omega))).2
    unfold CommCircuit.stepState
    cases hkind : sch.kind t with
    | aliceToBob =>
      have hcomm : sch.isCommStep t = true := by simp [CommSchedule.isCommStep, hkind]
      have hbit := congrFun htr ⟨t, hcomm⟩
      simp only [commTranscript, hkind, CommCircuit.stateAt, Fin.val_castSucc] at hbit
      dsimp only
      rw [hprev, hbit]
    | bobToAlice => dsimp only; rw [hprev]
    | localStep => dsimp only; rw [hprev]
    | emitAlice _ => dsimp only; rw [hprev]
    | emitBob _ => dsimp only; rw [hprev]

/-- With `x` fixed, Alice's state at every step `k` is determined solely by `commTranscript D x y`.
-/
private theorem stateA_eq_of_commTranscript_eq {X Y Out : Type*} {S : ℕ}
    {sch : CommSchedule Out S} (D : CommCircuit X Y sch) (x : X) (y₁ y₂ : Y)
    (htr : commTranscript D x y₁ = commTranscript D x y₂) :
    ∀ (k : ℕ) (hk : k ≤ sch.steps),
      (D.stateAtNat x y₁ k hk).1 = (D.stateAtNat x y₂ k hk).1 := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro hk
    have hprev := ih (by omega)
    let t : Fin sch.steps := ⟨k, by omega⟩
    change (D.stepState x y₁ t (D.stateAtNat x y₁ k (by omega))).1 =
      (D.stepState x y₂ t (D.stateAtNat x y₂ k (by omega))).1
    unfold CommCircuit.stepState
    cases hkind : sch.kind t with
    | bobToAlice =>
      have hcomm : sch.isCommStep t = true := by simp [CommSchedule.isCommStep, hkind]
      have hbit := congrFun htr ⟨t, hcomm⟩
      simp only [commTranscript, hkind, CommCircuit.stateAt, Fin.val_castSucc] at hbit
      dsimp only
      rw [hprev, hbit]
    | aliceToBob => dsimp only; rw [hprev]
    | localStep => dsimp only; rw [hprev]
    | emitAlice _ => dsimp only; rw [hprev]
    | emitBob _ => dsimp only; rw [hprev]

/-- Double-counting lower bound when Bob emits `m` outputs and `S_X` shatters those `m` outputs
for a fixed `y₀`. -/
private theorem commCount_ge_of_bob_shatters {X Y Out : Type*} {S : ℕ}
    {sch : CommSchedule Out S} {μ : RandCommCircuit X Y sch} {ε : ℝ} {f : X → Y → Out → Bool}
    (hsolves : μ.Solves ε f) (hε : ε ≤ 1 / 3)
    (OB : Finset Out) (hOB : ∀ o ∈ OB, sch.kind (sch.emitStep o) = .emitBob o)
    (y₀ : Y) (SX : Finset X) (hSX_card : SX.card = 2 ^ OB.card)
    (hSX_inj : ∀ x₁ ∈ SX, ∀ x₂ ∈ SX,
      (∀ o ∈ OB, f x₁ y₀ o = f x₂ y₀ o) → x₁ = x₂) :
    OB.card ≤ sch.commCount + 1 := by
  classical
  -- Step 1: Every deterministic circuit `D` succeeds on at most `2 ^ sch.commCount` inputs in `SX`.
  have hdet_le : ∀ D : CommCircuit X Y sch,
      (SX.filter fun x => D.eval x y₀ = f x y₀).card ≤ 2 ^ sch.commCount := by
    intro D
    let T := {s : Fin sch.steps // sch.isCommStep s = true} → Bool
    have hcardT : Fintype.card T = 2 ^ sch.commCount := by
      rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_subtype, CommSchedule.commCount]
    have hinj : Set.InjOn (fun x => commTranscript D x y₀)
        (SX.filter fun x => D.eval x y₀ = f x y₀ : Set X) := by
      intro x₁ hx₁ x₂ hx₂ htr
      simp only [Finset.mem_coe, Finset.mem_filter] at hx₁ hx₂
      apply hSX_inj x₁ hx₁.1 x₂ hx₂.1
      intro o ho
      have h1 := congrFun hx₁.2 o
      have h2 := congrFun hx₂.2 o
      rw [← h1, ← h2]
      unfold CommCircuit.eval
      dsimp only
      rw [hOB o ho]
      simp only [CommCircuit.stateAt, Fin.val_castSucc]
      rw [stateB_eq_of_commTranscript_eq D x₁ x₂ y₀ htr (sch.emitStep o).val
        (Nat.le_of_lt (sch.emitStep o).isLt)]
    calc
      (SX.filter fun x => D.eval x y₀ = f x y₀).card
        ≤ (Finset.univ : Finset T).card :=
          Finset.card_le_card_of_injOn (fun x => commTranscript D x y₀)
            (fun _ _ => Finset.mem_univ _) hinj
      _ = 2 ^ sch.commCount := by rw [Finset.card_univ, hcardT]
  -- Step 2: Double-counting over `x ∈ SX` and `D ~ μ` in `ENNReal`.
  have hsum_le : ∑ x ∈ SX, μ.successProb f x y₀ ≤ (2 ^ sch.commCount : ℝ) := by
    have hENN : ∑ x ∈ SX, μ.toOuterMeasure {D | D.eval x y₀ = f x y₀} ≤
        ((2 ^ sch.commCount : ℕ) : ENNReal) := by
      simp_rw [PMF.toOuterMeasure_apply]
      rw [← Summable.tsum_finsetSum (fun _ _ => CompleteLattice.summable)]
      calc
        ∑' D : CommCircuit X Y sch, ∑ x ∈ SX,
            ({D' | D'.eval x y₀ = f x y₀}).indicator (⇑μ) D
          = ∑' D : CommCircuit X Y sch,
              ((SX.filter fun x => D.eval x y₀ = f x y₀).card : ENNReal) * μ D := by
            congr 1; funext D
            rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_mul, Finset.sum_filter]
            refine Finset.sum_congr rfl fun x _ => ?_
            by_cases h : D.eval x y₀ = f x y₀ <;> simp [Set.indicator, h]
        _ ≤ ∑' D : CommCircuit X Y sch, ((2 ^ sch.commCount : ℕ) : ENNReal) * μ D := by
            refine tsum_le_tsum fun D => ?_
            gcongr
            exact_mod_cast hdet_le D
        _ = ((2 ^ sch.commCount : ℕ) : ENNReal) * ∑' D, μ D := ENNReal.tsum_mul_left
        _ = ((2 ^ sch.commCount : ℕ) : ENNReal) := by rw [μ.tsum_coe, mul_one]
    have htoReal := ENNReal.toReal_mono (ENNReal.natCast_ne_top _) hENN
    rw [ENNReal.toReal_sum (fun x _ => ne_of_lt (lt_of_le_of_lt
      (Cslib.Probability.PMF.toOuterMeasure_le_one μ _) ENNReal.one_lt_top)),
      ENNReal.toReal_natCast, Nat.cast_pow, Nat.cast_ofNat] at htoReal
    exact htoReal
  -- Step 3: Compare with `∑ x ∈ SX, (2 / 3) = (2 / 3) * 2 ^ OB.card`.
  have hsum_ge : (2 / 3 : ℝ) * (2 ^ OB.card : ℝ) ≤ ∑ x ∈ SX, μ.successProb f x y₀ := by
    calc
      (2 / 3 : ℝ) * (2 ^ OB.card : ℝ)
        = ∑ _x ∈ SX, (2 / 3 : ℝ) := by
          rw [Finset.sum_const, hSX_card, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat, mul_comm]
      _ ≤ ∑ x ∈ SX, μ.successProb f x y₀ :=
          Finset.sum_le_sum fun x _ => by linarith [hsolves.successProb_ge x y₀]
  have hpow : (2 : ℝ) ^ OB.card ≤ (2 : ℝ) ^ (sch.commCount + 1) := by
    have hpos : (0 : ℝ) ≤ (2 : ℝ) ^ OB.card := by positivity
    rw [pow_succ]
    linarith [hsum_ge.trans hsum_le]
  exact_mod_cast (pow_le_pow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp hpow

/-- Symmetric double-counting lower bound when Alice emits `m` outputs and `S_Y` shatters those
`m` outputs for a fixed `x₀`. -/
private theorem commCount_ge_of_alice_shatters {X Y Out : Type*} {S : ℕ}
    {sch : CommSchedule Out S} {μ : RandCommCircuit X Y sch} {ε : ℝ} {f : X → Y → Out → Bool}
    (hsolves : μ.Solves ε f) (hε : ε ≤ 1 / 3)
    (OA : Finset Out) (hOA : ∀ o ∈ OA, sch.kind (sch.emitStep o) = .emitAlice o)
    (x₀ : X) (SY : Finset Y) (hSY_card : SY.card = 2 ^ OA.card)
    (hSY_inj : ∀ y₁ ∈ SY, ∀ y₂ ∈ SY,
      (∀ o ∈ OA, f x₀ y₁ o = f x₀ y₂ o) → y₁ = y₂) :
    OA.card ≤ sch.commCount + 1 := by
  classical
  have hdet_le : ∀ D : CommCircuit X Y sch,
      (SY.filter fun y => D.eval x₀ y = f x₀ y).card ≤ 2 ^ sch.commCount := by
    intro D
    let T := {s : Fin sch.steps // sch.isCommStep s = true} → Bool
    have hcardT : Fintype.card T = 2 ^ sch.commCount := by
      rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_subtype, CommSchedule.commCount]
    have hinj : Set.InjOn (fun y => commTranscript D x₀ y)
        (SY.filter fun y => D.eval x₀ y = f x₀ y : Set Y) := by
      intro y₁ hy₁ y₂ hy₂ htr
      simp only [Finset.mem_coe, Finset.mem_filter] at hy₁ hy₂
      apply hSY_inj y₁ hy₁.1 y₂ hy₂.1
      intro o ho
      have h1 := congrFun hy₁.2 o
      have h2 := congrFun hy₂.2 o
      rw [← h1, ← h2]
      unfold CommCircuit.eval
      dsimp only
      rw [hOA o ho]
      simp only [CommCircuit.stateAt, Fin.val_castSucc]
      rw [stateA_eq_of_commTranscript_eq D x₀ y₁ y₂ htr (sch.emitStep o).val
        (Nat.le_of_lt (sch.emitStep o).isLt)]
    calc
      (SY.filter fun y => D.eval x₀ y = f x₀ y).card
        ≤ (Finset.univ : Finset T).card :=
          Finset.card_le_card_of_injOn (fun y => commTranscript D x₀ y)
            (fun _ _ => Finset.mem_univ _) hinj
      _ = 2 ^ sch.commCount := by rw [Finset.card_univ, hcardT]
  have hsum_le : ∑ y ∈ SY, μ.successProb f x₀ y ≤ (2 ^ sch.commCount : ℝ) := by
    have hENN : ∑ y ∈ SY, μ.toOuterMeasure {D | D.eval x₀ y = f x₀ y} ≤
        ((2 ^ sch.commCount : ℕ) : ENNReal) := by
      simp_rw [PMF.toOuterMeasure_apply]
      rw [← Summable.tsum_finsetSum (fun _ _ => CompleteLattice.summable)]
      calc
        ∑' D : CommCircuit X Y sch, ∑ y ∈ SY,
            ({D' | D'.eval x₀ y = f x₀ y}).indicator (⇑μ) D
          = ∑' D : CommCircuit X Y sch,
              ((SY.filter fun y => D.eval x₀ y = f x₀ y).card : ENNReal) * μ D := by
            congr 1; funext D
            rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_mul, Finset.sum_filter]
            refine Finset.sum_congr rfl fun y _ => ?_
            by_cases h : D.eval x₀ y = f x₀ y <;> simp [Set.indicator, h]
        _ ≤ ∑' D : CommCircuit X Y sch, ((2 ^ sch.commCount : ℕ) : ENNReal) * μ D := by
            refine tsum_le_tsum fun D => ?_
            gcongr
            exact_mod_cast hdet_le D
        _ = ((2 ^ sch.commCount : ℕ) : ENNReal) * ∑' D, μ D := ENNReal.tsum_mul_left
        _ = ((2 ^ sch.commCount : ℕ) : ENNReal) := by rw [μ.tsum_coe, mul_one]
    have htoReal := ENNReal.toReal_mono (ENNReal.natCast_ne_top _) hENN
    rw [ENNReal.toReal_sum (fun y _ => ne_of_lt (lt_of_le_of_lt
      (Cslib.Probability.PMF.toOuterMeasure_le_one μ _) ENNReal.one_lt_top)),
      ENNReal.toReal_natCast, Nat.cast_pow, Nat.cast_ofNat] at htoReal
    exact htoReal
  have hsum_ge : (2 / 3 : ℝ) * (2 ^ OA.card : ℝ) ≤ ∑ y ∈ SY, μ.successProb f x₀ y := by
    calc
      (2 / 3 : ℝ) * (2 ^ OA.card : ℝ)
        = ∑ _y ∈ SY, (2 / 3 : ℝ) := by
          rw [Finset.sum_const, hSY_card, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat, mul_comm]
      _ ≤ ∑ y ∈ SY, μ.successProb f x₀ y :=
          Finset.sum_le_sum fun y _ => by linarith [hsolves.successProb_ge x₀ y]
  have hpow : (2 : ℝ) ^ OA.card ≤ (2 : ℝ) ^ (sch.commCount + 1) := by
    have hpos : (0 : ℝ) ≤ (2 : ℝ) ^ OA.card := by positivity
    rw [pow_succ]
    linarith [hsum_ge.trans hsum_le]
  exact_mod_cast (pow_le_pow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp hpow

/-- For `N ≥ 1`, any bounded-error circuit for `boolMatVec N` uses `1 ≤ S` and `N ≤ 4 * C`. -/
theorem mv_unconstrained_bounds {N S : ℕ} (hN : 1 ≤ N)
    {sch : CommSchedule (Fin N) S} {μ : RandCommCircuit (Fin N → BitString N) (BitString N) sch}
    (hsolves : μ.Solves (1 / 3) (boolMatVec N)) :
    1 ≤ S ∧ N ≤ 4 * sch.commCount := by
  classical
  let i₀ : Fin N := ⟨0, by omega⟩
  have hS : 1 ≤ S := by
    refine space_pos_of_depends_both hsolves (by norm_num) i₀ ?_ ?_
    · refine ⟨fun _ _ => true, fun _ => false, fun _ => true, ?_⟩
      have h1 : boolMatVec N (fun _ _ => true) (fun _ => false) i₀ = false :=
        ndisj_const_false_right _
      have h2 : boolMatVec N (fun _ _ => true) (fun _ => true) i₀ = true :=
        ndisj_eq_true_iff_exists.mpr ⟨i₀, rfl, rfl⟩
      rw [h1, h2]; decide
    · refine ⟨fun _ _ => false, fun _ _ => true, fun _ => true, ?_⟩
      have h1 : boolMatVec N (fun _ _ => false) (fun _ => true) i₀ = false :=
        ndisj_const_false_left _
      have h2 : boolMatVec N (fun _ _ => true) (fun _ => true) i₀ = true :=
        ndisj_eq_true_iff_exists.mpr ⟨i₀, rfl, rfl⟩
      rw [h1, h2]; decide
  -- Partition `Fin N` into Alice-emitted and Bob-emitted outputs.
  let OA := Finset.univ.filter fun i : Fin N => sch.kind (sch.emitStep i) = .emitAlice i
  let OB := Finset.univ.filter fun i : Fin N => sch.kind (sch.emitStep i) = .emitBob i
  have hpart : OA.card + OB.card = N := by
    have hdisj : Disjoint OA OB := by
      rw [Finset.disjoint_left]
      intro i h1 h2
      simp only [OA, OB, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
      cases h1.symm.trans h2
    have hunion : OA ∪ OB = Finset.univ := by
      ext i
      simp only [OA, OB, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      exact sch.emitStep_spec i
    rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_univ, Fintype.card_fin]
  -- First show `1 ≤ sch.commCount`.
  have hC1 : 1 ≤ sch.commCount := by
    by_contra hC0
    have hCeq : sch.commCount = 0 := by omega
    rcases sch.emitStep_spec i₀ with hA | hB
    · have htr : ∀ (D : CommCircuit (Fin N → BitString N) (BitString N) sch) x y₁ y₂,
          commTranscript D x y₁ = commTranscript D x y₂ := by
        intro D x y₁ y₂; funext ⟨s, hs⟩
        have hmem : s ∈ Finset.univ.filter (fun t : Fin sch.steps => sch.isCommStep t = true) := by
          simpa using hs
        have hpos : 0 < sch.commCount := Finset.card_pos.mpr ⟨s, hmem⟩
        omega
      have hdisj : Disjoint
          {D : CommCircuit (Fin N → BitString N) (BitString N) sch |
            D.eval (fun _ _ => true) (fun _ => false) =
              boolMatVec N (fun _ _ => true) (fun _ => false)}
          {D : CommCircuit (Fin N → BitString N) (BitString N) sch |
            D.eval (fun _ _ => true) (fun _ => true) =
              boolMatVec N (fun _ _ => true) (fun _ => true)} := by
        rw [Set.disjoint_left]
        intro D h1 h2
        have h1o := congrFun h1 i₀
        have h2o := congrFun h2 i₀
        have heq : D.eval (fun _ _ => true) (fun _ => false) i₀ =
            D.eval (fun _ _ => true) (fun _ => true) i₀ := by
          unfold CommCircuit.eval; dsimp only; rw [hA]
          simp only [CommCircuit.stateAt, Fin.val_castSucc]
          rw [stateA_eq_of_commTranscript_eq D _ _ _ (htr D _ _ _) (sch.emitStep i₀).val
            (Nat.le_of_lt (sch.emitStep i₀).isLt)]
        have hne : boolMatVec N (fun _ _ => true) (fun _ => false) i₀ ≠
            boolMatVec N (fun _ _ => true) (fun _ => true) i₀ := by
          have hb1 : boolMatVec N (fun _ _ => true) (fun _ => false) i₀ = false :=
            ndisj_const_false_right _
          have hb2 : boolMatVec N (fun _ _ => true) (fun _ => true) i₀ = true :=
            ndisj_eq_true_iff_exists.mpr ⟨i₀, rfl, rfl⟩
          rw [hb1, hb2]; decide
        exact hne (h1o.symm.trans (heq.trans h2o))
      have hsum : μ.successProb (boolMatVec N) (fun _ _ => true) (fun _ => false) +
          μ.successProb (boolMatVec N) (fun _ _ => true) (fun _ => true) ≤ 1 := by
        unfold RandCommCircuit.successProb
        exact toOuterMeasure_toReal_add_le_one_of_disjoint μ hdisj
      linarith [hsolves.successProb_ge (fun _ _ => true) (fun _ => false),
        hsolves.successProb_ge (fun _ _ => true) (fun _ => true)]
    · have htr : ∀ (D : CommCircuit (Fin N → BitString N) (BitString N) sch) x₁ x₂ y,
          commTranscript D x₁ y = commTranscript D x₂ y := by
        intro D x₁ x₂ y; funext ⟨s, hs⟩
        have hmem : s ∈ Finset.univ.filter (fun t : Fin sch.steps => sch.isCommStep t = true) := by
          simpa using hs
        have hpos : 0 < sch.commCount := Finset.card_pos.mpr ⟨s, hmem⟩
        omega
      have hdisj : Disjoint
          {D : CommCircuit (Fin N → BitString N) (BitString N) sch |
            D.eval (fun _ _ => false) (fun _ => true) =
              boolMatVec N (fun _ _ => false) (fun _ => true)}
          {D : CommCircuit (Fin N → BitString N) (BitString N) sch |
            D.eval (fun _ _ => true) (fun _ => true) =
              boolMatVec N (fun _ _ => true) (fun _ => true)} := by
        rw [Set.disjoint_left]
        intro D h1 h2
        have h1o := congrFun h1 i₀
        have h2o := congrFun h2 i₀
        have heq : D.eval (fun _ _ => false) (fun _ => true) i₀ =
            D.eval (fun _ _ => true) (fun _ => true) i₀ := by
          unfold CommCircuit.eval; dsimp only; rw [hB]
          simp only [CommCircuit.stateAt, Fin.val_castSucc]
          rw [stateB_eq_of_commTranscript_eq D _ _ _ (htr D _ _ _) (sch.emitStep i₀).val
            (Nat.le_of_lt (sch.emitStep i₀).isLt)]
        have hne : boolMatVec N (fun _ _ => false) (fun _ => true) i₀ ≠
            boolMatVec N (fun _ _ => true) (fun _ => true) i₀ := by
          have hb1 : boolMatVec N (fun _ _ => false) (fun _ => true) i₀ = false :=
            ndisj_const_false_left _
          have hb2 : boolMatVec N (fun _ _ => true) (fun _ => true) i₀ = true :=
            ndisj_eq_true_iff_exists.mpr ⟨i₀, rfl, rfl⟩
          rw [hb1, hb2]; decide
        exact hne (h1o.symm.trans (heq.trans h2o))
      have hsum : μ.successProb (boolMatVec N) (fun _ _ => false) (fun _ => true) +
          μ.successProb (boolMatVec N) (fun _ _ => true) (fun _ => true) ≤ 1 := by
        unfold RandCommCircuit.successProb
        exact toOuterMeasure_toReal_add_le_one_of_disjoint μ hdisj
      linarith [hsolves.successProb_ge (fun _ _ => false) (fun _ => true),
        hsolves.successProb_ge (fun _ _ => true) (fun _ => true)]
  -- Second, shatter whichever of `OA`, `OB` has cardinality ≥ N / 2.
  have hCbound : N ≤ 2 * (sch.commCount + 1) := by
    by_cases hmaj : OB.card ≤ OA.card
    · -- Alice emits ≥ N / 2 outputs: fix `A = I_N` and shatter `b` on `OA`.
      let emb : (OA → Bool) → BitString N := fun v i => if h : i ∈ OA then v ⟨i, h⟩ else false
      have hemb_inj : Function.Injective emb := by
        intro v₁ v₂ h; funext ⟨i, hi⟩
        have := congrFun h i; simp only [emb, hi, ↓reduceDIte] at this; exact this
      let SY : Finset (BitString N) := Finset.univ.image emb
      have hSY_card : SY.card = 2 ^ OA.card := by
        rw [Finset.card_image_of_injective _ hemb_inj, Finset.card_univ, Fintype.card_fun,
          Fintype.card_bool, Fintype.card_coe]
      have hbd := commCount_ge_of_alice_shatters hsolves le_rfl OA
        (fun o ho => (Finset.mem_filter.mp ho).2)
        (fun i j => decide (i = j)) SY hSY_card (by
          intro y₁ hy₁ y₂ hy₂ hEq
          obtain ⟨v₁, _, rfl⟩ := Finset.mem_image.mp hy₁
          obtain ⟨v₂, _, rfl⟩ := Finset.mem_image.mp hy₂
          congr 1; funext ⟨o, ho⟩
          have h := hEq o ho
          have heval_v : ∀ v : OA → Bool,
              boolMatVec N (fun i j => decide (i = j)) (emb v) o = v ⟨o, ho⟩ := by
            intro v
            apply Bool.eq_iff_iff.mpr
            rw [boolMatVec, ndisj_eq_true_iff_exists]
            simp [emb, ho]
          rw [heval_v v₁, heval_v v₂] at h; exact h)
      omega
    · -- Bob emits > N / 2 outputs: fix `b = e_0` and shatter column 0 of `A` on `OB`.
      let emb : (OB → Bool) → (Fin N → BitString N) := fun v i j =>
        if h : i ∈ OB ∧ j = i₀ then v ⟨i, h.1⟩ else false
      have hemb_inj : Function.Injective emb := by
        intro v₁ v₂ h; funext ⟨i, hi⟩
        have := congrFun (congrFun h i) i₀
        simp only [emb, hi, true_and, ↓reduceDIte] at this; exact this
      let SX : Finset (Fin N → BitString N) := Finset.univ.image emb
      have hSX_card : SX.card = 2 ^ OB.card := by
        rw [Finset.card_image_of_injective _ hemb_inj, Finset.card_univ, Fintype.card_fun,
          Fintype.card_bool, Fintype.card_coe]
      let b₀ : BitString N := fun j => decide (j = i₀)
      have hbd := commCount_ge_of_bob_shatters hsolves le_rfl OB
        (fun o ho => (Finset.mem_filter.mp ho).2) b₀ SX hSX_card (by
          intro x₁ hx₁ x₂ hx₂ hEq
          obtain ⟨v₁, _, rfl⟩ := Finset.mem_image.mp hx₁
          obtain ⟨v₂, _, rfl⟩ := Finset.mem_image.mp hx₂
          congr 1; funext ⟨o, ho⟩
          have h := hEq o ho
          have heval_v : ∀ v : OB → Bool, boolMatVec N (emb v) b₀ o = v ⟨o, ho⟩ := by
            intro v
            apply Bool.eq_iff_iff.mpr
            rw [boolMatVec, ndisj_eq_true_iff_exists]
            simp [emb, b₀, ho]
          rw [heval_v v₁, heval_v v₂] at h; exact h)
      omega
  exact ⟨hS, by omega⟩

/-- For `N ≥ 1`, any bounded-error circuit for `boolMatMul N` uses `1 ≤ S` and `N^2 ≤ 4 * C`. -/
theorem mm_unconstrained_bounds {N S : ℕ} (hN : 1 ≤ N)
    {sch : CommSchedule (Fin N × Fin N) S}
    {μ : RandCommCircuit (Fin N → BitString N) (Fin N → BitString N) sch}
    (hsolves : μ.Solves (1 / 3) (boolMatMul N)) :
    1 ≤ S ∧ N ^ 2 ≤ 4 * sch.commCount := by
  classical
  let i₀ : Fin N := ⟨0, by omega⟩
  let p₀ : Fin N × Fin N := (i₀, i₀)
  have hS : 1 ≤ S := by
    refine space_pos_of_depends_both hsolves (by norm_num) p₀ ?_ ?_
    · refine ⟨fun _ _ => true, fun _ _ => false, fun _ _ => true, ?_⟩
      have h1 : boolMatMul N (fun _ _ => true) (fun _ _ => false) p₀ = false :=
        ndisj_const_false_right _
      have h2 : boolMatMul N (fun _ _ => true) (fun _ _ => true) p₀ = true :=
        ndisj_eq_true_iff_exists.mpr ⟨i₀, rfl, rfl⟩
      rw [h1, h2]; decide
    · refine ⟨fun _ _ => false, fun _ _ => true, fun _ _ => true, ?_⟩
      have h1 : boolMatMul N (fun _ _ => false) (fun _ _ => true) p₀ = false :=
        ndisj_const_false_left _
      have h2 : boolMatMul N (fun _ _ => true) (fun _ _ => true) p₀ = true :=
        ndisj_eq_true_iff_exists.mpr ⟨i₀, rfl, rfl⟩
      rw [h1, h2]; decide
  let OA := Finset.univ.filter fun p : Fin N × Fin N => sch.kind (sch.emitStep p) = .emitAlice p
  let OB := Finset.univ.filter fun p : Fin N × Fin N => sch.kind (sch.emitStep p) = .emitBob p
  have hpart : OA.card + OB.card = N ^ 2 := by
    have hdisj : Disjoint OA OB := by
      rw [Finset.disjoint_left]
      intro p h1 h2
      simp only [OA, OB, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
      cases h1.symm.trans h2
    have hunion : OA ∪ OB = Finset.univ := by
      ext p
      simp only [OA, OB, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      exact sch.emitStep_spec p
    rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_univ, Fintype.card_prod,
      Fintype.card_fin, sq]
  have hC1 : 1 ≤ sch.commCount := by
    by_contra hC0
    have hCeq : sch.commCount = 0 := by omega
    rcases sch.emitStep_spec p₀ with hA | hB
    · have htr : ∀ (D : CommCircuit (Fin N → BitString N) (Fin N → BitString N) sch) x y₁ y₂,
          commTranscript D x y₁ = commTranscript D x y₂ := by
        intro D x y₁ y₂; funext ⟨s, hs⟩
        have hmem : s ∈ Finset.univ.filter (fun t : Fin sch.steps => sch.isCommStep t = true) := by
          simpa using hs
        have hpos : 0 < sch.commCount := Finset.card_pos.mpr ⟨s, hmem⟩
        omega
      have hdisj : Disjoint
          {D : CommCircuit (Fin N → BitString N) (Fin N → BitString N) sch |
            D.eval (fun _ _ => true) (fun _ _ => false) =
              boolMatMul N (fun _ _ => true) (fun _ _ => false)}
          {D : CommCircuit (Fin N → BitString N) (Fin N → BitString N) sch |
            D.eval (fun _ _ => true) (fun _ _ => true) =
              boolMatMul N (fun _ _ => true) (fun _ _ => true)} := by
        rw [Set.disjoint_left]
        intro D h1 h2
        have h1o := congrFun h1 p₀
        have h2o := congrFun h2 p₀
        have heq : D.eval (fun _ _ => true) (fun _ _ => false) p₀ =
            D.eval (fun _ _ => true) (fun _ _ => true) p₀ := by
          unfold CommCircuit.eval; dsimp only; rw [hA]
          simp only [CommCircuit.stateAt, Fin.val_castSucc]
          rw [stateA_eq_of_commTranscript_eq D _ _ _ (htr D _ _ _) (sch.emitStep p₀).val
            (Nat.le_of_lt (sch.emitStep p₀).isLt)]
        have hne : boolMatMul N (fun _ _ => true) (fun _ _ => false) p₀ ≠
            boolMatMul N (fun _ _ => true) (fun _ _ => true) p₀ := by
          have hb1 : boolMatMul N (fun _ _ => true) (fun _ _ => false) p₀ = false :=
            ndisj_const_false_right _
          have hb2 : boolMatMul N (fun _ _ => true) (fun _ _ => true) p₀ = true :=
            ndisj_eq_true_iff_exists.mpr ⟨i₀, rfl, rfl⟩
          rw [hb1, hb2]; decide
        exact hne (h1o.symm.trans (heq.trans h2o))
      have hsum : μ.successProb (boolMatMul N) (fun _ _ => true) (fun _ _ => false) +
          μ.successProb (boolMatMul N) (fun _ _ => true) (fun _ _ => true) ≤ 1 := by
        unfold RandCommCircuit.successProb
        exact toOuterMeasure_toReal_add_le_one_of_disjoint μ hdisj
      linarith [hsolves.successProb_ge (fun _ _ => true) (fun _ _ => false),
        hsolves.successProb_ge (fun _ _ => true) (fun _ _ => true)]
    · have htr : ∀ (D : CommCircuit (Fin N → BitString N) (Fin N → BitString N) sch) x₁ x₂ y,
          commTranscript D x₁ y = commTranscript D x₂ y := by
        intro D x₁ x₂ y; funext ⟨s, hs⟩
        have hmem : s ∈ Finset.univ.filter (fun t : Fin sch.steps => sch.isCommStep t = true) := by
          simpa using hs
        have hpos : 0 < sch.commCount := Finset.card_pos.mpr ⟨s, hmem⟩
        omega
      have hdisj : Disjoint
          {D : CommCircuit (Fin N → BitString N) (Fin N → BitString N) sch |
            D.eval (fun _ _ => false) (fun _ _ => true) =
              boolMatMul N (fun _ _ => false) (fun _ _ => true)}
          {D : CommCircuit (Fin N → BitString N) (Fin N → BitString N) sch |
            D.eval (fun _ _ => true) (fun _ _ => true) =
              boolMatMul N (fun _ _ => true) (fun _ _ => true)} := by
        rw [Set.disjoint_left]
        intro D h1 h2
        have h1o := congrFun h1 p₀
        have h2o := congrFun h2 p₀
        have heq : D.eval (fun _ _ => false) (fun _ _ => true) p₀ =
            D.eval (fun _ _ => true) (fun _ _ => true) p₀ := by
          unfold CommCircuit.eval; dsimp only; rw [hB]
          simp only [CommCircuit.stateAt, Fin.val_castSucc]
          rw [stateB_eq_of_commTranscript_eq D _ _ _ (htr D _ _ _) (sch.emitStep p₀).val
            (Nat.le_of_lt (sch.emitStep p₀).isLt)]
        have hne : boolMatMul N (fun _ _ => false) (fun _ _ => true) p₀ ≠
            boolMatMul N (fun _ _ => true) (fun _ _ => true) p₀ := by
          have hb1 : boolMatMul N (fun _ _ => false) (fun _ _ => true) p₀ = false :=
            ndisj_const_false_left _
          have hb2 : boolMatMul N (fun _ _ => true) (fun _ _ => true) p₀ = true :=
            ndisj_eq_true_iff_exists.mpr ⟨i₀, rfl, rfl⟩
          rw [hb1, hb2]; decide
        exact hne (h1o.symm.trans (heq.trans h2o))
      have hsum : μ.successProb (boolMatMul N) (fun _ _ => false) (fun _ _ => true) +
          μ.successProb (boolMatMul N) (fun _ _ => true) (fun _ _ => true) ≤ 1 := by
        unfold RandCommCircuit.successProb
        exact toOuterMeasure_toReal_add_le_one_of_disjoint μ hdisj
      linarith [hsolves.successProb_ge (fun _ _ => false) (fun _ _ => true),
        hsolves.successProb_ge (fun _ _ => true) (fun _ _ => true)]
  have hCbound : N ^ 2 ≤ 2 * (sch.commCount + 1) := by
    by_cases hmaj : OB.card ≤ OA.card
    · let emb : (OA → Bool) → (Fin N → BitString N) := fun v i j =>
        if h : (i, j) ∈ OA then v ⟨(i, j), h⟩ else false
      have hemb_inj : Function.Injective emb := by
        intro v₁ v₂ h; funext ⟨⟨i, j⟩, hij⟩
        have := congrFun (congrFun h i) j
        simp only [emb, hij, ↓reduceDIte] at this; exact this
      let SY : Finset (Fin N → BitString N) := Finset.univ.image emb
      have hSY_card : SY.card = 2 ^ OA.card := by
        rw [Finset.card_image_of_injective _ hemb_inj, Finset.card_univ, Fintype.card_fun,
          Fintype.card_bool, Fintype.card_coe]
      have hbd := commCount_ge_of_alice_shatters hsolves le_rfl OA
        (fun o ho => (Finset.mem_filter.mp ho).2)
        (fun i j => decide (i = j)) SY hSY_card (by
          intro y₁ hy₁ y₂ hy₂ hEq
          obtain ⟨v₁, _, rfl⟩ := Finset.mem_image.mp hy₁
          obtain ⟨v₂, _, rfl⟩ := Finset.mem_image.mp hy₂
          congr 1; funext ⟨⟨i, j⟩, hij⟩
          have h := hEq (i, j) hij
          have heval_v : ∀ v : OA → Bool,
              boolMatMul N (fun a b => decide (a = b)) (emb v) (i, j) = v ⟨(i, j), hij⟩ := by
            intro v
            apply Bool.eq_iff_iff.mpr
            rw [boolMatMul, ndisj_eq_true_iff_exists]
            simp [emb, hij]
          rw [heval_v v₁, heval_v v₂] at h; exact h)
      omega
    · let emb : (OB → Bool) → (Fin N → BitString N) := fun v i j =>
        if h : (i, j) ∈ OB then v ⟨(i, j), h⟩ else false
      have hemb_inj : Function.Injective emb := by
        intro v₁ v₂ h; funext ⟨⟨i, j⟩, hij⟩
        have := congrFun (congrFun h i) j
        simp only [emb, hij, ↓reduceDIte] at this; exact this
      let SX : Finset (Fin N → BitString N) := Finset.univ.image emb
      have hSX_card : SX.card = 2 ^ OB.card := by
        rw [Finset.card_image_of_injective _ hemb_inj, Finset.card_univ, Fintype.card_fun,
          Fintype.card_bool, Fintype.card_coe]
      have hbd := commCount_ge_of_bob_shatters hsolves le_rfl OB
        (fun o ho => (Finset.mem_filter.mp ho).2)
        (fun i j => decide (i = j)) SX hSX_card (by
          intro x₁ hx₁ x₂ hx₂ hEq
          obtain ⟨v₁, _, rfl⟩ := Finset.mem_image.mp hx₁
          obtain ⟨v₂, _, rfl⟩ := Finset.mem_image.mp hx₂
          congr 1; funext ⟨⟨i, j⟩, hij⟩
          have h := hEq (i, j) hij
          have heval_v : ∀ v : OB → Bool,
              boolMatMul N (emb v) (fun a b => decide (a = b)) (i, j) = v ⟨(i, j), hij⟩ := by
            intro v
            apply Bool.eq_iff_iff.mpr
            rw [boolMatMul, ndisj_eq_true_iff_exists]
            simp [emb, hij]
          rw [heval_v v₁, heval_v v₂] at h; exact h)
      omega
  exact ⟨hS, by omega⟩


end

end CslibFrontier.Computability.Communication
