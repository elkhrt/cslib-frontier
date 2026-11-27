/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Streaming.Basic
public import Mathlib.Data.Fintype.Card

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.List.OfFn

/-!
# Layered Deterministic Read-Once Branching Programs

Layered deterministic read-once branching programs (`LayeredROBP n Alph Z`) over an arbitrary
input alphabet `Alph` and output type `Z`, generalizing uniform-state Boolean read-once programs
(`CslibFrontier.Computability.BranchingProgram.ReadOnce`) to arbitrary finite vertex layers
`V : Fin (n + 1) → Type w` with layerwise reachability, combinators (`ofLayeredSystem`,
`reindex`, `mapOutput`, `comap`), and width-preserving reductions from `Cslib.Streaming.Algorithm`
(both finite-state and `SpaceLE`).
-/

public section

namespace CslibFrontier.Computability.BranchingProgram

universe u u' v v' w

section CoreDefs

/-- Auxiliary recursive prefix evaluation of a layered transition system with vertex layers
`V : Fin (n + 1) → Type w`, initial state `start : V 0`, and transitions `step`. -/
@[expose] def layeredROBPEvalPrefixAux {n : ℕ} {Alph : Type u} {V : Fin (n + 1) → Type w}
    (start : V 0) (step : ∀ i : Fin n, V i.castSucc → Alph → V i.succ) :
    (k : ℕ) → (hk : k ≤ n) → (Fin k → Alph) → V ⟨k, Nat.lt_succ_of_le hk⟩
  | 0, _, _ => start
  | k + 1, hk, x =>
    step ⟨k, hk⟩
      (layeredROBPEvalPrefixAux start step k (Nat.le_of_succ_le hk) (fun i ↦ x i.castSucc))
      (x (Fin.last k))

/-- Base equation for `layeredROBPEvalPrefixAux` at prefix length `0`. -/
@[simp]
lemma layeredROBPEvalPrefixAux_zero {n : ℕ} {Alph : Type u} {V : Fin (n + 1) → Type w}
    (start : V 0) (step : ∀ i : Fin n, V i.castSucc → Alph → V i.succ)
    (h0 : 0 ≤ n) (x : Fin 0 → Alph) :
    layeredROBPEvalPrefixAux start step 0 h0 x = start := rfl

/-- Step equation for `layeredROBPEvalPrefixAux` at prefix length `k + 1`. -/
@[simp]
lemma layeredROBPEvalPrefixAux_succ {n : ℕ} {Alph : Type u} {V : Fin (n + 1) → Type w}
    (start : V 0) (step : ∀ i : Fin n, V i.castSucc → Alph → V i.succ)
    (k : ℕ) (hk : k + 1 ≤ n) (x : Fin (k + 1) → Alph) :
    layeredROBPEvalPrefixAux start step (k + 1) hk x =
      step ⟨k, hk⟩
        (layeredROBPEvalPrefixAux start step k (Nat.le_of_succ_le hk) (fun i ↦ x i.castSucc))
        (x (Fin.last k)) := rfl

/-- A deterministic length-`n` read-once branching program (LayeredROBP) over input alphabet `Alph`
with
outputs in `Z`, consisting of finite vertex layers `V 0, ..., V n`, a unique start state
`start : V 0`, single-step transitions `step`, terminal outputs `output`, and reachability of every
vertex in every layer. -/
structure LayeredROBP (n : ℕ) (Alph : Type u) (Z : Type v) where
  /-- Vertex sets `V t` for each layer `t : Fin (n + 1)`. -/
  V : Fin (n + 1) → Type w
  /-- Finiteness of each layer `V t`. -/
  instFintypeV : ∀ t : Fin (n + 1), Fintype (V t)
  /-- Unique start vertex in layer `V 0`. -/
  start : V 0
  /-- Every vertex in `V 0` equals `start`. -/
  eq_start : ∀ v : V 0, v = start
  /-- Deterministic edge transition from layer `i` to layer `i + 1` labeled by `Alph`. -/
  step : ∀ i : Fin n, V i.castSucc → Alph → V i.succ
  /-- Terminal output label on layer `V (Fin.last n)`. -/
  output : V (Fin.last n) → Z
  /-- Every vertex in every layer is reachable by some prefix input. -/
  reachable : ∀ (t : Fin (n + 1)) (v : V t),
    ∃ x : Fin t.1 → Alph, layeredROBPEvalPrefixAux start step t.1 (Nat.lt_succ_iff.mp t.2) x = v

instance LayeredROBP.instFintypeLayer {n : ℕ} {Alph : Type u} {Z : Type v}
    (P : LayeredROBP.{u, v, w} n Alph Z) (t : Fin (n + 1)) : Fintype (P.V t) :=
  P.instFintypeV t

end CoreDefs

namespace LayeredROBP

section Evaluation

variable {n : ℕ} {Alph : Type u} {Z : Type v} (P : LayeredROBP.{u, v, w} n Alph Z)

/-- Vertex in layer `V t` reached by `P` on a prefix input `x : Fin t.1 → Alph`. -/
def evalPrefix (t : Fin (n + 1)) (x : Fin t.1 → Alph) : P.V t :=
  layeredROBPEvalPrefixAux P.start P.step t.1 (Nat.lt_succ_iff.mp t.2) x

/-- Every vertex in every layer `t` is reachable by `P.evalPrefix t`. -/
theorem evalPrefix_reachable (t : Fin (n + 1)) (v : P.V t) :
    ∃ x : Fin t.1 → Alph, P.evalPrefix t x = v :=
  P.reachable t v

/-- Evaluating `P` on the empty prefix at layer `0` yields `P.start`. -/
@[simp, grind =]
lemma evalPrefix_zero (x : Fin (0 : Fin (n + 1)).1 → Alph) :
    P.evalPrefix 0 x = P.start :=
  P.eq_start _

/-- Right-step recurrence for `LayeredROBP.evalPrefix` at layer `k + 1`. -/
lemma evalPrefix_step_right {k : ℕ} (hk : k < n) (x : Fin (k + 1) → Alph) :
    P.evalPrefix ⟨k + 1, Nat.succ_lt_succ hk⟩ x =
      P.step ⟨k, hk⟩
        (P.evalPrefix ⟨k, Nat.lt_succ_of_lt hk⟩ (fun i ↦ x i.castSucc))
        (x (Fin.last k)) := by
  rfl

/-- Vertex in layer `m ≤ n` reached by `P` on the `m`-letter prefix of a full input
`x : Fin n → Alph`. -/
def evalPrefixOn {m : ℕ} (hm : m ≤ n) (x : Fin n → Alph) : P.V ⟨m, Nat.lt_succ_of_le hm⟩ :=
  P.evalPrefix ⟨m, Nat.lt_succ_of_le hm⟩ (fun i ↦ x ⟨i.1, lt_of_lt_of_le i.2 hm⟩)

/-- Evaluating `P.evalPrefixOn` at prefix length `0` yields `P.start`. -/
@[simp, grind =]
lemma evalPrefixOn_zero (h0 : 0 ≤ n) (x : Fin n → Alph) :
    P.evalPrefixOn h0 x = P.start := by
  rfl

/-- Step recurrence for `LayeredROBP.evalPrefixOn` at prefix length `m + 1 ≤ n`. -/
@[simp, grind =]
lemma evalPrefixOn_succ {m : ℕ} (hm : m + 1 ≤ n) (x : Fin n → Alph) :
    P.evalPrefixOn hm x =
      P.step ⟨m, hm⟩ (P.evalPrefixOn (Nat.le_of_succ_le hm) x) (x ⟨m, hm⟩) := by
  rfl

/-- Congruence of `LayeredROBP.evalPrefixOn`: inputs agreeing on the first `m` coordinates reach the
same
vertex in layer `m`. -/
lemma evalPrefixOn_congr {m : ℕ} (hm : m ≤ n) {x y : Fin n → Alph}
    (hxy : ∀ i : Fin m, x ⟨i.1, lt_of_lt_of_le i.2 hm⟩ = y ⟨i.1, lt_of_lt_of_le i.2 hm⟩) :
    P.evalPrefixOn hm x = P.evalPrefixOn hm y := by
  unfold evalPrefixOn
  congr 1
  ext i
  exact hxy i

/-- Terminal vertex in `V (Fin.last n)` reached by `P` on full input `x : Fin n → Alph`. -/
def eval (x : Fin n → Alph) : P.V (Fin.last n) :=
  P.evalPrefix (Fin.last n) x

/-- Evaluating `P.evalPrefixOn` on all `n` coordinates agrees with `P.eval`. -/
@[simp, grind =]
lemma evalPrefixOn_last (x : Fin n → Alph) : P.evalPrefixOn le_rfl x = P.eval x := by
  rfl

/-- Evaluating `P.eval x` equals `P.evalPrefix (Fin.last n) x`. -/
lemma eval_eq_evalPrefix_last (x : Fin n → Alph) :
    P.eval x = P.evalPrefix (Fin.last n) x := by
  rfl

/-- Output in `Z` produced by `P` on full input `x : Fin n → Alph`. -/
def run (x : Fin n → Alph) : Z :=
  P.output (P.eval x)

/-- Evaluation formula for `LayeredROBP.run` via `P.output` and `P.eval`. -/
@[grind =]
lemma run_eq (x : Fin n → Alph) : P.run x = P.output (P.eval x) := by
  rfl

/-- Width of `P`, defined as the maximum layer cardinality `max_{0 ≤ t ≤ n} |V t|`. -/
def width : ℕ :=
  Finset.univ.sup fun t : Fin (n + 1) ↦ Fintype.card (P.V t)

/-- Width characterization via the supremum over layers. -/
lemma width_eq_sup :
    P.width = Finset.univ.sup fun t : Fin (n + 1) ↦ Fintype.card (P.V t) := by
  rfl

/-- Upper-bound characterization of `P.width`. -/
lemma width_le_iff {m : ℕ} : P.width ≤ m ↔ ∀ t : Fin (n + 1), Fintype.card (P.V t) ≤ m := by
  simp [width]

/-- An LayeredROBP `P` computes a function `f : (Fin n → Alph) → Z` if `P.run x = f x` for all `x`.
-/
def Computes (f : (Fin n → Alph) → Z) : Prop :=
  ∀ x, P.run x = f x

/-- Pointwise characterization of `LayeredROBP.Computes`. -/
@[grind =]
lemma computes_iff {f : (Fin n → Alph) → Z} : P.Computes f ↔ ∀ x, P.run x = f x := Iff.rfl

/-- An LayeredROBP `P` computes an input-output relation `R : (Fin n → Alph) → Z → Prop` if
`R x (P.run x)` holds for every input `x`. -/
def ComputesRel (R : (Fin n → Alph) → Z → Prop) : Prop :=
  ∀ x, R x (P.run x)

/-- Pointwise characterization of `LayeredROBP.ComputesRel`. -/
@[grind =]
lemma computesRel_iff {R : (Fin n → Alph) → Z → Prop} :
    P.ComputesRel R ↔ ∀ x, R x (P.run x) := Iff.rfl

/-- Every layer `P.V t` has cardinality at most `P.width`. -/
lemma card_layer_le_width (t : Fin (n + 1)) : Fintype.card (P.V t) ≤ P.width :=
  Finset.le_sup (f := fun s : Fin (n + 1) ↦ Fintype.card (P.V s)) (Finset.mem_univ t)

/-- The initial layer `P.V 0` has cardinality `1`. -/
@[simp]
lemma card_V_zero : Fintype.card (P.V 0) = 1 :=
  Fintype.card_eq_one_iff.mpr ⟨P.start, P.eq_start⟩

/-- Every LayeredROBP has width at least `1`. -/
lemma one_le_width : 1 ≤ P.width :=
  P.card_V_zero ▸ P.card_layer_le_width 0

/-- The terminal layer `P.V (Fin.last n)` has cardinality at most `P.width`. -/
lemma card_last_le_width : Fintype.card (P.V (Fin.last n)) ≤ P.width :=
  P.card_layer_le_width (Fin.last n)

/-- Over a nonempty alphabet `Alph`, every layer `P.V t` of `P` is nonempty. -/
lemma layerNonempty [Nonempty Alph] (t : Fin (n + 1)) : Nonempty (P.V t) :=
  ⟨P.evalPrefix t (fun _ ↦ Classical.arbitrary Alph)⟩

/-- Over a finite alphabet `Alph` and decidable output type `Z`, the image of `P.run` has
cardinality at most `P.width`. -/
theorem card_image_run_le_width [Fintype Alph] [DecidableEq Z] :
    (Finset.univ.image P.run).card ≤ P.width := by
  have hsub :
      Finset.univ.image P.run ⊆ (Finset.univ : Finset (P.V (Fin.last n))).image P.output := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨x, _, rfl⟩
    exact Finset.mem_image.mpr ⟨P.eval x, Finset.mem_univ _, (P.run_eq x).symm⟩
  calc
    (Finset.univ.image P.run).card
      ≤ ((Finset.univ : Finset (P.V (Fin.last n))).image P.output).card :=
        Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset (P.V (Fin.last n))).card := Finset.card_image_le
    _ = Fintype.card (P.V (Fin.last n)) := Finset.card_univ
    _ ≤ P.width := P.card_last_le_width

/-- Over a nonempty alphabet `Alph`, any prefix input `x : Fin m → Alph` with `m ≤ n` extends to a
full input `y : Fin n → Alph` agreeing with `x` on the first `m` coordinates and reaching the same
layer-`m` vertex. -/
lemma exists_input_extends_prefix [Nonempty Alph] {m : ℕ} (hm : m ≤ n) (x : Fin m → Alph) :
    ∃ y : Fin n → Alph,
      (∀ i : Fin m, y ⟨i.1, lt_of_lt_of_le i.2 hm⟩ = x i) ∧
        P.evalPrefixOn hm y = P.evalPrefix ⟨m, Nat.lt_succ_of_le hm⟩ x := by
  classical
  let a : Alph := Classical.arbitrary Alph
  let y : Fin n → Alph := fun j ↦ if hj : j.1 < m then x ⟨j.1, hj⟩ else a
  refine ⟨y, fun i ↦ by simp [y, i.2], ?_⟩
  unfold evalPrefixOn
  congr 1
  ext i
  simp [y, i.2]

/-- Over a nonempty alphabet `Alph`, any prefix input `x : Fin m → Alph` with `m ≤ n` extends to a
full input `y : Fin n → Alph` whose `evalPrefixOn hm y` equals
`P.evalPrefix ⟨m, Nat.lt_succ_of_le hm⟩ x`. -/
theorem exists_input_evalPrefixOn_eq [Nonempty Alph] {m : ℕ} (hm : m ≤ n) (x : Fin m → Alph) :
    ∃ y : Fin n → Alph, P.evalPrefixOn hm y = P.evalPrefix ⟨m, Nat.lt_succ_of_le hm⟩ x := by
  obtain ⟨y, _, hy⟩ := P.exists_input_extends_prefix hm x
  exact ⟨y, hy⟩

/-- Over a nonempty alphabet `Alph`, every vertex in layer `t` is reached by `evalPrefixOn` on some
full input `y : Fin n → Alph`. -/
lemma exists_input_evalPrefixOn_eq_vertex [Nonempty Alph] (t : Fin (n + 1)) (v : P.V t) :
    ∃ y : Fin n → Alph, P.evalPrefixOn (Nat.lt_succ_iff.mp t.2) y = v := by
  obtain ⟨x, hx⟩ := P.evalPrefix_reachable t v
  obtain ⟨y, hy⟩ := P.exists_input_evalPrefixOn_eq (Nat.lt_succ_iff.mp t.2) x
  exact ⟨y, hy.trans hx⟩

end Evaluation

end LayeredROBP

section Combinators

private lemma layeredROBPEvalPrefixAux_val_eq {n : ℕ} {Alph : Type u}
    {U V : Fin (n + 1) → Type w} (val : ∀ t, V t → U t)
    (startU : U 0) (stepU : ∀ i : Fin n, U i.castSucc → Alph → U i.succ)
    (startV : V 0) (stepV : ∀ i : Fin n, V i.castSucc → Alph → V i.succ)
    (h0 : val 0 startV = startU)
    (hstep : ∀ i v a, val i.succ (stepV i v a) = stepU i (val i.castSucc v) a) :
    ∀ (k : ℕ) (hk : k ≤ n) (x : Fin k → Alph),
      val ⟨k, Nat.lt_succ_of_le hk⟩ (layeredROBPEvalPrefixAux startV stepV k hk x) =
        layeredROBPEvalPrefixAux startU stepU k hk x := by
  intro k
  induction k with
  | zero =>
    intro hk x
    rw [layeredROBPEvalPrefixAux_zero, layeredROBPEvalPrefixAux_zero]
    simpa using h0
  | succ k ih =>
    intro hk x
    rw [layeredROBPEvalPrefixAux_succ, layeredROBPEvalPrefixAux_succ]
    have hs := hstep ⟨k, hk⟩
      (layeredROBPEvalPrefixAux startV stepV k (Nat.le_of_succ_le hk) (fun i ↦ x i.castSucc))
      (x (Fin.last k))
    have ih' := ih (Nat.le_of_succ_le hk) (fun i ↦ x i.castSucc)
    change val (⟨k, hk⟩ : Fin n).castSucc _ = _ at ih'
    change val (⟨k, hk⟩ : Fin n).succ _ = _
    rw [hs, ih']

private lemma layeredROBPEvalPrefixAux_step_reachable {n : ℕ} {Alph : Type u}
    {U : Fin (n + 1) → Type w}
    (start : U 0) (step : ∀ i : Fin n, U i.castSucc → Alph → U i.succ)
    (i : Fin n)
    (v : {u : U i.castSucc // ∃ x : Fin i.castSucc.1 → Alph,
      layeredROBPEvalPrefixAux start step i.castSucc.1 (Nat.lt_succ_iff.mp i.castSucc.2) x = u})
    (a : Alph) :
    ∃ y : Fin i.succ.1 → Alph,
      layeredROBPEvalPrefixAux start step i.succ.1 (Nat.lt_succ_iff.mp i.succ.2) y =
        step i v.1 a := by
  rcases v with ⟨u, x, hx⟩
  have hcast : i.castSucc.1 = i.1 := Fin.val_castSucc i
  have hsucc : i.succ.1 = i.1 + 1 := Fin.val_succ i
  let x' : Fin i.1 → Alph := fun j ↦ x (Fin.cast hcast.symm j)
  let y' : Fin (i.1 + 1) → Alph := Fin.snoc (α := fun _ ↦ Alph) x' a
  refine ⟨fun j ↦ y' (Fin.cast hsucc j), ?_⟩
  have heq :
      layeredROBPEvalPrefixAux start step i.succ.1 (Nat.lt_succ_iff.mp i.succ.2)
          (fun j ↦ y' (Fin.cast hsucc j)) =
        layeredROBPEvalPrefixAux start step (i.1 + 1) (Nat.succ_le_of_lt i.2) y' := by
    cases hsucc
    rfl
  rw [heq, layeredROBPEvalPrefixAux_succ]
  have hpref : (fun j : Fin i.1 ↦ y' j.castSucc) = x' := by
    ext j
    simp [y']
  have hlast : y' (Fin.last i.1) = a := by simp [y']
  rw [hpref, hlast]
  have hsub :
      layeredROBPEvalPrefixAux start step i.1 (Nat.le_of_succ_le (Nat.succ_le_of_lt i.2)) x' =
        u := by
    have h1 :
        layeredROBPEvalPrefixAux start step i.1 (Nat.le_of_succ_le (Nat.succ_le_of_lt i.2)) x' =
          layeredROBPEvalPrefixAux start step i.castSucc.1 (Nat.lt_succ_iff.mp i.castSucc.2) x := by
      cases hcast
      rfl
    exact h1.trans hx
  rw [hsub]

private lemma layeredROBPEvalPrefixAux_zero_reachable {n : ℕ} {Alph : Type u}
    {U : Fin (n + 1) → Type w}
    (start : U 0) (step : ∀ i : Fin n, U i.castSucc → Alph → U i.succ) :
    ∃ x : Fin (0 : Fin (n + 1)).1 → Alph,
      layeredROBPEvalPrefixAux start step (0 : Fin (n + 1)).1
        (Nat.lt_succ_iff.mp (0 : Fin (n + 1)).2) x = start := by
  have h0 : ∀ (k : ℕ) (hk : k ≤ n) (hk0 : k = 0) (x : Fin k → Alph),
      HEq (layeredROBPEvalPrefixAux start step k hk x) start := by
    rintro k hk rfl x
    rw [layeredROBPEvalPrefixAux_zero]
    rfl
  exact ⟨fun i ↦ Fin.elim0 (Fin.cast (Fin.val_zero _) i), eq_of_heq (h0 _ _ (Fin.val_zero _) _)⟩

/-- Construct an `LayeredROBP` from any finite layered transition system `(U, start, step, output)`
by
pruning each layer `t` to the subtype of vertices reachable from `start`. -/
@[expose] noncomputable def LayeredROBP.ofLayeredSystem {n : ℕ} {Alph : Type u} {Z : Type v}
    (U : Fin (n + 1) → Type w) [∀ t, Fintype (U t)]
    (start : U 0) (step : ∀ i : Fin n, U i.castSucc → Alph → U i.succ)
    (output : U (Fin.last n) → Z) : LayeredROBP.{u, v, w} n Alph Z where
  V t :=
    {u : U t //
      ∃ x : Fin t.1 → Alph, layeredROBPEvalPrefixAux start step t.1 (Nat.lt_succ_iff.mp t.2) x = u}
  instFintypeV _ := by
    classical
    exact inferInstance
  start := ⟨start, by exact layeredROBPEvalPrefixAux_zero_reachable start step⟩
  eq_start v := by
    rcases v with ⟨u, x, hx⟩
    have hx' : layeredROBPEvalPrefixAux start step 0 (Nat.zero_le n) x = start :=
      layeredROBPEvalPrefixAux_zero start step (Nat.zero_le n) x
    exact Subtype.ext (hx'.symm.trans hx).symm
  step i v a := ⟨step i v.1 a, by exact layeredROBPEvalPrefixAux_step_reachable start step i v a⟩
  output v := output v.1
  reachable t v := by
    rcases v with ⟨u, x, hx⟩
    refine ⟨x, Subtype.ext ?_⟩
    have heval := layeredROBPEvalPrefixAux_val_eq (n := n)
      (fun (t : Fin (n + 1)) (v : {u : U t //
        ∃ x : Fin t.1 →
          Alph, layeredROBPEvalPrefixAux start step t.1 (Nat.lt_succ_iff.mp t.2) x = u}) ↦
          v.1)
      start step ⟨start, layeredROBPEvalPrefixAux_zero_reachable start step⟩
      (fun i v a ↦ ⟨step i v.1 a, layeredROBPEvalPrefixAux_step_reachable start step i v a⟩)
      rfl (fun _ _ _ ↦ rfl) t.1 (Nat.lt_succ_iff.mp t.2) x
    exact heval.trans hx

/-- Underlying state reached in `U t` by `LayeredROBP.ofLayeredSystem`. -/
lemma LayeredROBP.ofLayeredSystem_evalPrefix_val {n : ℕ} {Alph : Type u} {Z : Type v}
    (U : Fin (n + 1) → Type w) [∀ t, Fintype (U t)]
    (start : U 0) (step : ∀ i : Fin n, U i.castSucc → Alph → U i.succ)
    (output : U (Fin.last n) → Z) (t : Fin (n + 1)) (x : Fin t.1 → Alph) :
    ((LayeredROBP.ofLayeredSystem U start step output).evalPrefix t x).1 =
      layeredROBPEvalPrefixAux start step t.1 (Nat.lt_succ_iff.mp t.2) x :=
  layeredROBPEvalPrefixAux_val_eq (n := n)
    (fun (t : Fin (n + 1)) (v : (LayeredROBP.ofLayeredSystem U start step output).V t) ↦ v.1)
    start step (LayeredROBP.ofLayeredSystem U start step output).start
    (LayeredROBP.ofLayeredSystem U start step output).step rfl (fun _ _ _ ↦ rfl)
    t.1 (Nat.lt_succ_iff.mp t.2) x

/-- Output of `LayeredROBP.ofLayeredSystem` on `x : Fin n → Alph` matches evaluating the underlying
layered
system directly via `layeredROBPEvalPrefixAux`. -/
@[simp, grind =]
theorem LayeredROBP.ofLayeredSystem_run {n : ℕ} {Alph : Type u} {Z : Type v}
    (U : Fin (n + 1) → Type w) [∀ t, Fintype (U t)]
    (start : U 0) (step : ∀ i : Fin n, U i.castSucc → Alph → U i.succ)
    (output : U (Fin.last n) → Z) (x : Fin n → Alph) :
    (LayeredROBP.ofLayeredSystem U start step output).run x =
      output (layeredROBPEvalPrefixAux start step n le_rfl x) := by
  rw [LayeredROBP.run_eq, LayeredROBP.eval_eq_evalPrefix_last]
  change output ((LayeredROBP.ofLayeredSystem U start step output).evalPrefix (Fin.last n) x).1 = _
  rw [LayeredROBP.ofLayeredSystem_evalPrefix_val]
  rfl

/-- Pruning to reachable vertices never increases the cardinality of any layer `t`. -/
lemma LayeredROBP.ofLayeredSystem_layerCard_le {n : ℕ} {Alph : Type u} {Z : Type v}
    (U : Fin (n + 1) → Type w) [∀ t, Fintype (U t)]
    (start : U 0) (step : ∀ i : Fin n, U i.castSucc → Alph → U i.succ)
    (output : U (Fin.last n) → Z) (t : Fin (n + 1)) :
    Fintype.card ((LayeredROBP.ofLayeredSystem U start step output).V t) ≤ Fintype.card (U t) :=
  Fintype.card_le_of_injective
    (fun v : (LayeredROBP.ofLayeredSystem U start step output).V t ↦ v.1)
    Subtype.coe_injective

/-- The width of `LayeredROBP.ofLayeredSystem` is bounded by the supremum of layer cardinalities of
`U`. -/
theorem LayeredROBP.ofLayeredSystem_width_le {n : ℕ} {Alph : Type u} {Z : Type v}
    (U : Fin (n + 1) → Type w) [∀ t, Fintype (U t)]
    (start : U 0) (step : ∀ i : Fin n, U i.castSucc → Alph → U i.succ)
    (output : U (Fin.last n) → Z) :
    (LayeredROBP.ofLayeredSystem U start step output).width ≤
      Finset.univ.sup fun t ↦ Fintype.card (U t) := by
  rw [LayeredROBP.width_le_iff]
  intro t
  exact (LayeredROBP.ofLayeredSystem_layerCard_le U start step output t).trans
    (Finset.le_sup (f := fun s : Fin (n + 1) ↦ Fintype.card (U s)) (Finset.mem_univ t))

private lemma layeredROBPEvalPrefixAux_reindex {n : ℕ} {Alph : Type u} {Z : Type v}
    (P : LayeredROBP.{u, v, w} n Alph Z) :
    ∀ (k : ℕ) (hk : k ≤ n) (x : Fin k → Alph),
      layeredROBPEvalPrefixAux (V := fun t ↦ Fin (Fintype.card (P.V t)))
          (Fintype.equivFin (P.V 0) P.start)
          (fun i v a ↦ Fintype.equivFin (P.V i.succ)
            (P.step i ((Fintype.equivFin (P.V i.castSucc)).symm v) a))
          k hk x =
        Fintype.equivFin (P.V ⟨k, Nat.lt_succ_of_le hk⟩)
          (layeredROBPEvalPrefixAux P.start P.step k hk x) := by
  intro k
  induction k with
  | zero =>
    intro hk x
    rw [layeredROBPEvalPrefixAux_zero, layeredROBPEvalPrefixAux_zero]
    rfl
  | succ k ih =>
    intro hk x
    rw [layeredROBPEvalPrefixAux_succ, layeredROBPEvalPrefixAux_succ]
    have ih' := ih (Nat.le_of_succ_le hk) (fun i ↦ x i.castSucc)
    change layeredROBPEvalPrefixAux (V := fun t ↦ Fin (Fintype.card (P.V t)))
        (Fintype.equivFin (P.V 0) P.start)
        (fun i v a ↦ Fintype.equivFin (P.V i.succ)
          (P.step i ((Fintype.equivFin (P.V i.castSucc)).symm v) a))
        k (Nat.le_of_succ_le hk) (fun i ↦ x i.castSucc) =
      Fintype.equivFin (P.V (⟨k, hk⟩ : Fin n).castSucc)
        (layeredROBPEvalPrefixAux P.start P.step k (Nat.le_of_succ_le hk)
          (fun i ↦ x i.castSucc)) at ih'
    rw [ih', Equiv.symm_apply_apply]
    rfl

/-- Canonical reindexing of an `LayeredROBP` replacing each vertex layer `P.V t` by the universe-`0`
finite type `Fin (Fintype.card (P.V t))` via `Fintype.equivFin`. -/
noncomputable def LayeredROBP.reindex {n : ℕ} {Alph : Type u} {Z : Type v}
    (P : LayeredROBP.{u, v, w} n Alph Z) : LayeredROBP.{u, v, 0} n Alph Z where
  V t := Fin (Fintype.card (P.V t))
  instFintypeV _ := inferInstance
  start := Fintype.equivFin (P.V 0) P.start
  eq_start v := by
    have hv : (Fintype.equivFin (P.V 0)).symm v = P.start := P.eq_start _
    simpa [hv] using ((Fintype.equivFin (P.V 0)).apply_symm_apply v).symm
  step i v a :=
    Fintype.equivFin (P.V i.succ) (P.step i ((Fintype.equivFin (P.V i.castSucc)).symm v) a)
  output v := P.output ((Fintype.equivFin (P.V (Fin.last n))).symm v)
  reachable t v := by
    obtain ⟨x, hx⟩ := P.reachable t ((Fintype.equivFin (P.V t)).symm v)
    refine ⟨x, ?_⟩
    rw [layeredROBPEvalPrefixAux_reindex P t.1 (Nat.lt_succ_iff.mp t.2) x, hx]
    exact (Fintype.equivFin (P.V t)).apply_symm_apply v

/-- Reindexing an LayeredROBP preserves its output on every input `x : Fin n → Alph`. -/
@[simp, grind =]
theorem LayeredROBP.reindex_run {n : ℕ} {Alph : Type u} {Z : Type v}
    (P : LayeredROBP.{u, v, w} n Alph Z) (x : Fin n → Alph) :
    P.reindex.run x = P.run x := by
  rw [LayeredROBP.run_eq, LayeredROBP.run_eq, LayeredROBP.eval_eq_evalPrefix_last,
    LayeredROBP.eval_eq_evalPrefix_last]
  change P.output ((Fintype.equivFin (P.V (Fin.last n))).symm
    (layeredROBPEvalPrefixAux (V := fun t ↦ Fin (Fintype.card (P.V t)))
      (Fintype.equivFin (P.V 0) P.start)
      (fun i v a ↦ Fintype.equivFin (P.V i.succ)
        (P.step i ((Fintype.equivFin (P.V i.castSucc)).symm v) a))
      n le_rfl x)) = _
  rw [layeredROBPEvalPrefixAux_reindex P n le_rfl x]
  change P.output ((Fintype.equivFin (P.V (Fin.last n))).symm
    ((Fintype.equivFin (P.V (Fin.last n))) (layeredROBPEvalPrefixAux P.start P.step n le_rfl x))) =
      _
  simp [LayeredROBP.evalPrefix]

/-- Reindexing an LayeredROBP preserves its width. -/
@[simp, grind =]
theorem LayeredROBP.reindex_width {n : ℕ} {Alph : Type u} {Z : Type v}
    (P : LayeredROBP.{u, v, w} n Alph Z) :
    P.reindex.width = P.width := by
  rw [LayeredROBP.width_eq_sup, LayeredROBP.width_eq_sup]
  refine Finset.sup_congr rfl fun t _ ↦ ?_
  change Fintype.card (Fin (Fintype.card (P.V t))) = Fintype.card (P.V t)
  exact Fintype.card_fin _

/-- Reindexing an LayeredROBP preserves function computation. -/
@[simp, grind =]
theorem LayeredROBP.reindex_computes_iff {n : ℕ} {Alph : Type u} {Z : Type v}
    (P : LayeredROBP.{u, v, w} n Alph Z) {f : (Fin n → Alph) → Z} :
    P.reindex.Computes f ↔ P.Computes f := by
  simp only [LayeredROBP.computes_iff, LayeredROBP.reindex_run]

/-- Reindexing an LayeredROBP preserves relation computation. -/
@[simp, grind =]
theorem LayeredROBP.reindex_computesRel_iff {n : ℕ} {Alph : Type u} {Z : Type v}
    (P : LayeredROBP.{u, v, w} n Alph Z) {R : (Fin n → Alph) → Z → Prop} :
    P.reindex.ComputesRel R ↔ P.ComputesRel R := by
  simp only [LayeredROBP.computesRel_iff, LayeredROBP.reindex_run]

/-- Post-compose the terminal outputs of an LayeredROBP `P` with a map `g : Z → Z'`. -/
@[expose] def LayeredROBP.mapOutput {n : ℕ} {Alph : Type u} {Z : Type v} {Z' : Type v'}
    (P : LayeredROBP.{u, v, w} n Alph Z) (g : Z → Z') : LayeredROBP.{u, v', w} n Alph Z' where
  V := P.V
  instFintypeV := P.instFintypeV
  start := P.start
  eq_start := P.eq_start
  step := P.step
  output v := g (P.output v)
  reachable := P.reachable

/-- Vertex layers of `P.mapOutput g` agree with `P.V`. -/
@[simp]
lemma LayeredROBP.mapOutput_V {n : ℕ} {Alph : Type u} {Z : Type v} {Z' : Type v'}
    (P : LayeredROBP.{u, v, w} n Alph Z) (g : Z → Z') (t : Fin (n + 1)) :
    (P.mapOutput g).V t = P.V t := rfl

/-- Terminal vertex reached by `P.mapOutput g` agrees with `P.eval`. -/
@[simp, grind =]
lemma LayeredROBP.mapOutput_eval {n : ℕ} {Alph : Type u} {Z : Type v} {Z' : Type v'}
    (P : LayeredROBP.{u, v, w} n Alph Z) (g : Z → Z') (x : Fin n → Alph) :
    (P.mapOutput g).eval x = P.eval x := by
  rfl

/-- Executing `P.mapOutput g` on `x` applies `g` to `P.run x`. -/
@[simp, grind =]
theorem LayeredROBP.mapOutput_run {n : ℕ} {Alph : Type u} {Z : Type v} {Z' : Type v'}
    (P : LayeredROBP.{u, v, w} n Alph Z) (g : Z → Z') (x : Fin n → Alph) :
    (P.mapOutput g).run x = g (P.run x) := by
  rfl

/-- Post-composing outputs preserves the width of an LayeredROBP. -/
@[simp, grind =]
theorem LayeredROBP.mapOutput_width {n : ℕ} {Alph : Type u} {Z : Type v} {Z' : Type v'}
    (P : LayeredROBP.{u, v, w} n Alph Z) (g : Z → Z') :
    (P.mapOutput g).width = P.width := by
  rfl

/-- Pull back an LayeredROBP `P` along an alphabet map `ι : Alph' → Alph`, pruning layers to
reachable
vertices over `Alph'`. -/
noncomputable def LayeredROBP.comap {n : ℕ} {Alph : Type u} {Alph' : Type u'} {Z : Type v}
    (P : LayeredROBP.{u, v, w} n Alph Z) (ι : Alph' → Alph) : LayeredROBP.{u', v, w} n Alph' Z :=
  LayeredROBP.ofLayeredSystem P.V P.start (fun i v a ↦ P.step i v (ι a)) P.output

private lemma layeredROBPEvalPrefixAux_comap {n : ℕ} {Alph : Type u} {Alph' : Type u'} {Z : Type v}
    (P : LayeredROBP.{u, v, w} n Alph Z) (ι : Alph' → Alph) :
    ∀ (k : ℕ) (hk : k ≤ n) (x : Fin k → Alph'),
      layeredROBPEvalPrefixAux P.start (fun i v a ↦ P.step i v (ι a)) k hk x =
        layeredROBPEvalPrefixAux P.start P.step k hk (ι ∘ x) := by
  intro k
  induction k with
  | zero =>
    intro hk x
    rfl
  | succ k ih =>
    intro hk x
    rw [layeredROBPEvalPrefixAux_succ, layeredROBPEvalPrefixAux_succ, ih (Nat.le_of_succ_le hk)]
    rfl

/-- Executing `P.comap ι` on `x : Fin n → Alph'` equals executing `P` on `ι ∘ x`. -/
@[simp, grind =]
theorem LayeredROBP.comap_run {n : ℕ} {Alph : Type u} {Alph' : Type u'} {Z : Type v}
    (P : LayeredROBP.{u, v, w} n Alph Z) (ι : Alph' → Alph) (x : Fin n → Alph') :
    (P.comap ι).run x = P.run (ι ∘ x) := by
  unfold LayeredROBP.comap
  rw [LayeredROBP.ofLayeredSystem_run, layeredROBPEvalPrefixAux_comap, LayeredROBP.run_eq,
    LayeredROBP.eval_eq_evalPrefix_last]
  rfl

/-- Pulling back along `ι : Alph' → Alph` cannot increase the width of an LayeredROBP. -/
theorem LayeredROBP.comap_width_le {n : ℕ} {Alph : Type u} {Alph' : Type u'} {Z : Type v}
    (P : LayeredROBP.{u, v, w} n Alph Z) (ι : Alph' → Alph) :
    (P.comap ι).width ≤ P.width := by
  unfold LayeredROBP.comap
  exact (LayeredROBP.ofLayeredSystem_width_le P.V P.start
    (fun i v a ↦ P.step i v (ι a)) P.output).trans_eq P.width_eq_sup.symm

end Combinators

section StreamingBridge

private lemma layeredROBPEvalPrefixAux_foldl_eq {n : ℕ} {Alph : Type u} {S : Type w}
    (s0 : S) (stepS : S → Alph → S) :
    ∀ (k : ℕ) (hk : k ≤ n) (x : Fin k → Alph),
      layeredROBPEvalPrefixAux (V := fun _ : Fin (n + 1) ↦ S) s0 (fun _ s a ↦ stepS s a) k hk x =
        (List.ofFn x).foldl stepS s0 := by
  intro k
  induction k with
  | zero =>
    intro hk x
    simp
  | succ k ih =>
    intro hk x
    rw [layeredROBPEvalPrefixAux_succ, ih (Nat.le_of_succ_le hk),
      List.ofFn_succ', List.concat_eq_append, List.foldl_append]
    rfl

/-- Canonical length-`n` LayeredROBP induced by a finite-state single-pass
`Cslib.Streaming.Algorithm`
over token alphabet `Alph`, obtained by restricting each layer `t` to states reachable in `t`
steps. -/
@[expose] noncomputable def streamingToLayeredROBP {Alph : Type u} {Z : Type v} {S : Type w}
    [Fintype S] (A : Cslib.Streaming.Algorithm S Alph Z) (n : ℕ) : LayeredROBP.{u, v, w} n Alph Z :=
  LayeredROBP.ofLayeredSystem (fun _ : Fin (n + 1) ↦ S) A.init (fun _ s a ↦ A.update s a) A.output

/-- Running `streamingToLayeredROBP A n` on `x : Fin n → Alph` matches `A.run (List.ofFn x)`. -/
@[simp, grind =]
theorem streamingToLayeredROBP_run {Alph : Type u} {Z : Type v} {S : Type w} [Fintype S]
    (A : Cslib.Streaming.Algorithm S Alph Z) (n : ℕ) (x : Fin n → Alph) :
    (streamingToLayeredROBP A n).run x = A.run (List.ofFn x) := by
  unfold streamingToLayeredROBP
  rw [LayeredROBP.ofLayeredSystem_run, layeredROBPEvalPrefixAux_foldl_eq]
  rfl

/-- The layer-`t` underlying state of `streamingToLayeredROBP A n` equals `A.state (List.ofFn x)`.
-/
lemma streamingToLayeredROBP_evalPrefix_val {Alph : Type u} {Z : Type v} {S : Type w} [Fintype S]
    (A : Cslib.Streaming.Algorithm S Alph Z) (n : ℕ) (t : Fin (n + 1)) (x : Fin t.1 → Alph) :
    ((streamingToLayeredROBP A n).evalPrefix t x).1 = A.state (List.ofFn x) := by
  unfold streamingToLayeredROBP
  rw [LayeredROBP.ofLayeredSystem_evalPrefix_val, layeredROBPEvalPrefixAux_foldl_eq]
  rfl

/-- The width of `streamingToLayeredROBP A n` is at most `Fintype.card S`. -/
theorem streamingToLayeredROBP_width_le {Alph : Type u} {Z : Type v} {S : Type w} [Fintype S]
    (A : Cslib.Streaming.Algorithm S Alph Z) (n : ℕ) :
    (streamingToLayeredROBP A n).width ≤ Fintype.card S := by
  unfold streamingToLayeredROBP
  refine (LayeredROBP.ofLayeredSystem_width_le _ _ _ _).trans ?_
  exact Finset.sup_le fun _ _ ↦ le_rfl

/-- Canonical length-`n` universe-`0` LayeredROBP induced by any `Cslib.Streaming.Algorithm`
satisfying
`A.SpaceLE n b` (without requiring `[Fintype S]`), obtained by encoding reachable states into
`Cslib.BitString b`. -/
noncomputable def streamingToLayeredROBPOfSpaceLE {Alph : Type u} {Z : Type v} {S : Type w}
    (A : Cslib.Streaming.Algorithm S Alph Z) {n b : ℕ} (hA : A.SpaceLE n b) :
    LayeredROBP.{u, v, 0} n Alph Z := by
  classical
  let enc : S → Cslib.BitString b := Classical.choose hA
  let decode (t : Fin (n + 1)) (c : Cslib.BitString b) : S :=
    if h : ∃ x : Fin t.1 → Alph, enc (A.state (List.ofFn x)) = c then
      A.state (List.ofFn (Classical.choose h))
    else A.init
  let stepEnc : ∀ i : Fin n, Cslib.BitString b → Alph → Cslib.BitString b := fun i c a ↦
    enc (A.update (decode i.castSucc c) a)
  exact LayeredROBP.ofLayeredSystem (fun _ : Fin (n + 1) ↦ Cslib.BitString b)
    (enc A.init) stepEnc (fun c ↦ A.output (decode (Fin.last n) c))

/-- Running `streamingToLayeredROBPOfSpaceLE A hA` on `x : Fin n → Alph` matches
`A.run (List.ofFn x)`. -/
@[simp, grind =]
theorem streamingToLayeredROBPOfSpaceLE_run {Alph : Type u} {Z : Type v} {S : Type w}
    (A : Cslib.Streaming.Algorithm S Alph Z) {n b : ℕ} (hA : A.SpaceLE n b) (x : Fin n → Alph) :
    (streamingToLayeredROBPOfSpaceLE A hA).run x = A.run (List.ofFn x) := by
  classical
  unfold streamingToLayeredROBPOfSpaceLE
  simp only [LayeredROBP.ofLayeredSystem_run]
  set enc := Classical.choose hA
  have henc : Set.InjOn enc (A.reachable n) := Classical.choose_spec hA
  have hmem_reach : ∀ (t : Fin (n + 1)) (y : Fin t.1 → Alph),
      A.state (List.ofFn y) ∈ A.reachable n :=
    fun t y ↦ ⟨List.ofFn y, by rw [List.length_ofFn]; exact Nat.lt_succ_iff.mp t.2, rfl⟩
  let decode (t : Fin (n + 1)) (c : Cslib.BitString b) : S :=
    if h : ∃ y : Fin t.1 → Alph, enc (A.state (List.ofFn y)) = c then
      A.state (List.ofFn (Classical.choose h))
    else A.init
  have hdecode : ∀ (t : Fin (n + 1)) (y : Fin t.1 → Alph),
      decode t (enc (A.state (List.ofFn y))) = A.state (List.ofFn y) := by
    intro t y
    have h : ∃ z : Fin t.1 → Alph, enc (A.state (List.ofFn z)) = enc (A.state (List.ofFn y)) :=
      ⟨y, rfl⟩
    dsimp only [decode]
    simp only [h, ↓reduceDIte]
    exact henc (hmem_reach t _) (hmem_reach t y) (Classical.choose_spec h)
  have heval : ∀ (k : ℕ) (hk : k ≤ n) (y : Fin k → Alph),
      layeredROBPEvalPrefixAux (V := fun _ : Fin (n + 1) ↦ Cslib.BitString b)
          (enc A.init) (fun i c a ↦ enc (A.update (decode i.castSucc c) a)) k hk y =
        enc (A.state (List.ofFn y)) := by
    intro k
    induction k with
    | zero =>
      intro hk y
      rw [layeredROBPEvalPrefixAux_zero]
      have hnil : List.ofFn y = [] := List.ofFn_eq_nil_iff.mpr rfl
      rw [hnil]
      rfl
    | succ k ih =>
      intro hk y
      rw [layeredROBPEvalPrefixAux_succ, ih (Nat.le_of_succ_le hk)]
      have hstep : decode (⟨k, hk⟩ : Fin n).castSucc
            (enc (A.state (List.ofFn fun i : Fin k ↦ y i.castSucc))) =
          A.state (List.ofFn fun i : Fin k ↦ y i.castSucc) :=
        hdecode (⟨k, hk⟩ : Fin n).castSucc (fun i ↦ y i.castSucc)
      rw [hstep, List.ofFn_succ', List.concat_eq_append, Cslib.Streaming.Algorithm.state_append]
      rfl
  rw [heval n le_rfl x]
  exact congrArg A.output (hdecode (Fin.last n) x)

/-- The width of `streamingToLayeredROBPOfSpaceLE A hA` is at most `2 ^ b`. -/
theorem streamingToLayeredROBPOfSpaceLE_width_le {Alph : Type u} {Z : Type v} {S : Type w}
    (A : Cslib.Streaming.Algorithm S Alph Z) {n b : ℕ} (hA : A.SpaceLE n b) :
    (streamingToLayeredROBPOfSpaceLE A hA).width ≤ 2 ^ b := by
  unfold streamingToLayeredROBPOfSpaceLE
  refine (LayeredROBP.ofLayeredSystem_width_le _ _ _ _).trans ?_
  refine Finset.sup_le fun _ _ ↦ ?_
  simp [Cslib.BitString]

end StreamingBridge

section Witnesses

private lemma exactHamming_evalAux (n : ℕ) :
    let V : Fin (n + 1) → Type := fun t ↦ Fin (t.1 + 1)
    let start : V 0 := ⟨0, Nat.zero_lt_succ _⟩
    let step : ∀ i : Fin n, V i.castSucc → Bool → V i.succ := fun i v b ↦
      ⟨v.1 + (if b then 1 else 0), by
        have hv : v.1 < i.1 + 1 := by simpa [Fin.val_castSucc] using v.2
        rw [Fin.val_succ]
        split_ifs <;> omega⟩
    ∀ (k : ℕ) (hk : k ≤ n) (x : Fin k → Bool),
      (layeredROBPEvalPrefixAux start step k hk x).1 =
        (Finset.univ.filter fun i : Fin k ↦ x i = true).card := by
  intro V start step k
  induction k with
  | zero =>
    intro hk x
    simp [start]
  | succ k ih =>
    intro hk x
    rw [layeredROBPEvalPrefixAux_succ]
    change (layeredROBPEvalPrefixAux start step k (Nat.le_of_succ_le hk) (fun i ↦ x i.castSucc)).1 +
        (if x (Fin.last k) = true then 1 else 0) = _
    rw [ih (Nat.le_of_succ_le hk) (fun i ↦ x i.castSucc)]
    simp only [Finset.card_filter]
    rw [Fin.sum_univ_castSucc]

private lemma card_filter_lt_eq (m k : ℕ) (hk : k ≤ m) :
    (Finset.univ.filter fun j : Fin m ↦ decide (j.1 < k) = true).card = k := by
  have heq : (Finset.univ.filter fun j : Fin m ↦ decide (j.1 < k) = true) =
      (Finset.range k).attach.map
        ⟨fun i ↦ ⟨i.1, lt_of_lt_of_le (Finset.mem_range.mp i.2) hk⟩, fun a b h ↦ by
          ext; exact congrArg Fin.val h⟩ := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, decide_eq_true_eq, true_and, Finset.mem_map,
      Finset.mem_attach, Subtype.exists, Finset.mem_range]
    constructor
    · intro hj
      exact ⟨j.1, hj, Fin.ext rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ha
  rw [heq, Finset.card_map, Finset.card_attach, Finset.card_range]

/-- Length-`n` LayeredROBP over `Bool` computing the exact Hamming weight of its input, with layer
`t`
having size `t + 1`. -/
def exactHammingLayeredROBP (n : ℕ) : LayeredROBP.{0, 0, 0} n Bool ℕ where
  V t := Fin (t.1 + 1)
  instFintypeV _ := inferInstance
  start := ⟨0, Nat.zero_lt_succ _⟩
  eq_start v := by
    have hv : v.1 < 1 := by simpa [Fin.val_zero] using v.2
    exact Fin.ext (Nat.lt_one_iff.mp hv)
  step i v b := ⟨v.1 + (if b then 1 else 0), by
    have hv : v.1 < i.1 + 1 := by simpa [Fin.val_castSucc] using v.2
    rw [Fin.val_succ]
    split_ifs <;> omega⟩
  output v := v.1
  reachable t v := by
    refine ⟨fun j ↦ decide (j.1 < v.1), Fin.ext ?_⟩
    rw [exactHamming_evalAux n t.1 (Nat.lt_succ_iff.mp t.2) _]
    exact card_filter_lt_eq t.1 v.1 (Nat.lt_succ_iff.mp v.2)

/-- Width of `exactHammingLayeredROBP n` is at most `n + 1`. -/
theorem exactHammingLayeredROBP_width_le (n : ℕ) : (exactHammingLayeredROBP n).width ≤ n + 1 := by
  rw [LayeredROBP.width_le_iff]
  intro t
  change Fintype.card (Fin (t.1 + 1)) ≤ n + 1
  rw [Fintype.card_fin]
  omega

/-- Width of `exactHammingLayeredROBP n` equals `n + 1`. -/
@[simp]
theorem exactHammingLayeredROBP_width (n : ℕ) : (exactHammingLayeredROBP n).width = n + 1 := by
  refine le_antisymm (exactHammingLayeredROBP_width_le n) ?_
  have hlast := (exactHammingLayeredROBP n).card_last_le_width
  change Fintype.card (Fin ((Fin.last n).1 + 1)) ≤ (exactHammingLayeredROBP n).width at hlast
  simpa using hlast

/-- Output of `exactHammingLayeredROBP n` on `x : Fin n → Bool` is the Hamming weight of `x`. -/
@[simp, grind =]
theorem exactHammingLayeredROBP_run (n : ℕ) (x : Fin n → Bool) :
    (exactHammingLayeredROBP n).run x = (Finset.univ.filter fun i ↦ x i = true).card := by
  rw [LayeredROBP.run_eq, LayeredROBP.eval_eq_evalPrefix_last]
  exact exactHamming_evalAux n n le_rfl x

/-- `exactHammingLayeredROBP n` computes the exact Hamming weight function on `Fin n → Bool`. -/
theorem computes_exactHammingLayeredROBP (n : ℕ) :
    (exactHammingLayeredROBP n).Computes fun x ↦ (Finset.univ.filter fun i ↦ x i = true).card :=
  fun x ↦ exactHammingLayeredROBP_run n x

private lemma bne_foldr_bne (ys : List Bool) (a : Bool) :
    bne (ys.foldr bne false) a = ys.foldr bne a := by
  induction ys with
  | nil => simp
  | cons y ys ih =>
    simp only [List.foldr_cons, ← ih]
    cases y <;> cases ys.foldr bne false <;> cases a <;> rfl

private lemma parity_evalAux (n : ℕ) :
    ∀ (k : ℕ) (hk : k ≤ n) (x : Fin k → Bool),
      layeredROBPEvalPrefixAux (V := fun _ : Fin (n + 1) ↦ Bool)
          false (fun _ s b ↦ bne s b) k hk x =
        (List.ofFn x).foldr bne false := by
  intro k
  induction k with
  | zero =>
    intro hk x
    simp
  | succ k ih =>
    intro hk x
    rw [layeredROBPEvalPrefixAux_succ, ih (Nat.le_of_succ_le hk)]
    rw [List.ofFn_succ', List.concat_eq_append, List.foldr_append, bne_foldr_bne]
    simp

/-- Length-`n` LayeredROBP over `Bool` of width at most `2` computing the Boolean parity of its
input. -/
noncomputable def parityLayeredROBP (n : ℕ) : LayeredROBP.{0, 0, 0} n Bool Bool :=
  LayeredROBP.ofLayeredSystem (fun _ ↦ Bool) false (fun _ s b ↦ bne s b) id

/-- Width of `parityLayeredROBP n` is at most `2`. -/
theorem parityLayeredROBP_width_le (n : ℕ) : (parityLayeredROBP n).width ≤ 2 := by
  unfold parityLayeredROBP
  refine (LayeredROBP.ofLayeredSystem_width_le _ _ _ _).trans ?_
  refine Finset.sup_le fun _ _ ↦ ?_
  simp

/-- Output of `parityLayeredROBP n` on `x : Fin n → Bool` is the parity
`(List.ofFn x).foldr bne false`. -/
@[simp, grind =]
theorem parityLayeredROBP_run (n : ℕ) (x : Fin n → Bool) :
    (parityLayeredROBP n).run x = (List.ofFn x).foldr bne false := by
  unfold parityLayeredROBP
  rw [LayeredROBP.ofLayeredSystem_run]
  exact parity_evalAux n n le_rfl x

/-- `parityLayeredROBP n` computes the Boolean parity function
`fun x ↦ (List.ofFn x).foldr bne false`. -/
theorem computes_parityLayeredROBP (n : ℕ) :
    (parityLayeredROBP n).Computes fun x ↦ (List.ofFn x).foldr bne false :=
  fun x ↦ parityLayeredROBP_run n x

/-- Any LayeredROBP computing a non-constant function `f : (Fin n → Alph) → Z` has width at least
`2`. -/
theorem LayeredROBP.two_le_width_of_computes {n : ℕ} {Alph : Type u} {Z : Type v}
    (P : LayeredROBP.{u, v, w} n Alph Z) {f : (Fin n → Alph) → Z} (hP : P.Computes f)
    {x y : Fin n → Alph} (hxy : f x ≠ f y) : 2 ≤ P.width := by
  by_contra hlt
  have hle : P.width ≤ 1 := by omega
  have hcard : Fintype.card (P.V (Fin.last n)) ≤ 1 := P.card_last_le_width.trans hle
  have hsub : Subsingleton (P.V (Fin.last n)) := Fintype.card_le_one_iff_subsingleton.mp hcard
  have heval : P.eval x = P.eval y := Subsingleton.elim _ _
  have hrun : P.run x = P.run y := by rw [P.run_eq, P.run_eq, heval]
  exact hxy ((hP x).symm.trans (hrun.trans (hP y)))

/-- No LayeredROBP of width at most `1` can compute a function `f : (Fin n → Alph) → Z` taking two
distinct values `f x ≠ f y`. -/
theorem not_exists_width_one_robp_computes {n : ℕ} {Alph : Type u} {Z : Type v}
    {f : (Fin n → Alph) → Z} {x y : Fin n → Alph} (hxy : f x ≠ f y) :
    ¬ ∃ P : LayeredROBP.{u, v, w} n Alph Z, P.width ≤ 1 ∧ P.Computes f := by
  rintro ⟨P, hw, hP⟩
  have h2 := P.two_le_width_of_computes hP hxy
  omega

private lemma foldr_bne_const_false :
    ∀ (m : ℕ) (f : Fin m → Bool), (∀ i, f i = false) → (List.ofFn f).foldr bne false = false := by
  intro m
  induction m with
  | zero => intro _ _; simp
  | succ m ih =>
    intro f hf
    rw [List.ofFn_succ, List.foldr_cons, ih _ fun i ↦ hf i.succ, hf 0]
    rfl

/-- Concrete width separation: for every `n ≥ 1`, parity on `Fin n → Bool` is computed by a
width-`2` LayeredROBP (`parityLayeredROBP n`) and by no LayeredROBP of width at most `1`. -/
theorem not_exists_width_one_robp_computes_parity {n : ℕ} (hn : 1 ≤ n) :
    ¬ ∃ P : LayeredROBP.{0, 0, w} n Bool Bool,
      P.width ≤ 1 ∧ P.Computes fun x ↦ (List.ofFn x).foldr bne false := by
  let x : Fin n → Bool := fun _ ↦ false
  let y : Fin n → Bool := fun i ↦ decide (i.1 = 0)
  have hfx : (List.ofFn x).foldr bne false = false :=
    foldr_bne_const_false n x fun _ ↦ rfl
  have hfy : (List.ofFn y).foldr bne false = true := by
    cases n with
    | zero => omega
    | succ m =>
      rw [List.ofFn_succ, List.foldr_cons]
      have hy0 : y 0 = true := by simp [y]
      have htail : (List.ofFn fun i : Fin m ↦ y i.succ).foldr bne false = false :=
        foldr_bne_const_false m _ fun i ↦ by simp [y]
      rw [hy0, htail]
      rfl
  exact not_exists_width_one_robp_computes (x := x) (y := y) (by rw [hfx, hfy]; decide)

end Witnesses

end CslibFrontier.Computability.BranchingProgram
