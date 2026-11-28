/-
Copyright (c) 2026 Google DeepMind. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Google DeepMind
-/
module
-- upstream: candidate

public import Cslib.Init
public import Cslib.Foundations.Control.Monad.Free
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Order.FixedPoints
public import Mathlib.Data.Nat.Log

/-!
# Query Complexity Reductions for Tarski Fixed Points on Finite Hypergrids

This module develops general query-complexity reductions for computing fixed points of monotone
functions on finite `k`-dimensional hypergrids `[n]^k` (`Fin k → Fin n`), together with the
intermediate monotone up-or-down relaxation over `[n]^k → [n]^k × {-1, +1}`, represented as pure
effect trees in `Cslib.FreeM`.

## Main definitions

* `CslibFrontier.Computability.QueryComplexity.Hypergrid`: the finite product lattice
  `Fin k → Fin n`.
* `CslibFrontier.Computability.QueryComplexity.UpDownSign`,
  `CslibFrontier.Computability.QueryComplexity.TarskiUpDownFn`,
  `CslibFrontier.Computability.QueryComplexity.IsMonotoneUpDown`,
  `CslibFrontier.Computability.QueryComplexity.IsUpDownSol`: monotone functions and postfixed /
  prefixed directional solutions for the up-or-down search relaxation on `[n]^k`.
* `CslibFrontier.Computability.QueryComplexity.TarskiGridQuery`,
  `CslibFrontier.Computability.QueryComplexity.TarskiUpDownQuery`: oracle effect signatures in
  `Cslib.FreeM`, paired with structural interpreters `evalOracle` and `queryCount`.
* `CslibFrontier.Computability.QueryComplexity.clampUnitDisp`: unit-displacement clamping map
  restricting coordinatewise steps `f(x)_i - x_i` to `{-1, 0, +1}`.
* `CslibFrontier.Computability.QueryComplexity.reduceTarskiSliceBisect`: hypergrid slice-bisection
  reduction computing a fixed point on `[n]^{k+1}` via `Nat.log 2 n + 1` calls to a `k`-dimensional
  up-or-down solver followed by one call to a `k`-dimensional fixed-point solver.
* `CslibFrontier.Computability.QueryComplexity.decompUpDown`: product decomposition algorithm
  solving `(a + b)`-dimensional monotone up-or-down search using an `a`-dimensional solver and a
  `b`-dimensional solver via Kleene least fixed points on invariant sublattice fibers.

## Main results

* `CslibFrontier.Computability.QueryComplexity.exists_hypergrid_fixedPoint`: Kleene/Tarski
  existence of fixed points for monotone self-maps on `Hypergrid n k`.
* `CslibFrontier.Computability.QueryComplexity.clampUnitDisp_spec`: unit-displacement clamping
  preserves monotonicity and the exact set of up-or-down solutions.
* `CslibFrontier.Computability.QueryComplexity.reduceTarskiSliceBisect_spec`: slice-bisection
  finds a genuine fixed point on `Hypergrid n (k + 1)` in at most
  `(Nat.log 2 n + 1) * (Q_star + 1) + Q_base` queries.
* `CslibFrontier.Computability.QueryComplexity.decompUpDown_spec`: product decomposition solves
  `(a + b)`-dimensional monotone up-or-down search in at most
  `(Q_a + 1) * (2 * a + 1) * (Q_b + 1)` queries.
-/

public section

namespace CslibFrontier.Computability.QueryComplexity

open Cslib

/-! ## Structural Query Interpreters on `Cslib.FreeM` -/

/-- Structural deterministic evaluation of a `FreeM` computation against `oracle`. -/
def evalOracle {F : Type → Type} {α : Type}
    (oracle : {ι : Type} → F ι → ι) : FreeM F α → α
  | .pure a => a
  | .liftBind op cont => evalOracle oracle (cont (oracle op))

/-- Structural query count along the execution path determined by `oracle`. -/
def queryCount {F : Type → Type} {α : Type}
    (oracle : {ι : Type} → F ι → ι) : FreeM F α → ℕ
  | .pure _ => 0
  | .liftBind op cont => 1 + queryCount oracle (cont (oracle op))

@[simp]
theorem evalOracle_pure {F : Type → Type} {α : Type}
    (oracle : {ι : Type} → F ι → ι) (a : α) :
    evalOracle oracle (pure a : FreeM F α) = a := by rfl

@[simp]
theorem queryCount_pure {F : Type → Type} {α : Type}
    (oracle : {ι : Type} → F ι → ι) (a : α) :
    queryCount oracle (pure a : FreeM F α) = 0 := by rfl

@[simp]
theorem evalOracle_lift {F : Type → Type} {ι : Type}
    (oracle : {ρ : Type} → F ρ → ρ) (op : F ι) :
    evalOracle oracle (FreeM.lift op) = oracle op := by rfl

@[simp]
theorem queryCount_lift {F : Type → Type} {ι : Type}
    (oracle : {ρ : Type} → F ρ → ρ) (op : F ι) :
    queryCount oracle (FreeM.lift op) = 1 := by rfl

@[simp]
theorem evalOracle_map {F : Type → Type} {α β : Type}
    (oracle : {ι : Type} → F ι → ι) (f : α → β) (t : FreeM F α) :
    evalOracle oracle (f <$> t) = f (evalOracle oracle t) := by
  induction t with
  | pure a => rfl
  | lift_bind op cont ih =>
    rw [← FreeM.liftBind_eq]
    exact ih (oracle op)

@[simp]
theorem queryCount_map {F : Type → Type} {α β : Type}
    (oracle : {ι : Type} → F ι → ι) (f : α → β) (t : FreeM F α) :
    queryCount oracle (f <$> t) = queryCount oracle t := by
  induction t with
  | pure a => rfl
  | lift_bind op cont ih =>
    rw [← FreeM.liftBind_eq]
    exact congr_arg (1 + ·) (ih (oracle op))

@[simp]
theorem evalOracle_bind {F : Type → Type} {α β : Type}
    (oracle : {ι : Type} → F ι → ι) (t : FreeM F α) (f : α → FreeM F β) :
    evalOracle oracle (t >>= f) = evalOracle oracle (f (evalOracle oracle t)) := by
  induction t with
  | pure a => rfl
  | lift_bind op cont ih =>
    rw [← FreeM.liftBind_eq]
    exact ih (oracle op)

@[simp]
theorem queryCount_bind {F : Type → Type} {α β : Type}
    (oracle : {ι : Type} → F ι → ι) (t : FreeM F α) (f : α → FreeM F β) :
    queryCount oracle (t >>= f) =
      queryCount oracle t + queryCount oracle (f (evalOracle oracle t)) := by
  induction t with
  | pure a => simp
  | lift_bind op cont ih =>
    rw [← FreeM.liftBind_eq]
    change 1 + queryCount oracle (cont (oracle op) >>= f) =
      (1 + queryCount oracle (cont (oracle op))) +
        queryCount oracle (f (evalOracle oracle (cont (oracle op))))
    rw [ih (oracle op), Nat.add_assoc]

theorem evalOracle_liftM {F G : Type → Type} {α : Type}
    (t : FreeM F α) (handler : {ι : Type} → F ι → FreeM G ι)
    (oracle : {ι : Type} → G ι → ι) :
    evalOracle oracle (t.liftM handler) =
      evalOracle (fun op ↦ evalOracle oracle (handler op)) t := by
  induction t with
  | pure a => rfl
  | lift_bind op cont ih =>
    simp only [FreeM.bind_eq_bind, FreeM.liftM_lift_bind, evalOracle_bind, evalOracle_lift]
    exact ih (evalOracle oracle (handler op))

theorem queryCount_liftM_le {F G : Type → Type} {α : Type}
    (t : FreeM F α) (handler : {ι : Type} → F ι → FreeM G ι)
    (oracle : {ι : Type} → G ι → ι) {c : ℕ}
    (hc : ∀ {ι : Type} (op : F ι), queryCount oracle (handler op) ≤ c) :
    queryCount oracle (t.liftM handler) ≤
      c * queryCount (fun op ↦ evalOracle oracle (handler op)) t := by
  induction t with
  | pure a => simp
  | lift_bind op cont ih =>
    simp only [FreeM.bind_eq_bind, FreeM.liftM_lift_bind, queryCount_bind, queryCount_lift,
      evalOracle_lift, Nat.mul_add, Nat.mul_one]
    exact Nat.add_le_add (hc op) (ih (evalOracle oracle (handler op)))

/-! ## Hypergrids, Monotone Fixed Points, and Up-or-Down Search -/

/-- The `k`-dimensional finite hypergrid `[n]^k`, represented as `Fin k → Fin n`. -/
public abbrev Hypergrid (n k : ℕ) : Type := Fin k → Fin n

/-- Existence of a fixed point for any monotone self-map on a nonempty finite hypergrid. -/
theorem exists_hypergrid_fixedPoint {n k : ℕ} [NeZero n] {f : Hypergrid n k → Hypergrid n k}
    (hf : Monotone f) : ∃ x : Hypergrid n k, Function.IsFixedPt f x := by
  let g : Hypergrid n k →o Hypergrid n k := ⟨f, hf⟩
  have hchain : Monotone (fun t : ℕ ↦ (g^[t]) ⊥) := by
    refine monotone_nat_of_le_succ fun t ↦ ?_
    induction t with
    | zero => exact bot_le
    | succ t ih => simpa only [Function.iterate_succ_apply'] using g.monotone ih
  by_contra hno
  push Not at hno
  have hstrict : StrictMono (fun t : Fin (Fintype.card (Hypergrid n k) + 1) ↦ (g^[t.val]) ⊥) := by
    intro a b hab
    have hstep : (g^[a.val]) ⊥ < (g^[a.val + 1]) ⊥ := by
      refine lt_of_le_of_ne (hchain (Nat.le_succ a.val)) fun heq ↦ hno ((g^[a.val]) ⊥) ?_
      change g ((g^[a.val]) ⊥) = (g^[a.val]) ⊥
      simpa only [Function.iterate_succ_apply'] using heq.symm
    exact lt_of_lt_of_le hstep (hchain hab)
  have hcard := Fintype.card_le_of_injective _ hstrict.injective
  rw [Fintype.card_fin] at hcard
  omega

/-- Two-valued directional sign `{-1, +1}` with `.neg < .pos`. -/
inductive UpDownSign : Type
  /-- Downward / prefixed sign `-1`. -/
  | neg
  /-- Upward / postfixed sign `+1`. -/
  | pos
  deriving DecidableEq, Repr

namespace UpDownSign

/-- Map `UpDownSign` injectively into `ℤ` (`-1` and `1`). -/
@[expose] def toInt : UpDownSign → ℤ
  | .neg => -1
  | .pos => 1

theorem toInt_injective : Function.Injective toInt := by
  intro a b h; cases a <;> cases b <;> cases h <;> rfl

instance instLinearOrder : LinearOrder UpDownSign :=
  LinearOrder.lift' toInt toInt_injective

/-- Opposite sign involution. -/
@[expose] def dual : UpDownSign → UpDownSign
  | .neg => .pos
  | .pos => .neg

end UpDownSign

/-- Function space `Hypergrid n k → Hypergrid n k × UpDownSign` for monotone up-or-down search. -/
public abbrev TarskiUpDownFn (n k : ℕ) : Type := Hypergrid n k → Hypergrid n k × UpDownSign

/-- Monotonicity in both the hypergrid output and the directional sign bit. -/
def IsMonotoneUpDown {n k : ℕ} (f : TarskiUpDownFn n k) : Prop :=
  (∀ ⦃a b : Hypergrid n k⦄, a ≤ b → (f a).1 ≤ (f b).1) ∧
  (∀ ⦃a b : Hypergrid n k⦄, a ≤ b → (f a).2 ≤ (f b).2)

/-- Solution predicate for monotone up-or-down search: either `x` is postfixed with `.pos` or
prefixed with `.neg`. -/
def IsUpDownSol {n k : ℕ} (f : TarskiUpDownFn n k) (x : Hypergrid n k) : Prop :=
  (x ≤ (f x).1 ∧ (f x).2 = .pos) ∨ ((f x).1 ≤ x ∧ (f x).2 = .neg)

/-- Oracle query signature for hypergrid fixed-point search. -/
inductive TarskiGridQuery (n k : ℕ) : Type → Type where
  /-- Evaluate `g(x)` at `x ∈ [n]^k`. -/
  | query (x : Hypergrid n k) : TarskiGridQuery n k (Hypergrid n k)

namespace TarskiGridQuery

/-- Issue one query at `x`. -/
public abbrev ask {n k : ℕ} (x : Hypergrid n k) : FreeM (TarskiGridQuery n k) (Hypergrid n k) :=
  FreeM.lift (.query x)

/-- Canonical oracle induced by `g : Hypergrid n k → Hypergrid n k`. -/
@[expose] def oracleOf {n k : ℕ} (g : Hypergrid n k → Hypergrid n k) :
    {ι : Type} → TarskiGridQuery n k ι → ι
  | _, .query x => g x

theorem evalOracle_ask {n k : ℕ} (g : Hypergrid n k → Hypergrid n k) (x : Hypergrid n k) :
    evalOracle (oracleOf g) (ask x) = g x := by rfl

theorem queryCount_ask {n k : ℕ} (g : Hypergrid n k → Hypergrid n k) (x : Hypergrid n k) :
    queryCount (oracleOf g) (ask x) = 1 := by rfl

end TarskiGridQuery

/-- Oracle query signature for monotone up-or-down search. -/
inductive TarskiUpDownQuery (n k : ℕ) : Type → Type where
  /-- Evaluate `f(x)` at `x ∈ [n]^k`. -/
  | query (x : Hypergrid n k) : TarskiUpDownQuery n k (Hypergrid n k × UpDownSign)

namespace TarskiUpDownQuery

/-- Issue one query at `x`. -/
public abbrev ask {n k : ℕ} (x : Hypergrid n k) :
    FreeM (TarskiUpDownQuery n k) (Hypergrid n k × UpDownSign) :=
  FreeM.lift (.query x)

/-- Canonical oracle induced by `f : TarskiUpDownFn n k`. -/
@[expose] def oracleOf {n k : ℕ} (f : TarskiUpDownFn n k) :
    {ι : Type} → TarskiUpDownQuery n k ι → ι
  | _, .query x => f x

theorem evalOracle_ask {n k : ℕ} (f : TarskiUpDownFn n k) (x : Hypergrid n k) :
    evalOracle (oracleOf f) (ask x) = f x := by rfl

theorem queryCount_ask {n k : ℕ} (f : TarskiUpDownFn n k) (x : Hypergrid n k) :
    queryCount (oracleOf f) (ask x) = 1 := by rfl

end TarskiUpDownQuery

/-! ## Unit-Displacement Clamping Reduction -/

/-- Clamp each output coordinate `f(x)_i` to `x_i + sgn(f(x)_i - x_i) ∈ {x_i - 1, x_i, x_i + 1}`. -/
def clampUnitDisp {n k : ℕ} (f : TarskiUpDownFn n k) : TarskiUpDownFn n k :=
  fun x ↦
    (fun i ↦
      if (f x).1 i < x i then
        ⟨(x i).val - 1, by have := (x i).isLt; omega⟩
      else if hlt : x i < (f x).1 i then
        ⟨(x i).val + 1, by
          have hlt' : (x i).val < ((f x).1 i).val := hlt
          have hfx := ((f x).1 i).isLt
          omega⟩
      else x i,
    (f x).2)

@[simp]
theorem clampUnitDisp_snd {n k : ℕ} (f : TarskiUpDownFn n k) (x : Hypergrid n k) :
    (clampUnitDisp f x).2 = (f x).2 := by rfl

theorem clampUnitDisp_fst_val {n k : ℕ} (f : TarskiUpDownFn n k) (x : Hypergrid n k) (i : Fin k) :
    ((clampUnitDisp f x).1 i).val =
      if (f x).1 i < x i then (x i).val - 1
      else if x i < (f x).1 i then (x i).val + 1
      else (x i).val := by
  simp only [clampUnitDisp]
  split_ifs <;> rfl

/-- Unit-displacement clamping preserves monotonicity and the exact set of up-or-down solutions. -/
theorem clampUnitDisp_spec {n k : ℕ} {f : TarskiUpDownFn n k} (hf : IsMonotoneUpDown f) :
    IsMonotoneUpDown (clampUnitDisp f) ∧
    ∀ x, IsUpDownSol (clampUnitDisp f) x ↔ IsUpDownSol f x := by
  refine ⟨⟨fun a b hab i ↦ ?_, fun a b hab ↦ hf.2 hab⟩, fun x ↦ ?_⟩
  · apply Fin.le_def.mpr
    rw [clampUnitDisp_fst_val, clampUnitDisp_fst_val]
    have hai : (a i).val ≤ (b i).val := hab i
    have hfi : ((f a).1 i).val ≤ ((f b).1 i).val := hf.1 hab i
    have hlt1 : (f a).1 i < a i ↔ ((f a).1 i).val < (a i).val := Iff.rfl
    have hlt2 : a i < (f a).1 i ↔ (a i).val < ((f a).1 i).val := Iff.rfl
    have hlt3 : (f b).1 i < b i ↔ ((f b).1 i).val < (b i).val := Iff.rfl
    have hlt4 : b i < (f b).1 i ↔ (b i).val < ((f b).1 i).val := Iff.rfl
    split_ifs <;> simp_all <;> omega
  · dsimp only [IsUpDownSol]
    rw [clampUnitDisp_snd]
    have hge_iff : x ≤ (clampUnitDisp f x).1 ↔ x ≤ (f x).1 := by
      refine ⟨fun h i ↦ ?_, fun h i ↦ ?_⟩
      · have hi : (x i).val ≤ ((clampUnitDisp f x).1 i).val := h i
        rw [clampUnitDisp_fst_val] at hi
        apply Fin.le_def.mpr
        by_cases h1 : (f x).1 i < x i
        · rw [ite_eq_left h1] at hi
          have h1' : ((f x).1 i).val < (x i).val := h1
          omega
        · exact le_of_not_gt h1
      · have hi : (x i).val ≤ ((f x).1 i).val := h i
        apply Fin.le_def.mpr
        rw [clampUnitDisp_fst_val]
        have hnot : ¬ ((f x).1 i < x i) := not_lt_of_ge (h i)
        rw [ite_eq_right hnot]
        split_ifs <;> omega
    have hle_iff : (clampUnitDisp f x).1 ≤ x ↔ (f x).1 ≤ x := by
      refine ⟨fun h i ↦ ?_, fun h i ↦ ?_⟩
      · have hi : ((clampUnitDisp f x).1 i).val ≤ (x i).val := h i
        rw [clampUnitDisp_fst_val] at hi
        apply Fin.le_def.mpr
        by_cases h1 : (f x).1 i < x i
        · exact le_of_lt h1
        · rw [ite_eq_right h1] at hi
          by_cases h2 : x i < (f x).1 i
          · rw [ite_eq_left h2] at hi; omega
          · exact le_of_not_gt h2
      · apply Fin.le_def.mpr
        rw [clampUnitDisp_fst_val]
        by_cases h1 : (f x).1 i < x i
        · rw [ite_eq_left h1]; omega
        · rw [ite_eq_right h1, ite_eq_right (not_lt_of_ge (h i))]
    rw [hge_iff, hle_iff]

/-! ## Box Clamping and Hypergrid Slice-Bisection Reduction -/

/-- Coordinatewise clamping onto the sublattice box `[l, u] ⊆ Hypergrid n m`. -/
def clampHyperbox {n m : ℕ} (l u x : Hypergrid n m) : Hypergrid n m :=
  fun i ↦ max (l i) (min (u i) (x i))

theorem clampHyperbox_mem {n m : ℕ} {l u : Hypergrid n m} (hlu : l ≤ u) (x : Hypergrid n m) :
    l ≤ clampHyperbox l u x ∧ clampHyperbox l u x ≤ u :=
  ⟨fun _ ↦ le_max_left _ _, fun i ↦ max_le (hlu i) (min_le_left _ _)⟩

theorem clampHyperbox_eq_of_mem {n m : ℕ} {l u x : Hypergrid n m} (hl : l ≤ x) (hu : x ≤ u) :
    clampHyperbox l u x = x := by
  ext i
  change (max (l i) (min (u i) (x i))).val = (x i).val
  rw [min_eq_right (hu i), max_eq_right (hl i)]

theorem clampHyperbox_mono {n m : ℕ} (l u : Hypergrid n m) : Monotone (clampHyperbox l u) :=
  fun _ _ hxy i ↦ max_le_max_left (l i) (min_le_min_left (u i) (hxy i))

theorem clampHyperbox_le_of_le {n m : ℕ} {l u x v : Hypergrid n m} (hlv : l ≤ v) (hxv : x ≤ v) :
    clampHyperbox l u x ≤ v :=
  fun i ↦ max_le (hlv i) ((min_le_right _ _).trans (hxv i))

theorem le_clampHyperbox_of_le {n m : ℕ} {l u x v : Hypergrid n m} (hvu : v ≤ u) (hvx : v ≤ x) :
    v ≤ clampHyperbox l u x :=
  fun i ↦ (le_min (hvu i) (hvx i)).trans (le_max_right _ _)

private def initCoords {n k : ℕ} (z : Hypergrid n (k + 1)) : Hypergrid n k :=
  fun i ↦ z i.castSucc

private def liftSlicePoint {n k : ℕ} (l u : Hypergrid n (k + 1)) (mid : Fin n)
    (y : Hypergrid n k) : Hypergrid n (k + 1) :=
  Fin.snoc (clampHyperbox (initCoords l) (initCoords u) y) mid

private def sliceMidUpDown {n k : ℕ} (g : Hypergrid n (k + 1) → Hypergrid n (k + 1))
    (l u : Hypergrid n (k + 1)) (mid : Fin n) : TarskiUpDownFn n k :=
  fun y ↦
    let x := liftSlicePoint l u mid y
    (initCoords (g x), if mid < g x (Fin.last k) then .pos else .neg)

private def sliceMidQueryHandler {n k : ℕ} (l u : Hypergrid n (k + 1)) (mid : Fin n) :
    {ι : Type} → TarskiUpDownQuery n k ι → FreeM (TarskiGridQuery n (k + 1)) ι
  | _, .query y' => do
    let gx ← TarskiGridQuery.ask (liftSlicePoint l u mid y')
    pure (initCoords gx, if mid < gx (Fin.last k) then .pos else .neg)

private def bisectHypergridLoop {n k : ℕ} [NeZero n]
    (algStar : FreeM (TarskiUpDownQuery n k) (Hypergrid n k)) :
    ℕ → Hypergrid n (k + 1) → Hypergrid n (k + 1) →
      FreeM (TarskiGridQuery n (k + 1)) (Hypergrid n (k + 1) × Hypergrid n (k + 1))
  | 0, l, u => pure (l, u)
  | t + 1, l, u =>
    if hlt : l (Fin.last k) < u (Fin.last k) then do
      let mid : Fin n := ⟨((l (Fin.last k)).val + (u (Fin.last k)).val) / 2, by
        have := (u (Fin.last k)).isLt; omega⟩
      let y ← algStar.liftM (sliceMidQueryHandler l u mid)
      let x := liftSlicePoint l u mid y
      let gx ← TarskiGridQuery.ask x
      if hpos : mid < gx (Fin.last k) then
        let l' : Hypergrid n (k + 1) := Function.update x (Fin.last k) ⟨mid.val + 1, by
          have := (gx (Fin.last k)).isLt
          have hlt' : mid.val < (gx (Fin.last k)).val := hpos
          omega⟩
        bisectHypergridLoop algStar t l' u
      else
        bisectHypergridLoop algStar t l x
    else
      pure (l, u)

private theorem bisectHypergridLoop_spec {n k : ℕ} [NeZero n]
    {algStar : FreeM (TarskiUpDownQuery n k) (Hypergrid n k)} {Q_star : ℕ}
    (hStar : ∀ F : TarskiUpDownFn n k, IsMonotoneUpDown F →
      IsUpDownSol F (evalOracle (TarskiUpDownQuery.oracleOf F) algStar) ∧
      queryCount (TarskiUpDownQuery.oracleOf F) algStar ≤ Q_star)
    {g : Hypergrid n (k + 1) → Hypergrid n (k + 1)} (hg : Monotone g) :
    ∀ (t : ℕ) (l u : Hypergrid n (k + 1)),
      l ≤ u → l ≤ g l → g u ≤ u →
      (evalOracle (TarskiGridQuery.oracleOf g) (bisectHypergridLoop algStar t l u)).1 ≤
        (evalOracle (TarskiGridQuery.oracleOf g) (bisectHypergridLoop algStar t l u)).2 ∧
      (evalOracle (TarskiGridQuery.oracleOf g) (bisectHypergridLoop algStar t l u)).1 ≤
        g (evalOracle (TarskiGridQuery.oracleOf g) (bisectHypergridLoop algStar t l u)).1 ∧
      g (evalOracle (TarskiGridQuery.oracleOf g) (bisectHypergridLoop algStar t l u)).2 ≤
        (evalOracle (TarskiGridQuery.oracleOf g) (bisectHypergridLoop algStar t l u)).2 ∧
      ((evalOracle (TarskiGridQuery.oracleOf g)
          (bisectHypergridLoop algStar t l u)).2 (Fin.last k)).val -
        ((evalOracle (TarskiGridQuery.oracleOf g)
          (bisectHypergridLoop algStar t l u)).1 (Fin.last k)).val ≤
        ((u (Fin.last k)).val - (l (Fin.last k)).val) / 2 ^ t ∧
      queryCount (TarskiGridQuery.oracleOf g) (bisectHypergridLoop algStar t l u) ≤
        t * (Q_star + 1) := by
  intro t
  induction t with
  | zero =>
    intro l u hlu hlg hgu
    simp only [bisectHypergridLoop, evalOracle_pure, queryCount_pure, pow_zero, Nat.div_one,
      Nat.zero_mul]
    exact ⟨hlu, hlg, hgu, le_rfl, le_rfl⟩
  | succ t ih =>
    intro l u hlu hlg hgu
    dsimp only [bisectHypergridLoop]
    by_cases hlt : l (Fin.last k) < u (Fin.last k)
    · rw [dite_eq_left hlt]
      let mid : Fin n := ⟨((l (Fin.last k)).val + (u (Fin.last k)).val) / 2, by
        have := (u (Fin.last k)).isLt; omega⟩
      have hlm : l (Fin.last k) ≤ mid := Fin.le_def.mpr (by dsimp [mid]; omega)
      have hmu : mid ≤ u (Fin.last k) := Fin.le_def.mpr (by dsimp [mid]; omega)
      have hlift_mono : Monotone (liftSlicePoint l u mid) := by
        intro y₁ y₂ hy j
        refine Fin.lastCases (by simp [liftSlicePoint]) (fun i ↦ ?_) j
        simpa only [liftSlicePoint, Fin.snoc_castSucc] using
          clampHyperbox_mono (initCoords l) (initCoords u) hy i
      have hmid_mono : IsMonotoneUpDown (sliceMidUpDown g l u mid) := by
        refine ⟨fun y₁ y₂ hy i ↦ hg (hlift_mono hy) i.castSucc, fun y₁ y₂ hy ↦ ?_⟩
        have hgx := hg (hlift_mono hy) (Fin.last k)
        dsimp only [sliceMidUpDown]
        split_ifs with h1 h2
        · exact le_rfl
        · exact absurd (lt_of_lt_of_le h1 hgx) h2
        · decide
        · exact le_rfl
      have hor_eq : (fun {ι} (op : TarskiUpDownQuery n k ι) ↦
          evalOracle (TarskiGridQuery.oracleOf g) (sliceMidQueryHandler l u mid op)) =
          @TarskiUpDownQuery.oracleOf n k (sliceMidUpDown g l u mid) := by
        funext ι op; cases op; rfl
      obtain ⟨hsol_y, hcnt_y⟩ := hStar (sliceMidUpDown g l u mid) hmid_mono
      set y := evalOracle (TarskiUpDownQuery.oracleOf (sliceMidUpDown g l u mid)) algStar
      set x := liftSlicePoint l u mid y
      obtain ⟨hcl, hcu⟩ := clampHyperbox_mem (fun i ↦ hlu i.castSucc) y
      have hlx : l ≤ x := fun j ↦ Fin.lastCases (by simpa [x, liftSlicePoint] using hlm)
        (fun i ↦ by dsimp only [x, liftSlicePoint]; rw [Fin.snoc_castSucc]; exact hcl i) j
      have hxu : x ≤ u := fun j ↦ Fin.lastCases (by simpa [x, liftSlicePoint] using hmu)
        (fun i ↦ by dsimp only [x, liftSlicePoint]; rw [Fin.snoc_castSucc]; exact hcu i) j
      have hlgx : l ≤ g x := hlg.trans (hg hlx)
      have hgxu : g x ≤ u := (hg hxu).trans hgu
      have hcnt_lift :
          queryCount (TarskiGridQuery.oracleOf g) (algStar.liftM (sliceMidQueryHandler l u mid)) ≤
            Q_star := by
        have hle := queryCount_liftM_le algStar (sliceMidQueryHandler l u mid)
          (TarskiGridQuery.oracleOf g) (c :=
            1) fun {ι} op ↦ by cases op; simp [sliceMidQueryHandler]
        rw [hor_eq, Nat.one_mul] at hle
        exact hle.trans hcnt_y
      have heval_lift :
          evalOracle (TarskiGridQuery.oracleOf g) (algStar.liftM (sliceMidQueryHandler l u mid)) =
            y := by
        rw [evalOracle_liftM, hor_eq]
      rw [evalOracle_bind, queryCount_bind, heval_lift, evalOracle_bind, queryCount_bind,
        TarskiGridQuery.evalOracle_ask, TarskiGridQuery.queryCount_ask]
      by_cases hpos : mid < g x (Fin.last k)
      · rw [dite_eq_left hpos]
        have hpos_val : mid.val < (g x (Fin.last k)).val := hpos
        have hsol_pos : y ≤ initCoords (g x) := by
          rcases hsol_y with ⟨hge, _⟩ | ⟨_, hneg⟩
          · exact hge
          · exfalso; dsimp only [sliceMidUpDown] at hneg; rw [ite_eq_left hpos] at hneg; cases hneg
        have hclamp_le : clampHyperbox (initCoords l) (initCoords u) y ≤ initCoords (g x) :=
          clampHyperbox_le_of_le (fun i ↦ hlgx i.castSucc) hsol_pos
        let l' : Hypergrid n (k + 1) := Function.update x (Fin.last k) ⟨mid.val + 1, by
          have := (g x (Fin.last k)).isLt; omega⟩
        have hxl' : x ≤ l' := fun j ↦ Fin.lastCases
          (by simp only [l', x, liftSlicePoint, Fin.snoc_last, Function.update_self]
              exact Fin.le_def.mpr (Nat.le_succ _))
          (fun i ↦ by simp [l', Fin.castSucc_ne_last]) j
        have hl'u : l' ≤ u := fun j ↦ Fin.lastCases
          (by have hgu_last : (g x (Fin.last k)).val ≤ (u (Fin.last k)).val := hgxu (Fin.last k)
              simp only [l', Function.update_self]
              exact Fin.le_def.mpr (Nat.succ_le_of_lt (lt_of_lt_of_le hpos_val hgu_last)))
          (fun i ↦ by simpa [l', Fin.castSucc_ne_last] using hxu i.castSucc) j
        have hl'_gl' : l' ≤ g l' := by
          have hl'_gx : l' ≤ g x := fun j ↦ Fin.lastCases
            (by simp only [l', Function.update_self]
                exact Fin.le_def.mpr (Nat.succ_le_of_lt hpos_val))
            (fun i ↦ by simpa [l', Fin.castSucc_ne_last, x, liftSlicePoint, initCoords]
              using hclamp_le i) j
          exact hl'_gx.trans (hg hxl')
        obtain ⟨ih1, ih2, ih3, ih4, ih5⟩ := ih l' u hl'u hl'_gl' hgu
        have hgap : (u (Fin.last k)).val - (l' (Fin.last k)).val ≤
            ((u (Fin.last k)).val - (l (Fin.last k)).val) / 2 := by
          simp only [l', Function.update_self, mid]; omega
        have hdiv : ((u (Fin.last k)).val - (l' (Fin.last k)).val) / 2 ^ t ≤
            ((u (Fin.last k)).val - (l (Fin.last k)).val) / 2 ^ (t + 1) := by
          calc ((u (Fin.last k)).val - (l' (Fin.last k)).val) / 2 ^ t
              ≤ (((u (Fin.last k)).val - (l (Fin.last k)).val) / 2) / 2 ^ t :=
                Nat.div_le_div_right hgap
            _ = ((u (Fin.last k)).val - (l (Fin.last k)).val) / (2 * 2 ^ t) :=
                Nat.div_div_eq_div_mul _ _ _
            _ = ((u (Fin.last k)).val - (l (Fin.last k)).val) / 2 ^ (t + 1) := by
                rw [Nat.pow_succ']
        refine ⟨ih1, ih2, ih3, ih4.trans hdiv, ?_⟩
        calc queryCount (TarskiGridQuery.oracleOf g)
              (algStar.liftM (sliceMidQueryHandler l u mid)) +
              (1 + queryCount (TarskiGridQuery.oracleOf g) (bisectHypergridLoop algStar t l' u))
            ≤ Q_star + (1 + t * (Q_star + 1)) :=
              Nat.add_le_add hcnt_lift (Nat.add_le_add_left ih5 1)
          _ = (t + 1) * (Q_star + 1) := by rw [Nat.succ_mul]; omega
      · rw [dite_eq_right hpos]
        have hsol_neg : initCoords (g x) ≤ y := by
          rcases hsol_y with ⟨_, hp⟩ | ⟨hle, _⟩
          · exfalso; dsimp only [sliceMidUpDown] at hp; rw [ite_eq_right hpos] at hp; cases hp
          · exact hle
        have hle_clamp : initCoords (g x) ≤ clampHyperbox (initCoords l) (initCoords u) y :=
          le_clampHyperbox_of_le (fun i ↦ hgxu i.castSucc) hsol_neg
        have hgx_le_x : g x ≤ x := fun j ↦ Fin.lastCases
          (by simpa [x, liftSlicePoint] using le_of_not_gt hpos)
          (fun i ↦ by simpa [x, liftSlicePoint, initCoords] using hle_clamp i) j
        obtain ⟨ih1, ih2, ih3, ih4, ih5⟩ := ih l x hlx hlg hgx_le_x
        have hgap : (x (Fin.last k)).val - (l (Fin.last k)).val ≤
            ((u (Fin.last k)).val - (l (Fin.last k)).val) / 2 := by
          simp only [x, liftSlicePoint, Fin.snoc_last, mid]; omega
        have hdiv : ((x (Fin.last k)).val - (l (Fin.last k)).val) / 2 ^ t ≤
            ((u (Fin.last k)).val - (l (Fin.last k)).val) / 2 ^ (t + 1) := by
          calc ((x (Fin.last k)).val - (l (Fin.last k)).val) / 2 ^ t
              ≤ (((u (Fin.last k)).val - (l (Fin.last k)).val) / 2) / 2 ^ t :=
                Nat.div_le_div_right hgap
            _ = ((u (Fin.last k)).val - (l (Fin.last k)).val) / (2 * 2 ^ t) :=
                Nat.div_div_eq_div_mul _ _ _
            _ = ((u (Fin.last k)).val - (l (Fin.last k)).val) / 2 ^ (t + 1) := by
                rw [Nat.pow_succ']
        refine ⟨ih1, ih2, ih3, ih4.trans hdiv, ?_⟩
        calc queryCount (TarskiGridQuery.oracleOf g)
              (algStar.liftM (sliceMidQueryHandler l u mid)) +
              (1 + queryCount (TarskiGridQuery.oracleOf g) (bisectHypergridLoop algStar t l x))
            ≤ Q_star + (1 + t * (Q_star + 1)) :=
              Nat.add_le_add hcnt_lift (Nat.add_le_add_left ih5 1)
          _ = (t + 1) * (Q_star + 1) := by rw [Nat.succ_mul]; omega
    · rw [dite_eq_right hlt, evalOracle_pure, queryCount_pure]
      have hle_val : (u (Fin.last k)).val ≤ (l (Fin.last k)).val := le_of_not_gt hlt
      have hsub_zero : (u (Fin.last k)).val - (l (Fin.last k)).val = 0 := by omega
      refine ⟨hlu, hlg, hgu, ?_, Nat.zero_le _⟩
      dsimp only
      rw [hsub_zero, Nat.zero_div]

private def baseSliceHandler {n k : ℕ} (l u : Hypergrid n (k + 1)) (c : Fin n) :
    {ι : Type} → TarskiGridQuery n k ι → FreeM (TarskiGridQuery n (k + 1)) ι
  | _, .query y' => do
    let gz ← TarskiGridQuery.ask (Fin.snoc (clampHyperbox (initCoords l) (initCoords u) y') c)
    pure (initCoords gz)

/-- Slice-bisection reduction computing a fixed point on `Hypergrid n (k + 1)` from a
`k`-dimensional up-or-down solver and a `k`-dimensional fixed-point solver. -/
def reduceTarskiSliceBisect {n k : ℕ} [NeZero n]
    (algStar : FreeM (TarskiUpDownQuery n k) (Hypergrid n k))
    (algBase : FreeM (TarskiGridQuery n k) (Hypergrid n k)) :
    FreeM (TarskiGridQuery n (k + 1)) (Hypergrid n (k + 1)) := do
  let lu ← bisectHypergridLoop algStar (Nat.log 2 n + 1) ⊥ ⊤
  let c := lu.1 (Fin.last k)
  let y ← algBase.liftM (baseSliceHandler lu.1 lu.2 c)
  pure (Fin.snoc y c)

/-- Slice-bisection finds a genuine fixed point in at most
`(Nat.log 2 n + 1) * (Q_star + 1) + Q_base` queries. -/
theorem reduceTarskiSliceBisect_spec {n k : ℕ} [NeZero n]
    {algStar : FreeM (TarskiUpDownQuery n k) (Hypergrid n k)} {Q_star : ℕ}
    (hStar : ∀ F : TarskiUpDownFn n k, IsMonotoneUpDown F →
      IsUpDownSol F (evalOracle (TarskiUpDownQuery.oracleOf F) algStar) ∧
      queryCount (TarskiUpDownQuery.oracleOf F) algStar ≤ Q_star)
    {algBase : FreeM (TarskiGridQuery n k) (Hypergrid n k)} {Q_base : ℕ}
    (hBase : ∀ h : Hypergrid n k → Hypergrid n k, Monotone h →
      Function.IsFixedPt h (evalOracle (TarskiGridQuery.oracleOf h) algBase) ∧
      queryCount (TarskiGridQuery.oracleOf h) algBase ≤ Q_base) :
    ∀ g : Hypergrid n (k + 1) → Hypergrid n (k + 1), Monotone g →
      Function.IsFixedPt g
        (evalOracle (TarskiGridQuery.oracleOf g) (reduceTarskiSliceBisect algStar algBase)) ∧
      queryCount (TarskiGridQuery.oracleOf g) (reduceTarskiSliceBisect algStar algBase) ≤
        (Nat.log 2 n + 1) * (Q_star + 1) + Q_base := by
  intro g hg
  set T := Nat.log 2 n + 1
  obtain ⟨hlu, hlg, hgu, hgap, hcnt_bi⟩ :=
    bisectHypergridLoop_spec hStar hg T ⊥ ⊤ bot_le bot_le le_top
  set lu := evalOracle (TarskiGridQuery.oracleOf g) (bisectHypergridLoop algStar T ⊥ ⊤)
  have hpow_gt : n < 2 ^ T := Nat.lt_pow_succ_log_self (by decide : 1 < 2) n
  have htop_val : ((⊤ : Hypergrid n (k + 1)) (Fin.last k)).val -
      ((⊥ : Hypergrid n (k + 1)) (Fin.last k)).val < 2 ^ T := by
    have := ((⊤ : Hypergrid n (k + 1)) (Fin.last k)).isLt; omega
  rw [Nat.div_eq_of_lt htop_val] at hgap
  have hlast_eq : lu.1 (Fin.last k) = lu.2 (Fin.last k) := by
    apply Fin.ext
    have hle_last : (lu.1 (Fin.last k)).val ≤ (lu.2 (Fin.last k)).val := hlu (Fin.last k)
    omega
  set c := lu.1 (Fin.last k)
  let gRed : Hypergrid n k → Hypergrid n k := fun y ↦
    initCoords (g (Fin.snoc (clampHyperbox (initCoords lu.1) (initCoords lu.2) y) c))
  have hgRed_mono : Monotone gRed := by
    intro y₁ y₂ hy i
    refine hg (fun j ↦ Fin.lastCases (by simp) (fun m ↦ ?_) j) i.castSucc
    simpa only [Fin.snoc_castSucc] using clampHyperbox_mono (initCoords lu.1) (initCoords lu.2) hy m
  obtain ⟨hfix_y, hcnt_base⟩ := hBase gRed hgRed_mono
  set y := evalOracle (TarskiGridQuery.oracleOf gRed) algBase
  have hor_eq : (fun {ι} (op : TarskiGridQuery n k ι) ↦
      evalOracle (TarskiGridQuery.oracleOf g) (baseSliceHandler lu.1 lu.2 c op)) =
      @TarskiGridQuery.oracleOf n k gRed := by
    funext ι op; cases op; rfl
  have heval_base :
      evalOracle (TarskiGridQuery.oracleOf g) (algBase.liftM (baseSliceHandler lu.1 lu.2 c)) = y :=
    by rw [evalOracle_liftM, hor_eq]
  have hcnt_lift :
      queryCount (TarskiGridQuery.oracleOf g) (algBase.liftM (baseSliceHandler lu.1 lu.2 c)) ≤
        Q_base := by
    have hle := queryCount_liftM_le algBase (baseSliceHandler lu.1 lu.2 c)
      (TarskiGridQuery.oracleOf g) (c := 1) fun {ι} op ↦ by cases op; simp [baseSliceHandler]
    rw [hor_eq, Nat.one_mul] at hle
    exact hle.trans hcnt_base
  set yClamp := clampHyperbox (initCoords lu.1) (initCoords lu.2) y
  obtain ⟨hcl, hcu⟩ := clampHyperbox_mem (fun i ↦ hlu i.castSucc) y
  have hzc_mem : lu.1 ≤ Fin.snoc yClamp c ∧ Fin.snoc yClamp c ≤ lu.2 :=
    ⟨fun j ↦ Fin.lastCases (by simp [c]) (fun i ↦ by rw [Fin.snoc_castSucc]; exact hcl i) j,
     fun j ↦ Fin.lastCases (by simp [c, hlast_eq])
       (fun i ↦ by rw [Fin.snoc_castSucc]; exact hcu i) j⟩
  have hgz_mem : lu.1 ≤ g (Fin.snoc yClamp c) ∧ g (Fin.snoc yClamp c) ≤ lu.2 :=
    ⟨hlg.trans (hg hzc_mem.1), (hg hzc_mem.2).trans hgu⟩
  have hyClamp_eq : yClamp = y := clampHyperbox_eq_of_mem
    (by rw [← hfix_y]; exact fun i ↦ hgz_mem.1 i.castSucc)
    (by rw [← hfix_y]; exact fun i ↦ hgz_mem.2 i.castSucc)
  dsimp only [reduceTarskiSliceBisect]
  rw [evalOracle_bind, queryCount_bind, evalOracle_bind, queryCount_bind, heval_base,
    evalOracle_pure, queryCount_pure]
  refine ⟨?_, ?_⟩
  · change g (Fin.snoc y c) = Fin.snoc y c
    rw [← hyClamp_eq]
    funext j
    refine Fin.lastCases ?_ (fun i ↦ ?_) j
    · simp only [Fin.snoc_last]
      exact le_antisymm (hlast_eq ▸ hgz_mem.2 (Fin.last k)) (hgz_mem.1 (Fin.last k))
    · simp only [Fin.snoc_castSucc]
      exact (congr_fun hfix_y i).trans (congr_fun hyClamp_eq.symm i)
  · calc queryCount (TarskiGridQuery.oracleOf g) (bisectHypergridLoop algStar T ⊥ ⊤) +
          (queryCount (TarskiGridQuery.oracleOf g)
            (algBase.liftM (baseSliceHandler lu.1 lu.2 c)) + 0)
        ≤ T * (Q_star + 1) + (Q_base + 0) :=
          Nat.add_le_add hcnt_bi (Nat.add_le_add hcnt_lift le_rfl)
      _ = T * (Q_star + 1) + Q_base := rfl

/-! ## Product Decomposition for Monotone Up-or-Down Search -/

/-- Project `Hypergrid n (a + b)` onto its first `a` coordinates. -/
def fstBlock {n a b : ℕ} (z : Hypergrid n (a + b)) : Hypergrid n a :=
  fun i ↦ z (Fin.castAdd b i)

/-- Project `Hypergrid n (a + b)` onto its last `b` coordinates. -/
def sndBlock {n a b : ℕ} (z : Hypergrid n (a + b)) : Hypergrid n b :=
  fun j ↦ z (Fin.natAdd a j)

/-- Concatenate points `x : Hypergrid n a` and `y : Hypergrid n b` into `Hypergrid n (a + b)`. -/
def concatBlocks {n a b : ℕ} (x : Hypergrid n a) (y : Hypergrid n b) :
    Hypergrid n (a + b) :=
  Fin.append x y

theorem concatBlocks_mono {n a b : ℕ} {x₁ x₂ : Hypergrid n a} {y₁ y₂ : Hypergrid n b}
    (hx : x₁ ≤ x₂) (hy : y₁ ≤ y₂) : concatBlocks x₁ y₁ ≤ concatBlocks x₂ y₂ := by
  intro k
  refine Fin.addCases (fun i ↦ by simpa [concatBlocks] using hx i)
    (fun j ↦ by simpa [concatBlocks] using hy j) k

/-- Increment coordinate `i` of `x` by `1`, clamped at `n - 1`. -/
def stepCoordUp {n k : ℕ} [NeZero n] (x : Hypergrid n k) (i : Fin k) : Hypergrid n k :=
  Function.update x i ⟨min ((x i).val + 1) (n - 1), by
    have := Nat.pos_of_ne_zero (NeZero.ne n); omega⟩

/-- Decrement coordinate `i` of `x` by `1`, clamped at `0`. -/
def stepCoordDown {n k : ℕ} (x : Hypergrid n k) (i : Fin k) : Hypergrid n k :=
  Function.update x i ⟨(x i).val - 1, by have := (x i).isLt; omega⟩

/-- Witness accumulator maintaining cross-ordered postfixed and prefixed fiber points. -/
structure FiberWitnessState (n a b : ℕ) : Type where
  /-- Recorded pairs `(x, y)` with `y ≤ H_B(x, y)`. -/
  posts : List (Hypergrid n a × Hypergrid n b)
  /-- Recorded pairs `(x, y)` with `H_B(x, y) ≤ y`. -/
  pres : List (Hypergrid n a × Hypergrid n b)

namespace FiberWitnessState

/-- Inclusion order on recorded witness lists. -/
def Subset {n a b : ℕ} (s₁ s₂ : FiberWitnessState n a b) : Prop :=
  s₁.posts ⊆ s₂.posts ∧ s₁.pres ⊆ s₂.pres

theorem subset_refl {n a b : ℕ} (s : FiberWitnessState n a b) : s.Subset s :=
  ⟨List.Subset.refl _, List.Subset.refl _⟩

theorem subset_trans {n a b : ℕ} {s₁ s₂ s₃ : FiberWitnessState n a b}
    (h12 : s₁.Subset s₂) (h23 : s₂.Subset s₃) : s₁.Subset s₃ :=
  ⟨List.Subset.trans h12.1 h23.1, List.Subset.trans h12.2 h23.2⟩

/-- Validity invariant ensuring `[lowerBound, upperBound]` is a nonempty `H_B`-invariant box. -/
def Valid {n a b : ℕ} (H : TarskiUpDownFn n (a + b)) (st : FiberWitnessState n a b) : Prop :=
  (∀ p ∈ st.posts, p.2 ≤ sndBlock (H (concatBlocks p.1 p.2)).1) ∧
  (∀ q ∈ st.pres, sndBlock (H (concatBlocks q.1 q.2)).1 ≤ q.2) ∧
  (∀ p ∈ st.posts, ∀ q ∈ st.pres, p.1 ≤ q.1 → p.2 ≤ q.2)

/-- Lower fiber bound `⊔ { y | (x', y) ∈ posts, x' ≤ x }`. -/
def lowerBound {n a b : ℕ} [NeZero n] (st : FiberWitnessState n a b) (x : Hypergrid n a) :
    Hypergrid n b :=
  (st.posts.filter fun p ↦ decide (p.1 ≤ x)).foldr (fun p acc ↦ p.2 ⊔ acc) ⊥

/-- Upper fiber bound `⊓ { y | (x', y) ∈ pres, x ≤ x' }`. -/
def upperBound {n a b : ℕ} [NeZero n] (st : FiberWitnessState n a b) (x : Hypergrid n a) :
    Hypergrid n b :=
  (st.pres.filter fun q ↦ decide (x ≤ q.1)).foldr (fun q acc ↦ q.2 ⊓ acc) ⊤

private theorem foldr_sup_ge_mem {α β : Type*} [SemilatticeSup β] [OrderBot β]
    (f : α → β) : ∀ (l : List α) {p : α}, p ∈ l → f p ≤ l.foldr (fun a acc ↦ f a ⊔ acc) ⊥
  | [], _, hp => absurd hp List.not_mem_nil
  | a :: tl, p, hp => by
    rcases List.mem_cons.mp hp with rfl | htl
    · exact le_sup_left
    · exact (foldr_sup_ge_mem f tl htl).trans le_sup_right

private theorem foldr_inf_le_mem {α β : Type*} [SemilatticeInf β] [OrderTop β]
    (f : α → β) : ∀ (l : List α) {q : α}, q ∈ l → l.foldr (fun a acc ↦ f a ⊓ acc) ⊤ ≤ f q
  | [], _, hq => absurd hq List.not_mem_nil
  | a :: tl, q, hq => by
    rcases List.mem_cons.mp hq with rfl | htl
    · exact inf_le_left
    · exact inf_le_right.trans (foldr_inf_le_mem f tl htl)

private theorem foldr_sup_le_of_forall {α β : Type*} [SemilatticeSup β] [OrderBot β]
    (f : α → β) {u : β} :
    ∀ (l : List α), (∀ a ∈ l, f a ≤ u) → l.foldr (fun a acc ↦ f a ⊔ acc) ⊥ ≤ u
  | [], _ => bot_le
  | a :: tl, h =>
    sup_le (h a List.mem_cons_self)
      (foldr_sup_le_of_forall f tl fun z hz ↦ h z (List.mem_cons_of_mem a hz))

private theorem le_foldr_inf_of_forall {α β : Type*} [SemilatticeInf β] [OrderTop β]
    (f : α → β) {v : β} :
    ∀ (l : List α), (∀ a ∈ l, v ≤ f a) → v ≤ l.foldr (fun a acc ↦ f a ⊓ acc) ⊤
  | [], _ => le_top
  | a :: tl, h =>
    le_inf (h a List.mem_cons_self)
      (le_foldr_inf_of_forall f tl fun z hz ↦ h z (List.mem_cons_of_mem a hz))

theorem mem_posts_le_lowerBound {n a b : ℕ} [NeZero n] {st : FiberWitnessState n a b}
    {p : Hypergrid n a × Hypergrid n b} {x : Hypergrid n a}
    (hp : p ∈ st.posts) (hpx : p.1 ≤ x) : p.2 ≤ st.lowerBound x :=
  foldr_sup_ge_mem Prod.snd _ (List.mem_filter.mpr ⟨hp, decide_eq_true hpx⟩)

theorem upperBound_le_mem_pres {n a b : ℕ} [NeZero n] {st : FiberWitnessState n a b}
    {q : Hypergrid n a × Hypergrid n b} {x : Hypergrid n a}
    (hq : q ∈ st.pres) (hxq : x ≤ q.1) : st.upperBound x ≤ q.2 :=
  foldr_inf_le_mem Prod.snd _ (List.mem_filter.mpr ⟨hq, decide_eq_true hxq⟩)

theorem lowerBound_mono {n a b : ℕ} [NeZero n] (st : FiberWitnessState n a b) :
    Monotone st.lowerBound := by
  intro x₁ x₂ hx
  refine foldr_sup_le_of_forall Prod.snd _ fun p hp ↦ ?_
  obtain ⟨hp_in, hpx₁⟩ := List.mem_filter.mp hp
  exact mem_posts_le_lowerBound hp_in ((of_decide_eq_true hpx₁).trans hx)

theorem lowerBound_le_upperBound {n a b : ℕ} [NeZero n] {H : TarskiUpDownFn n (a + b)}
    {st : FiberWitnessState n a b} (hv : st.Valid H) (x : Hypergrid n a) :
    st.lowerBound x ≤ st.upperBound x := by
  refine foldr_sup_le_of_forall Prod.snd _ fun p hp ↦ ?_
  obtain ⟨hp_in, hpx⟩ := List.mem_filter.mp hp
  refine le_foldr_inf_of_forall Prod.snd _ fun q hq ↦ ?_
  obtain ⟨hq_in, hxq⟩ := List.mem_filter.mp hq
  exact hv.2.2 p hp_in q hq_in ((of_decide_eq_true hpx).trans (of_decide_eq_true hxq))

theorem lowerBound_postfixed {n a b : ℕ} [NeZero n] {H : TarskiUpDownFn n (a + b)}
    (hH : IsMonotoneUpDown H) {st : FiberWitnessState n a b} (hv : st.Valid H)
    (x : Hypergrid n a) :
    st.lowerBound x ≤ sndBlock (H (concatBlocks x (st.lowerBound x))).1 := by
  refine foldr_sup_le_of_forall Prod.snd _ fun p hp ↦ ?_
  obtain ⟨hp_in, hpx⟩ := List.mem_filter.mp hp
  have hpx' : p.1 ≤ x := of_decide_eq_true hpx
  have hp_le_L : p.2 ≤ st.lowerBound x := mem_posts_le_lowerBound hp_in hpx'
  exact (hv.1 p hp_in).trans fun j ↦ hH.1 (concatBlocks_mono hpx' hp_le_L) (Fin.natAdd a j)

theorem upperBound_prefixed {n a b : ℕ} [NeZero n] {H : TarskiUpDownFn n (a + b)}
    (hH : IsMonotoneUpDown H) {st : FiberWitnessState n a b} (hv : st.Valid H)
    (x : Hypergrid n a) :
    sndBlock (H (concatBlocks x (st.upperBound x))).1 ≤ st.upperBound x := by
  refine le_foldr_inf_of_forall Prod.snd _ fun q hq ↦ ?_
  obtain ⟨hq_in, hxq⟩ := List.mem_filter.mp hq
  have hxq' : x ≤ q.1 := of_decide_eq_true hxq
  have hU_le_q : st.upperBound x ≤ q.2 := upperBound_le_mem_pres hq_in hxq'
  exact le_trans (fun j ↦ hH.1 (concatBlocks_mono hxq' hU_le_q) (Fin.natAdd a j)) (hv.2.1 q hq_in)

/-- Kleene least fixed point of `y ↦ H_B(x, y)` inside `[st.lowerBound x, st.upperBound x]`. -/
def idealFiber {n a b : ℕ} [NeZero n] (H : TarskiUpDownFn n (a + b))
    (st : FiberWitnessState n a b) (x : Hypergrid n a) : Hypergrid n b :=
  ((fun y ↦ sndBlock (H (concatBlocks x y)).1)^[Fintype.card (Hypergrid n b)]) (st.lowerBound x)

theorem idealFiber_bounds {n a b : ℕ} [NeZero n] {H : TarskiUpDownFn n (a + b)}
    (hH : IsMonotoneUpDown H) {st : FiberWitnessState n a b} (hv : st.Valid H)
    (x : Hypergrid n a) :
    st.lowerBound x ≤ st.idealFiber H x ∧ st.idealFiber H x ≤ st.upperBound x := by
  let gx : Hypergrid n b → Hypergrid n b := fun y ↦ sndBlock (H (concatBlocks x y)).1
  have hgx_mono : Monotone gx := fun y₁ y₂ hy j ↦
    hH.1 (concatBlocks_mono le_rfl hy) (Fin.natAdd a j)
  suffices h : ∀ t : ℕ,
      st.lowerBound x ≤ (gx^[t]) (st.lowerBound x) ∧
      (gx^[t]) (st.lowerBound x) ≤ (gx^[t + 1]) (st.lowerBound x) ∧
      (gx^[t]) (st.lowerBound x) ≤ st.upperBound x by
    obtain ⟨hl, -, hu⟩ := h (Fintype.card (Hypergrid n b))
    exact ⟨hl, hu⟩
  intro t
  induction t with
  | zero =>
    simp only [Function.iterate_zero, id_eq]
    exact ⟨le_rfl, lowerBound_postfixed hH hv x, lowerBound_le_upperBound hv x⟩
  | succ t ih =>
    obtain ⟨hl, hstep, hu⟩ := ih
    have hnext_u : (gx^[t + 1]) (st.lowerBound x) ≤ st.upperBound x := by
      rw [Function.iterate_succ_apply']
      exact (hgx_mono hu).trans (upperBound_prefixed hH hv x)
    have hstep' : (gx^[t]) (st.lowerBound x) ≤ gx ((gx^[t]) (st.lowerBound x)) := by
      simpa only [Function.iterate_succ_apply'] using hstep
    refine ⟨hl.trans hstep, ?_, hnext_u⟩
    rw [Function.iterate_succ_apply' gx (t + 1), Function.iterate_succ_apply' gx t]
    exact hgx_mono hstep'

theorem idealFiber_mono {n a b : ℕ} [NeZero n] {H : TarskiUpDownFn n (a + b)}
    (hH : IsMonotoneUpDown H) (st : FiberWitnessState n a b) :
    Monotone (st.idealFiber H) := by
  intro x₁ x₂ hx
  suffices h : ∀ t : ℕ,
      ((fun y ↦ sndBlock (H (concatBlocks x₁ y)).1)^[t]) (st.lowerBound x₁) ≤
      ((fun y ↦ sndBlock (H (concatBlocks x₂ y)).1)^[t]) (st.lowerBound x₂) from
    h (Fintype.card (Hypergrid n b))
  intro t
  induction t with
  | zero => exact lowerBound_mono st hx
  | succ t ih =>
    simp only [Function.iterate_succ_apply']
    exact fun j ↦ hH.1 (concatBlocks_mono hx ih) (Fin.natAdd a j)

/-- Globally monotone outer function induced by `st.idealFiber H`. -/
def idealOuterFn {n a b : ℕ} [NeZero n] (H : TarskiUpDownFn n (a + b))
    (st : FiberWitnessState n a b) : TarskiUpDownFn n a :=
  fun x ↦
    let hz := H (concatBlocks x (st.idealFiber H x))
    (fstBlock hz.1, hz.2)

theorem isMonotoneUpDown_idealOuterFn {n a b : ℕ} [NeZero n] {H : TarskiUpDownFn n (a + b)}
    (hH : IsMonotoneUpDown H) (st : FiberWitnessState n a b) :
    IsMonotoneUpDown (st.idealOuterFn H) :=
  ⟨fun _ _ hx i ↦ hH.1 (concatBlocks_mono hx (idealFiber_mono hH st hx)) (Fin.castAdd b i),
   fun _ _ hx ↦ hH.2 (concatBlocks_mono hx (idealFiber_mono hH st hx))⟩

end FiberWitnessState

private def innerFiberHandler {n a b : ℕ} (x : Hypergrid n a) (L U : Hypergrid n b)
    (test : Hypergrid n (a + b) × UpDownSign → UpDownSign) :
    {ι : Type} → TarskiUpDownQuery n b ι → FreeM (TarskiUpDownQuery n (a + b)) ι
  | _, .query y' => do
    let hz ← TarskiUpDownQuery.ask (concatBlocks x (clampHyperbox L U y'))
    pure (sndBlock hz.1, test hz)

/-- Evaluate one monotone fiber predicate `test` by running `algB` clamped to `[L(x), U(x)]`. -/
def runFiberCheck {n a b : ℕ} [NeZero n]
    (algB : FreeM (TarskiUpDownQuery n b) (Hypergrid n b))
    (x : Hypergrid n a) (st : FiberWitnessState n a b)
    (test : Hypergrid n (a + b) × UpDownSign → UpDownSign) :
    FreeM (TarskiUpDownQuery n (a + b))
      (UpDownSign × Hypergrid n b × FiberWitnessState n a b) := do
  let L := st.lowerBound x
  let U := st.upperBound x
  let y₀ ← algB.liftM (innerFiberHandler x L U test)
  let y := clampHyperbox L U y₀
  let hz ← TarskiUpDownQuery.ask (concatBlocks x y)
  match test hz with
  | .pos => pure (.pos, y, ⟨(x, y) :: st.posts, st.pres⟩)
  | .neg => pure (.neg, y, ⟨st.posts, (x, y) :: st.pres⟩)

private theorem runFiberCheck_spec {n a b : ℕ} [NeZero n]
    {algB : FreeM (TarskiUpDownQuery n b) (Hypergrid n b)} {Q_b : ℕ}
    (hB : ∀ G : TarskiUpDownFn n b, IsMonotoneUpDown G →
      IsUpDownSol G (evalOracle (TarskiUpDownQuery.oracleOf G) algB) ∧
      queryCount (TarskiUpDownQuery.oracleOf G) algB ≤ Q_b)
    {H : TarskiUpDownFn n (a + b)} (hH : IsMonotoneUpDown H)
    {x : Hypergrid n a} {st : FiberWitnessState n a b} (hv : st.Valid H)
    {test : Hypergrid n (a + b) × UpDownSign → UpDownSign}
    (htest : ∀ ⦃u₁ u₂ : Hypergrid n (a + b) × UpDownSign⦄,
      u₁.1 ≤ u₂.1 → u₁.2 ≤ u₂.2 → test u₁ ≤ test u₂) :
    queryCount (TarskiUpDownQuery.oracleOf H) (runFiberCheck algB x st test) ≤ Q_b + 1 ∧
    st.Subset (evalOracle (TarskiUpDownQuery.oracleOf H) (runFiberCheck algB x st test)).2.2 ∧
    (evalOracle (TarskiUpDownQuery.oracleOf H) (runFiberCheck algB x st test)).2.2.Valid H ∧
    (((evalOracle (TarskiUpDownQuery.oracleOf H) (runFiberCheck algB x st test)).1 = .pos ∧
        (evalOracle (TarskiUpDownQuery.oracleOf H) (runFiberCheck algB x st test)).2.1 ≤
          sndBlock (H (concatBlocks x
            (evalOracle (TarskiUpDownQuery.oracleOf H) (runFiberCheck algB x st test)).2.1)).1 ∧
        test (H (concatBlocks x
          (evalOracle (TarskiUpDownQuery.oracleOf H) (runFiberCheck algB x st test)).2.1)) =
          .pos) ∨
      ((evalOracle (TarskiUpDownQuery.oracleOf H) (runFiberCheck algB x st test)).1 = .neg ∧
        sndBlock (H (concatBlocks x
          (evalOracle (TarskiUpDownQuery.oracleOf H) (runFiberCheck algB x st test)).2.1)).1 ≤
          (evalOracle (TarskiUpDownQuery.oracleOf H) (runFiberCheck algB x st test)).2.1 ∧
        test (H (concatBlocks x
          (evalOracle (TarskiUpDownQuery.oracleOf H) (runFiberCheck algB x st test)).2.1)) =
          .neg)) ∧
    (∀ stf : FiberWitnessState n a b,
      (evalOracle (TarskiUpDownQuery.oracleOf H) (runFiberCheck algB x st test)).2.2.Subset stf →
      stf.Valid H →
      (evalOracle (TarskiUpDownQuery.oracleOf H) (runFiberCheck algB x st test)).1 =
        test (H (concatBlocks x (stf.idealFiber H x)))) := by
  set L := st.lowerBound x
  set U := st.upperBound x
  have hLU : L ≤ U := FiberWitnessState.lowerBound_le_upperBound hv x
  have hL_post := FiberWitnessState.lowerBound_postfixed hH hv x
  have hU_pre := FiberWitnessState.upperBound_prefixed hH hv x
  let G : TarskiUpDownFn n b := fun y' ↦
    let hz := H (concatBlocks x (clampHyperbox L U y'))
    (sndBlock hz.1, test hz)
  have hG_mono : IsMonotoneUpDown G :=
    ⟨fun _ _ hy j ↦ hH.1 (concatBlocks_mono le_rfl (clampHyperbox_mono L U hy)) (Fin.natAdd a j),
     fun _ _ hy ↦
       let hle := concatBlocks_mono (x₁ := x) le_rfl (clampHyperbox_mono L U hy)
       htest (hH.1 hle) (hH.2 hle)⟩
  obtain ⟨hsol_y₀, hcnt_y₀⟩ := hB G hG_mono
  set y₀ := evalOracle (TarskiUpDownQuery.oracleOf G) algB
  set y := clampHyperbox L U y₀
  obtain ⟨hLy, hyU⟩ := clampHyperbox_mem hLU y₀
  have hgy_L : L ≤ sndBlock (H (concatBlocks x y)).1 :=
    hL_post.trans fun j ↦ hH.1 (concatBlocks_mono (x₁ := x) le_rfl hLy) (Fin.natAdd a j)
  have hgy_U : sndBlock (H (concatBlocks x y)).1 ≤ U :=
    le_trans (fun j ↦ hH.1 (concatBlocks_mono (x₁ := x) le_rfl hyU) (Fin.natAdd a j)) hU_pre
  have hor_eq : (fun {ι} (op : TarskiUpDownQuery n b ι) ↦
      evalOracle (TarskiUpDownQuery.oracleOf H) (innerFiberHandler x L U test op)) =
      @TarskiUpDownQuery.oracleOf n b G := by
    funext ι op; cases op; rfl
  have heval_lift :
      evalOracle (TarskiUpDownQuery.oracleOf H) (algB.liftM (innerFiberHandler x L U test)) = y₀ :=
    by rw [evalOracle_liftM, hor_eq]
  have hcnt_lift :
      queryCount (TarskiUpDownQuery.oracleOf H) (algB.liftM (innerFiberHandler x L U test)) ≤
        Q_b := by
    have hle := queryCount_liftM_le algB (innerFiberHandler x L U test)
      (TarskiUpDownQuery.oracleOf H) (c := 1) fun {ι} op ↦ by cases op; simp [innerFiberHandler]
    rw [hor_eq, Nat.one_mul] at hle
    exact hle.trans hcnt_y₀
  dsimp only [runFiberCheck]
  rw [evalOracle_bind, queryCount_bind, heval_lift, evalOracle_bind, queryCount_bind,
    evalOracle_lift, queryCount_lift]
  dsimp only [TarskiUpDownQuery.oracleOf]
  rcases hsol_y₀ with ⟨hy₀_ge, hpos⟩ | ⟨hy₀_le, hneg⟩
  · have ht_eq : test (H (concatBlocks x y)) = .pos := hpos
    have hy_post : y ≤ sndBlock (H (concatBlocks x y)).1 := clampHyperbox_le_of_le hgy_L hy₀_ge
    rw [ht_eq, evalOracle_pure, queryCount_pure]
    dsimp only
    have hval' : (FiberWitnessState.mk ((x, y) :: st.posts) st.pres).Valid H :=
      ⟨fun p hp ↦ by
        rcases List.mem_cons.mp hp with rfl | h₀
        · exact hy_post
        · exact hv.1 p h₀,
       hv.2.1,
       fun p hp q hq hpq ↦ by
        rcases List.mem_cons.mp hp with rfl | h₀
        · exact hyU.trans (FiberWitnessState.upperBound_le_mem_pres hq hpq)
        · exact hv.2.2 p h₀ q hq hpq⟩
    refine ⟨Nat.add_le_add hcnt_lift (le_refl 1),
      ⟨List.subset_cons_self _ _, List.Subset.refl _⟩, hval',
      Or.inl ⟨rfl, hy_post, ht_eq⟩, fun stf hsubf hvf ↦ ?_⟩
    have hy_le_fib : y ≤ stf.idealFiber H x :=
      (FiberWitnessState.mem_posts_le_lowerBound (hsubf.1 List.mem_cons_self) le_rfl).trans
        (FiberWitnessState.idealFiber_bounds hH hvf x).1
    have hle_join := concatBlocks_mono (x₁ := x) le_rfl hy_le_fib
    have hle_test := htest (hH.1 hle_join) (hH.2 hle_join)
    rw [ht_eq] at hle_test
    cases hc : test (H (concatBlocks x (stf.idealFiber H x)))
    · rw [hc] at hle_test; exfalso; revert hle_test; decide
    · rfl
  · have ht_eq : test (H (concatBlocks x y)) = .neg := hneg
    have hy_pre : sndBlock (H (concatBlocks x y)).1 ≤ y := le_clampHyperbox_of_le hgy_U hy₀_le
    rw [ht_eq, evalOracle_pure, queryCount_pure]
    dsimp only
    have hval' : (FiberWitnessState.mk st.posts ((x, y) :: st.pres)).Valid H :=
      ⟨hv.1,
       fun q hq ↦ by
        rcases List.mem_cons.mp hq with rfl | h₀
        · exact hy_pre
        · exact hv.2.1 q h₀,
       fun p hp q hq hpq ↦ by
        rcases List.mem_cons.mp hq with rfl | h₀
        · exact (FiberWitnessState.mem_posts_le_lowerBound hp hpq).trans hLy
        · exact hv.2.2 p hp q h₀ hpq⟩
    refine ⟨Nat.add_le_add hcnt_lift (le_refl 1),
      ⟨List.Subset.refl _, List.subset_cons_self _ _⟩, hval',
      Or.inr ⟨rfl, hy_pre, ht_eq⟩, fun stf hsubf hvf ↦ ?_⟩
    have hfib_le_y : stf.idealFiber H x ≤ y :=
      (FiberWitnessState.idealFiber_bounds hH hvf x).2.trans
        (FiberWitnessState.upperBound_le_mem_pres (hsubf.2 List.mem_cons_self) le_rfl)
    have hle_join := concatBlocks_mono (x₁ := x) le_rfl hfib_le_y
    have hle_test := htest (hH.1 hle_join) (hH.2 hle_join)
    rw [ht_eq] at hle_test
    cases hc : test (H (concatBlocks x (stf.idealFiber H x)))
    · rfl
    · rw [hc] at hle_test; exfalso; revert hle_test; decide

/-- Bundle of answers and fiber witnesses produced at an outer point `x ∈ [n]^a`. -/
structure OuterFiberResult (n a b : ℕ) : Type where
  /-- Clamped up-or-down answer at `x`. -/
  ans : Hypergrid n a × UpDownSign
  /-- Fiber witnesses for `x_i ≤ H_A(x, y)_i`. -/
  yGe : Fin a → Hypergrid n b
  /-- Fiber witnesses for `x_i < H_A(x, y)_i`. -/
  yUp : Fin a → Hypergrid n b
  /-- Fiber witness for `H(x, y)_{a+b+1}`. -/
  ySgn : Hypergrid n b
  /-- Updated witness accumulator. -/
  state : FiberWitnessState n a b

/-- Scan coordinates `0, ..., m - 1` at outer point `x`. -/
def scanOuterFiberCoords {n a b : ℕ} [NeZero n]
    (algB : FreeM (TarskiUpDownQuery n b) (Hypergrid n b)) (x : Hypergrid n a) :
    (m : ℕ) → (hm : m ≤ a) → FiberWitnessState n a b →
      FreeM (TarskiUpDownQuery n (a + b))
        (Hypergrid n a × (Fin a → Hypergrid n b) × (Fin a → Hypergrid n b) ×
          FiberWitnessState n a b)
  | 0, _, st => pure (x, fun _ ↦ ⊥, fun _ ↦ ⊤, st)
  | m + 1, hm, st => do
    let prev ← scanOuterFiberCoords algB x m (by omega) st
    let idx : Fin a := ⟨m, hm⟩
    let rUp ← runFiberCheck algB x prev.2.2.2 fun hz ↦
      if x idx < fstBlock hz.1 idx then .pos else .neg
    let rGe ← runFiberCheck algB x rUp.2.2 fun hz ↦
      if x idx ≤ fstBlock hz.1 idx then .pos else .neg
    let val_idx : Fin n :=
      if rUp.1 = .pos then stepCoordUp x idx idx
      else if rGe.1 = .pos then x idx
      else stepCoordDown x idx idx
    pure (Function.update prev.1 idx val_idx,
      Function.update prev.2.1 idx rGe.2.1,
      Function.update prev.2.2.1 idx rUp.2.1,
      rGe.2.2)

/-- Evaluate all `2a + 1` inner fiber checks at `x`. -/
def evalOuterFiber {n a b : ℕ} [NeZero n]
    (algB : FreeM (TarskiUpDownQuery n b) (Hypergrid n b))
    (x : Hypergrid n a) (st : FiberWitnessState n a b) :
    FreeM (TarskiUpDownQuery n (a + b)) (OuterFiberResult n a b) := do
  let coordsRes ← scanOuterFiberCoords algB x a le_rfl st
  let rSgn ← runFiberCheck algB x coordsRes.2.2.2 Prod.snd
  pure ⟨(coordsRes.1, rSgn.1), coordsRes.2.1, coordsRes.2.2.1, rSgn.2.1, rSgn.2.2⟩

private theorem evalOuterFiber_spec {n a b : ℕ} [NeZero n]
    {algB : FreeM (TarskiUpDownQuery n b) (Hypergrid n b)} {Q_b : ℕ}
    (hB : ∀ G : TarskiUpDownFn n b, IsMonotoneUpDown G →
      IsUpDownSol G (evalOracle (TarskiUpDownQuery.oracleOf G) algB) ∧
      queryCount (TarskiUpDownQuery.oracleOf G) algB ≤ Q_b)
    {H : TarskiUpDownFn n (a + b)} (hH : IsMonotoneUpDown H)
    {x : Hypergrid n a} {st : FiberWitnessState n a b} (hv : st.Valid H) :
    queryCount (TarskiUpDownQuery.oracleOf H) (evalOuterFiber algB x st) ≤
      (2 * a + 1) * (Q_b + 1) ∧
    st.Subset (evalOracle (TarskiUpDownQuery.oracleOf H) (evalOuterFiber algB x st)).state ∧
    (evalOracle (TarskiUpDownQuery.oracleOf H) (evalOuterFiber algB x st)).state.Valid H ∧
    (∀ stf : FiberWitnessState n a b,
      (evalOracle (TarskiUpDownQuery.oracleOf H) (evalOuterFiber algB x st)).state.Subset stf →
      stf.Valid H →
      (evalOracle (TarskiUpDownQuery.oracleOf H) (evalOuterFiber algB x st)).ans =
        clampUnitDisp (stf.idealOuterFn H) x ∧
      (IsUpDownSol (stf.idealOuterFn H) x →
        let out := evalOracle (TarskiUpDownQuery.oracleOf H) (evalOuterFiber algB x st)
        IsUpDownSol H (concatBlocks x
          (if out.ans.2 = .pos then Finset.univ.sup out.yGe ⊔ out.ySgn
           else Finset.univ.inf out.yUp ⊓ out.ySgn)))) := by
  have hscan : ∀ (m : ℕ) (hm : m ≤ a),
      queryCount (TarskiUpDownQuery.oracleOf H) (scanOuterFiberCoords algB x m hm st) ≤
        (2 * m) * (Q_b + 1) ∧
      st.Subset (evalOracle (TarskiUpDownQuery.oracleOf H)
        (scanOuterFiberCoords algB x m hm st)).2.2.2 ∧
      (evalOracle (TarskiUpDownQuery.oracleOf H)
        (scanOuterFiberCoords algB x m hm st)).2.2.2.Valid H ∧
      ∀ stf : FiberWitnessState n a b,
        (evalOracle (TarskiUpDownQuery.oracleOf H)
          (scanOuterFiberCoords algB x m hm st)).2.2.2.Subset stf →
        stf.Valid H →
        ∀ i : Fin a, i.val < m →
          let res := evalOracle (TarskiUpDownQuery.oracleOf H)
            (scanOuterFiberCoords algB x m hm st)
          res.1 i = (clampUnitDisp (stf.idealOuterFn H) x).1 i ∧
          (x i ≤ (stf.idealOuterFn H x).1 i →
            res.2.1 i ≤ sndBlock (H (concatBlocks x (res.2.1 i))).1 ∧
            x i ≤ fstBlock (H (concatBlocks x (res.2.1 i))).1 i) ∧
          ((stf.idealOuterFn H x).1 i ≤ x i →
            sndBlock (H (concatBlocks x (res.2.2.1 i))).1 ≤ res.2.2.1 i ∧
            fstBlock (H (concatBlocks x (res.2.2.1 i))).1 i ≤ x i) := by
    intro m hm
    induction m with
    | zero =>
      simp only [scanOuterFiberCoords, evalOracle_pure, queryCount_pure, Nat.mul_zero,
        Nat.zero_mul]
      exact ⟨le_rfl, FiberWitnessState.subset_refl st, hv,
        fun _ _ _ i hi ↦ absurd hi (Nat.not_lt_zero _)⟩
    | succ m ih =>
      obtain ⟨hcnt_m, hsub_m, hval_m, hprop_m⟩ := ih (by omega)
      set prev := evalOracle (TarskiUpDownQuery.oracleOf H)
        (scanOuterFiberCoords algB x m (by omega) st)
      let idx : Fin a := ⟨m, hm⟩
      let testUp : Hypergrid n (a + b) × UpDownSign → UpDownSign := fun hz ↦
        if x idx < fstBlock hz.1 idx then .pos else .neg
      let testGe : Hypergrid n (a + b) × UpDownSign → UpDownSign := fun hz ↦
        if x idx ≤ fstBlock hz.1 idx then .pos else .neg
      have htUp_mono : ∀ ⦃u₁ u₂ : Hypergrid n (a + b) × UpDownSign⦄,
          u₁.1 ≤ u₂.1 → u₁.2 ≤ u₂.2 → testUp u₁ ≤ testUp u₂ := by
        intro u₁ u₂ hu1 _
        have hi : fstBlock u₁.1 idx ≤ fstBlock u₂.1 idx := hu1 (Fin.castAdd b idx)
        dsimp only [testUp]
        split_ifs with h1 h2
        · exact le_rfl
        · exact absurd (lt_of_lt_of_le h1 hi) h2
        · decide
        · exact le_rfl
      have htGe_mono : ∀ ⦃u₁ u₂ : Hypergrid n (a + b) × UpDownSign⦄,
          u₁.1 ≤ u₂.1 → u₁.2 ≤ u₂.2 → testGe u₁ ≤ testGe u₂ := by
        intro u₁ u₂ hu1 _
        have hi : fstBlock u₁.1 idx ≤ fstBlock u₂.1 idx := hu1 (Fin.castAdd b idx)
        dsimp only [testGe]
        split_ifs with h1 h2
        · exact le_rfl
        · exact absurd (h1.trans hi) h2
        · decide
        · exact le_rfl
      obtain ⟨hc_up, hsub_up, hval_up, hbr_up, heq_up⟩ :=
        runFiberCheck_spec hB hH hval_m htUp_mono (x := x)
      set rUp := evalOracle (TarskiUpDownQuery.oracleOf H) (runFiberCheck algB x prev.2.2.2 testUp)
      obtain ⟨hc_ge, hsub_ge, hval_ge, hbr_ge, heq_ge⟩ :=
        runFiberCheck_spec hB hH hval_up htGe_mono (x := x)
      set rGe := evalOracle (TarskiUpDownQuery.oracleOf H) (runFiberCheck algB x rUp.2.2 testGe)
      dsimp only [scanOuterFiberCoords]
      rw [evalOracle_bind, queryCount_bind, evalOracle_bind, queryCount_bind,
        evalOracle_bind, queryCount_bind, evalOracle_pure, queryCount_pure]
      dsimp only
      refine ⟨?_, FiberWitnessState.subset_trans hsub_m
        (FiberWitnessState.subset_trans hsub_up hsub_ge), hval_ge, fun stf hsub_f hvf i hi ↦ ?_⟩
      · have hmul_eq : (2 * (m + 1)) * (Q_b + 1) =
            (2 * m) * (Q_b + 1) + ((Q_b + 1) + ((Q_b + 1) + 0)) := by
          simp only [Nat.mul_add, Nat.add_mul]; omega
        rw [hmul_eq]
        exact Nat.add_le_add hcnt_m (Nat.add_le_add hc_up (Nat.add_le_add hc_ge le_rfl))
      · have hsub_up_f := FiberWitnessState.subset_trans hsub_ge hsub_f
        have hsub_m_f := FiberWitnessState.subset_trans hsub_up hsub_up_f
        rcases eq_or_lt_of_le (Nat.lt_succ_iff.mp hi) with hval_eq | hlt_m
        · have hi_eq : i = idx := Fin.ext hval_eq
          subst hi_eq
          simp only [idx, Function.update_self]
          have hup_f := heq_up stf hsub_up_f hvf
          have hge_f := heq_ge stf hsub_f hvf
          set v := (stf.idealOuterFn H x).1 idx
          have hup_iff : rUp.1 = .pos ↔ x idx < v := by
            rw [hup_f]; dsimp only [testUp, FiberWitnessState.idealOuterFn, v]
            split_ifs with h <;> simp [h]
          have hge_iff : rGe.1 = .pos ↔ x idx ≤ v := by
            rw [hge_f]; dsimp only [testGe, FiberWitnessState.idealOuterFn, v]
            split_ifs with h <;> simp [h]
          refine ⟨?_, fun hx_le_v ↦ ?_, fun hv_le_x ↦ ?_⟩
          · apply Fin.ext
            rw [clampUnitDisp_fst_val]
            change (if rUp.1 = .pos then stepCoordUp x idx idx
              else if rGe.1 = .pos then x idx else stepCoordDown x idx idx).val =
              if v < x idx then (x idx).val - 1
              else if x idx < v then (x idx).val + 1 else (x idx).val
            by_cases hlt_xv : x idx < v
            · have hnot_vx : ¬ (v < x idx) := lt_asymm hlt_xv
              have hlt_val : (x idx).val < v.val := hlt_xv
              have hv_lt := v.isLt
              rw [ite_eq_left (hup_iff.mpr hlt_xv), ite_eq_right hnot_vx, ite_eq_left hlt_xv]
              simp [stepCoordUp, Nat.min_eq_left (by omega : (x idx).val + 1 ≤ n - 1)]
            · rw [ite_eq_right (mt hup_iff.mp hlt_xv)]
              by_cases hle_xv : x idx ≤ v
              · rw [ite_eq_left (hge_iff.mpr hle_xv), ite_eq_right (not_lt_of_ge hle_xv),
                  ite_eq_right hlt_xv]
              · have hlt_vx : v < x idx := lt_of_not_ge hle_xv
                rw [ite_eq_right (mt hge_iff.mp hle_xv), ite_eq_left hlt_vx]
                simp [stepCoordDown]
          · have hrGe_pos : rGe.1 = .pos := hge_iff.mpr hx_le_v
            rcases hbr_ge with ⟨_, hpost_ge, ht_ge⟩ | ⟨hr_neg, _, _⟩
            · refine ⟨hpost_ge, ?_⟩
              dsimp only [testGe] at ht_ge; split_ifs at ht_ge with hle_ok; exact hle_ok
            · rw [hrGe_pos] at hr_neg; cases hr_neg
          · have hrUp_neg : rUp.1 ≠ .pos := mt hup_iff.mp (not_lt_of_ge hv_le_x)
            rcases hbr_up with ⟨hr_pos, _, _⟩ | ⟨_, hpre_up, ht_up⟩
            · exact absurd hr_pos hrUp_neg
            · refine ⟨hpre_up, ?_⟩
              dsimp only [testUp] at ht_up; split_ifs at ht_up with hlt_bad
              exact le_of_not_gt hlt_bad
        · have hne : i ≠ ⟨m, hm⟩ := fun heq ↦ by subst heq; exact Nat.lt_irrefl _ hlt_m
          simp only [Function.update_of_ne hne]
          exact hprop_m stf hsub_m_f hvf i hlt_m
  obtain ⟨hcnt_a, hsub_a, hval_a, hprop_a⟩ := hscan a le_rfl
  set coordsRes :=
    evalOracle (TarskiUpDownQuery.oracleOf H) (scanOuterFiberCoords algB x a le_rfl st)
  obtain ⟨hc_sgn, hsub_sgn, hval_sgn, hbr_sgn, heq_sgn⟩ :=
    runFiberCheck_spec hB hH hval_a (fun _ _ _ h2 ↦ h2) (x := x)
  set rSgn := evalOracle (TarskiUpDownQuery.oracleOf H)
    (runFiberCheck algB x coordsRes.2.2.2 Prod.snd)
  dsimp only [evalOuterFiber]
  rw [evalOracle_bind, queryCount_bind, evalOracle_bind, queryCount_bind,
    evalOracle_pure, queryCount_pure]
  dsimp only
  refine ⟨?_, FiberWitnessState.subset_trans hsub_a hsub_sgn, hval_sgn, fun stf hsub_f hvf ↦ ?_⟩
  · have hmul_eq : (2 * a + 1) * (Q_b + 1) = (2 * a) * (Q_b + 1) + ((Q_b + 1) + 0) := by
      simp only [Nat.add_mul, Nat.one_mul, Nat.add_zero]
    rw [hmul_eq]
    exact Nat.add_le_add hcnt_a (Nat.add_le_add hc_sgn le_rfl)
  · have hsub_a_f := FiberWitnessState.subset_trans hsub_sgn hsub_f
    have hsgn_f := heq_sgn stf hsub_f hvf
    have hans_eq : (coordsRes.1, rSgn.1) = clampUnitDisp (stf.idealOuterFn H) x := by
      ext i
      · exact congr_arg Fin.val (hprop_a stf hsub_a_f hvf i i.isLt).1
      · rw [hsgn_f, clampUnitDisp_snd]; rfl
    refine ⟨hans_eq, fun hsol_ideal ↦ ?_⟩
    rcases hsol_ideal with ⟨hx_le, hpos_f⟩ | ⟨hle_x, hneg_f⟩
    · have hrSgn_pos : rSgn.1 = .pos := hsgn_f.trans hpos_f
      rw [ite_eq_left hrSgn_pos]
      rcases hbr_sgn with ⟨_, hySgn_post, hySgn_sgn⟩ | ⟨hr_neg, _, _⟩
      · set ySol := Finset.univ.sup coordsRes.2.1 ⊔ rSgn.2.1
        have hySgn_le : rSgn.2.1 ≤ ySol := le_sup_right
        have hyGe_le : ∀ i : Fin a, coordsRes.2.1 i ≤ ySol := fun i ↦
          (Finset.le_sup (f := coordsRes.2.1) (Finset.mem_univ i)).trans le_sup_left
        left
        refine ⟨fun k ↦ ?_, ?_⟩
        · refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) k
          · obtain ⟨_, hge_i, _⟩ := hprop_a stf hsub_a_f hvf i i.isLt
            obtain ⟨_, hxi_le⟩ := hge_i (hx_le i)
            have hm := hH.1 (concatBlocks_mono (x₁ := x) le_rfl (hyGe_le i)) (Fin.castAdd b i)
            simpa [concatBlocks, fstBlock] using hxi_le.trans hm
          · have hySol_post : ySol ≤ sndBlock (H (concatBlocks x ySol)).1 := by
              refine sup_le (Finset.sup_le fun i _ ↦ ?_) ?_
              · exact ((hprop_a stf hsub_a_f hvf i i.isLt).2.1 (hx_le i)).1.trans
                  fun m ↦ hH.1 (concatBlocks_mono le_rfl (hyGe_le i)) (Fin.natAdd a m)
              · exact hySgn_post.trans
                  fun m ↦ hH.1 (concatBlocks_mono le_rfl hySgn_le) (Fin.natAdd a m)
            simpa [concatBlocks, sndBlock] using hySol_post j
        · have hle_sgn := hH.2 (concatBlocks_mono (x₁ := x) le_rfl hySgn_le)
          change (H (concatBlocks x rSgn.2.1)).2 = .pos at hySgn_sgn
          rw [hySgn_sgn] at hle_sgn
          cases hc : (H (concatBlocks x ySol)).2
          · rw [hc] at hle_sgn; exfalso; revert hle_sgn; decide
          · rfl
      · rw [hrSgn_pos] at hr_neg; cases hr_neg
    · have hrSgn_neg : rSgn.1 = .neg := hsgn_f.trans hneg_f
      have hnot_pos : ¬ (rSgn.1 = .pos) := by rw [hrSgn_neg]; decide
      rw [ite_eq_right hnot_pos]
      rcases hbr_sgn with ⟨hr_pos, _, _⟩ | ⟨_, hySgn_pre, hySgn_sgn⟩
      · exact absurd hr_pos hnot_pos
      · set ySol := Finset.univ.inf coordsRes.2.2.1 ⊓ rSgn.2.1
        have hySol_le_sgn : ySol ≤ rSgn.2.1 := inf_le_right
        have hySol_le_up : ∀ i : Fin a, ySol ≤ coordsRes.2.2.1 i := fun i ↦
          inf_le_left.trans (Finset.inf_le (f := coordsRes.2.2.1) (Finset.mem_univ i))
        right
        refine ⟨fun k ↦ ?_, ?_⟩
        · refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) k
          · obtain ⟨_, _, hup_i⟩ := hprop_a stf hsub_a_f hvf i i.isLt
            obtain ⟨_, hle_xi⟩ := hup_i (hle_x i)
            have hm := hH.1 (concatBlocks_mono (x₁ := x) le_rfl (hySol_le_up i)) (Fin.castAdd b i)
            simpa [concatBlocks, fstBlock] using hm.trans hle_xi
          · have hySol_pre : sndBlock (H (concatBlocks x ySol)).1 ≤ ySol := by
              refine le_inf (Finset.le_inf fun i _ ↦ ?_) ?_
              · exact le_trans
                  (fun m ↦ hH.1 (concatBlocks_mono (x₁ := x) le_rfl (hySol_le_up i))
                    (Fin.natAdd a m))
                  ((hprop_a stf hsub_a_f hvf i i.isLt).2.2 (hle_x i)).1
              · exact le_trans
                  (fun m ↦ hH.1 (concatBlocks_mono (x₁ := x) le_rfl hySol_le_sgn) (Fin.natAdd a m))
                  hySgn_pre
            simpa [concatBlocks, sndBlock] using hySol_pre j
        · have hle_sgn := hH.2 (concatBlocks_mono (x₁ := x) le_rfl hySol_le_sgn)
          change (H (concatBlocks x rSgn.2.1)).2 = .neg at hySgn_sgn
          rw [hySgn_sgn] at hle_sgn
          cases hc : (H (concatBlocks x ySol)).2
          · rfl
          · rw [hc] at hle_sgn; exfalso; revert hle_sgn; decide

/-- Thread `FiberWitnessState` through an outer `FreeM (TarskiUpDownQuery n a)` tree. -/
def simOuterUpDown {n a b : ℕ} [NeZero n]
    (algB : FreeM (TarskiUpDownQuery n b) (Hypergrid n b)) :
    FreeM (TarskiUpDownQuery n a) (Hypergrid n a) → FiberWitnessState n a b →
      FreeM (TarskiUpDownQuery n (a + b)) (Hypergrid n a × FiberWitnessState n a b)
  | .pure x, st => pure (x, st)
  | .liftBind (.query x) cont, st => do
    let out ← evalOuterFiber algB x st
    simOuterUpDown algB (cont out.ans) out.state

private theorem simOuterUpDown_spec {n a b : ℕ} [NeZero n]
    {algB : FreeM (TarskiUpDownQuery n b) (Hypergrid n b)} {Q_b : ℕ}
    (hB : ∀ G : TarskiUpDownFn n b, IsMonotoneUpDown G →
      IsUpDownSol G (evalOracle (TarskiUpDownQuery.oracleOf G) algB) ∧
      queryCount (TarskiUpDownQuery.oracleOf G) algB ≤ Q_b)
    {H : TarskiUpDownFn n (a + b)} (hH : IsMonotoneUpDown H) :
    ∀ (t : FreeM (TarskiUpDownQuery n a) (Hypergrid n a)) (st : FiberWitnessState n a b),
      st.Valid H →
      st.Subset (evalOracle (TarskiUpDownQuery.oracleOf H) (simOuterUpDown algB t st)).2 ∧
      (evalOracle (TarskiUpDownQuery.oracleOf H) (simOuterUpDown algB t st)).2.Valid H ∧
      ∀ stf : FiberWitnessState n a b,
        (evalOracle (TarskiUpDownQuery.oracleOf H) (simOuterUpDown algB t st)).2.Subset stf →
        stf.Valid H →
        (evalOracle (TarskiUpDownQuery.oracleOf H) (simOuterUpDown algB t st)).1 =
          evalOracle (TarskiUpDownQuery.oracleOf (clampUnitDisp (stf.idealOuterFn H))) t ∧
        queryCount (TarskiUpDownQuery.oracleOf H) (simOuterUpDown algB t st) ≤
          queryCount (TarskiUpDownQuery.oracleOf (clampUnitDisp (stf.idealOuterFn H))) t *
            ((2 * a + 1) * (Q_b + 1)) := by
  intro t
  induction t with
  | pure x =>
    intro st hv
    simp only [evalOracle_pure, queryCount_pure, Nat.zero_mul]
    exact ⟨FiberWitnessState.subset_refl st, hv, fun _ _ _ ↦ ⟨rfl, le_rfl⟩⟩
  | lift_bind op cont ih =>
    cases op with
    | query x =>
      intro st hv
      rw [← FreeM.liftBind_eq]
      dsimp only [simOuterUpDown]
      obtain ⟨hcnt_x, hsub_x, hval_x, hprop_x⟩ := evalOuterFiber_spec hB hH hv (x := x)
      set out := evalOracle (TarskiUpDownQuery.oracleOf H) (evalOuterFiber algB x st)
      obtain ⟨hsub_cont, hval_cont, hprop_cont⟩ := ih out.ans out.state hval_x
      rw [evalOracle_bind, queryCount_bind]
      refine ⟨FiberWitnessState.subset_trans hsub_x hsub_cont, hval_cont,
        fun stf hsub_f hvf ↦ ?_⟩
      have hsub_out_f := FiberWitnessState.subset_trans hsub_cont hsub_f
      obtain ⟨hans_eq, -⟩ := hprop_x stf hsub_out_f hvf
      obtain ⟨heval_c, hcnt_c⟩ := hprop_cont stf hsub_f hvf
      refine ⟨?_, ?_⟩
      · rw [heval_c, hans_eq]; rfl
      · change queryCount (TarskiUpDownQuery.oracleOf H) (evalOuterFiber algB x st) +
            queryCount (TarskiUpDownQuery.oracleOf H)
              (simOuterUpDown algB (cont out.ans) out.state) ≤
          (1 + queryCount (TarskiUpDownQuery.oracleOf (clampUnitDisp (stf.idealOuterFn H)))
            (cont (clampUnitDisp (stf.idealOuterFn H) x))) * ((2 * a + 1) * (Q_b + 1))
        rw [Nat.add_mul, Nat.one_mul, ← hans_eq]
        exact Nat.add_le_add hcnt_x hcnt_c

/-- Product decomposition algorithm solving `(a + b)`-dimensional monotone up-or-down search
from an `a`-dimensional solver `algA` and a `b`-dimensional solver `algB`. -/
def decompUpDown {n a b : ℕ} [NeZero n]
    (algA : FreeM (TarskiUpDownQuery n a) (Hypergrid n a))
    (algB : FreeM (TarskiUpDownQuery n b) (Hypergrid n b)) :
    FreeM (TarskiUpDownQuery n (a + b)) (Hypergrid n (a + b)) := do
  let leaf ← simOuterUpDown algB algA ⟨[], []⟩
  let x := leaf.1
  let out ← evalOuterFiber algB x leaf.2
  let y :=
    if out.ans.2 = .pos then Finset.univ.sup out.yGe ⊔ out.ySgn
    else Finset.univ.inf out.yUp ⊓ out.ySgn
  pure (concatBlocks x y)

/-- Product decomposition solves `(a + b)`-dimensional monotone up-or-down search in at most
`(Q_a + 1) * (2 * a + 1) * (Q_b + 1)` queries. -/
theorem decompUpDown_spec {n a b : ℕ} [NeZero n]
    {algA : FreeM (TarskiUpDownQuery n a) (Hypergrid n a)} {Q_a : ℕ}
    (hA : ∀ F : TarskiUpDownFn n a, IsMonotoneUpDown F →
      IsUpDownSol F (evalOracle (TarskiUpDownQuery.oracleOf F) algA) ∧
      queryCount (TarskiUpDownQuery.oracleOf F) algA ≤ Q_a)
    {algB : FreeM (TarskiUpDownQuery n b) (Hypergrid n b)} {Q_b : ℕ}
    (hB : ∀ G : TarskiUpDownFn n b, IsMonotoneUpDown G →
      IsUpDownSol G (evalOracle (TarskiUpDownQuery.oracleOf G) algB) ∧
      queryCount (TarskiUpDownQuery.oracleOf G) algB ≤ Q_b) :
    ∀ H : TarskiUpDownFn n (a + b), IsMonotoneUpDown H →
      IsUpDownSol H (evalOracle (TarskiUpDownQuery.oracleOf H) (decompUpDown algA algB)) ∧
      queryCount (TarskiUpDownQuery.oracleOf H) (decompUpDown algA algB) ≤
        (Q_a + 1) * (2 * a + 1) * (Q_b + 1) := by
  intro H hH
  have hv₀ : (FiberWitnessState.mk ([] : List (Hypergrid n a × Hypergrid n b)) []).Valid H :=
    ⟨fun _ h ↦ absurd h List.not_mem_nil, fun _ h ↦ absurd h List.not_mem_nil,
     fun _ h ↦ absurd h List.not_mem_nil⟩
  obtain ⟨_, hval_sim, hprop_sim⟩ := simOuterUpDown_spec hB hH algA ⟨[], []⟩ hv₀
  set leaf := evalOracle (TarskiUpDownQuery.oracleOf H) (simOuterUpDown algB algA ⟨[], []⟩)
  obtain ⟨hcnt_end, hsub_end, hval_end, hprop_end⟩ :=
    evalOuterFiber_spec hB hH hval_sim (x := leaf.1)
  set out := evalOracle (TarskiUpDownQuery.oracleOf H) (evalOuterFiber algB leaf.1 leaf.2)
  set stf := out.state
  obtain ⟨hx_eq, hcnt_sim⟩ := hprop_sim stf hsub_end hval_end
  obtain ⟨_, hsol_extract⟩ := hprop_end stf (FiberWitnessState.subset_refl stf) hval_end
  obtain ⟨hsimp_mono, hsimp_iff⟩ :=
    clampUnitDisp_spec (FiberWitnessState.isMonotoneUpDown_idealOuterFn hH stf)
  obtain ⟨hsol_simp, hcnt_A⟩ := hA (clampUnitDisp (stf.idealOuterFn H)) hsimp_mono
  rw [← hx_eq] at hsol_simp
  dsimp only [decompUpDown]
  rw [evalOracle_bind, queryCount_bind, evalOracle_bind, queryCount_bind,
    evalOracle_pure, queryCount_pure]
  refine ⟨hsol_extract ((hsimp_iff leaf.1).mp hsol_simp), ?_⟩
  have hmul_A := Nat.mul_le_mul_right ((2 * a + 1) * (Q_b + 1)) hcnt_A
  have hprod_eq : (Q_a + 1) * (2 * a + 1) * (Q_b + 1) =
      Q_a * ((2 * a + 1) * (Q_b + 1)) + ((2 * a + 1) * (Q_b + 1) + 0) := by
    rw [Nat.mul_assoc, Nat.succ_mul]; rfl
  rw [hprod_eq]
  exact Nat.add_le_add (hcnt_sim.trans hmul_A) (Nat.add_le_add hcnt_end le_rfl)

end CslibFrontier.Computability.QueryComplexity
