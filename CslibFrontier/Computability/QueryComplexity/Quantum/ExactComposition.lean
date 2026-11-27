/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.QueryComplexity.Quantum.Exact
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Compositional Toolkit for Exact Quantum Query Algorithms

This module develops computational-basis readout algorithms (`ReadoutAlgorithm`,
`ReadoutSpecInMod`, `ReadoutComputableInMod`) in the modular-addition quantum query model of
`CslibFrontier.Computability.QueryComplexity.Quantum.Exact` and establishes the core
composition operations under standard Lean axioms:

* Relational specifications (`ReadoutSpecInMod`) and exact functions (`ReadoutComputableInMod`)
* Post-processing (`map`) and implication weakening (`weaken`)
* Query-count padding via the invariant uniform superposition (`pad`)
* Coordinate-subinstance embedding (`subinstance`)
* Modulus-divisibility lifting (`modulusLift`)
* Coordinatewise input masking at modulus `2` (`compXorMask`, `compNot`)
* Adaptive sequential composition / deferred measurement (`bind`, `bind_lcm`)
* Constant, single-bit, two-bit XOR (Deutsch), and `n`-query full-read algorithms, yielding
  the trivial upper bound `Q_E(f) ≤ n`.

## Main definitions

* `CslibFrontier.Quantum.ReadoutAlgorithm`: an exact quantum query algorithm whose final
  measurement is a computational-basis readout.
* `CslibFrontier.Quantum.ReadoutSpecInMod`: existence of a `T`-query readout algorithm at
  modulus `d` satisfying a relational output specification `spec : BitString n → X → Prop`.
* `CslibFrontier.Quantum.ReadoutComputableInMod`: existence of a `T`-query readout
  algorithm computing `f : BitString n → X` exactly at modulus `d`.

## Main results

* `CslibFrontier.Quantum.ReadoutSpecInMod.pad`,
  `CslibFrontier.Quantum.ReadoutComputableInMod.pad`: padding from `T` to `T' ≥ T` queries.
* `CslibFrontier.Quantum.ReadoutSpecInMod.subinstance`,
  `CslibFrontier.Quantum.ReadoutComputableInMod.subinstance`: embedding `k`-bit algorithms
  into `n` bits along `Fin k ↪ Fin n`.
* `CslibFrontier.Quantum.ReadoutSpecInMod.modulusLift`,
  `CslibFrontier.Quantum.ReadoutComputableInMod.modulusLift`: `m ∣ d` lifts an `m`-modulus
  algorithm to a `d`-modulus algorithm.
* `CslibFrontier.Quantum.ReadoutSpecInMod.bind`,
  `CslibFrontier.Quantum.ReadoutComputableInMod.bind`: adaptive sequential composition.
* `CslibFrontier.Quantum.readoutComputableInMod_xor_of_two_dvd`: two-bit XOR in `1` query
  for any even modulus `d`.
* `CslibFrontier.Quantum.exactQuantumQueryComplexity_le_length`: `Q_E(f) ≤ n`.
-/

public section

namespace CslibFrontier.Quantum

open Cslib Cslib.BitString Cslib.Quantum Finset Matrix
open scoped ComplexOrder

/-! ### Zero-extension helpers for modular-addition query runs -/

section ExtendHelpers

private theorem extendByZero_apply_emb {A P : Type*} [Fintype A] [Fintype P]
    (j : A ↪ P) (ψ : EuclideanSpace ℂ A) (a : A) :
    (LinearIsometry.piLpExtendByZero 2 ℂ ℂ j ψ).ofLp (j a) = ψ.ofLp a := by
  change Function.extend j ψ.ofLp 0 (j a) = ψ.ofLp a
  exact j.injective.extend_apply ψ.ofLp 0 a

private theorem directSumUnitary_extendByZero {A P : Type*} [Fintype A] [Fintype P]
    (j : A ↪ P) (U : EuclideanSpace ℂ A ≃ₗᵢ[ℂ] EuclideanSpace ℂ A)
    (ψ : EuclideanSpace ℂ A) :
    directSumUnitary j U (LinearIsometry.piLpExtendByZero 2 ℂ ℂ j ψ) =
      LinearIsometry.piLpExtendByZero 2 ℂ ℂ j (U ψ) := by
  classical
  ext p
  by_cases hp : p ∈ Set.range j
  · obtain ⟨a, rfl⟩ := hp
    rw [directSumUnitary_apply_emb, extendByZero_apply_emb]
    have harg : (WithLp.toLp 2 fun a' =>
        (LinearIsometry.piLpExtendByZero 2 ℂ ℂ j ψ).ofLp (j a')) = ψ := by
      ext a'; exact extendByZero_apply_emb j ψ a'
    rw [harg]
  · rw [directSumUnitary_apply_of_not_mem _ _ _ hp,
      LinearIsometry.piLpExtendByZero_apply_eq_zero hp,
      LinearIsometry.piLpExtendByZero_apply_eq_zero hp]

private theorem fiberUnitary_extendByZero {P B A : Type*} [Fintype P] [Fintype B] [Fintype A]
    (e : P ≃ B × A) (b₀ : B) (U : EuclideanSpace ℂ A ≃ₗᵢ[ℂ] EuclideanSpace ℂ A)
    (ψ : EuclideanSpace ℂ A) :
    let j : A ↪ P := ⟨fun a => e.symm (b₀, a), fun _ _ h => (Prod.mk.inj (e.symm.injective h)).2⟩
    fiberUnitary e (fun _ => U) (LinearIsometry.piLpExtendByZero 2 ℂ ℂ j ψ) =
      LinearIsometry.piLpExtendByZero 2 ℂ ℂ j (U ψ) := by
  classical
  intro j
  ext p
  rw [fiberUnitary_apply]
  by_cases hb : (e p).1 = b₀
  · have hp : p = j (e p).2 := by
      change p = e.symm (b₀, (e p).2)
      rw [← hb, e.symm_apply_apply]
    have harg : (WithLp.toLp 2 fun a =>
        (LinearIsometry.piLpExtendByZero 2 ℂ ℂ j ψ).ofLp (e.symm ((e p).1, a))) = ψ := by
      ext a; rw [hb]; exact extendByZero_apply_emb j ψ a
    rw [harg]
    conv_rhs => rw [hp]
    rw [extendByZero_apply_emb]
  · have hnot : p ∉ Set.range j := by
      rintro ⟨a, rfl⟩
      apply hb
      change (e (e.symm (b₀, a))).1 = b₀
      rw [e.apply_symm_apply]
    have hzero : (WithLp.toLp 2 fun a =>
        (LinearIsometry.piLpExtendByZero 2 ℂ ℂ j ψ).ofLp (e.symm ((e p).1, a))) = 0 := by
      ext a
      have ha : e.symm ((e p).1, a) ∉ Set.range j := by
        rintro ⟨a', h⟩
        exact hb (Prod.mk.inj (e.symm.injective h)).1.symm
      exact LinearIsometry.piLpExtendByZero_apply_eq_zero ha ψ
    rw [hzero, map_zero, LinearIsometry.piLpExtendByZero_apply_eq_zero hnot]
    rfl

private theorem runValue_directSum {k m d₁ d₂ : ℕ} [NeZero d₁] [NeZero d₂]
    {W₁ W₂ : Type*} [Fintype W₁] [Fintype W₂]
    (emb : (Fin k × ZMod d₁ × W₁) ↪ (Fin m × ZMod d₂ × W₂))
    (U : ℕ → ValueState (Fin k) (ZMod d₁) W₁ ≃ₗᵢ[ℂ] ValueState (Fin k) (ZMod d₁) W₁)
    (ψ₀ : ValueState (Fin k) (ZMod d₁) W₁)
    (x₁ : BitString k) (x₂ : BitString m)
    (hvo : ∀ ψ, modAddOracle d₂ x₂ (LinearIsometry.piLpExtendByZero 2 ℂ ℂ emb ψ) =
      LinearIsometry.piLpExtendByZero 2 ℂ ℂ emb (modAddOracle d₁ x₁ ψ)) (t : ℕ) :
    runValue (modAddStep d₂) (fun s => (directSumUnitary emb (U s)).toLinearIsometry)
        (LinearIsometry.piLpExtendByZero 2 ℂ ℂ emb ψ₀) x₂ t =
      LinearIsometry.piLpExtendByZero 2 ℂ ℂ emb
        (runValue (modAddStep d₁) (fun s => (U s).toLinearIsometry) ψ₀ x₁ t) := by
  induction t with
  | zero =>
    rw [runValue_modAddStep_zero, runValue_modAddStep_zero]
    exact directSumUnitary_extendByZero emb (U 0) ψ₀
  | succ t ih =>
    rw [runValue_modAddStep_succ, runValue_modAddStep_succ, ih, hvo,
      directSumUnitary_extendByZero]

end ExtendHelpers

/-! ### Computational-basis readout algorithms -/

section Readout

/-- An exact quantum query algorithm whose final measurement is a computational-basis readout
`readout : Fin n × ZMod d × W → X`. -/
structure ReadoutAlgorithm (n d : ℕ) [NeZero d] (W X : Type*) [Fintype W] (T : ℕ) where
  /-- Initial unit state `|ψ₀⟩`. -/
  init : ValueState (Fin n) (ZMod d) W
  /-- Unit-norm condition on `init`. -/
  norm_init : ‖init‖ = 1
  /-- Input-independent unitaries `U_0, ..., U_T`. -/
  unitary : ℕ → ValueState (Fin n) (ZMod d) W ≃ₗᵢ[ℂ] ValueState (Fin n) (ZMod d) W
  /-- Classical readout map on final computational-basis states. -/
  readout : Fin n × ZMod d × W → X

namespace ReadoutAlgorithm

variable {n d T : ℕ} [NeZero d] {W X : Type*} [Fintype W]

/-- Final state of a `ReadoutAlgorithm`. -/
@[expose]
noncomputable def finalState (A : ReadoutAlgorithm n d W X T) (x : BitString n) :
    ValueState (Fin n) (ZMod d) W :=
  runValue (modAddStep d) (fun t => (A.unitary t).toLinearIsometry) A.init x T

@[simp]
theorem norm_finalState (A : ReadoutAlgorithm n d W X T) (x : BitString n) :
    ‖A.finalState x‖ = 1 := by
  rw [finalState, norm_runValue, A.norm_init]

theorem finalState_eq_runValue (A : ReadoutAlgorithm n d W X T) (x : BitString n) :
    A.finalState x =
      runValue (modAddStep d) (fun t => (A.unitary t).toLinearIsometry) A.init x T := rfl

@[simp]
theorem finalState_zero (A : ReadoutAlgorithm n d W X 0) (x : BitString n) :
    A.finalState x = A.unitary 0 A.init :=
  runValue_modAddStep_zero A.unitary A.init x

theorem finalState_succ (A : ReadoutAlgorithm n d W X (T + 1)) (x : BitString n) :
    A.finalState x =
      A.unitary (T + 1)
        (modAddOracle d x
          (runValue (modAddStep d) (fun t => (A.unitary t).toLinearIsometry) A.init x T)) :=
  runValue_modAddStep_succ A.unitary A.init x T

/-- Relational exact computation: every basis state with nonzero amplitude in `A.finalState x`
decodes to an output satisfying `spec x`. -/
@[expose]
def SatisfiesSpec (A : ReadoutAlgorithm n d W X T) (spec : BitString n → X → Prop) : Prop :=
  ∀ (x : BitString n) (p : Fin n × ZMod d × W),
    ¬ spec x (A.readout p) → (A.finalState x).ofLp p = 0

/-- Exact computation via computational-basis readout: every basis state with nonzero
amplitude in `finalState x` decodes to `f x`. -/
@[expose]
def ComputesExactly (A : ReadoutAlgorithm n d W X T) (f : BitString n → X) : Prop :=
  A.SatisfiesSpec (fun x a => a = f x)

/-- The projective POVM induced by a classical readout function `out : ι → X`. -/
noncomputable def povmOfReadout {ι X : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype X] [DecidableEq X] (out : ι → X) : POVM X ι where
  effect a := diagonal fun p => if out p = a then (1 : ℂ) else 0
  posSemidef a := posSemidef_diagonal_iff.mpr fun p => by
    split_ifs <;> simp
  sum_effect := by
    ext p q
    by_cases hpq : p = q
    · subst hpq; simp [Matrix.sum_apply]
    · simp [Matrix.sum_apply, hpq]

theorem povmOfReadout_prob {ι X : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype X] [DecidableEq X] (out : ι → X) (ψ : EuclideanSpace ℂ ι) (a : X) :
    (povmOfReadout out).prob ψ a = ∑ p : ι, if out p = a then ‖ψ.ofLp p‖ ^ 2 else 0 := by
  simp only [POVM.prob, povmOfReadout, Matrix.mulVec_diagonal, dotProduct, Pi.star_apply,
    Complex.re_sum]
  refine sum_congr rfl fun p _ => ?_
  split_ifs
  · rw [one_mul, Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
  · simp

/-- Convert a `ReadoutAlgorithm` into a `QuantumQueryAlgorithm` using `povmOfReadout`. -/
noncomputable def toQuantumQueryAlgorithm [DecidableEq W] [Fintype X] [DecidableEq X]
    (A : ReadoutAlgorithm n d W X T) : QuantumQueryAlgorithm n d W X T where
  init := A.init
  norm_init := A.norm_init
  unitary := A.unitary
  povm := povmOfReadout A.readout

theorem toQuantumQueryAlgorithm_computesExactly [DecidableEq W] [Fintype X] [DecidableEq X]
    {A : ReadoutAlgorithm n d W X T} {f : BitString n → X} (hA : A.ComputesExactly f) :
    A.toQuantumQueryAlgorithm.ComputesExactly f := fun x => by
  change (povmOfReadout A.readout).prob (A.finalState x) (f x) = 1
  rw [povmOfReadout_prob]
  have hnorm : ∑ p : Fin n × ZMod d × W, ‖(A.finalState x).ofLp p‖ ^ 2 = 1 := by
    rw [← EuclideanSpace.norm_sq_eq, A.norm_finalState x, one_pow]
  rw [← hnorm]
  refine sum_congr rfl fun p _ => ?_
  by_cases hp : A.readout p = f x
  · simp [hp]
  · simp [hp, hA x p hp]

/-- Post-processing the output of a `ReadoutAlgorithm` costs zero additional queries. -/
noncomputable def map {Y : Type*} (A : ReadoutAlgorithm n d W X T) (g : X → Y) :
    ReadoutAlgorithm n d W Y T where
  init := A.init
  norm_init := A.norm_init
  unitary := A.unitary
  readout := g ∘ A.readout

theorem map_satisfiesSpec {Y : Type*} {A : ReadoutAlgorithm n d W X T}
    {spec : BitString n → X → Prop} {spec' : BitString n → Y → Prop}
    (hA : A.SatisfiesSpec spec) (g : X → Y) (hg : ∀ x a, spec x a → spec' x (g a)) :
    (A.map g).SatisfiesSpec spec' := fun x p hp =>
  hA x p fun h => hp (hg x _ h)

theorem map_computesExactly {Y : Type*} {A : ReadoutAlgorithm n d W X T} {f : BitString n → X}
    (hA : A.ComputesExactly f) (g : X → Y) :
    (A.map g).ComputesExactly (g ∘ f) :=
  map_satisfiesSpec hA g fun _ _ h => congrArg g h

/-- Lift a `ReadoutAlgorithm` to a larger workspace along an embedding `j : W ↪ W'`. -/
noncomputable def liftWorkspace {W' : Type*} [Fintype W']
    (A : ReadoutAlgorithm n d W X T) (j : W ↪ W') (x₀ : X) :
    ReadoutAlgorithm n d W' X T := by
  classical
  let emb : (Fin n × ZMod d × W) ↪ (Fin n × ZMod d × W') :=
    ⟨fun p => (p.1, p.2.1, j p.2.2), fun p₁ p₂ h => by
      simp only [Prod.mk.injEq] at h
      exact Prod.ext h.1 (Prod.ext h.2.1 (j.injective h.2.2))⟩
  refine
    { init := LinearIsometry.piLpExtendByZero 2 ℂ ℂ emb A.init
      norm_init := by rw [LinearIsometry.norm_map, A.norm_init]
      unitary := fun t => directSumUnitary emb (A.unitary t)
      readout := fun p =>
        if h : p.2.2 ∈ Set.range j then
          A.readout (p.1, p.2.1, (Equiv.ofInjective j j.injective).symm ⟨p.2.2, h⟩)
        else x₀ }

theorem liftWorkspace_satisfiesSpec {W' : Type*} [Fintype W']
    {A : ReadoutAlgorithm n d W X T} {spec : BitString n → X → Prop}
    (hA : A.SatisfiesSpec spec) (j : W ↪ W') (x₀ : X) :
    (A.liftWorkspace j x₀).SatisfiesSpec spec := by
  classical
  let emb : (Fin n × ZMod d × W) ↪ (Fin n × ZMod d × W') :=
    ⟨fun p => (p.1, p.2.1, j p.2.2), fun p₁ p₂ h => by
      simp only [Prod.mk.injEq] at h
      exact Prod.ext h.1 (Prod.ext h.2.1 (j.injective h.2.2))⟩
  have hvo : ∀ (x : BitString n) (ψ : ValueState (Fin n) (ZMod d) W),
      modAddOracle d x (LinearIsometry.piLpExtendByZero 2 ℂ ℂ emb ψ) =
        LinearIsometry.piLpExtendByZero 2 ℂ ℂ emb (modAddOracle d x ψ) := fun x ψ => by
    ext ⟨i, b, w'⟩
    rw [modAddOracle_apply]
    by_cases hw : w' ∈ Set.range j
    · obtain ⟨w, rfl⟩ := hw
      have he1 : (i, b - (if x i then (1 : ZMod d) else 0), j w) =
          emb (i, b - (if x i then (1 : ZMod d) else 0), w) := rfl
      have he2 : (i, b, j w) = emb (i, b, w) := rfl
      rw [he1, he2, extendByZero_apply_emb, extendByZero_apply_emb, modAddOracle_apply]
    · have hnot1 : (i, b - (if x i then (1 : ZMod d) else 0), w') ∉ Set.range emb := by
        rintro ⟨⟨_, _, w⟩, h⟩; exact hw ⟨w, (Prod.mk.inj (Prod.mk.inj h).2).2⟩
      have hnot2 : (i, b, w') ∉ Set.range emb := by
        rintro ⟨⟨_, _, w⟩, h⟩; exact hw ⟨w, (Prod.mk.inj (Prod.mk.inj h).2).2⟩
      rw [LinearIsometry.piLpExtendByZero_apply_eq_zero hnot1,
        LinearIsometry.piLpExtendByZero_apply_eq_zero hnot2]
  intro x ⟨i, b, w'⟩ hp
  have hfinal : (A.liftWorkspace j x₀).finalState x =
      LinearIsometry.piLpExtendByZero 2 ℂ ℂ emb (A.finalState x) :=
    runValue_directSum emb A.unitary A.init x x (hvo x) T
  rw [hfinal]
  by_cases hw : w' ∈ Set.range j
  · have hread : (A.liftWorkspace j x₀).readout (i, b, w') =
        A.readout (i, b, (Equiv.ofInjective j j.injective).symm ⟨w', hw⟩) := by
      unfold liftWorkspace; simp only [hw, ↓reduceDIte]
    have hw' : w' = j ((Equiv.ofInjective j j.injective).symm ⟨w', hw⟩) :=
      (congrArg Subtype.val ((Equiv.ofInjective j j.injective).apply_symm_apply ⟨w', hw⟩)).symm
    conv_lhs => rw [hw']
    have he : (i, b, j ((Equiv.ofInjective j j.injective).symm ⟨w', hw⟩)) =
        emb (i, b, (Equiv.ofInjective j j.injective).symm ⟨w', hw⟩) := rfl
    rw [he, extendByZero_apply_emb]
    exact hA x _ (hread ▸ hp)
  · have hnot : (i, b, w') ∉ Set.range emb := by
      rintro ⟨⟨_, _, w⟩, h⟩; exact hw ⟨w, (Prod.mk.inj (Prod.mk.inj h).2).2⟩
    exact LinearIsometry.piLpExtendByZero_apply_eq_zero hnot _

end ReadoutAlgorithm

/-- `spec : BitString n → X → Prop` is satisfied by an exact `T`-query readout algorithm at
modulus `d`: every nonzero-amplitude final basis state decodes to a value satisfying `spec x`. -/
@[expose]
def ReadoutSpecInMod {n : ℕ} (d : ℕ) [NeZero d] {X : Type*}
    (spec : BitString n → X → Prop) (T : ℕ) : Prop :=
  ∃ (W : Type) (_ : Fintype W) (A : ReadoutAlgorithm n d W X T), A.SatisfiesSpec spec

/-- `f : BitString n → X` is computable in `T` queries with modulus `d` via a
computational-basis readout algorithm. -/
@[expose]
def ReadoutComputableInMod {n : ℕ} (d : ℕ) [NeZero d] {X : Type*}
    (f : BitString n → X) (T : ℕ) : Prop :=
  ReadoutSpecInMod d (fun x a => a = f x) T

theorem ReadoutSpecInMod.weaken {n d T : ℕ} [NeZero d] {X : Type*}
    {spec spec' : BitString n → X → Prop} (h : ReadoutSpecInMod d spec T)
    (himp : ∀ x a, spec x a → spec' x a) : ReadoutSpecInMod d spec' T := by
  obtain ⟨W, hW, A, hA⟩ := h
  exact ⟨W, hW, A, fun x p hp => hA x p fun hs => hp (himp x _ hs)⟩

theorem ReadoutSpecInMod.map {n d T : ℕ} [NeZero d] {X Y : Type*}
    {spec : BitString n → X → Prop} {spec' : BitString n → Y → Prop}
    (h : ReadoutSpecInMod d spec T) (g : X → Y) (hg : ∀ x a, spec x a → spec' x (g a)) :
    ReadoutSpecInMod d spec' T := by
  obtain ⟨W, hW, A, hA⟩ := h
  exact ⟨W, hW, A.map g, A.map_satisfiesSpec hA g hg⟩

theorem ReadoutSpecInMod.toComputable_map {n d T : ℕ} [NeZero d] {X Y : Type*}
    {spec : BitString n → X → Prop} {f : BitString n → Y}
    (h : ReadoutSpecInMod d spec T) (g : X → Y) (hg : ∀ x a, spec x a → g a = f x) :
    ReadoutComputableInMod d f T :=
  h.map g hg

theorem ReadoutComputableInMod.toExact {n d T : ℕ} [NeZero d] {X : Type*} [Fintype X]
    {f : BitString n → X} (h : ReadoutComputableInMod d f T) :
    ExactQuantumComputableInMod d f T := by
  classical
  obtain ⟨W, hW, A, hA⟩ := h
  exact ⟨W, hW, inferInstance, A.toQuantumQueryAlgorithm,
    A.toQuantumQueryAlgorithm_computesExactly hA⟩

theorem ReadoutComputableInMod.toComputable {n d T : ℕ} [NeZero d] {X : Type*} [Fintype X]
    {f : BitString n → X} (h : ReadoutComputableInMod d f T) :
    ExactQuantumComputableIn f T :=
  ⟨d, inferInstance, h.toExact⟩

theorem ReadoutComputableInMod.map {n d T : ℕ} [NeZero d] {X Y : Type*}
    {f : BitString n → X} (h : ReadoutComputableInMod d f T) (g : X → Y) :
    ReadoutComputableInMod d (g ∘ f) T :=
  ReadoutSpecInMod.map h g fun _ _ heq => congrArg g heq

/-- Zero-query computation of any constant function (when `n > 0`). -/
theorem readoutComputableInMod_const {n d : ℕ} [NeZero n] [NeZero d] {X : Type*} (c : X) :
    ReadoutComputableInMod d (fun _ : BitString n => c) 0 := by
  let i₀ : Fin n := ⟨0, NeZero.pos n⟩
  refine ⟨Unit, inferInstance,
    { init := ket (i₀, (0 : ZMod d), ())
      norm_init := norm_ket _
      unitary := fun _ => LinearIsometryEquiv.refl ℂ _
      readout := fun _ => c },
    fun _ _ h => (h rfl).elim⟩

/-- Single-bit query in `1` query for any modulus `d ≥ 2`. -/
theorem readoutComputableInMod_coord {n d : ℕ} [NeZero d] (hd : 2 ≤ d) (i₀ : Fin n) :
    ReadoutComputableInMod d (fun x : BitString n => x i₀) 1 := by
  have h10 : (1 : ZMod d) ≠ 0 := by
    have : Fact (1 < d) := ⟨by omega⟩
    exact one_ne_zero
  refine ⟨Unit, inferInstance,
    { init := ket (i₀, (0 : ZMod d), ())
      norm_init := norm_ket _
      unitary := fun _ => LinearIsometryEquiv.refl ℂ _
      readout := fun p => decide (p.2.1 ≠ 0) },
    fun x ⟨i, b, u⟩ hne => ?_⟩
  have hrun : runValue (modAddStep d) (fun _ => LinearIsometry.id)
      (ket (i₀, (0 : ZMod d), ())) x 1 =
      ket (i₀, (if x i₀ then (1 : ZMod d) else 0), ()) := by
    ext ⟨i', b', u'⟩
    simp only [runValue, LinearIsometry.id_apply, valueOracle_apply, modAddStep_apply, ket_apply]
    by_cases hi : i' = i₀
    · subst hi; cases x i' <;> simp [sub_eq_zero]
    · simp [hi]
  change (runValue (modAddStep d) (fun _ => LinearIsometry.id)
      (ket (i₀, (0 : ZMod d), ())) x 1).ofLp (i, b, u) = 0
  rw [hrun, ket_apply]
  by_cases heq : (i, b, u) = (i₀, (if x i₀ then (1 : ZMod d) else 0), ())
  · exfalso
    apply hne
    have hb : b = if x i₀ then (1 : ZMod d) else 0 := (Prod.mk.inj (Prod.mk.inj heq).2).1
    subst hb
    change decide ((if x i₀ then (1 : ZMod d) else 0) ≠ 0) = x i₀
    cases x i₀ <;> simp [h10]
  · simp [heq]

/-- Padding a relational `ReadoutAlgorithm` from `T` queries to any `T' ≥ T` queries using the
invariant uniform superposition `QFT_d† |0⟩` in the answer register. -/
theorem ReadoutSpecInMod.pad {n d T T' : ℕ} [NeZero d] {X : Type*}
    {spec : BitString n → X → Prop} (h : ReadoutSpecInMod d spec T) (hTT' : T ≤ T') :
    ReadoutSpecInMod d spec T' := by
  classical
  obtain ⟨W, hW, A, hA⟩ := h
  by_cases hEq : T = T'
  · subst hEq; exact ⟨W, hW, A, hA⟩
  have hlt : T < T' := lt_of_le_of_ne hTT' hEq
  let swapAns : Equiv.Perm (Fin n × ZMod d × (W × ZMod d)) :=
    { toFun := fun (i, b, w, b') => (i, b', w, b)
      invFun := fun (i, b, w, b') => (i, b', w, b)
      left_inv := fun ⟨_, _, _, _⟩ => rfl
      right_inv := fun ⟨_, _, _, _⟩ => rfl }
  let eAns : (Fin n × ZMod d × (W × ZMod d)) ≃ (Fin n × W × ZMod d) × ZMod d :=
    { toFun := fun (i, b, w, b') => ((i, w, b'), b)
      invFun := fun ((i, w, b'), b) => (i, b, w, b')
      left_inv := fun ⟨_, _, _, _⟩ => rfl
      right_inv := fun ⟨⟨_, _, _⟩, _⟩ => rfl }
  let eW : (Fin n × ZMod d × (W × ZMod d)) ≃ ZMod d × (Fin n × ZMod d × W) :=
    { toFun := fun (i, b, w, b') => (b', (i, b, w))
      invFun := fun (b', (i, b, w)) => (i, b, w, b')
      left_inv := fun ⟨_, _, _, _⟩ => rfl
      right_inv := fun ⟨_, _, _, _⟩ => rfl }
  let emb0 : (Fin n × ZMod d × W) ↪ (Fin n × ZMod d × (W × ZMod d)) :=
    ⟨fun p => eW.symm (0, p), fun _ _ h => (Prod.mk.inj (eW.symm.injective h)).2⟩
  let qftOnAns := fiberUnitary eAns (fun _ => qftEquiv d)
  let parkGate := (permUnitary swapAns).trans qftOnAns.symm
  let unparkGate := qftOnAns.trans (permUnitary swapAns)
  let liftW (U : ValueState (Fin n) (ZMod d) W ≃ₗᵢ[ℂ] ValueState (Fin n) (ZMod d) W) :=
    fiberUnitary eW (fun _ => U)
  let init' := LinearIsometry.piLpExtendByZero 2 ℂ ℂ emb0 A.init
  let U' : ℕ → ValueState (Fin n) (ZMod d) (W × ZMod d) ≃ₗᵢ[ℂ]
      ValueState (Fin n) (ZMod d) (W × ZMod d) := fun t =>
    if t < T then liftW (A.unitary t)
    else if t = T then (liftW (A.unitary T)).trans parkGate
    else if t = T' then unparkGate
    else LinearIsometryEquiv.refl ℂ _
  let A' : ReadoutAlgorithm n d (W × ZMod d) X T' :=
    { init := init'
      norm_init := by rw [LinearIsometry.norm_map, A.norm_init]
      unitary := U'
      readout := fun (i, b, w, _) => A.readout (i, b, w) }
  refine ⟨W × ZMod d, inferInstance, A', fun x p hp => ?_⟩
  have hvo : ∀ ψ : ValueState (Fin n) (ZMod d) W,
      modAddOracle d x (LinearIsometry.piLpExtendByZero 2 ℂ ℂ emb0 ψ) =
        LinearIsometry.piLpExtendByZero 2 ℂ ℂ emb0 (modAddOracle d x ψ) := fun ψ => by
    ext ⟨i, b, w, b'⟩
    rw [modAddOracle_apply]
    by_cases hb' : b' = 0
    · subst hb'
      change (LinearIsometry.piLpExtendByZero 2 ℂ ℂ emb0 ψ).ofLp
          (emb0 (i, b - (if x i then 1 else 0), w)) =
        (LinearIsometry.piLpExtendByZero 2 ℂ ℂ emb0 (modAddOracle d x ψ)).ofLp (emb0 (i, b, w))
      rw [extendByZero_apply_emb, extendByZero_apply_emb, modAddOracle_apply]
    · have hn1 : (i, b - (if x i then (1 : ZMod d) else 0), w, b') ∉ Set.range emb0 := by
        rintro ⟨⟨_, _, _⟩, h⟩; exact hb' (Prod.mk.inj (Prod.mk.inj (Prod.mk.inj h).2).2).2.symm
      have hn2 : (i, b, w, b') ∉ Set.range emb0 := by
        rintro ⟨⟨_, _, _⟩, h⟩; exact hb' (Prod.mk.inj (Prod.mk.inj (Prod.mk.inj h).2).2).2.symm
      rw [LinearIsometry.piLpExtendByZero_apply_eq_zero hn1,
        LinearIsometry.piLpExtendByZero_apply_eq_zero hn2]
  have hrun_lt : ∀ t, t < T →
      runValue (modAddStep d) (fun s => (U' s).toLinearIsometry) init' x t =
        LinearIsometry.piLpExtendByZero 2 ℂ ℂ emb0
          (runValue (modAddStep d) (fun s => (A.unitary s).toLinearIsometry) A.init x t) := by
    intro t ht
    induction t with
    | zero =>
      rw [runValue_modAddStep_zero, runValue_modAddStep_zero]
      simp only [U', ht, ↓reduceIte, init']
      exact fiberUnitary_extendByZero eW 0 (A.unitary 0) A.init
    | succ t ih =>
      rw [runValue_modAddStep_succ, runValue_modAddStep_succ, ih (by omega), hvo,
        show U' (t + 1) = liftW (A.unitary (t + 1)) by simp [U', ht]]
      exact fiberUnitary_extendByZero eW 0 (A.unitary (t + 1)) _
  have hrun_T : runValue (modAddStep d) (fun s => (U' s).toLinearIsometry) init' x T =
      parkGate (LinearIsometry.piLpExtendByZero 2 ℂ ℂ emb0 (A.finalState x)) := by
    cases T with
    | zero =>
      rw [runValue_modAddStep_zero]
      simp only [U', lt_irrefl, ↓reduceIte, LinearIsometryEquiv.trans_apply, init',
        ReadoutAlgorithm.finalState, runValue_modAddStep_zero]
      congr 1; exact fiberUnitary_extendByZero eW 0 (A.unitary 0) A.init
    | succ T₀ =>
      rw [runValue_modAddStep_succ, hrun_lt T₀ (Nat.lt_succ_self T₀), hvo,
        show U' (T₀ + 1) = (liftW (A.unitary (T₀ + 1))).trans parkGate by simp [U']]
      simp only [LinearIsometryEquiv.trans_apply, ReadoutAlgorithm.finalState,
        runValue_modAddStep_succ]
      congr 1; exact fiberUnitary_extendByZero eW 0 (A.unitary (T₀ + 1)) _
  have hpark_inv : ∀ ψ : ValueState (Fin n) (ZMod d) W,
      modAddOracle d x (parkGate (LinearIsometry.piLpExtendByZero 2 ℂ ℂ emb0 ψ)) =
        parkGate (LinearIsometry.piLpExtendByZero 2 ℂ ℂ emb0 ψ) := fun ψ => by
    ext ⟨i, b, w, b'⟩
    rw [modAddOracle_apply]
    change (qftOnAns.symm (permUnitary swapAns
        (LinearIsometry.piLpExtendByZero 2 ℂ ℂ emb0 ψ))).ofLp
        (i, b - (if x i then 1 else 0), w, b') =
      (qftOnAns.symm (permUnitary swapAns
        (LinearIsometry.piLpExtendByZero 2 ℂ ℂ emb0 ψ))).ofLp (i, b, w, b')
    simp only [qftOnAns, fiberUnitary_symm_apply, eAns, Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk,
      qftEquiv_symm_apply, permUnitary_apply]
    refine sum_congr rfl fun k _ => ?_
    by_cases hk : k = 0
    · subst hk; simp
    · have hn : (i, b', w, k) ∉ Set.range emb0 := by
        rintro ⟨⟨_, _, _⟩, h⟩; exact hk (Prod.mk.inj (Prod.mk.inj (Prod.mk.inj h).2).2).2.symm
      change _ * (LinearIsometry.piLpExtendByZero 2 ℂ ℂ emb0 ψ).ofLp (i, b', w, k) =
        _ * (LinearIsometry.piLpExtendByZero 2 ℂ ℂ emb0 ψ).ofLp (i, b', w, k)
      rw [LinearIsometry.piLpExtendByZero_apply_eq_zero hn, mul_zero, mul_zero]
  have hrun_mid : ∀ t, T ≤ t → t < T' →
      runValue (modAddStep d) (fun s => (U' s).toLinearIsometry) init' x t =
        parkGate (LinearIsometry.piLpExtendByZero 2 ℂ ℂ emb0 (A.finalState x)) := by
    intro t hTt ht'
    induction t, hTt using Nat.le_induction with
    | base => exact hrun_T
    | succ t hTt ih =>
      rw [runValue_modAddStep_succ, ih (by omega), hpark_inv,
        show U' (t + 1) = LinearIsometryEquiv.refl ℂ _ by
          simp [U', show ¬ t + 1 < T by omega, show t + 1 ≠ T by omega,
            show t + 1 ≠ T' by omega]]
      rfl
  have hfinal : A'.finalState x =
      LinearIsometry.piLpExtendByZero 2 ℂ ℂ emb0 (A.finalState x) := by
    obtain ⟨t₀, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : T' ≠ 0)
    change runValue (modAddStep d) (fun s => (U' s).toLinearIsometry) init' x (t₀ + 1) = _
    rw [runValue_modAddStep_succ, hrun_mid t₀ (by omega) (Nat.lt_succ_self t₀), hpark_inv,
      show U' (t₀ + 1) = unparkGate by
        simp [U', show ¬ t₀ + 1 < T by omega, show t₀ + 1 ≠ T by omega]]
    change (qftOnAns.trans (permUnitary swapAns))
      (((permUnitary swapAns).trans qftOnAns.symm) _) = _
    simp only [LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.apply_symm_apply]
    ext ⟨i, b, w, b'⟩
    simp [permUnitary_apply, swapAns]
  rw [hfinal]
  rcases p with ⟨i, b, w, b'⟩
  by_cases hb' : b' = 0
  · subst hb'
    change (LinearIsometry.piLpExtendByZero 2 ℂ ℂ emb0 (A.finalState x)).ofLp
      (emb0 (i, b, w)) = 0
    rw [extendByZero_apply_emb]
    exact hA x (i, b, w) hp
  · have hn : (i, b, w, b') ∉ Set.range emb0 := by
      rintro ⟨⟨_, _, _⟩, h⟩; exact hb' (Prod.mk.inj (Prod.mk.inj (Prod.mk.inj h).2).2).2.symm
    exact LinearIsometry.piLpExtendByZero_apply_eq_zero hn _

theorem ReadoutComputableInMod.pad {n d T T' : ℕ} [NeZero d] {X : Type*}
    {f : BitString n → X} (h : ReadoutComputableInMod d f T) (hTT' : T ≤ T') :
    ReadoutComputableInMod d f T' :=
  ReadoutSpecInMod.pad h hTT'

/-- Embedding a `k`-bit relational subinstance along `ι : Fin k ↪ Fin n` preserves query count
at the same modulus `d`. -/
theorem ReadoutSpecInMod.subinstance {k n d T : ℕ} [NeZero d] {X : Type*}
    {spec : BitString k → X → Prop} (h : ReadoutSpecInMod d spec T) (ι : Fin k ↪ Fin n) :
    ReadoutSpecInMod d (fun x : BitString n => spec (x ∘ ι)) T := by
  classical
  obtain ⟨W, hW, A, hA⟩ := h
  by_cases hk : k = 0
  · subst hk
    exfalso
    have : A.init = 0 := Subsingleton.elim _ _
    have h0 : ‖A.init‖ = 0 := by rw [this, norm_zero]
    linarith [A.norm_init]
  have hKne : Nonempty (Fin k) := ⟨⟨0, Nat.pos_of_ne_zero hk⟩⟩
  have hWne : Nonempty W := by
    by_contra hempty
    have : IsEmpty W := not_nonempty_iff.mp hempty
    have : A.init = 0 := Subsingleton.elim _ _
    have h0 : ‖A.init‖ = 0 := by rw [this, norm_zero]
    linarith [A.norm_init]
  let emb : (Fin k × ZMod d × W) ↪ (Fin n × ZMod d × W) :=
    ⟨fun (j, b, w) => (ι j, b, w), fun p₁ p₂ h => by
      rcases p₁ with ⟨j₁, b₁, w₁⟩; rcases p₂ with ⟨j₂, b₂, w₂⟩
      simp only [Prod.mk.injEq] at h
      exact Prod.ext (ι.injective h.1) (Prod.ext h.2.1 h.2.2)⟩
  let x₀ : X := A.readout (hKne.some, 0, hWne.some)
  let A' : ReadoutAlgorithm n d W X T :=
    { init := LinearIsometry.piLpExtendByZero 2 ℂ ℂ emb A.init
      norm_init := by rw [LinearIsometry.norm_map, A.norm_init]
      unitary := fun t => directSumUnitary emb (A.unitary t)
      readout := fun p =>
        if h : p.1 ∈ Set.range ι then
          A.readout ((Equiv.ofInjective ι ι.injective).symm ⟨p.1, h⟩, p.2.1, p.2.2)
        else x₀ }
  refine ⟨W, hW, A', fun x ⟨i, b, w⟩ hp => ?_⟩
  have hvo : ∀ ψ : ValueState (Fin k) (ZMod d) W,
      modAddOracle d x (LinearIsometry.piLpExtendByZero 2 ℂ ℂ emb ψ) =
        LinearIsometry.piLpExtendByZero 2 ℂ ℂ emb (modAddOracle d (x ∘ ι) ψ) := fun ψ => by
    ext ⟨i', b', w'⟩
    rw [modAddOracle_apply]
    by_cases hi : i' ∈ Set.range ι
    · obtain ⟨j, rfl⟩ := hi
      have he1 : (ι j, b' - (if x (ι j) then (1 : ZMod d) else 0), w') =
          emb (j, b' - (if (x ∘ ι) j then (1 : ZMod d) else 0), w') := rfl
      have he2 : (ι j, b', w') = emb (j, b', w') := rfl
      rw [he1, he2, extendByZero_apply_emb, extendByZero_apply_emb, modAddOracle_apply]
    · have hn1 : (i', b' - (if x i' then (1 : ZMod d) else 0), w') ∉ Set.range emb := by
        rintro ⟨⟨j, _, _⟩, h⟩; exact hi ⟨j, (Prod.mk.inj h).1⟩
      have hn2 : (i', b', w') ∉ Set.range emb := by
        rintro ⟨⟨j, _, _⟩, h⟩; exact hi ⟨j, (Prod.mk.inj h).1⟩
      rw [LinearIsometry.piLpExtendByZero_apply_eq_zero hn1,
        LinearIsometry.piLpExtendByZero_apply_eq_zero hn2]
  have hfinal : A'.finalState x =
      LinearIsometry.piLpExtendByZero 2 ℂ ℂ emb (A.finalState (x ∘ ι)) :=
    runValue_directSum emb A.unitary A.init (x ∘ ι) x hvo T
  rw [hfinal]
  by_cases hi : i ∈ Set.range ι
  · have hi' : i = ι ((Equiv.ofInjective ι ι.injective).symm ⟨i, hi⟩) :=
      (congrArg Subtype.val ((Equiv.ofInjective ι ι.injective).apply_symm_apply ⟨i, hi⟩)).symm
    have hread : A'.readout (i, b, w) =
        A.readout ((Equiv.ofInjective ι ι.injective).symm ⟨i, hi⟩, b, w) := by
      simp only [A', hi, ↓reduceDIte]
    conv_lhs => rw [hi']
    have he : (ι ((Equiv.ofInjective ι ι.injective).symm ⟨i, hi⟩), b, w) =
        emb ((Equiv.ofInjective ι ι.injective).symm ⟨i, hi⟩, b, w) := rfl
    rw [he, extendByZero_apply_emb]
    exact hA (x ∘ ι) _ (hread ▸ hp)
  · have hn : (i, b, w) ∉ Set.range emb := by
      rintro ⟨⟨j, _, _⟩, h⟩; exact hi ⟨j, (Prod.mk.inj h).1⟩
    exact LinearIsometry.piLpExtendByZero_apply_eq_zero hn _

theorem ReadoutComputableInMod.subinstance {k n d T : ℕ} [NeZero d] {X : Type*}
    {f : BitString k → X} (h : ReadoutComputableInMod d f T) (ι : Fin k ↪ Fin n) :
    ReadoutComputableInMod d (fun x : BitString n => f (x ∘ ι)) T :=
  ReadoutSpecInMod.subinstance h ι

/-- Modulus-divisibility lift for relational readout algorithms: if `m ∣ d` (`m, d ≥ 1`), any
`m`-modulus `T`-query readout algorithm lifts to modulus `d` with the same query count. -/
theorem ReadoutSpecInMod.modulusLift {n m d T : ℕ} [NeZero m] [NeZero d] {X : Type*}
    {spec : BitString n → X → Prop} (h : ReadoutSpecInMod m spec T) (hmd : m ∣ d) :
    ReadoutSpecInMod d spec T := by
  classical
  obtain ⟨W, hW, A, hA⟩ := h
  obtain ⟨q, hq⟩ := hmd
  have hq_pos : 0 < q := by
    rcases Nat.eq_zero_or_pos q with rfl | hqp
    · simp only [mul_zero] at hq; exact (NeZero.ne d hq).elim
    · exact hqp
  have hne_idx : Nonempty (Fin n × ZMod m × W) := by
    by_contra hempty
    have : IsEmpty (Fin n × ZMod m × W) := not_nonempty_iff.mp hempty
    have : A.init = 0 := Subsingleton.elim _ _
    have h0 : ‖A.init‖ = 0 := by rw [this, norm_zero]
    linarith [A.norm_init]
  let embZ : ZMod m ↪ ZMod d :=
    { toFun := fun b => ((b.val * q : ℕ) : ZMod d)
      inj' := fun b₁ b₂ heq => by
        have h1 : b₁.val * q < d := by
          rw [hq]; exact Nat.mul_lt_mul_of_pos_right b₁.val_lt hq_pos
        have h2 : b₂.val * q < d := by
          rw [hq]; exact Nat.mul_lt_mul_of_pos_right b₂.val_lt hq_pos
        have hval : b₁.val * q = b₂.val * q := by
          have := congrArg ZMod.val heq
          rwa [ZMod.val_natCast_of_lt h1, ZMod.val_natCast_of_lt h2] at this
        exact ZMod.val_injective m (Nat.eq_of_mul_eq_mul_right hq_pos hval) }
  have hchar : ∀ b : ZMod m, ZMod.stdAddChar (embZ b) = ZMod.stdAddChar b := fun b => by
    have hb : b = ((b.val : ℕ) : ZMod m) := (ZMod.natCast_zmod_val b).symm
    conv_rhs => rw [hb]
    change ZMod.stdAddChar ((b.val * q : ℕ) : ZMod d) = ZMod.stdAddChar ((b.val : ℕ) : ZMod m)
    rw [← Int.cast_natCast (b.val * q), ← Int.cast_natCast b.val,
      ZMod.stdAddChar_coe, ZMod.stdAddChar_coe, hq]
    congr 1
    push_cast
    have hqC : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hq_pos.ne'
    field_simp [hqC]
  let emb : (Fin n × ZMod m × W) ↪ (Fin n × ZMod d × W) :=
    ⟨fun (i, b, w) => (i, embZ b, w), fun p₁ p₂ heq => by
      rcases p₁ with ⟨i₁, b₁, w₁⟩; rcases p₂ with ⟨i₂, b₂, w₂⟩
      simp only [Prod.mk.injEq] at heq
      exact Prod.ext heq.1 (Prod.ext (embZ.injective heq.2.1) heq.2.2)⟩
  let eAns (k : ℕ) [NeZero k] : (Fin n × ZMod k × W) ≃ (Fin n × W) × ZMod k :=
    { toFun := fun (i, b, w) => ((i, w), b)
      invFun := fun ((i, w), b) => (i, b, w)
      left_inv := fun ⟨_, _, _⟩ => rfl
      right_inv := fun ⟨⟨_, _⟩, _⟩ => rfl }
  let Fm := fiberUnitary (eAns m) (fun _ => qftEquiv m)
  let Fd := fiberUnitary (eAns d) (fun _ => qftEquiv d)
  let init' := LinearIsometry.piLpExtendByZero 2 ℂ ℂ emb A.init
  let x₀ : X := A.readout hne_idx.some
  by_cases hT0 : T = 0
  · subst hT0
    refine ⟨W, hW,
      { init := init'
        norm_init := by rw [LinearIsometry.norm_map, A.norm_init]
        unitary := fun _ => directSumUnitary emb (A.unitary 0)
        readout := fun p =>
          if hp : p.2.1 ∈ Set.range embZ then
            A.readout (p.1, (Equiv.ofInjective embZ embZ.injective).symm ⟨p.2.1, hp⟩, p.2.2)
          else x₀ },
      fun x ⟨i, b, w⟩ hp => ?_⟩
    change (directSumUnitary emb (A.unitary 0) init').ofLp (i, b, w) = 0
    rw [directSumUnitary_extendByZero]
    by_cases hb : b ∈ Set.range embZ
    · obtain ⟨bm, rfl⟩ := hb
      have he : (i, embZ bm, w) = emb (i, bm, w) := rfl
      rw [he, extendByZero_apply_emb]
      refine hA x (i, bm, w) ?_
      have hsymm : (Equiv.ofInjective embZ embZ.injective).symm
          ⟨embZ bm, Set.mem_range_self _⟩ = bm :=
        (Equiv.ofInjective embZ embZ.injective).symm_apply_apply bm
      simpa [hsymm] using hp
    · have hn : (i, b, w) ∉ Set.range emb := by
        rintro ⟨⟨_, bm, _⟩, h⟩; exact hb ⟨bm, (Prod.mk.inj (Prod.mk.inj h).2).1⟩
      exact LinearIsometry.piLpExtendByZero_apply_eq_zero hn _
  let Uhat (t : ℕ) : ValueState (Fin n) (ZMod m) W ≃ₗᵢ[ℂ] ValueState (Fin n) (ZMod m) W :=
    if t = 0 then (A.unitary 0).trans Fm
    else if t = T then Fm.symm.trans (A.unitary T)
    else Fm.symm.trans ((A.unitary t).trans Fm)
  let Ud (t : ℕ) : ValueState (Fin n) (ZMod d) W ≃ₗᵢ[ℂ] ValueState (Fin n) (ZMod d) W :=
    if t = 0 then (directSumUnitary emb (Uhat 0)).trans Fd.symm
    else if t = T then Fd.trans (directSumUnitary emb (Uhat T))
    else Fd.trans ((directSumUnitary emb (Uhat t)).trans Fd.symm)
  have hOhat : ∀ {k : ℕ} [NeZero k] (x : BitString n)
      (ψ : ValueState (Fin n) (ZMod k) W) (i : Fin n) (b : ZMod k) (w : W),
      (fiberUnitary (eAns k) (fun _ => qftEquiv k)
        (modAddOracle k x ((fiberUnitary (eAns k) (fun _ => qftEquiv k)).symm ψ))).ofLp
          (i, b, w) =
        (if x i then ZMod.stdAddChar b else 1) * ψ.ofLp (i, b, w) := by
    intro k _ x ψ i b w
    rw [fiberUnitary_apply]
    change (qftEquiv k (WithLp.toLp 2 fun a =>
        (modAddOracle k x ((fiberUnitary (eAns k) (fun _ => qftEquiv k)).symm ψ)).ofLp
          (i, a, w))).ofLp b = _
    have hslice : (WithLp.toLp 2 fun a : ZMod k =>
        (modAddOracle k x ((fiberUnitary (eAns k) (fun _ => qftEquiv k)).symm ψ)).ofLp
          (i, a, w)) =
        modAddStep k (x i)
          ((qftEquiv k).symm (WithLp.toLp 2 fun a => ψ.ofLp (i, a, w))) := by
      ext a
      rw [WithLp.ofLp_toLp, modAddOracle_apply, modAddStep_apply, fiberUnitary_symm_apply]
      rfl
    rw [hslice, qft_modAddStep_qft_symm]
  have hOhat_emb : ∀ (x : BitString n) (φ : ValueState (Fin n) (ZMod m) W),
      Fd (modAddOracle d x (Fd.symm (LinearIsometry.piLpExtendByZero 2 ℂ ℂ emb φ))) =
        LinearIsometry.piLpExtendByZero 2 ℂ ℂ emb (Fm (modAddOracle m x (Fm.symm φ))) := by
    intro x φ
    ext ⟨i, b, w⟩
    rw [hOhat x]
    by_cases hb : b ∈ Set.range embZ
    · obtain ⟨bm, rfl⟩ := hb
      have he : (i, embZ bm, w) = emb (i, bm, w) := rfl
      rw [he, extendByZero_apply_emb, extendByZero_apply_emb, hOhat x, hchar]
    · have hn : (i, b, w) ∉ Set.range emb := by
        rintro ⟨⟨_, bm, _⟩, h⟩; exact hb ⟨bm, (Prod.mk.inj (Prod.mk.inj h).2).1⟩
      rw [LinearIsometry.piLpExtendByZero_apply_eq_zero hn,
        LinearIsometry.piLpExtendByZero_apply_eq_zero hn, mul_zero]
  have hrun_lt : ∀ (x : BitString n) (t : ℕ), t < T →
      runValue (modAddStep d) (fun s => (Ud s).toLinearIsometry) init' x t =
        Fd.symm (LinearIsometry.piLpExtendByZero 2 ℂ ℂ emb
          (Fm (runValue (modAddStep m) (fun s => (A.unitary s).toLinearIsometry) A.init x t))) := by
    intro x t ht
    induction t with
    | zero =>
      rw [runValue_modAddStep_zero, runValue_modAddStep_zero]
      simp only [Ud, ↓reduceIte, LinearIsometryEquiv.trans_apply, Uhat, init',
        directSumUnitary_extendByZero]
    | succ t ih =>
      rw [runValue_modAddStep_succ, runValue_modAddStep_succ, ih (by omega)]
      have hUd : Ud (t + 1) = Fd.trans ((directSumUnitary emb (Uhat (t + 1))).trans Fd.symm) := by
        simp [Ud, show t + 1 ≠ T by omega]
      have hUh : Uhat (t + 1) = Fm.symm.trans ((A.unitary (t + 1)).trans Fm) := by
        simp [Uhat, show t + 1 ≠ T by omega]
      rw [hUd, hUh]
      simp only [LinearIsometryEquiv.trans_apply, hOhat_emb, directSumUnitary_extendByZero,
        LinearIsometryEquiv.symm_apply_apply]
  let A' : ReadoutAlgorithm n d W X T :=
    { init := init'
      norm_init := by rw [LinearIsometry.norm_map, A.norm_init]
      unitary := Ud
      readout := fun p =>
        if hp : p.2.1 ∈ Set.range embZ then
          A.readout (p.1, (Equiv.ofInjective embZ embZ.injective).symm ⟨p.2.1, hp⟩, p.2.2)
        else x₀ }
  refine ⟨W, hW, A', fun x ⟨i, b, w⟩ hp => ?_⟩
  have hfinal : A'.finalState x =
      LinearIsometry.piLpExtendByZero 2 ℂ ℂ emb (A.finalState x) := by
    obtain ⟨t₀, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hT0
    unfold ReadoutAlgorithm.finalState
    rw [runValue_modAddStep_succ, hrun_lt x t₀ (Nat.lt_succ_self t₀)]
    have hUd : Ud (t₀ + 1) = Fd.trans (directSumUnitary emb (Uhat (t₀ + 1))) := by simp [Ud]
    have hUh : Uhat (t₀ + 1) = Fm.symm.trans (A.unitary (t₀ + 1)) := by simp [Uhat]
    dsimp only [A']
    rw [hUd, hUh]
    simp only [LinearIsometryEquiv.trans_apply, hOhat_emb, directSumUnitary_extendByZero,
      LinearIsometryEquiv.symm_apply_apply]
    rw [runValue_modAddStep_succ]
  rw [hfinal]
  by_cases hb : b ∈ Set.range embZ
  · obtain ⟨bm, rfl⟩ := hb
    have he : (i, embZ bm, w) = emb (i, bm, w) := rfl
    rw [he, extendByZero_apply_emb]
    refine hA x (i, bm, w) ?_
    have hsymm : (Equiv.ofInjective embZ embZ.injective).symm
        ⟨embZ bm, Set.mem_range_self _⟩ = bm :=
      (Equiv.ofInjective embZ embZ.injective).symm_apply_apply bm
    simpa [A', hsymm] using hp
  · have hn : (i, b, w) ∉ Set.range emb := by
      rintro ⟨⟨_, bm, _⟩, h⟩; exact hb ⟨bm, (Prod.mk.inj (Prod.mk.inj h).2).1⟩
    exact LinearIsometry.piLpExtendByZero_apply_eq_zero hn _

theorem ReadoutComputableInMod.modulusLift {n m d T : ℕ} [NeZero m] [NeZero d] {X : Type*}
    {f : BitString n → X} (h : ReadoutComputableInMod m f T) (hmd : m ∣ d) :
    ReadoutComputableInMod d f T :=
  ReadoutSpecInMod.modulusLift h hmd

/-- **Relational adaptive sequential composition (`bind`)**: running a `T₁`-query readout algorithm
satisfying `spec₁`, then a branch-dependent `T₂`-query readout algorithm satisfying `spec₂ a`
whenever `spec₁ x a` holds, compiles into a single flat `(T₁ + T₂)`-query readout algorithm at the
same modulus `d`. -/
theorem ReadoutSpecInMod.bind {n d T₁ T₂ : ℕ} [NeZero n] [NeZero d]
    {X₁ X₂ : Type*} [Finite X₁]
    {spec₁ : BitString n → X₁ → Prop} {spec₂ : X₁ → BitString n → X₂ → Prop}
    {spec_out : BitString n → X₂ → Prop}
    (h₁ : ReadoutSpecInMod d spec₁ T₁)
    (h₂ : ∀ a : X₁, ReadoutSpecInMod d (fun x b => spec₁ x a → spec₂ a x b) T₂)
    (hcomb : ∀ x a b, spec₁ x a → spec₂ a x b → spec_out x b) :
    ReadoutSpecInMod d spec_out (T₁ + T₂) := by
  classical
  have : Fintype X₁ := Fintype.ofFinite X₁
  obtain ⟨W₁, hW₁, A₁, hA₁⟩ := h₁
  choose W₂ hW₂ A₂ hA₂ using h₂
  have hW₁ne : Nonempty W₁ := by
    by_contra hempty
    have : IsEmpty W₁ := not_nonempty_iff.mp hempty
    have : A₁.init = 0 := Subsingleton.elim _ _
    have h0 : ‖A₁.init‖ = 0 := by rw [this, norm_zero]
    linarith [A₁.norm_init]
  have hW₂ne : ∀ a : X₁, Nonempty (W₂ a) := fun a => by
    by_contra hempty
    have : IsEmpty (W₂ a) := not_nonempty_iff.mp hempty
    have : (A₂ a).init = 0 := Subsingleton.elim _ _
    have h0 : ‖(A₂ a).init‖ = 0 := by rw [this, norm_zero]
    linarith [(A₂ a).norm_init]
  let i₀ : Fin n := ⟨0, NeZero.pos n⟩
  let w₁₀ : W₁ := hW₁ne.some
  let a₀ : X₁ := A₁.readout (i₀, 0, w₁₀)
  let eX : X₁ ≃ Fin (Fintype.card X₁) := Fintype.equivFin X₁
  let W₂u : Type := Σ k : Fin (Fintype.card X₁), W₂ (eX.symm k)
  let w₂₀ : W₂u := ⟨eX a₀, (hW₂ne (eX.symm (eX a₀))).some⟩
  let x₂₀ : X₂ := (A₂ a₀).readout (i₀, 0, (hW₂ne a₀).some)
  let emb₂ (a : X₁) : W₂ a ↪ W₁ × W₂u :=
    ⟨fun w => (w₁₀, ⟨eX a, cast (by rw [eX.symm_apply_apply]) w⟩), fun u₁ u₂ h => by
      have hheq : HEq (cast (by rw [eX.symm_apply_apply]) u₁ : W₂ (eX.symm (eX a)))
          (cast (by rw [eX.symm_apply_apply]) u₂ : W₂ (eX.symm (eX a))) :=
        (Sigma.mk.inj_iff.mp (Prod.mk.inj h).2).2
      have hcast := eq_of_heq hheq
      have hc : ∀ u : W₂ a,
          cast (by rw [eX.symm_apply_apply] : W₂ (eX.symm (eX a)) = W₂ a)
            (cast (by rw [eX.symm_apply_apply]) u) = u := fun u => cast_cast _ _ u
      rw [← hc u₁, ← hc u₂, hcast]⟩
  let B₂ (a : X₁) : ReadoutAlgorithm n d (W₁ × W₂u) X₂ T₂ :=
    (A₂ a).liftWorkspace (emb₂ a) x₂₀
  have hB₂ : ∀ a, (B₂ a).SatisfiesSpec (fun x b => spec₁ x a → spec₂ a x b) := fun a =>
    (A₂ a).liftWorkspace_satisfiesSpec (hA₂ a) (emb₂ a) x₂₀
  let G : Type := Fin n × ZMod d × W₁
  let g₀ : G := (i₀, 0, w₁₀)
  let e1 : (Fin n × ZMod d × (W₁ × W₂u × G)) ≃ (W₂u × G) × (Fin n × ZMod d × W₁) :=
    { toFun := fun (i, b, w₁, w₂, g) => ((w₂, g), (i, b, w₁))
      invFun := fun ((w₂, g), (i, b, w₁)) => (i, b, w₁, w₂, g)
      left_inv := fun ⟨_, _, _, _, _⟩ => rfl
      right_inv := fun ⟨⟨_, _⟩, _, _, _⟩ => rfl }
  let e2 : (Fin n × ZMod d × (W₁ × W₂u × G)) ≃ G × (Fin n × ZMod d × (W₁ × W₂u)) :=
    { toFun := fun (i, b, w₁, w₂, g) => (g, (i, b, w₁, w₂))
      invFun := fun (g, (i, b, w₁, w₂)) => (i, b, w₁, w₂, g)
      left_inv := fun ⟨_, _, _, _, _⟩ => rfl
      right_inv := fun ⟨_, _, _, _, _⟩ => rfl }
  let lift1 (U : ValueState (Fin n) (ZMod d) W₁ ≃ₗᵢ[ℂ] ValueState (Fin n) (ZMod d) W₁) :=
    fiberUnitary e1 (fun _ => U)
  let ctrl2 (F : G → (ValueState (Fin n) (ZMod d) (W₁ × W₂u) ≃ₗᵢ[ℂ]
      ValueState (Fin n) (ZMod d) (W₁ × W₂u))) :=
    fiberUnitary e2 F
  let swapG : Equiv.Perm (Fin n × ZMod d × (W₁ × W₂u × G)) :=
    { toFun := fun (i, b, w₁, w₂, g) => (g.1, g.2.1, g.2.2, w₂, (i, b, w₁))
      invFun := fun (i, b, w₁, w₂, g) => (g.1, g.2.1, g.2.2, w₂, (i, b, w₁))
      left_inv := fun ⟨_, _, _, _, ⟨_, _, _⟩⟩ => rfl
      right_inv := fun ⟨_, _, _, _, ⟨_, _, _⟩⟩ => rfl }
  let prep2 := ctrl2 fun p : G =>
    let B := B₂ (A₁.readout p)
    prepareUnitary (i₀, (0 : ZMod d), w₁₀, w₂₀) (B.unitary 0 B.init)
      (by rw [(B.unitary 0).norm_map, B.norm_init])
  let transGate := ((lift1 (A₁.unitary T₁)).trans (permUnitary swapG)).trans prep2
  let Ubind : ℕ → ValueState (Fin n) (ZMod d) (W₁ × W₂u × G) ≃ₗᵢ[ℂ]
      ValueState (Fin n) (ZMod d) (W₁ × W₂u × G) := fun t =>
    if t < T₁ then lift1 (A₁.unitary t)
    else if t = T₁ then transGate
    else ctrl2 fun p : G => (B₂ (A₁.readout p)).unitary (t - T₁)
  let embInit : (Fin n × ZMod d × W₁) ↪ (Fin n × ZMod d × (W₁ × W₂u × G)) :=
    ⟨fun p => e1.symm ((w₂₀, g₀), p), fun _ _ h => (Prod.mk.inj (e1.symm.injective h)).2⟩
  let initBind := LinearIsometry.piLpExtendByZero 2 ℂ ℂ embInit A₁.init
  let Abind : ReadoutAlgorithm n d (W₁ × W₂u × G) X₂ (T₁ + T₂) :=
    { init := initBind
      norm_init := by rw [LinearIsometry.norm_map, A₁.norm_init]
      unitary := Ubind
      readout := fun (i, b, w₁, w₂, g) => (B₂ (A₁.readout g)).readout (i, b, w₁, w₂) }
  refine ⟨W₁ × W₂u × G, inferInstance, Abind, fun x p hp => ?_⟩
  have hvo : ∀ ψ : ValueState (Fin n) (ZMod d) W₁,
      modAddOracle d x (LinearIsometry.piLpExtendByZero 2 ℂ ℂ embInit ψ) =
        LinearIsometry.piLpExtendByZero 2 ℂ ℂ embInit (modAddOracle d x ψ) := fun ψ => by
    ext ⟨i, b, w₁, w₂, g⟩
    rw [modAddOracle_apply]
    by_cases hwg : w₂ = w₂₀ ∧ g = g₀
    · obtain ⟨rfl, rfl⟩ := hwg
      change (LinearIsometry.piLpExtendByZero 2 ℂ ℂ embInit ψ).ofLp
          (embInit (i, b - (if x i then 1 else 0), w₁)) =
        (LinearIsometry.piLpExtendByZero 2 ℂ ℂ embInit (modAddOracle d x ψ)).ofLp
          (embInit (i, b, w₁))
      rw [extendByZero_apply_emb, extendByZero_apply_emb, modAddOracle_apply]
    · have hnot : ∀ b' : ZMod d, (i, b', w₁, w₂, g) ∉ Set.range embInit := fun b' => by
        rintro ⟨⟨_, _, _⟩, h⟩
        have hpair : (w₂₀, g₀) = (w₂, g) :=
          (Prod.mk.inj (Prod.mk.inj (Prod.mk.inj h).2).2).2
        exact hwg ⟨(Prod.mk.inj hpair).1.symm, (Prod.mk.inj hpair).2.symm⟩
      rw [LinearIsometry.piLpExtendByZero_apply_eq_zero (hnot _),
        LinearIsometry.piLpExtendByZero_apply_eq_zero (hnot _)]
  have hphase1 : ∀ t, t < T₁ →
      runValue (modAddStep d) (fun s => (Ubind s).toLinearIsometry) initBind x t =
        LinearIsometry.piLpExtendByZero 2 ℂ ℂ embInit
          (runValue (modAddStep d) (fun s => (A₁.unitary s).toLinearIsometry) A₁.init x t) := by
    intro t ht
    induction t with
    | zero =>
      rw [runValue_modAddStep_zero, runValue_modAddStep_zero]
      simp only [Ubind, ht, ↓reduceIte, initBind]
      exact fiberUnitary_extendByZero e1 (w₂₀, g₀) (A₁.unitary 0) A₁.init
    | succ t ih =>
      rw [runValue_modAddStep_succ, runValue_modAddStep_succ, ih (by omega), hvo,
        show Ubind (t + 1) = lift1 (A₁.unitary (t + 1)) by simp [Ubind, ht]]
      exact fiberUnitary_extendByZero e1 (w₂₀, g₀) (A₁.unitary (t + 1)) _
  let gSlice (ψ : ValueState (Fin n) (ZMod d) (W₁ × W₂u × G)) (g : G) :
      ValueState (Fin n) (ZMod d) (W₁ × W₂u) :=
    WithLp.toLp 2 fun (i, b, w₁, w₂) => ψ.ofLp (i, b, w₁, w₂, g)
  have hmid : ∀ g : G,
      gSlice (runValue (modAddStep d) (fun s => (Ubind s).toLinearIsometry) initBind x T₁) g =
        (A₁.finalState x).ofLp g •
          ((B₂ (A₁.readout g)).unitary 0 (B₂ (A₁.readout g)).init) := by
    intro g
    have hstepT : runValue (modAddStep d) (fun s => (Ubind s).toLinearIsometry) initBind x T₁ =
        prep2 (permUnitary swapG
          (LinearIsometry.piLpExtendByZero 2 ℂ ℂ embInit (A₁.finalState x))) := by
      cases T₁ with
      | zero =>
        rw [runValue_modAddStep_zero]
        simp only [Ubind, lt_irrefl, ↓reduceIte, transGate, LinearIsometryEquiv.trans_apply,
          initBind, ReadoutAlgorithm.finalState, runValue_modAddStep_zero]
        congr 2; exact fiberUnitary_extendByZero e1 (w₂₀, g₀) (A₁.unitary 0) A₁.init
      | succ T₀ =>
        rw [runValue_modAddStep_succ, hphase1 T₀ (Nat.lt_succ_self T₀), hvo,
          show Ubind (T₀ + 1) = transGate by simp [Ubind]]
        simp only [transGate, LinearIsometryEquiv.trans_apply, ReadoutAlgorithm.finalState,
          runValue_modAddStep_succ]
        congr 2; exact fiberUnitary_extendByZero e1 (w₂₀, g₀) (A₁.unitary (T₀ + 1)) _
    rw [hstepT]
    have hsw : gSlice (permUnitary swapG
        (LinearIsometry.piLpExtendByZero 2 ℂ ℂ embInit (A₁.finalState x))) g =
        (A₁.finalState x).ofLp g • ket (i₀, (0 : ZMod d), w₁₀, w₂₀) := by
      ext ⟨i, b, w₁, w₂⟩
      simp only [gSlice, permUnitary_apply, PiLp.smul_apply, smul_eq_mul, ket_apply]
      change (LinearIsometry.piLpExtendByZero 2 ℂ ℂ embInit (A₁.finalState x)).ofLp
        (g.1, g.2.1, g.2.2, w₂, (i, b, w₁)) = _
      by_cases hq : (i, b, w₁, w₂) = (i₀, 0, w₁₀, w₂₀)
      · rcases hq with ⟨rfl, rfl, rfl, rfl⟩
        change (LinearIsometry.piLpExtendByZero 2 ℂ ℂ embInit (A₁.finalState x)).ofLp
          (embInit g) = _
        rw [extendByZero_apply_emb]
        simp
      · have hn : (g.1, g.2.1, g.2.2, w₂, (i, b, w₁)) ∉ Set.range embInit := by
          rintro ⟨⟨_, _, _⟩, h⟩
          apply hq
          have hpair : (w₂₀, g₀) = (w₂, (i, b, w₁)) :=
            (Prod.mk.inj (Prod.mk.inj (Prod.mk.inj h).2).2).2
          have hw2 : w₂ = w₂₀ := (Prod.mk.inj hpair).1.symm
          have hib : (i, b, w₁) = g₀ := (Prod.mk.inj hpair).2.symm
          rcases Prod.mk.inj (Prod.mk.inj hib).2 with ⟨rfl, rfl⟩
          exact Prod.ext (Prod.mk.inj hib).1 (Prod.ext rfl (Prod.ext rfl hw2))
        rw [LinearIsometry.piLpExtendByZero_apply_eq_zero hn]
        simp [hq]
    ext ⟨i, b, w₁, w₂⟩
    simp only [gSlice, prep2, ctrl2, fiberUnitary_apply, e2, Equiv.coe_fn_mk,
      Equiv.coe_fn_symm_mk]
    change (prepareUnitary (i₀, (0 : ZMod d), w₁₀, w₂₀) _ _
      (gSlice (permUnitary swapG
        (LinearIsometry.piLpExtendByZero 2 ℂ ℂ embInit (A₁.finalState x))) g)).ofLp _ = _
    rw [hsw, map_smul, prepareUnitary_ket]
  have hphase2 : ∀ (s : ℕ) (g : G),
      gSlice (runValue (modAddStep d) (fun r => (Ubind r).toLinearIsometry) initBind x (T₁ + s)) g =
        (A₁.finalState x).ofLp g •
          runValue (modAddStep d) (fun r => ((B₂ (A₁.readout g)).unitary r).toLinearIsometry)
            (B₂ (A₁.readout g)).init x s := by
    intro s g
    induction s with
    | zero => simpa [runValue_modAddStep_zero] using hmid g
    | succ s ih =>
      rw [← Nat.add_assoc, runValue_modAddStep_succ, runValue_modAddStep_succ]
      have hUs : Ubind (T₁ + s + 1) =
          ctrl2 fun g' : G => (B₂ (A₁.readout g')).unitary (s + 1) := by
        simp [Ubind, show ¬ T₁ + s + 1 < T₁ by omega, show T₁ + s + 1 ≠ T₁ by omega,
          show T₁ + s + 1 - T₁ = s + 1 by omega]
      have hslice_ctrl : ∀ φ, gSlice (Ubind (T₁ + s + 1) φ) g =
          (B₂ (A₁.readout g)).unitary (s + 1) (gSlice φ g) := fun φ => by
        rw [hUs]; ext ⟨i, b, w₁, w₂⟩; simp [gSlice, ctrl2, fiberUnitary_apply, e2]
      have hslice_vo : ∀ φ, gSlice (modAddOracle d x φ) g =
          modAddOracle d x (gSlice φ g) := fun φ => by ext ⟨i, b, w₁, w₂⟩; simp [gSlice]
      rw [hslice_ctrl, hslice_vo, ih, map_smul, map_smul]
  rcases p with ⟨i, b, w₁, w₂, g⟩
  have hfinal := congrArg (fun φ => φ.ofLp (i, b, w₁, w₂)) (hphase2 T₂ g)
  change (Abind.finalState x).ofLp (i, b, w₁, w₂, g) = _ at hfinal
  rw [hfinal, PiLp.smul_apply, smul_eq_mul]
  by_cases hg : spec₁ x (A₁.readout g)
  · have hzero : ((B₂ (A₁.readout g)).finalState x).ofLp (i, b, w₁, w₂) = 0 :=
      hB₂ (A₁.readout g) x (i, b, w₁, w₂) fun h2 => hp (hcomb x (A₁.readout g) _ hg (h2 hg))
    change _ * ((B₂ (A₁.readout g)).finalState x).ofLp (i, b, w₁, w₂) = 0
    rw [hzero, mul_zero]
  · rw [hA₁ x g hg, zero_mul]

/-- Adaptive sequential composition with a deterministic second stage when `spec₁` holds. -/
theorem ReadoutSpecInMod.bind_fun {n d T₁ T₂ : ℕ} [NeZero n] [NeZero d]
    {X₁ X₂ : Type*} [Finite X₁]
    {spec₁ : BitString n → X₁ → Prop} {f : BitString n → X₂}
    (h₁ : ReadoutSpecInMod d spec₁ T₁)
    (h₂ : ∀ a : X₁, ReadoutSpecInMod d (fun x b => spec₁ x a → b = f x) T₂) :
    ReadoutComputableInMod d f (T₁ + T₂) :=
  h₁.bind h₂ (fun _ _ _ _ h => h)

/-- **Adaptive sequential composition (`bind`)** for deterministic readout algorithms. -/
theorem ReadoutComputableInMod.bind {n d T₁ T₂ : ℕ} [NeZero n] [NeZero d]
    {X₁ X₂ : Type*} [Finite X₁]
    {f₁ : BitString n → X₁} {f₂ : X₁ → BitString n → X₂}
    (h₁ : ReadoutComputableInMod d f₁ T₁)
    (h₂ : ∀ a : X₁, ReadoutComputableInMod d (f₂ a) T₂) :
    ReadoutComputableInMod d (fun x => f₂ (f₁ x) x) (T₁ + T₂) :=
  ReadoutSpecInMod.bind h₁
    (fun a => (h₂ a).weaken fun _ _ h _ => h)
    (fun x a b ha hb => by subst ha; exact hb)

/-- Adaptive sequential composition across two possibly different moduli `d₁, d₂`, lifting both
to `Nat.lcm d₁ d₂`. -/
theorem ReadoutComputableInMod.bind_lcm {n d₁ d₂ T₁ T₂ : ℕ} [NeZero n] [NeZero d₁] [NeZero d₂]
    {X₁ X₂ : Type*} [Finite X₁]
    {f₁ : BitString n → X₁} {f₂ : X₁ → BitString n → X₂}
    (h₁ : ReadoutComputableInMod d₁ f₁ T₁)
    (h₂ : ∀ a : X₁, ReadoutComputableInMod d₂ (f₂ a) T₂) :
    have : NeZero (Nat.lcm d₁ d₂) := ⟨Nat.lcm_ne_zero (NeZero.ne d₁) (NeZero.ne d₂)⟩
    ReadoutComputableInMod (Nat.lcm d₁ d₂) (fun x => f₂ (f₁ x) x) (T₁ + T₂) := by
  have : NeZero (Nat.lcm d₁ d₂) := ⟨Nat.lcm_ne_zero (NeZero.ne d₁) (NeZero.ne d₂)⟩
  exact (h₁.modulusLift (Nat.dvd_lcm_left d₁ d₂)).bind fun a =>
    (h₂ a).modulusLift (Nat.dvd_lcm_right d₁ d₂)

/-- Pre-composing a modulus-`2` relational readout algorithm with coordinatewise XOR by a fixed
`mask` costs zero additional queries. -/
theorem ReadoutSpecInMod.compXorMask {n T : ℕ} {X : Type*}
    {spec : BitString n → X → Prop} (h : ReadoutSpecInMod 2 spec T) (mask : BitString n) :
    ReadoutSpecInMod 2 (fun x : BitString n => spec (fun i => xor (x i) (mask i))) T := by
  obtain ⟨W, hW, A, hA⟩ := h
  let A' : ReadoutAlgorithm n 2 W X T :=
    { init := A.init
      norm_init := A.norm_init
      unitary := fun t => if t = 0 then A.unitary 0 else (modAddOracle 2 mask).trans (A.unitary t)
      readout := A.readout }
  refine ⟨W, hW, A', fun x p hp => ?_⟩
  have hcomb : ∀ ψ : ValueState (Fin n) (ZMod 2) W,
      modAddOracle 2 mask (modAddOracle 2 x ψ) =
        modAddOracle 2 (fun i => xor (x i) (mask i)) ψ := fun ψ => by
    ext ⟨i, b, w⟩
    simp only [modAddOracle_apply]
    have hsub : b - (if mask i then (1 : ZMod 2) else 0) - (if x i then 1 else 0) =
        b - (if xor (x i) (mask i) then 1 else 0) := by
      cases x i <;> cases mask i
      · simp
      · simp
      · simp
      · simp only [↓reduceIte, Bool.xor_self, Bool.false_eq_true, sub_zero]
        rw [sub_sub, show (1 : ZMod 2) + 1 = 0 from rfl, sub_zero]
    rw [hsub]
  have hrun : ∀ t : ℕ,
      runValue (modAddStep 2) (fun s => (A'.unitary s).toLinearIsometry) A'.init x t =
        runValue (modAddStep 2) (fun s => (A.unitary s).toLinearIsometry) A.init
          (fun i => xor (x i) (mask i)) t := fun t => by
    induction t with
    | zero =>
      rw [runValue_modAddStep_zero, runValue_modAddStep_zero]
      simp [A']
    | succ t ih =>
      rw [runValue_modAddStep_succ, runValue_modAddStep_succ, ih]
      simp only [A', Nat.add_one_ne_zero, ↓reduceIte, LinearIsometryEquiv.trans_apply, hcomb]
  have hfin : A'.finalState x = A.finalState (fun i => xor (x i) (mask i)) := hrun T
  rw [hfin]
  exact hA (fun i => xor (x i) (mask i)) p hp

theorem ReadoutComputableInMod.compXorMask {n T : ℕ} {X : Type*}
    {f : BitString n → X} (h : ReadoutComputableInMod 2 f T) (mask : BitString n) :
    ReadoutComputableInMod 2 (fun x : BitString n => f (fun i => xor (x i) (mask i))) T :=
  ReadoutSpecInMod.compXorMask h mask

/-- Pre-composing a modulus-`2` readout algorithm with bitwise negation costs zero extra queries. -/
theorem ReadoutComputableInMod.compNot {n T : ℕ} {X : Type*}
    {f : BitString n → X} (h : ReadoutComputableInMod 2 f T) :
    ReadoutComputableInMod 2 (fun x : BitString n => f (fun i => !x i)) T := by
  simpa using h.compXorMask (fun _ => true)

/-- Two-bit XOR (`x i ⊕ x j`) in `1` query for any even modulus `d` (Deutsch's algorithm). -/
theorem readoutComputableInMod_xor_of_two_dvd {n d : ℕ} [NeZero d] (h2d : 2 ∣ d)
    (i₀ j₀ : Fin n) :
    ReadoutComputableInMod d (fun x : BitString n => x i₀ != x j₀) 1 := by
  classical
  suffices h2 : ReadoutComputableInMod 2 (fun x : BitString n => x i₀ != x j₀) 1 from
    h2.modulusLift h2d
  by_cases hij : i₀ = j₀
  · subst hij
    have hconst : (fun x : BitString n => x i₀ != x i₀) = fun _ => false := by
      funext x; simp
    rw [hconst]
    have : NeZero n := ⟨fun h => by subst h; exact i₀.elim0⟩
    exact (readoutComputableInMod_const false).pad (Nat.zero_le 1)
  have : NeZero n := ⟨fun h => by subst h; exact i₀.elim0⟩
  let eAns : (Fin n × ZMod 2 × Unit) ≃ (Fin n × Unit) × ZMod 2 :=
    { toFun := fun (i, b, u) => ((i, u), b)
      invFun := fun ((i, u), b) => (i, b, u)
      left_inv := fun ⟨_, _, _⟩ => rfl
      right_inv := fun ⟨⟨_, _⟩, _⟩ => rfl }
  let F2 := fiberUnitary eAns (fun _ => qftEquiv 2)
  let c2 : ℂ := (((Real.sqrt 2)⁻¹ : ℝ) : ℂ)
  have hc2_sq : c2 ^ 2 = 1 / 2 := by
    rw [sq]; simpa [c2] using sqrt_inv_mul_sqrt_inv 2
  let emb2 : Bool ↪ (Fin n × ZMod 2 × Unit) :=
    ⟨fun b => (if b then j₀ else i₀, (1 : ZMod 2), ()), fun b₁ b₂ h => by
      cases b₁ <;> cases b₂ <;> simp_all [Ne.symm hij]⟩
  let hadB : EuclideanSpace ℂ Bool ≃ₗᵢ[ℂ] EuclideanSpace ℂ Bool :=
    { toFun := fun φ => WithLp.toLp 2 fun b =>
        c2 * (φ.ofLp false + (if b then -1 else 1) * φ.ofLp true)
      invFun := fun φ => WithLp.toLp 2 fun b =>
        c2 * (φ.ofLp false + (if b then -1 else 1) * φ.ofLp true)
      map_add' := fun φ₁ φ₂ => by ext b; simp only [PiLp.add_apply]; ring
      map_smul' := fun r φ => by
        ext b; simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]; ring
      left_inv := fun φ => by
        ext b; cases b <;> simp only [ite_true, Bool.false_eq_true, ite_false]
        · linear_combination (2 * φ.ofLp false) * hc2_sq
        · linear_combination (2 * φ.ofLp true) * hc2_sq
      right_inv := fun φ => by
        ext b; cases b <;> simp only [ite_true, Bool.false_eq_true, ite_false]
        · linear_combination (2 * φ.ofLp false) * hc2_sq
        · linear_combination (2 * φ.ofLp true) * hc2_sq
      norm_map' := fun φ => by
        have hsq : ‖(WithLp.toLp 2 fun b : Bool =>
            c2 * (φ.ofLp false + (if b then -1 else 1) * φ.ofLp true) :
            EuclideanSpace ℂ Bool)‖ ^ 2 = ‖φ‖ ^ 2 := by
          rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Fintype.sum_bool,
            Fintype.sum_bool]
          simp only [ite_true, Bool.false_eq_true, ite_false, norm_mul, mul_pow, c2,
            Complex.norm_real, Real.norm_eq_abs, sq_abs, inv_pow, Real.sq_sqrt zero_le_two,
            neg_one_mul, one_mul, ← sub_eq_add_neg, Complex.sq_norm, Complex.normSq_add,
            Complex.normSq_sub]
          ring
        exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq }
  let R := directSumUnitary emb2 hadB
  let init0 : ValueState (Fin n) (ZMod 2) Unit := ket (i₀, (1 : ZMod 2), ())
  let A : ReadoutAlgorithm n 2 Unit Bool 1 :=
    { init := init0
      norm_init := norm_ket _
      unitary := fun t => if t = 0 then R.trans F2.symm else F2.trans R
      readout := fun (i, _, _) => decide (i = j₀) }
  refine ⟨Unit, inferInstance, A, fun x ⟨i, b, u⟩ hne => ?_⟩
  have hOhat : ∀ (ψ : ValueState (Fin n) (ZMod 2) Unit) (i' : Fin n) (b' : ZMod 2) (u' : Unit),
      (F2 (modAddOracle 2 x (F2.symm ψ))).ofLp (i', b', u') =
        (if x i' then ZMod.stdAddChar b' else 1) * ψ.ofLp (i', b', u') := fun ψ i' b' u' => by
    rw [fiberUnitary_apply]
    change (qftEquiv 2 (WithLp.toLp 2 fun a =>
        (modAddOracle 2 x (F2.symm ψ)).ofLp (i', a, u'))).ofLp b' = _
    have hslice : (WithLp.toLp 2 fun a : ZMod 2 =>
        (modAddOracle 2 x (F2.symm ψ)).ofLp (i', a, u')) =
        modAddStep 2 (x i') ((qftEquiv 2).symm (WithLp.toLp 2 fun a => ψ.ofLp (i', a, u'))) := by
      ext a
      rw [WithLp.ofLp_toLp, modAddOracle_apply, modAddStep_apply, fiberUnitary_symm_apply]
      rfl
    rw [hslice, qft_modAddStep_qft_symm]
  have hR_init : ∀ (i' : Fin n) (b' : ZMod 2) (u' : Unit),
      (R init0).ofLp (i', b', u') =
        if (i', b', u') = (i₀, 1, ()) then c2
        else if (i', b', u') = (j₀, 1, ()) then c2 else 0 := fun i' b' u' => by
    by_cases h1 : (i', b', u') = (i₀, 1, ())
    · simp only [h1, ↓reduceIte]
      rw [show (i₀, (1 : ZMod 2), ()) = emb2 false from rfl, directSumUnitary_apply_emb]
      change c2 * (init0.ofLp (i₀, 1, ()) + 1 * init0.ofLp (j₀, 1, ())) = c2
      simp [init0, Ne.symm hij]
    · by_cases h2 : (i', b', u') = (j₀, 1, ())
      · simp only [h1, ↓reduceIte]
        simp only [h2, ↓reduceIte]
        rw [show (j₀, (1 : ZMod 2), ()) = emb2 true from rfl, directSumUnitary_apply_emb]
        change c2 * (init0.ofLp (i₀, 1, ()) + -1 * init0.ofLp (j₀, 1, ())) = c2
        simp [init0, Ne.symm hij]
      · have hn : (i', b', u') ∉ Set.range emb2 := by
          rintro ⟨bb, h⟩; cases bb
          · exact h1 h.symm
          · exact h2 h.symm
        rw [directSumUnitary_apply_of_not_mem _ _ _ hn]
        simp [init0, h1, h2]
  have hchar1 : ZMod.stdAddChar (1 : ZMod 2) = -1 := by
    change ZMod.stdAddChar ((1 : ℤ) : ZMod 2) = -1
    rw [ZMod.stdAddChar_coe]
    have harg : (2 * Real.pi * Complex.I * (1 : ℤ) / (2 : ℕ) : ℂ) = Real.pi * Complex.I := by
      push_cast; ring
    rw [harg, Complex.exp_pi_mul_I]
  let ψ1 := F2 (modAddOracle 2 x (F2.symm (R init0)))
  have hψ1 : ∀ (i' : Fin n) (b' : ZMod 2) (u' : Unit),
      ψ1.ofLp (i', b', u') =
        if (i', b', u') = (i₀, 1, ()) then (if x i₀ then -1 else 1) * c2
        else if (i', b', u') = (j₀, 1, ()) then (if x j₀ then -1 else 1) * c2 else 0 :=
    fun i' b' u' => by
      change (F2 (modAddOracle 2 x (F2.symm (R init0)))).ofLp (i', b', u') = _
      rw [hOhat, hR_init]
      by_cases h1 : (i', b', u') = (i₀, 1, ())
      · have hi' : i' = i₀ := (Prod.mk.inj h1).1
        have hb' : b' = 1 := (Prod.mk.inj (Prod.mk.inj h1).2).1
        rw [h1, hi', hb']
        cases x i₀ <;> simp [hchar1]
      · by_cases h2 : (i', b', u') = (j₀, 1, ())
        · have hi' : i' = j₀ := (Prod.mk.inj h2).1
          have hb' : b' = 1 := (Prod.mk.inj (Prod.mk.inj h2).2).1
          rw [h2, hi', hb']
          cases x j₀ <;> simp [hchar1, Ne.symm hij]
        · simp [h1, h2]
  have hfinal_eq : A.finalState x = R ψ1 := by
    unfold ReadoutAlgorithm.finalState
    rw [runValue_modAddStep_succ, runValue_modAddStep_zero]
    simp [A, LinearIsometryEquiv.trans_apply, ψ1]
  rw [hfinal_eq]
  have hfalse : ψ1.ofLp (emb2 false) = (if x i₀ then -1 else 1) * c2 := by
    change ψ1.ofLp (i₀, 1, ()) = _
    simpa using hψ1 i₀ 1 ()
  have htrue : ψ1.ofLp (emb2 true) = (if x j₀ then -1 else 1) * c2 := by
    change ψ1.ofLp (j₀, 1, ()) = _
    simpa [hij, Ne.symm hij] using hψ1 j₀ 1 ()
  by_cases h1 : (i, b, u) = (i₀, 1, ())
  · rw [h1, show (i₀, (1 : ZMod 2), ()) = emb2 false from rfl, directSumUnitary_apply_emb]
    have hhi : i = i₀ := (Prod.mk.inj h1).1
    have hxor : (x i₀ != x j₀) = true := by
      have hne' : decide (i = j₀) ≠ (x i₀ != x j₀) := hne
      rw [hhi, decide_eq_false hij] at hne'
      cases h : (x i₀ != x j₀) <;> simp_all
    change c2 * (ψ1.ofLp (emb2 false) + 1 * ψ1.ofLp (emb2 true)) = 0
    rw [hfalse, htrue]
    cases hx0 : x i₀ <;> cases hxj : x j₀ <;> simp_all
  · by_cases h2 : (i, b, u) = (j₀, 1, ())
    · rw [h2, show (j₀, (1 : ZMod 2), ()) = emb2 true from rfl, directSumUnitary_apply_emb]
      have hhj : i = j₀ := (Prod.mk.inj h2).1
      have hxor : (x i₀ != x j₀) = false := by
        have hne' : decide (i = j₀) ≠ (x i₀ != x j₀) := hne
        rw [hhj, decide_eq_true rfl] at hne'
        cases h : (x i₀ != x j₀) <;> simp_all
      change c2 * (ψ1.ofLp (emb2 false) + -1 * ψ1.ofLp (emb2 true)) = 0
      rw [hfalse, htrue]
      cases hx0 : x i₀ <;> cases hxj : x j₀ <;> simp_all
    · have hn : (i, b, u) ∉ Set.range emb2 := by
        rintro ⟨bb, h⟩; cases bb
        · exact h1 h.symm
        · exact h2 h.symm
      rw [directSumUnitary_apply_of_not_mem _ _ _ hn, hψ1]
      simp [h1, h2]

/-- Trivial `n`-query exact algorithm for any function `f : BitString n → X`: query all `n`
bits classically (at modulus `d = 2`) and post-process by `f`. -/
theorem readoutComputableInMod_full {n : ℕ} [NeZero n] {X : Type*} (f : BitString n → X) :
    ReadoutComputableInMod 2 f n := by
  suffices h : ∀ (k : ℕ) (hk : k ≤ n),
      ReadoutComputableInMod 2
        (fun (x : BitString n) (j : Fin k) => x ⟨j.1, lt_of_lt_of_le j.2 hk⟩) k by
    have h' := (h n le_rfl).map (fun (g : Fin n → Bool) => f fun j => g j)
    have hEq : ((fun (g : Fin n → Bool) => f fun j => g j) ∘
        fun (x : BitString n) (j : Fin n) => x ⟨j.1, lt_of_lt_of_le j.2 le_rfl⟩) = f := by
      funext x; rfl
    rwa [hEq] at h'
  intro k hk
  induction k with
  | zero =>
    have h0 : (fun (x : BitString n) (j : Fin 0) => x ⟨j.1, lt_of_lt_of_le j.2 hk⟩) =
        fun _ j => j.elim0 := by funext x j; exact j.elim0
    rw [h0]
    exact readoutComputableInMod_const (fun j : Fin 0 => j.elim0)
  | succ k ih =>
    have hprev := ih (Nat.le_of_succ_le hk)
    have hbit := readoutComputableInMod_coord (n := n) (d := 2) le_rfl ⟨k, hk⟩
    have hbind := hprev.bind fun (prev : Fin k → Bool) =>
      hbit.map fun (b : Bool) (j : Fin (k + 1)) =>
        if hj : j.1 < k then prev ⟨j.1, hj⟩ else b
    have hEq : (fun (x : BitString n) =>
        ((fun (b : Bool) (j : Fin (k + 1)) =>
            if hj : j.1 < k then x ⟨j.1, lt_of_lt_of_le hj (Nat.le_of_succ_le hk)⟩ else b) ∘
          fun x => x ⟨k, hk⟩) x) =
        fun (x : BitString n) (j : Fin (k + 1)) => x ⟨j.1, lt_of_lt_of_le j.2 hk⟩ := by
      funext x j
      dsimp only [Function.comp_apply]
      split_ifs with hj
      · rfl
      · congr 1; ext; dsimp; omega
    rwa [hEq] at hbind

theorem exactQuantumComputableIn_full {n : ℕ} [NeZero n] {X : Type*} [Fintype X]
    (f : BitString n → X) : ExactQuantumComputableIn f n :=
  (readoutComputableInMod_full f).toComputable

theorem exactQuantumQueryComplexity_le_length {n : ℕ} [NeZero n] {X : Type*} [Fintype X]
    (f : BitString n → X) : exactQuantumQueryComplexity f ≤ n :=
  exactQuantumQueryComplexity_le (exactQuantumComputableIn_full f)

end Readout

end CslibFrontier.Quantum
