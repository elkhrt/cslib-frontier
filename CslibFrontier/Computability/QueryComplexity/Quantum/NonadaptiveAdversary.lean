/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.QueryComplexity.Quantum.ValueAdversary
public import Mathlib.Data.Fintype.Pi

import CslibFrontier.Foundations.Quantum.Measurement.Overlap
import CslibFrontier.Foundations.Quantum.Measurement.ReadoutOverlap
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Non-Adaptive Quantum Query Oracles and Weighted Adversary Bounds

This module formalizes parallel non-adaptive quantum value-query algorithms (`O_x^k`, applying `k`
queries simultaneously in one input-independent round) together with the tuple weight-load reduction
and one-sided weighted adversary lower bound of Koiran, Landes, Portier, and Yao under
standard Lean axioms.

## Main definitions

* `CslibFrontier.QuantumQuery.NonadaptiveState`: state space
  `EuclideanSpace ℂ ((Fin k → ι) × (Fin k → V) × W)` for a single parallel round of `k` value
  queries.
* `CslibFrontier.QuantumQuery.nonadaptiveOracle`: parallel `k`-query unitary applying
  `step (x (I j))` independently on each of the `k` value registers.
* `CslibFrontier.QuantumQuery.nonadaptiveSlice`: amplitude slice at query tuple `I : Fin k → ι`.
* `CslibFrontier.QuantumQuery.SymWeightScheme`: symmetric positive adversary weight scheme `(R, w)`
  on `(ι → α) × (ι → α)`.
* `CslibFrontier.QuantumQuery.SymWeightScheme.tupleWtFst`,
  `CslibFrontier.QuantumQuery.SymWeightScheme.tupleLoadFst`: lifted `k`-tuple endpoint weight and
  load.

## Main results

* `CslibFrontier.QuantumQuery.one_sub_norm_inner_nonadaptiveOracle_le`: one parallel `k`-query round
  from an input-independent state `ψ₀` reduces state overlap by at most
  `2 * ∑_{I : x ∘ I ≠ y ∘ I} ‖nonadaptiveSlice I ψ₀‖²`.
* `CslibFrontier.QuantumQuery.SymWeightScheme.tupleLoadFst_le_mul_max` and
  `CslibFrontier.QuantumQuery.SymWeightScheme.div_mul_min_le_tupleRatio`: of Koiran, Landes,
  Portier, and Yao bounding the `k`-tuple load by `k` times the maximum coordinate load.
* `CslibFrontier.QuantumQuery.SymWeightScheme.mul_le_of_tuple_disturbance_fst` and
  `CslibFrontier.QuantumQuery.SymWeightScheme.mul_le_of_tuple_disturbance_snd`: general transfer
  from a tuple-query disturbance bound `Δ ≤ M * ∑_{I : x ∘ I ≠ y ∘ I} q(I)` to
  `Δ * wt(x) ≤ M * k * v_x`.
* `CslibFrontier.QuantumQuery.SymWeightScheme.one_sub_two_mul_sqrt_le_two_mul_nonadaptive`: Koiran,
  Landes, Portier, and Yao, for non-adaptive quantum query algorithms.
-/

public section

namespace CslibFrontier.QuantumQuery

open Finset Cslib.Quantum

section ParallelOracle

variable {ι α V W : Type*} [Fintype ι] [Fintype V] [Fintype W]

/-- State space `ℂ^{(Fin k → ι) × (Fin k → V) × W}` of a `k`-wide parallel non-adaptive quantum
value-query round. -/
abbrev NonadaptiveState (k : ℕ) (ι V W : Type*) :=
  ValueState (Fin k → ι) (Fin k → V) W

private noncomputable def prodCurry {A B : Type*} [Fintype A] [Fintype B] :
    EuclideanSpace ℂ (A × B) ≃ₗᵢ[ℂ] PiLp 2 (fun _ : A => EuclideanSpace ℂ B) :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (Equiv.sigmaEquivProd A B).symm).trans
    (LinearIsometryEquiv.piLpCurry ℂ 2 fun _ : A => fun _ : B => ℂ)

private noncomputable def mapSndIso {A B : Type*} [Fintype A] [Fintype B]
    (g : EuclideanSpace ℂ B ≃ₗᵢ[ℂ] EuclideanSpace ℂ B) :
    EuclideanSpace ℂ (A × B) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (A × B) :=
  (prodCurry (A := A) (B := B)).trans
    ((LinearIsometryEquiv.piLpCongrRight 2 fun _ : A => g).trans prodCurry.symm)

private theorem mapSndIso_apply {A B : Type*} [Fintype A] [Fintype B]
    (g : EuclideanSpace ℂ B ≃ₗᵢ[ℂ] EuclideanSpace ℂ B)
    (ψ : EuclideanSpace ℂ (A × B)) (a : A) (b : B) :
    (mapSndIso g ψ).ofLp (a, b) = (g (WithLp.toLp 2 fun b' => ψ.ofLp (a, b'))).ofLp b :=
  rfl

private noncomputable def mapFstIso {A B : Type*} [Fintype A] [Fintype B]
    (f : EuclideanSpace ℂ A ≃ₗᵢ[ℂ] EuclideanSpace ℂ A) :
    EuclideanSpace ℂ (A × B) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (A × B) :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (Equiv.prodComm A B)).trans
    ((mapSndIso (A := B) f).trans
      (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (Equiv.prodComm B A)))

private theorem mapFstIso_apply {A B : Type*} [Fintype A] [Fintype B]
    (f : EuclideanSpace ℂ A ≃ₗᵢ[ℂ] EuclideanSpace ℂ A)
    (ψ : EuclideanSpace ℂ (A × B)) (a : A) (b : B) :
    (mapFstIso f ψ).ofLp (a, b) = (f (WithLp.toLp 2 fun a' => ψ.ofLp (a', b))).ofLp a :=
  rfl

/-- Tuple-level unitary on `EuclideanSpace ℂ (Fin k → V)` applying `F j` to coordinate `j`. -/
noncomputable def tupleStep {k : ℕ}
    (F : Fin k → (EuclideanSpace ℂ V ≃ₗᵢ[ℂ] EuclideanSpace ℂ V)) :
    EuclideanSpace ℂ (Fin k → V) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin k → V) :=
  match k with
  | 0 => LinearIsometryEquiv.refl ℂ _
  | n + 1 =>
    let eSplit : (Fin (n + 1) → V) ≃ V × (Fin n → V) :=
      (Fin.consEquiv fun _ => V).symm
    (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ eSplit).trans <|
      (mapSndIso (tupleStep fun j => F j.succ)).trans <|
      (mapFstIso (F 0)).trans <|
      (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ eSplit.symm)

/-- When two `k`-tuples of unitaries agree at every coordinate, `tupleStep` agrees. -/
theorem tupleStep_congr {k : ℕ}
    {F G : Fin k → (EuclideanSpace ℂ V ≃ₗᵢ[ℂ] EuclideanSpace ℂ V)}
    (h : ∀ j, F j = G j) : tupleStep F = tupleStep G :=
  congrArg tupleStep (funext h)

/-- Action of `tupleStep F` on a product vector `⨂_{j : Fin k} φ j`. -/
theorem tupleStep_prod {k : ℕ}
    (F : Fin k → (EuclideanSpace ℂ V ≃ₗᵢ[ℂ] EuclideanSpace ℂ V))
    (φ : Fin k → EuclideanSpace ℂ V) :
    tupleStep F (WithLp.toLp 2 fun v => ∏ j : Fin k, (φ j).ofLp (v j)) =
      WithLp.toLp 2 fun v => ∏ j : Fin k, (F j (φ j)).ofLp (v j) := by
  induction k with
  | zero =>
    ext v
    rfl
  | succ n ih =>
    ext v
    dsimp only [tupleStep]
    simp only [LinearIsometryEquiv.trans_apply]
    let eSplit : (Fin (n + 1) → V) ≃ V × (Fin n → V) := (Fin.consEquiv fun _ => V).symm
    let ψ₀ : EuclideanSpace ℂ (Fin (n + 1) → V) :=
      WithLp.toLp 2 fun u => ∏ j : Fin (n + 1), (φ j).ofLp (u j)
    let ψ₁ := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ eSplit ψ₀
    have hψ₁ : ∀ (a : V) (vt : Fin n → V),
        ψ₁.ofLp (a, vt) = (φ 0).ofLp a * ∏ j : Fin n, (φ j.succ).ofLp (vt j) := fun a vt => by
      change ψ₀.ofLp (Fin.cons a vt) = _
      simp [ψ₀, Fin.prod_univ_succ]
    let ψ₂ := mapSndIso (tupleStep fun j => F j.succ) ψ₁
    have hψ₂ : ∀ (a : V) (vt : Fin n → V),
        ψ₂.ofLp (a, vt) = (φ 0).ofLp a * ∏ j : Fin n, (F j.succ (φ j.succ)).ofLp (vt j) := by
      intro a vt
      rw [mapSndIso_apply]
      have hslice : (WithLp.toLp 2 fun vt' => ψ₁.ofLp (a, vt') : EuclideanSpace ℂ (Fin n → V)) =
          (φ 0).ofLp a • WithLp.toLp 2 (fun vt' => ∏ j : Fin n, (φ j.succ).ofLp (vt' j)) := by
        ext vt'
        simp [hψ₁]
      rw [hslice, map_smul, ih (fun j => F j.succ) (fun j => φ j.succ)]
      simp
    let ψ₃ := mapFstIso (F 0) ψ₂
    have hψ₃ : ∀ (a : V) (vt : Fin n → V),
        ψ₃.ofLp (a, vt) = (F 0 (φ 0)).ofLp a * ∏ j : Fin n, (F j.succ (φ j.succ)).ofLp (vt j) := by
      intro a vt
      rw [mapFstIso_apply]
      have hslice : (WithLp.toLp 2 fun a' => ψ₂.ofLp (a', vt) : EuclideanSpace ℂ V) =
          (∏ j : Fin n, (F j.succ (φ j.succ)).ofLp (vt j)) • φ 0 := by
        ext a'
        simp [hψ₂, mul_comm]
      rw [hslice, map_smul]
      simp [mul_comm]
    change ψ₃.ofLp (v 0, Fin.tail v) = _
    rw [hψ₃, Fin.prod_univ_succ]
    rfl

/-- Parallel `k`-query oracle `O_x^k` applying `step (x (I j))` to each of the `k` value registers
controlled on the query-index tuple `I : Fin k → ι`. -/
noncomputable def nonadaptiveOracle (k : ℕ)
    (step : α → (EuclideanSpace ℂ V ≃ₗᵢ[ℂ] EuclideanSpace ℂ V))
    (x : ι → α) : NonadaptiveState k ι V W ≃ₗᵢ[ℂ] NonadaptiveState k ι V W :=
  valueOracle (fun vals : Fin k → α => tupleStep (fun j => step (vals j))) (fun I => x ∘ I)

/-- Coordinate action of `nonadaptiveOracle k step x` at `(I, vals, w)`. -/
theorem nonadaptiveOracle_apply (k : ℕ)
    (step : α → (EuclideanSpace ℂ V ≃ₗᵢ[ℂ] EuclideanSpace ℂ V))
    (x : ι → α) (ψ : NonadaptiveState k ι V W)
    (I : Fin k → ι) (vals : Fin k → V) (w : W) :
    (nonadaptiveOracle k step x ψ).ofLp (I, vals, w) =
      (tupleStep (fun j => step (x (I j)))
        (WithLp.toLp 2 fun vals' => ψ.ofLp (I, vals', w))).ofLp vals := by
  rw [nonadaptiveOracle, valueOracle_apply]
  rfl

/-- Norm preservation for `nonadaptiveOracle`. -/
theorem norm_nonadaptiveOracle (k : ℕ)
    (step : α → (EuclideanSpace ℂ V ≃ₗᵢ[ℂ] EuclideanSpace ℂ V))
    (x : ι → α) (ψ : NonadaptiveState k ι V W) :
    ‖nonadaptiveOracle k step x ψ‖ = ‖ψ‖ :=
  (nonadaptiveOracle k step x).norm_map ψ

/-- Amplitude slice of a `NonadaptiveState` at query tuple `I : Fin k → ι`. -/
abbrev nonadaptiveSlice {k : ℕ} (I : Fin k → ι) (ψ : NonadaptiveState k ι V W) :
    EuclideanSpace ℂ ((Fin k → V) × W) :=
  querySlice I ψ

/-- Parseval identity across query-index tuples `I : Fin k → ι`. -/
theorem sum_sq_norm_nonadaptiveSlice {k : ℕ} (ψ : NonadaptiveState k ι V W) :
    ∑ I : Fin k → ι, ‖nonadaptiveSlice I ψ‖ ^ 2 = ‖ψ‖ ^ 2 :=
  sum_sq_norm_querySlice ψ

/-- **One-round non-adaptive overlap loss bound**: applying `nonadaptiveOracle k step x` and
`nonadaptiveOracle k step y` to the *same* input-independent state `ψ` yields
`‖ψ‖² - ‖inner ℂ (O_x^k ψ) (O_y^k ψ)‖ ≤ 2 * ∑_{I : x ∘ I ≠ y ∘ I} ‖nonadaptiveSlice I ψ‖²`. -/
theorem one_sub_norm_inner_nonadaptiveOracle_le [DecidableEq α] (k : ℕ)
    (step : α → (EuclideanSpace ℂ V ≃ₗᵢ[ℂ] EuclideanSpace ℂ V))
    (x y : ι → α) {ψ : NonadaptiveState k ι V W} (hψ : ‖ψ‖ = 1) :
    1 - ‖inner ℂ (nonadaptiveOracle k step x ψ) (nonadaptiveOracle k step y ψ)‖ ≤
      2 * ∑ I : Fin k → ι with x ∘ I ≠ y ∘ I, ‖nonadaptiveSlice I ψ‖ ^ 2 := by
  have hge := norm_inner_valueOracle_valueOracle_ge
    (fun vals : Fin k → α => tupleStep (fun j => step (vals j)))
    (fun I : Fin k → ι => x ∘ I) (fun I : Fin k → ι => y ∘ I) ψ ψ
  have hself : ‖inner ℂ ψ ψ‖ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hψ]
    simp
  have hsq : ∀ I : Fin k → ι, ‖querySlice I ψ‖ * ‖querySlice I ψ‖ = ‖nonadaptiveSlice I ψ‖ ^ 2 :=
    fun _ => (sq _).symm
  simp only [hself, hsq] at hge
  rw [nonadaptiveOracle, nonadaptiveOracle]
  linarith

end ParallelOracle

/-! ### Symmetric adversary weight schemes and Koiran–Landes–Portier–Yao tuple load bounds -/

section WeightScheme

variable {ι α : Type*}

/-- A symmetric positive adversary weight scheme on `(ι → α) × (ι → α)`
: a relation `R` of input pairs equipped with nonnegative pair weights
`w(x, y)`.
-/
@[ext]
structure SymWeightScheme (ι α : Type*) where
  /-- Finite relation of input pairs `(x, y)`. -/
  R : Finset ((ι → α) × (ι → α))
  /-- Pair weights `w(x, y)`. -/
  w : (ι → α) × (ι → α) → ℝ
  /-- Pair weights are nonnegative on `R`. -/
  w_nonneg : ∀ p ∈ R, 0 ≤ w p

namespace SymWeightScheme

/-- First-endpoint weight `wt(x) = ∑_{(x, y) ∈ R} w(x, y)`. -/
noncomputable def wtFst [DecidableEq (ι → α)] (S : SymWeightScheme ι α) (x : ι → α) : ℝ :=
  ∑ p ∈ S.R with p.1 = x, S.w p

/-- Second-endpoint weight `wt(y) = ∑_{(x, y) ∈ R} w(x, y)`. -/
noncomputable def wtSnd [DecidableEq (ι → α)] (S : SymWeightScheme ι α) (y : ι → α) : ℝ :=
  ∑ p ∈ S.R with p.2 = y, S.w p

/-- First-endpoint coordinate load `v(x, i) = ∑_{(x, y) ∈ R, x i ≠ y i} w(x, y)`. -/
noncomputable def loadFst [DecidableEq α] [DecidableEq (ι → α)]
    (S : SymWeightScheme ι α) (x : ι → α) (i : ι) : ℝ :=
  ∑ p ∈ S.R with p.1 i ≠ p.2 i ∧ p.1 = x, S.w p

/-- Second-endpoint coordinate load `v(y, i) = ∑_{(x, y) ∈ R, x i ≠ y i} w(x, y)`. -/
noncomputable def loadSnd [DecidableEq α] [DecidableEq (ι → α)]
    (S : SymWeightScheme ι α) (y : ι → α) (i : ι) : ℝ :=
  ∑ p ∈ S.R with p.1 i ≠ p.2 i ∧ p.2 = y, S.w p

/-- Lifted `k`-tuple first-endpoint weight `WT({}^k x) = wt(x)`. -/
noncomputable def tupleWtFst [DecidableEq (ι → α)] (S : SymWeightScheme ι α) (x : ι → α) : ℝ :=
  S.wtFst x

/-- Lifted `k`-tuple first-endpoint load `V({}^k x, I) = ∑_{(x, y) ∈ R, x ∘ I ≠ y ∘ I} w(x, y)`. -/
noncomputable def tupleLoadFst [DecidableEq α] [DecidableEq (ι → α)]
    (S : SymWeightScheme ι α) {k : ℕ} (x : ι → α) (I : Fin k → ι) : ℝ :=
  ∑ p ∈ S.R with p.1 ∘ I ≠ p.2 ∘ I ∧ p.1 = x, S.w p

/-- Lifted `k`-tuple second-endpoint load `V({}^k y, I) = ∑_{(x, y) ∈ R, x ∘ I ≠ y ∘ I} w(x, y)`. -/
noncomputable def tupleLoadSnd [DecidableEq α] [DecidableEq (ι → α)]
    (S : SymWeightScheme ι α) {k : ℕ} (y : ι → α) (I : Fin k → ι) : ℝ :=
  ∑ p ∈ S.R with p.1 ∘ I ≠ p.2 ∘ I ∧ p.2 = y, S.w p

theorem wtFst_mk [DecidableEq (ι → α)] (R : Finset ((ι → α) × (ι → α)))
    (w : (ι → α) × (ι → α) → ℝ) (hw : ∀ p ∈ R, 0 ≤ w p) (x : ι → α) :
    (SymWeightScheme.mk R w hw).wtFst x = ∑ p ∈ R with p.1 = x, w p := by
  rw [wtFst]

theorem wtSnd_mk [DecidableEq (ι → α)] (R : Finset ((ι → α) × (ι → α)))
    (w : (ι → α) × (ι → α) → ℝ) (hw : ∀ p ∈ R, 0 ≤ w p) (y : ι → α) :
    (SymWeightScheme.mk R w hw).wtSnd y = ∑ p ∈ R with p.2 = y, w p := by
  rw [wtSnd]

theorem loadFst_mk [DecidableEq α] [DecidableEq (ι → α)] (R : Finset ((ι → α) × (ι → α)))
    (w : (ι → α) × (ι → α) → ℝ) (hw : ∀ p ∈ R, 0 ≤ w p) (x : ι → α) (i : ι) :
    (SymWeightScheme.mk R w hw).loadFst x i = ∑ p ∈ R with p.1 i ≠ p.2 i ∧ p.1 = x, w p := by
  rw [loadFst]

theorem loadSnd_mk [DecidableEq α] [DecidableEq (ι → α)] (R : Finset ((ι → α) × (ι → α)))
    (w : (ι → α) × (ι → α) → ℝ) (hw : ∀ p ∈ R, 0 ≤ w p) (y : ι → α) (i : ι) :
    (SymWeightScheme.mk R w hw).loadSnd y i = ∑ p ∈ R with p.1 i ≠ p.2 i ∧ p.2 = y, w p := by
  rw [loadSnd]

theorem tupleLoadFst_mk [DecidableEq α] [DecidableEq (ι → α)] (R : Finset ((ι → α) × (ι → α)))
    (w : (ι → α) × (ι → α) → ℝ) (hw : ∀ p ∈ R, 0 ≤ w p) {k : ℕ} (x : ι → α) (I : Fin k → ι) :
    (SymWeightScheme.mk R w hw).tupleLoadFst x I =
      ∑ p ∈ R with p.1 ∘ I ≠ p.2 ∘ I ∧ p.1 = x, w p := by
  rw [tupleLoadFst]

theorem tupleLoadSnd_mk [DecidableEq α] [DecidableEq (ι → α)] (R : Finset ((ι → α) × (ι → α)))
    (w : (ι → α) × (ι → α) → ℝ) (hw : ∀ p ∈ R, 0 ≤ w p) {k : ℕ} (y : ι → α) (I : Fin k → ι) :
    (SymWeightScheme.mk R w hw).tupleLoadSnd y I =
      ∑ p ∈ R with p.1 ∘ I ≠ p.2 ∘ I ∧ p.2 = y, w p := by
  rw [tupleLoadSnd]

theorem wtFst_nonneg [DecidableEq (ι → α)] (S : SymWeightScheme ι α) (x : ι → α) :
    0 ≤ S.wtFst x :=
  sum_nonneg fun p hp => S.w_nonneg p (mem_filter.mp hp).1

theorem wtSnd_nonneg [DecidableEq (ι → α)] (S : SymWeightScheme ι α) (y : ι → α) :
    0 ≤ S.wtSnd y :=
  sum_nonneg fun p hp => S.w_nonneg p (mem_filter.mp hp).1

theorem loadFst_nonneg [DecidableEq α] [DecidableEq (ι → α)] (S : SymWeightScheme ι α)
    (x : ι → α) (i : ι) : 0 ≤ S.loadFst x i :=
  sum_nonneg fun p hp => S.w_nonneg p (mem_filter.mp hp).1

theorem loadSnd_nonneg [DecidableEq α] [DecidableEq (ι → α)] (S : SymWeightScheme ι α)
    (y : ι → α) (i : ι) : 0 ≤ S.loadSnd y i :=
  sum_nonneg fun p hp => S.w_nonneg p (mem_filter.mp hp).1

/-- `V({}^k x, I) ≤ WT({}^k x)` for every `x` and index tuple `I`. -/
theorem tupleLoadFst_le_tupleWtFst [DecidableEq α] [DecidableEq (ι → α)]
    (S : SymWeightScheme ι α) {k : ℕ} (x : ι → α) (I : Fin k → ι) :
    S.tupleLoadFst x I ≤ S.tupleWtFst x := by
  refine sum_le_sum_of_subset_of_nonneg ?_ fun p hp _ => S.w_nonneg p (mem_filter.mp hp).1
  intro p hp
  exact mem_filter.mpr ⟨(mem_filter.mp hp).1, (mem_filter.mp hp).2.2⟩

/-- `V({}^k y, I) ≤ WT({}^k y)` for every `y` and index tuple `I`. -/
theorem tupleLoadSnd_le_wtSnd [DecidableEq α] [DecidableEq (ι → α)]
    (S : SymWeightScheme ι α) {k : ℕ} (y : ι → α) (I : Fin k → ι) :
    S.tupleLoadSnd y I ≤ S.wtSnd y := by
  refine sum_le_sum_of_subset_of_nonneg ?_ fun p hp _ => S.w_nonneg p (mem_filter.mp hp).1
  intro p hp
  exact mem_filter.mpr ⟨(mem_filter.mp hp).1, (mem_filter.mp hp).2.2⟩

/-- **Subadditivity of tuple load**: `V({}^k x, I) ≤ ∑_{j : Fin k} v(x, I j)`. -/
theorem tupleLoadFst_le_sum_loadFst [DecidableEq α] [DecidableEq (ι → α)]
    (S : SymWeightScheme ι α) {k : ℕ} (x : ι → α) (I : Fin k → ι) :
    S.tupleLoadFst x I ≤ ∑ j : Fin k, S.loadFst x (I j) := by
  simp only [tupleLoadFst, loadFst, sum_filter]
  rw [sum_comm]
  refine sum_le_sum fun p hp => ?_
  by_cases h2 : p.1 = x
  · subst h2
    by_cases h1 : p.1 ∘ I = p.2 ∘ I
    · have h1j : ∀ j, p.1 (I j) = p.2 (I j) := congrFun h1
      simp [h1, h1j]
    · have hex : ∃ j : Fin k, p.1 (I j) ≠ p.2 (I j) := by
        by_contra! hall
        exact h1 (funext hall)
      obtain ⟨j₀, hj₀⟩ := hex
      refine (le_of_eq ?_).trans
        (single_le_sum (fun j _ => by split_ifs <;> [exact S.w_nonneg p hp; exact le_rfl])
          (mem_univ j₀))
      simp [h1, hj₀]
  · simp [h2]

/-- Symmetric second-endpoint subadditivity: `V({}^k y, I) ≤ ∑_{j : Fin k} v(y, I j)`. -/
theorem tupleLoadSnd_le_sum_loadSnd [DecidableEq α] [DecidableEq (ι → α)]
    (S : SymWeightScheme ι α) {k : ℕ} (y : ι → α) (I : Fin k → ι) :
    S.tupleLoadSnd y I ≤ ∑ j : Fin k, S.loadSnd y (I j) := by
  simp only [tupleLoadSnd, loadSnd, sum_filter]
  rw [sum_comm]
  refine sum_le_sum fun p hp => ?_
  by_cases h2 : p.2 = y
  · subst h2
    by_cases h1 : p.1 ∘ I = p.2 ∘ I
    · have h1j : ∀ j, p.1 (I j) = p.2 (I j) := congrFun h1
      simp [h1, h1j]
    · have hex : ∃ j : Fin k, p.1 (I j) ≠ p.2 (I j) := by
        by_contra! hall
        exact h1 (funext hall)
      obtain ⟨j₀, hj₀⟩ := hex
      refine (le_of_eq ?_).trans
        (single_le_sum (fun j _ => by split_ifs <;> [exact S.w_nonneg p hp; exact le_rfl])
          (mem_univ j₀))
      simp [h1, hj₀]
  · simp [h2]

/-- If `v(x, I j) ≤ B` for every `j : Fin k`, then `V({}^k x, I) ≤ k * B`. -/
theorem tupleLoadFst_le_mul_max [DecidableEq α] [DecidableEq (ι → α)]
    (S : SymWeightScheme ι α) {k : ℕ} (x : ι → α) (I : Fin k → ι) {B : ℝ}
    (hB : ∀ j : Fin k, S.loadFst x (I j) ≤ B) :
    S.tupleLoadFst x I ≤ k * B :=
  (S.tupleLoadFst_le_sum_loadFst x I).trans <|
    (sum_le_sum fun j _ => hB j).trans_eq (by simp)

/-- ** of Koiran, Landes, Portier, and Yao**: if `r ≤ wt(x) / v(x, I j)` for all
`j : Fin k` (with `0 < V({}^k x, I)` and `0 ≤ r`), then `(1 / k) * r ≤
  WT({}^k x) / V({}^k x, I)`.
-/
theorem div_mul_min_le_tupleRatio [DecidableEq α] [DecidableEq (ι → α)]
    (S : SymWeightScheme ι α) {k : ℕ} (hk : 0 < k) (x : ι → α) (I : Fin k → ι)
    (hV : 0 < S.tupleLoadFst x I) {r : ℝ} (hr : 0 ≤ r)
    (hmin : ∀ j : Fin k, r * S.loadFst x (I j) ≤ S.wtFst x) :
    r / (k : ℝ) ≤ S.tupleWtFst x / S.tupleLoadFst x I := by
  have hkR : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  rw [div_le_div_iff₀ hkR hV, tupleWtFst]
  calc
    r * S.tupleLoadFst x I ≤ r * ∑ j : Fin k, S.loadFst x (I j) :=
      mul_le_mul_of_nonneg_left (S.tupleLoadFst_le_sum_loadFst x I) hr
    _ = ∑ j : Fin k, r * S.loadFst x (I j) := mul_sum _ _ _
    _ ≤ ∑ _j : Fin k, S.wtFst x := sum_le_sum fun j _ => hmin j
    _ = S.wtFst x * k := by simp [mul_comm]

section FintypeDomain

variable [Fintype ι]

/-- **First-endpoint non-adaptive transfer bound**: if a probability distribution `q` over
`k`-tuples `I : Fin k → ι` (`0 ≤ q I`, `∑ I, q I = 1`) satisfies
`Δ ≤ M * ∑_{I : x ∘ I ≠ y ∘ I} q I` for every `(x, y) ∈ R` (`0 ≤ M`), and `v(x, i) ≤ v_x` for all
`i : ι`, then `Δ * wt(x) ≤ M * k * v_x`. -/
theorem mul_le_of_tuple_disturbance_fst [DecidableEq α] [DecidableEq (ι → α)]
    (S : SymWeightScheme ι α) {k : ℕ} (q : (Fin k → ι) → ℝ)
    (hq_nonneg : ∀ I, 0 ≤ q I) (hq_sum : ∑ I : Fin k → ι, q I = 1)
    {Δ M : ℝ} (hM : 0 ≤ M)
    (hdist : ∀ p ∈ S.R, Δ ≤ M * ∑ I : Fin k → ι with p.1 ∘ I ≠ p.2 ∘ I, q I)
    (x : ι → α) {vx : ℝ} (hvx : ∀ i : ι, S.loadFst x i ≤ vx) :
    Δ * S.wtFst x ≤ M * (k : ℝ) * vx := by
  calc
    Δ * S.wtFst x = ∑ p ∈ S.R with p.1 = x, Δ * S.w p := by
      rw [wtFst, mul_sum]
    _ ≤ ∑ p ∈ S.R with p.1 = x,
        (M * ∑ I : Fin k → ι with p.1 ∘ I ≠ p.2 ∘ I, q I) * S.w p :=
      sum_le_sum fun p hp =>
        mul_le_mul_of_nonneg_right (hdist p (mem_filter.mp hp).1)
          (S.w_nonneg p (mem_filter.mp hp).1)
    _ = M * ∑ I : Fin k → ι, q I * S.tupleLoadFst x I := by
      rw [mul_sum]
      trans ∑ p ∈ S.R with p.1 = x, ∑ I : Fin k → ι,
        if p.1 ∘ I ≠ p.2 ∘ I then M * (q I * S.w p) else 0
      · refine sum_congr rfl fun p _ => ?_
        rw [mul_sum, sum_mul, sum_filter]
        exact sum_congr rfl fun I _ => by split_ifs <;> ring
      · rw [sum_comm]
        refine sum_congr rfl fun I _ => ?_
        simp only [tupleLoadFst, mul_sum, sum_filter]
        refine sum_congr rfl fun p _ => ?_
        by_cases h1 : p.1 = x <;> by_cases h2 : p.1 ∘ I ≠ p.2 ∘ I <;> simp [h1, h2]
    _ ≤ M * ∑ I : Fin k → ι, q I * ((k : ℝ) * vx) :=
      mul_le_mul_of_nonneg_left
        (sum_le_sum fun I _ =>
          mul_le_mul_of_nonneg_left (S.tupleLoadFst_le_mul_max x I fun j => hvx (I j))
            (hq_nonneg I))
        hM
    _ = M * (k : ℝ) * vx := by
      rw [← sum_mul, hq_sum, one_mul, mul_assoc]

/-- **Second-endpoint non-adaptive transfer bound**: symmetric dual of
`mul_le_of_tuple_disturbance_fst`. -/
theorem mul_le_of_tuple_disturbance_snd [DecidableEq α] [DecidableEq (ι → α)]
    (S : SymWeightScheme ι α) {k : ℕ} (q : (Fin k → ι) → ℝ)
    (hq_nonneg : ∀ I, 0 ≤ q I) (hq_sum : ∑ I : Fin k → ι, q I = 1)
    {Δ M : ℝ} (hM : 0 ≤ M)
    (hdist : ∀ p ∈ S.R, Δ ≤ M * ∑ I : Fin k → ι with p.1 ∘ I ≠ p.2 ∘ I, q I)
    (y : ι → α) {vy : ℝ} (hvy : ∀ i : ι, S.loadSnd y i ≤ vy) :
    Δ * S.wtSnd y ≤ M * (k : ℝ) * vy := by
  let S' : SymWeightScheme ι α :=
    { R := S.R.image Prod.swap
      w := fun p => S.w p.swap
      w_nonneg := fun p hp => by
        obtain ⟨p₀, hp₀, rfl⟩ := mem_image.mp hp
        exact S.w_nonneg p₀ hp₀ }
  have hswap_inj : Function.Injective (Prod.swap : (ι → α) × (ι → α) → (ι → α) × (ι → α)) :=
    Prod.swap_bijective.injective
  have hwt : S'.wtFst y = S.wtSnd y := by
    simp only [wtFst, wtSnd, S', filter_image, sum_image (fun _ _ _ _ h => hswap_inj h)]
    exact sum_congr (by ext ⟨a, b⟩; simp) (fun ⟨a, b⟩ _ => rfl)
  have hload : ∀ i : ι, S'.loadFst y i = S.loadSnd y i := fun i => by
    simp only [loadFst, loadSnd, S', filter_image, sum_image (fun _ _ _ _ h => hswap_inj h)]
    exact sum_congr (by ext ⟨a, b⟩; simp [ne_comm]) (fun ⟨a, b⟩ _ => rfl)
  rw [← hwt]
  refine S'.mul_le_of_tuple_disturbance_fst q hq_nonneg hq_sum hM ?_ y
    (fun i => (hload i).le.trans (hvy i))
  intro p hp
  obtain ⟨p₀, hp₀, rfl⟩ := mem_image.mp hp
  simpa [ne_comm] using hdist p₀ hp₀

/-- **Koiran–Landes–Portier–Yao,**: for any `k`-query non-adaptive quantum
value-query algorithm `(U₁ ∘ nonadaptiveOracle k step x) ψ₀` (`‖ψ₀‖ = 1`) distinguishing all
pairs `(x, y) ∈ S.R` with bounded error `ε` (`2 * ε ≤ 1`), if `mA * loadFst x i ≤ wtFst x` for some
`x` with `0 < wtFst x` and `mB * loadSnd y i ≤ wtSnd y` for some `y` with `0 < wtSnd y`, then
`(1 - 2 * √(ε * (1 - ε))) * max mA mB ≤ 2 * k`.
-/
theorem one_sub_two_mul_sqrt_le_two_mul_nonadaptive
    {V W β : Type*} [DecidableEq α] [DecidableEq (ι → α)] [DecidableEq β]
    [Fintype V] [Fintype W]
    (S : SymWeightScheme ι α) {k : ℕ}
    (step : α → (EuclideanSpace ℂ V ≃ₗᵢ[ℂ] EuclideanSpace ℂ V))
    (U₁ : NonadaptiveState k ι V W →ₗᵢ[ℂ] NonadaptiveState k ι V W)
    {ψ₀ : NonadaptiveState k ι V W} (hψ₀ : ‖ψ₀‖ = 1)
    (out : (Fin k → ι) × (Fin k → V) × W → β) (f : (ι → α) → β)
    (hne : ∀ p ∈ S.R, f p.1 ≠ f p.2) {ε : ℝ}
    (h₁ : ∀ p ∈ S.R, 1 - ε ≤ measureProb (U₁ (nonadaptiveOracle k step p.1 ψ₀)) {q | out q = f p.1})
    (h₂ : ∀ p ∈ S.R, 1 - ε ≤ measureProb (U₁ (nonadaptiveOracle k step p.2 ψ₀)) {q | out q = f p.2})
    (hε : 2 * ε ≤ 1)
    {x y : ι → α} (hx : 0 < S.wtFst x) (hy : 0 < S.wtSnd y)
    {mA mB : ℝ} (hmA : 0 < mA) (hmB : 0 < mB)
    (hA : ∀ i : ι, mA * S.loadFst x i ≤ S.wtFst x)
    (hB : ∀ i : ι, mB * S.loadSnd y i ≤ S.wtSnd y) :
    (1 - 2 * √(ε * (1 - ε))) * max mA mB ≤ 2 * k := by
  let q : (Fin k → ι) → ℝ := fun I => ‖nonadaptiveSlice I ψ₀‖ ^ 2
  have hq_nonneg : ∀ I, 0 ≤ q I := fun _ => sq_nonneg _
  have hq_sum : ∑ I : Fin k → ι, q I = 1 := by
    dsimp only [q]
    rw [sum_sq_norm_nonadaptiveSlice, hψ₀, one_pow]
  have hdist : ∀ p ∈ S.R,
      1 - 2 * √(ε * (1 - ε)) ≤ 2 * ∑ I : Fin k → ι with p.1 ∘ I ≠ p.2 ∘ I, q I := by
    intro p hp
    have hov := norm_inner_le_two_mul_sqrt_of_readout_ne
      (by rw [U₁.norm_map, norm_nonadaptiveOracle, hψ₀])
      (by rw [U₁.norm_map, norm_nonadaptiveOracle, hψ₀])
      out (hne p hp) (h₁ p hp) (h₂ p hp) hε
    rw [U₁.inner_map_map] at hov
    have hloss := one_sub_norm_inner_nonadaptiveOracle_le k step p.1 p.2 hψ₀
    linarith
  have hfst := S.mul_le_of_tuple_disturbance_fst q hq_nonneg hq_sum (by norm_num : (0 : ℝ) ≤ 2)
    hdist x (fun i => (le_div_iff₀' hmA).mpr (hA i))
  have hsnd := S.mul_le_of_tuple_disturbance_snd q hq_nonneg hq_sum (by norm_num : (0 : ℝ) ≤ 2)
    hdist y (fun i => (le_div_iff₀' hmB).mpr (hB i))
  have hmA_bound : (1 - 2 * √(ε * (1 - ε))) * mA ≤ 2 * k := by
    have hmul := mul_le_mul_of_nonneg_right hfst (div_nonneg hmA.le hx.le)
    have h1 : (1 - 2 * √(ε * (1 - ε))) * S.wtFst x * (mA / S.wtFst x) =
        (1 - 2 * √(ε * (1 - ε))) * mA := by field_simp [hx.ne']
    have h2 : 2 * (k : ℝ) * (S.wtFst x / mA) * (mA / S.wtFst x) = 2 * k := by
      field_simp [hx.ne', hmA.ne']
    linarith
  have hmB_bound : (1 - 2 * √(ε * (1 - ε))) * mB ≤ 2 * k := by
    have hmul := mul_le_mul_of_nonneg_right hsnd (div_nonneg hmB.le hy.le)
    have h1 : (1 - 2 * √(ε * (1 - ε))) * S.wtSnd y * (mB / S.wtSnd y) =
        (1 - 2 * √(ε * (1 - ε))) * mB := by field_simp [hy.ne']
    have h2 : 2 * (k : ℝ) * (S.wtSnd y / mB) * (mB / S.wtSnd y) = 2 * k := by
      field_simp [hy.ne', hmB.ne']
    linarith
  rcases le_total mA mB with hle | hle
  · rwa [max_eq_right hle]
  · rwa [max_eq_left hle]

end FintypeDomain

end SymWeightScheme

-- Non-vacuity witness on `Fin 2 → Bool`: constant-1 weight scheme on `{(00, 10), (00, 01)}` has
-- `wtFst 00 = 2` and `loadFst 00 i = 1`.
private example :
    let z : Fin 2 → Bool := fun _ => false
    let e₀ : Fin 2 → Bool := Function.update z 0 true
    let e₁ : Fin 2 → Bool := Function.update z 1 true
    let S : SymWeightScheme (Fin 2) Bool :=
      { R := {(z, e₀), (z, e₁)}
        w := fun _ => 1
        w_nonneg := fun _ _ => zero_le_one }
    S.wtFst z = 2 ∧ S.loadFst z 0 = 1 := by
  intro z e₀ e₁ S
  have hne : (z, e₀) ≠ (z, e₁) := by
    intro h
    have h0 := congrFun (Prod.mk.inj h).2 0
    simp [e₀, e₁, z] at h0
  refine ⟨?_, ?_⟩
  · have hfilt0 : ({p ∈ S.R | p.1 = z} : Finset _) = {(z, e₀), (z, e₁)} := by
      ext p
      simp only [S, mem_filter, mem_insert, mem_singleton]
      exact ⟨fun h => h.1, by rintro (rfl | rfl) <;> simp⟩
    rw [SymWeightScheme.wtFst, hfilt0]
    simp only [S, sum_const, card_pair hne]
    norm_num
  · have hfilt : ({p ∈ S.R | p.1 0 ≠ p.2 0 ∧ p.1 = z} : Finset _) = {(z, e₀)} := by
      ext p
      simp only [S, mem_filter, mem_insert, mem_singleton]
      constructor
      · rintro ⟨rfl | rfl, h0, _⟩
        · exact rfl
        · simp [e₁, z] at h0
      · rintro rfl
        simp [e₀, z]
    rw [SymWeightScheme.loadFst, hfilt]
    simp [S]

end WeightScheme

end CslibFrontier.QuantumQuery
