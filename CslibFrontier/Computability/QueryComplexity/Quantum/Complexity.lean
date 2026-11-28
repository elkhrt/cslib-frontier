module
-- upstream: candidate

public import Cslib.Computability.QueryComplexity.Measures
public import CslibFrontier.Computability.DecisionTree.Basic
public import CslibFrontier.Computability.QueryComplexity.Quantum.Search
public import CslibFrontier.Foundations.Data.BitString.Sign
import CslibFrontier.Computability.QueryComplexity.Quantum.Adversary
import CslibFrontier.Computability.QueryComplexity.Quantum.BitQuery
import CslibFrontier.Computability.QueryComplexity.Relations
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Bounded-Error Quantum Query Complexity and Polynomial Upper Bounds

Defines bounded-error quantum query computation and the complexity measure `Q_ε(f)` in the unitary
phase-query model `Cslib.Quantum.run`, proves existence of an optimal `ε`-error quantum query
algorithm on positive input lengths via an exact `N`-query bit-reading procedure, and establishes
fourth-power bounds `C(f) ≤ 256 Q_{1/3}(f)⁴` and `D(f) ≤ 20736 Q_{1/3}(f)⁴` for total Boolean
functions.

## Main definitions

* `CslibFrontier.QueryComplexity.QuantumComputes`: predicate stating that a `T`-query quantum
  algorithm in `Cslib.Quantum.run` computes `f` within error `ε`.
* `CslibFrontier.QueryComplexity.quantumComplexity`: minimum query count `Q_ε(f)` of a quantum
  query algorithm computing `f` within error `ε`.
* `CslibFrontier.QueryComplexity.quantumQueryComplexity`: bounded-error (`1/3`) quantum query
  complexity `Q_{1/3}(f)`.

## Main results

* `CslibFrontier.QueryComplexity.quantumComputes_zero_card`: exact `N`-query quantum algorithm
  computing any `N`-bit Boolean function when `N > 0`.
* `CslibFrontier.QueryComplexity.exists_quantumComputes_eq_quantumComplexity`: attainment of
  `Q_ε(f)` when `N > 0`.
* `CslibFrontier.QueryComplexity.certificateComplexity_le_mul_quantumQueryComplexity_pow_four`:
  `C(f) ≤ 256 Q_{1/3}(f)⁴`.
* `CslibFrontier.QueryComplexity.decisionTreeComplexity_le_mul_quantumQueryComplexity_pow_four`:
  `D(f) ≤ 20736 Q_{1/3}(f)⁴`.
-/

public section

namespace CslibFrontier.QueryComplexity

open Cslib Cslib.BitString Cslib.QueryComplexity Cslib.Quantum Finset
open scoped NNReal

/-- A `T`-query quantum query algorithm in `Cslib.Quantum.run` computes `f : BooleanFunction N`
with error at most `ε` when there exist a finite workspace `W`, step isometries `U`, a unit initial
state `ψ₀`, and an accepting outcome set `S` whose measurement probability on every input `x` is
within `ε` of `f x`. -/
@[expose]
public def QuantumComputes {N : ℕ} (ε : ℝ) (f : BooleanFunction N) (T : ℕ) : Prop :=
  ∃ (W : Type) (_ : Fintype W) (U : ℕ → State N W →ₗᵢ[ℂ] State N W)
    (ψ₀ : State N W) (S : Finset (Fin N × Bool × W)),
    ‖ψ₀‖ = 1 ∧ ∀ x : BitString N, |measureProb (run U ψ₀ x T) S - bitVal ℝ (f x)| ≤ ε

/-- Monotonicity of `QuantumComputes` in the allowed error `ε`. -/
public theorem QuantumComputes.mono {N : ℕ} {ε ε' : ℝ} {f : BooleanFunction N} {T : ℕ}
    (h : QuantumComputes ε f T) (hε : ε ≤ ε') : QuantumComputes ε' f T := by
  obtain ⟨W, hW, U, ψ₀, S, hψ, hx⟩ := h
  exact ⟨W, hW, U, ψ₀, S, hψ, fun x => (hx x).trans hε⟩

/-- Quantum query complexity `Q_ε(f)`: the minimum number of phase queries `T` of a quantum query
algorithm computing `f` with error at most `ε`. -/
public noncomputable def quantumComplexity {N : ℕ} (ε : ℝ≥0) (f : BooleanFunction N) : ℕ :=
  sInf {T : ℕ | QuantumComputes ε f T}

/-- Bounded-error (`1/3`) quantum query complexity `Q_{1/3}(f)`. -/
public noncomputable abbrev quantumQueryComplexity {N : ℕ} (f : BooleanFunction N) : ℕ :=
  quantumComplexity (1 / 3) f

/-- Upper-bound rule for `Q_ε(f)` from exhibiting a `T`-query quantum algorithm. -/
public theorem quantumComplexity_le {N : ℕ} {ε : ℝ≥0} {f : BooleanFunction N} {T : ℕ}
    (h : QuantumComputes ε f T) : quantumComplexity ε f ≤ T :=
  Nat.sInf_le h

private def saveBitPerm {N : ℕ} (j : Fin N) : Equiv.Perm (Fin N × Bool × BitString N) where
  toFun | (i, b, w) => (i, w j, Function.update w j b)
  invFun | (i, b, w) => (i, w j, Function.update w j b)
  left_inv | (i, b, w) => by simp
  right_inv | (i, b, w) => by simp

@[simp]
private theorem saveBitPerm_apply {N : ℕ} (j : Fin N) (i : Fin N) (b : Bool) (w : BitString N) :
    saveBitPerm j (i, b, w) = (i, w j, Function.update w j b) :=
  rfl

private def swapIdxPerm {N : ℕ} (j₁ j₂ : Fin N) : Equiv.Perm (Fin N × Bool × BitString N) where
  toFun | (i, b, w) => (Equiv.swap j₁ j₂ i, b, w)
  invFun | (i, b, w) => (Equiv.swap j₁ j₂ i, b, w)
  left_inv | (i, b, w) => by simp
  right_inv | (i, b, w) => by simp

@[simp]
private theorem swapIdxPerm_apply {N : ℕ} (j₁ j₂ : Fin N) (i : Fin N) (b : Bool)
    (w : BitString N) :
    swapIdxPerm j₁ j₂ (i, b, w) = (Equiv.swap j₁ j₂ i, b, w) :=
  rfl

private def readAllStepPerm {N : ℕ} : ℕ → Equiv.Perm (Fin N × Bool × BitString N)
  | 0 => 1
  | t + 1 =>
    if hlt : t < N then
      if hnext : t + 1 < N then
        swapIdxPerm ⟨t, hlt⟩ ⟨t + 1, hnext⟩ * saveBitPerm ⟨t, hlt⟩
      else
        saveBitPerm ⟨t, hlt⟩
    else 1

/-- Querying all `N` input bits via `bitQueryAlg` computes any `f : BooleanFunction N` with zero
error in `N` queries when `N > 0`. -/
public theorem quantumComputes_zero_card {N : ℕ} (hN : 0 < N) (f : BooleanFunction N) :
    QuantumComputes 0 f N := by
  classical
  let i₀ : Fin N := ⟨0, hN⟩
  let U : ℕ → State N (BitString N) →ₗᵢ[ℂ] State N (BitString N) :=
    bitQueryAlg N (readAllStepPerm (N := N)) LinearIsometry.id LinearIsometry.id
  let ψ₀ : State N (BitString N) := ket (i₀, false, fun _ => false)
  let S : Finset (Fin N × Bool × BitString N) := univ.filter fun (_, _, w) => f w = true
  refine ⟨BitString N, inferInstance, U, ψ₀, S, norm_ket _, fun x => ?_⟩
  have hperm (t : ℕ) (ht : t ≤ N) :
      bitQueryPerm readAllStepPerm x t (i₀, false, fun _ => false) =
        (if hlt : t < N then ⟨t, hlt⟩ else ⟨N - 1, by omega⟩,
          false, fun k : Fin N => if (k : ℕ) < t then x k else false) := by
    induction t with
    | zero =>
      simp [bitQueryPerm, readAllStepPerm, hN, i₀]
    | succ t ih =>
      have htlt : t < N := by omega
      rw [bitQueryPerm_succ, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ih htlt.le]
      simp only [htlt, ↓reduceDIte, bitFlip_apply, Bool.false_bne, readAllStepPerm]
      have hw_upd : Function.update (fun k : Fin N => if (k : ℕ) < t then x k else false)
          ⟨t, htlt⟩ (x ⟨t, htlt⟩) =
          fun k : Fin N => if (k : ℕ) < t + 1 then x k else false := by
        funext k
        by_cases hk : k = ⟨t, htlt⟩
        · subst hk; simp
        · rw [Function.update_of_ne hk]
          have hkv : (k : ℕ) ≠ t := fun h => hk (Fin.ext h)
          clear hk
          split_ifs <;> first | rfl | omega
      by_cases hnext : t + 1 < N
      · simp only [hnext, ↓reduceDIte, Equiv.Perm.mul_apply, saveBitPerm_apply,
          swapIdxPerm_apply, Equiv.swap_apply_left, lt_irrefl, ↓reduceIte, hw_upd]
      · have heq : (⟨t, htlt⟩ : Fin N) = ⟨N - 1, by omega⟩ := by
          apply Fin.ext; simp; omega
        simp only [hnext, ↓reduceDIte, saveBitPerm_apply, lt_irrefl, ↓reduceIte,
          hw_upd]
        rw [heq]
  have hrun : run U ψ₀ x N = ket (⟨N - 1, by omega⟩, false, x) := by
    dsimp [U, ψ₀]
    rw [run_bitQueryAlg, LinearIsometry.id_apply, LinearIsometry.id_apply, permute_ket,
      hperm N le_rfl]
    simp only [lt_irrefl, ↓reduceDIte]
    have hx_eq : (fun k : Fin N => if (k : ℕ) < N then x k else false) = x := by
      funext k; simp [k.isLt]
    rw [hx_eq]
  rw [hrun, measureProb_ket]
  cases hfx : f x <;> simp [S, hfx]

/-- When `N > 0`, some quantum algorithm attains `quantumComplexity ε f`. -/
public theorem exists_quantumComputes_eq_quantumComplexity {N : ℕ} (hN : 0 < N)
    (ε : ℝ≥0) (f : BooleanFunction N) :
    QuantumComputes ε f (quantumComplexity ε f) := by
  let A : Set ℕ := {T : ℕ | QuantumComputes ε f T}
  have hne : A.Nonempty := ⟨N, (quantumComputes_zero_card hN f).mono ε.coe_nonneg⟩
  exact Nat.sInf_mem hne

/-- Certificate complexity is at most a fourth-degree polynomial in bounded-error quantum query
complexity: `C(f) ≤ 256 Q_{1/3}(f)⁴`. -/
public theorem certificateComplexity_le_mul_quantumQueryComplexity_pow_four {N : ℕ}
    (f : BooleanFunction N) :
    certificateComplexity f ≤ 256 * quantumQueryComplexity f ^ 4 := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · exact (certificateComplexity_le_card f).trans (Nat.zero_le _)
  · obtain ⟨W, hW, U, ψ₀, S, hψ, hx⟩ :=
      exists_quantumComputes_eq_quantumComplexity hN (1 / 3) f
    have hx' : ∀ x : Fin N → Bool,
        |measureProb (run U ψ₀ x (quantumQueryComplexity f)) S - bitVal ℝ (f x)| ≤ 1 / 3 :=
      fun x => (hx x).trans (by norm_num)
    have hbs : blockSensitivity f ≤ 16 * quantumQueryComplexity f ^ 2 :=
      @blockSensitivity_le_sixteen_mul_sq N W hW f U ψ₀ hψ (quantumQueryComplexity f) S hx'
    calc
      certificateComplexity f ≤ blockSensitivity f ^ 2 :=
        certificateComplexity_le_blockSensitivity_sq f
      _ ≤ (16 * quantumQueryComplexity f ^ 2) ^ 2 := Nat.pow_le_pow_left hbs 2
      _ = 256 * quantumQueryComplexity f ^ 4 := by ring

/-- Deterministic decision-tree complexity is at most a fourth-degree polynomial in bounded-error
quantum query complexity: `D(f) ≤ 20736 Q_{1/3}(f)⁴`. -/
public theorem decisionTreeComplexity_le_mul_quantumQueryComplexity_pow_four {N : ℕ}
    (f : BooleanFunction N) :
    DecisionTree.complexity f ≤ 20736 * quantumQueryComplexity f ^ 4 := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · exact (DecisionTree.complexity_le_card f).trans (by simp)
  · obtain ⟨W, hW, U, ψ₀, S, hψ, hx⟩ :=
      exists_quantumComputes_eq_quantumComplexity hN (1 / 3) f
    have hx' : ∀ x : Fin N → Bool,
        |measureProb (run U ψ₀ x (quantumQueryComplexity f)) S - bitVal ℝ (f x)| ≤ 1 / 3 :=
      fun x => (hx x).trans (by norm_num)
    exact @complexity_le_mul_pow_four N W hW f U ψ₀ hψ (quantumQueryComplexity f) S hx'

end CslibFrontier.QueryComplexity
