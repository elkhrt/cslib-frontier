/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import Cslib.Computability.Circuit.Basic
public import CslibFrontier.Foundations.Data.Nat.PolynomialBound.Closure
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Data.Matrix.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

import Cslib.Computability.Circuit.Synthesis
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Nonuniform Algebraic BSS Complexity Classes and Bordered-Determinant Witness Elimination

Defines nonuniform Blum–Shub–Smale (BSS) circuit complexity classes over an arbitrary field `K`:
- `BSSAdditiveNP K`: nonuniform additive BSS `NP` circuits with addition, subtraction, and
  equality-to-zero branching, polynomially many constants in `K`, and polynomially many witness
  coordinates in `K`.
- `BSSRingP K`: nonuniform deterministic ring BSS `P` circuits with addition, subtraction,
  multiplication, and equality-to-zero branching.

Establishes two general algebraic results for additive BSS circuits and linear witness systems:
1. **Branch linear-form decomposition** (`circuit_accepts_iff_exists_branch`, `wireLinForm_bound`):
   fixing a branch vector `b : Fin C.size → Bool` collapses every wire of an additive BSS circuit
   to an integer linear form in `(z, y)` with coefficients bounded in magnitude by `2 ^ C.size`.
2. **Bordered-determinant continuous witness elimination** (`borderMat_det_eq`,
   `exists_linear_solution_iff`): over any field `K` of characteristic zero, solvability of a finite
   system of integer-linear equations and disequations in `y : Fin M → K` is equivalent to the
   existence of a maximal-rank integer pivot minor satisfying bordered-determinant rank,
   consistency, and disequation-compatibility conditions on `z : Fin D → K`.

## Main definitions

* `CslibFrontier.Complexity.RealAlgebraic.BSSAdditiveOp`, `bssAdditiveSignature`,
  `bssAdditiveInterp`: additive BSS gate basis `{+, -, zeroBranch}`.
* `CslibFrontier.Complexity.RealAlgebraic.BSSRingOp`, `bssRingSignature`, `bssRingInterp`:
  ring BSS gate basis `{+, -, ×, zeroBranch}`.
* `CslibFrontier.Complexity.RealAlgebraic.BSSAdditiveNP`, `BSSRingP`: nonuniform classes
  `NP_nu_{(K, +, -, =)}` and `P_nu_{(K, +, -, ×, =)}`.
* `CslibFrontier.Complexity.RealAlgebraic.subsetSumLang`: Subset Sum decision problem over a field.
* `CslibFrontier.Complexity.RealAlgebraic.borderMat`, `dotK`, `wireLinForm`, `BranchConsistent`:
  bordered matrices and branch-conditioned linear forms of additive BSS programs.

## Main results

* `CslibFrontier.Complexity.RealAlgebraic.subsetSumLang_mem_BSSAdditiveNP`: Subset Sum lies in
  `BSSAdditiveNP K` for every field `K`.
* `CslibFrontier.Complexity.RealAlgebraic.circuit_accepts_iff_exists_branch`: path decomposition of
  additive BSS circuits.
* `CslibFrontier.Complexity.RealAlgebraic.det_natAbs_le_factorial_mul_pow`, `borderMat_det_eq`:
  Leibniz height bound and Cramer block-triangular expansion for bordered determinants.
* `CslibFrontier.Complexity.RealAlgebraic.exists_linear_solution_iff`: exact elimination of
  continuous field witnesses over any field of characteristic zero.
-/

public section

namespace CslibFrontier.Complexity.RealAlgebraic

open Cslib Cslib.Circuits
open scoped BigOperators Matrix

/-- Operations of an additive BSS circuit over `(K, +, -, =)`: addition, subtraction, and
equality-to-zero branching (`if a = 0 then b else c`). -/
inductive BSSAdditiveOp where
  | add
  | sub
  | zeroBranch
  deriving DecidableEq

/-- Signature of additive BSS circuits over `(K, +, -, =)`. -/
abbrev bssAdditiveSignature : Signature where
  Op := BSSAdditiveOp
  Arity
    | .add | .sub => 2
    | .zeroBranch => 3

/-- Standard interpretation of additive BSS gates over a field `K`. -/
@[expose] noncomputable def bssAdditiveInterp (K : Type*) [Field K] :
    Interpretation bssAdditiveSignature K
  | .add, x => x 0 + x 1
  | .sub, x => x 0 - x 1
  | .zeroBranch, x => by classical exact if x 0 = 0 then x 1 else x 2

/-- Operations of a ring BSS circuit over `(K, +, -, ×, =)`: addition, subtraction,
multiplication, and equality-to-zero branching (`if a = 0 then b else c`). -/
inductive BSSRingOp where
  | add
  | sub
  | mul
  | zeroBranch
  deriving DecidableEq

/-- Signature of ring BSS circuits over `(K, +, -, ×, =)`. -/
abbrev bssRingSignature : Signature where
  Op := BSSRingOp
  Arity
    | .add | .sub | .mul => 2
    | .zeroBranch => 3

/-- Standard interpretation of ring BSS gates over a field `K`. -/
@[expose] noncomputable def bssRingInterp (K : Type*) [Field K] :
    Interpretation bssRingSignature K
  | .add, x => x 0 + x 1
  | .sub, x => x 0 - x 1
  | .mul, x => x 0 * x 1
  | .zeroBranch, x => by classical exact if x 0 = 0 then x 1 else x 2

/-- Evaluation of `bssRingInterp` on `.add`. -/
@[simp] theorem bssRingInterp_add {K : Type*} [Field K] (x : Fin 2 → K) :
    bssRingInterp K .add x = x 0 + x 1 := rfl

/-- Evaluation of `bssRingInterp` on `.sub`. -/
@[simp] theorem bssRingInterp_sub {K : Type*} [Field K] (x : Fin 2 → K) :
    bssRingInterp K .sub x = x 0 - x 1 := rfl

/-- Evaluation of `bssRingInterp` on `.mul`. -/
@[simp] theorem bssRingInterp_mul {K : Type*} [Field K] (x : Fin 2 → K) :
    bssRingInterp K .mul x = x 0 * x 1 := rfl

/-- Evaluation of `bssRingInterp` on `.zeroBranch`. -/
@[simp] theorem bssRingInterp_zeroBranch {K : Type*} [Field K] (x : Fin 3 → K) :
    bssRingInterp K .zeroBranch x =
      @ite K (x 0 = 0) (Classical.propDecidable _) (x 1) (x 2) := rfl

/-- Nonuniform additive BSS class `NP_nu_{(K, +, -, =)}`: decision problems over
`K^∞ = Σ n, Fin n → K` recognized by polynomial-size additive BSS circuits with polynomially many
nonuniform constants `α_n : Fin (c n) → K` and witness coordinates `y : Fin (m n) → K` (accepting
when the output wire evaluates to `0`). -/
def BSSAdditiveNP (K : Type*) [Field K] : Set (Set (Σ n : ℕ, Fin n → K)) :=
  {L | ∃ (c m : ℕ → ℕ) (α : ∀ n, Fin (c n) → K)
      (C : ∀ n, Circuit bssAdditiveSignature ((n + c n) + m n) 1),
    PolynomiallyBounded c ∧ PolynomiallyBounded m ∧
    PolynomiallyBounded (fun n => (C n).size) ∧
    ∀ (n : ℕ) (x : Fin n → K),
      (⟨n, x⟩ : Σ n : ℕ, Fin n → K) ∈ L ↔
        ∃ y : Fin (m n) → K,
          (C n).eval (bssAdditiveInterp K) (Fin.append (Fin.append x (α n)) y) 0 = 0}

/-- Nonuniform ring BSS class `P_nu_{(K, +, -, ×, =)}`: decision problems over
`K^∞ = Σ n, Fin n → K` decided deterministically by polynomial-size ring BSS circuits with
polynomially many nonuniform constants `α_n : Fin (c n) → K` (accepting when the output wire
evaluates to `0`). -/
def BSSRingP (K : Type*) [Field K] : Set (Set (Σ n : ℕ, Fin n → K)) :=
  {L | ∃ (c : ℕ → ℕ) (α : ∀ n, Fin (c n) → K)
      (C : ∀ n, Circuit bssRingSignature (n + c n) 1),
    PolynomiallyBounded c ∧ PolynomiallyBounded (fun n => (C n).size) ∧
    ∀ (n : ℕ) (x : Fin n → K),
      (⟨n, x⟩ : Σ n : ℕ, Fin n → K) ∈ L ↔
        (C n).eval (bssRingInterp K) (Fin.append x (α n)) 0 = 0}

/-- Membership characterization for `BSSAdditiveNP`. -/
theorem mem_BSSAdditiveNP {K : Type*} [Field K] {L : Set (Σ n : ℕ, Fin n → K)} :
    L ∈ BSSAdditiveNP K ↔
      ∃ (c m : ℕ → ℕ) (α : ∀ n, Fin (c n) → K)
        (C : ∀ n, Circuit bssAdditiveSignature ((n + c n) + m n) 1),
      PolynomiallyBounded c ∧ PolynomiallyBounded m ∧
      PolynomiallyBounded (fun n => (C n).size) ∧
      ∀ (n : ℕ) (x : Fin n → K),
        (⟨n, x⟩ : Σ n : ℕ, Fin n → K) ∈ L ↔
          ∃ y : Fin (m n) → K,
            (C n).eval (bssAdditiveInterp K) (Fin.append (Fin.append x (α n)) y) 0 = 0 :=
  Iff.rfl

/-- Membership characterization for `BSSRingP`. -/
theorem mem_BSSRingP {K : Type*} [Field K] {L : Set (Σ n : ℕ, Fin n → K)} :
    L ∈ BSSRingP K ↔
      ∃ (c : ℕ → ℕ) (α : ∀ n, Fin (c n) → K)
        (C : ∀ n, Circuit bssRingSignature (n + c n) 1),
      PolynomiallyBounded c ∧ PolynomiallyBounded (fun n => (C n).size) ∧
      ∀ (n : ℕ) (x : Fin n → K),
        (⟨n, x⟩ : Σ n : ℕ, Fin n → K) ∈ L ↔
          (C n).eval (bssRingInterp K) (Fin.append x (α n)) 0 = 0 :=
  Iff.rfl

/-- Subset Sum over a field `K`: given `(x_0, x_1, ..., x_{n-1}) ∈ K^n`, decide whether some subset
of `{x_1, ..., x_{n-1}}` sums to `x_0` (trivially true for `n = 0`). -/
def subsetSumLang (K : Type*) [Field K] : Set (Σ n : ℕ, Fin n → K) :=
  {p | ∃ s : Fin p.1 → Bool,
    (∑ i : Fin p.1, if i.val = 0 then -(p.2 i) else if s i then p.2 i else 0) = 0}

/-- Membership characterization for `subsetSumLang`. -/
theorem mem_subsetSumLang {K : Type*} [Field K] {n : ℕ} {x : Fin n → K} :
    (⟨n, x⟩ : Σ n : ℕ, Fin n → K) ∈ subsetSumLang K ↔
      ∃ s : Fin n → Bool,
        (∑ i : Fin n, if i.val = 0 then -(x i) else if s i then x i else 0) = 0 :=
  Iff.rfl

/-- Subset Sum belongs to `BSSAdditiveNP K` for every field `K`. -/
theorem subsetSumLang_mem_BSSAdditiveNP (K : Type*) [Field K] :
    subsetSumLang K ∈ BSSAdditiveNP K := by
  classical
  let I := bssAdditiveInterp K
  have hcirc (n : ℕ) :
      ∃ C : Circuit bssAdditiveSignature ((n + 1) + n) 1,
        C.size ≤ 2 * n + 2 ∧
        ∀ (x : Fin n → K) (y : Fin n → K),
          C.eval I (Fin.append (Fin.append x (fun _ : Fin 1 => (0 : K))) y) 0 =
            ∑ i : Fin n, if i.val = 0 then -(x i) else if y i = 0 then 0 else x i := by
    let N := (n + 1) + n
    let zeroWire : Fin N := Fin.castAdd n (Fin.natAdd n 0)
    let termFn (i : Fin n) : (Fin N → K) → K := fun w =>
      if i.val = 0 then w zeroWire - w (Fin.castAdd n (Fin.castAdd 1 i))
      else if w (Fin.natAdd (n + 1) i) = 0 then w zeroWire
      else w (Fin.castAdd n (Fin.castAdd 1 i))
    let prefFn : ∀ k ≤ n, (Fin N → K) → K := fun k _ w =>
      w zeroWire + ∑ i : Fin n, if i.val < k then termFn i w else 0
    have hstep : ∀ k (hk : k ≤ n),
        Synthesis I (inputs N) {prefFn k hk} (2 * k) := by
      intro k
      induction k with
      | zero =>
        intro hk
        have hEq : prefFn 0 hk = fun w => w zeroWire := by
          funext w
          simp [prefFn]
        exact Synthesis.of_mem (hEq ▸ Set.mem_range_self zeroWire)
      | succ k ih =>
        intro hk
        have hk' : k ≤ n := Nat.le_of_succ_le hk
        let idx : Fin n := ⟨k, hk⟩
        have hprev := ih hk'
        have hterm : Synthesis I (inputs N ∪ {prefFn k hk'}) {termFn idx} 1 := by
          by_cases h0 : k = 0
          · have hsub : Synthesis I (inputs N ∪ {prefFn k hk'})
                {fun w => w zeroWire - w (Fin.castAdd n (Fin.castAdd 1 idx))} 1 :=
              Synthesis.gate (σ := bssAdditiveSignature) .sub
                ![fun w => w zeroWire, fun w => w (Fin.castAdd n (Fin.castAdd 1 idx))]
                (fun j => by fin_cases j <;> exact Set.mem_union_left _ (Set.mem_range_self _))
            refine hsub.mono Set.Subset.rfl ?_ le_rfl
            rw [Set.singleton_subset_iff]
            funext w; simp [termFn, idx, h0]
          · have hbr : Synthesis I (inputs N ∪ {prefFn k hk'})
                {fun w => if w (Fin.natAdd (n + 1) idx) = 0 then w zeroWire
                  else w (Fin.castAdd n (Fin.castAdd 1 idx))} 1 :=
              Synthesis.gate (σ := bssAdditiveSignature) .zeroBranch
                ![fun w => w (Fin.natAdd (n + 1) idx), fun w => w zeroWire,
                  fun w => w (Fin.castAdd n (Fin.castAdd 1 idx))]
                (fun j => by fin_cases j <;> exact Set.mem_union_left _ (Set.mem_range_self _))
            refine hbr.mono Set.Subset.rfl ?_ le_rfl
            rw [Set.singleton_subset_iff]
            funext w; simp [termFn, idx, h0]
        have hadd : Synthesis I (inputs N ∪ ({prefFn k hk'} ∪ {termFn idx}))
            {fun w => prefFn k hk' w + termFn idx w} 1 :=
          Synthesis.gate (σ := bssAdditiveSignature) .add ![prefFn k hk', termFn idx]
            (fun j => by
              fin_cases j
              · exact Set.mem_union_right _ (Set.mem_union_left _ rfl)
              · exact Set.mem_union_right _ (Set.mem_union_right _ rfl))
        have hsum_eq : (fun w => prefFn k hk' w + termFn idx w) = prefFn (k + 1) hk := by
          funext w
          simp only [prefFn, add_assoc]
          congr 1
          have hidx_lt : idx.val < k + 1 := Nat.lt_succ_self k
          have hidx_nlt : ¬idx.val < k := Nat.lt_irrefl k
          conv_rhs => rw [← Finset.add_sum_erase _ _ (Finset.mem_univ idx), ite_eq_left hidx_lt]
          conv_lhs =>
            rw [← Finset.add_sum_erase _ _ (Finset.mem_univ idx), ite_eq_right hidx_nlt, zero_add,
              add_comm]
          congr 1
          refine Finset.sum_congr rfl fun i hi => ?_
          have hne : i.val ≠ k := fun h => (Finset.mem_erase.mp hi).1 (Fin.ext h)
          by_cases hlt : i.val < k
          · rw [ite_eq_left hlt, ite_eq_left (Nat.lt_succ_of_lt hlt)]
          · rw [ite_eq_right hlt, ite_eq_right (by omega)]
        exact ((hprev.comp hterm).trans hadd).mono Set.Subset.rfl
          (by rw [hsum_eq]) (by omega)
    obtain ⟨C, hC, hsz⟩ := (hstep n le_rfl).exists_circuit
    refine ⟨C, hsz.trans (by omega), fun x y => ?_⟩
    have hev := congrFun (hC (Fin.append (Fin.append x (fun _ : Fin 1 => (0 : K))) y)) 0
    rw [single_apply] at hev
    dsimp only [prefFn] at hev
    rw [hev]
    have hz : (Fin.append (Fin.append x (fun _ : Fin 1 => (0 : K))) y) zeroWire = 0 := by
      simp [zeroWire, Fin.append_left, Fin.append_right]
    rw [hz, zero_add]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ite_eq_left i.isLt]
    simp only [termFn, hz, zero_sub, Fin.append_left, Fin.append_right]
  choose C hC_sz hC_ev using hcirc
  refine mem_BSSAdditiveNP.mpr ⟨fun _ => 1, id, fun _ _ => 0, C,
    by fun_prop, by fun_prop,
    (show PolynomiallyBounded fun n => 2 * n + 2 by fun_prop).mono_of_le hC_sz,
    fun n x => ?_⟩
  rw [mem_subsetSumLang]
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨fun i => if s i then (1 : K) else 0, ?_⟩
    rw [hC_ev n x]
    convert hs using 1
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h0 : i.val = 0
    · simp [h0]
    · cases s i <;> simp [h0]
  · rintro ⟨y, hy⟩
    rw [hC_ev n x] at hy
    refine ⟨fun i => decide (y i ≠ 0), ?_⟩
    convert hy using 1
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h0 : i.val = 0
    · simp [h0]
    · by_cases hy0 : y i = 0 <;> simp [h0, hy0]

/-- Dot product of an integer vector with a vector over a field `K`. -/
def dotK {K : Type*} [Field K] {d : ℕ} (a : Fin d → ℤ) (x : Fin d → K) : K :=
  ∑ i : Fin d, (a i : K) * x i

/-- Evaluate an integer linear form `(u, v)` on `(z, y)`. -/
def evalLinForm {K : Type*} [Field K] {D M : ℕ} (z : Fin D → K) (y : Fin M → K)
    (lf : (Fin D → ℤ) × (Fin M → ℤ)) : K :=
  dotK lf.1 z + dotK lf.2 y

/-- Evaluation formula for `dotK`. -/
theorem dotK_eq {K : Type*} [Field K] {d : ℕ} (a : Fin d → ℤ) (x : Fin d → K) :
    dotK a x = ∑ i : Fin d, (a i : K) * x i := by
  unfold dotK; rfl

/-- Evaluation formula for `evalLinForm`. -/
theorem evalLinForm_eq {K : Type*} [Field K] {D M : ℕ} (z : Fin D → K) (y : Fin M → K)
    (lf : (Fin D → ℤ) × (Fin M → ℤ)) :
    evalLinForm z y lf = dotK lf.1 z + dotK lf.2 y := by
  unfold evalLinForm; rfl

/-- Zero-vector dot product vanishes. -/
theorem dotK_zero {K : Type*} [Field K] {d : ℕ} (x : Fin d → K) :
    dotK (fun _ => 0) x = 0 := by
  simp [dotK]

/-- Additivity of `dotK` in its integer vector argument. -/
theorem dotK_add {K : Type*} [Field K] {d : ℕ} (a b : Fin d → ℤ) (x : Fin d → K) :
    dotK (fun i => a i + b i) x = dotK a x + dotK b x := by
  simp only [dotK, Int.cast_add, add_mul, Finset.sum_add_distrib]

/-- Linearity of `dotK` under subtraction in its integer vector argument. -/
theorem dotK_sub {K : Type*} [Field K] {d : ℕ} (a b : Fin d → ℤ) (x : Fin d → K) :
    dotK (fun i => a i - b i) x = dotK a x - dotK b x := by
  simp only [dotK, Int.cast_sub, sub_mul, Finset.sum_sub_distrib]

/-- Standard basis linear form of an input wire `i : Fin (D + M)`. -/
@[expose] def inputLinForm (D M : ℕ) (i : Fin (D + M)) : (Fin D → ℤ) × (Fin M → ℤ) :=
  Fin.addCases
    (fun a => (fun d => if d = a then 1 else 0, fun _ => 0))
    (fun j => (fun _ => 0, fun r => if r = j then 1 else 0)) i

/-- `inputLinForm` on a `z`-input coordinate. -/
@[simp] theorem inputLinForm_castAdd (D M : ℕ) (a : Fin D) :
    inputLinForm D M (Fin.castAdd M a) = (fun d => if d = a then 1 else 0, fun _ => 0) := by
  simp [inputLinForm]

/-- `inputLinForm` on a `y`-witness coordinate. -/
@[simp] theorem inputLinForm_natAdd (D M : ℕ) (j : Fin M) :
    inputLinForm D M (Fin.natAdd D j) = (fun _ => 0, fun r => if r = j then 1 else 0) := by
  simp [inputLinForm]

/-- Combine argument linear forms at a single additive BSS gate under branch bit `bk`. -/
@[expose] def lineLinForm {D M g : ℕ} (wf : Wire (D + M) g → (Fin D → ℤ) × (Fin M → ℤ))
    (bk : Bool) (line : Line bssAdditiveSignature (D + M) g) : (Fin D → ℤ) × (Fin M → ℤ) :=
  match line.op, line.wires with
  | .add, ws => (fun d => (wf (ws 0)).1 d + (wf (ws 1)).1 d,
      fun r => (wf (ws 0)).2 r + (wf (ws 1)).2 r)
  | .sub, ws => (fun d => (wf (ws 0)).1 d - (wf (ws 1)).1 d,
      fun r => (wf (ws 0)).2 r - (wf (ws 1)).2 r)
  | .zeroBranch, ws => if bk then wf (ws 1) else wf (ws 2)

/-- `lineLinForm` on an `.add` gate. -/
@[simp] theorem lineLinForm_add {D M g : ℕ}
    (wf : Wire (D + M) g → (Fin D → ℤ) × (Fin M → ℤ)) (bk : Bool)
    (ws : Fin 2 → Wire (D + M) g) :
    lineLinForm wf bk ⟨.add, ws⟩ =
      (fun d => (wf (ws 0)).1 d + (wf (ws 1)).1 d,
       fun r => (wf (ws 0)).2 r + (wf (ws 1)).2 r) := rfl

/-- `lineLinForm` on a `.sub` gate. -/
@[simp] theorem lineLinForm_sub {D M g : ℕ}
    (wf : Wire (D + M) g → (Fin D → ℤ) × (Fin M → ℤ)) (bk : Bool)
    (ws : Fin 2 → Wire (D + M) g) :
    lineLinForm wf bk ⟨.sub, ws⟩ =
      (fun d => (wf (ws 0)).1 d - (wf (ws 1)).1 d,
       fun r => (wf (ws 0)).2 r - (wf (ws 1)).2 r) := rfl

/-- `lineLinForm` on a `.zeroBranch` gate. -/
@[simp] theorem lineLinForm_zeroBranch {D M g : ℕ}
    (wf : Wire (D + M) g → (Fin D → ℤ) × (Fin M → ℤ)) (bk : Bool)
    (ws : Fin 3 → Wire (D + M) g) :
    lineLinForm wf bk ⟨.zeroBranch, ws⟩ = if bk then wf (ws 1) else wf (ws 2) := rfl

/-- Linear forms of all gates of an additive BSS program under branch vector `b : Fin g → Bool`. -/
@[expose] def progLinForms {D M : ℕ} : {g : ℕ} → Program bssAdditiveSignature (D + M) g →
    (Fin g → Bool) → Fin g → (Fin D → ℤ) × (Fin M → ℤ)
  | 0, .empty, _ => Fin.elim0
  | _ + 1, .gate q line, b =>
    let bPrev : Fin _ → Bool := fun k => b k.castSucc
    let wf := Wire.elim (inputLinForm D M) (progLinForms q bPrev)
    Fin.snoc (progLinForms q bPrev) (lineLinForm wf (b (Fin.last _)) line)

/-- `progLinForms` on `.gate`. -/
theorem progLinForms_gate {D M g : ℕ} (q : Program bssAdditiveSignature (D + M) g)
    (line : Line bssAdditiveSignature (D + M) g) (b : Fin (g + 1) → Bool) :
    progLinForms (.gate q line) b =
      Fin.snoc (progLinForms q (fun k => b k.castSucc))
        (lineLinForm (Wire.elim (inputLinForm D M) (progLinForms q (fun k => b k.castSucc)))
          (b (Fin.last g)) line) := rfl

/-- Linear form of any wire `w` of an additive BSS program under branch vector `b`. -/
@[expose] def wireLinForm {D M g : ℕ} (p : Program bssAdditiveSignature (D + M) g)
    (b : Fin g → Bool) : Wire (D + M) g → (Fin D → ℤ) × (Fin M → ℤ) :=
  Wire.elim (inputLinForm D M) (progLinForms p b)

/-- `wireLinForm` on an input wire. -/
@[simp] theorem wireLinForm_input {D M g : ℕ} (p : Program bssAdditiveSignature (D + M) g)
    (b : Fin g → Bool) (i : Fin (D + M)) :
    wireLinForm p b (.input i) = inputLinForm D M i := rfl

/-- `wireLinForm` on a gate wire. -/
@[simp] theorem wireLinForm_gate {D M g : ℕ} (p : Program bssAdditiveSignature (D + M) g)
    (b : Fin g → Bool) (k : Fin g) :
    wireLinForm p b (.gate k) = progLinForms p b k := rfl

/-- Branch consistency of `b : Fin g → Bool` with `(z, y)`: every `zeroBranch` gate's test wire
vanishes on `(z, y)` iff its corresponding bit in `b` is `true`. -/
@[expose] def BranchConsistent {K : Type*} [Field K] {D M : ℕ} :
    {g : ℕ} → Program bssAdditiveSignature (D + M) g → (Fin g → Bool) →
    (Fin D → K) → (Fin M → K) → Prop
  | 0, .empty, _, _, _ => True
  | _ + 1, .gate q line, b, z, y =>
    let bPrev : Fin _ → Bool := fun k => b k.castSucc
    BranchConsistent q bPrev z y ∧
      match line.op, line.wires with
      | .zeroBranch, ws =>
        (evalLinForm z y (wireLinForm q bPrev (ws 0)) = 0) ↔ b (Fin.last _) = true
      | _, _ => True

/-- Unfolding of `BranchConsistent` on `.gate`. -/
theorem branchConsistent_gate {K : Type*} [Field K] {D M g : ℕ}
    (q : Program bssAdditiveSignature (D + M) g) (line : Line bssAdditiveSignature (D + M) g)
    (b : Fin (g + 1) → Bool) (z : Fin D → K) (y : Fin M → K) :
    BranchConsistent (.gate q line) b z y ↔
      (BranchConsistent q (fun k => b k.castSucc) z y ∧
        match line.op, line.wires with
        | .zeroBranch, ws =>
          (evalLinForm z y (wireLinForm q (fun k => b k.castSucc) (ws 0)) = 0) ↔
            b (Fin.last g) = true
        | _, _ => True) := Iff.rfl

private theorem evalLinForm_inputLinForm {K : Type*} [Field K] {D M : ℕ}
    (z : Fin D → K) (y : Fin M → K) (i : Fin (D + M)) :
    evalLinForm z y (inputLinForm D M i) = Fin.append z y i := by
  induction i using Fin.addCases with
  | left a =>
    simp [evalLinForm, inputLinForm, dotK, Fin.append_left]
  | right j =>
    simp [evalLinForm, inputLinForm, dotK, Fin.append_right]

/-- Every coefficient in `wireLinForm p b w` has magnitude at most `2 ^ g`. -/
theorem wireLinForm_bound {D M : ℕ} :
    ∀ {g : ℕ} (p : Program bssAdditiveSignature (D + M) g) (b : Fin g → Bool)
      (w : Wire (D + M) g),
      (∀ d : Fin D, ((wireLinForm p b w).1 d).natAbs ≤ 2 ^ g) ∧
      (∀ r : Fin M, ((wireLinForm p b w).2 r).natAbs ≤ 2 ^ g)
  | 0, .empty, _, w => by
    cases w with
    | input i =>
      induction i using Fin.addCases with
      | left a =>
        refine ⟨fun d => ?_, fun r => ?_⟩
        · simp only [wireLinForm, Wire.elim, inputLinForm, Fin.addCases_left, pow_zero]
          split_ifs <;> simp
        · simp [wireLinForm, Wire.elim, inputLinForm]
      | right j =>
        refine ⟨fun d => ?_, fun r => ?_⟩
        · simp [wireLinForm, Wire.elim, inputLinForm]
        · simp only [wireLinForm, Wire.elim, inputLinForm, Fin.addCases_right, pow_zero]
          split_ifs <;> simp
    | gate k => exact Fin.elim0 k
  | g + 1, .gate q line, b, w => by
    let bPrev : Fin g → Bool := fun k => b k.castSucc
    have ih := wireLinForm_bound q bPrev
    cases w with
    | input i =>
      have h0 := wireLinForm_bound (D := D) (M := M) Program.empty Fin.elim0 (.input i)
      refine ⟨fun d => (h0.1 d).trans (by simp [Nat.one_le_two_pow]),
        fun r => (h0.2 r).trans (by simp [Nat.one_le_two_pow])⟩
    | gate k =>
      cases k using Fin.lastCases with
      | last =>
        simp only [wireLinForm, Wire.elim, progLinForms, Fin.snoc_last]
        rcases line with ⟨op, ws⟩
        cases op with
        | add =>
          have h0 := ih (ws 0)
          have h1 := ih (ws 1)
          refine ⟨fun d => ?_, fun r => ?_⟩
          · change ((wireLinForm q bPrev (ws 0)).1 d + (wireLinForm q bPrev (ws 1)).1 d).natAbs ≤ _
            exact (Int.natAbs_add_le _ _).trans
              (by rw [pow_succ']; have := h0.1 d; have := h1.1 d; omega)
          · change ((wireLinForm q bPrev (ws 0)).2 r + (wireLinForm q bPrev (ws 1)).2 r).natAbs ≤ _
            exact (Int.natAbs_add_le _ _).trans
              (by rw [pow_succ']; have := h0.2 r; have := h1.2 r; omega)
        | sub =>
          have h0 := ih (ws 0)
          have h1 := ih (ws 1)
          refine ⟨fun d => ?_, fun r => ?_⟩
          · change ((wireLinForm q bPrev (ws 0)).1 d - (wireLinForm q bPrev (ws 1)).1 d).natAbs ≤ _
            exact (Int.natAbs_sub_le _ _).trans
              (by rw [pow_succ']; have := h0.1 d; have := h1.1 d; omega)
          · change ((wireLinForm q bPrev (ws 0)).2 r - (wireLinForm q bPrev (ws 1)).2 r).natAbs ≤ _
            exact (Int.natAbs_sub_le _ _).trans
              (by rw [pow_succ']; have := h0.2 r; have := h1.2 r; omega)
        | zeroBranch =>
          dsimp only [lineLinForm]
          split_ifs
          · have h1 := ih (ws 1)
            exact ⟨fun d => (h1.1 d).trans (Nat.pow_le_pow_right (by omega) (Nat.le_succ _)),
              fun r => (h1.2 r).trans (Nat.pow_le_pow_right (by omega) (Nat.le_succ _))⟩
          · have h2 := ih (ws 2)
            exact ⟨fun d => (h2.1 d).trans (Nat.pow_le_pow_right (by omega) (Nat.le_succ _)),
              fun r => (h2.2 r).trans (Nat.pow_le_pow_right (by omega) (Nat.le_succ _))⟩
      | cast j =>
        simp only [wireLinForm, Wire.elim, progLinForms, Fin.snoc_castSucc]
        have hj := ih (.gate j)
        exact ⟨fun d => (hj.1 d).trans (Nat.pow_le_pow_right (by omega) (Nat.le_succ _)),
          fun r => (hj.2 r).trans (Nat.pow_le_pow_right (by omega) (Nat.le_succ _))⟩

/-- Under a branch-consistent vector `b`, every wire of an additive BSS program evaluates to its
branch-conditioned linear form. -/
theorem trace_eq_evalLinForm_of_branchConsistent {K : Type*} [Field K] {D M : ℕ} :
    ∀ {g : ℕ} (p : Program bssAdditiveSignature (D + M) g) (b : Fin g → Bool)
      (z : Fin D → K) (y : Fin M → K),
      BranchConsistent p b z y →
      ∀ w : Wire (D + M) g,
        p.trace (bssAdditiveInterp K) (Fin.append z y) w = evalLinForm z y (wireLinForm p b w)
  | 0, .empty, _, z, y, _, w => by
    cases w with
    | input i =>
      rw [Program.trace_input]
      exact (evalLinForm_inputLinForm z y i).symm
    | gate k => exact Fin.elim0 k
  | g + 1, .gate q line, b, z, y, hcons, w => by
    let bPrev : Fin g → Bool := fun k => b k.castSucc
    have ih := trace_eq_evalLinForm_of_branchConsistent q bPrev z y hcons.1
    cases w with
    | input i =>
      rw [Program.trace_input]
      exact (evalLinForm_inputLinForm z y i).symm
    | gate k =>
      cases k using Fin.lastCases with
      | last =>
        change (q.gate line).eval (bssAdditiveInterp K) (Fin.append z y) (Fin.last g) = _
        rw [Program.eval_gate_last]
        simp only [wireLinForm, Wire.elim, progLinForms, Fin.snoc_last]
        have hline_ev : line.eval (bssAdditiveInterp K) (Fin.append z y)
            (q.eval (bssAdditiveInterp K) (Fin.append z y)) =
            bssAdditiveInterp K line.op
              (fun j => evalLinForm z y (wireLinForm q bPrev (line.wires j))) := by
          rw [Line.eval]
          congr 1; funext j
          have htr := ih (line.wires j)
          simpa [Program.trace] using htr
        rw [hline_ev]
        change bssAdditiveInterp K line.op
            (fun j => evalLinForm z y (wireLinForm q bPrev (line.wires j))) =
          evalLinForm z y (lineLinForm (wireLinForm q bPrev) (b (Fin.last g)) line)
        have hcond := hcons.2
        rcases line with ⟨op, ws⟩
        cases op with
        | add =>
          simp only [bssAdditiveInterp, lineLinForm, evalLinForm, dotK_add]
          ring
        | sub =>
          simp only [bssAdditiveInterp, lineLinForm, evalLinForm, dotK_sub]
          ring
        | zeroBranch =>
          dsimp only [bssAdditiveInterp, lineLinForm]
          dsimp only at hcond
          classical
          by_cases h0 : evalLinForm z y (wireLinForm q bPrev (ws 0)) = 0
          · have hb : b (Fin.last g) = true := hcond.mp h0
            simp [h0, hb]
          · have hb : b (Fin.last g) = false := by
              cases hbv : b (Fin.last g)
              · rfl
              · exact absurd (hcond.mpr hbv) h0
            simp [h0, hb]
      | cast j =>
        change (q.gate line).eval (bssAdditiveInterp K) (Fin.append z y) j.castSucc = _
        rw [Program.eval_gate_castSucc]
        simp only [wireLinForm, Wire.elim, progLinForms, Fin.snoc_castSucc]
        exact ih (.gate j)

/-- Every input `(z, y)` induces a branch-consistent vector `b : Fin g → Bool`. -/
theorem exists_branchConsistent {K : Type*} [Field K] {D M : ℕ} :
    ∀ {g : ℕ} (p : Program bssAdditiveSignature (D + M) g) (z : Fin D → K) (y : Fin M → K),
      ∃ b : Fin g → Bool, BranchConsistent p b z y
  | 0, .empty, _, _ => ⟨Fin.elim0, trivial⟩
  | g + 1, .gate q line, z, y => by
    classical
    obtain ⟨bPrev, hbPrev⟩ := exists_branchConsistent q z y
    let bitLast : Bool :=
      match line.op, line.wires with
      | .zeroBranch, ws => decide (evalLinForm z y (wireLinForm q bPrev (ws 0)) = 0)
      | _, _ => false
    refine ⟨Fin.snoc (α := fun _ => Bool) bPrev bitLast, ?_⟩
    have hprev_eq :
        (fun k : Fin g => Fin.snoc (α := fun _ => Bool) bPrev bitLast k.castSucc) = bPrev :=
      funext fun k => by simp [Fin.snoc_castSucc]
    refine ⟨?_, ?_⟩
    · change BranchConsistent q
        (fun k : Fin g => Fin.snoc (α := fun _ => Bool) bPrev bitLast k.castSucc) z y
      rw [hprev_eq]; exact hbPrev
    rcases line with ⟨op, ws⟩
    cases op with
    | add => trivial
    | sub => trivial
    | zeroBranch =>
      dsimp only [bitLast]
      rw [hprev_eq, Fin.snoc_last, decide_eq_true_iff]

/-- Path-decomposition characterization of acceptance for an additive BSS circuit. -/
theorem circuit_accepts_iff_exists_branch {K : Type*} [Field K] {D M : ℕ}
    (C : Circuit bssAdditiveSignature (D + M) 1) (z : Fin D → K) (y : Fin M → K) :
    C.eval (bssAdditiveInterp K) (Fin.append z y) 0 = 0 ↔
      ∃ b : Fin C.size → Bool,
        BranchConsistent C.program b z y ∧
        evalLinForm z y (wireLinForm C.program b (C.outputs 0)) = 0 := by
  constructor
  · intro hacc
    obtain ⟨b, hb⟩ := exists_branchConsistent C.program z y
    refine ⟨b, hb, ?_⟩
    rw [← trace_eq_evalLinForm_of_branchConsistent C.program b z y hb (C.outputs 0)]
    exact hacc
  · rintro ⟨b, hb, hout⟩
    change C.program.trace (bssAdditiveInterp K) (Fin.append z y) (C.outputs 0) = 0
    rw [trace_eq_evalLinForm_of_branchConsistent C.program b z y hb (C.outputs 0)]
    exact hout

/-- Border a `ρ × ρ` matrix `P` by a right column `col`, bottom row `row`, and bottom-right
entry `corner`. -/
def borderMat {ρ : ℕ} {R : Type*} (P : Matrix (Fin ρ) (Fin ρ) R)
    (col : Fin ρ → R) (row : Fin ρ → R) (corner : R) :
    Matrix (Fin (ρ + 1)) (Fin (ρ + 1)) R :=
  Matrix.of fun i j =>
    Fin.lastCases (Fin.lastCases corner row j)
      (fun a => Fin.lastCases (col a) (fun b => P a b) j) i

/-- Top-left block entry of `borderMat`. -/
theorem borderMat_cast_cast {ρ : ℕ} {R : Type*} (P : Matrix (Fin ρ) (Fin ρ) R)
    (col row : Fin ρ → R) (corner : R) (a b : Fin ρ) :
    borderMat P col row corner a.castSucc b.castSucc = P a b := by
  simp [borderMat]

/-- Right border column entry of `borderMat`. -/
theorem borderMat_cast_last {ρ : ℕ} {R : Type*} (P : Matrix (Fin ρ) (Fin ρ) R)
    (col row : Fin ρ → R) (corner : R) (a : Fin ρ) :
    borderMat P col row corner a.castSucc (Fin.last ρ) = col a := by
  simp [borderMat]

/-- Bottom border row entry of `borderMat`. -/
theorem borderMat_last_cast {ρ : ℕ} {R : Type*} (P : Matrix (Fin ρ) (Fin ρ) R)
    (col row : Fin ρ → R) (corner : R) (b : Fin ρ) :
    borderMat P col row corner (Fin.last ρ) b.castSucc = row b := by
  simp [borderMat]

/-- Bottom-right corner entry of `borderMat`. -/
theorem borderMat_last_last {ρ : ℕ} {R : Type*} (P : Matrix (Fin ρ) (Fin ρ) R)
    (col row : Fin ρ → R) (corner : R) :
    borderMat P col row corner (Fin.last ρ) (Fin.last ρ) = corner := by
  simp [borderMat]

/-- Leibniz bound on the determinant of an integer matrix with bounded entries. -/
theorem det_natAbs_le_factorial_mul_pow {k B : ℕ} (A : Matrix (Fin k) (Fin k) ℤ)
    (hB : ∀ i j, (A i j).natAbs ≤ B) :
    A.det.natAbs ≤ k.factorial * B ^ k := by
  rw [Matrix.det_apply]
  have hsum_le : (∑ σ : Equiv.Perm (Fin k),
      (Equiv.Perm.sign σ : ℤ) • ∏ i : Fin k, A (σ i) i).natAbs ≤
      ∑ σ : Equiv.Perm (Fin k),
        ((Equiv.Perm.sign σ : ℤ) • ∏ i : Fin k, A (σ i) i).natAbs := by
    have h1 := Finset.abs_sum_le_sum_abs (s := Finset.univ)
      (f := fun σ : Equiv.Perm (Fin k) => (Equiv.Perm.sign σ : ℤ) • ∏ i : Fin k, A (σ i) i)
    have h2 : ∀ σ ∈ (Finset.univ : Finset (Equiv.Perm (Fin k))),
        |(Equiv.Perm.sign σ : ℤ) • ∏ i : Fin k, A (σ i) i| =
          (((Equiv.Perm.sign σ : ℤ) • ∏ i : Fin k, A (σ i) i).natAbs : ℤ) :=
      fun _ _ => (Int.natCast_natAbs _).symm
    rw [Finset.sum_congr rfl h2, ← Nat.cast_sum] at h1
    exact_mod_cast (Int.natCast_natAbs _ ▸ h1)
  refine hsum_le.trans ?_
  calc ∑ σ : Equiv.Perm (Fin k), ((Equiv.Perm.sign σ : ℤ) • ∏ i : Fin k, A (σ i) i).natAbs
      ≤ ∑ _σ : Equiv.Perm (Fin k), B ^ k := Finset.sum_le_sum fun σ _ => by
        rw [smul_eq_mul, Int.natAbs_mul, Int.natAbs_prod]
        have hsign : (Equiv.Perm.sign σ : ℤ).natAbs = 1 := by
          rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
        rw [hsign, one_mul]
        calc ∏ i : Fin k, (A (σ i) i).natAbs
            ≤ ∏ _i : Fin k, B := Finset.prod_le_prod fun i _ => hB (σ i) i
          _ = B ^ k := by simp
    _ = k.factorial * B ^ k := by simp [Fintype.card_perm]

/-- Cramer expansion of a bordered determinant via block-triangular elimination (`P.det ≠ 0`). -/
theorem borderMat_det_eq {ρ : ℕ} {R : Type*} [CommRing R] [IsDomain R]
    (P : Matrix (Fin ρ) (Fin ρ) R) (col row : Fin ρ → R) (corner : R) (hP : P.det ≠ 0) :
    (borderMat P col row corner).det =
      P.det * corner - ∑ a : Fin ρ, (P.updateRow a row).det * col a := by
  let c : Fin ρ → R := fun a => (P.updateRow a row).det
  have hc_eq : ∀ a : Fin ρ, c a = (row ᵥ* P.adjugate) a := fun a => by
    have htr : (P.updateRow a row)ᵀ = Pᵀ.updateCol a row := by
      ext i j
      by_cases hj : j = a <;> simp [Matrix.updateRow, Matrix.updateCol, Function.update, hj]
    have h1 : c a = (Pᵀ.updateCol a row).det := by
      dsimp only [c]
      rw [← Matrix.det_transpose, htr]
    rw [h1, ← Matrix.cramer_apply, Matrix.cramer_eq_adjugate_mulVec]
    simp only [Matrix.mulVec, Matrix.vecMul, dotProduct]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← Matrix.adjugate_transpose P, Matrix.transpose_apply, mul_comm]
  let L : Matrix (Fin (ρ + 1)) (Fin (ρ + 1)) R :=
    borderMat (1 : Matrix (Fin ρ) (Fin ρ) R) 0 (fun b => -c b) P.det
  let B : Matrix (Fin (ρ + 1)) (Fin (ρ + 1)) R := borderMat P col row corner
  have hL_det : L.det = P.det := by
    rw [Matrix.det_succ_column L (Fin.last ρ)]
    rw [Finset.sum_eq_single (Fin.last ρ)]
    · have hsub : L.submatrix (Fin.last ρ).succAbove (Fin.last ρ).succAbove = 1 := by
        ext a b
        simp [L, borderMat_cast_cast]
      rw [hsub, Matrix.det_one, mul_one, show L (Fin.last ρ) (Fin.last ρ) = P.det from
        borderMat_last_last ..]
      have hpow : (-1 : R) ^ ((Fin.last ρ).val + (Fin.last ρ).val) = 1 := by
        rw [← two_mul, pow_mul]; norm_num
      rw [hpow, one_mul]
    · intro i _ hne
      cases i using Fin.lastCases with
      | last => exact absurd rfl hne
      | cast a =>
        rw [show L a.castSucc (Fin.last ρ) = 0 from borderMat_cast_last ..]
        simp
    · intro h; exact absurd (Finset.mem_univ _) h
  have hLB : L * B =
      borderMat P col 0 (P.det * corner - ∑ a : Fin ρ, c a * col a) := by
    ext i j
    rw [Matrix.mul_apply, Fin.sum_univ_castSucc]
    cases i using Fin.lastCases with
    | last =>
      cases j using Fin.lastCases with
      | last =>
        simp only [L, B, borderMat_last_cast, borderMat_cast_last, borderMat_last_last]
        ring_nf
        simp [sub_eq_add_neg, add_comm]
      | cast b =>
        simp only [L, B, borderMat_last_cast, borderMat_cast_cast, borderMat_last_last,
          Pi.zero_apply]
        have hsum : ∑ a : Fin ρ, c a * P a b = P.det * row b := by
          have hmul : (row ᵥ* P.adjugate) ᵥ* P = P.det • row := by
            rw [Matrix.vecMul_vecMul, Matrix.adjugate_mul, Matrix.vecMul_smul, Matrix.vecMul_one]
          have hcomp := congrFun hmul b
          simpa [Matrix.vecMul, dotProduct, hc_eq] using hcomp
        calc ∑ a : Fin ρ, -c a * P a b + P.det * row b
            = -(∑ a : Fin ρ, c a * P a b) + P.det * row b := by simp [neg_mul]
          _ = 0 := by rw [hsum, neg_add_cancel]
    | cast a =>
      cases j using Fin.lastCases with
      | last =>
        simp only [L, B, borderMat_cast_cast, borderMat_cast_last, borderMat_last_last,
          Pi.zero_apply, zero_mul, add_zero, Matrix.one_apply]
        simp
      | cast b =>
        simp only [L, B, borderMat_cast_cast, borderMat_cast_last, borderMat_last_cast,
          Pi.zero_apply, zero_mul, add_zero, Matrix.one_apply]
        simp
  have hLB_det : (L * B).det = P.det * (P.det * corner - ∑ a : Fin ρ, c a * col a) := by
    rw [hLB, Matrix.det_succ_row _ (Fin.last ρ)]
    rw [Finset.sum_eq_single (Fin.last ρ)]
    · have hsub : (borderMat P col 0 (P.det * corner - ∑ a : Fin ρ, c a * col a)).submatrix
          (Fin.last ρ).succAbove (Fin.last ρ).succAbove = P := by
        ext a b; simp [borderMat_cast_cast]
      rw [hsub, borderMat_last_last]
      have hpow : (-1 : R) ^ ((Fin.last ρ).val + (Fin.last ρ).val) = 1 := by
        rw [← two_mul, pow_mul]; norm_num
      rw [hpow, one_mul, mul_comm]
    · intro j _ hne
      cases j using Fin.lastCases with
      | last => exact absurd rfl hne
      | cast b => rw [borderMat_last_cast]; simp
    · intro h; exact absurd (Finset.mem_univ _) h
  have hmul_det : P.det * B.det = P.det * (P.det * corner - ∑ a : Fin ρ, c a * col a) := by
    calc P.det * B.det = L.det * B.det := by rw [hL_det]
      _ = (L * B).det := (Matrix.det_mul L B).symm
      _ = P.det * (P.det * corner - ∑ a : Fin ρ, c a * col a) := hLB_det
  exact mul_left_cancel₀ hP hmul_det

/-- Bordering a matrix `P` by a copy of one of its own columns yields determinant `0`. -/
theorem borderMat_det_eq_zero_of_col_eq {ρ : ℕ} {R : Type*} [CommRing R]
    (P : Matrix (Fin ρ) (Fin ρ) R) (col row : Fin ρ → R) (corner : R)
    {b₀ : Fin ρ} (hcol : col = fun a => P a b₀) (hcor : corner = row b₀) :
    (borderMat P col row corner).det = 0 := by
  apply Matrix.det_zero_of_column_eq (i := b₀.castSucc) (j := Fin.last ρ) (Fin.castSucc_ne_last b₀)
  intro i
  cases i using Fin.lastCases with
  | last => rw [borderMat_last_cast, borderMat_last_last, hcor]
  | cast a => rw [borderMat_cast_cast, borderMat_cast_last, hcol]

/-- **Algebraic witness elimination over any field `K` of characteristic zero**: existence of a
continuous witness `y : Fin M → K` satisfying a finite system of integer-linear equations and
disequations is equivalent to the existence of a maximal-rank integer pivot minor `(I, J)`
satisfying bordered-determinant rank, consistency, and disequation-compatibility conditions. -/
theorem exists_linear_solution_iff {K : Type*} [Field K] [CharZero K] {E N D M : ℕ}
    (u : Fin E → Fin D → ℤ) (v : Fin E → Fin M → ℤ)
    (q : Fin N → Fin D → ℤ) (w : Fin N → Fin M → ℤ)
    (isNeq : Fin N → Bool) (z : Fin D → K) :
    (∃ y : Fin M → K,
      (∀ i : Fin E, dotK (u i) z + dotK (v i) y = 0) ∧
      (∀ r : Fin N, isNeq r = true → dotK (q r) z + dotK (w r) y ≠ 0)) ↔
    ∃ (ρ : ℕ) (_ : ρ ≤ M) (I : Fin ρ → Fin E) (J : Fin ρ → Fin M),
      let P : Matrix (Fin ρ) (Fin ρ) ℤ := Matrix.of fun a b => v (I a) (J b)
      P.det ≠ 0 ∧
      (∀ (i : Fin E) (j : Fin M),
        (borderMat P (fun a => v (I a) j) (fun b => v i (J b)) (v i j)).det = 0) ∧
      (∀ i : Fin E,
        dotK (fun d =>
          (borderMat P (fun a => u (I a) d) (fun b => v i (J b)) (u i d)).det) z = 0) ∧
      (∀ r : Fin N, isNeq r = true →
        (∃ j : Fin M,
          (borderMat P (fun a => v (I a) j) (fun b => w r (J b)) (w r j)).det ≠ 0) ∨
        dotK (fun d =>
          (borderMat P (fun a => u (I a) d) (fun b => w r (J b)) (q r d)).det) z ≠ 0) := by
  classical
  have hcomb : ∀ {ρ : ℕ} (I : Fin ρ → Fin E) (J : Fin ρ → Fin M)
      (u0 : Fin D → ℤ) (v0 : Fin M → ℤ) (y : Fin M → K),
      let P : Matrix (Fin ρ) (Fin ρ) ℤ := Matrix.of fun a b => v (I a) (J b)
      P.det ≠ 0 →
      (P.det : K) * (dotK u0 z + dotK v0 y) -
          ∑ a : Fin ρ, ((P.updateRow a (fun b => v0 (J b))).det : K) *
            (dotK (u (I a)) z + dotK (v (I a)) y) =
        dotK (fun d => (borderMat P (fun a => u (I a) d) (fun b => v0 (J b)) (u0 d)).det) z +
        dotK (fun j => (borderMat P (fun a => v (I a) j) (fun b => v0 (J b)) (v0 j)).det) y := by
    intro ρ I J u0 v0 y P hP
    let cof (a : Fin ρ) : ℤ := (P.updateRow a (fun b => v0 (J b))).det
    have hdotU : dotK (fun d =>
        (borderMat P (fun a => u (I a) d) (fun b => v0 (J b)) (u0 d)).det) z =
        (P.det : K) * dotK u0 z - ∑ a : Fin ρ, (cof a : K) * dotK (u (I a)) z := by
      simp only [dotK]
      have heq : ∀ d : Fin D,
          ((borderMat P (fun a => u (I a) d) (fun b => v0 (J b)) (u0 d)).det : K) * z d =
          (P.det : K) * ((u0 d : K) * z d) -
            ∑ a : Fin ρ, (cof a : K) * ((u (I a) d : K) * z d) := fun d => by
        rw [borderMat_det_eq P _ _ _ hP]
        simp only [Int.cast_sub, Int.cast_mul, Int.cast_sum]
        rw [sub_mul, Finset.sum_mul, mul_assoc]
        congr 1
        refine Finset.sum_congr rfl fun a _ => by dsimp only [cof]; ring
      rw [Finset.sum_congr rfl fun d _ => heq d, Finset.sum_sub_distrib, ← Finset.mul_sum,
        Finset.sum_comm]
      congr 1
      refine Finset.sum_congr rfl fun a _ => (Finset.mul_sum _ _ _).symm
    have hdotV : dotK (fun j =>
        (borderMat P (fun a => v (I a) j) (fun b => v0 (J b)) (v0 j)).det) y =
        (P.det : K) * dotK v0 y - ∑ a : Fin ρ, (cof a : K) * dotK (v (I a)) y := by
      simp only [dotK]
      have heq : ∀ j : Fin M,
          ((borderMat P (fun a => v (I a) j) (fun b => v0 (J b)) (v0 j)).det : K) * y j =
          (P.det : K) * ((v0 j : K) * y j) -
            ∑ a : Fin ρ, (cof a : K) * ((v (I a) j : K) * y j) := fun j => by
        rw [borderMat_det_eq P _ _ _ hP]
        simp only [Int.cast_sub, Int.cast_mul, Int.cast_sum]
        rw [sub_mul, Finset.sum_mul, mul_assoc]
        congr 1
        refine Finset.sum_congr rfl fun a _ => by dsimp only [cof]; ring
      rw [Finset.sum_congr rfl fun j _ => heq j, Finset.sum_sub_distrib, ← Finset.mul_sum,
        Finset.sum_comm]
      congr 1
      refine Finset.sum_congr rfl fun a _ => (Finset.mul_sum _ _ _).symm
    rw [hdotU, hdotV]
    have hdist : ∑ a : Fin ρ, (cof a : K) * (dotK (u (I a)) z + dotK (v (I a)) y) =
        (∑ a : Fin ρ, (cof a : K) * dotK (u (I a)) z) +
        (∑ a : Fin ρ, (cof a : K) * dotK (v (I a)) y) := by
      simp only [mul_add, Finset.sum_add_distrib]
    dsimp only [cof] at hdist ⊢
    rw [hdist]
    ring
  have hinj_of_det_ne : ∀ {ρ : ℕ} {I : Fin ρ → Fin E} {J : Fin ρ → Fin M},
      (Matrix.of fun a b => v (I a) (J b)).det ≠ 0 → Function.Injective J := by
    intro ρ I J hdet b₁ b₂ hJ
    by_contra hne
    exact hdet (Matrix.det_zero_of_column_eq hne fun a => by simp [hJ])
  have hle_of_det_ne : ∀ {ρ : ℕ} {I : Fin ρ → Fin E} {J : Fin ρ → Fin M},
      (Matrix.of fun a b => v (I a) (J b)).det ≠ 0 → ρ ≤ M := by
    intro ρ I J hdet
    have hinj := hinj_of_det_ne hdet
    simpa [Fintype.card_fin] using Fintype.card_le_of_injective J hinj
  constructor
  · rintro ⟨y, hy_eq, hy_neq⟩
    let S : Finset ℕ := (Finset.range (M + 1)).filter fun ρ =>
      ∃ (I : Fin ρ → Fin E) (J : Fin ρ → Fin M),
        (Matrix.of fun a b => v (I a) (J b)).det ≠ 0
    have h0S : 0 ∈ S := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.succ_pos M),
        Fin.elim0, Fin.elim0, by simp⟩
    let ρ := S.max' ⟨0, h0S⟩
    have hρS : ρ ∈ S := Finset.max'_mem S ⟨0, h0S⟩
    have hρ_le : ρ ≤ M := Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_filter.mp hρS).1)
    obtain ⟨I, J, hP⟩ := (Finset.mem_filter.mp hρS).2
    let P : Matrix (Fin ρ) (Fin ρ) ℤ := Matrix.of fun a b => v (I a) (J b)
    have hmax : ∀ (i : Fin E) (j : Fin M),
        (borderMat P (fun a => v (I a) j) (fun b => v i (J b)) (v i j)).det = 0 := by
      intro i j
      by_contra hne
      let I' : Fin (ρ + 1) → Fin E := Fin.snoc I i
      let J' : Fin (ρ + 1) → Fin M := Fin.snoc J j
      have hmat : Matrix.of (fun a b => v (I' a) (J' b)) =
          borderMat P (fun a => v (I a) j) (fun b => v i (J b)) (v i j) := by
        ext a b
        cases a using Fin.lastCases <;> cases b using Fin.lastCases <;>
          simp [I', J', P, borderMat]
      have hdet' : (Matrix.of fun a b => v (I' a) (J' b)).det ≠ 0 := hmat.symm ▸ hne
      have hle' : ρ + 1 ≤ M := hle_of_det_ne hdet'
      have hmem' : ρ + 1 ∈ S :=
        Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hle'), I', J', hdet'⟩
      have hge : ρ + 1 ≤ ρ := Finset.le_max' S (ρ + 1) hmem'
      omega
    refine ⟨ρ, hρ_le, I, J, hP, hmax, fun i => ?_, fun r hr => ?_⟩
    · have hc := hcomb I J (u i) (v i) y hP
      have hzero_rhs : dotK (fun j =>
          (borderMat P (fun a => v (I a) j) (fun b => v i (J b)) (v i j)).det) y = 0 := by
        simp [dotK, hmax]
      have hzero_lhs : (P.det : K) * (dotK (u i) z + dotK (v i) y) -
          ∑ a : Fin ρ, ((P.updateRow a (fun b => v i (J b))).det : K) *
            (dotK (u (I a)) z + dotK (v (I a)) y) = 0 := by
        simp [hy_eq]
      rw [hzero_lhs, hzero_rhs, add_zero] at hc
      exact hc.symm
    · by_cases hex : ∃ j : Fin M,
          (borderMat P (fun a => v (I a) j) (fun b => w r (J b)) (w r j)).det ≠ 0
      · exact Or.inl hex
      · right
        push Not at hex
        have hc := hcomb I J (q r) (w r) y hP
        have hzero_v : dotK (fun j =>
            (borderMat P (fun a => v (I a) j) (fun b => w r (J b)) (w r j)).det) y = 0 := by
          simp [dotK, hex]
        have hzero_sum : ∑ a : Fin ρ, ((P.updateRow a (fun b => w r (J b))).det : K) *
            (dotK (u (I a)) z + dotK (v (I a)) y) = 0 := by
          simp [hy_eq]
        rw [hzero_sum, sub_zero, hzero_v, add_zero] at hc
        rw [← hc]
        have hPK_ne : (P.det : K) ≠ 0 := Int.cast_ne_zero.mpr hP
        exact mul_ne_zero hPK_ne (hy_neq r hr)
  · rintro ⟨ρ, _, I, J, hP, hmax, hcons, hneq⟩
    let P : Matrix (Fin ρ) (Fin ρ) ℤ := Matrix.of fun a b => v (I a) (J b)
    have hJinj : Function.Injective J := hinj_of_det_ne hP
    let PK : Matrix (Fin ρ) (Fin ρ) K := P.map (Int.cast : ℤ → K)
    have hPK_det : PK.det = (P.det : K) := by
      have h := RingHom.map_det (Int.castRingHom K) P
      simpa [PK] using h.symm
    have hΔ : (P.det : K) ≠ 0 := Int.cast_ne_zero.mpr hP
    let yFree (t : K) (j : Fin M) : K := if j ∈ Set.range J then 0 else t ^ (j.val + 1)
    let yPivot (t : K) : Fin ρ → K :=
      (P.det : K)⁻¹ • (PK.adjugate *ᵥ fun a => -(dotK (u (I a)) z + dotK (v (I a)) (yFree t)))
    let yOf (t : K) (j : Fin M) : K :=
      if h : ∃ b : Fin ρ, J b = j then yPivot t h.choose else yFree t j
    have hyOf_J (t : K) (b : Fin ρ) : yOf t (J b) = yPivot t b := by
      have hex : ∃ b' : Fin ρ, J b' = J b := ⟨b, rfl⟩
      simp only [yOf, dite_eq_left hex]
      congr 1
      exact hJinj hex.choose_spec
    have hyOf_notMem (t : K) {j : Fin M} (hj : j ∉ Set.range J) :
        yOf t j = t ^ (j.val + 1) := by
      have hne : ¬∃ b : Fin ρ, J b = j := hj
      simp [yOf, yFree, hne]
    have hyOf_pivot (t : K) (a : Fin ρ) : dotK (u (I a)) z + dotK (v (I a)) (yOf t) = 0 := by
      have hsplit : dotK (v (I a)) (yOf t) =
          (PK *ᵥ yPivot t) a + dotK (v (I a)) (yFree t) := by
        simp only [dotK, Matrix.mulVec, dotProduct, PK, P, Matrix.map_apply, Matrix.of_apply]
        rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.univ)
          (p := fun j : Fin M => j ∈ Set.range J)]
        congr 1
        · symm
          refine Finset.sum_bij (fun b _ => J b)
            (fun b _ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨b, rfl⟩⟩)
            (fun _ _ _ _ h => hJinj h)
            (fun j hj => by
              obtain ⟨b, rfl⟩ := (Finset.mem_filter.mp hj).2
              exact ⟨b, Finset.mem_univ b, rfl⟩)
            fun b _ => by rw [hyOf_J]
        · rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.univ)
            (p := fun j : Fin M => j ∈ Set.range J)]
          have hzero : ∑ j ∈ Finset.univ.filter (fun j : Fin M => j ∈ Set.range J),
              (v (I a) j : K) * yFree t j = 0 :=
            Finset.sum_eq_zero fun j hj => by
              dsimp only [yFree]
              rw [ite_eq_left (Finset.mem_filter.mp hj).2, mul_zero]
          rw [hzero, zero_add]
          refine Finset.sum_congr rfl fun j hj => by
            have hnm : j ∉ Set.range J := (Finset.mem_filter.mp hj).2
            rw [hyOf_notMem t hnm]
            dsimp only [yFree]
            rw [ite_eq_right hnm]
      have hmul : (PK *ᵥ yPivot t) a = -(dotK (u (I a)) z + dotK (v (I a)) (yFree t)) := by
        dsimp only [yPivot]
        rw [Matrix.mulVec_smul, Pi.smul_apply, Matrix.mulVec_mulVec, Matrix.mul_adjugate,
          hPK_det, Matrix.smul_mulVec, Matrix.one_mulVec, Pi.smul_apply, smul_eq_mul,
          smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hΔ, one_mul]
      rw [hsplit, hmul]
      ring
    have hyOf_eq (t : K) (i : Fin E) : dotK (u i) z + dotK (v i) (yOf t) = 0 := by
      have hc := hcomb I J (u i) (v i) (yOf t) hP
      have hzero_sum : ∑ a : Fin ρ, ((P.updateRow a (fun b => v i (J b))).det : K) *
          (dotK (u (I a)) z + dotK (v (I a)) (yOf t)) = 0 := by
        simp [hyOf_pivot]
      have hzero_v : dotK (fun j =>
          (borderMat P (fun a => v (I a) j) (fun b => v i (J b)) (v i j)).det) (yOf t) = 0 := by
        dsimp only [P]
        simp [dotK, hmax]
      rw [hzero_sum, sub_zero, hcons i, hzero_v, add_zero] at hc
      exact (mul_eq_zero.mp hc).resolve_left hΔ
    let freeSet : Finset (Fin M) := Finset.univ.filter (fun j : Fin M => j ∉ Set.range J)
    let Pr (r : Fin N) : Polynomial K :=
      Polynomial.C (dotK (fun d =>
        (borderMat P (fun a => u (I a) d) (fun b => w r (J b)) (q r d)).det) z) +
      ∑ j ∈ freeSet,
        Polynomial.C ((borderMat P (fun a => v (I a) j) (fun b => w r (J b)) (w r j)).det : K) *
          Polynomial.X ^ (j.val + 1)
    have hPr_eval (r : Fin N) (t : K) :
        (Pr r).eval t = (P.det : K) * (dotK (q r) z + dotK (w r) (yOf t)) := by
      have hc := hcomb I J (q r) (w r) (yOf t) hP
      have hzero_sum : ∑ a : Fin ρ, ((P.updateRow a (fun b => w r (J b))).det : K) *
          (dotK (u (I a)) z + dotK (v (I a)) (yOf t)) = 0 := by
        simp [hyOf_pivot]
      rw [hzero_sum, sub_zero] at hc
      rw [hc]
      simp only [Pr, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_finsetSum,
        Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]
      congr 1
      dsimp only [dotK]
      symm
      rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.univ)
        (p := fun j : Fin M => j ∈ Set.range J)]
      have hzero_in : ∑ j ∈ Finset.univ.filter (fun j : Fin M => j ∈ Set.range J),
          ((borderMat P (fun a => v (I a) j) (fun b => w r (J b)) (w r j)).det : K) * yOf t j =
          0 := by
        refine Finset.sum_eq_zero fun j hj => ?_
        obtain ⟨b₀, rfl⟩ := (Finset.mem_filter.mp hj).2
        have h0 := borderMat_det_eq_zero_of_col_eq P (fun a => v (I a) (J b₀))
          (fun b => w r (J b)) (w r (J b₀)) (b₀ := b₀) rfl rfl
        simp [h0]
      rw [hzero_in, zero_add]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [hyOf_notMem t (Finset.mem_filter.mp hj).2]
    have hPr_ne (r : Fin N) (hr : isNeq r = true) : Pr r ≠ 0 := by
      rcases hneq r hr with ⟨j₀, hj₀⟩ | hconst
      · have hj₀_free : j₀ ∈ freeSet := by
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ j₀, ?_⟩
          rintro ⟨b₀, rfl⟩
          exact hj₀ (borderMat_det_eq_zero_of_col_eq P (fun a => v (I a) (J b₀))
            (fun b => w r (J b)) (w r (J b₀)) (b₀ := b₀) rfl rfl)
        intro h0
        have hcoeff := congrArg (fun p : Polynomial K => p.coeff (j₀.val + 1)) h0
        simp only [Pr, Polynomial.coeff_zero, Polynomial.coeff_add, Polynomial.coeff_C_succ,
          zero_add, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow] at hcoeff
        rw [Finset.sum_eq_single j₀] at hcoeff
        · simp only [↓reduceIte] at hcoeff
          exact hj₀ (Int.cast_eq_zero.mp hcoeff)
        · intro j _ hne
          have hval : j₀.val + 1 ≠ j.val + 1 := fun h => hne (Fin.ext (by omega))
          rw [ite_eq_right hval]
        · intro hnm; exact absurd hj₀_free hnm
      · intro h0
        have hcoeff := congrArg (fun p : Polynomial K => p.coeff 0) h0
        simp only [Pr, Polynomial.coeff_zero, Polynomial.coeff_add, Polynomial.coeff_C_zero,
          Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow] at hcoeff
        have hsum0 : ∑ j ∈ freeSet,
            (if 0 = j.val + 1 then
              ((borderMat P (fun a => v (I a) j) (fun b => w r (J b)) (w r j)).det : K)
            else 0) = 0 :=
          Finset.sum_eq_zero fun j _ => by simp
        rw [hsum0, add_zero] at hcoeff
        exact hconst hcoeff
    let active : Finset (Fin N) := Finset.univ.filter fun r => isNeq r = true
    let Qpoly : Polynomial K := ∏ r ∈ active, Pr r
    have hQ_ne : Qpoly ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun r hr => hPr_ne r (Finset.mem_filter.mp hr).2
    have : Infinite K := Infinite.of_injective (Nat.cast : ℕ → K) Nat.cast_injective
    obtain ⟨t, ht⟩ := Infinite.exists_notMem_finset Qpoly.roots.toFinset
    have hQ_eval : Qpoly.eval t ≠ 0 := by
      intro hev
      exact ht (Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hQ_ne).mpr hev))
    refine ⟨yOf t, hyOf_eq t, fun r hr => ?_⟩
    have hr_act : r ∈ active := Finset.mem_filter.mpr ⟨Finset.mem_univ r, hr⟩
    have hPr_ev_ne : (Pr r).eval t ≠ 0 := by
      rw [Polynomial.eval_prod] at hQ_eval
      exact (Finset.prod_ne_zero_iff.mp hQ_eval) r hr_act
    rw [hPr_eval r t] at hPr_ev_ne
    exact (mul_ne_zero_iff.mp hPr_ev_ne).2

end CslibFrontier.Complexity.RealAlgebraic
