module

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Bool
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Pair
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Unary
public import CslibFrontier.Computability.Machines.Turing.MultiTape.PolyTime
public import Mathlib.MeasureTheory.Constructions.Pi
import Cslib.Probability.PMF
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Bounded-Depth Linear-Threshold Circuits and Polynomial-Time Weak PAC Learning

This module defines bounded-depth, bounded-size directed acyclic real-weight linear-threshold
circuits (`ThresholdCircuit`, `thresholdCircuitClass`), deterministic multi-tape Turing machine
polynomial-time weak PAC learnability (`IsWeaklyPolyTimePACLearnable`), and the canonical
cryptographic learning-hardness conjecture for constant-depth polynomial-size linear-threshold
circuits (`TC0LearningHardnessConjecture`), proved strictly under standard Lean axioms.

## Main definitions

* `CslibFrontier.MachineLearning.PACLearning.ThresholdCircuit`: directed acyclic real-weight
  linear-threshold circuits
  over `{0, 1}^n` partitioned by topological layer.
* `CslibFrontier.MachineLearning.PACLearning.ThresholdCircuit.gateVal`,
    `CslibFrontier.MachineLearning.PACLearning.ThresholdCircuit.eval`: recursive gate evaluation and
  circuit output on
  bitstrings.
* `CslibFrontier.MachineLearning.PACLearning.thresholdCircuitClass`: the Boolean concept class of
  `n`-input
  linear-threshold circuits of bounded depth and size.
* `CslibFrontier.MachineLearning.PACLearning.IsWeaklyPolyTimePACLearnable`: deterministic multi-tape
  Turing machine
  polynomial-time weak PAC learnability of a parameterized Boolean concept family over `{0, 1}^n`.
* `CslibFrontier.MachineLearning.PACLearning.TC0LearningHardnessConjecture`: canonical cryptographic
  hardness
  conjecture asserting the existence of a constant depth `L ≥ 1` and polynomial size bound
  `p(n) = C_s * (n + 1)^k_s` such that depth-`L`, size-`p(n)` linear-threshold circuits are not
  weakly PAC learnable in deterministic polynomial time.

## Main results

* `CslibFrontier.MachineLearning.PACLearning.ThresholdCircuit.gateVal_eq`: dense gate-evaluation
  recurrence summing
  over all internal gates.
* `CslibFrontier.MachineLearning.PACLearning.IsWeaklyPolyTimePACLearnable.mono`: antitonicity of
  weak polynomial-time
  PAC learnability with respect to concept-class inclusion.
* `CslibFrontier.MachineLearning.PACLearning.isWeaklyPolyTimePACLearnable_const`: unconditional
  positive witness that
  the two-function constant Boolean class is weakly PAC learnable in deterministic polynomial time.
* `CslibFrontier.MachineLearning.PACLearning.not_isWeaklyPolyTimePACLearnable_univ`: unconditional
  information-theoretic impossibility of weakly PAC learning the family of all Boolean functions
  in polynomial sample complexity.
* `CslibFrontier.MachineLearning.PACLearning.tc0LearningHardnessConjecture_iff` and
  `TC0LearningHardnessConjecture.not_of_polyTime_reduction`: unfolding characterization and
  generic polynomial-time reduction transfer for `TC0LearningHardnessConjecture`.


## Tags

threshold circuit, TC0, PAC learning, weak learning, cryptographic hardness, polynomial time
-/

public section

open MeasureTheory
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime
open scoped ENNReal NNReal

namespace CslibFrontier.MachineLearning.PACLearning

/-! ### Bounded-depth linear-threshold circuits -/

/-- A directed acyclic real-weight linear-threshold circuit over `{0, 1}^n` with `numGates`
internal gates partitioned by topological layer `layer g ∈ {0, …, depth - 1}`, real input edge
weights `inWeight`, strictly feedforward internal edge weights `gateWeight`, and designated output
gate `outGate`. -/
structure ThresholdCircuit (n : ℕ) where
  /-- Number of internal gates. -/
  numGates : ℕ
  /-- Circuit depth (number of layers). -/
  depth : ℕ
  /-- Topological layer `layer g < depth` of each internal gate `g`. -/
  layer : Fin numGates → ℕ
  /-- Every gate layer is strictly below the circuit depth. -/
  layer_lt_depth : ∀ g, layer g < depth
  /-- Edge weights from the `n` input nodes to each internal gate. -/
  inWeight : Fin numGates → Fin n → ℝ
  /-- Edge weights between internal gates, supported on `layer u < layer v`. -/
  gateWeight : Fin numGates → Fin numGates → ℝ
  /-- Feedforward acyclicity: internal edge weights vanish unless `layer u < layer v`. -/
  gateWeight_eq_zero_of_le : ∀ v u, layer v ≤ layer u → gateWeight v u = 0
  /-- Designated output gate. -/
  outGate : Fin numGates

/-- Evaluation of gate `v` of a `ThresholdCircuit n` on input `x : Fin n → Bool`, defined by
well-founded recursion on `C.layer v`. -/
noncomputable def ThresholdCircuit.gateVal {n : ℕ} (C : ThresholdCircuit n) (x : Fin n → Bool)
    (v : Fin C.numGates) : Bool :=
  decide (0 ≤
    (∑ k : Fin n, C.inWeight v k * ((x k).toNat : ℝ)) +
      ∑ u : {u : Fin C.numGates // C.layer u < C.layer v},
        C.gateWeight v u.1 * ((C.gateVal x u.1).toNat : ℝ))
termination_by C.layer v
decreasing_by exact u.2

/-- Unfolding equation for `ThresholdCircuit.gateVal` summing over all `u : Fin C.numGates`
(using `C.gateWeight v u = 0` whenever `C.layer v ≤ C.layer u`). -/
theorem ThresholdCircuit.gateVal_eq {n : ℕ} (C : ThresholdCircuit n) (x : Fin n → Bool)
    (v : Fin C.numGates) :
    C.gateVal x v = decide (0 ≤
      (∑ k : Fin n, C.inWeight v k * ((x k).toNat : ℝ)) +
        ∑ u : Fin C.numGates, C.gateWeight v u * ((C.gateVal x u).toNat : ℝ)) := by
  classical
  rw [ThresholdCircuit.gateVal]
  have hsum : (∑ u : {u : Fin C.numGates // C.layer u < C.layer v},
      C.gateWeight v u.1 * ((C.gateVal x u.1).toNat : ℝ)) =
      ∑ u : Fin C.numGates, C.gateWeight v u * ((C.gateVal x u).toNat : ℝ) := by
    have hsub : (∑ u : {u : Fin C.numGates // C.layer u < C.layer v},
        C.gateWeight v u.1 * ((C.gateVal x u.1).toNat : ℝ)) =
        ∑ u ∈ Finset.univ.filter (fun u : Fin C.numGates => C.layer u < C.layer v),
          C.gateWeight v u * ((C.gateVal x u).toNat : ℝ) := by
      simpa using (Finset.sum_subtype
        (Finset.univ.filter fun u : Fin C.numGates => C.layer u < C.layer v)
        (fun _ => by simp)
        (fun u => C.gateWeight v u * ((C.gateVal x u).toNat : ℝ))).symm
    rw [hsub]
    refine Finset.sum_subset (Finset.subset_univ _) fun u _ hu => ?_
    have hle : C.layer v ≤ C.layer u :=
      not_lt.mp fun hlt => hu (Finset.mem_filter.mpr ⟨Finset.mem_univ u, hlt⟩)
    rw [C.gateWeight_eq_zero_of_le v u hle, zero_mul]
  rw [hsum]

/-- Output `C(x) = val(v_out)` of a `ThresholdCircuit n` on `x : List Bool` (reading `x[k]` via
`x.getD k false`). -/
@[expose] noncomputable def ThresholdCircuit.eval {n : ℕ} (C : ThresholdCircuit n) (x : List Bool) :
    Bool :=
  C.gateVal (fun k => x.getD k.1 false) C.outGate

/-- Hypothesis class of `n`-input linear-threshold circuits of depth at most `L` and size at most
`s`. -/
@[expose] def thresholdCircuitClass (n L s : ℕ) : Set (List Bool → Bool) :=
  {f | ∃ C : ThresholdCircuit n, C.depth ≤ L ∧ C.numGates ≤ s ∧ f = C.eval}

/-- Monotonicity of `thresholdCircuitClass` in depth and size bounds. -/
@[gcongr]
theorem thresholdCircuitClass_mono {n L₁ L₂ s₁ s₂ : ℕ} (hL : L₁ ≤ L₂) (hs : s₁ ≤ s₂) :
    thresholdCircuitClass n L₁ s₁ ⊆ thresholdCircuitClass n L₂ s₂ := by
  rintro f ⟨C, hCdepth, hCsize, rfl⟩
  exact ⟨C, hCdepth.trans hL, hCsize.trans hs, rfl⟩

/-- Every `ThresholdCircuit` has at least one gate (`outGate`), so depth `0` circuits do not exist.
-/
@[simp]
theorem thresholdCircuitClass_zero_depth (n s : ℕ) : thresholdCircuitClass n 0 s = ∅ := by
  ext f
  simp only [thresholdCircuitClass, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨C, hdepth, -, -⟩
  have hlt := C.layer_lt_depth C.outGate
  omega

/-- Every `ThresholdCircuit` has a designated `outGate : Fin C.numGates`, so size `0` is empty. -/
@[simp]
theorem thresholdCircuitClass_zero_size (n L : ℕ) : thresholdCircuitClass n L 0 = ∅ := by
  ext f
  simp only [thresholdCircuitClass, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨C, -, hsize, -⟩
  have hlt := C.outGate.isLt
  omega

/-! ### Polynomial-time weak PAC learnability and `TC^0` learning-hardness conjecture -/

/-- Deterministic multi-tape Turing machine polynomial-time weak PAC learnability for a
parameterized Boolean concept family `(n ↦ C n)` over `{0, 1}^n` (with the discrete σ-algebra `⊤`
on `List Bool`): there exist accuracy/confidence constants `ε₀ ∈ (0, 1 / 2)` and `δ₀ ∈ (0, 1)`, a
polynomial sample-size schedule `m(n) ≤ C_m * (n + 1)^k_m`, a hypothesis representation
`(Θ, encΘ)`, a polynomial-time learner `learn (n, S) : Θ`, and a polynomial-time evaluator
`eval (n, θ, x)` achieving population error `≤ ε₀` with probability `≥ 1 - δ₀` over every
probability distribution `D` supported on `{x : List Bool | x.length = n}` and every target
`c ∈ C n`. -/
def IsWeaklyPolyTimePACLearnable (C : ℕ → Set (List Bool → Bool)) : Prop :=
  let _ : MeasurableSpace (List Bool) := ⊤
  ∃ (ε₀ δ₀ : ℝ) (_hε0 : 0 < ε₀) (_hεhalf : ε₀ < 1 / 2) (_hδ0 : 0 < δ₀) (_hδ1 : δ₀ < 1)
    (m : ℕ → ℕ) (C_m k_m : ℕ) (_hm_poly : ∀ n, m n ≤ C_m * (n + 1) ^ k_m)
    (Θ : Type) (encΘ : Θ ↪ List Bool)
    (learn : ℕ → List (List Bool × Bool) → Θ)
    (eval : ℕ → Θ → List Bool → Bool),
    ComputableInPolyTime (fun p : ℕ × List (List Bool × Bool) => learn p.1 p.2)
      (encPair encUnary (encList (encPair (encList encBool) encBool))) encΘ ∧
    ComputableInPolyTime (fun p : (ℕ × Θ) × List Bool => eval p.1.1 p.1.2 p.2)
      (encPair (encPair encUnary encΘ) (encList encBool)) encBool ∧
    ∀ (n : ℕ), 1 ≤ n →
      ∀ (D : Measure (List Bool)) [IsProbabilityMeasure D],
        D {x : List Bool | x.length = n}ᶜ = 0 →
        ∀ c ∈ C n,
          Measure.pi (fun _ : Fin (m n) => D)
            {xs : Fin (m n) → List Bool |
              ENNReal.ofReal ε₀ <
                D {x | eval n (learn n (List.ofFn fun i => (xs i, c (xs i)))) x ≠ c x}} ≤
            ENNReal.ofReal δ₀

/-- Characterization of `IsWeaklyPolyTimePACLearnable` exposing the weak-learning constants,
polynomial sample bound, hypothesis encoding, and polynomial-time learner/evaluator pair. -/
theorem isWeaklyPolyTimePACLearnable_iff (C : ℕ → Set (List Bool → Bool)) :
    IsWeaklyPolyTimePACLearnable C ↔
      let _ : MeasurableSpace (List Bool) := ⊤
      ∃ (ε₀ δ₀ : ℝ) (_hε0 : 0 < ε₀) (_hεhalf : ε₀ < 1 / 2) (_hδ0 : 0 < δ₀) (_hδ1 : δ₀ < 1)
        (m : ℕ → ℕ) (C_m k_m : ℕ) (_hm_poly : ∀ n, m n ≤ C_m * (n + 1) ^ k_m)
        (Θ : Type) (encΘ : Θ ↪ List Bool)
        (learn : ℕ → List (List Bool × Bool) → Θ)
        (eval : ℕ → Θ → List Bool → Bool),
        ComputableInPolyTime (fun p : ℕ × List (List Bool × Bool) => learn p.1 p.2)
          (encPair encUnary (encList (encPair (encList encBool) encBool))) encΘ ∧
        ComputableInPolyTime (fun p : (ℕ × Θ) × List Bool => eval p.1.1 p.1.2 p.2)
          (encPair (encPair encUnary encΘ) (encList encBool)) encBool ∧
        ∀ (n : ℕ), 1 ≤ n →
          ∀ (D : Measure (List Bool)) [IsProbabilityMeasure D],
            D {x : List Bool | x.length = n}ᶜ = 0 →
            ∀ c ∈ C n,
              Measure.pi (fun _ : Fin (m n) => D)
                {xs : Fin (m n) → List Bool |
                  ENNReal.ofReal ε₀ <
                    D {x | eval n (learn n (List.ofFn fun i => (xs i, c (xs i)))) x ≠ c x}} ≤
                ENNReal.ofReal δ₀ :=
  Iff.rfl

/-- Weak polynomial-time PAC learnability is antitone in the concept family. -/
theorem IsWeaklyPolyTimePACLearnable.mono {C₁ C₂ : ℕ → Set (List Bool → Bool)}
    (h : IsWeaklyPolyTimePACLearnable C₂) (hsub : ∀ n, C₁ n ⊆ C₂ n) :
    IsWeaklyPolyTimePACLearnable C₁ := by
  let _ : MeasurableSpace (List Bool) := ⊤
  obtain ⟨ε₀, δ₀, hε0, hεhalf, hδ0, hδ1, m, C_m, k_m, hm_poly, Θ, encΘ, learn, eval,
    hlearn_pt, heval_pt, hpac⟩ := h
  exact ⟨ε₀, δ₀, hε0, hεhalf, hδ0, hδ1, m, C_m, k_m, hm_poly, Θ, encΘ, learn, eval,
    hlearn_pt, heval_pt, fun n hn D hprob hD c hc => hpac n hn D hD c (hsub n hc)⟩

/-- Positive witness: the two-function constant Boolean concept family `{fun _ => false,
fun _ => true}` is weakly PAC learnable in deterministic polynomial time using a single example. -/
theorem isWeaklyPolyTimePACLearnable_const :
    IsWeaklyPolyTimePACLearnable (fun _ => {fun _ => false, fun _ => true}) := by
  let _ : MeasurableSpace (List Bool) := ⊤
  let learn : ℕ → List (List Bool × Bool) → Bool := fun _ S => (S.headD ([], false)).2
  let eval : ℕ → Bool → List Bool → Bool := fun _ b _ => b
  have hlearn_pt : ComputableInPolyTime (fun p : ℕ × List (List Bool × Bool) => learn p.1 p.2)
      (encPair encUnary (encList (encPair (encList encBool) encBool))) encBool :=
    (snd (encList encBool) encBool).comp
      (listHeadDWithInput (snd encUnary _) (const ([], false)))
  have heval_pt : ComputableInPolyTime (fun p : (ℕ × Bool) × List Bool => eval p.1.1 p.1.2 p.2)
      (encPair (encPair encUnary encBool) (encList encBool)) encBool :=
    (snd encUnary encBool).comp (fst _ _)
  refine ⟨1 / 4, 1 / 2, by norm_num, by norm_num, by norm_num, by norm_num,
    fun _ => 1, 1, 0, fun _ => by simp, Bool, encBool, learn, eval, hlearn_pt, heval_pt,
    fun n _ D _ _ c hc => ?_⟩
  have hzero : ∀ xs : Fin 1 → List Bool,
      D {x | eval n (learn n (List.ofFn fun i => (xs i, c (xs i)))) x ≠ c x} = 0 := by
    intro xs
    have hconst : ∀ x y : List Bool, c x = c y := by
      rcases hc with rfl | rfl <;> intro _ _ <;> rfl
    have heq : {x | eval n (learn n (List.ofFn fun i => (xs i, c (xs i)))) x ≠ c x} = ∅ := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_not, eval, learn,
        List.ofFn_succ, List.ofFn_zero, List.headD_cons]
      exact hconst (xs 0) x
    rw [heq, measure_empty]
  have hempty : {xs : Fin 1 → List Bool |
      ENNReal.ofReal (1 / 4) <
        D {x | eval n (learn n (List.ofFn fun i => (xs i, c (xs i)))) x ≠ c x}} = ∅ := by
    ext xs
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt]
    rw [hzero xs]
    exact zero_le
  rw [hempty, measure_empty]
  exact zero_le

private theorem exists_pow_lt_two_pow (k : ℕ) {M : ℝ} (hM : 0 < M) :
    ∃ n : ℕ, 1 ≤ n ∧ M * ((n + 1 : ℝ) ^ k) < (2 : ℝ) ^ n := by
  let q : ℕ := ⌈M * ((k + 1 : ℝ) ^ k)⌉₊ + 1
  have hq1 : 1 ≤ q := Nat.succ_pos _
  have hq_gt : M * ((k + 1 : ℝ) ^ k) < (q : ℝ) := by
    have h1 := Nat.le_ceil (M * ((k + 1 : ℝ) ^ k))
    have h2 : (q : ℝ) = (⌈M * ((k + 1 : ℝ) ^ k)⌉₊ : ℝ) + 1 := by simp [q]
    linarith
  have hq_two : (q : ℝ) < (2 : ℝ) ^ q := by
    exact_mod_cast Nat.lt_two_pow_self (n := q)
  have hq_succ_le : ((q + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ q := by
    exact_mod_cast Nat.succ_le_of_lt (Nat.lt_two_pow_self (n := q))
  let n : ℕ := (k + 1) * q
  refine ⟨n, Nat.mul_pos (Nat.succ_pos k) hq1, ?_⟩
  have hn1 : ((n + 1 : ℕ) : ℝ) ≤ ((k + 1 : ℝ) * ((q + 1 : ℕ) : ℝ)) := by
    have : n + 1 ≤ (k + 1) * (q + 1) := by
      dsimp [n]; rw [mul_add, mul_one]; exact Nat.add_le_add_left (Nat.succ_pos k) _
    exact_mod_cast this
  have hpow : ((n + 1 : ℝ) ^ k) ≤ ((k + 1 : ℝ) ^ k) * ((2 : ℝ) ^ q) ^ k := by
    have h1 : ((n + 1 : ℝ) ^ k) ≤ ((k + 1 : ℝ) * ((q + 1 : ℕ) : ℝ)) ^ k :=
      pow_le_pow_left₀ (by positivity) (by simpa using hn1) k
    rw [mul_pow] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) hq_succ_le k) (by positivity))
  have hlt : M * (((k + 1 : ℝ) ^ k) * ((2 : ℝ) ^ q) ^ k) < (2 : ℝ) ^ q * ((2 : ℝ) ^ q) ^ k := by
    rw [← mul_assoc]
    exact mul_lt_mul_of_pos_right (hq_gt.trans hq_two) (by positivity)
  have h2n : (2 : ℝ) ^ q * ((2 : ℝ) ^ q) ^ k = (2 : ℝ) ^ n := by
    rw [← pow_succ', ← pow_mul, mul_comm q (k + 1)]
  exact (mul_le_mul_of_nonneg_left hpow hM.le).trans_lt (hlt.trans_eq h2n)

private theorem sum_sq_rademacher {α : Type*} [Fintype α] [DecidableEq α] (g : α → Bool) :
    ∑ f : α → Bool,
      ((∑ u : α, if f u = g u then (1 : ℤ) else -1 : ℤ) : ℝ) ^ 2 =
      (Fintype.card α : ℝ) * (2 : ℝ) ^ Fintype.card α := by
  let s : (α → Bool) → α → ℤ := fun f u => if f u = g u then 1 else -1
  have hsq : ∀ f : α → Bool,
      ((∑ u : α, s f u : ℤ) : ℝ) ^ 2 =
        ∑ u : α, ∑ v : α, ((s f u * s f v : ℤ) : ℝ) := by
    intro f
    rw [sq, Int.cast_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun v _ => by push_cast; rfl
  change ∑ f : α → Bool, ((∑ u : α, s f u : ℤ) : ℝ) ^ 2 = _
  simp_rw [hsq]
  rw [Finset.sum_comm]
  have hinner : ∀ u : α,
      (∑ f : α → Bool, ∑ v : α, ((s f u * s f v : ℤ) : ℝ)) = (2 : ℝ) ^ Fintype.card α := by
    intro u
    rw [Finset.sum_comm, Finset.sum_eq_single u]
    · have hdiag : ∀ f : α → Bool, ((s f u * s f u : ℤ) : ℝ) = 1 := fun f => by
        dsimp [s]; split_ifs <;> norm_num
      simp_rw [hdiag]
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
        nsmul_eq_mul, mul_one, Nat.cast_pow, Nat.cast_ofNat]
    · intro v _ hvu
      have hflip : (∑ f : α → Bool, ((s f u * s f v : ℤ) : ℝ)) =
          ∑ f : α → Bool, -((s f u * s f v : ℤ) : ℝ) := by
        let inv : (α → Bool) ≃ (α → Bool) :=
          { toFun := fun f => Function.update f u (!f u)
            invFun := fun f => Function.update f u (!f u)
            left_inv := fun f => by
              funext w; by_cases hw : w = u
              · subst hw; simp
              · simp [hw]
            right_inv := fun f => by
              funext w; by_cases hw : w = u
              · subst hw; simp
              · simp [hw] }
        rw [← Equiv.sum_comp inv]
        refine Finset.sum_congr rfl fun f _ => ?_
        have hsu : s (inv f) u = -s f u := by
          dsimp [s, inv]; simp only [Function.update_self]
          cases f u <;> cases g u <;> decide
        have hsv : s (inv f) v = s f v := by
          dsimp [s, inv]; simp [hvu]
        rw [hsu, hsv]; push_cast; ring
      rw [Finset.sum_neg_distrib] at hflip
      linarith
    · intro h; exact (h (Finset.mem_univ u)).elim
  simp_rw [hinner]
  simp

/-- Sharpness / negative witness: the class of all Boolean functions is not weakly PAC learnable in
polynomial sample complexity (and hence not in polynomial time). -/
theorem not_isWeaklyPolyTimePACLearnable_univ :
    ¬ IsWeaklyPolyTimePACLearnable (fun _ => Set.univ) := by
  classical
  let _ : MeasurableSpace (List Bool) := ⊤
  have _ : MeasurableSingletonClass (List Bool) := ⟨fun _ => trivial⟩
  rintro ⟨ε₀, δ₀, hε0, hεhalf, hδ0, hδ1, m, C_m, k_m, hm_poly, Θ, encΘ, learn, eval, _, _, hpac⟩
  have hgap : 0 < 1 / 2 - ε₀ := by linarith
  have h1d : 0 < 1 - δ₀ := by linarith
  let M : ℝ := max ((2 * (C_m : ℝ) + 1) / (1 / 2 - ε₀)) (2 / ((1 - δ₀) * (1 / 2 - ε₀) ^ 2))
  have hM_pos : 0 < M := lt_of_lt_of_le (by positivity) (le_max_right _ _)
  obtain ⟨n, hn1, hMn⟩ := exists_pow_lt_two_pow k_m hM_pos
  have hpow_ge1 : (1 : ℝ) ≤ ((n + 1 : ℝ) ^ k_m) := one_le_pow₀ (by linarith)
  have hm_small : (m n : ℝ) ≤ ((1 / 2 - ε₀) / 2) * (2 : ℝ) ^ n := by
    have h1 : ((2 * (C_m : ℝ) + 1) / (1 / 2 - ε₀)) * ((n + 1 : ℝ) ^ k_m) < (2 : ℝ) ^ n :=
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)).trans_lt hMn
    rw [div_mul_eq_mul_div, div_lt_iff₀ hgap] at h1
    have hm_cast : (m n : ℝ) ≤ (C_m : ℝ) * ((n + 1 : ℝ) ^ k_m) := by exact_mod_cast hm_poly n
    have hCm_nn : (0 : ℝ) ≤ C_m := Nat.cast_nonneg _
    nlinarith
  have hvar_small : 1 < (1 - δ₀) * ((1 / 2 - ε₀) ^ 2 * (2 : ℝ) ^ n) := by
    have h1 : (2 / ((1 - δ₀) * (1 / 2 - ε₀) ^ 2)) * ((n + 1 : ℝ) ^ k_m) < (2 : ℝ) ^ n :=
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)).trans_lt hMn
    have h2 : 2 / ((1 - δ₀) * (1 / 2 - ε₀) ^ 2) < (2 : ℝ) ^ n :=
      lt_of_le_of_lt (le_mul_of_one_le_right (by positivity) hpow_ge1) h1
    have hden : 0 < (1 - δ₀) * (1 / 2 - ε₀) ^ 2 := by positivity
    have h3 := (div_lt_iff₀ hden).mp h2
    nlinarith
  let W : Finset (List Bool) := Finset.univ.image (fun v : Fin n → Bool => List.ofFn v)
  have hW_card : W.card = 2 ^ n := by
    rw [Finset.card_image_of_injective _ List.ofFn_injective]
    simp
  have hW_pos : 0 < W.card := by rw [hW_card]; positivity
  have hW_ne : W.Nonempty := Finset.card_pos.mp hW_pos
  have hW_mem : ∀ x : List Bool, x ∈ W ↔ x.length = n := fun x => by
    simp only [W, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨fun ⟨v, hv⟩ => by rw [← hv, List.length_ofFn],
      fun hx => ⟨fun i => x[i.1]'(hx ▸ i.2), List.ext_getElem (by simp [hx]) fun i hi _ => by simp⟩⟩
  let μ : PMF (List Bool) := Cslib.Probability.PMF.uniformOfFinset W hW_ne
  let D : Measure (List Bool) := μ.toMeasure
  have hD_prob : IsProbabilityMeasure D := PMF.toMeasure.isProbabilityMeasure μ
  have hD_supp : D {x : List Bool | x.length = n}ᶜ = 0 := by
    rw [PMF.toMeasure_apply μ trivial]
    refine tsum_eq_zero_iff.mpr fun x => ?_
    by_cases hx : x ∈ W
    · simp [Set.indicator_of_notMem, (hW_mem x).mp hx]
    · simp [μ, Cslib.Probability.PMF.uniformOfFinset_apply, hx]
  have hD_err : ∀ f g : List Bool → Bool,
      D {x : List Bool | f x ≠ g x} = ((W.filter fun x => f x ≠ g x).card : ℝ≥0∞) / W.card := by
    intro f g
    change μ.toMeasure {x | f x ≠ g x} = _
    rw [PMF.toMeasure_apply_eq_toOuterMeasure, PMF.toOuterMeasure_apply]
    have hsum : (∑' x : List Bool, Set.indicator {x | f x ≠ g x} μ x) =
        ∑ x ∈ W.filter (fun x => f x ≠ g x), (W.card : ℝ≥0∞)⁻¹ := by
      rw [tsum_eq_sum (s := W.filter fun x => f x ≠ g x)]
      · refine Finset.sum_congr rfl fun x hx => ?_
        obtain ⟨hxW, hfg⟩ := Finset.mem_filter.mp hx
        rw [Set.indicator_of_mem (show x ∈ {x | f x ≠ g x} from hfg)]
        simp [μ, Cslib.Probability.PMF.uniformOfFinset_apply, hxW]
      · intro x hx
        by_cases hxW : x ∈ W
        · exact Set.indicator_of_notMem (fun h => hx (Finset.mem_filter.mpr ⟨hxW, h⟩)) μ
        · simp [Set.indicator_apply, μ, Cslib.Probability.PMF.uniformOfFinset_apply, hxW]
    rw [hsum, Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]
  let cOf (b : ↥W → Bool) : List Bool → Bool := fun x => if hx : x ∈ W then b ⟨x, hx⟩ else false
  let isBad (xs : Fin (m n) → ↥W) (b : ↥W → Bool) : Bool :=
    decide (ENNReal.ofReal ε₀ <
      D {x | eval n (learn n (List.ofFn fun i => ((xs i).1, b (xs i)))) x ≠ cOf b x})
  -- For every fixed sample tuple `xs`, strictly more than `δ₀ * 2^|W|` concepts `b` are bad.
  have hpointwise : ∀ xs : Fin (m n) → ↥W,
      δ₀ * (2 : ℝ) ^ W.card <
        ((Finset.univ.filter fun b : ↥W → Bool => isBad xs b = true).card : ℝ) := by
    intro xs
    let seen : Finset ↥W := Finset.univ.image xs
    let U : Finset ↥W := Finset.univ \ seen
    have hdisj : Disjoint seen U := disjoint_sdiff_self_right
    have hunion : seen ∪ U = Finset.univ := Finset.union_sdiff_of_subset (Finset.subset_univ _)
    have hU_card : seen.card + U.card = W.card := by
      rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_univ, Fintype.card_coe]
    have hseen_le : seen.card ≤ m n := Finset.card_image_le.trans (by simp)
    let splitEquiv : (↥W → Bool) ≃ (↥seen → Bool) × (↥U → Bool) :=
      { toFun := fun b => (fun w => b w.1, fun w => b w.1)
        invFun := fun p w => if hw : w ∈ seen then p.1 ⟨w, hw⟩ else p.2 ⟨w, Finset.mem_sdiff.mpr
          ⟨Finset.mem_univ w, hw⟩⟩
        left_inv := fun b => by funext w; by_cases hw : w ∈ seen <;> simp [hw]
        right_inv := fun ⟨bS, bU⟩ => by
          ext w
          · simp [w.2]
          · have hnot : w.1 ∉ seen := (Finset.mem_sdiff.mp w.2).2
            simp [hnot] }
    -- For each fixed restriction `bS` on `seen`, bound the number of good completions `bU`.
    have hper : ∀ bS : ↥seen → Bool,
        ((Finset.univ.filter fun bU : ↥U → Bool =>
            isBad xs (splitEquiv.symm (bS, bU)) = false).card : ℝ) <
          (1 - δ₀) * (2 : ℝ) ^ U.card := by
      intro bS
      let hHyp : List Bool → Bool := eval n (learn n (List.ofFn fun i : Fin (m n) =>
        ((xs i).1, bS ⟨xs i, Finset.mem_image_of_mem xs (Finset.mem_univ i)⟩)))
      let goodU : Finset (↥U → Bool) :=
        Finset.univ.filter fun bU => isBad xs (splitEquiv.symm (bS, bU)) = false
      have hgood_bound : ∀ bU ∈ goodU,
          (1 / 2 - ε₀) * (W.card : ℝ) ≤
            ((∑ u : ↥U, if bU u = hHyp u.1.1 then (1 : ℤ) else -1 : ℤ) : ℝ) := by
        intro bU hbU
        have hnotbad : ¬ ENNReal.ofReal ε₀ <
            D {x | eval n (learn n (List.ofFn fun i =>
              ((xs i).1, splitEquiv.symm (bS, bU) (xs i)))) x ≠
              cOf (splitEquiv.symm (bS, bU)) x} := by
          have := (Finset.mem_filter.mp hbU).2
          simpa [isBad] using this
        have hsample_eq : (List.ofFn fun i : Fin (m n) =>
            ((xs i).1, splitEquiv.symm (bS, bU) (xs i))) =
            List.ofFn fun i : Fin (m n) =>
              ((xs i).1, bS ⟨xs i, Finset.mem_image_of_mem xs (Finset.mem_univ i)⟩) := by
          refine List.ext_getElem (by simp) fun i hi1 hi2 => ?_
          simp only [List.getElem_ofFn, splitEquiv, Equiv.coe_fn_symm_mk]
          have hmem : xs ⟨i, by simpa using hi1⟩ ∈ seen :=
            Finset.mem_image_of_mem xs (Finset.mem_univ _)
          simp [hmem]
        rw [hsample_eq] at hnotbad
        have hle_enn : D {x | hHyp x ≠ cOf (splitEquiv.symm (bS, bU)) x} ≤ ENNReal.ofReal ε₀ :=
          le_of_not_gt hnotbad
        rw [hD_err] at hle_enn
        have hW_ne0 : (W.card : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr hW_pos.ne'
        have hW_top : (W.card : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
        have herr_real : ((W.filter fun x => hHyp x ≠ cOf (splitEquiv.symm (bS, bU)) x).card : ℝ) ≤
            ε₀ * (W.card : ℝ) := by
          have hmul := (ENNReal.div_le_iff_le_mul (Or.inl hW_ne0) (Or.inl hW_top)).mp hle_enn
          have htoR := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hW_top) hmul
          rw [ENNReal.toReal_natCast, ENNReal.toReal_mul, ENNReal.toReal_ofReal hε0.le,
            ENNReal.toReal_natCast] at htoR
          exact htoR
        have hU_err_le : ((Finset.univ.filter fun u : ↥U => bU u ≠ hHyp u.1.1).card : ℝ) ≤
            ((W.filter fun x => hHyp x ≠ cOf (splitEquiv.symm (bS, bU)) x).card : ℝ) := by
          have hsub : (Finset.univ.filter fun u : ↥U => bU u ≠ hHyp u.1.1).image
              (fun u : ↥U => u.1.1) ⊆
              W.filter fun x => hHyp x ≠ cOf (splitEquiv.symm (bS, bU)) x := by
            intro x hx
            obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
            have hne : bU u ≠ hHyp u.1.1 := (Finset.mem_filter.mp hu).2
            have hnotS : u.1 ∉ seen := (Finset.mem_sdiff.mp u.2).2
            refine Finset.mem_filter.mpr ⟨u.1.2, ?_⟩
            simp only [cOf, u.1.2, ↓reduceDIte, splitEquiv, Equiv.coe_fn_symm_mk, hnotS]
            exact hne.symm
          have hinj : Function.Injective (fun u : ↥U => u.1.1) :=
            fun u₁ u₂ h => Subtype.ext (Subtype.ext h)
          have hcard := Finset.card_le_card hsub
          rw [Finset.card_image_of_injective _ hinj] at hcard
          exact_mod_cast hcard
        have hsum_id : (∑ u : ↥U, if bU u = hHyp u.1.1 then (1 : ℤ) else -1) =
            (U.card : ℤ) - 2 * ((Finset.univ.filter fun u : ↥U => bU u ≠ hHyp u.1.1).card : ℤ) := by
          have hpart : (Finset.univ.filter fun u : ↥U => bU u = hHyp u.1.1).card +
              (Finset.univ.filter fun u : ↥U => bU u ≠ hHyp u.1.1).card = U.card := by
            rw [← Finset.card_union_of_disjoint
              (Finset.disjoint_filter.mpr fun _ _ h1 h2 => h2 h1)]
            have hun : (Finset.univ.filter fun u : ↥U => bU u = hHyp u.1.1) ∪
                (Finset.univ.filter fun u : ↥U => bU u ≠ hHyp u.1.1) = Finset.univ := by
              ext u; simp [em]
            rw [hun, Finset.card_univ, Fintype.card_coe]
          have hsplit : (∑ u : ↥U, if bU u = hHyp u.1.1 then (1 : ℤ) else -1) =
              ((Finset.univ.filter fun u : ↥U => bU u = hHyp u.1.1).card : ℤ) -
                ((Finset.univ.filter fun u : ↥U => bU u ≠ hHyp u.1.1).card : ℤ) := by
            rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
            simp only [mul_one, mul_neg, sub_eq_add_neg]
          omega
        have hU_ge : (W.card : ℝ) - (m n : ℝ) ≤ (U.card : ℝ) := by
          have h1 : (seen.card : ℝ) + (U.card : ℝ) = (W.card : ℝ) := by exact_mod_cast hU_card
          have h2 : (seen.card : ℝ) ≤ (m n : ℝ) := by exact_mod_cast hseen_le
          linarith
        have hWc : (W.card : ℝ) = (2 : ℝ) ^ n := by exact_mod_cast hW_card
        have hcast : ((∑ u : ↥U, if bU u = hHyp u.1.1 then (1 : ℤ) else -1 : ℤ) : ℝ) =
            (U.card : ℝ) - 2 * ((Finset.univ.filter fun u : ↥U => bU u ≠ hHyp u.1.1).card : ℝ) := by
          exact_mod_cast hsum_id
        rw [hcast]
        nlinarith [hm_small, hWc, hU_ge, hU_err_le, herr_real]
      have hmarkov : (goodU.card : ℝ) * ((1 / 2 - ε₀) * (W.card : ℝ)) ^ 2 ≤
          (U.card : ℝ) * (2 : ℝ) ^ U.card := by
        calc (goodU.card : ℝ) * ((1 / 2 - ε₀) * (W.card : ℝ)) ^ 2
            = ∑ _bU ∈ goodU, ((1 / 2 - ε₀) * (W.card : ℝ)) ^ 2 := by simp
          _ ≤ ∑ bU ∈ goodU,
                ((∑ u : ↥U, if bU u = hHyp u.1.1 then (1 : ℤ) else -1 : ℤ) : ℝ) ^ 2 :=
              Finset.sum_le_sum fun bU hbU =>
                pow_le_pow_left₀ (by positivity) (hgood_bound bU hbU) 2
          _ ≤ ∑ bU : ↥U → Bool,
                ((∑ u : ↥U, if bU u = hHyp u.1.1 then (1 : ℤ) else -1 : ℤ) : ℝ) ^ 2 :=
              Finset.sum_le_univ_sum_of_nonneg fun _ => sq_nonneg _
          _ = (U.card : ℝ) * (2 : ℝ) ^ U.card := by
              simpa [Fintype.card_coe] using sum_sq_rademacher (fun u : ↥U => hHyp u.1.1)
      have hU_le_W : (U.card : ℝ) ≤ (W.card : ℝ) := by
        have : U.card ≤ W.card := by omega
        exact_mod_cast this
      have hWc : (W.card : ℝ) = (2 : ℝ) ^ n := by exact_mod_cast hW_card
      have hWposR : (0 : ℝ) < W.card := by exact_mod_cast hW_pos
      have hsq_pos : 0 < ((1 / 2 - ε₀) * (W.card : ℝ)) ^ 2 := by positivity
      have hlt : (U.card : ℝ) * (2 : ℝ) ^ U.card <
          ((1 - δ₀) * (2 : ℝ) ^ U.card) * ((1 / 2 - ε₀) * (W.card : ℝ)) ^ 2 := by
        have hmul : (W.card : ℝ) < (1 - δ₀) * ((1 / 2 - ε₀) * (W.card : ℝ)) ^ 2 := by
          rw [mul_pow, ← mul_assoc]
          have : 1 * (W.card : ℝ) <
              ((1 - δ₀) * ((1 / 2 - ε₀) ^ 2 * (W.card : ℝ))) * (W.card : ℝ) :=
            mul_lt_mul_of_pos_right (hWc.symm ▸ hvar_small) hWposR
          linarith
        have hstep : (U.card : ℝ) < (1 - δ₀) * ((1 / 2 - ε₀) * (W.card : ℝ)) ^ 2 :=
          hU_le_W.trans_lt hmul
        have := mul_lt_mul_of_pos_right hstep (by positivity : (0 : ℝ) < (2 : ℝ) ^ U.card)
        linarith
      exact lt_of_mul_lt_mul_right (hmarkov.trans_lt hlt) hsq_pos.le
    -- Sum `good` over all `bS : seen → Bool` and take the complement inside `W → Bool`.
    have hgood_tot : ((Finset.univ.filter fun b : ↥W → Bool => isBad xs b = false).card : ℝ) <
        (1 - δ₀) * (2 : ℝ) ^ W.card := by
      have hcard_eq : (Finset.univ.filter fun b : ↥W → Bool => isBad xs b = false).card =
          ∑ bS : ↥seen → Bool,
            (Finset.univ.filter fun bU : ↥U → Bool =>
              isBad xs (splitEquiv.symm (bS, bU)) = false).card := by
        rw [Finset.card_filter, ← Equiv.sum_comp splitEquiv.symm, Fintype.sum_prod_type]
        simp_rw [Finset.card_filter]
      rw [hcard_eq, Nat.cast_sum]
      calc ∑ bS : ↥seen → Bool,
            ((Finset.univ.filter fun bU : ↥U → Bool =>
              isBad xs (splitEquiv.symm (bS, bU)) = false).card : ℝ)
          < ∑ _bS : ↥seen → Bool, (1 - δ₀) * (2 : ℝ) ^ U.card :=
            Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun bS _ => hper bS
        _ = (2 : ℝ) ^ seen.card * ((1 - δ₀) * (2 : ℝ) ^ U.card) := by
            simp
        _ = (1 - δ₀) * (2 : ℝ) ^ W.card := by
            rw [← hU_card, pow_add]; ring
    have hcomp : (Finset.univ.filter fun b : ↥W → Bool => isBad xs b = true).card +
        (Finset.univ.filter fun b : ↥W → Bool => isBad xs b = false).card = 2 ^ W.card := by
      rw [← Finset.card_union_of_disjoint (Finset.disjoint_filter.mpr fun _ _ h1 h2 => by
        rw [h1] at h2; exact Bool.false_ne_true h2.symm)]
      have hun : (Finset.univ.filter fun b : ↥W → Bool => isBad xs b = true) ∪
          (Finset.univ.filter fun b : ↥W → Bool => isBad xs b = false) = Finset.univ := by
        ext b; cases isBad xs b <;> simp
      rw [hun, Finset.card_univ, Fintype.card_pi]
      simp
    have hcompR : ((Finset.univ.filter fun b : ↥W → Bool => isBad xs b = true).card : ℝ) +
        ((Finset.univ.filter fun b : ↥W → Bool => isBad xs b = false).card : ℝ) =
        (2 : ℝ) ^ W.card := by exact_mod_cast hcomp
    linarith
  -- Double count over `(xs, b)` to find a concept `bStar` with failure probability `> δ₀`.
  have hdouble : δ₀ * (2 : ℝ) ^ W.card * (W.card : ℝ) ^ m n <
      ∑ b : ↥W → Bool,
        ((Finset.univ.filter fun xs : Fin (m n) → ↥W => isBad xs b = true).card : ℝ) := by
    have hswap : (∑ b : ↥W → Bool,
        ((Finset.univ.filter fun xs : Fin (m n) → ↥W => isBad xs b = true).card : ℝ)) =
        ∑ xs : Fin (m n) → ↥W,
          ((Finset.univ.filter fun b : ↥W → Bool => isBad xs b = true).card : ℝ) := by
      simp only [Finset.card_filter, Nat.cast_sum]
      exact Finset.sum_comm
    rw [hswap]
    have hne_xs : (Finset.univ : Finset (Fin (m n) → ↥W)).Nonempty :=
      ⟨fun _ => ⟨hW_ne.choose, hW_ne.choose_spec⟩, Finset.mem_univ _⟩
    calc δ₀ * (2 : ℝ) ^ W.card * (W.card : ℝ) ^ m n
        = ∑ _xs : Fin (m n) → ↥W, δ₀ * (2 : ℝ) ^ W.card := by
          simp [Fintype.card_coe, mul_comm]
      _ < ∑ xs : Fin (m n) → ↥W,
            ((Finset.univ.filter fun b : ↥W → Bool => isBad xs b = true).card : ℝ) :=
          Finset.sum_lt_sum_of_nonempty hne_xs fun xs _ => hpointwise xs
  obtain ⟨bStar, -, hbStar⟩ : ∃ bStar ∈ (Finset.univ : Finset (↥W → Bool)),
      δ₀ * (W.card : ℝ) ^ m n <
        ((Finset.univ.filter fun xs : Fin (m n) → ↥W => isBad xs bStar = true).card : ℝ) := by
    by_contra hall
    push Not at hall
    have hle : (∑ b : ↥W → Bool,
        ((Finset.univ.filter fun xs : Fin (m n) → ↥W => isBad xs b = true).card : ℝ)) ≤
        δ₀ * (2 : ℝ) ^ W.card * (W.card : ℝ) ^ m n := by
      calc ∑ b : ↥W → Bool,
            ((Finset.univ.filter fun xs : Fin (m n) → ↥W => isBad xs b = true).card : ℝ)
          ≤ ∑ _b : ↥W → Bool, δ₀ * (W.card : ℝ) ^ m n :=
            Finset.sum_le_sum fun b hb => hall b hb
        _ = δ₀ * (2 : ℝ) ^ W.card * (W.card : ℝ) ^ m n := by
            simp; ring
    linarith
  -- Compute the product measure of bad tuples for `cOf bStar` and contradict `hpac`.
  let Good : Finset (Fin (m n) → ↥W) :=
    Finset.univ.filter fun xs => isBad xs bStar = true
  let emb : (Fin (m n) → ↥W) → (Fin (m n) → List Bool) := fun xs i => (xs i).1
  have hemb_inj : Function.Injective emb :=
    fun _ _ h => funext fun i => Subtype.ext (congrFun h i)
  have hpi_single : ∀ xs : Fin (m n) → ↥W,
      Measure.pi (fun _ : Fin (m n) => D) {emb xs} = ((W.card : ℝ≥0∞) ^ m n)⁻¹ := by
    intro xs
    have hset : ({emb xs} : Set (Fin (m n) → List Bool)) = Set.univ.pi fun i => {(xs i).1} := by
      ext ys; simp [emb, funext_iff]
    rw [hset, Measure.pi_pi]
    have hfac : ∀ i : Fin (m n), D {(xs i).1} = (W.card : ℝ≥0∞)⁻¹ := fun i => by
      change μ.toMeasure {(xs i).1} = _
      rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
      simp [μ, Cslib.Probability.PMF.uniformOfFinset_apply, (xs i).2]
    simp [hfac, ENNReal.inv_pow]
  have hsub_ev : ((Good.image emb : Finset (Fin (m n) → List Bool)) :
      Set (Fin (m n) → List Bool)) ⊆
      {xs : Fin (m n) → List Bool |
        ENNReal.ofReal ε₀ <
          D {x | eval n (learn n (List.ofFn fun i => (xs i, cOf bStar (xs i)))) x ≠
            cOf bStar x}} := by
    intro ys hys
    obtain ⟨xs, hxs, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hys)
    have hbad : ENNReal.ofReal ε₀ <
        D {x | eval n (learn n (List.ofFn fun i => ((xs i).1, bStar (xs i)))) x ≠
          cOf bStar x} := by simpa [Good, isBad] using hxs
    have hS : (List.ofFn fun i => (emb xs i, cOf bStar (emb xs i))) =
        List.ofFn fun i => ((xs i).1, bStar (xs i)) := by
      refine List.ext_getElem (by simp) fun i hi1 hi2 => ?_
      simp [emb, cOf]
    simpa [Set.mem_ofPred_eq, hS] using hbad
  have hmeas_img :
      Measure.pi (fun _ : Fin (m n) => D) (Good.image emb : Set (Fin (m n) → List Bool)) =
        (Good.card : ℝ≥0∞) * ((W.card : ℝ≥0∞) ^ m n)⁻¹ := by
    have hunion : ((Good.image emb : Finset (Fin (m n) → List Bool)) :
        Set (Fin (m n) → List Bool)) = ⋃ xs ∈ Good, ({emb xs} : Set (Fin (m n) → List Bool)) := by
      ext ys; simp [eq_comm]
    rw [hunion, measure_biUnion_finset
      (fun a _ b _ hab => Set.disjoint_singleton.mpr (hemb_inj.ne hab))
      (fun _ _ => measurableSet_singleton _)]
    simp [hpi_single]
  have hle_pac := (measure_mono hsub_ev).trans (hpac n hn1 D hD_supp (cOf bStar) trivial)
  rw [hmeas_img] at hle_pac
  have hpow_ne0 : ((W.card : ℝ≥0∞) ^ m n) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr hW_pos.ne')
  have hpow_top : ((W.card : ℝ≥0∞) ^ m n) ≠ ⊤ := ENNReal.pow_ne_top (ENNReal.natCast_ne_top _)
  rw [← div_eq_mul_inv, ENNReal.div_le_iff_le_mul (Or.inl hpow_ne0) (Or.inl hpow_top)] at hle_pac
  have htoR := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hpow_top) hle_pac
  rw [ENNReal.toReal_natCast, ENNReal.toReal_mul, ENNReal.toReal_ofReal hδ0.le,
    ENNReal.toReal_pow, ENNReal.toReal_natCast] at htoR
  linarith

/-- **Cryptographic Hardness of Weakly PAC-Learning Constant-Depth Threshold Circuits
.**
There exist a constant depth `L ≥ 1` and a polynomial size bound `p(n) = C_s * (n + 1)^k_s`
(`C_s ≥ 1`) such that the family of nonempty `n`-input linear-threshold circuits of depth at most
`L` and size at most `p(n)` is not weakly PAC learnable in deterministic polynomial time.
-/
def TC0LearningHardnessConjecture : Prop :=
  ∃ (L C_s k_s : ℕ), 1 ≤ L ∧ 1 ≤ C_s ∧
    ¬ IsWeaklyPolyTimePACLearnable (fun n =>
      {f | ∃ C : ThresholdCircuit n,
        1 ≤ C.numGates ∧ C.depth ≤ L ∧ C.numGates ≤ C_s * (n + 1) ^ k_s ∧ f = C.eval})

/-- Unfolding characterization of `TC0LearningHardnessConjecture`. -/
theorem tc0LearningHardnessConjecture_iff :
    TC0LearningHardnessConjecture ↔
      ∃ (L C_s k_s : ℕ), 1 ≤ L ∧ 1 ≤ C_s ∧
        ¬ IsWeaklyPolyTimePACLearnable (fun n =>
          {f | ∃ C : ThresholdCircuit n,
            1 ≤ C.numGates ∧ C.depth ≤ L ∧ C.numGates ≤ C_s * (n + 1) ^ k_s ∧ f = C.eval}) :=
  Iff.rfl

/-- Conditional hardness transfer: any property `P` whose truth yields a deterministic
polynomial-time weak PAC learner for every constant-depth, polynomial-size family of nonempty
linear-threshold circuits is refuted under `TC0LearningHardnessConjecture`. -/
theorem TC0LearningHardnessConjecture.not_of_polyTime_reduction {P : Prop}
    (hHard : TC0LearningHardnessConjecture)
    (hred : ∀ {L C_s k_s : ℕ}, 1 ≤ L → 1 ≤ C_s → P →
      IsWeaklyPolyTimePACLearnable (fun n =>
        {f | ∃ C : ThresholdCircuit n,
          1 ≤ C.numGates ∧ C.depth ≤ L ∧ C.numGates ≤ C_s * (n + 1) ^ k_s ∧ f = C.eval})) :
    ¬ P := by
  obtain ⟨L, C_s, k_s, hL, hCs, hnot⟩ := hHard
  exact fun hP => hnot (hred hL hCs hP)

-- Concrete sanity check: a single-gate halfspace circuit computes `x_0` on `[x_0, true]`.
example : ∃ C : ThresholdCircuit 2,
    C.numGates = 1 ∧ C.depth = 1 ∧
      ∀ b₀ : Bool, C.eval [b₀, true] = b₀ := by
  let C : ThresholdCircuit 2 :=
    { numGates := 1
      depth := 1
      layer := fun _ => 0
      layer_lt_depth := fun _ => Nat.zero_lt_one
      inWeight := fun _ => ![2, -1]
      gateWeight := fun _ _ => 0
      gateWeight_eq_zero_of_le := fun _ _ _ => rfl
      outGate := ⟨0, Nat.zero_lt_one⟩ }
  refine ⟨C, rfl, rfl, fun b₀ => ?_⟩
  change C.gateVal (fun k : Fin 2 => [b₀, true].getD k.1 false) ⟨0, Nat.zero_lt_one⟩ = b₀
  rw [ThresholdCircuit.gateVal_eq]
  simp only [Fin.sum_univ_two, Fin.sum_univ_one, C]
  cases b₀ <;> simp

end CslibFrontier.MachineLearning.PACLearning
