/-
Copyright (c) 2026 The PanMath contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The PanMath contributors
-/
module

public import CslibFrontier.Computability.Complexity.Classes.P
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Pair
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Rat
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Unary
public import CslibFrontier.Foundations.Probability.Gaussian.Multivariate
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Basic.Real.Basic
public import CslibFrontier.Foundations.Probability.Gaussian.RationalProjection
public import CslibFrontier.Foundations.Probability.Gaussian.RationalQuadrature

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Rat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Frame.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.IntBinary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeLoops
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeNatFrontends
import CslibFrontier.Foundations.Probability.Gaussian.ConvexCap
import CslibFrontier.Foundations.Probability.Gaussian.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Size
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Deterministic Gaussian Halfspace-Conjunction Derandomisation

This module proves deterministic polynomial-time derandomisation for systems of conjunctions of
at most `d` rational halfspaces in `ℝ^n` under the standard Gaussian measure `N(0, I_n)`:
given `m` conjunctions of `d` rational halfspaces `⟪a_{ij}, x⟫ > b_{ij}` and a unary inverse-error
parameter `q ≥ 1`, a deterministic polynomial-time algorithm produces `x* ∈ ℚ^n` satisfying at
least `E_x[count(x)] - 1 / q` conjunctions.

## Main definitions

* `CslibFrontier.Foundations.Probability.Gaussian.encDerandGaussianInput`: unary-`n`, unary-`q`
  input encoding of
  `(n, clauses, q)`.
* `CslibFrontier.Foundations.Probability.Gaussian.gaussianConjunctionExpect`,
  `CslibFrontier.Foundations.Probability.Gaussian.gaussianConjunctionCount`: Gaussian expected and
  deterministic satisfied
  conjunction counts.
* `CslibFrontier.Foundations.Probability.Gaussian.stepOneCoord`,
  `CslibFrontier.Foundations.Probability.Gaussian.updateClausesByInts`,
  `CslibFrontier.Foundations.Probability.Gaussian.approxClauseScore`,
  `CslibFrontier.Foundations.Probability.Gaussian.derandGaussianAlg`: method of
  conditional expectations over a uniform rational grid backed by `approxClauseProb`.

## Main results

* `CslibFrontier.Foundations.Probability.Gaussian.gaussianConjunctionExpect_succ`: coordinate-`0`
  Fubini decomposition of
  `gaussianConjunctionExpect`.
* `CslibFrontier.Foundations.Probability.Gaussian.derandGaussian_polyTime`: for every fixed constant
  `d`, there is a
  deterministic polynomial-time algorithm outputting `x* ∈ ℚ^n` with
  `gaussianConjunctionExpect n clauses - 1 / q ≤ gaussianConjunctionCount n clauses x*`.
-/

public section

open MeasureTheory ProbabilityTheory Real Set Finset BigOperators Turing.MultiTapeTM
open scoped NNReal ENNReal RealInnerProductSpace

namespace CslibFrontier.Foundations.Probability.Gaussian

/-! ### Problem definitions and basic semantic lemmas -/

/-- Input encoding for Gaussian halfspace-conjunction derandomisation `(n, clauses, q)` with
unary dimension `n`, list of rational halfspace conjunctions `clauses`, and unary inverse-error
parameter `q`. -/
@[expose] def encDerandGaussianInput :
    (ℕ × List (List (List ℚ × ℚ)) × ℕ) ↪ List Bool :=
  encPair encUnary (encPair (encList (encList (encPair (encList encRat) encRat))) encUnary)

/-- Expected number of satisfied rational halfspace conjunctions under `x ~ N(0, I_n)`. -/
@[expose] noncomputable def gaussianConjunctionExpect (n : ℕ)
    (clauses : List (List (List ℚ × ℚ))) : ℝ :=
  (clauses.map fun cl =>
    (stdGaussian (EuclideanSpace ℝ (Fin n))).real
      {x : EuclideanSpace ℝ (Fin n) |
        ∀ p ∈ cl, (p.2 : ℝ) < ⟪ratVecToEuclidean n p.1, x⟫}).sum

@[simp]
theorem gaussianConjunctionExpect_nil (n : ℕ) : gaussianConjunctionExpect n [] = 0 := rfl

@[simp]
theorem gaussianConjunctionExpect_cons (n : ℕ) (cl : List (List ℚ × ℚ))
    (clauses : List (List (List ℚ × ℚ))) :
    gaussianConjunctionExpect n (cl :: clauses) =
      (stdGaussian (EuclideanSpace ℝ (Fin n))).real
        {x : EuclideanSpace ℝ (Fin n) |
          ∀ p ∈ cl, (p.2 : ℝ) < ⟪ratVecToEuclidean n p.1, x⟫} +
        gaussianConjunctionExpect n clauses := rfl

theorem gaussianConjunctionExpect_nonneg (n : ℕ) (clauses : List (List (List ℚ × ℚ))) :
    0 ≤ gaussianConjunctionExpect n clauses := by
  induction clauses with
  | nil => simp
  | cons cl rest ih => exact add_nonneg measureReal_nonneg ih

theorem gaussianConjunctionExpect_le_length (n : ℕ) (clauses : List (List (List ℚ × ℚ))) :
    gaussianConjunctionExpect n clauses ≤ (clauses.length : ℝ) := by
  induction clauses with
  | nil => simp
  | cons cl rest ih =>
    rw [gaussianConjunctionExpect_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    linarith [measureReal_le_one (μ := stdGaussian (EuclideanSpace ℝ (Fin n)))
      (s := {x | ∀ p ∈ cl, (p.2 : ℝ) < ⟪ratVecToEuclidean n p.1, x⟫})]

/-- Deterministic number of satisfied rational halfspace conjunctions at `xStar : List ℚ`. -/
@[expose] noncomputable def gaussianConjunctionCount (n : ℕ)
    (clauses : List (List (List ℚ × ℚ))) (xStar : List ℚ) : ℝ :=
  ((clauses.countP fun cl =>
    decide (∀ p ∈ cl, (p.2 : ℝ) < ⟪ratVecToEuclidean n p.1, ratVecToEuclidean n xStar⟫) : ℕ) : ℝ)

@[simp]
theorem gaussianConjunctionCount_nil (n : ℕ) (xStar : List ℚ) :
    gaussianConjunctionCount n [] xStar = 0 := by
  simp [gaussianConjunctionCount]

@[simp]
theorem gaussianConjunctionCount_cons (n : ℕ) (cl : List (List ℚ × ℚ))
    (clauses : List (List (List ℚ × ℚ))) (xStar : List ℚ) :
    gaussianConjunctionCount n (cl :: clauses) xStar =
      (if ∀ p ∈ cl, (p.2 : ℝ) < ⟪ratVecToEuclidean n p.1, ratVecToEuclidean n xStar⟫
        then (1 : ℝ) else 0) +
        gaussianConjunctionCount n clauses xStar := by
  simp only [gaussianConjunctionCount, List.countP_cons, decide_eq_true_eq]
  split_ifs
  · simp only [Nat.cast_add, Nat.cast_one]; ring
  · simp only [add_zero, zero_add]

/-! ### Single-coordinate and prefix conditioning updates -/

/-- Fix coordinate `0` of every halfspace `(a, b)` in `clauses` to the rational value `u`. -/
@[expose] def stepOneCoord (u : ℚ) (clauses : List (List (List ℚ × ℚ))) :
    List (List (List ℚ × ℚ)) :=
  clauses.map fun cl => cl.map fun p => (p.1.tail, p.2 - p.1.headD 0 * u)

@[simp]
theorem stepOneCoord_length (u : ℚ) (clauses : List (List (List ℚ × ℚ))) :
    (stepOneCoord u clauses).length = clauses.length := by
  simp [stepOneCoord]

/-- Fix the first `ks.length` coordinates of every halfspace in `clauses` to `k / H` for `k ∈ ks`,
dropping the prefix and subtracting its rational dot product from each threshold. -/
@[expose] def updateClausesByInts (H : ℕ) (ks : List ℤ) (clauses : List (List (List ℚ × ℚ))) :
    List (List (List ℚ × ℚ)) :=
  let uList := ks.map fun k => Rat.divInt k (H : ℤ)
  clauses.map fun cl => cl.map fun p => (p.1.drop ks.length, p.2 - ratDot p.1 uList)

@[simp]
theorem updateClausesByInts_nil (H : ℕ) (clauses : List (List (List ℚ × ℚ))) :
    updateClausesByInts H [] clauses = clauses := by
  simp [updateClausesByInts]

@[simp]
theorem updateClausesByInts_length (H : ℕ) (ks : List ℤ) (clauses : List (List (List ℚ × ℚ))) :
    (updateClausesByInts H ks clauses).length = clauses.length := by
  simp [updateClausesByInts]

private theorem ratDot_append_singleton {a uList : List ℚ} {u : ℚ} (h : uList.length < a.length) :
    ratDot a (uList ++ [u]) = ratDot a uList + a.getD uList.length 0 * u := by
  induction uList generalizing a with
  | nil =>
    cases a with
    | nil => simp at h
    | cons x xs => simp
  | cons y ys ih =>
    cases a with
    | nil => simp at h
    | cons x xs =>
      simp only [List.length_cons, Nat.succ_lt_succ_iff] at h
      simp only [List.cons_append, ratDot_cons, ih h, List.length_cons, List.getD_cons_succ]
      ring

private theorem headD_drop_eq_getD (a : List ℚ) (t : ℕ) :
    (a.drop t).headD 0 = a.getD t 0 := by
  induction t generalizing a with
  | zero => cases a <;> simp
  | succ t ih =>
    cases a with
    | nil => simp
    | cons x xs => simp

private theorem tail_drop_eq_drop_succ (a : List ℚ) (t : ℕ) :
    (a.drop t).tail = a.drop (t + 1) := by
  induction t generalizing a with
  | zero => simp
  | succ t ih =>
    cases a with
    | nil => simp
    | cons x xs => simp [ih xs]

theorem updateClausesByInts_snoc {H : ℕ} {ks : List ℤ} {k : ℤ}
    {clauses : List (List (List ℚ × ℚ))}
    (hlen : ∀ cl ∈ clauses, ∀ p ∈ cl, ks.length < p.1.length) :
    updateClausesByInts H (ks ++ [k]) clauses =
      stepOneCoord (Rat.divInt k (H : ℤ)) (updateClausesByInts H ks clauses) := by
  simp only [updateClausesByInts, stepOneCoord, List.map_map, List.length_append,
    List.length_singleton]
  refine List.map_congr_left fun cl hcl => ?_
  simp only [Function.comp_def, List.map_map]
  refine List.map_congr_left fun p hp => ?_
  have hlt : (ks.map fun z => Rat.divInt z (H : ℤ)).length < p.1.length := by
    simpa using hlen cl hcl p hp
  rw [List.map_append, List.map_singleton, ratDot_append_singleton hlt, List.length_map,
    headD_drop_eq_getD, tail_drop_eq_drop_succ]
  exact Prod.ext rfl (by ring)

theorem gaussianConjunctionExpect_zero (clauses : List (List (List ℚ × ℚ))) :
    gaussianConjunctionExpect 0 clauses = gaussianConjunctionCount 0 clauses [] := by
  induction clauses with
  | nil => simp
  | cons cl rest ih =>
    rw [gaussianConjunctionExpect_cons, gaussianConjunctionCount_cons, ih]
    congr 1
    have hset : {x : EuclideanSpace ℝ (Fin 0) |
        ∀ p ∈ cl, (p.2 : ℝ) < ⟪ratVecToEuclidean 0 p.1, x⟫} =
        if ∀ p ∈ cl, (p.2 : ℝ) < ⟪ratVecToEuclidean 0 p.1, ratVecToEuclidean 0 []⟫
          then Set.univ else ∅ := by
      ext x
      have hx : x = ratVecToEuclidean 0 [] := Subsingleton.elim _ _
      rw [hx]
      split_ifs with h
      · simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]; exact h
      · simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]; exact h
    rw [hset]
    split_ifs <;> simp [Measure.real_def]

theorem gaussianConjunctionCount_zero_updateClausesByInts {n H : ℕ} {ks : List ℤ}
    {clauses : List (List (List ℚ × ℚ))} (hks : ks.length = n)
    (hlen : ∀ cl ∈ clauses, ∀ p ∈ cl, p.1.length = n) :
    gaussianConjunctionCount 0 (updateClausesByInts H ks clauses) [] =
      gaussianConjunctionCount n clauses (ks.map fun k => Rat.divInt k (H : ℤ)) := by
  set uList := ks.map fun k => Rat.divInt k (H : ℤ)
  have hu_len : uList.length = n := by simp [uList, hks]
  induction clauses with
  | nil => simp [updateClausesByInts]
  | cons cl rest ih =>
    have hrest := ih fun c hc => hlen c (List.mem_cons_of_mem _ hc)
    simp only [updateClausesByInts, List.map_cons] at hrest ⊢
    rw [gaussianConjunctionCount_cons, gaussianConjunctionCount_cons, hrest]
    congr 1
    have hiff : (∀ q ∈ cl.map (fun p => (p.1.drop ks.length, p.2 - ratDot p.1 uList)),
          (q.2 : ℝ) < ⟪ratVecToEuclidean 0 q.1, ratVecToEuclidean 0 []⟫) ↔
        (∀ p ∈ cl, (p.2 : ℝ) < ⟪ratVecToEuclidean n p.1, ratVecToEuclidean n uList⟫) := by
      simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
      refine forall₂_congr fun p hp => ?_
      have hp_len : p.1.length = n := hlen cl (List.mem_cons_self) p hp
      rw [ratVecToEuclidean_zero, inner_zero_left,
        inner_ratVecToEuclidean_eq_ratDot hp_len hu_len, Rat.cast_sub, sub_lt_zero]
    dsimp only [uList] at hiff ⊢
    split_ifs
    · rfl
    · rename_i h1 h2; exact absurd (hiff.mp h1) h2
    · rename_i h1 h2; exact absurd (hiff.mpr h2) h1
    · rfl

/-! ### Coordinate-0 Fubini identity -/

private theorem clauseProb_fubini (n : ℕ) (cl : List (List ℚ × ℚ)) :
    let f : ℝ → ℝ := fun u =>
      (stdGaussian (EuclideanSpace ℝ (Fin n))).real
        {y : EuclideanSpace ℝ (Fin n) |
          ∀ p ∈ cl, (p.2 : ℝ) - ((p.1.headD 0 : ℚ) : ℝ) * u <
            ⟪ratVecToEuclidean n p.1.tail, y⟫}
    Integrable f (gaussianReal 0 1) ∧
      (stdGaussian (EuclideanSpace ℝ (Fin (n + 1)))).real
        {x : EuclideanSpace ℝ (Fin (n + 1)) |
          ∀ p ∈ cl, (p.2 : ℝ) < ⟪ratVecToEuclidean (n + 1) p.1, x⟫} =
      ∫ u : ℝ, f u ∂(gaussianReal 0 1) := by
  intro f
  set μ₀ : Measure ℝ := gaussianReal 0 1
  set μn : Measure (Fin n → ℝ) := Measure.pi fun _ : Fin n => gaussianReal 0 1
  set S : Set (ℝ × (Fin n → ℝ)) :=
    {z | ∀ p ∈ cl, (p.2 : ℝ) <
      ((p.1.headD 0 : ℚ) : ℝ) * z.1 +
        ∑ j : Fin n, ((p.1.tail.getD j.1 0 : ℚ) : ℝ) * z.2 j}
  have hS : MeasurableSet S := by
    have hfin : S = ⋂ p ∈ cl.toFinset,
        {z : ℝ × (Fin n → ℝ) | (p.2 : ℝ) <
          ((p.1.headD 0 : ℚ) : ℝ) * z.1 +
            ∑ j : Fin n, ((p.1.tail.getD j.1 0 : ℚ) : ℝ) * z.2 j} := by
      ext z; simp [S]
    rw [hfin]
    exact Finset.measurableSet_biInter _ fun _ _ =>
      (isOpen_lt continuous_const (by fun_prop)).measurableSet
  have hf_eq : ∀ u : ℝ, f u = μn.real (Prod.mk u ⁻¹' S) := fun u => by
    have hmeas_u : MeasurableSet {y : EuclideanSpace ℝ (Fin n) |
        ∀ p ∈ cl, (p.2 : ℝ) - ((p.1.headD 0 : ℚ) : ℝ) * u <
          ⟪ratVecToEuclidean n p.1.tail, y⟫} := by
      have hfin : {y : EuclideanSpace ℝ (Fin n) |
          ∀ p ∈ cl, (p.2 : ℝ) - ((p.1.headD 0 : ℚ) : ℝ) * u <
            ⟪ratVecToEuclidean n p.1.tail, y⟫} =
          ⋂ p ∈ cl.toFinset,
            {y : EuclideanSpace ℝ (Fin n) |
              (p.2 : ℝ) - ((p.1.headD 0 : ℚ) : ℝ) * u <
                ⟪ratVecToEuclidean n p.1.tail, y⟫} := by ext y; simp
      rw [hfin]
      exact Finset.measurableSet_biInter _ fun p _ =>
        (isOpen_lt continuous_const (innerSL ℝ _).continuous).measurableSet
    have hset : {ω : Fin n → ℝ | WithLp.toLp 2 ω ∈ {y : EuclideanSpace ℝ (Fin n) |
        ∀ p ∈ cl, (p.2 : ℝ) - ((p.1.headD 0 : ℚ) : ℝ) * u <
          ⟪ratVecToEuclidean n p.1.tail, y⟫}} = Prod.mk u ⁻¹' S := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_preimage, S]
      refine forall₂_congr fun p _ => ?_
      have hinner : ⟪ratVecToEuclidean n p.1.tail, WithLp.toLp 2 ω⟫ =
          ∑ j : Fin n, ((p.1.tail.getD j.1 0 : ℚ) : ℝ) * ω j := by
        rw [PiLp.inner_apply]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [ratVecToEuclidean_apply, RCLike.inner_apply, conj_trivial]; ring
      rw [hinner]; constructor <;> intro h <;> linarith
    dsimp only [f]
    rw [← ProbabilityTheory.measureReal_pi_gaussianReal_eq hmeas_u, hset]
  have hf_meas : Measurable f := by
    have h1 : f = fun u => (μn (Prod.mk u ⁻¹' S)).toReal := funext fun u => by
      rw [hf_eq u, Measure.real_def]
    rw [h1]
    exact (measurable_measure_prodMk_left hS).ennreal_toReal
  have hf_int : Integrable f μ₀ := by
    refine Integrable.of_bound hf_meas.aestronglyMeasurable 1 (ae_of_all _ fun u => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
    exact measureReal_le_one
  refine ⟨hf_int, ?_⟩
  have hprod_eq : (stdGaussian (EuclideanSpace ℝ (Fin (n + 1)))).real
      {x : EuclideanSpace ℝ (Fin (n + 1)) |
        ∀ p ∈ cl, (p.2 : ℝ) < ⟪ratVecToEuclidean (n + 1) p.1, x⟫} =
      (μ₀.prod μn).real S := by
    have hmeas_E : MeasurableSet {x : EuclideanSpace ℝ (Fin (n + 1)) |
        ∀ p ∈ cl, (p.2 : ℝ) < ⟪ratVecToEuclidean (n + 1) p.1, x⟫} := by
      have hfin : {x : EuclideanSpace ℝ (Fin (n + 1)) |
          ∀ p ∈ cl, (p.2 : ℝ) < ⟪ratVecToEuclidean (n + 1) p.1, x⟫} =
          ⋂ p ∈ cl.toFinset,
            {x : EuclideanSpace ℝ (Fin (n + 1)) |
              (p.2 : ℝ) < ⟪ratVecToEuclidean (n + 1) p.1, x⟫} := by ext x; simp
      rw [hfin]
      exact Finset.measurableSet_biInter _ fun _ _ =>
        (isOpen_lt continuous_const (innerSL ℝ _).continuous).measurableSet
    rw [← ProbabilityTheory.measureReal_pi_gaussianReal_eq hmeas_E]
    have hmp := MeasureTheory.measurePreserving_piFinSuccAbove
      (fun _ : Fin (n + 1) => gaussianReal 0 1) 0
    have hpre : MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0 ⁻¹' S =
        {ω : Fin (n + 1) → ℝ | WithLp.toLp 2 ω ∈ {x : EuclideanSpace ℝ (Fin (n + 1)) |
          ∀ p ∈ cl, (p.2 : ℝ) < ⟪ratVecToEuclidean (n + 1) p.1, x⟫}} := by
      ext ω
      have h1 : (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0 ω).1 = ω 0 := rfl
      have h2 : ∀ j : Fin n,
          (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0 ω).2 j = ω j.succ :=
        fun _ => rfl
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, S, h1, h2]
      refine forall₂_congr fun p _ => ?_
      have hinner : ⟪ratVecToEuclidean (n + 1) p.1, WithLp.toLp 2 ω⟫ =
          ((p.1.headD 0 : ℚ) : ℝ) * ω 0 +
            ∑ j : Fin n, ((p.1.tail.getD j.1 0 : ℚ) : ℝ) * ω j.succ := by
        rw [PiLp.inner_apply, Fin.sum_univ_succ]
        congr 1
        · have h0 : p.1.getD 0 0 = p.1.headD 0 := by cases p.1 <;> rfl
          simp only [ratVecToEuclidean_apply, Fin.val_zero, h0, RCLike.inner_apply, conj_trivial]
          ring
        · refine Finset.sum_congr rfl fun j _ => ?_
          have hj : p.1.getD (j.1 + 1) 0 = p.1.tail.getD j.1 0 := by cases p.1 <;> simp
          simp only [ratVecToEuclidean_apply, Fin.val_succ, hj, RCLike.inner_apply, conj_trivial]
          ring
      rw [hinner]
    rw [← hpre, hmp.measureReal_preimage hS.nullMeasurableSet]
  rw [hprod_eq, Measure.real_def, MeasureTheory.Measure.prod_apply hS]
  have hlin : ∫ u : ℝ, f u ∂μ₀ = (∫⁻ u : ℝ, ENNReal.ofReal (f u) ∂μ₀).toReal :=
    MeasureTheory.integral_eq_lintegral_of_nonneg_ae
      (ae_of_all _ fun _ => measureReal_nonneg) hf_meas.aestronglyMeasurable
  rw [hlin]
  congr 1
  refine lintegral_congr fun u => ?_
  rw [hf_eq u, Measure.real_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]

theorem gaussianConjunctionExpect_succ (n : ℕ) (clauses : List (List (List ℚ × ℚ))) :
    gaussianConjunctionExpect (n + 1) clauses =
      ∫ u : ℝ, (clauses.map fun cl =>
        (stdGaussian (EuclideanSpace ℝ (Fin n))).real
          {y : EuclideanSpace ℝ (Fin n) |
            ∀ p ∈ cl, (p.2 : ℝ) - ((p.1.headD 0 : ℚ) : ℝ) * u <
              ⟪ratVecToEuclidean n p.1.tail, y⟫}).sum ∂(gaussianReal 0 1) := by
  induction clauses with
  | nil => simp
  | cons cl rest ih =>
    rw [gaussianConjunctionExpect_cons, ih]
    obtain ⟨hf_int, hf_eq⟩ := clauseProb_fubini n cl
    have hrest_int : Integrable (fun u : ℝ =>
        (rest.map fun c =>
          (stdGaussian (EuclideanSpace ℝ (Fin n))).real
            {y : EuclideanSpace ℝ (Fin n) |
              ∀ p ∈ c, (p.2 : ℝ) - ((p.1.headD 0 : ℚ) : ℝ) * u <
                ⟪ratVecToEuclidean n p.1.tail, y⟫}).sum) (gaussianReal 0 1) := by
      clear hf_int hf_eq ih
      induction rest with
      | nil => simp
      | cons c cs ihc =>
        have hadd := (clauseProb_fubini n c).1.add ihc
        exact hadd.congr (ae_of_all _ fun u => by simp)
    rw [hf_eq, ← integral_add hf_int hrest_int]
    rfl

/-! ### One-step uniform-grid variation bound -/

/-- Bad interval around `b / a0` for a sharp halfspace `(a0 :: v, b)`. -/
private noncomputable def sharpBadInterval (invEta : ℕ) (p : List ℚ × ℚ) : Set ℝ :=
  let a0 := p.1.headD 0
  let v := p.1.tail
  if a0 ≠ 0 ∧ ratDot v v ≤ (1 / (invEta : ℚ)) ^ 4 * a0 ^ 2 then
    Icc ((p.2 : ℝ) / (a0 : ℝ) - 2 / (invEta : ℝ)) ((p.2 : ℝ) / (a0 : ℝ) + 2 / (invEta : ℝ))
  else ∅

private theorem measurableSet_sharpBadInterval (invEta : ℕ) (p : List ℚ × ℚ) :
    MeasurableSet (sharpBadInterval invEta p) := by
  unfold sharpBadInterval; dsimp only
  split_ifs
  · exact measurableSet_Icc
  · exact MeasurableSet.empty

private theorem gaussianReal_sharpBadInterval_le {invEta : ℕ} (hEta : 1 ≤ invEta)
    (p : List ℚ × ℚ) :
    (gaussianReal 0 1).real (sharpBadInterval invEta p) ≤ 4 / (invEta : ℝ) := by
  unfold sharpBadInterval; dsimp only
  split_ifs
  · have hpos : (0 : ℝ) < (invEta : ℝ) := Nat.cast_pos.mpr hEta
    rw [Measure.real_def]
    have hle := ProbabilityTheory.gaussianReal_le_ofReal_mul_volume 0
      (v := (1 : ℝ≥0)) one_ne_zero
      (Icc ((p.2 : ℝ) / (p.1.headD 0 : ℝ) - 2 / (invEta : ℝ))
        ((p.2 : ℝ) / (p.1.headD 0 : ℝ) + 2 / (invEta : ℝ)))
    have hvol : volume (Icc ((p.2 : ℝ) / (p.1.headD 0 : ℝ) - 2 / (invEta : ℝ))
        ((p.2 : ℝ) / (p.1.headD 0 : ℝ) + 2 / (invEta : ℝ))) =
        ENNReal.ofReal (4 / (invEta : ℝ)) := by
      rw [Real.volume_Icc]; congr 1; ring
    rw [hvol, ← ENNReal.ofReal_mul (by positivity)] at hle
    simp only [NNReal.coe_one, mul_one] at hle
    refine (ENNReal.toReal_le_of_le_ofReal (by positivity) hle).trans ?_
    have h2pi : (1 : ℝ) ≤ Real.sqrt (2 * Real.pi) := by
      simpa using Real.sqrt_le_sqrt (by linarith [Real.pi_gt_three] : (1 : ℝ) ≤ 2 * Real.pi)
    have hinv : (Real.sqrt (2 * Real.pi))⁻¹ ≤ 1 := by
      rw [inv_le_one_iff₀]; exact Or.inr h2pi
    calc (Real.sqrt (2 * Real.pi))⁻¹ * (4 / (invEta : ℝ))
        ≤ 1 * (4 / (invEta : ℝ)) :=
          mul_le_mul_of_nonneg_right (by simpa using hinv) (by positivity)
      _ = 4 / (invEta : ℝ) := one_mul _
  · simp only [Measure.real_def, measure_empty, ENNReal.toReal_zero]; positivity

private theorem halfspace_step_prob_diff_le {nRem invEta H : ℕ}
    (hEta : 2 ≤ invEta) (hH : invEta ≤ H) (p : List ℚ × ℚ) (hp_len : p.1.length = nRem + 1)
    {u uStar : ℝ} (hdist : |u - uStar| ≤ 1 / (H : ℝ)) (hu : u ∉ sharpBadInterval invEta p) :
    (stdGaussian (EuclideanSpace ℝ (Fin nRem))).real
        ({y : EuclideanSpace ℝ (Fin nRem) |
          (p.2 : ℝ) - ((p.1.headD 0 : ℚ) : ℝ) * u < ⟪ratVecToEuclidean nRem p.1.tail, y⟫} \
        {y : EuclideanSpace ℝ (Fin nRem) |
          (p.2 : ℝ) - ((p.1.headD 0 : ℚ) : ℝ) * uStar < ⟪ratVecToEuclidean nRem p.1.tail, y⟫}) ≤
      1 / (invEta : ℝ) + (invEta : ℝ) ^ 2 / (H : ℝ) := by
  set a0 : ℚ := p.1.headD 0
  set v : List ℚ := p.1.tail
  set vVec : EuclideanSpace ℝ (Fin nRem) := ratVecToEuclidean nRem v
  have hv_len : v.length = nRem := by simp [v, hp_len]
  have hEta_pos : (0 : ℝ) < (invEta : ℝ) := Nat.cast_pos.mpr (by omega)
  have hH_pos : (0 : ℝ) < (H : ℝ) := Nat.cast_pos.mpr (by omega)
  have hH_ge : (invEta : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH
  by_cases ha0 : a0 = 0
  · change (stdGaussian (EuclideanSpace ℝ (Fin nRem))).real
      ({y | (p.2 : ℝ) - (a0 : ℝ) * u < ⟪vVec, y⟫} \
        {y | (p.2 : ℝ) - (a0 : ℝ) * uStar < ⟪vVec, y⟫}) ≤ _
    simp only [ha0, Rat.cast_zero, zero_mul, sub_zero, sdiff_self, measureReal_empty]
    positivity
  · have ha0_r : (a0 : ℝ) ≠ 0 := by exact_mod_cast ha0
    have ha0_abs_pos : 0 < |(a0 : ℝ)| := abs_pos.mpr ha0_r
    by_cases hsharp : ratDot v v ≤ (1 / (invEta : ℚ)) ^ 4 * a0 ^ 2
    · -- Sharp halfspace: `u ∉ sharpBadInterval`, so `|p.2 - a0 * u| > 2 * |a0| / invEta`.
      have hu_out : 2 / (invEta : ℝ) < |u - (p.2 : ℝ) / (a0 : ℝ)| := by
        simp only [sharpBadInterval, a0, v, ha0, ne_eq, not_false_eq_true, hsharp, and_self,
          ↓reduceIte, Set.mem_Icc, not_and_or, not_le] at hu
        rw [lt_abs]
        rcases hu with hlt | hgt
        · exact Or.inr (by linarith)
        · exact Or.inl (by linarith)
      have hsep_u : 2 * |(a0 : ℝ)| / (invEta : ℝ) < |(p.2 : ℝ) - (a0 : ℝ) * u| := by
        have hEq : |(p.2 : ℝ) - (a0 : ℝ) * u| = |(a0 : ℝ)| * |u - (p.2 : ℝ) / (a0 : ℝ)| := by
          rw [← abs_mul, show (a0 : ℝ) * (u - (p.2 : ℝ) / (a0 : ℝ)) =
            -((p.2 : ℝ) - (a0 : ℝ) * u) by field_simp [ha0_r]; ring, abs_neg]
        rw [hEq, show 2 * |(a0 : ℝ)| / (invEta : ℝ) = |(a0 : ℝ)| * (2 / (invEta : ℝ)) by ring]
        exact mul_lt_mul_of_pos_left hu_out ha0_abs_pos
      have hstep_le : |(a0 : ℝ)| * |u - uStar| ≤ |(a0 : ℝ)| / (invEta : ℝ) := by
        calc |(a0 : ℝ)| * |u - uStar| ≤ |(a0 : ℝ)| * (1 / (H : ℝ)) :=
              mul_le_mul_of_nonneg_left hdist ha0_abs_pos.le
          _ ≤ |(a0 : ℝ)| * (1 / (invEta : ℝ)) :=
              mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le hEta_pos hH_ge) ha0_abs_pos.le
          _ = |(a0 : ℝ)| / (invEta : ℝ) := by ring
      have hsub_sub : {y : EuclideanSpace ℝ (Fin nRem) |
            (p.2 : ℝ) - (a0 : ℝ) * u < ⟪vVec, y⟫} \
          {y : EuclideanSpace ℝ (Fin nRem) | (p.2 : ℝ) - (a0 : ℝ) * uStar < ⟪vVec, y⟫} ⊆
          {y : EuclideanSpace ℝ (Fin nRem) | |(a0 : ℝ)| / (invEta : ℝ) ≤ |⟪vVec, y⟫|} := by
        intro y hy
        simp only [Set.mem_sdiff, Set.mem_ofPred_eq, not_lt] at hy ⊢
        rcases le_or_gt 0 ((p.2 : ℝ) - (a0 : ℝ) * u) with hnn | hneg
        · rw [abs_of_nonneg hnn] at hsep_u
          have h1 : |(a0 : ℝ)| / (invEta : ℝ) < ⟪vVec, y⟫ := by
            have hpos : (0 : ℝ) < |(a0 : ℝ)| / (invEta : ℝ) := by positivity
            have hlt2 : 2 * |(a0 : ℝ)| / (invEta : ℝ) < ⟪vVec, y⟫ := lt_trans hsep_u hy.1
            have : 2 * |(a0 : ℝ)| / (invEta : ℝ) = 2 * (|(a0 : ℝ)| / (invEta : ℝ)) := by ring
            linarith
          exact h1.le.trans (le_abs_self _)
        · rw [abs_of_neg hneg] at hsep_u
          have hdiff : |((p.2 : ℝ) - (a0 : ℝ) * uStar) - ((p.2 : ℝ) - (a0 : ℝ) * u)| =
              |(a0 : ℝ)| * |u - uStar| := by
            rw [← abs_mul]; congr 1; ring
          have hupper : (p.2 : ℝ) - (a0 : ℝ) * uStar ≤ -(|(a0 : ℝ)| / (invEta : ℝ)) := by
            have hle := (abs_le.mp (hdiff.symm ▸ hstep_le)).2
            have : 2 * |(a0 : ℝ)| / (invEta : ℝ) = 2 * (|(a0 : ℝ)| / (invEta : ℝ)) := by ring
            linarith
          have h2 : ⟪vVec, y⟫ ≤ -(|(a0 : ℝ)| / (invEta : ℝ)) := hy.2.trans hupper
          exact (by linarith : |(a0 : ℝ)| / (invEta : ℝ) ≤ -⟪vVec, y⟫).trans (neg_le_abs _)
      have hv_norm_le : ‖vVec‖ ≤ |(a0 : ℝ)| / (invEta : ℝ) ^ 2 := by
        have hsq : ‖vVec‖ ^ 2 ≤ (|(a0 : ℝ)| / (invEta : ℝ) ^ 2) ^ 2 := by
          rw [norm_sq_ratVecToEuclidean_eq_ratDot hv_len]
          have hr : (ratDot v v : ℝ) ≤ ((1 / (invEta : ℚ)) ^ 4 * a0 ^ 2 : ℚ) := by
            exact_mod_cast hsharp
          refine hr.trans_eq ?_
          push_cast; rw [div_pow, div_pow, sq_abs]; ring
        have h1 := Real.sqrt_le_sqrt hsq
        rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (by positivity)] at h1
      by_cases hv0 : vVec = 0
      · have hempty : {y : EuclideanSpace ℝ (Fin nRem) |
            |(a0 : ℝ)| / (invEta : ℝ) ≤ |⟪vVec, y⟫|} = ∅ := by
          ext y
          simp only [hv0, inner_zero_left, abs_zero, Set.mem_ofPred_eq, Set.mem_empty_iff_false,
            iff_false, not_le]
          positivity
        refine (measureReal_mono hsub_sub).trans ?_
        rw [hempty, measureReal_empty]; positivity
      · have hv_pos : 0 < ‖vVec‖ := norm_pos_iff.mpr hv0
        let uUnit : Fin 1 → EuclideanSpace ℝ (Fin nRem) := fun _ => (‖vVec‖)⁻¹ • vVec
        have hu_norm : ∀ s : Fin 1, ‖uUnit s‖ = 1 := fun _ => by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hv_pos),
            inv_mul_cancel₀ hv_pos.ne']
        have hu_orth : Pairwise fun s t : Fin 1 => ⟪uUnit s, uUnit t⟫ = 0 := fun s t hst =>
          absurd (Subsingleton.elim s t) hst
        have hmap := ProbabilityTheory.stdGaussian_map_inner_pi hu_norm hu_orth
        have hsub2 : {y : EuclideanSpace ℝ (Fin nRem) |
            |(a0 : ℝ)| / (invEta : ℝ) ≤ |⟪vVec, y⟫|} ⊆
            (fun y : EuclideanSpace ℝ (Fin nRem) => fun _ : Fin 1 => ⟪uUnit 0, y⟫) ⁻¹'
              {z : Fin 1 → ℝ | (invEta : ℝ) ≤ |z 0|} := by
          intro y hy
          simp only [Set.mem_preimage, Set.mem_ofPred_eq, uUnit, real_inner_smul_left, abs_mul,
            abs_of_pos (inv_pos.mpr hv_pos)] at hy ⊢
          rw [inv_mul_eq_div, le_div_iff₀ hv_pos]
          have hmul : (invEta : ℝ) * ‖vVec‖ ≤ |(a0 : ℝ)| / (invEta : ℝ) := by
            calc (invEta : ℝ) * ‖vVec‖ ≤ (invEta : ℝ) * (|(a0 : ℝ)| / (invEta : ℝ) ^ 2) :=
                  mul_le_mul_of_nonneg_left hv_norm_le hEta_pos.le
              _ = |(a0 : ℝ)| / (invEta : ℝ) := by field_simp [hEta_pos.ne']
          exact hmul.trans hy
        have hmeas_proj : Measurable (fun y : EuclideanSpace ℝ (Fin nRem) =>
            fun _ : Fin 1 => ⟪uUnit 0, y⟫) :=
          Measurable.of_eval fun _ => (innerSL ℝ (uUnit 0)).continuous.measurable
        have hmeas_tail : MeasurableSet {z : Fin 1 → ℝ | (invEta : ℝ) ≤ |z 0|} :=
          (isClosed_le continuous_const ((continuous_apply 0).abs)).measurableSet
        have htail_eq : (stdGaussian (EuclideanSpace ℝ (Fin nRem))).real
            ((fun y => fun _ : Fin 1 => ⟪uUnit 0, y⟫) ⁻¹'
              {z : Fin 1 → ℝ | (invEta : ℝ) ≤ |z 0|}) =
            (gaussianReal 0 1).real {t : ℝ | (invEta : ℝ) ≤ |t|} := by
          rw [Measure.real_def, Measure.real_def, ← Measure.map_apply hmeas_proj hmeas_tail, hmap]
          have hmp := MeasureTheory.measurePreserving_eval (fun _ : Fin 1 => gaussianReal 0 1) 0
          have hpre : (fun z : Fin 1 → ℝ => z 0) ⁻¹' {t : ℝ | (invEta : ℝ) ≤ |t|} =
              {z : Fin 1 → ℝ | (invEta : ℝ) ≤ |z 0|} := rfl
          rw [← hpre, hmp.measure_preimage
            ((isClosed_le continuous_const continuous_abs).measurableSet.nullMeasurableSet)]
        have hpow_le : (invEta : ℝ) ≤ (2 : ℝ) ^ invEta := by
          exact_mod_cast Nat.lt_two_pow_self.le
        have h2pow : 1 / (2 : ℝ) ^ invEta ≤ 1 / (invEta : ℝ) :=
          one_div_le_one_div_of_le hEta_pos hpow_le
        calc (stdGaussian (EuclideanSpace ℝ (Fin nRem))).real _
            ≤ (stdGaussian (EuclideanSpace ℝ (Fin nRem))).real _ :=
              measureReal_mono (hsub_sub.trans hsub2)
          _ = (gaussianReal 0 1).real {t : ℝ | (invEta : ℝ) ≤ |t|} := htail_eq
          _ ≤ 1 / (2 : ℝ) ^ invEta := gaussianReal_abs_ge_le_two_pow hEta
          _ ≤ 1 / (invEta : ℝ) := h2pow
          _ ≤ 1 / (invEta : ℝ) + (invEta : ℝ) ^ 2 / (H : ℝ) :=
              le_add_of_nonneg_right (by positivity)
    · -- Smooth halfspace: `‖vVec‖ > |a0| / invEta^2 > 0`.
      push Not at hsharp
      have hv_norm_gt : |(a0 : ℝ)| / (invEta : ℝ) ^ 2 < ‖vVec‖ := by
        have hsq : (|(a0 : ℝ)| / (invEta : ℝ) ^ 2) ^ 2 < ‖vVec‖ ^ 2 := by
          rw [norm_sq_ratVecToEuclidean_eq_ratDot hv_len]
          have hr : ((1 / (invEta : ℚ)) ^ 4 * a0 ^ 2 : ℚ) < (ratDot v v : ℝ) := by
            exact_mod_cast hsharp
          refine lt_of_eq_of_lt ?_ hr
          push_cast; rw [div_pow, sq_abs]; ring
        have h1 := Real.sqrt_lt_sqrt (by positivity) hsq
        rwa [Real.sqrt_sq (by positivity), Real.sqrt_sq (norm_nonneg _)] at h1
      have hv_pos : 0 < ‖vVec‖ := lt_trans (by positivity) hv_norm_gt
      have hv_ne : vVec ≠ 0 := norm_pos_iff.mp hv_pos
      set lo : ℝ := min ((p.2 : ℝ) - (a0 : ℝ) * u) ((p.2 : ℝ) - (a0 : ℝ) * uStar)
      set hi : ℝ := max ((p.2 : ℝ) - (a0 : ℝ) * u) ((p.2 : ℝ) - (a0 : ℝ) * uStar)
      have hsub_slab : {y : EuclideanSpace ℝ (Fin nRem) |
            (p.2 : ℝ) - (a0 : ℝ) * u < ⟪vVec, y⟫} \
          {y : EuclideanSpace ℝ (Fin nRem) | (p.2 : ℝ) - (a0 : ℝ) * uStar < ⟪vVec, y⟫} ⊆
          {y : EuclideanSpace ℝ (Fin nRem) | ⟪vVec, y⟫ ∈ Icc lo hi} := by
        intro y hy
        simp only [Set.mem_sdiff, Set.mem_ofPred_eq, not_lt, Set.mem_Icc] at hy ⊢
        exact ⟨(min_le_left _ _).trans hy.1.le, hy.2.trans (le_max_right _ _)⟩
      refine (measureReal_mono hsub_slab).trans ?_
      rw [Measure.real_def]
      have hle_enn := ProbabilityTheory.stdGaussian_inner_mem_le hv_ne
        (measurableSet_Icc (a := lo) (b := hi))
      have hlen_eq : hi - lo = |(a0 : ℝ)| * |u - uStar| := by
        dsimp only [hi, lo]
        rw [max_sub_min_eq_abs, ← abs_mul]
        have : (p.2 : ℝ) - (a0 : ℝ) * uStar - ((p.2 : ℝ) - (a0 : ℝ) * u) =
            (a0 : ℝ) * (u - uStar) := by ring
        rw [this]
      have hvol : volume (Icc lo hi) = ENNReal.ofReal (|(a0 : ℝ)| * |u - uStar|) := by
        rw [Real.volume_Icc, hlen_eq]
      rw [hvol, ← ENNReal.ofReal_mul (by positivity)] at hle_enn
      refine (ENNReal.toReal_le_of_le_ofReal (by positivity) hle_enn).trans ?_
      have h2pi_gt : (1 : ℝ) ≤ Real.sqrt (2 * Real.pi) := by
        simpa using Real.sqrt_le_sqrt (by linarith [Real.pi_gt_three] : (1 : ℝ) ≤ 2 * Real.pi)
      have hcoeff : (Real.sqrt (2 * Real.pi) * ‖vVec‖)⁻¹ * (|(a0 : ℝ)| * |u - uStar|) ≤
          (invEta : ℝ) ^ 2 / (H : ℝ) := by
        have h1 : (Real.sqrt (2 * Real.pi) * ‖vVec‖)⁻¹ ≤ ‖vVec‖⁻¹ :=
          inv_anti₀ hv_pos (by nlinarith)
        have h2 : ‖vVec‖⁻¹ ≤ (invEta : ℝ) ^ 2 / |(a0 : ℝ)| := by
          rw [inv_eq_one_div, div_le_div_iff₀ hv_pos ha0_abs_pos, one_mul, mul_comm]
          exact (div_le_iff₀ (by positivity)).mp hv_norm_gt.le
        calc (Real.sqrt (2 * Real.pi) * ‖vVec‖)⁻¹ * (|(a0 : ℝ)| * |u - uStar|)
            ≤ ((invEta : ℝ) ^ 2 / |(a0 : ℝ)|) * (|(a0 : ℝ)| * (1 / (H : ℝ))) :=
              mul_le_mul (h1.trans h2) (mul_le_mul_of_nonneg_left hdist ha0_abs_pos.le)
                (by positivity) (by positivity)
          _ = (invEta : ℝ) ^ 2 / (H : ℝ) := by field_simp [ha0_abs_pos.ne', hH_pos.ne']
      linarith [hcoeff, show (0 : ℝ) ≤ 1 / (invEta : ℝ) by positivity]

/-! ### Deterministic grid-search algorithm and `ComputableInPolyTime` certificate -/

/-- Exact rational score evaluated at integer grid point `k / H` during a coordinate step. -/
@[expose] def approxClauseScore (d : ℕ) (curClauses : List (List (List ℚ × ℚ)))
    (H invDelta : ℕ) (k : ℤ) : ℚ :=
  ratSum ((stepOneCoord (Rat.divInt k (H : ℤ)) curClauses).map fun cl =>
    approxClauseProb d cl invDelta)

/-- Parameters `(R, H, invDelta)` for the 1D grid search at clause width `d`, dimension `n`,
clause count `m`, and inverse error `q`. -/
private def derandGridParams (d n m q : ℕ) : ℕ × ℕ × ℕ :=
  let d1 := max 1 d
  let n1 := max 1 n
  let m1 := max 1 m
  let q1 := max 1 q
  let invEta := 64 * m1 * m1 * d1 * q1 * n1
  let R := 16 * m1 * q1 * n1
  let H := 64 * q1 * n1 * m1 * d1 * invEta * invEta
  let invDelta := 16 * m1 * q1 * n1
  (R, H, invDelta)

/-- Uniform integer grid `[-R * H, R * H] ∩ ℤ` used to search for the next coordinate. -/
private def derandIntGrid (R H : ℕ) : List ℤ :=
  (List.range (2 * (R * H) + 1)).map fun (j : ℕ) => (j : ℤ) - ((R * H : ℕ) : ℤ)

private theorem mem_derandIntGrid_natAbs_le {R H : ℕ} {k : ℤ} (hk : k ∈ derandIntGrid R H) :
    k.natAbs ≤ R * H := by
  set M := R * H
  simp only [derandIntGrid, List.mem_map] at hk
  rcases hk with ⟨j, hj, rfl⟩
  rw [List.mem_range] at hj
  omega

private theorem mem_derandIntGrid_of_bounds {R H : ℕ} {k : ℤ}
    (hlo : -((R * H : ℕ) : ℤ) ≤ k) (hhi : k ≤ ((R * H : ℕ) : ℤ)) :
    k ∈ derandIntGrid R H := by
  set M := R * H
  simp only [derandIntGrid, List.mem_map]
  exact ⟨(k + (M : ℤ)).toNat, List.mem_range.mpr (by omega), by omega⟩

/-- Single greedy coordinate-selection step appending the best integer grid coordinate `kBest` to
`ks`. -/
private def derandCoordStep (d : ℕ) (inp : ℕ × List (List (List ℚ × ℚ)) × ℕ)
    (ks : List ℤ) : List ℤ :=
  let n := inp.1
  let clauses := inp.2.1
  let q := inp.2.2
  let params := derandGridParams d n clauses.length q
  let R := params.1
  let H := params.2.1
  let invDelta := params.2.2
  let curClauses := updateClausesByInts H ks clauses
  let grid := derandIntGrid R H
  let kBest := grid.foldl (fun best k =>
    if decide (approxClauseScore d curClauses H invDelta best ≤
        approxClauseScore d curClauses H invDelta k) then k else best) (0 : ℤ)
  ks ++ [kBest]

/-- Deterministic polynomial-time Gaussian halfspace-conjunction derandomisation algorithm for
fixed clause width `d`. -/
def derandGaussianAlg (d : ℕ) (inp : ℕ × List (List (List ℚ × ℚ)) × ℕ) : List ℚ :=
  if inp.2.1.isEmpty || decide (d = 0) then List.replicate inp.1 0
  else
    let params := derandGridParams d inp.1 inp.2.1.length inp.2.2
    let H := params.2.1
    let ks := (derandCoordStep d inp)^[inp.1] []
    ks.map fun k => Rat.divInt k (H : ℤ)

private theorem foldl_max_spec {α : Type*} (score : α → ℚ) (l : List α) (init : α) :
    let res := l.foldl (fun best a => if decide (score best ≤ score a) then a else best) init
    (res = init ∨ res ∈ l) ∧ score init ≤ score res ∧ ∀ a ∈ l, score a ≤ score res := by
  induction l generalizing init with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons]
    set next := if decide (score init ≤ score x) then x else init
    obtain ⟨hmem, hle_next, hall⟩ := ih next
    have hinit_le_next : score init ≤ score next := by
      dsimp only [next]; split_ifs with h
      · exact decide_eq_true_eq.mp h
      · exact le_rfl
    have hx_le_next : score x ≤ score next := by
      dsimp only [next]; split_ifs with h
      · exact le_rfl
      · exact le_of_not_ge (fun hle => h (decide_eq_true hle))
    refine ⟨?_, hinit_le_next.trans hle_next, fun a ha => ?_⟩
    · rcases hmem with h1 | h2
      · rw [h1]; dsimp only [next]; split_ifs
        · exact Or.inr List.mem_cons_self
        · exact Or.inl rfl
      · exact Or.inr (List.mem_cons_of_mem _ h2)
    · rcases List.mem_cons.mp ha with rfl | hxs
      · exact hx_le_next.trans hle_next
      · exact hall a hxs

private theorem computableInPolyTime_stepOneCoord :
    ComputableInPolyTime
      (fun p : ℚ × List (List (List ℚ × ℚ)) => stepOneCoord p.1 p.2)
      (encPair encRat (encList (encList (encPair (encList encRat) encRat))))
      (encList (encList (encPair (encList encRat) encRat))) := by
  let eHalf := encPair (encList encRat) encRat
  let eCl := encList eHalf
  let eCls := encList eCl
  have hhalf : ComputableInPolyTime
      (fun y : ℚ × (List ℚ × ℚ) => (y.2.1.tail, y.2.2 - y.2.1.headD 0 * y.1))
      (encPair encRat eHalf) eHalf := by
    have hu := ComputableInPolyTime.fst encRat eHalf
    have hp := ComputableInPolyTime.snd encRat eHalf
    have hp1 := (ComputableInPolyTime.fst (encList encRat) encRat).comp hp
    have hp2 := (ComputableInPolyTime.snd (encList encRat) encRat).comp hp
    have htail := (ComputableInPolyTime.listTail encRat).comp hp1
    have hhead :=
      (ComputableInPolyTime.headD (encA := encRat) (encL := encList encRat) 0).comp hp1
    exact (htail.prod (ComputableInPolyTime.rat_sub' hp2
      (ComputableInPolyTime.rat_mul' hhead hu))).of_enc_eq fun _ => rfl
  have hcl : ComputableInPolyTime
      (fun y : ℚ × List (List ℚ × ℚ) =>
        y.2.map fun p => (p.1.tail, p.2 - p.1.headD 0 * y.1))
      (encPair encRat eCl) eCl :=
    (ComputableInPolyTime.mapWith hhalf (ComputableInPolyTime.fst encRat eCl)
      (ComputableInPolyTime.snd encRat eCl)).of_enc_eq fun _ => rfl
  exact (ComputableInPolyTime.mapWith hcl (ComputableInPolyTime.fst encRat eCls)
    (ComputableInPolyTime.snd encRat eCls)).of_enc_eq fun _ => rfl

private theorem computableInPolyTime_updateClausesByInts :
    ComputableInPolyTime
      (fun p : (ℕ × List ℤ) × List (List (List ℚ × ℚ)) =>
        updateClausesByInts p.1.1 p.1.2 p.2)
      (encPair (encPair encUnary (encList encIntBin))
        (encList (encList (encPair (encList encRat) encRat))))
      (encList (encList (encPair (encList encRat) encRat))) := by
  let eHalf := encPair (encList encRat) encRat
  let eCl := encList eHalf
  let eCls := encList eCl
  let ePar := encPair encUnary (encList encIntBin)
  let eIn := encPair ePar eCls
  have hpar := ComputableInPolyTime.fst ePar eCls
  have hcls := ComputableInPolyTime.snd ePar eCls
  have hH := (ComputableInPolyTime.fst encUnary (encList encIntBin)).comp hpar
  have hks := (ComputableInPolyTime.snd encUnary (encList encIntBin)).comp hpar
  have hHInt := ComputableInPolyTime.intBin_natCast.comp
    (ComputableInPolyTime.unary_to_binary.comp hH)
  have hdivStep : ComputableInPolyTime (fun y : ℤ × ℤ => Rat.divInt y.2 y.1)
      (encPair encIntBin encIntBin) encRat :=
    ComputableInPolyTime.rat_divInt' (ComputableInPolyTime.snd encIntBin encIntBin)
      (ComputableInPolyTime.fst encIntBin encIntBin)
  have huList := ComputableInPolyTime.mapWith hdivStep hHInt hks
  have hksLen := (ComputableInPolyTime.length (enc := encIntBin)).comp hks
  let eState := encPair encUnary (encList encRat)
  have hhalf : ComputableInPolyTime
      (fun y : (ℕ × List ℚ) × (List ℚ × ℚ) =>
        (y.2.1.drop y.1.1, y.2.2 - ratDot y.2.1 y.1.2))
      (encPair eState eHalf) eHalf := by
    have hst := ComputableInPolyTime.fst eState eHalf
    have hp := ComputableInPolyTime.snd eState eHalf
    have ht := (ComputableInPolyTime.fst encUnary (encList encRat)).comp hst
    have hu := (ComputableInPolyTime.snd encUnary (encList encRat)).comp hst
    have hp1 := (ComputableInPolyTime.fst (encList encRat) encRat).comp hp
    have hp2 := (ComputableInPolyTime.snd (encList encRat) encRat).comp hp
    have hdrop := ComputableInPolyTime.listDropWithInput hp1 ht
    have hdot := computableInPolyTime_ratDot.comp (hp1.prod hu)
    exact (hdrop.prod (ComputableInPolyTime.rat_sub' hp2 hdot)).of_enc_eq fun _ => rfl
  have hcl : ComputableInPolyTime
      (fun y : (ℕ × List ℚ) × List (List ℚ × ℚ) =>
        y.2.map fun p => (p.1.drop y.1.1, p.2 - ratDot p.1 y.1.2))
      (encPair eState eCl) eCl :=
    (ComputableInPolyTime.mapWith hhalf (ComputableInPolyTime.fst eState eCl)
      (ComputableInPolyTime.snd eState eCl)).of_enc_eq fun _ => rfl
  exact (ComputableInPolyTime.mapWith hcl (hksLen.prod huList) hcls).of_enc_eq fun _ => rfl

private theorem computableInPolyTime_mapApproxClauseProb (d : ℕ) :
    ComputableInPolyTime
      (fun p : ℕ × List (List (List ℚ × ℚ)) => p.2.map fun cl => approxClauseProb d cl p.1)
      (encPair encUnary (encList (encList (encPair (encList encRat) encRat)))) (encList encRat)
        := by
  let eCl := encList (encPair (encList encRat) encRat)
  have hprobStep : ComputableInPolyTime
      (fun y : ℕ × List (List ℚ × ℚ) => approxClauseProb d y.2 y.1)
      (encPair encUnary eCl) encRat :=
    ((computableInPolyTime_approxClauseProb d).comp
      ((ComputableInPolyTime.snd encUnary eCl).prod
        (ComputableInPolyTime.fst encUnary eCl))).of_enc_eq fun _ => rfl
  exact (ComputableInPolyTime.mapWith hprobStep
    (ComputableInPolyTime.fst encUnary (encList eCl))
    (ComputableInPolyTime.snd encUnary (encList eCl))).of_enc_eq fun _ => rfl

private theorem computableInPolyTime_approxClauseScore (d : ℕ) :
    ComputableInPolyTime
      (fun p : (List (List (List ℚ × ℚ)) × (ℕ × ℕ)) × ℤ =>
        approxClauseScore d p.1.1 p.1.2.1 p.1.2.2 p.2)
      (encPair
        (encPair (encList (encList (encPair (encList encRat) encRat)))
          (encPair encUnary encUnary))
        encIntBin)
      encRat := by
  let eCls := encList (encList (encPair (encList encRat) encRat))
  let ePar := encPair eCls (encPair encUnary encUnary)
  have hpar := ComputableInPolyTime.fst ePar encIntBin
  have hk := ComputableInPolyTime.snd ePar encIntBin
  have hcls := (ComputableInPolyTime.fst eCls (encPair encUnary encUnary)).comp hpar
  have hHI := (ComputableInPolyTime.snd eCls (encPair encUnary encUnary)).comp hpar
  have hH := (ComputableInPolyTime.fst encUnary encUnary).comp hHI
  have hinv := (ComputableInPolyTime.snd encUnary encUnary).comp hHI
  have hHInt := ComputableInPolyTime.intBin_natCast.comp
    (ComputableInPolyTime.unary_to_binary.comp hH)
  have hu := ComputableInPolyTime.rat_divInt' hk hHInt
  have hstep := computableInPolyTime_stepOneCoord.comp (hu.prod hcls)
  have hmapped := (computableInPolyTime_mapApproxClauseProb d).comp (hinv.prod hstep)
  exact (computableInPolyTime_ratSum.comp hmapped).of_enc_eq fun p =>
    congrArg encRat (by dsimp only [approxClauseScore, Function.comp_apply])

private theorem computableInPolyTime_derandGridParams (d : ℕ) :
    ComputableInPolyTime
      (fun inp : ℕ × List (List (List ℚ × ℚ)) × ℕ =>
        derandGridParams d inp.1 inp.2.1.length inp.2.2)
      encDerandGaussianInput (encPair encUnary (encPair encUnary encUnary)) := by
  let eHalf := encPair (encList encRat) encRat
  let eCls := encList (encList eHalf)
  have hn := ComputableInPolyTime.fst encUnary (encPair eCls encUnary)
  have hrest := ComputableInPolyTime.snd encUnary (encPair eCls encUnary)
  have hcls := (ComputableInPolyTime.fst eCls encUnary).comp hrest
  have hq := (ComputableInPolyTime.snd eCls encUnary).comp hrest
  have hm := (ComputableInPolyTime.length (enc := encList eHalf)).comp hcls
  have hd1 : ComputableInPolyTime (fun _ : ℕ × List (List (List ℚ × ℚ)) × ℕ => max 1 d)
      encDerandGaussianInput encUnary := ComputableInPolyTime.const (max 1 d)
  have hn1 := ComputableInPolyTime.unary_max.comp ((ComputableInPolyTime.const 1).prod hn)
  have hm1 := ComputableInPolyTime.unary_max.comp ((ComputableInPolyTime.const 1).prod hm)
  have hq1 := ComputableInPolyTime.unary_max.comp ((ComputableInPolyTime.const 1).prod hq)
  have hinvEta := ComputableInPolyTime.unary_mul'
    (ComputableInPolyTime.unary_mul'
      (ComputableInPolyTime.unary_mul'
        (ComputableInPolyTime.unary_mul'
          (ComputableInPolyTime.unary_mul' (ComputableInPolyTime.const 64) hm1) hm1) hd1) hq1)
    hn1
  have hR := ComputableInPolyTime.unary_mul'
    (ComputableInPolyTime.unary_mul'
      (ComputableInPolyTime.unary_mul' (ComputableInPolyTime.const 16) hm1) hq1) hn1
  have hH := ComputableInPolyTime.unary_mul'
    (ComputableInPolyTime.unary_mul'
      (ComputableInPolyTime.unary_mul'
        (ComputableInPolyTime.unary_mul'
          (ComputableInPolyTime.unary_mul'
            (ComputableInPolyTime.unary_mul' (ComputableInPolyTime.const 64) hq1) hn1) hm1) hd1)
        hinvEta) hinvEta
  exact (hR.prod (hH.prod hR)).of_enc_eq fun _ => rfl

private theorem computableInPolyTime_derandGaussianAlg (d : ℕ) :
    ComputableInPolyTime (derandGaussianAlg d) encDerandGaussianInput (encList encRat) := by
  let eHalf := encPair (encList encRat) encRat
  let eCl := encList eHalf
  let eCls := encList eCl
  let eIn := encDerandGaussianInput
  have hn := ComputableInPolyTime.fst encUnary (encPair eCls encUnary)
  have hrest := ComputableInPolyTime.snd encUnary (encPair eCls encUnary)
  have hcls := (ComputableInPolyTime.fst eCls encUnary).comp hrest
  have hparams := computableInPolyTime_derandGridParams d
  have hR := (ComputableInPolyTime.fst encUnary (encPair encUnary encUnary)).comp hparams
  have hHI := (ComputableInPolyTime.snd encUnary (encPair encUnary encUnary)).comp hparams
  have hH := (ComputableInPolyTime.fst encUnary encUnary).comp hHI
  have hinv := (ComputableInPolyTime.snd encUnary encUnary).comp hHI
  -- Polynomial-time certificate for a single coordinate step `derandCoordStep d`.
  have hstep : ComputableInPolyTime
      (fun p : (ℕ × List (List (List ℚ × ℚ)) × ℕ) × List ℤ => derandCoordStep d p.1 p.2)
      (encPair eIn (encList encIntBin)) (encList encIntBin) := by
    let eStepIn := encPair eIn (encList encIntBin)
    have hinp := ComputableInPolyTime.fst eIn (encList encIntBin)
    have hks := ComputableInPolyTime.snd eIn (encList encIntBin)
    have hcls' := hcls.comp hinp
    have hR' := hR.comp hinp
    have hH' := hH.comp hinp
    have hinv' := hinv.comp hinp
    have hcur := computableInPolyTime_updateClausesByInts.comp ((hH'.prod hks).prod hcls')
    have hRH := ComputableInPolyTime.unary_mul' hR' hH'
    have hgridLen := ComputableInPolyTime.unary_add'
      (ComputableInPolyTime.unary_mul' (ComputableInPolyTime.const 2) hRH)
      (ComputableInPolyTime.const 1)
    have hgridRange := ComputableInPolyTime.range.comp hgridLen
    have hRHInt := ComputableInPolyTime.intBin_natCast.comp
      (ComputableInPolyTime.unary_to_binary.comp hRH)
    have hsubStep : ComputableInPolyTime (fun y : ℤ × ℕ => (y.2 : ℤ) - y.1)
        (encPair encIntBin encUnary) encIntBin :=
      ComputableInPolyTime.intBin_sub'
        (ComputableInPolyTime.intBin_natCast.comp
          (ComputableInPolyTime.unary_to_binary.comp (ComputableInPolyTime.snd encIntBin encUnary)))
        (ComputableInPolyTime.fst encIntBin encUnary)
    have hgrid : ComputableInPolyTime
        (fun p : (ℕ × List (List (List ℚ × ℚ)) × ℕ) × List ℤ =>
          derandIntGrid (derandGridParams d p.1.1 p.1.2.1.length p.1.2.2).1
            (derandGridParams d p.1.1 p.1.2.1.length p.1.2.2).2.1)
        eStepIn (encList encIntBin) :=
      (ComputableInPolyTime.mapWith hsubStep hRHInt hgridRange).of_enc_eq fun _ => rfl
    let eFoldPar := encPair eCls (encPair encUnary encUnary)
    have hfoldStep : ComputableInPolyTime
        (fun y : ((List (List (List ℚ × ℚ)) × (ℕ × ℕ)) × ℤ) × ℤ =>
          if decide (approxClauseScore d y.1.1.1 y.1.1.2.1 y.1.1.2.2 y.1.2 ≤
              approxClauseScore d y.1.1.1 y.1.1.2.1 y.1.1.2.2 y.2) then y.2 else y.1.2)
        (encPair (encPair eFoldPar encIntBin) encIntBin) encIntBin := by
      have hp := ComputableInPolyTime.fst (encPair eFoldPar encIntBin) encIntBin
      have hk := ComputableInPolyTime.snd (encPair eFoldPar encIntBin) encIntBin
      have hfp := (ComputableInPolyTime.fst eFoldPar encIntBin).comp hp
      have hbest := (ComputableInPolyTime.snd eFoldPar encIntBin).comp hp
      have hsBest := (computableInPolyTime_approxClauseScore d).comp (hfp.prod hbest)
      have hsK := (computableInPolyTime_approxClauseScore d).comp (hfp.prod hk)
      exact (ComputableInPolyTime.rat_le.comp (hsBest.prod hsK)).ite' hk hbest
    have hgrowthFold : ComputableInPolyTime
        (fun p : (ℕ × List (List (List ℚ × ℚ)) × ℕ) × List ℤ =>
          (derandGridParams d p.1.1 p.1.2.1.length p.1.2.2).1 *
            (derandGridParams d p.1.1 p.1.2.1.length p.1.2.2).2.1 + 1)
        eStepIn encUnary :=
      ComputableInPolyTime.unary_add' hRH (ComputableInPolyTime.const 1)
    have hkBest := ComputableInPolyTime.foldlWith_of_bounded_growth
      (encA := encIntBin) (encB := encIntBin)
      (step := fun (par : List (List (List ℚ × ℚ)) × (ℕ × ℕ)) (best k : ℤ) =>
        if decide (approxClauseScore d par.1 par.2.1 par.2.2 best ≤
            approxClauseScore d par.1 par.2.1 par.2.2 k) then k else best)
      (hcur.prod (hH'.prod hinv')) hgrid (ComputableInPolyTime.const (0 : ℤ))
      hfoldStep hgrowthFold.polyBounded (fun x state k hk => by
        have hnat := mem_derandIntGrid_natAbs_le hk
        have hlen_k : (encIntBin k).length ≤
            (derandGridParams d x.1.1 x.1.2.1.length x.1.2.2).1 *
              (derandGridParams d x.1.1 x.1.2.1.length x.1.2.2).2.1 + 1 := by
          rw [length_encIntBin]
          exact Nat.add_le_add_right ((Nat.size_le.mpr Nat.lt_two_pow_self).trans hnat) 1
        split_ifs
        · exact hlen_k.trans (Nat.le_add_left _ _)
        · exact Nat.le_add_right _ _)
    have hsingle : ComputableInPolyTime (fun z : ℤ => [z]) encIntBin (encList encIntBin) :=
      (ComputableInPolyTime.replicate (ComputableInPolyTime.const 1)
        ComputableInPolyTime.id').of_enc_eq fun _ => rfl
    exact ((ComputableInPolyTime.listAppend encIntBin).comp
      (hks.prod (hsingle.comp hkBest))).of_enc_eq fun _ => rfl
  -- Iterate `derandCoordStep d` for `n` steps with bounded state growth.
  have hgrowthIter : ComputableInPolyTime
      (fun inp : ℕ × List (List (List ℚ × ℚ)) × ℕ =>
        2 * ((derandGridParams d inp.1 inp.2.1.length inp.2.2).1 *
          (derandGridParams d inp.1 inp.2.1.length inp.2.2).2.1) + 4)
      eIn encUnary :=
    ComputableInPolyTime.unary_add'
      (ComputableInPolyTime.unary_mul' (ComputableInPolyTime.const 2)
        (ComputableInPolyTime.unary_mul' hR hH))
      (ComputableInPolyTime.const 4)
  have hiter := ComputableInPolyTime.iterateWith_of_bounded_growth
    ComputableInPolyTime.id' hn (ComputableInPolyTime.const ([] : List ℤ)) hstep
    hgrowthIter.polyBounded (fun x ks => by
      dsimp only [derandCoordStep]
      set params := derandGridParams d x.1 x.2.1.length x.2.2
      set cur := updateClausesByInts params.2.1 ks x.2.1
      set kBest : ℤ := (derandIntGrid params.1 params.2.1).foldl
        (fun best k => if decide (approxClauseScore d cur params.2.1 params.2.2 best ≤
          approxClauseScore d cur params.2.1 params.2.2 k) then k else best) (0 : ℤ)
      have hkBest_abs : kBest.natAbs ≤ params.1 * params.2.1 := by
        rcases (foldl_max_spec (approxClauseScore d cur params.2.1 params.2.2)
          (derandIntGrid params.1 params.2.1) (0 : ℤ)).1 with h0 | hmem
        · change (List.foldl _ (0 : ℤ) _).natAbs ≤ _; rw [h0]; simp
        · exact mem_derandIntGrid_natAbs_le hmem
      have hlen_k : (encIntBin kBest).length ≤ params.1 * params.2.1 + 1 := by
        rw [length_encIntBin]
        exact Nat.add_le_add_right ((Nat.size_le.mpr Nat.lt_two_pow_self).trans hkBest_abs) 1
      rw [encList_append, List.length_append, encList_cons, List.length_append, length_frame]
      have hnil : (encList encIntBin []).length = 0 := rfl
      rw [hnil, Nat.add_zero]; omega)
  have hHInt := ComputableInPolyTime.intBin_natCast.comp
    (ComputableInPolyTime.unary_to_binary.comp hH)
  have hdivStep : ComputableInPolyTime (fun y : ℤ × ℤ => Rat.divInt y.2 y.1)
      (encPair encIntBin encIntBin) encRat :=
    ComputableInPolyTime.rat_divInt' (ComputableInPolyTime.snd encIntBin encIntBin)
      (ComputableInPolyTime.fst encIntBin encIntBin)
  have helse := ComputableInPolyTime.mapWith hdivStep hHInt hiter
  have hthen := ComputableInPolyTime.replicate (encA := encRat) hn
    (ComputableInPolyTime.const (0 : ℚ))
  have hcond := ComputableInPolyTime.bool_or'
    ((ComputableInPolyTime.listIsEmpty' eCl).comp hcls)
    (ComputableInPolyTime.const (decide (d = 0)))
  exact (hcond.ite' hthen helse).of_enc_eq fun x =>
    congrArg (encList encRat) (by dsimp only [derandGaussianAlg, Function.comp_apply])

/-! ### One-step conditional-expectation loss bound and telescoping -/

private theorem one_step_derand_loss {d nOrig nRem q : ℕ}
    (hd : 1 ≤ d) (hnOrig : 1 ≤ nOrig) (hq : 1 ≤ q)
    {curClauses : List (List (List ℚ × ℚ))} (hm : 1 ≤ curClauses.length)
    (hcl_len : ∀ cl ∈ curClauses, cl.length ≤ d)
    (hp_len : ∀ cl ∈ curClauses, ∀ p ∈ cl, p.1.length = nRem + 1) :
    let params := derandGridParams d nOrig curClauses.length q
    let R := params.1
    let H := params.2.1
    let invDelta := params.2.2
    let kBest := (derandIntGrid R H).foldl (fun best k =>
      if decide (approxClauseScore d curClauses H invDelta best ≤
          approxClauseScore d curClauses H invDelta k) then k else best) 0
    gaussianConjunctionExpect (nRem + 1) curClauses - 9 / (32 * (q : ℝ) * (nOrig : ℝ)) ≤
      gaussianConjunctionExpect nRem (stepOneCoord (Rat.divInt kBest (H : ℤ)) curClauses) := by
  intro params R H invDelta kBest
  set m := curClauses.length
  set invEta := 64 * m * m * d * q * nOrig
  have hR_eq : R = 16 * m * q * nOrig := by
    dsimp only [R, params, derandGridParams]
    rw [max_eq_right hnOrig, max_eq_right hm, max_eq_right hq]
  have hH_eq : H = 64 * q * nOrig * m * d * invEta * invEta := by
    dsimp only [H, params, derandGridParams, invEta]
    rw [max_eq_right hd, max_eq_right hnOrig, max_eq_right hm, max_eq_right hq]
  have hinvDelta_eq : invDelta = 16 * m * q * nOrig := by
    dsimp only [invDelta, params, derandGridParams]
    rw [max_eq_right hnOrig, max_eq_right hm, max_eq_right hq]
  have hd_pos : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr hd
  have hn_pos : (0 : ℝ) < (nOrig : ℝ) := Nat.cast_pos.mpr hnOrig
  have hm_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm
  have hq_pos : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr hq
  have hEta_ge2 : 2 ≤ invEta :=
    le_trans (by norm_num) (show 64 * 1 * 1 * 1 * 1 * 1 ≤ invEta by dsimp only [invEta]; gcongr)
  have hEta_pos : (0 : ℝ) < (invEta : ℝ) := Nat.cast_pos.mpr (by omega)
  have hR_ge2 : 2 ≤ R :=
    le_trans (by norm_num) (show 16 * 1 * 1 * 1 ≤ R by rw [hR_eq]; gcongr)
  have hH_ge_Eta : invEta ≤ H := by
    rw [hH_eq]
    have h1 : 1 ≤ 64 * q * nOrig * m * d * invEta :=
      le_trans (by norm_num) (show 64 * 1 * 1 * 1 * 1 * 1 ≤ _ by gcongr; omega)
    simpa only [one_mul] using Nat.mul_le_mul_right invEta h1
  have hH_pos : (0 : ℝ) < (H : ℝ) := Nat.cast_pos.mpr (by omega)
  have hinvDelta_ge1 : 1 ≤ invDelta :=
    le_trans (by norm_num) (show 16 * 1 * 1 * 1 ≤ invDelta by rw [hinvDelta_eq]; gcongr)
  -- Define the real conditional expectation `f u`.
  let f : ℝ → ℝ := fun u =>
    (curClauses.map fun cl =>
      (stdGaussian (EuclideanSpace ℝ (Fin nRem))).real
        {y : EuclideanSpace ℝ (Fin nRem) |
          ∀ p ∈ cl, (p.2 : ℝ) - ((p.1.headD 0 : ℚ) : ℝ) * u <
            ⟪ratVecToEuclidean nRem p.1.tail, y⟫}).sum
  have hf_at_rat : ∀ k : ℤ,
      f ((Rat.divInt k (H : ℤ) : ℚ) : ℝ) =
        gaussianConjunctionExpect nRem (stepOneCoord (Rat.divInt k (H : ℤ)) curClauses) := by
    intro k
    simp only [f, gaussianConjunctionExpect, stepOneCoord, List.map_map, Function.comp_def]
    congr 1
    refine List.map_congr_left fun cl _ => ?_
    congr 1; ext y
    simp only [Set.mem_ofPred_eq, List.mem_map, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂, Rat.cast_sub, Rat.cast_mul]
  -- Quadrature accuracy at every grid point `k`.
  have hquad : ∀ k : ℤ,
      |(approxClauseScore d curClauses H invDelta k : ℝ) -
        f ((Rat.divInt k (H : ℤ) : ℚ) : ℝ)| ≤ 1 / (16 * (q : ℝ) * (nOrig : ℝ)) := by
    intro k
    rw [hf_at_rat k]
    simp only [approxClauseScore, gaussianConjunctionExpect, ratSum_eq_sum]
    have hsum_cast : ((List.map (fun cl => approxClauseProb d cl invDelta)
        (stepOneCoord (Rat.divInt k (H : ℤ)) curClauses)).sum : ℝ) =
        (List.map (fun cl => (approxClauseProb d cl invDelta : ℝ))
          (stepOneCoord (Rat.divInt k (H : ℤ)) curClauses)).sum := by
      rw [Rat.cast_list_sum, List.map_map]; rfl
    rw [hsum_cast]
    have hlist_bound : ∀ L : List (List (List ℚ × ℚ)),
        (∀ cl ∈ L, cl.length ≤ d ∧ ∀ p ∈ cl, p.1.length = nRem) →
        |(L.map fun cl => (approxClauseProb d cl invDelta : ℝ)).sum -
          (L.map fun cl => (stdGaussian (EuclideanSpace ℝ (Fin nRem))).real
            {y | ∀ p ∈ cl, (p.2 : ℝ) < ⟪ratVecToEuclidean nRem p.1, y⟫}).sum| ≤
          (L.length : ℝ) / (invDelta : ℝ) := by
      intro L hL
      induction L with
      | nil => simp
      | cons c cs ih =>
        have hc := hL c List.mem_cons_self
        have hcs := ih fun c' hc' => hL c' (List.mem_cons_of_mem _ hc')
        simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
        have h1 := abs_approxClauseProb_sub_le (N := nRem) hd hinvDelta_ge1 hc.1 hc.2
        have htri := abs_add_le
          ((approxClauseProb d c invDelta : ℝ) -
            (stdGaussian (EuclideanSpace ℝ (Fin nRem))).real
              {y | ∀ p ∈ c, (p.2 : ℝ) < ⟪ratVecToEuclidean nRem p.1, y⟫})
          ((cs.map fun cl => (approxClauseProb d cl invDelta : ℝ)).sum -
            (cs.map fun cl => (stdGaussian (EuclideanSpace ℝ (Fin nRem))).real
              {y | ∀ p ∈ cl, (p.2 : ℝ) < ⟪ratVecToEuclidean nRem p.1, y⟫}).sum)
        rw [sub_add_sub_comm] at htri
        linarith only [htri, h1, hcs, show 1 / (invDelta : ℝ) + (cs.length : ℝ) / (invDelta : ℝ) =
          ((cs.length : ℝ) + 1) / (invDelta : ℝ) by ring]
    have hstep_ok : ∀ cl ∈ stepOneCoord (Rat.divInt k (H : ℤ)) curClauses,
        cl.length ≤ d ∧ ∀ p ∈ cl, p.1.length = nRem := by
      intro cl hcl
      simp only [stepOneCoord, List.mem_map] at hcl
      rcases hcl with ⟨cl0, hcl0, rfl⟩
      refine ⟨by simpa using hcl_len cl0 hcl0, fun p hp => ?_⟩
      simp only [List.mem_map] at hp
      rcases hp with ⟨p0, hp0, rfl⟩
      have hlen0 := hp_len cl0 hcl0 p0 hp0
      simp [hlen0]
    refine (hlist_bound _ hstep_ok).trans ?_
    rw [stepOneCoord_length, hinvDelta_eq]
    change (m : ℝ) / ((16 * m * q * nOrig : ℕ) : ℝ) ≤ 1 / (16 * (q : ℝ) * (nOrig : ℝ))
    push_cast
    exact le_of_eq (by field_simp [hm_pos.ne', hq_pos.ne', hn_pos.ne'])
  -- Define bad union `B` and grid maximum `M`.
  set allHalfs : List (List ℚ × ℚ) := curClauses.flatten
  have hall_len : allHalfs.length ≤ m * d := by
    have hflat : ∀ L : List (List (List ℚ × ℚ)),
        (∀ cl ∈ L, cl.length ≤ d) → L.flatten.length ≤ L.length * d := fun L hL => by
      induction L with
      | nil => simp
      | cons c cs ih =>
        simp only [List.flatten_cons, List.length_append, List.length_cons, Nat.succ_mul]
        have := hL c List.mem_cons_self; have := ih fun c' hc' => hL c' (List.mem_cons_of_mem _ hc')
        omega
    exact hflat curClauses hcl_len
  set B : Set ℝ := ⋃ p ∈ allHalfs.toFinset, sharpBadInterval invEta p
  have hB_meas : MeasurableSet B :=
    Finset.measurableSet_biUnion _ fun p _ => measurableSet_sharpBadInterval invEta p
  have hB_prob : (gaussianReal 0 1).real B ≤ 1 / (16 * (m : ℝ) * (q : ℝ) * (nOrig : ℝ)) := by
    calc (gaussianReal 0 1).real B
        ≤ ∑ p ∈ allHalfs.toFinset, (gaussianReal 0 1).real (sharpBadInterval invEta p) :=
          measureReal_biUnion_finset_le _ _
      _ ≤ ∑ _p ∈ allHalfs.toFinset, (4 / (invEta : ℝ)) :=
          Finset.sum_le_sum fun p _ => gaussianReal_sharpBadInterval_le (by omega) p
      _ = (allHalfs.toFinset.card : ℝ) * (4 / (invEta : ℝ)) := by simp
      _ ≤ ((m * d : ℕ) : ℝ) * (4 / (invEta : ℝ)) := by
          have hcard : (allHalfs.toFinset.card : ℝ) ≤ ((m * d : ℕ) : ℝ) := by
            exact_mod_cast (List.toFinset_card_le allHalfs).trans hall_len
          exact mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = 1 / (16 * (m : ℝ) * (q : ℝ) * (nOrig : ℝ)) := by
          dsimp only [invEta]; push_cast
          field_simp [hm_pos.ne', hd_pos.ne', hq_pos.ne', hn_pos.ne']; ring
  set box1 : Set ℝ := Icc (-(R : ℝ)) (R : ℝ)
  have hbox1_meas : MeasurableSet box1 := measurableSet_Icc
  have hbox1_compl : (gaussianReal 0 1).real box1ᶜ ≤
      1 / (16 * (m : ℝ) * (q : ℝ) * (nOrig : ℝ)) := by
    have hsub : box1ᶜ ⊆ {u : ℝ | (R : ℝ) ≤ |u|} := by
      intro u hu
      simp only [box1, Set.mem_compl_iff, Set.mem_Icc, not_and_or, not_le] at hu
      rcases hu with hlt | hgt
      · exact (le_of_lt (by linarith)).trans (neg_le_abs u)
      · exact (le_of_lt hgt).trans (le_abs_self u)
    have hpow : 16 * m * q * nOrig ≤ 2 ^ R := hR_eq ▸ Nat.lt_two_pow_self.le
    refine (measureReal_mono hsub).trans ((gaussianReal_abs_ge_le_two_pow hR_ge2).trans ?_)
    have hpow_r : (16 * (m : ℝ) * (q : ℝ) * (nOrig : ℝ)) ≤ (2 : ℝ) ^ R := by exact_mod_cast hpow
    exact one_div_le_one_div_of_le (by positivity) hpow_r
  -- For `u ∈ box1 \ B`, bound `f u ≤ f (kBest / H) + 5 / (32 * q * nOrig)`.
  have hf_good : ∀ u ∈ box1 \ B,
      f u ≤ f ((Rat.divInt kBest (H : ℤ) : ℚ) : ℝ) + 5 / (32 * (q : ℝ) * (nOrig : ℝ)) := by
    intro u ⟨hu_box, hu_nB⟩
    set k : ℤ := ⌊u * (H : ℝ)⌋
    have hk_mem : k ∈ derandIntGrid R H := by
      refine mem_derandIntGrid_of_bounds ?_ ?_
      · have h1 : -((R * H : ℕ) : ℝ) ≤ u * (H : ℝ) := by
          push_cast; nlinarith [hu_box.1]
        have h2 : ((-((R * H : ℕ) : ℤ) : ℤ) : ℝ) ≤ u * (H : ℝ) := by
          simpa only [Int.cast_neg, Int.cast_natCast] using h1
        exact Int.le_floor.mpr h2
      · have h1 : u * (H : ℝ) ≤ ((R * H : ℕ) : ℝ) := by
          push_cast; nlinarith [hu_box.2]
        have h2 : (k : ℝ) ≤ ((R * H : ℕ) : ℝ) := (Int.floor_le _).trans h1
        exact_mod_cast h2
    have hdist : |u - ((Rat.divInt k (H : ℤ) : ℚ) : ℝ)| ≤ 1 / (H : ℝ) := by
      rw [Rat.cast_divInt, Int.cast_natCast]
      have hlo := Int.floor_le (u * (H : ℝ))
      have hhi := Int.lt_floor_add_one (u * (H : ℝ))
      rw [abs_le]
      have hdiv_le : (k : ℝ) / (H : ℝ) ≤ u := (div_le_iff₀ hH_pos).mpr hlo
      have hu_lt : u < (k : ℝ) / (H : ℝ) + 1 / (H : ℝ) := by
        rw [← add_div, lt_div_iff₀ hH_pos]; exact hhi
      exact ⟨by linarith, by linarith⟩
    have hvar : f u - f ((Rat.divInt k (H : ℤ) : ℚ) : ℝ) ≤ 1 / (32 * (q : ℝ) * (nOrig : ℝ)) := by
      have hlist_var : ∀ L : List (List (List ℚ × ℚ)),
          (∀ cl ∈ L, cl.length ≤ d ∧ ∀ p ∈ cl, p.1.length = nRem + 1 ∧
            u ∉ sharpBadInterval invEta p) →
          (L.map fun cl => (stdGaussian (EuclideanSpace ℝ (Fin nRem))).real
              {y | ∀ p ∈ cl, (p.2 : ℝ) - ((p.1.headD 0 : ℚ) : ℝ) * u <
                ⟪ratVecToEuclidean nRem p.1.tail, y⟫}).sum -
            (L.map fun cl => (stdGaussian (EuclideanSpace ℝ (Fin nRem))).real
              {y | ∀ p ∈ cl, (p.2 : ℝ) -
                ((p.1.headD 0 : ℚ) : ℝ) * ((Rat.divInt k (H : ℤ) : ℚ) : ℝ) <
                ⟪ratVecToEuclidean nRem p.1.tail, y⟫}).sum ≤
            ((L.length * d : ℕ) : ℝ) * (1 / (invEta : ℝ) + (invEta : ℝ) ^ 2 / (H : ℝ)) := by
        intro L hL
        induction L with
        | nil => simp
        | cons cl cs ih =>
          have hcl := hL cl List.mem_cons_self
          have hcs := ih fun c hc => hL c (List.mem_cons_of_mem _ hc)
          simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul, Nat.cast_add]
          set A : Set (EuclideanSpace ℝ (Fin nRem)) :=
            {y | ∀ p ∈ cl, (p.2 : ℝ) - ((p.1.headD 0 : ℚ) : ℝ) * u <
              ⟪ratVecToEuclidean nRem p.1.tail, y⟫}
          set A' : Set (EuclideanSpace ℝ (Fin nRem)) :=
            {y | ∀ p ∈ cl, (p.2 : ℝ) -
              ((p.1.headD 0 : ℚ) : ℝ) * ((Rat.divInt k (H : ℤ) : ℚ) : ℝ) <
              ⟪ratVecToEuclidean nRem p.1.tail, y⟫}
          have hcl_diff : (stdGaussian (EuclideanSpace ℝ (Fin nRem))).real A -
              (stdGaussian (EuclideanSpace ℝ (Fin nRem))).real A' ≤
              (d : ℝ) * (1 / (invEta : ℝ) + (invEta : ℝ) ^ 2 / (H : ℝ)) := by
            have hA_sub : A ⊆ A' ∪ (A \ A') := fun y hy =>
              if hy' : y ∈ A' then Or.inl hy' else Or.inr ⟨hy, hy'⟩
            have hstep_union : (stdGaussian (EuclideanSpace ℝ (Fin nRem))).real A -
                (stdGaussian (EuclideanSpace ℝ (Fin nRem))).real A' ≤
                (stdGaussian (EuclideanSpace ℝ (Fin nRem))).real (A \ A') := by
              have hle :=
                (measureReal_mono (h₂ := measure_ne_top (stdGaussian _) _) hA_sub).trans
                  (measureReal_union_le A' (A \ A'))
              linarith
            have hdiff_sub : A \ A' ⊆ ⋃ p ∈ cl.toFinset,
                ({y : EuclideanSpace ℝ (Fin nRem) |
                  (p.2 : ℝ) - ((p.1.headD 0 : ℚ) : ℝ) * u <
                    ⟪ratVecToEuclidean nRem p.1.tail, y⟫} \
                {y : EuclideanSpace ℝ (Fin nRem) |
                  (p.2 : ℝ) - ((p.1.headD 0 : ℚ) : ℝ) * ((Rat.divInt k (H : ℤ) : ℚ) : ℝ) <
                    ⟪ratVecToEuclidean nRem p.1.tail, y⟫}) := by
              intro y ⟨hyA, hyA'⟩
              simp only [A', Set.mem_ofPred_eq, not_forall, not_lt] at hyA'
              obtain ⟨p, hp, hple⟩ := hyA'
              exact Set.mem_iUnion₂.mpr ⟨p, List.mem_toFinset.mpr hp, hyA p hp, not_lt.mpr hple⟩
            refine hstep_union.trans
              ((measureReal_mono (h₂ := measure_ne_top (stdGaussian _) _) hdiff_sub).trans
                ((measureReal_biUnion_finset_le _ _).trans ?_))
            calc ∑ p ∈ cl.toFinset, _
                ≤ ∑ _p ∈ cl.toFinset, (1 / (invEta : ℝ) + (invEta : ℝ) ^ 2 / (H : ℝ)) :=
                  Finset.sum_le_sum fun p hp =>
                    have hp' := hcl.2 p (List.mem_toFinset.mp hp)
                    halfspace_step_prob_diff_le hEta_ge2 hH_ge_Eta p hp'.1 hdist hp'.2
              _ = (cl.toFinset.card : ℝ) * (1 / (invEta : ℝ) + (invEta : ℝ) ^ 2 / (H : ℝ)) := by
                  rw [Finset.sum_const, nsmul_eq_mul]
              _ ≤ (d : ℝ) * (1 / (invEta : ℝ) + (invEta : ℝ) ^ 2 / (H : ℝ)) := by
                  have hcard : (cl.toFinset.card : ℝ) ≤ (d : ℝ) := by
                    exact_mod_cast (List.toFinset_card_le cl).trans hcl.1
                  exact mul_le_mul_of_nonneg_right hcard (by positivity)
          linarith
      have hcur_ok : ∀ cl ∈ curClauses, cl.length ≤ d ∧ ∀ p ∈ cl, p.1.length = nRem + 1 ∧
          u ∉ sharpBadInterval invEta p := fun cl hcl =>
        ⟨hcl_len cl hcl, fun p hp => ⟨hp_len cl hcl p hp, fun hmem =>
          hu_nB (Set.mem_iUnion₂.mpr ⟨p,
            List.mem_toFinset.mpr (List.mem_flatten.mpr ⟨cl, hcl, hp⟩), hmem⟩)⟩⟩
      refine (hlist_var curClauses hcur_ok).trans ?_
      have hterm1 : ((m * d : ℕ) : ℝ) * (1 / (invEta : ℝ)) ≤ 1 / (64 * (q : ℝ) * (nOrig : ℝ)) := by
        dsimp only [invEta]; push_cast
        have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
        have hEq : (m : ℝ) * (d : ℝ) * (1 / (64 * (m : ℝ) * (m : ℝ) * (d : ℝ) * (q : ℝ) *
            (nOrig : ℝ))) = 1 / (64 * (q : ℝ) * (nOrig : ℝ)) / (m : ℝ) := by
          field_simp [hm_pos.ne', hd_pos.ne', hq_pos.ne', hn_pos.ne']
        rw [hEq, div_le_iff₀ hm_pos]
        nlinarith [show (0 : ℝ) < 1 / (64 * (q : ℝ) * (nOrig : ℝ)) by positivity]
      have hterm2 : ((m * d : ℕ) : ℝ) * ((invEta : ℝ) ^ 2 / (H : ℝ)) =
          1 / (64 * (q : ℝ) * (nOrig : ℝ)) := by
        rw [hH_eq]; push_cast
        field_simp [hm_pos.ne', hd_pos.ne', hq_pos.ne', hn_pos.ne', hEta_pos.ne']
      have h64 : 1 / (64 * (q : ℝ) * (nOrig : ℝ)) + 1 / (64 * (q : ℝ) * (nOrig : ℝ)) =
          1 / (32 * (q : ℝ) * (nOrig : ℝ)) := by field_simp [hq_pos.ne', hn_pos.ne']; ring
      linarith [mul_add ((m * d : ℕ) : ℝ) (1 / (invEta : ℝ)) ((invEta : ℝ) ^ 2 / (H : ℝ)), h64]
    have hscore_le : approxClauseScore d curClauses H invDelta k ≤
        approxClauseScore d curClauses H invDelta kBest :=
      (foldl_max_spec _ (derandIntGrid R H) 0).2.2 k hk_mem
    have hscore_le_r : (approxClauseScore d curClauses H invDelta k : ℝ) ≤
        (approxClauseScore d curClauses H invDelta kBest : ℝ) := by exact_mod_cast hscore_le
    have hq1 := (abs_le.mp (hquad k)).1
    have hq2 := (abs_le.mp (hquad kBest)).2
    have h532 : 1 / (32 * (q : ℝ) * (nOrig : ℝ)) + 1 / (16 * (q : ℝ) * (nOrig : ℝ)) +
        1 / (16 * (q : ℝ) * (nOrig : ℝ)) = 5 / (32 * (q : ℝ) * (nOrig : ℝ)) := by
      field_simp [hq_pos.ne', hn_pos.ne']; ring
    linarith [hvar, hscore_le_r, hq1, hq2, h532]
  -- Integrate `f` over `ℝ = (box1 \ B) ∪ B ∪ box1ᶜ`.
  have hf_int : Integrable f (gaussianReal 0 1) := by
    have haux : ∀ L : List (List (List ℚ × ℚ)),
        Integrable (fun u : ℝ => (L.map fun cl =>
          (stdGaussian (EuclideanSpace ℝ (Fin nRem))).real
            {y | ∀ p ∈ cl, (p.2 : ℝ) - ((p.1.headD 0 : ℚ) : ℝ) * u <
              ⟪ratVecToEuclidean nRem p.1.tail, y⟫}).sum) (gaussianReal 0 1) := fun L => by
      induction L with
      | nil => simp
      | cons c cs ih =>
        exact ((clauseProb_fubini nRem c).1.add ih).congr (ae_of_all _ fun _ => by simp)
    exact haux curClauses
  have hf_le_m : ∀ u : ℝ, f u ≤ (m : ℝ) := fun u => by
    have haux : ∀ L : List (List (List ℚ × ℚ)),
        (L.map fun cl => (stdGaussian (EuclideanSpace ℝ (Fin nRem))).real
          {y | ∀ p ∈ cl, (p.2 : ℝ) - ((p.1.headD 0 : ℚ) : ℝ) * u <
            ⟪ratVecToEuclidean nRem p.1.tail, y⟫}).sum ≤ (L.length : ℝ) := fun L => by
      induction L with
      | nil => simp
      | cons c cs ih =>
        simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
        linarith [measureReal_le_one (μ := stdGaussian (EuclideanSpace ℝ (Fin nRem)))
          (s := {y | ∀ p ∈ c, (p.2 : ℝ) - ((p.1.headD 0 : ℚ) : ℝ) * u <
            ⟪ratVecToEuclidean nRem p.1.tail, y⟫})]
    exact haux curClauses
  set Gset : Set ℝ := box1 \ B
  have hG_meas : MeasurableSet Gset := hbox1_meas.diff hB_meas
  have hsplit_int : ∫ u : ℝ, f u ∂(gaussianReal 0 1) =
      (∫ u in Gset, f u ∂(gaussianReal 0 1)) + (∫ u in Gsetᶜ, f u ∂(gaussianReal 0 1)) :=
    (integral_add_compl hG_meas hf_int).symm
  have hG_bound : ∫ u in Gset, f u ∂(gaussianReal 0 1) ≤
      f ((Rat.divInt kBest (H : ℤ) : ℚ) : ℝ) + 5 / (32 * (q : ℝ) * (nOrig : ℝ)) := by
    set C : ℝ := f ((Rat.divInt kBest (H : ℤ) : ℚ) : ℝ) + 5 / (32 * (q : ℝ) * (nOrig : ℝ))
    have hC_nn : 0 ≤ C := by
      dsimp only [C]
      rw [hf_at_rat kBest]
      exact add_nonneg (gaussianConjunctionExpect_nonneg _ _) (by positivity)
    calc ∫ u in Gset, f u ∂(gaussianReal 0 1)
        ≤ ∫ _u in Gset, C ∂(gaussianReal 0 1) :=
          setIntegral_mono_on hf_int.integrableOn (integrableOn_const (measure_ne_top _ _))
            hG_meas hf_good
      _ = (gaussianReal 0 1).real Gset * C := by rw [setIntegral_const, smul_eq_mul]
      _ ≤ 1 * C := mul_le_mul_of_nonneg_right measureReal_le_one hC_nn
      _ = C := one_mul C
  have hGc_bound : ∫ u in Gsetᶜ, f u ∂(gaussianReal 0 1) ≤
      1 / (8 * (q : ℝ) * (nOrig : ℝ)) := by
    have hGc_sub : Gsetᶜ ⊆ box1ᶜ ∪ B := fun u hu => by
      simp only [Gset, Set.mem_compl_iff, Set.mem_sdiff, not_and, not_not] at hu
      exact if hb : u ∈ box1 then Or.inr (hu hb) else Or.inl hb
    have hGc_prob : (gaussianReal 0 1).real Gsetᶜ ≤
        1 / (8 * (m : ℝ) * (q : ℝ) * (nOrig : ℝ)) := by
      have h1 := (measureReal_mono (h₂ := measure_ne_top (gaussianReal 0 1) _) hGc_sub).trans
        (measureReal_union_le box1ᶜ B)
      have h16 : 1 / (16 * (m : ℝ) * (q : ℝ) * (nOrig : ℝ)) +
          1 / (16 * (m : ℝ) * (q : ℝ) * (nOrig : ℝ)) =
          1 / (8 * (m : ℝ) * (q : ℝ) * (nOrig : ℝ)) := by
        field_simp [hm_pos.ne', hq_pos.ne', hn_pos.ne']; ring
      linarith [hbox1_compl, hB_prob, h16]
    calc ∫ u in Gsetᶜ, f u ∂(gaussianReal 0 1)
        ≤ ∫ _u in Gsetᶜ, (m : ℝ) ∂(gaussianReal 0 1) :=
          setIntegral_mono_on hf_int.integrableOn (integrableOn_const (measure_ne_top _ _))
            hG_meas.compl (fun u _ => hf_le_m u)
      _ = (gaussianReal 0 1).real Gsetᶜ * (m : ℝ) := by rw [setIntegral_const, smul_eq_mul]
      _ ≤ (1 / (8 * (m : ℝ) * (q : ℝ) * (nOrig : ℝ))) * (m : ℝ) :=
          mul_le_mul_of_nonneg_right hGc_prob hm_pos.le
      _ = 1 / (8 * (q : ℝ) * (nOrig : ℝ)) := by
          field_simp [hm_pos.ne', hq_pos.ne', hn_pos.ne']
  rw [gaussianConjunctionExpect_succ, ← hf_at_rat kBest, hsplit_int]
  have h932 : 5 / (32 * (q : ℝ) * (nOrig : ℝ)) + 1 / (8 * (q : ℝ) * (nOrig : ℝ)) =
      9 / (32 * (q : ℝ) * (nOrig : ℝ)) := by field_simp [hq_pos.ne', hn_pos.ne']; ring
  linarith [hG_bound, hGc_bound, h932]

/-! ### Main derandomisation theorem -/

/-- **Deterministic polynomial-time Gaussian halfspace-conjunction derandomisation**:
for every fixed clause width `d`, there exists a deterministic polynomial-time algorithm
(with unary `n` and unary `q`) that, given `m` conjunctions of `d` rational halfspaces in `ℝ^n`,
outputs `x* ∈ ℚ^n` satisfying at least `gaussianConjunctionExpect n clauses - 1 / q`
conjunctions. -/
theorem derandGaussian_polyTime (d : ℕ) :
    ∃ alg : (ℕ × List (List (List ℚ × ℚ)) × ℕ) → List ℚ,
      ComputableInPolyTime alg encDerandGaussianInput (encList encRat) ∧
      ∀ (n : ℕ) (clauses : List (List (List ℚ × ℚ))) (q : ℕ),
        1 ≤ n → 1 ≤ q →
        (∀ cl ∈ clauses, cl.length = d ∧ ∀ p ∈ cl, p.1.length = n) →
        (alg (n, clauses, q)).length = n ∧
        gaussianConjunctionExpect n clauses - 1 / (q : ℝ) ≤
          gaussianConjunctionCount n clauses (alg (n, clauses, q)) := by
  refine ⟨derandGaussianAlg d, computableInPolyTime_derandGaussianAlg d,
    fun n clauses q hn hq hclauses => ?_⟩
  by_cases htriv : clauses.isEmpty || decide (d = 0)
  · simp only [derandGaussianAlg, htriv, ↓reduceIte, List.length_replicate, true_and]
    have hq_nn : (0 : ℝ) ≤ 1 / (q : ℝ) := by positivity
    rcases Bool.or_eq_true_iff.mp htriv with hempty | hd0
    · have hnil : clauses = [] := List.isEmpty_iff.mp hempty
      subst hnil; simp
    · have hd_eq : d = 0 := decide_eq_true_eq.mp hd0
      subst hd_eq
      have hall_nil : ∀ cl ∈ clauses, cl = [] := fun cl hcl =>
        List.eq_nil_of_length_eq_zero (hclauses cl hcl).1
      have hE : ∀ L : List (List (List ℚ × ℚ)), (∀ cl ∈ L, cl = []) →
          gaussianConjunctionExpect n L = (L.length : ℝ) := fun L hL => by
        induction L with
        | nil => simp
        | cons cl rest ih =>
          obtain rfl : cl = [] := hL cl List.mem_cons_self
          rw [gaussianConjunctionExpect_cons, ih fun c hc => hL c (List.mem_cons_of_mem _ hc)]
          simp [Measure.real_def, add_comm]
      have hC : ∀ L : List (List (List ℚ × ℚ)), (∀ cl ∈ L, cl = []) →
          gaussianConjunctionCount n L (List.replicate n 0) = (L.length : ℝ) := fun L hL => by
        induction L with
        | nil => simp
        | cons cl rest ih =>
          obtain rfl : cl = [] := hL cl List.mem_cons_self
          rw [gaussianConjunctionCount_cons, ih fun c hc => hL c (List.mem_cons_of_mem _ hc)]
          simp [add_comm]
      rw [hE clauses hall_nil, hC clauses hall_nil]; linarith
  · have htriv_false : (clauses.isEmpty || decide (d = 0)) = false :=
      Bool.eq_false_iff.mpr htriv
    have hm : 1 ≤ clauses.length := List.length_pos_iff.mpr (fun h => htriv (by simp [h]))
    have hd : 1 ≤ d := by have : d ≠ 0 := fun h => htriv (by simp [h]); omega
    simp only [derandGaussianAlg, htriv_false, Bool.false_eq_true, ↓reduceIte]
    set params := derandGridParams d n clauses.length q
    set H := params.2.1
    have hloop : ∀ t : ℕ, t ≤ n →
        let ks := (derandCoordStep d (n, clauses, q))^[t] []
        ks.length = t ∧
        gaussianConjunctionExpect n clauses - (t : ℝ) * (9 / (32 * (q : ℝ) * (n : ℝ))) ≤
          gaussianConjunctionExpect (n - t) (updateClausesByInts H ks clauses) := by
      intro t ht
      induction t with
      | zero => simp
      | succ t ih =>
        obtain ⟨hlen_t, hexp_t⟩ := ih (by omega)
        set ks := (derandCoordStep d (n, clauses, q))^[t] []
        rw [Function.iterate_succ_apply']
        dsimp only [derandCoordStep]
        set curClauses := updateClausesByInts H ks clauses
        set kBest : ℤ := (derandIntGrid params.1 params.2.1).foldl _ (0 : ℤ)
        refine ⟨by rw [List.length_append, List.length_singleton, hlen_t], ?_⟩
        have hcur_m : 1 ≤ curClauses.length := by simp [curClauses, hm]
        have hcur_cl : ∀ cl ∈ curClauses, cl.length ≤ d := by
          rintro cl hcl; simp only [curClauses, updateClausesByInts, List.mem_map] at hcl
          rcases hcl with ⟨cl0, hcl0, rfl⟩; simp [(hclauses cl0 hcl0).1]
        have hcur_p : ∀ cl ∈ curClauses, ∀ p ∈ cl, p.1.length = (n - (t + 1)) + 1 := by
          rintro cl hcl p hp; simp only [curClauses, updateClausesByInts, List.mem_map] at hcl
          rcases hcl with ⟨cl0, hcl0, rfl⟩; simp only [List.mem_map] at hp
          rcases hp with ⟨p0, hp0, rfl⟩
          simp only [List.length_drop, (hclauses cl0 hcl0).2 p0 hp0, hlen_t]; omega
        have hsnoc : updateClausesByInts H (ks ++ [kBest]) clauses =
            stepOneCoord (Rat.divInt kBest (H : ℤ)) curClauses :=
          updateClausesByInts_snoc fun cl hcl p hp => by
            rw [hlen_t, (hclauses cl hcl).2 p hp]; omega
        have hloss := one_step_derand_loss (nRem := n - (t + 1)) hd hn hq hcur_m hcur_cl hcur_p
        have hcur_len : curClauses.length = clauses.length := updateClausesByInts_length _ _ _
        dsimp only at hloss; rw [hcur_len] at hloss
        rw [show n - t = (n - (t + 1)) + 1 by omega] at hexp_t
        rw [hsnoc, show ((t + 1 : ℕ) : ℝ) * (9 / (32 * (q : ℝ) * (n : ℝ))) =
          (t : ℝ) * (9 / (32 * (q : ℝ) * (n : ℝ))) + 9 / (32 * (q : ℝ) * (n : ℝ)) by
            push_cast; ring]
        linarith only [hexp_t, hloss]
    obtain ⟨hlen_n, hexp_n⟩ := hloop n le_rfl
    set ksN := (derandCoordStep d (n, clauses, q))^[n] []
    refine ⟨by simpa using hlen_n, ?_⟩
    rw [Nat.sub_self, gaussianConjunctionExpect_zero,
      gaussianConjunctionCount_zero_updateClausesByInts hlen_n (fun cl hcl => (hclauses cl hcl).2)]
      at hexp_n
    have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
    have hq_pos : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr hq
    have h932 : (n : ℝ) * (9 / (32 * (q : ℝ) * (n : ℝ))) ≤ 1 / (q : ℝ) := by
      have hEq : (n : ℝ) * (9 / (32 * (q : ℝ) * (n : ℝ))) = (9 / 32 : ℝ) * (1 / (q : ℝ)) := by
        field_simp [hn_pos.ne', hq_pos.ne']
      rw [hEq]
      nlinarith [show (0 : ℝ) < 1 / (q : ℝ) by positivity]
    linarith

end CslibFrontier.Foundations.Probability.Gaussian
