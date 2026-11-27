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
public import CslibFrontier.Foundations.Probability.Gaussian.RationalProjection

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Rat
import CslibFrontier.Foundations.Probability.Gaussian.ConvexCap
import CslibFrontier.Foundations.Probability.Gaussian.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.List.GetD
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Polynomial-Time Rational Quadrature for Gaussian Halfspace Conjunctions

This module develops deterministic low-dimensional Gaussian grid quadrature for estimating the
standard Gaussian probability `Pr_{x ~ N(0, I_N)}[∀ (a, b) ∈ cl, ⟪a, x⟫ > b]` of a conjunction of
at most `d` rational halfspaces in `ℝ^N` to additive error `1 / invDelta` in time polynomial in the
encoding length of `cl` and unary `invDelta` (for every fixed constant `d`).

## Main definitions

* `CslibFrontier.Foundations.Probability.Gaussian.evalGridSum`,
  `CslibFrontier.Foundations.Probability.Gaussian.evalGridSumLe`: recursive `k`-fold
  integer-weighted grid evaluation for halfspace conjunctions.
* `CslibFrontier.Foundations.Probability.Gaussian.approxClauseProb`: deterministic polynomial-time
  rational estimator for the
  Gaussian measure of a `d`-conjunction of rational halfspaces.

## Main results

* `CslibFrontier.Foundations.Probability.Gaussian.evalGridSum_eq_sum_fin`: exact Finset-sum
  characterization of
  `evalGridSum`.
* `CslibFrontier.Foundations.Probability.Gaussian.computableInPolyTime_approxClauseProb`:
  polynomial-time computability of
  `approxClauseProb d` for every fixed constant `d`.
* `CslibFrontier.Foundations.Probability.Gaussian.abs_approxClauseProb_sub_le`: additive `1 /
  invDelta` accuracy of
  `approxClauseProb` under standard Lean axioms.
-/

public section

open MeasureTheory ProbabilityTheory Real Set Finset BigOperators Turing.MultiTapeTM
open scoped NNReal ENNReal RealInnerProductSpace

namespace CslibFrontier.Foundations.Probability.Gaussian

/-! ### Recursive `k`-dimensional integer-weighted grid summation and `approxClauseProb` -/

/-- Recursive `k`-dimensional integer-weighted grid sum over 1D grid points `(u_m, w_m)`:
evaluates `∑_z (if ∀ (cs, b) ∈ remCl, b < ∑_s cs[s] * u_{z_s} then ∏ w_{z_s} else 0)`. -/
@[expose] def evalGridSum : ℕ → List (ℚ × ℕ) → List (List ℚ × ℚ) → ℕ
  | 0, _, remCl =>
    if remCl.all fun p => decide (p.2 < 0) then 1 else 0
  | k + 1, gridPts, remCl =>
    (gridPts.map fun pt =>
      pt.2 * evalGridSum k gridPts
        (remCl.map fun p => (p.1.tail, p.2 - p.1.headD 0 * pt.1))).sum

/-- Dispatch wrapper evaluating `evalGridSum k` for any runtime `k ≤ d`. -/
@[expose] def evalGridSumLe : ℕ → ℕ → List (ℚ × ℕ) → List (List ℚ × ℚ) → ℕ
  | 0, _, gridPts, remCl => evalGridSum 0 gridPts remCl
  | d + 1, k, gridPts, remCl =>
    if k = d + 1 then evalGridSum (d + 1) gridPts remCl
    else evalGridSumLe d k gridPts remCl

@[simp]
theorem evalGridSum_zero (gridPts : List (ℚ × ℕ)) (remCl : List (List ℚ × ℚ)) :
    evalGridSum 0 gridPts remCl =
      if remCl.all fun p => decide (p.2 < 0) then 1 else 0 := rfl

theorem evalGridSumLe_eq_of_le {d k : ℕ} (hk : k ≤ d)
    (gridPts : List (ℚ × ℕ)) (remCl : List (List ℚ × ℚ)) :
    evalGridSumLe d k gridPts remCl = evalGridSum k gridPts remCl := by
  induction d with
  | zero =>
    have h0 : k = 0 := Nat.eq_zero_of_le_zero hk
    subst h0; rfl
  | succ d ih =>
    unfold evalGridSumLe
    split_ifs with h
    · subst h; rfl
    · exact ih (by omega)

private theorem list_sum_eq_sum_fin_real {α : Type*} (l : List α) (f : α → ℝ) :
    (l.map f).sum = ∑ i : Fin l.length, f l[i] := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.map_cons, List.sum_cons, ih]
    exact (Fin.sum_univ_succ fun i : Fin (a :: t).length => f (a :: t)[i]).symm

theorem evalGridSum_eq_sum_fin : ∀ (k : ℕ) (gridPts : List (ℚ × ℕ))
    (remCl : List (List ℚ × ℚ)),
    (evalGridSum k gridPts remCl : ℝ) =
      ∑ z : Fin k → Fin gridPts.length,
        if ∀ p ∈ remCl, (p.2 : ℝ) <
            ∑ s : Fin k, ((p.1.getD s.1 0 : ℚ) : ℝ) * ((gridPts[z s]).1 : ℝ)
        then ((∏ s : Fin k, (gridPts[z s]).2 : ℕ) : ℝ) else 0 := by
  intro k
  induction k with
  | zero =>
    intro gridPts remCl
    simp only [evalGridSum_zero, Fin.sum_univ_zero, Fin.prod_univ_zero, Nat.cast_one]
    have h1 : (remCl.all fun p => decide (p.2 < 0)) = true ↔
        ∀ p ∈ remCl, (p.2 : ℝ) < 0 := by
      simp only [List.all_eq_true, decide_eq_true_eq]
      exact ⟨fun h p hp => by exact_mod_cast h p hp, fun h p hp => by exact_mod_cast h p hp⟩
    have hcard : (Finset.univ : Finset (Fin 0 → Fin gridPts.length)) = {Fin.elim0} := by
      ext z
      simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
      exact Subsingleton.elim z Fin.elim0
    rw [hcard, Finset.sum_singleton]
    split_ifs
    · norm_num
    · rename_i ha hb; exact absurd (h1.mp ha) hb
    · rename_i ha hb; exact absurd (h1.mpr hb) ha
    · norm_num
  | succ k ih =>
    intro gridPts remCl
    simp only [evalGridSum]
    rw [Nat.cast_list_sum, List.map_map, list_sum_eq_sum_fin_real]
    let e := (Fin.consEquiv (fun _ : Fin (k + 1) => Fin gridPts.length)).symm
    rw [← Equiv.sum_comp e.symm, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun m _ => ?_
    simp only [Function.comp_apply, Nat.cast_mul, ih, Finset.mul_sum]
    refine Finset.sum_congr rfl fun z _ => ?_
    simp only [e, Equiv.symm_symm, Fin.consEquiv_apply, Fin.prod_univ_succ, Fin.cons_zero,
      Fin.cons_succ, Fin.sum_univ_succ, Nat.cast_mul]
    have hiff : (∀ p ∈ remCl.map (fun p => (p.1.tail, p.2 - p.1.headD 0 * (gridPts[m]).1)),
          (p.2 : ℝ) < ∑ s : Fin k, ((p.1.getD s.1 0 : ℚ) : ℝ) * ((gridPts[z s]).1 : ℝ)) ↔
        (∀ p ∈ remCl, (p.2 : ℝ) < ((p.1.getD 0 0 : ℚ) : ℝ) * ((gridPts[m]).1 : ℝ) +
          ∑ s : Fin k, ((p.1.getD (s.1 + 1) 0 : ℚ) : ℝ) * ((gridPts[z s]).1 : ℝ)) := by
      simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
      refine forall₂_congr fun p _ => ?_
      have hhead : (p.1.headD 0 : ℝ) = (p.1.getD 0 0 : ℝ) := by cases p.1 <;> simp
      have htail : ∀ s : Fin k, (p.1.tail.getD s.1 0 : ℝ) = (p.1.getD (s.1 + 1) 0 : ℝ) := by
        intro s; cases p.1 <;> simp
      simp only [Rat.cast_sub, Rat.cast_mul, hhead, htail, sub_lt_iff_lt_add']
    split_ifs
    · rfl
    · rename_i ha hb; exact absurd (hiff.mp ha) hb
    · rename_i ha hb; exact absurd (hiff.mpr hb) ha
    · rw [mul_zero]

/-- Deterministic rational quadrature estimator for the Gaussian probability of a conjunction of
at most `d` rational halfspaces `(a_j, b_j)` to additive error `1 / invDelta`. -/
def approxClauseProb (d : ℕ) (cl : List (List ℚ × ℚ)) (invDelta : ℕ) : ℚ :=
  let d1 : ℕ := max 1 d
  let invD : ℕ := max 1 invDelta
  let R0 : ℕ := Nat.log 2 (32 * d1 * invD) + 3
  let H0 : ℕ := 64 * d1 * d1 * R0 * R0 * invD
  let Bexp : ℕ := Nat.log 2 (64 * d1 * R0 * invD) + 2
  let Kexp : ℕ := 3 * R0 * R0 + 2 * Bexp + 2
  let Wscale : ℕ := 64 * d1 * R0 * invD
  let Msqrt : ℕ := 4 * d1 * invD
  let basis := ratGramSchmidtBounded d ((cl.take d).map Prod.fst)
  let rVals := basis.map fun e => ratSqrtUpper (ratDot e e) Msqrt
  let scaledBasis := basis.zip rVals
  let remCl := (cl.take d).map fun p =>
    (scaledBasis.map fun er => (ratDot p.1 er.1 / ratDot er.1 er.1) * er.2, p.2)
  let Glen : ℕ := 2 * R0 * H0
  let gridPts : List (ℚ × ℕ) := (List.range Glen).map fun (m : ℕ) =>
    let u : ℚ := -((R0 : ℚ)) + (m : ℚ) / (H0 : ℚ)
    let w : ℕ := (Rat.floor ((Wscale : ℚ) * ratExpNeg (u * u / 2) Kexp)).toNat
    (u, w)
  let Ntot : ℕ := evalGridSumLe d basis.length gridPts remCl
  let W1 : ℕ := (gridPts.map Prod.snd).sum
  let Wtot : ℕ := W1 ^ basis.length
  Rat.divInt (Ntot : ℤ) (Wtot : ℤ)

private theorem computableInPolyTime_evalGridSum (k : ℕ) :
    ComputableInPolyTime
      (fun p : List (ℚ × ℕ) × List (List ℚ × ℚ) => evalGridSum k p.1 p.2)
      (encPair (encList (encPair encRat encNat)) (encList (encPair (encList encRat) encRat)))
      encNat := by
  let ePt := encPair encRat encNat
  let eGrid := encList ePt
  let eHalf := encPair (encList encRat) encRat
  let eCl := encList eHalf
  let eIn := encPair eGrid eCl
  induction k with
  | zero =>
    have hcl := ComputableInPolyTime.snd eGrid eCl
    have hall := ComputableInPolyTime.allWith
      (encA := eHalf) (encP := encBool)
      (ComputableInPolyTime.rat_lt'
        ((ComputableInPolyTime.snd (encList encRat) encRat).comp
          (ComputableInPolyTime.snd encBool eHalf))
        (ComputableInPolyTime.const (0 : ℚ)))
      (ComputableInPolyTime.const false) hcl
    exact (hall.ite' (ComputableInPolyTime.const 1) (ComputableInPolyTime.const 0)).of_enc_eq
      fun _ => rfl
  | succ k ih =>
    have hgrid := ComputableInPolyTime.fst eGrid eCl
    have hcl := ComputableInPolyTime.snd eGrid eCl
    have hbody : ComputableInPolyTime
        (fun x : (List (ℚ × ℕ) × List (List ℚ × ℚ)) × (ℚ × ℕ) =>
          x.2.2 * evalGridSum k x.1.1
            (x.1.2.map fun p => (p.1.tail, p.2 - p.1.headD 0 * x.2.1)))
        (encPair eIn ePt) encNat := by
      let eStep := encPair eIn ePt
      have hx1 := ComputableInPolyTime.fst eIn ePt
      have hpt := ComputableInPolyTime.snd eIn ePt
      have hgrid' := hgrid.comp hx1
      have hcl' := hcl.comp hx1
      have hu := (ComputableInPolyTime.fst encRat encNat).comp hpt
      have hw := (ComputableInPolyTime.snd encRat encNat).comp hpt
      have hrem_step : ComputableInPolyTime
          (fun y : ℚ × (List ℚ × ℚ) => (y.2.1.tail, y.2.2 - y.2.1.headD 0 * y.1))
          (encPair encRat eHalf) eHalf := by
        have hpar := ComputableInPolyTime.fst encRat eHalf
        have hp := ComputableInPolyTime.snd encRat eHalf
        have hp1 := (ComputableInPolyTime.fst (encList encRat) encRat).comp hp
        have hp2 := (ComputableInPolyTime.snd (encList encRat) encRat).comp hp
        have htail := (ComputableInPolyTime.listTail encRat).comp hp1
        have hhead :=
          (ComputableInPolyTime.headD (encA := encRat) (encL := encList encRat) 0).comp hp1
        exact (htail.prod (ComputableInPolyTime.rat_sub' hp2
          (ComputableInPolyTime.rat_mul' hhead hpar))).of_enc_eq fun _ => rfl
      have hrem := ComputableInPolyTime.mapWith hrem_step hu hcl'
      have heval := ih.comp (hgrid'.prod hrem)
      exact (ComputableInPolyTime.binary_mul.comp (hw.prod heval)).of_enc_eq fun _ => rfl
    exact (ComputableInPolyTime.binary_sum.comp
      (ComputableInPolyTime.mapWithInput hgrid hbody)).of_enc_eq fun _ => rfl

private theorem computableInPolyTime_evalGridSumLe (d : ℕ) :
    ComputableInPolyTime
      (fun p : ℕ × List (ℚ × ℕ) × List (List ℚ × ℚ) => evalGridSumLe d p.1 p.2.1 p.2.2)
      (encPair encUnary (encPair (encList (encPair encRat encNat))
        (encList (encPair (encList encRat) encRat)))) encNat := by
  let eRest := encPair (encList (encPair encRat encNat))
    (encList (encPair (encList encRat) encRat))
  induction d with
  | zero =>
    exact ((computableInPolyTime_evalGridSum 0).comp
      (ComputableInPolyTime.snd encUnary eRest)).of_enc_eq fun _ => rfl
  | succ d ih =>
    have hk := ComputableInPolyTime.fst encUnary eRest
    have hrest := ComputableInPolyTime.snd encUnary eRest
    have hcond := ComputableInPolyTime.unary_beq hk (ComputableInPolyTime.const (d + 1))
    have hthen := (computableInPolyTime_evalGridSum (d + 1)).comp hrest
    refine (hcond.ite' hthen ih).of_enc_eq fun p => congrArg encNat ?_
    simp [evalGridSumLe]

/-- Single 1D grid point `(u_m, w_m)` for `approxClauseProb`. -/
private def approxGridPt (d : ℕ) (p : List (List ℚ × ℚ) × ℕ) (m : ℕ) : ℚ × ℕ :=
  let d1 := max 1 d
  let invD := max 1 p.2
  let R0 := Nat.log 2 (32 * d1 * invD) + 3
  let H0 := 64 * d1 * d1 * R0 * R0 * invD
  let Wscale := 64 * d1 * R0 * invD
  let Bexp := Nat.log 2 Wscale + 2
  let Kexp := 3 * R0 * R0 + 2 * Bexp + 2
  let u : ℚ := -((R0 : ℚ)) + (m : ℚ) / (H0 : ℚ)
  let w : ℕ := (Rat.floor ((Wscale : ℚ) * ratExpNeg (u * u / 2) Kexp)).toNat
  (u, w)

/-- `approxClauseProb d` is computable in polynomial time for every fixed constant `d` (with
`invDelta` in unary). -/
theorem computableInPolyTime_approxClauseProb (d : ℕ) :
    ComputableInPolyTime
      (fun p : List (List ℚ × ℚ) × ℕ => approxClauseProb d p.1 p.2)
      (encPair (encList (encPair (encList encRat) encRat)) encUnary) encRat := by
  let eHalf := encPair (encList encRat) encRat
  let eCl := encList eHalf
  let eIn := encPair eCl encUnary
  have hcl := ComputableInPolyTime.fst eCl encUnary
  have hinv := ComputableInPolyTime.snd eCl encUnary
  have hd1 : ComputableInPolyTime (fun _ : List (List ℚ × ℚ) × ℕ => max 1 d) eIn encUnary :=
    ComputableInPolyTime.const (max 1 d)
  have hinvD : ComputableInPolyTime (fun p : List (List ℚ × ℚ) × ℕ => max 1 p.2) eIn encUnary :=
    ComputableInPolyTime.unary_max.comp ((ComputableInPolyTime.const 1).prod hinv)
  have hR0 := ComputableInPolyTime.unary_add'
    (ComputableInPolyTime.unary_log_two.comp
      (ComputableInPolyTime.unary_mul'
        (ComputableInPolyTime.unary_mul' (ComputableInPolyTime.const 32) hd1) hinvD))
    (ComputableInPolyTime.const 3)
  have hH0 := ComputableInPolyTime.unary_mul'
    (ComputableInPolyTime.unary_mul'
      (ComputableInPolyTime.unary_mul'
        (ComputableInPolyTime.unary_mul'
          (ComputableInPolyTime.unary_mul' (ComputableInPolyTime.const 64) hd1) hd1) hR0) hR0)
    hinvD
  have hWscale := ComputableInPolyTime.unary_mul'
    (ComputableInPolyTime.unary_mul'
      (ComputableInPolyTime.unary_mul' (ComputableInPolyTime.const 64) hd1) hR0) hinvD
  have hBexp := ComputableInPolyTime.unary_add'
    (ComputableInPolyTime.unary_log_two.comp hWscale) (ComputableInPolyTime.const 2)
  have hKexp := ComputableInPolyTime.unary_add'
    (ComputableInPolyTime.unary_add'
      (ComputableInPolyTime.unary_mul'
        (ComputableInPolyTime.unary_mul' (ComputableInPolyTime.const 3) hR0) hR0)
      (ComputableInPolyTime.unary_mul' (ComputableInPolyTime.const 2) hBexp))
    (ComputableInPolyTime.const 2)
  have hMsqrt := ComputableInPolyTime.unary_mul'
    (ComputableInPolyTime.unary_mul' (ComputableInPolyTime.const 4) hd1) hinvD
  have htake := ComputableInPolyTime.listTakeWithInput hcl (ComputableInPolyTime.const d)
  have hvecs := (ComputableInPolyTime.map (ComputableInPolyTime.fst (encList encRat) encRat)).comp
    htake
  have hbasis := (computableInPolyTime_ratGramSchmidtBounded d).comp hvecs
  have hrStep : ComputableInPolyTime
      (fun y : ℕ × List ℚ => ratSqrtUpper (ratDot y.2 y.2) y.1)
      (encPair encUnary (encList encRat)) encRat := by
    have hM := ComputableInPolyTime.fst encUnary (encList encRat)
    have he := ComputableInPolyTime.snd encUnary (encList encRat)
    exact (computableInPolyTime_ratSqrtUpper.comp
      ((computableInPolyTime_ratDot.comp (he.prod he)).prod hM)).of_enc_eq fun _ => rfl
  have hrVals := ComputableInPolyTime.mapWith hrStep hMsqrt hbasis
  have hscaled := (ComputableInPolyTime.zip (encList encRat) encRat).comp (hbasis.prod hrVals)
  have hremStep : ComputableInPolyTime
      (fun y : List (List ℚ × ℚ) × (List ℚ × ℚ) =>
        (y.1.map fun er => (ratDot y.2.1 er.1 / ratDot er.1 er.1) * er.2, y.2.2))
      (encPair (encList (encPair (encList encRat) encRat)) eHalf) eHalf := by
    let eSB := encList (encPair (encList encRat) encRat)
    have hsb := ComputableInPolyTime.fst eSB eHalf
    have hq := ComputableInPolyTime.snd eSB eHalf
    have hq1 := (ComputableInPolyTime.fst (encList encRat) encRat).comp hq
    have hq2 := (ComputableInPolyTime.snd (encList encRat) encRat).comp hq
    have hinnerStep : ComputableInPolyTime
        (fun z : List ℚ × (List ℚ × ℚ) => (ratDot z.1 z.2.1 / ratDot z.2.1 z.2.1) * z.2.2)
        (encPair (encList encRat) (encPair (encList encRat) encRat)) encRat := by
      have hv := ComputableInPolyTime.fst (encList encRat) (encPair (encList encRat) encRat)
      have her := ComputableInPolyTime.snd (encList encRat) (encPair (encList encRat) encRat)
      have he1 := (ComputableInPolyTime.fst (encList encRat) encRat).comp her
      have he2 := (ComputableInPolyTime.snd (encList encRat) encRat).comp her
      exact (ComputableInPolyTime.rat_mul'
        (ComputableInPolyTime.rat_div'
          (computableInPolyTime_ratDot.comp (hv.prod he1))
          (computableInPolyTime_ratDot.comp (he1.prod he1)))
        he2).of_enc_eq fun _ => rfl
    exact ((ComputableInPolyTime.mapWith hinnerStep hq1 hsb).prod hq2).of_enc_eq fun _ => rfl
  have hremCl := ComputableInPolyTime.mapWith hremStep hscaled htake
  have hGlen := ComputableInPolyTime.unary_mul'
    (ComputableInPolyTime.unary_mul' (ComputableInPolyTime.const 2) hR0) hH0
  have hgridStep : ComputableInPolyTime
      (fun x : (List (List ℚ × ℚ) × ℕ) × ℕ => approxGridPt d x.1 x.2)
      (encPair eIn encUnary) (encPair encRat encNat) := by
    have hx := ComputableInPolyTime.fst eIn encUnary
    have hm := ComputableInPolyTime.snd eIn encUnary
    have hR0q := ComputableInPolyTime.rat_natCast.comp
      (ComputableInPolyTime.unary_to_binary.comp (hR0.comp hx))
    have hH0q := ComputableInPolyTime.rat_natCast.comp
      (ComputableInPolyTime.unary_to_binary.comp (hH0.comp hx))
    have hmq := ComputableInPolyTime.rat_natCast.comp
      (ComputableInPolyTime.unary_to_binary.comp hm)
    have hu := ComputableInPolyTime.rat_add' (ComputableInPolyTime.rat_neg' hR0q)
      (ComputableInPolyTime.rat_div' hmq hH0q)
    have hWsq := ComputableInPolyTime.rat_natCast.comp
      (ComputableInPolyTime.unary_to_binary.comp (hWscale.comp hx))
    have hu2 := ComputableInPolyTime.rat_div'
      (ComputableInPolyTime.rat_mul' hu hu) (ComputableInPolyTime.const (2 : ℚ))
    have hexp := computableInPolyTime_ratExpNeg.comp (hu2.prod (hKexp.comp hx))
    have hw := ComputableInPolyTime.intBin_toNat.comp
      (ComputableInPolyTime.rat_floor' (ComputableInPolyTime.rat_mul' hWsq hexp))
    exact (hu.prod hw).of_enc_eq fun _ => rfl
  have hgridPts := ComputableInPolyTime.mapWithInput (f := approxGridPt d)
    (ComputableInPolyTime.range.comp hGlen) hgridStep
  have hblen := (ComputableInPolyTime.length (enc := encList encRat)).comp hbasis
  have hNtot := (computableInPolyTime_evalGridSumLe d).comp (hblen.prod (hgridPts.prod hremCl))
  have hW1 := ComputableInPolyTime.binary_sum.comp
    ((ComputableInPolyTime.map (ComputableInPolyTime.snd encRat encNat)).comp hgridPts)
  have hWtot := ComputableInPolyTime.binary_pow' hW1 hblen
  exact (ComputableInPolyTime.rat_divInt'
    (ComputableInPolyTime.intBin_natCast.comp hNtot)
    (ComputableInPolyTime.intBin_natCast.comp hWtot)).of_enc_eq fun p => congrArg encRat (by
      dsimp only [approxClauseProb, approxGridPt, Function.comp_apply]; rfl)

/-! ### Additive accuracy theorem for `approxClauseProb` -/

/-- Helper bounding the 1D Riemann, Taylor, and floor-rounding error per grid interval. -/
private theorem approxClauseProb_point_err {R0 H0 Bexp Kexp Wscale : ℕ}
    (hH0 : 0 < H0) (hWs : 0 < Wscale) (hK : 3 * (R0 * R0) + 2 * Bexp + 2 ≤ Kexp)
    (m : Fin (2 * R0 * H0)) :
    let uPt : ℝ := -((R0 : ℝ)) + (m.1 : ℝ) / (H0 : ℝ)
    let uRat : ℚ := -((R0 : ℚ)) + (m.1 : ℚ) / (H0 : ℚ)
    let wInt : ℕ := (Rat.floor ((Wscale : ℚ) * ratExpNeg (uRat * uRat / 2) Kexp)).toNat
    let c_pi : ℝ := Real.sqrt (2 * Real.pi)
    |(gaussianReal 0 1).real (Ico uPt (uPt + 1 / (H0 : ℝ))) -
      ((wInt : ℝ) / (Wscale : ℝ)) / (H0 : ℝ) / c_pi| ≤
      (R0 : ℝ) / (H0 : ℝ) ^ 2 + (1 / 4 : ℝ) ^ Bexp / (H0 : ℝ) +
      (1 / (Wscale : ℝ)) / (H0 : ℝ) := by
  intro uPt uRat wInt c_pi
  have hH0_rpos : (0 : ℝ) < (H0 : ℝ) := Nat.cast_pos.mpr hH0
  have hW_pos : (0 : ℝ) < (Wscale : ℝ) := Nat.cast_pos.mpr hWs
  have hc_pi_ge : (1 : ℝ) ≤ c_pi := by
    have : (1 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
    simpa [c_pi] using Real.sqrt_le_sqrt this
  have hc_pi_pos : 0 < c_pi := by linarith
  have hu_eq : (uRat : ℝ) = uPt := by simp [uRat, uPt]
  have hu_abs : |uPt| ≤ (R0 : ℝ) := by
    have hm_le : (m.1 : ℝ) ≤ ((2 * R0 * H0 : ℕ) : ℝ) := by exact_mod_cast m.2.le
    have hG : ((2 * R0 * H0 : ℕ) : ℝ) / (H0 : ℝ) = 2 * (R0 : ℝ) := by
      push_cast; field_simp [hH0_rpos.ne']
    have h1 : -(R0 : ℝ) ≤ uPt := by
      simp only [uPt]; linarith [show (0 : ℝ) ≤ (m.1 : ℝ) / (H0 : ℝ) by positivity]
    have h2 : uPt ≤ (R0 : ℝ) := by
      simp only [uPt]
      have : (m.1 : ℝ) / (H0 : ℝ) ≤ 2 * (R0 : ℝ) := by rw [← hG]; gcongr
      linarith
    exact abs_le.mpr ⟨h1, h2⟩
  have hu2_le : ((uRat * uRat / 2 : ℚ) : ℝ) ≤ ((R0 * R0 : ℕ) : ℝ) := by
    have : ((uRat * uRat / 2 : ℚ) : ℝ) = uPt ^ 2 / 2 := by push_cast [hu_eq]; ring
    rw [this]
    have hsq : uPt ^ 2 ≤ (R0 : ℝ) ^ 2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hu_abs 2
    push_cast; nlinarith
  have hu2_nn : (0 : ℝ) ≤ ((uRat * uRat / 2 : ℚ) : ℝ) := by
    rw [show ((uRat * uRat / 2 : ℚ) : ℝ) = uPt ^ 2 / 2 by push_cast [hu_eq]; ring]
    positivity
  have htaylor := abs_ratExpNeg_sub_exp_le (T := R0 * R0) (B := Bexp) (K := Kexp)
    hu2_nn hu2_le hK
  have hfloor_err : |((wInt : ℝ) / (Wscale : ℝ)) - Real.exp (-(uPt ^ 2 / 2))| ≤
      (1 / 4 : ℝ) ^ Bexp + 1 / (Wscale : ℝ) := by
    have hexp_eq : Real.exp (-((uRat * uRat / 2 : ℚ) : ℝ)) = Real.exp (-(uPt ^ 2 / 2)) := by
      congr 1; push_cast [hu_eq]; ring
    rw [hexp_eq] at htaylor
    set r0 : ℝ := (ratExpNeg (uRat * uRat / 2) Kexp : ℝ)
    set e0 : ℝ := Real.exp (-(uPt ^ 2 / 2))
    have hclamp : |max r0 0 - e0| ≤ (1 / 4 : ℝ) ^ Bexp := by
      rcases le_or_gt 0 r0 with hr | hr
      · simpa [max_eq_left hr] using htaylor
      · rw [max_eq_right hr.le, zero_sub, abs_neg, abs_of_nonneg (Real.exp_pos _).le]
        have h1 : e0 ≤ e0 - r0 := by linarith
        exact h1.trans ((le_abs_self _).trans (by simpa [abs_sub_comm] using htaylor))
    have hfl_bound : |((wInt : ℝ) / (Wscale : ℝ)) - max r0 0| ≤ 1 / (Wscale : ℝ) := by
      have hfl_eq : ((Wscale : ℚ) * ratExpNeg (uRat * uRat / 2) Kexp : ℝ) =
          (Wscale : ℝ) * r0 := by push_cast; rfl
      rcases le_or_gt 0 r0 with hr | hr
      · rw [max_eq_left hr]
        have hnn : 0 ≤ ((Wscale : ℚ) * ratExpNeg (uRat * uRat / 2) Kexp) := by
          have : (0 : ℝ) ≤ ((Wscale : ℚ) * ratExpNeg (uRat * uRat / 2) Kexp : ℝ) := by
            rw [hfl_eq]; positivity
          exact_mod_cast this
        have hq1r : ((Rat.floor ((Wscale : ℚ) * ratExpNeg (uRat * uRat / 2) Kexp) : ℤ) : ℝ) ≤
            (Wscale : ℝ) * r0 := by
          have hq1 := Rat.floor_le ((Wscale : ℚ) * ratExpNeg (uRat * uRat / 2) Kexp)
          have : ((Rat.floor ((Wscale : ℚ) * ratExpNeg (uRat * uRat / 2) Kexp) : ℚ) : ℝ) ≤
              ((Wscale : ℚ) * ratExpNeg (uRat * uRat / 2) Kexp : ℝ) := by exact_mod_cast hq1
          simpa [hfl_eq] using this
        have hq2r : (Wscale : ℝ) * r0 <
            ((Rat.floor ((Wscale : ℚ) * ratExpNeg (uRat * uRat / 2) Kexp) : ℤ) : ℝ) + 1 := by
          have hq2 := Rat.lt_floor_add_one ((Wscale : ℚ) * ratExpNeg (uRat * uRat / 2) Kexp)
          have : ((Wscale : ℚ) * ratExpNeg (uRat * uRat / 2) Kexp : ℝ) <
              ((Rat.floor ((Wscale : ℚ) * ratExpNeg (uRat * uRat / 2) Kexp) : ℚ) : ℝ) + 1 := by
            exact_mod_cast hq2
          simpa [hfl_eq] using this
        have hfl_nn : 0 ≤ Rat.floor ((Wscale : ℚ) * ratExpNeg (uRat * uRat / 2) Kexp) := by
          have hlt0 : (-1 : ℝ) <
              ((Rat.floor ((Wscale : ℚ) * ratExpNeg (uRat * uRat / 2) Kexp) : ℤ) : ℝ) := by
            nlinarith
          have hlt0z : (-1 : ℤ) < Rat.floor ((Wscale : ℚ) * ratExpNeg (uRat * uRat / 2) Kexp) := by
            exact_mod_cast hlt0
          omega
        have hw_eq : (wInt : ℝ) =
            ((Rat.floor ((Wscale : ℚ) * ratExpNeg (uRat * uRat / 2) Kexp) : ℤ) : ℝ) := by
          exact_mod_cast Int.toNat_of_nonneg hfl_nn
        rw [hw_eq,
          show ((Rat.floor ((Wscale : ℚ) * ratExpNeg (uRat * uRat / 2) Kexp) : ℤ) : ℝ) /
              (Wscale : ℝ) - r0 =
            (((Rat.floor ((Wscale : ℚ) * ratExpNeg (uRat * uRat / 2) Kexp) : ℤ) : ℝ) -
              (Wscale : ℝ) * r0) / (Wscale : ℝ) by field_simp [hW_pos.ne'],
          abs_div, abs_of_pos hW_pos]
        refine div_le_div_of_nonneg_right ?_ hW_pos.le
        rw [abs_le]
        exact ⟨by linarith, by linarith⟩
      · rw [max_eq_right hr.le]
        have hneg : ((Wscale : ℚ) * ratExpNeg (uRat * uRat / 2) Kexp) ≤ 0 := by
          have : ((Wscale : ℚ) * ratExpNeg (uRat * uRat / 2) Kexp : ℝ) ≤ 0 := by
            rw [hfl_eq]; nlinarith
          exact_mod_cast this
        have hfl_le : Rat.floor ((Wscale : ℚ) * ratExpNeg (uRat * uRat / 2) Kexp) ≤ 0 := by
          have h1 := (Rat.floor_le ((Wscale : ℚ) * ratExpNeg (uRat * uRat / 2) Kexp)).trans hneg
          exact_mod_cast h1
        have hw0 : wInt = 0 := Int.toNat_of_nonpos hfl_le
        simp [hw0]
    calc |((wInt : ℝ) / (Wscale : ℝ)) - e0|
        ≤ |((wInt : ℝ) / (Wscale : ℝ)) - max r0 0| + |max r0 0 - e0| := abs_sub_le _ _ _
      _ ≤ 1 / (Wscale : ℝ) + (1 / 4 : ℝ) ^ Bexp := add_le_add hfl_bound hclamp
      _ = (1 / 4 : ℝ) ^ Bexp + 1 / (Wscale : ℝ) := add_comm _ _
  have hriemann : |(gaussianReal 0 1).real (Ico uPt (uPt + 1 / (H0 : ℝ))) -
      (Real.exp (-(uPt ^ 2 / 2)) / (H0 : ℝ)) / c_pi| ≤ (R0 : ℝ) / (H0 : ℝ) ^ 2 := by
    have hp_int : (gaussianReal 0 1).real (Ico uPt (uPt + 1 / (H0 : ℝ))) =
        (∫ x in Ico uPt (uPt + 1 / (H0 : ℝ)), Real.exp (-(x ^ 2) / 2)) / c_pi := by
      rw [Measure.real_def, gaussianReal_apply_eq_integral 0 one_ne_zero,
        ENNReal.toReal_ofReal (integral_nonneg fun x => gaussianPDFReal_nonneg _ _ x)]
      have hpdf : ∀ x, gaussianPDFReal 0 1 x = c_pi⁻¹ * Real.exp (-(x ^ 2) / 2) := fun x => by
        simp [gaussianPDFReal_def, c_pi]
      simp_rw [hpdf, integral_const_mul, inv_mul_eq_div]
    have hconst_int : Real.exp (-(uPt ^ 2 / 2)) / (H0 : ℝ) =
        ∫ _x in Ico uPt (uPt + 1 / (H0 : ℝ)), Real.exp (-(uPt ^ 2 / 2)) := by
      rw [setIntegral_const, Measure.real_def, Real.volume_Ico, add_sub_cancel_left,
        ENNReal.toReal_ofReal (by positivity), smul_eq_mul, mul_comm, mul_one_div]
    have hint_exp : Integrable (fun x : ℝ => Real.exp (-(x ^ 2) / 2)) :=
      ((integrable_gaussianPDFReal 0 1).const_mul c_pi).congr (ae_of_all _ fun x => by
        simp only [gaussianPDFReal_def, sub_zero, NNReal.coe_one, mul_one, c_pi]
        rw [mul_inv_cancel_left₀ hc_pi_pos.ne'])
    have hint_c : IntegrableOn (fun _ : ℝ => Real.exp (-(uPt ^ 2 / 2)))
        (Ico uPt (uPt + 1 / (H0 : ℝ))) :=
      integrableOn_const (by rw [Real.volume_Ico]; exact ENNReal.ofReal_lt_top.ne)
    rw [hp_int, hconst_int, ← sub_div, ← integral_sub hint_exp.integrableOn hint_c,
      abs_div, abs_of_pos hc_pi_pos]
    have hcube_int : |∫ x in Ico uPt (uPt + 1 / (H0 : ℝ)),
        (Real.exp (-(x ^ 2) / 2) - Real.exp (-(uPt ^ 2 / 2)))| ≤ (R0 : ℝ) / (H0 : ℝ) ^ 2 := by
      calc |∫ x in Ico uPt (uPt + 1 / (H0 : ℝ)),
              (Real.exp (-(x ^ 2) / 2) - Real.exp (-(uPt ^ 2 / 2)))|
          ≤ ∫ x in Ico uPt (uPt + 1 / (H0 : ℝ)),
              |Real.exp (-(x ^ 2) / 2) - Real.exp (-(uPt ^ 2 / 2))| :=
            abs_integral_le_integral_abs
        _ ≤ ∫ _x in Ico uPt (uPt + 1 / (H0 : ℝ)), (R0 : ℝ) / (H0 : ℝ) := by
            refine setIntegral_mono_on (hint_exp.integrableOn.sub hint_c).abs
              (integrableOn_const (by rw [Real.volume_Ico]; exact ENNReal.ofReal_lt_top.ne))
              measurableSet_Ico fun x hx => ?_
            rw [show -(x ^ 2) / 2 = -(x ^ 2 / 2) by ring]
            have hle_exp : |Real.exp (-(x ^ 2 / 2)) - Real.exp (-(uPt ^ 2 / 2))| ≤
                |x ^ 2 / 2 - uPt ^ 2 / 2| := by
              have h1 : ∀ {a b : ℝ}, 0 ≤ a → a ≤ b → Real.exp (-a) - Real.exp (-b) ≤ b - a :=
                fun {a b} ha hab => by
                  have hba : 1 - (b - a) ≤ Real.exp (-(b - a)) := by
                    linarith [Real.add_one_le_exp (-(b - a))]
                  have he : Real.exp (-b) = Real.exp (-a) * Real.exp (-(b - a)) := by
                    rw [← Real.exp_add]; congr 1; ring
                  have ha1 : Real.exp (-a) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
                  nlinarith [Real.exp_pos (-a)]
              rcases le_total (x ^ 2 / 2) (uPt ^ 2 / 2) with h | h
              · rw [abs_of_nonneg (sub_nonneg.mpr (Real.exp_le_exp.mpr (by linarith))),
                  abs_of_nonpos (sub_nonpos.mpr h), neg_sub]
                exact h1 (by positivity) h
              · rw [abs_of_nonpos (sub_nonpos.mpr (Real.exp_le_exp.mpr (by linarith))), neg_sub,
                  abs_of_nonneg (sub_nonneg.mpr h)]
                exact h1 (by positivity) h
            refine hle_exp.trans ?_
            have hdiff : |x ^ 2 / 2 - uPt ^ 2 / 2| = |x - uPt| * |x + uPt| / 2 := by
              rw [show x ^ 2 / 2 - uPt ^ 2 / 2 = (x - uPt) * (x + uPt) / 2 by ring,
                abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
            rw [hdiff]
            have hx_abs : |x| ≤ (R0 : ℝ) := by
              have hm_lt : (m.1 : ℝ) + 1 ≤ ((2 * R0 * H0 : ℕ) : ℝ) := by exact_mod_cast m.2
              have hG : ((2 * R0 * H0 : ℕ) : ℝ) / (H0 : ℝ) = 2 * (R0 : ℝ) := by
                push_cast; field_simp [hH0_rpos.ne']
              have hup : uPt + 1 / (H0 : ℝ) ≤ (R0 : ℝ) := by
                simp only [uPt]; rw [add_assoc, ← add_div]
                have : ((m.1 : ℝ) + 1) / (H0 : ℝ) ≤ 2 * (R0 : ℝ) := by rw [← hG]; gcongr
                linarith
              exact abs_le.mpr ⟨by linarith [hx.1, (abs_le.mp hu_abs).1], by linarith [hx.2]⟩
            have hx_sum : |x + uPt| ≤ 2 * (R0 : ℝ) := (abs_add_le x uPt).trans (by linarith)
            have hx_sub : |x - uPt| ≤ 1 / (H0 : ℝ) := by
              rw [abs_of_nonneg (sub_nonneg.mpr hx.1)]; linarith [hx.2]
            calc |x - uPt| * |x + uPt| / 2 ≤ (1 / (H0 : ℝ)) * (2 * (R0 : ℝ)) / 2 := by gcongr
              _ = (R0 : ℝ) / (H0 : ℝ) := by ring
        _ = (R0 : ℝ) / (H0 : ℝ) ^ 2 := by
            rw [setIntegral_const, Measure.real_def, Real.volume_Ico, add_sub_cancel_left,
              ENNReal.toReal_ofReal (by positivity), smul_eq_mul]
            ring
    calc |∫ x in Ico uPt (uPt + 1 / (H0 : ℝ)),
            (Real.exp (-(x ^ 2) / 2) - Real.exp (-(uPt ^ 2 / 2)))| / c_pi
        ≤ ((R0 : ℝ) / (H0 : ℝ) ^ 2) / 1 :=
          div_le_div₀ (by positivity) hcube_int (by norm_num) hc_pi_ge
      _ = (R0 : ℝ) / (H0 : ℝ) ^ 2 := div_one _
  have hdisc : |(Real.exp (-(uPt ^ 2 / 2)) / (H0 : ℝ)) / c_pi -
      ((wInt : ℝ) / (Wscale : ℝ)) / (H0 : ℝ) / c_pi| ≤
      ((1 / 4 : ℝ) ^ Bexp + 1 / (Wscale : ℝ)) / (H0 : ℝ) := by
    rw [← sub_div, ← sub_div, abs_div, abs_div, abs_of_pos hc_pi_pos, abs_of_pos hH0_rpos,
      abs_sub_comm]
    calc |((wInt : ℝ) / (Wscale : ℝ)) - Real.exp (-(uPt ^ 2 / 2))| / (H0 : ℝ) / c_pi
        ≤ (((1 / 4 : ℝ) ^ Bexp + 1 / (Wscale : ℝ)) / (H0 : ℝ)) / 1 :=
          div_le_div₀ (by positivity) (div_le_div_of_nonneg_right hfloor_err hH0_rpos.le)
            (by norm_num) hc_pi_ge
      _ = ((1 / 4 : ℝ) ^ Bexp + 1 / (Wscale : ℝ)) / (H0 : ℝ) := div_one _
  calc |(gaussianReal 0 1).real (Ico uPt (uPt + 1 / (H0 : ℝ))) -
          ((wInt : ℝ) / (Wscale : ℝ)) / (H0 : ℝ) / c_pi|
      ≤ |(gaussianReal 0 1).real (Ico uPt (uPt + 1 / (H0 : ℝ))) -
          (Real.exp (-(uPt ^ 2 / 2)) / (H0 : ℝ)) / c_pi| +
        |(Real.exp (-(uPt ^ 2 / 2)) / (H0 : ℝ)) / c_pi -
          ((wInt : ℝ) / (Wscale : ℝ)) / (H0 : ℝ) / c_pi| := abs_sub_le _ _ _
    _ ≤ (R0 : ℝ) / (H0 : ℝ) ^ 2 + ((1 / 4 : ℝ) ^ Bexp + 1 / (Wscale : ℝ)) / (H0 : ℝ) :=
        add_le_add hriemann hdisc
    _ = (R0 : ℝ) / (H0 : ℝ) ^ 2 + (1 / 4 : ℝ) ^ Bexp / (H0 : ℝ) +
        (1 / (Wscale : ℝ)) / (H0 : ℝ) := by ring

/-- Disjointness and exact union of the `2 * R0 * H0` uniform grid intervals on `[-R0, R0)`. -/
private theorem cube1D_disj_union {R0 H0 : ℕ} (hH0 : 0 < H0) :
    let uPt : Fin (2 * R0 * H0) → ℝ := fun m => -((R0 : ℝ)) + (m.1 : ℝ) / (H0 : ℝ)
    (Pairwise fun m₁ m₂ : Fin (2 * R0 * H0) =>
      Disjoint (Ico (uPt m₁) (uPt m₁ + 1 / (H0 : ℝ)))
        (Ico (uPt m₂) (uPt m₂ + 1 / (H0 : ℝ)))) ∧
    (⋃ m : Fin (2 * R0 * H0), Ico (uPt m) (uPt m + 1 / (H0 : ℝ))) =
      Ico (-(R0 : ℝ)) (R0 : ℝ) := by
  intro uPt
  have hH0_rpos : (0 : ℝ) < (H0 : ℝ) := Nat.cast_pos.mpr hH0
  refine ⟨?_, ?_⟩
  · intro m₁ m₂ hne
    rw [Set.disjoint_left]
    intro x hx₁ hx₂
    have hlt_or : m₁.1 + 1 ≤ m₂.1 ∨ m₂.1 + 1 ≤ m₁.1 := by
      have : m₁.1 ≠ m₂.1 := fun h => hne (Fin.ext h)
      omega
    rcases hlt_or with h | h
    · have hle : (m₁.1 : ℝ) + 1 ≤ (m₂.1 : ℝ) := by exact_mod_cast h
      have : uPt m₁ + 1 / (H0 : ℝ) ≤ uPt m₂ := by
        simp only [uPt]; rw [add_assoc, ← add_div]; gcongr
      linarith [hx₁.2, hx₂.1]
    · have hle : (m₂.1 : ℝ) + 1 ≤ (m₁.1 : ℝ) := by exact_mod_cast h
      have : uPt m₂ + 1 / (H0 : ℝ) ≤ uPt m₁ := by
        simp only [uPt]; rw [add_assoc, ← add_div]; gcongr
      linarith [hx₂.2, hx₁.1]
  · ext x
    simp only [Set.mem_iUnion, Set.mem_Ico]
    constructor
    · rintro ⟨m, hm1, hm2⟩
      refine ⟨?_, ?_⟩
      · simp only [uPt] at hm1
        linarith [show (0 : ℝ) ≤ (m.1 : ℝ) / (H0 : ℝ) by positivity]
      · have hm_lt : (m.1 : ℝ) + 1 ≤ ((2 * R0 * H0 : ℕ) : ℝ) := by exact_mod_cast m.2
        have hG : ((2 * R0 * H0 : ℕ) : ℝ) / (H0 : ℝ) = 2 * (R0 : ℝ) := by
          push_cast; field_simp [hH0_rpos.ne']
        have hstep : uPt m + 1 / (H0 : ℝ) ≤ (R0 : ℝ) := by
          simp only [uPt]; rw [add_assoc, ← add_div]
          have : ((m.1 : ℝ) + 1) / (H0 : ℝ) ≤ 2 * (R0 : ℝ) := by rw [← hG]; gcongr
          linarith
        linarith
    · rintro ⟨hx1, hx2⟩
      have h0 : 0 ≤ (x + (R0 : ℝ)) * (H0 : ℝ) := by nlinarith
      set mNat : ℕ := Int.toNat ⌊(x + (R0 : ℝ)) * (H0 : ℝ)⌋
      have hfl_nn : 0 ≤ ⌊(x + (R0 : ℝ)) * (H0 : ℝ)⌋ := Int.floor_nonneg.mpr h0
      have hm_cast : (mNat : ℝ) = (⌊(x + (R0 : ℝ)) * (H0 : ℝ)⌋ : ℝ) := by
        exact_mod_cast Int.toNat_of_nonneg hfl_nn
      have hm_lt : mNat < 2 * R0 * H0 := by
        have h1 : (x + (R0 : ℝ)) * (H0 : ℝ) < ((2 * R0 * H0 : ℕ) : ℝ) := by
          have : ((2 * R0 * H0 : ℕ) : ℝ) = 2 * (R0 : ℝ) * (H0 : ℝ) := by push_cast; ring
          nlinarith
        have hfl_lt : (mNat : ℝ) < ((2 * R0 * H0 : ℕ) : ℝ) :=
          hm_cast.symm ▸ (Int.floor_le _).trans_lt h1
        exact_mod_cast hfl_lt
      refine ⟨⟨mNat, hm_lt⟩, ?_, ?_⟩
      · have hle := Int.floor_le ((x + (R0 : ℝ)) * (H0 : ℝ))
        simp only [uPt, hm_cast]; rw [neg_add_le_iff_le_add, div_le_iff₀ hH0_rpos]; linarith
      · have hlt := Int.lt_floor_add_one ((x + (R0 : ℝ)) * (H0 : ℝ))
        simp only [uPt, hm_cast]; rw [add_assoc, ← add_div, lt_iff_not_ge]
        intro hge; rw [neg_add_le_iff_le_add, div_le_iff₀ hH0_rpos] at hge; linarith

/-- Helper bounding the 1D-to-`k`D discrete weight `ℓ¹` error (Step 3c of
`abs_approxClauseProb_sub_le`), keeping parameters abstract to avoid unfolding `Nat.log`. -/
private theorem approxClauseProb_l1_weights_le {d invDelta R0 H0 Bexp Kexp Wscale : ℕ}
    (hd : 1 ≤ d) (hinv : 1 ≤ invDelta) (hR0_ge2 : 2 ≤ R0) (hH0 : 0 < H0) (hWs : 0 < Wscale)
    (hH0_eq : H0 = 64 * d * d * R0 * R0 * invDelta)
    (hWs_eq : Wscale = 64 * d * R0 * invDelta)
    (hK : 3 * (R0 * R0) + 2 * Bexp + 2 ≤ Kexp)
    (hR0_pow : 32 * d * invDelta ≤ 2 ^ R0)
    (hBexp_pow : 64 * d * R0 * invDelta ≤ 2 ^ Bexp) :
    let Glen := 2 * R0 * H0
    let uPt : Fin Glen → ℝ := fun m => -((R0 : ℝ)) + (m.1 : ℝ) / (H0 : ℝ)
    let p1D : Fin Glen → ℝ := fun m => (gaussianReal 0 1).real (Ico (uPt m) (uPt m + 1 / (H0 : ℝ)))
    let uRat : Fin Glen → ℚ := fun m => -((R0 : ℚ)) + (m.1 : ℚ) / (H0 : ℚ)
    let wInt : Fin Glen → ℕ := fun m =>
      (Rat.floor ((Wscale : ℚ) * ratExpNeg (uRat m * uRat m / 2) Kexp)).toNat
    let c_pi : ℝ := Real.sqrt (2 * Real.pi)
    let γ1D : Fin Glen → ℝ := fun m => ((wInt m : ℝ) / (Wscale : ℝ)) / (H0 : ℝ) / c_pi
    let Γ : ℝ := ∑ m : Fin Glen, γ1D m
    (0 < Γ) ∧ (∑ m : Fin Glen, |p1D m - γ1D m / Γ| ≤ 7 / (32 * (d : ℝ) * (invDelta : ℝ))) := by
  intro Glen uPt p1D uRat wInt c_pi γ1D Γ
  have hR0_pos : (0 : ℝ) < (R0 : ℝ) := Nat.cast_pos.mpr (by omega)
  have hd_pos : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr hd
  have hinv_pos : (0 : ℝ) < (invDelta : ℝ) := Nat.cast_pos.mpr hinv
  have hH0_rpos : (0 : ℝ) < (H0 : ℝ) := Nat.cast_pos.mpr hH0
  obtain ⟨hcube1D_disj, hcube1D_union⟩ := cube1D_disj_union (R0 := R0) hH0
  have hP_sub : 1 - ∑ m : Fin Glen, p1D m ≤ 1 / (2 : ℝ) ^ R0 := by
    have hdisj_sum := measureReal_iUnion_fintype (μ := gaussianReal 0 1)
      hcube1D_disj (fun _ => measurableSet_Ico) (fun _ => measure_ne_top _ _)
    rw [hcube1D_union] at hdisj_sum
    have hcompl := measureReal_compl (μ := gaussianReal 0 1) (s := Ico (-(R0 : ℝ)) (R0 : ℝ))
      measurableSet_Ico
    simp only [Measure.real_def, measure_univ, ENNReal.toReal_one] at hcompl
    have hsub : (Ico (-(R0 : ℝ)) (R0 : ℝ))ᶜ ⊆ {x : ℝ | (R0 : ℝ) ≤ |x|} := by
      intro x hx
      simp only [Set.mem_compl_iff, Set.mem_Ico, not_and_or, not_le, not_lt] at hx
      rcases hx with hlt | hge
      · exact (le_of_lt (by linarith)).trans (neg_le_abs x)
      · exact hge.trans (le_abs_self x)
    have hmono := measureReal_mono (μ := gaussianReal 0 1) hsub
    have htail := gaussianReal_abs_ge_le_two_pow (R := R0) hR0_ge2
    simp only [p1D, Measure.real_def] at hdisj_sum hmono htail ⊢
    linarith
  have hp1D_sum_le : ∑ m : Fin Glen, p1D m ≤ 1 := by
    have hdisj_sum := measureReal_iUnion_fintype (μ := gaussianReal 0 1)
      hcube1D_disj (fun _ => measurableSet_Ico) (fun _ => measure_ne_top _ _)
    rw [hcube1D_union] at hdisj_sum
    have h1 : (gaussianReal 0 1).real (Ico (-(R0 : ℝ)) (R0 : ℝ)) ≤ 1 := measureReal_le_one
    simpa only [p1D] using hdisj_sum ▸ h1
  have hΔ1_le : ∑ m : Fin Glen, |p1D m - γ1D m| ≤
      2 * (R0 : ℝ) ^ 2 / (H0 : ℝ) +
      2 * (R0 : ℝ) * (1 / 4 : ℝ) ^ Bexp +
      2 * (R0 : ℝ) / (Wscale : ℝ) := by
    have hGlen_eq : (Glen : ℝ) = 2 * (R0 : ℝ) * (H0 : ℝ) := by
      simp only [Glen]; push_cast; ring
    calc ∑ m : Fin Glen, |p1D m - γ1D m|
        ≤ ∑ _m : Fin Glen, ((R0 : ℝ) / (H0 : ℝ) ^ 2 + (1 / 4 : ℝ) ^ Bexp / (H0 : ℝ) +
            (1 / (Wscale : ℝ)) / (H0 : ℝ)) :=
          Finset.sum_le_sum fun m _ => approxClauseProb_point_err hH0 hWs hK m
      _ = (Glen : ℝ) * ((R0 : ℝ) / (H0 : ℝ) ^ 2 + (1 / 4 : ℝ) ^ Bexp / (H0 : ℝ) +
            (1 / (Wscale : ℝ)) / (H0 : ℝ)) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ = 2 * (R0 : ℝ) ^ 2 / (H0 : ℝ) + 2 * (R0 : ℝ) * (1 / 4 : ℝ) ^ Bexp +
            2 * (R0 : ℝ) / (Wscale : ℝ) := by
          rw [hGlen_eq]; field_simp [hH0_rpos.ne']
  have hΔ1_total : ∑ m : Fin Glen, |p1D m - γ1D m| ≤ 3 / (32 * (d : ℝ) * (invDelta : ℝ)) := by
    have hp1 : 2 * (R0 : ℝ) ^ 2 / (H0 : ℝ) ≤ 1 / (32 * (d : ℝ) * (invDelta : ℝ)) := by
      have hH0_r : (H0 : ℝ) = 64 * (d : ℝ) ^ 2 * (R0 : ℝ) ^ 2 * (invDelta : ℝ) := by
        rw [hH0_eq]; push_cast; ring
      rw [hH0_r]
      have h1 : 2 * (R0 : ℝ) ^ 2 / (64 * (d : ℝ) ^ 2 * (R0 : ℝ) ^ 2 * (invDelta : ℝ)) =
          1 / (32 * (d : ℝ) * (invDelta : ℝ)) / (d : ℝ) := by
        field_simp [hd_pos.ne', hR0_pos.ne', hinv_pos.ne']; ring
      rw [h1, div_le_iff₀ hd_pos]
      have hd_ge1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
      nlinarith [show (0 : ℝ) < 1 / (32 * (d : ℝ) * (invDelta : ℝ)) by positivity]
    have hp2 : 2 * (R0 : ℝ) * (1 / 4 : ℝ) ^ Bexp ≤ 1 / (32 * (d : ℝ) * (invDelta : ℝ)) := by
      have hpow : (1 / 4 : ℝ) ^ Bexp ≤ 1 / (64 * (d : ℝ) * (R0 : ℝ) * (invDelta : ℝ)) := by
        have h1 : (64 * (d : ℝ) * (R0 : ℝ) * (invDelta : ℝ)) ≤ (2 : ℝ) ^ Bexp := by
          exact_mod_cast hBexp_pow
        have h2 : (2 : ℝ) ^ Bexp ≤ (4 : ℝ) ^ Bexp :=
          pow_le_pow_left₀ (by norm_num) (by norm_num) _
        rw [one_div, one_div, inv_pow]
        exact inv_anti₀ (by positivity) (h1.trans h2)
      calc 2 * (R0 : ℝ) * (1 / 4 : ℝ) ^ Bexp
          ≤ 2 * (R0 : ℝ) * (1 / (64 * (d : ℝ) * (R0 : ℝ) * (invDelta : ℝ))) := by gcongr
        _ = 1 / (32 * (d : ℝ) * (invDelta : ℝ)) := by
            field_simp [hd_pos.ne', hR0_pos.ne', hinv_pos.ne']; ring
    have hp3 : 2 * (R0 : ℝ) / (Wscale : ℝ) = 1 / (32 * (d : ℝ) * (invDelta : ℝ)) := by
      have hWs_r : (Wscale : ℝ) = 64 * (d : ℝ) * (R0 : ℝ) * (invDelta : ℝ) := by
        rw [hWs_eq]; push_cast; ring
      rw [hWs_r]; field_simp [hd_pos.ne', hR0_pos.ne', hinv_pos.ne']; ring
    have hsum3 : 1 / (32 * (d : ℝ) * (invDelta : ℝ)) + 1 / (32 * (d : ℝ) * (invDelta : ℝ)) +
        1 / (32 * (d : ℝ) * (invDelta : ℝ)) = 3 / (32 * (d : ℝ) * (invDelta : ℝ)) := by ring
    linarith
  have hτ1_total : 1 - ∑ m : Fin Glen, p1D m ≤ 1 / (32 * (d : ℝ) * (invDelta : ℝ)) := by
    refine hP_sub.trans ?_
    have h1 : (32 * (d : ℝ) * (invDelta : ℝ)) ≤ (2 : ℝ) ^ R0 := by exact_mod_cast hR0_pow
    exact one_div_le_one_div_of_le (by positivity) h1
  have hΓ_sub : |∑ m : Fin Glen, p1D m - Γ| ≤ 3 / (32 * (d : ℝ) * (invDelta : ℝ)) := by
    rw [show ∑ m : Fin Glen, p1D m - Γ = ∑ m : Fin Glen, (p1D m - γ1D m) by
      simp only [Γ, Finset.sum_sub_distrib]]
    exact (Finset.abs_sum_le_sum_abs _ _).trans hΔ1_total
  have hΓ_pos : 0 < Γ := by
    have h1 : (1 : ℝ) / (32 * (d : ℝ) * (invDelta : ℝ)) ≤ 1 / 32 := by
      have : (1 : ℝ) ≤ (d : ℝ) * (invDelta : ℝ) := by
        have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
        have hi1 : (1 : ℝ) ≤ (invDelta : ℝ) := by exact_mod_cast hinv
        nlinarith
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
    have h3 : 3 / (32 * (d : ℝ) * (invDelta : ℝ)) =
        3 * (1 / (32 * (d : ℝ) * (invDelta : ℝ))) := by ring
    have h2 : |∑ m, p1D m - Γ| ≤ 3 / 32 := hΓ_sub.trans (by linarith)
    linarith [(abs_le.mp h2).2]
  refine ⟨hΓ_pos, ?_⟩
  have hγ1D_nn : ∀ m, 0 ≤ γ1D m := fun _ => by positivity
  have hnorm_sum : ∑ m : Fin Glen, |γ1D m - γ1D m / Γ| = |Γ - 1| := by
    have hfactor : ∀ m : Fin Glen, |γ1D m - γ1D m / Γ| = γ1D m * |1 - 1 / Γ| := fun m => by
      rw [show γ1D m - γ1D m / Γ = γ1D m * (1 - 1 / Γ) by ring, abs_mul,
        abs_of_nonneg (hγ1D_nn m)]
    simp_rw [hfactor, ← Finset.sum_mul]
    rw [show Γ * |1 - 1 / Γ| = |Γ * (1 - 1 / Γ)| by rw [abs_mul, abs_of_pos hΓ_pos],
      show Γ * (1 - 1 / Γ) = Γ - 1 by field_simp [hΓ_pos.ne']]
  have hΓ1 : |Γ - 1| ≤ 4 / (32 * (d : ℝ) * (invDelta : ℝ)) := by
    have h1 : |Γ - 1| ≤ |Γ - ∑ m, p1D m| + |∑ m, p1D m - 1| := abs_sub_le _ _ _
    rw [abs_sub_comm Γ (∑ m, p1D m)] at h1
    have h2 : |∑ m, p1D m - 1| = 1 - ∑ m, p1D m := by
      rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    have hsum4 : 3 / (32 * (d : ℝ) * (invDelta : ℝ)) + 1 / (32 * (d : ℝ) * (invDelta : ℝ)) =
        4 / (32 * (d : ℝ) * (invDelta : ℝ)) := by ring
    linarith
  have hsum7 : 3 / (32 * (d : ℝ) * (invDelta : ℝ)) + 4 / (32 * (d : ℝ) * (invDelta : ℝ)) =
      7 / (32 * (d : ℝ) * (invDelta : ℝ)) := by ring
  calc ∑ m : Fin Glen, |p1D m - γ1D m / Γ|
      ≤ ∑ m : Fin Glen, (|p1D m - γ1D m| + |γ1D m - γ1D m / Γ|) :=
        Finset.sum_le_sum fun m _ => abs_sub_le _ _ _
    _ = ∑ m, |p1D m - γ1D m| + |Γ - 1| := by rw [Finset.sum_add_distrib, hnorm_sum]
    _ ≤ 3 / (32 * (d : ℝ) * (invDelta : ℝ)) + 4 / (32 * (d : ℝ) * (invDelta : ℝ)) :=
        add_le_add hΔ1_total hΓ1
    _ = 7 / (32 * (d : ℝ) * (invDelta : ℝ)) := hsum7

/-- Helper bounding the hyperplane-slab boundary error (Step 3b of `abs_approxClauseProb_sub_le`),
keeping all parameters abstract to avoid unfolding `Nat.log`. -/
private theorem approxClauseProb_slab_err {k d R0 H0 : ℕ} (hd : 1 ≤ d) (hk_le : k ≤ d)
    (hH0 : 0 < H0) (cl : List (List ℚ × ℚ)) (hcl_len : cl.length ≤ d)
    (cRat : (List ℚ × ℚ) → Fin k → ℚ) :
    let Glen := 2 * R0 * H0
    let uPt : Fin Glen → ℝ := fun m => -((R0 : ℝ)) + (m.1 : ℝ) / (H0 : ℝ)
    let cube1D : Fin Glen → Set ℝ := fun m => Ico (uPt m) (uPt m + 1 / (H0 : ℝ))
    let boxK : Set (Fin k → ℝ) := Set.univ.pi fun _ => Ico (-(R0 : ℝ)) (R0 : ℝ)
    let cubeK : (Fin k → Fin Glen) → Set (Fin k → ℝ) := fun z => Set.univ.pi fun s => cube1D (z s)
    let A_rat : Set (Fin k → ℝ) :=
      {z | ∀ p ∈ cl, (p.2 : ℝ) < ∑ s : Fin k, ((cRat p s : ℚ) : ℝ) * z s}
    let U_grid : Set (Fin k → ℝ) :=
      ⋃ z ∈ (Finset.univ.filter fun z : Fin k → Fin Glen =>
        @Decidable.decide ((fun s => uPt (z s)) ∈ A_rat) (Classical.propDecidable _)), cubeK z
    |(Measure.pi fun _ : Fin k => gaussianReal 0 1).real (A_rat ∩ boxK) -
      (Measure.pi fun _ : Fin k => gaussianReal 0 1).real U_grid| ≤
      (d : ℝ) * (d : ℝ) / (H0 : ℝ) := by
  intro Glen uPt cube1D boxK cubeK A_rat U_grid
  classical
  have hH0_rpos : (0 : ℝ) < (H0 : ℝ) := Nat.cast_pos.mpr hH0
  obtain ⟨hcube1D_disj, hcube1D_union⟩ := cube1D_disj_union (R0 := R0) hH0
  have hcubeK_disj : Pairwise fun z₁ z₂ : Fin k → Fin Glen => Disjoint (cubeK z₁) (cubeK z₂) := by
    intro z₁ z₂ hne
    obtain ⟨s, hs⟩ : ∃ s, z₁ s ≠ z₂ s := Function.ne_iff.mp hne
    rw [Set.disjoint_left]
    intro y hy₁ hy₂
    exact Set.disjoint_left.mp (hcube1D_disj hs) (hy₁ s trivial) (hy₂ s trivial)
  have hcubeK_union : (⋃ z : Fin k → Fin Glen, cubeK z) = boxK := by
    ext y
    simp only [Set.mem_iUnion, cubeK, boxK, Set.mem_pi, Set.mem_univ, forall_true_left]
    constructor
    · rintro ⟨z, hz⟩ s
      rw [← hcube1D_union]
      exact Set.mem_iUnion.mpr ⟨z s, hz s⟩
    · intro hy
      have h' : ∀ s : Fin k, ∃ m : Fin Glen, y s ∈ cube1D m := fun s =>
        Set.mem_iUnion.mp (hcube1D_union.symm ▸ hy s)
      choose z hz using h'
      exact ⟨z, hz⟩
  let μk := Measure.pi fun _ : Fin k => gaussianReal 0 1
  let Cvec : (List ℚ × ℚ) → EuclideanSpace ℝ (Fin k) :=
    fun p => WithLp.toLp 2 fun s : Fin k => ((cRat p s : ℚ) : ℝ)
  let badSlab : (List ℚ × ℚ) → Set (Fin k → ℝ) := fun p =>
    {y | |∑ s : Fin k, ((cRat p s : ℚ) : ℝ) * y s - (p.2 : ℝ)| ≤
      ‖Cvec p‖ * Real.sqrt (k : ℝ) / (H0 : ℝ)}
  have hdiff_sub : ((A_rat ∩ boxK) \ U_grid) ∪ (U_grid \ (A_rat ∩ boxK)) ⊆
      ⋃ p ∈ cl.toFinset.filter (fun p => Cvec p ≠ 0), badSlab p := by
    intro y hy
    have hy_box : y ∈ boxK := by
      rcases hy with ⟨⟨_, hbox⟩, _⟩ | ⟨hyU, _⟩
      · exact hbox
      · rw [← hcubeK_union]
        rcases Set.mem_iUnion₂.mp hyU with ⟨z, _, hz⟩
        exact Set.mem_iUnion.mpr ⟨z, hz⟩
    rw [← hcubeK_union] at hy_box
    obtain ⟨z, hz⟩ := Set.mem_iUnion.mp hy_box
    have hcorner_dist : ∀ s : Fin k, |y s - uPt (z s)| ≤ 1 / (H0 : ℝ) := fun s => by
      have hs := hz s trivial
      rw [abs_of_nonneg (sub_nonneg.mpr hs.1)]; linarith [hs.2]
    have hnorm_diff : ‖WithLp.toLp 2 (fun s => y s - uPt (z s))‖ ≤
        Real.sqrt (k : ℝ) / (H0 : ℝ) := by
      have hsq : ‖WithLp.toLp 2 (fun s => y s - uPt (z s))‖ ^ 2 ≤
          (k : ℝ) * (1 / (H0 : ℝ)) ^ 2 := by
        rw [EuclideanSpace.norm_sq_eq]
        calc ∑ s : Fin k, ‖y s - uPt (z s)‖ ^ 2
            ≤ ∑ _s : Fin k, (1 / (H0 : ℝ)) ^ 2 :=
              Finset.sum_le_sum fun s _ => by
                rw [Real.norm_eq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hcorner_dist s) 2
          _ = (k : ℝ) * (1 / (H0 : ℝ)) ^ 2 := by simp
      calc ‖WithLp.toLp 2 (fun s => y s - uPt (z s))‖
          = Real.sqrt (‖WithLp.toLp 2 (fun s => y s - uPt (z s))‖ ^ 2) :=
            (Real.sqrt_sq (norm_nonneg _)).symm
        _ ≤ Real.sqrt ((k : ℝ) * (1 / (H0 : ℝ)) ^ 2) := Real.sqrt_le_sqrt hsq
        _ = Real.sqrt (k : ℝ) / (H0 : ℝ) := by
            rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity), mul_one_div]
    have hyU_iff : y ∈ U_grid ↔ (fun s => uPt (z s)) ∈ A_rat := by
      constructor
      · intro hyU
        rcases Set.mem_iUnion₂.mp hyU with ⟨z', hz'S, hz'⟩
        have hzz' : z = z' := by
          by_contra hne
          exact Set.disjoint_left.mp (hcubeK_disj hne) hz hz'
        subst hzz'
        have := (Finset.mem_filter.mp hz'S).2
        simpa only [decide_eq_true_eq] using this
      · intro hA_z
        refine Set.mem_iUnion₂.mpr ⟨z, Finset.mem_filter.mpr ⟨Finset.mem_univ z, ?_⟩, hz⟩
        simpa only [decide_eq_true_eq] using hA_z
    have hinner_diff : ∀ p : List ℚ × ℚ,
        |∑ s : Fin k, ((cRat p s : ℚ) : ℝ) * y s -
          ∑ s : Fin k, ((cRat p s : ℚ) : ℝ) * uPt (z s)| ≤
        ‖Cvec p‖ * Real.sqrt (k : ℝ) / (H0 : ℝ) := fun p => by
      have heq : ∑ s : Fin k, ((cRat p s : ℚ) : ℝ) * y s -
          ∑ s : Fin k, ((cRat p s : ℚ) : ℝ) * uPt (z s) =
          ⟪Cvec p, WithLp.toLp 2 (fun s => y s - uPt (z s))⟫ := by
        rw [PiLp.inner_apply, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun s _ => ?_
        simp only [Cvec, RCLike.inner_apply, conj_trivial]; ring
      rw [heq]
      calc |⟪Cvec p, WithLp.toLp 2 (fun s => y s - uPt (z s))⟫|
          ≤ ‖Cvec p‖ * ‖WithLp.toLp 2 (fun s => y s - uPt (z s))‖ :=
            abs_real_inner_le_norm _ _
        _ ≤ ‖Cvec p‖ * (Real.sqrt (k : ℝ) / (H0 : ℝ)) := by gcongr
        _ = ‖Cvec p‖ * Real.sqrt (k : ℝ) / (H0 : ℝ) := by ring
    have hsep : ∃ p ∈ cl, Cvec p ≠ 0 ∧ y ∈ badSlab p := by
      have hxor : (y ∈ A_rat ∧ (fun s => uPt (z s)) ∉ A_rat) ∨
          (y ∉ A_rat ∧ (fun s => uPt (z s)) ∈ A_rat) := by
        rcases hy with ⟨⟨hyA, _⟩, hyU⟩ | ⟨hyU, hyA⟩
        · exact Or.inl ⟨hyA, fun h => hyU (hyU_iff.mpr h)⟩
        · have hbox : y ∈ boxK := hcubeK_union ▸ Set.mem_iUnion.mpr ⟨z, hz⟩
          exact Or.inr ⟨fun h => hyA ⟨h, hbox⟩, hyU_iff.mp hyU⟩
      rcases hxor with ⟨hyA, hzNA⟩ | ⟨hyNA, hzA⟩
      · simp only [A_rat, Set.mem_ofPred_eq, not_forall, not_lt] at hzNA
        obtain ⟨p, hp, hple⟩ := hzNA
        have hpgt := hyA p hp
        have hCne : Cvec p ≠ 0 := fun h0 => by
          have hc0 : ∀ s : Fin k, ((cRat p s : ℚ) : ℝ) = 0 := fun s => by
            simpa [Cvec] using congrArg (fun v : EuclideanSpace ℝ (Fin k) => v.ofLp s) h0
          simp only [hc0, zero_mul, Finset.sum_const_zero] at hple hpgt; linarith
        refine ⟨p, hp, hCne, ?_⟩
        have hd0 := hinner_diff p
        rw [abs_of_nonneg (by linarith)] at hd0
        simp only [badSlab, Set.mem_ofPred_eq, abs_of_nonneg (by linarith :
          0 ≤ ∑ s : Fin k, ((cRat p s : ℚ) : ℝ) * y s - (p.2 : ℝ))]
        linarith
      · simp only [A_rat, Set.mem_ofPred_eq, not_forall, not_lt] at hyNA
        obtain ⟨p, hp, hple⟩ := hyNA
        have hpgt := hzA p hp
        have hCne : Cvec p ≠ 0 := fun h0 => by
          have hc0 : ∀ s : Fin k, ((cRat p s : ℚ) : ℝ) = 0 := fun s => by
            simpa [Cvec] using congrArg (fun v : EuclideanSpace ℝ (Fin k) => v.ofLp s) h0
          simp only [hc0, zero_mul, Finset.sum_const_zero] at hple hpgt; linarith
        refine ⟨p, hp, hCne, ?_⟩
        have hd0 := hinner_diff p
        rw [abs_of_nonpos (by linarith), neg_sub] at hd0
        simp only [badSlab, Set.mem_ofPred_eq, abs_of_nonpos (by linarith :
          ∑ s : Fin k, ((cRat p s : ℚ) : ℝ) * y s - (p.2 : ℝ) ≤ 0), neg_sub]
        linarith
    obtain ⟨p, hp, hCne, hbad⟩ := hsep
    exact Set.mem_iUnion₂.mpr ⟨p, Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hp, hCne⟩, hbad⟩
  have hslab_bound : ∀ p ∈ cl.toFinset.filter (fun p => Cvec p ≠ 0),
      μk.real (badSlab p) ≤ (d : ℝ) / (H0 : ℝ) := fun p hp => by
    have hCne : Cvec p ≠ 0 := (Finset.mem_filter.mp hp).2
    have hCpos : 0 < ‖Cvec p‖ := norm_pos_iff.mpr hCne
    set r_w : ℝ := ‖Cvec p‖ * Real.sqrt (k : ℝ) / (H0 : ℝ)
    have hpre : (fun x : EuclideanSpace ℝ (Fin k) => x.ofLp) ⁻¹' badSlab p =
        {x : EuclideanSpace ℝ (Fin k) |
          ⟪Cvec p, x⟫ ∈ Icc ((p.2 : ℝ) - r_w) ((p.2 : ℝ) + r_w)} := by
      ext x
      simp only [Set.mem_preimage, badSlab, Set.mem_ofPred_eq, Set.mem_Icc, abs_sub_le_iff]
      have hinner : ⟪Cvec p, x⟫ = ∑ s : Fin k, ((cRat p s : ℚ) : ℝ) * x.ofLp s := by
        rw [PiLp.inner_apply]
        refine Finset.sum_congr rfl fun s _ => ?_
        simp only [Cvec, RCLike.inner_apply, conj_trivial]; ring
      rw [hinner]
      constructor <;> intro ⟨h1, h2⟩ <;> exact ⟨by linarith, by linarith⟩
    have hμ_eq : μk.real (badSlab p) =
        (stdGaussian (EuclideanSpace ℝ (Fin k))).real
          {x | ⟪Cvec p, x⟫ ∈ Icc ((p.2 : ℝ) - r_w) ((p.2 : ℝ) + r_w)} := by
      have hmeas_tgt : MeasurableSet
          {x : EuclideanSpace ℝ (Fin k) |
            ⟪Cvec p, x⟫ ∈ Icc ((p.2 : ℝ) - r_w) ((p.2 : ℝ) + r_w)} :=
        measurableSet_Icc.preimage (innerSL ℝ (Cvec p)).continuous.measurable
      have h1 := ProbabilityTheory.measureReal_pi_gaussianReal_eq hmeas_tgt
      have hset_eq : {ω : Fin k → ℝ | WithLp.toLp 2 ω ∈
          {x : EuclideanSpace ℝ (Fin k) |
            ⟪Cvec p, x⟫ ∈ Icc ((p.2 : ℝ) - r_w) ((p.2 : ℝ) + r_w)}} = badSlab p := by
        ext ω
        have := Set.ext_iff.mp hpre (WithLp.toLp 2 ω)
        simpa using this.symm
      rw [← h1, hset_eq]
    rw [hμ_eq, Measure.real_def]
    have hle_enn := ProbabilityTheory.stdGaussian_inner_mem_le hCne
      (measurableSet_Icc (a := (p.2 : ℝ) - r_w) (b := (p.2 : ℝ) + r_w))
    have hvol : volume (Icc ((p.2 : ℝ) - r_w) ((p.2 : ℝ) + r_w)) = ENNReal.ofReal (2 * r_w) := by
      rw [Real.volume_Icc]; congr 1; ring
    rw [hvol, ← ENNReal.ofReal_mul (by positivity)] at hle_enn
    refine (ENNReal.toReal_le_of_le_ofReal (by positivity) hle_enn).trans ?_
    have h2pi_gt : (2 : ℝ) < Real.sqrt (2 * Real.pi) := by
      have : (4 : ℝ) < 2 * Real.pi := by linarith [Real.pi_gt_three]
      calc (2 : ℝ) = Real.sqrt (2 ^ 2) := (Real.sqrt_sq (by norm_num)).symm
        _ = Real.sqrt 4 := by norm_num
        _ < Real.sqrt (2 * Real.pi) := Real.sqrt_lt_sqrt (by norm_num) this
    have hcoeff : (Real.sqrt (2 * Real.pi) * ‖Cvec p‖)⁻¹ * (2 * r_w) =
        (2 / Real.sqrt (2 * Real.pi)) * (Real.sqrt (k : ℝ) / (H0 : ℝ)) := by
      simp only [r_w]; field_simp [hCpos.ne', hH0_rpos.ne', h2pi_gt.ne']
    rw [hcoeff]
    have h2div : 2 / Real.sqrt (2 * Real.pi) ≤ 1 := by
      rw [div_le_one (by positivity)]; exact h2pi_gt.le
    have hsqrt_k : Real.sqrt (k : ℝ) ≤ (d : ℝ) := by
      have hk_le_d : (k : ℝ) ≤ (d : ℝ) := by exact_mod_cast hk_le
      have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
      calc Real.sqrt (k : ℝ) ≤ Real.sqrt ((d : ℝ) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
        _ = (d : ℝ) := Real.sqrt_sq (by positivity)
    calc (2 / Real.sqrt (2 * Real.pi)) * (Real.sqrt (k : ℝ) / (H0 : ℝ))
        ≤ 1 * ((d : ℝ) / (H0 : ℝ)) :=
          mul_le_mul h2div (div_le_div_of_nonneg_right hsqrt_k hH0_rpos.le)
            (by positivity) zero_le_one
      _ = (d : ℝ) / (H0 : ℝ) := one_mul _
  have hsym_diff : |μk.real (A_rat ∩ boxK) - μk.real U_grid| ≤
      μk.real (((A_rat ∩ boxK) \ U_grid) ∪ (U_grid \ (A_rat ∩ boxK))) := by
    have hE : A_rat ∩ boxK ⊆ U_grid ∪ ((A_rat ∩ boxK) \ U_grid) := fun y hy =>
      if h : y ∈ U_grid then Or.inl h else Or.inr ⟨hy, h⟩
    have hF : U_grid ⊆ (A_rat ∩ boxK) ∪ (U_grid \ (A_rat ∩ boxK)) := fun y hy =>
      if h : y ∈ A_rat ∩ boxK then Or.inl h else Or.inr ⟨hy, h⟩
    have h1 : μk.real (A_rat ∩ boxK) - μk.real U_grid ≤ μk.real ((A_rat ∩ boxK) \ U_grid) := by
      linarith [measureReal_mono (μ := μk) (h₂ := measure_ne_top _ _) hE,
        measureReal_union_le (μ := μk) U_grid ((A_rat ∩ boxK) \ U_grid)]
    have h2 : μk.real U_grid - μk.real (A_rat ∩ boxK) ≤ μk.real (U_grid \ (A_rat ∩ boxK)) := by
      linarith [measureReal_mono (μ := μk) (h₂ := measure_ne_top _ _) hF,
        measureReal_union_le (μ := μk) (A_rat ∩ boxK) (U_grid \ (A_rat ∩ boxK))]
    have hsr : U_grid \ (A_rat ∩ boxK) ⊆
        ((A_rat ∩ boxK) \ U_grid) ∪ (U_grid \ (A_rat ∩ boxK)) := Set.subset_union_right
    rw [abs_le]
    exact ⟨by linarith [measureReal_mono (μ := μk) (h₂ := measure_ne_top _ _) hsr],
      h1.trans (measureReal_mono (h₂ := measure_ne_top _ _) Set.subset_union_left)⟩
  calc |μk.real (A_rat ∩ boxK) - μk.real U_grid|
      ≤ μk.real (((A_rat ∩ boxK) \ U_grid) ∪ (U_grid \ (A_rat ∩ boxK))) := hsym_diff
    _ ≤ μk.real (⋃ p ∈ cl.toFinset.filter (fun p => Cvec p ≠ 0), badSlab p) :=
        measureReal_mono (h₂ := measure_ne_top _ _) hdiff_sub
    _ ≤ ∑ p ∈ cl.toFinset.filter (fun p => Cvec p ≠ 0), μk.real (badSlab p) :=
        measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _p ∈ cl.toFinset.filter (fun p => Cvec p ≠ 0), (d : ℝ) / (H0 : ℝ) :=
        Finset.sum_le_sum hslab_bound
    _ ≤ (d : ℝ) * ((d : ℝ) / (H0 : ℝ)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        have hcard_le : ((cl.toFinset.filter (fun p => Cvec p ≠ 0)).card : ℝ) ≤ (d : ℝ) := by
          have h1 : (cl.toFinset.filter (fun p => Cvec p ≠ 0)).card ≤ cl.length :=
            (Finset.card_filter_le _ _).trans (List.toFinset_card_le cl)
          exact_mod_cast h1.trans hcl_len
        exact mul_le_mul_of_nonneg_right hcard_le (by positivity)
    _ = (d : ℝ) * (d : ℝ) / (H0 : ℝ) := by ring

/-- Helper combining exact rotational invariance (Step 1) and diagonal-scaling TV error (Step 2)
for `abs_approxClauseProb_sub_le`. -/
private theorem approxClauseProb_rot_scale_err {N d invDelta Msqrt : ℕ}
    (hd : 1 ≤ d) (hinv : 1 ≤ invDelta) (hMsqrt : Msqrt = 4 * d * invDelta)
    {cl : List (List ℚ × ℚ)} (hcl_len : cl.length ≤ d) (hv_len : ∀ p ∈ cl, p.1.length = N) :
    let basis := ratGramSchmidtBounded d (cl.map Prod.fst)
    let k := basis.length
    let cRat : (List ℚ × ℚ) → Fin k → ℚ := fun p s =>
      (ratDot p.1 basis[s] / ratDot basis[s] basis[s]) *
        ratSqrtUpper (ratDot basis[s] basis[s]) Msqrt
    let A_rat : Set (Fin k → ℝ) :=
      {z | ∀ p ∈ cl, (p.2 : ℝ) < ∑ s : Fin k, ((cRat p s : ℚ) : ℝ) * z s}
    |(stdGaussian (EuclideanSpace ℝ (Fin N))).real
        {x : EuclideanSpace ℝ (Fin N) | ∀ p ∈ cl, (p.2 : ℝ) < ⟪ratVecToEuclidean N p.1, x⟫} -
      (Measure.pi fun _ : Fin k => gaussianReal 0 1).real A_rat| ≤
      1 / (4 * (invDelta : ℝ)) := by
  intro basis k cRat A_rat
  have hvecs_len : (cl.map Prod.fst).length ≤ d := by simpa using hcl_len
  obtain ⟨hk_le, hb_info, hb_orth, hb_span⟩ := ratGramSchmidtBounded_spec hvecs_len
    (fun v hv => by rcases List.mem_map.mp hv with ⟨p, hp, rfl⟩; exact hv_len p hp)
  have hMsqrt_ge1 : 1 ≤ Msqrt := by subst hMsqrt; nlinarith
  have hd_pos : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr hd
  have hinv_pos : (0 : ℝ) < (invDelta : ℝ) := Nat.cast_pos.mpr hinv
  let eVec : Fin k → EuclideanSpace ℝ (Fin N) := fun s => ratVecToEuclidean N basis[s]
  have he_norm_pos : ∀ s : Fin k, 0 < ‖eVec s‖ := fun s => by
    have hinfo := hb_info basis[s] (List.getElem_mem s.2)
    have hne : eVec s ≠ 0 :=
      fun h0 => hinfo.2 ((ratVecToEuclidean_eq_zero_iff_ratDot hinfo.1).mp h0)
    exact norm_pos_iff.mpr hne
  have he_dot_pos : ∀ s : Fin k, (0 : ℚ) < ratDot basis[s] basis[s] := fun s => by
    have hinfo := hb_info basis[s] (List.getElem_mem s.2)
    exact lt_of_le_of_ne (ratDot_self_nonneg _) (Ne.symm hinfo.2)
  let uUnit : Fin k → EuclideanSpace ℝ (Fin N) := fun s => (‖eVec s‖)⁻¹ • eVec s
  have hu_norm : ∀ s : Fin k, ‖uUnit s‖ = 1 := fun s => by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (he_norm_pos s)),
      inv_mul_cancel₀ (he_norm_pos s).ne']
  have hu_orth : Pairwise fun s t => ⟪uUnit s, uUnit t⟫ = 0 := fun s t hst => by
    dsimp only
    rw [real_inner_smul_left, real_inner_smul_right]
    have hpair : ⟪eVec s, eVec t⟫ = 0 := by
      rcases lt_or_gt_of_ne hst with hlt | hgt
      · exact List.pairwise_iff_getElem.mp hb_orth s.1 t.1 s.2 t.2 hlt
      · rw [real_inner_comm]
        exact List.pairwise_iff_getElem.mp hb_orth t.1 s.1 t.2 s.2 hgt
    rw [hpair, mul_zero, mul_zero]
  have hmap_pi := ProbabilityTheory.stdGaussian_map_inner_pi hu_norm hu_orth
  let aCoeff : (List ℚ × ℚ) → Fin k → ℚ := fun p s => ratDot p.1 basis[s] / ratDot basis[s] basis[s]
  let rRat : Fin k → ℚ := fun s => ratSqrtUpper (ratDot basis[s] basis[s]) Msqrt
  let σ : Fin k → ℝ := fun s => (rRat s : ℝ) / ‖eVec s‖
  have hσ_bounds : ∀ s : Fin k, 1 ≤ σ s ∧ σ s ≤ 1 + 1 / (Msqrt : ℝ) := fun s => by
    have hinfo := hb_info basis[s] (List.getElem_mem s.2)
    have hspec := ratSqrtUpper_spec (he_dot_pos s) hMsqrt_ge1
    have hnorm_eq : ‖eVec s‖ = Real.sqrt (ratDot basis[s] basis[s] : ℝ) := by
      rw [← Real.sqrt_sq (norm_nonneg (eVec s)), norm_sq_ratVecToEuclidean_eq_ratDot hinfo.1]
    rw [show σ s = (rRat s : ℝ) / ‖eVec s‖ from rfl, hnorm_eq]
    have hsq_pos : 0 < Real.sqrt (ratDot basis[s] basis[s] : ℝ) := hnorm_eq ▸ he_norm_pos s
    exact ⟨(one_le_div hsq_pos).mpr hspec.1.le,
      (div_le_iff₀ hsq_pos).mpr (by linarith [hspec.2])⟩
  let A_orig : Set (Fin k → ℝ) :=
    {y | ∀ p ∈ cl, (p.2 : ℝ) < ∑ s : Fin k, ((aCoeff p s : ℚ) : ℝ) * ‖eVec s‖ * y s}
  have hA_orig_meas : MeasurableSet A_orig := by
    have hcl_fin : A_orig = ⋂ p ∈ cl.toFinset,
        {y : Fin k → ℝ | (p.2 : ℝ) < ∑ s : Fin k, ((aCoeff p s : ℚ) : ℝ) * ‖eVec s‖ * y s} := by
      ext y; simp [A_orig]
    rw [hcl_fin]
    exact Finset.measurableSet_biInter _ fun _ _ =>
      (isOpen_lt continuous_const (by fun_prop)).measurableSet
  have hrot : (stdGaussian (EuclideanSpace ℝ (Fin N))).real
      {x : EuclideanSpace ℝ (Fin N) | ∀ p ∈ cl, (p.2 : ℝ) < ⟪ratVecToEuclidean N p.1, x⟫} =
      (Measure.pi fun _ : Fin k => gaussianReal 0 1).real A_orig := by
    have hpre : (fun x : EuclideanSpace ℝ (Fin N) => fun s : Fin k => ⟪uUnit s, x⟫) ⁻¹' A_orig =
        {x : EuclideanSpace ℝ (Fin N) | ∀ p ∈ cl, (p.2 : ℝ) < ⟪ratVecToEuclidean N p.1, x⟫} := by
      ext x
      simp only [Set.mem_preimage, A_orig, Set.mem_ofPred_eq]
      refine forall₂_congr fun p hp => ?_
      rw [hb_span p.1 (List.mem_map_of_mem hp), sum_inner]
      have hsum : ∑ s : Fin k, ⟪((aCoeff p s : ℚ) : ℝ) • eVec s, x⟫ =
          ∑ s : Fin k, ((aCoeff p s : ℚ) : ℝ) * ‖eVec s‖ * ⟪uUnit s, x⟫ := by
        refine Finset.sum_congr rfl fun s _ => ?_
        have hne := (he_norm_pos s).ne'
        simp only [uUnit, real_inner_smul_left, eVec] at hne ⊢
        field_simp [hne]
      rw [hsum]
    have hmeas_proj : Measurable (fun x : EuclideanSpace ℝ (Fin N) => fun s : Fin k => ⟪uUnit s,
      x⟫) :=
      Measurable.of_eval fun s => (innerSL ℝ (uUnit s)).continuous.measurable
    rw [Measure.real_def, Measure.real_def, ← hpre,
      ← Measure.map_apply hmeas_proj hA_orig_meas, hmap_pi]
  rw [hrot]
  let ν : Fin k → Measure ℝ := fun s => gaussianReal 0 ⟨(σ s) ^ 2, sq_nonneg (σ s)⟩
  have hA_rat_eq : (Measure.pi fun _ : Fin k => gaussianReal 0 1).real A_rat =
      (Measure.pi ν).real A_orig := by
    have hmap_ν : (Measure.pi fun _ : Fin k => gaussianReal 0 1).map (fun z s => σ s * z s) =
        Measure.pi ν := by
      have hind : iIndepFun (fun s (z : Fin k → ℝ) => σ s * z s)
          (Measure.pi fun _ : Fin k => gaussianReal 0 1) := by
        have h0 : iIndepFun (fun (s : Fin k) (z : Fin k → ℝ) => z s)
            (Measure.pi fun _ : Fin k => gaussianReal 0 1) :=
          ProbabilityTheory.iIndepFun_pi fun _ => aemeasurable_id
        exact h0.comp (fun s t => σ s * t) fun s => by fun_prop
      rw [hind.map_fun_eq_pi_map fun s => ((continuous_apply s).const_mul (σ s)).aemeasurable]
      congr 1
      funext s
      have h1 : (Measure.pi fun _ : Fin k => gaussianReal 0 1).map (fun z : Fin k → ℝ => z s) =
          gaussianReal 0 1 := by
        simpa using
          (MeasureTheory.measurePreserving_eval (fun _ : Fin k => gaussianReal 0 1) s).map_eq
      have h2 : (fun z : Fin k → ℝ => σ s * z s) = (fun t => σ s * t) ∘ (fun z => z s) := rfl
      rw [h2, ← Measure.map_map (by fun_prop) (by fun_prop), h1, gaussianReal_map_const_mul]
      simp only [ν, mul_zero, mul_one]; rfl
    have hpre : (fun z : Fin k → ℝ => fun s : Fin k => σ s * z s) ⁻¹' A_orig = A_rat := by
      ext z
      simp only [Set.mem_preimage, A_orig, A_rat, Set.mem_ofPred_eq]
      refine forall₂_congr fun p _ => ?_
      have hsum : ∑ s : Fin k, ((aCoeff p s : ℚ) : ℝ) * ‖eVec s‖ * (σ s * z s) =
          ∑ s : Fin k, ((cRat p s : ℚ) : ℝ) * z s := by
        refine Finset.sum_congr rfl fun s _ => ?_
        simp only [cRat, aCoeff, rRat, Rat.cast_mul, σ]
        have hne := (he_norm_pos s).ne'
        field_simp [hne]
      rw [hsum]
    have hmeas_sc : Measurable (fun z : Fin k → ℝ => fun s : Fin k => σ s * z s) :=
      Measurable.of_eval fun s => (continuous_const.mul (continuous_apply s)).measurable
    rw [Measure.real_def, Measure.real_def, ← hpre,
      ← Measure.map_apply hmeas_sc hA_orig_meas, hmap_ν]
  rw [hA_rat_eq]
  have hν_prob : ∀ s : Fin k, IsProbabilityMeasure (ν s) := fun s =>
    ProbabilityTheory.instIsProbabilityMeasureGaussianReal 0 _
  have htv := abs_pi_measureReal_sub_le (μ := fun _ : Fin k => gaussianReal 0 1) (ν := ν)
    (τ := 1 / (Msqrt : ℝ)) (by positivity)
    (fun s _ hS => (abs_gaussianReal_sub_scaled_le (hσ_bounds s).1 hS).trans
      (by linarith [(hσ_bounds s).2])) hA_orig_meas
  refine htv.trans ?_
  have hk_r : (k : ℝ) ≤ (d : ℝ) := by exact_mod_cast hk_le
  calc (k : ℝ) * (1 / (Msqrt : ℝ)) ≤ (d : ℝ) * (1 / (Msqrt : ℝ)) := by gcongr
    _ = 1 / (4 * (invDelta : ℝ)) := by
      subst hMsqrt; push_cast; field_simp [hd_pos.ne', hinv_pos.ne']

/-- Helper bounding Step 3 (tail, slab, and 1D Riemann weight error) with all parameters
abstract so `Nat.log` is never unfolded during `whnf`. -/
private theorem approxClauseProb_step3_err {d invDelta R0 H0 Bexp Kexp Wscale Msqrt : ℕ}
    (hd : 1 ≤ d) (hinv : 1 ≤ invDelta) (hR0_ge2 : 2 ≤ R0) (hH0 : 0 < H0) (hWs : 0 < Wscale)
    (hH0_eq : H0 = 64 * d * d * R0 * R0 * invDelta)
    (hWs_eq : Wscale = 64 * d * R0 * invDelta)
    (hK : 3 * (R0 * R0) + 2 * Bexp + 2 ≤ Kexp)
    (hR0_pow : 32 * d * invDelta ≤ 2 ^ R0)
    (hBexp_pow : 64 * d * R0 * invDelta ≤ 2 ^ Bexp)
    (cl : List (List ℚ × ℚ)) (hcl_len : cl.length ≤ d)
    (basis : List (List ℚ)) (hk_le : basis.length ≤ d) :
    let k := basis.length
    let Glen := 2 * R0 * H0
    let cRat : (List ℚ × ℚ) → Fin k → ℚ := fun p s =>
      (ratDot p.1 basis[s] / ratDot basis[s] basis[s]) *
        ratSqrtUpper (ratDot basis[s] basis[s]) Msqrt
    let A_rat : Set (Fin k → ℝ) :=
      {z | ∀ p ∈ cl, (p.2 : ℝ) < ∑ s : Fin k, ((cRat p s : ℚ) : ℝ) * z s}
    let gridPts : List (ℚ × ℕ) := (List.range Glen).map fun (m : ℕ) =>
      let u : ℚ := -((R0 : ℚ)) + (m : ℚ) / (H0 : ℚ)
      let w : ℕ := (Rat.floor ((Wscale : ℚ) * ratExpNeg (u * u / 2) Kexp)).toNat
      (u, w)
    let scaledBasis := basis.zip (basis.map fun e => ratSqrtUpper (ratDot e e) Msqrt)
    let remCl := cl.map fun p =>
      (scaledBasis.map fun er => (ratDot p.1 er.1 / ratDot er.1 er.1) * er.2, p.2)
    |(Measure.pi fun _ : Fin k => gaussianReal 0 1).real A_rat -
      (evalGridSum k gridPts remCl : ℝ) / (((gridPts.map Prod.snd).sum : ℕ) : ℝ) ^ k| ≤
      3 / (4 * (invDelta : ℝ)) := by
  intro k Glen cRat A_rat gridPts scaledBasis remCl
  have hR0_pos : (0 : ℝ) < (R0 : ℝ) := Nat.cast_pos.mpr (by omega)
  have hd_pos : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr hd
  have hinv_pos : (0 : ℝ) < (invDelta : ℝ) := Nat.cast_pos.mpr hinv
  have hH0_rpos : (0 : ℝ) < (H0 : ℝ) := Nat.cast_pos.mpr hH0
  have hA_rat_meas : MeasurableSet A_rat := by
    have hcl_fin : A_rat = ⋂ p ∈ cl.toFinset,
        {z : Fin k → ℝ | (p.2 : ℝ) < ∑ s : Fin k, ((cRat p s : ℚ) : ℝ) * z s} := by
      ext z; simp [A_rat]
    rw [hcl_fin]
    exact Finset.measurableSet_biInter _ fun _ _ =>
      (isOpen_lt continuous_const (by fun_prop)).measurableSet
  let uPt : Fin Glen → ℝ := fun m => -((R0 : ℝ)) + (m.1 : ℝ) / (H0 : ℝ)
  let cube1D : Fin Glen → Set ℝ := fun m => Ico (uPt m) (uPt m + 1 / (H0 : ℝ))
  let box1D : Set ℝ := Ico (-(R0 : ℝ)) (R0 : ℝ)
  let boxK : Set (Fin k → ℝ) := Set.univ.pi fun _ => box1D
  let cubeK : (Fin k → Fin Glen) → Set (Fin k → ℝ) := fun z => Set.univ.pi fun s => cube1D (z s)
  obtain ⟨hcube1D_disj, hcube1D_union⟩ := cube1D_disj_union (R0 := R0) hH0
  have hcubeK_disj : Pairwise fun z₁ z₂ : Fin k → Fin Glen => Disjoint (cubeK z₁) (cubeK z₂) := by
    intro z₁ z₂ hne
    obtain ⟨s, hs⟩ : ∃ s, z₁ s ≠ z₂ s := Function.ne_iff.mp hne
    exact Set.disjoint_left.mpr fun y hy₁ hy₂ =>
      Set.disjoint_left.mp (hcube1D_disj hs) (hy₁ s trivial) (hy₂ s trivial)
  classical
  let S_grid : Finset (Fin k → Fin Glen) :=
    Finset.univ.filter fun z => (fun s => uPt (z s)) ∈ A_rat
  let U_grid : Set (Fin k → ℝ) := ⋃ z ∈ S_grid, cubeK z
  have hboxK_meas : MeasurableSet boxK := MeasurableSet.univ_pi fun _ => measurableSet_Ico
  have htail_err : (Measure.pi fun _ : Fin k => gaussianReal 0 1).real boxKᶜ ≤
      (k : ℝ) * (1 / (2 : ℝ) ^ R0) := by
    have hcompl_sub : boxKᶜ ⊆ ⋃ s : Fin k, {y : Fin k → ℝ | (R0 : ℝ) ≤ |y s|} := by
      intro y hy
      simp only [boxK, Set.mem_compl_iff, Set.mem_pi, Set.mem_univ, forall_true_left, box1D,
        Set.mem_Ico, not_forall, not_and_or, not_le, not_lt] at hy
      obtain ⟨s, hs⟩ := hy
      refine Set.mem_iUnion.mpr ⟨s, ?_⟩
      rcases hs with hlt | hge
      · exact (le_of_lt (by linarith)).trans (neg_le_abs (y s))
      · exact hge.trans (le_abs_self (y s))
    calc (Measure.pi fun _ : Fin k => gaussianReal 0 1).real boxKᶜ
        ≤ (Measure.pi fun _ : Fin k => gaussianReal 0 1).real
            (⋃ s : Fin k, {y : Fin k → ℝ | (R0 : ℝ) ≤ |y s|}) := measureReal_mono hcompl_sub
      _ ≤ ∑ s : Fin k, (Measure.pi fun _ : Fin k => gaussianReal 0 1).real
            {y : Fin k → ℝ | (R0 : ℝ) ≤ |y s|} := measureReal_iUnion_fintype_le _
      _ = ∑ _s : Fin k, (gaussianReal 0 1).real {x : ℝ | (R0 : ℝ) ≤ |x|} := by
          refine Finset.sum_congr rfl fun s _ => ?_
          have hpre : (fun y : Fin k → ℝ => y s) ⁻¹' {x : ℝ | (R0 : ℝ) ≤ |x|} =
              {y : Fin k → ℝ | (R0 : ℝ) ≤ |y s|} := rfl
          rw [← hpre, (MeasureTheory.measurePreserving_eval _ s).measureReal_preimage
            ((isClosed_le continuous_const continuous_abs).measurableSet.nullMeasurableSet)]
      _ ≤ ∑ _s : Fin k, (1 / (2 : ℝ) ^ R0) :=
          Finset.sum_le_sum fun _ _ => gaussianReal_abs_ge_le_two_pow hR0_ge2
      _ = (k : ℝ) * (1 / (2 : ℝ) ^ R0) := by simp
  have hA_box_err : |(Measure.pi fun _ : Fin k => gaussianReal 0 1).real A_rat -
      (Measure.pi fun _ : Fin k => gaussianReal 0 1).real (A_rat ∩ boxK)| ≤
      (k : ℝ) * (1 / (2 : ℝ) ^ R0) := by
    have hunion := measureReal_union (μ := Measure.pi fun _ : Fin k => gaussianReal 0 1)
      (Disjoint.mono Set.inter_subset_right Set.inter_subset_right disjoint_compl_right)
      (hA_rat_meas.inter hboxK_meas.compl)
    rw [Set.inter_union_compl A_rat boxK] at hunion
    rw [hunion, add_sub_cancel_left, abs_of_nonneg measureReal_nonneg]
    exact (measureReal_mono Set.inter_subset_right).trans htail_err
  have hslab_err : |(Measure.pi fun _ : Fin k => gaussianReal 0 1).real (A_rat ∩ boxK) -
      (Measure.pi fun _ : Fin k => gaussianReal 0 1).real U_grid| ≤
      (d : ℝ) * (d : ℝ) / (H0 : ℝ) := by
    have hU_same : U_grid =
        ⋃ z ∈ (Finset.univ.filter fun z : Fin k → Fin Glen =>
          @Decidable.decide ((fun s => uPt (z s)) ∈ A_rat) (Classical.propDecidable _)),
          cubeK z := by
      ext y
      simp only [U_grid, S_grid, Set.mem_iUnion, Finset.mem_filter, Finset.mem_univ, true_and,
        decide_eq_true_eq]
    rw [hU_same]
    exact approxClauseProb_slab_err (R0 := R0) hd hk_le hH0 cl hcl_len cRat
  let p1D : Fin Glen → ℝ := fun m => (gaussianReal 0 1).real (cube1D m)
  let c_pi : ℝ := Real.sqrt (2 * Real.pi)
  have hc_pi_pos : 0 < c_pi := by
    have h2 : (1 : ℝ) ≤ c_pi := by
      simpa [c_pi] using Real.sqrt_le_sqrt (by linarith [Real.pi_gt_three] : (1 : ℝ) ≤ 2 * Real.pi)
    linarith
  let uRat : Fin Glen → ℚ := fun m => -((R0 : ℚ)) + (m.1 : ℚ) / (H0 : ℚ)
  let wInt : Fin Glen → ℕ := fun m =>
    (Rat.floor ((Wscale : ℚ) * ratExpNeg (uRat m * uRat m / 2) Kexp)).toNat
  let γ1D : Fin Glen → ℝ := fun m => ((wInt m : ℝ) / (Wscale : ℝ)) / (H0 : ℝ) / c_pi
  have hp1D_nn : ∀ m, 0 ≤ p1D m := fun _ => measureReal_nonneg
  have hγ1D_nn : ∀ m, 0 ≤ γ1D m := fun _ => by positivity
  have hp1D_sum_le : ∑ m : Fin Glen, p1D m ≤ 1 := by
    have hdisj_sum := measureReal_iUnion_fintype (μ := gaussianReal 0 1)
      hcube1D_disj (fun _ => measurableSet_Ico) (fun _ => measure_ne_top _ _)
    rw [hcube1D_union] at hdisj_sum; rw [← hdisj_sum]; exact measureReal_le_one
  set Γ : ℝ := ∑ m : Fin Glen, γ1D m
  obtain ⟨hΓ_pos, hl1_pq⟩ := approxClauseProb_l1_weights_le hd hinv hR0_ge2
    hH0 hWs hH0_eq hWs_eq hK hR0_pow hBexp_pow
  change 0 < Γ at hΓ_pos
  change ∑ m : Fin Glen, |p1D m - γ1D m / Γ| ≤ 7 / (32 * (d : ℝ) * (invDelta : ℝ)) at hl1_pq
  let q1D : Fin Glen → ℝ := fun m => γ1D m / Γ
  have hq1D_nn : ∀ m, 0 ≤ q1D m := fun m => div_nonneg (hγ1D_nn m) hΓ_pos.le
  have hq1D_sum : ∑ m : Fin Glen, q1D m = 1 := by
    simp only [q1D, ← Finset.sum_div]; exact div_self hΓ_pos.ne'
  have hU_eq : (Measure.pi fun _ : Fin k => gaussianReal 0 1).real U_grid =
      ∑ z ∈ S_grid, ∏ s : Fin k, p1D (z s) := by
    rw [measureReal_biUnion_finset (fun z₁ _ z₂ _ hne => hcubeK_disj hne)
      (fun _ _ => MeasurableSet.univ_pi fun _ => measurableSet_Ico)
      (fun _ _ => measure_ne_top _ _)]
    refine Finset.sum_congr rfl fun z _ => ?_
    simp only [cubeK, p1D, Measure.real_def, Measure.pi_pi]; rw [ENNReal.toReal_prod]
  have happrox_eq : (evalGridSum k gridPts remCl : ℝ) / (((gridPts.map Prod.snd).sum : ℕ) : ℝ) ^ k =
      ∑ z ∈ S_grid, ∏ s : Fin k, q1D (z s) := by
    have hW1_pos : (0 : ℝ) < ((∑ m : Fin Glen, wInt m : ℕ) : ℝ) := by
      have hΓ_eq : Γ = (((∑ m : Fin Glen, wInt m : ℕ) : ℝ) / (Wscale : ℝ)) / (H0 : ℝ) / c_pi := by
        simp only [Γ, γ1D, ← Finset.sum_div, Nat.cast_sum]
      rw [hΓ_eq] at hΓ_pos
      have h1 := (div_pos_iff_of_pos_right hc_pi_pos).mp hΓ_pos
      have h2 := (div_pos_iff_of_pos_right hH0_rpos).mp h1
      exact (div_pos_iff_of_pos_right (by positivity : (0 : ℝ) < (Wscale : ℝ))).mp h2
    have hq_eq : ∀ m : Fin Glen, q1D m = (wInt m : ℝ) / ((∑ j : Fin Glen, wInt j : ℕ) : ℝ) := by
      intro m
      simp only [q1D, Γ, γ1D, ← Finset.sum_div, Nat.cast_sum]
      have hW_ne : (Wscale : ℝ) ≠ 0 := by positivity
      have hsum_ne : ((∑ j : Fin Glen, wInt j : ℕ) : ℝ) ≠ 0 := hW1_pos.ne'
      field_simp [hW_ne, hH0_rpos.ne', hc_pi_pos.ne', hsum_ne]
    have hgrid_len : gridPts.length = Glen := by simp [gridPts]
    have hW1_eq : (((gridPts.map Prod.snd).sum : ℕ) : ℝ) = ((∑ m : Fin Glen, wInt m : ℕ) : ℝ) := by
      congr 1
      simp only [gridPts, List.map_map, Function.comp_def]
      have hrange : ∀ (n : ℕ) (f : ℕ → ℕ), ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i :=
        fun n f => by
          induction n with
          | zero => simp
          | succ n ih => simp [List.range_succ, ih, Finset.sum_range_succ]
      rw [hrange, ← Fin.sum_univ_eq_sum_range]
    have hN_eq : (evalGridSum k gridPts remCl : ℝ) =
        ∑ z ∈ S_grid, ((∏ s : Fin k, wInt (z s) : ℕ) : ℝ) := by
      rw [evalGridSum_eq_sum_fin]
      let eG := finCongr hgrid_len
      let eFun : (Fin k → Fin gridPts.length) ≃ (Fin k → Fin Glen) :=
        ⟨fun f s => eG (f s), fun g s => eG.symm (g s),
          fun f => funext fun s => eG.symm_apply_apply (f s),
          fun g => funext fun s => eG.apply_symm_apply (g s)⟩
      rw [← Equiv.sum_comp eFun.symm, Finset.sum_filter]
      refine Finset.sum_congr rfl fun z _ => ?_
      have hpt_eq : ∀ s : Fin k, gridPts[eFun.symm z s] = (uRat (z s), wInt (z s)) :=
        fun s => by simp [gridPts, eFun, eG, uRat, wInt]
      have hcond_iff : (∀ p ∈ remCl, (p.2 : ℝ) <
            ∑ s : Fin k, ((p.1.getD s.1 0 : ℚ) : ℝ) * ((gridPts[eFun.symm z s]).1 : ℝ)) ↔
          (fun s => uPt (z s)) ∈ A_rat := by
        simp only [remCl, List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
          A_rat, Set.mem_ofPred_eq]
        refine forall₂_congr fun p _ => ?_
        have hsum : ∑ s : Fin k, (((scaledBasis.map fun er =>
            (ratDot p.1 er.1 / ratDot er.1 er.1) * er.2).getD s.1 0 : ℚ) : ℝ) *
              ((gridPts[eFun.symm z s]).1 : ℝ) =
            ∑ s : Fin k, ((cRat p s : ℚ) : ℝ) * uPt (z s) := by
          refine Finset.sum_congr rfl fun s _ => ?_
          rw [hpt_eq s]
          have hs_lt : s.1 < scaledBasis.length := by simp [scaledBasis, k]
          have hget : (scaledBasis.map fun er =>
              (ratDot p.1 er.1 / ratDot er.1 er.1) * er.2).getD s.1 0 = cRat p s := by
            rw [List.getD_eq_getElem _ _ (by simpa using hs_lt), List.getElem_map]
            simp [scaledBasis, cRat]
          rw [hget]; simp [uRat, uPt]
        rw [hsum]
      have hprod_eq : (∏ s : Fin k, (gridPts[eFun.symm z s]).2) = ∏ s : Fin k, wInt (z s) :=
        Finset.prod_congr rfl fun s _ => by rw [hpt_eq s]
      split_ifs
      · exact congrArg Nat.cast hprod_eq
      · rename_i ha hb; exact absurd (hcond_iff.mp ha) hb
      · rename_i ha hb; exact absurd (hcond_iff.mpr hb) ha
      · rfl
    rw [hN_eq, hW1_eq, Finset.sum_div]
    refine Finset.sum_congr rfl fun z _ => ?_
    have hpow_prod : (((∑ m : Fin Glen, wInt m : ℕ) : ℝ) ^ k) =
        ∏ _s : Fin k, ((∑ m : Fin Glen, wInt m : ℕ) : ℝ) := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [Nat.cast_prod, hpow_prod, ← Finset.prod_div_distrib]
    exact Finset.prod_congr rfl fun s _ => (hq_eq (z s)).symm
  have hgrid_err : |(Measure.pi fun _ : Fin k => gaussianReal 0 1).real U_grid -
      (evalGridSum k gridPts remCl : ℝ) / (((gridPts.map Prod.snd).sum : ℕ) : ℝ) ^ k| ≤
      7 * (k : ℝ) / (32 * (d : ℝ) * (invDelta : ℝ)) := by
    rw [hU_eq, happrox_eq, ← Finset.sum_sub_distrib]
    calc |∑ z ∈ S_grid, (∏ s : Fin k, p1D (z s) - ∏ s : Fin k, q1D (z s))|
        ≤ ∑ z ∈ S_grid, |∏ s : Fin k, p1D (z s) - ∏ s : Fin k, q1D (z s)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ z : Fin k → Fin Glen, |∏ s : Fin k, p1D (z s) - ∏ s : Fin k, q1D (z s)| :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => abs_nonneg _
      _ ≤ (k : ℝ) * ∑ m : Fin Glen, |p1D m - q1D m| :=
          sum_abs_prod_sub_le k hp1D_nn hq1D_nn hp1D_sum_le (by rw [hq1D_sum])
      _ ≤ (k : ℝ) * (7 / (32 * (d : ℝ) * (invDelta : ℝ))) :=
          mul_le_mul_of_nonneg_left hl1_pq (Nat.cast_nonneg k)
      _ = 7 * (k : ℝ) / (32 * (d : ℝ) * (invDelta : ℝ)) := by ring
  have hk_le_d : (k : ℝ) ≤ (d : ℝ) := by exact_mod_cast hk_le
  have htail_num : (k : ℝ) * (1 / (2 : ℝ) ^ R0) ≤ 1 / (32 * (invDelta : ℝ)) := by
    have h2 := one_div_le_one_div_of_le (by positivity)
      (by exact_mod_cast hR0_pow : (32 * (d : ℝ) * (invDelta : ℝ)) ≤ (2 : ℝ) ^ R0)
    calc (k : ℝ) * (1 / (2 : ℝ) ^ R0)
        ≤ (d : ℝ) * (1 / (32 * (d : ℝ) * (invDelta : ℝ))) :=
          mul_le_mul hk_le_d h2 (by positivity) (by positivity)
      _ = 1 / (32 * (invDelta : ℝ)) := by field_simp [hd_pos.ne', hinv_pos.ne']
  have hslab_num : (d : ℝ) * (d : ℝ) / (H0 : ℝ) ≤ 1 / (64 * (invDelta : ℝ)) := by
    have hH0_r : (H0 : ℝ) = 64 * (d : ℝ) ^ 2 * (R0 : ℝ) ^ 2 * (invDelta : ℝ) := by
      subst hH0_eq; push_cast; ring
    rw [hH0_r, show (d : ℝ) * (d : ℝ) / (64 * (d : ℝ) ^ 2 * (R0 : ℝ) ^ 2 * (invDelta : ℝ)) =
        1 / (64 * (invDelta : ℝ)) / (R0 : ℝ) ^ 2 by
      field_simp [hd_pos.ne', hR0_pos.ne', hinv_pos.ne'], div_le_iff₀ (by positivity)]
    have hR0_sq : (1 : ℝ) ≤ (R0 : ℝ) ^ 2 := by
      have : (1 : ℝ) ≤ (R0 : ℝ) := by exact_mod_cast (show 1 ≤ R0 by omega)
      nlinarith only [this]
    nlinarith only [hR0_sq, show (0 : ℝ) < 1 / (64 * (invDelta : ℝ)) by positivity]
  have hgrid_num : 7 * (k : ℝ) / (32 * (d : ℝ) * (invDelta : ℝ)) ≤ 7 / (32 * (invDelta : ℝ)) := by
    calc 7 * (k : ℝ) / (32 * (d : ℝ) * (invDelta : ℝ))
        ≤ 7 * (d : ℝ) / (32 * (d : ℝ) * (invDelta : ℝ)) :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hk_le_d (by norm_num))
            (by positivity)
      _ = 7 / (32 * (invDelta : ℝ)) := by field_simp [hd_pos.ne', hinv_pos.ne']
  set μk := Measure.pi fun _ : Fin k => gaussianReal 0 1
  set vAppr := (evalGridSum k gridPts remCl : ℝ) / (((gridPts.map Prod.snd).sum : ℕ) : ℝ) ^ k
  have htri : |μk.real A_rat - vAppr| ≤
      |μk.real A_rat - μk.real (A_rat ∩ boxK)| +
      |μk.real (A_rat ∩ boxK) - μk.real U_grid| + |μk.real U_grid - vAppr| := by
    linarith only [abs_sub_le (μk.real A_rat) (μk.real (A_rat ∩ boxK)) vAppr,
      abs_sub_le (μk.real (A_rat ∩ boxK)) (μk.real U_grid) vAppr]
  have hsum3 : 1 / (32 * (invDelta : ℝ)) + 1 / (64 * (invDelta : ℝ)) +
      7 / (32 * (invDelta : ℝ)) ≤ 3 / (4 * (invDelta : ℝ)) := by
    have h1 : 1 / (32 * (invDelta : ℝ)) + 1 / (64 * (invDelta : ℝ)) + 7 / (32 * (invDelta : ℝ)) =
        (17 / 64 : ℝ) * (1 / (invDelta : ℝ)) := by field_simp [hinv_pos.ne']; ring
    have h2 : 3 / (4 * (invDelta : ℝ)) = (48 / 64 : ℝ) * (1 / (invDelta : ℝ)) := by
      field_simp [hinv_pos.ne']; ring
    rw [h1, h2]; nlinarith only [show (0 : ℝ) < 1 / (invDelta : ℝ) by positivity]
  linarith only [htri, hA_box_err, htail_num, hslab_err, hslab_num, hgrid_err, hgrid_num, hsum3]

/-- **Additive accuracy of `approxClauseProb`**: for every `1 ≤ d`, `1 ≤ invDelta`, and
well-formed conjunction `cl` of length at most `d` with all vectors of length `N`,
`approxClauseProb d cl invDelta` estimates the `N`-dimensional Gaussian probability of `cl`
to within additive error `1 / invDelta`. -/
theorem abs_approxClauseProb_sub_le {N d invDelta : ℕ} (hd : 1 ≤ d) (hinv : 1 ≤ invDelta)
    {cl : List (List ℚ × ℚ)} (hcl_len : cl.length ≤ d) (hv_len : ∀ p ∈ cl, p.1.length = N) :
    |(approxClauseProb d cl invDelta : ℝ) -
      (stdGaussian (EuclideanSpace ℝ (Fin N))).real
        {x : EuclideanSpace ℝ (Fin N) |
          ∀ p ∈ cl, (p.2 : ℝ) < ⟪ratVecToEuclidean N p.1, x⟫}| ≤
      1 / (invDelta : ℝ) := by
  have htake_eq : cl.take d = cl := List.take_of_length_le hcl_len
  have hd1_eq : max 1 d = d := max_eq_right hd
  have hinv_eq : max 1 invDelta = invDelta := max_eq_right hinv
  set R0 : ℕ := Nat.log 2 (32 * d * invDelta) + 3
  set H0 : ℕ := 64 * d * d * R0 * R0 * invDelta
  set Bexp : ℕ := Nat.log 2 (64 * d * R0 * invDelta) + 2
  set Kexp : ℕ := 3 * R0 * R0 + 2 * Bexp + 2
  set Wscale : ℕ := 64 * d * R0 * invDelta
  set Msqrt : ℕ := 4 * d * invDelta
  set basis := ratGramSchmidtBounded d (cl.map Prod.fst)
  set k : ℕ := basis.length
  have hk_le : k ≤ d := (ratGramSchmidtBounded_spec (by simpa using hcl_len)
    (fun v hv => by rcases List.mem_map.mp hv with ⟨p, hp, rfl⟩; exact hv_len p hp)).1
  have hR0_pow : 32 * d * invDelta ≤ 2 ^ R0 :=
    (Nat.lt_pow_succ_log_self (by norm_num) _).le.trans
      (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hBexp_pow : 64 * d * R0 * invDelta ≤ 2 ^ Bexp :=
    (Nat.lt_pow_succ_log_self (by norm_num) _).le.trans
      (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hR0_pos : 0 < R0 := by omega
  have hH0_pos : 0 < H0 := by positivity
  have hW_pos : 0 < Wscale := by positivity
  have hrot_scale := approxClauseProb_rot_scale_err (Msqrt := Msqrt) hd hinv rfl hcl_len hv_len
  have hstep3 := approxClauseProb_step3_err (R0 := R0) (H0 := H0) (Bexp := Bexp) (Kexp := Kexp)
    (Wscale := Wscale) (Msqrt := Msqrt) hd hinv (by omega) hH0_pos hW_pos rfl rfl
    (le_of_eq (by dsimp only [Kexp]; ring)) hR0_pow hBexp_pow cl hcl_len basis hk_le
  let gridPts : List (ℚ × ℕ) := (List.range (2 * R0 * H0)).map fun (m : ℕ) =>
    let u : ℚ := -((R0 : ℚ)) + (m : ℚ) / (H0 : ℚ)
    (u, (Rat.floor ((Wscale : ℚ) * ratExpNeg (u * u / 2) Kexp)).toNat)
  let remCl := cl.map fun p =>
    ((basis.zip (basis.map fun e => ratSqrtUpper (ratDot e e) Msqrt)).map fun er =>
      (ratDot p.1 er.1 / ratDot er.1 er.1) * er.2, p.2)
  have happrox_val : (approxClauseProb d cl invDelta : ℝ) =
      (evalGridSum k gridPts remCl : ℝ) / (((gridPts.map Prod.snd).sum : ℕ) : ℝ) ^ k := by
    unfold approxClauseProb; simp only [hd1_eq, hinv_eq, htake_eq]
    rw [evalGridSumLe_eq_of_le hk_le, Rat.cast_divInt]
    simp only [Int.cast_pow, Int.cast_natCast, Nat.cast_pow]; rfl
  rw [abs_sub_comm, happrox_val]
  have hinv_pos : (0 : ℝ) < (invDelta : ℝ) := Nat.cast_pos.mpr hinv
  have hsum_final : 1 / (4 * (invDelta : ℝ)) + 3 / (4 * (invDelta : ℝ)) = 1 / (invDelta : ℝ) := by
    field_simp [hinv_pos.ne']; ring
  exact (abs_sub_le _ _ _).trans (by linarith only [hrot_scale, hstep3, hsum_final])

end CslibFrontier.Foundations.Probability.Gaussian
