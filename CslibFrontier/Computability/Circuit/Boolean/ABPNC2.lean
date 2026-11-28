/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.AlgebraicBranchingProgram
public import CslibFrontier.Computability.Circuit.Boolean.LayeredCircuitClasses
public import Cslib.Computability.Circuit.Basic
public import Cslib.Computability.Circuit.Composition
public import Cslib.Computability.Languages.Slice
public import CslibFrontier.Computability.Circuit.Boolean.DepthClasses
public import CslibFrontier.Computability.Circuit.Boolean.Formula
public import CslibFrontier.Computability.Circuit.CompositionDepth
public import CslibFrontier.Computability.Circuit.Monotone.Basic
public import CslibFrontier.Foundations.Data.Nat.PolynomialBound.Closure
public import CslibFrontier.Foundations.Data.Nat.PolynomialBound.Log

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Simulation of Algebraic Branching Programs over `ZMod p` in `NC²`

This module simulates algebraic branching programs over `ZMod p` by polynomial-size,
`O(log² n)`-depth Boolean circuits via one-hot `ZMod p` encoding and repeated squaring of
strictly upper-triangular path-sum matrices, establishing `NuDet p ⊆ NC 2`, closure of `NC 2`
under constant-height composition, `NuItDet ⊆ NC 2`, and `NuItDetCompMON ⊆ NC2CompMON`.

## Main results

* `CslibFrontier.Computability.Circuit.abpGate_to_deMorgan`: every `ZMod p` ABP gate of size `s` is
  simulated by a De Morgan Boolean circuit of depth `O((log₂ (s + 2))²)` and size `O(p³ s⁵)`.
* `CslibFrontier.Computability.Circuit.NuDet_subset_NC_two`: `NuDet p ⊆ NC 2`.
* `CslibFrontier.Computability.Circuit.NC2_comp_closed`: `NC 2` is closed under constant-height
  layered composition.
* `CslibFrontier.Computability.Circuit.NuItDet_subset_NC_two`: `NuItDet ⊆ NC 2`.
* `CslibFrontier.Computability.Circuit.NuItDetCompMON_subset_NC2CompMON`:
  `NuItDetCompMON ⊆ NC2CompMON`.
-/

public section

namespace CslibFrontier.Computability.Circuit

open Cslib
open Cslib.Circuits
open Cslib.Circuits.Boolean
open Cslib.Circuits.Monotone
open scoped Matrix

/-! ### `NuDet p ⊆ NC²` via One-Hot `ZMod p` Repeated Squaring -/

section OneHotNC2

/-- One-hot encoding of `a : ZMod p` as `Fin p → Bool`: bit `r` is `true` iff `a = r`. -/
private def oneHotZMod {p : ℕ} (a : ZMod p) : Fin p → Bool :=
  fun r => decide (a = (r.1 : ZMod p))

private theorem oneHotZMod_eq_true {p : ℕ} (a : ZMod p) (r : Fin p) :
    oneHotZMod a r = true ↔ a = (r.1 : ZMod p) := by
  simp [oneHotZMod]

/-- Constant one-hot circuit outputting `oneHotZMod c` in depth `1` and size `p`. -/
private def constOneHotCircuit (p : ℕ) (c : ZMod p) : Circuit Boolean.signature 0 p :=
  (appendCircuits (fun r : Fin p => (Formula.const (oneHotZMod c r)).toCircuit)).comapOutputs
    (fun r => finProdFinEquiv (r, 0))

private theorem eval_constOneHotCircuit {p : ℕ} (c : ZMod p) (x : Fin 0 → Bool) :
    (constOneHotCircuit p c).eval Boolean.interpretation x = oneHotZMod c := by
  funext r
  simp [constOneHotCircuit, Circuit.eval_comapOutputs, eval_appendCircuits,
    Formula.eval_toCircuit, Formula.eval_const]

private theorem size_constOneHotCircuit {p : ℕ} (c : ZMod p) :
    (constOneHotCircuit p c).size = p := by
  simp [constOneHotCircuit, size_appendCircuits, Formula.size_toCircuit, Formula.size_const]

private theorem depth_constOneHotCircuit {p : ℕ} (c : ZMod p) :
    (constOneHotCircuit p c).depth ≤ 1 := by
  refine (depth_comapOutputs_le _ _).trans ?_
  refine depth_appendCircuits_le _ fun r => ?_
  exact (Formula.depth_toCircuit_le _).trans (by simp [Formula.depth_const])

/-- De Morgan circuit computing one-hot `ZMod p` addition `a + b`. -/
private def addOneHotCircuit (p : ℕ) [NeZero p] : Circuit Boolean.signature (p + p) p :=
  let bitFormula (r : Fin p) : Formula Boolean.signature (p + p) :=
    Formula.orList <| (List.finRange p).map fun s : Fin p =>
      let t : Fin p := ⟨(r.1 + p - s.1) % p, Nat.mod_lt _ (NeZero.pos p)⟩
      (Formula.input (Fin.castAdd p s)).and (Formula.input (Fin.natAdd p t))
  (appendCircuits (fun r : Fin p => (bitFormula r).toCircuit)).comapOutputs
    (fun r => finProdFinEquiv (r, 0))

private theorem eval_addOneHotCircuit {p : ℕ} [NeZero p] (a b : ZMod p) :
    (addOneHotCircuit p).eval Boolean.interpretation (Fin.append (oneHotZMod a) (oneHotZMod b)) =
      oneHotZMod (a + b) := by
  funext r
  rw [Bool.eq_iff_iff]
  simp only [addOneHotCircuit, Circuit.eval_comapOutputs, eval_appendCircuits,
    Formula.eval_toCircuit, Formula.eval_orList, List.any_map, List.any_eq_true,
    Function.comp_apply, List.mem_finRange, true_and, Formula.eval_and, Formula.eval_input,
    Fin.append_left, Fin.append_right, Bool.and_eq_true, oneHotZMod_eq_true]
  constructor
  · rintro ⟨s, ha, hb⟩
    rw [ha, hb, ← Nat.cast_add]
    have hmod : (s.1 + (r.1 + p - s.1) % p) % p = r.1 % p := by
      rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
      have hs : s.1 < p := s.2
      rw [show s.1 + (r.1 + p - s.1) = r.1 + p by omega, Nat.add_mod_right]
    exact (ZMod.natCast_eq_natCast_iff' _ _ p).mpr hmod
  · intro hab
    let s : Fin p := ⟨a.val, a.val_lt⟩
    refine ⟨s, (ZMod.natCast_zmod_val a).symm, ?_⟩
    have h1 : (s.1 : ZMod p) + ((r.1 + p - s.1) % p : ℕ) = (r.1 : ZMod p) := by
      rw [← Nat.cast_add]
      apply (ZMod.natCast_eq_natCast_iff' _ _ p).mpr
      rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
      have hs : s.1 < p := s.2
      rw [show s.1 + (r.1 + p - s.1) = r.1 + p by omega, Nat.add_mod_right]
    have ha' : (s.1 : ZMod p) = a := ZMod.natCast_zmod_val a
    rw [ha'] at h1
    have hb' : a + b = a + (((r.1 + p - s.1) % p : ℕ) : ZMod p) := hab.trans h1.symm
    exact add_left_cancel hb'

/-- De Morgan circuit computing one-hot `ZMod p` multiplication `a * b`. -/
private def mulOneHotCircuit (p : ℕ) : Circuit Boolean.signature (p + p) p :=
  let bitFormula (r : Fin p) : Formula Boolean.signature (p + p) :=
    Formula.orList <|
      ((List.finRange p).flatMap fun s : Fin p =>
        ((List.finRange p).filter fun t : Fin p =>
          decide ((s.1 * t.1) % p = r.1)).map fun t =>
            (Formula.input (Fin.castAdd p s)).and (Formula.input (Fin.natAdd p t)))
  (appendCircuits (fun r : Fin p => (bitFormula r).toCircuit)).comapOutputs
    (fun r => finProdFinEquiv (r, 0))

private theorem eval_mulOneHotCircuit {p : ℕ} [NeZero p] (a b : ZMod p) :
    (mulOneHotCircuit p).eval Boolean.interpretation (Fin.append (oneHotZMod a) (oneHotZMod b)) =
      oneHotZMod (a * b) := by
  funext r
  rw [Bool.eq_iff_iff]
  simp only [mulOneHotCircuit, Circuit.eval_comapOutputs, Function.comp_apply, eval_appendCircuits,
    Formula.eval_toCircuit, Formula.eval_orList, List.any_eq_true, List.mem_flatMap,
    List.mem_map, List.mem_filter, List.mem_finRange, true_and, oneHotZMod_eq_true]
  constructor
  · rintro ⟨_, ⟨s, ⟨t, hst, rfl⟩⟩, hev⟩
    simp only [Formula.eval_and, Formula.eval_input, Fin.append_left, Fin.append_right,
      Bool.and_eq_true, oneHotZMod_eq_true] at hev
    obtain ⟨ha, hb⟩ := hev
    rw [ha, hb, ← Nat.cast_mul]
    have hmod := of_decide_eq_true hst
    exact (ZMod.natCast_eq_natCast_iff' _ _ p).mpr (hmod.trans (Nat.mod_eq_of_lt r.2).symm)
  · intro hab
    let s : Fin p := ⟨a.val, a.val_lt⟩
    let t : Fin p := ⟨b.val, b.val_lt⟩
    have ha : a = (s.1 : ZMod p) := (ZMod.natCast_zmod_val a).symm
    have hb : b = (t.1 : ZMod p) := (ZMod.natCast_zmod_val b).symm
    have hst : (s.1 * t.1) % p = r.1 := by
      have hcast : ((s.1 * t.1 : ℕ) : ZMod p) = (r.1 : ZMod p) := by
        rw [Nat.cast_mul, ← ha, ← hb, hab]
      have hmod := (ZMod.natCast_eq_natCast_iff' _ _ p).mp hcast
      rwa [Nat.mod_eq_of_lt r.2] at hmod
    refine ⟨(Formula.input (Fin.castAdd p s)).and (Formula.input (Fin.natAdd p t)),
      ⟨s, ⟨t, decide_eq_true hst, rfl⟩⟩, ?_⟩
    simp only [Formula.eval_and, Formula.eval_input, Fin.append_left, Fin.append_right,
      Bool.and_eq_true, oneHotZMod_eq_true, ha, hb, and_self]

/-- Balanced binary-tree sum of `k` one-hot `ZMod p` elements. -/
private def sumOneHotTree (p : ℕ) [NeZero p] :
    (k : ℕ) → Circuit Boolean.signature (k * p) p
  | 0 => (constOneHotCircuit p 0).mapInputs Fin.elim0
  | 1 => Circuit.wiring Boolean.signature (fun r => r.cast (by ring))
  | k + 2 =>
    let k₁ := (k + 2) / 2
    let k₂ := (k + 2) - k₁
    have hk₁ : k₁ < k + 2 := by omega
    have hk₂ : k₂ < k + 2 := by omega
    let left : Circuit Boolean.signature ((k + 2) * p) p :=
      (sumOneHotTree p k₁).mapInputs (fun idx => ⟨idx.1, by
        have := idx.2; exact lt_of_lt_of_le this (Nat.mul_le_mul_right p (by omega))⟩)
    let right : Circuit Boolean.signature ((k + 2) * p) p :=
      (sumOneHotTree p k₂).mapInputs (fun idx => ⟨k₁ * p + idx.1, by
        have := idx.2
        calc k₁ * p + idx.1 < k₁ * p + k₂ * p := Nat.add_lt_add_left this _
          _ = (k₁ + k₂) * p := (Nat.add_mul k₁ k₂ p).symm
          _ = (k + 2) * p := by rw [show k₁ + k₂ = k + 2 by omega]⟩)
    (addOneHotCircuit p).comp (left.append right)
termination_by k => k

private theorem eval_sumOneHotTree {p : ℕ} [NeZero p] :
    ∀ (k : ℕ) (a : Fin k → ZMod p),
      (sumOneHotTree p k).eval Boolean.interpretation
        (fun idx => oneHotZMod (a (finProdFinEquiv.symm idx).1) (finProdFinEquiv.symm idx).2) =
      oneHotZMod (∑ i : Fin k, a i) := by
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro a
    match k with
    | 0 =>
      simp only [sumOneHotTree, Circuit.eval_mapInputs, eval_constOneHotCircuit,
        Finset.univ_eq_empty, Finset.sum_empty]
    | 1 =>
      funext r
      simp only [sumOneHotTree, Circuit.eval_wiring, Function.comp_apply, Fin.sum_univ_one]
      congr 2
      · have h1 : (finProdFinEquiv.symm (r.cast (by ring : p = 1 * p))).1 = 0 :=
          Subsingleton.elim _ _
        rw [h1]
      · ext; simp [finProdFinEquiv, Fin.modNat, Nat.mod_eq_of_lt r.2]
    | k + 2 =>
      let k₁ := (k + 2) / 2
      let k₂ := (k + 2) - k₁
      have hk₁ : k₁ < k + 2 := by omega
      have hk₂ : k₂ < k + 2 := by omega
      have hk_sum : k₁ + k₂ = k + 2 := by omega
      simp only [sumOneHotTree, Circuit.eval_comp, Circuit.eval_append, Circuit.eval_mapInputs]
      have hleft : ∀ (mapL : Fin (k₁ * p) → Fin ((k + 2) * p)),
          (∀ idx, (mapL idx).1 = idx.1) →
          (sumOneHotTree p k₁).eval Boolean.interpretation
            (fun idx => oneHotZMod (a (finProdFinEquiv.symm (mapL idx)).1)
              (finProdFinEquiv.symm (mapL idx)).2) =
          oneHotZMod (∑ i : Fin k₁, a ⟨i.1, by omega⟩) := by
        intro mapL hmapL
        have hfn : (fun idx : Fin (k₁ * p) =>
            oneHotZMod (a (finProdFinEquiv.symm (mapL idx)).1)
              (finProdFinEquiv.symm (mapL idx)).2) =
            (fun idx : Fin (k₁ * p) =>
              oneHotZMod (a ⟨(finProdFinEquiv.symm idx).1.1, by omega⟩)
                (finProdFinEquiv.symm idx).2) := by
          funext idx
          have hdiv : (finProdFinEquiv.symm (mapL idx)).1.1 = (finProdFinEquiv.symm idx).1.1 := by
            simp [finProdFinEquiv, hmapL idx]
          have hmod : (finProdFinEquiv.symm (mapL idx)).2 = (finProdFinEquiv.symm idx).2 := by
            ext; simp [finProdFinEquiv, hmapL idx]
          rw [hmod]; congr 2; exact Fin.ext hdiv
        rw [hfn]
        exact ih k₁ hk₁ (fun i => a ⟨i.1, by omega⟩)
      have hright : ∀ (mapR : Fin (k₂ * p) → Fin ((k + 2) * p)),
          (∀ idx, (mapR idx).1 = k₁ * p + idx.1) →
          (sumOneHotTree p k₂).eval Boolean.interpretation
            (fun idx => oneHotZMod (a (finProdFinEquiv.symm (mapR idx)).1)
              (finProdFinEquiv.symm (mapR idx)).2) =
          oneHotZMod (∑ j : Fin k₂, a ⟨k₁ + j.1, by omega⟩) := by
        intro mapR hmapR
        have hfn : (fun idx : Fin (k₂ * p) =>
            oneHotZMod (a (finProdFinEquiv.symm (mapR idx)).1)
              (finProdFinEquiv.symm (mapR idx)).2) =
            (fun idx : Fin (k₂ * p) =>
              oneHotZMod (a ⟨k₁ + (finProdFinEquiv.symm idx).1.1, by omega⟩)
                (finProdFinEquiv.symm idx).2) := by
          funext idx
          have hp_pos : 0 < p := NeZero.pos p
          have hdiv : (k₁ * p + idx.1) / p = k₁ + idx.1 / p := by
            rw [Nat.add_comm, Nat.add_mul_div_right _ _ hp_pos, Nat.add_comm]
          have h1 : (finProdFinEquiv.symm (mapR idx)).1.1 =
              k₁ + (finProdFinEquiv.symm idx).1.1 := by
            simpa [finProdFinEquiv, hmapR idx] using hdiv
          have h2 : (finProdFinEquiv.symm (mapR idx)).2 = (finProdFinEquiv.symm idx).2 := by
            ext; simp [finProdFinEquiv, hmapR idx]
          rw [h2]; congr 2; exact Fin.ext h1
        rw [hfn]
        exact ih k₂ hk₂ (fun j => a ⟨k₁ + j.1, by omega⟩)
      rw [show (fun idx => oneHotZMod (a (finProdFinEquiv.symm _).1)
            (finProdFinEquiv.symm _).2) ∘ _ = _ from rfl]
      erw [hleft _ (fun _ => rfl), hright _ (fun _ => rfl), eval_addOneHotCircuit]
      congr 1
      have hsplit : (∑ i : Fin (k + 2), a i) =
          (∑ i : Fin k₁, a ⟨i.1, by omega⟩) + (∑ j : Fin k₂, a ⟨k₁ + j.1, by omega⟩) := by
        rw [← (finCongr hk_sum).sum_comp, Fin.sum_univ_add]
        rfl
      exact hsplit.symm

private theorem size_sumOneHotTree_le {p : ℕ} [NeZero p] :
    ∀ k : ℕ, (sumOneHotTree p k).size ≤ ((addOneHotCircuit p).size + p) * (2 * k + 1) := by
  have hsharp : ∀ k : ℕ,
      (sumOneHotTree p k).size ≤
        ((addOneHotCircuit p).size + p) * (if k = 0 then 1 else k - 1) := by
    intro k
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      match k with
      | 0 => simp [sumOneHotTree, size_constOneHotCircuit]
      | 1 => simp [sumOneHotTree]
      | k + 2 =>
        let k₁ := (k + 2) / 2
        let k₂ := (k + 2) - k₁
        have hk₁ : k₁ < k + 2 := by omega
        have hk₂ : k₂ < k + 2 := by omega
        have h1 := ih k₁ hk₁
        have h2 := ih k₂ hk₂
        simp only [show k₁ ≠ 0 by omega, show k₂ ≠ 0 by omega, ↓reduceIte] at h1 h2
        simp only [sumOneHotTree, Circuit.size_comp, Circuit.size_append, Circuit.mapInputs_size,
          Nat.add_eq_zero_iff, OfNat.ofNat_ne_zero, and_false, ↓reduceIte]
        have hsum : (k₁ - 1) + (k₂ - 1) + 1 = k + 2 - 1 := by omega
        have hle : (sumOneHotTree p k₁).size + (sumOneHotTree p k₂).size +
            (addOneHotCircuit p).size ≤
            ((addOneHotCircuit p).size + p) * (k₁ - 1) +
              ((addOneHotCircuit p).size + p) * (k₂ - 1) +
              ((addOneHotCircuit p).size + p) * 1 := by
          have : (addOneHotCircuit p).size ≤ ((addOneHotCircuit p).size + p) * 1 := by omega
          exact add_le_add (add_le_add h1 h2) this
        calc (sumOneHotTree p k₁).size + (sumOneHotTree p k₂).size + (addOneHotCircuit p).size
            ≤ ((addOneHotCircuit p).size + p) * (k₁ - 1) +
              ((addOneHotCircuit p).size + p) * (k₂ - 1) +
              ((addOneHotCircuit p).size + p) * 1 := hle
          _ = ((addOneHotCircuit p).size + p) * ((k₁ - 1) + (k₂ - 1) + 1) := by ring
          _ = ((addOneHotCircuit p).size + p) * (k + 2 - 1) := by rw [hsum]
  intro k
  exact (hsharp k).trans (Nat.mul_le_mul_left _ (by split_ifs <;> omega))

private theorem depth_sumOneHotTree_le {p : ℕ} [NeZero p] :
    ∀ k : ℕ, (sumOneHotTree p k).depth ≤ (addOneHotCircuit p).depth * Nat.clog 2 k + 1 := by
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    match k with
    | 0 =>
      simp only [sumOneHotTree, depth_mapInputs, Nat.clog_zero_right, mul_zero, zero_add]
      exact depth_constOneHotCircuit 0
    | 1 => simp [sumOneHotTree]
    | k + 2 =>
      let k₁ := (k + 2) / 2
      let k₂ := (k + 2) - k₁
      have hk₁ : k₁ < k + 2 := by omega
      have hk₂ : k₂ < k + 2 := by omega
      have hpos : 1 ≤ Nat.clog 2 (k + 2) :=
        Nat.succ_le_of_lt ((Nat.lt_clog_iff_pow_lt (by omega)).mpr (by simp; omega))
      have hmul : (addOneHotCircuit p).depth +
            ((addOneHotCircuit p).depth * (Nat.clog 2 (k + 2) - 1) + 1) =
          (addOneHotCircuit p).depth * Nat.clog 2 (k + 2) + 1 := by
        have h1 : (addOneHotCircuit p).depth +
              (addOneHotCircuit p).depth * (Nat.clog 2 (k + 2) - 1) =
            (addOneHotCircuit p).depth * Nat.clog 2 (k + 2) := by
          calc (addOneHotCircuit p).depth + (addOneHotCircuit p).depth * (Nat.clog 2 (k + 2) - 1)
              = (addOneHotCircuit p).depth * (1 + (Nat.clog 2 (k + 2) - 1)) := by ring
            _ = (addOneHotCircuit p).depth * Nat.clog 2 (k + 2) := by congr 1; omega
        omega
      simp only [sumOneHotTree]
      refine (Circuit.depth_comp_le _ _).trans ?_
      refine (add_le_add le_rfl
        (show _ ≤ (addOneHotCircuit p).depth * (Nat.clog 2 (k + 2) - 1) + 1 from ?_)).trans
        (le_of_eq hmul)
      refine (Circuit.depth_append_le _ _).trans (max_le ?_ ?_)
      · rw [depth_mapInputs]
        have hclog : Nat.clog 2 k₁ ≤ Nat.clog 2 (k + 2) - 1 := by
          have hle : k₁ ≤ (k + 2 + 1) / 2 := by omega
          have h1 := Nat.clog_mono_right 2 hle
          have h2 : Nat.clog 2 (k + 2) = Nat.clog 2 ((k + 2 + 1) / 2) + 1 := by
            rw [Nat.clog_of_one_lt (by omega) (by omega), show k + 2 + 2 - 1 = k + 2 + 1 by omega]
          omega
        exact (ih k₁ hk₁).trans (by gcongr)
      · rw [depth_mapInputs]
        have hclog : Nat.clog 2 k₂ ≤ Nat.clog 2 (k + 2) - 1 := by
          have hle : k₂ ≤ (k + 2 + 1) / 2 := by omega
          have h1 := Nat.clog_mono_right 2 hle
          have h2 : Nat.clog 2 (k + 2) = Nat.clog 2 ((k + 2 + 1) / 2) + 1 := by
            rw [Nat.clog_of_one_lt (by omega) (by omega), show k + 2 + 2 - 1 = k + 2 + 1 by omega]
          omega
        exact (ih k₂ hk₂).trans (by gcongr)

/-- One-hot encoding of an `m × m` matrix `A` over `ZMod p` as `Fin (m * m * p) → Bool`. -/
private def oneHotMat {p m : ℕ} (A : Matrix (Fin m) (Fin m) (ZMod p)) :
    Fin (m * m * p) → Bool :=
  fun idx =>
    let q := finProdFinEquiv.symm idx
    let ij := finProdFinEquiv.symm q.1
    oneHotZMod (A ij.1 ij.2) q.2

/-- De Morgan circuit multiplying two `m × m` one-hot matrices over `ZMod p`. -/
private def matMulOneHotCircuit (p m : ℕ) [NeZero p] :
    Circuit Boolean.signature (m * m * p + m * m * p) (m * m * p) :=
  let entryCirc (i j : Fin m) : Circuit Boolean.signature (m * m * p + m * m * p) p :=
    let prodCirc (k : Fin m) : Circuit Boolean.signature (m * m * p + m * m * p) p :=
      (mulOneHotCircuit p).mapInputs (fun idx =>
        Fin.addCases
          (fun r => Fin.castAdd (m * m * p) (finProdFinEquiv (finProdFinEquiv (i, k), r)))
          (fun r => Fin.natAdd (m * m * p) (finProdFinEquiv (finProdFinEquiv (k, j), r)))
          idx)
    (sumOneHotTree p m).comp (appendCircuits prodCirc)
  appendCircuits (fun idx : Fin (m * m) =>
    entryCirc (finProdFinEquiv.symm idx).1 (finProdFinEquiv.symm idx).2)

private theorem eval_matMulOneHotCircuit {p m : ℕ} [NeZero p]
    (A B : Matrix (Fin m) (Fin m) (ZMod p)) :
    (matMulOneHotCircuit p m).eval Boolean.interpretation
      (Fin.append (oneHotMat A) (oneHotMat B)) = oneHotMat (A * B) := by
  funext idx
  obtain ⟨⟨q, r⟩, rfl⟩ := finProdFinEquiv.surjective idx
  obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective q
  simp only [matMulOneHotCircuit, eval_appendCircuits, Equiv.symm_apply_apply,
    Circuit.eval_comp, oneHotMat, Matrix.mul_apply]
  have hprod :
      (appendCircuits (fun k : Fin m =>
        (mulOneHotCircuit p).mapInputs (fun idx' =>
          Fin.addCases
            (fun r' => Fin.castAdd (m * m * p) (finProdFinEquiv (finProdFinEquiv (i, k), r')))
            (fun r' => Fin.natAdd (m * m * p) (finProdFinEquiv (finProdFinEquiv (k, j), r')))
            idx'))).eval Boolean.interpretation
          (Fin.append (oneHotMat A) (oneHotMat B)) =
      (fun idx' => oneHotZMod
        (A i (finProdFinEquiv.symm idx').1 * B (finProdFinEquiv.symm idx').1 j)
        (finProdFinEquiv.symm idx').2) := by
    funext idx'
    obtain ⟨⟨k, r'⟩, rfl⟩ := finProdFinEquiv.surjective idx'
    simp only [eval_appendCircuits, Equiv.symm_apply_apply, Circuit.eval_mapInputs]
    have hpair :
        (Fin.append (oneHotMat A) (oneHotMat B) ∘ fun idx'' =>
          Fin.addCases
            (fun r'' => Fin.castAdd (m * m * p) (finProdFinEquiv (finProdFinEquiv (i, k), r'')))
            (fun r'' => Fin.natAdd (m * m * p) (finProdFinEquiv (finProdFinEquiv (k, j), r'')))
            idx'') =
        Fin.append (oneHotZMod (A i k)) (oneHotZMod (B k j)) := by
      funext idx''
      induction idx'' using Fin.addCases <;>
        simp only [Fin.addCases_left, Fin.addCases_right, Fin.append_left, Fin.append_right,
          oneHotMat, Function.comp_apply, Equiv.symm_apply_apply]
    rw [hpair, eval_mulOneHotCircuit]
  rw [hprod, eval_sumOneHotTree m (fun k => A i k * B k j)]

private theorem size_matMulOneHotCircuit_le (p m : ℕ) [NeZero p] :
    (matMulOneHotCircuit p m).size ≤
      m * m * (m * (mulOneHotCircuit p).size + ((addOneHotCircuit p).size + p) * (2 * m + 1)) := by
  simp only [matMulOneHotCircuit, size_appendCircuits, Circuit.size_comp, Circuit.mapInputs_size]
  calc ∑ _ : Fin (m * m), ((∑ _ : Fin m, (mulOneHotCircuit p).size) + (sumOneHotTree p m).size)
      ≤ ∑ _ : Fin (m * m),
          (m * (mulOneHotCircuit p).size + ((addOneHotCircuit p).size + p) * (2 * m + 1)) := by
        refine Finset.sum_le_sum fun _ _ => ?_
        have h := size_sumOneHotTree_le (p := p) m
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
        omega
    _ = m * m *
          (m * (mulOneHotCircuit p).size + ((addOneHotCircuit p).size + p) * (2 * m + 1)) := by
        simp [mul_assoc]

private theorem depth_matMulOneHotCircuit_le (p m : ℕ) [NeZero p] :
    (matMulOneHotCircuit p m).depth ≤
      (addOneHotCircuit p).depth * Nat.clog 2 m + 1 + (mulOneHotCircuit p).depth := by
  simp only [matMulOneHotCircuit]
  refine depth_appendCircuits_le _ fun _ => (Circuit.depth_comp_le _ _).trans ?_
  have h1 := depth_sumOneHotTree_le (p := p) m
  refine (add_le_add h1 (show _ ≤ (mulOneHotCircuit p).depth from ?_)).trans (by omega)
  exact depth_appendCircuits_le _ fun _ => by rw [depth_mapInputs]

/-- De Morgan circuit computing `1 + M` on an `m × m` one-hot matrix over `ZMod p`. -/
private def matAddOneCircuit (p m : ℕ) [NeZero p] :
    Circuit Boolean.signature (m * m * p) (m * m * p) :=
  let entryCirc (i j : Fin m) : Circuit Boolean.signature (m * m * p) p :=
    if i = j then
      let c1 : Circuit Boolean.signature (m * m * p) p :=
        (constOneHotCircuit p 1).mapInputs Fin.elim0
      let selfW : Circuit Boolean.signature (m * m * p) p :=
        Circuit.wiring Boolean.signature (fun r => finProdFinEquiv (finProdFinEquiv (i, j), r))
      (addOneHotCircuit p).comp (c1.append selfW)
    else
      Circuit.wiring Boolean.signature (fun r => finProdFinEquiv (finProdFinEquiv (i, j), r))
  appendCircuits (fun idx : Fin (m * m) =>
    entryCirc (finProdFinEquiv.symm idx).1 (finProdFinEquiv.symm idx).2)

private theorem eval_matAddOneCircuit {p m : ℕ} [NeZero p] (M : Matrix (Fin m) (Fin m) (ZMod p)) :
    (matAddOneCircuit p m).eval Boolean.interpretation (oneHotMat M) = oneHotMat (1 + M) := by
  funext idx
  obtain ⟨⟨q, r⟩, rfl⟩ := finProdFinEquiv.surjective idx
  obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective q
  simp only [matAddOneCircuit, eval_appendCircuits, Equiv.symm_apply_apply, oneHotMat,
    Matrix.add_apply, Matrix.one_apply]
  split_ifs with hij
  · simp only [Circuit.eval_comp, Circuit.eval_append, Circuit.eval_mapInputs,
      eval_constOneHotCircuit, Circuit.eval_wiring]
    have hself : (oneHotMat M ∘ fun r' => finProdFinEquiv (finProdFinEquiv (i, j), r')) =
        oneHotZMod (M i j) := by
      funext r'; simp [oneHotMat, Function.comp_apply]
    rw [hself, eval_addOneHotCircuit]
  · simp [Circuit.eval_wiring, oneHotMat, Function.comp_apply]

/-- Iterated squaring circuit outputting `(M ^ (2^t), ∏_{r < t} (1 + M ^ (2^r)))` on `m × m`
one-hot matrices over `ZMod p`. -/
private def iterSquareOneHotCircuit (p m : ℕ) [NeZero p] :
    (t : ℕ) → Circuit Boolean.signature (m * m * p) (m * m * p + m * m * p)
  | 0 =>
    let constOne : Circuit Boolean.signature (m * m * p) (m * m * p) :=
      appendCircuits (fun idx : Fin (m * m) =>
        let ij := finProdFinEquiv.symm idx
        (constOneHotCircuit p (if ij.1 = ij.2 then 1 else 0)).mapInputs Fin.elim0)
    (Circuit.id Boolean.signature (m * m * p)).append constOne
  | t + 1 =>
    let w := m * m * p
    let selM : Circuit Boolean.signature (w + w) w :=
      Circuit.wiring Boolean.signature (Fin.castAdd w)
    let selA : Circuit Boolean.signature (w + w) w :=
      Circuit.wiring Boolean.signature (Fin.natAdd w)
    let nextM : Circuit Boolean.signature (w + w) w :=
      (matMulOneHotCircuit p m).comp (selM.append selM)
    let nextA : Circuit Boolean.signature (w + w) w :=
      (matMulOneHotCircuit p m).comp (selA.append ((matAddOneCircuit p m).comp selM))
    (nextM.append nextA).comp (iterSquareOneHotCircuit p m t)

private theorem eval_iterSquareOneHotCircuit {p m : ℕ} [NeZero p]
    (M : Matrix (Fin m) (Fin m) (ZMod p)) :
    ∀ t : ℕ,
      (iterSquareOneHotCircuit p m t).eval Boolean.interpretation (oneHotMat M) =
        Fin.append (oneHotMat (M ^ (2 ^ t)))
          (oneHotMat (∑ j ∈ Finset.range (2 ^ t), M ^ j)) := by
  intro t
  induction t with
  | zero =>
    simp only [iterSquareOneHotCircuit, Circuit.eval_append, Circuit.eval_wiring, Function.comp_id,
      pow_zero, pow_one, Finset.range_one, Finset.sum_singleton]
    congr 1
    funext idx
    obtain ⟨⟨q, r⟩, rfl⟩ := finProdFinEquiv.surjective idx
    obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective q
    simp only [eval_appendCircuits, Equiv.symm_apply_apply, Circuit.eval_mapInputs,
      eval_constOneHotCircuit, oneHotMat, Matrix.one_apply]
  | succ t ih =>
    simp only [iterSquareOneHotCircuit, Circuit.eval_comp, ih, Circuit.eval_append,
      Circuit.eval_wiring]
    have hselM : (Fin.append (oneHotMat (M ^ 2 ^ t))
          (oneHotMat (∑ j ∈ Finset.range (2 ^ t), M ^ j)) ∘
        Fin.castAdd (m * m * p)) = oneHotMat (M ^ 2 ^ t) :=
      Fin.append_comp_castAdd _ _
    have hselA : (Fin.append (oneHotMat (M ^ 2 ^ t))
          (oneHotMat (∑ j ∈ Finset.range (2 ^ t), M ^ j)) ∘
        Fin.natAdd (m * m * p)) = oneHotMat (∑ j ∈ Finset.range (2 ^ t), M ^ j) :=
      Fin.append_comp_natAdd _ _
    rw [hselM, hselA, eval_matAddOneCircuit, eval_matMulOneHotCircuit, eval_matMulOneHotCircuit]
    congr 1
    · congr 1
      rw [← pow_add, show 2 ^ t + 2 ^ t = 2 ^ (t + 1) by ring]
    · congr 1
      rw [mul_add, mul_one, show 2 ^ (t + 1) = 2 ^ t + 2 ^ t by ring, Finset.sum_range_add]
      congr 1
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← pow_add, add_comm]

/-- Strictly upper-triangular `m × m` matrices vanish at power `m`: `(N ^ j) a b = 0`
whenever `b.1 < a.1 + j`. -/
private theorem strictUpper_pow_eq_zero {R : Type*} [Semiring R] {m : ℕ}
    (N : Matrix (Fin m) (Fin m) R) (hN : ∀ i j, j ≤ i → N i j = 0) :
    ∀ (j : ℕ) (a b : Fin m), b.1 < a.1 + j → (N ^ j) a b = 0 := by
  intro j
  induction j with
  | zero =>
    intro a b hab
    rw [pow_zero, Matrix.one_apply]
    split_ifs with h
    · subst h; omega
    · rfl
  | succ j ih =>
    intro a b hab
    rw [pow_succ, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hkb : k.1 < b.1
    · rw [ih a k (by omega), zero_mul]
    · rw [hN k b (not_lt.mp hkb), mul_zero]

/-- For a strictly upper-triangular `m × m` matrix `N`, the unique path-sum vector
`q = Pi.single 0 1 + q ᵥ* N` equals the first row of `∑_{j < 2^t} N^j` whenever `m ≤ 2^t`. -/
private theorem pathSum_eq_sum_pow {R : Type*} [CommRing R] {m : ℕ} [NeZero m]
    (N : Matrix (Fin m) (Fin m) R) (hN : ∀ i j, j ≤ i → N i j = 0)
    {q : Fin m → R} (hq : q = Pi.single 0 1 + q ᵥ* N)
    {t : ℕ} (ht : m ≤ 2 ^ t) (j : Fin m) :
    q j = (∑ r ∈ Finset.range (2 ^ t), N ^ r) 0 j := by
  let S : Matrix (Fin m) (Fin m) R := ∑ r ∈ Finset.range (2 ^ t), N ^ r
  have hS_eq : S = 1 + S * N := by
    have hmul : S * N = ∑ r ∈ Finset.range (2 ^ t), N ^ (r + 1) := by
      simp only [S, Finset.sum_mul]; refine Finset.sum_congr rfl fun r _ => (pow_succ N r).symm
    have hzero : N ^ (2 ^ t) = 0 := by
      ext a b
      exact strictUpper_pow_eq_zero N hN (2 ^ t) a b (by have := b.2; omega)
    have hsplit : ∑ r ∈ Finset.range (2 ^ t + 1), N ^ r =
        1 + ∑ r ∈ Finset.range (2 ^ t), N ^ (r + 1) := by
      rw [Finset.sum_range_succ', pow_zero, add_comm]
    have hsplit2 : ∑ r ∈ Finset.range (2 ^ t + 1), N ^ r = S + N ^ (2 ^ t) :=
      Finset.sum_range_succ _ _
    rw [hmul, ← hsplit, hsplit2, hzero, add_zero]
  let q' : Fin m → R := fun i => S 0 i
  have hq' : q' = Pi.single 0 1 + q' ᵥ* N := by
    funext i
    have hi := congrFun (congrFun hS_eq 0) i
    simp only [Matrix.add_apply, Matrix.one_apply, Matrix.mul_apply, Pi.add_apply,
      Pi.single_apply, Matrix.vecMul, dotProduct, q'] at hi ⊢
    convert hi using 2
    by_cases h : i = 0 <;> simp [h, eq_comm]
  have heq := ABP.pathSum_unique hN hq hq'
  exact congrFun heq j

/-- Uniform gate-level simulation: every `abpGate p` of size `≤ s` is computed by a De Morgan
circuit of size `≤ C_p * (s + 1)^3 * (Nat.clog 2 (s + 1) + 1)` and depth
`≤ D_p * (Nat.clog 2 (s + 1) + 1)^2`. -/
public theorem abpGate_to_deMorgan {p : ℕ} [Fact p.Prime] :
    ∃ (C D : ℕ), ∀ (n s : ℕ) (f : (Fin n → Bool) → Bool),
      f ∈ abpGate p n s →
      ∃ circ : Circuit Boolean.signature n 1,
        circ.Computes Boolean.interpretation (single f) ∧
        circ.size ≤ C * (s + 1) ^ 3 * (Nat.clog 2 (s + 1) + 1) ∧
        circ.depth ≤ D * (Nat.clog 2 (s + 1) + 1) ^ 2 := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  let C_add := (addOneHotCircuit p).size
  let C_mul := (mulOneHotCircuit p).size
  let D_add := (addOneHotCircuit p).depth
  let D_mul := (mulOneHotCircuit p).depth
  -- Constant bounds on `matAddOneCircuit` and `iterSquareOneHotCircuit`:
  have hsz_addOne : ∀ m : ℕ, (matAddOneCircuit p m).size ≤ m * m * (C_add + p) := by
    intro m
    simp only [matAddOneCircuit, size_appendCircuits]
    calc ∑ idx : Fin (m * m), _
        ≤ ∑ _ : Fin (m * m), (C_add + p) := Finset.sum_le_sum fun idx _ => by
            split_ifs <;> simp [C_add, size_constOneHotCircuit]; omega
      _ = m * m * (C_add + p) := by simp
  have hdp_addOne : ∀ m : ℕ, (matAddOneCircuit p m).depth ≤ D_add + 1 := by
    intro m
    refine depth_appendCircuits_le _ fun idx => ?_
    dsimp only
    split_ifs
    · refine (Circuit.depth_comp_le _ _).trans ?_
      refine (add_le_add le_rfl (show _ ≤ 1 from ?_)).trans (by omega)
      refine (Circuit.depth_append_le _ _).trans (max_le ?_ (by simp))
      rw [depth_mapInputs]; exact depth_constOneHotCircuit 1
    · simp
  let C_step := 2 * (C_mul + (C_add + p) * 3) + (C_add + p) + 11 * p + 10
  let D_step := D_add + D_mul + 5
  refine ⟨C_step + p + 10, D_step + D_add + Nat.clog 2 p + 10, ?_⟩
  intro n s f ⟨P, S, hPs, hf⟩
  have hsub := P.isSubstABP_subdivide
  obtain ⟨N, q, hN_subst, hN_ut, hq, hq_last⟩ := hsub
  let m := P.innerVerts + P.edges.length + 2
  have hm_le : m ≤ s + 1 := by
    have : P.size = P.innerVerts + 2 + P.edges.length := rfl
    omega
  have hm_pos : 0 < m := by omega
  have : NeZero m := ⟨by omega⟩
  let t := Nat.clog 2 m
  have ht_pow : m ≤ 2 ^ t := Nat.le_pow_clog (by omega) m
  -- Build initial one-hot matrix circuit from `N`:
  -- Each entry `N i j` is `X r` or `C c` (from `hN_subst i j`).
  classical
  let initEntry (i j : Fin m) : Circuit Boolean.signature n p :=
    let sEntry := (hN_subst i j).choose
    match sEntry with
    | .inr c => (constOneHotCircuit p c).mapInputs Fin.elim0
    | .inl idx =>
      let bitF (r : Fin p) : Formula Boolean.signature n :=
        ((Formula.input idx).and (Formula.const (oneHotZMod (1 : ZMod p) r))).or
          ((Formula.input idx).not.and (Formula.const (oneHotZMod (0 : ZMod p) r)))
      (appendCircuits (fun r : Fin p => (bitF r).toCircuit)).comapOutputs
        (fun r => finProdFinEquiv (r, 0))
  let initCirc : Circuit Boolean.signature n (m * m * p) :=
    appendCircuits (fun idx : Fin (m * m) =>
      initEntry (finProdFinEquiv.symm idx).1 (finProdFinEquiv.symm idx).2)
  have heval_init : ∀ x : Fin n → Bool,
      initCirc.eval Boolean.interpretation x =
        oneHotMat (N.map (MvPolynomial.aeval (fun i => if x i then (1 : ZMod p) else 0))) := by
    intro x
    funext idx
    obtain ⟨⟨q', r⟩, rfl⟩ := finProdFinEquiv.surjective idx
    obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective q'
    simp only [initCirc, eval_appendCircuits, Equiv.symm_apply_apply, oneHotMat, Matrix.map_apply]
    have hspec : Sum.elim MvPolynomial.X MvPolynomial.C (hN_subst i j).choose = N i j :=
      (hN_subst i j).choose_spec
    simp only [initEntry]
    cases hs_ch : (hN_subst i j).choose with
    | inr c =>
      rw [hs_ch] at hspec; simp only [Sum.elim_inr] at hspec
      rw [← hspec, MvPolynomial.aeval_C]
      simp [Circuit.eval_mapInputs, eval_constOneHotCircuit]
    | inl v =>
      rw [hs_ch] at hspec; simp only [Sum.elim_inl] at hspec
      rw [← hspec, MvPolynomial.aeval_X]
      simp only [Circuit.eval_comapOutputs, Function.comp_apply, eval_appendCircuits,
        Formula.eval_toCircuit, Formula.eval_or, Formula.eval_and, Formula.eval_not,
        Formula.eval_input, Formula.eval_const]
      cases x v <;> simp
  -- Acceptance circuit reading `entry (0, last)` and checking `∈ S`:
  let acceptCirc : Circuit Boolean.signature (m * m * p + m * m * p) 1 :=
    let rs : List (Fin p) := (List.finRange p).filter (fun r => decide ((r.1 : ZMod p) ∈ S))
    let fOut : Formula Boolean.signature (m * m * p + m * m * p) :=
      Formula.orList <| rs.map fun r =>
        Formula.input (Fin.natAdd (m * m * p)
          (finProdFinEquiv (finProdFinEquiv (0, Fin.last (m - 1)), r)))
    fOut.toCircuit
  let fullCirc : Circuit Boolean.signature n 1 :=
    acceptCirc.comp ((iterSquareOneHotCircuit p m t).comp initCirc)
  refine ⟨fullCirc, ?_, ?_, ?_⟩
  · -- Correctness:
    intro x
    funext o; obtain rfl : o = 0 := Subsingleton.elim o 0
    simp only [fullCirc, Circuit.eval_comp, heval_init, eval_iterSquareOneHotCircuit, single_apply]
    rw [hf x]
    let Nx := N.map (MvPolynomial.aeval (fun i => if x i then (1 : ZMod p) else 0))
    have hNx_ut : ∀ i j, j ≤ i → Nx i j = 0 := fun i j hji => by
      simp [Nx, hN_ut i j hji]
    let qx : Fin m → ZMod p := fun i => MvPolynomial.aeval (fun i => if x i then 1 else 0) (q i)
    have hqx : qx = Pi.single 0 1 + qx ᵥ* Nx := by
      funext j
      have hj := congrArg (MvPolynomial.aeval
        (fun i => if x i then (1 : ZMod p) else 0)) (congrFun hq j)
      simpa [qx, Nx, Pi.single_apply, Matrix.vecMul, dotProduct, map_sum, map_mul] using hj
    have hval : P.eval (fun i => if x i then 1 else 0) =
        (∑ r ∈ Finset.range (2 ^ t), Nx ^ r) 0 (Fin.last (m - 1)) := by
      have h1 : P.eval (fun i => if x i then 1 else 0) = qx (Fin.last (m - 1)) := by
        rw [ABP.eval_eq_aeval_poly]
        simp only [qx, ← hq_last]; rfl
      rw [h1]
      exact pathSum_eq_sum_pow Nx hNx_ut hqx ht_pow (Fin.last (m - 1))
    have hfn : (fun i : Fin n => @ite _ (x i = true) (Classical.propDecidable _) (1 : ZMod p) 0) =
        (fun i : Fin n => if x i = true then (1 : ZMod p) else 0) :=
      funext fun i => by split_ifs <;> rfl
    rw [hfn, hval, Bool.eq_iff_iff]
    simp only [acceptCirc, Formula.eval_toCircuit, Formula.eval_orList, List.any_map,
      List.any_eq_true, Function.comp_apply, List.mem_filter, List.mem_finRange, true_and,
      Formula.eval_input, Fin.append_right, oneHotMat, Equiv.symm_apply_apply, oneHotZMod_eq_true]
    rw [@decide_eq_true_iff _ (Classical.propDecidable _)]
    constructor
    · rintro ⟨r, hrS, heq⟩
      rw [heq]; exact of_decide_eq_true hrS
    · intro hmem
      let v := (∑ r ∈ Finset.range (2 ^ t), Nx ^ r) 0 (Fin.last (m - 1))
      exact ⟨⟨v.val, v.val_lt⟩, decide_eq_true (by rwa [ZMod.natCast_zmod_val]),
        (ZMod.natCast_zmod_val v).symm⟩
  · -- Size bound:
    have hsz_iter : ∀ t' : ℕ,
        (iterSquareOneHotCircuit p m t').size ≤
          t' * (2 * (m * m * (m * C_mul + (C_add + p) * (2 * m + 1))) + m * m * (C_add + p)) +
          m * m * p := by
      intro t'
      induction t' with
      | zero =>
        simp only [iterSquareOneHotCircuit, Circuit.size_append, Circuit.size_wiring, zero_add,
          size_appendCircuits, Circuit.mapInputs_size, size_constOneHotCircuit, zero_mul]
        simp
      | succ t' ih' =>
        simp only [iterSquareOneHotCircuit, Circuit.size_comp, Circuit.size_append,
          Circuit.size_wiring, zero_add, add_zero]
        have hm1 := size_matMulOneHotCircuit_le p m
        have hm2 := hsz_addOne m
        nlinarith
    have hsz_init : initCirc.size ≤ m * m * (8 * p) := by
      simp only [initCirc, size_appendCircuits]
      calc ∑ idx : Fin (m * m), (initEntry _ _).size
          ≤ ∑ _ : Fin (m * m), (8 * p) := Finset.sum_le_sum fun idx _ => by
              simp only [initEntry]
              cases (hN_subst _ _).choose
              · simp only [Circuit.comapOutputs_size, size_appendCircuits, Formula.size_toCircuit,
                  Formula.size_or, Formula.size_and, Formula.size_not, Formula.size_input,
                  Formula.size_const]
                simp [mul_comm]; omega
              · simp [size_constOneHotCircuit]; omega
        _ = m * m * (8 * p) := by simp
    have hsz_acc : acceptCirc.size ≤ 2 * p + 1 := by
      simp only [acceptCirc, Formula.size_toCircuit]
      have hor : ∀ l : List (Formula Boolean.signature (m * m * p + m * m * p)),
          (Formula.orList l).size ≤ (l.map Formula.size).sum + l.length + 1 := by
        intro l; cases l with
        | nil => simp [Formula.orList, Formula.balanced_nil]
        | cons a as =>
          have h := Formula.size_balanced_add_one (op := Boolean.Op.or) (hop := rfl)
            (Formula.const false) (List.cons_ne_nil a as)
          simp only [Formula.orList]; omega
      have hlen : ((List.finRange p).filter fun r => decide ((r.1 : ZMod p) ∈ S)).length ≤ p :=
        (List.length_filter_le _ _).trans (by simp)
      have h1 := hor (((List.finRange p).filter fun r => decide ((r.1 : ZMod p) ∈ S)).map fun r =>
        Formula.input (Fin.natAdd (m * m * p)
          (finProdFinEquiv (finProdFinEquiv (0, Fin.last (m - 1)), r))))
      simp only [List.map_map, Function.comp_def, Formula.size_input, List.map_const',
        List.sum_replicate, smul_zero, List.length_map, zero_add] at h1
      omega
    have ht_le : t ≤ Nat.clog 2 (s + 1) := Nat.clog_mono_right 2 hm_le
    have h1 := hsz_iter t
    simp only [fullCirc, Circuit.size_comp]
    have hm1 : 1 ≤ m := hm_pos
    have h2 : m ^ 2 ≤ (s + 1) ^ 2 := Nat.pow_le_pow_left hm_le 2
    have h3 : m ^ 3 ≤ (s + 1) ^ 3 := Nat.pow_le_pow_left hm_le 3
    have hp1 : 1 ≤ p := NeZero.pos p
    have hmm : m * m ≤ m ^ 3 := by
      calc m * m = m ^ 2 * 1 := by ring
        _ ≤ m ^ 2 * m := Nat.mul_le_mul_left _ hm1
        _ = m ^ 3 := by ring
    have hstep_le :
        2 * (m * m * (m * C_mul + (C_add + p) * (2 * m + 1))) + m * m * (C_add + p) ≤
          (2 * (C_mul + (C_add + p) * 3) + (C_add + p)) * m ^ 3 := by
      have h2m : 2 * m + 1 ≤ 3 * m := by omega
      have hlin : m * C_mul + (C_add + p) * (2 * m + 1) ≤ (C_mul + (C_add + p) * 3) * m := by
        calc m * C_mul + (C_add + p) * (2 * m + 1)
            ≤ m * C_mul + (C_add + p) * (3 * m) :=
              Nat.add_le_add_left (Nat.mul_le_mul_left _ h2m) _
          _ = (C_mul + (C_add + p) * 3) * m := by ring
      calc 2 * (m * m * (m * C_mul + (C_add + p) * (2 * m + 1))) + m * m * (C_add + p)
          ≤ 2 * (m * m * ((C_mul + (C_add + p) * 3) * m)) + m ^ 3 * (C_add + p) :=
            add_le_add (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hlin))
              (Nat.mul_le_mul_right _ hmm)
        _ = (2 * (C_mul + (C_add + p) * 3) + (C_add + p)) * m ^ 3 := by ring
    have hrest_le : m * m * (8 * p) + m * m * p + (2 * p + 1) ≤ (11 * p + 1) * m ^ 3 := by
      have h1m3 : 1 ≤ m ^ 3 := by nlinarith
      calc m * m * (8 * p) + m * m * p + (2 * p + 1)
          = m * m * (9 * p) + (2 * p + 1) * 1 := by ring
        _ ≤ m ^ 3 * (9 * p) + (2 * p + 1) * m ^ 3 :=
            add_le_add (Nat.mul_le_mul_right _ hmm) (Nat.mul_le_mul_left _ h1m3)
        _ = (11 * p + 1) * m ^ 3 := by ring
    have hcoeff : 2 * (C_mul + (C_add + p) * 3) + (C_add + p) + (11 * p + 1) ≤
        (C_step + p + 10) := by
      dsimp only [C_step]; omega
    calc initCirc.size + (iterSquareOneHotCircuit p m t).size + acceptCirc.size
        ≤ m * m * (8 * p) +
            (t * (2 * (m * m * (m * C_mul + (C_add + p) * (2 * m + 1))) + m * m * (C_add + p)) +
              m * m * p) +
            (2 * p + 1) := add_le_add (add_le_add hsz_init h1) hsz_acc
      _ = t * (2 * (m * m * (m * C_mul + (C_add + p) * (2 * m + 1))) + m * m * (C_add + p)) +
            (m * m * (8 * p) + m * m * p + (2 * p + 1)) := by ring
      _ ≤ Nat.clog 2 (s + 1) * ((2 * (C_mul + (C_add + p) * 3) + (C_add + p)) * m ^ 3) +
            (11 * p + 1) * m ^ 3 :=
            add_le_add (Nat.mul_le_mul ht_le hstep_le) hrest_le
      _ ≤ (Nat.clog 2 (s + 1) + 1) * ((2 * (C_mul + (C_add + p) * 3) + (C_add + p)) * m ^ 3) +
            (Nat.clog 2 (s + 1) + 1) * ((11 * p + 1) * m ^ 3) := by
            have h1c : 1 ≤ Nat.clog 2 (s + 1) + 1 := Nat.succ_pos _
            exact add_le_add
              (Nat.mul_le_mul_right _ (Nat.le_succ _))
              (le_trans (by rw [one_mul]) (Nat.mul_le_mul_right _ h1c))
      _ = (2 * (C_mul + (C_add + p) * 3) + (C_add + p) + (11 * p + 1)) * m ^ 3 *
            (Nat.clog 2 (s + 1) + 1) := by ring
      _ ≤ (C_step + p + 10) * (s + 1) ^ 3 * (Nat.clog 2 (s + 1) + 1) :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul hcoeff h3)
  · -- Depth bound:
    have hdp_iter : ∀ t' : ℕ,
        (iterSquareOneHotCircuit p m t').depth ≤
          t' * (D_add * Nat.clog 2 m + 1 + D_mul + D_add + 1) + 1 := by
      intro t'
      induction t' with
      | zero =>
        simp only [iterSquareOneHotCircuit, zero_mul, zero_add]
        refine (Circuit.depth_append_le _ _).trans (max_le (by simp) ?_)
        refine depth_appendCircuits_le _ fun idx => ?_
        rw [depth_mapInputs]; exact depth_constOneHotCircuit _
      | succ t' ih' =>
        simp only [iterSquareOneHotCircuit]
        refine (Circuit.depth_comp_le _ _).trans ?_
        have hmul : (D_add * Nat.clog 2 m + 1 + D_mul + D_add + 1) +
            (t' * (D_add * Nat.clog 2 m + 1 + D_mul + D_add + 1) + 1) =
            (t' + 1) * (D_add * Nat.clog 2 m + 1 + D_mul + D_add + 1) + 1 := by ring
        refine (add_le_add
          (show _ ≤ D_add * Nat.clog 2 m + 1 + D_mul + D_add + 1 from ?_) ih').trans
          (le_of_eq hmul)
        refine (Circuit.depth_append_le _ _).trans (max_le ?_ ?_)
        · refine (Circuit.depth_comp_le _ _).trans ?_
          have h1 := depth_matMulOneHotCircuit_le p m
          refine (add_le_add h1 (show _ ≤ 0 from ?_)).trans (by dsimp only [D_add, D_mul]; omega)
          exact (Circuit.depth_append_le _ _).trans (by simp)
        · refine (Circuit.depth_comp_le _ _).trans ?_
          have h1 := depth_matMulOneHotCircuit_le p m
          refine (add_le_add h1 (show _ ≤ D_add + 1 from ?_)).trans
            (by dsimp only [D_add, D_mul]; omega)
          refine (Circuit.depth_append_le _ _).trans (max_le (by simp) ?_)
          exact (Circuit.depth_comp_le _ _).trans (by simp [hdp_addOne m])
    have hdp_init : initCirc.depth ≤ 5 := by
      refine depth_appendCircuits_le _ fun idx => ?_
      simp only [initEntry]
      cases (hN_subst _ _).choose
      · refine (depth_comapOutputs_le _ _).trans ?_
        refine depth_appendCircuits_le _ fun r => (Formula.depth_toCircuit_le _).trans ?_
        simp [Formula.depth_or, Formula.depth_and, Formula.depth_not, Formula.depth_input,
          Formula.depth_const]
      · rw [depth_mapInputs]; exact (depth_constOneHotCircuit _).trans (by omega)
    have hdp_acc : acceptCirc.depth ≤ Nat.clog 2 p + 1 := by
      simp only [acceptCirc]
      refine (Formula.depth_toCircuit_le _).trans ?_
      have hbal : ∀ (l : List (Formula Boolean.signature (m * m * p + m * m * p))),
          (∀ F ∈ l, F.depth ≤ 0) →
          (Formula.orList l).depth ≤ Nat.clog 2 l.length + 1 := by
        intro l hl
        have h1 := Formula.depthWith_balanced_le (op := Boolean.Op.or) (hop := rfl)
          (cost := 1) (d := 1) (Formula.const false) (l := l)
          (fun F hF => by have := hl F hF; rw [Formula.depthWith_one]; omega)
          (fun _ => by rw [Formula.depthWith_one]; simp [Formula.depth_const])
        rw [Formula.orList, ← Formula.depthWith_one]
        simpa only [Pi.one_apply, one_mul, add_comm] using h1
      have hlen : ((List.finRange p).filter fun r => decide ((r.1 : ZMod p) ∈ S)).length ≤ p :=
        (List.length_filter_le _ _).trans (by simp)
      have h2 := hbal
        (((List.finRange p).filter fun r => decide ((r.1 : ZMod p) ∈ S)).map fun r =>
          Formula.input (Fin.natAdd (m * m * p)
            (finProdFinEquiv (finProdFinEquiv (0, Fin.last (m - 1)), r))))
        (fun F hF => by
          obtain ⟨r, _, rfl⟩ := List.mem_map.mp hF
          simp)
      simp only [List.length_map] at h2
      exact h2.trans (Nat.add_le_add_right (Nat.clog_mono_right 2 hlen) 1)
    have ht_le : t ≤ Nat.clog 2 (s + 1) := Nat.clog_mono_right 2 hm_le
    have h1 := hdp_iter t
    have h2 : fullCirc.depth ≤
        acceptCirc.depth + (iterSquareOneHotCircuit p m t).depth + initCirc.depth := by
      have ha := Circuit.depth_comp_le acceptCirc ((iterSquareOneHotCircuit p m t).comp initCirc)
      have hb := Circuit.depth_comp_le (iterSquareOneHotCircuit p m t) initCirc
      dsimp only [fullCirc]; omega
    have h3 : (Nat.clog 2 (s + 1) + 1) * (D_add * Nat.clog 2 (s + 1) + 1 + D_mul + D_add + 1) ≤
        (D_add + D_mul + 2) * (Nat.clog 2 (s + 1) + 1) ^ 2 := by
      have hlin : D_add * Nat.clog 2 (s + 1) + 1 + D_mul + D_add + 1 ≤
          (D_add + D_mul + 2) * (Nat.clog 2 (s + 1) + 1) := by nlinarith
      calc (Nat.clog 2 (s + 1) + 1) * (D_add * Nat.clog 2 (s + 1) + 1 + D_mul + D_add + 1)
          ≤ (Nat.clog 2 (s + 1) + 1) * ((D_add + D_mul + 2) * (Nat.clog 2 (s + 1) + 1)) :=
            Nat.mul_le_mul_left _ hlin
        _ = (D_add + D_mul + 2) * (Nat.clog 2 (s + 1) + 1) ^ 2 := by ring
    have h4 : t * (D_add * Nat.clog 2 m + 1 + D_mul + D_add + 1) ≤
        (Nat.clog 2 (s + 1) + 1) * (D_add * Nat.clog 2 (s + 1) + 1 + D_mul + D_add + 1) :=
      Nat.mul_le_mul (by omega) (by gcongr)
    have hsq : 1 ≤ (Nat.clog 2 (s + 1) + 1) ^ 2 := by nlinarith
    have hconst : (Nat.clog 2 p + 1) + 1 + 5 ≤
        (Nat.clog 2 p + 7) * (Nat.clog 2 (s + 1) + 1) ^ 2 := by
      calc (Nat.clog 2 p + 1) + 1 + 5
          = (Nat.clog 2 p + 7) * 1 := by ring
        _ ≤ (Nat.clog 2 p + 7) * (Nat.clog 2 (s + 1) + 1) ^ 2 := Nat.mul_le_mul_left _ hsq
    have hDcoeff : (D_add + D_mul + 2) + (Nat.clog 2 p + 7) ≤
        D_step + D_add + Nat.clog 2 p + 10 := by
      dsimp only [D_step]; omega
    calc fullCirc.depth
        ≤ acceptCirc.depth + (iterSquareOneHotCircuit p m t).depth + initCirc.depth := h2
      _ ≤ (Nat.clog 2 p + 1) +
            (t * (D_add * Nat.clog 2 m + 1 + D_mul + D_add + 1) + 1) + 5 := by omega
      _ = t * (D_add * Nat.clog 2 m + 1 + D_mul + D_add + 1) + ((Nat.clog 2 p + 1) + 1 + 5) := by
          ring
      _ ≤ (D_add + D_mul + 2) * (Nat.clog 2 (s + 1) + 1) ^ 2 +
            (Nat.clog 2 p + 7) * (Nat.clog 2 (s + 1) + 1) ^ 2 :=
          add_le_add (h4.trans h3) hconst
      _ = ((D_add + D_mul + 2) + (Nat.clog 2 p + 7)) * (Nat.clog 2 (s + 1) + 1) ^ 2 := by ring
      _ ≤ (D_step + D_add + Nat.clog 2 p + 10) * (Nat.clog 2 (s + 1) + 1) ^ 2 :=
          Nat.mul_le_mul_right _ hDcoeff

/-- Uniform gate-level simulation of a chain of `abpGate` layers into De Morgan circuits of
polynomial size and `O((log s)²)` depth. -/
public theorem gateCompList_abpGate_to_deMorgan (ps : List ℕ) (hps : ∀ p ∈ ps, Nat.Prime p) :
    ∃ (C D E : ℕ), 1 ≤ E ∧ ∀ (n s : ℕ) (f : (Fin n → Bool) → Bool),
      f ∈ gateCompList (ps.map abpGate) n s →
      ∃ circ : Circuit Boolean.signature n 1,
        circ.Computes Boolean.interpretation (single f) ∧
        circ.size ≤ C * (s + 1) ^ E ∧
        circ.depth ≤ D * (Nat.clog 2 (s + 1) + 1) ^ 2 := by
  induction ps with
  | nil =>
    refine ⟨1, 1, 1, le_rfl, fun n s f ⟨_, i, hf⟩ => ?_⟩
    refine ⟨Circuit.wiring Boolean.signature (fun _ => i), fun x => ?_, by simp, by simp⟩
    funext o; fin_cases o; simp [single_apply, hf]
  | cons p qs ih =>
    have : Fact p.Prime := ⟨hps p List.mem_cons_self⟩
    obtain ⟨C₁, D₁, hsim₁⟩ := abpGate_to_deMorgan (p := p)
    cases qs with
    | nil =>
      refine ⟨2 * C₁, D₁, 4, by omega, fun n s f hf => ?_⟩
      obtain ⟨circ, hcomp, hsz, hdp⟩ := hsim₁ n s f hf
      refine ⟨circ, hcomp, ?_, hdp⟩
      have hcl : Nat.clog 2 (s + 1) + 1 ≤ 2 * (s + 1) := by
        have := (Nat.clog_le_iff_le_pow one_lt_two).mpr (Nat.lt_two_pow_self (n := s + 1)).le
        omega
      calc circ.size ≤ C₁ * (s + 1) ^ 3 * (Nat.clog 2 (s + 1) + 1) := hsz
        _ ≤ C₁ * (s + 1) ^ 3 * (2 * (s + 1)) := Nat.mul_le_mul_left _ hcl
        _ = 2 * C₁ * (s + 1) ^ 4 := by ring
    | cons q qs' =>
      obtain ⟨C₂, D₂, E₂, hE₂, hsim₂⟩ := ih (fun r hr => hps r (List.mem_cons_of_mem _ hr))
      let E := max 4 E₂
      have hE4 : 4 ≤ E := le_max_left _ _
      have hEE₂ : E₂ ≤ E := le_max_right _ _
      refine ⟨2 * C₁ + C₂, D₁ + D₂, E, by omega,
        fun n s f ⟨k, g, hs_fn, sg, sh, hg, hhs, hsz, hf⟩ => ?_⟩
      obtain ⟨Cg, hCg_comp, hCg_sz, hCg_dp⟩ := hsim₁ k sg g hg
      have hsub : ∀ i : Fin k, ∃ Ci : Circuit Boolean.signature n 1,
          Ci.Computes Boolean.interpretation (single (hs_fn i)) ∧
          Ci.size ≤ C₂ * (sh i + 1) ^ E₂ ∧
          Ci.depth ≤ D₂ * (Nat.clog 2 (sh i + 1) + 1) ^ 2 :=
        fun i => hsim₂ n (sh i) (hs_fn i) (hhs i)
      choose Ci hCi_comp hCi_sz hCi_dp using hsub
      let Cin : Circuit Boolean.signature n k :=
        (appendCircuits Ci).comapOutputs (fun j => finProdFinEquiv (j, 0))
      let Cfull : Circuit Boolean.signature n 1 := Cg.comp Cin
      refine ⟨Cfull, ?_, ?_, ?_⟩
      · intro x; funext o; obtain rfl : o = 0 := Subsingleton.elim o 0
        simp only [Cfull, Circuit.eval_comp, single_apply, hf]
        have h1 := congrFun (hCg_comp (fun i => hs_fn i x)) 0
        simp only [single_apply] at h1
        rw [← h1]; congr 1; funext i
        simp only [Cin, Circuit.eval_comapOutputs, Function.comp_apply, eval_appendCircuits]
        have h2 := congrFun (hCi_comp i x) 0
        simpa [single_apply] using h2
      · have hcl : Nat.clog 2 (sg + 1) + 1 ≤ 2 * (sg + 1) := by
          have := (Nat.clog_le_iff_le_pow one_lt_two).mpr (Nat.lt_two_pow_self (n := sg + 1)).le
          omega
        have hCg_sz' : Cg.size ≤ 2 * C₁ * (s + 1) ^ E := by
          calc Cg.size ≤ C₁ * (sg + 1) ^ 3 * (Nat.clog 2 (sg + 1) + 1) := hCg_sz
            _ ≤ C₁ * (sg + 1) ^ 3 * (2 * (sg + 1)) := Nat.mul_le_mul_left _ hcl
            _ = 2 * C₁ * (sg + 1) ^ 4 := by ring
            _ ≤ 2 * C₁ * (s + 1) ^ 4 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 4)
            _ ≤ 2 * C₁ * (s + 1) ^ E := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) hE4)
        have hsum_pow : (∑ i : Fin k, (sh i + 1) ^ E₂) ≤ (∑ i : Fin k, (sh i + 1)) ^ E₂ := by
          have hgen : ∀ (t : Finset (Fin k)) (a : Fin k → ℕ),
              (∑ i ∈ t, a i ^ E₂) ≤ (∑ i ∈ t, a i) ^ E₂ := by
            intro t a
            classical
            induction t using Finset.induction_on with
            | empty => simp [zero_pow (by omega : E₂ ≠ 0)]
            | @insert x t hx ih' =>
              rw [Finset.sum_insert hx, Finset.sum_insert hx]
              have hadd_pow : ∀ u v : ℕ, u ^ E₂ + v ^ E₂ ≤ (u + v) ^ E₂ := fun u v => by
                have h2 : ∀ d ≥ 1, u ^ d + v ^ d ≤ (u + v) ^ d := by
                  intro d hd
                  induction d with
                  | zero => omega
                  | succ d ihd =>
                    cases d with
                    | zero => simp
                    | succ d' =>
                      have ihd' := ihd (by omega)
                      calc u ^ (d' + 2) + v ^ (d' + 2)
                          = u * u ^ (d' + 1) + v * v ^ (d' + 1) := by ring
                        _ ≤ (u + v) * u ^ (d' + 1) + (u + v) * v ^ (d' + 1) := by
                            gcongr <;> omega
                        _ = (u + v) * (u ^ (d' + 1) + v ^ (d' + 1)) := by ring
                        _ ≤ (u + v) * (u + v) ^ (d' + 1) := Nat.mul_le_mul_left _ ihd'
                        _ = (u + v) ^ (d' + 2) := by ring
                exact h2 E₂ hE₂
              exact (add_le_add (le_refl (a x ^ E₂)) ih').trans (hadd_pow _ _)
          exact hgen Finset.univ (fun i => sh i + 1)
        have hCin_sz : Cin.size ≤ C₂ * (s + 1) ^ E := by
          simp only [Cin, Circuit.comapOutputs_size, size_appendCircuits]
          calc ∑ i : Fin k, (Ci i).size
              ≤ ∑ i : Fin k, C₂ * (sh i + 1) ^ E₂ := Finset.sum_le_sum fun i _ => hCi_sz i
            _ = C₂ * ∑ i : Fin k, (sh i + 1) ^ E₂ := (Finset.mul_sum _ _ _).symm
            _ ≤ C₂ * (∑ i : Fin k, (sh i + 1)) ^ E₂ := Nat.mul_le_mul_left _ hsum_pow
            _ ≤ C₂ * (s + 1) ^ E₂ := by
                have hsum_le : ∑ i : Fin k, (sh i + 1) ≤ s + 1 := by
                  rw [Finset.sum_add_distrib]; simp; omega
                exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hsum_le E₂)
            _ ≤ C₂ * (s + 1) ^ E := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) hEE₂)
        simp only [Cfull, Circuit.size_comp]
        calc Cin.size + Cg.size
            ≤ C₂ * (s + 1) ^ E + 2 * C₁ * (s + 1) ^ E := add_le_add hCin_sz hCg_sz'
          _ = (2 * C₁ + C₂) * (s + 1) ^ E := by ring
      · refine (Circuit.depth_comp_le _ _).trans ?_
        have hd1 : Cg.depth ≤ D₁ * (Nat.clog 2 (s + 1) + 1) ^ 2 :=
          hCg_dp.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left
            (Nat.add_le_add_right (Nat.clog_mono_right 2 (by omega)) 1) 2))
        have hd2 : Cin.depth ≤ D₂ * (Nat.clog 2 (s + 1) + 1) ^ 2 := by
          refine (depth_comapOutputs_le _ _).trans ?_
          refine depth_appendCircuits_le Ci fun i => ?_
          have hsh : sh i ≤ s := by
            have := Finset.single_le_sum (f := sh) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
            omega
          exact (hCi_dp i).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left
            (Nat.add_le_add_right (Nat.clog_mono_right 2 (by omega)) 1) 2))
        calc Cg.depth + Cin.depth
            ≤ D₁ * (Nat.clog 2 (s + 1) + 1) ^ 2 + D₂ * (Nat.clog 2 (s + 1) + 1) ^ 2 :=
              add_le_add hd1 hd2
          _ = (D₁ + D₂) * (Nat.clog 2 (s + 1) + 1) ^ 2 := by ring

/-- For every prime `p`, `NuDet p ⊆ NC 2`. -/
public theorem NuDet_subset_NC_two (p : ℕ) [Fact p.Prime] : NuDet p ⊆ NC 2 := by
  rintro L ⟨s, hs, hL⟩
  obtain ⟨C, D, hsim⟩ := abpGate_to_deMorgan (p := p)
  obtain ⟨e, he⟩ := (hs.add (PolynomiallyBounded.const 1)).exists_clog_le_mul_log
  refine ⟨D * (e + 1) ^ 2, fun n => 2 * C * (s n + 1) ^ 4, by fun_prop, fun n => ?_⟩
  obtain ⟨circ, hcomp, hsz, hdp⟩ := hsim n (s n) (L.slice n) (hL n)
  refine ⟨circ, hcomp, ?_, ?_⟩
  · have hclog : Nat.clog 2 (s n + 1) + 1 ≤ (e + 1) * (Nat.log 2 n + 1) := by
      have := he n; nlinarith
    calc circ.depth ≤ D * (Nat.clog 2 (s n + 1) + 1) ^ 2 := hdp
      _ ≤ D * ((e + 1) * (Nat.log 2 n + 1)) ^ 2 :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hclog 2)
      _ = D * (e + 1) ^ 2 * (Nat.log 2 n + 1) ^ 2 := by ring
  · have hcl : Nat.clog 2 (s n + 1) + 1 ≤ 2 * (s n + 1) := by
      have := (Nat.clog_le_iff_le_pow one_lt_two).mpr (Nat.lt_two_pow_self (n := s n + 1)).le
      omega
    calc circ.size ≤ C * (s n + 1) ^ 3 * (Nat.clog 2 (s n + 1) + 1) := hsz
      _ ≤ C * (s n + 1) ^ 3 * (2 * (s n + 1)) := Nat.mul_le_mul_left _ hcl
      _ = 2 * C * (s n + 1) ^ 4 := by ring

/-- Closure of `NC 2` under constant-height circuit composition. -/
public theorem NC2_comp_closed {c₁ c₂ : ℕ} :
    langClass (gateComp (nc2Gate c₁) (nc2Gate c₂)) ⊆ NC 2 := by
  rintro L ⟨s, hs, hL⟩
  obtain ⟨e, he⟩ := hs.exists_clog_le_mul_log
  refine ⟨c₁ * (e + 1) ^ 2 + c₂, s, hs, fun n => ?_⟩
  obtain ⟨k, g, hs_fn, sg, sh, ⟨Cg, hCg_sz, hCg_dp, hCg_comp⟩, hhs, hsz, hf⟩ := hL n
  choose Ci hCi_sz hCi_dp hCi_comp using hhs
  let Cin : Circuit Boolean.signature n k :=
    (appendCircuits Ci).comapOutputs (fun j => finProdFinEquiv (j, 0))
  let Cfull : Circuit Boolean.signature n 1 := Cg.comp Cin
  refine ⟨Cfull, ?_, ?_, ?_⟩
  · intro x; funext o; obtain rfl : o = 0 := Subsingleton.elim o 0
    simp only [Cfull, Circuit.eval_comp, single_apply, hf]
    have h1 := congrFun (hCg_comp (fun i => hs_fn i x)) 0
    simp only [single_apply] at h1
    rw [← h1]; congr 1; funext i
    simp only [Cin, Circuit.eval_comapOutputs, Function.comp_apply, eval_appendCircuits]
    have h2 := congrFun (hCi_comp i x) 0
    simpa [single_apply] using h2
  · refine (Circuit.depth_comp_le _ _).trans ?_
    have hCin_dp : Cin.depth ≤ c₂ * (Nat.log 2 n + 1) ^ 2 :=
      (depth_comapOutputs_le _ _).trans (depth_appendCircuits_le Ci hCi_dp)
    have hk_le : k ≤ s n := by omega
    have hlog_k : Nat.log 2 k + 1 ≤ (e + 1) * (Nat.log 2 n + 1) := by
      have h1 : Nat.log 2 k ≤ Nat.clog 2 k := Nat.log_le_clog 2 k
      have h2 : Nat.clog 2 k ≤ Nat.clog 2 (s n) := Nat.clog_mono_right 2 hk_le
      have h3 := he n
      nlinarith
    have hCg_dp' : Cg.depth ≤ c₁ * (e + 1) ^ 2 * (Nat.log 2 n + 1) ^ 2 :=
      calc Cg.depth ≤ c₁ * (Nat.log 2 k + 1) ^ 2 := hCg_dp
        _ ≤ c₁ * ((e + 1) * (Nat.log 2 n + 1)) ^ 2 :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hlog_k 2)
        _ = c₁ * (e + 1) ^ 2 * (Nat.log 2 n + 1) ^ 2 := by ring
    calc Cg.depth + Cin.depth
        ≤ c₁ * (e + 1) ^ 2 * (Nat.log 2 n + 1) ^ 2 + c₂ * (Nat.log 2 n + 1) ^ 2 :=
          add_le_add hCg_dp' hCin_dp
      _ = (c₁ * (e + 1) ^ 2 + c₂) * (Nat.log 2 n + 1) ^ 2 := by ring
  · simp only [Cfull, Circuit.size_comp, Cin, Circuit.comapOutputs_size, size_appendCircuits]
    have hsum : ∑ i : Fin k, (Ci i).size ≤ ∑ i : Fin k, sh i :=
      Finset.sum_le_sum fun i _ => hCi_sz i
    omega

/-- `NuItDet ⊆ NC 2`. -/
public theorem NuItDet_subset_NC_two : NuItDet ⊆ NC 2 := by
  rintro L ⟨_, ⟨ps, rfl⟩, _, ⟨hps, rfl⟩, s, hs, hL⟩
  obtain ⟨C, D, E, _, hsim⟩ := gateCompList_abpGate_to_deMorgan ps hps
  obtain ⟨e, he⟩ := (hs.add (PolynomiallyBounded.const 1)).exists_clog_le_mul_log
  refine ⟨D * (e + 1) ^ 2, fun n => C * (s n + 1) ^ E, by fun_prop, fun n => ?_⟩
  obtain ⟨circ, hcomp, hsz, hdp⟩ := hsim n (s n) (L.slice n) (hL n)
  refine ⟨circ, hcomp, ?_, hsz⟩
  have hclog : Nat.clog 2 (s n + 1) + 1 ≤ (e + 1) * (Nat.log 2 n + 1) := by
    have := he n; nlinarith
  calc circ.depth ≤ D * (Nat.clog 2 (s n + 1) + 1) ^ 2 := hdp
    _ ≤ D * ((e + 1) * (Nat.log 2 n + 1)) ^ 2 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hclog 2)
    _ = D * (e + 1) ^ 2 * (Nat.log 2 n + 1) ^ 2 := by ring

/-- `NuItDetCompMON ⊆ NC2CompMON`. -/
public theorem NuItDetCompMON_subset_NC2CompMON : NuItDetCompMON ⊆ NC2CompMON := by
  rintro L ⟨_, ⟨ps, rfl⟩, _, ⟨hps, rfl⟩, s, hs, hL⟩
  obtain ⟨C, D, E, hE, hsim⟩ := gateCompList_abpGate_to_deMorgan ps hps
  -- Pad the outer arity with `n` zero-size monotone input wires so `k' = k + n ≥ n`,
  -- ensuring `(log₂ n + 1)² ≤ (log₂ k' + 1)²` for the `nc2Gate` depth envelope.
  obtain ⟨e, he⟩ := (hs.add (PolynomiallyBounded.const 1)).exists_clog_le_mul_log
  refine Set.mem_iUnion.mpr ⟨D * (e + 1) ^ 2,
    ⟨fun n => C * (s n + 1) ^ E + s n + n, by fun_prop, fun n => ?_⟩⟩
  obtain ⟨k, g, hs_fn, sg, sh, hg, hhs, hsz, hf⟩ := hL n
  obtain ⟨Cg, hCg_comp, hCg_sz, hCg_dp⟩ := hsim k sg g hg
  let Cg' : Circuit Boolean.signature (k + n) 1 := Cg.mapInputs (Fin.castAdd n)
  let hs' : Fin (k + n) → (Fin n → Bool) → Bool := Fin.append hs_fn (fun j x => x j)
  let sh' : Fin (k + n) → ℕ := Fin.append sh (fun _ => 0)
  refine ⟨k + n, fun y => g (y ∘ Fin.castAdd n), hs', C * (s n + 1) ^ E, sh',
    ?_, ?_, ?_, ?_⟩
  · refine ⟨Cg', ?_, ?_, ?_⟩
    · rw [Circuit.mapInputs_size]
      exact hCg_sz.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) E))
    · rw [depth_mapInputs]
      have hclog : Nat.clog 2 (sg + 1) + 1 ≤ (e + 1) * (Nat.log 2 n + 1) := by
        have h1 : Nat.clog 2 (sg + 1) ≤ Nat.clog 2 (s n + 1) := Nat.clog_mono_right 2 (by omega)
        have h2 := he n
        nlinarith
      have hlog_le : Nat.log 2 n ≤ Nat.log 2 (k + n) := Nat.log_mono_right (by omega)
      calc Cg.depth ≤ D * (Nat.clog 2 (sg + 1) + 1) ^ 2 := hCg_dp
        _ ≤ D * ((e + 1) * (Nat.log 2 n + 1)) ^ 2 :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hclog 2)
        _ = D * (e + 1) ^ 2 * (Nat.log 2 n + 1) ^ 2 := by ring
        _ ≤ D * (e + 1) ^ 2 * (Nat.log 2 (k + n) + 1) ^ 2 :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)
    · intro y
      rw [Circuit.eval_mapInputs]
      exact hCg_comp (y ∘ Fin.castAdd n)
  · intro i
    refine Fin.addCases (fun j => by simpa [hs', sh'] using hhs j) (fun j => ?_) i
    refine ⟨Circuit.wiring Monotone.signature (fun _ => j), by simp [sh'], fun x => ?_⟩
    funext o; fin_cases o; simp [single_apply, hs']
  · have hsum : (∑ i : Fin (k + n), sh' i) = ∑ i : Fin k, sh i := by
      rw [Fin.sum_univ_add]; simp [sh']
    dsimp only; rw [hsum]; omega
  · intro x; rw [hf x]; congr 1; funext i; simp [hs']

end OneHotNC2

end CslibFrontier.Computability.Circuit
