/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FormalPapers Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.Unbounded.Certificate
public import CslibFrontier.Computability.Complexity.Parameterized.WHierarchy.Clique.Graph
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Lists
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.ListsUpTo
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Eq
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Tactic.PolyTime
import Mathlib.Data.List.GetD

/-!
# Bounded-Weft Circuit Certificates and Refutation Duality

For an unbounded fan-in Boolean circuit of weft at most `t + 1` and depth at most `d`, any wire
evaluation `(evalCode interpretation false x gates).getD w false = b` is characterized by a short
list of at most `2 ^ d` wire-value claims whose Kleene evaluation under `WeftOne.overrideGates`
determines `w` to `some b` and whose `WeftOne.claimChecks` all lie at weft at most `t` and depth at
most `d`. Applying Boolean negation to the target value yields an alternating certificate/refutation
duality across weft levels, culminating at weft `1` in bracket refutations (`WCS.ToClique.refutes`).

This module develops capped polynomial-time wire-depth and wire-weft evaluators (`cappedDepths`,
`cappedWefts`), weft-`1` and weft-`(t + 1)` value certificates (`validCertOne`, `certsOne`,
`validCertSucc`, `certsSucc`), soundness and completeness equivalences, refutation dualities, and
polynomial-time listing theorems for fixed depth and weft bounds. All results are proved
unconditionally under standard Lean axioms.

## Main definitions

- `CslibFrontier.ParameterizedComplexity.cappedMax`,
  `CslibFrontier.ParameterizedComplexity.cappedDepths`,
  `CslibFrontier.ParameterizedComplexity.cappedWefts`: capped list maximum and capped wire depths
  and
  wefts of unbounded fan-in gate lists.
- `CslibFrontier.ParameterizedComplexity.validCertOne`,
  `CslibFrontier.ParameterizedComplexity.certsOne`: weft-`1` certificates for a wire taking value
  `b`.
- `CslibFrontier.ParameterizedComplexity.validCertSucc`,
  `CslibFrontier.ParameterizedComplexity.certsSucc`: weft-`(t + 1)` certificates for a wire taking
  value
  `b`, whose checks have weft at most `t` and depth at most `d`.
- `CslibFrontier.ParameterizedComplexity.selectedBits`: the weight-`kk` bitstring of length `n`
  determined by `kk` selected positions `u 0 < ⋯ < u (kk - 1)`.

## Main results

- `CslibFrontier.ParameterizedComplexity.getD_cappedDepths_le_iff`,
  `CslibFrontier.ParameterizedComplexity.getD_cappedWefts_le_iff`: exact correspondence between
  capped
  wire depths/wefts and `depthInterpretation`.
- `CslibFrontier.ParameterizedComplexity.eval_eq_iff_exists_certsOne`,
  `CslibFrontier.ParameterizedComplexity.eval_eq_iff_forall_certsOne_not`: weft-`1` certificate
  characterization and refutation duality.
- `CslibFrontier.ParameterizedComplexity.eval_selectedBits_eq_iff_forall_certsOne_refutes`: weft-`1`
  evaluation on a selected weight-`kk` input via bracket refutations.
- `CslibFrontier.ParameterizedComplexity.eval_eq_iff_exists_certsSucc`,
  `CslibFrontier.ParameterizedComplexity.eval_eq_iff_forall_certsSucc_not`: weft-`(t + 1)`
  certificate
  characterization and refutation duality.
- `CslibFrontier.ParameterizedComplexity.computableInPolyTime_certsOne`,
  `CslibFrontier.ParameterizedComplexity.computableInPolyTime_certsSucc`,
  `CslibFrontier.ParameterizedComplexity.computableInPolyTime_brackets_poly`,
  `CslibFrontier.ParameterizedComplexity.computableInPolyTime_indexLists_poly`,
  `CslibFrontier.ParameterizedComplexity.computableInPolyTime_refutes_poly`: polynomial-time
  certificate
  enumeration and bracket refutation for fixed depth and weft bounds.

## Tags

parameterized complexity, W-hierarchy, Boolean circuit, weft, Kleene evaluation, certificate
-/

public section

open Cslib Cslib.Circuits Cslib.Circuits.Boolean.Unbounded
open Cslib.Complexity Cslib.Complexity.WCS.ToClique Turing.MultiTapeTM

namespace CslibFrontier.ParameterizedComplexity

/-! ### Capped wire depths and wefts -/

/-- Maximum of a list of natural numbers capped at `cap`, defined by recursion on `cap` so that for
every fixed `cap` it is polynomial-time over unary-encoded lists without accumulator growth. -/
def cappedMax : ℕ → List ℕ → ℕ
  | 0, _ => 0
  | cap + 1, l => if l.any (fun v => decide (cap + 1 ≤ v)) then cap + 1 else cappedMax cap l

/-- `cappedMax cap l` never exceeds `cap`. -/
theorem cappedMax_le (cap : ℕ) (l : List ℕ) : cappedMax cap l ≤ cap := by
  induction cap with
  | zero => simp [cappedMax]
  | succ cap ih =>
    unfold cappedMax
    split_ifs
    · exact le_rfl
    · exact ih.trans (Nat.le_succ cap)

/-- Every member `v ∈ l` satisfies `min cap v ≤ cappedMax cap l`. -/
theorem min_le_cappedMax (cap : ℕ) {l : List ℕ} {v : ℕ} (hv : v ∈ l) :
    min cap v ≤ cappedMax cap l := by
  induction cap with
  | zero => simp [cappedMax]
  | succ cap ih =>
    unfold cappedMax
    split_ifs with h
    · exact min_le_left _ _
    · rw [Bool.not_eq_true, List.any_eq_false] at h
      have hvle : v ≤ cap := by
        have := h v hv
        simp only [decide_eq_true_eq] at this
        omega
      have hmin : min (cap + 1) v = min cap v := by omega
      rw [hmin]
      exact ih

/-- An upper bound `D` on all entries of `l` bounds `cappedMax cap l` by `min cap D`. -/
theorem cappedMax_le_of_forall_le (cap : ℕ) {l : List ℕ} {D : ℕ} (h : ∀ v ∈ l, v ≤ D) :
    cappedMax cap l ≤ min cap D := by
  induction cap with
  | zero => simp [cappedMax]
  | succ cap ih =>
    unfold cappedMax
    split_ifs with ha
    · obtain ⟨u, hu, hle⟩ := List.any_eq_true.1 ha
      simp only [decide_eq_true_eq] at hle
      have huD := h u hu
      omega
    · exact ih.trans (min_le_min_right D (Nat.le_succ cap))

/-- Over `List.ofFn f`, `cappedMax cap` computes `min cap (Finset.univ.sup f)`. -/
theorem cappedMax_eq_min_sup (cap : ℕ) {m : ℕ} (f : Fin m → ℕ) :
    cappedMax cap (List.ofFn f) = min cap (Finset.univ.sup f) := by
  refine le_antisymm ?_ ?_
  · refine cappedMax_le_of_forall_le cap fun v hv => ?_
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hv
    exact Finset.le_sup (f := f) (Finset.mem_univ i)
  · rcases le_total (Finset.univ.sup f) cap with hsup | hsup
    · rw [min_eq_right hsup]
      refine Finset.sup_le fun i _ => ?_
      have hfi : f i ≤ cap := (Finset.le_sup (f := f) (Finset.mem_univ i)).trans hsup
      have hmin : min cap (f i) = f i := min_eq_right hfi
      rw [← hmin]
      exact min_le_cappedMax cap (List.mem_ofFn.2 ⟨i, rfl⟩)
    · rw [min_eq_left hsup]
      rcases Nat.eq_zero_or_pos cap with rfl | hpos
      · exact Nat.zero_le _
      · have hex : ∃ i : Fin m, cap ≤ f i := by
          by_contra! hc
          have hle : Finset.univ.sup f ≤ cap - 1 :=
            Finset.sup_le fun i _ => by have := hc i; omega
          omega
        obtain ⟨i, hi⟩ := hex
        calc cap = min cap (f i) := (min_eq_left hi).symm
          _ ≤ cappedMax cap (List.ofFn f) := min_le_cappedMax cap (List.mem_ofFn.2 ⟨i, rfl⟩)

/-- One step of capped unit-cost depth evaluation, capped at `d + 1`. -/
def cappedDepthOp (d : ℕ) (_op : Op) (l : List ℕ) : ℕ :=
  min (d + 1) (cappedMax (d + 1) l + 1)

/-- Capped wire depths of `gates` from `n` inputs, capped at `d + 1`. -/
def cappedDepths (d n : ℕ) (gates : List (Op × List ℕ)) : List ℕ :=
  gates.foldl (fun cd g => cd ++ [cappedDepthOp d g.1 (g.2.map (cd.getD · (d + 1)))])
    (List.replicate n 0)

/-- One step of capped weft evaluation, charging `1` when fan-in exceeds `2` and capping at
`t + 1`. -/
def cappedWeftOp (t : ℕ) (_op : Op) (l : List ℕ) : ℕ :=
  min (t + 1) (cappedMax (t + 1) l + if 2 < l.length then 1 else 0)

/-- Capped wire wefts of `gates` from `n` inputs, capped at `t + 1`. -/
def cappedWefts (t n : ℕ) (gates : List (Op × List ℕ)) : List ℕ :=
  gates.foldl (fun cw g => cw ++ [cappedWeftOp t g.1 (g.2.map (cw.getD · (t + 1)))])
    (List.replicate n 0)

/-- Length of `cappedDepths d n gates`. -/
theorem length_cappedDepths (d n : ℕ) (gates : List (Op × List ℕ)) :
    (cappedDepths d n gates).length = n + gates.length := by
  suffices ∀ x : List ℕ, (gates.foldl (fun cd g =>
      cd ++ [cappedDepthOp d g.1 (g.2.map (cd.getD · (d + 1)))]) x).length =
      x.length + gates.length by
    simpa [cappedDepths] using this (List.replicate n 0)
  intro x
  induction gates generalizing x with
  | nil => simp
  | cons g gates ih =>
    rw [List.foldl_cons, ih, List.length_append, List.length_singleton, List.length_cons]
    omega

/-- Length of `cappedWefts t n gates`. -/
theorem length_cappedWefts (t n : ℕ) (gates : List (Op × List ℕ)) :
    (cappedWefts t n gates).length = n + gates.length := by
  suffices ∀ x : List ℕ, (gates.foldl (fun cw g =>
      cw ++ [cappedWeftOp t g.1 (g.2.map (cw.getD · (t + 1)))]) x).length =
      x.length + gates.length by
    simpa [cappedWefts] using this (List.replicate n 0)
  intro x
  induction gates generalizing x with
  | nil => simp
  | cons g gates ih =>
    rw [List.foldl_cons, ih, List.length_append, List.length_singleton, List.length_cons]
    omega

private theorem getD_cappedDepths_of_lt (d n : ℕ) (gates : List (Op × List ℕ)) {w : ℕ}
    (hw : w < n) : (cappedDepths d n gates).getD w (d + 1) = 0 := by
  have hpre : List.replicate n 0 <+: cappedDepths d n gates := by
    unfold cappedDepths
    generalize List.replicate n 0 = x
    induction gates generalizing x with
    | nil => exact List.prefix_refl _
    | cons g gates ih => exact (List.prefix_append _ _).trans (ih _)
  obtain ⟨r, hr⟩ := hpre
  rw [← hr, List.getD_append _ _ _ _ (by simpa using hw)]
  simp [List.getD_eq_getElem?_getD, hw]

private theorem getD_cappedWefts_of_lt (t n : ℕ) (gates : List (Op × List ℕ)) {w : ℕ}
    (hw : w < n) : (cappedWefts t n gates).getD w (t + 1) = 0 := by
  have hpre : List.replicate n 0 <+: cappedWefts t n gates := by
    unfold cappedWefts
    generalize List.replicate n 0 = x
    induction gates generalizing x with
    | nil => exact List.prefix_refl _
    | cons g gates ih => exact (List.prefix_append _ _).trans (ih _)
  obtain ⟨r, hr⟩ := hpre
  rw [← hr, List.getD_append _ _ _ _ (by simpa using hw)]
  simp [List.getD_eq_getElem?_getD, hw]

private theorem getD_cappedDepths_add {d n : ℕ} {gates : List (Op × List ℕ)}
    (h : Program.IsCodeFrom signature n 0 gates) {j : ℕ} {g : Op × List ℕ}
    (hg : gates[j]? = some g) :
    (cappedDepths d n gates).getD (n + j) (d + 1) =
      cappedDepthOp d g.1 (g.2.map ((cappedDepths d n gates).getD · (d + 1))) := by
  have heq : cappedDepths d n gates =
      evalCode (σ := signature) (fun op a => cappedDepthOp d op (List.ofFn a))
        (d + 1) (List.replicate n 0) gates :=
    foldl_eq_evalCode (σ := signature) (cappedDepthOp d) (d + 1) _ (length_eq_arity_of_isCodeFrom h)
  rw [heq]
  exact getD_evalCode_eq_map (σ := signature) (cappedDepthOp d) (fun _ _ => rfl) (d + 1)
    List.length_replicate h hg

private theorem getD_cappedWefts_add {t n : ℕ} {gates : List (Op × List ℕ)}
    (h : Program.IsCodeFrom signature n 0 gates) {j : ℕ} {g : Op × List ℕ}
    (hg : gates[j]? = some g) :
    (cappedWefts t n gates).getD (n + j) (t + 1) =
      cappedWeftOp t g.1 (g.2.map ((cappedWefts t n gates).getD · (t + 1))) := by
  have heq : cappedWefts t n gates =
      evalCode (σ := signature) (fun op a => cappedWeftOp t op (List.ofFn a))
        (t + 1) (List.replicate n 0) gates :=
    foldl_eq_evalCode (σ := signature) (cappedWeftOp t) (t + 1) _ (length_eq_arity_of_isCodeFrom h)
  rw [heq]
  exact getD_evalCode_eq_map (σ := signature) (cappedWeftOp t) (fun _ _ => rfl) (t + 1)
    List.length_replicate h hg

private theorem exists_gate_at_offset {n w : ℕ} {gates : List (Op × List ℕ)}
    (h : Program.IsCodeFrom signature n 0 gates) (hw : w < n + gates.length) (hwn : n ≤ w) :
    ∃ (j : ℕ) (g : Op × List ℕ), w = n + j ∧ j < gates.length ∧ gates[j]? = some g ∧
      g.2.length = signature.Arity g.1 ∧ ∀ c ∈ g.2, c < n + j := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hwn
  have hj : j < gates.length := by omega
  obtain ⟨hlen, hlt⟩ := h.getElem j hj
  exact ⟨j, gates[j], rfl, hj, List.getElem?_eq_getElem hj, hlen, hlt⟩

/-- On every valid wire `w < n + gates.length`, `cappedDepths d n gates` computes the unit-cost
wire depth capped at `d + 1`. -/
theorem getD_cappedDepths_eq_min {d n : ℕ} {gates : List (Op × List ℕ)}
    (h : Program.IsCodeFrom signature n 0 gates) {w : ℕ} (hw : w < n + gates.length) :
    (cappedDepths d n gates).getD w (d + 1) =
      min (d + 1) ((evalCode (depthInterpretation (σ := signature) 1) 0
        (List.replicate n 0) gates).getD w 0) := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    rcases Nat.lt_or_ge w n with hwn | hwn
    · rw [getD_cappedDepths_of_lt d n gates hwn,
        getD_evalCode_of_lt _ _ _ _ (by simpa using hwn)]
      simp [List.getD_eq_getElem?_getD, hwn]
    obtain ⟨j, g, rfl, _, hg, hlen, hlt⟩ := exists_gate_at_offset h hw hwn
    rw [getD_cappedDepths_add h hg]
    have h' : Program.IsCodeFrom signature (List.replicate n 0).length 0 gates := by
      rwa [List.length_replicate]
    have hv := getD_evalCode (depthInterpretation (σ := signature) 1) 0 (List.replicate n 0) h' hg
    rw [List.length_replicate] at hv
    rw [hv, depthInterpretation, Fin.foldl_max_eq_max_sup, Nat.zero_max, Pi.one_apply]
    let f : Fin (signature.Arity g.1) → ℕ := fun a =>
      g.2[a.val]?.elim 0
        ((evalCode (depthInterpretation (σ := signature) 1) 0 (List.replicate n 0) gates).getD · 0)
    have hmap : g.2.map ((cappedDepths d n gates).getD · (d + 1)) =
        List.ofFn (fun a => min (d + 1) (f a)) := by
      rw [← ofFn_elim_eq_map (σ := signature) (d + 1) (cappedDepths d n gates) g hlen]
      refine List.ext_getElem (by simp) fun i h₁ h₂ => ?_
      simp only [List.getElem_ofFn, f]
      have hi : i < g.2.length := by simpa [hlen] using h₁
      rw [List.getElem?_eq_getElem hi]
      simp only [Option.elim_some]
      have hci : g.2[i] < n + j := hlt g.2[i] (List.getElem_mem hi)
      exact ih g.2[i] hci (by omega)
    rw [cappedDepthOp, hmap, cappedMax_eq_min_sup]
    have hsup : (Finset.univ.sup fun a => min (d + 1) (f a)) = min (d + 1) (Finset.univ.sup f) := by
      refine le_antisymm (Finset.sup_le fun a _ =>
          min_le_min_left (d + 1) (Finset.le_sup (f := f) (Finset.mem_univ a))) ?_
      rcases le_total (Finset.univ.sup f) (d + 1) with hle | hle
      · rw [min_eq_right hle]
        refine Finset.sup_le fun a _ => ?_
        have hfa : f a ≤ d + 1 := (Finset.le_sup (f := f) (Finset.mem_univ a)).trans hle
        rw [← min_eq_right hfa]
        exact Finset.le_sup (f := fun b => min (d + 1) (f b)) (Finset.mem_univ a)
      · rw [min_eq_left hle]
        have hex : ∃ a, d + 1 ≤ f a := by
          by_contra! hc
          have hle' : Finset.univ.sup f ≤ d := Finset.sup_le fun a _ => by have := hc a; omega
          omega
        obtain ⟨a, ha⟩ := hex
        calc d + 1 = min (d + 1) (f a) := (min_eq_left ha).symm
          _ ≤ Finset.univ.sup fun b => min (d + 1) (f b) :=
            Finset.le_sup (f := fun b => min (d + 1) (f b)) (Finset.mem_univ a)
    rw [hsup]
    change min (d + 1) (min (d + 1) (min (d + 1) (Finset.univ.sup f)) + 1) =
      min (d + 1) (Finset.univ.sup f + 1)
    omega

/-- On every valid wire `w < n + gates.length`, `cappedWefts t n gates` computes the wire weft
capped at `t + 1`. -/
theorem getD_cappedWefts_eq_min {t n : ℕ} {gates : List (Op × List ℕ)}
    (h : Program.IsCodeFrom signature n 0 gates) {w : ℕ} (hw : w < n + gates.length) :
    (cappedWefts t n gates).getD w (t + 1) =
      min (t + 1) ((evalCode (depthInterpretation (largeGateCost signature)) 0
        (List.replicate n 0) gates).getD w 0) := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    rcases Nat.lt_or_ge w n with hwn | hwn
    · rw [getD_cappedWefts_of_lt t n gates hwn,
        getD_evalCode_of_lt _ _ _ _ (by simpa using hwn)]
      simp [List.getD_eq_getElem?_getD, hwn]
    obtain ⟨j, g, rfl, _, hg, hlen, hlt⟩ := exists_gate_at_offset h hw hwn
    rw [getD_cappedWefts_add h hg]
    have h' : Program.IsCodeFrom signature (List.replicate n 0).length 0 gates := by
      rwa [List.length_replicate]
    have hv := getD_evalCode (depthInterpretation (largeGateCost signature)) 0
      (List.replicate n 0) h' hg
    rw [List.length_replicate] at hv
    rw [hv, depthInterpretation, Fin.foldl_max_eq_max_sup, Nat.zero_max]
    let f : Fin (signature.Arity g.1) → ℕ := fun a =>
      g.2[a.val]?.elim 0
        ((evalCode (depthInterpretation (largeGateCost signature)) 0
          (List.replicate n 0) gates).getD · 0)
    have hmap : g.2.map ((cappedWefts t n gates).getD · (t + 1)) =
        List.ofFn (fun a => min (t + 1) (f a)) := by
      rw [← ofFn_elim_eq_map (σ := signature) (t + 1) (cappedWefts t n gates) g hlen]
      refine List.ext_getElem (by simp) fun i h₁ h₂ => ?_
      simp only [List.getElem_ofFn, f]
      have hi : i < g.2.length := by simpa [hlen] using h₁
      rw [List.getElem?_eq_getElem hi]
      simp only [Option.elim_some]
      have hci : g.2[i] < n + j := hlt g.2[i] (List.getElem_mem hi)
      exact ih g.2[i] hci (by omega)
    have hcost : (if 2 < (g.2.map ((cappedWefts t n gates).getD · (t + 1))).length then 1 else 0) =
        largeGateCost signature g.1 := by
      rw [List.length_map, hlen]
      rfl
    rw [cappedWeftOp, hcost, hmap, cappedMax_eq_min_sup]
    have hsup : (Finset.univ.sup fun a => min (t + 1) (f a)) = min (t + 1) (Finset.univ.sup f) := by
      refine le_antisymm (Finset.sup_le fun a _ =>
          min_le_min_left (t + 1) (Finset.le_sup (f := f) (Finset.mem_univ a))) ?_
      rcases le_total (Finset.univ.sup f) (t + 1) with hle | hle
      · rw [min_eq_right hle]
        refine Finset.sup_le fun a _ => ?_
        have hfa : f a ≤ t + 1 := (Finset.le_sup (f := f) (Finset.mem_univ a)).trans hle
        rw [← min_eq_right hfa]
        exact Finset.le_sup (f := fun b => min (t + 1) (f b)) (Finset.mem_univ a)
      · rw [min_eq_left hle]
        have hex : ∃ a, t + 1 ≤ f a := by
          by_contra! hc
          have hle' : Finset.univ.sup f ≤ t := Finset.sup_le fun a _ => by have := hc a; omega
          omega
        obtain ⟨a, ha⟩ := hex
        calc t + 1 = min (t + 1) (f a) := (min_eq_left ha).symm
          _ ≤ Finset.univ.sup fun b => min (t + 1) (f b) :=
            Finset.le_sup (f := fun b => min (t + 1) (f b)) (Finset.mem_univ a)
    rw [hsup]
    change min (t + 1) (min (t + 1) (min (t + 1) (Finset.univ.sup f)) +
        largeGateCost signature g.1) =
      min (t + 1) (Finset.univ.sup f + largeGateCost signature g.1)
    omega

/-- For `D ≤ d`, `(cappedDepths d n gates).getD w (d + 1) ≤ D` holds if and only if `w` is a wire
of the code with unit-cost depth at most `D`. -/
theorem getD_cappedDepths_le_iff {d n : ℕ} {gates : List (Op × List ℕ)}
    (h : Program.IsCodeFrom signature n 0 gates) {w D : ℕ} (hD : D ≤ d) :
    (cappedDepths d n gates).getD w (d + 1) ≤ D ↔
      w < n + gates.length ∧
        (evalCode (depthInterpretation (σ := signature) 1) 0
          (List.replicate n 0) gates).getD w 0 ≤ D := by
  rcases Nat.lt_or_ge w (n + gates.length) with hw | hw
  · rw [getD_cappedDepths_eq_min h hw]
    constructor
    · intro hle
      exact ⟨hw, by omega⟩
    · rintro ⟨-, hle⟩
      omega
  · rw [List.getD_eq_default _ _ (by rw [length_cappedDepths]; exact hw)]
    omega

/-- For `T ≤ t`, `(cappedWefts t n gates).getD w (t + 1) ≤ T` holds if and only if `w` is a wire of
the code with weft at most `T`. -/
theorem getD_cappedWefts_le_iff {t n : ℕ} {gates : List (Op × List ℕ)}
    (h : Program.IsCodeFrom signature n 0 gates) {w T : ℕ} (hT : T ≤ t) :
    (cappedWefts t n gates).getD w (t + 1) ≤ T ↔
      w < n + gates.length ∧
        (evalCode (depthInterpretation (largeGateCost signature)) 0
          (List.replicate n 0) gates).getD w 0 ≤ T := by
  rcases Nat.lt_or_ge w (n + gates.length) with hw | hw
  · rw [getD_cappedWefts_eq_min h hw]
    constructor
    · intro hle
      exact ⟨hw, by omega⟩
    · rintro ⟨-, hle⟩
      omega
  · rw [List.getD_eq_default _ _ (by rw [length_cappedWefts]; exact hw)]
    omega

/-! ### Certificates for arbitrary Boolean values and weft levels -/

/-- Weft-`1` certificate validity for wire `w` taking Boolean value `b` at depth bound `d`. -/
def validCertOne (d n : ℕ) (gates : List (Op × List ℕ)) (w : ℕ) (b : Bool)
    (claims : List (ℕ × Bool)) : Bool :=
  decide ((kleeneEval (WeftOne.claimInputs n claims)
    (WeftOne.overrideGates n claims gates)).getD w none = some b) &&
  (claims.flatMap (WeftOne.claimChecks n gates)).all fun e =>
    decide ((WeftOne.smallDepths d n gates).getD e.1 (d + 1) ≤ d)

/-- All weft-`1` certificates of length at most `2 ^ d` for wire `w` taking value `b`. -/
def certsOne (d n : ℕ) (gates : List (Op × List ℕ)) (w : ℕ) (b : Bool) :
    List (List (ℕ × Bool)) :=
  ((claimUniverse n gates.length).listsUpTo (2 ^ d)).filter (validCertOne d n gates w b)

/-- Weft-`(t + 1)` certificate validity for wire `w` taking Boolean value `b` at depth bound `d`:
Kleene evaluation under `overrideGates` determines `w` to `some b`, and every check has weft at
most `t` and depth at most `d`. -/
@[expose]
def validCertSucc (t d n : ℕ) (gates : List (Op × List ℕ)) (w : ℕ) (b : Bool)
    (claims : List (ℕ × Bool)) : Bool :=
  decide ((kleeneEval (WeftOne.claimInputs n claims)
    (WeftOne.overrideGates n claims gates)).getD w none = some b) &&
  (claims.flatMap (WeftOne.claimChecks n gates)).all fun e =>
    decide ((cappedWefts t n gates).getD e.1 (t + 1) ≤ t) &&
      decide ((cappedDepths d n gates).getD e.1 (d + 1) ≤ d)

/-- All weft-`(t + 1)` certificates of length at most `2 ^ d` for wire `w` taking value `b`. -/
def certsSucc (t d n : ℕ) (gates : List (Op × List ℕ)) (w : ℕ) (b : Bool) :
    List (List (ℕ × Bool)) :=
  ((claimUniverse n gates.length).listsUpTo (2 ^ d)).filter (validCertSucc t d n gates w b)

/-- Membership in `certsOne`. -/
theorem mem_certsOne {d n : ℕ} {gates : List (Op × List ℕ)} {w : ℕ} {b : Bool}
    {cl : List (ℕ × Bool)} :
    cl ∈ certsOne d n gates w b ↔
      cl.length ≤ 2 ^ d ∧ (∀ c ∈ cl, c.1 < n + gates.length) ∧
        validCertOne d n gates w b cl = true := by
  simp only [certsOne, List.mem_filter, List.mem_listsUpTo, mem_claimUniverse, and_assoc]

/-- Membership in `certsSucc`. -/
theorem mem_certsSucc {t d n : ℕ} {gates : List (Op × List ℕ)} {w : ℕ} {b : Bool}
    {cl : List (ℕ × Bool)} :
    cl ∈ certsSucc t d n gates w b ↔
      cl.length ≤ 2 ^ d ∧ (∀ c ∈ cl, c.1 < n + gates.length) ∧
        validCertSucc t d n gates w b cl = true := by
  simp only [certsSucc, List.mem_filter, List.mem_listsUpTo, mem_claimUniverse, and_assoc]

/-- **Universal soundness of Kleene override certificates.** If Kleene evaluation from claimed
inputs and gates determines wire `w` to `some b`, and every check of `claims` holds on `x`, then
wire `w` evaluates to `b` on `x`. -/
theorem eval_eq_of_kleeneEval_override {n : ℕ} {gates : List (Op × List ℕ)}
    (h : Program.IsCodeFrom signature n 0 gates) {w : ℕ} {b : Bool}
    {claims : List (ℕ × Bool)}
    (hkl : (kleeneEval (WeftOne.claimInputs n claims)
      (WeftOne.overrideGates n claims gates)).getD w none = some b)
    {x : List Bool} (hx : x.length = n)
    (hchecks : ∀ e ∈ claims.flatMap (WeftOne.claimChecks n gates),
      (evalCode interpretation false x gates).getD e.1 false = e.2) :
    (evalCode interpretation false x gates).getD w false = b := by
  have hcl : ∀ c ∈ claims, (c.1 < n ∨ WeftOne.claimable (WeftOne.gateAt n gates c.1) = some c.2) →
      (evalCode interpretation false x gates).getD c.1 false = c.2 := by
    intro c hc hcases
    rcases Nat.lt_or_ge c.1 n with hlt | hge
    · exact hchecks c (List.mem_flatMap.2 ⟨c, hc, by simp [WeftOne.claimChecks, hlt]⟩)
    · obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le hge
      have hb := hcases.resolve_left hge.not_gt
      have hlt' : ¬n + j < n := by omega
      rcases hg : gates[j]? with _ | g
      · rw [hj, WeftOne.gateAt, Nat.add_sub_cancel_left, List.getD_eq_getElem?_getD, hg] at hb
        simp [WeftOne.claimable] at hb
      rw [hj, WeftOne.gateAt_add hg] at hb
      rw [hj, WeftOne.getD_evalCode_eq_iff_of_claimable h hx hg hb]
      exact fun c' hc' => hchecks (c', c.2)
        (List.mem_flatMap.2 ⟨c, hc,
          by simp [WeftOne.claimChecks, hj, WeftOne.gateAt_add hg, hb, hlt', hc']⟩)
  exact (approx_some.1 (hkl ▸ WeftOne.approx_override h hx hcl w)).symm

/-- **Weft-`1` certificate characterization** for any target Boolean `b`. -/
theorem eval_eq_iff_exists_certsOne {d n : ℕ} {gates : List (Op × List ℕ)}
    (h : Program.IsCodeFrom signature n 0 gates) {x : List Bool} (hx : x.length = n)
    {w : ℕ} (hw : w < n + gates.length)
    (hweft : (evalCode (depthInterpretation (largeGateCost signature)) 0
      (List.replicate n 0) gates).getD w 0 ≤ 1)
    (hdepth : (evalCode (depthInterpretation (σ := signature) 1) 0
      (List.replicate n 0) gates).getD w 0 ≤ d)
    (b : Bool) :
    (evalCode interpretation false x gates).getD w false = b ↔
      ∃ cl ∈ certsOne d n gates w b,
        ∀ e ∈ cl.flatMap (WeftOne.claimChecks n gates),
          (evalCode interpretation false x gates).getD e.1 false = e.2 := by
  constructor
  · intro hv
    obtain ⟨cl, hlen, hcorr, hchk, hfin⟩ := WeftOne.exists_claims h hx hw hweft hdepth
    have hkl : (kleeneEval (WeftOne.claimInputs n cl)
        (WeftOne.overrideGates n cl gates)).getD w none = some b :=
      (WeftOne.getD_kleeneEval_overrideGates_eq h hx (fun c hc => (hcorr c hc).2)
        (hfin cl (.refl _) fun c hc => (hcorr c hc).2)).trans (congrArg some hv)
    refine ⟨cl, mem_certsOne.2 ⟨hlen.trans (Nat.pow_le_pow_right (by decide) hdepth),
      fun c hc => (hcorr c hc).1, ?_⟩,
      WeftOne.checks_correct h hx fun c hc => (hcorr c hc).2⟩
    simp only [validCertOne, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
    exact ⟨hkl, hchk⟩
  · rintro ⟨cl, hcl, hchecks⟩
    have hvalid := (mem_certsOne.1 hcl).2.2
    simp only [validCertOne, Bool.and_eq_true, decide_eq_true_eq] at hvalid
    exact eval_eq_of_kleeneEval_override h hvalid.1 hx hchecks

/-- **Weft-`1` refutation duality.** A wire `w` of weft at most `1` and depth at most `d` takes
value `b` on `x` if and only if every weft-`1` certificate for `!b` has a failing check on `x`. -/
theorem eval_eq_iff_forall_certsOne_not {d n : ℕ} {gates : List (Op × List ℕ)}
    (h : Program.IsCodeFrom signature n 0 gates) {x : List Bool} (hx : x.length = n)
    {w : ℕ} (hw : w < n + gates.length)
    (hweft : (evalCode (depthInterpretation (largeGateCost signature)) 0
      (List.replicate n 0) gates).getD w 0 ≤ 1)
    (hdepth : (evalCode (depthInterpretation (σ := signature) 1) 0
      (List.replicate n 0) gates).getD w 0 ≤ d)
    (b : Bool) :
    (evalCode interpretation false x gates).getD w false = b ↔
      ∀ cl ∈ certsOne d n gates w (!b),
        ∃ e ∈ cl.flatMap (WeftOne.claimChecks n gates),
          (evalCode interpretation false x gates).getD e.1 false = !e.2 := by
  have hnot := eval_eq_iff_exists_certsOne h hx hw hweft hdepth (!b)
  have hbool : (evalCode interpretation false x gates).getD w false = b ↔
      ¬((evalCode interpretation false x gates).getD w false = !b) := by
    cases (evalCode interpretation false x gates).getD w false <;> cases b <;> decide
  rw [hbool, hnot]
  push Not
  refine forall_congr' fun cl => imp_congr_right fun _ => exists_congr fun e =>
    and_congr_right fun _ => ?_
  cases (evalCode interpretation false x gates).getD e.1 false <;> cases e.2 <;> decide

private theorem kleeneOp_of_claimable' {g : Op × List ℕ} {b : Bool}
    (hb : WeftOne.claimable g = some b) {l : List (Option Bool)} (hl : some (!b) ∈ l) :
    kleeneOp g.1 l = some (!b) := by
  rcases g with ⟨_ | m | m, args⟩
  · simp [WeftOne.claimable] at hb
  · obtain rfl := Option.some.inj hb
    exact kleeneAnd_of_mem hl
  · obtain rfl := Option.some.inj hb
    exact kleeneOr_of_mem hl

private theorem getD_evalCode_add' {n : ℕ} {gates : List (Op × List ℕ)}
    (h : Program.IsCodeFrom signature n 0 gates) {x : List Bool} (hx : x.length = n) {j : ℕ}
    {g : Op × List ℕ} (hg : gates[j]? = some g) :
    (evalCode interpretation false x gates).getD (n + j) false =
      interpretation g.1 fun a => g.2[a.val]?.elim false
        ((evalCode interpretation false x gates).getD · false) := by
  subst hx
  exact getD_evalCode interpretation false x h hg

/-- **Claims for a wire of weft at most `t + 1`.** Every wire `w < n + gates.length` of weft at
most `t + 1` and depth at most `d` admits a list `cl` of at most `2 ^ depth(w)` correct claims
whose checks all have weft at most `t` and depth at most `d`, and which determine `w` under Kleene
evaluation of `overrideGates`. -/
theorem exists_claims_succ {t d n : ℕ} {gates : List (Op × List ℕ)}
    (h : Program.IsCodeFrom signature n 0 gates) {x : List Bool} (hx : x.length = n) {w : ℕ}
    (hw : w < n + gates.length)
    (hwd : (evalCode (depthInterpretation (largeGateCost signature)) 0
      (List.replicate n 0) gates).getD w 0 ≤ t + 1)
    (hdp : (evalCode (depthInterpretation (σ := signature) 1) 0
      (List.replicate n 0) gates).getD w 0 ≤ d) :
    ∃ cl : List (ℕ × Bool),
      cl.length ≤ 2 ^ (evalCode (depthInterpretation (σ := signature) 1) 0
        (List.replicate n 0) gates).getD w 0 ∧
      (∀ c ∈ cl, c.1 < n + gates.length ∧
        (evalCode interpretation false x gates).getD c.1 false = c.2) ∧
      (∀ e ∈ cl.flatMap (WeftOne.claimChecks n gates),
        (cappedWefts t n gates).getD e.1 (t + 1) ≤ t ∧
          (cappedDepths d n gates).getD e.1 (d + 1) ≤ d) ∧
      ∀ claims : List (ℕ × Bool), cl ⊆ claims →
        (∀ c ∈ claims, (evalCode interpretation false x gates).getD c.1 false = c.2) →
        (kleeneEval (WeftOne.claimInputs n claims)
          (WeftOne.overrideGates n claims gates)).getD w none ≠ none := by
  have hρ (claims : List (ℕ × Bool)) := WeftOne.length_claimInputs n claims
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    rcases Nat.lt_or_ge w n with hwn | hwn
    · refine ⟨[(w, (evalCode interpretation false x gates).getD w false)],
        by simpa using Nat.one_le_two_pow,
        fun c hc => ?_, fun e he => ?_, fun claims hsub _ => ?_⟩
      · exact List.mem_singleton.1 hc ▸ ⟨hw, rfl⟩
      · simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, WeftOne.claimChecks,
          hwn, ↓reduceIte, List.mem_singleton] at he
        subst he
        exact ⟨(getD_cappedWefts_of_lt t n gates hwn).le.trans (Nat.zero_le _),
          (getD_cappedDepths_of_lt d n gates hwn).le.trans (Nat.zero_le _)⟩
      · have hmem := hsub (List.mem_singleton_self _)
        rw [getD_kleeneEval_of_lt _ _ (by rw [hρ]; exact hwn), WeftOne.getD_claimInputs _ hwn,
          WeftOne.claimInput]
        split_ifs <;> try exact Option.some_ne_none _
        cases hb : (evalCode interpretation false x gates).getD w false <;>
          rw [hb] at hmem <;> contradiction
    obtain ⟨j, g, rfl, _, hg, hlen, hlt⟩ := exists_gate_at_offset h hw hwn
    have hwdc : ∀ c ∈ g.2, (evalCode (depthInterpretation (largeGateCost signature)) 0
        (List.replicate n 0) gates).getD c 0 + largeGateCost signature g.1 ≤ t + 1 :=
      fun c hc => (getD_evalCode_depth_le _ h hg hc).trans hwd
    have hdpc : ∀ c ∈ g.2,
        (evalCode (depthInterpretation (σ := signature) 1) 0 (List.replicate n 0)
          gates).getD c 0 + 1 ≤
          (evalCode (depthInterpretation (σ := signature) 1) 0 (List.replicate n 0)
            gates).getD (n + j) 0 :=
      fun c hc => getD_evalCode_depth_le 1 h hg hc
    have hcw : ∀ c ∈ g.2, c < n + j := fun c hc => by have := hlt c hc; omega
    set v := evalCode interpretation false x gates
    by_cases hlarge : 2 < g.2.length
    · have hcost : largeGateCost signature g.1 = 1 := by
        unfold largeGateCost
        have : 2 < signature.Arity g.1 := by simpa [hlen] using hlarge
        simp [this]
      have hchild_bounds : ∀ c ∈ g.2,
          (cappedWefts t n gates).getD c (t + 1) ≤ t ∧
            (cappedDepths d n gates).getD c (d + 1) ≤ d := by
        intro c hc
        have hclt : c < n + gates.length := by have := hcw c hc; omega
        rw [getD_cappedWefts_le_iff h le_rfl, getD_cappedDepths_le_iff h le_rfl]
        refine ⟨⟨hclt, ?_⟩, ⟨hclt, ?_⟩⟩
        · have := hwdc c hc; omega
        · have := hdpc c hc; omega
      obtain ⟨b0, hb0⟩ : ∃ b0, WeftOne.claimable g = some b0 := by
        obtain ⟨_ | _ | _, args⟩ := g
        · exact absurd (hlarge : 2 < args.length) (by rw [show args.length = 1 from hlen]; decide)
        all_goals exact ⟨_, rfl⟩
      by_cases hvb : v.getD (n + j) false = b0
      · refine ⟨[(n + j, b0)], ?_, fun c hc => ?_, fun e he => ?_, fun claims hsub _ => ?_⟩
        · simpa only [List.length_singleton] using Nat.one_le_two_pow
        · rw [List.mem_singleton] at hc; subst hc; exact ⟨hw, hvb⟩
        · have hnj : ¬n + j < n := Nat.not_lt.2 (Nat.le_add_right n j)
          simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, WeftOne.claimChecks,
            hnj, WeftOne.gateAt_add hg, hb0, ↓reduceIte, List.mem_map] at he
          obtain ⟨c, hc, rfl⟩ := he
          exact hchild_bounds c hc
        · have hmem := hsub (List.mem_singleton_self _)
          rw [WeftOne.getD_kleeneEval_overrideGates h (hρ claims) claims hg]
          cases b0 <;> simp [hb0, hmem]
      · obtain ⟨c, hc, hvc⟩ : ∃ c ∈ g.2, v.getD c false = !b0 := by
          by_contra! hcon
          exact hvb ((WeftOne.getD_evalCode_eq_iff_of_claimable h hx hg hb0).2 fun c hc => by
            cases b0 <;> simpa using hcon c hc)
        obtain ⟨cl, hcl_len, hcl_corr, hcl_chk, hcl_fin⟩ := ih c (hcw c hc)
          (by have := hcw c hc; omega) (by have := hwdc c hc; omega)
          (by have := hdpc c hc; omega)
        refine ⟨cl,
          hcl_len.trans (Nat.pow_le_pow_right Nat.zero_lt_two (by have := hdpc c hc; omega)),
          hcl_corr, hcl_chk, fun claims hsub hcorr => ?_⟩
        have hκc := WeftOne.getD_kleeneEval_overrideGates_eq h hx hcorr (hcl_fin claims hsub hcorr)
        rw [WeftOne.getD_kleeneEval_overrideGates h (hρ claims) claims hg]
        split_ifs <;> try exact Option.some_ne_none _
        rw [kleeneOp_of_claimable' hb0 (List.mem_map.2 ⟨c, hc, hκc.trans (congrArg some hvc)⟩)]
        exact Option.some_ne_none _
    · rw [not_lt] at hlarge
      choose! CL hCL_len hCL_corr hCL_chk hCL_fin using fun c (hc : c ∈ g.2) =>
        ih c (hcw c hc) (by have := hcw c hc; omega) (by have := hwdc c hc; omega)
          (by have := hdpc c hc; omega)
      refine ⟨g.2.flatMap CL, ?_, List.forall_mem_flatMap.2 hCL_corr, ?_,
        fun claims hsub hcorr => ?_⟩
      · have hX := cost_le_getD_evalCode_depth 1 h hg
        simp only [Pi.one_apply] at hX
        rw [List.length_flatMap]
        refine (List.sum_le_length_nsmul _ _
          (List.forall_mem_map.2 fun c hc => (hCL_len c hc).trans
            (Nat.pow_le_pow_right (by decide) (Nat.le_sub_one_of_lt (hdpc c hc))))).trans ?_
        rw [List.length_map, smul_eq_mul]
        exact (Nat.mul_le_mul_right _ hlarge).trans_eq (by rw [← pow_succ', Nat.sub_add_cancel hX])
      · rw [List.flatMap_assoc]
        exact List.forall_mem_flatMap.2 hCL_chk
      · have hkc : ∀ c ∈ g.2, (kleeneEval (WeftOne.claimInputs n claims)
            (WeftOne.overrideGates n claims gates)).getD c none = some (v.getD c false) :=
          fun c hc => WeftOne.getD_kleeneEval_overrideGates_eq h hx hcorr (hCL_fin c hc claims
            (fun c' hc' => hsub (List.mem_flatMap.2 ⟨c, hc, hc'⟩)) hcorr)
        rw [WeftOne.getD_kleeneEval_overrideGates h (hρ claims) claims hg]
        split_ifs <;> try exact Option.some_ne_none _
        have hmap : g.2.map (fun a => some (v.getD a false)) =
            (g.2.map (v.getD · false)).map some := List.map_map.symm
        rw [List.map_congr_left hkc, hmap]
        exact kleeneOp_map_some_ne_none g.1 (by rw [List.length_map]; exact hlen)

/-- Every check of a certificate `cl ∈ certsSucc t d n gates w b` lies on a valid wire of weft at
most `t` and depth at most `d`. -/
theorem check_bounds_of_mem_certsSucc {t d n : ℕ} {gates : List (Op × List ℕ)}
    (h : Program.IsCodeFrom signature n 0 gates) {w : ℕ} {b : Bool} {cl : List (ℕ × Bool)}
    (hcl : cl ∈ certsSucc t d n gates w b) {e : ℕ × Bool}
    (he : e ∈ cl.flatMap (WeftOne.claimChecks n gates)) :
    e.1 < n + gates.length ∧
      (evalCode (depthInterpretation (largeGateCost signature)) 0
        (List.replicate n 0) gates).getD e.1 0 ≤ t ∧
      (evalCode (depthInterpretation (σ := signature) 1) 0
        (List.replicate n 0) gates).getD e.1 0 ≤ d := by
  have hvalid := (mem_certsSucc.1 hcl).2.2
  simp only [validCertSucc, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hvalid
  obtain ⟨hwft, hdp⟩ := hvalid.2 e he
  rw [getD_cappedWefts_le_iff h le_rfl] at hwft
  rw [getD_cappedDepths_le_iff h le_rfl] at hdp
  exact ⟨hwft.1, hwft.2, hdp.2⟩

/-- Every certificate `cl ∈ certsSucc t d n gates w b` evaluates `w` to `some b` under `kleeneEval`
with `WeftOne.overrideGates`. -/
theorem kleeneEval_of_mem_certsSucc {t d n w : ℕ} {gates : List (Op × List ℕ)}
    {b : Bool} {cl : List (ℕ × Bool)} (hcl : cl ∈ certsSucc t d n gates w b) :
    (kleeneEval (WeftOne.claimInputs n cl) (WeftOne.overrideGates n cl gates)).getD w none =
      some b := by
  have hvalid := (mem_certsSucc.1 hcl).2.2
  simp only [validCertSucc, Bool.and_eq_true, decide_eq_true_eq] at hvalid
  exact hvalid.1

/-- **Weft-`(t + 1)` certificate characterization** for any target Boolean `b`. -/
theorem eval_eq_iff_exists_certsSucc {t d n : ℕ} {gates : List (Op × List ℕ)}
    (h : Program.IsCodeFrom signature n 0 gates) {x : List Bool} (hx : x.length = n)
    {w : ℕ} (hw : w < n + gates.length)
    (hweft : (evalCode (depthInterpretation (largeGateCost signature)) 0
      (List.replicate n 0) gates).getD w 0 ≤ t + 1)
    (hdepth : (evalCode (depthInterpretation (σ := signature) 1) 0
      (List.replicate n 0) gates).getD w 0 ≤ d)
    (b : Bool) :
    (evalCode interpretation false x gates).getD w false = b ↔
      ∃ cl ∈ certsSucc t d n gates w b,
        ∀ e ∈ cl.flatMap (WeftOne.claimChecks n gates),
          (evalCode interpretation false x gates).getD e.1 false = e.2 := by
  constructor
  · intro hv
    obtain ⟨cl, hlen, hcorr, hchk, hfin⟩ := exists_claims_succ h hx hw hweft hdepth
    have hkl : (kleeneEval (WeftOne.claimInputs n cl)
        (WeftOne.overrideGates n cl gates)).getD w none = some b :=
      (WeftOne.getD_kleeneEval_overrideGates_eq h hx (fun c hc => (hcorr c hc).2)
        (hfin cl (.refl _) fun c hc => (hcorr c hc).2)).trans (congrArg some hv)
    refine ⟨cl, mem_certsSucc.2 ⟨hlen.trans (Nat.pow_le_pow_right (by decide) hdepth),
      fun c hc => (hcorr c hc).1, ?_⟩,
      WeftOne.checks_correct h hx fun c hc => (hcorr c hc).2⟩
    simp only [validCertSucc, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
    exact ⟨hkl, hchk⟩
  · rintro ⟨cl, hcl, hchecks⟩
    have hvalid := (mem_certsSucc.1 hcl).2.2
    simp only [validCertSucc, Bool.and_eq_true, decide_eq_true_eq] at hvalid
    exact eval_eq_of_kleeneEval_override h hvalid.1 hx hchecks

/-- **Weft-`(t + 1)` refutation duality.** A wire `w` of weft at most `t + 1` and depth at most `d`
takes value `b` on `x` if and only if every weft-`(t + 1)` certificate for `!b` has a failing check
on `x`. -/
theorem eval_eq_iff_forall_certsSucc_not {t d n : ℕ} {gates : List (Op × List ℕ)}
    (h : Program.IsCodeFrom signature n 0 gates) {x : List Bool} (hx : x.length = n)
    {w : ℕ} (hw : w < n + gates.length)
    (hweft : (evalCode (depthInterpretation (largeGateCost signature)) 0
      (List.replicate n 0) gates).getD w 0 ≤ t + 1)
    (hdepth : (evalCode (depthInterpretation (σ := signature) 1) 0
      (List.replicate n 0) gates).getD w 0 ≤ d)
    (b : Bool) :
    (evalCode interpretation false x gates).getD w false = b ↔
      ∀ cl ∈ certsSucc t d n gates w (!b),
        ∃ e ∈ cl.flatMap (WeftOne.claimChecks n gates),
          (evalCode interpretation false x gates).getD e.1 false = !e.2 := by
  have hnot := eval_eq_iff_exists_certsSucc h hx hw hweft hdepth (!b)
  have hbool : (evalCode interpretation false x gates).getD w false = b ↔
      ¬((evalCode interpretation false x gates).getD w false = !b) := by
    cases (evalCode interpretation false x gates).getD w false <;> cases b <;> decide
  rw [hbool, hnot]
  push Not
  refine forall_congr' fun cl => imp_congr_right fun _ => exists_congr fun e =>
    and_congr_right fun _ => ?_
  cases (evalCode interpretation false x gates).getD e.1 false <;> cases e.2 <;> decide

/-! ### Selected weight-`kk` inputs and bracket refutations -/

/-- The `BitString n` whose `1`-positions are `u 0, …, u (kk - 1)`. -/
def selectedBits (n kk : ℕ) (u : ℕ → ℕ) : BitString n :=
  fun i => decide (∃ j < kk, u j = i.1)

/-- Selecting `kk` strictly increasing positions below `n` yields Hamming weight `kk`. -/
theorem weight_selectedBits {n kk : ℕ} {u : ℕ → ℕ} (hu : StrictMonoOn u (Set.Iio kk))
    (hun : ∀ j < kk, u j < n) : BitString.weight (selectedBits n kk u) = kk := by
  classical
  have himg : (Finset.univ.filter fun i : Fin n => selectedBits n kk u i = true).map
      Fin.valEmbedding = (Finset.range kk).image u := by
    ext s
    simp only [selectedBits, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Fin.valEmbedding_apply, Finset.mem_image, Finset.mem_range, decide_eq_true_eq]
    constructor
    · rintro ⟨i, ⟨j, hj, hji⟩, rfl⟩
      exact ⟨j, hj, hji⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨⟨u j, hun j hj⟩, ⟨j, hj, rfl⟩, rfl⟩
  have hinj : Set.InjOn u ↑(Finset.range kk) := Finset.coe_range kk ▸ hu.injOn
  rw [BitString.weight, ← Finset.card_map Fin.valEmbedding, himg,
    Finset.card_image_of_injOn hinj, Finset.card_range]

/-- Every `x : BitString n` of weight `k` equals `selectedBits n k u` for a strictly increasing
enumeration `u` of its `1`-positions. -/
theorem exists_eq_selectedBits {n k : ℕ} (x : BitString n) (hk : BitString.weight x = k) :
    ∃ u : ℕ → ℕ, StrictMonoOn u (Set.Iio k) ∧ (∀ j < k, u j < n) ∧ x = selectedBits n k u := by
  classical
  set T : Finset ℕ := (Finset.univ.filter fun i : Fin n => x i = true).map Fin.valEmbedding
    with hTdef
  have hmemT : ∀ s, s ∈ T ↔ ∃ h : s < n, x ⟨s, h⟩ = true := by
    intro s
    simp only [hTdef, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Fin.valEmbedding_apply]
    exact ⟨fun ⟨i, hi, hval⟩ => hval ▸ ⟨i.2, hi⟩, fun ⟨hs, hx⟩ => ⟨⟨s, hs⟩, hx, rfl⟩⟩
  have hTcard : T.card = k := by
    rw [hTdef, Finset.card_map, ← hk]
    rfl
  let e := T.orderEmbOfFin hTcard
  let u : ℕ → ℕ := fun j => if hj : j < k then e ⟨j, hj⟩ else 0
  have hu : StrictMonoOn u (Set.Iio k) := by
    intro i hi j hj hij
    simp only [Set.mem_Iio] at hi hj
    simp only [u, hi, hj, dite_true]
    exact e.strictMono (Fin.mk_lt_mk.2 hij)
  have hTu : ∀ s, s ∈ T ↔ ∃ j < k, u j = s := by
    intro s
    constructor
    · intro hs
      obtain ⟨i, hi⟩ := (Finset.range_orderEmbOfFin T hTcard ▸ hs : s ∈ Set.range e)
      exact ⟨i.1, i.2, by simp only [u, i.2, dite_true, Fin.eta]; exact hi⟩
    · rintro ⟨j, hj, rfl⟩
      simp only [u, hj, dite_true]
      exact Finset.orderEmbOfFin_mem T hTcard _
  refine ⟨u, hu, fun j hj => ((hmemT (u j)).1 ((hTu (u j)).2 ⟨j, hj, rfl⟩)).1, ?_⟩
  funext i
  simp only [selectedBits, ← hTu, hmemT, Fin.eta, exists_prop_of_true i.2]
  cases x i <;> rfl

/-- Reading position `s < n` of `List.ofFn (selectedBits n kk u)`. -/
theorem getD_ofFn_selectedBits {n kk : ℕ} (u : ℕ → ℕ) {s : ℕ} (hs : s < n) :
    (List.ofFn (selectedBits n kk u)).getD s false = decide (∃ j < kk, u j = s) := by
  rw [List.getD_eq_getElem _ _ (by rwa [List.length_ofFn]), List.getElem_ofFn]
  rfl

/-- For a strictly increasing selection `u` on `[0, kk)` and any weft-`1` certificate
`cl ∈ certsOne d n gates w b`, all checks of `cl` hold on `selectedBits n kk u` if and only if no
true bracket `C.map (j, u j)` (`C ∈ indexLists d kk`) refutes `cl`. -/
theorem checks_selectedBits_iff_forall_not_refutes {d n kk : ℕ} {gates : List (Op × List ℕ)}
    (h : Program.IsCodeFrom signature n 0 gates) {u : ℕ → ℕ} (hu : StrictMonoOn u (Set.Iio kk))
    {w : ℕ} {b : Bool} {cl : List (ℕ × Bool)} (hcl : cl ∈ certsOne d n gates w b) :
    (∀ e ∈ cl.flatMap (WeftOne.claimChecks n gates),
      (evalCode interpretation false (List.ofFn (selectedBits n kk u)) gates).getD e.1 false =
        e.2) ↔
      ∀ C ∈ indexLists d kk, refutes n kk gates cl (C.map fun j => (j, u j)) = false := by
  constructor
  · intro hchecks C hC
    refine refutes_eq_false h (forall₂_knowList List.length_ofFn ?_) hchecks
    intro s hs b' hb'
    have hPu : ∀ p ∈ (C.map fun j => (j, u j)), p.1 < kk ∧ p.2 = u p.1 := by
      intro p hp
      obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hp
      exact ⟨(mem_indexLists.1 hC).2 j hj, rfl⟩
    rw [know_sound hu hPu hb', getD_ofFn_selectedBits u hs]
  · intro hnr e he
    have hvalid := (mem_certsOne.1 hcl).2.2
    simp only [validCertOne, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hvalid
    obtain ⟨S, hScard, hSlt, hSdet⟩ := WeftOne.exists_determining h (hvalid.2 e he) le_rfl
    obtain ⟨J, hJcard, hJlt, hJknow⟩ := exists_cover hu S
    have hJlen : J.toList.length ≤ 2 ^ (d + 1) := by
      rw [Finset.length_toList, pow_succ, mul_comm]
      exact hJcard.trans (Nat.mul_le_mul_left 2 hScard)
    have hJin : J.toList ∈ indexLists d kk :=
      mem_indexLists.2 ⟨hJlen, fun j hj => hJlt j (Finset.mem_toList.1 hj)⟩
    set P := J.toList.map fun j => (j, u j)
    have hPu : ∀ p ∈ P, p.1 < kk ∧ p.2 = u p.1 := by
      intro p hp
      obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hp
      exact ⟨hJlt j (Finset.mem_toList.1 hj), rfl⟩
    have hJP : ∀ j ∈ J, (j, u j) ∈ P := fun j hj =>
      List.mem_map.2 ⟨j, Finset.mem_toList.2 hj, rfl⟩
    have hdet := hSdet (List.ofFn (selectedBits n kk u)) (knowList n kk P) List.length_ofFn
        (length_knowList n kk P) fun s hs => by
      rw [getD_knowList P (hSlt s hs), getD_ofFn_selectedBits u (hSlt s hs)]
      obtain ⟨b', hb'⟩ := Option.ne_none_iff_exists'.1 (hJknow P hJP s hs)
      rw [hb', know_sound hu hPu hb']
    have hbad := hnr J.toList hJin
    rw [refutes, List.any_eq_false] at hbad
    have he_ok := hbad e he
    rw [hdet] at he_ok
    obtain ⟨ew, eb⟩ := e
    simp only at he_ok ⊢
    generalize (evalCode interpretation false (List.ofFn (selectedBits n kk u)) gates).getD
      ew false = v at he_ok ⊢
    cases v <;> cases eb <;> simp at he_ok ⊢

/-- **Weft-`1` bracket-refutation characterization.** On `selectedBits n kk u`, a wire `w` of weft
at most `1` and depth at most `d` evaluates to `b` if and only if every refuting weft-`1`
certificate `cl₁ ∈ certsOne d n gates w (!b)` is refuted by the true bracket of some index list
`C ∈ indexLists d kk`. -/
theorem eval_selectedBits_eq_iff_forall_certsOne_refutes {d n kk : ℕ}
    {gates : List (Op × List ℕ)} (h : Program.IsCodeFrom signature n 0 gates)
    {u : ℕ → ℕ} (hu : StrictMonoOn u (Set.Iio kk))
    {w : ℕ} (hw : w < n + gates.length)
    (hweft : (evalCode (depthInterpretation (largeGateCost signature)) 0
      (List.replicate n 0) gates).getD w 0 ≤ 1)
    (hdepth : (evalCode (depthInterpretation (σ := signature) 1) 0
      (List.replicate n 0) gates).getD w 0 ≤ d)
    (b : Bool) :
    (evalCode interpretation false (List.ofFn (selectedBits n kk u)) gates).getD w false = b ↔
      ∀ cl₁ ∈ certsOne d n gates w (!b),
        ∃ C ∈ indexLists d kk, refutes n kk gates cl₁ (C.map fun j => (j, u j)) = true := by
  rw [eval_eq_iff_forall_certsOne_not h List.length_ofFn hw hweft hdepth b]
  refine forall_congr' fun cl₁ => imp_congr_right fun hcl₁ => ?_
  have hiff := checks_selectedBits_iff_forall_not_refutes h hu hcl₁
  have hneg := not_congr hiff
  push Not at hneg
  refine (iff_congr ?_ ?_).mp hneg
  · refine exists_congr fun e => and_congr_right fun _ => ?_
    cases (evalCode interpretation false (List.ofFn (selectedBits n kk u)) gates).getD e.1 false <;>
      cases e.2 <;> decide
  · refine exists_congr fun C => and_congr_right fun _ => ?_
    cases refutes n kk gates cl₁ (C.map fun j => (j, u j)) <;> decide

/-! ### Polynomial-time computability -/

section PolyTime

variable {γ : Type} {encIn : γ ↪ List Bool}

/-- `cappedMax cap` is polynomial-time for every fixed `cap`. -/
theorem computableInPolyTime_cappedMax (cap : ℕ) :
    ComputableInPolyTime (cappedMax cap) (encList encUnary) encUnary := by
  induction cap with
  | zero => exact ComputableInPolyTime.const 0
  | succ cap ih =>
    have hdef : cappedMax (cap + 1) = fun l =>
        if l.any (fun v => decide (cap + 1 ≤ v)) then cap + 1 else cappedMax cap l := rfl
    rw [hdef]
    exact ComputableInPolyTime.ite' (by fun_prop) (ComputableInPolyTime.const (cap + 1)) ih

private theorem cappedDepthOp_le (d : ℕ) (op : Op) (l : List ℕ) :
    cappedDepthOp d op l ≤ d + 1 :=
  min_le_left _ _

private theorem cappedWeftOp_le (t : ℕ) (op : Op) (l : List ℕ) :
    cappedWeftOp t op l ≤ t + 1 :=
  min_le_left _ _

private theorem computableInPolyTime_cappedDepthOp (d : ℕ) :
    ComputableInPolyTime (fun l : List ℕ => cappedDepthOp d Op.not l)
      (encList encUnary) encUnary := by
  have hm := computableInPolyTime_cappedMax (d + 1)
  unfold cappedDepthOp
  fun_prop

private theorem computableInPolyTime_cappedWeftOp (t : ℕ) :
    ComputableInPolyTime (fun l : List ℕ => cappedWeftOp t Op.not l)
      (encList encUnary) encUnary := by
  have hm := computableInPolyTime_cappedMax (t + 1)
  unfold cappedWeftOp
  fun_prop

/-- `cappedDepths d` is polynomial-time for every fixed depth bound `d`. -/
theorem computableInPolyTime_cappedDepths (d : ℕ)
    {nf : γ → ℕ} {gf : γ → List (Op × List ℕ)}
    (hn : ComputableInPolyTime nf encIn encUnary)
    (hg : ComputableInPolyTime gf encIn (encList (Circuit.encGate encOp))) :
    ComputableInPolyTime (fun a => cappedDepths d (nf a) (gf a)) encIn (encList encUnary) := by
  have hstep : ComputableInPolyTime
      (fun p : List ℕ × (Op × List ℕ) =>
        p.1 ++ [cappedDepthOp d p.2.1 (p.2.2.map (p.1.getD · (d + 1)))])
      (encPair (encList encUnary) (Circuit.encGate encOp)) (encList encUnary) := by
    refine ComputableInPolyTime.listAppend' (by fun_prop)
      (ComputableInPolyTime.cons' ((computableInPolyTime_cappedDepthOp d).comp
        (ComputableInPolyTime.mapWithInput (by fun_prop) ?_)) (by fun_prop))
    exact ComputableInPolyTime.listGetD_binary (encA := encUnary) (encL := encList encUnary)
      (d + 1) (by fun_prop) (by fun_prop)
  unfold cappedDepths
  exact ComputableInPolyTime.foldl_of_bounded_growth hg
    (ComputableInPolyTime.replicate hn (ComputableInPolyTime.const 0)) hstep
    (growth := 2 * (d + 1) + 5) fun cd g => by
      have := cappedDepthOp_le d g.1 (g.2.map (cd.getD · (d + 1)))
      simp only [encList_append, List.length_append, encList_cons, encList_nil, List.append_nil,
        length_frame, encUnary_apply, List.length_replicate]
      omega

/-- `cappedWefts t` is polynomial-time for every fixed weft bound `t`. -/
theorem computableInPolyTime_cappedWefts (t : ℕ)
    {nf : γ → ℕ} {gf : γ → List (Op × List ℕ)}
    (hn : ComputableInPolyTime nf encIn encUnary)
    (hg : ComputableInPolyTime gf encIn (encList (Circuit.encGate encOp))) :
    ComputableInPolyTime (fun a => cappedWefts t (nf a) (gf a)) encIn (encList encUnary) := by
  have hstep : ComputableInPolyTime
      (fun p : List ℕ × (Op × List ℕ) =>
        p.1 ++ [cappedWeftOp t p.2.1 (p.2.2.map (p.1.getD · (t + 1)))])
      (encPair (encList encUnary) (Circuit.encGate encOp)) (encList encUnary) := by
    refine ComputableInPolyTime.listAppend' (by fun_prop)
      (ComputableInPolyTime.cons' ((computableInPolyTime_cappedWeftOp t).comp
        (ComputableInPolyTime.mapWithInput (by fun_prop) ?_)) (by fun_prop))
    exact ComputableInPolyTime.listGetD_binary (encA := encUnary) (encL := encList encUnary)
      (t + 1) (by fun_prop) (by fun_prop)
  unfold cappedWefts
  exact ComputableInPolyTime.foldl_of_bounded_growth hg
    (ComputableInPolyTime.replicate hn (ComputableInPolyTime.const 0)) hstep
    (growth := 2 * (t + 1) + 5) fun cw g => by
      have := cappedWeftOp_le t g.1 (g.2.map (cw.getD · (t + 1)))
      simp only [encList_append, List.length_append, encList_cons, encList_nil, List.append_nil,
        length_frame, encUnary_apply, List.length_replicate]
      omega

private def claimFlag' (op : Op) (b : Bool) : Bool :=
  !(op.toNat == 0) && ((op.toNat % 2 == 1) == b)

private theorem claimFlag'_eq (op : Op) (b : Bool) (g : List ℕ) :
    claimFlag' op b = decide (WeftOne.claimable (op, g) = some b) := by
  cases op <;> cases b <;> simp [claimFlag', WeftOne.claimable, Op.toNat, Nat.add_mod]

private theorem claimInput_eq' (claims : List (ℕ × Bool)) (i : ℕ) :
    WeftOne.claimInput claims i = if decide ((i, true) ∈ claims) then some true
      else if decide ((i, false) ∈ claims) then some false else none := by
  simp only [WeftOne.claimInput, decide_eq_true_eq]

private theorem computableInPolyTime_claimInputs'
    {nf : γ → ℕ} {cf : γ → List (ℕ × Bool)}
    (hn : ComputableInPolyTime nf encIn encUnary)
    (hc : ComputableInPolyTime cf encIn (encList (encPair encUnary encBool))) :
    ComputableInPolyTime (fun a => WeftOne.claimInputs (nf a) (cf a)) encIn
      (encList (encOption encBool)) := by
  refine ComputableInPolyTime.mapWithInput (by fun_prop) ?_
  simp only [claimInput_eq']
  polytime

private theorem computableInPolyTime_opNat' :
    ComputableInPolyTime (fun g : Op × List ℕ => g.1.toNat) (Circuit.encGate encOp) encUnary :=
  (ComputableInPolyTime.fst _ _).of_enc_eq fun _ => rfl

@[local fun_prop]
private theorem computableInPolyTime_claimFlag' {f : γ → Op × List ℕ} {b : γ → Bool}
    (hf : ComputableInPolyTime f encIn (Circuit.encGate encOp))
    (hb : ComputableInPolyTime b encIn encBool) :
    ComputableInPolyTime (fun a => claimFlag' (f a).1 (b a)) encIn encBool := by
  have hop := computableInPolyTime_opNat'.comp hf
  unfold claimFlag'
  polytime

private theorem overrideGate_eq' (n : ℕ) (claims : List (ℕ × Bool)) (g : Op × List ℕ) (j : ℕ) :
    WeftOne.overrideGate n claims g j =
      if claimFlag' g.1 true && decide ((n + j, true) ∈ claims) then (.and 0, [])
      else if claimFlag' g.1 false && decide ((n + j, false) ∈ claims) then (.or 0, [])
      else g := by
  simp only [WeftOne.overrideGate, claimFlag'_eq g.1 _ g.2, Bool.and_eq_true, decide_eq_true_eq]

private theorem computableInPolyTime_overrideGates'
    {nf : γ → ℕ} {gf : γ → List (Op × List ℕ)} {cf : γ → List (ℕ × Bool)}
    (hn : ComputableInPolyTime nf encIn encUnary)
    (hg : ComputableInPolyTime gf encIn (encList (Circuit.encGate encOp)))
    (hc : ComputableInPolyTime cf encIn (encList (encPair encUnary encBool))) :
    ComputableInPolyTime (fun a => WeftOne.overrideGates (nf a) (cf a) (gf a)) encIn
      (encList (Circuit.encGate encOp)) := by
  simp only [WeftOne.overrideGates, overrideGate_eq']
  polytime

private theorem computableInPolyTime_smallDepthOp' (d : ℕ) :
    ComputableInPolyTime (fun l : List ℕ => WeftOne.smallDepthOp d Op.not l)
      (encList encUnary) encUnary := by
  fun_prop [WeftOne.smallDepthOp, WeftOne.maxTwo]

private theorem smallDepthOp_le' (d : ℕ) (op : Op) (l : List ℕ) :
    WeftOne.smallDepthOp d op l ≤ d + 1 := by
  by_cases h : l.length ≤ 2 <;> simp [WeftOne.smallDepthOp, h]

private theorem computableInPolyTime_smallDepths' (d : ℕ)
    {nf : γ → ℕ} {gf : γ → List (Op × List ℕ)}
    (hn : ComputableInPolyTime nf encIn encUnary)
    (hg : ComputableInPolyTime gf encIn (encList (Circuit.encGate encOp))) :
    ComputableInPolyTime (fun a => WeftOne.smallDepths d (nf a) (gf a)) encIn
      (encList encUnary) := by
  have hstep : ComputableInPolyTime
      (fun p : List ℕ × (Op × List ℕ) =>
        p.1 ++ [WeftOne.smallDepthOp d p.2.1 (p.2.2.map (p.1.getD · (d + 1)))])
      (encPair (encList encUnary) (Circuit.encGate encOp)) (encList encUnary) := by
    refine ComputableInPolyTime.listAppend' (by fun_prop)
      (ComputableInPolyTime.cons' ((computableInPolyTime_smallDepthOp' d).comp
        (ComputableInPolyTime.mapWithInput (by fun_prop) ?_)) (by fun_prop))
    exact ComputableInPolyTime.listGetD_binary (encA := encUnary) (encL := encList encUnary)
      (d + 1) (by fun_prop) (by fun_prop)
  unfold WeftOne.smallDepths
  exact ComputableInPolyTime.foldl_of_bounded_growth hg
    (ComputableInPolyTime.replicate hn (ComputableInPolyTime.const 0)) hstep
    (growth := 2 * (d + 1) + 5) fun sd g => by
      have := smallDepthOp_le' d g.1 (g.2.map (sd.getD · (d + 1)))
      simp only [encList_append, List.length_append, encList_cons, encList_nil, List.append_nil,
        length_frame, encUnary_apply, List.length_replicate]
      omega

private theorem decide_eq_some_bool (v : Option Bool) (b : Bool) :
    decide (v = some b) = decide (v = if b then some true else some false) := by
  cases b <;> rfl

/-- `validCertOne d` is polynomial-time for every fixed depth bound `d`. -/
theorem computableInPolyTime_validCertOne (d : ℕ)
    {nf wf : γ → ℕ} {gf : γ → List (Op × List ℕ)} {bf : γ → Bool} {cf : γ → List (ℕ × Bool)}
    (hn : ComputableInPolyTime nf encIn encUnary)
    (hg : ComputableInPolyTime gf encIn (encList (Circuit.encGate encOp)))
    (hw : ComputableInPolyTime wf encIn encNat)
    (hb : ComputableInPolyTime bf encIn encBool)
    (hc : ComputableInPolyTime cf encIn (encList (encPair encUnary encBool))) :
    ComputableInPolyTime (fun a => validCertOne d (nf a) (gf a) (wf a) (bf a) (cf a))
      encIn encBool := by
  have hval := ComputableInPolyTime.listGetD_binary (encA := encOption encBool)
    (encL := encList (encOption encBool)) none
    (computableInPolyTime_kleeneEval (computableInPolyTime_claimInputs' hn hc)
      (computableInPolyTime_overrideGates' hn hg hc)) hw
  unfold validCertOne
  simp only [decide_eq_some_bool]
  refine ComputableInPolyTime.bool_and' (by polytime)
    (ComputableInPolyTime.allWithInput (WeftOne.computableInPolyTime_checks hn hg hc) ?_)
  exact ComputableInPolyTime.unary_le'
    (ComputableInPolyTime.listGetD_binary (encA := encUnary) (encL := encList encUnary) (d + 1)
      ((computableInPolyTime_smallDepths' d hn hg).comp (by fun_prop)) (by fun_prop))
    (by fun_prop)

/-- `validCertSucc t d` is polynomial-time for fixed weft bound `t` and depth bound `d`. -/
theorem computableInPolyTime_validCertSucc (t d : ℕ)
    {nf wf : γ → ℕ} {gf : γ → List (Op × List ℕ)} {bf : γ → Bool} {cf : γ → List (ℕ × Bool)}
    (hn : ComputableInPolyTime nf encIn encUnary)
    (hg : ComputableInPolyTime gf encIn (encList (Circuit.encGate encOp)))
    (hw : ComputableInPolyTime wf encIn encNat)
    (hb : ComputableInPolyTime bf encIn encBool)
    (hc : ComputableInPolyTime cf encIn (encList (encPair encUnary encBool))) :
    ComputableInPolyTime (fun a => validCertSucc t d (nf a) (gf a) (wf a) (bf a) (cf a))
      encIn encBool := by
  have hval := ComputableInPolyTime.listGetD_binary (encA := encOption encBool)
    (encL := encList (encOption encBool)) none
    (computableInPolyTime_kleeneEval (computableInPolyTime_claimInputs' hn hc)
      (computableInPolyTime_overrideGates' hn hg hc)) hw
  unfold validCertSucc
  simp only [decide_eq_some_bool]
  refine ComputableInPolyTime.bool_and' (by polytime)
    (ComputableInPolyTime.allWithInput (WeftOne.computableInPolyTime_checks hn hg hc) ?_)
  refine ComputableInPolyTime.bool_and' ?_ ?_
  · exact ComputableInPolyTime.unary_le'
      (ComputableInPolyTime.listGetD_binary (encA := encUnary) (encL := encList encUnary) (t + 1)
        ((computableInPolyTime_cappedWefts t hn hg).comp (by fun_prop)) (by fun_prop))
      (by fun_prop)
  · exact ComputableInPolyTime.unary_le'
      (ComputableInPolyTime.listGetD_binary (encA := encUnary) (encL := encList encUnary) (d + 1)
        ((computableInPolyTime_cappedDepths d hn hg).comp (by fun_prop)) (by fun_prop))
      (by fun_prop)

/-- Listing `claimUniverse` is polynomial-time. -/
theorem computableInPolyTime_claimUniverse_poly {n L : γ → ℕ}
    (hn : ComputableInPolyTime n encIn encUnary) (hL : ComputableInPolyTime L encIn encUnary) :
    ComputableInPolyTime (fun a => claimUniverse (n a) (L a)) encIn
      (encList (encPair encUnary encBool)) := by
  unfold claimUniverse
  fun_prop

/-- Listing `certsOne d` is polynomial-time for fixed depth `d`. -/
theorem computableInPolyTime_certsOne (d : ℕ)
    {nf wf : γ → ℕ} {gf : γ → List (Op × List ℕ)} {bf : γ → Bool}
    (hn : ComputableInPolyTime nf encIn encUnary)
    (hg : ComputableInPolyTime gf encIn (encList (Circuit.encGate encOp)))
    (hw : ComputableInPolyTime wf encIn encNat)
    (hb : ComputableInPolyTime bf encIn encBool) :
    ComputableInPolyTime (fun a => certsOne d (nf a) (gf a) (wf a) (bf a)) encIn
      (encList (encList (encPair encUnary encBool))) := by
  have hU := ComputableInPolyTime.listsUpTo
    (computableInPolyTime_claimUniverse_poly (L := fun a => (gf a).length) hn (by fun_prop)) (2 ^ d)
  unfold certsOne
  refine ComputableInPolyTime.filterWithInput hU ?_
  exact computableInPolyTime_validCertOne d
    (hn.comp (by fun_prop)) (hg.comp (by fun_prop)) (hw.comp (by fun_prop))
    (hb.comp (by fun_prop)) (by fun_prop)

/-- Listing `certsSucc t d` is polynomial-time for fixed weft `t` and depth `d`. -/
theorem computableInPolyTime_certsSucc (t d : ℕ)
    {nf wf : γ → ℕ} {gf : γ → List (Op × List ℕ)} {bf : γ → Bool}
    (hn : ComputableInPolyTime nf encIn encUnary)
    (hg : ComputableInPolyTime gf encIn (encList (Circuit.encGate encOp)))
    (hw : ComputableInPolyTime wf encIn encNat)
    (hb : ComputableInPolyTime bf encIn encBool) :
    ComputableInPolyTime (fun a => certsSucc t d (nf a) (gf a) (wf a) (bf a)) encIn
      (encList (encList (encPair encUnary encBool))) := by
  have hU := ComputableInPolyTime.listsUpTo
    (computableInPolyTime_claimUniverse_poly (L := fun a => (gf a).length) hn (by fun_prop)) (2 ^ d)
  unfold certsSucc
  refine ComputableInPolyTime.filterWithInput hU ?_
  exact computableInPolyTime_validCertSucc t d
    (hn.comp (by fun_prop)) (hg.comp (by fun_prop)) (hw.comp (by fun_prop))
    (hb.comp (by fun_prop)) (by fun_prop)

/-- Listing `brackets d` is polynomial-time for fixed depth `d`. -/
theorem computableInPolyTime_brackets_poly (d : ℕ) {n kk : γ → ℕ}
    (hn : ComputableInPolyTime n encIn encUnary) (hkk : ComputableInPolyTime kk encIn encUnary) :
    ComputableInPolyTime (fun a => brackets d (n a) (kk a)) encIn
      (encList (encList (encPair encUnary encUnary))) := by
  have hp : ComputableInPolyTime (fun a => pairs (n a) (kk a)) encIn
      (encList (encPair encUnary encUnary)) := by
    unfold pairs
    fun_prop
  exact ComputableInPolyTime.listsUpTo hp (2 ^ (d + 1))

/-- Listing `indexLists d` is polynomial-time for fixed depth `d`. -/
theorem computableInPolyTime_indexLists_poly (d : ℕ) {kk : γ → ℕ}
    (hkk : ComputableInPolyTime kk encIn encUnary) :
    ComputableInPolyTime (fun a => indexLists d (kk a)) encIn (encList (encList encUnary)) :=
  ComputableInPolyTime.listsUpTo (by fun_prop) (2 ^ (d + 1))

private theorem beq_some_not_eq' (v : Option Bool) (b : Bool) :
    (v == some (!b)) = decide (v = if b then some false else some true) := by
  cases b <;> exact Bool.beq_eq_decide_eq _ _

/-- Creating an all-`true` bit mask of unary-encoded length `n` is polynomial-time under `encBits`.
-/
@[fun_prop]
theorem computableInPolyTime_replicate_true {n : γ → ℕ}
    (hn : ComputableInPolyTime n encIn encUnary) :
    ComputableInPolyTime (fun a => List.replicate (n a) true) encIn encBits :=
  hn.of_enc_eq fun _ => rfl

attribute [local fun_prop] computableInPolyTime_know in
/-- `refutes` is polynomial-time. -/
theorem computableInPolyTime_refutes_poly {n kk : γ → ℕ}
    {gates : γ → List (Op × List ℕ)}
    {cl : γ → List (ℕ × Bool)} {P : γ → List (ℕ × ℕ)}
    (hn : ComputableInPolyTime n encIn encUnary) (hkk : ComputableInPolyTime kk encIn encUnary)
    (hg : ComputableInPolyTime gates encIn (encList (Circuit.encGate encOp)))
    (hcl : ComputableInPolyTime cl encIn (encList (encPair encUnary encBool)))
    (hP : ComputableInPolyTime P encIn (encList (encPair encUnary encUnary))) :
    ComputableInPolyTime (fun a => refutes (n a) (kk a) (gates a) (cl a) (P a)) encIn
      encBool := by
  have hknow : ComputableInPolyTime (fun a => knowList (n a) (kk a) (P a)) encIn
      (encList (encOption encBool)) := by
    polytime [knowList]
  unfold refutes
  simp only [beq_some_not_eq']
  refine ComputableInPolyTime.anyWithInput (WeftOne.computableInPolyTime_checks hn hg hcl) ?_
  have hval := ComputableInPolyTime.listGetD_binary
    (encIn := encPair encIn (encPair encNat encBool)) (encA := encOption encBool)
    (encL := encList (encOption encBool)) (i := fun p => p.2.1) none
    ((computableInPolyTime_kleeneEval hknow hg).comp (ComputableInPolyTime.fst _ _)) (by fun_prop)
  exact ComputableInPolyTime.decide_eq' hval
    (ComputableInPolyTime.ite'
      ((ComputableInPolyTime.snd _ _).comp (ComputableInPolyTime.snd _ _))
      (ComputableInPolyTime.const (some false))
      (ComputableInPolyTime.const (some true)))

end PolyTime

section Witnesses

private theorem weftCertificate_nondegenerate_example :
    ∃ (gates : List (Op × List ℕ)) (cl : List (ℕ × Bool)),
      Program.IsCodeFrom signature 3 0 gates ∧
      cl ∈ certsSucc 1 2 3 gates 4 true ∧
      (evalCode interpretation false [true, true, false] gates).getD 4 false = true := by
  let gates : List (Op × List ℕ) := [(.or 3, [0, 1, 2]), (.and 2, [0, 3])]
  have hcode : Program.IsCodeFrom signature 3 0 gates := by
    refine Program.isCodeFrom_of_getElem fun j hj => ?_
    rcases (show j = 0 ∨ j = 1 by simp [gates] at hj; omega) with rfl | rfl <;>
      simp [gates, signature]
  have heval : (evalCode interpretation false [true, true, false] gates).getD 4 false = true := by
    decide
  have hwft : (evalCode (depthInterpretation (largeGateCost signature)) 0
      (List.replicate 3 0) gates).getD 4 0 ≤ 2 := by
    decide
  have hdp : (evalCode (depthInterpretation (σ := signature) 1) 0
      (List.replicate 3 0) gates).getD 4 0 ≤ 2 := by
    decide
  obtain ⟨cl, hcl, -⟩ :=
    (eval_eq_iff_exists_certsSucc (t := 1) (d := 2) hcode (by decide) (by decide) hwft hdp true).1
      heval
  exact ⟨gates, cl, hcode, hcl, heval⟩

end Witnesses

end CslibFrontier.ParameterizedComplexity
