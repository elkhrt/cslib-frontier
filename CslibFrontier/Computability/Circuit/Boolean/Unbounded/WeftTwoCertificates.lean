/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Google LLC
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Parameterized.WHierarchy.Clique
import CslibFrontier.Computability.Circuit.Encoding.Layer
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Lists
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Length
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.ListsUpTo
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Eq
import CslibFrontier.Foundations.Data.List.Lookup
import CslibFrontier.Tactic.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Mathlib.Data.List.GetD

/-!
# Weft-2 Top-Level Claim Certificates and Negated Check Wires

Under standard Lean axioms, this module develops the polynomial-time claim-certificate machinery for
bounded-depth **weft-2** unbounded fan-in Boolean circuits (`Cslib.Circuits.Boolean.Unbounded`),
extending `Cslib.Circuits.Boolean.Unbounded.WeftOne`:

1. **Capped wire weft and depth propagation (`capWefts`, `capDepths`)**: polynomial-time forward
   evaluations computing `min 3 (weft w)` and `min (d + 1) (depth w)` on every wire `w`.
2. **Weft-2 top-level claim certificates (`weftTwoClaimsValid`, `weftTwoCerts`)**: lists of at most
   `2 ^ d` wire-value claims forcing the output wire to `some true` under Kleene three-valued
   evaluation while ensuring every check wire has weft `≤ 1` and depth `≤ d`.
3. **Negated check-wire extension (`gatesWithNeg`, `negWire`)**: appending one `NOT` gate per wire
   yields a circuit of depth `≤ d + 1` in which the negation of every weft-1 check wire `(w, b)`
   itself has weft `≤ 1` and depth `≤ d + 1`.

## Main definitions

* `Cslib.Complexity.capWefts`,
  `Cslib.Complexity.capDepths`: capped wire weft and depth lists.
* `Cslib.Complexity.weftTwoClaimsValid`,
  `Cslib.Complexity.weftTwoCerts`: weft-2 claim validity predicate and bounded
  certificate enumeration.
* `Cslib.Complexity.gatesWithNeg`,
  `Cslib.Complexity.negWire`: negated-wire gate extension and wire selector.

## Main results

* `Cslib.Complexity.getD_capWefts_eq_min`,
  `Cslib.Complexity.getD_capDepths_eq_min`: exact correspondence with `evalCode`
  wire wefts and depths.
* `Cslib.Complexity.eval_of_weftTwoClaimsValid`,
  `Cslib.Complexity.exists_weftTwoClaims`: soundness and completeness of weft-2
  claim certificates.
* `Cslib.Complexity.isCodeFrom_gatesWithNeg`,
  `Cslib.Complexity.getD_evalCode_negWire`,
  `Cslib.Complexity.weft_depth_negWire`: semantics and weft-1 / depth-`(d + 1)`
  bounds for negated check wires.
* `Cslib.Complexity.computableInPolyTime_weftTwoClaimsValid`,
  `Cslib.Complexity.computableInPolyTime_gatesWithNeg`: polynomial-time
  certificates.

## Tags

weft-2 circuit, W-hierarchy, Kleene evaluation, claim certificate, parameterized complexity
-/

public section

open Cslib.Complexity Cslib.Circuits Cslib.Circuits.Boolean Cslib.Circuits.Boolean.Unbounded
open Turing.MultiTapeTM ComputableInPolyTime

namespace Cslib.Complexity

/-! ### 1. Capped Wire Weft and Depth Lists -/

private def listMaxNat (l : List ℕ) : ℕ :=
  l.foldr max 0

private def capWeftStep (l : List ℕ) : ℕ :=
  min 3 (listMaxNat l + if decide (2 < l.length) then 1 else 0)

/-- Forward list of wire wefts capped at `3` for an `n`-input gate list `gates`. -/
def capWefts (n : ℕ) (gates : List (Unbounded.Op × List ℕ)) : List ℕ :=
  gates.foldl (fun wf g => wf ++ [capWeftStep (g.2.map (wf.getD · 3))])
    (List.replicate n 0)

private def capDepthStep (d : ℕ) (l : List ℕ) : ℕ :=
  min (d + 1) (listMaxNat l + 1)

/-- Forward list of wire depths capped at `d + 1` for an `n`-input gate list `gates`. -/
def capDepths (d n : ℕ) (gates : List (Unbounded.Op × List ℕ)) : List ℕ :=
  gates.foldl (fun dp g => dp ++ [capDepthStep d (g.2.map (dp.getD · (d + 1)))])
    (List.replicate n 0)

/-- Length of `capWefts n gates`. -/
theorem length_capWefts (n : ℕ) (gates : List (Unbounded.Op × List ℕ)) :
    (capWefts n gates).length = n + gates.length := by
  suffices ∀ s : List ℕ,
      (gates.foldl (fun wf g => wf ++ [capWeftStep (g.2.map (wf.getD · 3))]) s).length =
        s.length + gates.length by
    simpa only [capWefts, List.length_replicate] using this (List.replicate n 0)
  intro s
  induction gates generalizing s with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih, List.length_append, List.length_singleton, List.length_cons]
    omega

/-- Length of `capDepths d n gates`. -/
theorem length_capDepths (d n : ℕ) (gates : List (Unbounded.Op × List ℕ)) :
    (capDepths d n gates).length = n + gates.length := by
  suffices ∀ s : List ℕ,
      (gates.foldl (fun dp g => dp ++ [capDepthStep d (g.2.map (dp.getD · (d + 1)))]) s).length =
        s.length + gates.length by
    simpa only [capDepths, List.length_replicate] using this (List.replicate n 0)
  intro s
  induction gates generalizing s with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih, List.length_append, List.length_singleton, List.length_cons]
    omega

private lemma le_listMaxNat_of_mem {l : List ℕ} {x : ℕ} (hx : x ∈ l) : x ≤ listMaxNat l := by
  induction l with
  | nil => cases hx
  | cons y ys ih =>
    rw [listMaxNat, List.foldr_cons]
    rcases List.mem_cons.1 hx with rfl | hmem
    · exact le_max_left _ _
    · exact (ih hmem).trans (le_max_right _ _)

private lemma listMaxNat_le_of_forall {l : List ℕ} {b : ℕ} (h : ∀ x ∈ l, x ≤ b) :
    listMaxNat l ≤ b := by
  induction l with
  | nil => simp [listMaxNat]
  | cons y ys ih =>
    rw [listMaxNat, List.foldr_cons]
    exact max_le (h y (List.mem_cons_self ..)) (ih fun x hx => h x (List.mem_cons_of_mem _ hx))

private lemma listMaxNat_ofFn_eq_finset_sup {m : ℕ} (a : Fin m → ℕ) :
    listMaxNat (List.ofFn a) = Finset.univ.sup a :=
  le_antisymm
    (listMaxNat_le_of_forall fun x hx => by
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx
      exact Finset.le_sup (Finset.mem_univ i))
    (Finset.sup_le fun i _ => le_listMaxNat_of_mem (List.mem_ofFn.2 ⟨i, rfl⟩))

private lemma capWefts_eq_evalCode {n : ℕ} {gates : List (Unbounded.Op × List ℕ)}
    (h : Program.IsCodeFrom Unbounded.signature n 0 gates) :
    capWefts n gates =
      evalCode (σ := Unbounded.signature)
        (fun _ a => capWeftStep (List.ofFn a)) 3 (List.replicate n 0) gates :=
  foldl_eq_evalCode (σ := Unbounded.signature) (fun _ l => capWeftStep l) 3 _
    (length_eq_arity_of_isCodeFrom h)

private lemma capDepths_eq_evalCode (d : ℕ) {n : ℕ} {gates : List (Unbounded.Op × List ℕ)}
    (h : Program.IsCodeFrom Unbounded.signature n 0 gates) :
    capDepths d n gates =
      evalCode (σ := Unbounded.signature)
        (fun _ a => capDepthStep d (List.ofFn a)) (d + 1) (List.replicate n 0) gates :=
  foldl_eq_evalCode (σ := Unbounded.signature) (fun _ l => capDepthStep d l) (d + 1) _
    (length_eq_arity_of_isCodeFrom h)

private lemma gateElem_of_isCodeFrom {n : ℕ} {gates : List (Unbounded.Op × List ℕ)}
    (h : Program.IsCodeFrom Unbounded.signature n 0 gates) {j : ℕ} (hj : j < gates.length) :
    ∃ g, gates[j]? = some g ∧ g.2.length = Unbounded.signature.Arity g.1 ∧
      ∀ c ∈ g.2, c < n + j := by
  obtain ⟨hlen, hlt⟩ := h.getElem j hj
  exact ⟨gates[j], List.getElem?_eq_getElem hj, hlen, hlt⟩

/-- Each entry of `capWefts n gates` equals `min 3` of the exact wire weft. -/
theorem getD_capWefts_eq_min {n : ℕ} {gates : List (Unbounded.Op × List ℕ)}
    (h : Program.IsCodeFrom Unbounded.signature n 0 gates) {w : ℕ} (hw : w < n + gates.length) :
    (capWefts n gates).getD w 3 =
      min 3 ((evalCode (depthInterpretation (largeGateCost Unbounded.signature)) 0
        (List.replicate n 0) gates).getD w 0) := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    rcases Nat.lt_or_ge w n with hwn | hwn
    · rw [capWefts_eq_evalCode h, getD_evalCode_of_lt _ _ _ _ (by simpa using hwn),
        getD_evalCode_of_lt _ _ _ _ (by simpa using hwn)]
      simp [List.getD_eq_getElem?_getD, hwn]
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hwn
      obtain ⟨g, hg, hlen, hlt⟩ := gateElem_of_isCodeFrom h (by omega : j < gates.length)
      rw [capWefts_eq_evalCode h,
        getD_evalCode_eq_map (σ := Unbounded.signature) (fun _ l => capWeftStep l)
          (fun _ _ => rfl) 3 List.length_replicate h hg,
        ← capWefts_eq_evalCode h]
      have hmap_eq : g.2.map ((capWefts n gates).getD · 3) =
          g.2.map (fun c =>
            min 3 ((evalCode (depthInterpretation (largeGateCost Unbounded.signature))
              0 (List.replicate n 0) gates).getD c 0)) :=
        List.map_congr_left fun c hc => ih c (hlt c hc) (by have := hlt c hc; omega)
      rw [hmap_eq]
      have hsup : listMaxNat (g.2.map fun c =>
            min 3 ((evalCode (depthInterpretation (largeGateCost Unbounded.signature)) 0
              (List.replicate n 0) gates).getD c 0)) =
          min 3 (listMaxNat (g.2.map fun c =>
            (evalCode (depthInterpretation (largeGateCost Unbounded.signature)) 0
              (List.replicate n 0) gates).getD c 0)) := by
        generalize g.2 = cs
        induction cs with
        | nil => simp [listMaxNat]
        | cons c cs ihc =>
          simp only [List.map_cons, listMaxNat, List.foldr_cons] at ihc ⊢
          rw [ihc]
          omega
      have hdep' : (evalCode (depthInterpretation (largeGateCost Unbounded.signature)) 0
            (List.replicate n 0) gates).getD (n + j) 0 =
          listMaxNat (g.2.map fun c =>
            (evalCode (depthInterpretation (largeGateCost Unbounded.signature)) 0
              (List.replicate n 0) gates).getD c 0) +
            largeGateCost Unbounded.signature g.1 :=
        getD_evalCode_eq_map (σ := Unbounded.signature)
          (fun op l => listMaxNat l + largeGateCost Unbounded.signature op)
          (fun _ a => by
            rw [depthInterpretation, Fin.foldl_max_eq_max_sup, Nat.zero_max,
              listMaxNat_ofFn_eq_finset_sup])
          0 List.length_replicate h hg
      rw [hdep', capWeftStep, List.length_map, hsup]
      unfold largeGateCost
      rw [← hlen]
      simp only [decide_eq_true_eq]
      split_ifs <;> omega

/-- Each entry of `capDepths d n gates` equals `min (d + 1)` of the exact wire depth. -/
theorem getD_capDepths_eq_min (d : ℕ) {n : ℕ} {gates : List (Unbounded.Op × List ℕ)}
    (h : Program.IsCodeFrom Unbounded.signature n 0 gates) {w : ℕ} (hw : w < n + gates.length) :
    (capDepths d n gates).getD w (d + 1) =
      min (d + 1) ((evalCode (depthInterpretation (σ := Unbounded.signature) 1) 0
        (List.replicate n 0) gates).getD w 0) := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    rcases Nat.lt_or_ge w n with hwn | hwn
    · rw [capDepths_eq_evalCode d h, getD_evalCode_of_lt _ _ _ _ (by simpa using hwn),
        getD_evalCode_of_lt _ _ _ _ (by simpa using hwn)]
      simp [List.getD_eq_getElem?_getD, hwn]
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hwn
      obtain ⟨g, hg, hlen, hlt⟩ := gateElem_of_isCodeFrom h (by omega : j < gates.length)
      rw [capDepths_eq_evalCode d h,
        getD_evalCode_eq_map (σ := Unbounded.signature) (fun _ l => capDepthStep d l)
          (fun _ _ => rfl) (d + 1) List.length_replicate h hg,
        ← capDepths_eq_evalCode d h]
      have hmap_eq : g.2.map ((capDepths d n gates).getD · (d + 1)) =
          g.2.map (fun c =>
            min (d + 1) ((evalCode (depthInterpretation (σ := Unbounded.signature) 1)
              0 (List.replicate n 0) gates).getD c 0)) :=
        List.map_congr_left fun c hc => ih c (hlt c hc) (by have := hlt c hc; omega)
      rw [hmap_eq]
      have hsup : listMaxNat (g.2.map fun c =>
            min (d + 1) ((evalCode (depthInterpretation (σ := Unbounded.signature) 1) 0
              (List.replicate n 0) gates).getD c 0)) =
          min (d + 1) (listMaxNat (g.2.map fun c =>
            (evalCode (depthInterpretation (σ := Unbounded.signature) 1) 0
              (List.replicate n 0) gates).getD c 0)) := by
        generalize g.2 = cs
        induction cs with
        | nil => simp [listMaxNat]
        | cons c cs ihc =>
          simp only [List.map_cons, listMaxNat, List.foldr_cons] at ihc ⊢
          rw [ihc]
          omega
      have hdep' : (evalCode (depthInterpretation (σ := Unbounded.signature) 1) 0
            (List.replicate n 0) gates).getD (n + j) 0 =
          listMaxNat (g.2.map fun c =>
            (evalCode (depthInterpretation (σ := Unbounded.signature) 1) 0
              (List.replicate n 0) gates).getD c 0) + 1 :=
        getD_evalCode_eq_map (σ := Unbounded.signature)
          (fun _ l => listMaxNat l + 1)
          (fun _ a => by
            simp only [depthInterpretation, Pi.one_apply]
            rw [Fin.foldl_max_eq_max_sup, Nat.zero_max, listMaxNat_ofFn_eq_finset_sup])
          0 List.length_replicate h hg
      rw [hdep', capDepthStep, hsup]
      omega

/-! ### 2. Weft-2 Claim Certificates and Negated Check Wires -/

/-- Boolean test checking that `claims` forces output wire `o` to `some true` under Kleene
evaluation and that every induced check wire has weft `≤ 1` and depth `≤ d`. -/
@[expose] def weftTwoClaimsValid (d n : ℕ) (gates : List (Unbounded.Op × List ℕ)) (o : ℕ)
    (claims : List (ℕ × Bool)) : Bool :=
  decide ((kleeneEval (WeftOne.claimInputs n claims) (WeftOne.overrideGates n claims gates)).getD o
      none = some true) &&
    (claims.flatMap (WeftOne.claimChecks n gates)).all fun e =>
      decide ((capWefts n gates).getD e.1 3 ≤ 1) &&
      decide ((capDepths d n gates).getD e.1 (d + 1) ≤ d)

/-- All valid weft-2 claim lists of length at most `2 ^ d` for output wire `o`. -/
@[expose] def weftTwoCerts (d n : ℕ) (gates : List (Unbounded.Op × List ℕ)) (o : ℕ) :
    List (List (ℕ × Bool)) :=
  ((WCS.ToClique.claimUniverse n gates.length).listsUpTo (2 ^ d)).filter
    (weftTwoClaimsValid d n gates o)

/-- Membership characterization of `weftTwoCerts`. -/
theorem mem_weftTwoCerts {d n : ℕ} {gates : List (Unbounded.Op × List ℕ)} {o : ℕ}
    {cl : List (ℕ × Bool)} :
    cl ∈ weftTwoCerts d n gates o ↔
      cl.length ≤ 2 ^ d ∧ (∀ c ∈ cl, c.1 < n + gates.length) ∧
        weftTwoClaimsValid d n gates o cl = true := by
  simp only [weftTwoCerts, List.mem_filter, List.mem_listsUpTo, WCS.ToClique.mem_claimUniverse,
    and_assoc]

/-- Soundness of `weftTwoClaimsValid`: if every check wire in `claims` evaluates to its claimed
Boolean value on `x`, then output wire `o` evaluates to `true`. -/
theorem eval_of_weftTwoClaimsValid {d n : ℕ} {gates : List (Unbounded.Op × List ℕ)}
    (h : Program.IsCodeFrom Unbounded.signature n 0 gates) {o : ℕ} {claims : List (ℕ × Bool)}
    (hvalid : weftTwoClaimsValid d n gates o claims = true) {x : List Bool} (hx : x.length = n)
    (hchecks : ∀ e ∈ claims.flatMap (WeftOne.claimChecks n gates),
      (evalCode Unbounded.interpretation false x gates).getD e.1 false = e.2) :
    (evalCode Unbounded.interpretation false x gates).getD o false = true := by
  have hcl : ∀ c ∈ claims, (c.1 < n ∨ WeftOne.claimable (WeftOne.gateAt n gates c.1) = some c.2) →
      (evalCode Unbounded.interpretation false x gates).getD c.1 false = c.2 := by
    intro c hc hcases
    rcases Nat.lt_or_ge c.1 n with hlt | hge
    · exact hchecks c (List.mem_flatMap.2 ⟨c, hc, by simp [WeftOne.claimChecks, hlt]⟩)
    · obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le hge
      have hb := hcases.resolve_left hge.not_gt
      have hlt' : ¬n + j < n := by omega
      rcases hg : gates[j]? with _ | g
      · simp [WeftOne.gateAt, hj, List.getD_eq_getElem?_getD, hg, WeftOne.claimable] at hb
      rw [hj, WeftOne.gateAt_add hg] at hb
      rw [hj, WeftOne.getD_evalCode_eq_iff_of_claimable h hx hg hb]
      exact fun c' hc' => hchecks (c', c.2)
        (List.mem_flatMap.2 ⟨c, hc,
          by simp [WeftOne.claimChecks, hj, WeftOne.gateAt_add hg, hb, hlt', hc']⟩)
  simp only [weftTwoClaimsValid, Bool.and_eq_true, decide_eq_true_eq] at hvalid
  exact (approx_some.1 (hvalid.1 ▸ WeftOne.approx_override h hx hcl o)).symm

/-- Completeness of weft-2 claim lists: every wire `w` of weft `≤ 2` and depth `≤ d` admits a
consistent claim list of length at most `2 ^ depth(w)` whose check wires all have weft `≤ 1` and
depth `≤ d`. -/
theorem exists_weftTwoClaims {d n : ℕ} {gates : List (Unbounded.Op × List ℕ)}
    (h : Program.IsCodeFrom Unbounded.signature n 0 gates) {x : List Bool} (hx : x.length = n)
    {w : ℕ} (hw : w < n + gates.length)
    (hwd : (evalCode (depthInterpretation (largeGateCost Unbounded.signature)) 0
      (List.replicate n 0) gates).getD w 0 ≤ 2)
    (hdp : (evalCode (depthInterpretation (σ := Unbounded.signature) 1) 0
      (List.replicate n 0) gates).getD w 0 ≤ d) :
    ∃ cl : List (ℕ × Bool),
      cl.length ≤ 2 ^ (evalCode (depthInterpretation (σ := Unbounded.signature) 1) 0
        (List.replicate n 0) gates).getD w 0 ∧
      (∀ c ∈ cl, c.1 < n + gates.length ∧
        (evalCode Unbounded.interpretation false x gates).getD c.1 false = c.2) ∧
      (∀ e ∈ cl.flatMap (WeftOne.claimChecks n gates),
        (capWefts n gates).getD e.1 3 ≤ 1 ∧ (capDepths d n gates).getD e.1 (d + 1) ≤ d) ∧
      ∀ claims : List (ℕ × Bool), cl ⊆ claims →
        (∀ c ∈ claims, (evalCode Unbounded.interpretation false x gates).getD c.1 false = c.2) →
        (kleeneEval (WeftOne.claimInputs n claims) (WeftOne.overrideGates n claims gates)).getD w
          none ≠ none := by
  have hρ (claims : List (ℕ × Bool)) := WeftOne.length_claimInputs n claims
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    rcases Nat.lt_or_ge w n with hwn | hwn
    · refine ⟨[(w, (evalCode Unbounded.interpretation false x gates).getD w false)],
        by simpa using Nat.one_le_two_pow,
        fun c hc => List.mem_singleton.1 hc ▸ ⟨hw, rfl⟩,
        fun e he => ?_, fun claims hsub _ => ?_⟩
      · simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, WeftOne.claimChecks, hwn,
          ↓reduceIte, List.mem_singleton] at he
        subst he
        rw [getD_capWefts_eq_min h hw, getD_capDepths_eq_min d h hw,
          getD_evalCode_of_lt _ _ _ _ (by simpa using hwn),
          getD_evalCode_of_lt _ _ _ _ (by simpa using hwn)]
        simp [List.getD_eq_getElem?_getD, hwn]
      · have hmem := hsub (List.mem_singleton_self _)
        rw [getD_kleeneEval_of_lt _ _ (by rw [hρ]; exact hwn), WeftOne.getD_claimInputs _ hwn,
          WeftOne.claimInput]
        split_ifs <;> try exact Option.some_ne_none _
        cases hb : (evalCode Unbounded.interpretation false x gates).getD w false <;>
          rw [hb] at hmem <;> contradiction
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hwn
    obtain ⟨g, hg, hlen, hlt⟩ := gateElem_of_isCodeFrom h (by omega : j < gates.length)
    have hwdc : ∀ c ∈ g.2, (evalCode (depthInterpretation (largeGateCost Unbounded.signature)) 0
        (List.replicate n 0) gates).getD c 0 + largeGateCost Unbounded.signature g.1 ≤ 2 :=
      fun c hc => (getD_evalCode_depth_le _ h hg hc).trans hwd
    have hdpc : ∀ c ∈ g.2,
        (evalCode (depthInterpretation (σ := Unbounded.signature) 1) 0 (List.replicate n 0)
          gates).getD c 0 + 1 ≤
          (evalCode (depthInterpretation (σ := Unbounded.signature) 1) 0 (List.replicate n 0)
            gates).getD (n + j) 0 :=
      fun c hc => getD_evalCode_depth_le 1 h hg hc
    have hcw : ∀ c ∈ g.2, c < n + j := fun c hc => by have := hlt c hc; omega
    set v := evalCode Unbounded.interpretation false x gates
    by_cases hlarge : 2 < g.2.length
    · have hcost : largeGateCost Unbounded.signature g.1 = 1 := by
        unfold largeGateCost
        rw [← hlen]
        simp [hlarge]
      have hchk_bounds : ∀ c ∈ g.2,
          (capWefts n gates).getD c 3 ≤ 1 ∧ (capDepths d n gates).getD c (d + 1) ≤ d := by
        intro c hc
        have hc_lt : c < n + gates.length := by have := hcw c hc; omega
        rw [getD_capWefts_eq_min h hc_lt, getD_capDepths_eq_min d h hc_lt]
        have h1 := hwdc c hc
        have h2 := hdpc c hc
        omega
      obtain ⟨b0, hb0⟩ : ∃ b0, WeftOne.claimable g = some b0 := by
        obtain ⟨_ | _ | _, args⟩ := g
        · exact absurd (hlarge : 2 < args.length) (by rw [show args.length = 1 from hlen]; decide)
        all_goals exact ⟨_, rfl⟩
      by_cases hvb : v.getD (n + j) false = b0
      · refine ⟨[(n + j, b0)], by simpa using Nat.one_le_two_pow,
          fun c hc => List.mem_singleton.1 hc ▸ ⟨hw, hvb⟩,
          fun e he => ?_, fun claims hsub _ => ?_⟩
        · have hnj : ¬n + j < n := Nat.not_lt.2 (Nat.le_add_right n j)
          simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, WeftOne.claimChecks,
            hnj, WeftOne.gateAt_add hg, hb0, ↓reduceIte, List.mem_map] at he
          obtain ⟨c, hc, rfl⟩ := he
          exact hchk_bounds c hc
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
        rcases g with ⟨_ | m | m, args⟩
        · simp [WeftOne.claimable] at hb0
        · obtain rfl := Option.some.inj hb0
          rw [kleeneOp, kleeneAnd_of_mem (List.mem_map.2 ⟨c, hc, hκc.trans (congrArg some hvc)⟩)]
          exact Option.some_ne_none _
        · obtain rfl := Option.some.inj hb0
          rw [kleeneOp, kleeneOr_of_mem (List.mem_map.2 ⟨c, hc, hκc.trans (congrArg some hvc)⟩)]
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
            (WeftOne.overrideGates n claims gates)).getD c none =
              some (v.getD c false) := fun c hc =>
          WeftOne.getD_kleeneEval_overrideGates_eq h hx hcorr (hCL_fin c hc claims
            (fun c' hc' => hsub (List.mem_flatMap.2 ⟨c, hc, hc'⟩)) hcorr)
        rw [WeftOne.getD_kleeneEval_overrideGates h (hρ claims) claims hg]
        split_ifs <;> try exact Option.some_ne_none _
        have hmap : g.2.map (fun a => some (v.getD a false)) =
            (g.2.map (v.getD · false)).map some := List.map_map.symm
        rw [List.map_congr_left hkc, hmap]
        exact kleeneOp_map_some_ne_none g.1 (by rw [List.length_map]; exact hlen)

/-- Gate list obtained by appending a unary `NOT` gate for every wire
`0, …, n + gates.length - 1`. -/
@[expose] def gatesWithNeg (n : ℕ) (gates : List (Unbounded.Op × List ℕ)) :
    List (Unbounded.Op × List ℕ) :=
  gates ++ (List.range (n + gates.length)).map fun w => (Unbounded.Op.not, [w])

/-- Wire index in `gatesWithNeg n gates` evaluating to `!(val(e.1) == e.2)`. -/
@[expose] def negWire (n L : ℕ) (e : ℕ × Bool) : ℕ :=
  if e.2 then n + L + e.1 else e.1

/-- `gatesWithNeg n gates` is well-formed whenever `gates` is well-formed. -/
theorem isCodeFrom_gatesWithNeg {n : ℕ} {gates : List (Unbounded.Op × List ℕ)}
    (h : Program.IsCodeFrom Unbounded.signature n 0 gates) :
    Program.IsCodeFrom Unbounded.signature n 0 (gatesWithNeg n gates) := by
  rw [gatesWithNeg, Program.isCodeFrom_append]
  refine ⟨h, Program.isCodeFrom_of_forall (List.forall_mem_map.2 fun w hw => ⟨rfl, ?_⟩)⟩
  intro z hz
  rw [List.mem_singleton] at hz
  subst hz
  have hlt := List.mem_range.1 hw
  omega

private lemma evalCode_gatesWithNeg {n : ℕ} {gates : List (Unbounded.Op × List ℕ)}
    (x : List Bool) (hx : x.length = n) :
    evalCode Unbounded.interpretation false x (gatesWithNeg n gates) =
      let base := evalCode Unbounded.interpretation false x gates
      base ++ (List.range (n + gates.length)).map fun w => !(base.getD w false) := by
  rw [gatesWithNeg, evalCode_append, evalCode_layer]
  · simp [List.map_map, Unbounded.interpretation]
  · refine List.forall_mem_map.2 fun w hw z hz => ?_
    rw [List.mem_singleton] at hz
    subst hz
    rw [length_evalCode, hx]
    exact List.mem_range.1 hw

/-- Evaluation of `negWire n gates.length e` in `gatesWithNeg n gates`: evaluates to `true` iff
wire `e.1` does not equal `e.2`. -/
theorem getD_evalCode_negWire {n : ℕ} {gates : List (Unbounded.Op × List ℕ)}
    {x : List Bool} (hx : x.length = n) {e : ℕ × Bool} (he : e.1 < n + gates.length) :
    (evalCode Unbounded.interpretation false x (gatesWithNeg n gates)).getD
        (negWire n gates.length e) false =
      !(evalCode Unbounded.interpretation false x gates).getD e.1 false == e.2 := by
  rw [evalCode_gatesWithNeg x hx]
  dsimp only [negWire]
  have hbase_len : (evalCode Unbounded.interpretation false x gates).length = n + gates.length := by
    rw [length_evalCode, hx]
  cases hb : e.2
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [List.getD_append _ _ _ _ (by rw [hbase_len]; exact he)]
    cases (evalCode Unbounded.interpretation false x gates).getD e.1 false <;> rfl
  · simp only [↓reduceIte]
    rw [show n + gates.length + e.1 =
        (evalCode Unbounded.interpretation false x gates).length + e.1 by rw [hbase_len],
      List.getD_append_right _ _ _ _ (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
      List.getD_eq_getElem _ _ (by simpa using he), List.getElem_map, List.getElem_range]
    cases (evalCode Unbounded.interpretation false x gates).getD e.1 false <;> rfl

/-- If wire `e.1` has weft `≤ 1` and depth `≤ d` in `gates`, then `negWire n gates.length e` has
weft `≤ 1` and depth `≤ d + 1` in `gatesWithNeg n gates`. -/
theorem weft_depth_negWire {d n : ℕ} {gates : List (Unbounded.Op × List ℕ)}
    (h : Program.IsCodeFrom Unbounded.signature n 0 gates) {e : ℕ × Bool}
    (he_lt : e.1 < n + gates.length)
    (hweft : (evalCode (depthInterpretation (largeGateCost Unbounded.signature)) 0
      (List.replicate n 0) gates).getD e.1 0 ≤ 1)
    (hdepth : (evalCode (depthInterpretation (σ := Unbounded.signature) 1) 0
      (List.replicate n 0) gates).getD e.1 0 ≤ d) :
    negWire n gates.length e < n + (gatesWithNeg n gates).length ∧
      (evalCode (depthInterpretation (largeGateCost Unbounded.signature)) 0
        (List.replicate n 0) (gatesWithNeg n gates)).getD (negWire n gates.length e) 0 ≤ 1 ∧
      (evalCode (depthInterpretation (σ := Unbounded.signature) 1) 0
        (List.replicate n 0) (gatesWithNeg n gates)).getD (negWire n gates.length e) 0 ≤ d + 1 := by
  have hlen_ext : (gatesWithNeg n gates).length = gates.length + (n + gates.length) := by
    simp [gatesWithNeg]
  have hbase_w_len : (evalCode (depthInterpretation (largeGateCost Unbounded.signature)) 0
      (List.replicate n 0) gates).length = n + gates.length := by
    rw [length_evalCode, List.length_replicate]
  have hbase_d_len : (evalCode (depthInterpretation (σ := Unbounded.signature) 1) 0
      (List.replicate n 0) gates).length = n + gates.length := by
    rw [length_evalCode, List.length_replicate]
  have hpre_getD : ∀ (cost : Unbounded.signature.Op → ℕ) (w : ℕ), w < n + gates.length →
      (evalCode (depthInterpretation cost) 0 (List.replicate n 0)
        (gatesWithNeg n gates)).getD w 0 =
      (evalCode (depthInterpretation cost) 0 (List.replicate n 0) gates).getD w 0 := by
    intro cost w hw
    have hbl : (evalCode (depthInterpretation cost) 0 (List.replicate n 0) gates).length =
        n + gates.length := by rw [length_evalCode, List.length_replicate]
    rw [gatesWithNeg, evalCode_append, evalCode_layer]
    · exact List.getD_append _ _ _ _ (by rw [hbl]; exact hw)
    · refine List.forall_mem_map.2 fun u hu z hz => ?_
      rw [List.mem_singleton] at hz; subst hz; rw [hbl]; exact List.mem_range.1 hu
  dsimp only [negWire]
  cases e.2
  · simp only [Bool.false_eq_true, ↓reduceIte]
    refine ⟨by omega, ?_, ?_⟩
    · rw [hpre_getD _ _ he_lt]; exact hweft
    · rw [hpre_getD _ _ he_lt]; omega
  · simp only [↓reduceIte]
    refine ⟨by omega, ?_, ?_⟩
    · have hg_ext : (gatesWithNeg n gates)[gates.length + e.1]? =
          some (Unbounded.Op.not, [e.1]) := by
        simp only [gatesWithNeg]
        rw [List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
          List.getElem?_map, List.getElem?_range he_lt]
        rfl
      have hdm : (evalCode (depthInterpretation (largeGateCost Unbounded.signature)) 0
            (List.replicate n 0) (gatesWithNeg n gates)).getD (n + (gates.length + e.1)) 0 =
          listMaxNat ([e.1].map fun c =>
            (evalCode (depthInterpretation (largeGateCost Unbounded.signature)) 0
              (List.replicate n 0) (gatesWithNeg n gates)).getD c 0) +
            largeGateCost Unbounded.signature Unbounded.Op.not :=
        getD_evalCode_eq_map (σ := Unbounded.signature)
          (fun op l => listMaxNat l + largeGateCost Unbounded.signature op)
          (fun _ a => by
            rw [depthInterpretation, Fin.foldl_max_eq_max_sup, Nat.zero_max,
              listMaxNat_ofFn_eq_finset_sup])
          0 List.length_replicate (isCodeFrom_gatesWithNeg h) hg_ext
      rw [show n + gates.length + e.1 = n + (gates.length + e.1) by omega, hdm]
      simp only [List.map_singleton, listMaxNat, List.foldr_cons, List.foldr_nil, Nat.max_zero]
      have hcost0 : largeGateCost Unbounded.signature Unbounded.Op.not = 0 := by decide
      rw [hcost0, add_zero, hpre_getD _ _ he_lt]
      exact hweft
    · have hg_ext : (gatesWithNeg n gates)[gates.length + e.1]? =
          some (Unbounded.Op.not, [e.1]) := by
        simp only [gatesWithNeg]
        rw [List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
          List.getElem?_map, List.getElem?_range he_lt]
        rfl
      have hdm : (evalCode (depthInterpretation (σ := Unbounded.signature) 1) 0
            (List.replicate n 0) (gatesWithNeg n gates)).getD (n + (gates.length + e.1)) 0 =
          listMaxNat ([e.1].map fun c =>
            (evalCode (depthInterpretation (σ := Unbounded.signature) 1) 0
              (List.replicate n 0) (gatesWithNeg n gates)).getD c 0) + 1 :=
        getD_evalCode_eq_map (σ := Unbounded.signature)
          (fun _ l => listMaxNat l + 1)
          (fun _ a => by
            simp only [depthInterpretation, Pi.one_apply]
            rw [Fin.foldl_max_eq_max_sup, Nat.zero_max, listMaxNat_ofFn_eq_finset_sup])
          0 List.length_replicate (isCodeFrom_gatesWithNeg h) hg_ext
      rw [show n + gates.length + e.1 = n + (gates.length + e.1) by omega, hdm]
      simp only [List.map_singleton, listMaxNat, List.foldr_cons, List.foldr_nil, Nat.max_zero]
      rw [hpre_getD _ _ he_lt]
      omega

/-! ### 3. Polynomial-Time Certificates -/

private lemma computableInPolyTime_listMaxNat :
    ComputableInPolyTime listMaxNat (encList encUnary) encUnary := by
  have hrev : ComputableInPolyTime (List.reverse : List ℕ → List ℕ)
      (encList encUnary) (encList encUnary) := by fun_prop
  have hfold : ComputableInPolyTime (fun l : List ℕ => l.foldl max 0)
      (encList encUnary) encUnary := by
    refine ComputableInPolyTime.foldl' (encA := encUnary) (encB := encUnary)
      (list := fun l => l) (init := fun _ => 0) (step := max)
      ComputableInPolyTime.id' (const 0) (by fun_prop)
      (B := fun l => (encList encUnary l).length + 4)
      (PolyBounded.of_forall_le 5 1 fun l => by simp; omega) ?_
    intro l i _
    have hle : ((l.take i).foldl max 0) ≤ (encList encUnary l).length := by
      have hsub : List.Sublist (l.take i) l := List.take_sublist i l
      suffices ∀ xs : List ℕ, (∀ a ∈ xs, a ≤ (encList encUnary l).length) →
          xs.foldl max 0 ≤ (encList encUnary l).length by
        refine this (l.take i) fun a ha => ?_
        have hal := hsub.subset ha
        have hlen_elem := SizedListEncoding.length_elem_le (encA := encUnary)
          (encL := encList encUnary) l a hal
        simpa using hlen_elem
      intro xs
      suffices ∀ (acc : ℕ), acc ≤ (encList encUnary l).length →
          (∀ a ∈ xs, a ≤ (encList encUnary l).length) →
          xs.foldl max acc ≤ (encList encUnary l).length from
        this 0 (Nat.zero_le _)
      induction xs with
      | nil => intro acc hacc _; exact hacc
      | cons y ys ihy =>
        intro acc hacc hall
        exact ihy (max acc y) (max_le hacc (hall y (List.mem_cons_self ..)))
          fun z hz => hall z (List.mem_cons_of_mem _ hz)
    simpa only [encUnary_apply, List.length_replicate] using hle.trans (Nat.le_add_right _ 4)
  have heq : listMaxNat = fun l : List ℕ => l.reverse.foldl max 0 := by
    funext l
    rw [listMaxNat, ← List.foldl_reverse]
    congr 1
    funext a b
    exact max_comm b a
  rw [heq]
  exact hfold.comp hrev

private lemma computableInPolyTime_capWefts {γ : Type} {encIn : γ ↪ List Bool}
    {nf : γ → ℕ} {gf : γ → List (Unbounded.Op × List ℕ)}
    (hn : ComputableInPolyTime nf encIn encUnary)
    (hg : ComputableInPolyTime gf encIn (encList (Circuit.encGate Unbounded.encOp))) :
    ComputableInPolyTime (fun a => capWefts (nf a) (gf a)) encIn (encList encUnary) := by
  have hstepOp : ComputableInPolyTime capWeftStep (encList encUnary) encUnary := by
    unfold capWeftStep
    have hm := computableInPolyTime_listMaxNat
    have hgt2 : ComputableInPolyTime (fun l : List ℕ => decide (2 < l.length))
        (encList encUnary) encBool := unary_lt' (const 2) (length_list encUnary)
    have hinc : ComputableInPolyTime
        (fun l : List ℕ => if decide (2 < l.length) then 1 else 0)
        (encList encUnary) encUnary := hgt2.ite (const 1) (const 0)
    exact unary_min.comp ((const 3).prod (unary_add' hm hinc))
  have hstep : ComputableInPolyTime
      (fun p : List ℕ × (Unbounded.Op × List ℕ) =>
        p.1 ++ [capWeftStep (p.2.2.map (p.1.getD · 3))])
      (encPair (encList encUnary) (Circuit.encGate Unbounded.encOp)) (encList encUnary) := by
    refine listAppend' (fst _ _) (cons' (hstepOp.comp (mapWithInput (by fun_prop) ?_)) (const []))
    exact listGetD_binary (encA := encUnary) (encL := encList encUnary) 3 (by fun_prop)
      (by fun_prop)
  unfold capWefts
  exact foldl_of_bounded_growth (encA := Circuit.encGate Unbounded.encOp)
    (encL := encList (Circuit.encGate Unbounded.encOp))
    hg (replicate hn (const 0)) hstep (growth := 11) fun wf g => by
    have hle : capWeftStep (g.2.map (wf.getD · 3)) ≤ 3 := min_le_left _ _
    simp only [encList_append, List.length_append, encList_cons, encList_nil, List.append_nil,
      length_frame, encUnary_apply, List.length_replicate]
    omega

private lemma computableInPolyTime_capDepths (d : ℕ) {γ : Type} {encIn : γ ↪ List Bool}
    {nf : γ → ℕ} {gf : γ → List (Unbounded.Op × List ℕ)}
    (hn : ComputableInPolyTime nf encIn encUnary)
    (hg : ComputableInPolyTime gf encIn (encList (Circuit.encGate Unbounded.encOp))) :
    ComputableInPolyTime (fun a => capDepths d (nf a) (gf a)) encIn (encList encUnary) := by
  have hstepOp : ComputableInPolyTime (capDepthStep d) (encList encUnary) encUnary := by
    unfold capDepthStep
    exact unary_min.comp ((const (d + 1)).prod
      (unary_add' computableInPolyTime_listMaxNat (const 1)))
  have hstep : ComputableInPolyTime
      (fun p : List ℕ × (Unbounded.Op × List ℕ) =>
        p.1 ++ [capDepthStep d (p.2.2.map (p.1.getD · (d + 1)))])
      (encPair (encList encUnary) (Circuit.encGate Unbounded.encOp)) (encList encUnary) := by
    refine listAppend' (fst _ _) (cons' (hstepOp.comp (mapWithInput (by fun_prop) ?_)) (const []))
    exact listGetD_binary (encA := encUnary) (encL := encList encUnary) (d + 1) (by fun_prop)
      (by fun_prop)
  unfold capDepths
  exact foldl_of_bounded_growth (encA := Circuit.encGate Unbounded.encOp)
    (encL := encList (Circuit.encGate Unbounded.encOp))
    hg (replicate hn (const 0)) hstep
    (growth := 2 * (d + 1) + 5) fun dp g => by
      have hle : capDepthStep d (g.2.map (dp.getD · (d + 1))) ≤ d + 1 := min_le_left _ _
      simp only [encList_append, List.length_append, encList_cons, encList_nil, List.append_nil,
        length_frame, encUnary_apply, List.length_replicate]
      omega

private lemma claimInput_eq_w2 (claims : List (ℕ × Bool)) (i : ℕ) :
    WeftOne.claimInput claims i = if decide ((i, true) ∈ claims) then some true
      else if decide ((i, false) ∈ claims) then some false else none := by
  simp only [WeftOne.claimInput, decide_eq_true_eq]

private def claimFlagW2 (op : Unbounded.Op) (b : Bool) : Bool :=
  !(op.toNat == 0) && ((op.toNat % 2 == 1) == b)

private lemma claimFlagW2_eq (op : Unbounded.Op) (b : Bool) (g : List ℕ) :
    claimFlagW2 op b = decide (WeftOne.claimable (op, g) = some b) := by
  cases op <;> cases b <;> simp [claimFlagW2, WeftOne.claimable, Unbounded.Op.toNat, Nat.add_mod]

private lemma overrideGate_eq_w2 (n : ℕ) (claims : List (ℕ × Bool)) (g : Unbounded.Op × List ℕ)
    (j : ℕ) :
    WeftOne.overrideGate n claims g j =
      if claimFlagW2 g.1 true && decide ((n + j, true) ∈ claims) then (.and 0, [])
      else if claimFlagW2 g.1 false && decide ((n + j, false) ∈ claims) then (.or 0, [])
      else g := by
  simp only [WeftOne.overrideGate, claimFlagW2_eq g.1 _ g.2, Bool.and_eq_true, decide_eq_true_eq]

/-- Polynomial-time certificate for `weftTwoClaimsValid`. -/
theorem computableInPolyTime_weftTwoClaimsValid (d : ℕ) {γ : Type} {encIn : γ ↪ List Bool}
    {nf : γ → ℕ} {gf : γ → List (Unbounded.Op × List ℕ)} {of : γ → ℕ}
    {cf : γ → List (ℕ × Bool)}
    (hn : ComputableInPolyTime nf encIn encUnary)
    (hg : ComputableInPolyTime gf encIn (encList (Circuit.encGate Unbounded.encOp)))
    (ho : ComputableInPolyTime of encIn encNat)
    (hc : ComputableInPolyTime cf encIn WCS.ToClique.encClaimList) :
    ComputableInPolyTime (fun a => weftTwoClaimsValid d (nf a) (gf a) (of a) (cf a))
      encIn encBool := by
  have hclIn : ComputableInPolyTime (fun a => WeftOne.claimInputs (nf a) (cf a))
      encIn (encList (encOption encBool)) := by
    unfold WeftOne.claimInputs
    refine mapWithInput (range.comp hn) ?_
    simp only [claimInput_eq_w2]
    have hi : ComputableInPolyTime (fun p : γ × ℕ => p.2) (encPair encIn encUnary) encUnary :=
      snd _ _
    have hc' := hc.comp (fst encIn encUnary)
    have hmT : ComputableInPolyTime (fun p : γ × ℕ => decide ((p.2, true) ∈ cf p.1))
        (encPair encIn encUnary) encBool :=
      (by fun_prop : ComputableInPolyTime
        (fun r : (ℕ × Bool) × List (ℕ × Bool) => decide (r.1 ∈ r.2))
        (encPair (encPair encUnary encBool) WCS.ToClique.encClaimList) encBool).comp
        ((hi.prod (const true)).prod hc')
    have hmF : ComputableInPolyTime (fun p : γ × ℕ => decide ((p.2, false) ∈ cf p.1))
        (encPair encIn encUnary) encBool :=
      (by fun_prop : ComputableInPolyTime
        (fun r : (ℕ × Bool) × List (ℕ × Bool) => decide (r.1 ∈ r.2))
        (encPair (encPair encUnary encBool) WCS.ToClique.encClaimList) encBool).comp
        ((hi.prod (const false)).prod hc')
    exact hmT.ite (const (some true)) (hmF.ite (const (some false)) (const none))
  have hovG : ComputableInPolyTime (fun a => WeftOne.overrideGates (nf a) (cf a) (gf a))
      encIn (encList (Circuit.encGate Unbounded.encOp)) := by
    simp only [WeftOne.overrideGates, overrideGate_eq_w2]
    have hz := (zipIdx (Circuit.encGate Unbounded.encOp)).comp hg
    refine mapWithInput hz ?_
    let E := encPair encIn (encPair (Circuit.encGate Unbounded.encOp) encUnary)
    have hopNat : ComputableInPolyTime
        (fun p : γ × ((Unbounded.Op × List ℕ) × ℕ) => p.2.1.1.toNat) E encUnary :=
      ((fst _ _).comp ((fst _ _).comp (snd _ _))).of_enc_eq fun _ => rfl
    have hflT : ComputableInPolyTime
        (fun p : γ × ((Unbounded.Op × List ℕ) × ℕ) => claimFlagW2 p.2.1.1 true) E encBool := by
      unfold claimFlagW2
      polytime
    have hflF : ComputableInPolyTime
        (fun p : γ × ((Unbounded.Op × List ℕ) × ℕ) => claimFlagW2 p.2.1.1 false) E encBool := by
      unfold claimFlagW2
      polytime
    have hnj : ComputableInPolyTime
        (fun p : γ × ((Unbounded.Op × List ℕ) × ℕ) => nf p.1 + p.2.2) E encUnary := by
      have hn1 := hn.comp (fst encIn (encPair (Circuit.encGate Unbounded.encOp) encUnary))
      have hj1 : ComputableInPolyTime (fun p : γ × ((Unbounded.Op × List ℕ) × ℕ) => p.2.2)
          E encUnary := (snd _ _).comp (snd _ _)
      fun_prop
    have hc1 := hc.comp (fst encIn (encPair (Circuit.encGate Unbounded.encOp) encUnary))
    have hmT : ComputableInPolyTime
        (fun p : γ × ((Unbounded.Op × List ℕ) × ℕ) => decide ((nf p.1 + p.2.2, true) ∈ cf p.1))
        E encBool :=
      (by fun_prop : ComputableInPolyTime
        (fun r : (ℕ × Bool) × List (ℕ × Bool) => decide (r.1 ∈ r.2))
        (encPair (encPair encUnary encBool) WCS.ToClique.encClaimList) encBool).comp
        ((hnj.prod (const true)).prod hc1)
    have hmF : ComputableInPolyTime
        (fun p : γ × ((Unbounded.Op × List ℕ) × ℕ) => decide ((nf p.1 + p.2.2, false) ∈ cf p.1))
        E encBool :=
      (by fun_prop : ComputableInPolyTime
        (fun r : (ℕ × Bool) × List (ℕ × Bool) => decide (r.1 ∈ r.2))
        (encPair (encPair encUnary encBool) WCS.ToClique.encClaimList) encBool).comp
        ((hnj.prod (const false)).prod hc1)
    have hg_orig : ComputableInPolyTime
        (fun p : γ × ((Unbounded.Op × List ℕ) × ℕ) => p.2.1)
        E (Circuit.encGate Unbounded.encOp) := (fst _ _).comp (snd _ _)
    exact (bool_and' hflT hmT).ite (const ((Unbounded.Op.and 0, []) : Unbounded.Op × List ℕ))
      ((bool_and' hflF hmF).ite (const ((Unbounded.Op.or 0, []) : Unbounded.Op × List ℕ))
        hg_orig)
  have hkl := listGetD_binary (encA := encOption encBool) (encL := encList (encOption encBool)) none
    (computableInPolyTime_kleeneEval hclIn hovG) ho
  have hok1 : ComputableInPolyTime
      (fun a => decide ((kleeneEval (WeftOne.claimInputs (nf a) (cf a))
        (WeftOne.overrideGates (nf a) (cf a) (gf a))).getD (of a) none = some true))
      encIn encBool := by
    have heq_opt : ComputableInPolyTime (fun opt : Option Bool => decide (opt = some true))
        (encOption encBool) encBool := by fun_prop
    exact heq_opt.comp hkl
  have hchks := WeftOne.computableInPolyTime_checks hn hg hc
  have hcw := computableInPolyTime_capWefts hn hg
  have hcd := computableInPolyTime_capDepths d hn hg
  have hok2 : ComputableInPolyTime
      (fun a => ((cf a).flatMap (WeftOne.claimChecks (nf a) (gf a))).all fun e =>
        decide ((capWefts (nf a) (gf a)).getD e.1 3 ≤ 1) &&
        decide ((capDepths d (nf a) (gf a)).getD e.1 (d + 1) ≤ d))
      encIn encBool := by
    refine allWithInput hchks ?_
    have he1 : ComputableInPolyTime (fun p : γ × (ℕ × Bool) => p.2.1)
        (encPair encIn (encPair encNat encBool)) encNat := (fst _ _).comp (snd _ _)
    have hgw := listGetD_binary (encA := encUnary) (encL := encList encUnary) 3
      (hcw.comp (fst _ _)) he1
    have hgd := listGetD_binary (encA := encUnary) (encL := encList encUnary) (d + 1)
      (hcd.comp (fst _ _)) he1
    exact (bool_and' ((unary_le' hgw (const 1))) ((unary_le' hgd (const d))))
  unfold weftTwoClaimsValid
  exact (bool_and' (hok1) (hok2))

/-- Polynomial-time certificate for `gatesWithNeg`. -/
theorem computableInPolyTime_gatesWithNeg {γ : Type} {encIn : γ ↪ List Bool}
    {nf : γ → ℕ} {gf : γ → List (Unbounded.Op × List ℕ)}
    (hn : ComputableInPolyTime nf encIn encUnary)
    (hg : ComputableInPolyTime gf encIn (encList (Circuit.encGate Unbounded.encOp))) :
    ComputableInPolyTime (fun a => gatesWithNeg (nf a) (gf a))
      encIn (encList (Circuit.encGate Unbounded.encOp)) := by
  have htot : ComputableInPolyTime (fun a => nf a + (gf a).length) encIn encUnary := by
    have hgl := (length_list (Circuit.encGate Unbounded.encOp)).comp hg
    fun_prop
  have hnots : ComputableInPolyTime
      (fun a => (List.range (nf a + (gf a).length)).map fun w =>
        ((Unbounded.Op.not, [w]) : Unbounded.Op × List ℕ))
      encIn (encList (Circuit.encGate Unbounded.encOp)) := by
    refine mapWithInput (range.comp htot) ?_
    have hw := unary_to_binary.comp (snd encIn encUnary)
    exact (const Unbounded.Op.not).prod (cons' hw (const []))
  unfold gatesWithNeg
  exact listAppend' hg hnots

@[simp]
theorem negWire_true (n L w : ℕ) : negWire n L (w, true) = n + L + w := rfl

@[simp]
theorem negWire_false (n L w : ℕ) : negWire n L (w, false) = w := rfl

/-- Characterization of `weftTwoClaimsValid = true`. -/
theorem weftTwoClaimsValid_eq_true_iff {d n : ℕ} {gates : List (Unbounded.Op × List ℕ)}
    {o : ℕ} {claims : List (ℕ × Bool)} :
    weftTwoClaimsValid d n gates o claims = true ↔
      (kleeneEval (WeftOne.claimInputs n claims) (WeftOne.overrideGates n claims gates)).getD o
        none = some true ∧
      ∀ e ∈ claims.flatMap (WeftOne.claimChecks n gates),
        (capWefts n gates).getD e.1 3 ≤ 1 ∧ (capDepths d n gates).getD e.1 (d + 1) ≤ d := by
  simp only [weftTwoClaimsValid, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]

/-- Polynomial-time certificate for `weftTwoCerts`. -/
theorem computableInPolyTime_weftTwoCerts (d : ℕ) {γ : Type} {encIn : γ ↪ List Bool}
    {nf : γ → ℕ} {gf : γ → List (Unbounded.Op × List ℕ)} {of : γ → ℕ}
    (hn : ComputableInPolyTime nf encIn encUnary)
    (hg : ComputableInPolyTime gf encIn (encList (Circuit.encGate Unbounded.encOp)))
    (ho : ComputableInPolyTime of encIn encNat) :
    ComputableInPolyTime (fun a => weftTwoCerts d (nf a) (gf a) (of a))
      encIn (encList WCS.ToClique.encClaimList) := by
  have hclU : ComputableInPolyTime
      (fun a => WCS.ToClique.claimUniverse (nf a) (gf a).length)
      encIn WCS.ToClique.encClaimList := by
    have hgl := (length_list (Circuit.encGate Unbounded.encOp)).comp hg
    unfold WCS.ToClique.claimUniverse
    fun_prop
  unfold weftTwoCerts
  refine filterWithInput (listsUpTo hclU (2 ^ d)) ?_
  exact computableInPolyTime_weftTwoClaimsValid d (hn.comp (fst _ _)) (hg.comp (fst _ _))
    (ho.comp (fst _ _)) (snd _ _)

/-- Polynomial-time certificate for `negWire`. -/
theorem computableInPolyTime_negWire {γ : Type} {encIn : γ ↪ List Bool}
    {nf lf : γ → ℕ} {ef : γ → ℕ × Bool}
    (hn : ComputableInPolyTime nf encIn encNat)
    (hl : ComputableInPolyTime lf encIn encNat)
    (he : ComputableInPolyTime ef encIn (encPair encNat encBool)) :
    ComputableInPolyTime (fun a => negWire (nf a) (lf a) (ef a)) encIn encNat := by
  unfold negWire
  have hb : ComputableInPolyTime (fun a => (ef a).2) encIn encBool := (snd _ _).comp he
  have he1 : ComputableInPolyTime (fun a => (ef a).1) encIn encNat := (fst _ _).comp he
  exact hb.ite (by fun_prop) he1

end Cslib.Complexity
