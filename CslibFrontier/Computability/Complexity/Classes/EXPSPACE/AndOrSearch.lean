/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.EXPSPACE
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.Recursion
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Sum

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolySpace.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.NatLength
import CslibFrontier.Tactic.EncLen
import Mathlib.Data.List.GetD
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Bounded-Depth AND-OR Tree Search in `DSPACE` and `EXPSPACE`

General stack-recursive evaluator (`Turing.MultiTapeTM.ComputableInSpace.recWith`) for bounded-depth
AND-OR derivation search (unary and binary rules) with polynomial-time leaf and rule-generation
oracles. When the depth bound, reachable node encoding size, and rule-list length are all
bounded by `2 ^ h n` for a polynomially bounded `h`, the search language lies in
`Cslib.Complexity.EXPSPACE`.
-/

public section

namespace Cslib.Complexity

open Cslib Cslib.Complexity Turing Turing.MultiTapeTM

section AndOr

variable {α ν : Type}

/-- Bounded-depth AND-OR provability: `v` is provable within depth `d` iff either `isAxiom v` or
`d = d' + 1` and some rule `(v₁, ov₂) ∈ rules v` has `v₁` (and `v₂` when `ov₂ = some v₂`)
provable within depth `d'`. -/
@[expose] def AndOrProvable (isAxiom : ν → Bool) (rules : ν → List (ν × Option ν)) :
    ℕ → ν → Bool
  | 0, v => isAxiom v
  | d + 1, v =>
      isAxiom v || (rules v).any fun r ↦
        AndOrProvable isAxiom rules d r.1 &&
          match r.2 with
          | none => true
          | some v₂ => AndOrProvable isAxiom rules d v₂

@[simp] lemma AndOrProvable_zero (isAxiom : ν → Bool) (rules : ν → List (ν × Option ν)) (v : ν) :
    AndOrProvable isAxiom rules 0 v = isAxiom v := rfl

lemma AndOrProvable_succ (isAxiom : ν → Bool) (rules : ν → List (ν × Option ν)) (d : ℕ) (v : ν) :
    AndOrProvable isAxiom rules (d + 1) v =
      (isAxiom v || (rules v).any fun r ↦
        AndOrProvable isAxiom rules d r.1 &&
          match r.2 with
          | none => true
          | some v₂ => AndOrProvable isAxiom rules d v₂) := rfl

/-- Reachability of `(d', v)` at remaining depth `d'` along a derivation search from `(d, v₀)`. -/
inductive AndOrNodeReach (rules : ν → List (ν × Option ν)) : ℕ → ν → ℕ → ν → Prop where
  /-- Root node at full depth `d`. -/
  | refl (d : ℕ) (v : ν) : AndOrNodeReach rules d v d v
  /-- First premise of an applicable rule. -/
  | left {d d' : ℕ} {v₀ v w : ν} {r : ν × Option ν} :
      AndOrNodeReach rules d v₀ (d' + 1) v → r ∈ rules v → r.1 = w →
      AndOrNodeReach rules d v₀ d' w
  /-- Second premise of an applicable binary rule. -/
  | right {d d' : ℕ} {v₀ v w : ν} {r : ν × Option ν} :
      AndOrNodeReach rules d v₀ (d' + 1) v → r ∈ rules v → r.2 = some w →
      AndOrNodeReach rules d v₀ d' w

lemma AndOrNodeReach.depth_le {rules : ν → List (ν × Option ν)} {d d' : ℕ} {v₀ v : ν}
    (h : AndOrNodeReach rules d v₀ d' v) : d' ≤ d := by
  induction h with
  | refl _ => exact le_rfl
  | left _ _ _ ih => omega
  | right _ _ _ ih => omega

/-- Call-stack frame for depth-first AND-OR tree evaluation: `none` forwards a tail call's return
value, while `some ((d, v), (idx, stage))` tracks remaining depth `d`, node `v`, rule index `idx`,
and whether premise 1 (`false`) or premise 2 (`true`) is currently active. -/
abbrev AndOrFrame (ν : Type) := Option ((ℕ × ν) × (ℕ × Bool))

/-- Framed encoding of `AndOrFrame ν`. -/
abbrev encAndOrFrame (encN : ν ↪ List Bool) : AndOrFrame ν ↪ List Bool :=
  encOption (encPair (encPair encNat encN) (encPair encNat encBool))

/-- Evaluation of rules starting from index `idx` at node `v` and depth `d`. -/
private def searchFrom (isAxiom : ν → Bool) (rules : ν → List (ν × Option ν)) :
    ℕ → ν → ℕ → Bool
  | 0, v, idx => if idx == 0 then isAxiom v else false
  | d + 1, v, idx =>
      if idx == 0 && isAxiom v then true
      else ((rules v).drop idx).any fun r ↦
        AndOrProvable isAxiom rules d r.1 &&
          match r.2 with
          | none => true
          | some v₂ => AndOrProvable isAxiom rules d v₂

private lemma searchFrom_zero (isAxiom : ν → Bool) (rules : ν → List (ν × Option ν))
    (d : ℕ) (v : ν) :
    searchFrom isAxiom rules d v 0 = AndOrProvable isAxiom rules d v := by
  cases d <;> simp [searchFrom, AndOrProvable]

private lemma searchFrom_of_ge (isAxiom : ν → Bool) (rules : ν → List (ν × Option ν))
    {d idx : ℕ} {v : ν} (h : (rules v).length ≤ idx) (h0 : idx ≠ 0 ∨ isAxiom v = false) :
    searchFrom isAxiom rules (d + 1) v idx = false := by
  simp only [searchFrom, List.drop_eq_nil_of_le h, List.any_nil, ite_eq_right_iff,
    Bool.and_eq_true, beq_iff_eq]
  rintro ⟨rfl, hax⟩
  rcases h0 with hne | hfalse
  · exact absurd rfl hne
  · simp [hfalse] at hax

private lemma searchFrom_step (isAxiom : ν → Bool) (rules : ν → List (ν × Option ν))
    {d idx : ℕ} {v : ν} (hlt : idx < (rules v).length) (h0 : idx ≠ 0 ∨ isAxiom v = false) :
    let r := (rules v).getD idx (v, none)
    searchFrom isAxiom rules (d + 1) v idx =
      ((AndOrProvable isAxiom rules d r.1 &&
          match r.2 with | none => true | some v₂ => AndOrProvable isAxiom rules d v₂) ||
        searchFrom isAxiom rules (d + 1) v (idx + 1)) := by
  have hnot : (idx == 0 && isAxiom v) = false := by
    simp only [Bool.and_eq_false_iff, beq_eq_false_iff_ne]
    exact h0
  have hnot1 : (idx + 1 == 0 && isAxiom v) = false := by simp
  have hdrop : (rules v).drop idx = (rules v)[idx] :: (rules v).drop (idx + 1) :=
    List.drop_eq_getElem_cons hlt
  have hgetD : (rules v).getD idx (v, none) = (rules v)[idx] := List.getD_eq_getElem _ _ hlt
  simp only [searchFrom, hnot, hnot1, Bool.false_eq_true, ↓reduceIte, hdrop, hgetD, List.any_cons]

/-- One step of the stack-recursive AND-OR search body. -/
private def andOrBody [Inhabited ν] (isAxiom : ν × α → Bool)
    (rules : ν × α → List (ν × Option ν)) :
    (AndOrFrame ν × Option Bool) × α → (AndOrFrame ν × AndOrFrame ν) ⊕ Bool :=
  fun p ↦
    let a := p.2
    let ret := p.1.2
    if !p.1.1.isSome then
      .inr (ret.getD false)
    else
      let fr := p.1.1.getD ((0, default), (0, false))
      let d := fr.1.1
      let v := fr.1.2
      let idx := fr.2.1
      let stage := fr.2.2
      let rs := rules (v, a)
      let r := rs.getD idx (default, none)
      if !ret.isSome then
        if (idx == 0) && !stage && isAxiom (v, a) then .inr true
        else if d == 0 then .inr false
        else if idx < rs.length then .inl (some fr, some ((d - 1, r.1), (0, false)))
        else .inr false
      else
        let b := ret.getD false
        if d == 0 then .inr false
        else if !stage then
          if !b then .inl (none, some ((d, v), (idx + 1, false)))
          else if !r.2.isSome then .inr true
          else .inl (some ((d, v), (idx, true)),
            some ((d - 1, r.2.getD default), (0, false)))
        else
          if b then .inr true
          else .inl (none, some ((d, v), (idx + 1, false)))

private theorem andOrBody_polyTime [Inhabited ν] {encA : α ↪ List Bool} {encN : ν ↪ List Bool}
    {isAxiom : ν × α → Bool} {rules : ν × α → List (ν × Option ν)}
    (hisAxiom : ComputableInPolyTime isAxiom (encPair encN encA) encBool)
    (hrules : ComputableInPolyTime rules (encPair encN encA)
      (encList (encPair encN (encOption encN)))) :
    ComputableInPolyTime (andOrBody isAxiom rules)
      (encPair (encPair (encAndOrFrame encN) (encOption encBool)) encA)
      (encSum (encPair (encAndOrFrame encN) (encAndOrFrame encN)) encBool) := by
  set encF := encAndOrFrame encN
  set encIn := encPair (encPair encF (encOption encBool)) encA
  set encOut := encSum (encPair encF encF) encBool
  have hframeOpt : ComputableInPolyTime (fun p : (AndOrFrame ν × Option Bool) × α ↦ p.1.1)
      encIn (encOption (encPair (encPair encNat encN) (encPair encNat encBool))) := by fun_prop
  have hretOpt : ComputableInPolyTime (fun p : (AndOrFrame ν × Option Bool) × α ↦ p.1.2)
      encIn (encOption encBool) := by fun_prop
  have ha : ComputableInPolyTime (fun p : (AndOrFrame ν × Option Bool) × α ↦ p.2)
      encIn encA := by fun_prop
  have hfr : ComputableInPolyTime
      (fun p : (AndOrFrame ν × Option Bool) × α ↦ p.1.1.getD ((0, default), (0, false)))
      encIn (encPair (encPair encNat encN) (encPair encNat encBool)) :=
    ComputableInPolyTime.optionGetDWithInput hframeOpt
      (ComputableInPolyTime.const ((0, default), (0, false)))
  have hd : ComputableInPolyTime (fun p ↦ (p.1.1.getD ((0, default), (0, false))).1.1)
      encIn encNat := (ComputableInPolyTime.fst _ _).comp ((ComputableInPolyTime.fst _ _).comp hfr)
  have hv : ComputableInPolyTime (fun p ↦ (p.1.1.getD ((0, default), (0, false))).1.2)
      encIn encN := (ComputableInPolyTime.snd _ _).comp ((ComputableInPolyTime.fst _ _).comp hfr)
  have hidx : ComputableInPolyTime (fun p ↦ (p.1.1.getD ((0, default), (0, false))).2.1)
      encIn encNat := (ComputableInPolyTime.fst _ _).comp ((ComputableInPolyTime.snd _ _).comp hfr)
  have hstage : ComputableInPolyTime (fun p ↦ (p.1.1.getD ((0, default), (0, false))).2.2)
      encIn encBool := (ComputableInPolyTime.snd _ _).comp ((ComputableInPolyTime.snd _ _).comp hfr)
  have hrs : ComputableInPolyTime (fun p ↦ rules ((p.1.1.getD ((0, default), (0, false))).1.2, p.2))
      encIn (encList (encPair encN (encOption encN))) := hrules.comp (hv.prod ha)
  have hr : ComputableInPolyTime
      (fun p ↦ (rules ((p.1.1.getD ((0, default), (0, false))).1.2, p.2)).getD
        (p.1.1.getD ((0, default), (0, false))).2.1 (default, none))
      encIn (encPair encN (encOption encN)) :=
    ComputableInPolyTime.listGetD_binary (default, none) hrs hidx
  have hr1 : ComputableInPolyTime
      (fun p ↦ ((rules ((p.1.1.getD ((0, default), (0, false))).1.2, p.2)).getD
        (p.1.1.getD ((0, default), (0, false))).2.1 (default, none)).1) encIn encN :=
    (ComputableInPolyTime.fst _ _).comp hr
  have hr2 : ComputableInPolyTime
      (fun p ↦ ((rules ((p.1.1.getD ((0, default), (0, false))).1.2, p.2)).getD
        (p.1.1.getD ((0, default), (0, false))).2.1 (default, none)).2)
      encIn (encOption encN) := (ComputableInPolyTime.snd _ _).comp hr
  have hax : ComputableInPolyTime (fun p ↦ isAxiom ((p.1.1.getD ((0, default), (0, false))).1.2,
    p.2))
      encIn encBool := hisAxiom.comp (hv.prod ha)
  have hb : ComputableInPolyTime (fun p : (AndOrFrame ν × Option Bool) × α ↦ p.1.2.getD false)
      encIn encBool :=
    ComputableInPolyTime.optionGetDWithInput hretOpt (ComputableInPolyTime.const false)
  have hlen : ComputableInPolyTime
      (fun p ↦ (rules ((p.1.1.getD ((0, default), (0, false))).1.2, p.2)).length) encIn encNat :=
    ComputableInPolyTime.unary_to_binary.comp
      ((ComputableInPolyTime.length (encPair encN (encOption encN))).comp hrs)
  have hd_sub : ComputableInPolyTime
      (fun p ↦ (p.1.1.getD ((0, default), (0, false))).1.1 - 1) encIn encNat :=
    ComputableInPolyTime.binary_sub' hd (ComputableInPolyTime.const 1)
  have hidx_succ : ComputableInPolyTime
      (fun p ↦ (p.1.1.getD ((0, default), (0, false))).2.1 + 1) encIn encNat :=
    ComputableInPolyTime.binary_add.comp (hidx.prod (ComputableInPolyTime.const 1))
  have hd0 : ComputableInPolyTime
      (fun p ↦ (p.1.1.getD ((0, default), (0, false))).1.1 == 0) encIn encBool := by
    refine (ComputableInPolyTime.decide_eq' hd
      (ComputableInPolyTime.const (encOut := encNat) 0)).of_enc_eq fun p ↦ ?_
    exact congrArg encBool
      (Bool.eq_iff_iff.mpr (by simp only [beq_iff_eq, decide_eq_true_eq]))
  have hidx0 : ComputableInPolyTime
      (fun p ↦ (p.1.1.getD ((0, default), (0, false))).2.1 == 0) encIn encBool := by
    refine (ComputableInPolyTime.decide_eq' hidx
      (ComputableInPolyTime.const (encOut := encNat) 0)).of_enc_eq fun p ↦ ?_
    exact congrArg encBool
      (Bool.eq_iff_iff.mpr (by simp only [beq_iff_eq, decide_eq_true_eq]))
  have hlt : ComputableInPolyTime
      (fun p ↦ decide ((p.1.1.getD ((0, default), (0, false))).2.1 <
        (rules ((p.1.1.getD ((0, default), (0, false))).1.2, p.2)).length)) encIn encBool :=
    ComputableInPolyTime.binary_lt.comp (hidx.prod hlen)
  have hInl : ∀ {g₁ g₂ : (AndOrFrame ν × Option Bool) × α → AndOrFrame ν},
      ComputableInPolyTime g₁ encIn encF → ComputableInPolyTime g₂ encIn encF →
      ComputableInPolyTime (fun p ↦ (Sum.inl (g₁ p, g₂ p) : (AndOrFrame ν × AndOrFrame ν) ⊕ Bool))
        encIn encOut :=
    fun hg₁ hg₂ ↦ (ComputableInPolyTime.sumInl (encPair encF encF) encBool).comp (hg₁.prod hg₂)
  have hInr : ∀ {g : (AndOrFrame ν × Option Bool) × α → Bool},
      ComputableInPolyTime g encIn encBool →
      ComputableInPolyTime (fun p ↦ (Sum.inr (g p) : (AndOrFrame ν × AndOrFrame ν) ⊕ Bool))
        encIn encOut :=
    fun hg ↦ (ComputableInPolyTime.sumInr (encPair encF encF) encBool).comp hg
  have hSomeFr : ∀ {gd gv gidx gstage},
      ComputableInPolyTime gd encIn encNat → ComputableInPolyTime gv encIn encN →
      ComputableInPolyTime gidx encIn encNat → ComputableInPolyTime gstage encIn encBool →
      ComputableInPolyTime (fun p ↦ (some ((gd p, gv p), (gidx p, gstage p)) : AndOrFrame ν))
        encIn encF :=
    fun h1 h2 h3 h4 ↦ (ComputableInPolyTime.optionSome _).comp ((h1.prod h2).prod (h3.prod h4))
  have hNext := hInl (ComputableInPolyTime.const (encOut := encF) none)
    (hSomeFr hd hv hidx_succ (ComputableInPolyTime.const false))
  have hCall1 := hInl ((ComputableInPolyTime.optionSome _).comp hfr)
    (hSomeFr hd_sub hr1 (ComputableInPolyTime.const 0) (ComputableInPolyTime.const false))
  have hCall2 := hInl
    (hSomeFr hd hv hidx (ComputableInPolyTime.const true))
    (hSomeFr hd_sub
      (ComputableInPolyTime.optionGetDWithInput hr2 (ComputableInPolyTime.const default))
      (ComputableInPolyTime.const 0) (ComputableInPolyTime.const false))
  have hTrue := hInr (ComputableInPolyTime.const true)
  have hFalse := hInr (ComputableInPolyTime.const false)
  have hBranchNone :=
    ComputableInPolyTime.ite
      (ComputableInPolyTime.bool_and.comp
        ((ComputableInPolyTime.bool_and.comp
          (hidx0.prod (ComputableInPolyTime.bool_not.comp hstage))).prod hax))
      hTrue
      (ComputableInPolyTime.ite hd0 hFalse
        (ComputableInPolyTime.ite hlt hCall1 hFalse))
  have hBranchSome :=
    ComputableInPolyTime.ite hd0 hFalse
      (ComputableInPolyTime.ite (ComputableInPolyTime.bool_not.comp hstage)
        (ComputableInPolyTime.ite (ComputableInPolyTime.bool_not.comp hb) hNext
          (ComputableInPolyTime.ite
            (ComputableInPolyTime.bool_not.comp (ComputableInPolyTime.optionIsSome hr2))
            hTrue hCall2))
        (ComputableInPolyTime.ite hb hTrue hNext))
  refine (ComputableInPolyTime.ite
    (ComputableInPolyTime.bool_not.comp (ComputableInPolyTime.optionIsSome hframeOpt))
    (hInr hb)
    (ComputableInPolyTime.ite
      (ComputableInPolyTime.bool_not.comp (ComputableInPolyTime.optionIsSome hretOpt))
      hBranchNone hBranchSome)).of_enc_eq fun p ↦ ?_
  simp only [andOrBody, Function.comp_apply, decide_eq_true_eq]

/-- **Bounded-depth AND-OR search in `DSPACE` / `EXPSPACE`**: given polynomial-time leaf and
rule-generation oracles and exponential bounds `D`, `F`, `L ≤ 2 ^ h n` on depth, reachable node
encoding length, and reachable rule-list length, bounded-depth AND-OR provability belongs to
`Cslib.Complexity.EXPSPACE`. -/
theorem mem_EXPSPACE_of_bounded_andOrSearch [Inhabited ν]
    {encA : α ↪ List Bool} {encN : ν ↪ List Bool}
    {init : α → ν} {isAxiom : ν × α → Bool} {rules : ν × α → List (ν × Option ν)}
    {D F L : α → ℕ} {h : ℕ → ℕ}
    (hh : PolynomiallyBounded h)
    (hinit : ComputableInSpace (fun a ↦ (some ((D a, init a), (0, false)) : AndOrFrame ν))
      encA (encAndOrFrame encN) (fun a ↦ 2 ^ h (encA a).length))
    (hisAxiom : ComputableInPolyTime isAxiom (encPair encN encA) encBool)
    (hrules : ComputableInPolyTime rules (encPair encN encA)
      (encList (encPair encN (encOption encN))))
    (hD : ∀ a, D a ≤ 2 ^ h (encA a).length)
    (hF : ∀ a d' v, AndOrNodeReach (fun w ↦ rules (w, a)) (D a) (init a) d' v →
      (encN v).length ≤ F a ∧ F a ≤ 2 ^ h (encA a).length)
    (hL : ∀ a d' v, AndOrNodeReach (fun w ↦ rules (w, a)) (D a) (init a) d' v →
      (rules (v, a)).length ≤ L a ∧ L a ≤ 2 ^ h (encA a).length)
    (hL₀ : ∀ a, L a ≤ 2 ^ h (encA a).length) :
    { a : α | AndOrProvable (fun v ↦ isAxiom (v, a)) (fun v ↦ rules (v, a)) (D a) (init a) = true }
      ∈ EXPSPACE encA := by
  classical
  set encF := encAndOrFrame encN
  have hbody_pt := andOrBody_polyTime (encA := encA) (encN := encN) hisAxiom hrules
  obtain ⟨T, hTpoly, hbody⟩ := (ComputableInPolySpace.of_polyTime hbody_pt).exists_inSpace
  obtain ⟨cT, dT, hTle⟩ := hTpoly.exists_le
  -- Uniform upper bound on frame length and body budget for all reachable configurations.
  let Bframe (a : α) : ℕ := 8 * (h (encA a).length + 2 ^ h (encA a).length + (encA a).length + 10)
  let Tmax (a : α) : ℕ := cT * (4 * Bframe a + (encA a).length + 10) ^ dT + 1
  let StepCost (a : α) : ℕ := 4 + Bframe a + Tmax a + 2
  let needBase (a : α) (d : ℕ) : ℕ :=
    d * (L a * StepCost a + Bframe a + 2 + Tmax a) + Tmax a
  let Reach (a : α) : AndOrFrame ν × Option Bool → Prop
    | (none, some _) => True
    | (none, none) => False
    | (some ((d, v), (idx, stage)), ret) =>
        AndOrNodeReach (fun w ↦ rules (w, a)) (D a) (init a) d v ∧
        idx ≤ (rules (v, a)).length ∧
        (stage = true → d > 0 ∧ idx < (rules (v, a)).length ∧
          ret.isSome = true ∧ ((rules (v, a)).getD idx (default, none)).2.isSome = true) ∧
        (ret.isSome = true → d > 0 ∧ idx < (rules (v, a)).length)
  let val (a : α) : AndOrFrame ν × Option Bool → Bool
    | (none, ret) => ret.getD false
    | (some ((d, v), (idx, stage)), none) =>
        if stage then false else searchFrom (fun w ↦ isAxiom (w, a)) (fun w ↦ rules (w, a)) d v idx
    | (some ((0, _), _), some _) => false
    | (some ((d' + 1, v), (idx, false)), some b) =>
        if !b then searchFrom (fun w ↦ isAxiom (w, a)) (fun w ↦ rules (w, a)) (d' + 1) v (idx + 1)
        else
          let r := (rules (v, a)).getD idx (default, none)
          match r.2 with
          | none => true
          | some v₂ =>
              if AndOrProvable (fun w ↦ isAxiom (w, a)) (fun w ↦ rules (w, a)) d' v₂ then true
              else searchFrom (fun w ↦ isAxiom (w, a)) (fun w ↦ rules (w, a)) (d' + 1) v (idx + 1)
    | (some ((d' + 1, v), (idx, true)), some b) =>
        if b then true
        else searchFrom (fun w ↦ isAxiom (w, a)) (fun w ↦ rules (w, a)) (d' + 1) v (idx + 1)
  let rank (a : α) : AndOrFrame ν × Option Bool → ℕ
    | (none, _) => 0
    | (some ((d, _), (idx, stage)), ret) =>
        4 * (L a + 1) * d + 4 * (L a + 1 - min idx (L a + 1)) +
          (if stage then 1 else 3) - (if ret.isSome then 1 else 0)
  let need (a : α) : AndOrFrame ν × Option Bool → ℕ
    | (none, _) => Tmax a
    | (some ((0, _), _), _) => Tmax a
    | (some ((d' + 1, _), (idx, stage)), ret) =>
        needBase a d' + (L a - idx) * StepCost a +
          (if stage then 0 else Bframe a) + (if ret.isSome then 0 else 2) + Tmax a
  have hFrameLen : ∀ a (d : ℕ) (v : ν) (idx : ℕ) (stage : Bool),
      AndOrNodeReach (fun w ↦ rules (w, a)) (D a) (init a) d v →
      idx ≤ (rules (v, a)).length →
      (encF (some ((d, v), (idx, stage)))).length + 1 ≤ Bframe a := by
    intro a d v idx stage hreach hidx
    have hd_le : d ≤ 2 ^ h (encA a).length := hreach.depth_le.trans (hD a)
    have hv_le : (encN v).length ≤ 2 ^ h (encA a).length :=
      (hF a d v hreach).1.trans (hF a d v hreach).2
    have hi_le : idx ≤ 2 ^ h (encA a).length :=
      hidx.trans ((hL a d v hreach).1.trans (hL a d v hreach).2)
    have hnat_d : (encNat d).length ≤ h (encA a).length + 1 := by
      refine length_encNat_le_of_lt_two_pow ?_
      have := Nat.pow_le_pow_right (show 1 ≤ 2 by norm_num) (Nat.le_succ (h (encA a).length))
      rw [Nat.pow_succ] at this
      have := Nat.one_le_two_pow (n := h (encA a).length)
      omega
    have hnat_i : (encNat idx).length ≤ h (encA a).length + 1 := by
      refine length_encNat_le_of_lt_two_pow ?_
      rw [Nat.pow_succ]
      have := Nat.one_le_two_pow (n := h (encA a).length)
      omega
    have hbool : (encBool stage).length = 1 := by cases stage <;> rfl
    simp only [encF, encAndOrFrame, Bframe]
    enc_len
  have hNoneLen : (encF (none : AndOrFrame ν)).length + 1 ≤ 2 := by
    simp [encF, encAndOrFrame]
  have hT_bound : ∀ a c, Reach a c → T (c, a) ≤ Tmax a := by
    intro a c hR
    have hpair : (encPair (encPair encF (encOption encBool)) encA (c, a)).length ≤
        4 * Bframe a + (encA a).length + 9 := by
      have hc : (encF c.1).length ≤ Bframe a := by
        rcases c with ⟨fr, ret⟩
        cases fr with
        | none =>
          have h1 : (encF none).length ≤ 1 := by have := hNoneLen; omega
          have h2 : 1 ≤ Bframe a :=
            Nat.le_trans (by norm_num) (Nat.mul_le_mul_left 8 (Nat.le_add_left 10 _))
          exact h1.trans h2
        | some x =>
          rcases x with ⟨⟨d, v⟩, ⟨idx, stage⟩⟩
          exact (Nat.le_succ _).trans (hFrameLen a d v idx stage hR.1 hR.2.1)
      have hret : (encOption encBool c.2).length ≤ 3 := by
        cases c.2 with | none => simp | some b => cases b <;> simp
      enc_len
    exact (hTle (c, a)).trans (by
      have harg : (encPair (encPair (encAndOrFrame encN) (encOption encBool)) encA (c, a)).length +
          1 ≤ 4 * Bframe a + (encA a).length + 10 := by
        dsimp only [encF] at hpair; omega
      have hpow := Nat.pow_le_pow_left harg dT
      have hmul := Nat.mul_le_mul_left cT hpow
      dsimp only [Tmax]; omega)
  have hneedBase_le : ∀ a d, needBase a d ≤ need a (some ((d, init a), (0, false)), none) := by
    intro a d
    cases d with
    | zero => simp [needBase, need]
    | succ d' =>
      simp only [needBase, need, Nat.sub_zero, Bool.false_eq_true, ↓reduceIte, Option.isSome_none]
      nlinarith
  have hT_need : ∀ a c, Reach a c → T (c, a) ≤ need a c := fun a c hR ↦
    (hT_bound a c hR).trans (by
      rcases c with ⟨fr, ret⟩
      cases fr with
      | none => simp [need]
      | some x =>
        rcases x with ⟨⟨d, _⟩, ⟨_, _⟩⟩
        cases d <;> simp [need])
  have hrec := ComputableInSpace.recWith (encA := encA) (encF := encF) (encB := encBool)
    (init := fun a ↦ (some ((D a, init a), (0, false)) : AndOrFrame ν))
    (body := andOrBody isAxiom rules)
    (S := fun a ↦ 2 ^ h (encA a).length)
    (B := fun a ↦ needBase a (D a) + (L a + 1) * StepCost a + Bframe a + 2 + Tmax a)
    val rank need Reach hinit hbody
    (fun a ↦ ⟨AndOrNodeReach.refl _ _, Nat.zero_le _, by simp, by simp⟩)
    (by
      intro a c saved child hR hcall
      rcases c with ⟨fr, ret⟩
      cases fr with
      | none => simp [andOrBody] at hcall
      | some x =>
        rcases x with ⟨⟨d, v⟩, ⟨idx, stage⟩⟩
        rcases hR with ⟨hreach, hidx, hstage, hret⟩
        cases ret with
        | none =>
          simp only [andOrBody, Option.isSome_some, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
            Option.getD_some, Option.isSome_none, Bool.not_false] at hcall
          by_cases hax : ((idx == 0) && !stage && isAxiom (v, a)) = true
          · simp [hax] at hcall
          · simp only [hax] at hcall
            by_cases hd0 : (d == 0) = true
            · simp [hd0] at hcall
            · simp only [hd0] at hcall
              by_cases hlt : idx < (rules (v, a)).length
              · simp only [hlt, ↓reduceIte] at hcall
                rcases Prod.mk.inj (Sum.inl.inj hcall) with ⟨rfl, rfl⟩
                obtain ⟨d', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by simpa using hd0)
                have hmem : (rules (v, a)).getD idx (default, none) ∈ rules (v, a) := by
                  rw [List.getD_eq_getElem _ _ hlt]; exact List.getElem_mem hlt
                have hreach₁ : AndOrNodeReach (fun w ↦ rules (w, a)) (D a) (init a) d'
                    ((rules (v, a)).getD idx (default, none)).1 := .left hreach hmem rfl
                have hLle := (hL a (d' + 1) v hreach).1
                have hstage0 : stage = false := by
                  cases stage with
                  | false => rfl
                  | true => exfalso; exact absurd (hstage rfl).2.2.1 (by simp)
                subst hstage0
                have h0_or : idx ≠ 0 ∨ isAxiom (v, a) = false := by
                  by_cases hi : idx = 0
                  · right; subst hi; simpa using hax
                  · exact Or.inl hi
                refine ⟨⟨hreach₁, Nat.zero_le _, by simp, by simp⟩,
                  ⟨hreach, hidx, by simp, by simp [hlt]⟩, ?_, ?_, ?_⟩
                · simp only [rank, Bool.false_eq_true, ↓reduceIte, Option.isSome_none,
                    Nat.succ_sub_one, Nat.sub_zero, Nat.zero_min]
                  have hmul : 4 * (L a + 1) * d'.succ = 4 * (L a + 1) * d' + 4 * (L a + 1) := by
                    rw [Nat.succ_eq_add_one]; ring
                  have hmin : min idx (L a + 1) ≤ L a := by omega
                  rw [hmul]; omega
                · simp only [rank, Bool.false_eq_true, ↓reduceIte, Option.isSome_none,
                    Option.isSome_some]
                  omega
                · simp only [val, Bool.false_eq_true, ↓reduceIte, Nat.succ_sub_one]
                  have hget : (rules (v, a)).getD idx (v, none) =
                      (rules (v, a)).getD idx (default, none) := by
                    rw [List.getD_eq_getElem _ _ hlt, List.getD_eq_getElem _ _ hlt]
                  rw [searchFrom_zero,
                    searchFrom_step (fun w ↦ isAxiom (w, a)) (fun w ↦ rules (w, a)) hlt h0_or,
                    hget]
                  cases hval1 : AndOrProvable (fun w ↦ isAxiom (w, a)) (fun w ↦ rules (w, a)) d'
                    ((rules (v, a)).getD idx (default, none)).1
                  · simp
                  · simp only [Bool.true_and]
                    cases h2 : ((rules (v, a)).getD idx (default, none)).2 <;> simp
              · simp [hlt] at hcall
        | some b =>
          simp only [andOrBody, Option.isSome_some, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
            Option.getD_some] at hcall
          rcases hret rfl with ⟨hdpos, hlt⟩
          obtain ⟨d', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hdpos)
          have hLle := (hL a (d' + 1) v hreach).1
          have hd0 : (d' + 1 == 0) = false := by simp
          simp only [hd0, Bool.false_eq_true, ↓reduceIte] at hcall
          cases stage with
          | false =>
            simp only [Bool.not_false, ↓reduceIte] at hcall
            cases b with
            | false =>
              simp only [Bool.not_false, ↓reduceIte, Sum.inl.injEq, Prod.mk.injEq] at hcall
              rcases hcall with ⟨rfl, rfl⟩
              refine ⟨⟨hreach, hlt, by simp, by simp⟩, trivial, ?_, ?_, ?_⟩
              · simp only [rank, Bool.false_eq_true, ↓reduceIte, Option.isSome_none,
                  Option.isSome_some]
                have h1 : min idx (L a + 1) = idx := Nat.min_eq_left (by omega)
                have h2 : min (idx + 1) (L a + 1) = idx + 1 := Nat.min_eq_left (by omega)
                rw [h1, h2]; omega
              · simp only [rank, Bool.false_eq_true, ↓reduceIte, Option.isSome_some]
                omega
              · simp [val]
            | true =>
              simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hcall
              cases hr2 : ((rules (v, a)).getD idx (default, none)).2 with
              | none =>
                simp only [hr2, Option.isSome_none, Bool.not_false, ↓reduceIte] at hcall
                cases hcall
              | some v₂ =>
                simp only [hr2, Option.isSome_some, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
                  Option.getD_some, Sum.inl.injEq, Prod.mk.injEq] at hcall
                rcases hcall with ⟨rfl, rfl⟩
                have hr2_some : ((rules (v, a)).getD idx (default, none)).2.isSome = true := by
                  simp only [hr2, Option.isSome_some]
                have hmem : (rules (v, a)).getD idx (default, none) ∈ rules (v, a) := by
                  rw [List.getD_eq_getElem _ _ hlt]; exact List.getElem_mem hlt
                have hreach₂ : AndOrNodeReach (fun w ↦ rules (w, a)) (D a) (init a) d' v₂ :=
                  .right hreach hmem hr2
                refine ⟨⟨hreach₂, Nat.zero_le _, by simp, by simp⟩,
                  ⟨hreach, hidx, fun _ ↦ ⟨Nat.succ_pos _, hlt, rfl, hr2_some⟩,
                    fun _ ↦ ⟨Nat.succ_pos _, hlt⟩⟩, ?_, ?_, ?_⟩
                · simp only [rank, Bool.false_eq_true, ↓reduceIte, Option.isSome_none,
                    Option.isSome_some, Nat.sub_zero, Nat.zero_min, Nat.succ_sub_one]
                  have hmul : 4 * (L a + 1) * d'.succ = 4 * (L a + 1) * d' + 4 * (L a + 1) := by
                    rw [Nat.succ_eq_add_one]; ring
                  have hmin : min idx (L a + 1) ≤ L a := by omega
                  rw [hmul]; omega
                · simp only [rank, Bool.false_eq_true, ↓reduceIte, Option.isSome_some]
                  omega
                · simp only [val, hr2, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
                    Nat.succ_sub_one, searchFrom_zero]
          | true =>
            simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hcall
            cases b with
            | true => simp only [↓reduceIte] at hcall; cases hcall
            | false =>
              simp only [Bool.false_eq_true, ↓reduceIte, Sum.inl.injEq, Prod.mk.injEq] at hcall
              rcases hcall with ⟨rfl, rfl⟩
              refine ⟨⟨hreach, hlt, by simp, by simp⟩, trivial, ?_, ?_, ?_⟩
              · simp only [rank, Bool.false_eq_true, ↓reduceIte, Option.isSome_none,
                  Option.isSome_some]
                have h1 : min idx (L a + 1) = idx := Nat.min_eq_left (by omega)
                have h2 : min (idx + 1) (L a + 1) = idx + 1 := Nat.min_eq_left (by omega)
                rw [h1, h2]; omega
              · simp only [rank, ↓reduceIte, Option.isSome_some]
                omega
              · simp [val])
    (by
      intro a c saved child hR hcall
      rcases c with ⟨fr, ret⟩
      cases fr with
      | none => simp [andOrBody] at hcall
      | some x =>
        rcases x with ⟨⟨d, v⟩, ⟨idx, stage⟩⟩
        rcases hR with ⟨hreach, hidx, hstage, hret⟩
        cases ret with
        | none =>
          simp only [andOrBody, Option.isSome_some, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
            Option.getD_some, Option.isSome_none, Bool.not_false] at hcall
          by_cases hax : ((idx == 0) && !stage && isAxiom (v, a)) = true
          · simp [hax] at hcall
          · simp only [hax] at hcall
            by_cases hd0 : (d == 0) = true
            · simp [hd0] at hcall
            · simp only [hd0] at hcall
              by_cases hlt : idx < (rules (v, a)).length
              · simp only [hlt, ↓reduceIte] at hcall
                rcases Prod.mk.inj (Sum.inl.inj hcall) with ⟨rfl, rfl⟩
                obtain ⟨d', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by simpa using hd0)
                have hstage0 : stage = false := by
                  cases stage with
                  | false => rfl
                  | true => exfalso; exact absurd (hstage rfl).2.2.1 (by simp)
                subst hstage0
                have hflen : (encF (some ((d'.succ, v), (idx, false)))).length + 1 ≤ Bframe a :=
                  hFrameLen a d'.succ v idx false hreach hidx
                have hLle := (hL a (d' + 1) v hreach).1
                have hchild_le : need a (some ((d', ((rules (v, a)).getD idx (default, none)).1),
                    (0, false)), none) ≤ needBase a d' + (L a - idx) * StepCost a := by
                  cases d' with
                  | zero =>
                    simp only [need, needBase, Nat.zero_mul, Nat.zero_add]
                    omega
                  | succ d'' =>
                    simp only [need, needBase, Nat.sub_zero, Bool.false_eq_true, ↓reduceIte,
                      Option.isSome_none]
                    nlinarith
                simp only [need, Bool.false_eq_true, ↓reduceIte, Option.isSome_none,
                  Option.isSome_some, Nat.succ_sub_one] at hchild_le ⊢
                constructor
                · omega
                · omega
              · simp [hlt] at hcall
        | some b =>
          simp only [andOrBody, Option.isSome_some, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
            Option.getD_some] at hcall
          rcases hret rfl with ⟨hdpos, hlt⟩
          obtain ⟨d', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hdpos)
          have hLle := (hL a (d' + 1) v hreach).1
          have hd0 : (d' + 1 == 0) = false := by simp
          simp only [hd0, Bool.false_eq_true, ↓reduceIte] at hcall
          cases stage with
          | false =>
            simp only [Bool.not_false, ↓reduceIte] at hcall
            cases b with
            | false =>
              simp only [Bool.not_false, ↓reduceIte, Sum.inl.injEq, Prod.mk.injEq] at hcall
              rcases hcall with ⟨rfl, rfl⟩
              have hstep_sub : (L a - idx) * StepCost a =
                  (L a - (idx + 1)) * StepCost a + StepCost a := by
                have : L a - idx = (L a - (idx + 1)) + 1 := by omega
                rw [this, Nat.add_mul, Nat.one_mul]
              simp only [need, StepCost, Bool.false_eq_true, ↓reduceIte, Option.isSome_none,
                Option.isSome_some] at hstep_sub ⊢
              rw [hstep_sub]
              constructor <;> omega
            | true =>
              simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hcall
              cases hr2 : ((rules (v, a)).getD idx (default, none)).2 with
              | none =>
                simp only [hr2, Option.isSome_none, Bool.not_false, ↓reduceIte] at hcall
                cases hcall
              | some v₂ =>
                simp only [hr2, Option.isSome_some, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
                  Option.getD_some, Sum.inl.injEq, Prod.mk.injEq] at hcall
                rcases hcall with ⟨rfl, rfl⟩
                have hflen : (encF (some ((d'.succ, v), (idx, true)))).length + 1 ≤ Bframe a :=
                  hFrameLen a d'.succ v idx true hreach hidx
                have hchild_le : need a (some ((d', v₂), (0, false)), none) ≤
                    needBase a d' + (L a - idx) * StepCost a := by
                  cases d' with
                  | zero => simp only [need, needBase, Nat.zero_mul, Nat.zero_add]; omega
                  | succ d'' =>
                    simp only [need, needBase, Nat.sub_zero, Bool.false_eq_true, ↓reduceIte,
                      Option.isSome_none]
                    nlinarith
                simp only [need, Bool.false_eq_true, ↓reduceIte, Option.isSome_some,
                  Nat.succ_sub_one] at hchild_le ⊢
                constructor <;> omega
          | true =>
            simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hcall
            cases b with
            | true => simp only [↓reduceIte] at hcall; cases hcall
            | false =>
              simp only [Bool.false_eq_true, ↓reduceIte, Sum.inl.injEq, Prod.mk.injEq] at hcall
              rcases hcall with ⟨rfl, rfl⟩
              have hstep_sub : (L a - idx) * StepCost a =
                  (L a - (idx + 1)) * StepCost a + StepCost a := by
                have : L a - idx = (L a - (idx + 1)) + 1 := by omega
                rw [this, Nat.add_mul, Nat.one_mul]
              simp only [need, StepCost, Bool.false_eq_true, ↓reduceIte, Option.isSome_none,
                Option.isSome_some] at hstep_sub ⊢
              rw [hstep_sub]
              constructor <;> omega)
    (by
      intro a c v hR hret
      rcases c with ⟨fr, ret⟩
      cases fr with
      | none =>
        simp only [andOrBody, Option.isSome_none, Bool.not_false, ↓reduceIte, Sum.inr.injEq] at hret
        simpa [val] using hret
      | some x =>
        rcases x with ⟨⟨d, w⟩, ⟨idx, stage⟩⟩
        rcases hR with ⟨hreach, hidx, hstage, hretR⟩
        cases ret with
        | none =>
          simp only [andOrBody, Option.isSome_some, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
            Option.getD_some, Option.isSome_none, Bool.not_false] at hret
          have hstage0 : stage = false := by
            cases stage with
            | false => rfl
            | true => exfalso; exact absurd (hstage rfl).2.2.1 (by simp)
          subst hstage0
          by_cases hax : ((idx == 0) && !false && isAxiom (w, a)) = true
          · simp only [hax, ↓reduceIte] at hret
            have hv_eq : true = v := Sum.inr.inj hret
            subst hv_eq
            have hi0 : idx = 0 := by
              simp only [Bool.and_eq_true, beq_iff_eq] at hax; exact hax.1.1
            have hax' : isAxiom (w, a) = true := by
              simp only [Bool.and_eq_true] at hax; exact hax.2
            subst hi0
            cases d <;> simp [val, searchFrom, hax']
          · simp only [hax] at hret
            by_cases hd0 : (d == 0) = true
            · simp only [hd0, ↓reduceIte] at hret
              have hv_eq : false = v := Sum.inr.inj hret
              subst hv_eq
              have hd0' : d = 0 := by simpa using hd0
              subst hd0'
              have h0_or : idx ≠ 0 ∨ isAxiom (w, a) = false := by
                by_cases hi : idx = 0
                · right; subst hi; simpa using hax
                · exact Or.inl hi
              dsimp only [val, searchFrom]
              rcases h0_or with hne | hfalse
              · simp [hne]
              · simp [hfalse]
            · simp only [hd0] at hret
              by_cases hlt : idx < (rules (w, a)).length
              · simp [hlt] at hret
              · simp only [hlt, ↓reduceIte] at hret
                have hv_eq : false = v := Sum.inr.inj hret
                subst hv_eq
                obtain ⟨d', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by simpa using hd0)
                have h0_or : idx ≠ 0 ∨ isAxiom (w, a) = false := by
                  by_cases hi : idx = 0
                  · right; subst hi; simpa using hax
                  · exact Or.inl hi
                dsimp only [val]
                exact searchFrom_of_ge (fun w ↦ isAxiom (w, a)) (fun w ↦ rules (w, a))
                  (by omega) h0_or
        | some b =>
          simp only [andOrBody, Option.isSome_some, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
            Option.getD_some] at hret
          rcases hretR rfl with ⟨hdpos, hlt⟩
          obtain ⟨d', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hdpos)
          have hd0 : (d' + 1 == 0) = false := by simp
          simp only [hd0, Bool.false_eq_true, ↓reduceIte] at hret
          cases stage with
          | false =>
            simp only [Bool.not_false, ↓reduceIte] at hret
            cases b with
            | false => simp at hret
            | true =>
              simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hret
              cases hr2 : ((rules (w, a)).getD idx (default, none)).2 with
              | none =>
                simp only [hr2, Option.isSome_none, Bool.not_false, ↓reduceIte] at hret
                have hv_eq : true = v := Sum.inr.inj hret
                subst hv_eq
                simp only [val, hr2, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
              | some v₂ =>
                simp only [hr2, Option.isSome_some, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
                  at hret
                cases hret
          | true =>
            simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hret
            cases b with
            | true =>
              simp only [↓reduceIte, Sum.inr.injEq] at hret; subst hret; simp [val]
            | false => simp at hret)
    hT_need
    (fun a ↦ by
      cases hD0 : D a with
      | zero => simp [need, needBase]
      | succ d' =>
        simp only [need, needBase, Nat.sub_zero, Bool.false_eq_true, ↓reduceIte, Option.isSome_none]
        have : L a * StepCost a ≤ (L a + 1) * StepCost a := Nat.mul_le_mul_right _ (Nat.le_succ _)
        nlinarith)
  -- Convert the resulting space bound `O(2^h(n) + needBase(D) + ... + log n)` to `EXPSPACE`.
  have hval_eq : (fun a ↦ val a (some ((D a, init a), (0, false)), none)) =
      (fun a ↦ AndOrProvable (fun v ↦ isAxiom (v, a)) (fun v ↦ rules (v, a)) (D a) (init a)) := by
    funext a; exact searchFrom_zero _ _ _ _
  rw [hval_eq] at hrec
  -- Bound the space function by `2 ^ H n` for a polynomially bounded `H`.
  let E : ℕ → ℕ := fun n ↦ h n + n + 10
  let H : ℕ → ℕ := fun n ↦ cT + 20 + (dT + 4) * (E n + 8)
  have hH_poly : PolynomiallyBounded H := by
    obtain ⟨c₀, d₀, hh₀⟩ := polynomiallyBounded_iff_le.mp hh
    refine polynomiallyBounded_iff_le.mpr
      ⟨(cT + 20 + (dT + 4) * (c₀ + 19)), d₀ + 1, fun n ↦ ?_⟩
    have hn : h n ≤ c₀ * (n + 1) ^ d₀ := hh₀ n
    have h1 : 1 ≤ (n + 1) ^ (d₀ + 1) := Nat.one_le_pow _ _ (Nat.succ_pos n)
    have h2 : n + 1 ≤ (n + 1) ^ (d₀ + 1) :=
      le_self_pow₀ (Nat.succ_pos n) (Nat.succ_ne_zero d₀)
    have h3 : (n + 1) ^ d₀ ≤ (n + 1) ^ (d₀ + 1) :=
      Nat.pow_le_pow_right (Nat.succ_pos n) (Nat.le_succ d₀)
    have hE_le : E n + 8 ≤ (c₀ + 19) * (n + 1) ^ (d₀ + 1) := by
      dsimp only [E]; nlinarith
    have hmul := Nat.mul_le_mul_left (dT + 4) hE_le
    have h20 := Nat.mul_le_mul_left (cT + 20) h1
    dsimp only [H]
    linarith
  have hbound : ∀ a,
      2 ^ h (encA a).length +
        (needBase a (D a) + (L a + 1) * StepCost a + Bframe a + 2 + Tmax a) +
        Nat.log2 (encA a).length ≤ 2 ^ H (encA a).length := by
    intro a
    set n := (encA a).length
    have hEn : h n ≤ E n := by dsimp only [E]; omega
    have hnE : n ≤ E n := by dsimp only [E]; omega
    have h10E : 10 ≤ E n := by dsimp only [E]; omega
    have h2h : 2 ^ h n ≤ 2 ^ E n := Nat.pow_le_pow_right (by norm_num) hEn
    have hEpow : E n ≤ 2 ^ E n := (Nat.lt_two_pow_self (n := E n)).le
    have hlog : Nat.log2 n ≤ 2 ^ E n :=
      (Nat.log2_le_self n).trans (hnE.trans hEpow)
    have hBf : Bframe a ≤ 2 ^ (E n + 5) := by
      dsimp only [Bframe]
      have hsum : h n + 2 ^ h n + n + 10 ≤ 4 * 2 ^ E n := by linarith
      have hpow : 2 ^ (E n + 5) = 32 * 2 ^ E n := by rw [Nat.pow_add]; ring
      linarith
    have hArg : 4 * Bframe a + n + 10 ≤ 2 ^ (E n + 8) := by
      have hpow1 : 2 ^ (E n + 8) = 8 * 2 ^ (E n + 5) := by
        have : E n + 8 = (E n + 5) + 3 := by omega
        rw [this, Nat.pow_add]; ring
      have hpow2 : 2 ^ E n ≤ 2 ^ (E n + 5) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      linarith
    have hcT_pow : cT + 1 ≤ 2 ^ (cT + 1) := (Nat.lt_two_pow_self (n := cT + 1)).le
    have hTm : Tmax a ≤ 2 ^ (cT + 1 + (E n + 8) * dT) := by
      dsimp only [Tmax]
      have hpow := Nat.pow_le_pow_left hArg dT
      have hmul : (2 ^ (E n + 8)) ^ dT = 2 ^ ((E n + 8) * dT) := (Nat.pow_mul 2 _ _).symm
      rw [hmul] at hpow
      have h1 : 1 ≤ 2 ^ ((E n + 8) * dT) := Nat.one_le_two_pow
      calc cT * (4 * Bframe a + n + 10) ^ dT + 1
          ≤ cT * 2 ^ ((E n + 8) * dT) + 2 ^ ((E n + 8) * dT) := by
            have := Nat.mul_le_mul_left cT hpow; omega
        _ = (cT + 1) * 2 ^ ((E n + 8) * dT) := by ring
        _ ≤ 2 ^ (cT + 1) * 2 ^ ((E n + 8) * dT) := Nat.mul_le_mul_right _ hcT_pow
        _ = 2 ^ (cT + 1 + (E n + 8) * dT) := (Nat.pow_add 2 _ _).symm
    have hSC : StepCost a ≤ 2 ^ (cT + 4 + (E n + 8) * (dT + 1)) := by
      dsimp only [StepCost]
      have h1 : Bframe a ≤ 2 ^ (cT + 1 + (E n + 8) * dT + (E n + 8)) :=
        hBf.trans (Nat.pow_le_pow_right (by norm_num) (by omega))
      have h2 : Tmax a ≤ 2 ^ (cT + 1 + (E n + 8) * dT + (E n + 8)) :=
        hTm.trans (Nat.pow_le_pow_right (by norm_num) (by omega))
      have h3 : 6 ≤ 2 ^ (cT + 1 + (E n + 8) * dT + (E n + 8)) := by
        have : 3 ≤ cT + 1 + (E n + 8) * dT + (E n + 8) := by omega
        exact (show 6 ≤ 2 ^ 3 by norm_num).trans (Nat.pow_le_pow_right (by norm_num) this)
      have hpow : 2 ^ (cT + 4 + (E n + 8) * (dT + 1)) =
          8 * 2 ^ (cT + 1 + (E n + 8) * dT + (E n + 8)) := by
        have : cT + 4 + (E n + 8) * (dT + 1) =
            (cT + 1 + (E n + 8) * dT + (E n + 8)) + 3 := by ring
        rw [this, Nat.pow_add]; ring
      linarith
    have hL1 : L a + 1 ≤ 2 ^ (E n + 1) := by
      have hLle := hL₀ a
      have hpow : 2 ^ (E n + 1) = 2 * 2 ^ E n := by rw [Nat.pow_add]; ring
      have h1 : 1 ≤ 2 ^ E n := Nat.one_le_two_pow
      linarith
    have hD2 : D a + 2 ≤ 2 ^ (E n + 1) := by
      have hDle := hD a
      have hpow : 2 ^ (E n + 1) = 2 * 2 ^ E n := by rw [Nat.pow_add]; ring
      have h2 : 2 ≤ 2 ^ E n :=
        (show 2 ≤ 2 ^ 1 by norm_num).trans (Nat.pow_le_pow_right (by norm_num) (by omega))
      linarith
    have hNB : needBase a (D a) + (L a + 1) * StepCost a + Bframe a + 2 + Tmax a ≤
        (D a + 2) * ((L a + 1) * StepCost a + Bframe a + 2 + Tmax a) := by
      have hS1 : L a * StepCost a + Bframe a + 2 + Tmax a ≤
          (L a + 1) * StepCost a + Bframe a + 2 + Tmax a :=
        Nat.add_le_add_right
          (Nat.add_le_add_right
            (Nat.add_le_add_right (Nat.mul_le_mul_right _ (Nat.le_succ _)) _) _) _
      have hDmul := Nat.mul_le_mul_left (D a) hS1
      dsimp only [needBase]
      nlinarith
    have hInner : (L a + 1) * StepCost a + Bframe a + 2 + Tmax a ≤
        2 ^ (cT + 7 + (E n + 8) * (dT + 2)) := by
      have hLS : (L a + 1) * StepCost a ≤ 2 ^ (cT + 5 + (E n + 8) * (dT + 2)) := by
        calc (L a + 1) * StepCost a
            ≤ 2 ^ (E n + 1) * 2 ^ (cT + 4 + (E n + 8) * (dT + 1)) :=
              Nat.mul_le_mul hL1 hSC
          _ = 2 ^ (E n + 1 + (cT + 4 + (E n + 8) * (dT + 1))) := (Nat.pow_add 2 _ _).symm
          _ ≤ 2 ^ (cT + 5 + (E n + 8) * (dT + 2)) :=
              Nat.pow_le_pow_right (by norm_num) (by ring_nf; omega)
      have hBf' : Bframe a ≤ 2 ^ (cT + 5 + (E n + 8) * (dT + 2)) :=
        hBf.trans (Nat.pow_le_pow_right (by norm_num) (by nlinarith))
      have hTm' : Tmax a ≤ 2 ^ (cT + 5 + (E n + 8) * (dT + 2)) :=
        hTm.trans (Nat.pow_le_pow_right (by norm_num) (by nlinarith))
      have h2' : 2 ≤ 2 ^ (cT + 5 + (E n + 8) * (dT + 2)) :=
        (show 2 ≤ 2 ^ 1 by norm_num).trans (Nat.pow_le_pow_right (by norm_num) (by omega))
      have hpow : 2 ^ (cT + 7 + (E n + 8) * (dT + 2)) =
          4 * 2 ^ (cT + 5 + (E n + 8) * (dT + 2)) := by
        have : cT + 7 + (E n + 8) * (dT + 2) =
            (cT + 5 + (E n + 8) * (dT + 2)) + 2 := by ring
        rw [this, Nat.pow_add]; ring
      linarith
    have hProd : (D a + 2) * ((L a + 1) * StepCost a + Bframe a + 2 + Tmax a) ≤
        2 ^ (cT + 8 + (E n + 8) * (dT + 3)) := by
      calc (D a + 2) * ((L a + 1) * StepCost a + Bframe a + 2 + Tmax a)
          ≤ 2 ^ (E n + 1) * 2 ^ (cT + 7 + (E n + 8) * (dT + 2)) :=
            Nat.mul_le_mul hD2 hInner
        _ = 2 ^ (E n + 1 + (cT + 7 + (E n + 8) * (dT + 2))) := (Nat.pow_add 2 _ _).symm
        _ ≤ 2 ^ (cT + 8 + (E n + 8) * (dT + 3)) :=
            Nat.pow_le_pow_right (by norm_num) (by ring_nf; omega)
    set K := cT + 8 + (E n + 8) * (dT + 3)
    have h1 : 2 ^ h n ≤ 2 ^ K :=
      h2h.trans (Nat.pow_le_pow_right (by norm_num) (by
        change E n ≤ cT + 8 + (E n + 8) * (dT + 3)
        have hle : E n + 8 ≤ (E n + 8) * (dT + 3) :=
          Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
        omega))
    have h2 : Nat.log2 n ≤ 2 ^ K :=
      hlog.trans (Nat.pow_le_pow_right (by norm_num) (by
        change E n ≤ cT + 8 + (E n + 8) * (dT + 3)
        have hle : E n + 8 ≤ (E n + 8) * (dT + 3) :=
          Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
        omega))
    have hKH : K + 2 ≤ H n := by
      change cT + 8 + (E n + 8) * (dT + 3) + 2 ≤ cT + 20 + (dT + 4) * (E n + 8)
      have hmul : (dT + 4) * (E n + 8) = (E n + 8) * (dT + 3) + (E n + 8) := by ring
      rw [hmul]; omega
    have h3 : 4 * 2 ^ K ≤ 2 ^ H n := by
      calc 4 * 2 ^ K = 2 ^ K * 2 ^ 2 := by ring
        _ = 2 ^ (K + 2) := (Nat.pow_add 2 K 2).symm
        _ ≤ 2 ^ H n := Nat.pow_le_pow_right (by norm_num) hKH
    linarith
  refine DSPACE_two_pow_subset_EXPSPACE hH_poly ?_
  obtain ⟨t, c, hc, _⟩ := hrec
  refine mem_DSPACE_iff.mpr ⟨c, c, t, ?_⟩
  rw [decidableInTimeAndSpace_iff]
  refine ⟨_, hc.mono (fun _ ↦ le_rfl) fun a ↦ ?_, fun _ ↦ Iff.rfl⟩
  have := hbound a
  nlinarith

end AndOr

end Cslib.Complexity
