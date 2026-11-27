/-
Copyright (c) 2026 The CslibFrontier contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The CslibFrontier contributors
-/
module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Logics.Datalog
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Sum

/-!
# Dalmau's Bounded Pathwidth Duality Theorem for Linear Datalog

This module proves Dalmau's theorem characterizing finite relational structures whose
Constraint Satisfaction Problem `CSP(A)` is solvable by linear Datalog as precisely those enjoying
bounded pathwidth duality, strictly under standard Lean axioms. The forward implication unfolds any
unbranched linear Datalog goal derivation into a bounded-pathwidth quotient obstruction; the
converse combines the injective-scope pigeonhole cloud cover with a bag-by-bag forget-and-introduce
sweep in the canonical `(k + 1)`-variable linear Datalog program.

## Main results

* `CslibFrontier.Logics.hasBoundedPathwidthDuality_of_linearDatalog`: every structure whose
  CSP is decided by a linear Datalog program has bounded pathwidth duality.
* `CslibFrontier.Logics.canonicalLinearProgram_decides_of_pathwidthDuality`: if `A` has
  pathwidth duality at most `k`, then `canonicalLinearProgram L A (k + 1)` decides `CSP(A)`.
* `CslibFrontier.Logics.hasBoundedPathwidthDuality_iff_exists_linearDatalog`: Dalmau's
  equivalence between bounded pathwidth duality and solvability by linear Datalog.

## Tags

Dalmau theorem, bounded pathwidth duality, linear Datalog, constraint satisfaction
-/

public section

namespace CslibFrontier.Logics

open FirstOrder FirstOrder.Language

section CanonicalLinearHelpers

/-- Semantic `0`-IDB introduction for `canonicalLinearProgram L A r`. -/
private theorem canonicalLinearDerives_of_init {L : FirstOrder.Language} [IsFinitePosRelational L]
    {A : Type*} [L.Structure A] [Finite A] {r : ℕ} {V : Type*} {I : CSPInstance L V}
    {U : Set V} (hUsub : U ⊆ I.vars) (hUcard : U.ncard ≤ r)
    {n : ℕ} (hn_pos : 0 < n) (hn_le : n ≤ r) (R : Set (Fin n → A))
    (ρ : Fin n → V) (hρ : Set.range ρ ⊆ U)
    (cs : List (CSPConstraint L V))
    (hcs_mem : ∀ c ∈ cs, c ∈ I.constraints)
    (hcs_ar : ∀ c ∈ cs, c.arity ≤ r)
    (hcs_sc : ∀ c ∈ cs, Set.range c.scope ⊆ U)
    (himp : ∀ f : V → A,
      (∀ c ∈ cs, Structure.RelMap c.rel (f ∘ c.scope)) → f ∘ ρ ∈ R) :
    (canonicalLinearProgram L A r).Derives I ⟨n, hn_pos, hn_le, R⟩ ρ := by
  obtain ⟨_, _, hd⟩ := MaxSymDerives.of_init hUsub hUcard hn_pos hn_le R ρ hρ cs
    hcs_mem hcs_ar hcs_sc himp
  exact maximalSymProgram_derives_to_canonical hd

/-- Semantic one-way `1`-IDB step for `canonicalLinearProgram L A r`. -/
private theorem canonicalLinearDerives_of_step {L : FirstOrder.Language} [IsFinitePosRelational L]
    {A : Type*} [L.Structure A] [Finite A] {r : ℕ} {V : Type*} {I : CSPInstance L V}
    {U : Set V} (hUsub : U ⊆ I.vars) (hUcard : U.ncard ≤ r)
    {s : ℕ} (hs_pos : 0 < s) (hs_le : s ≤ r) {S : Set (Fin s → A)} {σ : Fin s → V}
    (hdS : (canonicalLinearProgram L A r).Derives I ⟨s, hs_pos, hs_le, S⟩ σ)
    (hσ : Set.range σ ⊆ U)
    {n : ℕ} (hn_pos : 0 < n) (hn_le : n ≤ r) (R : Set (Fin n → A))
    (ρ : Fin n → V) (hρ : Set.range ρ ⊆ U)
    (cs : List (CSPConstraint L V))
    (hcs_mem : ∀ c ∈ cs, c ∈ I.constraints)
    (hcs_ar : ∀ c ∈ cs, c.arity ≤ r)
    (hcs_sc : ∀ c ∈ cs, Set.range c.scope ⊆ U)
    (hfwd : ∀ f : V → A, f ∘ σ ∈ S →
      (∀ c ∈ cs, Structure.RelMap c.rel (f ∘ c.scope)) → f ∘ ρ ∈ R) :
    (canonicalLinearProgram L A r).Derives I ⟨n, hn_pos, hn_le, R⟩ ρ := by
  classical
  have hUfin : U.Finite := I.finite_vars.subset hUsub
  have hUne : U.Nonempty := ⟨ρ ⟨0, hn_pos⟩, hρ ⟨⟨0, hn_pos⟩, rfl⟩⟩
  have hr_pos : 0 < r := lt_of_lt_of_le hn_pos hn_le
  let _ : Fintype U := hUfin.fintype
  have hcard : Fintype.card U ≤ r := by
    rwa [Set.ncard_eq_toFinset_card U hUfin, Set.Finite.card_toFinset] at hUcard
  let eU : Fin (Fintype.card U) ≃ U := (Fintype.equivFin U).symm
  let ω : Fin r → V := fun x ↦ if hx : x.1 < Fintype.card U then (eU ⟨x.1, hx⟩).1 else hUne.some
  let idx : (v : V) → v ∈ U → Fin r := fun v hv ↦
    let j := eU.symm ⟨v, hv⟩
    ⟨j.1, lt_of_lt_of_le j.2 hcard⟩
  have hω_idx : ∀ (v : V) (hv : v ∈ U), ω (idx v hv) = v := by
    intro v hv
    have hj : (eU.symm ⟨v, hv⟩).1 < Fintype.card U := (eU.symm ⟨v, hv⟩).2
    simp only [ω, idx, hj, ↓reduceDIte, Fin.eta, Equiv.apply_symm_apply]
  have hω_mem : ∀ x : Fin r, ω x ∈ I.vars := by
    intro x
    apply hUsub
    dsimp [ω]
    split_ifs with hx
    · exact (eU ⟨x.1, hx⟩).2
    · exact hUne.some_mem
  let τR : Fin n → Fin r := fun i ↦ idx (ρ i) (hρ ⟨i, rfl⟩)
  let τS : Fin s → Fin r := fun i ↦ idx (σ i) (hσ ⟨i, rfl⟩)
  let edbs :=
    (cs.attach.map fun ⟨c, hc⟩ ↦
      (⟨c.arity, c.rel, fun i ↦ idx (c.scope i) (hcs_sc c hc ⟨i, rfl⟩)⟩ : EDBAtom L (Fin r))).dedup
  let headRel : BoundedRel A r := ⟨n, hn_pos, hn_le, R⟩
  let bodyRel : BoundedRel A r := ⟨s, hs_pos, hs_le, S⟩
  let α : DatalogRule L (fun R : BoundedRel A r ↦ R.arity) (Fin r) :=
    DatalogRule.mkStep (idbArity := fun R : BoundedRel A r ↦ R.arity) headRel τR bodyRel τS edbs
  have hα_mem : α ∈ (canonicalLinearProgram L A r).rules := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · change (α.body.filter fun a ↦ a.isIdb = true).length ≤ 1
      rw [← DatalogProgram.length_bodyIdbs]
      change (⟨bodyRel, τS⟩ :: DatalogProgram.bodyIdbs (edbs.map EDBAtom.toAtom)).length ≤ 1
      rw [DatalogProgram.bodyIdbs_map_toAtom]
      exact le_rfl
    · refine List.nodup_cons.mpr ⟨?_, ?_⟩
      · intro h
        rcases List.mem_map.mp h with ⟨_, _, he⟩
        cases he
      · refine (List.nodup_dedup _).map ?_
        intro e₁ e₂ h
        rcases e₁ with ⟨_, _, _⟩
        rcases e₂ with ⟨_, _, _⟩
        cases h; rfl
    · intro e he
      change e ∈ DatalogProgram.bodyEdbs (edbs.map EDBAtom.toAtom) at he
      rw [DatalogProgram.bodyEdbs_map_toAtom] at he
      rcases List.mem_map.mp (List.mem_dedup.mp he) with ⟨⟨c, hc⟩, _, rfl⟩
      exact hcs_ar c hc
    · intro f hf
      by_cases hA : IsEmpty A
      · exact hA.elim (f ⟨0, hr_pos⟩)
      · rw [not_isEmpty_iff] at hA
        let F : V → A := fun v ↦ if hv : v ∈ U then f (idx v hv) else Classical.arbitrary A
        have hFρ : F ∘ ρ = f ∘ τR := funext fun i ↦ by simp [F, τR, hρ ⟨i, rfl⟩]
        have hFσ : F ∘ σ = f ∘ τS := funext fun i ↦ by simp [F, τS, hσ ⟨i, rfl⟩]
        change f ∘ τR ∈ R
        rw [← hFρ]
        refine hfwd F (hFσ.symm ▸ hf (.idb bodyRel τS) List.mem_cons_self) fun c hc ↦ ?_
        let e : EDBAtom L (Fin r) :=
          ⟨c.arity, c.rel, fun i ↦ idx (c.scope i) (hcs_sc c hc ⟨i, rfl⟩)⟩
        have hemem : e.toAtom ∈ α.body :=
          List.mem_cons_of_mem _ (List.mem_map.mpr ⟨e, List.mem_dedup.mpr
            (List.mem_map.mpr ⟨⟨c, hc⟩, List.mem_attach _ _, rfl⟩), rfl⟩)
        have harg : F ∘ c.scope = f ∘ e.scope := by
          ext i
          simp only [Function.comp_def, F, e, hcs_sc c hc ⟨i, rfl⟩, ↓reduceDIte]
        rw [harg]
        exact hf e.toAtom hemem
  have hωR : ω ∘ τR = ρ := funext fun i ↦ hω_idx (ρ i) (hρ ⟨i, rfl⟩)
  have hωS : ω ∘ τS = σ := funext fun i ↦ hω_idx (σ i) (hσ ⟨i, rfl⟩)
  rw [← hωR]
  refine DatalogProgram.Derives.step (P := canonicalLinearProgram L A r) α hα_mem ω hω_mem ?_ ?_
  · intro m T η hmem
    rcases List.mem_cons.mp hmem with h | h
    · cases h
    · rcases List.mem_map.mp h with ⟨e, he, heq⟩
      rcases e with ⟨_, _, _⟩
      cases heq
      rcases List.mem_map.mp (List.mem_dedup.mp he) with ⟨⟨c, hc⟩, _, hce⟩
      have hc_eq : (⟨c.arity, c.rel, ω ∘ fun i ↦ idx (c.scope i) (hcs_sc c hc ⟨i, rfl⟩)⟩ :
          CSPConstraint L V) = c := by
        cases c
        simp only [Function.comp_def, hω_idx]
      cases hce
      exact hc_eq.symm ▸ hcs_mem c hc
  · intro S' σ' hmem
    rcases List.mem_cons.mp hmem with h | h
    · cases h
      exact hωS.symm ▸ hdS
    · rcases List.mem_map.mp h with ⟨_, _, he⟩
      cases he

end CanonicalLinearHelpers

section DalmauTheorem

/-- Forward direction of Dalmau's theorem: if a linear Datalog program `P` decides `CSP(A)`, then
`A` has bounded pathwidth duality (specifically at most `max(1, |P.Var|) - 1`). -/
theorem hasBoundedPathwidthDuality_of_linearDatalog {L : FirstOrder.Language}
    {A : Type*} [L.Structure A] {P : DatalogProgram L} (hlin : P.IsLinear)
    (hdec : P.Decides A) :
    HasBoundedPathwidthDuality L A := by
  classical
  have := P.finite_var
  let _ : Fintype P.Var := Fintype.ofFinite P.Var
  let k : ℕ := Fintype.card P.Var
  let eVar : P.Var ≃ Fin k := Fintype.equivFin P.Var
  refine ⟨k, HasPathwidthDualityAtMost.of_forall fun n I hunsat ↦ ?_⟩
  have hgoal : P.DerivesGoal I := (hdec I).mpr hunsat
  rcases hgoal with ⟨G, ρG, hGgoal, hderG⟩
  obtain ⟨u₀, hinit, hpath⟩ := (hlin.derives_iff_chain I G ρG).mp hderG
  -- Unfold `hpath` inductively into a finite quotient of layer copies `Fin m × P.Var`.
  suffices H : ∀ (v : (S : P.IDB) × (Fin (P.idbArity S) → Fin n)),
      Relation.ReflTransGen (P.DerivationStep I) u₀ v →
      ∃ (m : ℕ) (W : Type) (finW : Fintype W) (J : CSPInstance L W)
        (U : Fin (m + 1) → Set W) (h : W → Fin n) (ψ : Fin (P.idbArity v.1) → W),
        J.vars = ⋃ i, U i ∧
        (∀ i, (U i).ncard ≤ k + 1) ∧
        (∀ ⦃i l j : Fin (m + 1)⦄, i < l → l < j → U i ∩ U j ⊆ U l) ∧
        (∀ c ∈ J.constraints, ∃ i, Set.range c.scope ⊆ U i) ∧
        (J.map h).IsSubinstance I ∧
        Set.range ψ ⊆ U (Fin.last m) ∧
        h ∘ ψ = v.2 ∧
        P.Derives J v.1 ψ by
    obtain ⟨m, W, finW, J, U, h, ψ, hvars, hcard, hrun, hsc, hsub, _, _, hdJ⟩ := H ⟨G, ρG⟩ hpath
    have hJgoal : P.DerivesGoal J := ⟨G, ψ, hGgoal, hdJ⟩
    have hJunsat : ¬ J.Satisfiable A := (hdec.derivesGoal_iff J).mp hJgoal
    have hJpw : J.HasPathwidthAtMost k :=
      ⟨m + 1, U, hvars.subset, fun i ↦ ⟨Set.toFinite _, hcard i⟩,
        fun i l j hil hlj x _ hxi hxj ↦ hrun hil hlj ⟨hxi, hxj⟩, hsc⟩
    exact ⟨W, J, h, hJunsat, hJpw, hsub⟩
  intro v hp
  induction hp with
  | refl =>
    rcases u₀ with ⟨S₀, σ₀⟩
    rcases hinit with ⟨r, hr, ω, hω, hbi, hbedb, hhead, hsc⟩
    cases hhead
    cases eq_of_heq hsc
    let C₀ : Set (CSPConstraint L (Fin k)) :=
      {c | ∃ e ∈ DatalogProgram.bodyEdbs r.body,
        c = ⟨e.arity, e.rel, fun i ↦ eVar (e.scope i)⟩}
    have hC₀_fin : C₀.Finite :=
      ((DatalogProgram.bodyEdbs r.body).toFinset : Set _).toFinite.image
        (fun e : EDBAtom L P.Var ↦
          (⟨e.arity, e.rel, fun i ↦ eVar (e.scope i)⟩ : CSPConstraint L (Fin k)))
        |>.subset fun c ⟨e, he, hc⟩ ↦ ⟨e, List.mem_toFinset.mpr he, hc.symm⟩
    let J₀ : CSPInstance L (Fin k) :=
      { vars := Set.univ
        constraints := C₀
        finite_vars := Set.finite_univ
        finite_constraints := hC₀_fin
        scope_mem := fun _ _ _ ↦ trivial }
    refine ⟨0, Fin k, inferInstance, J₀, fun _ ↦ Set.univ, fun x ↦ ω (eVar.symm x),
      fun i ↦ eVar (r.headScope i), (Set.iUnion_const Set.univ).symm, ?_, ?_, ?_, ?_, ?_,
      by ext i; simp, ?_⟩
    · intro _
      dsimp only
      rw [Set.ncard_univ, Nat.card_fin]
      omega
    · intro i l j hil hlj
      omega
    · intro c _
      exact ⟨0, fun _ _ ↦ trivial⟩
    · refine ⟨?_, ?_⟩
      · rw [CSPInstance.map_vars]
        rintro _ ⟨x, _, rfl⟩
        exact hω (eVar.symm x)
      · rw [CSPInstance.map_constraints]
        rintro _ ⟨_, ⟨e, he, rfl⟩, rfl⟩
        have hcomp : ((fun x ↦ ω (eVar.symm x)) ∘ fun i ↦ eVar (e.scope i)) = ω ∘ e.scope :=
          funext fun i ↦ by simp
        change (⟨e.arity, e.rel, (fun x ↦ ω (eVar.symm x)) ∘ fun i ↦ eVar (e.scope i)⟩ :
          CSPConstraint L (Fin n)) ∈ I.constraints
        rw [hcomp]; exact hbedb e he
    · intro _ _
      exact trivial
    · have hmem := DatalogProgram.mem_body_iff r.body
      exact DatalogProgram.Derives.step r hr eVar (fun _ ↦ trivial)
        (fun _ T τ ht ↦ ⟨⟨_, T, τ⟩, (hmem.2 _ T τ).mp ht, rfl⟩)
        (fun S σ hs ↦ by have := (hmem.1 S σ).mp hs; simp [hbi] at this)
  | @tail u w _ hstep ih =>
    obtain ⟨m, W, finW, J, U, h, ψ, hvars, hcard, hrun, hsc, hsub, hψU, hψh, hdJ⟩ := ih
    let _ : Fintype W := finW
    rcases hstep with ⟨r, hr, ω, S, η, hω, hbi, hbedb, hu, hw⟩
    rcases u with ⟨uR, uρ⟩
    rcases w with ⟨wR, wρ⟩
    cases hu
    cases hw
    dsimp at hψh hψU hdJ
    let rel : W ⊕ Fin k → W ⊕ Fin k → Prop := fun a b ↦
      ∃ i : Fin (P.idbArity S), a = Sum.inl (ψ i) ∧ b = Sum.inr (eVar (η i))
    let s : Setoid (W ⊕ Fin k) := Relation.EqvGen.setoid rel
    let W' : Type := Quotient s
    have hcompat : ∀ a b, rel a b → Sum.elim h (fun x : Fin k ↦ ω (eVar.symm x)) a =
        Sum.elim h (fun x : Fin k ↦ ω (eVar.symm x)) b := by
      rintro _ _ ⟨i, rfl, rfl⟩
      simpa [Function.comp_def] using congrFun hψh i
    have heqv_compat : ∀ a b, s.r a b → Sum.elim h (fun x : Fin k ↦ ω (eVar.symm x)) a =
        Sum.elim h (fun x : Fin k ↦ ω (eVar.symm x)) b := by
      intro a b hab
      induction hab with
      | rel x y hxy => exact hcompat x y hxy
      | refl _ => rfl
      | symm _ _ _ ih' => exact ih'.symm
      | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂
    let h' : W' → Fin n :=
      Quotient.lift (Sum.elim h (fun x : Fin k ↦ ω (eVar.symm x))) heqv_compat
    let inL : W → W' := fun x ↦ Quotient.mk s (Sum.inl x)
    let inR : P.Var → W' := fun x ↦ Quotient.mk s (Sum.inr (eVar x))
    have hglue : inR ∘ η = inL ∘ ψ := funext fun i ↦
      Quotient.sound (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ ⟨i, rfl, rfl⟩))
    have hsep : ∀ a b, s.r a b →
        (∀ x x', a = Sum.inl x → b = Sum.inl x' →
          x = x' ∨ (x ∈ U (Fin.last m) ∧ x' ∈ U (Fin.last m))) ∧
        (∀ x y, a = Sum.inl x → b = Sum.inr y → x ∈ U (Fin.last m)) ∧
        (∀ y x, a = Sum.inr y → b = Sum.inl x → x ∈ U (Fin.last m)) := by
      intro a b hab
      induction hab with
      | rel a₀ b₀ hrel =>
        rcases hrel with ⟨i, rfl, rfl⟩
        exact ⟨by simp, fun x _ hx _ ↦ by cases hx; exact hψU ⟨i, rfl⟩, by simp⟩
      | refl a₀ =>
        refine ⟨fun x x' h1 h2 ↦ Or.inl (by cases h1; cases h2; rfl),
          fun _ _ h1 h2 ↦ ?_, fun _ _ h1 h2 ↦ ?_⟩
        · cases h1.symm.trans h2
        · cases h1.symm.trans h2
      | symm _ _ _ ih' =>
        exact ⟨fun x x' h1 h2 ↦ (ih'.1 x' x h2 h1).imp Eq.symm And.symm,
          fun x y h1 h2 ↦ ih'.2.2 y x h2 h1,
          fun y x h1 h2 ↦ ih'.2.1 x y h2 h1⟩
      | trans a₀ b₀ c₀ _ _ ih₁ ih₂ =>
        cases b₀ with
        | inl z =>
          refine ⟨fun x x' h1 h2 ↦ ?_, fun x y h1 h2 ↦ ?_, fun y x h1 h2 ↦ ?_⟩
          · rcases ih₁.1 x z h1 rfl with rfl | ⟨hx, hz⟩
            · exact ih₂.1 x x' rfl h2
            · rcases ih₂.1 z x' rfl h2 with rfl | ⟨_, hx'⟩
              · exact Or.inr ⟨hx, hz⟩
              · exact Or.inr ⟨hx, hx'⟩
          · rcases ih₁.1 x z h1 rfl with rfl | ⟨hx, _⟩
            · exact ih₂.2.1 x y rfl h2
            · exact hx
          · rcases ih₂.1 z x rfl h2 with rfl | ⟨_, hx⟩
            · exact ih₁.2.2 y z h1 rfl
            · exact hx
        | inr z =>
          exact ⟨fun x x' h1 h2 ↦ Or.inr ⟨ih₁.2.1 x z h1 rfl, ih₂.2.2 z x' rfl h2⟩,
            fun x _ h1 _ ↦ ih₁.2.1 x z h1 rfl,
            fun _ x _ h2 ↦ ih₂.2.2 z x rfl h2⟩
    let U' : Fin (m + 2) → Set W' :=
      Fin.lastCases (Set.range inR) (fun i ↦ inL '' U i)
    let newCs : Set (CSPConstraint L W') :=
      {c | ∃ e ∈ DatalogProgram.bodyEdbs r.body, c = ⟨e.arity, e.rel, inR ∘ e.scope⟩}
    have hnewCs_fin : newCs.Finite :=
      ((DatalogProgram.bodyEdbs r.body).toFinset : Set _).toFinite.image
        (fun e : EDBAtom L P.Var ↦ (⟨e.arity, e.rel, inR ∘ e.scope⟩ : CSPConstraint L W'))
        |>.subset fun c ⟨e, he, hc⟩ ↦ ⟨e, List.mem_toFinset.mpr he, hc.symm⟩
    let _ : DecidableRel s.r := fun _ _ ↦ Classical.propDecidable _
    let finW' : Fintype W' := Quotient.fintype s
    let J' : CSPInstance L W' :=
      { vars := (inL '' J.vars) ∪ Set.range inR
        constraints := (CSPConstraint.map inL '' J.constraints) ∪ newCs
        finite_vars := (J.finite_vars.image inL).union (Set.toFinite (Set.range inR))
        finite_constraints := (J.finite_constraints.image _).union hnewCs_fin
        scope_mem := by
          rintro c (⟨c₀, hc₀, rfl⟩ | ⟨e, _, rfl⟩) i
          · exact Or.inl ⟨c₀.scope i, J.scope_mem hc₀ i, rfl⟩
          · exact Or.inr ⟨e.scope i, rfl⟩ }
    dsimp
    refine ⟨m + 1, W', finW', J', U', h', inR ∘ r.headScope, ?_, ?_, ?_, ?_, ?_, ?_,
      by ext i; simp [h', inR], ?_⟩
    · -- `J'.vars = ⋃ i, U' i`
      ext q
      simp only [J', Set.mem_union, Set.mem_iUnion]
      constructor
      · rintro (⟨x, hx, rfl⟩ | hq)
        · rw [hvars] at hx
          obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
          exact ⟨i.castSucc, by simpa [U', Fin.lastCases_castSucc] using ⟨x, hi, rfl⟩⟩
        · exact ⟨Fin.last (m + 1), by simpa [U', Fin.lastCases_last] using hq⟩
      · rintro ⟨i, hi⟩
        cases i using Fin.lastCases with
        | last =>
          simp only [U', Fin.lastCases_last] at hi
          exact Or.inr hi
        | cast j =>
          simp only [U', Fin.lastCases_castSucc] at hi
          rcases hi with ⟨x, hx, rfl⟩
          exact Or.inl ⟨x, hvars ▸ Set.mem_iUnion.mpr ⟨j, hx⟩, rfl⟩
    · -- Bag sizes `≤ k + 1`
      intro i
      cases i using Fin.lastCases with
      | last =>
        simp only [U', Fin.lastCases_last]
        rw [← Set.image_univ]
        exact (Set.ncard_image_le (Set.finite_univ : (Set.univ : Set P.Var).Finite)).trans
          (by simp [Set.ncard_univ, Nat.card_eq_fintype_card, k])
      | cast j =>
        simp only [U', Fin.lastCases_castSucc]
        exact (Set.ncard_image_le (Set.toFinite _)).trans (hcard j)
    · -- Running intersection property on `U'`
      intro i l j hil hlj q ⟨hqi, hqj⟩
      cases i using Fin.lastCases with
      | last => exact absurd hil (not_lt_of_ge (Fin.le_last l))
      | cast i₀ =>
        cases j using Fin.lastCases with
        | last =>
          cases l using Fin.lastCases with
          | last => exact absurd hlj (lt_irrefl _)
          | cast l₀ =>
            simp only [U', Fin.lastCases_castSucc] at hqi ⊢
            simp only [U', Fin.lastCases_last] at hqj
            rcases hqi with ⟨x, hxi, rfl⟩
            rcases hqj with ⟨y, hy⟩
            have hsr : s.r (Sum.inl x) (Sum.inr (eVar y)) := Quotient.exact hy.symm
            have hxm : x ∈ U (Fin.last m) := (hsep _ _ hsr).2.1 x (eVar y) rfl rfl
            have hil₀ : i₀ < l₀ := Fin.castSucc_lt_castSucc_iff.mp hil
            rcases eq_or_lt_of_le (Fin.le_last l₀) with hl_eq | hl_lt
            · exact ⟨x, hl_eq ▸ hxm, rfl⟩
            · exact ⟨x, hrun hil₀ hl_lt ⟨hxi, hxm⟩, rfl⟩
        | cast j₀ =>
          cases l using Fin.lastCases with
          | last => exact absurd hlj (not_lt_of_ge (Fin.le_last j₀.castSucc))
          | cast l₀ =>
            have hil₀ : i₀ < l₀ := Fin.castSucc_lt_castSucc_iff.mp hil
            have hlj₀ : l₀ < j₀ := Fin.castSucc_lt_castSucc_iff.mp hlj
            simp only [U', Fin.lastCases_castSucc] at hqi hqj ⊢
            rcases hqi with ⟨x, hxi, rfl⟩
            rcases hqj with ⟨x', hxj, hxx'⟩
            have hsr : s.r (Sum.inl x) (Sum.inl x') := Quotient.exact hxx'.symm
            rcases (hsep _ _ hsr).1 x x' rfl rfl with rfl | ⟨hxm, _⟩
            · exact ⟨x, hrun hil₀ hlj₀ ⟨hxi, hxj⟩, rfl⟩
            · have hl_lt : l₀ < Fin.last m := lt_of_lt_of_le hlj₀ (Fin.le_last j₀)
              exact ⟨x, hrun hil₀ hl_lt ⟨hxi, hxm⟩, rfl⟩
    · -- Constraint scope coverage
      rintro c (⟨c₀, hc₀, rfl⟩ | ⟨e, _, rfl⟩)
      · obtain ⟨i, hi⟩ := hsc c₀ hc₀
        refine ⟨i.castSucc, ?_⟩
        simp only [U', Fin.lastCases_castSucc]
        rintro _ ⟨t, rfl⟩
        exact ⟨c₀.scope t, hi ⟨t, rfl⟩, rfl⟩
      · refine ⟨Fin.last (m + 1), ?_⟩
        simp only [U', Fin.lastCases_last]
        rintro _ ⟨t, rfl⟩
        exact ⟨e.scope t, rfl⟩
    · -- `(J'.map h').IsSubinstance I`
      refine ⟨?_, ?_⟩
      · rw [CSPInstance.map_vars]
        rintro _ ⟨q, (⟨x, hx, rfl⟩ | ⟨y, rfl⟩), rfl⟩
        · exact hsub.1 (by rw [CSPInstance.map_vars]; exact ⟨x, hx, rfl⟩)
        · simpa [h', inR] using hω y
      · rw [CSPInstance.map_constraints]
        rintro _ ⟨c, (⟨c₀, hc₀, rfl⟩ | ⟨e, he, rfl⟩), rfl⟩
        · exact hsub.2 (by rw [CSPInstance.map_constraints]; exact ⟨c₀, hc₀, rfl⟩)
        · have hcomp : (h' ∘ inR ∘ e.scope) = ω ∘ e.scope := funext fun t ↦ by simp [h', inR]
          change (⟨e.arity, e.rel, h' ∘ inR ∘ e.scope⟩ : CSPConstraint L (Fin n)) ∈ I.constraints
          rw [hcomp]; exact hbedb e he
    · -- `Set.range (inR ∘ r.headScope) ⊆ U' (Fin.last (m + 1))`
      simp only [U', Fin.lastCases_last]
      rintro _ ⟨t, rfl⟩
      exact ⟨r.headScope t, rfl⟩
    · -- `P.Derives J' r.head (inR ∘ r.headScope)`
      have hsubL : (J.map inL).IsSubinstance J' := by
        refine ⟨?_, ?_⟩
        · rw [CSPInstance.map_vars]; exact Set.subset_union_left
        · rw [CSPInstance.map_constraints]; exact Set.subset_union_left
      have hdS : P.Derives J' S (inL ∘ ψ) := hdJ.map hsubL
      rw [← hglue] at hdS
      have hmem := DatalogProgram.mem_body_iff r.body
      refine DatalogProgram.Derives.step r hr inR (fun x ↦ Or.inr ⟨x, rfl⟩)
        (fun _ T τ ht ↦ Or.inr ⟨⟨_, T, τ⟩, (hmem.2 _ T τ).mp ht, rfl⟩)
        (fun S' σ' hs ↦ ?_)
      have hm := (hmem.1 S' σ').mp hs
      rw [hbi, List.mem_singleton] at hm
      cases hm
      exact hdS

/-- Converse direction of Dalmau's theorem: if a finite `L`-structure `A` with
`[IsFinitePosRelational L]` has pathwidth duality at most `k`, then `canonicalLinearProgram L A
(k + 1)` decides `CSP(A)`. -/
theorem canonicalLinearProgram_decides_of_pathwidthDuality
    {L : FirstOrder.Language} [IsFinitePosRelational L]
    {A : Type*} [L.Structure A] [Finite A] {k : ℕ}
    (hdual : HasPathwidthDualityAtMost L A k) :
    (canonicalLinearProgram L A (k + 1)).Decides A := by
  classical
  intro n I
  refine ⟨canonicalLinearProgram_unsatisfiable_of_derivesGoal, fun hunsat ↦ ?_⟩
  -- Handle empty universe `A` directly via the empty full unary relation `Set.univ = ∅`.
  by_cases hA : IsEmpty A
  · obtain ⟨v, hv⟩ := CSPInstance.vars_nonempty_of_not_satisfiable hunsat
    have hd := canonicalLinearDerives_of_init (L := L) (A := A) (r := k + 1) (I := I)
      (U := {v}) (Set.singleton_subset_iff.mpr hv) (by simp)
      (by decide : 0 < 1) (Nat.succ_le_succ (Nat.zero_le k)) (∅ : Set (Fin 1 → A))
      (fun _ ↦ v) (by simp) [] (by simp) (by simp) (by simp)
      (fun f _ ↦ hA.elim (f v))
    exact ⟨⟨1, by decide, Nat.succ_le_succ (Nat.zero_le k), ∅⟩, fun _ ↦ v, rfl, hd⟩
  · rw [not_isEmpty_iff] at hA
    -- Step 1: Pass to an injective-scope unsatisfiable cover `Ĩ`, then a pathwidth-`≤ k`
    -- unsatisfiable obstruction `J` whose constraints all have arity `≤ k + 1`.
    obtain ⟨N, Itilde, π, hIt_unsat, hIt_sub, hIt_inj⟩ :=
      CSPInstance.exists_injective_scope_cover hunsat
    obtain ⟨M, J, h, hJ_unsat, hJ_pw, hJ_sub⟩ := hdual Itilde hIt_unsat
    have hcomp_sub : (J.map (π ∘ h)).IsSubinstance I := by
      refine ⟨?_, ?_⟩
      · rw [CSPInstance.map_vars]
        rintro _ ⟨x, hx, rfl⟩
        exact hIt_sub.1 (by
          rw [CSPInstance.map_vars]
          exact ⟨h x, hJ_sub.1 (by rw [CSPInstance.map_vars]; exact ⟨x, hx, rfl⟩), rfl⟩)
      · rw [CSPInstance.map_constraints]
        rintro _ ⟨c, hc, rfl⟩
        exact hIt_sub.2 (by
          rw [CSPInstance.map_constraints]
          exact ⟨c.map h, hJ_sub.2 (by rw [CSPInstance.map_constraints]; exact ⟨c, hc, rfl⟩),
            CSPConstraint.map_comp π h c⟩)
    suffices hJgoal : (canonicalLinearProgram L A (k + 1)).DerivesGoal J from
      hJgoal.map hcomp_sub
    obtain ⟨m, U, hUsub, hUcov, hUcard, hUrun, hUsc⟩ := hJ_pw.exists_subset_vars
    have hJar : ∀ c ∈ J.constraints, c.arity ≤ k + 1 := by
      intro c hc
      have hcinj : Function.Injective c.scope := by
        have hinc : Function.Injective (h ∘ c.scope) :=
          hIt_inj (c.map h) (hJ_sub.2 (by rw [CSPInstance.map_constraints]; exact ⟨c, hc, rfl⟩))
        exact Function.Injective.of_comp hinc
      obtain ⟨i, hi⟩ := hUsc hc
      have hrc : (Set.range c.scope).ncard = c.arity := by
        rw [Set.ncard_range_of_injective hcinj, Nat.card_fin]
      rw [← hrc]
      exact (Set.ncard_le_ncard hi (hUcard i).1).trans (hUcard i).2
    have hJne : J.vars.Nonempty := CSPInstance.vars_nonempty_of_not_satisfiable hJ_unsat
    have hm_pos : 0 < m := by
      rcases m with _ | m'
      · obtain ⟨v, hv⟩ := hJne
        rw [← hUcov] at hv
        simp at hv
      · exact Nat.succ_pos m'
    -- Pad empty bags with a fixed variable `v₀ ∈ U i₀`? Wait: inserting `v₀` could break
    -- running intersection; instead filter out empty bags `U i`.
    let nonempIdx : List (Fin m) := (List.finRange m).filter fun i ↦ decide (U i).Nonempty
    have hne_len : 0 < nonempIdx.length := by
      obtain ⟨v, hv⟩ := hJne
      rw [← hUcov] at hv
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hv
      have him : i ∈ nonempIdx :=
        List.mem_filter.mpr ⟨List.mem_finRange i, decide_eq_true ⟨v, hi⟩⟩
      exact List.length_pos_of_mem him
    let b : ℕ := nonempIdx.length
    let B : Fin b → Set (Fin M) := fun t ↦ U (nonempIdx.get t)
    have hBne : ∀ t : Fin b, (B t).Nonempty := by
      intro t
      have hm' := List.get_mem nonempIdx t
      exact of_decide_eq_true (List.mem_filter.mp hm').2
    have hBsub : ∀ t : Fin b, B t ⊆ J.vars := fun t ↦ hUsub _
    have hBcard : ∀ t : Fin b, (B t).ncard ≤ k + 1 := fun t ↦ (hUcard _).2
    have hBmono : StrictMono nonempIdx.get := by
      have hpw : nonempIdx.Pairwise (· < ·) :=
        (List.pairwise_lt_finRange m).filter _
      intro i j hij
      exact List.pairwise_iff_get.mp hpw i j hij
    have hBrun : ∀ ⦃i l j : Fin b⦄, i ≤ l → l ≤ j → B i ∩ B j ⊆ B l :=
      fun _ _ _ hil hlj ↦ hUrun (hBmono.monotone hil) (hBmono.monotone hlj)
    have hBcov : (⋃ t, B t) = J.vars := by
      ext v
      simp only [Set.mem_iUnion]
      refine ⟨fun ⟨t, ht⟩ ↦ hBsub t ht, fun hv ↦ ?_⟩
      rw [← hUcov] at hv
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hv
      have him : i ∈ nonempIdx :=
        List.mem_filter.mpr ⟨List.mem_finRange i, decide_eq_true ⟨v, hi⟩⟩
      obtain ⟨t, ht⟩ := List.mem_iff_get.mp him
      exact ⟨t, by dsimp only [B]; rwa [ht]⟩
    have hBsc : ∀ c ∈ J.constraints, ∃ t : Fin b, Set.range c.scope ⊆ B t := by
      intro c hc
      obtain ⟨i, hi⟩ := hUsc hc
      have hpos := IsFinitePosRelational.arity_pos c.rel
      have hine : (U i).Nonempty := ⟨c.scope ⟨0, hpos⟩, hi ⟨⟨0, hpos⟩, rfl⟩⟩
      have him : i ∈ nonempIdx :=
        List.mem_filter.mpr ⟨List.mem_finRange i, decide_eq_true hine⟩
      obtain ⟨t, ht⟩ := List.mem_iff_get.mp him
      exact ⟨t, by dsimp only [B]; rwa [ht]⟩
    let prefVars (t : Fin b) : Set (Fin M) := ⋃ s ≤ t, B s
    let bagCs (t : Fin b) : List (CSPConstraint L (Fin M)) :=
      (J.finite_constraints.toFinset.toList).filter fun c ↦ decide (Set.range c.scope ⊆ B t)
    let prefSol (t : Fin b) (f : Fin M → A) : Prop :=
      ∀ s ≤ t, ∀ c ∈ bagCs s, Structure.RelMap c.rel (f ∘ c.scope)
    have hpref_congr : ∀ (t : Fin b) {f g : Fin M → A},
        (∀ v ∈ prefVars t, f v = g v) → prefSol t f → prefSol t g := by
      intro t f g hfg hf s hst c hc
      have hsc : Set.range c.scope ⊆ B s := of_decide_eq_true (List.mem_filter.mp hc).2
      have harg : g ∘ c.scope = f ∘ c.scope := by
        ext i
        exact (hfg (c.scope i) (Set.mem_iUnion₂.mpr ⟨s, hst, hsc ⟨i, rfl⟩⟩)).symm
      rw [harg]
      exact hf s hst c hc
    let enumSet (S : Set (Fin M)) : Fin S.ncard → Fin M := fun i ↦
      (((Set.toFinite S).toFinset.equivFin.symm
        ⟨i.1, by simpa [Set.ncard_eq_toFinset_card'] using i.2⟩) : Fin M)
    have henum_mem : ∀ (S : Set (Fin M)) (i : Fin S.ncard), enumSet S i ∈ S := by
      intro S i
      have hm := ((Set.toFinite S).toFinset.equivFin.symm
        ⟨i.1, by simpa [Set.ncard_eq_toFinset_card'] using i.2⟩).2
      exact (Set.Finite.mem_toFinset _).mp hm
    have henum_range : ∀ S : Set (Fin M), Set.range (enumSet S) = S := by
      intro S
      ext v
      refine ⟨fun ⟨i, hi⟩ ↦ hi ▸ henum_mem S i, fun hv ↦ ?_⟩
      have hv' : v ∈ (Set.toFinite S).toFinset := (Set.Finite.mem_toFinset _).mpr hv
      let j := (Set.toFinite S).toFinset.equivFin ⟨v, hv'⟩
      refine ⟨⟨j.1, by simpa [Set.ncard_eq_toFinset_card'] using j.2⟩, ?_⟩
      simp [enumSet, j]
    let Srel (t : Fin b) : Set (Fin (B t).ncard → A) :=
      {u | ∃ f : Fin M → A, prefSol t f ∧ f ∘ enumSet (B t) = u}
    have hBpos : ∀ t : Fin b, 0 < (B t).ncard :=
      fun t ↦ (Set.ncard_pos (Set.toFinite _)).mpr (hBne t)
    have hbag_cs : ∀ (t : Fin b),
        (∀ c ∈ bagCs t, c ∈ J.constraints) ∧
        (∀ c ∈ bagCs t, c.arity ≤ k + 1) ∧
        (∀ c ∈ bagCs t, Set.range c.scope ⊆ B t) := by
      intro t
      refine ⟨fun c hc ↦ ?_, fun c hc ↦ ?_, fun c hc ↦ ?_⟩
      · exact (Set.Finite.mem_toFinset _).mp (Finset.mem_toList.mp (List.mem_filter.mp hc).1)
      · exact hJar c ((Set.Finite.mem_toFinset _).mp
          (Finset.mem_toList.mp (List.mem_filter.mp hc).1))
      · exact of_decide_eq_true (List.mem_filter.mp hc).2
    -- Prove by induction on `t` that either `DerivesGoal J` or `Derives J (Srel t) (enumSet (B
    -- t))`.
    have hsweep : ∀ (idx : ℕ) (hidx : idx < b),
        (canonicalLinearProgram L A (k + 1)).DerivesGoal J ∨
        (canonicalLinearProgram L A (k + 1)).Derives J
          ⟨(B ⟨idx, hidx⟩).ncard, hBpos ⟨idx, hidx⟩, hBcard ⟨idx, hidx⟩, Srel ⟨idx, hidx⟩⟩
          (enumSet (B ⟨idx, hidx⟩)) := by
      intro idx hidx
      induction idx with
      | zero =>
        let t₀ : Fin b := ⟨0, hidx⟩
        right
        exact canonicalLinearDerives_of_init (hBsub t₀) (hBcard t₀) (hBpos t₀) (hBcard t₀)
          (Srel t₀) (enumSet (B t₀)) (henum_range (B t₀)).subset (bagCs t₀)
          (hbag_cs t₀).1 (hbag_cs t₀).2.1 (hbag_cs t₀).2.2 fun f hf ↦
            ⟨f, fun s hs c hc ↦ by
              have hs0 : s = t₀ := Fin.ext (Nat.eq_zero_of_le_zero hs)
              subst hs0; exact hf c hc, rfl⟩
      | succ idx ih =>
        let t₁ : Fin b := ⟨idx, by omega⟩
        let t₂ : Fin b := ⟨idx + 1, hidx⟩
        rcases ih (by omega) with hgoal | hdt₁
        · exact Or.inl hgoal
        · by_cases hempty : Srel t₁ = ∅
          · exact Or.inl ⟨_, _, hempty, hdt₁⟩
          · obtain ⟨u₀, f₀, hf₀, _⟩ := Set.nonempty_iff_ne_empty.mpr hempty
            let Z : Set (Fin M) := B t₁ ∩ B t₂
            have hsep_pref : prefVars t₁ ∩ B t₂ = Z := by
              ext v
              simp only [prefVars, Set.mem_inter_iff, Set.mem_iUnion, exists_prop, Z]
              refine ⟨fun ⟨⟨s, hst₁, hvs⟩, hvt₂⟩ ↦ ⟨?_, hvt₂⟩,
                fun ⟨hv₁, hv₂⟩ ↦ ⟨⟨t₁, le_rfl, hv₁⟩, hv₂⟩⟩
              exact hBrun hst₁ (by change idx ≤ idx + 1; omega) ⟨hvs, hvt₂⟩
            by_cases hZ : Z.Nonempty
            · right
              have hZpos : 0 < Z.ncard := (Set.ncard_pos (Set.toFinite _)).mpr hZ
              have hZle : Z.ncard ≤ k + 1 :=
                (Set.ncard_le_ncard Set.inter_subset_left (Set.toFinite _)).trans (hBcard t₁)
              let Trel : Set (Fin Z.ncard → A) :=
                {u | ∃ f : Fin M → A, prefSol t₁ f ∧ f ∘ enumSet Z = u}
              -- Forget step inside `B t₁`: `Srel t₁ → Trel`.
              have hdT := canonicalLinearDerives_of_step (hBsub t₁) (hBcard t₁)
                (hBpos t₁) (hBcard t₁) hdt₁ (henum_range (B t₁)).subset
                hZpos hZle Trel (enumSet Z)
                ((henum_range Z).subset.trans Set.inter_subset_left) []
                (by simp) (by simp) (by simp)
                (fun f ⟨g, hg, hge⟩ _ ↦ ⟨g, hg, by
                  ext i
                  have hzi : enumSet Z i ∈ B t₁ := (henum_mem Z i).1
                  obtain ⟨j, hj⟩ := (henum_range (B t₁)).symm.subset hzi
                  have h := congrFun hge j
                  dsimp only [Function.comp_def] at h ⊢
                  rwa [hj] at h⟩)
              -- Introduce + constrain step inside `B t₂`: `Trel ∧ bagCs t₂ → Srel t₂`.
              exact canonicalLinearDerives_of_step (hBsub t₂) (hBcard t₂)
                hZpos hZle hdT ((henum_range Z).subset.trans Set.inter_subset_right)
                (hBpos t₂) (hBcard t₂) (Srel t₂) (enumSet (B t₂))
                (henum_range (B t₂)).subset (bagCs t₂)
                (hbag_cs t₂).1 (hbag_cs t₂).2.1 (hbag_cs t₂).2.2
                (fun f ⟨g, hg, hge⟩ hfcs ↦ by
                  let hglue : Fin M → A := fun v ↦ if v ∈ B t₂ then f v else g v
                  have hglue_g : ∀ v ∈ prefVars t₁, hglue v = g v := by
                    intro v hv
                    dsimp [hglue]
                    split_ifs with hv₂
                    · have hvZ : v ∈ Z := hsep_pref ▸ ⟨hv, hv₂⟩
                      obtain ⟨i, hi⟩ := (henum_range Z).symm.subset hvZ
                      have h := (congrFun hge i).symm
                      dsimp only [Function.comp_def] at h
                      rwa [hi] at h
                    · rfl
                  refine ⟨hglue, ?_, funext fun i ↦ by
                    simp only [Function.comp_def, hglue, henum_mem (B t₂) i, ↓reduceIte]⟩
                  intro s hs c hc
                  rcases eq_or_lt_of_le (show s.1 ≤ idx + 1 from hs) with hseq | hslt
                  · have hst₂ : s = t₂ := Fin.ext hseq
                    subst hst₂
                    have harg : hglue ∘ c.scope = f ∘ c.scope := by
                      ext i
                      simp only [Function.comp_def, hglue, (hbag_cs t₂).2.2 c hc ⟨i, rfl⟩,
                        ↓reduceIte]
                    rw [harg]
                    exact hfcs c hc
                  · exact hpref_congr t₁ (fun v hv ↦ (hglue_g v hv).symm) hg s
                      (show s.1 ≤ idx by omega) c hc)
            · -- Disjoint case `Z = ∅`: glue with `f₀` directly using a `0`-IDB rule on `B t₂`.
              right
              have hZempty : Z = ∅ := Set.not_nonempty_iff_eq_empty.mp hZ
              exact canonicalLinearDerives_of_init (hBsub t₂) (hBcard t₂)
                (hBpos t₂) (hBcard t₂) (Srel t₂) (enumSet (B t₂))
                (henum_range (B t₂)).subset (bagCs t₂)
                (hbag_cs t₂).1 (hbag_cs t₂).2.1 (hbag_cs t₂).2.2
                (fun f hfcs ↦ by
                  let hglue : Fin M → A := fun v ↦ if v ∈ B t₂ then f v else f₀ v
                  have hglue_f₀ : ∀ v ∈ prefVars t₁, hglue v = f₀ v := by
                    intro v hv
                    dsimp [hglue]
                    split_ifs with hv₂
                    · have : v ∈ (∅ : Set (Fin M)) := hZempty ▸ hsep_pref ▸ ⟨hv, hv₂⟩
                      exact False.elim this
                    · rfl
                  refine ⟨hglue, ?_, funext fun i ↦ by
                    simp only [Function.comp_def, hglue, henum_mem (B t₂) i, ↓reduceIte]⟩
                  intro s hs c hc
                  rcases eq_or_lt_of_le (show s.1 ≤ idx + 1 from hs) with hseq | hslt
                  · have hst₂ : s = t₂ := Fin.ext hseq
                    subst hst₂
                    have harg : hglue ∘ c.scope = f ∘ c.scope := by
                      ext i
                      simp only [Function.comp_def, hglue, (hbag_cs t₂).2.2 c hc ⟨i, rfl⟩,
                        ↓reduceIte]
                    rw [harg]
                    exact hfcs c hc
                  · exact hpref_congr t₁ (fun v hv ↦ (hglue_f₀ v hv).symm) hf₀ s
                      (show s.1 ≤ idx by omega) c hc)
    let tLast : Fin b := ⟨b - 1, by omega⟩
    rcases hsweep (b - 1) (by omega) with hgoal | hdLast
    · exact hgoal
    · refine ⟨_, _, ?_, hdLast⟩
      ext u
      simp only [Set.mem_empty_iff_false, iff_false]
      rintro ⟨f, hf, _⟩
      apply hJ_unsat
      rw [CSPInstance.satisfiable_iff_exists_total]
      refine ⟨f, fun c hc ↦ ?_⟩
      obtain ⟨t, ht⟩ := hBsc c hc
      have hcb : c ∈ bagCs t := List.mem_filter.mpr
        ⟨Finset.mem_toList.mpr ((Set.Finite.mem_toFinset _).mpr hc), decide_eq_true ht⟩
      exact hf t (show t.1 ≤ b - 1 by omega) c hcb

/-- **Dalmau's Theorem**: a finite relational structure `A` over a finite positive-arity
relational signature `L` has bounded pathwidth duality if and only if there exists a linear Datalog
program deciding `CSP(A)`.
-/
theorem hasBoundedPathwidthDuality_iff_exists_linearDatalog.{u, u₁, u₂}
    (L : FirstOrder.Language.{u₁, u₂}) [IsFinitePosRelational L]
    (A : Type u) [L.Structure A] [Finite A] :
    HasBoundedPathwidthDuality L A ↔
      ∃ P : DatalogProgram.{u} L, P.IsLinear ∧ P.Decides A :=
  ⟨fun ⟨k, hk⟩ ↦
    ⟨canonicalLinearProgram L A (k + 1), canonicalLinearProgram_isLinear L A (k + 1),
      canonicalLinearProgram_decides_of_pathwidthDuality hk⟩,
    fun ⟨_, hlin, hdec⟩ ↦ hasBoundedPathwidthDuality_of_linearDatalog hlin hdec⟩

end DalmauTheorem

end CslibFrontier.Logics
