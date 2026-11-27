/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Papers Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CSP.MaxCSP
public import Mathlib.Analysis.InnerProductSpace.PiL2

import Mathlib.Data.Finset.Sort

/-!
# Trevisan's $k$-Conjunction Reduction and Makarychev–Makarychev SDP Relaxation for `Max-CSP`

This module formalizes two general building blocks for Boolean `Max-k-CSP` approximation in
`CslibFrontier`:

1. **Variable-Padded Trevisan Conjunction Compilation (`toConjunctionInstance`)**: compiles any
   Boolean `Cslib.Logic.PL.WeightedMaxCSP Rel ℕ ℝ` (with scope lengths `≤ k`, nonnegative weights,
   and occurring variables `< F.numVars`) into an instance of exact-$k$-literal conjunctions on
   `F.numVars + F.constraints.length * k` variables with at most `F.constraints.length * 2 ^ k`
   conjunctions, preserving the exact weighted score of every assignment
   (`val_toConjunctionInstance`) and the exact optimum (`opt_toConjunctionInstance`).
2. **Makarychev–Makarychev Semidefinite Relaxation (`ConjunctionSDPSolution`)**: defines feasible
   vector solutions `(v, z)` on any real inner product space together with the integral assignment
   embedding (`integralConjunctionSDPSolution`, `obj_integralConjunctionSDPSolution`).

## Main definitions

* `CslibFrontier.CSP.LiteralConjunction`: weighted exact-$k$-literal conjunction on `N` variables.
* `CslibFrontier.CSP.ConjunctionInstance`: list of weighted $k$-literal conjunctions with objective
  `val` and maximum value `opt`.
* `CslibFrontier.CSP.toConjunctionInstance`: variable-padded Trevisan compilation from
  `Cslib.Logic.PL.WeightedMaxCSP Rel ℕ ℝ`.
* `CslibFrontier.CSP.ConjunctionSDPSolution`, `CslibFrontier.CSP.integralConjunctionSDPSolution`:
  the Makarychev–Makarychev vector relaxation and its integral assignment lift.

## Main results

* `CslibFrontier.CSP.length_toConjunctionInstance_le`: conjunction count bound `≤ m * 2 ^ k`.
* `CslibFrontier.CSP.val_toConjunctionInstance`, `CslibFrontier.CSP.opt_toConjunctionInstance`:
  exact per-assignment score and optimum preservation.
* `CslibFrontier.CSP.obj_integralConjunctionSDPSolution`: exact objective preservation under the
  integral SDP embedding.
-/

public section

noncomputable section

open scoped BigOperators RealInnerProductSpace

namespace CslibFrontier.CSP

/-- A weighted exact-$k$-literal conjunction on `N` Boolean variables, specified by `k` distinct
variables `vars : Fin k ↪ Fin N`, required Boolean values `req : Fin k → Bool`, and nonnegative
weight `weight ≥ 0`. -/
@[ext]
structure LiteralConjunction (k N : ℕ) where
  /-- Distinct variable indices read by the conjunction. -/
  vars : Fin k ↪ Fin N
  /-- Required Boolean value on each position `r : Fin k`. -/
  req : Fin k → Bool
  /-- Nonnegative conjunction weight. -/
  weight : ℝ
  /-- Nonnegativity of `weight`. -/
  weight_nonneg : 0 ≤ weight

namespace LiteralConjunction

variable {k N : ℕ}

/-- Satisfaction indicator: `C.satisfied X = true` iff `X (C.vars r) = C.req r` for all `r`. -/
def satisfied (C : LiteralConjunction k N) (X : Fin N → Bool) : Bool :=
  decide (∀ r : Fin k, X (C.vars r) = C.req r)

theorem satisfied_eq_true_iff (C : LiteralConjunction k N) (X : Fin N → Bool) :
    C.satisfied X = true ↔ ∀ r : Fin k, X (C.vars r) = C.req r := by
  simp [satisfied]

end LiteralConjunction

/-- An instance of weighted exact-$k$-literal conjunctions (`Max-k-AND`) on `N` variables. -/
@[ext]
structure ConjunctionInstance (k N : ℕ) where
  /-- List of weighted $k$-literal conjunctions. -/
  clauses : List (LiteralConjunction k N)

namespace ConjunctionInstance

variable {k N : ℕ}

/-- Total weight of conjunctions satisfied by `X : Fin N → Bool`. -/
def val (inst : ConjunctionInstance k N) (X : Fin N → Bool) : ℝ :=
  ∑ idx : Fin inst.clauses.length,
    if inst.clauses[idx].satisfied X then inst.clauses[idx].weight else 0

/-- Optimal value over all assignments `X : Fin N → Bool`. -/
def opt (inst : ConjunctionInstance k N) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty inst.val

theorem val_le_opt (inst : ConjunctionInstance k N) (X : Fin N → Bool) :
    inst.val X ≤ inst.opt :=
  Finset.le_sup' inst.val (Finset.mem_univ X)

end ConjunctionInstance

section Reduction

private def paddedConstraintSupport {Rel : Type*} (k : ℕ)
    (F : Cslib.Logic.PL.WeightedMaxCSP Rel ℕ ℝ)
    (hvars : ∀ v ∈ F.vars, v < F.numVars)
    (j : Fin F.constraints.length) :
    Finset (Fin (F.numVars + F.constraints.length * k)) :=
  let m := F.constraints.length
  let c := F.constraints[j]
  have hc_mem : c ∈ F.constraints := List.getElem_mem j.2
  let scopeFin : List (Fin F.numVars) :=
    c.scope.attach.map fun ⟨v, hv⟩ ↦
      ⟨v, hvars v (List.mem_flatMap.mpr ⟨c, hc_mem, hv⟩)⟩
  let S : Finset (Fin F.numVars) := scopeFin.toFinset
  let orig : Finset (Fin (F.numVars + m * k)) := S.map (Fin.castAddEmb (m * k))
  let pad : Finset (Fin (F.numVars + m * k)) :=
    (Finset.range (k - S.card)).attach.image fun ⟨t, ht⟩ ↦
      ⟨F.numVars + j.1 * k + t, by
        have ht_lt : t < k - S.card := Finset.mem_range.mp ht
        have hjk : (j.1 + 1) * k ≤ m * k := Nat.mul_le_mul_right k (Nat.succ_le_of_lt j.2)
        have hsucc : (j.1 + 1) * k = j.1 * k + k := Nat.succ_mul j.1 k
        omega⟩
  orig ∪ pad

private theorem card_paddedConstraintSupport {Rel : Type*} {k : ℕ}
    (F : Cslib.Logic.PL.WeightedMaxCSP Rel ℕ ℝ)
    (hk : ∀ c ∈ F.constraints, c.scope.length ≤ k)
    (hvars : ∀ v ∈ F.vars, v < F.numVars)
    (j : Fin F.constraints.length) :
    (paddedConstraintSupport k F hvars j).card = k := by
  unfold paddedConstraintSupport
  dsimp only
  set c := F.constraints[j]
  have hc_mem : c ∈ F.constraints := List.getElem_mem j.2
  set scopeFin : List (Fin F.numVars) :=
    c.scope.attach.map fun ⟨v, hv⟩ ↦
      ⟨v, hvars v (List.mem_flatMap.mpr ⟨c, hc_mem, hv⟩)⟩
  set S : Finset (Fin F.numVars) := scopeFin.toFinset
  have hS_le : S.card ≤ k := by
    calc S.card ≤ scopeFin.length := List.toFinset_card_le scopeFin
      _ = c.scope.length := by simp [scopeFin]
      _ ≤ k := hk c hc_mem
  set orig : Finset (Fin (F.numVars + F.constraints.length * k)) :=
    S.map (Fin.castAddEmb (F.constraints.length * k))
  set pad : Finset (Fin (F.numVars + F.constraints.length * k)) :=
    (Finset.range (k - S.card)).attach.image fun ⟨t, ht⟩ ↦
      ⟨F.numVars + j.1 * k + t, by
        have ht_lt : t < k - S.card := Finset.mem_range.mp ht
        have hjk : (j.1 + 1) * k ≤ F.constraints.length * k :=
          Nat.mul_le_mul_right k (Nat.succ_le_of_lt j.2)
        have hsucc : (j.1 + 1) * k = j.1 * k + k := Nat.succ_mul j.1 k
        omega⟩
  have hdisj : Disjoint orig pad := by
    rw [Finset.disjoint_left]
    intro u hu_orig hu_pad
    rcases Finset.mem_map.mp hu_orig with ⟨v, _, rfl⟩
    rcases Finset.mem_image.mp hu_pad with ⟨⟨t, _⟩, _, hpad_eq⟩
    have hv_lt : (Fin.castAddEmb (F.constraints.length * k) v).1 < F.numVars := v.2
    have hv_ge : F.numVars ≤ (Fin.castAddEmb (F.constraints.length * k) v).1 := by
      rw [← hpad_eq]; dsimp; omega
    omega
  have hcard_orig : orig.card = S.card := Finset.card_map _
  have hcard_pad : pad.card = k - S.card := by
    rw [Finset.card_image_of_injective]
    · simp
    · exact fun ⟨_, _⟩ ⟨_, _⟩ h ↦ Subtype.ext (Nat.add_left_cancel (congrArg Fin.val h))
  change (orig ∪ pad).card = k
  rw [Finset.card_union_of_disjoint hdisj, hcard_orig, hcard_pad]
  exact Nat.add_sub_of_le hS_le

private def paddedConstraintVars {Rel : Type*} {k : ℕ}
    (F : Cslib.Logic.PL.WeightedMaxCSP Rel ℕ ℝ)
    (hk : ∀ c ∈ F.constraints, c.scope.length ≤ k)
    (hvars : ∀ v ∈ F.vars, v < F.numVars)
    (j : Fin F.constraints.length) :
    Fin k ↪ Fin (F.numVars + F.constraints.length * k) :=
  ((paddedConstraintSupport k F hvars j).orderEmbOfFin
    (card_paddedConstraintSupport F hk hvars j)).toEmbedding

private theorem mem_paddedConstraintVars {Rel : Type*} {k : ℕ}
    (F : Cslib.Logic.PL.WeightedMaxCSP Rel ℕ ℝ)
    (hk : ∀ c ∈ F.constraints, c.scope.length ≤ k)
    (hvars : ∀ v ∈ F.vars, v < F.numVars)
    (j : Fin F.constraints.length)
    (v : { v // v ∈ F.constraints[j].scope }) :
    ∃ r : Fin k,
      paddedConstraintVars F hk hvars j r =
        Fin.castAdd (F.constraints.length * k)
          ⟨v.1, hvars v.1 (List.mem_flatMap.mpr ⟨F.constraints[j], List.getElem_mem j.2,
            v.2⟩)⟩ := by
  let u : Fin F.numVars :=
    ⟨v.1, hvars v.1 (List.mem_flatMap.mpr ⟨F.constraints[j], List.getElem_mem j.2, v.2⟩)⟩
  have hu_mem : Fin.castAddEmb (F.constraints.length * k) u ∈
      paddedConstraintSupport k F hvars j := by
    unfold paddedConstraintSupport
    refine Finset.mem_union_left _ (Finset.mem_map.mpr ⟨u, ?_, rfl⟩)
    rw [List.mem_toFinset]
    exact List.mem_map.mpr ⟨v, List.mem_attach _ v, rfl⟩
  have hrange : Fin.castAddEmb (F.constraints.length * k) u ∈
      Set.range ((paddedConstraintSupport k F hvars j).orderEmbOfFin
        (card_paddedConstraintSupport F hk hvars j)) := by
    rw [Finset.range_orderEmbOfFin]
    exact hu_mem
  rcases hrange with ⟨r, hr⟩
  exact ⟨r, hr⟩

private def expandWeightedConstraint {Rel : Type*} (sem : Rel → List Bool → Bool) {k : ℕ}
    (F : Cslib.Logic.PL.WeightedMaxCSP Rel ℕ ℝ)
    (hk : ∀ c ∈ F.constraints, c.scope.length ≤ k)
    (hw : ∀ c ∈ F.constraints, 0 ≤ c.weight)
    (hvars : ∀ v ∈ F.vars, v < F.numVars)
    (j : Fin F.constraints.length) :
    List (LiteralConjunction k (F.numVars + F.constraints.length * k)) :=
  let emb := paddedConstraintVars F hk hvars j
  let posOf (v : { v // v ∈ F.constraints[j].scope }) : Fin k :=
    (mem_paddedConstraintVars F hk hvars j v).choose
  let accepts : Finset (Fin k → Bool) :=
    Finset.univ.filter fun a : Fin k → Bool ↦
      sem F.constraints[j].rel (F.constraints[j].scope.attach.map fun v ↦ a (posOf v)) = true
  accepts.toList.map fun a ↦
    { vars := emb
      req := a
      weight := F.constraints[j].weight
      weight_nonneg := hw F.constraints[j] (List.getElem_mem j.2) }

/-- **Variable-Padded Trevisan Conjunction Reduction**: compiles a Boolean
`Cslib.Logic.PL.WeightedMaxCSP Rel ℕ ℝ` of arity at most `k` into a `ConjunctionInstance` of
exact-$k$-literal conjunctions on `F.numVars + F.constraints.length * k` variables. -/
def toConjunctionInstance {Rel : Type*} (sem : Rel → List Bool → Bool) {k : ℕ}
    (F : Cslib.Logic.PL.WeightedMaxCSP Rel ℕ ℝ)
    (hk : ∀ c ∈ F.constraints, c.scope.length ≤ k)
    (hw : ∀ c ∈ F.constraints, 0 ≤ c.weight)
    (hvars : ∀ v ∈ F.vars, v < F.numVars) :
    ConjunctionInstance k (F.numVars + F.constraints.length * k) where
  clauses := (List.finRange F.constraints.length).flatMap
    (expandWeightedConstraint sem F hk hw hvars)

/-- Restrict an extended assignment `X : Fin (n + pad) → Bool` to the original `n` variables. -/
def restrictAssign {n pad : ℕ} (X : Fin (n + pad) → Bool) (i : Fin n) : Bool :=
  X (Fin.castAdd pad i)

/-- Pad an assignment `x : Fin n → Bool` with `false` on `pad` fresh variables. -/
def padAssign {n pad : ℕ} (x : Fin n → Bool) (v : Fin (n + pad)) : Bool :=
  if hv : v.1 < n then x ⟨v.1, hv⟩ else false

@[simp]
theorem restrictAssign_padAssign {n pad : ℕ} (x : Fin n → Bool) :
    restrictAssign (pad := pad) (padAssign x) = x := by
  ext i
  simp [restrictAssign, padAssign, i.2]

/-- Polynomial conjunction count bound: at most `F.constraints.length * 2 ^ k` conjunctions. -/
theorem length_toConjunctionInstance_le {Rel : Type*} (sem : Rel → List Bool → Bool) {k : ℕ}
    (F : Cslib.Logic.PL.WeightedMaxCSP Rel ℕ ℝ)
    (hk : ∀ c ∈ F.constraints, c.scope.length ≤ k)
    (hw : ∀ c ∈ F.constraints, 0 ≤ c.weight)
    (hvars : ∀ v ∈ F.vars, v < F.numVars) :
    (toConjunctionInstance sem F hk hw hvars).clauses.length ≤ F.constraints.length * 2 ^ k := by
  unfold toConjunctionInstance
  have hbound : ∀ j ∈ List.finRange F.constraints.length,
      (expandWeightedConstraint sem F hk hw hvars j).length ≤ 2 ^ k := by
    intro j _
    unfold expandWeightedConstraint
    simp only [List.length_map, Finset.length_toList]
    calc (Finset.univ.filter _).card ≤ (Finset.univ : Finset (Fin k → Bool)).card :=
          Finset.card_filter_le _ _
      _ = 2 ^ k := by simp
  calc ((List.finRange F.constraints.length).flatMap _).length
      = ((List.finRange F.constraints.length).map fun j ↦
          (expandWeightedConstraint sem F hk hw hvars j).length).sum := List.length_flatMap
    _ ≤ ((List.finRange F.constraints.length).map fun _ ↦ 2 ^ k).sum :=
        List.sum_le_sum fun j hj ↦ hbound j hj
    _ = F.constraints.length * 2 ^ k := by simp

private theorem list_attach_map_val {α β : Type*} (L : List α) (g : α → β) :
    (L.attach.map fun u ↦ g u.1) = L.map g := by
  induction L with
  | nil => rfl
  | cons a tl ih => simp [List.attach_cons, List.map_map, Function.comp_def, ih]

private theorem sum_expandWeightedConstraint_eq {Rel : Type*} (sem : Rel → List Bool → Bool)
    {k : ℕ} (F : Cslib.Logic.PL.WeightedMaxCSP Rel ℕ ℝ)
    (hk : ∀ c ∈ F.constraints, c.scope.length ≤ k)
    (hw : ∀ c ∈ F.constraints, 0 ≤ c.weight)
    (hvars : ∀ v ∈ F.vars, v < F.numVars)
    (j : Fin F.constraints.length)
    (X : Fin (F.numVars + F.constraints.length * k) → Bool) :
    ((expandWeightedConstraint sem F hk hw hvars j).map
        fun C ↦ if C.satisfied X then C.weight else 0).sum =
      F.constraints[j].evalWeight sem
        (Cslib.Logic.PL.MaxCSP.assignment F.numVars (restrictAssign X)) := by
  unfold expandWeightedConstraint Cslib.Logic.PL.WeightedConstraint.evalWeight
  set emb := paddedConstraintVars F hk hvars j
  let posOf (v : { v // v ∈ F.constraints[j].scope }) : Fin k :=
    (mem_paddedConstraintVars F hk hvars j v).choose
  have hpos : ∀ v : { v // v ∈ F.constraints[j].scope },
      emb (posOf v) = Fin.castAdd (F.constraints.length * k)
        ⟨v.1, hvars v.1 (List.mem_flatMap.mpr ⟨F.constraints[j], List.getElem_mem j.2, v.2⟩)⟩ :=
    fun v ↦ (mem_paddedConstraintVars F hk hvars j v).choose_spec
  set accepts : Finset (Fin k → Bool) :=
    Finset.univ.filter fun a : Fin k → Bool ↦
      sem F.constraints[j].rel (F.constraints[j].scope.attach.map fun v ↦ a (posOf v)) = true
  let mkConj (a : Fin k → Bool) :
      LiteralConjunction k (F.numVars + F.constraints.length * k) :=
    { vars := emb
      req := a
      weight := F.constraints[j].weight
      weight_nonneg := hw F.constraints[j] (List.getElem_mem j.2) }
  change ((accepts.toList.map mkConj).map fun C ↦ if C.satisfied X then C.weight else 0).sum = _
  rw [List.map_map, Finset.sum_map_toList]
  set a_X : Fin k → Bool := fun r ↦ X (emb r)
  have hsat_iff : ∀ a : Fin k → Bool, (mkConj a).satisfied X = true ↔ a = a_X := by
    intro a
    rw [LiteralConjunction.satisfied_eq_true_iff]
    exact ⟨fun h ↦ funext fun r ↦ (h r).symm, fun h ↦ h ▸ fun _ ↦ rfl⟩
  have hmap_eq :
      (F.constraints[j].scope.attach.map fun v ↦ a_X (posOf v)) =
        F.constraints[j].scope.map
          (Cslib.Logic.PL.MaxCSP.assignment F.numVars (restrictAssign X)) := by
    have hfun : (fun v : { v // v ∈ F.constraints[j].scope } ↦ a_X (posOf v)) =
        fun v ↦ Cslib.Logic.PL.MaxCSP.assignment F.numVars (restrictAssign X) v.1 := by
      ext v
      have hv_lt : v.1 < F.numVars :=
        hvars v.1 (List.mem_flatMap.mpr ⟨F.constraints[j], List.getElem_mem j.2, v.2⟩)
      simp [a_X, hpos v, restrictAssign, Cslib.Logic.PL.MaxCSP.assignment_lt _ hv_lt]
    rw [hfun, list_attach_map_val]
  by_cases hacc : a_X ∈ accepts
  · rw [Finset.sum_eq_single a_X]
    · have htrue : (mkConj a_X).satisfied X = true := (hsat_iff a_X).mpr rfl
      have hsem : sem F.constraints[j].rel
          (F.constraints[j].scope.map
            (Cslib.Logic.PL.MaxCSP.assignment F.numVars (restrictAssign X))) = true := by
        rw [← hmap_eq]
        exact (Finset.mem_filter.mp hacc).2
      dsimp only [Function.comp_apply]
      rw [htrue, hsem]
    · intro a _ ha_ne
      have hfalse : ¬ (mkConj a).satisfied X = true := by rwa [hsat_iff]
      simp [Function.comp_apply, hfalse]
    · intro habs; exact absurd hacc habs
  · have hsem : sem F.constraints[j].rel
        (F.constraints[j].scope.map
          (Cslib.Logic.PL.MaxCSP.assignment F.numVars (restrictAssign X))) = false := by
      rw [← Bool.not_eq_true, ← hmap_eq]
      intro ht
      exact hacc (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht⟩)
    simp only [hsem, Bool.false_eq_true, ↓reduceIte]
    refine Finset.sum_eq_zero fun a ha_mem ↦ ?_
    have ha_ne : a ≠ a_X := fun h ↦ hacc (h ▸ ha_mem)
    have hfalse : ¬ (mkConj a).satisfied X = true := by rwa [hsat_iff]
    simp [Function.comp_apply, hfalse]

private theorem list_sum_flatMap {α : Type*} (l : List α) (g : α → List ℝ) :
    (l.flatMap g).sum = (l.map fun x ↦ (g x).sum).sum := by
  induction l with
  | nil => simp
  | cons a tl ih => simp [ih]

/-- **Exact Per-Assignment Score Preservation** under `toConjunctionInstance`. -/
theorem val_toConjunctionInstance {Rel : Type*} (sem : Rel → List Bool → Bool) {k : ℕ}
    (F : Cslib.Logic.PL.WeightedMaxCSP Rel ℕ ℝ)
    (hk : ∀ c ∈ F.constraints, c.scope.length ≤ k)
    (hw : ∀ c ∈ F.constraints, 0 ≤ c.weight)
    (hvars : ∀ v ∈ F.vars, v < F.numVars)
    (X : Fin (F.numVars + F.constraints.length * k) → Bool) :
    (toConjunctionInstance sem F hk hw hvars).val X = F.score sem (restrictAssign X) := by
  unfold ConjunctionInstance.val toConjunctionInstance
    Cslib.Logic.PL.WeightedMaxCSP.score Cslib.Logic.PL.WeightedMaxCSP.evalScore
  have hsum_list : ∀ L : List (LiteralConjunction k (F.numVars + F.constraints.length * k)),
      (∑ idx : Fin L.length, if L[idx].satisfied X then L[idx].weight else 0) =
        (L.map fun C ↦ if C.satisfied X then C.weight else 0).sum := by
    intro L
    rw [← List.sum_ofFn]
    congr 1
    apply List.ext_getElem <;> simp
  rw [hsum_list, List.map_flatMap, list_sum_flatMap]
  congr 1
  apply List.ext_getElem
  · simp
  · intro i hi₁ hi₂
    simp only [List.getElem_map, List.getElem_finRange]
    exact sum_expandWeightedConstraint_eq sem F hk hw hvars ⟨i, by simpa using hi₁⟩ X

/-- **Exact Optimum Preservation** under `toConjunctionInstance`. -/
theorem opt_toConjunctionInstance {Rel : Type*} (sem : Rel → List Bool → Bool) {k : ℕ}
    (F : Cslib.Logic.PL.WeightedMaxCSP Rel ℕ ℝ)
    (hk : ∀ c ∈ F.constraints, c.scope.length ≤ k)
    (hw : ∀ c ∈ F.constraints, 0 ≤ c.weight)
    (hvars : ∀ v ∈ F.vars, v < F.numVars) :
    (toConjunctionInstance sem F hk hw hvars).opt = F.optimum sem := by
  apply le_antisymm
  · refine Finset.sup'_le Finset.univ_nonempty _ fun X _ ↦ ?_
    rw [val_toConjunctionInstance]
    exact F.score_le_optimum sem (restrictAssign X)
  · refine Finset.sup'_le Finset.univ_nonempty _ fun x _ ↦ ?_
    have hpad := val_toConjunctionInstance sem F hk hw hvars (padAssign x)
    rw [restrictAssign_padAssign] at hpad
    rw [← hpad]
    exact (toConjunctionInstance sem F hk hw hvars).val_le_opt (padAssign x)

end Reduction

/-! ### Makarychev–Makarychev Semidefinite Vector Relaxation -/

/-- A feasible vector solution `(v, z)` to the Makarychev–Makarychev semidefinite relaxation of a
weighted $k$-literal conjunction instance `inst`. -/
@[ext]
structure ConjunctionSDPSolution {k N : ℕ} (inst : ConjunctionInstance k N)
    (E : Type*) [SeminormedAddCommGroup E] [InnerProductSpace ℝ E] where
  /-- Literal vectors `v_{i, b}` for `i : Fin N` and `b : Bool`. -/
  v : Fin N → Bool → E
  /-- Conjunction vectors `z_C`. -/
  z : Fin inst.clauses.length → E
  /-- `‖v_{i,0}‖² + ‖v_{i,1}‖² ≤ 1`. -/
  norm_sq_add_le : ∀ i : Fin N, ‖v i false‖ ^ 2 + ‖v i true‖ ^ 2 ≤ 1
  /-- `⟪v_{i,0}, v_{i,1}⟫ = 0`. -/
  inner_false_true : ∀ i : Fin N, ⟪v i false, v i true⟫ = 0
  /-- `⟪v_{i, b_C(i)}, z_C⟫ = ‖z_C‖²`. -/
  inner_req_eq : ∀ (idx : Fin inst.clauses.length) (r : Fin k),
    ⟪v (inst.clauses[idx].vars r) (inst.clauses[idx].req r), z idx⟫ = ‖z idx‖ ^ 2
  /-- `⟪v_{i, 1 - b_C(i)}, z_C⟫ = 0`. -/
  inner_not_req_eq : ∀ (idx : Fin inst.clauses.length) (r : Fin k),
    ⟪v (inst.clauses[idx].vars r) (!inst.clauses[idx].req r), z idx⟫ = 0
  /-- `‖z_C‖² ≤ 1`. -/
  norm_z_sq_le : ∀ idx : Fin inst.clauses.length, ‖z idx‖ ^ 2 ≤ 1

/-- Objective value `∑_C λ_C ‖z_C‖²` of a feasible `ConjunctionSDPSolution`. -/
def ConjunctionSDPSolution.obj {k N : ℕ} {inst : ConjunctionInstance k N}
    {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    (sol : ConjunctionSDPSolution inst E) : ℝ :=
  ∑ idx : Fin inst.clauses.length, inst.clauses[idx].weight * ‖sol.z idx‖ ^ 2

private def sdpUnitVec1 : EuclideanSpace ℝ (Fin 1) :=
  EuclideanSpace.single 0 1

private theorem norm_sdpUnitVec1 : ‖sdpUnitVec1‖ = 1 := by
  simp [sdpUnitVec1]

/-- Integral assignment embedding into `ConjunctionSDPSolution` along `EuclideanSpace ℝ (Fin 1)`. -/
def integralConjunctionSDPSolution {k N : ℕ} (inst : ConjunctionInstance k N)
    (X : Fin N → Bool) : ConjunctionSDPSolution inst (EuclideanSpace ℝ (Fin 1)) where
  v i b := if X i = b then sdpUnitVec1 else 0
  z idx := if inst.clauses[idx].satisfied X then sdpUnitVec1 else 0
  norm_sq_add_le i := by cases X i <;> simp [norm_sdpUnitVec1]
  inner_false_true i := by cases X i <;> simp
  inner_req_eq idx r := by
    cases hsat : inst.clauses[idx].satisfied X
    · simp
    · have hreq := (LiteralConjunction.satisfied_eq_true_iff _ _).mp hsat r
      simp only [Fin.getElem_fin] at hreq ⊢
      simp [hreq, norm_sdpUnitVec1]
  inner_not_req_eq idx r := by
    cases hsat : inst.clauses[idx].satisfied X
    · simp
    · have hreq := (LiteralConjunction.satisfied_eq_true_iff _ _).mp hsat r
      simp only [Fin.getElem_fin] at hreq ⊢
      simp [hreq]
  norm_z_sq_le idx := by split_ifs <;> simp [norm_sdpUnitVec1]

/-- Exact objective preservation under `integralConjunctionSDPSolution`. -/
theorem obj_integralConjunctionSDPSolution {k N : ℕ} (inst : ConjunctionInstance k N)
    (X : Fin N → Bool) :
    (integralConjunctionSDPSolution inst X).obj = inst.val X := by
  unfold ConjunctionSDPSolution.obj ConjunctionInstance.val integralConjunctionSDPSolution
  refine Finset.sum_congr rfl fun idx _ ↦ ?_
  dsimp only
  split_ifs <;> simp [norm_sdpUnitVec1]

end CslibFrontier.CSP
