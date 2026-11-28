/-
Copyright (c) 2026 The cslib-frontier contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CslibFrontier.Computability.Complexity.Problems.DominatingSet
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Rat

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.ListProd
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Rat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.EqualityPrimitives
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListBinaryLookup
import CslibFrontier.Foundations.Data.List.GetD
import CslibFrontier.Foundations.Data.Rat.ClearDenom
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# NP-Completeness of Uncapacitated Facility Location

This module establishes NP-completeness (under standard Lean axioms) on multi-tape Turing machines
for **Uncapacitated Facility Location (`UncapacitatedFacilityLocation`)**: deciding whether a
rational facility-opening and client-service instance admits a nonempty open facility set and
client assignment within budget `B`. NP-hardness is proved via a polynomial-time reduction from
`Cslib.Complexity.DominatingSet`.

## Main definitions

- `CslibFrontier.Computability.Complexity.UFLInstance`,
  `CslibFrontier.Computability.Complexity.uflServiceEntry`,
  `CslibFrontier.Computability.Complexity.UncapacitatedFacilityLocation`: uncapacitated facility
  location decision problem.

## Main results

- `CslibFrontier.Computability.Complexity.UncapacitatedFacilityLocation.mem_NP`,
  `CslibFrontier.Computability.Complexity.UncapacitatedFacilityLocation.fromDominatingSet_mem_iff`,
  `CslibFrontier.Computability.Complexity.UncapacitatedFacilityLocation_npHard`,
  `CslibFrontier.Computability.Complexity.UncapacitatedFacilityLocation_npComplete`.

## Tags

computational complexity, NP-completeness, uncapacitated facility location, dominating set
-/

public section

namespace CslibFrontier.Computability.Complexity

open Finset Cslib.Complexity Turing.MultiTapeTM ComputableInPolyTime

/-! ### 1. Internal Rational List-Sum and Deduplication Helpers -/

private def uflDenomProd (l : List ℚ) : ℕ :=
  (l.map Rat.den).prod

private lemma uflDenomProd_pos (l : List ℚ) : 0 < uflDenomProd l :=
  List.prod_pos fun _ hd ↦ by
    obtain ⟨q, _, rfl⟩ := List.mem_map.mp hd
    exact q.pos

private lemma dvd_uflDenomProd {l : List ℚ} {q : ℚ} (hq : q ∈ l) :
    q.den ∣ uflDenomProd l :=
  List.dvd_prod (List.mem_map.mpr ⟨q, hq, rfl⟩)

private def uflScaledNumSum (l : List ℚ) : ℤ :=
  (l.map fun q ↦ q.num * ((uflDenomProd l / q.den : ℕ) : ℤ)).sum

private lemma cast_sum_clearDenom_ufl (D : ℕ) :
    ∀ (s : List ℚ), (∀ q ∈ s, q.den ∣ D) →
      (((s.map fun q ↦ q.num * ((D / q.den : ℕ) : ℤ)).sum : ℤ) : ℚ) = (D : ℚ) * s.sum
  | [], _ => by simp
  | q :: s, h => by
    simp only [List.map_cons, List.sum_cons, Int.cast_add, mul_add]
    rw [← Rat.clearDenom_entry (h q List.mem_cons_self),
      cast_sum_clearDenom_ufl D s fun r hr ↦ h r (List.mem_cons_of_mem q hr)]

private lemma divInt_uflScaledNumSum (l : List ℚ) :
    Rat.divInt (uflScaledNumSum l) (uflDenomProd l : ℤ) = l.sum := by
  have hD : (uflDenomProd l : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (uflDenomProd_pos l).ne'
  rw [Rat.divInt_eq_div, Int.cast_natCast, uflScaledNumSum,
    cast_sum_clearDenom_ufl (uflDenomProd l) l fun _ hq ↦ dvd_uflDenomProd hq,
    mul_div_cancel_left₀ _ hD]

@[local fun_prop]
private theorem computableInPolyTime_uflDenomProd :
    ComputableInPolyTime uflDenomProd (encList encRat) encNat := by
  unfold uflDenomProd
  fun_prop

@[local fun_prop]
private theorem computableInPolyTime_uflScaledNumSum :
    ComputableInPolyTime uflScaledNumSum (encList encRat) encIntBin := by
  unfold uflScaledNumSum
  exact intBin_sum.comp (mapWithInput id' (by fun_prop))

private theorem ufl_listSum_polyTime {α : Type} {enc : α ↪ List Bool} {f : α → List ℚ}
    (hf : ComputableInPolyTime f enc (encList encRat)) :
    ComputableInPolyTime (fun a ↦ (f a).sum) enc encRat :=
  ((show ComputableInPolyTime
      (fun l : List ℚ ↦ Rat.divInt (uflScaledNumSum l) ((uflDenomProd l : ℕ) : ℤ))
      (encList encRat) encRat by fun_prop).of_enc_eq fun l ↦
    congrArg encRat (divInt_uflScaledNumSum l).symm).comp hf

private lemma ufl_sum_map_range (n : ℕ) (f : ℕ → ℚ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih,
      Finset.sum_range_succ, List.map_singleton, List.sum_singleton]

private def uflDedupNat (S : List ℕ) : List ℕ :=
  selectDistinct S (List.replicate S.length true)

private lemma nodup_uflDedupNat (S : List ℕ) : (uflDedupNat S).Nodup :=
  nodup_selectDistinct _ _

@[local fun_prop]
private theorem computableInPolyTime_uflDedupNat :
    ComputableInPolyTime uflDedupNat (encList encNat) (encList encNat) := by
  unfold uflDedupNat
  fun_prop

/-! ### 2. Uncapacitated Facility Location (`UncapacitatedFacilityLocation`) -/

/-- Entry `(i, j)` of a client-to-facility rational service-cost matrix, defaulting to `0`. -/
@[expose]
def uflServiceEntry (serviceCosts : List (List ℚ)) (i j : ℕ) : ℚ :=
  (serviceCosts.getD i []).getD j 0

private theorem computableInPolyTime_uflServiceEntry_unary {α : Type} {enc : α ↪ List Bool}
    {sc : α → List (List ℚ)} {i j : α → ℕ}
    (hs : ComputableInPolyTime sc enc (encList (encList encRat)))
    (hi : ComputableInPolyTime i enc encUnary)
    (hj : ComputableInPolyTime j enc encUnary) :
    ComputableInPolyTime (fun a ↦ uflServiceEntry (sc a) (i a) (j a)) enc encRat :=
  listGetDWithInput (listGetDWithInput hs hi ([] : List ℚ)) hj (0 : ℚ)

private theorem computableInPolyTime_uflServiceEntry_unary_binary {α : Type} {enc : α ↪ List Bool}
    {sc : α → List (List ℚ)} {i j : α → ℕ}
    (hs : ComputableInPolyTime sc enc (encList (encList encRat)))
    (hi : ComputableInPolyTime i enc encUnary)
    (hj : ComputableInPolyTime j enc encNat) :
    ComputableInPolyTime (fun a ↦ uflServiceEntry (sc a) (i a) (j a)) enc encRat :=
  listGetD_binary (encA := encRat) (0 : ℚ) (listGetDWithInput hs hi ([] : List ℚ)) hj

/-- An instance `(numFacilities, numClients, openingCosts, serviceCosts, budget)` of
**Uncapacitated Facility Location (UFL)**. -/
@[ext]
structure UFLInstance where
  /-- Number of candidate facilities `|F|`, encoded in unary. -/
  numFacilities : ℕ
  /-- Number of demand clients `|D|`, encoded in unary. -/
  numClients : ℕ
  /-- Facility opening costs `f_j` (`j < numFacilities`). -/
  openingCosts : List ℚ
  /-- Client-to-facility service cost matrix `c_{i, j}` (`numClients × numFacilities`). -/
  serviceCosts : List (List ℚ)
  /-- Upper bound `B` on total opening plus service cost. -/
  budget : ℚ
  deriving DecidableEq, Repr

/-- Encoding of `UFLInstance`. -/
enc_structure encUFL : UFLInstance where
  numFacilities : encUnary,
  numClients : encUnary,
  openingCosts : (encList encRat),
  serviceCosts : (encList (encList encRat)),
  budget : encRat

attribute [fun_prop] encUFL_numFacilities_polyTime encUFL_numClients_polyTime
  encUFL_openingCosts_polyTime encUFL_serviceCosts_polyTime encUFL_budget_polyTime
  encUFL_mk_polyTime

/-- **Uncapacitated Facility Location (UFL)**: nonnegative rational facility-location instances
admitting a nonempty subset of open facilities `F' ⊆ Fin numFacilities` and a client assignment
`π : Fin numClients → F'` with `∑_{j ∈ F'} f_j + ∑_{i} c_{i, π(i)} ≤ budget`. -/
@[expose]
def UncapacitatedFacilityLocation : Set UFLInstance :=
  {x | (∀ j : Fin x.numFacilities, 0 ≤ x.openingCosts.getD j.1 0) ∧
    (∀ (i : Fin x.numClients) (j : Fin x.numFacilities),
      0 ≤ uflServiceEntry x.serviceCosts i.1 j.1) ∧
    ∃ (F' : Finset (Fin x.numFacilities)), F'.Nonempty ∧
      ∃ assign : Fin x.numClients → F',
        (∑ j ∈ F', x.openingCosts.getD j.1 0) +
          (∑ i : Fin x.numClients, uflServiceEntry x.serviceCosts i.1 (assign i).1.1) ≤ x.budget}

namespace UncapacitatedFacilityLocation

private def check (p : UFLInstance × (List ℕ × List ℕ)) : Bool :=
  let x := p.1
  let openList := uflDedupNat p.2.1
  let assign := p.2.2
  ((List.range x.numFacilities).all fun j ↦ decide (0 ≤ x.openingCosts.getD j 0)) &&
  ((List.range x.numClients).all fun i ↦ (List.range x.numFacilities).all fun j ↦
    decide (0 ≤ uflServiceEntry x.serviceCosts i j)) &&
  !openList.isEmpty &&
  (openList.all fun j ↦ decide (j < x.numFacilities)) &&
  decide (assign.length = x.numClients) &&
  ((List.range x.numClients).all fun i ↦ decide (assign.getD i 0 ∈ openList)) &&
  decide
    ((openList.map fun j ↦ x.openingCosts.getD j 0).sum +
      ((List.range x.numClients).map fun i ↦
        uflServiceEntry x.serviceCosts i (assign.getD i 0)).sum ≤ x.budget)

private theorem computableInPolyTime_check :
    ComputableInPolyTime check
      (encPair encUFL (encPair (encList encNat) (encList encNat))) encBool := by
  let E := encPair encUFL (encPair (encList encNat) (encList encNat))
  have hX : ComputableInPolyTime (fun p : UFLInstance × (List ℕ × List ℕ) ↦ p.1) E encUFL :=
    fst _ _
  have hF : ComputableInPolyTime (fun p : UFLInstance × (List ℕ × List ℕ) ↦ p.1.numFacilities)
      E encUnary := encUFL_numFacilities_polyTime hX
  have hC : ComputableInPolyTime (fun p : UFLInstance × (List ℕ × List ℕ) ↦ p.1.numClients)
      E encUnary := encUFL_numClients_polyTime hX
  have hOC : ComputableInPolyTime (fun p : UFLInstance × (List ℕ × List ℕ) ↦ p.1.openingCosts)
      E (encList encRat) := encUFL_openingCosts_polyTime hX
  have hSC : ComputableInPolyTime (fun p : UFLInstance × (List ℕ × List ℕ) ↦ p.1.serviceCosts)
      E (encList (encList encRat)) := encUFL_serviceCosts_polyTime hX
  have hB : ComputableInPolyTime (fun p : UFLInstance × (List ℕ × List ℕ) ↦ p.1.budget)
      E encRat := encUFL_budget_polyTime hX
  have hopen : ComputableInPolyTime
      (fun p : UFLInstance × (List ℕ × List ℕ) ↦ uflDedupNat p.2.1) E (encList encNat) :=
    computableInPolyTime_uflDedupNat.comp ((fst _ _).comp (snd _ _))
  have hassign : ComputableInPolyTime (fun p : UFLInstance × (List ℕ × List ℕ) ↦ p.2.2)
      E (encList encNat) := (snd _ _).comp (snd _ _)
  have hnn1 : ComputableInPolyTime (fun p : UFLInstance × (List ℕ × List ℕ) ↦
      (List.range p.1.numFacilities).all fun j ↦ decide (0 ≤ p.1.openingCosts.getD j 0))
      E encBool :=
    allWithInput (ComputableInPolyTime.range.comp hF)
      (rat_le' (const 0) (listGetDWithInput (hOC.comp (fst _ _)) (snd _ _) (0 : ℚ)))
  have hnn2 : ComputableInPolyTime (fun p : UFLInstance × (List ℕ × List ℕ) ↦
      (List.range p.1.numClients).all fun i ↦ (List.range p.1.numFacilities).all fun j ↦
        decide (0 ≤ uflServiceEntry p.1.serviceCosts i j)) E encBool :=
    allWithInput (ComputableInPolyTime.range.comp hC)
      (allWithInput (ComputableInPolyTime.range.comp (hF.comp (fst _ _)))
        (rat_le' (const 0)
          (computableInPolyTime_uflServiceEntry_unary
            (hSC.comp ((fst _ _).comp (fst _ _)))
            ((snd _ _).comp (fst _ _)) (snd _ _))))
  have hltF : ComputableInPolyTime (fun p : UFLInstance × (List ℕ × List ℕ) ↦
      (uflDedupNat p.2.1).all fun j ↦ decide (j < p.1.numFacilities)) E encBool :=
    allWithInput hopen (binary_lt' (snd _ _) (unary_to_binary.comp (hF.comp (fst _ _))))
  have hlenA : ComputableInPolyTime (fun p : UFLInstance × (List ℕ × List ℕ) ↦
      decide (p.2.2.length = p.1.numClients)) E encBool :=
    decide_eq' ((length_list encNat).comp hassign) hC
  have hmemA : ComputableInPolyTime (fun p : UFLInstance × (List ℕ × List ℕ) ↦
      (List.range p.1.numClients).all fun i ↦ decide (p.2.2.getD i 0 ∈ uflDedupNat p.2.1))
      E encBool :=
    allWithInput (ComputableInPolyTime.range.comp hC)
      (decide_mem (hopen.comp (fst _ _))
        (listGetDWithInput (hassign.comp (fst _ _)) (snd _ _) 0))
  have hcost : ComputableInPolyTime (fun p : UFLInstance × (List ℕ × List ℕ) ↦
      decide
        (((uflDedupNat p.2.1).map fun j ↦ p.1.openingCosts.getD j 0).sum +
          ((List.range p.1.numClients).map fun i ↦
            uflServiceEntry p.1.serviceCosts i (p.2.2.getD i 0)).sum ≤ p.1.budget)) E encBool := by
    refine rat_le' (rat_add' ?_ ?_) hB
    · exact ufl_listSum_polyTime (mapWithInput hopen
        (listGetD_binary (encA := encRat) (0 : ℚ) (hOC.comp (fst _ _)) (snd _ _)))
    · exact ufl_listSum_polyTime (mapWithInput (ComputableInPolyTime.range.comp hC)
        (computableInPolyTime_uflServiceEntry_unary_binary
          (hSC.comp (fst _ _)) (snd _ _)
          (listGetDWithInput (hassign.comp (fst _ _)) (snd _ _) 0)))
  unfold check
  dsimp only
  exact bool_and'
    (bool_and'
      (bool_and'
        (bool_and' (bool_and' (bool_and' hnn1 hnn2)
          (bool_not.comp ((listIsEmpty' encNat).comp hopen))) hltF)
        hlenA)
      hmemA)
    hcost

private theorem mem_of_check {x : UFLInstance} {w : List ℕ × List ℕ}
    (h : check (x, w) = true) : x ∈ UncapacitatedFacilityLocation := by
  unfold check at h
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, List.all_eq_true,
    List.mem_range] at h
  rcases h with ⟨⟨⟨⟨⟨⟨hnn1, hnn2⟩, hne⟩, hltF⟩, _⟩, hmemA⟩, hcost⟩
  set openList := uflDedupNat w.1
  have hopen_nd : openList.Nodup := nodup_uflDedupNat w.1
  have hopen_ne : openList ≠ [] := fun h0 ↦ by simp [h0] at hne
  let F' : Finset (Fin x.numFacilities) :=
    openList.toFinset.attach.image fun j ↦ ⟨j.1, hltF j.1 (List.mem_toFinset.mp j.2)⟩
  obtain ⟨j₀, hj₀⟩ := List.exists_mem_of_ne_nil openList hopen_ne
  have hF'_ne : F'.Nonempty :=
    ⟨⟨j₀, hltF j₀ hj₀⟩, mem_image_of_mem _ (mem_attach _ ⟨j₀, List.mem_toFinset.mpr hj₀⟩)⟩
  let assign (i : Fin x.numClients) : F' :=
    ⟨⟨w.2.getD i.1 0, hltF _ (hmemA i.1 i.2)⟩,
      mem_image_of_mem _ (mem_attach _ ⟨w.2.getD i.1 0, List.mem_toFinset.mpr (hmemA i.1 i.2)⟩)⟩
  refine ⟨fun j ↦ hnn1 j.1 j.2, fun i j ↦ hnn2 i.1 i.2 j.1 j.2, F', hF'_ne, assign, ?_⟩
  have hsumF : ∑ j ∈ F', x.openingCosts.getD j.1 0 =
      (openList.map fun j ↦ x.openingCosts.getD j 0).sum := by
    dsimp [F']
    rw [sum_image fun a _ b _ h ↦ Subtype.ext (congrArg Fin.val h),
      sum_attach openList.toFinset (fun j ↦ x.openingCosts.getD j 0),
      ← List.sum_toFinset _ hopen_nd]
  have hsumC : ∑ i : Fin x.numClients, uflServiceEntry x.serviceCosts i.1 (assign i).1.1 =
      ((List.range x.numClients).map fun i ↦
        uflServiceEntry x.serviceCosts i (w.2.getD i 0)).sum := by
    rw [ufl_sum_map_range,
      ← Fin.sum_univ_eq_sum_range
        (fun i : ℕ ↦ uflServiceEntry x.serviceCosts i (w.2.getD i 0)) x.numClients]
  rw [hsumF, hsumC]
  exact hcost

private noncomputable def witnessPoly : Polynomial ℕ :=
  3 * Polynomial.X * (2 * Polynomial.X + 1) + 5

private theorem exists_check_of_mem {x : UFLInstance} (hx : x ∈ UncapacitatedFacilityLocation) :
    ∃ w : List ℕ × List ℕ, check (x, w) = true ∧
      (encPair (encList encNat) (encList encNat) w).length ≤
        witnessPoly.eval (encUFL x).length := by
  rcases hx with ⟨hnn1, hnn2, F', hF'ne, assign, hcost⟩
  set L := (encUFL x).length
  have hFL : x.numFacilities ≤ L := by
    simpa only [encUnary_apply, List.length_replicate] using encUFL_numFacilities_length_le x
  have hCL : x.numClients ≤ L := by
    simpa only [encUnary_apply, List.length_replicate] using encUFL_numClients_length_le x
  let eF := F'.equivFin
  let openList : List ℕ := List.ofFn fun k : Fin F'.card ↦ (eF.symm k).1.1
  let assignList : List ℕ := List.ofFn fun i : Fin x.numClients ↦ (assign i).1.1
  have hmem_dedup : ∀ v, v ∈ uflDedupNat openList ↔ v ∈ openList :=
    fun _ ↦ mem_selectDistinct_replicate
  refine ⟨(openList, assignList), ?_, ?_⟩
  · unfold check
    dsimp only
    have hne : (uflDedupNat openList).isEmpty = false := by
      rw [List.isEmpty_eq_false_iff]
      intro h0
      obtain ⟨j₀, hj₀⟩ := hF'ne
      have hmem : j₀.1 ∈ uflDedupNat openList := by
        rw [hmem_dedup, List.mem_ofFn']
        exact ⟨eF ⟨j₀, hj₀⟩, by simp⟩
      rw [h0] at hmem
      exact List.not_mem_nil hmem
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, List.all_eq_true,
      List.mem_range]
    refine ⟨⟨⟨⟨⟨⟨fun j hj ↦ hnn1 ⟨j, hj⟩, fun i hi j hj ↦ hnn2 ⟨i, hi⟩ ⟨j, hj⟩⟩, hne⟩, ?_⟩,
      List.length_ofFn⟩, ?_⟩, ?_⟩
    · intro j hj
      rw [hmem_dedup] at hj
      obtain ⟨k, rfl⟩ := (List.mem_ofFn' _ _).mp hj
      exact (eF.symm k).1.2
    · intro i hi
      have hget : assignList.getD i 0 = (assign ⟨i, hi⟩).1.1 := by
        simp [assignList, List.getD_eq_getElem?_getD, hi]
      rw [hget, hmem_dedup, List.mem_ofFn']
      exact ⟨eF (assign ⟨i, hi⟩), by simp⟩
    · have hsum1 : ((uflDedupNat openList).map fun j ↦ x.openingCosts.getD j 0).sum =
          ∑ j ∈ F', x.openingCosts.getD j.1 0 := by
        rw [← List.sum_toFinset _ (nodup_uflDedupNat openList)]
        have htf : (uflDedupNat openList).toFinset = F'.map ⟨Fin.val, Fin.val_injective⟩ := by
          ext v
          simp only [List.mem_toFinset, hmem_dedup, openList, List.mem_ofFn', mem_map,
            Function.Embedding.coeFn_mk]
          constructor
          · rintro ⟨k, rfl⟩
            exact ⟨(eF.symm k).1, (eF.symm k).2, rfl⟩
          · rintro ⟨j, hjF, rfl⟩
            exact ⟨eF ⟨j, hjF⟩, by simp⟩
        rw [htf, sum_map]
        rfl
      have hsum2 : ((List.range x.numClients).map fun i ↦
            uflServiceEntry x.serviceCosts i (assignList.getD i 0)).sum =
          ∑ i : Fin x.numClients, uflServiceEntry x.serviceCosts i.1 (assign i).1.1 := by
        rw [ufl_sum_map_range,
          ← Fin.sum_univ_eq_sum_range
            (fun i : ℕ ↦ uflServiceEntry x.serviceCosts i (assignList.getD i 0)) x.numClients]
        refine sum_congr rfl fun i _ ↦ ?_
        have hget : assignList.getD i.1 0 = (assign i).1.1 := by
          simp [assignList, List.getD_eq_getElem?_getD, i.2]
        rw [hget]
      rw [hsum1, hsum2]
      exact hcost
  · have hpoly_val : witnessPoly.eval L = 3 * L * (2 * L + 1) + 5 := by simp [witnessPoly]
    rw [hpoly_val, length_encPair]
    have hlen_nat : ∀ v : ℕ, v < x.numFacilities → (encNat v).length ≤ L := by
      intro v hv
      rw [encNat_apply, Nat.size_eq_bits_len]
      exact Nat.size_le.mpr (hv.trans_le (hFL.trans Nat.lt_two_pow_self.le))
    have hF_le : F'.card ≤ x.numFacilities := (card_le_univ F').trans_eq (Fintype.card_fin _)
    have h1 : (encList encNat openList).length ≤ F'.card * (2 * L + 1) := by
      have := length_encList_le encNat openList (b := L) fun v hv ↦ by
        obtain ⟨k, rfl⟩ := (List.mem_ofFn' _ _).mp hv
        exact hlen_nat _ (eF.symm k).1.2
      simpa [openList] using this
    have h2 : (encList encNat assignList).length ≤ x.numClients * (2 * L + 1) := by
      have := length_encList_le encNat assignList (b := L) fun v hv ↦ by
        obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).mp hv
        exact hlen_nat _ (assign i).1.2
      simpa [assignList] using this
    have hF_L : F'.card ≤ L := hF_le.trans hFL
    nlinarith

/-- `UncapacitatedFacilityLocation` belongs to `NP`. -/
theorem mem_NP : UncapacitatedFacilityLocation ∈ NP encUFL :=
  mem_NP_of_check (.pair (.list .nat) (.list .nat)) computableInPolyTime_check
    (fun _ _ h ↦ mem_of_check h) fun _ hx ↦ exists_check_of_mem hx

/-- Fixed accepted `UFL` instance (`1` facility of cost `0`, `0` clients, `budget = 0`). -/
def yesInstance : UFLInstance :=
  ⟨1, 0, [0], [], 0⟩

private theorem yesInstance_mem : yesInstance ∈ UncapacitatedFacilityLocation := by
  change (∀ j : Fin 1, 0 ≤ ([0] : List ℚ).getD j.1 0) ∧
    (∀ (i : Fin 0) (j : Fin 1), 0 ≤ uflServiceEntry [] i.1 j.1) ∧
    ∃ (F' : Finset (Fin 1)), F'.Nonempty ∧
      ∃ assign : Fin 0 → F',
        (∑ j ∈ F', ([0] : List ℚ).getD j.1 0) +
          (∑ i : Fin 0, uflServiceEntry [] i.1 (assign i).1.1) ≤ 0
  refine ⟨fun j ↦ ?_, fun i ↦ Fin.elim0 i, {⟨0, Nat.one_pos⟩}, singleton_nonempty _,
    fun i ↦ Fin.elim0 i, ?_⟩
  · fin_cases j; simp
  · simp

/-- Fixed rejected `UFL` instance (`0` facilities, `0` clients, `budget = 0`). -/
def noInstance : UFLInstance :=
  ⟨0, 0, [], [], 0⟩

private theorem noInstance_notMem : noInstance ∉ UncapacitatedFacilityLocation := by
  rintro ⟨_, _, F', ⟨j, _⟩, _, _⟩
  exact Fin.elim0 j

/-- Polynomial-time reduction from `DominatingSet` to `UncapacitatedFacilityLocation`. -/
def fromDominatingSet (x : DominatingSetInstance) : UFLInstance :=
  let vs := x.graph.distinctVertices
  let n := vs.length
  if decide (n = 0) then
    if decide (x.bound = 0) then yesInstance else noInstance
  else if decide (x.bound = 0) then noInstance
  else if decide (x.bound ≤ n) then
    ⟨n, n, List.replicate n (1 : ℚ),
      (List.range n).map fun i ↦
        (List.range n).map fun j ↦
          if decide (i = j) || x.graph.adjBool (vs.getD i 0) (vs.getD j 0) then (0 : ℚ)
          else ((x.bound + 1 : ℕ) : ℚ),
      (x.bound : ℚ)⟩
  else noInstance

@[fun_prop]
private theorem computableInPolyTime_fromDominatingSet :
    ComputableInPolyTime fromDominatingSet encDominatingSet encUFL := by
  have hG : ComputableInPolyTime DominatingSetInstance.graph encDominatingSet encGraph :=
    encDominatingSet_graph_polyTime id'
  have hk : ComputableInPolyTime DominatingSetInstance.bound encDominatingSet encNat :=
    encDominatingSet_bound_polyTime id'
  have hvs : ComputableInPolyTime
      (fun x : DominatingSetInstance ↦ x.graph.distinctVertices)
      encDominatingSet (encList encNat) :=
    Graph.computableInPolyTime_distinctVertices.comp hG
  have hn_un : ComputableInPolyTime
      (fun x : DominatingSetInstance ↦ x.graph.distinctVertices.length)
      encDominatingSet encUnary := (length_list encNat).comp hvs
  have hn_bin : ComputableInPolyTime
      (fun x : DominatingSetInstance ↦ x.graph.distinctVertices.length)
      encDominatingSet encNat := unary_to_binary.comp hn_un
  have hmat : ComputableInPolyTime
      (fun x : DominatingSetInstance ↦
        (List.range x.graph.distinctVertices.length).map fun i ↦
          (List.range x.graph.distinctVertices.length).map fun j ↦
            if decide (i = j) ||
                x.graph.adjBool (x.graph.distinctVertices.getD i 0)
                  (x.graph.distinctVertices.getD j 0)
            then (0 : ℚ)
            else ((x.bound + 1 : ℕ) : ℚ))
      encDominatingSet (encList (encList encRat)) := by
    apply mapWithInput (ComputableInPolyTime.range.comp hn_un)
    apply mapWithInput
      (ComputableInPolyTime.range.comp (hn_un.comp (fst encDominatingSet encUnary)))
    have hx : ComputableInPolyTime
        (fun q : (DominatingSetInstance × ℕ) × ℕ ↦ q.1.1)
        (encPair (encPair encDominatingSet encUnary) encUnary) encDominatingSet :=
      (fst encDominatingSet encUnary).comp (fst (encPair encDominatingSet encUnary) encUnary)
    have hfi : ComputableInPolyTime
        (fun q : (DominatingSetInstance × ℕ) × ℕ ↦ q.1.2)
        (encPair (encPair encDominatingSet encUnary) encUnary) encUnary :=
      (snd encDominatingSet encUnary).comp (fst (encPair encDominatingSet encUnary) encUnary)
    have hfj : ComputableInPolyTime
        (fun q : (DominatingSetInstance × ℕ) × ℕ ↦ q.2)
        (encPair (encPair encDominatingSet encUnary) encUnary) encUnary :=
      snd (encPair encDominatingSet encUnary) encUnary
    exact ite'
      (bool_or' (decide_eq' hfi hfj)
        (Graph.computableInPolyTime_adjBool_comp (hG.comp hx)
          (listGetDWithInput (hvs.comp hx) hfi 0)
          (listGetDWithInput (hvs.comp hx) hfj 0)))
      (const (0 : ℚ))
      (rat_natCast.comp (binary_add' (hk.comp hx) (const 1)))
  unfold fromDominatingSet
  dsimp only
  exact ite' (decide_eq' hn_un (const 0))
    (ite' (decide_eq' hk (const 0)) (const yesInstance) (const noInstance))
    (ite' (decide_eq' hk (const 0)) (const noInstance)
      (ite' (binary_le' hk hn_bin)
        (encUFL_mk_polyTime hn_un hn_un
          (ComputableInPolyTime.replicate hn_un (const (1 : ℚ)))
          hmat
          (rat_natCast.comp hk))
        (const noInstance)))

theorem fromDominatingSet_mem_iff (x : DominatingSetInstance) :
    fromDominatingSet x ∈ UncapacitatedFacilityLocation ↔ x ∈ DominatingSet := by
  obtain ⟨G, k⟩ := x
  unfold fromDominatingSet
  dsimp only
  set vs := G.distinctVertices
  set n := vs.length
  by_cases hn0 : n = 0
  · simp only [decide_eq_true hn0, ↓reduceIte]
    have hcard0 : G.vertices.toFinset.card = 0 := by
      rw [← Graph.length_distinctVertices]; exact hn0
    by_cases hk0 : k = 0
    · simp only [decide_eq_true hk0, ↓reduceIte]
      refine ⟨fun _ ↦ ?_, fun _ ↦ yesInstance_mem⟩
      rw [mem_DominatingSet_iff_exists_card_le, hcard0, hk0]
      refine ⟨le_rfl, ∅, by simp, fun v hv ↦ ?_, by simp⟩
      have : v ∈ G.vertices.toFinset := List.mem_toFinset.mpr hv
      rw [card_eq_zero.mp hcard0] at this
      exact (notMem_empty v this).elim
    · simp only [decide_eq_false hk0, Bool.false_eq_true, ↓reduceIte]
      refine ⟨fun h ↦ (noInstance_notMem h).elim, fun h ↦ ?_⟩
      have hle := (mem_DominatingSet_iff_exists_card_le.mp h).1
      omega
  · simp only [decide_eq_false hn0, Bool.false_eq_true, ↓reduceIte]
    have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
    by_cases hk0 : k = 0
    · simp only [decide_eq_true hk0, ↓reduceIte]
      refine ⟨fun h ↦ (noInstance_notMem h).elim, fun h ↦ ?_⟩
      obtain ⟨D, _, hD, hDcard⟩ := mem_DominatingSet_iff.mp h
      have hDemp : D = ∅ := card_eq_zero.mp (hDcard.trans hk0)
      have hne : vs ≠ [] := fun hnil ↦ by simp [n, hnil] at hnpos
      obtain ⟨v, hv⟩ := List.exists_mem_of_ne_nil vs hne
      have hv_dom := hD v (Graph.mem_distinctVertices.mp hv)
      simp [hDemp] at hv_dom
    · simp only [decide_eq_false hk0, Bool.false_eq_true, ↓reduceIte]
      have hk1 : 1 ≤ k := Nat.pos_of_ne_zero hk0
      by_cases hkle : k ≤ n
      · simp only [decide_eq_true hkle, ↓reduceIte]
        set svc := (List.range n).map fun i ↦
          (List.range n).map fun j ↦
            if decide (i = j) || G.adjBool (vs.getD i 0) (vs.getD j 0) then (0 : ℚ)
            else ((k + 1 : ℕ) : ℚ)
        have hsvc_entry : ∀ i j : Fin n,
            uflServiceEntry svc i.1 j.1 =
              if i = j ∨ G.adjBool (vs.getD i.1 0) (vs.getD j.1 0) = true then (0 : ℚ)
              else ((k + 1 : ℕ) : ℚ) := by
          intro i j
          unfold uflServiceEntry
          simp only [svc, List.getD_eq_getElem?_getD, List.getElem?_map,
            List.getElem?_range i.2, Option.map_some, Option.getD_some,
            List.getElem?_range j.2]
          by_cases hij : i = j
          · subst hij; simp
          · have hij_val : i.1 ≠ j.1 := Fin.val_ne_of_ne hij
            have hdec : decide (i.1 = j.1) = false := decide_eq_false hij_val
            rw [hdec, Bool.false_or]
            simp only [hij, false_or]
        have hopen_entry : ∀ j : Fin n, (List.replicate n (1 : ℚ)).getD j.1 0 = 1 := by
          intro j
          simp [List.getD_eq_getElem?_getD, j.2]
        constructor
        · rintro ⟨_, _, F', hF'ne, assign, hcost⟩
          dsimp at F' hF'ne assign hcost
          rw [mem_DominatingSet_iff_exists_card_le]
          have hn_card : G.vertices.toFinset.card = n := (Graph.length_distinctVertices G).symm
          rw [hn_card]
          have hopen_sum : ∑ j ∈ F', (List.replicate n (1 : ℚ)).getD j.1 0 = (F'.card : ℚ) := by
            rw [sum_congr rfl fun j _ ↦ hopen_entry j]
            simp
          have hsvc_nn : ∀ i : Fin n, 0 ≤ uflServiceEntry svc i.1 (assign i).1.1 := by
            intro i
            rw [hsvc_entry]
            split_ifs <;> positivity
          have hF'_le : F'.card ≤ k := by
            have : (F'.card : ℚ) ≤ (k : ℚ) := by
              calc
                (F'.card : ℚ) = ∑ j ∈ F', (List.replicate n (1 : ℚ)).getD j.1 0 := hopen_sum.symm
                _ ≤ (∑ j ∈ F', (List.replicate n (1 : ℚ)).getD j.1 0) +
                      ∑ i : Fin n, uflServiceEntry svc i.1 (assign i).1.1 :=
                  le_add_of_nonneg_right (sum_nonneg fun i _ ↦ hsvc_nn i)
                _ ≤ (k : ℚ) := hcost
            exact_mod_cast this
          have hall_zero : ∀ i : Fin n,
              i = (assign i).1 ∨
                G.toSimpleGraph.Adj (vs.getD i.1 0) (vs.getD (assign i).1.1 0) := by
            intro i
            rw [← Graph.adjBool_eq_true_iff]
            by_contra hnot
            have hval : uflServiceEntry svc i.1 (assign i).1.1 = ((k + 1 : ℕ) : ℚ) := by
              rw [hsvc_entry]
              split_ifs
              rfl
            have hF'1 : (1 : ℚ) ≤ (F'.card : ℚ) := by exact_mod_cast hF'ne.card_pos
            have hsingle : ((k + 1 : ℕ) : ℚ) ≤
              ∑ i' : Fin n, uflServiceEntry svc i'.1 (assign i').1.1 := by
              rw [← hval]
              exact single_le_sum (fun i' _ ↦ hsvc_nn i') (mem_univ i)
            rw [hopen_sum] at hcost
            push_cast at hsingle
            linarith
          let S : Finset ℕ := F'.image fun j ↦ vs.getD j.1 0
          refine ⟨hkle, S, fun v hv ↦ ?_, fun v hv ↦ ?_, ?_⟩
          · obtain ⟨j, _, rfl⟩ := mem_image.mp hv
            exact Graph.mem_distinctVertices.mp (List.getD_mem 0 j.2)
          · have hv_vs : v ∈ vs := Graph.mem_distinctVertices.mpr hv
            obtain ⟨i_nat, hi_lt, rfl⟩ := List.getElem_of_mem hv_vs
            let i : Fin n := ⟨i_nat, hi_lt⟩
            have hvi : vs[i_nat] = vs.getD i.1 0 := (List.getD_eq_getElem vs 0 hi_lt).symm
            rcases hall_zero i with hEq | hadj
            · left
              rw [hvi, hEq]
              exact mem_image_of_mem _ (assign i).2
            · right
              refine ⟨vs.getD (assign i).1.1 0, mem_image_of_mem _ (assign i).2, ?_⟩
              rwa [hvi]
          · exact card_image_le.trans hF'_le
        · intro hmem
          obtain ⟨D, hDV, hD, hDcard⟩ := mem_DominatingSet_iff.mp hmem
          let F' : Finset (Fin n) := univ.filter fun j : Fin n ↦ vs.getD j.1 0 ∈ D
          have hbij : F'.image (fun j : Fin n ↦ vs.getD j.1 0) = D := by
            ext v
            simp only [mem_image, F', mem_filter, mem_univ, true_and]
            constructor
            · rintro ⟨j, hjD, rfl⟩; exact hjD
            · intro hvD
              have hv_vs : v ∈ vs := Graph.mem_distinctVertices.mpr (hDV v hvD)
              obtain ⟨j_nat, hj_lt, rfl⟩ := List.getElem_of_mem hv_vs
              exact ⟨⟨j_nat, hj_lt⟩,
                by simpa [List.getD_eq_getElem?_getD, hj_lt] using hvD,
                List.getD_eq_getElem vs 0 hj_lt⟩
          have hinj_vs : Set.InjOn (fun j : Fin n ↦ vs.getD j.1 0) (F' : Set (Fin n)) := by
            intro j₁ _ j₂ _ hEq
            dsimp only at hEq
            apply Fin.ext
            rw [List.getD_eq_getElem vs 0 j₁.2, List.getD_eq_getElem vs 0 j₂.2] at hEq
            exact G.nodup_distinctVertices.getElem_inj_iff.mp hEq
          have hF'_card : F'.card = k := by
            rw [← card_image_of_injOn hinj_vs, hbij, hDcard]
          have hF'_ne : F'.Nonempty := card_pos.mp (by omega)
          have hdom_idx : ∀ i : Fin n, ∃ j ∈ F',
              i = j ∨ G.adjBool (vs.getD i.1 0) (vs.getD j.1 0) = true := by
            intro i
            have hiV : vs.getD i.1 0 ∈ G.vertices :=
              Graph.mem_distinctVertices.mp (List.getD_mem 0 i.2)
            rcases hD (vs.getD i.1 0) hiV with hiD | ⟨s, hsD, hadj⟩
            · exact ⟨i, mem_filter.mpr ⟨mem_univ i, hiD⟩, Or.inl rfl⟩
            · rw [← hbij, mem_image] at hsD
              obtain ⟨j, hjF', rfl⟩ := hsD
              exact ⟨j, hjF', Or.inr ((Graph.adjBool_eq_true_iff G _ _).mpr hadj)⟩
          let assign (i : Fin n) : F' :=
            ⟨Classical.choose (hdom_idx i), (Classical.choose_spec (hdom_idx i)).1⟩
          refine ⟨fun j ↦ by rw [hopen_entry]; norm_num,
            fun i j ↦ by rw [hsvc_entry]; split_ifs <;> positivity,
            F', hF'_ne, assign, ?_⟩
          have h1 : ∑ j ∈ F', (List.replicate n (1 : ℚ)).getD j.1 0 = (k : ℚ) := by
            rw [sum_congr rfl fun j _ ↦ hopen_entry j]
            simp [hF'_card]
          have h2 : ∑ i : Fin n, uflServiceEntry svc i.1 (assign i).1.1 = 0 := by
            refine sum_eq_zero fun i _ ↦ ?_
            have hcond := (Classical.choose_spec (hdom_idx i)).2
            rw [hsvc_entry]
            split_ifs with hc
            · rfl
            · dsimp [assign] at hc
              exact (hc hcond).elim
          rw [h1, h2, add_zero]
      · simp only [decide_eq_false hkle, Bool.false_eq_true, ↓reduceIte]
        refine ⟨fun h ↦ (noInstance_notMem h).elim, fun h ↦ ?_⟩
        have hle := (mem_DominatingSet_iff_exists_card_le.mp h).1
        rw [← Graph.length_distinctVertices] at hle
        exact (hkle hle).elim

end UncapacitatedFacilityLocation

/-- `DominatingSet` reduces in polynomial time to `UncapacitatedFacilityLocation`. -/
theorem polyTimeReducible_DominatingSet_UncapacitatedFacilityLocation :
    PolyTimeReducible encDominatingSet encUFL DominatingSet UncapacitatedFacilityLocation :=
  ⟨UncapacitatedFacilityLocation.fromDominatingSet,
    UncapacitatedFacilityLocation.computableInPolyTime_fromDominatingSet,
    fun x ↦ (UncapacitatedFacilityLocation.fromDominatingSet_mem_iff x).symm⟩

/-- `UncapacitatedFacilityLocation` is `NP`-hard. -/
theorem UncapacitatedFacilityLocation_npHard : NPHard encUFL UncapacitatedFacilityLocation :=
  DominatingSet_npHard.trans polyTimeReducible_DominatingSet_UncapacitatedFacilityLocation

/-- **Uncapacitated Facility Location (UFL) is `NP`-complete.** -/
theorem UncapacitatedFacilityLocation_npComplete :
    NPComplete encUFL UncapacitatedFacilityLocation :=
  ⟨UncapacitatedFacilityLocation.mem_NP, UncapacitatedFacilityLocation_npHard⟩

end CslibFrontier.Computability.Complexity
