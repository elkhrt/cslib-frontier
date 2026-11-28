/-
Copyright (c) 2026 The cslib-frontier contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CslibFrontier.Computability.Complexity.Problems.NAEThreeSAT
public import CslibFrontier.Computability.Complexity.EuclideanKMeans

import CslibFrontier.Computability.Complexity.Classes.NP.Witness
import CslibFrontier.Computability.Complexity.Problems.SAT.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Rat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.EqualityPrimitives
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListBinaryLookup
import CslibFrontier.Foundations.Data.List.GetD
import Mathlib.Data.List.GetD
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# NP-Completeness of Euclidean `2`-Means and `k`-Means Clustering

This module proves NP-hardness and NP-completeness (under standard Lean axioms) on multi-tape Turing
machines for **Euclidean `2`-Means (`TwoMeans`)** and **Euclidean `k`-Means (`EuclideanKMeans`)**
via a polynomial-time many-one reduction from `Cslib.Complexity.NAEEUThreeSAT`
(`TwoMeans.fromNAEEUThreeSAT`) that establishes an explicit rational additive cost gap
(`TwoMeans.fromNAEEUThreeSAT_gap`) between satisfiable and unsatisfiable instances.

## Main definitions

- `CslibFrontier.Computability.Complexity.TwoMeans.yesInstance`,
  `CslibFrontier.Computability.Complexity.TwoMeans.noInstance`,
  `CslibFrontier.Computability.Complexity.TwoMeans.gapOf`,
  `CslibFrontier.Computability.Complexity.TwoMeans.fromNAEEUThreeSAT`: polynomial-time gap
  reduction from `NAEEUThreeSAT` to `TwoMeans`.

## Main results

- `CslibFrontier.Computability.Complexity.TwoMeans.fromNAEEUThreeSAT_gap`,
  `CslibFrontier.Computability.Complexity.TwoMeans.fromNAEEUThreeSAT_mem_iff`,
  `CslibFrontier.Computability.Complexity.TwoMeans.fromNAEEUThreeSAT_mem_EuclideanKMeans_iff`.
- `CslibFrontier.Computability.Complexity.polyTimeReducible_NAEEUThreeSAT_TwoMeans`,
  `CslibFrontier.Computability.Complexity.polyTimeReducible_NAEEUThreeSAT_EuclideanKMeans`.
- `CslibFrontier.Computability.Complexity.TwoMeans_npHard`,
  `CslibFrontier.Computability.Complexity.TwoMeans_npComplete`,
  `CslibFrontier.Computability.Complexity.EuclideanKMeans_npHard`,
  `CslibFrontier.Computability.Complexity.EuclideanKMeans_npComplete`.

## Tags

computational complexity, NP-completeness, 2-means, k-means clustering, NAE-3SAT
-/

public section

namespace CslibFrontier.Computability.Complexity

open Finset Cslib.Complexity Cslib.Logic.PL Turing.MultiTapeTM ComputableInPolyTime

namespace TwoMeans

private def kmDedupNat (S : List ℕ) : List ℕ :=
  selectDistinct S (List.replicate S.length true)

private lemma mem_kmDedupNat {S : List ℕ} {v : ℕ} : v ∈ kmDedupNat S ↔ v ∈ S :=
  mem_selectDistinct_replicate

private lemma nodup_kmDedupNat (S : List ℕ) : (kmDedupNat S).Nodup :=
  nodup_selectDistinct _ _

@[local fun_prop]
private theorem computableInPolyTime_kmDedupNat :
    ComputableInPolyTime kmDedupNat (encList encNat) (encList encNat) := by
  unfold kmDedupNat
  fun_prop

private def naeVars (φ : CNF ℕ) : List ℕ :=
  kmDedupNat φ.vars

private lemma mem_naeVars {φ : CNF ℕ} {u : ℕ} : u ∈ naeVars φ ↔ u ∈ φ.vars :=
  mem_kmDedupNat

private lemma nodup_naeVars (φ : CNF ℕ) : (naeVars φ).Nodup :=
  nodup_kmDedupNat _

@[local fun_prop]
private theorem computableInPolyTime_naeVars :
    ComputableInPolyTime naeVars encCNF (encList encNat) :=
  computableInPolyTime_kmDedupNat.comp SAT.computableInPolyTime_vars

private lemma dite_lt_pos_km {α : Type*} {a k : ℕ} (ha : a < k)
    (t : a < k → α) (e : ¬a < k → α) : dite (a < k) t e = t ha := by
  split_ifs
  rfl

/-- Fixed accepted `TwoMeans` instance (`n = 2, d = 1, k = 2, bound = 0`). -/
def yesInstance : EuclideanKMeansInstance :=
  ⟨2, 1, [[0], [2]], 2, 0⟩

/-- Fixed rejected `TwoMeans` instance (`n = 3, d = 1, points = [[0], [4], [8]], k = 2, bound = 2`)
whose optimal `2`-means cost is at least `4 = 2 + 2`. -/
def noInstance : EuclideanKMeansInstance :=
  ⟨3, 1, [[0], [4], [8]], 2, 2⟩

private theorem yesInstance_mem : yesInstance ∈ TwoMeans := by
  refine ⟨rfl, ?_⟩
  obtain ⟨P, hPcard, hPsum⟩ :=
    EuclideanKMeans.exists_finpartition_sum_of_assign
      (fun v : Fin 2 ↦ v.1)
      (fun a ↦ if h : a < 2 then ⟨a, h⟩ else ⟨0, by decide⟩)
      (fun v ↦ v.2)
      (fun a ha ↦ by rw [dite_lt_pos_km ha])
      (kmeansClusterCost 1 [[0], [2]])
  refine ⟨P, hPcard, ?_⟩
  change kmeansCost 2 1 [[0], [2]] P ≤ 0
  rw [kmeansCost, hPsum]
  refine sum_nonpos fun a ha ↦ ?_
  have ha' : a < 2 := Finset.mem_range.mp ha
  have hsub : (univ.filter fun v : Fin 2 ↦ v.1 = a) = {⟨a, ha'⟩} := by
    ext v
    simp [Fin.ext_iff]
  rw [hsub]
  simp [kmeansClusterCost, centroidCoord]

private theorem noInstance_gap (P : Finpartition (univ : Finset (Fin 3)))
    (hPcard : P.parts.card = 2) :
    (4 : ℚ) ≤ kmeansCost 3 1 [[0], [4], [8]] P := by
  have hex2 : ∃ C ∈ P.parts, 2 ≤ C.card := by
    by_contra hall
    push Not at hall
    have hs : (P.parts.sup id).card = 3 := by rw [P.sup_parts, card_univ, Fintype.card_fin]
    have hsum3 : ∑ C ∈ P.parts, C.card = 3 := by
      calc
        ∑ C ∈ P.parts, C.card = (P.parts.sup id).card := by
          rw [sup_eq_biUnion, card_biUnion (fun A hA B hB hAB ↦ P.disjoint hA hB hAB)]
          rfl
        _ = 3 := hs
    have hle2 : ∑ C ∈ P.parts, C.card ≤ P.parts.card := by
      calc
        ∑ C ∈ P.parts, C.card ≤ ∑ _C ∈ P.parts, 1 := sum_le_sum fun C hC ↦ by
          have := hall C hC; omega
        _ = P.parts.card := by simp
    omega
  obtain ⟨C, hCP, hC2⟩ := hex2
  obtain ⟨i, hi, j, hj, hij⟩ := one_lt_card.mp (by omega : 1 < C.card)
  have hCne : C.Nonempty := ⟨i, hi⟩
  have hCle3 : C.card ≤ 3 := (card_le_univ C).trans_eq (Fintype.card_fin 3)
  have hpair16 : (16 : ℚ) ≤ (pointCoord [[0], [4], [8]] i.1 0 -
      pointCoord [[0], [4], [8]] j.1 0) ^ 2 := by
    fin_cases i <;> fin_cases j
    all_goals
      first
      | exact (hij rfl).elim
      | norm_num [pointCoord]
  have hpair_symm : (16 : ℚ) ≤ (pointCoord [[0], [4], [8]] j.1 0 -
      pointCoord [[0], [4], [8]] i.1 0) ^ 2 := by
    have : (pointCoord [[0], [4], [8]] j.1 0 - pointCoord [[0], [4], [8]] i.1 0) ^ 2 =
        (pointCoord [[0], [4], [8]] i.1 0 - pointCoord [[0], [4], [8]] j.1 0) ^ 2 := by ring
    linarith
  have hCcost : (4 : ℚ) ≤ kmeansClusterCost 1 [[0], [4], [8]] C := by
    rw [kmeansClusterCost_eq_half_pairwise 1 [[0], [4], [8]] hCne]
    have hnum : (32 : ℚ) ≤ ∑ u ∈ C, ∑ w ∈ C, ∑ r ∈ Finset.range 1,
        (pointCoord [[0], [4], [8]] u.1 r - pointCoord [[0], [4], [8]] w.1 r) ^ 2 := by
      have hsub : ({i, j} : Finset (Fin 3)) ⊆ C := by
        intro x hx
        simp only [mem_insert, mem_singleton] at hx
        rcases hx with rfl | rfl <;> assumption
      have h1 : ∑ u ∈ ({i, j} : Finset (Fin 3)), ∑ w ∈ ({i, j} : Finset (Fin 3)),
          ∑ r ∈ Finset.range 1,
            (pointCoord [[0], [4], [8]] u.1 r - pointCoord [[0], [4], [8]] w.1 r) ^ 2 ≤
          ∑ u ∈ C, ∑ w ∈ C, ∑ r ∈ Finset.range 1,
            (pointCoord [[0], [4], [8]] u.1 r - pointCoord [[0], [4], [8]] w.1 r) ^ 2 := by
        refine (sum_le_sum fun u _ ↦ sum_le_sum_of_subset_of_nonneg hsub
          fun _ _ _ ↦ sum_nonneg fun _ _ ↦ sq_nonneg _).trans ?_
        exact sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ ↦
          sum_nonneg fun _ _ ↦ sum_nonneg fun _ _ ↦ sq_nonneg _
      rw [sum_pair hij, sum_pair hij, sum_pair hij] at h1
      simp only [Finset.sum_range_one, sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        zero_pow] at h1 ⊢
      linarith
    have hden_pos : (0 : ℚ) < 2 * (C.card : ℚ) := by
      have : 0 < C.card := hCne.card_pos
      positivity
    have hden_le : 2 * (C.card : ℚ) ≤ 6 := by
      have : (C.card : ℚ) ≤ 3 := by exact_mod_cast hCle3
      linarith
    rw [le_div_iff₀ hden_pos]
    linarith
  exact hCcost.trans (single_le_sum (fun B _ ↦ kmeansClusterCost_nonneg 1 [[0], [4], [8]] B) hCP)

private def naeClausePairVal (u : ℕ) (pol : Bool) (ℓA ℓB : Literal ℕ) : ℚ :=
  if decide (u = ℓA.1) then
    if pol == ℓA.2 then (1 : ℚ) else -1
  else if decide (u = ℓB.1) then
    if pol == ℓB.2 then (-1 : ℚ) else 1
  else 0

private def naeCoordVal (V : List ℕ) (φ : CNF ℕ) (L : ℚ) (p r : ℕ) : ℚ :=
  let v := V.length
  let varIdx := p / 2
  let pol := decide (p % 2 = 0)
  if decide (r < v) then
    if decide (r = varIdx) then (if pol then L else -L) else 0
  else
    let t := r - v
    let c := φ.getD (t / 3) []
    let slot := t % 3
    let nextSlot := (slot + 1) % 3
    naeClausePairVal (V.getD varIdx 0) pol (c.getD slot (0, false)) (c.getD nextSlot (0, false))

private def naePoints (φ : CNF ℕ) : List (List ℚ) :=
  let V := naeVars φ
  let v := V.length
  let m := φ.length
  let L : ℚ := (((3 * m + 4) * v : ℕ) : ℚ)
  (List.range (2 * v)).map fun p ↦
    (List.range (v + 3 * m)).map fun r ↦ naeCoordVal V φ L p r

/-- Strict rational additive cost gap produced by `TwoMeans.fromNAEEUThreeSAT`. -/
def gapOf (φ : CNF ℕ) : ℚ :=
  if EUThreeSAT.syntaxCheck φ && decide (1 ≤ φ.length) then
    16 / ((naeVars φ).length : ℚ)
  else 2

/-- Polynomial-time reduction from `NAEEUThreeSAT` to `TwoMeans`. -/
def fromNAEEUThreeSAT (φ : CNF ℕ) : EuclideanKMeansInstance :=
  if !EUThreeSAT.syntaxCheck φ then noInstance
  else if decide (φ.length = 0) then yesInstance
  else
    let V := naeVars φ
    let v := V.length
    let m := φ.length
    let L : ℚ := (((3 * m + 4) * v : ℕ) : ℚ)
    let bound : ℚ := 2 * ((v - 1 : ℕ) : ℚ) * (L * L) + 12 * (m : ℚ) - (16 * (m : ℚ)) / (v : ℚ)
    ⟨2 * v, v + 3 * m, naePoints φ, 2, bound⟩

@[fun_prop]
theorem computableInPolyTime_fromNAEEUThreeSAT :
    ComputableInPolyTime fromNAEEUThreeSAT encCNF encEuclideanKMeans := by
  have hV : ComputableInPolyTime naeVars encCNF (encList encNat) :=
    computableInPolyTime_naeVars
  have hv : ComputableInPolyTime (fun φ : CNF ℕ ↦ (naeVars φ).length) encCNF encUnary :=
    (length_list encNat).comp hV
  have hm : ComputableInPolyTime (fun φ : CNF ℕ ↦ φ.length) encCNF encUnary :=
    SAT.computableInPolyTime_length id'
  have hv_bin : ComputableInPolyTime (fun φ : CNF ℕ ↦ (naeVars φ).length) encCNF encNat :=
    unary_to_binary.comp hv
  have hm_bin : ComputableInPolyTime (fun φ : CNF ℕ ↦ φ.length) encCNF encNat :=
    unary_to_binary.comp hm
  have hL : ComputableInPolyTime
      (fun φ : CNF ℕ ↦ (((3 * φ.length + 4) * (naeVars φ).length : ℕ) : ℚ)) encCNF encRat :=
    rat_natCast.comp
      (binary_mul' (binary_add' (binary_mul' (const 3) hm_bin) (const 4)) hv_bin)
  have h2v : ComputableInPolyTime (fun φ : CNF ℕ ↦ 2 * (naeVars φ).length) encCNF encUnary :=
    unary_mul' (const 2) hv
  have hd : ComputableInPolyTime
      (fun φ : CNF ℕ ↦ (naeVars φ).length + 3 * φ.length) encCNF encUnary :=
    unary_add' hv (unary_mul' (const 3) hm)
  have hpts : ComputableInPolyTime naePoints encCNF (encList (encList encRat)) := by
    unfold naePoints
    dsimp only
    refine mapWithInput (ComputableInPolyTime.range.comp h2v) ?_
    refine mapWithInput (ComputableInPolyTime.range.comp (hd.comp (fst _ _))) ?_
    let E2 := encPair (encPair encCNF encUnary) encUnary
    have hφ2 : ComputableInPolyTime (fun q : (CNF ℕ × ℕ) × ℕ ↦ q.1.1) E2 encCNF :=
      (fst _ _).comp (fst _ _)
    have hp2 : ComputableInPolyTime (fun q : (CNF ℕ × ℕ) × ℕ ↦ q.1.2) E2 encUnary :=
      (snd _ _).comp (fst _ _)
    have hr2 : ComputableInPolyTime (fun q : (CNF ℕ × ℕ) × ℕ ↦ q.2) E2 encUnary := snd _ _
    have hp_bin : ComputableInPolyTime (fun q : (CNF ℕ × ℕ) × ℕ ↦ q.1.2) E2 encNat :=
      unary_to_binary.comp hp2
    have hr_bin : ComputableInPolyTime (fun q : (CNF ℕ × ℕ) × ℕ ↦ q.2) E2 encNat :=
      unary_to_binary.comp hr2
    have hv2_bin : ComputableInPolyTime
        (fun q : (CNF ℕ × ℕ) × ℕ ↦ (naeVars q.1.1).length) E2 encNat := hv_bin.comp hφ2
    have hL2 : ComputableInPolyTime
        (fun q : (CNF ℕ × ℕ) × ℕ ↦
          (((3 * q.1.1.length + 4) * (naeVars q.1.1).length : ℕ) : ℚ)) E2 encRat := hL.comp hφ2
    have hvarIdx : ComputableInPolyTime (fun q : (CNF ℕ × ℕ) × ℕ ↦ q.1.2 / 2) E2 encNat :=
      binary_div' hp_bin (const 2)
    have hpol : ComputableInPolyTime
        (fun q : (CNF ℕ × ℕ) × ℕ ↦ decide (q.1.2 % 2 = 0)) E2 encBool :=
      decide_eq' (binary_mod' hp_bin (const 2)) (const 0)
    have hu : ComputableInPolyTime
        (fun q : (CNF ℕ × ℕ) × ℕ ↦ (naeVars q.1.1).getD (q.1.2 / 2) 0) E2 encNat :=
      listGetD_binary (encA := encNat) 0 (hV.comp hφ2) hvarIdx
    have ht : ComputableInPolyTime
        (fun q : (CNF ℕ × ℕ) × ℕ ↦ q.2 - (naeVars q.1.1).length) E2 encNat :=
      binary_sub' hr_bin hv2_bin
    have hφ2' : ComputableInPolyTime (fun q : (CNF ℕ × ℕ) × ℕ ↦ q.1.1) E2
        (encList (encList (encPair encNat encBool))) := by
      simpa only [encCNF] using hφ2
    have hc : ComputableInPolyTime
        (fun q : (CNF ℕ × ℕ) × ℕ ↦ q.1.1.getD ((q.2 - (naeVars q.1.1).length) / 3) [])
        E2 (encList (encPair encNat encBool)) :=
      listGetD_binary (encA := encList (encPair encNat encBool)) ([] : Clause ℕ) hφ2'
        (binary_div' ht (const 3))
    have hslot : ComputableInPolyTime
        (fun q : (CNF ℕ × ℕ) × ℕ ↦ (q.2 - (naeVars q.1.1).length) % 3) E2 encNat :=
      binary_mod' ht (const 3)
    have hnext : ComputableInPolyTime
        (fun q : (CNF ℕ × ℕ) × ℕ ↦ ((q.2 - (naeVars q.1.1).length) % 3 + 1) % 3) E2 encNat :=
      binary_mod' (binary_add' hslot (const 1)) (const 3)
    have hℓA : ComputableInPolyTime
        (fun q : (CNF ℕ × ℕ) × ℕ ↦
          (q.1.1.getD ((q.2 - (naeVars q.1.1).length) / 3) []).getD
            ((q.2 - (naeVars q.1.1).length) % 3) (0, false))
        E2 (encPair encNat encBool) :=
      listGetD_binary (encA := encPair encNat encBool) (0, false) hc hslot
    have hℓB : ComputableInPolyTime
        (fun q : (CNF ℕ × ℕ) × ℕ ↦
          (q.1.1.getD ((q.2 - (naeVars q.1.1).length) / 3) []).getD
            (((q.2 - (naeVars q.1.1).length) % 3 + 1) % 3) (0, false))
        E2 (encPair encNat encBool) :=
      listGetD_binary (encA := encPair encNat encBool) (0, false) hc hnext
    unfold naeCoordVal naeClausePairVal
    dsimp only
    refine ite' (binary_lt' hr_bin hv2_bin)
      (ite' (decide_eq' hr_bin hvarIdx) (ite' hpol hL2 (rat_neg' hL2)) (const (0 : ℚ))) ?_
    exact ite' (decide_eq' hu ((fst _ _).comp hℓA))
      (ite' (ComputableInPolyTime.beq hpol ((snd _ _).comp hℓA)) (const (1 : ℚ)) (const (-1 : ℚ)))
      (ite' (decide_eq' hu ((fst _ _).comp hℓB))
        (ite' (ComputableInPolyTime.beq hpol ((snd _ _).comp hℓB))
          (const (-1 : ℚ)) (const (1 : ℚ)))
        (const (0 : ℚ)))
  have hbound : ComputableInPolyTime
      (fun φ : CNF ℕ ↦
        let v := (naeVars φ).length
        let m := φ.length
        let L : ℚ := (((3 * m + 4) * v : ℕ) : ℚ)
        2 * ((v - 1 : ℕ) : ℚ) * (L * L) + 12 * (m : ℚ) - (16 * (m : ℚ)) / (v : ℚ))
      encCNF encRat := by
    dsimp only
    exact rat_sub'
      (rat_add'
        (rat_mul' (rat_mul' (const 2) (rat_natCast.comp (binary_sub' hv_bin (const 1))))
          (rat_mul' hL hL))
        (rat_mul' (const 12) (rat_natCast.comp hm_bin)))
      (rat_div' (rat_mul' (const 16) (rat_natCast.comp hm_bin)) (rat_natCast.comp hv_bin))
  unfold fromNAEEUThreeSAT
  dsimp only
  exact ite' (bool_not.comp EUThreeSAT.computableInPolyTime_syntaxCheck) (const noInstance)
    (ite' (decide_eq' hm (const 0)) (const yesInstance)
      (encEuclideanKMeans_mk_polyTime h2v hd hpts (const 2) hbound))

private lemma three_le_length_naeVars {φ : CNF ℕ} (hsyn : φ.IsExactThreeDistinct)
    (hm : 1 ≤ φ.length) : 3 ≤ (naeVars φ).length := by
  have hc0_mem : φ[0]'(by omega) ∈ φ := List.getElem_mem _
  obtain ⟨ℓ₀, ℓ₁, ℓ₂, hEq, h01, h02, h12⟩ :=
    Clause.isExactThreeDistinct_iff.mp (hsyn _ hc0_mem)
  have hm0 : ℓ₀.1 ∈ (naeVars φ).toFinset :=
    List.mem_toFinset.mpr (mem_naeVars.mpr (CNF.mem_vars.mpr
      ⟨φ[0]'(by omega), hc0_mem, ℓ₀.2, by rw [hEq]; simp⟩))
  have hm1 : ℓ₁.1 ∈ (naeVars φ).toFinset :=
    List.mem_toFinset.mpr (mem_naeVars.mpr (CNF.mem_vars.mpr
      ⟨φ[0]'(by omega), hc0_mem, ℓ₁.2, by rw [hEq]; simp⟩))
  have hm2 : ℓ₂.1 ∈ (naeVars φ).toFinset :=
    List.mem_toFinset.mpr (mem_naeVars.mpr (CNF.mem_vars.mpr
      ⟨φ[0]'(by omega), hc0_mem, ℓ₂.2, by rw [hEq]; simp⟩))
  have hsub : ({ℓ₀.1, ℓ₁.1, ℓ₂.1} : Finset ℕ) ⊆ (naeVars φ).toFinset := by
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  have hcard3 : ({ℓ₀.1, ℓ₁.1, ℓ₂.1} : Finset ℕ).card = 3 := by
    rw [card_insert_of_notMem (by simp [h01, h02]), card_pair h12]
  calc
    3 = ({ℓ₀.1, ℓ₁.1, ℓ₂.1} : Finset ℕ).card := hcard3.symm
    _ ≤ (naeVars φ).toFinset.card := card_le_card hsub
    _ = (naeVars φ).length := List.toFinset_card_of_nodup (nodup_naeVars φ)

private lemma sum_fin_two_mul (v : ℕ) (f : Fin (2 * v) → ℚ) :
    ∑ p : Fin (2 * v), f p =
      ∑ i : Fin v, (f ⟨2 * i.1, by omega⟩ + f ⟨2 * i.1 + 1, by omega⟩) := by
  let g : ℕ → ℚ := fun p ↦ if hp : p < 2 * v then f ⟨p, hp⟩ else 0
  have hfg : ∀ p : Fin (2 * v), f p = g p.1 := fun p ↦ by
    simp [g, p.2]
  rw [sum_congr rfl fun p _ ↦ hfg p, Fin.sum_univ_eq_sum_range g]
  have hrhs : ∑ i : Fin v, (f ⟨2 * i.1, by omega⟩ + f ⟨2 * i.1 + 1, by omega⟩) =
      ∑ i ∈ Finset.range v, (g (2 * i) + g (2 * i + 1)) := by
    rw [← Fin.sum_univ_eq_sum_range (fun i ↦ g (2 * i) + g (2 * i + 1))]
    refine sum_congr rfl fun i _ ↦ ?_
    have hi0 : 2 * i.1 < 2 * v := by omega
    have hi1 : 2 * i.1 + 1 < 2 * v := by omega
    dsimp [g]
    simp only [hi0, hi1, ↓reduceDIte]
  rw [hrhs]
  have hrange : ∀ k ≤ v, ∑ p ∈ Finset.range (2 * k), g p =
      ∑ i ∈ Finset.range k, (g (2 * i) + g (2 * i + 1)) := by
    intro k hk
    induction k with
    | zero => simp
    | succ k ih =>
      have heq2 : 2 * (k + 1) = 2 * k + 1 + 1 := by omega
      rw [heq2, Finset.sum_range_succ, Finset.sum_range_succ, ih (by omega),
        Finset.sum_range_succ, add_assoc]
  exact hrange v le_rfl

private lemma twoPart_coord_cost {n : ℕ} {C₁ C₂ : Finset (Fin n)}
    (h1 : C₁.Nonempty) (h2 : C₂.Nonempty) (hdisj : Disjoint C₁ C₂)
    (hunion : C₁ ∪ C₂ = (univ : Finset (Fin n))) (a : Fin n → ℚ)
    (hsum0 : ∑ i : Fin n, a i = 0) :
    (∑ i ∈ C₁, (a i - (∑ j ∈ C₁, a j) / (C₁.card : ℚ)) ^ 2) +
      (∑ i ∈ C₂, (a i - (∑ j ∈ C₂, a j) / (C₂.card : ℚ)) ^ 2) =
      (∑ i : Fin n, (a i) ^ 2) -
        ((n : ℚ) / ((C₁.card : ℚ) * (C₂.card : ℚ))) * (∑ i ∈ C₁, a i) ^ 2 := by
  have hm1 : (C₁.card : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr h1.card_pos.ne'
  have hm2 : (C₂.card : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr h2.card_pos.ne'
  have hS : (∑ i ∈ C₁, a i) + (∑ i ∈ C₂, a i) = 0 := by
    rw [← sum_union hdisj, hunion]
    exact hsum0
  have hS2 : (∑ i ∈ C₂, a i) ^ 2 = (∑ i ∈ C₁, a i) ^ 2 := by
    have : ∑ i ∈ C₂, a i = -(∑ i ∈ C₁, a i) := by linarith
    rw [this, neg_sq]
  have hQ : (∑ i ∈ C₁, (a i) ^ 2) + (∑ i ∈ C₂, (a i) ^ 2) = ∑ i : Fin n, (a i) ^ 2 := by
    rw [← sum_union hdisj, hunion]
  have hcard : (C₁.card : ℚ) + (C₂.card : ℚ) = (n : ℚ) := by
    have hc : C₁.card + C₂.card = n := by
      rw [← card_union_of_disjoint hdisj, hunion, card_univ, Fintype.card_fin]
    exact_mod_cast hc
  rw [coord_variance_eq C₁ h1 a, coord_variance_eq C₂ h2 a, hS2, ← hQ, ← hcard]
  field_simp [hm1, hm2]
  ring

private lemma pointCoord_naePoints {φ : CNF ℕ} {p r : ℕ}
    (hp : p < 2 * (naeVars φ).length) (hr : r < (naeVars φ).length + 3 * φ.length) :
    pointCoord (naePoints φ) p r =
      naeCoordVal (naeVars φ) φ
        ((((3 * φ.length + 4) * (naeVars φ).length : ℕ) : ℚ)) p r := by
  simp [naePoints, pointCoord, List.getD_eq_getElem?_getD, hp, hr]

private lemma nae_three_diff_sq (b₀ b₁ b₂ : Bool) :
    let e₀ : ℚ := if b₀ then 1 else -1
    let e₁ : ℚ := if b₁ then 1 else -1
    let e₂ : ℚ := if b₂ then 1 else -1
    (e₀ - e₁) ^ 2 + (e₁ - e₂) ^ 2 + (e₂ - e₀) ^ 2 =
      if (b₀ || b₁ || b₂) && (!b₀ || !b₁ || !b₂) then (8 : ℚ) else 0 := by
  cases b₀ <;> cases b₁ <;> cases b₂ <;> norm_num

private lemma clause_evalNAE_iff_three (σ : ℕ → Bool) (ℓ₀ ℓ₁ ℓ₂ : Literal ℕ) :
    (Clause.eval σ [ℓ₀, ℓ₁, ℓ₂] && Clause.eval (fun u ↦ !σ u) [ℓ₀, ℓ₁, ℓ₂]) =
      ((Literal.eval σ ℓ₀ || Literal.eval σ ℓ₁ || Literal.eval σ ℓ₂) &&
        (!Literal.eval σ ℓ₀ || !Literal.eval σ ℓ₁ || !Literal.eval σ ℓ₂)) := by
  simp only [Clause.eval_cons, Clause.eval_nil, Bool.or_false, Literal.eval_complement]
  cases Literal.eval σ ℓ₀ <;> cases Literal.eval σ ℓ₁ <;> cases Literal.eval σ ℓ₂ <;> rfl

private lemma clausePair_stats {v : ℕ} {V : List ℕ} (hVlen : V.length = v) (hVnd : V.Nodup)
    {ℓA ℓB : Literal ℕ} (hAB : ℓA.1 ≠ ℓB.1) (hAmem : ℓA.1 ∈ V) (hBmem : ℓB.1 ∈ V) :
    (∑ p : Fin (2 * v),
        naeClausePairVal (V.getD (p.1 / 2) 0) (decide (p.1 % 2 = 0)) ℓA ℓB = 0) ∧
      (∑ p : Fin (2 * v),
        (naeClausePairVal (V.getD (p.1 / 2) 0) (decide (p.1 % 2 = 0)) ℓA ℓB) ^ 2 = 4) := by
  obtain ⟨iA_nat, hiA_lt, hiA_eq⟩ := List.getElem_of_mem hAmem
  obtain ⟨iB_nat, hiB_lt, hiB_eq⟩ := List.getElem_of_mem hBmem
  let iA : Fin v := ⟨iA_nat, hVlen ▸ hiA_lt⟩
  let iB : Fin v := ⟨iB_nat, hVlen ▸ hiB_lt⟩
  have hiAB : iA ≠ iB := by
    intro hEq
    apply hAB
    have : iA_nat = iB_nat := congrArg Fin.val hEq
    subst this
    exact hiA_eq.symm.trans hiB_eq
  have hget_iff : ∀ (i : Fin v) (u : ℕ) (j : Fin v),
      V[j.1]'(hVlen.symm ▸ j.2) = u → (V.getD i.1 0 = u ↔ i = j) := by
    intro i u j hju
    have hi' : i.1 < V.length := hVlen.symm ▸ i.2
    have hj' : j.1 < V.length := hVlen.symm ▸ j.2
    rw [List.getD_eq_getElem V 0 hi', ← hju]
    refine ⟨fun h ↦ ?_, fun h ↦ by cases h; rfl⟩
    have hi_idx : V.idxOf V[i.1] = i.1 := hVnd.idxOf_getElem i.1 hi'
    have hj_idx : V.idxOf V[j.1] = j.1 := hVnd.idxOf_getElem j.1 hj'
    rw [h] at hi_idx
    exact Fin.ext (hi_idx.symm.trans hj_idx)
  have hA_iff : ∀ i : Fin v, V.getD i.1 0 = ℓA.1 ↔ i = iA :=
    fun i ↦ hget_iff i ℓA.1 iA hiA_eq
  have hB_iff : ∀ i : Fin v, V.getD i.1 0 = ℓB.1 ↔ i = iB :=
    fun i ↦ hget_iff i ℓB.1 iB hiB_eq
  constructor
  · rw [sum_fin_two_mul]
    refine sum_eq_zero fun i _ ↦ ?_
    have hd0 : (2 * i.1) / 2 = i.1 := Nat.mul_div_right i.1 (by decide)
    have hd1 : (2 * i.1 + 1) / 2 = i.1 := by omega
    have hm0 : decide ((2 * i.1) % 2 = 0) = true :=
      decide_eq_true (Nat.mul_mod_right 2 i.1)
    have hm1 : decide ((2 * i.1 + 1) % 2 = 0) = false :=
      decide_eq_false (by omega)
    rw [hd0, hd1, hm0, hm1]
    unfold naeClausePairVal
    by_cases h1 : V.getD i.1 0 = ℓA.1
    · have d1 : decide (V.getD i.1 0 = ℓA.1) = true := decide_eq_true h1
      rw [d1]
      simp only [↓reduceIte]
      cases ℓA.2 <;> norm_num
    · have d1 : decide (V.getD i.1 0 = ℓA.1) = false := decide_eq_false h1
      by_cases h2 : V.getD i.1 0 = ℓB.1
      · have d2 : decide (V.getD i.1 0 = ℓB.1) = true := decide_eq_true h2
        rw [d1, d2]
        simp only [Bool.false_eq_true, ↓reduceIte]
        cases ℓB.2 <;> norm_num
      · have d2 : decide (V.getD i.1 0 = ℓB.1) = false := decide_eq_false h2
        rw [d1, d2]
        norm_num
  · rw [sum_fin_two_mul]
    have hpair_sq : ∀ i : Fin v,
        (naeClausePairVal (V.getD ((2 * i.1) / 2) 0) (decide ((2 * i.1) % 2 = 0)) ℓA ℓB) ^ 2 +
          (naeClausePairVal (V.getD ((2 * i.1 + 1) / 2) 0)
            (decide ((2 * i.1 + 1) % 2 = 0)) ℓA ℓB) ^ 2 =
        if i = iA ∨ i = iB then 2 else 0 := by
      intro i
      have hd0 : (2 * i.1) / 2 = i.1 := Nat.mul_div_right i.1 (by decide)
      have hd1 : (2 * i.1 + 1) / 2 = i.1 := by omega
      have hm0 : decide ((2 * i.1) % 2 = 0) = true :=
        decide_eq_true (Nat.mul_mod_right 2 i.1)
      have hm1 : decide ((2 * i.1 + 1) % 2 = 0) = false :=
        decide_eq_false (by omega)
      rw [hd0, hd1, hm0, hm1]
      by_cases h1 : i = iA
      · have hA : decide (V.getD i.1 0 = ℓA.1) = true := decide_eq_true ((hA_iff i).mpr h1)
        unfold naeClausePairVal
        rw [hA]
        simp only [h1, true_or, ↓reduceIte]
        cases ℓA.2 <;> norm_num
      · have hA : decide (V.getD i.1 0 = ℓA.1) = false :=
          decide_eq_false fun h ↦ h1 ((hA_iff i).mp h)
        by_cases h2 : i = iB
        · have hB : decide (V.getD i.1 0 = ℓB.1) = true := decide_eq_true ((hB_iff i).mpr h2)
          unfold naeClausePairVal
          rw [hA, hB]
          simp only [h2, or_true, Bool.false_eq_true, ↓reduceIte]
          cases ℓB.2 <;> norm_num
        · have hB : decide (V.getD i.1 0 = ℓB.1) = false :=
            decide_eq_false fun h ↦ h2 ((hB_iff i).mp h)
          unfold naeClausePairVal
          rw [hA, hB]
          have hor : ¬(i = iA ∨ i = iB) := by tauto
          simp only [hor, Bool.false_eq_true, ↓reduceIte]
          norm_num
    rw [sum_congr rfl fun i _ ↦ hpair_sq i, ← sum_filter]
    have hfilt : (univ.filter fun i : Fin v ↦ i = iA ∨ i = iB) = {iA, iB} := by
      ext i
      simp
    rw [hfilt, sum_pair hiAB]
    norm_num

private lemma clausePair_split_sum {v : ℕ} {V : List ℕ} (hVlen : V.length = v) (hVnd : V.Nodup)
    {C₁ : Finset (Fin (2 * v))} (σ : ℕ → Bool)
    (hsplit : ∀ i : Fin v,
      ((⟨2 * i.1, by omega⟩ : Fin (2 * v)) ∈ C₁ ↔ σ (V.getD i.1 0) = true) ∧
      ((⟨2 * i.1 + 1, by omega⟩ : Fin (2 * v)) ∈ C₁ ↔ σ (V.getD i.1 0) = false))
    {ℓA ℓB : Literal ℕ} (hAB : ℓA.1 ≠ ℓB.1) (hAmem : ℓA.1 ∈ V) (hBmem : ℓB.1 ∈ V) :
    ∑ p ∈ C₁, naeClausePairVal (V.getD (p.1 / 2) 0) (decide (p.1 % 2 = 0)) ℓA ℓB =
      (if Literal.eval σ ℓA then (1 : ℚ) else -1) -
        (if Literal.eval σ ℓB then (1 : ℚ) else -1) := by
  obtain ⟨iA_nat, hiA_lt, hiA_eq⟩ := List.getElem_of_mem hAmem
  obtain ⟨iB_nat, hiB_lt, hiB_eq⟩ := List.getElem_of_mem hBmem
  let iA : Fin v := ⟨iA_nat, hVlen ▸ hiA_lt⟩
  let iB : Fin v := ⟨iB_nat, hVlen ▸ hiB_lt⟩
  have hiAB : iA ≠ iB := fun hEq ↦ hAB (by
    have : iA_nat = iB_nat := congrArg Fin.val hEq
    subst this
    exact hiA_eq.symm.trans hiB_eq)
  have hget_iff : ∀ (i : Fin v) (u : ℕ) (j : Fin v),
      V[j.1]'(hVlen.symm ▸ j.2) = u → (V.getD i.1 0 = u ↔ i = j) := by
    intro i u j hju
    have hi' : i.1 < V.length := hVlen.symm ▸ i.2
    have hj' : j.1 < V.length := hVlen.symm ▸ j.2
    rw [List.getD_eq_getElem V 0 hi', ← hju]
    refine ⟨fun h ↦ ?_, fun h ↦ by cases h; rfl⟩
    have hi_idx : V.idxOf V[i.1] = i.1 := hVnd.idxOf_getElem i.1 hi'
    have hj_idx : V.idxOf V[j.1] = j.1 := hVnd.idxOf_getElem j.1 hj'
    rw [h] at hi_idx
    exact Fin.ext (hi_idx.symm.trans hj_idx)
  have hA_iff : ∀ i : Fin v, V.getD i.1 0 = ℓA.1 ↔ i = iA :=
    fun i ↦ hget_iff i ℓA.1 iA hiA_eq
  have hB_iff : ∀ i : Fin v, V.getD i.1 0 = ℓB.1 ↔ i = iB :=
    fun i ↦ hget_iff i ℓB.1 iB hiB_eq
  have hind : ∑ p ∈ C₁, naeClausePairVal (V.getD (p.1 / 2) 0) (decide (p.1 % 2 = 0)) ℓA ℓB =
      ∑ p : Fin (2 * v), if p ∈ C₁ then
        naeClausePairVal (V.getD (p.1 / 2) 0) (decide (p.1 % 2 = 0)) ℓA ℓB else 0 := by
    rw [← sum_filter, filter_univ_mem]
  rw [hind, sum_fin_two_mul]
  have hpair : ∀ i : Fin v,
      (if (⟨2 * i.1, by omega⟩ : Fin (2 * v)) ∈ C₁ then
          naeClausePairVal (V.getD ((2 * i.1) / 2) 0) (decide ((2 * i.1) % 2 = 0)) ℓA ℓB else 0) +
        (if (⟨2 * i.1 + 1, by omega⟩ : Fin (2 * v)) ∈ C₁ then
          naeClausePairVal (V.getD ((2 * i.1 + 1) / 2) 0)
            (decide ((2 * i.1 + 1) % 2 = 0)) ℓA ℓB else 0) =
      (if i = iA then (if Literal.eval σ ℓA then (1 : ℚ) else -1) else 0) +
        (if i = iB then -(if Literal.eval σ ℓB then (1 : ℚ) else -1) else 0) := by
    intro i
    have hd0 : (2 * i.1) / 2 = i.1 := Nat.mul_div_right i.1 (by decide)
    have hd1 : (2 * i.1 + 1) / 2 = i.1 := by omega
    have hm0 : decide ((2 * i.1) % 2 = 0) = true :=
      decide_eq_true (Nat.mul_mod_right 2 i.1)
    have hm1 : decide ((2 * i.1 + 1) % 2 = 0) = false :=
      decide_eq_false (by omega)
    rw [hd0, hd1, hm0, hm1]
    obtain ⟨hs0, hs1⟩ := hsplit i
    by_cases hi1 : i = iA
    · subst hi1
      have hAi_eq : V.getD iA.1 0 = ℓA.1 := (hA_iff iA).mpr rfl
      have hAi : decide (V.getD iA.1 0 = ℓA.1) = true := decide_eq_true hAi_eq
      unfold naeClausePairVal
      rw [hAi]
      simp only [hiAB, ↓reduceIte, add_zero]
      rw [hAi_eq] at hs0 hs1
      cases hb : σ ℓA.1
      · have hnot0 : (⟨2 * iA.1, by omega⟩ : Fin (2 * v)) ∉ C₁ :=
          fun h ↦ Bool.false_ne_true (hb.symm.trans (hs0.mp h))
        have hin1 : (⟨2 * iA.1 + 1, by omega⟩ : Fin (2 * v)) ∈ C₁ := hs1.mpr hb
        cases hp : ℓA.2 <;> simp [hnot0, hin1, Literal.eval, hb, hp]
      · have hin0 : (⟨2 * iA.1, by omega⟩ : Fin (2 * v)) ∈ C₁ := hs0.mpr hb
        have hnot1 : (⟨2 * iA.1 + 1, by omega⟩ : Fin (2 * v)) ∉ C₁ :=
          fun h ↦ Bool.false_ne_true ((hs1.mp h).symm.trans hb)
        cases hp : ℓA.2 <;> simp [hin0, hnot1, Literal.eval, hb, hp]
    · have hAi : decide (V.getD i.1 0 = ℓA.1) = false :=
        decide_eq_false fun h ↦ hi1 ((hA_iff i).mp h)
      by_cases hi2 : i = iB
      · subst hi2
        have hBi_eq : V.getD iB.1 0 = ℓB.1 := (hB_iff iB).mpr rfl
        have hBi : decide (V.getD iB.1 0 = ℓB.1) = true := decide_eq_true hBi_eq
        unfold naeClausePairVal
        rw [hAi, hBi]
        simp only [hiAB.symm, Bool.false_eq_true, ↓reduceIte, zero_add]
        rw [hBi_eq] at hs0 hs1
        cases hb : σ ℓB.1
        · have hnot0 : (⟨2 * iB.1, by omega⟩ : Fin (2 * v)) ∉ C₁ :=
            fun h ↦ Bool.false_ne_true (hb.symm.trans (hs0.mp h))
          have hin1 : (⟨2 * iB.1 + 1, by omega⟩ : Fin (2 * v)) ∈ C₁ := hs1.mpr hb
          cases hp : ℓB.2 <;> simp [hnot0, hin1, Literal.eval, hb, hp]
        · have hin0 : (⟨2 * iB.1, by omega⟩ : Fin (2 * v)) ∈ C₁ := hs0.mpr hb
          have hnot1 : (⟨2 * iB.1 + 1, by omega⟩ : Fin (2 * v)) ∉ C₁ :=
            fun h ↦ Bool.false_ne_true ((hs1.mp h).symm.trans hb)
          cases hp : ℓB.2 <;> simp [hin0, hnot1, Literal.eval, hb, hp]
      · have hBi : decide (V.getD i.1 0 = ℓB.1) = false :=
          decide_eq_false fun h ↦ hi2 ((hB_iff i).mp h)
        unfold naeClausePairVal
        rw [hAi, hBi]
        simp [hi1, hi2]
  rw [sum_congr rfl fun i _ ↦ hpair i, sum_add_distrib]
  simp [sub_eq_add_neg]

private lemma split_partition_cost {φ : CNF ℕ} (hsyn : φ.IsExactThreeDistinct)
    (hm : 1 ≤ φ.length) {C₁ C₂ : Finset (Fin (2 * (naeVars φ).length))}
    (h1 : C₁.Nonempty) (h2 : C₂.Nonempty) (hdisj : Disjoint C₁ C₂)
    (hunion : C₁ ∪ C₂ = univ) (hcard1 : C₁.card = (naeVars φ).length)
    (hcard2 : C₂.card = (naeVars φ).length) (σ : ℕ → Bool)
    (hsplit : ∀ i : Fin (naeVars φ).length,
      ((⟨2 * i.1, by omega⟩ : Fin (2 * (naeVars φ).length)) ∈ C₁ ↔
        σ ((naeVars φ).getD i.1 0) = true) ∧
      ((⟨2 * i.1 + 1, by omega⟩ : Fin (2 * (naeVars φ).length)) ∈ C₁ ↔
        σ ((naeVars φ).getD i.1 0) = false)) :
    let v := (naeVars φ).length
    let m := φ.length
    let L : ℚ := (((3 * m + 4) * v : ℕ) : ℚ)
    let satCount := φ.countP fun c ↦ Clause.eval σ c && Clause.eval (fun u ↦ !σ u) c
    kmeansClusterCost (v + 3 * m) (naePoints φ) C₁ +
      kmeansClusterCost (v + 3 * m) (naePoints φ) C₂ =
      2 * ((v - 1 : ℕ) : ℚ) * (L * L) + 12 * (m : ℚ) -
        (16 * (satCount : ℚ)) / (v : ℚ) := by
  dsimp only
  let V := naeVars φ
  let v := V.length
  let m := φ.length
  let L : ℚ := (((3 * m + 4) * v : ℕ) : ℚ)
  have hv3 : 3 ≤ v := three_le_length_naeVars hsyn hm
  have hv_ne : (v : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  unfold kmeansClusterCost centroidCoord
  rw [sum_comm (s := C₁), sum_comm (s := C₂), ← sum_add_distrib, Finset.sum_range_add]
  have hfactor : ((2 * v : ℕ) : ℚ) / ((C₁.card : ℚ) * (C₂.card : ℚ)) = 2 / (v : ℚ) := by
    rw [hcard1, hcard2]
    change ((2 * v : ℕ) : ℚ) / ((v : ℚ) * (v : ℚ)) = 2 / (v : ℚ)
    push_cast
    field_simp [hv_ne]
  have hvar_each : ∀ r ∈ Finset.range v,
      (∑ i ∈ C₁, (pointCoord (naePoints φ) i.1 r -
          (∑ j ∈ C₁, pointCoord (naePoints φ) j.1 r) / (C₁.card : ℚ)) ^ 2) +
        (∑ i ∈ C₂, (pointCoord (naePoints φ) i.1 r -
          (∑ j ∈ C₂, pointCoord (naePoints φ) j.1 r) / (C₂.card : ℚ)) ^ 2) =
      2 * (L * L) - (2 / (v : ℚ)) * (L * L) := by
    intro r hr
    have hr_lt : r < v := Finset.mem_range.mp hr
    have hpt : ∀ p : Fin (2 * v), pointCoord (naePoints φ) p.1 r =
        if r = p.1 / 2 then (if p.1 % 2 = 0 then L else -L) else 0 := by
      intro p
      rw [pointCoord_naePoints p.2 (by dsimp [V, v, m] at *; omega)]
      simp [naeCoordVal, V, v, m, L, hr_lt]
    rw [twoPart_coord_cost h1 h2 hdisj hunion (fun p ↦ pointCoord (naePoints φ) p.1 r)]
    · rw [hfactor]
      let rFin : Fin v := ⟨r, hr_lt⟩
      have hQ : ∑ p : Fin (2 * v), (pointCoord (naePoints φ) p.1 r) ^ 2 = 2 * (L * L) := by
        rw [sum_fin_two_mul]
        have hq_term : ∀ i : Fin v,
            (pointCoord (naePoints φ) (2 * i.1) r) ^ 2 +
              (pointCoord (naePoints φ) (2 * i.1 + 1) r) ^ 2 =
            if i = rFin then 2 * (L * L) else 0 := by
          intro i
          rw [hpt ⟨2 * i.1, by omega⟩, hpt ⟨2 * i.1 + 1, by omega⟩]
          have hd0 : (2 * i.1) / 2 = i.1 := Nat.mul_div_right i.1 (by decide)
          have hd1 : (2 * i.1 + 1) / 2 = i.1 := by omega
          have hm0 : (2 * i.1) % 2 = 0 := Nat.mul_mod_right 2 i.1
          have hm1 : (2 * i.1 + 1) % 2 ≠ 0 := by omega
          rw [hd0, hd1]
          simp only [hm0, hm1, ↓reduceIte]
          by_cases hir : i = rFin
          · subst hir; simp [rFin]; ring
          · have hne : r ≠ i.1 := fun h ↦ hir (Fin.ext h.symm)
            simp [hne, hir]
        rw [sum_congr rfl fun i _ ↦ hq_term i]
        simp
      have hS1 : (∑ p ∈ C₁, pointCoord (naePoints φ) p.1 r) ^ 2 = L * L := by
        have hind : ∑ p ∈ C₁, pointCoord (naePoints φ) p.1 r =
            ∑ p : Fin (2 * v), if p ∈ C₁ then pointCoord (naePoints φ) p.1 r else 0 := by
          rw [← sum_filter, filter_univ_mem]
        rw [hind, sum_fin_two_mul]
        have hs_term : ∀ i : Fin v,
            (if (⟨2 * i.1, by omega⟩ : Fin (2 * v)) ∈ C₁ then
                pointCoord (naePoints φ) (2 * i.1) r else 0) +
              (if (⟨2 * i.1 + 1, by omega⟩ : Fin (2 * v)) ∈ C₁ then
                pointCoord (naePoints φ) (2 * i.1 + 1) r else 0) =
            if i = rFin then (if σ (V.getD r 0) then L else -L) else 0 := by
          intro i
          rw [hpt ⟨2 * i.1, by omega⟩, hpt ⟨2 * i.1 + 1, by omega⟩]
          have hd0 : (2 * i.1) / 2 = i.1 := Nat.mul_div_right i.1 (by decide)
          have hd1 : (2 * i.1 + 1) / 2 = i.1 := by omega
          have hm0 : (2 * i.1) % 2 = 0 := Nat.mul_mod_right 2 i.1
          have hm1 : (2 * i.1 + 1) % 2 ≠ 0 := by omega
          rw [hd0, hd1]
          simp only [hm0, hm1, ↓reduceIte]
          by_cases hir : i = rFin
          · subst hir
            obtain ⟨hs0, hs1⟩ := hsplit rFin
            cases hb : σ (V.getD r 0)
            · have hnot0 : (⟨2 * r, by omega⟩ : Fin (2 * v)) ∉ C₁ :=
                fun h ↦ Bool.false_ne_true (hb.symm.trans (hs0.mp h))
              have hin1 : (⟨2 * r + 1, by omega⟩ : Fin (2 * v)) ∈ C₁ := hs1.mpr hb
              simp [rFin, hnot0, hin1]
            · have hin0 : (⟨2 * r, by omega⟩ : Fin (2 * v)) ∈ C₁ := hs0.mpr hb
              have hnot1 : (⟨2 * r + 1, by omega⟩ : Fin (2 * v)) ∉ C₁ :=
                fun h ↦ Bool.false_ne_true ((hs1.mp h).symm.trans hb)
              simp [rFin, hin0, hnot1]
          · have hne : r ≠ i.1 := fun h ↦ hir (Fin.ext h.symm)
            simp [hne, hir]
        rw [sum_congr rfl fun i _ ↦ hs_term i]
        simp only [sum_ite_eq', mem_univ, ↓reduceIte]
        cases σ (V.getD r 0) <;> simp <;> ring
      rw [hQ, hS1]
    · rw [sum_fin_two_mul]
      refine sum_eq_zero fun i _ ↦ ?_
      have hi_lt : i.1 < v := i.2
      have hi0 : 2 * i.1 < 2 * v := by omega
      have hi1 : 2 * i.1 + 1 < 2 * v := by omega
      rw [hpt ⟨2 * i.1, hi0⟩, hpt ⟨2 * i.1 + 1, hi1⟩]
      have hd0 : (2 * i.1) / 2 = i.1 := Nat.mul_div_right i.1 (by decide)
      have hd1 : (2 * i.1 + 1) / 2 = i.1 := by omega
      have hm0 : (2 * i.1) % 2 = 0 := Nat.mul_mod_right 2 i.1
      have hm1 : (2 * i.1 + 1) % 2 ≠ 0 := by omega
      rw [hd0, hd1]
      simp only [hm0, hm1, ↓reduceIte]
      split_ifs <;> ring
  have hvar_sum : ∑ r ∈ Finset.range v,
      ((∑ i ∈ C₁, (pointCoord (naePoints φ) i.1 r -
          (∑ j ∈ C₁, pointCoord (naePoints φ) j.1 r) / (C₁.card : ℚ)) ^ 2) +
        (∑ i ∈ C₂, (pointCoord (naePoints φ) i.1 r -
          (∑ j ∈ C₂, pointCoord (naePoints φ) j.1 r) / (C₂.card : ℚ)) ^ 2)) =
      2 * ((v - 1 : ℕ) : ℚ) * (L * L) := by
    rw [sum_congr rfl hvar_each, sum_const, card_range, nsmul_eq_mul]
    have hv1 : ((v - 1 : ℕ) : ℚ) = (v : ℚ) - 1 := by
      rw [Nat.cast_sub (by omega), Nat.cast_one]
    rw [hv1]
    field_simp [hv_ne]
  have h3m_split : ∀ g : ℕ → ℚ,
      ∑ t ∈ Finset.range (3 * m), g t =
        ∑ cIdx ∈ Finset.range m, (g (3 * cIdx) + g (3 * cIdx + 1) + g (3 * cIdx + 2)) := by
    intro g
    have hrec : ∀ k, ∑ t ∈ Finset.range (3 * k), g t =
        ∑ cIdx ∈ Finset.range k, (g (3 * cIdx) + g (3 * cIdx + 1) + g (3 * cIdx + 2)) := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        have h3 : 3 * (k + 1) = 3 * k + 1 + 1 + 1 := by omega
        rw [h3, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, ih,
          Finset.sum_range_succ]
        ring
    exact hrec m
  rw [hvar_sum, h3m_split]
  have hclause_each : ∀ cIdx ∈ Finset.range m,
      (let g := fun t ↦
        (∑ i ∈ C₁, (pointCoord (naePoints φ) i.1 (v + t) -
            (∑ j ∈ C₁, pointCoord (naePoints φ) j.1 (v + t)) / (C₁.card : ℚ)) ^ 2) +
          (∑ i ∈ C₂, (pointCoord (naePoints φ) i.1 (v + t) -
            (∑ j ∈ C₂, pointCoord (naePoints φ) j.1 (v + t)) / (C₂.card : ℚ)) ^ 2)
       g (3 * cIdx) + g (3 * cIdx + 1) + g (3 * cIdx + 2)) =
      12 - (2 / (v : ℚ)) *
        (if Clause.eval σ (φ.getD cIdx []) && Clause.eval (fun u ↦ !σ u) (φ.getD cIdx [])
         then (8 : ℚ) else 0) := by
    intro cIdx hcIdx
    have hc_lt : cIdx < φ.length := Finset.mem_range.mp hcIdx
    have hc_mem : φ[cIdx] ∈ φ := List.getElem_mem hc_lt
    have hc_getD : φ.getD cIdx [] = φ[cIdx] := List.getD_eq_getElem φ [] hc_lt
    rw [hc_getD]
    obtain ⟨ℓ₀, ℓ₁, ℓ₂, hcEq, h01, h02, h12⟩ :=
      Clause.isExactThreeDistinct_iff.mp (hsyn _ hc_mem)
    have hm0 : ℓ₀.1 ∈ V :=
      mem_naeVars.mpr (CNF.mem_vars.mpr ⟨φ[cIdx], hc_mem, ℓ₀.2, by rw [hcEq]; simp⟩)
    have hm1 : ℓ₁.1 ∈ V :=
      mem_naeVars.mpr (CNF.mem_vars.mpr ⟨φ[cIdx], hc_mem, ℓ₁.2, by rw [hcEq]; simp⟩)
    have hm2 : ℓ₂.1 ∈ V :=
      mem_naeVars.mpr (CNF.mem_vars.mpr ⟨φ[cIdx], hc_mem, ℓ₂.2, by rw [hcEq]; simp⟩)
    have hslot_val : ∀ (slot : ℕ) (ℓA ℓB : Literal ℕ),
        slot < 3 →
        (φ[cIdx]).getD slot (0, false) = ℓA →
        (φ[cIdx]).getD ((slot + 1) % 3) (0, false) = ℓB →
        ℓA.1 ≠ ℓB.1 → ℓA.1 ∈ V → ℓB.1 ∈ V →
        (∑ i ∈ C₁, (pointCoord (naePoints φ) i.1 (v + (3 * cIdx + slot)) -
            (∑ j ∈ C₁, pointCoord (naePoints φ) j.1 (v + (3 * cIdx + slot))) / (C₁.card : ℚ)) ^ 2) +
          (∑ i ∈ C₂, (pointCoord (naePoints φ) i.1 (v + (3 * cIdx + slot)) -
            (∑ j ∈ C₂, pointCoord (naePoints φ) j.1 (v + (3 * cIdx + slot))) / (C₂.card : ℚ)) ^ 2) =
        4 - (2 / (v : ℚ)) *
          ((if Literal.eval σ ℓA then (1 : ℚ) else -1) -
            (if Literal.eval σ ℓB then (1 : ℚ) else -1)) ^ 2 := by
      intro slot ℓA ℓB hslot hgetA hgetB hAB hAV hBV
      have hpt_slot : ∀ p : Fin (2 * v),
          pointCoord (naePoints φ) p.1 (v + (3 * cIdx + slot)) =
            naeClausePairVal (V.getD (p.1 / 2) 0) (decide (p.1 % 2 = 0)) ℓA ℓB := by
        intro p
        have hlt_coord : v + (3 * cIdx + slot) < (naeVars φ).length + 3 * φ.length := by
          have : v = (naeVars φ).length := rfl
          omega
        rw [pointCoord_naePoints p.2 hlt_coord]
        unfold naeCoordVal
        have hnot_lt : decide (v + (3 * cIdx + slot) < (naeVars φ).length) = false :=
          decide_eq_false (by have : v = (naeVars φ).length := rfl; omega)
        have hsub : v + (3 * cIdx + slot) - (naeVars φ).length = 3 * cIdx + slot := by
          have : v = (naeVars φ).length := rfl; omega
        have hdiv : (3 * cIdx + slot) / 3 = cIdx := by omega
        have hmod : (3 * cIdx + slot) % 3 = slot := by omega
        dsimp only [V]
        rw [hnot_lt]
        simp only [Bool.false_eq_true, ↓reduceIte, hsub, hdiv, hmod, hc_getD, hgetA, hgetB]
      obtain ⟨hsum0, hsq4⟩ := clausePair_stats (v := v) rfl (nodup_naeVars φ) hAB hAV hBV
      have hsum0' : ∑ p : Fin (2 * v), pointCoord (naePoints φ) p.1 (v + (3 * cIdx + slot)) =
        0 := by
        simpa only [hpt_slot] using hsum0
      have hsq4' : ∑ p : Fin (2 * v),
          (pointCoord (naePoints φ) p.1 (v + (3 * cIdx + slot))) ^ 2 = 4 := by
        simpa only [hpt_slot] using hsq4
      have hS1' : ∑ p ∈ C₁, pointCoord (naePoints φ) p.1 (v + (3 * cIdx + slot)) =
          (if Literal.eval σ ℓA then (1 : ℚ) else -1) -
            (if Literal.eval σ ℓB then (1 : ℚ) else -1) := by
        simpa only [hpt_slot] using
          clausePair_split_sum (v := v) rfl (nodup_naeVars φ) σ hsplit hAB hAV hBV
      rw [twoPart_coord_cost h1 h2 hdisj hunion
        (fun p ↦ pointCoord (naePoints φ) p.1 (v + (3 * cIdx + slot))) hsum0',
        hfactor, hsq4', hS1']
    dsimp only
    have hs0 := hslot_val 0 ℓ₀ ℓ₁ (by decide) (by rw [hcEq]; rfl) (by rw [hcEq]; rfl) h01 hm0 hm1
    have hs1 := hslot_val 1 ℓ₁ ℓ₂ (by decide) (by rw [hcEq]; rfl) (by rw [hcEq]; rfl) h12 hm1 hm2
    have hs2 := hslot_val 2 ℓ₂ ℓ₀ (by decide) (by rw [hcEq]; rfl)
      (by rw [hcEq]; rfl) h02.symm hm2 hm0
    simp only [add_zero] at hs0
    rw [hs0, hs1, hs2, hcEq, clause_evalNAE_iff_three]
    have hdiff := nae_three_diff_sq (Literal.eval σ ℓ₀) (Literal.eval σ ℓ₁) (Literal.eval σ ℓ₂)
    dsimp only at hdiff
    have hcomb :
        (4 - (2 / (v : ℚ)) *
            ((if Literal.eval σ ℓ₀ then (1 : ℚ) else -1) -
              (if Literal.eval σ ℓ₁ then (1 : ℚ) else -1)) ^ 2) +
          (4 - (2 / (v : ℚ)) *
            ((if Literal.eval σ ℓ₁ then (1 : ℚ) else -1) -
              (if Literal.eval σ ℓ₂ then (1 : ℚ) else -1)) ^ 2) +
          (4 - (2 / (v : ℚ)) *
            ((if Literal.eval σ ℓ₂ then (1 : ℚ) else -1) -
              (if Literal.eval σ ℓ₀ then (1 : ℚ) else -1)) ^ 2) =
        12 - (2 / (v : ℚ)) *
          (((if Literal.eval σ ℓ₀ then (1 : ℚ) else -1) -
              (if Literal.eval σ ℓ₁ then (1 : ℚ) else -1)) ^ 2 +
            ((if Literal.eval σ ℓ₁ then (1 : ℚ) else -1) -
              (if Literal.eval σ ℓ₂ then (1 : ℚ) else -1)) ^ 2 +
            ((if Literal.eval σ ℓ₂ then (1 : ℚ) else -1) -
              (if Literal.eval σ ℓ₀ then (1 : ℚ) else -1)) ^ 2) := by
      ring
    rw [hcomb, hdiff]
  rw [sum_congr rfl hclause_each]
  have hlist_count : ∀ (ψ : CNF ℕ),
      ∑ x ∈ Finset.range ψ.length,
        (if Clause.eval σ (ψ.getD x []) && Clause.eval (fun u ↦ !σ u) (ψ.getD x [])
         then (8 : ℚ) else 0) =
      8 * ((ψ.countP fun c ↦ Clause.eval σ c && Clause.eval (fun u ↦ !σ u) c : ℕ) : ℚ) := by
    intro ψ
    induction ψ with
    | nil => simp
    | cons c cs ih =>
      rw [List.length_cons, Finset.sum_range_succ', List.countP_cons]
      simp only [List.getD_cons_zero, List.getD_cons_succ]
      rw [ih, Nat.cast_add]
      cases (Clause.eval σ c && Clause.eval (fun u ↦ !σ u) c) <;> simp; ring
  rw [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul, ← mul_sum, hlist_count φ]
  dsimp [m]
  ring

private lemma nonsplit_var_cost_lower {φ : CNF ℕ} (hsyn : φ.IsExactThreeDistinct)
    (hm : 1 ≤ φ.length) {C₁ C₂ : Finset (Fin (2 * (naeVars φ).length))}
    (h1 : C₁.Nonempty) (h2 : C₂.Nonempty) (hdisj : Disjoint C₁ C₂)
    (hunion : C₁ ∪ C₂ = univ)
    (hnonsplit : ¬(∀ i : Fin (naeVars φ).length,
      ((⟨2 * i.1, by omega⟩ : Fin (2 * (naeVars φ).length)) ∈ C₁ ↔
        (⟨2 * i.1 + 1, by omega⟩ : Fin (2 * (naeVars φ).length)) ∉ C₁))) :
    let v := (naeVars φ).length
    let m := φ.length
    let L : ℚ := (((3 * m + 4) * v : ℕ) : ℚ)
    2 * ((v - 1 : ℕ) : ℚ) * (L * L) + 12 * (m : ℚ) + 16 ≤
      kmeansClusterCost (v + 3 * m) (naePoints φ) C₁ +
        kmeansClusterCost (v + 3 * m) (naePoints φ) C₂ := by
  dsimp only
  let V := naeVars φ
  let v := V.length
  let m := φ.length
  let L : ℚ := (((3 * m + 4) * v : ℕ) : ℚ)
  have hv3 : 3 ≤ v := three_le_length_naeVars hsyn hm
  have hv_pos : (0 : ℚ) < (v : ℚ) := Nat.cast_pos.mpr (by omega)
  let splitPred (i : Fin v) : Bool :=
    decide ((⟨2 * i.1, by omega⟩ : Fin (2 * v)) ∈ C₁) !=
      decide ((⟨2 * i.1 + 1, by omega⟩ : Fin (2 * v)) ∈ C₁)
  let splitSet : Finset (Fin v) := univ.filter fun i ↦ splitPred i = true
  have hsplitPred_iff : ∀ i : Fin v,
      splitPred i = true ↔
        ((⟨2 * i.1, by omega⟩ : Fin (2 * v)) ∈ C₁ ↔
          (⟨2 * i.1 + 1, by omega⟩ : Fin (2 * v)) ∉ C₁) := by
    intro i
    dsimp [splitPred]
    by_cases h0 : (⟨2 * i.1, by omega⟩ : Fin (2 * v)) ∈ C₁ <;>
      by_cases h1' : (⟨2 * i.1 + 1, by omega⟩ : Fin (2 * v)) ∈ C₁ <;>
      simp [h0, h1']
  have hsplit_lt : splitSet.card < v := by
    by_contra hge
    have hEq : splitSet = univ :=
      eq_of_subset_of_card_le (subset_univ _) (by rw [card_univ, Fintype.card_fin]; omega)
    apply hnonsplit
    intro i
    have hi_mem : i ∈ splitSet := hEq.symm ▸ mem_univ i
    exact (hsplitPred_iff i).mp (mem_filter.mp hi_mem).2
  let s := splitSet.card
  unfold kmeansClusterCost centroidCoord
  rw [sum_comm (s := C₁), sum_comm (s := C₂), ← sum_add_distrib, Finset.sum_range_add]
  have hclause_nn : 0 ≤ ∑ t ∈ Finset.range (3 * m),
      ((∑ i ∈ C₁, (pointCoord (naePoints φ) i.1 (v + t) -
          (∑ j ∈ C₁, pointCoord (naePoints φ) j.1 (v + t)) / (C₁.card : ℚ)) ^ 2) +
        (∑ i ∈ C₂, (pointCoord (naePoints φ) i.1 (v + t) -
          (∑ j ∈ C₂, pointCoord (naePoints φ) j.1 (v + t)) / (C₂.card : ℚ)) ^ 2)) :=
    sum_nonneg fun _ _ ↦ add_nonneg (sum_nonneg fun _ _ ↦ sq_nonneg _)
      (sum_nonneg fun _ _ ↦ sq_nonneg _)
  have hvar_each : ∀ r ∈ Finset.range v,
      (∑ i ∈ C₁, (pointCoord (naePoints φ) i.1 r -
          (∑ j ∈ C₁, pointCoord (naePoints φ) j.1 r) / (C₁.card : ℚ)) ^ 2) +
        (∑ i ∈ C₂, (pointCoord (naePoints φ) i.1 r -
          (∑ j ∈ C₂, pointCoord (naePoints φ) j.1 r) / (C₂.card : ℚ)) ^ 2) =
      2 * (L * L) -
        (((2 * v : ℕ) : ℚ) / ((C₁.card : ℚ) * (C₂.card : ℚ))) *
          (if hr' : r < v then (if (⟨r, hr'⟩ : Fin v) ∈ splitSet then L * L else 0) else 0) := by
    intro r hr
    have hr_lt : r < v := Finset.mem_range.mp hr
    let rFin : Fin v := ⟨r, hr_lt⟩
    have hpt : ∀ p : Fin (2 * v), pointCoord (naePoints φ) p.1 r =
        if r = p.1 / 2 then (if p.1 % 2 = 0 then L else -L) else 0 := by
      intro p
      have hr_lt' : r < (naeVars φ).length := hr_lt
      rw [pointCoord_naePoints p.2 (by omega)]
      simp [naeCoordVal, V, v, m, L, hr_lt]
    rw [twoPart_coord_cost h1 h2 hdisj hunion (fun p ↦ pointCoord (naePoints φ) p.1 r)]
    · simp only [hr_lt, ↓reduceDIte]
      have hQ : ∑ p : Fin (2 * v), (pointCoord (naePoints φ) p.1 r) ^ 2 = 2 * (L * L) := by
        rw [sum_fin_two_mul]
        have hq_term : ∀ i : Fin v,
            (pointCoord (naePoints φ) (2 * i.1) r) ^ 2 +
              (pointCoord (naePoints φ) (2 * i.1 + 1) r) ^ 2 =
            if i = rFin then 2 * (L * L) else 0 := by
          intro i
          have hi_lt : i.1 < v := i.2
          rw [hpt ⟨2 * i.1, by omega⟩, hpt ⟨2 * i.1 + 1, by omega⟩]
          have hd0 : (2 * i.1) / 2 = i.1 := Nat.mul_div_right i.1 (by decide)
          have hd1 : (2 * i.1 + 1) / 2 = i.1 := by omega
          have hm0 : (2 * i.1) % 2 = 0 := Nat.mul_mod_right 2 i.1
          have hm1 : (2 * i.1 + 1) % 2 ≠ 0 := by omega
          rw [hd0, hd1]
          simp only [hm0, hm1, ↓reduceIte]
          by_cases hir : i = rFin
          · subst hir; simp [rFin]; ring
          · have hne : r ≠ i.1 := fun h ↦ hir (Fin.ext h.symm)
            simp [hne, hir]
        rw [sum_congr rfl fun i _ ↦ hq_term i]
        simp
      have hS1 : (∑ p ∈ C₁, pointCoord (naePoints φ) p.1 r) ^ 2 =
          if rFin ∈ splitSet then L * L else 0 := by
        have hind : ∑ p ∈ C₁, pointCoord (naePoints φ) p.1 r =
            ∑ p : Fin (2 * v), if p ∈ C₁ then pointCoord (naePoints φ) p.1 r else 0 := by
          rw [← sum_filter, filter_univ_mem]
        rw [hind, sum_fin_two_mul]
        have hs_term : ∀ i : Fin v,
            (if (⟨2 * i.1, by omega⟩ : Fin (2 * v)) ∈ C₁ then
                pointCoord (naePoints φ) (2 * i.1) r else 0) +
              (if (⟨2 * i.1 + 1, by omega⟩ : Fin (2 * v)) ∈ C₁ then
                pointCoord (naePoints φ) (2 * i.1 + 1) r else 0) =
            if i = rFin then
              ((if (⟨2 * r, by omega⟩ : Fin (2 * v)) ∈ C₁ then L else 0) +
                (if (⟨2 * r + 1, by omega⟩ : Fin (2 * v)) ∈ C₁ then -L else 0))
            else 0 := by
          intro i
          have hi_lt : i.1 < v := i.2
          rw [hpt ⟨2 * i.1, by omega⟩, hpt ⟨2 * i.1 + 1, by omega⟩]
          have hd0 : (2 * i.1) / 2 = i.1 := Nat.mul_div_right i.1 (by decide)
          have hd1 : (2 * i.1 + 1) / 2 = i.1 := by omega
          have hm0 : (2 * i.1) % 2 = 0 := Nat.mul_mod_right 2 i.1
          have hm1 : (2 * i.1 + 1) % 2 ≠ 0 := by omega
          rw [hd0, hd1]
          simp only [hm0, hm1, ↓reduceIte]
          by_cases hir : i = rFin
          · subst hir; simp [rFin]
          · have hne : r ≠ i.1 := fun h ↦ hir (Fin.ext h.symm)
            simp [hne, hir]
        rw [sum_congr rfl fun i _ ↦ hs_term i]
        simp only [sum_ite_eq', mem_univ, ↓reduceIte, splitSet, mem_filter, true_and,
          hsplitPred_iff]
        by_cases hp0 : (⟨2 * r, by omega⟩ : Fin (2 * v)) ∈ C₁ <;>
          by_cases hp1 : (⟨2 * r + 1, by omega⟩ : Fin (2 * v)) ∈ C₁
        all_goals simp [rFin, hp0, hp1, sq]
      rw [hQ, hS1]
    · rw [sum_fin_two_mul]
      refine sum_eq_zero fun i _ ↦ ?_
      have hi_lt : i.1 < v := i.2
      have hi0 : 2 * i.1 < 2 * v := by omega
      have hi1 : 2 * i.1 + 1 < 2 * v := by omega
      rw [hpt ⟨2 * i.1, hi0⟩, hpt ⟨2 * i.1 + 1, hi1⟩]
      have hd0 : (2 * i.1) / 2 = i.1 := Nat.mul_div_right i.1 (by decide)
      have hd1 : (2 * i.1 + 1) / 2 = i.1 := by omega
      have hm0 : (2 * i.1) % 2 = 0 := Nat.mul_mod_right 2 i.1
      have hm1 : (2 * i.1 + 1) % 2 ≠ 0 := by omega
      rw [hd0, hd1]
      simp only [hm0, hm1, ↓reduceIte]
      split_ifs <;> ring
  let bothOne : Finset (Fin v) := univ.filter fun i ↦
    (⟨2 * i.1, by omega⟩ : Fin (2 * v)) ∈ C₁ ∧ (⟨2 * i.1 + 1, by omega⟩ : Fin (2 * v)) ∈ C₁
  let bothTwo : Finset (Fin v) := univ.filter fun i ↦
    (⟨2 * i.1, by omega⟩ : Fin (2 * v)) ∉ C₁ ∧ (⟨2 * i.1 + 1, by omega⟩ : Fin (2 * v)) ∉ C₁
  let a := bothOne.card
  let b := bothTwo.card
  have hsab : s + a + b = v := by
    have hsum1 : ∀ i : Fin v,
        (if i ∈ splitSet then 1 else 0) + (if i ∈ bothOne then 1 else 0) +
          (if i ∈ bothTwo then 1 else 0) = (1 : ℕ) := by
      intro i
      simp only [splitSet, bothOne, bothTwo, mem_filter, mem_univ, true_and, hsplitPred_iff]
      by_cases h0 : (⟨2 * i.1, by omega⟩ : Fin (2 * v)) ∈ C₁ <;>
        by_cases h1' : (⟨2 * i.1 + 1, by omega⟩ : Fin (2 * v)) ∈ C₁ <;> simp [h0, h1']
    have htot :
        ∑ i : Fin v, ((if i ∈ splitSet then 1 else 0) + (if i ∈ bothOne then 1 else 0) +
          (if i ∈ bothTwo then 1 else 0)) =
        ∑ _i : Fin v, (1 : ℕ) :=
      sum_congr rfl fun i _ ↦ hsum1 i
    simp only [sum_add_distrib, ← sum_filter, filter_univ_mem, sum_const, card_univ,
      Fintype.card_fin, smul_eq_mul, mul_one] at htot
    exact htot
  have hc1_eq : C₁.card = s + 2 * a := by
    have h1q : ((C₁.card : ℕ) : ℚ) = ((s + 2 * a : ℕ) : ℚ) := by
      have hcard_q : (C₁.card : ℚ) = ∑ p : Fin (2 * v), if p ∈ C₁ then (1 : ℚ) else 0 := by
        rw [← sum_filter, filter_univ_mem, sum_const, nsmul_eq_mul, mul_one]
      rw [hcard_q, sum_fin_two_mul]
      have hpair1 : ∀ i : Fin v,
          (if (⟨2 * i.1, by omega⟩ : Fin (2 * v)) ∈ C₁ then (1 : ℚ) else 0) +
            (if (⟨2 * i.1 + 1, by omega⟩ : Fin (2 * v)) ∈ C₁ then (1 : ℚ) else 0) =
          (if i ∈ splitSet then (1 : ℚ) else 0) + 2 * (if i ∈ bothOne then (1 : ℚ) else 0) := by
        intro i
        simp only [splitSet, bothOne, mem_filter, mem_univ, true_and, hsplitPred_iff]
        by_cases hp0 : (⟨2 * i.1, by omega⟩ : Fin (2 * v)) ∈ C₁ <;>
          by_cases hp1 : (⟨2 * i.1 + 1, by omega⟩ : Fin (2 * v)) ∈ C₁ <;>
          simp [hp0, hp1]; norm_num
      rw [sum_congr rfl fun i _ ↦ hpair1 i, sum_add_distrib, ← mul_sum]
      simp only [← sum_filter, filter_univ_mem, sum_const, nsmul_eq_mul, mul_one]
      dsimp [s, a]
      push_cast
      ring
    exact_mod_cast h1q
  have hc2_eq : C₂.card = s + 2 * b := by
    have h12 : C₁.card + C₂.card = 2 * v := by
      rw [← card_union_of_disjoint hdisj, hunion, card_univ, Fintype.card_fin]
    omega
  have hprod_ge : s * v + 1 ≤ C₁.card * C₂.card := by
    have hc1_pos : 1 ≤ C₁.card := h1.card_pos
    have hc2_pos : 1 ≤ C₂.card := h2.card_pos
    rw [hc1_eq] at hc1_pos
    rw [hc2_eq] at hc2_pos
    rw [hc1_eq, hc2_eq]
    have hab_pos : 1 ≤ a + b := by omega
    have hid : (s + 2 * a) * (s + 2 * b) = s * (s + a + b) + (s * (a + b) + 4 * a * b) := by ring
    rw [← hsab, hid]
    by_cases hs0 : s = 0
    · rw [hs0] at hc1_pos hc2_pos ⊢
      have ha1 : 1 ≤ a := by omega
      have hb1 : 1 ≤ b := by omega
      nlinarith
    · have hs1 : 1 ≤ s := Nat.pos_of_ne_zero hs0
      nlinarith
  have hprod_le : C₁.card * C₂.card ≤ v * v := by
    have h12 : C₁.card + C₂.card = 2 * v := by
      rw [← card_union_of_disjoint hdisj, hunion, card_univ, Fintype.card_fin]
    nlinarith [sq_nonneg ((C₁.card : ℤ) - (C₂.card : ℤ))]
  have hvar_sum : ∑ r ∈ Finset.range v,
      ((∑ i ∈ C₁, (pointCoord (naePoints φ) i.1 r -
          (∑ j ∈ C₁, pointCoord (naePoints φ) j.1 r) / (C₁.card : ℚ)) ^ 2) +
        (∑ i ∈ C₂, (pointCoord (naePoints φ) i.1 r -
          (∑ j ∈ C₂, pointCoord (naePoints φ) j.1 r) / (C₂.card : ℚ)) ^ 2)) =
      2 * (v : ℚ) * (L * L) -
        (((2 * v : ℕ) : ℚ) / ((C₁.card : ℚ) * (C₂.card : ℚ))) * ((s : ℚ) * (L * L)) := by
    rw [sum_congr rfl hvar_each, sum_sub_distrib, sum_const, card_range, nsmul_eq_mul, ← mul_sum]
    have hsplit_sum :
        ∑ r ∈ Finset.range v,
          (if hr' : r < v then (if (⟨r, hr'⟩ : Fin v) ∈ splitSet then L * L else 0) else 0) =
          (s : ℚ) * (L * L) := by
      rw [← Fin.sum_univ_eq_sum_range (fun r ↦
        if hr' : r < v then (if (⟨r, hr'⟩ : Fin v) ∈ splitSet then L * L else 0) else 0)]
      have hfin_congr : ∀ r : Fin v,
          (if hr' : r.1 < v then (if (⟨r.1, hr'⟩ : Fin v) ∈ splitSet then L * L else 0) else 0) =
          (if r ∈ splitSet then L * L else 0) := fun r ↦ by
        simp only [r.2, ↓reduceDIte, Fin.eta]
      rw [sum_congr rfl fun r _ ↦ hfin_congr r, ← sum_filter, filter_univ_mem,
        sum_const, nsmul_eq_mul]
    rw [hsplit_sum]
    ring
  rw [hvar_sum]
  have hm_prod_pos : (0 : ℚ) < (C₁.card : ℚ) * (C₂.card : ℚ) :=
    mul_pos (Nat.cast_pos.mpr h1.card_pos) (Nat.cast_pos.mpr h2.card_pos)
  have hv1 : ((v - 1 : ℕ) : ℚ) = (v : ℚ) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  have hdiff_var :
      2 * ((v - 1 : ℕ) : ℚ) * (L * L) + (2 * (L * L)) / ((v : ℚ) * (v : ℚ)) ≤
        2 * (v : ℚ) * (L * L) -
          (((2 * v : ℕ) : ℚ) / ((C₁.card : ℚ) * (C₂.card : ℚ))) * ((s : ℚ) * (L * L)) := by
    rw [hv1]
    have hprod_ge_q : (s : ℚ) * (v : ℚ) + 1 ≤ (C₁.card : ℚ) * (C₂.card : ℚ) := by
      exact_mod_cast hprod_ge
    have hprod_le_q : (C₁.card : ℚ) * (C₂.card : ℚ) ≤ (v : ℚ) * (v : ℚ) := by
      exact_mod_cast hprod_le
    have hstep1 : (((2 * v : ℕ) : ℚ) / ((C₁.card : ℚ) * (C₂.card : ℚ))) * ((s : ℚ) * (L * L)) ≤
        2 * (L * L) * (1 - 1 / ((C₁.card : ℚ) * (C₂.card : ℚ))) := by
      rw [Nat.cast_mul, Nat.cast_ofNat, div_mul_eq_mul_div,
        one_sub_div hm_prod_pos.ne', mul_div_assoc', le_div_iff₀ hm_prod_pos,
        div_mul_cancel₀ _ hm_prod_pos.ne']
      have hLL_nn : 0 ≤ 2 * (L * L) := by positivity
      nlinarith
    have hstep2 : (2 * (L * L)) / ((v : ℚ) * (v : ℚ)) ≤
        (2 * (L * L)) / ((C₁.card : ℚ) * (C₂.card : ℚ)) :=
      div_le_div_of_nonneg_left (by positivity) hm_prod_pos hprod_le_q
    have hexp1 : 2 * (L * L) * (1 - 1 / ((C₁.card : ℚ) * (C₂.card : ℚ))) =
        2 * (L * L) - (2 * (L * L)) / ((C₁.card : ℚ) * (C₂.card : ℚ)) := by ring
    have hexp2 : 2 * ((v : ℚ) - 1) * (L * L) = 2 * (v : ℚ) * (L * L) - 2 * (L * L) := by ring
    linarith
  have hL_val : (2 * (L * L)) / ((v : ℚ) * (v : ℚ)) = 2 * ((3 * m + 4 : ℕ) : ℚ) ^ 2 := by
    dsimp [L]
    push_cast
    field_simp [hv_pos.ne']
  have hm_ge1 : (1 : ℚ) ≤ (m : ℚ) := by exact_mod_cast hm
  have hlarge : 12 * (m : ℚ) + 16 ≤ 2 * ((3 * m + 4 : ℕ) : ℚ) ^ 2 := by
    push_cast
    nlinarith
  linarith

/-- **Gap theorem for `TwoMeans.fromNAEEUThreeSAT`**:
every reduced instance has `k = 2`, `n ≥ 2`, and `gapOf φ > 0`; satisfiable `NAEEUThreeSAT`
formulas map to `TwoMeans` instances of cost at most `bound`, whereas unsatisfiable formulas have
every `2`-partition cost at least `bound + gapOf φ`. -/
theorem fromNAEEUThreeSAT_gap (φ : CNF ℕ) :
    let x := fromNAEEUThreeSAT φ
    x.k = 2 ∧ 2 ≤ x.n ∧ 0 < gapOf φ ∧
      (φ ∈ NAEEUThreeSAT → x ∈ TwoMeans) ∧
      (φ ∉ NAEEUThreeSAT →
        ∀ P : Finpartition (univ : Finset (Fin x.n)), P.parts.card = 2 →
          x.bound + gapOf φ ≤ kmeansCost x.n x.d x.points P) := by
  dsimp only
  by_cases hsyn_b : EUThreeSAT.syntaxCheck φ = true
  · have hsyn : φ.IsExactThreeDistinct := (EUThreeSAT.syntaxCheck_iff φ).mp hsyn_b
    by_cases hm0 : φ.length = 0
    · have hφnil : φ = [] := List.eq_nil_of_length_eq_zero hm0
      have hmemNAE : φ ∈ NAEEUThreeSAT := by
        rw [hφnil]
        exact And.intro (fun c hc ↦ nomatch hc) (Exists.intro (fun _ ↦ false) rfl)
      have hx_eq : fromNAEEUThreeSAT φ = yesInstance := by
        simp [fromNAEEUThreeSAT, hsyn_b, hm0]
      have hgap_eq : gapOf φ = 2 := by simp [gapOf, hm0]
      rw [hx_eq, hgap_eq]
      exact ⟨rfl, le_rfl, by norm_num, fun _ ↦ yesInstance_mem,
        fun hnot ↦ (hnot hmemNAE).elim⟩
    · have hm1 : 1 ≤ φ.length := Nat.pos_of_ne_zero hm0
      have hv3 : 3 ≤ (naeVars φ).length := three_le_length_naeVars hsyn hm1
      have hx_eq : fromNAEEUThreeSAT φ =
          (let V := naeVars φ
           let v := V.length
           let m := φ.length
           let L : ℚ := (((3 * m + 4) * v : ℕ) : ℚ)
           ⟨2 * v, v + 3 * m, naePoints φ, 2,
             2 * ((v - 1 : ℕ) : ℚ) * (L * L) + 12 * (m : ℚ) -
               (16 * (m : ℚ)) / (v : ℚ)⟩) := by
        simp [fromNAEEUThreeSAT, hsyn_b, hm0]
      have hgap_eq : gapOf φ = 16 / ((naeVars φ).length : ℚ) := by
        simp [gapOf, hsyn_b, hm1]
      rw [hx_eq, hgap_eq]
      dsimp only
      have hv_pos : (0 : ℚ) < ((naeVars φ).length : ℚ) := Nat.cast_pos.mpr (by omega)
      refine ⟨rfl, by omega, div_pos (by norm_num) hv_pos, ?_, ?_⟩
      · rintro ⟨_, σ, hσ⟩
        refine ⟨rfl, ?_⟩
        let V := naeVars φ
        let v := V.length
        let α : Fin (2 * v) → ℕ := fun p ↦
          if (decide (p.1 % 2 = 0)) == σ (V.getD (p.1 / 2) 0) then 0 else 1
        let cOf : ℕ → Fin (2 * v) := fun a ↦
          if a = 0 then
            if σ (V.getD 0 0) then ⟨0, by dsimp [V, v]; omega⟩ else ⟨1, by dsimp [V, v]; omega⟩
          else
            if σ (V.getD 0 0) then ⟨1, by dsimp [V, v]; omega⟩ else ⟨0, by dsimp [V, v]; omega⟩
        have hα_lt : ∀ p : Fin (2 * v), α p < 2 := fun p ↦ by
          dsimp [α]; split_ifs <;> decide
        have hα_mk : ∀ (k : ℕ) (hk : k < 2 * v),
            α ⟨k, hk⟩ = if (decide (k % 2 = 0) == σ (V.getD (k / 2) 0)) = true then 0 else 1 :=
          fun _ _ ↦ rfl
        have hα0 : α ⟨0, by dsimp [V, v]; omega⟩ = if σ (V.getD 0 0) then 0 else 1 := by
          rw [hα_mk 0]; have h0 : (0 : ℕ) / 2 = 0 := rfl; rw [h0]; cases σ (V.getD 0 0) <;> rfl
        have hα1 : α ⟨1, by dsimp [V, v]; omega⟩ = if σ (V.getD 0 0) then 1 else 0 := by
          rw [hα_mk 1]; have h1 : (1 : ℕ) / 2 = 0 := rfl; rw [h1]; cases σ (V.getD 0 0) <;> rfl
        have hc_eq : ∀ a < 2, α (cOf a) = a := by
          intro a ha
          interval_cases a
          · change α (if σ (V.getD 0 0) then ⟨0, _⟩ else ⟨1, _⟩) = 0
            split_ifs with hb <;> simp only [hα0, hα1, hb, Bool.false_eq_true, ↓reduceIte]
          · change α (if σ (V.getD 0 0) then ⟨1, _⟩ else ⟨0, _⟩) = 1
            split_ifs with hb <;> simp only [hα0, hα1, hb, Bool.false_eq_true, ↓reduceIte]
        obtain ⟨P, hPcard, hPsum⟩ :=
          EuclideanKMeans.exists_finpartition_sum_of_assign α cOf hα_lt hc_eq
            (kmeansClusterCost (v + 3 * φ.length) (naePoints φ))
        refine ⟨P, hPcard, ?_⟩
        change kmeansCost (2 * v) (v + 3 * φ.length) (naePoints φ) P ≤ _
        rw [kmeansCost, hPsum, Finset.sum_range_succ, Finset.sum_range_one]
        let C₁ := univ.filter fun p : Fin (2 * v) ↦ α p = 0
        let C₂ := univ.filter fun p : Fin (2 * v) ↦ α p = 1
        have h1 : C₁.Nonempty := ⟨cOf 0, mem_filter.mpr ⟨mem_univ _, hc_eq 0 (by decide)⟩⟩
        have h2 : C₂.Nonempty := ⟨cOf 1, mem_filter.mpr ⟨mem_univ _, hc_eq 1 (by decide)⟩⟩
        have hdisj : Disjoint C₁ C₂ := by
          refine Finset.disjoint_left.mpr fun p hp1 hp2 ↦ ?_
          have e1 := (mem_filter.mp hp1).2
          have e2 := (mem_filter.mp hp2).2
          omega
        have hunion : C₁ ∪ C₂ = univ := by
          ext p
          simp only [mem_union, C₁, C₂, mem_filter, mem_univ, true_and, iff_true]
          have := hα_lt p
          omega
        have hsplit : ∀ i : Fin v,
            ((⟨2 * i.1, by omega⟩ : Fin (2 * v)) ∈ C₁ ↔ σ (V.getD i.1 0) = true) ∧
            ((⟨2 * i.1 + 1, by omega⟩ : Fin (2 * v)) ∈ C₁ ↔ σ (V.getD i.1 0) = false) := by
          intro i
          have hd0 : (2 * i.1) / 2 = i.1 := Nat.mul_div_right i.1 (by decide)
          have hd1 : (2 * i.1 + 1) / 2 = i.1 := by omega
          have hm0 : decide ((2 * i.1) % 2 = 0) = true :=
            decide_eq_true (Nat.mul_mod_right 2 i.1)
          have hm1 : decide ((2 * i.1 + 1) % 2 = 0) = false :=
            decide_eq_false (by omega)
          simp only [C₁, mem_filter, mem_univ, true_and, α, hd0, hd1, hm0, hm1]
          cases σ (V.getD i.1 0) <;> simp
        have hcard1 : C₁.card = v := by
          have hq : (C₁.card : ℚ) = (v : ℚ) := by
            have hc : (C₁.card : ℚ) = ∑ p : Fin (2 * v), if p ∈ C₁ then (1 : ℚ) else 0 := by
              rw [← sum_filter, filter_univ_mem, sum_const, nsmul_eq_mul, mul_one]
            rw [hc, sum_fin_two_mul]
            have h1_each : ∀ i : Fin v,
                (if (⟨2 * i.1, by omega⟩ : Fin (2 * v)) ∈ C₁ then (1 : ℚ) else 0) +
                  (if (⟨2 * i.1 + 1, by omega⟩ : Fin (2 * v)) ∈ C₁ then (1 : ℚ) else 0) = 1 := by
              intro i
              obtain ⟨hs0, hs1⟩ := hsplit i
              cases hb : σ (V.getD i.1 0)
              · have hnot0 : (⟨2 * i.1, by omega⟩ : Fin (2 * v)) ∉ C₁ :=
                  fun h ↦ Bool.false_ne_true (hb.symm.trans (hs0.mp h))
                have hin1 : (⟨2 * i.1 + 1, by omega⟩ : Fin (2 * v)) ∈ C₁ := hs1.mpr hb
                simp [hnot0, hin1]
              · have hin0 : (⟨2 * i.1, by omega⟩ : Fin (2 * v)) ∈ C₁ := hs0.mpr hb
                have hnot1 : (⟨2 * i.1 + 1, by omega⟩ : Fin (2 * v)) ∉ C₁ :=
                  fun h ↦ Bool.false_ne_true ((hs1.mp h).symm.trans hb)
                simp [hin0, hnot1]
            rw [sum_congr rfl fun i _ ↦ h1_each i, sum_const, card_univ, Fintype.card_fin,
              nsmul_eq_mul, mul_one]
          exact_mod_cast hq
        have hcard2 : C₂.card = v := by
          have h12 : C₁.card + C₂.card = 2 * v := by
            rw [← card_union_of_disjoint hdisj, hunion, card_univ, Fintype.card_fin]
          omega
        have hcost_eq := split_partition_cost hsyn hm1 h1 h2 hdisj hunion hcard1 hcard2 σ hsplit
        dsimp only at hcost_eq
        have hcount_all :
            (φ.countP fun c ↦ Clause.eval σ c && Clause.eval (fun u ↦ !σ u) c) = φ.length := by
          rw [List.countP_eq_length]
          intro c hc
          simp only [CNF.evalNAE, Bool.and_eq_true, CNF.eval_eq_true_iff] at hσ
          simp [hσ.1 c hc, hσ.2 c hc]
        rw [hcount_all] at hcost_eq
        change kmeansClusterCost (v + 3 * φ.length) (naePoints φ) C₁ +
          kmeansClusterCost (v + 3 * φ.length) (naePoints φ) C₂ ≤ _
        linarith
      · intro hnotNAE P hPcard
        let V := naeVars φ
        let v := V.length
        let m := φ.length
        obtain ⟨C₁, C₂, hCne, hPparts⟩ := Finset.card_eq_two.mp hPcard
        have hC1_mem : C₁ ∈ P.parts := by rw [hPparts]; exact mem_insert_self C₁ {C₂}
        have hC2_mem : C₂ ∈ P.parts := by
          rw [hPparts]; exact mem_insert_of_mem (mem_singleton_self C₂)
        have h1 : C₁.Nonempty := P.nonempty_of_mem_parts hC1_mem
        have h2 : C₂.Nonempty := P.nonempty_of_mem_parts hC2_mem
        have hdisj : Disjoint C₁ C₂ := P.disjoint hC1_mem hC2_mem hCne
        have hunion : C₁ ∪ C₂ = univ := by
          have hs := P.sup_parts
          simpa only [hPparts, sup_insert, sup_singleton, id_eq] using hs
        rw [kmeansCost, hPparts, sum_pair hCne]
        by_cases hsplit_all : ∀ i : Fin v,
            ((⟨2 * i.1, by omega⟩ : Fin (2 * v)) ∈ C₁ ↔
              (⟨2 * i.1 + 1, by omega⟩ : Fin (2 * v)) ∉ C₁)
        · let σ : ℕ → Bool := fun u ↦
            if hmem : u ∈ V then
              decide ((⟨2 * V.idxOf u, by
                have := List.idxOf_lt_length_iff.mpr hmem; omega⟩ : Fin (2 * v)) ∈ C₁)
            else false
          have hsplit_σ : ∀ i : Fin v,
              ((⟨2 * i.1, by omega⟩ : Fin (2 * v)) ∈ C₁ ↔ σ (V.getD i.1 0) = true) ∧
              ((⟨2 * i.1 + 1, by omega⟩ : Fin (2 * v)) ∈ C₁ ↔ σ (V.getD i.1 0) = false) := by
            intro i
            have hi_lt : i.1 < V.length := i.2
            have hget : V.getD i.1 0 = V[i.1] := List.getD_eq_getElem V 0 hi_lt
            have hmem : V[i.1] ∈ V := List.getElem_mem hi_lt
            have hidx : V.idxOf V[i.1] = i.1 := (nodup_naeVars φ).idxOf_getElem i.1 hi_lt
            have hσi : σ (V.getD i.1 0) =
                decide ((⟨2 * i.1, by omega⟩ : Fin (2 * v)) ∈ C₁) := by
              rw [hget]
              dsimp [σ]
              simp only [hmem, ↓reduceDIte]
              congr 1
              exact propext (iff_of_eq (congrArg (· ∈ C₁) (Fin.ext (by dsimp only; rw [hidx]))))
            rw [hσi]
            have hsp := hsplit_all i
            by_cases hp0 : (⟨2 * i.1, by omega⟩ : Fin (2 * v)) ∈ C₁ <;>
              by_cases hp1 : (⟨2 * i.1 + 1, by omega⟩ : Fin (2 * v)) ∈ C₁
            all_goals simp [hp0, hp1] at hsp ⊢
          have hcard1 : C₁.card = v := by
            have hq : (C₁.card : ℚ) = (v : ℚ) := by
              have hc : (C₁.card : ℚ) = ∑ p : Fin (2 * v), if p ∈ C₁ then (1 : ℚ) else 0 := by
                rw [← sum_filter, filter_univ_mem, sum_const, nsmul_eq_mul, mul_one]
              rw [hc, sum_fin_two_mul]
              have h1_each : ∀ i : Fin v,
                  (if (⟨2 * i.1, by omega⟩ : Fin (2 * v)) ∈ C₁ then (1 : ℚ) else 0) +
                    (if (⟨2 * i.1 + 1, by omega⟩ : Fin (2 * v)) ∈ C₁ then (1 : ℚ) else 0) = 1 := by
                intro i
                have hsp := hsplit_all i
                by_cases hp0 : (⟨2 * i.1, by omega⟩ : Fin (2 * v)) ∈ C₁ <;>
                  by_cases hp1 : (⟨2 * i.1 + 1, by omega⟩ : Fin (2 * v)) ∈ C₁
                all_goals simp [hp0, hp1] at hsp ⊢
              rw [sum_congr rfl fun i _ ↦ h1_each i, sum_const, card_univ, Fintype.card_fin,
                nsmul_eq_mul, mul_one]
            exact_mod_cast hq
          have hcard2 : C₂.card = v := by
            have h12 : C₁.card + C₂.card = 2 * v := by
              rw [← card_union_of_disjoint hdisj, hunion, card_univ, Fintype.card_fin]
            omega
          have hcost_eq :=
            split_partition_cost hsyn hm1 h1 h2 hdisj hunion hcard1 hcard2 σ hsplit_σ
          dsimp only at hcost_eq
          have hcount_lt :
              (φ.countP fun c ↦ Clause.eval σ c && Clause.eval (fun u ↦ !σ u) c) < m := by
            have hle : (φ.countP fun c ↦ Clause.eval σ c && Clause.eval (fun u ↦ !σ u) c) ≤ m :=
              List.countP_le_length
            by_contra hge
            have heq_len :
                (φ.countP fun c ↦ Clause.eval σ c && Clause.eval (fun u ↦ !σ u) c) = φ.length := by
              omega
            have hall := List.countP_eq_length.mp heq_len
            apply hnotNAE
            refine ⟨hsyn, σ, ?_⟩
            simp only [CNF.evalNAE, Bool.and_eq_true, CNF.eval_eq_true_iff]
            exact ⟨fun c hc ↦ (Bool.and_eq_true_iff.mp (hall c hc)).1,
              fun c hc ↦ (Bool.and_eq_true_iff.mp (hall c hc)).2⟩
          have hcount_le_q :
              ((φ.countP fun c ↦ Clause.eval σ c && Clause.eval (fun u ↦ !σ u) c : ℕ) : ℚ) ≤
                (m : ℚ) - 1 := by
            have : (φ.countP fun c ↦ Clause.eval σ c && Clause.eval (fun u ↦ !σ u) c) + 1 ≤ m :=
              hcount_lt
            have hq : ((φ.countP fun c ↦ Clause.eval σ c && Clause.eval (fun u ↦ !σ u) c : ℕ) : ℚ) +
                1 ≤ (m : ℚ) := by exact_mod_cast this
            linarith
          rw [hcost_eq]
          have hdiv_le :
              (16 * ((φ.countP fun c ↦ Clause.eval σ c && Clause.eval (fun u ↦ !σ u) c : ℕ) : ℚ)) /
                (v : ℚ) ≤ (16 * (m : ℚ)) / (v : ℚ) - 16 / (v : ℚ) := by
            rw [← sub_div]
            exact div_le_div_of_nonneg_right (by linarith) hv_pos.le
          linarith
        · have hlow := nonsplit_var_cost_lower hsyn hm1 h1 h2 hdisj hunion hsplit_all
          dsimp only at hlow
          have hpos_div : 0 ≤ (16 * (m : ℚ)) / (v : ℚ) := by positivity
          have h16_le : 16 / (v : ℚ) ≤ 16 := by
            rw [div_le_iff₀ hv_pos]
            have : (1 : ℚ) ≤ (v : ℚ) := by
              have : 1 ≤ v := by dsimp [V, v]; omega
              exact_mod_cast this
            linarith
          linarith
  · have hnot_syn : ¬φ.IsExactThreeDistinct :=
      fun h ↦ hsyn_b ((EUThreeSAT.syntaxCheck_iff φ).mpr h)
    have hnotNAE : φ ∉ NAEEUThreeSAT := fun h ↦ hnot_syn h.1
    have hx_eq : fromNAEEUThreeSAT φ = noInstance := by
      simp [fromNAEEUThreeSAT, hsyn_b]
    have hgap_eq : gapOf φ = 2 := by simp [gapOf, hsyn_b]
    rw [hx_eq, hgap_eq]
    refine ⟨rfl, by decide, by norm_num, fun h ↦ (hnotNAE h).elim, fun _ P hP ↦ ?_⟩
    dsimp [noInstance] at P hP ⊢
    exact (by norm_num : (2 : ℚ) + 2 = 4).trans_le (noInstance_gap P hP)

theorem fromNAEEUThreeSAT_mem_iff (φ : CNF ℕ) :
    fromNAEEUThreeSAT φ ∈ TwoMeans ↔ φ ∈ NAEEUThreeSAT := by
  obtain ⟨hk2, _, hgap_pos, hyes, hno⟩ := fromNAEEUThreeSAT_gap φ
  refine ⟨fun hmem ↦ ?_, hyes⟩
  by_contra hnot
  obtain ⟨_, P, hPcard, hcost⟩ := hmem
  rw [hk2] at hPcard
  have hlow := hno hnot P hPcard
  linarith

theorem fromNAEEUThreeSAT_mem_EuclideanKMeans_iff (φ : CNF ℕ) :
    fromNAEEUThreeSAT φ ∈ EuclideanKMeans ↔ φ ∈ NAEEUThreeSAT := by
  obtain ⟨hk2, _, _, _, _⟩ := fromNAEEUThreeSAT_gap φ
  have hiff : fromNAEEUThreeSAT φ ∈ TwoMeans ↔ fromNAEEUThreeSAT φ ∈ EuclideanKMeans := by
    simp [TwoMeans, hk2]
  exact hiff.symm.trans (fromNAEEUThreeSAT_mem_iff φ)

end TwoMeans

/-- `NAEEUThreeSAT` reduces to `TwoMeans` in polynomial time. -/
theorem polyTimeReducible_NAEEUThreeSAT_TwoMeans :
    PolyTimeReducible encCNF encEuclideanKMeans NAEEUThreeSAT TwoMeans :=
  ⟨TwoMeans.fromNAEEUThreeSAT, TwoMeans.computableInPolyTime_fromNAEEUThreeSAT,
    fun φ ↦ (TwoMeans.fromNAEEUThreeSAT_mem_iff φ).symm⟩

/-- `NAEEUThreeSAT` reduces to `EuclideanKMeans` in polynomial time. -/
theorem polyTimeReducible_NAEEUThreeSAT_EuclideanKMeans :
    PolyTimeReducible encCNF encEuclideanKMeans NAEEUThreeSAT EuclideanKMeans :=
  ⟨TwoMeans.fromNAEEUThreeSAT, TwoMeans.computableInPolyTime_fromNAEEUThreeSAT,
    fun φ ↦ (TwoMeans.fromNAEEUThreeSAT_mem_EuclideanKMeans_iff φ).symm⟩

/-- **Euclidean `2`-Means is `NP`-hard.** -/
theorem TwoMeans_npHard : NPHard encEuclideanKMeans TwoMeans :=
  NAEEUThreeSAT_npHard.trans polyTimeReducible_NAEEUThreeSAT_TwoMeans

/-- **Euclidean `2`-Means is `NP`-complete.** -/
theorem TwoMeans_npComplete : NPComplete encEuclideanKMeans TwoMeans :=
  ⟨TwoMeans.mem_NP, TwoMeans_npHard⟩

/-- **Euclidean `k`-Means is `NP`-hard** (already for fixed `k = 2`). -/
theorem EuclideanKMeans_npHard : NPHard encEuclideanKMeans EuclideanKMeans :=
  NAEEUThreeSAT_npHard.trans polyTimeReducible_NAEEUThreeSAT_EuclideanKMeans

/-- **Euclidean `k`-Means is `NP`-complete.** -/
theorem EuclideanKMeans_npComplete : NPComplete encEuclideanKMeans EuclideanKMeans :=
  ⟨EuclideanKMeans.mem_NP, EuclideanKMeans_npHard⟩

end CslibFrontier.Computability.Complexity
