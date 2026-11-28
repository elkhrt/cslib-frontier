/-
Copyright (c) 2026 The cslib-frontier contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CslibFrontier.Computability.Complexity.Problems.ThreeExactCover
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Rat
public import Mathlib.Order.Partition.Finpartition

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
# NP-Completeness of Discrete Metric `k`-Median

This module establishes NP-completeness (under standard Lean axioms) on multi-tape Turing machines
for **Discrete Metric `k`-Median (`MetricKMedian`)**: deciding whether an `n`-point rational metric
space admits a `k`-partition of discrete `k`-median cost at most `B`. NP-hardness is proved via a
polynomial-time many-one reduction from `Cslib.Complexity.ThreeExactCover` over `{0, 1, 2}` graph
metrics.

## Main definitions

- `CslibFrontier.Computability.Complexity.MetricKMedianInstance`,
  `CslibFrontier.Computability.Complexity.distEntry`,
  `CslibFrontier.Computability.Complexity.IsMetricMatrix`,
  `CslibFrontier.Computability.Complexity.isMetricMatrixBool`,
  `CslibFrontier.Computability.Complexity.MetricKMedian`: discrete metric `k`-median problem.

## Main results

- `CslibFrontier.Computability.Complexity.isMetricMatrixBool_eq_true_iff`,
  `CslibFrontier.Computability.Complexity.computableInPolyTime_isMetricMatrixBool`.
- `CslibFrontier.Computability.Complexity.MetricKMedian.mem_NP`,
  `CslibFrontier.Computability.Complexity.MetricKMedian.fromThreeExactCover_mem_iff`,
  `CslibFrontier.Computability.Complexity.polyTimeReducible_ThreeExactCover_MetricKMedian`,
  `CslibFrontier.Computability.Complexity.MetricKMedian_npHard`,
  `CslibFrontier.Computability.Complexity.MetricKMedian_npComplete`.

## Tags

computational complexity, NP-completeness, k-median, exact cover by 3-sets
-/

public section

namespace CslibFrontier.Computability.Complexity

open Finset Cslib.Complexity Turing.MultiTapeTM ComputableInPolyTime

/-! ### 1. Internal Rational List-Sum and Deduplication Helpers -/

private def ratDenomProd (l : List ℚ) : ℕ :=
  (l.map Rat.den).prod

private lemma ratDenomProd_pos (l : List ℚ) : 0 < ratDenomProd l :=
  List.prod_pos fun _ hd ↦ by
    obtain ⟨q, _, rfl⟩ := List.mem_map.mp hd
    exact q.pos

private lemma dvd_ratDenomProd {l : List ℚ} {q : ℚ} (hq : q ∈ l) :
    q.den ∣ ratDenomProd l :=
  List.dvd_prod (List.mem_map.mpr ⟨q, hq, rfl⟩)

private def ratScaledNumSum (l : List ℚ) : ℤ :=
  (l.map fun q ↦ q.num * ((ratDenomProd l / q.den : ℕ) : ℤ)).sum

private lemma cast_sum_clearDenom_aux (D : ℕ) :
    ∀ (s : List ℚ), (∀ q ∈ s, q.den ∣ D) →
      (((s.map fun q ↦ q.num * ((D / q.den : ℕ) : ℤ)).sum : ℤ) : ℚ) = (D : ℚ) * s.sum
  | [], _ => by simp
  | q :: s, h => by
    simp only [List.map_cons, List.sum_cons, Int.cast_add, mul_add]
    rw [← Rat.clearDenom_entry (h q List.mem_cons_self),
      cast_sum_clearDenom_aux D s fun r hr ↦ h r (List.mem_cons_of_mem q hr)]

private lemma divInt_ratScaledNumSum (l : List ℚ) :
    Rat.divInt (ratScaledNumSum l) (ratDenomProd l : ℤ) = l.sum := by
  have hD : (ratDenomProd l : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (ratDenomProd_pos l).ne'
  rw [Rat.divInt_eq_div, Int.cast_natCast, ratScaledNumSum,
    cast_sum_clearDenom_aux (ratDenomProd l) l fun _ hq ↦ dvd_ratDenomProd hq,
    mul_div_cancel_left₀ _ hD]

@[local fun_prop]
private theorem computableInPolyTime_ratDenomProd :
    ComputableInPolyTime ratDenomProd (encList encRat) encNat := by
  unfold ratDenomProd
  fun_prop

@[local fun_prop]
private theorem computableInPolyTime_ratScaledNumSum :
    ComputableInPolyTime ratScaledNumSum (encList encRat) encIntBin := by
  unfold ratScaledNumSum
  exact intBin_sum.comp (mapWithInput id' (by fun_prop))

private theorem rat_listSum_polyTime {α : Type} {enc : α ↪ List Bool} {f : α → List ℚ}
    (hf : ComputableInPolyTime f enc (encList encRat)) :
    ComputableInPolyTime (fun a ↦ (f a).sum) enc encRat :=
  ((show ComputableInPolyTime
      (fun l : List ℚ ↦ Rat.divInt (ratScaledNumSum l) ((ratDenomProd l : ℕ) : ℤ))
      (encList encRat) encRat by fun_prop).of_enc_eq fun l ↦
    congrArg encRat (divInt_ratScaledNumSum l).symm).comp hf

private lemma sum_map_range (n : ℕ) (f : ℕ → ℚ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih,
      Finset.sum_range_succ, List.map_singleton, List.sum_singleton]

private def dedupNat (S : List ℕ) : List ℕ :=
  selectDistinct S (List.replicate S.length true)

private lemma mem_dedupNat {S : List ℕ} {v : ℕ} : v ∈ dedupNat S ↔ v ∈ S :=
  mem_selectDistinct_replicate

private lemma nodup_dedupNat (S : List ℕ) : (dedupNat S).Nodup :=
  nodup_selectDistinct _ _

@[local fun_prop]
private theorem computableInPolyTime_dedupNat :
    ComputableInPolyTime dedupNat (encList encNat) (encList encNat) := by
  unfold dedupNat
  fun_prop

/-! ### 2. Discrete Metric `k`-Median (`MetricKMedian`) -/

/-- An instance `(n, dist, k, bound)` of **Discrete Metric `k`-Median**: `n` points (unary),
explicit `n × n` rational distance matrix `dist`, cluster count `k` (binary), and rational cost
threshold `bound`. -/
@[ext]
structure MetricKMedianInstance where
  /-- Number of points in the metric space, encoded in unary. -/
  n : ℕ
  /-- Explicit `n × n` pairwise rational distance matrix. -/
  dist : List (List ℚ)
  /-- Target number of clusters `k`. -/
  k : ℕ
  /-- Upper bound on the discrete `k`-median cost. -/
  bound : ℚ
  deriving DecidableEq, Repr

/-- Encoding of `MetricKMedianInstance`. -/
enc_structure encMetricKMedian : MetricKMedianInstance where
  n : encUnary,
  dist : (encList (encList encRat)),
  k : encNat,
  bound : encRat

attribute [fun_prop] encMetricKMedian_n_polyTime encMetricKMedian_dist_polyTime
  encMetricKMedian_k_polyTime encMetricKMedian_bound_polyTime encMetricKMedian_mk_polyTime

/-- Entry `(i, j)` of a rational matrix `dist`, defaulting to `0` out of bounds. -/
@[expose]
def distEntry (dist : List (List ℚ)) (i j : ℕ) : ℚ :=
  (dist.getD i []).getD j 0

@[fun_prop]
theorem computableInPolyTime_distEntry_unary {α : Type} {enc : α ↪ List Bool}
    {dist : α → List (List ℚ)} {i j : α → ℕ}
    (hd : ComputableInPolyTime dist enc (encList (encList encRat)))
    (hi : ComputableInPolyTime i enc encUnary)
    (hj : ComputableInPolyTime j enc encUnary) :
    ComputableInPolyTime (fun a ↦ distEntry (dist a) (i a) (j a)) enc encRat :=
  listGetDWithInput (listGetDWithInput hd hi ([] : List ℚ)) hj (0 : ℚ)

private theorem computableInPolyTime_distEntry_unary_binary {α : Type} {enc : α ↪ List Bool}
    {dist : α → List (List ℚ)} {i j : α → ℕ}
    (hd : ComputableInPolyTime dist enc (encList (encList encRat)))
    (hi : ComputableInPolyTime i enc encUnary)
    (hj : ComputableInPolyTime j enc encNat) :
    ComputableInPolyTime (fun a ↦ distEntry (dist a) (i a) (j a)) enc encRat :=
  listGetD_binary (encA := encRat) (0 : ℚ) (listGetDWithInput hd hi ([] : List ℚ)) hj

/-- Predicate asserting that `dist` defines a symmetric nonnegative zero-diagonal metric satisfying
the triangle inequality on `Fin n` (with identity of indiscernibles `d i j = 0 ↔ i = j`). -/
@[expose]
def IsMetricMatrix (n : ℕ) (dist : List (List ℚ)) : Prop :=
  (∀ i j : Fin n, 0 ≤ distEntry dist i.1 j.1) ∧
  (∀ i j : Fin n, distEntry dist i.1 j.1 = 0 ↔ i = j) ∧
  (∀ i j : Fin n, distEntry dist i.1 j.1 = distEntry dist j.1 i.1) ∧
  (∀ i j l : Fin n,
    distEntry dist i.1 l.1 ≤ distEntry dist i.1 j.1 + distEntry dist j.1 l.1)

/-- Executable Boolean test for `IsMetricMatrix`. -/
def isMetricMatrixBool (n : ℕ) (dist : List (List ℚ)) : Bool :=
  ((List.range n).all fun i ↦ (List.range n).all fun j ↦
    decide (0 ≤ distEntry dist i j) &&
    (decide (distEntry dist i j = 0) == decide (i = j)) &&
    decide (distEntry dist i j = distEntry dist j i)) &&
  ((List.range n).all fun i ↦ (List.range n).all fun j ↦ (List.range n).all fun l ↦
    decide (distEntry dist i l ≤ distEntry dist i j + distEntry dist j l))

theorem isMetricMatrixBool_eq_true_iff (n : ℕ) (dist : List (List ℚ)) :
    isMetricMatrixBool n dist = true ↔ IsMetricMatrix n dist := by
  simp only [isMetricMatrixBool, IsMetricMatrix, Bool.and_eq_true, List.all_eq_true,
    List.mem_range, beq_iff_eq, decide_eq_decide, decide_eq_true_eq]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun i j ↦ ((h1 i.1 i.2 j.1 j.2).1).1,
      fun i j ↦ ((h1 i.1 i.2 j.1 j.2).1).2.trans Fin.ext_iff.symm,
      fun i j ↦ (h1 i.1 i.2 j.1 j.2).2,
      fun i j l ↦ h2 i.1 i.2 j.1 j.2 l.1 l.2⟩
  · rintro ⟨hnn, h0, hsymm, htri⟩
    refine ⟨fun i hi j hj ↦ ⟨⟨hnn ⟨i, hi⟩ ⟨j, hj⟩,
      (h0 ⟨i, hi⟩ ⟨j, hj⟩).trans Fin.ext_iff⟩, hsymm ⟨i, hi⟩ ⟨j, hj⟩⟩,
      fun i hi j hj l hl ↦ htri ⟨i, hi⟩ ⟨j, hj⟩ ⟨l, hl⟩⟩

private lemma beq_eq_decide_eq (a b : Bool) : (a == b) = decide (a = b) := by
  cases a <;> cases b <;> rfl

private lemma dite_lt_pos {α : Type*} {a k : ℕ} (ha : a < k) (t : a < k → α) (e : ¬a < k → α) :
    dite (a < k) t e = t ha := by
  split_ifs
  rfl

@[fun_prop]
theorem computableInPolyTime_isMetricMatrixBool :
    ComputableInPolyTime (fun p : ℕ × List (List ℚ) ↦ isMetricMatrixBool p.1 p.2)
      (encPair encUnary (encList (encList encRat))) encBool := by
  unfold isMetricMatrixBool
  apply bool_and'
  · apply allWithInput (ComputableInPolyTime.range.comp (fst _ _))
    apply allWithInput (ComputableInPolyTime.range.comp ((fst _ _).comp (fst _ _)))
    have hd1 : ComputableInPolyTime
        (fun q : ((ℕ × List (List ℚ)) × ℕ) × ℕ ↦ distEntry q.1.1.2 q.1.2 q.2)
        (encPair (encPair (encPair encUnary (encList (encList encRat))) encUnary) encUnary)
        encRat :=
      computableInPolyTime_distEntry_unary
        ((snd _ _).comp ((fst _ _).comp (fst _ _)))
        ((snd _ _).comp (fst _ _))
        (snd _ _)
    have hd2 : ComputableInPolyTime
        (fun q : ((ℕ × List (List ℚ)) × ℕ) × ℕ ↦ distEntry q.1.1.2 q.2 q.1.2)
        (encPair (encPair (encPair encUnary (encList (encList encRat))) encUnary) encUnary)
        encRat :=
      computableInPolyTime_distEntry_unary
        ((snd _ _).comp ((fst _ _).comp (fst _ _)))
        (snd _ _)
        ((snd _ _).comp (fst _ _))
    have hbeq : ComputableInPolyTime
        (fun q : ((ℕ × List (List ℚ)) × ℕ) × ℕ ↦
          decide (distEntry q.1.1.2 q.1.2 q.2 = 0) == decide (q.1.2 = q.2))
        (encPair (encPair (encPair encUnary (encList (encList encRat))) encUnary) encUnary)
        encBool :=
      (decide_eq' (rat_isZero.comp hd1)
        (decide_eq' ((snd _ _).comp (fst _ _)) (snd _ _))).of_enc_eq fun q ↦
        congrArg encBool (beq_eq_decide_eq _ _)
    exact bool_and' (bool_and' (rat_le' (const 0) hd1) hbeq) (rat_eq' hd1 hd2)
  · apply allWithInput (ComputableInPolyTime.range.comp (fst _ _))
    apply allWithInput (ComputableInPolyTime.range.comp ((fst _ _).comp (fst _ _)))
    apply allWithInput (ComputableInPolyTime.range.comp ((fst _ _).comp ((fst _ _).comp (fst _ _))))
    have hdist : ComputableInPolyTime
        (fun r : (((ℕ × List (List ℚ)) × ℕ) × ℕ) × ℕ ↦ r.1.1.1.2)
        (encPair
          (encPair (encPair (encPair encUnary (encList (encList encRat))) encUnary) encUnary)
          encUnary)
        (encList (encList encRat)) :=
      (snd _ _).comp ((fst _ _).comp ((fst _ _).comp (fst _ _)))
    have hi : ComputableInPolyTime
        (fun r : (((ℕ × List (List ℚ)) × ℕ) × ℕ) × ℕ ↦ r.1.1.2)
        (encPair
          (encPair (encPair (encPair encUnary (encList (encList encRat))) encUnary) encUnary)
          encUnary)
        encUnary :=
      (snd _ _).comp ((fst _ _).comp (fst _ _))
    have hj : ComputableInPolyTime
        (fun r : (((ℕ × List (List ℚ)) × ℕ) × ℕ) × ℕ ↦ r.1.2)
        (encPair
          (encPair (encPair (encPair encUnary (encList (encList encRat))) encUnary) encUnary)
          encUnary)
        encUnary :=
      (snd _ _).comp (fst _ _)
    have hl : ComputableInPolyTime
        (fun r : (((ℕ × List (List ℚ)) × ℕ) × ℕ) × ℕ ↦ r.2)
        (encPair
          (encPair (encPair (encPair encUnary (encList (encList encRat))) encUnary) encUnary)
          encUnary)
        encUnary := snd _ _
    exact rat_le' (computableInPolyTime_distEntry_unary hdist hi hl)
      (rat_add' (computableInPolyTime_distEntry_unary hdist hi hj)
        (computableInPolyTime_distEntry_unary hdist hj hl))

/-- **Discrete Metric `k`-Median**: valid metric instances admitting a `k`-partition `P` of `Fin n`
whose discrete `k`-median cost `∑_{C ∈ P} min_{c ∈ C} ∑_{i ∈ C} d(i, c)` is at most `bound`. -/
@[expose]
def MetricKMedian : Set MetricKMedianInstance :=
  {x | IsMetricMatrix x.n x.dist ∧
    ∃ P : Finpartition (univ : Finset (Fin x.n)), P.parts.card = x.k ∧
      ∑ C ∈ P.parts.attach, C.1.inf' (P.nonempty_of_mem_parts C.2)
        (fun c ↦ ∑ i ∈ C.1, distEntry x.dist i.1 c.1) ≤ x.bound}

namespace MetricKMedian

private def check (p : MetricKMedianInstance × (List ℕ × List ℕ)) : Bool :=
  let x := p.1
  let labels := p.2.1
  let centers := p.2.2
  isMetricMatrixBool x.n x.dist &&
  if decide (x.n = 0) then decide (x.k = 0) && decide (0 ≤ x.bound)
  else
    decide (1 ≤ x.k) && decide (x.k ≤ x.n) &&
    decide (labels.length = x.n) &&
    decide (centers.length = x.k) &&
    ((List.range x.n).all fun i ↦ decide (labels.getD i 0 < x.k)) &&
    ((List.range centers.length).all fun a ↦
      decide (centers.getD a 0 < x.n) &&
      decide (labels.getD (centers.getD a 0) 0 = a)) &&
    decide (((List.range x.n).map fun i ↦
      distEntry x.dist i (centers.getD (labels.getD i 0) 0)).sum ≤ x.bound)

private theorem computableInPolyTime_check :
    ComputableInPolyTime check
      (encPair encMetricKMedian (encPair (encList encNat) (encList encNat))) encBool := by
  let E := encPair encMetricKMedian (encPair (encList encNat) (encList encNat))
  have hX : ComputableInPolyTime (fun p : MetricKMedianInstance × (List ℕ × List ℕ) ↦ p.1)
      E encMetricKMedian := fst _ _
  have hn : ComputableInPolyTime (fun p : MetricKMedianInstance × (List ℕ × List ℕ) ↦ p.1.n)
      E encUnary := encMetricKMedian_n_polyTime hX
  have hn_bin : ComputableInPolyTime (fun p : MetricKMedianInstance × (List ℕ × List ℕ) ↦ p.1.n)
      E encNat := unary_to_binary.comp hn
  have hdist : ComputableInPolyTime (fun p : MetricKMedianInstance × (List ℕ × List ℕ) ↦ p.1.dist)
      E (encList (encList encRat)) := encMetricKMedian_dist_polyTime hX
  have hk : ComputableInPolyTime (fun p : MetricKMedianInstance × (List ℕ × List ℕ) ↦ p.1.k)
      E encNat := encMetricKMedian_k_polyTime hX
  have hB : ComputableInPolyTime (fun p : MetricKMedianInstance × (List ℕ × List ℕ) ↦ p.1.bound)
      E encRat := encMetricKMedian_bound_polyTime hX
  have hlab : ComputableInPolyTime (fun p : MetricKMedianInstance × (List ℕ × List ℕ) ↦ p.2.1)
      E (encList encNat) := (fst _ _).comp (snd _ _)
  have hcen : ComputableInPolyTime (fun p : MetricKMedianInstance × (List ℕ × List ℕ) ↦ p.2.2)
      E (encList encNat) := (snd _ _).comp (snd _ _)
  have hmet : ComputableInPolyTime
      (fun p : MetricKMedianInstance × (List ℕ × List ℕ) ↦ isMetricMatrixBool p.1.n p.1.dist)
      E encBool := computableInPolyTime_isMetricMatrixBool.comp (hn.prod hdist)
  have hall1 : ComputableInPolyTime
      (fun p : MetricKMedianInstance × (List ℕ × List ℕ) ↦
        (List.range p.1.n).all fun i ↦ decide (p.2.1.getD i 0 < p.1.k)) E encBool :=
    allWithInput (ComputableInPolyTime.range.comp hn)
      (binary_lt' (listGetDWithInput (hlab.comp (fst _ _)) (snd _ _) 0)
        (hk.comp (fst _ _)))
  have hall2 : ComputableInPolyTime
      (fun p : MetricKMedianInstance × (List ℕ × List ℕ) ↦
        (List.range p.2.2.length).all fun a ↦
          decide (p.2.2.getD a 0 < p.1.n) &&
          decide (p.2.1.getD (p.2.2.getD a 0) 0 = a)) E encBool := by
    apply allWithInput (ComputableInPolyTime.range.comp ((length_list encNat).comp hcen))
    have hca : ComputableInPolyTime
        (fun q : (MetricKMedianInstance × (List ℕ × List ℕ)) × ℕ ↦ q.1.2.2.getD q.2 0)
        (encPair E encUnary) encNat :=
      listGetDWithInput (hcen.comp (fst _ _)) (snd _ _) 0
    exact bool_and'
      (binary_lt' hca (hn_bin.comp (fst _ _)))
      (decide_eq' (listGetD_binary (encA := encNat) 0 (hlab.comp (fst _ _)) hca)
        (unary_to_binary.comp (snd _ _)))
  have hcost : ComputableInPolyTime
      (fun p : MetricKMedianInstance × (List ℕ × List ℕ) ↦
        decide (((List.range p.1.n).map fun i ↦
          distEntry p.1.dist i (p.2.2.getD (p.2.1.getD i 0) 0)).sum ≤ p.1.bound)) E encBool := by
    refine rat_le'
      (rat_listSum_polyTime (mapWithInput (ComputableInPolyTime.range.comp hn) ?_)) hB
    have hli : ComputableInPolyTime
        (fun q : (MetricKMedianInstance × (List ℕ × List ℕ)) × ℕ ↦ q.1.2.1.getD q.2 0)
        (encPair E encUnary) encNat :=
      listGetDWithInput (hlab.comp (fst _ _)) (snd _ _) 0
    exact computableInPolyTime_distEntry_unary_binary
      (hdist.comp (fst _ _)) (snd _ _)
      (listGetD_binary (encA := encNat) 0 (hcen.comp (fst _ _)) hli)
  unfold check
  dsimp only
  refine bool_and' hmet (ite' (decide_eq' hn (const 0))
    (bool_and' (decide_eq' hk (const 0)) (rat_le' (const 0) hB)) ?_)
  exact bool_and'
    (bool_and'
      (bool_and'
        (bool_and'
          (bool_and'
            (bool_and' (binary_le' (const 1) hk) (binary_le' hk hn_bin))
            (decide_eq' ((length_list encNat).comp hlab) hn))
          (decide_eq' (unary_to_binary.comp ((length_list encNat).comp hcen)) hk))
        hall1)
      hall2)
    hcost

private theorem exists_finpartition_of_assign {V : Type*} [Fintype V] [DecidableEq V]
    {k : ℕ} (α : V → ℕ) (cOf : ℕ → V) (hlt : ∀ v : V, α v < k)
    (hc : ∀ a < k, α (cOf a) = a) :
    ∃ P : Finpartition (univ : Finset V), P.parts.card = k ∧
      ∀ C ∈ P.parts, ∃ a < k, cOf a ∈ C ∧ ∀ v ∈ C, α v = a := by
  let clusterOf (a : ℕ) : Finset V := univ.filter fun v ↦ α v = a
  let parts : Finset (Finset V) := (Finset.range k).image clusterOf
  have hinj : Set.InjOn clusterOf (Finset.range k : Set ℕ) := by
    intro a₁ ha₁ a₂ _ hEq
    have ha₁' : a₁ < k := Finset.mem_range.mp ha₁
    have hmem1 : cOf a₁ ∈ clusterOf a₁ := mem_filter.mpr ⟨mem_univ _, hc a₁ ha₁'⟩
    have hmem2 : cOf a₁ ∈ clusterOf a₂ := hEq ▸ hmem1
    exact (hc a₁ ha₁').symm.trans (mem_filter.mp hmem2).2
  have hpw : (parts : Set (Finset V)).PairwiseDisjoint id := by
    intro A hA B hB hAB
    simp only [parts, coe_image, Set.mem_image, mem_coe] at hA hB
    rcases hA with ⟨a₁, _, rfl⟩
    rcases hB with ⟨a₂, _, rfl⟩
    refine Finset.disjoint_left.mpr fun v hv1 hv2 ↦ hAB ?_
    simp only [id_eq, clusterOf, mem_filter, mem_univ, true_and] at hv1 hv2
    rw [← hv1, hv2]
  have hsup : parts.sup id = (univ : Finset V) := by
    ext v
    simp only [parts, sup_image, id_eq, Function.comp_def, sup_eq_biUnion, mem_biUnion,
      Finset.mem_range, clusterOf, mem_filter, mem_univ, true_and, iff_true]
    exact ⟨α v, hlt v, rfl⟩
  have hbot : (⊥ : Finset V) ∉ parts := by
    simp only [parts, bot_eq_empty, mem_image, Finset.mem_range]
    rintro ⟨a, ha, hEmpty⟩
    have hmem : cOf a ∈ clusterOf a := mem_filter.mpr ⟨mem_univ _, hc a ha⟩
    rw [hEmpty] at hmem
    exact notMem_empty _ hmem
  let P : Finpartition (univ : Finset V) := ⟨parts, hpw.supIndep, hsup, hbot⟩
  refine ⟨P, ?_, fun C hC ↦ ?_⟩
  · dsimp [P, parts]
    rw [card_image_of_injOn hinj, card_range]
  · obtain ⟨a, ha, rfl⟩ := mem_image.mp hC
    have ha' : a < k := Finset.mem_range.mp ha
    exact ⟨a, ha', mem_filter.mpr ⟨mem_univ _, hc a ha'⟩, fun v hv ↦ (mem_filter.mp hv).2⟩

private theorem mem_of_check {x : MetricKMedianInstance} {w : List ℕ × List ℕ}
    (h : check (x, w) = true) : x ∈ MetricKMedian := by
  unfold check at h
  simp only [Bool.and_eq_true] at h
  rcases h with ⟨hmet, hrest⟩
  refine ⟨(isMetricMatrixBool_eq_true_iff x.n x.dist).mp hmet, ?_⟩
  by_cases hn0 : x.n = 0
  · simp only [decide_eq_true hn0, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq] at hrest
    rcases hrest with ⟨hxk, hbound⟩
    have hemp : (univ : Finset (Fin x.n)) = ⊥ :=
      card_eq_zero.mp (by rw [card_univ, Fintype.card_fin, hn0])
    let P : Finpartition (univ : Finset (Fin x.n)) := (Finpartition.empty _).copy hemp.symm
    have hPparts : P.parts = ∅ := by simp [P]
    have hattach_emp : P.parts.attach = ∅ :=
      card_eq_zero.mp (by rw [card_attach, hPparts, card_empty])
    refine ⟨P, by rw [hPparts, card_empty, hxk], ?_⟩
    rw [hattach_emp, sum_empty]
    exact hbound
  · simp only [decide_eq_false hn0, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true,
      decide_eq_true_eq, List.all_eq_true, List.mem_range] at hrest
    rcases hrest with ⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, hclen⟩, hlt_k⟩, hcenters_raw⟩, hcost⟩
    have hcenters : ∀ a < x.k, w.2.getD a 0 < x.n ∧ w.1.getD (w.2.getD a 0) 0 = a :=
      fun a ha ↦ hcenters_raw a (hclen.symm ▸ ha)
    have hpos : 0 < x.n := Nat.pos_of_ne_zero hn0
    let cOf (a : ℕ) : Fin x.n :=
      if ha : a < x.k then ⟨w.2.getD a 0, (hcenters a ha).1⟩ else ⟨0, hpos⟩
    obtain ⟨P, hPcard, hPclusters⟩ :=
      exists_finpartition_of_assign (fun i : Fin x.n ↦ w.1.getD i.1 0) cOf
        (fun i ↦ hlt_k i.1 i.2)
        (fun a ha ↦ by
          dsimp [cOf]
          rw [dite_lt_pos ha]
          exact (hcenters a ha).2)
    refine ⟨P, hPcard, ?_⟩
    set fTerm : Fin x.n → ℚ := fun i ↦ distEntry x.dist i.1 (w.2.getD (w.1.getD i.1 0) 0)
    have hsum_univ : ∑ i : Fin x.n, fTerm i =
        ((List.range x.n).map fun i ↦ distEntry x.dist i (w.2.getD (w.1.getD i 0) 0)).sum := by
      rw [sum_map_range,
        ← Fin.sum_univ_eq_sum_range
          (fun i : ℕ ↦ distEntry x.dist i (w.2.getD (w.1.getD i 0) 0)) x.n]
    have hsplit : ∑ i : Fin x.n, fTerm i =
        ∑ C ∈ P.parts.attach, ∑ i ∈ C.1, fTerm i := by
      have hu : (univ : Finset (Fin x.n)) = P.parts.biUnion id := by
        rw [← sup_eq_biUnion, P.sup_parts]
      rw [sum_attach P.parts (fun C : Finset (Fin x.n) ↦ ∑ i ∈ C, fTerm i)]
      calc
        ∑ i ∈ (univ : Finset (Fin x.n)), fTerm i = ∑ i ∈ P.parts.biUnion id, fTerm i :=
          congrArg (fun s ↦ ∑ i ∈ s, fTerm i) hu
        _ = ∑ C ∈ P.parts, ∑ i ∈ C, fTerm i := by
          rw [sum_biUnion (fun A hA B hB hAB ↦ P.disjoint hA hB hAB)]
          rfl
    have hpart_le : ∀ C ∈ P.parts.attach,
        C.1.inf' (P.nonempty_of_mem_parts C.2)
          (fun c ↦ ∑ i ∈ C.1, distEntry x.dist i.1 c.1) ≤ ∑ i ∈ C.1, fTerm i := by
      intro C _
      obtain ⟨a, ha, hcaC, hmemC⟩ := hPclusters C.1 C.2
      have hsum_ca : ∑ i ∈ C.1, fTerm i = ∑ i ∈ C.1, distEntry x.dist i.1 (cOf a).1 := by
        refine sum_congr rfl fun i hi ↦ ?_
        dsimp [fTerm, cOf]
        rw [dite_lt_pos ha, hmemC i hi]
      rw [hsum_ca]
      exact inf'_le (fun c : Fin x.n ↦ ∑ i ∈ C.1, distEntry x.dist i.1 c.1) hcaC
    exact ((sum_le_sum hpart_le).trans_eq (hsplit.symm.trans hsum_univ)).trans hcost

private noncomputable def witnessPoly : Polynomial ℕ :=
  3 * Polynomial.X * (2 * Polynomial.X + 1) + 5

private theorem exists_check_of_mem {x : MetricKMedianInstance} (hx : x ∈ MetricKMedian) :
    ∃ w : List ℕ × List ℕ, check (x, w) = true ∧
      (encPair (encList encNat) (encList encNat) w).length ≤
        witnessPoly.eval (encMetricKMedian x).length := by
  rcases hx with ⟨hmet, P, hPcard, hcost⟩
  set L := (encMetricKMedian x).length
  have hnL : x.n ≤ L := by
    simpa only [encUnary_apply, List.length_replicate] using encMetricKMedian_n_length_le x
  have hpoly_val : witnessPoly.eval L = 3 * L * (2 * L + 1) + 5 := by simp [witnessPoly]
  have hmet_bool : isMetricMatrixBool x.n x.dist = true :=
    (isMetricMatrixBool_eq_true_iff x.n x.dist).mpr hmet
  by_cases hn0 : x.n = 0
  · refine ⟨([], []), ?_, ?_⟩
    · have hemp : P.parts = ∅ := by
        by_contra hne
        obtain ⟨C, hC⟩ := nonempty_iff_ne_empty.mpr hne
        obtain ⟨i, _⟩ := P.nonempty_of_mem_parts hC
        exact Fin.elim0 (hn0 ▸ i)
      have hk0 : x.k = 0 := by rw [← hPcard, hemp, card_empty]
      have hcost0 : 0 ≤ x.bound := by
        have hattach_emp : P.parts.attach = ∅ :=
          card_eq_zero.mp (by rw [card_attach, hemp, card_empty])
        have hsum0 : ∑ C ∈ P.parts.attach, C.1.inf' (P.nonempty_of_mem_parts C.2)
            (fun c ↦ ∑ i ∈ C.1, distEntry x.dist i.1 c.1) = 0 := by
          rw [hattach_emp, sum_empty]
        rwa [hsum0] at hcost
      unfold check
      simp only [hmet_bool, decide_eq_true hn0, ↓reduceIte, decide_eq_true hk0,
        decide_eq_true hcost0, Bool.and_self]
    · rw [hpoly_val, length_encPair]
      have h0 : (encList encNat ([] : List ℕ)).length = 0 := rfl
      rw [h0]
      omega
  · have hkle : x.k ≤ x.n := by
      have hsup : (P.parts.sup id).card = x.n := by rw [P.sup_parts, card_univ, Fintype.card_fin]
      have hsum_c : ∑ C ∈ P.parts, C.card = (P.parts.sup id).card := by
        rw [sup_eq_biUnion, card_biUnion (fun A hA B hB hAB ↦ P.disjoint hA hB hAB)]
        rfl
      have hle_sum : P.parts.card ≤ ∑ C ∈ P.parts, C.card := by
        calc
          P.parts.card = ∑ _C ∈ P.parts, 1 := by simp
          _ ≤ ∑ C ∈ P.parts, C.card :=
            sum_le_sum fun C hC ↦ Nat.succ_le_of_lt (P.nonempty_of_mem_parts hC).card_pos
      omega
    have hk1 : 1 ≤ x.k := by
      by_contra hlt
      have hk0 : x.k = 0 := by omega
      have hemp : P.parts = ∅ := card_eq_zero.mp (hPcard.trans hk0)
      have huniv : (univ : Finset (Fin x.n)) = ∅ := by
        rw [← P.sup_parts, hemp, sup_empty, bot_eq_empty]
      have : x.n = 0 := by simpa [Fintype.card_fin] using congrArg Finset.card huniv
      exact hn0 this
    let e := P.parts.equivFin.trans (finCongr hPcard)
    have hvpart : ∀ i : Fin x.n, ∃ C : P.parts, i ∈ C.1 := by
      intro i
      have hi : i ∈ P.parts.sup id := by rw [P.sup_parts]; exact mem_univ i
      rw [sup_eq_biUnion, mem_biUnion] at hi
      rcases hi with ⟨C, hC, hiC⟩
      exact ⟨⟨C, hC⟩, hiC⟩
    let partOf (i : Fin x.n) : P.parts := Classical.choose (hvpart i)
    have hpartOf_eq : ∀ (C : P.parts) {i : Fin x.n}, i ∈ C.1 → partOf i = C := by
      intro C i hi
      by_contra hne
      exact Finset.disjoint_left.mp (P.disjoint (partOf i).2 C.2 (Subtype.coe_ne_coe.mpr hne))
        (Classical.choose_spec (hvpart i)) hi
    have hmin : ∀ C : P.parts, ∃ c ∈ C.1,
        C.1.inf' (P.nonempty_of_mem_parts C.2)
          (fun m ↦ ∑ i ∈ C.1, distEntry x.dist i.1 m.1) =
          ∑ i ∈ C.1, distEntry x.dist i.1 c.1 :=
      fun C ↦ exists_mem_eq_inf' (P.nonempty_of_mem_parts C.2) _
    choose cMin hcMin_mem hcMin_eq using hmin
    let labels : List ℕ := List.ofFn fun i : Fin x.n ↦ (e (partOf i)).1
    let centers : List ℕ := List.ofFn fun a : Fin x.k ↦ (cMin (e.symm a)).1
    refine ⟨(labels, centers), ?_, ?_⟩
    · unfold check
      dsimp only
      simp only [hmet_bool, decide_eq_false hn0, Bool.false_eq_true, ↓reduceIte, Bool.true_and,
        Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range]
      refine ⟨⟨⟨⟨⟨⟨hk1, hkle⟩, List.length_ofFn⟩, List.length_ofFn⟩, ?_⟩, ?_⟩, ?_⟩
      · intro i hi
        have hget : labels.getD i 0 = (e (partOf ⟨i, hi⟩)).1 := by
          simp [labels, List.getD_eq_getElem?_getD, hi]
        rw [hget]
        exact (e (partOf ⟨i, hi⟩)).2
      · intro a ha
        rw [List.length_ofFn] at ha
        have hcget : centers.getD a 0 = (cMin (e.symm ⟨a, ha⟩)).1 := by
          simp [centers, List.getD_eq_getElem?_getD, ha]
        rw [hcget]
        refine ⟨(cMin (e.symm ⟨a, ha⟩)).2, ?_⟩
        have hlget : labels.getD (cMin (e.symm ⟨a, ha⟩)).1 0 =
            (e (partOf (cMin (e.symm ⟨a, ha⟩)))).1 := by
          simp [labels, List.getD_eq_getElem?_getD, (cMin (e.symm ⟨a, ha⟩)).2]
        rw [hlget, hpartOf_eq (e.symm ⟨a, ha⟩) (hcMin_mem _), e.apply_symm_apply]
      · set gTerm : Fin x.n → ℚ :=
          fun i ↦ distEntry x.dist i.1 (centers.getD (labels.getD i.1 0) 0)
        have hsum_eq :
            ((List.range x.n).map fun i ↦
              distEntry x.dist i (centers.getD (labels.getD i 0) 0)).sum =
            ∑ C ∈ P.parts.attach, C.1.inf' (P.nonempty_of_mem_parts C.2)
              (fun c ↦ ∑ i ∈ C.1, distEntry x.dist i.1 c.1) := by
          rw [sum_map_range, ← Fin.sum_univ_eq_sum_range]
          have hu : (univ : Finset (Fin x.n)) = P.parts.biUnion id := by
            rw [← sup_eq_biUnion, P.sup_parts]
          have hpart_sum :
              ∑ i : Fin x.n, gTerm i = ∑ C ∈ P.parts.attach, ∑ i ∈ C.1, gTerm i := by
            rw [sum_attach P.parts (fun C : Finset (Fin x.n) ↦ ∑ i ∈ C, gTerm i)]
            calc
              ∑ i ∈ (univ : Finset (Fin x.n)), gTerm i = ∑ i ∈ P.parts.biUnion id, gTerm i :=
                congrArg (fun s ↦ ∑ i ∈ s, gTerm i) hu
              _ = ∑ C ∈ P.parts, ∑ i ∈ C, gTerm i := by
                rw [sum_biUnion (fun A hA B hB hAB ↦ P.disjoint hA hB hAB)]
                rfl
          change ∑ i : Fin x.n, gTerm i = _
          rw [hpart_sum]
          refine sum_congr rfl fun C _ ↦ ?_
          rw [hcMin_eq C]
          refine sum_congr rfl fun i hi ↦ ?_
          dsimp [gTerm]
          have hl : labels.getD i.1 0 = (e C).1 := by
            simp [labels, List.getD_eq_getElem?_getD, i.2, hpartOf_eq C hi]
          have hc : centers.getD (e C).1 0 = (cMin C).1 := by
            simp [centers, List.getD_eq_getElem?_getD, (e C).2]
          rw [hl, hc]
        rw [hsum_eq]
        exact hcost
    · rw [hpoly_val, length_encPair]
      have hlen_nat : ∀ v : ℕ, v < x.n → (encNat v).length ≤ L := by
        intro v hv
        rw [encNat_apply, Nat.size_eq_bits_len]
        exact Nat.size_le.mpr (hv.trans_le (hnL.trans Nat.lt_two_pow_self.le))
      have h1 : (encList encNat labels).length ≤ x.n * (2 * L + 1) := by
        have := length_encList_le encNat labels (b := L) fun v hv ↦ by
          obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).mp hv
          exact hlen_nat _ ((e (partOf i)).2.trans_le hkle)
        simpa [labels] using this
      have h2 : (encList encNat centers).length ≤ x.k * (2 * L + 1) := by
        have := length_encList_le encNat centers (b := L) fun v hv ↦ by
          obtain ⟨a, rfl⟩ := (List.mem_ofFn' _ _).mp hv
          exact hlen_nat _ (cMin (e.symm a)).2
        simpa [centers] using this
      have hkL : x.k ≤ L := hkle.trans hnL
      nlinarith

/-- `MetricKMedian` belongs to `NP`. -/
theorem mem_NP : MetricKMedian ∈ NP encMetricKMedian :=
  mem_NP_of_check (.pair (.list .nat) (.list .nat)) computableInPolyTime_check
    (fun _ _ h ↦ mem_of_check h) fun _ hx ↦ exists_check_of_mem hx

/-! #### Reduction from `ThreeExactCover` to `MetricKMedian` -/

private lemma exists_dominating_of_kMedian_le {N k : ℕ} {dist : List (List ℚ)}
    {adj : ℕ → ℕ → Bool}
    (hdist : ∀ i j : Fin N,
      distEntry dist i.1 j.1 = if i.1 = j.1 then 0 else if adj i.1 j.1 = true then 1 else 2)
    {P : Finpartition (univ : Finset (Fin N))} (hPcard : P.parts.card = k)
    (hcost : ∑ B ∈ P.parts.attach, B.1.inf' (P.nonempty_of_mem_parts B.2)
      (fun c ↦ ∑ i ∈ B.1, distEntry dist i.1 c.1) ≤ ((N - k : ℕ) : ℚ)) :
    ∃ Dom : Finset (Fin N), Dom.card = k ∧
      ∀ v : Fin N, v ∈ Dom ∨ ∃ d ∈ Dom, adj v.1 d.1 = true := by
  have hcenter : ∀ B : P.parts, ∃ c ∈ B.1,
      B.1.inf' (P.nonempty_of_mem_parts B.2)
        (fun z ↦ ∑ i ∈ B.1, distEntry dist i.1 z.1) =
      ∑ i ∈ B.1, distEntry dist i.1 c.1 :=
    fun B ↦ exists_mem_eq_inf' (P.nonempty_of_mem_parts B.2) _
  choose center hcenter_mem hcenter_eq using hcenter
  have hcenter_inj : Function.Injective center := by
    intro B₁ B₂ h
    by_contra hne
    exact Finset.disjoint_left.mp (P.disjoint B₁.2 B₂.2 (Subtype.coe_ne_coe.mpr hne))
      (hcenter_mem B₁) (h ▸ hcenter_mem B₂)
  let Dom : Finset (Fin N) := P.parts.attach.image center
  have hDom_card : Dom.card = k := by
    rw [card_image_of_injective _ hcenter_inj, card_attach, hPcard]
  have hsum_parts : ∑ B ∈ P.parts.attach, (B.1.card - 1 : ℕ) = N - k := by
    have h1 : ∑ B ∈ P.parts.attach, B.1.card = N := by
      rw [sum_attach P.parts (fun B : Finset (Fin N) ↦ B.card)]
      have hs : (P.parts.sup id).card = N := by
        rw [P.sup_parts, card_univ, Fintype.card_fin]
      calc
        ∑ x ∈ P.parts, x.card = (P.parts.sup id).card := by
          rw [sup_eq_biUnion, card_biUnion (fun A hA B hB hAB ↦ P.disjoint hA hB hAB)]
          rfl
        _ = N := hs
    have h2 : ∑ B ∈ P.parts.attach, (B.1.card - 1 : ℕ) + P.parts.attach.card =
        ∑ B ∈ P.parts.attach, B.1.card := by
      have hc1 : P.parts.attach.card = ∑ _B ∈ P.parts.attach, 1 := by simp
      rw [hc1, ← sum_add_distrib]
      refine sum_congr rfl fun B _ ↦ ?_
      have := (P.nonempty_of_mem_parts B.2).card_pos
      omega
    rw [card_attach, hPcard, h1] at h2
    omega
  have hlower : ∀ B : P.parts,
      ((B.1.card - 1 : ℕ) : ℚ) ≤ ∑ i ∈ B.1, distEntry dist i.1 (center B).1 := by
    intro B
    have hc0 : distEntry dist (center B).1 (center B).1 = 0 := by
      rw [hdist (center B) (center B)]; simp
    rw [← sum_erase_add _ _ (hcenter_mem B), hc0, add_zero]
    calc
      ((B.1.card - 1 : ℕ) : ℚ) = ∑ _i ∈ B.1.erase (center B), (1 : ℚ) := by
        simp [card_erase_of_mem (hcenter_mem B)]
      _ ≤ ∑ i ∈ B.1.erase (center B), distEntry dist i.1 (center B).1 := by
        refine sum_le_sum fun i hi ↦ ?_
        have hne : i.1 ≠ (center B).1 := fun h ↦ (mem_erase.mp hi).1 (Fin.ext h)
        rw [hdist i (center B)]
        simp only [hne, ↓reduceIte]
        split_ifs <;> norm_num
  refine ⟨Dom, hDom_card, fun v ↦ ?_⟩
  have hv : v ∈ P.parts.sup id := by rw [P.sup_parts]; exact mem_univ v
  rw [sup_eq_biUnion, mem_biUnion] at hv
  rcases hv with ⟨B, hB, hvB⟩
  let Bp : P.parts := ⟨B, hB⟩
  by_cases hvc : v = center Bp
  · exact Or.inl (hvc ▸ mem_image_of_mem center (mem_attach _ Bp))
  · right
    refine ⟨center Bp, mem_image_of_mem center (mem_attach _ Bp), ?_⟩
    have hsum_le :
        ∑ A ∈ P.parts.attach, ∑ i ∈ A.1, distEntry dist i.1 (center A).1 ≤
          ∑ A ∈ P.parts.attach, ((A.1.card - 1 : ℕ) : ℚ) := by
      calc
        _ = ∑ A ∈ P.parts.attach, A.1.inf' (P.nonempty_of_mem_parts A.2)
              (fun z ↦ ∑ i ∈ A.1, distEntry dist i.1 z.1) :=
          sum_congr rfl fun A _ ↦ (hcenter_eq A).symm
        _ ≤ ((N - k : ℕ) : ℚ) := hcost
        _ = ∑ A ∈ P.parts.attach, ((A.1.card - 1 : ℕ) : ℚ) := by
          exact_mod_cast hsum_parts.symm
    have hsum_eq := le_antisymm (sum_le_sum fun A _ ↦ hlower A) hsum_le
    have hBp_eq := ((sum_eq_sum_iff_of_le (fun A _ ↦ hlower A)).mp hsum_eq
      Bp (mem_attach _ Bp)).symm
    have hc0 : distEntry dist (center Bp).1 (center Bp).1 = 0 := by
      rw [hdist (center Bp) (center Bp)]; simp
    have hcB : center Bp ∈ B := hcenter_mem Bp
    rw [← sum_erase_add B _ hcB, hc0, add_zero] at hBp_eq
    have h1sum : ∑ _i ∈ B.erase (center Bp), (1 : ℚ) = ((B.card - 1 : ℕ) : ℚ) := by
      rw [sum_const, card_erase_of_mem hcB, nsmul_eq_mul, mul_one]
    have hv_eq := (sum_eq_sum_iff_of_le (s := B.erase (center Bp))
      (f := fun _ ↦ (1 : ℚ))
      (g := fun i ↦ distEntry dist i.1 (center Bp).1)
      (fun i hi ↦ by
        have hne : i.1 ≠ (center Bp).1 := fun h ↦ (mem_erase.mp hi).1 (Fin.ext h)
        rw [hdist i (center Bp)]
        simp only [hne, ↓reduceIte]
        split_ifs <;> norm_num)).mp (h1sum.trans hBp_eq.symm) v
      (mem_erase.mpr ⟨hvc, hvB⟩)
    have hne : v.1 ≠ (center Bp).1 := fun h ↦ hvc (Fin.ext h)
    rw [hdist v (center Bp)] at hv_eq
    simp only [hne, ↓reduceIte] at hv_eq
    by_cases hadj : adj v.1 (center Bp).1 = true
    · exact hadj
    · simp [hadj] at hv_eq

private lemma exists_kMedian_le_of_dominating {N k : ℕ} {dist : List (List ℚ)}
    {adj : ℕ → ℕ → Bool}
    (hdist : ∀ i j : Fin N,
      distEntry dist i.1 j.1 = if i.1 = j.1 then 0 else if adj i.1 j.1 = true then 1 else 2)
    {Dom : Finset (Fin N)} (hDom_card : Dom.card = k)
    (hdom_all : ∀ v : Fin N, ∃ d ∈ Dom, v = d ∨ adj v.1 d.1 = true) :
    ∃ P : Finpartition (univ : Finset (Fin N)), P.parts.card = k ∧
      ∑ B ∈ P.parts.attach, B.1.inf' (P.nonempty_of_mem_parts B.2)
        (fun c ↦ ∑ i ∈ B.1, distEntry dist i.1 c.1) ≤ ((N - k : ℕ) : ℚ) := by
  by_cases hN0 : N = 0
  · have hDom_emp : Dom = ∅ := eq_empty_iff_forall_notMem.mpr fun v _ ↦ Fin.elim0 (hN0 ▸ v)
    have hk0 : k = 0 := by rw [← hDom_card, hDom_emp, card_empty]
    have hemp : (univ : Finset (Fin N)) = ⊥ :=
      card_eq_zero.mp (by rw [card_univ, Fintype.card_fin, hN0])
    let P : Finpartition (univ : Finset (Fin N)) := (Finpartition.empty _).copy hemp.symm
    have hPparts : P.parts = ∅ := by simp [P]
    have hattach_emp : P.parts.attach = ∅ :=
      card_eq_zero.mp (by rw [card_attach, hPparts, card_empty])
    refine ⟨P, by rw [hPparts, card_empty, hk0], ?_⟩
    rw [hattach_emp, sum_empty, hN0, hk0]
    norm_num
  · have hNpos : 0 < N := Nat.pos_of_ne_zero hN0
    let eDom : Dom ≃ Fin k := Dom.equivFin.trans (finCongr hDom_card)
    let αFin (v : Fin N) : Dom :=
      if hv : v ∈ Dom then ⟨v, hv⟩
      else ⟨Classical.choose (hdom_all v), (Classical.choose_spec (hdom_all v)).1⟩
    let cOf (a : ℕ) : Fin N :=
      if ha : a < k then (eDom.symm ⟨a, ha⟩).1 else ⟨0, hNpos⟩
    have hα_self : ∀ d : Dom, αFin d.1 = d := fun d ↦ by simp [αFin, d.2]
    have hα_dist : ∀ v : Fin N, v ≠ (αFin v).1 → distEntry dist v.1 (αFin v).1.1 = 1 := by
      intro v hne
      have hvnot : v ∉ Dom := fun hv ↦ hne (by simp [αFin, hv])
      have hαeq : (αFin v).1 = Classical.choose (hdom_all v) := by simp [αFin, hvnot]
      have hspec := (Classical.choose_spec (hdom_all v)).2
      rw [hαeq] at hne ⊢
      rcases hspec with hEq | hadj
      · exact (hne hEq).elim
      · rw [hdist v (Classical.choose (hdom_all v))]
        have hne_val : v.1 ≠ (Classical.choose (hdom_all v)).1 := fun h ↦ hne (Fin.ext h)
        simp [hne_val, hadj]
    obtain ⟨P, hPcard, hPclusters⟩ :=
      exists_finpartition_of_assign (fun v : Fin N ↦ (eDom (αFin v)).1) cOf
        (fun v ↦ (eDom (αFin v)).2)
        (fun a ha ↦ by
          dsimp [cOf]
          rw [dite_lt_pos ha, hα_self (eDom.symm ⟨a, ha⟩), eDom.apply_symm_apply])
    refine ⟨P, hPcard, ?_⟩
    have hsum_parts : ∑ B ∈ P.parts.attach, (B.1.card - 1 : ℕ) = N - k := by
      have h1 : ∑ B ∈ P.parts.attach, B.1.card = N := by
        rw [sum_attach P.parts (fun B : Finset (Fin N) ↦ B.card)]
        have hs : (P.parts.sup id).card = N := by
          rw [P.sup_parts, card_univ, Fintype.card_fin]
        calc
          ∑ x ∈ P.parts, x.card = (P.parts.sup id).card := by
            rw [sup_eq_biUnion, card_biUnion (fun A hA B hB hAB ↦ P.disjoint hA hB hAB)]
            rfl
          _ = N := hs
      have h2 : ∑ B ∈ P.parts.attach, (B.1.card - 1 : ℕ) + P.parts.attach.card =
          ∑ B ∈ P.parts.attach, B.1.card := by
        have hc1 : P.parts.attach.card = ∑ _B ∈ P.parts.attach, 1 := by simp
        rw [hc1, ← sum_add_distrib]
        refine sum_congr rfl fun B _ ↦ ?_
        have := (P.nonempty_of_mem_parts B.2).card_pos
        omega
      rw [card_attach, hPcard, h1] at h2
      omega
    have hpart_le : ∀ B ∈ P.parts.attach,
        B.1.inf' (P.nonempty_of_mem_parts B.2)
          (fun c ↦ ∑ i ∈ B.1, distEntry dist i.1 c.1) ≤ ((B.1.card - 1 : ℕ) : ℚ) := by
      intro B _
      obtain ⟨a, ha, hdB, hmemB⟩ := hPclusters B.1 B.2
      let d : Fin N := cOf a
      have hd_eq : d = (eDom.symm ⟨a, ha⟩).1 := by dsimp [d, cOf]; rw [dite_lt_pos ha]
      have hsum_d : ((B.1.card - 1 : ℕ) : ℚ) = ∑ i ∈ B.1, distEntry dist i.1 d.1 := by
        have hd0 : distEntry dist d.1 d.1 = 0 := by rw [hdist d d]; simp
        rw [← sum_erase_add _ _ hdB, hd0, add_zero]
        have h1 : ∀ i ∈ B.1.erase d, distEntry dist i.1 d.1 = 1 := by
          intro i hi
          obtain ⟨hid, hiB⟩ := mem_erase.mp hi
          have hαi_fin : eDom (αFin i) = ⟨a, ha⟩ := Fin.ext (hmemB i hiB)
          have hαi : (αFin i).1 = d := by
            rw [hd_eq, ← eDom.symm_apply_apply (αFin i), hαi_fin]
          rw [← hαi]
          exact hα_dist i fun hEq ↦ hid (hEq.trans hαi)
        rw [sum_congr rfl h1, sum_const, card_erase_of_mem hdB, nsmul_eq_mul, mul_one]
      rw [hsum_d]
      exact inf'_le (fun c : Fin N ↦ ∑ i ∈ B.1, distEntry dist i.1 c.1) hdB
    have hcast : ∑ B ∈ P.parts.attach, ((B.1.card - 1 : ℕ) : ℚ) = ((N - k : ℕ) : ℚ) := by
      exact_mod_cast hsum_parts
    exact (sum_le_sum hpart_le).trans_eq hcast

private def isTripleBool (S : List ℕ) : Bool :=
  (S.length == 3) && (S.getD 0 0 != S.getD 1 0) && (S.getD 0 0 != S.getD 2 0) &&
    (S.getD 1 0 != S.getD 2 0)

private lemma isTripleBool_eq_true_iff (S : List ℕ) :
    isTripleBool S = true ↔ S.length = 3 ∧ S.Nodup := by
  rcases S with _ | ⟨a, _ | ⟨b, _ | ⟨d, _ | ⟨e, t⟩⟩⟩⟩
  all_goals simp [isTripleBool, List.getD, List.nodup_cons, and_assoc, and_left_comm, and_comm]

/-- Fixed accepted `MetricKMedian` instance (`n = 1, k = 1, bound = 0`). -/
def yesInstance : MetricKMedianInstance :=
  ⟨1, [[0]], 1, 0⟩

private theorem yesInstance_mem : yesInstance ∈ MetricKMedian := by
  change IsMetricMatrix 1 [[0]] ∧
    ∃ P : Finpartition (univ : Finset (Fin 1)), P.parts.card = 1 ∧
      ∑ C ∈ P.parts.attach, C.1.inf' (P.nonempty_of_mem_parts C.2)
        (fun c ↦ ∑ i ∈ C.1, distEntry [[0]] i.1 c.1) ≤ 0
  refine ⟨?_, ?_⟩
  · refine ⟨fun i j ↦ ?_, fun i j ↦ ?_, fun i j ↦ ?_, fun i j l ↦ ?_⟩
    · fin_cases i; fin_cases j; simp [distEntry]
    · fin_cases i; fin_cases j; simp [distEntry]
    · fin_cases i; fin_cases j; simp [distEntry]
    · fin_cases i; fin_cases j; fin_cases l; simp [distEntry]
  · obtain ⟨P, hPparts⟩ : ∃ P : Finpartition (univ : Finset (Fin 1)), P.parts = {univ} :=
      ⟨Finpartition.indiscrete (univ_nonempty_iff.mpr inferInstance).ne_empty, rfl⟩
    refine ⟨P, by rw [hPparts, card_singleton], ?_⟩
    refine sum_nonpos fun C _ ↦ ?_
    obtain ⟨c₀, hc₀⟩ := P.nonempty_of_mem_parts C.2
    have h0 : ∑ i ∈ C.1, distEntry [[0]] i.1 c₀.1 = 0 :=
      sum_eq_zero fun i _ ↦ by fin_cases i; fin_cases c₀; rfl
    exact (inf'_le (fun c : Fin 1 ↦ ∑ i ∈ C.1, distEntry [[0]] i.1 c.1) hc₀).trans_eq h0

/-- Fixed rejected `MetricKMedian` instance (`n = 2` at distance `1`, `k = 1`, `bound = 0`). -/
def noInstance : MetricKMedianInstance :=
  ⟨2, [[0, 1], [1, 0]], 1, 0⟩

private theorem noInstance_notMem : noInstance ∉ MetricKMedian := by
  change ¬(IsMetricMatrix 2 [[0, 1], [1, 0]] ∧
    ∃ P : Finpartition (univ : Finset (Fin 2)), P.parts.card = 1 ∧
      ∑ C ∈ P.parts.attach, C.1.inf' (P.nonempty_of_mem_parts C.2)
        (fun c ↦ ∑ i ∈ C.1, distEntry [[0, 1], [1, 0]] i.1 c.1) ≤ 0)
  rintro ⟨_, P, hPcard, hcost⟩
  obtain ⟨C, hCP⟩ := card_eq_one.mp hPcard
  have hCuniv : C = (univ : Finset (Fin 2)) := by
    have hs := P.sup_parts
    rw [hCP, sup_singleton, id_eq] at hs
    exact hs
  have hU_mem : (univ : Finset (Fin 2)) ∈ P.parts := hCuniv ▸ (hCP ▸ mem_singleton_self C)
  have hle_sum := single_le_sum (f := fun B : P.parts ↦
      B.1.inf' (P.nonempty_of_mem_parts B.2)
        (fun c ↦ ∑ i ∈ B.1, distEntry [[0, 1], [1, 0]] i.1 c.1))
    (fun B _ ↦ by
      rw [le_inf'_iff]
      intro c _
      refine sum_nonneg fun i _ ↦ ?_
      fin_cases i <;> fin_cases c <;> norm_num [distEntry])
    (mem_attach P.parts ⟨univ, hU_mem⟩)
  have hinf1 : (1 : ℚ) ≤ (univ : Finset (Fin 2)).inf'
      (P.nonempty_of_mem_parts hU_mem)
      (fun c ↦ ∑ i ∈ (univ : Finset (Fin 2)), distEntry [[0, 1], [1, 0]] i.1 c.1) := by
    rw [le_inf'_iff]
    intro c _
    rw [Fin.sum_univ_two]
    fin_cases c <;> norm_num [distEntry]
  linarith

private def x3cRawAdj (C : List (List ℕ)) (U : List ℕ) (a b : ℕ) : Bool :=
  let r := C.length
  let u := U.length
  (decide (a = 0) && decide (b = 1)) ||
  (decide (a = 0) && decide (2 ≤ b) && decide (b < 2 + r)) ||
  (decide (2 ≤ a) && decide (a < 2 + r) && decide (2 + r ≤ b) && decide (b < 2 + r + u) &&
    decide (U.getD (b - (2 + r)) 0 ∈ C.getD (a - 2) []))

private def x3cAdj (C : List (List ℕ)) (U : List ℕ) (i j : ℕ) : Bool :=
  x3cRawAdj C U i j || x3cRawAdj C U j i

private def x3cDistMatrix (C : List (List ℕ)) (U : List ℕ) : List (List ℚ) :=
  let N := 2 + C.length + U.length
  (List.range N).map fun i ↦
    (List.range N).map fun j ↦
      if decide (i = j) then (0 : ℚ)
      else if x3cAdj C U i j then (1 : ℚ)
      else (2 : ℚ)

/-- Polynomial-time reduction from `ThreeExactCover` to `MetricKMedian`. -/
def fromThreeExactCover (C : List (List ℕ)) : MetricKMedianInstance :=
  let U := dedupNat C.flatten
  if !(C.all isTripleBool) then noInstance
  else if U.isEmpty then yesInstance
  else if !(decide (U.length % 3 = 0)) then noInstance
  else
    let m := U.length / 3
    let N := 2 + C.length + U.length
    ⟨N, x3cDistMatrix C U, m + 1, ((N - (m + 1) : ℕ) : ℚ)⟩

@[fun_prop]
private theorem computableInPolyTime_fromThreeExactCover :
    ComputableInPolyTime fromThreeExactCover (encList (encList encNat)) encMetricKMedian := by
  let EC := encList (encList encNat)
  have hU : ComputableInPolyTime (fun C : List (List ℕ) ↦ dedupNat C.flatten)
      EC (encList encNat) :=
    computableInPolyTime_dedupNat.comp (ComputableInPolyTime.flatten encNat)
  have hTriples : ComputableInPolyTime (fun C : List (List ℕ) ↦ !(C.all isTripleBool))
      EC encBool := by
    unfold isTripleBool
    fun_prop
  have hlenU_bin : ComputableInPolyTime
      (fun C : List (List ℕ) ↦ (dedupNat C.flatten).length) EC encNat :=
    unary_to_binary.comp ((length_list encNat).comp hU)
  have hMod : ComputableInPolyTime
      (fun C : List (List ℕ) ↦ !(decide ((dedupNat C.flatten).length % 3 = 0)))
      EC encBool :=
    bool_not.comp (decide_eq' (binary_mod' hlenU_bin (const 3)) (const 0))
  have hN : ComputableInPolyTime
      (fun C : List (List ℕ) ↦ 2 + C.length + (dedupNat C.flatten).length)
      EC encUnary := by fun_prop
  have hm : ComputableInPolyTime
      (fun C : List (List ℕ) ↦ (dedupNat C.flatten).length / 3 + 1) EC encNat :=
    binary_add' (binary_div' hlenU_bin (const 3)) (const 1)
  have hbound : ComputableInPolyTime
      (fun C : List (List ℕ) ↦
        (((2 + C.length + (dedupNat C.flatten).length) -
          ((dedupNat C.flatten).length / 3 + 1) : ℕ) : ℚ))
      EC encRat :=
    rat_natCast.comp (binary_sub' (unary_to_binary.comp hN) hm)
  have hraw : ∀ {γ : Type} {enc : γ ↪ List Bool} {fC : γ → List (List ℕ)}
      {fU : γ → List ℕ} {fa fb : γ → ℕ},
      ComputableInPolyTime fC enc EC →
      ComputableInPolyTime fU enc (encList encNat) →
      ComputableInPolyTime fa enc encUnary →
      ComputableInPolyTime fb enc encUnary →
      ComputableInPolyTime (fun z ↦ x3cRawAdj (fC z) (fU z) (fa z) (fb z)) enc encBool := by
    intro γ enc fC fU fa fb hfC hfU hfa hfb
    have ha_bin := unary_to_binary.comp hfa
    have hb_bin := unary_to_binary.comp hfb
    have hr_bin := unary_to_binary.comp ((length_list (encList encNat)).comp hfC)
    have hu_bin := unary_to_binary.comp ((length_list encNat).comp hfU)
    have h2r := binary_add' (const 2) hr_bin
    have h2ru := binary_add' h2r hu_bin
    have hmem : ComputableInPolyTime
        (fun z ↦ decide ((fU z).getD (fb z - (2 + (fC z).length)) 0 ∈
          (fC z).getD (fa z - 2) [])) enc encBool :=
      decide_mem
        (listGetD_binary (encA := encList encNat) ([] : List ℕ) hfC (binary_sub' ha_bin (const 2)))
        (listGetD_binary (encA := encNat) 0 hfU (binary_sub' hb_bin h2r))
    unfold x3cRawAdj
    dsimp only
    exact bool_or'
      (bool_or'
        (bool_and' (decide_eq' ha_bin (const 0)) (decide_eq' hb_bin (const 1)))
        (bool_and' (bool_and' (decide_eq' ha_bin (const 0)) (binary_le' (const 2) hb_bin))
          (binary_lt' hb_bin h2r)))
      (bool_and'
        (bool_and'
          (bool_and' (bool_and' (binary_le' (const 2) ha_bin) (binary_lt' ha_bin h2r))
            (binary_le' h2r hb_bin))
          (binary_lt' hb_bin h2ru))
        hmem)
  have hmat : ComputableInPolyTime
      (fun C : List (List ℕ) ↦ x3cDistMatrix C (dedupNat C.flatten))
      EC (encList (encList encRat)) := by
    unfold x3cDistMatrix
    apply mapWithInput (ComputableInPolyTime.range.comp hN)
    apply mapWithInput (ComputableInPolyTime.range.comp (hN.comp (fst EC encUnary)))
    have hfC : ComputableInPolyTime
        (fun q : (List (List ℕ) × ℕ) × ℕ ↦ q.1.1)
        (encPair (encPair EC encUnary) encUnary) EC :=
      (fst EC encUnary).comp (fst (encPair EC encUnary) encUnary)
    have hfU := hU.comp hfC
    have hfi : ComputableInPolyTime
        (fun q : (List (List ℕ) × ℕ) × ℕ ↦ q.1.2)
        (encPair (encPair EC encUnary) encUnary) encUnary :=
      (snd EC encUnary).comp (fst (encPair EC encUnary) encUnary)
    have hfj : ComputableInPolyTime
        (fun q : (List (List ℕ) × ℕ) × ℕ ↦ q.2)
        (encPair (encPair EC encUnary) encUnary) encUnary :=
      snd (encPair EC encUnary) encUnary
    unfold x3cAdj
    exact ite' (decide_eq' hfi hfj) (const (0 : ℚ))
      (ite' (bool_or' (hraw hfC hfU hfi hfj) (hraw hfC hfU hfj hfi))
        (const (1 : ℚ)) (const (2 : ℚ)))
  have hcore : ComputableInPolyTime
      (fun C : List (List ℕ) ↦
        (⟨2 + C.length + (dedupNat C.flatten).length,
          x3cDistMatrix C (dedupNat C.flatten),
          (dedupNat C.flatten).length / 3 + 1,
          (((2 + C.length + (dedupNat C.flatten).length) -
            ((dedupNat C.flatten).length / 3 + 1) : ℕ) : ℚ)⟩ : MetricKMedianInstance))
      EC encMetricKMedian :=
    encMetricKMedian_mk_polyTime hN hmat hm hbound
  unfold fromThreeExactCover
  exact ite' hTriples (const noInstance)
    (ite' ((listIsEmpty' encNat).comp hU) (const yesInstance)
      (ite' hMod (const noInstance) hcore))

private lemma x3cRawAdj_eq_true_iff (C : List (List ℕ)) (U : List ℕ) (a b : ℕ) :
    x3cRawAdj C U a b = true ↔
      (a = 0 ∧ b = 1) ∨
      (a = 0 ∧ 2 ≤ b ∧ b < 2 + C.length) ∨
      (2 ≤ a ∧ a < 2 + C.length ∧ 2 + C.length ≤ b ∧ b < 2 + C.length + U.length ∧
        U.getD (b - (2 + C.length)) 0 ∈ C.getD (a - 2) []) := by
  unfold x3cRawAdj
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, or_assoc, and_assoc]

private lemma x3cAdj_symm (C : List (List ℕ)) (U : List ℕ) (i j : ℕ) :
    x3cAdj C U i j = x3cAdj C U j i := by
  unfold x3cAdj
  exact Bool.or_comm _ _

private lemma distEntry_x3cDistMatrix (C : List (List ℕ)) (U : List ℕ) {i j : ℕ}
    (hi : i < 2 + C.length + U.length) (hj : j < 2 + C.length + U.length) :
    distEntry (x3cDistMatrix C U) i j =
      if i = j then 0 else if x3cAdj C U i j = true then 1 else 2 := by
  unfold distEntry x3cDistMatrix
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi,
    Option.map_some, Option.getD_some, List.getElem?_range hj]
  by_cases hij : i = j <;> simp [hij]

private lemma isMetricMatrix_x3cDistMatrix (C : List (List ℕ)) (U : List ℕ) :
    IsMetricMatrix (2 + C.length + U.length) (x3cDistMatrix C U) := by
  refine ⟨fun i j ↦ ?_, fun i j ↦ ?_, fun i j ↦ ?_, fun i j l ↦ ?_⟩
  · rw [distEntry_x3cDistMatrix C U i.2 j.2]
    split_ifs <;> norm_num
  · rw [distEntry_x3cDistMatrix C U i.2 j.2]
    split_ifs with h1
    · exact ⟨fun _ ↦ Fin.ext h1, fun _ ↦ rfl⟩
    · exact ⟨fun h ↦ by norm_num at h, fun h ↦ (h1 (congrArg Fin.val h)).elim⟩
    · exact ⟨fun h ↦ by norm_num at h, fun h ↦ (h1 (congrArg Fin.val h)).elim⟩
  · rw [distEntry_x3cDistMatrix C U i.2 j.2, distEntry_x3cDistMatrix C U j.2 i.2]
    by_cases hij : i.1 = j.1
    · simp [hij]
    · have hji : j.1 ≠ i.1 := Ne.symm hij
      simp [hij, hji, x3cAdj_symm]
  · by_cases hil : i = l
    · subst hil
      rw [distEntry_x3cDistMatrix C U i.2 i.2]
      simp only [↓reduceIte]
      have h1 : 0 ≤ distEntry (x3cDistMatrix C U) i.1 j.1 := by
        rw [distEntry_x3cDistMatrix C U i.2 j.2]; split_ifs <;> norm_num
      have h2 : 0 ≤ distEntry (x3cDistMatrix C U) j.1 i.1 := by
        rw [distEntry_x3cDistMatrix C U j.2 i.2]; split_ifs <;> norm_num
      linarith
    by_cases hij : i = j
    · subst hij
      rw [distEntry_x3cDistMatrix C U i.2 i.2]
      simp only [↓reduceIte, zero_add, le_refl]
    by_cases hjl : j = l
    · subst hjl
      rw [distEntry_x3cDistMatrix C U j.2 j.2]
      simp only [↓reduceIte, add_zero, le_refl]
    have hil' : i.1 ≠ l.1 := Fin.val_ne_of_ne hil
    have hij' : i.1 ≠ j.1 := Fin.val_ne_of_ne hij
    have hjl' : j.1 ≠ l.1 := Fin.val_ne_of_ne hjl
    have hle2 : distEntry (x3cDistMatrix C U) i.1 l.1 ≤ 2 := by
      rw [distEntry_x3cDistMatrix C U i.2 l.2]; split_ifs <;> norm_num
    have hge1_a : 1 ≤ distEntry (x3cDistMatrix C U) i.1 j.1 := by
      rw [distEntry_x3cDistMatrix C U i.2 j.2]
      simp only [hij', ↓reduceIte]
      split_ifs <;> norm_num
    have hge1_b : 1 ≤ distEntry (x3cDistMatrix C U) j.1 l.1 := by
      rw [distEntry_x3cDistMatrix C U j.2 l.2]
      simp only [hjl', ↓reduceIte]
      split_ifs <;> norm_num
    linarith

private theorem exactCover_card_mul_three {C : List (List ℕ)} {D : Finset (List ℕ)}
    (htrip : ∀ S ∈ C, S.length = 3 ∧ S.Nodup) (hEC : IsExactCover C D) :
    3 * D.card = (dedupNat C.flatten).length := by
  let U := (dedupNat C.flatten).toFinset
  have hUcard : U.card = (dedupNat C.flatten).length :=
    List.toFinset_card_of_nodup (nodup_dedupNat C.flatten)
  rw [← hUcard]
  have hbi : D.biUnion List.toFinset = U := by
    ext u
    simp only [mem_biUnion, List.mem_toFinset, U, mem_dedupNat]
    constructor
    · rintro ⟨S, hSD, huS⟩
      exact List.mem_flatten.mpr ⟨S, hEC.1 S hSD, huS⟩
    · intro hu
      have h1 := hEC.2 u hu
      obtain ⟨S, hS⟩ := card_pos.mp (by omega : 0 < (D.filter (u ∈ ·)).card)
      exact ⟨S, (mem_filter.mp hS).1, (mem_filter.mp hS).2⟩
  have hpw : (D : Set (List ℕ)).PairwiseDisjoint List.toFinset := by
    intro S₁ hS₁ S₂ hS₂ hne
    refine Finset.disjoint_left.mpr fun u hu1 hu2 ↦ hne ?_
    rw [List.mem_toFinset] at hu1 hu2
    have hu : u ∈ C.flatten := List.mem_flatten.mpr ⟨S₁, hEC.1 S₁ hS₁, hu1⟩
    obtain ⟨T, hT⟩ := card_eq_one.mp (hEC.2 u hu)
    have h1 : S₁ ∈ ({T} : Finset (List ℕ)) := hT ▸ mem_filter.mpr ⟨hS₁, hu1⟩
    have h2 : S₂ ∈ ({T} : Finset (List ℕ)) := hT ▸ mem_filter.mpr ⟨hS₂, hu2⟩
    rw [mem_singleton.mp h1, mem_singleton.mp h2]
  rw [← hbi, card_biUnion hpw]
  have h3 : ∀ S ∈ D, S.toFinset.card = 3 := fun S hSD ↦ by
    obtain ⟨hlen, hnd⟩ := htrip S (hEC.1 S hSD)
    rw [List.toFinset_card_of_nodup hnd, hlen]
  rw [sum_congr rfl h3]
  simp [Nat.mul_comm]

theorem fromThreeExactCover_mem_iff (C : List (List ℕ)) :
    fromThreeExactCover C ∈ MetricKMedian ↔ C ∈ ThreeExactCover := by
  unfold fromThreeExactCover
  set U := dedupNat C.flatten
  by_cases hA' : C.all isTripleBool = true
  · have htrip : ∀ S ∈ C, S.length = 3 ∧ S.Nodup :=
      fun S hS ↦ (isTripleBool_eq_true_iff S).mp (List.all_eq_true.mp hA' S hS)
    simp only [hA', Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    by_cases hemp : U.isEmpty = true
    · simp only [hemp, ↓reduceIte]
      have hCnil : C = [] := by
        by_contra hne
        obtain ⟨S, hSC⟩ := List.exists_mem_of_ne_nil C hne
        obtain ⟨hlen, _⟩ := htrip S hSC
        have hSne : S ≠ [] := fun h ↦ by simp [h] at hlen
        obtain ⟨u, huS⟩ := List.exists_mem_of_ne_nil S hSne
        have huU : u ∈ U := mem_dedupNat.mpr (List.mem_flatten.mpr ⟨S, hSC, huS⟩)
        rw [List.isEmpty_iff] at hemp
        simp [hemp] at huU
      exact ⟨fun _ ↦ ⟨htrip, ∅, by simp [hCnil, IsExactCover]⟩, fun _ ↦ yesInstance_mem⟩
    · simp only [hemp, Bool.false_eq_true, ↓reduceIte]
      by_cases hmod : U.length % 3 = 0
      · simp only [decide_eq_true hmod, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        set m := U.length / 3
        have hUm : U.length = 3 * m := (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hmod)).symm
        set r := C.length
        set N := 2 + r + U.length
        set k := m + 1
        have hdist_fn : ∀ i j : Fin N,
            distEntry (x3cDistMatrix C U) i.1 j.1 =
              if i.1 = j.1 then 0 else if x3cAdj C U i.1 j.1 = true then 1 else 2 :=
          fun i j ↦ distEntry_x3cDistMatrix C U i.2 j.2
        constructor
        · rintro ⟨_, P, hPcard, hcost⟩
          obtain ⟨Dom, hDom_card, hdom_all⟩ :=
            exists_dominating_of_kMedian_le hdist_fn hPcard hcost
          refine ⟨htrip, ?_⟩
          let h0 : Fin N := ⟨0, by omega⟩
          let p1 : Fin N := ⟨1, by omega⟩
          have hp1_dom : h0 ∈ Dom ∨ p1 ∈ Dom := by
            rcases hdom_all p1 with hp | ⟨d, hd, hadj⟩
            · exact Or.inr hp
            · have hd0 : d.1 = 0 := by
                have hp1_val : p1.1 = 1 := rfl
                unfold x3cAdj at hadj
                rw [Bool.or_eq_true, x3cRawAdj_eq_true_iff, x3cRawAdj_eq_true_iff] at hadj
                rcases hadj with (⟨h1, _⟩ | ⟨h1, _, _⟩ | ⟨h1, _, _, _, _⟩) |
                  (⟨h1, _⟩ | ⟨_, h1, _⟩ | ⟨_, _, h1, _, _⟩) <;> omega
              have hd_eq : d = h0 := Fin.ext hd0
              exact Or.inl (hd_eq ▸ hd)
          let Dom' : Finset (Fin N) := (Dom.erase h0).erase p1
          have hDom'_le : Dom'.card ≤ m := by
            have hDom_m : Dom.card = m + 1 := hDom_card
            have hp1_ne_h0 : p1 ≠ h0 := fun h ↦ by
              have := congrArg Fin.val h; dsimp [p1, h0] at this; omega
            dsimp [Dom']
            rcases hp1_dom with hh0 | hp1
            · have := card_erase_add_one hh0
              have := card_erase_le (s := Dom.erase h0) (a := p1)
              omega
            · have hp1' : p1 ∈ Dom.erase h0 := mem_erase.mpr ⟨hp1_ne_h0, hp1⟩
              have := card_erase_add_one hp1'
              have := card_erase_le (s := Dom) (a := h0)
              omega
          let elemSet (w : Fin N) : Finset (Fin U.length) :=
            univ.filter fun t ↦
              w.1 = 2 + r + t.1 ∨ x3cAdj C U (2 + r + t.1) w.1 = true
          have hcover_U : (univ : Finset (Fin U.length)) ⊆ Dom'.biUnion elemSet := by
            intro t _
            rw [mem_biUnion]
            let xt : Fin N := ⟨2 + r + t.1, by omega⟩
            rcases hdom_all xt with hxt | ⟨d, hd, hadj⟩
            · refine ⟨xt, mem_erase.mpr ⟨?_, mem_erase.mpr ⟨?_, hxt⟩⟩, ?_⟩
              · intro h; have := congrArg Fin.val h; dsimp [xt, p1] at this; omega
              · intro h; have := congrArg Fin.val h; dsimp [xt, h0] at this; omega
              · simp [elemSet, xt]
            · have hd_ge2 : 2 ≤ d.1 := by
                have hxt_val : xt.1 = 2 + r + t.1 := rfl
                unfold x3cAdj at hadj
                rw [Bool.or_eq_true, x3cRawAdj_eq_true_iff, x3cRawAdj_eq_true_iff] at hadj
                rcases hadj with (⟨h1, _⟩ | ⟨h1, _, _⟩ | ⟨_, h1, _, _, _⟩) |
                  (⟨_, h1⟩ | ⟨_, _, h1⟩ | ⟨h1, _, _, _, _⟩) <;> omega
              refine ⟨d, mem_erase.mpr ⟨?_, mem_erase.mpr ⟨?_, hd⟩⟩, ?_⟩
              · intro h; have := congrArg Fin.val h; dsimp [p1] at this; omega
              · intro h; have := congrArg Fin.val h; dsimp [h0] at this; omega
              · simp [elemSet, xt, hadj]
          have hcard_elemSet : ∀ w ∈ Dom', (elemSet w).card ≤ 3 ∧
              ((elemSet w).card = 3 → 2 ≤ w.1 ∧ w.1 < 2 + r) := by
            intro w hw
            have hw2 : 2 ≤ w.1 := by
              have hne1 : w ≠ p1 := (mem_erase.mp hw).1
              have hne0 : w ≠ h0 := (mem_erase.mp (mem_erase.mp hw).2).1
              have : w.1 ≠ 1 := fun h ↦ hne1 (Fin.ext h)
              have : w.1 ≠ 0 := fun h ↦ hne0 (Fin.ext h)
              omega
            by_cases hwr : w.1 < 2 + r
            · refine ⟨?_, fun _ ↦ ⟨hw2, hwr⟩⟩
              let S_w := C.getD (w.1 - 2) []
              have hSw_mem : S_w ∈ C := List.getD_mem [] (by omega : w.1 - 2 < C.length)
              obtain ⟨hSw_len, hSw_nd⟩ := htrip S_w hSw_mem
              have hsub : (elemSet w).image (fun t : Fin U.length ↦ U.getD t.1 0) ⊆
                  S_w.toFinset := by
                intro u hu
                obtain ⟨t, ht, rfl⟩ := mem_image.mp hu
                simp only [elemSet, mem_filter, mem_univ, true_and] at ht
                rcases ht with hEq | hadj
                · omega
                · unfold x3cAdj at hadj
                  rw [Bool.or_eq_true, x3cRawAdj_eq_true_iff, x3cRawAdj_eq_true_iff] at hadj
                  rcases hadj with (⟨h1, _⟩ | ⟨h1, _, _⟩ | ⟨_, h2, _, _, _⟩) |
                    (⟨_, h2⟩ | ⟨_, _, h2⟩ | ⟨_, _, _, _, hmem⟩)
                  · omega
                  · omega
                  · omega
                  · omega
                  · omega
                  · rw [Nat.add_sub_cancel_left] at hmem
                    exact List.mem_toFinset.mpr hmem
              have hinj_U : Set.InjOn (fun t : Fin U.length ↦ U.getD t.1 0)
                  (elemSet w : Set (Fin U.length)) := by
                intro t₁ _ t₂ _ hEq
                apply Fin.ext
                exact (nodup_dedupNat C.flatten).getElem_inj_iff.mp
                  (by simpa [List.getD_eq_getElem?_getD, t₁.2, t₂.2] using hEq)
              calc
                (elemSet w).card =
                    ((elemSet w).image fun t : Fin U.length ↦ U.getD t.1 0).card :=
                  (card_image_of_injOn hinj_U).symm
                _ ≤ S_w.toFinset.card := card_le_card hsub
                _ = 3 := by rw [List.toFinset_card_of_nodup hSw_nd, hSw_len]
            · have hsingle : elemSet w = {⟨w.1 - (2 + r), by omega⟩} := by
                ext t
                simp only [elemSet, mem_filter, mem_univ, true_and, mem_singleton, Fin.ext_iff]
                constructor
                · rintro (hEq | hadj)
                  · omega
                  · unfold x3cAdj at hadj
                    rw [Bool.or_eq_true, x3cRawAdj_eq_true_iff, x3cRawAdj_eq_true_iff] at hadj
                    rcases hadj with (⟨h1, _⟩ | ⟨h1, _, _⟩ | ⟨_, h2, _, _, _⟩) |
                      (⟨h1, _⟩ | ⟨h1, _, _⟩ | ⟨_, h2, _, _, _⟩) <;> omega
                · intro hEq
                  left; omega
              rw [hsingle, card_singleton]
              exact ⟨by decide, fun h ↦ by omega⟩
          have hsum_3m : 3 * m ≤ ∑ w ∈ Dom', (elemSet w).card := by
            calc
              3 * m = (univ : Finset (Fin U.length)).card := by simp [Fintype.card_fin, hUm]
              _ ≤ (Dom'.biUnion elemSet).card := card_le_card hcover_U
              _ ≤ ∑ w ∈ Dom', (elemSet w).card := card_biUnion_le
          have hsum_ub_dom : ∑ w ∈ Dom', (elemSet w).card ≤ Dom'.card * 3 := by
            calc
              ∑ w ∈ Dom', (elemSet w).card ≤ ∑ _w ∈ Dom', 3 :=
                sum_le_sum fun w hw ↦ (hcard_elemSet w hw).1
              _ = Dom'.card * 3 := by simp
          have hDom'_eq : Dom'.card = m := by
            have := hsum_3m.trans hsum_ub_dom
            omega
          have hsum_eq3 : ∑ w ∈ Dom', (elemSet w).card = ∑ _w ∈ Dom', 3 := by
            apply le_antisymm (sum_le_sum fun w hw ↦ (hcard_elemSet w hw).1)
            simpa [hDom'_eq, Nat.mul_comm] using hsum_3m
          have hall3 : ∀ w ∈ Dom', (elemSet w).card = 3 := fun w hw ↦
            (sum_eq_sum_iff_of_le (fun z hz ↦ (hcard_elemSet z hz).1)).mp hsum_eq3 w hw
          have hall_triple : ∀ w ∈ Dom', 2 ≤ w.1 ∧ w.1 < 2 + r :=
            fun w hw ↦ (hcard_elemSet w hw).2 (hall3 w hw)
          have hbi_eq : (Dom'.biUnion elemSet).card = ∑ w ∈ Dom', (elemSet w).card := by
            apply le_antisymm card_biUnion_le
            calc
              ∑ w ∈ Dom', (elemSet w).card = 3 * m := by
                rw [hsum_eq3, sum_const, smul_eq_mul, hDom'_eq, Nat.mul_comm]
              _ = (univ : Finset (Fin U.length)).card := by simp [Fintype.card_fin, hUm]
              _ ≤ (Dom'.biUnion elemSet).card := card_le_card hcover_U
          have hpw_disj : (Dom' : Set (Fin N)).PairwiseDisjoint elemSet := by
            intro w₁ hw₁ w₂ hw₂ hne
            refine Finset.disjoint_left.mpr fun t ht1 ht2 ↦ ?_
            have hsub_union :
                Dom'.biUnion elemSet ⊆
                  (Dom'.erase w₁).biUnion elemSet ∪ (elemSet w₁).erase t := by
              intro s hs
              obtain ⟨w, hw, hsw⟩ := mem_biUnion.mp hs
              by_cases hww₁ : w = w₁
              · subst hww₁
                by_cases hst : s = t
                · subst hst
                  exact mem_union_left _
                    (mem_biUnion.mpr ⟨w₂, mem_erase.mpr ⟨hne.symm, hw₂⟩, ht2⟩)
                · exact mem_union_right _ (mem_erase.mpr ⟨hst, hsw⟩)
              · exact mem_union_left _ (mem_biUnion.mpr ⟨w, mem_erase.mpr ⟨hww₁, hw⟩, hsw⟩)
            have hlt : (Dom'.biUnion elemSet).card < ∑ w ∈ Dom', (elemSet w).card := by
              have hadd := sum_erase_add Dom' (fun w ↦ (elemSet w).card) hw₁
              have hcard_er := card_erase_add_one ht1
              calc
                (Dom'.biUnion elemSet).card ≤
                    ((Dom'.erase w₁).biUnion elemSet ∪ (elemSet w₁).erase t).card :=
                  card_le_card hsub_union
                _ ≤ ((Dom'.erase w₁).biUnion elemSet).card + ((elemSet w₁).erase t).card :=
                  card_union_le _ _
                _ ≤ (∑ w ∈ Dom'.erase w₁, (elemSet w).card) + ((elemSet w₁).erase t).card :=
                  Nat.add_le_add_right card_biUnion_le _
                _ < ∑ w ∈ Dom', (elemSet w).card := by omega
            exact (hlt.ne hbi_eq).elim
          let D : Finset (List ℕ) := Dom'.image fun w ↦ C.getD (w.1 - 2) []
          refine ⟨D, fun S hS ↦ ?_, fun u hu ↦ ?_⟩
          · obtain ⟨w, hw, rfl⟩ := mem_image.mp hS
            obtain ⟨_, hw_hi⟩ := hall_triple w hw
            exact List.getD_mem [] (by omega)
          · have huU : u ∈ U := mem_dedupNat.mpr hu
            obtain ⟨t_nat, ht_lt, rfl⟩ := List.getElem_of_mem huU
            let t : Fin U.length := ⟨t_nat, ht_lt⟩
            obtain ⟨w, hw, htw⟩ := mem_biUnion.mp (hcover_U (mem_univ t))
            obtain ⟨hw_lo, hw_hi⟩ := hall_triple w hw
            have hmem_Sw : U[t_nat] ∈ C.getD (w.1 - 2) [] := by
              simp only [elemSet, mem_filter, mem_univ, true_and] at htw
              rcases htw with hEq | hadj
              · omega
              · unfold x3cAdj at hadj
                rw [Bool.or_eq_true, x3cRawAdj_eq_true_iff, x3cRawAdj_eq_true_iff] at hadj
                rcases hadj with (⟨h1, _⟩ | ⟨h1, _, _⟩ | ⟨_, h2, _, _, _⟩) |
                  (⟨_, h2⟩ | ⟨_, _, h2⟩ | ⟨_, _, _, _, hmem⟩)
                · omega
                · omega
                · omega
                · omega
                · omega
                · rw [Nat.add_sub_cancel_left] at hmem
                  simpa [List.getD_eq_getElem?_getD, ht_lt] using hmem
            have hfilter_eq : D.filter (U[t_nat] ∈ ·) = {C.getD (w.1 - 2) []} := by
              ext S
              simp only [mem_filter, mem_singleton]
              constructor
              · rintro ⟨hSD, huS⟩
                obtain ⟨w', hw', rfl⟩ := mem_image.mp hSD
                obtain ⟨hw'_lo, hw'_hi⟩ := hall_triple w' hw'
                have htw' : t ∈ elemSet w' := by
                  simp only [elemSet, mem_filter, mem_univ, true_and]
                  right
                  unfold x3cAdj
                  rw [Bool.or_eq_true, x3cRawAdj_eq_true_iff, x3cRawAdj_eq_true_iff]
                  right
                  refine Or.inr (Or.inr ⟨hw'_lo, hw'_hi, by omega, by omega, ?_⟩)
                  rw [Nat.add_sub_cancel_left]
                  simpa [List.getD_eq_getElem?_getD, ht_lt] using huS
                have hweq : w' = w := by
                  by_contra hne
                  exact Finset.disjoint_left.mp (hpw_disj hw' hw hne) htw' htw
                rw [hweq]
              · rintro rfl
                exact ⟨mem_image_of_mem _ hw, hmem_Sw⟩
            rw [hfilter_eq, card_singleton]
        · rintro ⟨_, D, hEC⟩
          have h3D : 3 * D.card = 3 * m := (exactCover_card_mul_three htrip hEC).trans hUm
          have hDcard : D.card = m := by omega
          refine ⟨isMetricMatrix_x3cDistMatrix C U, ?_⟩
          have hj_of_mem : ∀ S ∈ D, ∃ j < r, C.getD j [] = S := fun S hSD ↦ by
            obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem (hEC.1 S hSD)
            exact ⟨j, hj, by simp [List.getD_eq_getElem?_getD, hj]⟩
          choose jOf hjOf_lt hjOf_eq using hj_of_mem
          have hjOf_inj : ∀ (S₁ S₂ : D), jOf S₁.1 S₁.2 = jOf S₂.1 S₂.2 → S₁ = S₂ := by
            intro S₁ S₂ hEq
            apply Subtype.ext
            rw [← hjOf_eq S₁.1 S₁.2, ← hjOf_eq S₂.1 S₂.2, hEq]
          let Dom : Finset (Fin N) :=
            insert ⟨0, by omega⟩ (D.attach.image fun S ↦ ⟨2 + jOf S.1 S.2, by
              have := hjOf_lt S.1 S.2; omega⟩)
          have hDom_card : Dom.card = k := by
            rw [card_insert_of_notMem (fun h ↦ by
              obtain ⟨S, _, hEq⟩ := mem_image.mp h
              have := congrArg Fin.val hEq
              dsimp at this; omega)]
            rw [card_image_of_injective _ fun S₁ S₂ hEq ↦ hjOf_inj S₁ S₂ (by
              have := congrArg Fin.val hEq; dsimp at this; omega)]
            rw [card_attach, hDcard]
          have hdom_all : ∀ v : Fin N, ∃ d ∈ Dom, v = d ∨ x3cAdj C U v.1 d.1 = true := by
            intro v
            by_cases hv0 : v.1 = 0
            · exact ⟨⟨0, by omega⟩, mem_insert_self _ _, Or.inl (Fin.ext hv0)⟩
            by_cases hv1 : v.1 = 1
            · refine ⟨⟨0, by omega⟩, mem_insert_self _ _, Or.inr ?_⟩
              unfold x3cAdj
              rw [Bool.or_eq_true, x3cRawAdj_eq_true_iff, x3cRawAdj_eq_true_iff]
              exact Or.inr (Or.inl ⟨rfl, hv1⟩)
            by_cases hvr : v.1 < 2 + r
            · refine ⟨⟨0, by omega⟩, mem_insert_self _ _, Or.inr ?_⟩
              unfold x3cAdj
              rw [Bool.or_eq_true, x3cRawAdj_eq_true_iff, x3cRawAdj_eq_true_iff]
              exact Or.inr (Or.inr (Or.inl ⟨rfl, by omega, hvr⟩))
            · let t_nat := v.1 - (2 + r)
              have ht_lt : t_nat < U.length := by omega
              have hu_mem : U[t_nat] ∈ C.flatten :=
                mem_dedupNat.mp (List.getElem_mem ht_lt)
              obtain ⟨S, hS⟩ := card_pos.mp (by rw [hEC.2 U[t_nat] hu_mem]; decide)
              obtain ⟨hSD, huS⟩ := mem_filter.mp hS
              let dS : Fin N := ⟨2 + jOf S hSD, by have := hjOf_lt S hSD; omega⟩
              have hdS_mem : dS ∈ Dom :=
                mem_insert_of_mem (mem_image_of_mem _ (mem_attach _ ⟨S, hSD⟩))
              refine ⟨dS, hdS_mem, Or.inr ?_⟩
              unfold x3cAdj
              rw [Bool.or_eq_true, x3cRawAdj_eq_true_iff, x3cRawAdj_eq_true_iff]
              have hjl := hjOf_lt S hSD
              right; right; right
              refine ⟨by dsimp [dS]; omega, by dsimp [dS]; omega, by omega, v.2, ?_⟩
              dsimp [dS]
              rw [Nat.add_sub_cancel_left, hjOf_eq S hSD]
              have hsub : v.1 - (2 + r) = t_nat := rfl
              rw [hsub]
              simpa [List.getD_eq_getElem?_getD, ht_lt] using huS
          exact exists_kMedian_le_of_dominating hdist_fn hDom_card hdom_all
      · simp only [decide_eq_false hmod, Bool.not_false, ↓reduceIte]
        refine ⟨fun h ↦ (noInstance_notMem h).elim, fun ⟨_, D, hEC⟩ ↦ ?_⟩
        have h3 : U.length = 3 * D.card := (exactCover_card_mul_three htrip hEC).symm
        have hrem : U.length % 3 = 0 := by rw [h3]; simp
        exact (hmod hrem).elim
  · have hA_false : C.all isTripleBool = false := Bool.eq_false_iff.mpr hA'
    simp only [hA_false, Bool.not_false, ↓reduceIte]
    refine ⟨fun h ↦ (noInstance_notMem h).elim, fun ⟨ht, _⟩ ↦ ?_⟩
    exact (hA' (List.all_eq_true.mpr fun S hS ↦ (isTripleBool_eq_true_iff S).mpr (ht S hS))).elim

end MetricKMedian

/-- `ThreeExactCover` reduces in polynomial time to `MetricKMedian`. -/
theorem polyTimeReducible_ThreeExactCover_MetricKMedian :
    PolyTimeReducible (encList (encList encNat)) encMetricKMedian
      ThreeExactCover MetricKMedian :=
  ⟨MetricKMedian.fromThreeExactCover, MetricKMedian.computableInPolyTime_fromThreeExactCover,
    fun C ↦ (MetricKMedian.fromThreeExactCover_mem_iff C).symm⟩

/-- `MetricKMedian` is `NP`-hard. -/
theorem MetricKMedian_npHard : NPHard encMetricKMedian MetricKMedian :=
  ThreeExactCover_npHard.trans polyTimeReducible_ThreeExactCover_MetricKMedian

/-- **Discrete Metric `k`-Median is `NP`-complete.** -/
theorem MetricKMedian_npComplete : NPComplete encMetricKMedian MetricKMedian :=
  ⟨MetricKMedian.mem_NP, MetricKMedian_npHard⟩

end CslibFrontier.Computability.Complexity
