module

public import CslibFrontier.Computability.Complexity.Problems.ThreeDimensionalMatching
public import CslibFrontier.Computability.Complexity.Classes.NP.Witness
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Length
import Mathlib.Data.List.GetD
import Mathlib.Data.List.OfFn
import Mathlib.Tactic.Linarith

/-!
# Three-Partition

An instance of *3-Partition* (`ThreePartition`) consists of item sizes `numbers`, group count
`numGroups`, and target sum `target`, satisfying `0 < numGroups`, `numbers.length = 3 * numGroups`,
`numbers.sum = numGroups * target`, and `target < 4 * s ∧ 2 * s < target` for all `s ∈ numbers`
(`ThreePartitionInstance.Valid`). It is a yes-instance when the items partition into `numGroups`
groups summing to `target`, which automatically forces every group to have size 3
(`fiber_card_eq_three`). We prove strong NP-completeness under `encThreePartitionUnary`
(`ThreePartition_npComplete_unary`) via a carry-free four-level base reduction from `ThreeDM`,
and binary NP-completeness under `encThreePartition` (`ThreePartition_npComplete`).

## Main definitions

* `Cslib.Complexity.ThreePartitionInstance`, `Cslib.Complexity.encThreePartitionUnary`,
  `Cslib.Complexity.encThreePartition`: instances with unary and binary encodings.
* `Cslib.Complexity.ThreePartitionInstance.Valid`, `Cslib.Complexity.IsThreePartition`,
  `Cslib.Complexity.ThreePartition`: validity, partition predicate, and decision problem.
* `Cslib.Complexity.ThreePartition.toThreePartition`: unary polynomial-time reduction.

## Main results

* `Cslib.Complexity.fiber_card_eq_three`: every group in a valid 3-partition has size 3.
* `Cslib.Complexity.ThreePartition_mem_NP`, `Cslib.Complexity.ThreePartition_mem_NP_unary`:
  membership in NP under binary and unary encodings.
* `Cslib.Complexity.ThreePartition.computableInPolyTime_toThreePartition_unary`,
  `Cslib.Complexity.ThreePartition.toThreePartition_mem_iff`: computability and correctness.
* `Cslib.Complexity.polyTimeReducible_ThreeDM_ThreePartition_unary`,
  `Cslib.Complexity.ThreePartition_npHard_unary`,
  `Cslib.Complexity.ThreePartition_npComplete_unary`: strong NP-completeness.
* `Cslib.Complexity.ThreePartition_npHard`, `Cslib.Complexity.ThreePartition_npComplete`:
  binary NP-completeness.
-/

public section

namespace Cslib.Complexity

open Cslib.Complexity Turing.MultiTapeTM ComputableInPolyTime

/-- An instance of 3-Partition: a list of item sizes `numbers`, a number of groups `numGroups`,
and a common group target sum `target`. -/
@[ext]
structure ThreePartitionInstance where
  /-- The list of item sizes. -/
  numbers : List ℕ
  /-- The number of groups into which the items are partitioned. -/
  numGroups : ℕ
  /-- The target sum for each group. -/
  target : ℕ
  deriving DecidableEq, Repr

/-- Unary encoding of a `ThreePartitionInstance` (every number, `numGroups`, and `target` in
unary), used for strong NP-completeness. -/
enc_structure encThreePartitionUnary : ThreePartitionInstance where
  numbers : (encList encUnary),
  numGroups : encUnary,
  target : encUnary

/-- Binary encoding of a `ThreePartitionInstance` (every number, `numGroups`, and `target` in
binary). -/
enc_structure encThreePartition : ThreePartitionInstance where
  numbers : (encList encNat),
  numGroups : encNat,
  target : encNat

/-- Standard validity conditions for a 3-Partition instance: positive group count,
`3 * numGroups` items, total sum `numGroups * target`, and every item strictly between
`target / 4` and `target / 2`. -/
structure ThreePartitionInstance.Valid (inst : ThreePartitionInstance) : Prop where
  /-- There is at least one group. -/
  numGroups_pos : 0 < inst.numGroups
  /-- There are `3 * numGroups` items. -/
  length_eq : inst.numbers.length = 3 * inst.numGroups
  /-- The items sum to `numGroups * target`. -/
  sum_eq : inst.numbers.sum = inst.numGroups * inst.target
  /-- Every item lies strictly between `target / 4` and `target / 2`. -/
  bounds : ∀ s ∈ inst.numbers, inst.target < 4 * s ∧ 2 * s < inst.target

/-- Characterization of `ThreePartitionInstance.Valid`. -/
theorem ThreePartitionInstance.valid_iff {inst : ThreePartitionInstance} :
    inst.Valid ↔
      0 < inst.numGroups ∧
      inst.numbers.length = 3 * inst.numGroups ∧
      inst.numbers.sum = inst.numGroups * inst.target ∧
      ∀ s ∈ inst.numbers, inst.target < 4 * s ∧ 2 * s < inst.target :=
  ⟨fun ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, h3, h4⟩, fun ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, h3, h4⟩⟩

/-- An assignment `assign : Fin inst.numbers.length → Fin inst.numGroups` is a valid 3-partition
if each group sums to `inst.target`. -/
def IsThreePartition (inst : ThreePartitionInstance)
    (assign : Fin inst.numbers.length → Fin inst.numGroups) : Prop :=
  ∀ j : Fin inst.numGroups,
    (Finset.univ.filter fun i => assign i = j).sum (fun i => inst.numbers[i]) = inst.target

/-- Characterization of `IsThreePartition`. -/
theorem isThreePartition_iff {inst : ThreePartitionInstance}
    {assign : Fin inst.numbers.length → Fin inst.numGroups} :
    IsThreePartition inst assign ↔
      ∀ j : Fin inst.numGroups,
        (Finset.univ.filter fun i => assign i = j).sum (fun i => inst.numbers[i]) =
          inst.target :=
  Iff.rfl

private theorem finset_sum_lt_sum {α : Type*} {s : Finset α} {f g : α → ℕ}
    (hs : s.Nonempty) (h : ∀ a ∈ s, f a < g a) : ∑ a ∈ s, f a < ∑ a ∈ s, g a := by
  classical
  induction s using Finset.induction_on with
  | empty => simp at hs
  | @insert x t hx ih =>
    rw [Finset.sum_insert hx, Finset.sum_insert hx]; have hfx := h x (Finset.mem_insert_self x t)
    rcases t.eq_empty_or_nonempty with rfl | ht
    · simp only [Finset.sum_empty, Nat.add_zero]; exact hfx
    · have := ih ht (fun a ha => h a (Finset.mem_insert_of_mem ha)); omega

private theorem card_eq_three_of_sum_bounds {α : Type*} {F : Finset α} {f : α → ℕ} {T : ℕ}
    (hT : 0 < T) (hsum : ∑ x ∈ F, f x = T) (hb : ∀ x ∈ F, T < 4 * f x ∧ 2 * f x < T) :
    F.card = 3 := by
  have hFne : F.Nonempty := by
    by_contra hne; rw [Finset.not_nonempty_iff_eq_empty] at hne
    rw [hne, Finset.sum_empty] at hsum; omega
  have hlt1 : ∑ x ∈ F, 2 * f x < ∑ _x ∈ F, T := finset_sum_lt_sum hFne fun x hx => (hb x hx).2
  have hlt2 : ∑ _x ∈ F, T < ∑ x ∈ F, 4 * f x := finset_sum_lt_sum hFne fun x hx => (hb x hx).1
  rw [← Finset.mul_sum, hsum, Finset.sum_const, smul_eq_mul] at hlt1
  rw [Finset.sum_const, smul_eq_mul, ← Finset.mul_sum, hsum] at hlt2; nlinarith

/-- In any valid 3-Partition instance, the strict bounds `target < 4 * s` and `2 * s < target`
force every group in a valid assignment to have cardinality exactly `3`. -/
theorem fiber_card_eq_three {inst : ThreePartitionInstance}
    (hvalid : ThreePartitionInstance.Valid inst)
    {assign : Fin inst.numbers.length → Fin inst.numGroups}
    (hpart : IsThreePartition inst assign) (j : Fin inst.numGroups) :
    (Finset.univ.filter fun i => assign i = j).card = 3 := by
  obtain ⟨hpos, hlen, -, hbounds⟩ := hvalid
  obtain ⟨s₀, hs₀⟩ := List.exists_mem_of_length_pos (by omega : 0 < inst.numbers.length)
  have htarget_pos : 0 < inst.target := by have := (hbounds s₀ hs₀).2; omega
  exact card_eq_three_of_sum_bounds htarget_pos (hpart j) fun i _ =>
    hbounds _ (List.getElem_mem i.isLt)

/-- **3-Partition**: valid instances having a partition
into `numGroups` groups each summing to `target`.
-/
def ThreePartition : Set ThreePartitionInstance :=
  {inst | ThreePartitionInstance.Valid inst ∧ ∃ assign, IsThreePartition inst assign}

/-- Membership characterization for `ThreePartition`. -/
theorem mem_ThreePartition_iff {inst : ThreePartitionInstance} :
    inst ∈ ThreePartition ↔
      ThreePartitionInstance.Valid inst ∧ ∃ assign, IsThreePartition inst assign :=
  Iff.rfl

namespace ThreePartition

/-! ### Membership in NP (binary and unary) -/

private def check (x : ThreePartitionInstance × List ℕ) : Bool :=
  decide (0 < x.1.numGroups) &&
  decide (x.1.numbers.length = 3 * x.1.numGroups) &&
  decide (x.1.numbers.sum = x.1.numGroups * x.1.target) &&
  (x.1.numbers.all fun s => decide (x.1.target < 4 * s) && decide (2 * s < x.1.target)) &&
  decide (x.2.length = x.1.numbers.length) &&
  (x.2.all fun j => decide (j < x.1.numGroups)) &&
  ((List.range (x.1.numbers.length / 3)).all fun j =>
    decide ((((List.range x.1.numbers.length).filter fun i => x.2.getD i 0 == j).map
      fun i => x.1.numbers.getD i 0).sum = x.1.target))

private theorem sum_filter_range_eq_finset_sum {n m : ℕ} (nums g : List ℕ)
    (hnums : nums.length = n) (j : Fin m) :
    (((List.range n).filter fun i => g.getD i 0 == j.val).map fun i => nums.getD i 0).sum =
      (Finset.univ.filter fun i : Fin n => g.getD i.val 0 = j.val).sum
        fun i => nums[i.val]'(by omega) := by
  classical
  rw [← List.sum_toFinset _ (List.nodup_range.filter _)]
  refine Finset.sum_bij (fun (i : ℕ) (hi : i ∈ ((List.range n).filter _).toFinset) =>
      (⟨i, List.mem_range.mp (List.mem_filter.mp (List.mem_toFinset.mp hi)).1⟩ : Fin n))
    (fun i hi => by
      simp only [Finset.mem_filter, List.mem_toFinset, List.mem_filter, List.mem_range, beq_iff_eq,
        Finset.mem_univ, true_and] at hi ⊢; exact hi.2)
    (fun _ _ _ _ h => congrArg Fin.val h)
    (fun i hi => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      refine ⟨i.val, ?_, rfl⟩
      simp only [List.mem_toFinset, List.mem_filter, List.mem_range, beq_iff_eq]
      exact ⟨i.isLt, hi⟩)
    (fun i hi => List.getD_eq_getElem nums 0
      (by have := List.mem_range.mp (List.mem_filter.mp (List.mem_toFinset.mp hi)).1; omega))

private theorem check_iff (inst : ThreePartitionInstance) (g : List ℕ) :
    check (inst, g) = true ↔
      ThreePartitionInstance.Valid inst ∧ g.length = inst.numbers.length ∧
      (∀ j ∈ g, j < inst.numGroups) ∧
      ∀ j : Fin inst.numGroups,
        (Finset.univ.filter fun i : Fin inst.numbers.length =>
          g.getD i.val 0 = j.val).sum (fun i => inst.numbers[i]) = inst.target := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    ThreePartitionInstance.valid_iff, and_assoc]
  exact ⟨fun ⟨hpos, hlen, hsum, hbounds, hglen, hglt, hgroups⟩ =>
      ⟨hpos, hlen, hsum, hbounds, hglen, hglt, fun j => by
        have := hgroups j.val (by omega)
        rwa [sum_filter_range_eq_finset_sum inst.numbers g rfl j] at this⟩,
    fun ⟨hpos, hlen, hsum, hbounds, hglen, hglt, hgroups⟩ =>
      ⟨hpos, hlen, hsum, hbounds, hglen, hglt, fun j hj => by
        rw [sum_filter_range_eq_finset_sum inst.numbers g rfl ⟨j, by omega⟩]
        exact hgroups ⟨j, by omega⟩⟩⟩

private theorem computableInPolyTime_check :
    ComputableInPolyTime check (encPair encThreePartition (encList encUnary)) encBool := by
  let encIn := encPair encThreePartition (encList encUnary)
  have hnums := encThreePartition_numbers_polyTime (fst encThreePartition (encList encUnary))
  have hng := encThreePartition_numGroups_polyTime (fst encThreePartition (encList encUnary))
  have ht := encThreePartition_target_polyTime (fst encThreePartition (encList encUnary))
  have hg := snd encThreePartition (encList encUnary)
  have hnlen := (length_list encNat).comp hnums
  have h4 : ComputableInPolyTime (fun x : ThreePartitionInstance × List ℕ =>
      x.1.numbers.all fun s => decide (x.1.target < 4 * s) && decide (2 * s < x.1.target))
      encIn encBool :=
    allWithInput hnums (bool_and'
      (binary_lt' (ht.comp (fst encIn encNat)) (binary_mul' (const 4) (snd encIn encNat)))
      (binary_lt' (binary_mul' (const 2) (snd encIn encNat)) (ht.comp (fst encIn encNat))))
  have h6 : ComputableInPolyTime (fun x : ThreePartitionInstance × List ℕ =>
      x.2.all fun j => decide (j < x.1.numGroups)) encIn encBool :=
    allWithInput hg
      (binary_lt' (unary_to_binary.comp (snd encIn encUnary)) (hng.comp (fst encIn encUnary)))
  have h7 : ComputableInPolyTime (fun x : ThreePartitionInstance × List ℕ =>
      (List.range (x.1.numbers.length / 3)).all fun j =>
        decide ((((List.range x.1.numbers.length).filter fun i => x.2.getD i 0 == j).map
          fun i => x.1.numbers.getD i 0).sum = x.1.target)) encIn encBool := by
    refine allWithInput (range.comp ((unary_div_const 3).comp hnlen)) ?_
    let encQ := encPair encIn encUnary
    have hfilt : ComputableInPolyTime (fun q : (ThreePartitionInstance × List ℕ) × ℕ =>
        (List.range q.1.1.numbers.length).filter fun i => q.1.2.getD i 0 == q.2)
        encQ (encList encUnary) :=
      filterWithInput (range.comp (hnlen.comp (fst encIn encUnary))) (unary_beq
        (listGetDWithInput ((hg.comp (fst encIn encUnary)).comp (fst encQ encUnary))
          (snd encQ encUnary) 0) ((snd encIn encUnary).comp (fst encQ encUnary)))
    have hmapped : ComputableInPolyTime (fun q : (ThreePartitionInstance × List ℕ) × ℕ =>
        ((List.range q.1.1.numbers.length).filter fun i => q.1.2.getD i 0 == q.2).map
          fun i => q.1.1.numbers.getD i 0) encQ (encList encNat) :=
      mapWithInput hfilt (listGetDWithInput
        ((hnums.comp (fst encIn encUnary)).comp (fst encQ encUnary)) (snd encQ encUnary) 0)
    exact decide_eq' (binary_sum.comp hmapped) (ht.comp (fst encIn encUnary))
  exact bool_and' (bool_and' (bool_and' (bool_and' (bool_and' (bool_and'
    (binary_lt' (const 0) hng) (decide_eq' (unary_to_binary.comp hnlen)
      (binary_mul' (const 3) hng)))
    (decide_eq' (binary_sum.comp hnums) (binary_mul' hng ht))) h4)
    (decide_eq' ((length_list encUnary).comp hg) hnlen)) h6) h7

private theorem list_sum_le_mul {l : List ℕ} {B : ℕ} (h : ∀ a ∈ l, a ≤ B) :
    l.sum ≤ l.length * B := by
  induction l with
  | nil => simp
  | cons a t ih =>
    have := h a List.mem_cons_self; have := ih fun b hb => h b (List.mem_cons_of_mem _ hb)
    simp only [List.sum_cons, List.length_cons]; nlinarith

private theorem computableInPolyTime_id_unary_to_binary :
    ComputableInPolyTime (fun x : ThreePartitionInstance => x)
      encThreePartitionUnary encThreePartition := by
  have h1 : ComputableInPolyTime (fun x : ThreePartitionInstance => x.numbers)
      encThreePartitionUnary (encList encNat) := by
    simpa only [Function.comp_def, List.map_id'] using
      (ComputableInPolyTime.map unary_to_binary).comp
        (encThreePartitionUnary_numbers_polyTime id')
  exact encThreePartition_mk_polyTime h1
    (unary_to_binary.comp (encThreePartitionUnary_numGroups_polyTime id'))
    (unary_to_binary.comp (encThreePartitionUnary_target_polyTime id'))

/-! ### Strong NP-hardness reduction from `ThreeDM` -/

private def coordProj : Fin 3 → ℕ × ℕ × ℕ → ℕ
  | ⟨0, _⟩, t => t.1
  | ⟨1, _⟩, t => t.2.1
  | ⟨2, _⟩, t => t.2.2

private def coordCount (triples : List (ℕ × ℕ × ℕ)) (c : Fin 3) (v : ℕ) : ℕ :=
  triples.countP fun t => coordProj c t == v

private def rReal (c : Fin 3) : ℕ := if c.val = 2 then 0 else 2

private def rDummy (c : Fin 3) : ℕ := if c.val = 2 then 2 else 1

/-- Units-level base `B1 = 16` of the 3-Partition gadget. -/
def gadgetBase1 : ℕ := 16

/-- Vertex-level base `B2 = 96 * q` of the 3-Partition gadget. -/
def gadgetBase2 (q : ℕ) : ℕ := 96 * q

/-- Triple-level base `B3 = 288 * q * k` of the 3-Partition gadget. -/
def gadgetBase3 (q k : ℕ) : ℕ := 288 * q * k

/-- Target sum `T = 315 * B3 + (k - 1) * B2 + (3 * q - 1) * B1 + 10` of the 3-Partition gadget. -/
def gadgetTarget (q k : ℕ) : ℕ :=
  315 * gadgetBase3 q k + (k - 1) * gadgetBase2 q + (3 * q - 1) * gadgetBase1 + 10

private def coreNumbers (q k : ℕ) (triples : List (ℕ × ℕ × ℕ)) : List ℕ :=
  (List.range k).flatMap fun i =>
    let t := triples.getD i (0, 0, 0)
    [100 * gadgetBase3 q k + i * gadgetBase2 q + (3 * q - 1 - t.1) * gadgetBase1 + 8,
     100 * gadgetBase3 q k + i * gadgetBase2 q + (3 * q - 1 - (q + t.2.1)) * gadgetBase1 + 7,
     100 * gadgetBase3 q k + i * gadgetBase2 q + (3 * q - 1 - (2 * q + t.2.2)) * gadgetBase1 + 8]

private def linkNumbers (q k : ℕ) : List ℕ :=
  (List.range k).flatMap fun i =>
    [104 * gadgetBase3 q k + (k - 1 - i) * gadgetBase2 q,
     104 * gadgetBase3 q k + (k - 1 - i) * gadgetBase2 q + 1,
     104 * gadgetBase3 q k + (k - 1 - i) * gadgetBase2 q + 2]

private def vertexNumbers (q k : ℕ) (triples : List (ℕ × ℕ × ℕ)) (c : Fin 3) : List ℕ :=
  (List.range q).flatMap fun v =>
    (111 * gadgetBase3 q k + (c.val * q + v) * gadgetBase1 + rReal c) ::
      List.replicate (coordCount triples c v - 1)
        (111 * gadgetBase3 q k + (c.val * q + v) * gadgetBase1 + rDummy c)

/-- All `9 * k` item sizes of the 3-Partition gadget for a 3DM instance. -/
def gadgetNumbers (inst : ThreeDMInstance) : List ℕ :=
  let q := inst.size; let k := inst.triples.length
  coreNumbers q k inst.triples ++ linkNumbers q k ++
    vertexNumbers q k inst.triples 0 ++ vertexNumbers q k inst.triples 1 ++
    vertexNumbers q k inst.triples 2

/-- Guard checking that a 3DM instance is positive, bounded, and covers every coordinate at least
once. -/
def validThreeDMCheck (inst : ThreeDMInstance) : Bool :=
  decide (0 < inst.size) && decide (0 < inst.triples.length) &&
  (inst.triples.all fun t =>
    decide (t.1 < inst.size) && decide (t.2.1 < inst.size) && decide (t.2.2 < inst.size)) &&
  ((List.range inst.size).all fun u =>
    decide (0 < coordCount inst.triples 0 u) &&
    decide (0 < coordCount inst.triples 1 u) &&
    decide (0 < coordCount inst.triples 2 u))

private def yesInstance : ThreePartitionInstance := ⟨[2, 2, 2], 1, 6⟩

private def noInstance : ThreePartitionInstance := ⟨[5, 5, 5, 5, 6, 8], 2, 17⟩

/-- Unary polynomial-time reduction from `ThreeDM` to `ThreePartition`. -/
def toThreePartition (inst : ThreeDMInstance) : ThreePartitionInstance :=
  if inst.size == 0 && inst.triples.isEmpty then yesInstance
  else if validThreeDMCheck inst then
    ⟨gadgetNumbers inst, 3 * inst.triples.length, gadgetTarget inst.size inst.triples.length⟩
  else noInstance

/-! ### Polynomial-time computability of the unary reduction -/

private theorem computableInPolyTime_coordCount (c : Fin 3) :
    ComputableInPolyTime (fun p : List (ℕ × ℕ × ℕ) × ℕ => coordCount p.1 c p.2)
      (encPair (encList (encPair encUnary (encPair encUnary encUnary))) encUnary) encUnary := by
  let encT := encPair encUnary (encPair encUnary encUnary)
  have hproj : ComputableInPolyTime (coordProj c) encT encUnary := by
    rcases c with ⟨_ | _ | _ | _, hc⟩; exacts [fst _ _, (snd _ _).fst', (snd _ _).snd', by omega]
  exact countPWithInput (fst (encList encT) encUnary)
    (unary_beq (hproj.comp (snd (encPair (encList encT) encUnary) encT))
      ((snd (encList encT) encUnary).comp (fst (encPair (encList encT) encUnary) encT)))

/-- The reduction `toThreePartition` is computable in polynomial time under unary encodings. -/
@[fun_prop]
theorem computableInPolyTime_toThreePartition_unary :
    ComputableInPolyTime toThreePartition encThreeDM encThreePartitionUnary := by
  let encT := encPair encUnary (encPair encUnary encUnary)
  have hq := encThreeDM_size_polyTime (id' (encIn := encThreeDM))
  have htr := encThreeDM_triples_polyTime (id' (encIn := encThreeDM))
  have hk := (length_list encT).comp htr
  have hB2 : ComputableInPolyTime gadgetBase2 encUnary encUnary := unary_mul' (const 96) id'
  have hB3 : ComputableInPolyTime (fun p : ℕ × ℕ => gadgetBase3 p.1 p.2)
      (encPair encUnary encUnary) encUnary :=
    unary_mul' (unary_mul' (const 288) (fst encUnary encUnary)) (snd encUnary encUnary)
  have hTgt : ComputableInPolyTime (fun p : ℕ × ℕ => gadgetTarget p.1 p.2)
      (encPair encUnary encUnary) encUnary := by
    unfold gadgetTarget gadgetBase1
    exact unary_add' (unary_add' (unary_add' (unary_mul' (const 315) hB3)
      (unary_mul' (unary_sub' (snd encUnary encUnary) (const 1))
        (hB2.comp (fst encUnary encUnary))))
      (unary_mul' (unary_sub' (unary_mul' (const 3) (fst encUnary encUnary)) (const 1))
        (const 16))) (const 10)
  have hCore : ComputableInPolyTime (fun inst : ThreeDMInstance =>
      coreNumbers inst.size inst.triples.length inst.triples) encThreeDM (encList encUnary) := by
    unfold coreNumbers gadgetBase1; refine flatMapWithInput (range.comp hk) ?_
    have hq' := hq.comp (fst encThreeDM encUnary); have hi := snd encThreeDM encUnary
    have ht := listGetDWithInput (htr.comp (fst encThreeDM encUnary)) hi (0, 0, 0)
    have hbase := unary_add'
      (unary_mul' (const 100) (hB3.comp (hq'.prod (hk.comp (fst encThreeDM encUnary)))))
      (unary_mul' hi (hB2.comp hq'))
    have h3q1 := unary_sub' (unary_mul' (const 3) hq') (const 1)
    exact cons'
      (unary_add' (unary_add' hbase (unary_mul' (unary_sub' h3q1 ht.fst') (const 16))) (const 8))
      (cons' (unary_add' (unary_add' hbase
        (unary_mul' (unary_sub' h3q1 (unary_add' hq' ht.snd'.fst')) (const 16))) (const 7))
      (cons' (unary_add' (unary_add' hbase (unary_mul'
        (unary_sub' h3q1 (unary_add' (unary_mul' (const 2) hq') ht.snd'.snd')) (const 16)))
        (const 8)) (const [])))
  have hLink : ComputableInPolyTime (fun inst : ThreeDMInstance =>
      linkNumbers inst.size inst.triples.length) encThreeDM (encList encUnary) := by
    unfold linkNumbers; refine flatMapWithInput (range.comp hk) ?_
    have hq' := hq.comp (fst encThreeDM encUnary); have hk' := hk.comp (fst encThreeDM encUnary)
    have hbase := unary_add' (unary_mul' (const 104) (hB3.comp (hq'.prod hk')))
      (unary_mul' (unary_sub' (unary_sub' hk' (const 1)) (snd encThreeDM encUnary)) (hB2.comp hq'))
    exact cons' hbase
      (cons' (unary_add' hbase (const 1)) (cons' (unary_add' hbase (const 2)) (const [])))
  have hVert : ∀ c : Fin 3, ComputableInPolyTime
      (fun inst : ThreeDMInstance => vertexNumbers inst.size inst.triples.length inst.triples c)
      encThreeDM (encList encUnary) := by
    intro c; unfold vertexNumbers gadgetBase1; refine flatMapWithInput (range.comp hq) ?_
    have hq' := hq.comp (fst encThreeDM encUnary); have hv := snd encThreeDM encUnary
    have hbase := unary_add'
      (unary_mul' (const 111) (hB3.comp (hq'.prod (hk.comp (fst encThreeDM encUnary)))))
      (unary_mul' (unary_add' (unary_mul' (const c.val) hq') hv) (const 16))
    have hc := (computableInPolyTime_coordCount c).comp
      ((htr.comp (fst encThreeDM encUnary)).prod hv)
    exact cons' (unary_add' hbase (const (rReal c)))
      (ComputableInPolyTime.replicate (unary_sub' hc (const 1))
        (unary_add' hbase (const (rDummy c))))
  have hNums : ComputableInPolyTime gadgetNumbers encThreeDM (encList encUnary) := by
    unfold gadgetNumbers
    exact listAppend' (listAppend' (listAppend' (listAppend' hCore hLink) (hVert 0)) (hVert 1))
      (hVert 2)
  have hValid : ComputableInPolyTime validThreeDMCheck encThreeDM encBool := by
    unfold validThreeDMCheck
    have h3 : ComputableInPolyTime (fun inst : ThreeDMInstance => inst.triples.all fun t =>
        decide (t.1 < inst.size) && decide (t.2.1 < inst.size) && decide (t.2.2 < inst.size))
        encThreeDM encBool :=
      allWithInput htr (bool_and' (bool_and'
        (unary_lt' (snd encThreeDM encT).fst' (hq.comp (fst encThreeDM encT)))
        (unary_lt' (snd encThreeDM encT).snd'.fst' (hq.comp (fst encThreeDM encT))))
        (unary_lt' (snd encThreeDM encT).snd'.snd' (hq.comp (fst encThreeDM encT))))
    have h4 : ComputableInPolyTime (fun inst : ThreeDMInstance =>
        (List.range inst.size).all fun u =>
          decide (0 < coordCount inst.triples 0 u) && decide (0 < coordCount inst.triples 1 u) &&
            decide (0 < coordCount inst.triples 2 u)) encThreeDM encBool :=
      allWithInput (range.comp hq) (bool_and' (bool_and'
        (unary_lt' (const 0) ((computableInPolyTime_coordCount 0).comp
          ((htr.comp (fst encThreeDM encUnary)).prod (snd encThreeDM encUnary))))
        (unary_lt' (const 0) ((computableInPolyTime_coordCount 1).comp
          ((htr.comp (fst encThreeDM encUnary)).prod (snd encThreeDM encUnary)))))
        (unary_lt' (const 0) ((computableInPolyTime_coordCount 2).comp
          ((htr.comp (fst encThreeDM encUnary)).prod (snd encThreeDM encUnary)))))
    exact bool_and' (bool_and' (bool_and' (unary_lt' (const 0) hq) (unary_lt' (const 0) hk)) h3) h4
  unfold toThreePartition
  exact (bool_and' (unary_beq hq (const 0)) ((listIsEmpty' encT).comp htr)).ite (const yesInstance)
    (hValid.ite (encThreePartitionUnary_mk_polyTime hNums (unary_mul' (const 3) hk)
      (hTgt.comp (hq.prod hk))) (const noInstance))

/-! ### Tagged items, unified coordinates, and zero-carry digit extraction -/

private inductive Item
  | core (i : ℕ) (coord : Fin 3) (u : ℕ)
  | link (i : ℕ) (r : Fin 3)
  | vertex (u : ℕ) (isReal : Bool) (copy : ℕ)
  deriving DecidableEq

private def itemVal (q k : ℕ) : Item → ℕ
  | .core i c u =>
    100 * gadgetBase3 q k + i * gadgetBase2 q + (3 * q - 1 - u) * gadgetBase1 +
      (if c = 1 then 7 else 8)
  | .link i r => 104 * gadgetBase3 q k + (k - 1 - i) * gadgetBase2 q + r.val
  | .vertex u isReal _ =>
    111 * gadgetBase3 q k + u * gadgetBase1 +
      (if u < 2 * q then (if isReal then 2 else 1) else (if isReal then 0 else 2))

private def itemType : Item → ℕ
  | .core _ _ _ => 100
  | .link _ _ => 104
  | .vertex _ _ _ => 111

private def itemRem3 (q k : ℕ) : Item → ℕ
  | .core i c u => i * gadgetBase2 q + (3 * q - 1 - u) * gadgetBase1 + (if c = 1 then 7 else 8)
  | .link i r => (k - 1 - i) * gadgetBase2 q + r.val
  | .vertex u isReal _ =>
    u * gadgetBase1 +
      (if u < 2 * q then (if isReal then 2 else 1) else (if isReal then 0 else 2))

private def itemValid (q k : ℕ) : Item → Prop
  | .core i _ u => i < k ∧ u < 3 * q
  | .link i _ => i < k
  | .vertex u _ _ => u < 3 * q

private def coreItems (inst : ThreeDMInstance) : List Item :=
  (List.range inst.triples.length).flatMap fun i =>
    let t := inst.triples.getD i (0, 0, 0)
    [Item.core i 0 t.1, Item.core i 1 (inst.size + t.2.1), Item.core i 2 (2 * inst.size + t.2.2)]

private def linkItems (k : ℕ) : List Item :=
  (List.range k).flatMap fun i => [Item.link i 0, Item.link i 1, Item.link i 2]

private def vertexBlockItems (inst : ThreeDMInstance) (c : Fin 3) : List Item :=
  (List.range inst.size).flatMap fun v =>
    Item.vertex (c.val * inst.size + v) true 0 ::
      (List.range (coordCount inst.triples c v - 1)).map
        (Item.vertex (c.val * inst.size + v) false)

private def itemList (inst : ThreeDMInstance) : List Item :=
  coreItems inst ++ linkItems inst.triples.length ++
    vertexBlockItems inst 0 ++ vertexBlockItems inst 1 ++ vertexBlockItems inst 2

private theorem flatMap_congr_eq {α β : Type*} {L : List α} {f g : α → List β}
    (h : ∀ a ∈ L, f a = g a) : L.flatMap f = L.flatMap g := by
  induction L with
  | nil => rfl
  | cons a t ih =>
    simp only [List.flatMap_cons, h a List.mem_cons_self,
      ih fun b hb => h b (List.mem_cons_of_mem _ hb)]

private theorem div_lt_three {u q : ℕ} (_ : 0 < q) (hu : u < 3 * q) : u / q < 3 := by
  by_contra h; have : 3 ≤ u / q := by omega
  have : 3 * q ≤ q * (u / q) := by nlinarith
  have := Nat.div_add_mod u q; omega

private theorem div_block {q c v : ℕ} (_ : 0 < q) (hv : v < q) : (c * q + v) / q = c :=
  Nat.div_eq_of_lt_le (by nlinarith) (by nlinarith)

private theorem mod_block {q c v : ℕ} (hq : 0 < q) (hv : v < q) : (c * q + v) % q = v := by
  have h := Nat.div_add_mod (c * q + v) q; rw [div_block hq hv] at h; nlinarith

private theorem map_vertexBlockItems (inst : ThreeDMInstance) (c : Fin 3) :
    (vertexBlockItems inst c).map (itemVal inst.size inst.triples.length) =
      vertexNumbers inst.size inst.triples.length inst.triples c := by
  rw [vertexBlockItems, vertexNumbers, List.map_flatMap]
  refine flatMap_congr_eq fun v hv => ?_
  have hvlt : v < inst.size := List.mem_range.mp hv
  have hval : ∀ (b : Bool) (cp : ℕ),
      itemVal inst.size inst.triples.length (Item.vertex (c.val * inst.size + v) b cp) =
        111 * gadgetBase3 inst.size inst.triples.length +
          (c.val * inst.size + v) * gadgetBase1 + (if b then rReal c else rDummy c) := by
    intro b cp
    rcases c with ⟨_ | _ | _ | _, hc⟩
    · simp [itemVal, rReal, rDummy, show v < 2 * inst.size by omega]
    · simp [itemVal, rReal, rDummy, show inst.size + v < 2 * inst.size by omega]
    · simp [itemVal, rReal, rDummy, show ¬(2 * inst.size + v < 2 * inst.size) by omega]
    · omega
  simp only [List.map_cons, hval true 0, ↓reduceIte, List.map_map, List.cons.injEq, true_and]
  apply List.ext_getElem (by simp)
  intro j hj _; simp only [List.length_map, List.length_range] at hj
  simp [Function.comp_def, hval false]

private theorem gadgetNumbers_eq_map_itemList (inst : ThreeDMInstance) :
    gadgetNumbers inst = (itemList inst).map (itemVal inst.size inst.triples.length) := by
  have h1 : (coreItems inst).map (itemVal inst.size inst.triples.length) =
      coreNumbers inst.size inst.triples.length inst.triples :=
    (List.map_flatMap ..).trans (flatMap_congr_eq fun _ _ => by simp [itemVal])
  have h2 : (linkItems inst.triples.length).map (itemVal inst.size inst.triples.length) =
      linkNumbers inst.size inst.triples.length :=
    (List.map_flatMap ..).trans (flatMap_congr_eq fun _ _ => by simp [itemVal])
  simp only [gadgetNumbers, itemList, List.map_append, h1, h2, map_vertexBlockItems]

private theorem mem_vertexBlockItems {inst : ThreeDMInstance} {c : Fin 3} {a : Item} :
    a ∈ vertexBlockItems inst c ↔
      ∃ v < inst.size, a = Item.vertex (c.val * inst.size + v) true 0 ∨
        ∃ cp < coordCount inst.triples c v - 1,
          a = Item.vertex (c.val * inst.size + v) false cp := by
  simp only [vertexBlockItems, List.mem_flatMap, List.mem_range, List.mem_cons, List.mem_map,
    eq_comm]

private theorem nodup_vertexBlockItems (inst : ThreeDMInstance) (c : Fin 3) :
    (vertexBlockItems inst c).Nodup := by
  refine List.nodup_flatMap.mpr ⟨fun v _ =>
    List.nodup_cons.mpr ⟨by simp, List.nodup_range.map fun a b h => by simpa using h⟩, ?_⟩
  refine List.nodup_range.pairwise_of_forall_ne fun v₁ _ v₂ _ hv =>
    List.disjoint_left.mpr fun a ha₁ ha₂ => ?_
  simp only [List.mem_cons, List.mem_map, List.mem_range] at ha₁ ha₂
  rcases ha₁ with rfl | ⟨_, _, rfl⟩ <;> rcases ha₂ with h | ⟨_, _, h⟩ <;>
    simp only [Item.vertex.injEq] at h <;> omega

private theorem vertexBlockItems_disjoint {inst : ThreeDMInstance} {c₁ c₂ : Fin 3}
    (hc : c₁ ≠ c₂) {a b : Item} (ha : a ∈ vertexBlockItems inst c₁)
    (hb : b ∈ vertexBlockItems inst c₂) : a ≠ b := by
  rintro rfl
  obtain ⟨v₁, hv₁, h₁ | ⟨_, _, h₁⟩⟩ := mem_vertexBlockItems.mp ha <;>
    obtain ⟨v₂, hv₂, h₂ | ⟨_, _, h₂⟩⟩ := mem_vertexBlockItems.mp hb <;>
    (have heq := (Item.vertex.inj (h₁.symm.trans h₂)).1
     have hq : 0 < inst.size := by omega
     exact hc (Fin.ext ((div_block hq hv₁).symm.trans
       ((congrArg (· / inst.size) heq).trans (div_block hq hv₂)))))

private theorem nodup_itemList (inst : ThreeDMInstance) : (itemList inst).Nodup := by
  set k := inst.triples.length
  have hcores : (coreItems inst).Nodup := List.nodup_flatMap.mpr ⟨fun _ _ => by simp,
    List.nodup_range.pairwise_of_forall_ne fun _ _ _ _ hij => by simp [Function.onFun, hij.symm]⟩
  have hlinks : (linkItems k).Nodup := List.nodup_flatMap.mpr ⟨fun _ _ => by simp,
    List.nodup_range.pairwise_of_forall_ne fun _ _ _ _ hij => by simp [Function.onFun, hij.symm]⟩
  have hdisj : ∀ {l₁ l₂ : List Item}, (∀ x ∈ l₁, ∀ y ∈ l₂, x ≠ y) →
      l₁.Nodup → l₂.Nodup → (l₁ ++ l₂).Nodup := fun hd h1 h2 => List.nodup_append.mpr ⟨h1, h2, hd⟩
  have htype : ∀ {a b : Item}, itemType a ≠ itemType b → a ≠ b := fun h hab => h (hab ▸ rfl)
  have hCL : ∀ a ∈ coreItems inst, ∀ b ∈ linkItems k, a ≠ b := fun a ha b hb => htype (by
    simp only [coreItems, linkItems, List.mem_flatMap, List.mem_cons, List.not_mem_nil,
      or_false] at ha hb
    obtain ⟨_, _, rfl | rfl | rfl⟩ := ha <;> obtain ⟨_, _, rfl | rfl | rfl⟩ := hb <;>
      (simp only [itemType]; decide))
  have hVt : ∀ {c b}, b ∈ vertexBlockItems inst c → itemType b = 111 := fun hb => by
    obtain ⟨_, _, rfl | ⟨_, _, rfl⟩⟩ := mem_vertexBlockItems.mp hb <;> rfl
  have hCLV : ∀ a ∈ coreItems inst ++ linkItems k,
      ∀ b ∈ vertexBlockItems inst 0 ++ vertexBlockItems inst 1 ++ vertexBlockItems inst 2,
        a ≠ b := fun a ha b hb => htype (by
    have hta : itemType a = 100 ∨ itemType a = 104 := by
      simp only [coreItems, linkItems, List.mem_append, List.mem_flatMap, List.mem_cons,
        List.not_mem_nil, or_false] at ha
      rcases ha with ⟨_, _, rfl | rfl | rfl⟩ | ⟨_, _, rfl | rfl | rfl⟩ <;> simp [itemType]
    have htb : itemType b = 111 := by
      rcases List.mem_append.mp hb with hb | hb
      · rcases List.mem_append.mp hb with hb | hb <;> exact hVt hb
      · exact hVt hb
    omega)
  have hV012 : (vertexBlockItems inst 0 ++ vertexBlockItems inst 1 ++
      vertexBlockItems inst 2).Nodup :=
    hdisj (fun _ ha _ hb => by
      rcases List.mem_append.mp ha with ha | ha <;>
        exact vertexBlockItems_disjoint (by decide) ha hb)
      (hdisj (fun _ ha _ hb => vertexBlockItems_disjoint (by decide) ha hb)
        (nodup_vertexBlockItems inst 0) (nodup_vertexBlockItems inst 1))
      (nodup_vertexBlockItems inst 2)
  unfold itemList
  simpa only [List.append_assoc] using
    hdisj (by simpa only [List.append_assoc] using hCLV) (hdisj hCL hcores hlinks) hV012

private theorem validThreeDMCheck_iff (inst : ThreeDMInstance) :
    validThreeDMCheck inst = true ↔
      0 < inst.size ∧ 0 < inst.triples.length ∧
      (∀ t ∈ inst.triples, t.1 < inst.size ∧ t.2.1 < inst.size ∧ t.2.2 < inst.size) ∧
      ∀ c : Fin 3, ∀ u < inst.size, 0 < coordCount inst.triples c u := by
  simp only [validThreeDMCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range, and_assoc]
  exact ⟨fun ⟨hq, hk, hb, hc⟩ => ⟨hq, hk, hb, fun c u hu => by
      rcases c with ⟨_ | _ | _ | _, _⟩
      exacts [(hc u hu).1, (hc u hu).2.1, (hc u hu).2.2, by omega]⟩,
    fun ⟨hq, hk, hb, hc⟩ => ⟨hq, hk, hb, fun u hu => ⟨hc 0 u hu, hc 1 u hu, hc 2 u hu⟩⟩⟩

private theorem itemValid_of_mem_itemList {inst : ThreeDMInstance}
    (hv : validThreeDMCheck inst = true) {x : Item} (hx : x ∈ itemList inst) :
    itemValid inst.size inst.triples.length x := by
  obtain ⟨hq, hk, hbounds, -⟩ := (validThreeDMCheck_iff inst).mp hv
  have hV : ∀ (c : Fin 3), x ∈ vertexBlockItems inst c →
      itemValid inst.size inst.triples.length x := fun c h => by
    obtain ⟨v, hvlt, rfl | ⟨_, _, rfl⟩⟩ := mem_vertexBlockItems.mp h <;>
      exact by have := c.isLt; dsimp [itemValid]; nlinarith
  simp only [itemList, List.mem_append] at hx
  rcases hx with (((hx | hx) | hx) | hx) | hx
  · simp only [coreItems, List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil,
      or_false] at hx
    obtain ⟨i, hi, rfl | rfl | rfl⟩ := hx <;>
      (have htb := hbounds (inst.triples.getD i (0, 0, 0))
        (by rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi)) <;>
      exact ⟨hi, by omega⟩
  · simp only [linkItems, List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil,
      or_false] at hx
    obtain ⟨i, hi, rfl | rfl | rfl⟩ := hx <;> exact hi
  exacts [hV 0 hx, hV 1 hx, hV 2 hx]

private theorem itemVal_bounds_of_itemValid {q k : ℕ} (hq : 0 < q) (hk : 0 < k) {x : Item}
    (hvx : itemValid q k x) :
    gadgetTarget q k < 4 * itemVal q k x ∧ 2 * itemVal q k x < gadgetTarget q k := by
  have h3q1 : (3 * q - 1) * 16 + 16 = 48 * q := by
    have : 3 * q - 1 + 1 = 3 * q := by omega
    nlinarith
  have hbound : 100 * gadgetBase3 q k ≤ itemVal q k x ∧
      itemVal q k x ≤ 111 * gadgetBase3 q k + (3 * q - 1) * gadgetBase1 + 2 := by
    cases x with
    | core i c u =>
      obtain ⟨hi, _⟩ := hvx
      have hsub : (3 * q - 1 - u) * 16 ≤ (3 * q - 1) * 16 :=
        Nat.mul_le_mul_right 16 (Nat.sub_le _ _)
      have hik : i * (96 * q) ≤ k * (96 * q) := Nat.mul_le_mul_right _ (by omega)
      simp only [itemVal, gadgetBase1, gadgetBase2, gadgetBase3]
      split_ifs <;> constructor <;> nlinarith
    | link i r =>
      have : i < k := hvx; have := r.isLt
      have hki : (k - 1 - i) * (96 * q) ≤ k * (96 * q) := Nat.mul_le_mul_right _ (by omega)
      simp only [itemVal, gadgetBase1, gadgetBase2, gadgetBase3]; constructor <;> nlinarith
    | vertex u _ _ =>
      have hu : u < 3 * q := hvx
      have hu1 : u * 16 ≤ (3 * q - 1) * 16 := Nat.mul_le_mul_right 16 (by omega)
      simp only [itemVal, gadgetBase1, gadgetBase3]; split_ifs <;> constructor <;> nlinarith
  have hk1 : (k - 1) * (96 * q) ≤ k * (96 * q) := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
  simp only [gadgetTarget, gadgetBase1, gadgetBase2, gadgetBase3] at hbound ⊢
  constructor <;> nlinarith

private theorem core_mem_itemList_iff {inst : ThreeDMInstance} {i u : ℕ} {c : Fin 3} :
    Item.core i c u ∈ itemList inst ↔
      i < inst.triples.length ∧
      u = c.val * inst.size + coordProj c (inst.triples.getD i (0, 0, 0)) := by
  have hnotL : Item.core i c u ∉ linkItems inst.triples.length := by simp [linkItems]
  have hnotV : ∀ c' : Fin 3, Item.core i c u ∉ vertexBlockItems inst c' := fun c' h => by
    obtain ⟨_, _, h | ⟨_, _, h⟩⟩ := mem_vertexBlockItems.mp h <;> simp at h
  simp only [itemList, List.mem_append, hnotL, hnotV, or_false, coreItems, List.mem_flatMap,
    List.mem_range, List.mem_cons, List.not_mem_nil]
  refine ⟨fun ⟨j, hj, h⟩ => ?_, fun ⟨hi, hu⟩ => ⟨i, hi, ?_⟩⟩
  · rcases h with h | h | h <;> simp only [Item.core.injEq] at h <;>
      obtain ⟨rfl, rfl, rfl⟩ := h <;> exact ⟨hj, by simp [coordProj]⟩
  · subst hu; rcases c with ⟨_ | _ | _ | _, hc⟩
    exacts [Or.inl (by simp [coordProj]), Or.inr (Or.inl (by simp [coordProj])),
      Or.inr (Or.inr (by simp [coordProj])), by omega]

private theorem link_mem_itemList_iff {inst : ThreeDMInstance} {i : ℕ} {r : Fin 3} :
    Item.link i r ∈ itemList inst ↔ i < inst.triples.length := by
  have hnotC : Item.link i r ∉ coreItems inst := by simp [coreItems]
  have hnotV : ∀ c' : Fin 3, Item.link i r ∉ vertexBlockItems inst c' := fun c' h => by
    obtain ⟨_, _, h | ⟨_, _, h⟩⟩ := mem_vertexBlockItems.mp h <;> simp at h
  simp only [itemList, List.mem_append, hnotC, hnotV, false_or, or_false, linkItems,
    List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil]
  refine ⟨fun ⟨j, hj, h⟩ => ?_, fun hi => ⟨i, hi, ?_⟩⟩
  · rcases h with h | h | h <;> simp only [Item.link.injEq] at h <;> exact h.1 ▸ hj
  · rcases r with ⟨_ | _ | _ | _, hr⟩
    exacts [Or.inl rfl, Or.inr (Or.inl rfl), Or.inr (Or.inr rfl), by omega]

private theorem vertex_mem_itemList_iff {inst : ThreeDMInstance} {c : Fin 3} {v copy : ℕ}
    (hv : v < inst.size) {isReal : Bool} :
    Item.vertex (c.val * inst.size + v) isReal copy ∈ itemList inst ↔
      (isReal = true ∧ copy = 0) ∨
      (isReal = false ∧ copy < coordCount inst.triples c v - 1) := by
  have hnotC : Item.vertex (c.val * inst.size + v) isReal copy ∉ coreItems inst := by
    simp [coreItems]
  have hnotL : Item.vertex (c.val * inst.size + v) isReal copy ∉ linkItems inst.triples.length := by
    simp [linkItems]
  have hq : 0 < inst.size := by omega
  have hblock : ∀ c' : Fin 3,
      Item.vertex (c.val * inst.size + v) isReal copy ∈ vertexBlockItems inst c' →
        (isReal = true ∧ copy = 0) ∨ (isReal = false ∧ copy < coordCount inst.triples c v - 1) := by
    intro c' hm
    obtain ⟨v', hv', h | ⟨cp, hcp, h⟩⟩ := mem_vertexBlockItems.mp hm <;>
      obtain ⟨hu, hr, hcp'⟩ := Item.vertex.inj h
    · exact Or.inl ⟨hr, hcp'⟩
    · have hc' : c = c' := Fin.ext ((div_block hq hv).symm.trans
        ((congrArg (· / inst.size) hu).trans (div_block hq hv')))
      have hv'eq : v = v' := (mod_block hq hv).symm.trans
        ((congrArg (· % inst.size) hu).trans (mod_block hq hv'))
      exact Or.inr ⟨hr, hc' ▸ hv'eq ▸ hcp' ▸ hcp⟩
  simp only [itemList, List.mem_append, hnotC, hnotL, false_or]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rcases h with (h | h) | h; exacts [hblock 0 h, hblock 1 h, hblock 2 h]
  · have hm : Item.vertex (c.val * inst.size + v) isReal copy ∈ vertexBlockItems inst c :=
      mem_vertexBlockItems.mpr ⟨v, hv,
        h.elim (fun ⟨h1, h2⟩ => Or.inl (by rw [h1, h2]))
          (fun ⟨h1, hm⟩ => Or.inr ⟨copy, hm, by rw [h1]⟩)⟩
    rcases c with ⟨_ | _ | _ | _, hc⟩
    exacts [Or.inl (Or.inl hm), Or.inl (Or.inr hm), Or.inr hm, by omega]

private theorem itemVal_eq_type_add_rem3 (q k : ℕ) (x : Item) :
    itemVal q k x = itemType x * gadgetBase3 q k + itemRem3 q k x := by
  cases x <;> simp [itemVal, itemType, itemRem3, Nat.add_assoc]

private theorem itemRem3_lt {q k : ℕ} (hq : 0 < q) (hk : 0 < k) {x : Item}
    (hx : itemValid q k x) : itemRem3 q k x < k * gadgetBase2 q := by
  cases x with
  | core i c u =>
    obtain ⟨hi, _⟩ := hx
    have := Nat.mul_le_mul_right 16 (show 3 * q - 1 - u ≤ 3 * q by omega)
    have := Nat.mul_le_mul_right (96 * q) hi
    simp only [itemRem3, gadgetBase2, gadgetBase1]; split_ifs <;> nlinarith
  | link i r =>
    have : i < k := hx; have := r.isLt
    have := Nat.mul_le_mul_right (96 * q) (show k - 1 - i + 1 ≤ k by omega)
    simp only [itemRem3, gadgetBase2]; nlinarith
  | vertex u _ _ =>
    have : u < 3 * q := hx; simp only [itemRem3, gadgetBase2, gadgetBase1]; split_ifs <;> nlinarith

private theorem ordered_match_of_sum_eq {q k : ℕ} (hq : 0 < q) (hk : 0 < k)
    {i j u u' : ℕ} {coord r : Fin 3} {isReal : Bool} {copy : ℕ}
    (hK : itemValid q k (Item.core i coord u)) (hL : itemValid q k (Item.link j r))
    (hV : itemValid q k (Item.vertex u' isReal copy))
    (hsum : itemVal q k (Item.core i coord u) + itemVal q k (Item.link j r) +
      itemVal q k (Item.vertex u' isReal copy) = gadgetTarget q k) :
    j = i ∧ u' = u ∧
    (if coord = 1 then 7 else 8) + r.val +
      (if u < 2 * q then (if isReal then 2 else 1) else (if isReal then 0 else 2)) = 10 := by
  obtain ⟨hi, hu⟩ := hK; have hj : j < k := hL; have hu' : u' < 3 * q := hV; have hr := r.isLt
  set B1 := gadgetBase1; set B2 := gadgetBase2 q
  have hB1 : B1 = 16 := rfl; have hB2 : B2 = 96 * q := rfl
  have hrem3 : i * B2 + (3 * q - 1 - u) * B1 + (if coord = 1 then 7 else 8) +
      ((k - 1 - j) * B2 + r.val) +
      (u' * B1 + if u' < 2 * q then (if isReal then 2 else 1) else (if isReal then 0 else 2)) =
      (k - 1) * B2 + (3 * q - 1) * B1 + 10 := by
    simp only [itemVal, gadgetTarget] at hsum; linarith
  set d0K := if coord = 1 then 7 else 8
  set d0V := if u' < 2 * q then (if isReal then 2 else 1) else (if isReal then 0 else 2)
  have hd0K : d0K ≤ 8 := by dsimp [d0K]; split_ifs <;> omega
  have hd0V : d0V ≤ 2 := by dsimp [d0V]; split_ifs <;> omega
  have hB2_eq : i + (k - 1 - j) = k - 1 := by
    by_contra hne; rw [hB1, hB2] at hrem3
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · have := Nat.mul_le_mul_right (96 * q) hlt
      have := Nat.mul_le_mul_right 16 (show 3 * q - 1 - u + 1 ≤ 3 * q by omega)
      have := Nat.mul_le_mul_right 16 hu'; nlinarith
    · have := Nat.mul_le_mul_right (96 * q) hgt
      have := Nat.mul_le_mul_right 16 (Nat.sub_le (3 * q) 1); nlinarith
  have hrem2 : (3 * q - 1 - u) * B1 + u' * B1 + (d0K + r.val + d0V) = (3 * q - 1) * B1 + 10 := by
    have : i * B2 + (k - 1 - j) * B2 = (k - 1) * B2 := by rw [← Nat.add_mul, hB2_eq]
    linarith
  have hB1_eq : (3 * q - 1 - u) + u' = 3 * q - 1 := by
    by_contra hne; rcases Nat.lt_or_gt_of_ne hne with hlt | hgt <;> (rw [hB1] at hrem2; nlinarith)
  have hu'u : u' = u := by omega
  have hd0 : d0K + r.val + d0V = 10 := by
    have : (3 * q - 1 - u) * B1 + u' * B1 = (3 * q - 1) * B1 := by rw [← Nat.add_mul, hB1_eq]
    linarith
  exact ⟨by omega, hu'u, by simpa only [d0K, d0V, hu'u] using hd0⟩

private theorem triple_match_of_sum_eq {q k : ℕ} (hq : 0 < q) (hk : 0 < k)
    {a b c : Item} (ha : itemValid q k a) (hb : itemValid q k b) (hc : itemValid q k c)
    (hsum : itemVal q k a + itemVal q k b + itemVal q k c = gadgetTarget q k) :
    ∃ (i : ℕ) (coord : Fin 3) (u : ℕ) (r : Fin 3) (isReal : Bool) (copy : ℕ),
      ({a, b, c} : Finset Item) =
        {Item.core i coord u, Item.link i r, Item.vertex u isReal copy} ∧
      (if coord = 1 then 7 else 8) + r.val +
        (if u < 2 * q then (if isReal then 2 else 1) else (if isReal then 0 else 2)) = 10 := by
  have hrem_lt : itemRem3 q k a + itemRem3 q k b + itemRem3 q k c < gadgetBase3 q k := by
    rw [show gadgetBase3 q k = 3 * (k * gadgetBase2 q) by
      simp only [gadgetBase3, gadgetBase2]; ring]
    have := itemRem3_lt hq hk ha; have := itemRem3_lt hq hk hb; have := itemRem3_lt hq hk hc
    omega
  have hTrem_lt : (k - 1) * gadgetBase2 q + (3 * q - 1) * gadgetBase1 + 10 < gadgetBase3 q k := by
    have hk1 : k - 1 + 1 = k := by omega
    have h3q : 3 * q - 1 + 1 = 3 * q := by omega
    simp only [gadgetBase1, gadgetBase2, gadgetBase3]; nlinarith
  have htype : itemType a + itemType b + itemType c = 315 := by
    rw [itemVal_eq_type_add_rem3 q k a, itemVal_eq_type_add_rem3 q k b,
      itemVal_eq_type_add_rem3 q k c, gadgetTarget] at hsum
    set s := itemType a + itemType b + itemType c
    have hs : s * gadgetBase3 q k = itemType a * gadgetBase3 q k +
        itemType b * gadgetBase3 q k + itemType c * gadgetBase3 q k := by simp only [s, Nat.add_mul]
    by_contra hne; rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · have h1 := Nat.mul_le_mul_right (gadgetBase3 q k) (show s + 1 ≤ 315 by omega)
      rw [Nat.add_mul, Nat.one_mul] at h1; omega
    · have h1 := Nat.mul_le_mul_right (gadgetBase3 q k) (show 316 ≤ s by omega); omega
  cases a <;> cases b <;> cases c <;> simp only [itemType] at htype <;> try omega
  · obtain ⟨rfl, rfl, h⟩ := ordered_match_of_sum_eq hq hk ha hb hc hsum
    exact ⟨_, _, _, _, _, _, rfl, h⟩
  · obtain ⟨rfl, rfl, h⟩ := ordered_match_of_sum_eq hq hk ha hc hb (by omega)
    exact ⟨_, _, _, _, _, _, by ext; simp; tauto, h⟩
  · obtain ⟨rfl, rfl, h⟩ := ordered_match_of_sum_eq hq hk hb ha hc (by omega)
    exact ⟨_, _, _, _, _, _, by ext; simp; tauto, h⟩
  · obtain ⟨rfl, rfl, h⟩ := ordered_match_of_sum_eq hq hk hc ha hb (by omega)
    exact ⟨_, _, _, _, _, _, by ext; simp; tauto, h⟩
  · obtain ⟨rfl, rfl, h⟩ := ordered_match_of_sum_eq hq hk hb hc ha (by omega)
    exact ⟨_, _, _, _, _, _, by ext; simp; tauto, h⟩
  · obtain ⟨rfl, rfl, h⟩ := ordered_match_of_sum_eq hq hk hc hb ha (by omega)
    exact ⟨_, _, _, _, _, _, by ext; simp; tauto, h⟩

private theorem exists_isThreePartition_of_item_assign {α : Type*} [DecidableEq α]
    {L : List α} (hL : L.Nodup) (f : α → ℕ) {m T : ℕ}
    (g : α → Fin m) (hg : ∀ j : Fin m, (L.toFinset.filter fun x => g x = j).sum f = T) :
    ∃ assign : Fin (L.map f).length → Fin m, IsThreePartition ⟨L.map f, m, T⟩ assign := by
  refine ⟨fun i => g (L[i.val]'(by simpa using i.isLt)), fun j => ?_⟩
  dsimp only [IsThreePartition]; rw [← hg j]
  refine Finset.sum_bij (fun (i : Fin (L.map f).length) _ => L[i.val]'(by simpa using i.isLt))
    (fun i hi => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, List.mem_toFinset] at hi ⊢
      exact ⟨List.getElem_mem _, hi⟩)
    (fun _ _ _ _ h => Fin.ext ((List.Nodup.getElem_inj_iff hL).mp h))
    (fun x hx => by
      simp only [Finset.mem_filter, List.mem_toFinset] at hx
      obtain ⟨idx, hidx, rfl⟩ := List.getElem_of_mem hx.1
      exact ⟨⟨idx, by simpa using hidx⟩, by simp [hx.2], rfl⟩) (fun _ _ => by simp)

private theorem exists_item_assign_of_isThreePartition {α : Type*} [DecidableEq α]
    {L : List α} (hL : L.Nodup) (f : α → ℕ) {m T : ℕ} (hm : 0 < m)
    {assign : Fin (L.map f).length → Fin m} (h : IsThreePartition ⟨L.map f, m, T⟩ assign) :
    ∃ g : α → Fin m, ∀ j : Fin m, (L.toFinset.filter fun x => g x = j).sum f = T := by
  classical
  let g : α → Fin m := fun x =>
    if hx : x ∈ L then assign ⟨L.idxOf x, by simpa using List.idxOf_lt_length_of_mem hx⟩
    else ⟨0, hm⟩
  refine ⟨g, fun j => ?_⟩
  dsimp only [IsThreePartition] at h; rw [← h j]
  refine Finset.sum_bij
    (fun x hx => ⟨L.idxOf x, by
      simpa using List.idxOf_lt_length_of_mem
        (List.mem_toFinset.mp (Finset.mem_filter.mp hx).1)⟩)
    (fun x hx => by
      simp only [Finset.mem_filter, List.mem_toFinset, Finset.mem_univ, true_and] at hx ⊢
      simpa only [g, hx.1, ↓reduceDIte] using hx.2)
    (fun x₁ hx₁ x₂ hx₂ hidx => by
      simp only [Finset.mem_filter, List.mem_toFinset] at hx₁ hx₂
      have hval : L.idxOf x₁ = L.idxOf x₂ := congrArg Fin.val hidx
      exact ((List.getElem_idxOf (List.idxOf_lt_length_of_mem hx₁.1)).symm.trans
        (by simp [hval])).trans (List.getElem_idxOf (List.idxOf_lt_length_of_mem hx₂.1)))
    (fun i hi => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      have hilt : i.val < L.length := by simpa using i.isLt
      have hidx : L.idxOf (L[i.val]'hilt) = i.val := by simp [hL.idxOf_getElem]
      refine ⟨L[i.val]'hilt, ?_, Fin.ext hidx⟩
      simp only [Finset.mem_filter, List.mem_toFinset, g, List.getElem_mem hilt, ↓reduceDIte]
      exact ⟨trivial, by
        rwa [show (⟨L.idxOf (L[i.val]'hilt), _⟩ : Fin (L.map f).length) = i from Fin.ext hidx]⟩)
    (fun x hx => by
      simp only [Finset.mem_filter, List.mem_toFinset] at hx
      change f x = (L.map f)[L.idxOf x]'(by simpa using List.idxOf_lt_length_of_mem hx.1)
      simp only [List.getElem_map, List.getElem_idxOf (List.idxOf_lt_length_of_mem hx.1)])

private theorem r_cycle_sync {b0 b1 b2 : Bool} {r0 r1 r2 : Fin 3}
    (h01 : r0 ≠ r1) (h02 : r0 ≠ r2) (h12 : r1 ≠ r2)
    (he0 : 8 + r0.val + (if b0 then 2 else 1) = 10)
    (he1 : 7 + r1.val + (if b1 then 2 else 1) = 10)
    (he2 : 8 + r2.val + (if b2 then 0 else 2) = 10) : b0 = b1 ∧ b1 = b2 := by
  have : r0.val ≠ r1.val := fun h => h01 (Fin.ext h)
  have : r0.val ≠ r2.val := fun h => h02 (Fin.ext h)
  have : r1.val ≠ r2.val := fun h => h12 (Fin.ext h)
  have := r0.isLt; have := r1.isLt; have := r2.isLt
  cases b0 <;> cases b1 <;> cases b2 <;> simp_all <;> omega

private theorem perm_range_of_nodup_lt {l : List ℕ} {q : ℕ}
    (hnd : l.Nodup) (hlen : l.length = q) (hlt : ∀ x ∈ l, x < q) :
    l.Perm (List.range q) := by
  have heq := Finset.eq_of_subset_of_card_le
    (fun x hx => Finset.mem_range.mpr (hlt x (List.mem_toFinset.mp hx)))
    (by rw [Finset.card_range, List.toFinset_card_of_nodup hnd, hlen])
  refine (List.perm_ext_iff_of_nodup hnd List.nodup_range).mpr fun x => ?_
  rw [← List.mem_toFinset, heq, Finset.mem_range, List.mem_range]

/-! ### Backward direction: 3-Partition implies 3DM -/

private theorem mem_ThreeDM_of_gadget {inst : ThreeDMInstance}
    (hv : validThreeDMCheck inst = true)
    (hpart : ⟨gadgetNumbers inst, 3 * inst.triples.length,
      gadgetTarget inst.size inst.triples.length⟩ ∈ ThreePartition) :
    inst ∈ ThreeDM := by
  classical
  obtain ⟨hq, hk, hbounds, -⟩ := (validThreeDMCheck_iff inst).mp hv
  set q := inst.size; set k := inst.triples.length
  set S := (itemList inst).toFinset
  have hS_mem : ∀ x, x ∈ S ↔ x ∈ itemList inst := fun _ => List.mem_toFinset
  have hgn : gadgetNumbers inst = (itemList inst).map (itemVal q k) :=
    gadgetNumbers_eq_map_itemList inst
  have hpart' : (⟨(itemList inst).map (itemVal q k), 3 * k, gadgetTarget q k⟩ :
      ThreePartitionInstance) ∈ ThreePartition := by rwa [← hgn]
  obtain ⟨hvalid', _, hassign''⟩ := hpart'
  obtain ⟨g, hg⟩ := exists_item_assign_of_isThreePartition (nodup_itemList inst) (itemVal q k)
    (by omega) hassign''
  have hgroup : ∀ j : Fin (3 * k),
      ∃ (i : ℕ) (coord : Fin 3) (u : ℕ) (r : Fin 3) (isReal : Bool) (copy : ℕ),
        S.filter (fun x => g x = j) =
          {Item.core i coord u, Item.link i r, Item.vertex u isReal copy} ∧
        (if coord = 1 then 7 else 8) + r.val +
          (if u < 2 * q then (if isReal then 2 else 1) else (if isReal then 0 else 2)) = 10 := by
    intro j
    have hcard3 := card_eq_three_of_sum_bounds (by simp only [gadgetTarget]; omega) (hg j)
      fun x hx => hvalid'.bounds (itemVal q k x)
        (List.mem_map.mpr ⟨x, List.mem_toFinset.mp (Finset.mem_filter.mp hx).1, rfl⟩)
    obtain ⟨a, b, c, hab, hac, hbc, hF⟩ := Finset.card_eq_three.mp hcard3
    have hmem : ∀ y, y ∈ ({a, b, c} : Finset Item) → y ∈ S := fun y hy =>
      (Finset.mem_filter.mp (hF ▸ hy)).1
    have hsum : itemVal q k a + itemVal q k b + itemVal q k c = gadgetTarget q k := by
      have hgj := hg j
      rw [hF, Finset.sum_insert (by simp [hab, hac]), Finset.sum_insert (by simp [hbc]),
        Finset.sum_singleton, ← Nat.add_assoc] at hgj; exact hgj
    obtain ⟨i, coord, u, r, isReal, copy, hset, hd0⟩ := triple_match_of_sum_eq hq hk
      (itemValid_of_mem_itemList hv (List.mem_toFinset.mp (hmem a (by simp))))
      (itemValid_of_mem_itemList hv (List.mem_toFinset.mp (hmem b (by simp))))
      (itemValid_of_mem_itemList hv (List.mem_toFinset.mp (hmem c (by simp)))) hsum
    exact ⟨i, coord, u, r, isReal, copy, hF.trans hset, hd0⟩
  have hcore_comp : ∀ {i u : ℕ} {c : Fin 3}, Item.core i c u ∈ S →
      ∃ (r : Fin 3) (b : Bool) (cp : ℕ),
        S.filter (fun x => g x = g (Item.core i c u)) =
          {Item.core i c u, Item.link i r, Item.vertex u b cp} ∧
        g (Item.link i r) = g (Item.core i c u) ∧
        Item.vertex u b cp ∈ S ∧ g (Item.vertex u b cp) = g (Item.core i c u) ∧
        (if c = 1 then 7 else 8) + r.val +
          (if u < 2 * q then (if b then 2 else 1) else (if b then 0 else 2)) = 10 := by
    intro i u c hK
    obtain ⟨i', c', u', r, b, cp, hF, hd0⟩ := hgroup (g (Item.core i c u))
    have hm : Item.core i c u ∈ ({Item.core i' c' u', Item.link i' r,
        Item.vertex u' b cp} : Finset Item) := hF ▸ Finset.mem_filter.mpr ⟨hK, rfl⟩
    simp only [Finset.mem_insert, Finset.mem_singleton, reduceCtorEq, or_false] at hm
    obtain ⟨rfl, rfl, rfl⟩ := Item.core.inj hm
    have hL := Finset.mem_filter.mp
      (hF.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    have hV := Finset.mem_filter.mp
      (hF.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))
    exact ⟨r, b, cp, hF, hL.2, hV.1, hV.2, hd0⟩
  have hcore_uniq : ∀ {i₁ i₂ u₁ u₂ : ℕ} {c₁ c₂ : Fin 3},
      Item.core i₁ c₁ u₁ ∈ S → Item.core i₂ c₂ u₂ ∈ S →
      g (Item.core i₁ c₁ u₁) = g (Item.core i₂ c₂ u₂) → i₁ = i₂ ∧ c₁ = c₂ ∧ u₁ = u₂ := by
    intro i₁ i₂ u₁ u₂ c₁ c₂ h1 h2 hgeq
    obtain ⟨r, b, cp, hF, -⟩ := hcore_comp h1
    have hm : Item.core i₂ c₂ u₂ ∈ ({Item.core i₁ c₁ u₁, Item.link i₁ r,
        Item.vertex u₁ b cp} : Finset Item) := hF ▸ Finset.mem_filter.mpr ⟨h2, hgeq.symm⟩
    simp only [Finset.mem_insert, Finset.mem_singleton, Item.core.injEq, reduceCtorEq,
      or_false] at hm
    exact ⟨hm.1.symm, hm.2.1.symm, hm.2.2.symm⟩
  have hcp0 : ∀ {c : Fin 3} {v cp : ℕ}, v < q →
      Item.vertex (c.val * q + v) true cp ∈ S → cp = 0 := fun hv hV => by
    rcases (vertex_mem_itemList_iff hv).mp (List.mem_toFinset.mp hV) with ⟨-, h⟩ | ⟨h, -⟩
    exacts [h, by simp at h]
  have hsync : ∀ (i : ℕ) (hi : i < k), let t := inst.triples[i]'hi
      g (Item.core i 0 t.1) = g (Item.vertex t.1 true 0) →
      g (Item.core i 1 (q + t.2.1)) = g (Item.vertex (q + t.2.1) true 0) ∧
      g (Item.core i 2 (2 * q + t.2.2)) = g (Item.vertex (2 * q + t.2.2) true 0) := by
    intro i hi t hreal0
    have htb := hbounds t (List.getElem_mem hi)
    have hK_m : ∀ c : Fin 3, Item.core i c (c.val * q + coordProj c t) ∈ S := fun c =>
      (hS_mem _).mpr (core_mem_itemList_iff.mpr ⟨hi, by rw [List.getD_eq_getElem _ _ hi]⟩)
    have hK0 : Item.core i 0 t.1 ∈ S := by simpa [coordProj] using hK_m 0
    have hK1 : Item.core i 1 (q + t.2.1) ∈ S := by simpa [coordProj] using hK_m 1
    have hK2 : Item.core i 2 (2 * q + t.2.2) ∈ S := by simpa [coordProj] using hK_m 2
    obtain ⟨r0, b0, cp0, hF0, hgl0, -, -, hd0⟩ := hcore_comp hK0
    obtain ⟨r1, b1, cp1, -, hgl1, hV1, hgV1, hd1⟩ := hcore_comp hK1
    obtain ⟨r2, b2, cp2, -, hgl2, hV2, hgV2, hd2⟩ := hcore_comp hK2
    have hV0 : Item.vertex t.1 true 0 ∈ S := (hS_mem _).mpr
      (by simpa using (vertex_mem_itemList_iff (c := 0) htb.1).mpr (Or.inl ⟨rfl, rfl⟩))
    have hb0 : b0 = true := by
      have hm := hF0 ▸ Finset.mem_filter.mpr ⟨hV0, hreal0.symm⟩
      simp only [Finset.mem_insert, Finset.mem_singleton, reduceCtorEq, false_or,
        Item.vertex.injEq] at hm; exact hm.2.1.symm
    simp only [show (0 : Fin 3) ≠ 1 by decide, show (2 : Fin 3) ≠ 1 by decide, ↓reduceIte,
      show t.1 < 2 * q by omega, show q + t.2.1 < 2 * q by omega,
      show ¬(2 * q + t.2.2 < 2 * q) by omega] at hd0 hd1 hd2
    obtain ⟨hb01, hb12⟩ := r_cycle_sync
      (fun h => absurd (hcore_uniq hK0 hK1 (by rw [← hgl0, ← hgl1, h])).2.1 (by decide))
      (fun h => absurd (hcore_uniq hK0 hK2 (by rw [← hgl0, ← hgl2, h])).2.1 (by decide))
      (fun h => absurd (hcore_uniq hK1 hK2 (by rw [← hgl1, ← hgl2, h])).2.1 (by decide))
      hd0 hd1 hd2
    obtain ⟨rfl, rfl⟩ : b1 = true ∧ b2 = true :=
      ⟨hb01.symm.trans hb0, hb12.symm.trans (hb01.symm.trans hb0)⟩
    have hcp1 : cp1 = 0 := hcp0 (c := 1) htb.2.1 (by simpa using hV1)
    have hcp2 : cp2 = 0 := hcp0 (c := 2) htb.2.2 hV2
    rw [hcp1] at hgV1; rw [hcp2] at hgV2; exact ⟨hgV1.symm, hgV2.symm⟩
  have hexW : ∀ w < q, ∃ i : ℕ, ∃ hi : i < k,
      (inst.triples[i]'hi).1 = w ∧ g (Item.core i 0 w) = g (Item.vertex w true 0) := by
    intro w hw
    have hVw : Item.vertex w true 0 ∈ S := (hS_mem _).mpr
      (by simpa using (vertex_mem_itemList_iff (c := 0) hw).mpr (Or.inl ⟨rfl, rfl⟩))
    obtain ⟨i, c, u, r, b, cp, hF, -⟩ := hgroup (g (Item.vertex w true 0))
    have hV_in : Item.vertex w true 0 ∈ ({Item.core i c u, Item.link i r,
        Item.vertex u b cp} : Finset Item) := hF ▸ Finset.mem_filter.mpr ⟨hVw, rfl⟩
    simp only [Finset.mem_insert, Finset.mem_singleton, reduceCtorEq, false_or,
      Item.vertex.injEq] at hV_in; obtain ⟨rfl, -, -⟩ := hV_in
    have hK := Finset.mem_filter.mp (hF.symm ▸ Finset.mem_insert_self _ _)
    obtain ⟨hi, hget⟩ := core_mem_itemList_iff.mp (List.mem_toFinset.mp hK.1)
    rcases c with ⟨_ | _ | _ | _, hc⟩
    · simp only [Nat.zero_mul, Nat.zero_add, coordProj, List.getD_eq_getElem _ _ hi] at hget
      exact ⟨i, hi, hget.symm, hK.2⟩
    · dsimp only at hget; omega
    · dsimp only at hget; omega
    · omega
  let idxOfW (w : ℕ) : ℕ := if hw : w < q then (hexW w hw).choose else 0
  have hidx_lt : ∀ w (hw : w < q), idxOfW w < k := fun w hw => by
    simp only [idxOfW, hw, ↓reduceDIte]; exact (hexW w hw).choose_spec.choose
  have hidx_fst : ∀ w (hw : w < q), (inst.triples[idxOfW w]'(hidx_lt w hw)).1 = w := fun w hw => by
    simp only [idxOfW, hw, ↓reduceDIte]; exact (hexW w hw).choose_spec.choose_spec.1
  have hidx_g : ∀ w (hw : w < q), g (Item.core (idxOfW w) 0 w) = g (Item.vertex w true 0) :=
    fun w hw => by simp only [idxOfW, hw, ↓reduceDIte]; exact (hexW w hw).choose_spec.choose_spec.2
  let M := (List.range q).map fun w => inst.triples.getD (idxOfW w) (0, 0, 0)
  have hM_get : ∀ w (hw : w < q), inst.triples.getD (idxOfW w) (0, 0, 0) =
      inst.triples[idxOfW w]'(hidx_lt w hw) := fun w hw => List.getD_eq_getElem _ _ (hidx_lt w hw)
  have hproj_perm : ∀ (c : Fin 3),
      (∀ w₁ (h₁ : w₁ < q) w₂ (h₂ : w₂ < q),
        coordProj c (inst.triples[idxOfW w₁]'(hidx_lt w₁ h₁)) =
          coordProj c (inst.triples[idxOfW w₂]'(hidx_lt w₂ h₂)) →
        g (Item.core (idxOfW w₁) c (c.val * q +
            coordProj c (inst.triples[idxOfW w₁]'(hidx_lt w₁ h₁)))) =
          g (Item.core (idxOfW w₂) c (c.val * q +
            coordProj c (inst.triples[idxOfW w₂]'(hidx_lt w₂ h₂))))) →
      (M.map (coordProj c)).Perm (List.range q) := by
    intro c hinj
    refine perm_range_of_nodup_lt ?_ (by simp [M]) fun x hx => ?_
    · dsimp only [M]; rw [List.map_map]
      refine List.nodup_range.map_on fun w₁ hw₁ w₂ hw₂ heq => ?_
      have h₁ := List.mem_range.mp hw₁; have h₂ := List.mem_range.mp hw₂
      simp only [Function.comp_def, hM_get w₁ h₁, hM_get w₂ h₂] at heq
      have hK_m : ∀ w (hw : w < q), Item.core (idxOfW w) c
          (c.val * q + coordProj c (inst.triples[idxOfW w]'(hidx_lt w hw))) ∈ S := fun w hw =>
        (hS_mem _).mpr (core_mem_itemList_iff.mpr
          ⟨hidx_lt w hw, by rw [List.getD_eq_getElem _ _ (hidx_lt w hw)]⟩)
      have hidx_eq : idxOfW w₁ = idxOfW w₂ :=
        (hcore_uniq (hK_m w₁ h₁) (hK_m w₂ h₂) (hinj w₁ h₁ w₂ h₂ heq)).1
      have hfst1 := hidx_fst w₁ h₁; have hfst2 := hidx_fst w₂ h₂
      simp only [hidx_eq] at hfst1; exact hfst1.symm.trans hfst2
    · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx; obtain ⟨w, hw, rfl⟩ := List.mem_map.mp ht
      rw [hM_get w (List.mem_range.mp hw)]
      have htb := hbounds _ (List.getElem_mem (hidx_lt w (List.mem_range.mp hw)))
      rcases c with ⟨_ | _ | _ | _, hc⟩; exacts [htb.1, htb.2.1, htb.2.2, by omega]
  refine mem_ThreeDM_iff.mpr ⟨hbounds, M, isThreeDM_iff.mpr ⟨fun t ht => ?_, ?_, ?_, ?_⟩⟩
  · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp ht
    rw [hM_get w (List.mem_range.mp hw)]; exact List.getElem_mem _
  · have hfst : M.map Prod.fst = List.range q := by
      apply List.ext_getElem (by simp [M])
      intro w hw _; simp only [M, List.length_map, List.length_range] at hw
      simp only [M, List.getElem_map, List.getElem_range, hM_get w hw, hidx_fst w hw]
    rw [hfst]
  · exact hproj_perm 1 fun w₁ h₁ w₂ h₂ heq => by
      simp only [coordProj, show (1 : Fin 3).val = 1 from rfl, Nat.one_mul] at heq ⊢
      rw [(hsync _ (hidx_lt w₁ h₁) (by simpa only [hidx_fst w₁ h₁] using hidx_g w₁ h₁)).1,
        (hsync _ (hidx_lt w₂ h₂) (by simpa only [hidx_fst w₂ h₂] using hidx_g w₂ h₂)).1, heq]
  · exact hproj_perm 2 fun w₁ h₁ w₂ h₂ heq => by
      simp only [coordProj, show (2 : Fin 3).val = 2 from rfl] at heq ⊢
      rw [(hsync _ (hidx_lt w₁ h₁) (by simpa only [hidx_fst w₁ h₁] using hidx_g w₁ h₁)).2,
        (hsync _ (hidx_lt w₂ h₂) (by simpa only [hidx_fst w₂ h₂] using hidx_g w₂ h₂)).2, heq]

/-! ### Forward direction: 3DM implies 3-Partition -/

private theorem eq_of_nodup_map_tp {α β : Type*} {f : α → β} {l : List α} (h : (l.map f).Nodup)
    {a b : α} (ha : a ∈ l) (hb : b ∈ l) (hfab : f a = f b) : a = b := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha; obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hb
  have hget : (l.map f)[i]'(by simpa using hi) = (l.map f)[j]'(by simpa using hj) := by
    simp only [List.getElem_map]; exact hfab
  have hij : i = j := (List.Nodup.getElem_inj_iff h).mp hget
  subst hij; rfl

private theorem length_filter_range_getD_tp {α : Type*} (l : List α) (d : α) (p : α → Bool) :
    ((List.range l.length).filter fun j => p (l.getD j d)).length = l.countP p := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.length_cons, List.range_succ_eq_map, List.filter_cons, List.filter_map,
      List.countP_cons, ← ih]
    simp only [List.getD_cons_zero, Function.comp_def, List.getD_cons_succ]; split <;> simp

private theorem mem_gadget_of_ThreeDM {inst : ThreeDMInstance}
    (hv : validThreeDMCheck inst = true) (h3dm : inst ∈ ThreeDM) :
    ⟨gadgetNumbers inst, 3 * inst.triples.length,
      gadgetTarget inst.size inst.triples.length⟩ ∈ ThreePartition := by
  classical
  obtain ⟨hq, hk, hbounds, -⟩ := (validThreeDMCheck_iff inst).mp hv
  obtain ⟨-, M, hM⟩ := mem_ThreeDM_iff.mp h3dm
  set q := inst.size; set k := inst.triples.length
  set S := (itemList inst).toFinset
  have hS_mem : ∀ x, x ∈ S ↔ x ∈ itemList inst := fun _ => List.mem_toFinset
  let selIdx : Finset ℕ := (M.map fun t => inst.triples.idxOf t).toFinset
  have hsel_lt : ∀ i ∈ selIdx, i < k := fun i hi => by
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hi)
    exact List.idxOf_lt_length_of_mem (hM.subset_triples t ht)
  have hperm_coord : ∀ c : Fin 3, (M.map (coordProj c)).Perm (List.range q) := fun c => by
    rcases c with ⟨_ | _ | _ | _, hc⟩
    exacts [hM.perm_fst, hM.perm_snd_fst, hM.perm_snd_snd, by omega]
  have hsel_uniq : ∀ (c : Fin 3) (v : ℕ), v < q →
      ∃! i, i ∈ selIdx ∧ coordProj c (inst.triples.getD i (0, 0, 0)) = v := by
    intro c v hvlt
    obtain ⟨t, htM, hft⟩ :=
      List.mem_map.mp ((hperm_coord c).symm.subset (List.mem_range.mpr hvlt))
    have hti := List.idxOf_lt_length_of_mem (hM.subset_triples t htM)
    refine ⟨inst.triples.idxOf t, ⟨List.mem_toFinset.mpr (List.mem_map.mpr ⟨t, htM, rfl⟩),
      by rw [List.getD_eq_getElem _ _ hti, List.getElem_idxOf hti, hft]⟩, ?_⟩
    rintro i ⟨hi_sel, hfi⟩
    obtain ⟨t', ht'M, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hi_sel)
    have hti' := List.idxOf_lt_length_of_mem (hM.subset_triples t' ht'M)
    rw [List.getD_eq_getElem _ _ hti', List.getElem_idxOf hti'] at hfi
    rw [eq_of_nodup_map_tp ((hperm_coord c).nodup_iff.mpr List.nodup_range) ht'M htM
      (hfi.trans hft.symm)]
  let realIdx (c : Fin 3) (v : ℕ) : ℕ := if hvlt : v < q then (hsel_uniq c v hvlt).choose else 0
  have hreal_spec : ∀ (c : Fin 3) (v : ℕ) (hvlt : v < q),
      realIdx c v ∈ selIdx ∧ coordProj c (inst.triples.getD (realIdx c v) (0, 0, 0)) = v :=
    fun c v hvlt => by
      simp only [realIdx, hvlt, ↓reduceDIte]; exact (hsel_uniq c v hvlt).choose_spec.1
  have hreal_uniq : ∀ (c : Fin 3) (v : ℕ) (hvlt : v < q) (i : ℕ),
      i ∈ selIdx → coordProj c (inst.triples.getD i (0, 0, 0)) = v → i = realIdx c v :=
    fun c v hvlt i h1 h2 => by
      simp only [realIdx, hvlt, ↓reduceDIte]; exact (hsel_uniq c v hvlt).choose_spec.2 i ⟨h1, h2⟩
  let dummy (c : Fin 3) (v : ℕ) : List ℕ :=
    (List.range k).filter fun i =>
      decide (i ∉ selIdx ∧ coordProj c (inst.triples.getD i (0, 0, 0)) = v)
  have hdummy_len : ∀ (c : Fin 3) (v : ℕ) (hvlt : v < q),
      (dummy c v).length = coordCount inst.triples c v - 1 := by
    intro c v hvlt
    let allV := (List.range k).filter fun i => coordProj c (inst.triples.getD i (0, 0, 0)) == v
    have hall_len : allV.length = coordCount inst.triples c v :=
      length_filter_range_getD_tp inst.triples (0, 0, 0) fun t => coordProj c t == v
    have hset : allV.toFinset = insert (realIdx c v) (dummy c v).toFinset := by
      ext i
      simp only [allV, dummy, List.mem_toFinset, List.mem_filter, List.mem_range, beq_iff_eq,
        decide_eq_true_eq, Finset.mem_insert]
      exact ⟨fun ⟨hi, hfi⟩ => if his : i ∈ selIdx then Or.inl (hreal_uniq c v hvlt i his hfi)
        else Or.inr ⟨hi, his, hfi⟩,
        fun h => h.elim (fun he => he ▸ ⟨hsel_lt _ (hreal_spec c v hvlt).1,
          (hreal_spec c v hvlt).2⟩) fun ⟨hi, _, hfi⟩ => ⟨hi, hfi⟩⟩
    have hcard := congrArg Finset.card hset
    rw [Finset.card_insert_of_notMem (by simp [dummy, (hreal_spec c v hvlt).1]),
      List.toFinset_card_of_nodup (List.nodup_range.filter _),
      List.toFinset_card_of_nodup (List.nodup_range.filter _)] at hcard
    change allV.length = (dummy c v).length + 1 at hcard; omega
  let g : Item → Fin (3 * k) := fun
    | .core i c _ =>
      if _ : i < k then ⟨3 * i + c.val, by have := c.isLt; omega⟩ else ⟨0, by omega⟩
    | .link i r =>
      if _ : i < k then
        if i ∈ selIdx then ⟨3 * i + r.val, by have := r.isLt; omega⟩
        else ⟨3 * i + (r.val + 2) % 3, by omega⟩
      else ⟨0, by omega⟩
    | .vertex u isReal copy =>
      if hu : u < 3 * q then
        let c : Fin 3 := ⟨u / q, div_lt_three hq hu⟩
        let i := if isReal then realIdx c (u % q) else (dummy c (u % q)).getD copy 0
        if _ : i < k then ⟨3 * i + c.val, by have := c.isLt; omega⟩ else ⟨0, by omega⟩
      else ⟨0, by omega⟩
  have hfiber : ∀ j : Fin (3 * k),
      (S.filter fun x => g x = j).card = 3 ∧
      (S.filter fun x => g x = j).sum (itemVal q k) = gadgetTarget q k := by
    intro j
    set i := j.val / 3; set c : Fin 3 := ⟨j.val % 3, Nat.mod_lt _ (by decide)⟩
    have hi : i < k := by have := j.isLt; omega
    have hj_eq : j = ⟨3 * i + c.val, by have := c.isLt; omega⟩ :=
      Fin.ext (by simp only [i, c]; omega)
    set t := inst.triples.getD i (0, 0, 0)
    have htb := hbounds t (by
      dsimp only [t]; rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi)
    have hvlt : coordProj c t < q := by
      have h0 : ∀ c₀ : Fin 3, coordProj c₀ t < q := fun c₀ => by
        rcases c₀ with ⟨_ | _ | _ | _, hc₀⟩
        exacts [htb.1, htb.2.1, htb.2.2, by omega]
      exact h0 c
    let u_c : ℕ := c.val * q + coordProj c t
    let r_c : Fin 3 := if i ∈ selIdx then c else ⟨(c.val + 1) % 3, Nat.mod_lt _ (by decide)⟩
    let copy_c : ℕ := if i ∈ selIdx then 0 else (dummy c (coordProj c t)).idxOf i
    have hF_eq : S.filter (fun x => g x = j) =
        {Item.core i c u_c, Item.link i r_c, Item.vertex u_c (decide (i ∈ selIdx)) copy_c} := by
      ext x; simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨hxS, hgx⟩
        have hxL := List.mem_toFinset.mp hxS
        cases x with
        | core i' c' u' =>
          obtain ⟨hi'0, hu'⟩ := core_mem_itemList_iff.mp hxL
          have hi' : i' < k := hi'0
          have hval := congrArg Fin.val hgx
          dsimp only [g] at hval; rw [hj_eq] at hval; simp only [hi', ↓reduceDIte] at hval
          have hii' : i' = i := by have := c'.isLt; have := c.isLt; omega
          have hcc' : c' = c := Fin.ext (by have := c'.isLt; have := c.isLt; omega)
          subst hii'; subst hcc'; exact Or.inl (congrArg (Item.core i c) hu')
        | link i' r' =>
          have hi' : i' < k := link_mem_itemList_iff.mp hxL
          have hval := congrArg Fin.val hgx
          dsimp only [g] at hval; rw [hj_eq] at hval; simp only [hi', ↓reduceDIte] at hval
          have hval' : 3 * i' + (if i' ∈ selIdx then r'.val else (r'.val + 2) % 3) =
              3 * i + c.val := by split_ifs at hval ⊢ <;> exact hval
          have hii' : i' = i := by have := r'.isLt; have := c.isLt; split_ifs at hval' <;> omega
          subst hii'; refine Or.inr (Or.inl (congrArg (Item.link i) ?_))
          dsimp only [r_c]; split_ifs at hval' ⊢ with his
          · exact Fin.ext (by omega)
          · exact Fin.ext (by dsimp; have := r'.isLt; have := c.isLt; omega)
        | vertex u' isReal copy' =>
          have hu' : u' < 3 * q := itemValid_of_mem_itemList hv hxL
          set c' : Fin 3 := ⟨u' / q, div_lt_three hq hu'⟩; set v' := u' % q
          have hv'lt : v' < q := Nat.mod_lt u' hq
          have hu'_decomp : u' = c'.val * q + v' := by
            have := Nat.div_add_mod u' q; simp only [c', v']; nlinarith
          have hmem_v := (vertex_mem_itemList_iff (c := c') hv'lt).mp (hu'_decomp ▸ hxL)
          set i' := if isReal then realIdx c' v' else (dummy c' v').getD copy' 0
          have hi'_lt : i' < k := by
            rcases hmem_v with ⟨rfl, _⟩ | ⟨rfl, hcp⟩
            · exact hsel_lt _ (hreal_spec c' v' hv'lt).1
            · rw [← hdummy_len c' v' hv'lt] at hcp
              simp only [i', Bool.false_eq_true, ↓reduceIte, List.getD_eq_getElem _ _ hcp]
              exact List.mem_range.mp (List.mem_filter.mp (List.getElem_mem hcp)).1
          have hval : 3 * i' + c'.val = 3 * i + c.val := by
            have h1 := congrArg Fin.val hgx; dsimp only [g] at h1; rw [hj_eq] at h1
            simp only [hu', ↓reduceDIte] at h1
            have hi'_lt' : (if isReal = true then realIdx ⟨u' / q, div_lt_three hq hu'⟩ (u' % q)
                else (dummy ⟨u' / q, div_lt_three hq hu'⟩ (u' % q)).getD copy' 0) < k := hi'_lt
            simp only [hi'_lt', ↓reduceDIte] at h1; exact h1
          have hii' : i' = i := by have := c'.isLt; have := c.isLt; omega
          have hcc' : c' = c := Fin.ext (by have := c'.isLt; have := c.isLt; omega)
          right; right
          rcases hmem_v with ⟨rfl, rfl⟩ | ⟨rfl, hcp⟩
          · have hreal_i : realIdx c' v' = i := by simpa [i'] using hii'
            have his : i ∈ selIdx := hreal_i ▸ (hreal_spec c' v' hv'lt).1
            have hv'eq : v' = coordProj c t := by
              dsimp only [t]; rw [← hcc', ← hreal_i]; exact (hreal_spec c' v' hv'lt).2.symm
            simp [u_c, copy_c, his, hu'_decomp, hv'eq, hcc']
          · rw [← hdummy_len c' v' hv'lt] at hcp
            have hi_eq : (dummy c' v')[copy']'hcp = i := by
              rw [← List.getD_eq_getElem _ _ hcp]; simpa [i'] using hii'
            have himem : i ∈ dummy c' v' := hi_eq ▸ List.getElem_mem hcp
            dsimp only [dummy] at himem
            obtain ⟨hnsel, hproj⟩ := of_decide_eq_true (List.mem_filter.mp himem).2
            have hv'eq : v' = coordProj c t := by rw [← hcc']; exact hproj.symm
            have hcp_eq : copy' = (dummy c (coordProj c t)).idxOf i := by
              rw [← hcc', hproj, ← hi_eq]
              have hnd : (dummy c' v').Nodup := List.nodup_range.filter _
              symm; simp [hnd.idxOf_getElem]
            simp [u_c, copy_c, hnsel, hu'_decomp, hv'eq, hcp_eq, hcc']
      · rintro (rfl | rfl | rfl)
        · exact ⟨(hS_mem _).mpr (core_mem_itemList_iff.mpr ⟨hi, rfl⟩),
            by dsimp only [g]; rw [hj_eq]; simp only [hi, ↓reduceDIte]⟩
        · refine ⟨(hS_mem _).mpr (link_mem_itemList_iff.mpr hi), ?_⟩
          dsimp only [g, r_c]; rw [hj_eq]; simp only [hi, ↓reduceDIte]
          split_ifs with his
          · rfl
          · exact Fin.ext (by dsimp; have := c.isLt; omega)
        · have hu_lt : u_c < 3 * q := by have := c.isLt; dsimp [u_c]; nlinarith
          have hdiv : u_c / q = c.val := div_block hq hvlt
          have hmod : u_c % q = coordProj c t := mod_block hq hvlt
          have hc_eq : (⟨u_c / q, div_lt_three hq hu_lt⟩ : Fin 3) = c := Fin.ext hdiv
          have hpair : Item.vertex u_c (decide (i ∈ selIdx)) copy_c ∈ S ∧
              (if decide (i ∈ selIdx) = true then
                realIdx ⟨u_c / q, div_lt_three hq hu_lt⟩ (u_c % q)
              else (dummy ⟨u_c / q, div_lt_three hq hu_lt⟩ (u_c % q)).getD copy_c 0) = i := by
            rw [hc_eq, hmod]
            by_cases his : i ∈ selIdx
            · exact ⟨(hS_mem _).mpr ((vertex_mem_itemList_iff (c := c) hvlt).mpr
                (Or.inl ⟨by simp [his], by simp [copy_c, his]⟩)), by
                  simp only [his, decide_true, ↓reduceIte]
                  exact (hreal_uniq c _ hvlt i his rfl).symm⟩
            · have himem : i ∈ dummy c (coordProj c t) :=
                List.mem_filter.mpr ⟨List.mem_range.mpr hi, decide_eq_true ⟨his, rfl⟩⟩
              have hcp : (dummy c (coordProj c t)).idxOf i <
                  coordCount inst.triples c (coordProj c t) - 1 := by
                rw [← hdummy_len c (coordProj c t) hvlt]; exact List.idxOf_lt_length_of_mem himem
              exact ⟨(hS_mem _).mpr ((vertex_mem_itemList_iff (c := c) hvlt).mpr
                (Or.inr ⟨by simp [his], by simp [copy_c, his, hcp]⟩)), by
                  simp only [his, decide_false, Bool.false_eq_true, ↓reduceIte, copy_c,
                    List.getD_eq_getElem _ _ (List.idxOf_lt_length_of_mem himem),
                    List.getElem_idxOf (List.idxOf_lt_length_of_mem himem)]⟩
          refine ⟨hpair.1, Fin.ext ?_⟩
          have hi' : (if decide (i ∈ selIdx) = true then
              realIdx ⟨u_c / q, div_lt_three hq hu_lt⟩ (u_c % q)
            else (dummy ⟨u_c / q, div_lt_three hq hu_lt⟩ (u_c % q)).getD copy_c 0) < k :=
            hpair.2.symm ▸ hi
          dsimp only [g]; rw [hj_eq]; simp only [hu_lt, hi', ↓reduceDIte]
          exact congrArg₂ (· + ·) (congrArg (3 * ·) hpair.2) hdiv
    refine ⟨by rw [hF_eq, Finset.card_insert_of_notMem (by simp),
        Finset.card_insert_of_notMem (by simp), Finset.card_singleton], ?_⟩
    rw [hF_eq, Finset.sum_insert (by simp), Finset.sum_insert (by simp), Finset.sum_singleton]
    simp only [itemVal, gadgetTarget, u_c, r_c]
    have hsubk : i * gadgetBase2 q + (k - 1 - i) * gadgetBase2 q = (k - 1) * gadgetBase2 q := by
      rw [← Nat.add_mul, Nat.add_comm, Nat.sub_add_cancel (by omega)]
    have hsubu : (3 * q - 1 - (c.val * q + coordProj c t)) * gadgetBase1 +
        (c.val * q + coordProj c t) * gadgetBase1 = (3 * q - 1) * gadgetBase1 := by
      have hle : c.val * q + coordProj c t ≤ 3 * q - 1 := by
        have := c.isLt; have : c.val * q + coordProj c t + 1 ≤ 3 * q := by nlinarith
        omega
      rw [← Nat.add_mul, Nat.sub_add_cancel hle]
    have hdigits : (if c = 1 then 7 else 8) + r_c.val +
        (if u_c < 2 * q then (if decide (i ∈ selIdx) then 2 else 1)
         else (if decide (i ∈ selIdx) then 0 else 2)) = 10 := by
      have h0 : ∀ (c₀ : Fin 3) (v₀ : ℕ), v₀ < q → (if c₀ = 1 then 7 else 8) +
          (if i ∈ selIdx then c₀ else ⟨(c₀.val + 1) % 3, Nat.mod_lt _ (by decide)⟩).val +
          (if c₀.val * q + v₀ < 2 * q then (if decide (i ∈ selIdx) then 2 else 1)
           else (if decide (i ∈ selIdx) then 0 else 2)) = 10 := fun c₀ v₀ hv₀ => by
        rcases c₀ with ⟨_ | _ | _ | _, hc₀⟩
        · by_cases his : i ∈ selIdx <;> simp [his, show v₀ < 2 * q by omega]
        · by_cases his : i ∈ selIdx <;> simp [his, show q + v₀ < 2 * q by omega]
        · by_cases his : i ∈ selIdx <;>
            simp [Fin.ext_iff, his, show ¬(2 * q + v₀ < 2 * q) by omega]
        · omega
      exact h0 c (coordProj c t) hvlt
    dsimp only [u_c, r_c] at hdigits; linarith
  refine ⟨⟨show 0 < 3 * k by omega, ?_, ?_, ?_⟩, ?_⟩
  · rw [gadgetNumbers_eq_map_itemList, List.length_map,
      ← List.toFinset_card_of_nodup (nodup_itemList inst)]
    change S.card = 3 * (3 * k)
    rw [Finset.card_eq_sum_card_fiberwise (f := g) (t := Finset.univ)
      (fun _ _ => Finset.mem_univ _), Finset.sum_congr rfl fun j _ => (hfiber j).1]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]; ring
  · rw [gadgetNumbers_eq_map_itemList, ← List.sum_toFinset _ (nodup_itemList inst)]
    change S.sum (itemVal q k) = (3 * k) * gadgetTarget q k
    rw [← Finset.sum_fiberwise S g (itemVal q k), Finset.sum_congr rfl fun j _ => (hfiber j).2]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  · intro s hs; rw [gadgetNumbers_eq_map_itemList] at hs
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hs
    exact itemVal_bounds_of_itemValid hq hk (itemValid_of_mem_itemList hv hx)
  · rw [gadgetNumbers_eq_map_itemList]
    exact exists_isThreePartition_of_item_assign (nodup_itemList inst) (itemVal q k) g
      fun j => (hfiber j).2

/-! ### Fixed edge-case instances and full reduction correctness -/

private theorem yesInstance_mem : yesInstance ∈ ThreePartition :=
  ⟨⟨by decide, by decide, by decide, by decide⟩, fun _ => ⟨0, by decide⟩,
    isThreePartition_iff.mpr (by decide)⟩

private theorem noInstance_notMem : noInstance ∉ ThreePartition := by
  rintro ⟨hvalid, assign, hassign⟩
  let i5 : Fin noInstance.numbers.length := ⟨5, by decide⟩
  set F := Finset.univ.filter fun i => assign i = assign i5
  have h5 : i5 ∈ F := by simp [F]
  have hrest_card : (F.erase i5).card = 2 := by
    rw [Finset.card_erase_of_mem h5, fiber_card_eq_three hvalid hassign (assign i5)]
  have hsum_split : noInstance.numbers[i5] + ∑ i ∈ F.erase i5, noInstance.numbers[i] = 17 := by
    rw [Finset.add_sum_erase F (fun i => noInstance.numbers[i]) h5]; exact hassign (assign i5)
  have hnum5 : noInstance.numbers[i5] = 8 := rfl
  have hrest_ge : ∑ _i ∈ F.erase i5, (5 : ℕ) ≤ ∑ i ∈ F.erase i5, noInstance.numbers[i] :=
    Finset.sum_le_sum fun i _ => by
      rcases i with ⟨_ | _ | _ | _ | _ | _ | _, hi⟩ <;> simp [noInstance] at hi ⊢; omega
  rw [Finset.sum_const, smul_eq_mul, hrest_card] at hrest_ge; omega

/-- **Correctness of the strong NP-hardness reduction from `ThreeDM` to `ThreePartition`.** -/
theorem toThreePartition_mem_iff (inst : ThreeDMInstance) :
    toThreePartition inst ∈ ThreePartition ↔ inst ∈ ThreeDM := by
  unfold toThreePartition
  by_cases hzero : (inst.size == 0 && inst.triples.isEmpty) = true
  · simp only [hzero, ↓reduceIte]
    have hs : inst.size = 0 := by simpa using (Bool.and_eq_true _ _ |>.mp hzero).1
    have ht : inst.triples = [] := List.isEmpty_iff.mp (Bool.and_eq_true _ _ |>.mp hzero).2
    refine iff_of_true yesInstance_mem (mem_ThreeDM_iff.mpr ⟨by simp [ht], [], ?_⟩)
    rw [isThreeDM_iff]; simp [hs, ht]
  · simp only [hzero, Bool.false_eq_true, ↓reduceIte]
    by_cases hv : validThreeDMCheck inst = true
    · simp only [hv, ↓reduceIte]; exact ⟨mem_ThreeDM_of_gadget hv, mem_gadget_of_ThreeDM hv⟩
    · simp only [hv, Bool.false_eq_true, ↓reduceIte]
      refine iff_of_false noInstance_notMem fun h3dm => ?_
      obtain ⟨hbounds, M, hM⟩ := mem_ThreeDM_iff.mp h3dm
      have hpos : 0 < inst.size := by
        by_contra h0; have hq0 : inst.size = 0 := by omega
        have hnil : inst.triples = [] := by
          cases htr : inst.triples with
          | nil => rfl
          | cons t ts => have := (hbounds t (htr ▸ List.mem_cons_self)).1; omega
        exact hzero (by simp [hq0, hnil])
      have hMlen := hM.length_eq
      obtain ⟨t₀, ht₀⟩ := List.exists_mem_of_length_pos (by omega : 0 < M.length)
      refine hv ((validThreeDMCheck_iff inst).mpr
        ⟨hpos, List.length_pos_of_mem (hM.subset_triples t₀ ht₀), hbounds, fun c u hu => ?_⟩)
      have hperm : (M.map (coordProj c)).Perm (List.range inst.size) := by
        rcases c with ⟨_ | _ | _ | _, hc⟩
        exacts [hM.perm_fst, hM.perm_snd_fst, hM.perm_snd_snd, by omega]
      obtain ⟨t, htM, htc⟩ := List.mem_map.mp (hperm.symm.subset (List.mem_range.mpr hu))
      exact List.countP_pos_iff.mpr ⟨t, hM.subset_triples t htM, by simp [htc]⟩

end ThreePartition

/-- `ThreePartition` belongs to NP under binary encoding. -/
theorem ThreePartition_mem_NP : ThreePartition ∈ NP encThreePartition := by
  refine mem_NP_of_check (p := 2 * Polynomial.X ^ 2 + Polynomial.X)
    (Decoder.list Decoder.unary) ThreePartition.computableInPolyTime_check ?_ ?_
  · intro inst g hcheck
    obtain ⟨hvalid, hglen, hglt, hgroups⟩ := (ThreePartition.check_iff inst g).mp hcheck
    refine ⟨hvalid, fun i => ⟨g[i.val]'(by omega), hglt _ (List.getElem_mem _)⟩, fun j => ?_⟩
    refine (Finset.sum_congr ?_ fun _ _ => rfl).trans (hgroups j)
    ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.ext_iff]
    rw [List.getD_eq_getElem g 0 (by omega)]
  · intro inst ⟨hvalid, assign, hassign⟩
    let g := List.ofFn fun i : Fin inst.numbers.length => (assign i).val
    refine ⟨g, (ThreePartition.check_iff inst g).mpr ⟨hvalid, by simp [g], ?_, ?_⟩, ?_⟩
    · intro j hj; obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hj; exact (assign i).isLt
    · intro j
      refine (Finset.sum_congr ?_ fun _ _ => rfl).trans (hassign j)
      ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.ext_iff]
      rw [List.getD_eq_getElem g 0 (by simp [g])]; simp [g]
    · have hle_len : inst.numbers.length ≤ (encThreePartition inst).length :=
        (length_le_length_encList encNat inst.numbers).trans
          (encThreePartition_numbers_length_le inst)
      have hglen : g.length = inst.numbers.length := by simp [g]
      have hbound : ∀ a ∈ g.map (fun a => 2 * (encUnary a).length + 1),
          a ≤ 2 * inst.numbers.length + 1 := fun a ha => by
        obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ha; obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hu
        have := (assign i).isLt; have := hvalid.length_eq
        simp only [encUnary_apply, List.length_replicate]; omega
      have hlen_enc : (encList encUnary g).length ≤
          inst.numbers.length * (2 * inst.numbers.length + 1) := by
        rw [length_encList]
        simpa [List.length_map, hglen] using ThreePartition.list_sum_le_mul hbound
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
        Polynomial.eval_ofNat, Polynomial.eval_X]; nlinarith

private theorem polyTimeReducible_ThreePartition_unary_binary :
    PolyTimeReducible encThreePartitionUnary encThreePartition ThreePartition ThreePartition :=
  ⟨id, ThreePartition.computableInPolyTime_id_unary_to_binary, fun _ => Iff.rfl⟩

/-- `ThreePartition` belongs to NP under unary encoding. -/
theorem ThreePartition_mem_NP_unary : ThreePartition ∈ NP encThreePartitionUnary :=
  polyTimeReducible_ThreePartition_unary_binary.mem_NP ThreePartition_mem_NP

/-- `ThreeDM` reduces to `ThreePartition` in polynomial time under unary encodings. -/
theorem polyTimeReducible_ThreeDM_ThreePartition_unary :
    PolyTimeReducible encThreeDM encThreePartitionUnary ThreeDM ThreePartition :=
  ⟨ThreePartition.toThreePartition, ThreePartition.computableInPolyTime_toThreePartition_unary,
    fun inst => (ThreePartition.toThreePartition_mem_iff inst).symm⟩

/-- **3-Partition is strongly NP-hard** (NP-hard under unary encoding). -/
theorem ThreePartition_npHard_unary : NPHard encThreePartitionUnary ThreePartition :=
  ThreeDM_npHard.trans polyTimeReducible_ThreeDM_ThreePartition_unary

/-- **3-Partition is strongly NP-complete** (NP-complete under unary encoding). -/
theorem ThreePartition_npComplete_unary : NPComplete encThreePartitionUnary ThreePartition :=
  ⟨ThreePartition_mem_NP_unary, ThreePartition_npHard_unary⟩

/-- `ThreePartition` is NP-hard under binary encoding. -/
theorem ThreePartition_npHard : NPHard encThreePartition ThreePartition :=
  ThreePartition_npHard_unary.trans polyTimeReducible_ThreePartition_unary_binary

/-- **3-Partition is NP-complete** under binary encoding. -/
theorem ThreePartition_npComplete : NPComplete encThreePartition ThreePartition :=
  ⟨ThreePartition_mem_NP, ThreePartition_npHard⟩

end Cslib.Complexity
