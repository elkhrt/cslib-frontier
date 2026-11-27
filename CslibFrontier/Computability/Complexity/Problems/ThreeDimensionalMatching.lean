module

public import CslibFrontier.Computability.Complexity.Classes.NP.Witness
public import CslibFrontier.Computability.Complexity.Problems.OneInThreeSAT.Reduction
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Length
import CslibFrontier.Logics.Propositional.CNF.PolyTime
import Mathlib.Data.List.GetD

/-!
# Three-Dimensional Matching

An instance of *3-Dimensional Matching* (`ThreeDM`) consists of a common cardinality `size`
for three disjoint sets `W`, `X`, `Y` (represented by `{0..., size - 1}`) and a list of
candidate triples `triples` in `W × X × Y`. It is a yes-instance when every candidate triple
lies in `{0..., size - 1}³` and some sublist `M` of `triples` covers every element of `W`,
`X`, and `Y` exactly once (`IsThreeDM`).

Instances are encoded in unary (`encThreeDM`) so that `ThreeDM` is NP-complete even with
unary coordinates, which makes subsequent reductions to strongly NP-complete numerical
problems direct.

Membership in NP (`ThreeDM_mem_NP`) selects a subset of `triples` via a mask witness and
verifies that each coordinate in `{0..., size - 1}` occurs exactly once. NP-hardness
(`ThreeDM_npHard`) reduces from positive exact-three exact-one satisfiability with at most
three occurrences per variable (`Cslib.Complexity.PositiveOneInExactThreeSATThree`) using
cyclic variable gadgets and garbage collection slots in the third coordinate.

## Main definitions

* `Cslib.Complexity.ThreeDMInstance`: an instance `(size, triples)` of 3-Dimensional Matching.
* `Cslib.Complexity.encThreeDM`: unary encoding of `ThreeDMInstance`.
* `Cslib.Complexity.IsThreeDM`: predicate for a valid 3-dimensional matching.
* `Cslib.Complexity.ThreeDM`: the 3-Dimensional Matching decision problem.
* `Cslib.Complexity.ThreeDM.reduce`: polynomial-time reduction from
  `PositiveOneInExactThreeSATThree` to `ThreeDM`.

## Main results

* `Cslib.Complexity.ThreeDM_mem_NP`: `ThreeDM` belongs to NP under `encThreeDM`.
* `Cslib.Complexity.ThreeDM.computableInPolyTime_reduce`: the reduction is polynomial-time.
* `Cslib.Complexity.ThreeDM.reduce_mem_iff`: correctness of the reduction.
* `Cslib.Complexity.polyTimeReducible_PositiveOneInExactThreeSATThree_ThreeDM`:
  polynomial-time reducibility from `PositiveOneInExactThreeSATThree` to `ThreeDM`.
* `Cslib.Complexity.ThreeDM_npHard`, `Cslib.Complexity.ThreeDM_npComplete`:
  `ThreeDM` is NP-complete under unary encoding.
-/

public section

namespace Cslib.Complexity

open Cslib.Complexity Cslib.Logic.PL Turing.MultiTapeTM ComputableInPolyTime

/-- An instance of 3-Dimensional Matching: a common cardinality `size` of three disjoint sets
`W`, `X`, `Y` (represented by `{0, ..., size - 1}`) and a list of candidate triples. -/
@[ext]
structure ThreeDMInstance where
  /-- The common size `q` of the three coordinate sets `{0, ..., q - 1}`. -/
  size : ℕ
  /-- The list of candidate triples `(w, x, y)`. -/
  triples : List (ℕ × ℕ × ℕ)
  deriving DecidableEq, Repr

/-- Unary encoding of a `ThreeDMInstance`: the size in unary paired with the framed list of
unary coordinate triples. -/
enc_structure encThreeDM : ThreeDMInstance where
  size : encUnary,
  triples : (encList (encPair encUnary (encPair encUnary encUnary)))

/-- A list `M` of triples is a 3-dimensional matching for `inst` if every triple of `M` belongs
to `inst.triples` and each of the three coordinate projections of `M` is a permutation of
`List.range inst.size`. -/
def IsThreeDM (inst : ThreeDMInstance) (M : List (ℕ × ℕ × ℕ)) : Prop :=
  (∀ t ∈ M, t ∈ inst.triples) ∧
  (M.map Prod.fst).Perm (List.range inst.size) ∧
  (M.map fun t => t.2.1).Perm (List.range inst.size) ∧
  (M.map fun t => t.2.2).Perm (List.range inst.size)

/-- Characterization of `IsThreeDM` by its defining conditions. -/
theorem isThreeDM_iff {inst : ThreeDMInstance} {M : List (ℕ × ℕ × ℕ)} :
    IsThreeDM inst M ↔
      (∀ t ∈ M, t ∈ inst.triples) ∧
      (M.map Prod.fst).Perm (List.range inst.size) ∧
      (M.map fun t => t.2.1).Perm (List.range inst.size) ∧
      (M.map fun t => t.2.2).Perm (List.range inst.size) :=
  Iff.rfl

/-- Every triple of a 3-dimensional matching belongs to the instance's candidate list. -/
theorem IsThreeDM.subset_triples {inst : ThreeDMInstance} {M : List (ℕ × ℕ × ℕ)}
    (h : IsThreeDM inst M) : ∀ t ∈ M, t ∈ inst.triples :=
  h.1

/-- The first-coordinate projection of a 3-dimensional matching permutes `List.range size`. -/
theorem IsThreeDM.perm_fst {inst : ThreeDMInstance} {M : List (ℕ × ℕ × ℕ)}
    (h : IsThreeDM inst M) : (M.map Prod.fst).Perm (List.range inst.size) :=
  h.2.1

/-- The second-coordinate projection of a 3-dimensional matching permutes `List.range size`. -/
theorem IsThreeDM.perm_snd_fst {inst : ThreeDMInstance} {M : List (ℕ × ℕ × ℕ)}
    (h : IsThreeDM inst M) : (M.map fun t => t.2.1).Perm (List.range inst.size) :=
  h.2.2.1

/-- The third-coordinate projection of a 3-dimensional matching permutes `List.range size`. -/
theorem IsThreeDM.perm_snd_snd {inst : ThreeDMInstance} {M : List (ℕ × ℕ × ℕ)}
    (h : IsThreeDM inst M) : (M.map fun t => t.2.2).Perm (List.range inst.size) :=
  h.2.2.2

/-- A 3-dimensional matching has length equal to `inst.size`. -/
theorem IsThreeDM.length_eq {inst : ThreeDMInstance} {M : List (ℕ × ℕ × ℕ)}
    (h : IsThreeDM inst M) : M.length = inst.size := by
  simpa only [List.length_map, List.length_range] using h.perm_fst.length_eq

private theorem nodup_of_map {α β : Type*} {f : α → β} {l : List α} (h : (l.map f).Nodup) :
    l.Nodup := by
  induction l with
  | nil => exact List.nodup_nil
  | cons a t ih =>
    rw [List.map_cons, List.nodup_cons] at h
    exact List.nodup_cons.mpr ⟨fun ha => h.1 (List.mem_map.mpr ⟨a, ha, rfl⟩), ih h.2⟩

private theorem eq_of_nodup_map {α β : Type*} {f : α → β} {l : List α} (h : (l.map f).Nodup)
    {a b : α} (ha : a ∈ l) (hb : b ∈ l) (hfab : f a = f b) : a = b := by
  induction l with
  | nil => simp at ha
  | cons x t ih =>
    rw [List.map_cons, List.nodup_cons] at h
    rcases List.mem_cons.mp ha with rfl | ha' <;> rcases List.mem_cons.mp hb with rfl | hb'
    · rfl
    · exact absurd (List.mem_map.mpr ⟨b, hb', hfab.symm⟩) h.1
    · exact absurd (List.mem_map.mpr ⟨a, ha', hfab⟩) h.1
    · exact ih h.2 ha' hb'

/-- A 3-dimensional matching is duplicate-free. -/
theorem IsThreeDM.nodup {inst : ThreeDMInstance} {M : List (ℕ × ℕ × ℕ)}
    (h : IsThreeDM inst M) : M.Nodup :=
  nodup_of_map (h.perm_fst.nodup_iff.mpr List.nodup_range)

/-- Every coordinate of a triple in a 3-dimensional matching is strictly less than `inst.size`. -/
theorem IsThreeDM.lt_size {inst : ThreeDMInstance} {M : List (ℕ × ℕ × ℕ)}
    (h : IsThreeDM inst M) {t : ℕ × ℕ × ℕ} (ht : t ∈ M) :
    t.1 < inst.size ∧ t.2.1 < inst.size ∧ t.2.2 < inst.size :=
  ⟨List.mem_range.mp (h.perm_fst.subset (List.mem_map.mpr ⟨t, ht, rfl⟩)),
   List.mem_range.mp (h.perm_snd_fst.subset (List.mem_map.mpr ⟨t, ht, rfl⟩)),
   List.mem_range.mp (h.perm_snd_snd.subset (List.mem_map.mpr ⟨t, ht, rfl⟩))⟩

private theorem count_range_eq (n u : ℕ) :
    (List.range n).count u = if u < n then 1 else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.count_append, ih]
    simp only [List.count_cons, List.count_nil, beq_iff_eq]
    split_ifs <;> omega

private theorem perm_range_iff_nodup_length_lt {l : List ℕ} {q : ℕ} :
    l.Perm (List.range q) ↔ l.Nodup ∧ l.length = q ∧ ∀ x ∈ l, x < q := by
  constructor
  · intro h
    exact ⟨h.nodup_iff.mpr List.nodup_range,
      h.length_eq.trans List.length_range,
      fun x hx => List.mem_range.mp (h.subset hx)⟩
  · rintro ⟨hnd, hlen, hlt⟩
    have hsub : l.toFinset ⊆ Finset.range q :=
      fun x hx => Finset.mem_range.mpr (hlt x (List.mem_toFinset.mp hx))
    have hcard : (Finset.range q).card ≤ l.toFinset.card := by
      rw [Finset.card_range, List.toFinset_card_of_nodup hnd, hlen]
    have heq := Finset.eq_of_subset_of_card_le hsub hcard
    refine (List.perm_ext_iff_of_nodup hnd List.nodup_range).mpr fun x => ?_
    rw [← List.mem_toFinset, heq, Finset.mem_range, List.mem_range]

private theorem perm_range_iff_count {l : List ℕ} {q : ℕ} :
    l.Perm (List.range q) ↔ (∀ x ∈ l, x < q) ∧ ∀ u < q, l.count u = 1 := by
  constructor
  · intro h
    refine ⟨fun x hx => List.mem_range.mp (h.subset hx), fun u hu => ?_⟩
    rw [List.perm_iff_count.mp h u, count_range_eq]
    simp [hu]
  · rintro ⟨hlt, hcnt⟩
    refine List.perm_iff_count.mpr fun u => ?_
    rw [count_range_eq]
    split_ifs with hu
    · exact hcnt u hu
    · exact List.count_eq_zero.mpr fun hm => hu (hlt u hm)

/-- Characterization of `IsThreeDM` in terms of duplicate-freeness, length, and coordinate
bounds. -/
theorem isThreeDM_iff_nodup {inst : ThreeDMInstance} {M : List (ℕ × ℕ × ℕ)} :
    IsThreeDM inst M ↔
      M.Nodup ∧
      (∀ t ∈ M, t ∈ inst.triples) ∧
      M.length = inst.size ∧
      (M.map Prod.fst).Nodup ∧
      (M.map fun t => t.2.1).Nodup ∧
      (M.map fun t => t.2.2).Nodup ∧
      ∀ t ∈ M, t.1 < inst.size ∧ t.2.1 < inst.size ∧ t.2.2 < inst.size := by
  constructor
  · intro h
    refine ⟨h.nodup, h.subset_triples, h.length_eq,
      (perm_range_iff_nodup_length_lt.mp h.perm_fst).1,
      (perm_range_iff_nodup_length_lt.mp h.perm_snd_fst).1,
      (perm_range_iff_nodup_length_lt.mp h.perm_snd_snd).1,
      fun t ht => h.lt_size ht⟩
  · rintro ⟨_, hsub, hlen, hnd1, hnd2, hnd3, hlt⟩
    refine ⟨hsub,
      perm_range_iff_nodup_length_lt.mpr
        ⟨hnd1, by simpa using hlen, fun x hx => by
          obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx; exact (hlt t ht).1⟩,
      perm_range_iff_nodup_length_lt.mpr
        ⟨hnd2, by simpa using hlen, fun x hx => by
          obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx; exact (hlt t ht).2.1⟩,
      perm_range_iff_nodup_length_lt.mpr
        ⟨hnd3, by simpa using hlen, fun x hx => by
          obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx; exact (hlt t ht).2.2⟩⟩

/-- **3-Dimensional Matching (3DM)**: instances whose candidate triples all lie in
`{0, ..., size - 1}³` and have a 3-dimensional matching. -/
def ThreeDM : Set ThreeDMInstance :=
  {inst | (∀ t ∈ inst.triples, t.1 < inst.size ∧ t.2.1 < inst.size ∧ t.2.2 < inst.size) ∧
    ∃ M, IsThreeDM inst M}

/-- Membership characterization for `ThreeDM`. -/
theorem mem_ThreeDM_iff {inst : ThreeDMInstance} :
    inst ∈ ThreeDM ↔
      (∀ t ∈ inst.triples, t.1 < inst.size ∧ t.2.1 < inst.size ∧ t.2.2 < inst.size) ∧
      ∃ M, IsThreeDM inst M :=
  Iff.rfl

namespace ThreeDM

/-! ### Membership in NP -/

private def check (x : ThreeDMInstance × List (ℕ × ℕ × ℕ)) : Bool :=
  (x.1.triples.all fun t =>
    decide (t.1 < x.1.size) && decide (t.2.1 < x.1.size) && decide (t.2.2 < x.1.size)) &&
  (List.range x.1.size).all (fun u => decide (x.2.countP (fun t => t.1 == u) = 1)) &&
  (List.range x.1.size).all (fun u => decide (x.2.countP (fun t => t.2.1 == u) = 1)) &&
  (List.range x.1.size).all (fun u => decide (x.2.countP (fun t => t.2.2 == u) = 1))

private theorem countP_eq_card_filter_toFinset {α : Type*} [DecidableEq α] {l : List α}
    (hl : l.Nodup) (f : α → ℕ) (u : ℕ) :
    l.countP (fun t => f t == u) = (l.toFinset.filter fun t => f t = u).card := by
  rw [List.countP_eq_length_filter,
    ← List.toFinset_card_of_nodup (hl.filter fun t => f t == u), List.toFinset_filter]
  simp

private theorem count_map_eq_card_filter_toFinset {α : Type*} [DecidableEq α] {l : List α}
    (hl : l.Nodup) (f : α → ℕ) (u : ℕ) :
    (l.map f).count u = (l.toFinset.filter fun t => f t = u).card := by
  have hlen : (l.map f).count u = (l.filter fun t => decide (f t = u)).length := by
    clear hl
    induction l with
    | nil => simp
    | cons a t ih =>
      rw [List.map_cons, List.count_cons, List.filter_cons, ih]
      simp only [beq_iff_eq]
      by_cases h : f a = u <;> simp [h]
  rw [hlen, ← List.toFinset_card_of_nodup (hl.filter fun t => decide (f t = u)),
    List.toFinset_filter]
  simp

private theorem check_iff (inst : ThreeDMInstance) (l : List (ℕ × ℕ × ℕ)) (hl : l.Nodup) :
    check (inst, l) = true ↔
      (∀ t ∈ inst.triples, t.1 < inst.size ∧ t.2.1 < inst.size ∧ t.2.2 < inst.size) ∧
      (∀ u < inst.size, (l.toFinset.filter fun t => t.1 = u).card = 1) ∧
      (∀ u < inst.size, (l.toFinset.filter fun t => t.2.1 = u).card = 1) ∧
      (∀ u < inst.size, (l.toFinset.filter fun t => t.2.2 = u).card = 1) := by
  simp only [check, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, List.mem_range,
    countP_eq_card_filter_toFinset hl, and_assoc]

private theorem computableInPolyTime_check :
    ComputableInPolyTime check
      (encPair encThreeDM (encList (encPair encUnary (encPair encUnary encUnary)))) encBool := by
  let encT : (ℕ × ℕ × ℕ) ↪ List Bool := encPair encUnary (encPair encUnary encUnary)
  let encIn : ThreeDMInstance × List (ℕ × ℕ × ℕ) ↪ List Bool :=
    encPair encThreeDM (encList encT)
  have htriples : ComputableInPolyTime (fun x : ThreeDMInstance × List (ℕ × ℕ × ℕ) => x.1.triples)
      encIn (encList encT) :=
    encThreeDM_triples_polyTime (fst encThreeDM (encList encT))
  have hsize : ComputableInPolyTime (fun x : ThreeDMInstance × List (ℕ × ℕ × ℕ) => x.1.size)
      encIn encUnary :=
    encThreeDM_size_polyTime (fst encThreeDM (encList encT))
  have hrange : ComputableInPolyTime
      (fun x : ThreeDMInstance × List (ℕ × ℕ × ℕ) => List.range x.1.size)
      encIn (encList encUnary) :=
    range.comp hsize
  have hbounds : ComputableInPolyTime
      (fun x : ThreeDMInstance × List (ℕ × ℕ × ℕ) =>
        x.1.triples.all fun t =>
          decide (t.1 < x.1.size) && decide (t.2.1 < x.1.size) && decide (t.2.2 < x.1.size))
      encIn encBool := by
    refine allWithInput htriples ?_
    have hs : ComputableInPolyTime (fun p : (ThreeDMInstance × List (ℕ × ℕ × ℕ)) × ℕ × ℕ × ℕ =>
        p.1.1.size) (encPair encIn encT) encUnary :=
      hsize.comp (fst encIn encT)
    have ht1 : ComputableInPolyTime (fun p : (ThreeDMInstance × List (ℕ × ℕ × ℕ)) × ℕ × ℕ × ℕ =>
        p.2.1) (encPair encIn encT) encUnary :=
      (snd encIn encT).fst'
    have ht2 : ComputableInPolyTime (fun p : (ThreeDMInstance × List (ℕ × ℕ × ℕ)) × ℕ × ℕ × ℕ =>
        p.2.2.1) (encPair encIn encT) encUnary :=
      (snd encIn encT).snd'.fst'
    have ht3 : ComputableInPolyTime (fun p : (ThreeDMInstance × List (ℕ × ℕ × ℕ)) × ℕ × ℕ × ℕ =>
        p.2.2.2) (encPair encIn encT) encUnary :=
      (snd encIn encT).snd'.snd'
    exact bool_and' (bool_and' (unary_lt' ht1 hs) (unary_lt' ht2 hs)) (unary_lt' ht3 hs)
  have hcnt1 : ComputableInPolyTime
      (fun x : ThreeDMInstance × List (ℕ × ℕ × ℕ) =>
        (List.range x.1.size).all fun u => decide (x.2.countP (fun t => t.1 == u) = 1))
      encIn encBool := by
    refine allWithInput hrange ?_
    have hcp : ComputableInPolyTime
        (fun p : (ThreeDMInstance × List (ℕ × ℕ × ℕ)) × ℕ =>
          p.1.2.countP fun t => t.1 == p.2)
        (encPair encIn encUnary) encUnary :=
      countPWithInput ((snd encThreeDM (encList encT)).comp (fst encIn encUnary))
        (unary_beq ((snd (encPair encIn encUnary) encT).fst')
          ((snd encIn encUnary).comp (fst (encPair encIn encUnary) encT)))
    exact decide_eq' hcp (const 1)
  have hcnt2 : ComputableInPolyTime
      (fun x : ThreeDMInstance × List (ℕ × ℕ × ℕ) =>
        (List.range x.1.size).all fun u => decide (x.2.countP (fun t => t.2.1 == u) = 1))
      encIn encBool := by
    refine allWithInput hrange ?_
    have hcp : ComputableInPolyTime
        (fun p : (ThreeDMInstance × List (ℕ × ℕ × ℕ)) × ℕ =>
          p.1.2.countP fun t => t.2.1 == p.2)
        (encPair encIn encUnary) encUnary :=
      countPWithInput ((snd encThreeDM (encList encT)).comp (fst encIn encUnary))
        (unary_beq ((snd (encPair encIn encUnary) encT).snd'.fst')
          ((snd encIn encUnary).comp (fst (encPair encIn encUnary) encT)))
    exact decide_eq' hcp (const 1)
  have hcnt3 : ComputableInPolyTime
      (fun x : ThreeDMInstance × List (ℕ × ℕ × ℕ) =>
        (List.range x.1.size).all fun u => decide (x.2.countP (fun t => t.2.2 == u) = 1))
      encIn encBool := by
    refine allWithInput hrange ?_
    have hcp : ComputableInPolyTime
        (fun p : (ThreeDMInstance × List (ℕ × ℕ × ℕ)) × ℕ =>
          p.1.2.countP fun t => t.2.2 == p.2)
        (encPair encIn encUnary) encUnary :=
      countPWithInput ((snd encThreeDM (encList encT)).comp (fst encIn encUnary))
        (unary_beq ((snd (encPair encIn encUnary) encT).snd'.snd')
          ((snd encIn encUnary).comp (fst (encPair encIn encUnary) encT)))
    exact decide_eq' hcp (const 1)
  exact bool_and' (bool_and' (bool_and' hbounds hcnt1) hcnt2) hcnt3

/-! ### Reduction from `PositiveOneInExactThreeSATThree` -/

/-- The variable at occurrence index `o` (clause `o / 3`, position `o % 3`) in `φ`. -/
def occVar (φ : CNF ℕ) (o : ℕ) : ℕ :=
  ((φ.getD (o / 3) []).getD (o % 3) (0, false)).1

/-- The occurrence indices in `{0, ..., 3 * φ.length - 1}` where variable `v` appears. -/
def varOccs (φ : CNF ℕ) (v : ℕ) : List ℕ :=
  (List.range (3 * φ.length)).filter fun o => occVar φ o == v

/-- The TRUE triples of a variable with occurrence list `O`: `(o, o, o / 3)` for each `o ∈ O`. -/
def trueTriples (O : List ℕ) : List (ℕ × ℕ × ℕ) :=
  O.map fun o => (o, o, o / 3)

/-- The FALSE triples of a variable with occurrence list `O` for a formula of `m` clauses:
`(O[j], O[(j + 1) % d], m + g)` for each `j < d` and garbage slot `g < 2 * m`. -/
def falseTriples (m : ℕ) (O : List ℕ) : List (ℕ × ℕ × ℕ) :=
  (List.range O.length).flatMap fun j =>
    (List.range (2 * m)).map fun g =>
      (O.getD j 0, O.getD ((j + 1) % O.length) 0, m + g)

/-- All candidate triples emitted for variable `v` in formula `φ`. -/
def varGadget (φ : CNF ℕ) (v : ℕ) : List (ℕ × ℕ × ℕ) :=
  trueTriples (varOccs φ v) ++ falseTriples φ.length (varOccs φ v)

/-- A fixed no-instance of `ThreeDM`: size 1 with no candidate triples. -/
def noInstance : ThreeDMInstance := ⟨1, []⟩

/-- The polynomial-time reduction from `PositiveOneInExactThreeSATThree` to `ThreeDM`. -/
def reduce (φ : CNF ℕ) : ThreeDMInstance :=
  if PositiveOneInExactThreeSATThree.syntaxCheck φ then
    ⟨3 * φ.length, φ.distinctVars.flatMap (varGadget φ)⟩
  else noInstance

private theorem computableInPolyTime_occVar :
    ComputableInPolyTime (fun p : CNF ℕ × ℕ => occVar p.1 p.2)
      (encPair encCNF encUnary) encNat := by
  unfold occVar
  have hdiv : ComputableInPolyTime (fun p : CNF ℕ × ℕ => p.2 / 3)
      (encPair encCNF encUnary) encUnary :=
    (unary_div_const 3).comp (snd encCNF encUnary)
  have hmod : ComputableInPolyTime (fun p : CNF ℕ × ℕ => p.2 % 3)
      (encPair encCNF encUnary) encUnary :=
    unary_mod' (snd encCNF encUnary) (const 3)
  have hclause : ComputableInPolyTime (fun p : CNF ℕ × ℕ => p.1.getD (p.2 / 3) [])
      (encPair encCNF encUnary) (encList (encPair encNat encBool)) :=
    listGetDWithInput (fst encCNF encUnary) hdiv []
  have hlit : ComputableInPolyTime
      (fun p : CNF ℕ × ℕ => (p.1.getD (p.2 / 3) []).getD (p.2 % 3) (0, false))
      (encPair encCNF encUnary) (encPair encNat encBool) :=
    listGetDWithInput hclause hmod (0, false)
  exact hlit.fst'

private theorem computableInPolyTime_varOccs :
    ComputableInPolyTime (fun p : CNF ℕ × ℕ => varOccs p.1 p.2)
      (encPair encCNF encNat) (encList encUnary) := by
  unfold varOccs
  have hlen : ComputableInPolyTime (fun p : CNF ℕ × ℕ => p.1.length)
      (encPair encCNF encNat) encUnary :=
    (length_list (encClause encNat)).comp (fst encCNF encNat)
  have hrange : ComputableInPolyTime (fun p : CNF ℕ × ℕ => List.range (3 * p.1.length))
      (encPair encCNF encNat) (encList encUnary) :=
    range.comp (unary_mul' (const 3) hlen)
  have hpred : ComputableInPolyTime (fun q : (CNF ℕ × ℕ) × ℕ => occVar q.1.1 q.2 == q.1.2)
      (encPair (encPair encCNF encNat) encUnary) encBool :=
    ComputableInPolyTime.beq
      (computableInPolyTime_occVar.comp
        (((fst encCNF encNat).comp (fst _ _)).prod (snd _ _)))
      ((snd encCNF encNat).comp (fst _ _))
  exact filterWithInput hrange hpred

private theorem computableInPolyTime_trueTriples :
    ComputableInPolyTime trueTriples (encList encUnary)
      (encList (encPair encUnary (encPair encUnary encUnary))) := by
  unfold trueTriples
  exact ComputableInPolyTime.map (id'.prod (id'.prod (unary_div_const 3)))

private theorem computableInPolyTime_falseTriples :
    ComputableInPolyTime (fun p : ℕ × List ℕ => falseTriples p.1 p.2)
      (encPair encUnary (encList encUnary))
      (encList (encPair encUnary (encPair encUnary encUnary))) := by
  unfold falseTriples
  let encP := encPair encUnary (encList encUnary)
  let encQ := encPair encP encUnary
  let encR := encPair encQ encUnary
  have hlenO : ComputableInPolyTime (fun p : ℕ × List ℕ => p.2.length) encP encUnary :=
    (length_list encUnary).comp (snd encUnary (encList encUnary))
  have houter : ComputableInPolyTime (fun p : ℕ × List ℕ => List.range p.2.length)
      encP (encList encUnary) :=
    range.comp hlenO
  have hinner : ComputableInPolyTime (fun q : (ℕ × List ℕ) × ℕ => List.range (2 * q.1.1))
      encQ (encList encUnary) :=
    range.comp (unary_mul' (const 2) ((fst encUnary (encList encUnary)).comp (fst encP encUnary)))
  have hO : ComputableInPolyTime (fun r : ((ℕ × List ℕ) × ℕ) × ℕ => r.1.1.2)
      encR (encList encUnary) :=
    (snd encUnary (encList encUnary)).comp ((fst encP encUnary).comp (fst encQ encUnary))
  have hj : ComputableInPolyTime (fun r : ((ℕ × List ℕ) × ℕ) × ℕ => r.1.2)
      encR encUnary :=
    (snd encP encUnary).comp (fst encQ encUnary)
  have hm : ComputableInPolyTime (fun r : ((ℕ × List ℕ) × ℕ) × ℕ => r.1.1.1)
      encR encUnary :=
    (fst encUnary (encList encUnary)).comp ((fst encP encUnary).comp (fst encQ encUnary))
  have hg : ComputableInPolyTime (fun r : ((ℕ × List ℕ) × ℕ) × ℕ => r.2)
      encR encUnary :=
    snd encQ encUnary
  have hfirst : ComputableInPolyTime
      (fun r : ((ℕ × List ℕ) × ℕ) × ℕ => r.1.1.2.getD r.1.2 0) encR encUnary :=
    listGetDWithInput hO hj 0
  have hnextIdx : ComputableInPolyTime
      (fun r : ((ℕ × List ℕ) × ℕ) × ℕ => (r.1.2 + 1) % r.1.1.2.length) encR encUnary :=
    unary_mod' (unary_add' hj (const 1)) ((length_list encUnary).comp hO)
  have hsecond : ComputableInPolyTime
      (fun r : ((ℕ × List ℕ) × ℕ) × ℕ => r.1.1.2.getD ((r.1.2 + 1) % r.1.1.2.length) 0)
      encR encUnary :=
    listGetDWithInput hO hnextIdx 0
  have hthird : ComputableInPolyTime
      (fun r : ((ℕ × List ℕ) × ℕ) × ℕ => r.1.1.1 + r.2) encR encUnary :=
    unary_add' hm hg
  exact flatMapWithInput houter (mapWithInput hinner (hfirst.prod (hsecond.prod hthird)))

private theorem computableInPolyTime_varGadget :
    ComputableInPolyTime (fun p : CNF ℕ × ℕ => varGadget p.1 p.2)
      (encPair encCNF encNat)
      (encList (encPair encUnary (encPair encUnary encUnary))) := by
  unfold varGadget
  have hlen : ComputableInPolyTime (fun p : CNF ℕ × ℕ => p.1.length)
      (encPair encCNF encNat) encUnary :=
    (length_list (encClause encNat)).comp (fst encCNF encNat)
  exact listAppend'
    (computableInPolyTime_trueTriples.comp computableInPolyTime_varOccs)
    (computableInPolyTime_falseTriples.comp (hlen.prod computableInPolyTime_varOccs))

/-- The reduction from `PositiveOneInExactThreeSATThree` to `ThreeDM` is computable in
polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_reduce : ComputableInPolyTime reduce encCNF encThreeDM := by
  unfold reduce
  have hsize : ComputableInPolyTime (fun φ : CNF ℕ => 3 * φ.length) encCNF encUnary :=
    unary_mul' (const 3) (length_list (encClause encNat))
  have htriples : ComputableInPolyTime (fun φ : CNF ℕ => φ.distinctVars.flatMap (varGadget φ))
      encCNF (encList (encPair encUnary (encPair encUnary encUnary))) :=
    flatMapWithInput (CNF.computableInPolyTime_distinctVars encNat)
      computableInPolyTime_varGadget
  exact PositiveOneInExactThreeSATThree.computableInPolyTime_syntaxCheck.ite
    (encThreeDM_mk_polyTime hsize htriples) (const noInstance)

/-! ### Structural properties of the reduction -/

private theorem mem_varOccs {φ : CNF ℕ} {v o : ℕ} :
    o ∈ varOccs φ v ↔ o < 3 * φ.length ∧ occVar φ o = v := by
  simp [varOccs]

private theorem nodup_varOccs (φ : CNF ℕ) (v : ℕ) : (varOccs φ v).Nodup :=
  List.nodup_range.filter _

private theorem occVar_eq {φ : CNF ℕ}
    (hcl : ∀ c ∈ φ, c.length = 3 ∧ (c.map Prod.fst).Nodup)
    {o i p : ℕ} (hi : i < φ.length) (hp : p < 3) (ho : o = 3 * i + p) :
    occVar φ o = (φ[i][p]'(by rw [(hcl _ (List.getElem_mem hi)).1]; exact hp)).1 := by
  subst ho
  have hdiv : (3 * i + p) / 3 = i := by omega
  have hmod : (3 * i + p) % 3 = p := by omega
  have hp' : p < φ[i].length := by rw [(hcl _ (List.getElem_mem hi)).1]; exact hp
  simp only [occVar, hdiv, hmod, List.getD_eq_getElem φ [] hi]
  rw [List.getD_eq_getElem (φ[i]) (0, false) hp']

private theorem mem_distinctVars_of_occVar {φ : CNF ℕ}
    (hcl : ∀ c ∈ φ, c.length = 3 ∧ (c.map Prod.fst).Nodup) {o : ℕ} (ho : o < 3 * φ.length) :
    occVar φ o ∈ φ.distinctVars := by
  have hi : o / 3 < φ.length := by omega
  have hp : o % 3 < 3 := by omega
  have hlen : φ[o / 3].length = 3 := (hcl _ (List.getElem_mem hi)).1
  rw [occVar_eq hcl hi hp (by omega), CNF.mem_distinctVars]
  exact CNF.mem_vars.mpr
    ⟨φ[o / 3], List.getElem_mem hi, (φ[o / 3][o % 3]'(by omega)).2, List.getElem_mem (by omega)⟩

private theorem one_le_length_varOccs {φ : CNF ℕ}
    (hcl : ∀ c ∈ φ, c.length = 3 ∧ (c.map Prod.fst).Nodup) {v : ℕ} (hv : v ∈ φ.distinctVars) :
    1 ≤ (varOccs φ v).length := by
  rw [CNF.mem_distinctVars] at hv
  obtain ⟨c, hc, b, hlb⟩ := CNF.mem_vars.mp hv
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc
  obtain ⟨p, hp, hlp⟩ := List.getElem_of_mem hlb
  have hcl3 : φ[i].length = 3 := (hcl _ (List.getElem_mem hi)).1
  have ho : 3 * i + p < 3 * φ.length := by omega
  have hocc : occVar φ (3 * i + p) = v := by
    rw [occVar_eq hcl hi (by omega) rfl, hlp]
  exact List.length_pos_of_mem (mem_varOccs.mpr ⟨ho, hocc⟩)

private theorem perm_flatten_varOccs {φ : CNF ℕ}
    (hcl : ∀ c ∈ φ, c.length = 3 ∧ (c.map Prod.fst).Nodup) :
    ((φ.distinctVars.map (varOccs φ)).flatten).Perm (List.range (3 * φ.length)) := by
  have hnd : ((φ.distinctVars.map (varOccs φ)).flatten).Nodup := by
    refine List.nodup_flatten.mpr ⟨by simp [nodup_varOccs], ?_⟩
    refine List.pairwise_map.mpr ((CNF.nodup_distinctVars φ).imp_of_mem fun {v w} _ _ hvw => ?_)
    refine List.disjoint_left.mpr fun o hvo hwo => hvw ?_
    exact (mem_varOccs.mp hvo).2.symm.trans (mem_varOccs.mp hwo).2
  refine (List.perm_ext_iff_of_nodup hnd List.nodup_range).mpr fun o => ?_
  rw [List.mem_flatten, List.mem_range]
  constructor
  · rintro ⟨O, hO, ho⟩
    obtain ⟨v, _, rfl⟩ := List.mem_map.mp hO
    exact (mem_varOccs.mp ho).1
  · intro ho
    exact ⟨varOccs φ (occVar φ o),
      List.mem_map.mpr ⟨occVar φ o, mem_distinctVars_of_occVar hcl ho, rfl⟩,
      mem_varOccs.mpr ⟨ho, rfl⟩⟩

private theorem mem_trueTriples {O : List ℕ} {t : ℕ × ℕ × ℕ} :
    t ∈ trueTriples O ↔ ∃ o ∈ O, t = (o, o, o / 3) := by
  simp only [trueTriples, List.mem_map, eq_comm]

private theorem mem_falseTriples {m : ℕ} {O : List ℕ} {t : ℕ × ℕ × ℕ} :
    t ∈ falseTriples m O ↔
      ∃ j < O.length, ∃ g < 2 * m,
        t = (O.getD j 0, O.getD ((j + 1) % O.length) 0, m + g) := by
  simp only [falseTriples, List.mem_flatMap, List.mem_map, List.mem_range, eq_comm]

private theorem reduce_of_syntaxCheck {φ : CNF ℕ}
    (hs : PositiveOneInExactThreeSATThree.syntaxCheck φ = true) :
    reduce φ = ⟨3 * φ.length, φ.distinctVars.flatMap (varGadget φ)⟩ := by
  simp [reduce, hs]

private theorem lt_size_of_mem_reduce {φ : CNF ℕ}
    (hs : PositiveOneInExactThreeSATThree.syntaxCheck φ = true)
    {t : ℕ × ℕ × ℕ} (ht : t ∈ (reduce φ).triples) :
    t.1 < 3 * φ.length ∧ t.2.1 < 3 * φ.length ∧ t.2.2 < 3 * φ.length := by
  obtain ⟨hcl, -, -⟩ := (PositiveOneInExactThreeSATThree.syntaxCheck_iff φ).mp hs
  rw [reduce_of_syntaxCheck hs] at ht
  obtain ⟨v, hv, htv⟩ := List.mem_flatMap.mp ht
  have hd : 1 ≤ (varOccs φ v).length := one_le_length_varOccs hcl hv
  rcases List.mem_append.mp htv with htr | hfl
  · obtain ⟨o, ho, rfl⟩ := mem_trueTriples.mp htr
    have hlt := (mem_varOccs.mp ho).1
    exact ⟨hlt, hlt, by dsimp only; omega⟩
  · obtain ⟨j, hj, g, hg, rfl⟩ := mem_falseTriples.mp hfl
    have hnext : (j + 1) % (varOccs φ v).length < (varOccs φ v).length :=
      Nat.mod_lt _ (by omega)
    rw [List.getD_eq_getElem _ _ hj, List.getD_eq_getElem _ _ hnext]
    exact ⟨(mem_varOccs.mp (List.getElem_mem hj)).1,
      (mem_varOccs.mp (List.getElem_mem hnext)).1, by dsimp only; omega⟩

/-! ### Correctness of the reduction -/

private theorem countP_eval_eq {σ : ℕ → Bool} {c : Clause ℕ} (hpos : ∀ l ∈ c, l.2 = true) :
    c.countP (Literal.eval σ) = (c.map Prod.fst).countP σ := by
  rw [List.countP_map]
  refine List.countP_congr fun l hl => ?_
  simp [Literal.eval, hpos l hl]

private theorem existsUnique_of_countP_eq_one {α : Type*} {l : List α} {p : α → Bool}
    (h : l.countP p = 1) : ∃ a ∈ l, p a = true ∧ ∀ b ∈ l, p b = true → b = a := by
  rw [List.countP_eq_length_filter] at h
  obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp h
  have hmem : ∀ x, x ∈ l ∧ p x = true ↔ x = a := fun x => by
    rw [← List.mem_filter, ha, List.mem_singleton]
  exact ⟨a, ((hmem a).mpr rfl).1, ((hmem a).mpr rfl).2, fun b hb hpb => (hmem b).mp ⟨hb, hpb⟩⟩

private theorem countP_eq_one_of_unique {l : List ℕ} {p : ℕ → Bool} {a : ℕ} (hl : l.Nodup)
    (ha : a ∈ l) (hpa : p a = true) (huniq : ∀ b ∈ l, p b = true → b = a) : l.countP p = 1 := by
  classical
  rw [List.countP_eq_length_filter, ← List.toFinset_card_of_nodup (hl.filter p)]
  refine Finset.card_eq_one.mpr ⟨a, Finset.ext fun b => ?_⟩
  simp only [List.mem_toFinset, List.mem_filter, Finset.mem_singleton]
  exact ⟨fun ⟨hb, hpb⟩ => huniq b hb hpb, fun h => h ▸ ⟨ha, hpa⟩⟩

/-- In any 3-dimensional matching of `reduce φ`, the occurrences of a variable `v` are either all
matched by TRUE triples (`t.2.2 < φ.length`) or all matched by FALSE triples
(`φ.length ≤ t.2.2`). -/
private theorem all_false_of_exists_false {φ : CNF ℕ}
    (hs : PositiveOneInExactThreeSATThree.syntaxCheck φ = true)
    {M : List (ℕ × ℕ × ℕ)} (hM : IsThreeDM (reduce φ) M)
    {v : ℕ} (hv : v ∈ φ.distinctVars) :
    ∀ (j : ℕ) (hj : j < (varOccs φ v).length),
      (∃ t ∈ M, t.1 = (varOccs φ v)[j] ∧ φ.length ≤ t.2.2) →
      ∀ (j' : ℕ) (hj' : j' < (varOccs φ v).length) (t' : ℕ × ℕ × ℕ),
        t' ∈ M → t'.1 = (varOccs φ v)[j'] → φ.length ≤ t'.2.2 := by
  obtain ⟨hcl, -, -⟩ := (PositiveOneInExactThreeSATThree.syntaxCheck_iff φ).mp hs
  set O := varOccs φ v
  set d := O.length
  have hd : 1 ≤ d := one_le_length_varOccs hcl hv
  have hOnd : O.Nodup := nodup_varOccs φ v
  have hMsub : ∀ t ∈ M, t ∈ φ.distinctVars.flatMap (varGadget φ) := by
    intro t ht
    have := hM.subset_triples t ht
    rwa [reduce_of_syntaxCheck hs] at this
  have hMnd2 : (M.map fun t => t.2.1).Nodup :=
    (perm_range_iff_nodup_length_lt.mp hM.perm_snd_fst).1
  -- Helper: any triple in `M` with first coordinate in `O` belongs to `varGadget φ v`.
  have hmem_v : ∀ {t : ℕ × ℕ × ℕ}, t ∈ M → t.1 ∈ O → t ∈ varGadget φ v := by
    intro t ht htO
    obtain ⟨w, _, htw⟩ := List.mem_flatMap.mp (hMsub t ht)
    have htw1 : t.1 ∈ varOccs φ w := by
      rcases List.mem_append.mp htw with htr | hfl
      · obtain ⟨o, ho, rfl⟩ := mem_trueTriples.mp htr; exact ho
      · obtain ⟨k, hk, _, _, rfl⟩ := mem_falseTriples.mp hfl
        rw [List.getD_eq_getElem _ _ hk]; exact List.getElem_mem hk
    have hwv : w = v := (mem_varOccs.mp htw1).2.symm.trans (mem_varOccs.mp htO).2
    exact hwv ▸ htw
  -- Single cyclic step: if `O[j]` is matched by a FALSE triple, so is `O[(j + 1) % d]`.
  have hstep : ∀ (j : ℕ) (hj : j < d),
      (∃ t ∈ M, t.1 = O[j] ∧ φ.length ≤ t.2.2) →
      ∀ (t' : ℕ × ℕ × ℕ), t' ∈ M → t'.1 = O[(j + 1) % d]'(Nat.mod_lt _ (by omega)) →
        φ.length ≤ t'.2.2 := by
    intro j hj ⟨t, htM, ht1, ht2⟩ t' ht'M ht'1
    have htv : t ∈ varGadget φ v := hmem_v htM (ht1 ▸ List.getElem_mem hj)
    have htfalse : t ∈ falseTriples φ.length O := by
      rcases List.mem_append.mp htv with htr | hfl
      · obtain ⟨o, ho, rfl⟩ := mem_trueTriples.mp htr
        have := (mem_varOccs.mp ho).1
        dsimp only at ht2; omega
      · exact hfl
    obtain ⟨j₀, hj₀, g, hg, ht_eq⟩ := mem_falseTriples.mp htfalse
    have hj₀j : j₀ = j := by
      have hget : O[j₀] = O[j] := by
        rw [← List.getD_eq_getElem O 0 hj₀]
        have : t.1 = O.getD j₀ 0 := by rw [ht_eq]
        exact this.symm.trans ht1
      exact (List.Nodup.getElem_inj_iff hOnd).mp hget
    have ht_snd : t.2.1 = O[(j + 1) % d]'(Nat.mod_lt _ (by omega)) := by
      rw [ht_eq, hj₀j, List.getD_eq_getElem O 0 (Nat.mod_lt _ (by omega))]
    by_contra hlt
    push Not at hlt
    have ht'v : t' ∈ varGadget φ v :=
      hmem_v ht'M (ht'1 ▸ List.getElem_mem (Nat.mod_lt _ (by omega)))
    have ht'true : t' ∈ trueTriples O := by
      rcases List.mem_append.mp ht'v with htr | hfl
      · exact htr
      · obtain ⟨_, _, g', _, ht'_eq⟩ := mem_falseTriples.mp hfl
        have : t'.2.2 = φ.length + g' := by rw [ht'_eq]
        omega
    obtain ⟨o', _, ht'_eq⟩ := mem_trueTriples.mp ht'true
    have ht'_snd : t'.2.1 = t'.1 := by rw [ht'_eq]
    have heq_tt' : t = t' := eq_of_nodup_map hMnd2 htM ht'M (by rw [ht_snd, ht'_snd, ht'1])
    rw [heq_tt'] at ht2
    omega
  -- Iterate `hstep` by induction on `r`.
  have hsz : (reduce φ).size = 3 * φ.length := by rw [reduce_of_syntaxCheck hs]
  have hiter : ∀ (j : ℕ) (hj : j < d),
      (∃ t ∈ M, t.1 = O[j] ∧ φ.length ≤ t.2.2) →
      ∀ (r : ℕ) (t' : ℕ × ℕ × ℕ), t' ∈ M →
        t'.1 = O[(j + r) % d]'(Nat.mod_lt _ (by omega)) → φ.length ≤ t'.2.2 := by
    intro j hj hex r
    induction r with
    | zero =>
      intro t' ht'M ht'1
      simp only [Nat.add_zero, Nat.mod_eq_of_lt hj] at ht'1
      obtain ⟨t, htM, ht1, ht2⟩ := hex
      have hMnd1 : (M.map Prod.fst).Nodup :=
        (perm_range_iff_nodup_length_lt.mp hM.perm_fst).1
      have := eq_of_nodup_map hMnd1 htM ht'M (ht1.trans ht'1.symm)
      exact this ▸ ht2
    | succ r ih =>
      intro t' ht'M ht'1
      have hkr : (j + r) % d < d := Nat.mod_lt _ (by omega)
      have hmem_kr : ∃ s ∈ M, s.1 = O[(j + r) % d]'hkr := by
        have hlt_s : O[(j + r) % d]'hkr < (reduce φ).size :=
          hsz ▸ (mem_varOccs.mp (List.getElem_mem hkr)).1
        have hmem_fst : O[(j + r) % d]'hkr ∈ M.map Prod.fst :=
          hM.perm_fst.symm.subset (List.mem_range.mpr hlt_s)
        obtain ⟨s, hsM, hs1⟩ := List.mem_map.mp hmem_fst
        exact ⟨s, hsM, hs1⟩
      obtain ⟨s, hsM, hs1⟩ := hmem_kr
      have hs2 := ih s hsM hs1
      have hmod_eq : ((j + r) % d + 1) % d = (j + (r + 1)) % d := by
        rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, Nat.add_assoc]
      exact hstep ((j + r) % d) hkr ⟨s, hsM, hs1, hs2⟩ t' ht'M (by simpa only [hmod_eq] using ht'1)
  intro j hj hex j' hj' t' ht'M ht'1
  have hmod : (j + (d - j + j')) % d = j' := by
    rw [show j + (d - j + j') = d + j' by omega, Nat.add_mod_left, Nat.mod_eq_of_lt hj']
  exact hiter j hj hex (d - j + j') t' ht'M (by simpa only [hmod] using ht'1)

/-- **3-dimensional matchings give exact-one assignments.** -/
private theorem oneSatisfiable_of_mem {φ : CNF ℕ}
    (hs : PositiveOneInExactThreeSATThree.syntaxCheck φ = true)
    (h : reduce φ ∈ ThreeDM) : φ.OneSatisfiable := by
  classical
  obtain ⟨hcl, hpos, -⟩ := (PositiveOneInExactThreeSATThree.syntaxCheck_iff φ).mp hs
  rw [OneSAT.positiveCheck_iff] at hpos
  obtain ⟨-, M, hM⟩ := h
  set m := φ.length with hm
  have hsz : (reduce φ).size = 3 * m := by rw [reduce_of_syntaxCheck hs]
  have hMsub : ∀ t ∈ M, t ∈ φ.distinctVars.flatMap (varGadget φ) := by
    intro t ht
    have := hM.subset_triples t ht
    rwa [reduce_of_syntaxCheck hs] at this
  have hMnd3 : (M.map fun t => t.2.2).Nodup :=
    (perm_range_iff_nodup_length_lt.mp hM.perm_snd_snd).1
  let σ : ℕ → Bool := fun v => decide (∃ t ∈ M, t.2.2 < m ∧ occVar φ t.1 = v)
  refine ⟨σ, ?_⟩
  simp only [CNF.evalOne, List.all_eq_true, Clause.evalOne, beq_iff_eq]
  intro c hc
  rw [countP_eval_eq (hpos c hc)]
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc
  have hcl3 : φ[i].length = 3 := (hcl _ hc).1
  -- Clause index `i < m < 3 * m` is covered in coordinate 3 by a unique triple `t₀ ∈ M`.
  have hi3 : i < (reduce φ).size := by omega
  obtain ⟨t₀, ht₀M, ht₀3⟩ : ∃ t₀ ∈ M, t₀.2.2 = i :=
    List.mem_map.mp (hM.perm_snd_snd.symm.subset (List.mem_range.mpr hi3))
  have ht₀lt : t₀.2.2 < m := by omega
  obtain ⟨v₀, hv₀, ht₀g⟩ := List.mem_flatMap.mp (hMsub t₀ ht₀M)
  have ht₀true : t₀ ∈ trueTriples (varOccs φ v₀) := by
    rcases List.mem_append.mp ht₀g with htr | hfl
    · exact htr
    · obtain ⟨_, _, g, _, ht₀_eq⟩ := mem_falseTriples.mp hfl
      have : t₀.2.2 = m + g := by rw [ht₀_eq]
      omega
  obtain ⟨o₀, ho₀, ht₀_eq⟩ := mem_trueTriples.mp ht₀true
  have ho₀_lt : o₀ < 3 * m := (mem_varOccs.mp ho₀).1
  have ho₀_var : occVar φ o₀ = v₀ := (mem_varOccs.mp ho₀).2
  have ho₀_div : o₀ / 3 = i := by
    have : t₀.2.2 = o₀ / 3 := by rw [ht₀_eq]
    omega
  have hv₀_mem : v₀ ∈ φ[i].map Prod.fst := by
    rw [← ho₀_var, occVar_eq hcl hi (by omega : o₀ % 3 < 3) (by omega)]
    exact List.mem_map.mpr ⟨φ[i][o₀ % 3]'(by omega), List.getElem_mem (by omega), rfl⟩
  have hσv₀ : σ v₀ = true :=
    decide_eq_true ⟨t₀, ht₀M, ht₀lt, by rw [ht₀_eq]; exact ho₀_var⟩
  refine countP_eq_one_of_unique (hcl _ hc).2 hv₀_mem hσv₀ fun v hv hσv => ?_
  obtain ⟨t', ht'M, ht'lt, ht'var⟩ := of_decide_eq_true hσv
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hv
  obtain ⟨p', hp', rfl⟩ := List.getElem_of_mem hl
  set o := 3 * i + p'
  have ho_lt : o < 3 * m := by omega
  have ho_div : o / 3 = i := by omega
  have ho_var : occVar φ o = (φ[i][p']).1 := occVar_eq hcl hi (by omega) rfl
  have hv_dv : (φ[i][p']).1 ∈ φ.distinctVars := by
    rw [← ho_var]; exact mem_distinctVars_of_occVar hcl ho_lt
  -- Obtain the triple `t_o ∈ M` covering `o` in coordinate 1.
  obtain ⟨t_o, ht_oM, ht_o1⟩ : ∃ t_o ∈ M, t_o.1 = o :=
    List.mem_map.mp (hM.perm_fst.symm.subset (List.mem_range.mpr (hsz ▸ ho_lt)))
  -- Since `t'.1` and `o` both belong to `varOccs φ (φ[i][p']).1` and `t'.2.2 < m`,
  -- `t_o` cannot have `t_o.2.2 ≥ m`.
  have ht_o_lt : t_o.2.2 < m := by
    by_contra hge
    push Not at hge
    have ho_mem : o ∈ varOccs φ (φ[i][p']).1 := mem_varOccs.mpr ⟨ho_lt, ho_var⟩
    obtain ⟨j, hj, hOj⟩ := List.getElem_of_mem ho_mem
    have ht'1_lt : t'.1 < 3 * m := hsz ▸ (hM.lt_size ht'M).1
    have ht'1_mem : t'.1 ∈ varOccs φ (φ[i][p']).1 := mem_varOccs.mpr ⟨ht'1_lt, ht'var⟩
    obtain ⟨j', hj', hOj'⟩ := List.getElem_of_mem ht'1_mem
    have := all_false_of_exists_false hs hM hv_dv j hj ⟨t_o, ht_oM, hOj.symm ▸ ht_o1, hge⟩
      j' hj' t' ht'M hOj'.symm
    omega
  -- Thus `t_o` is a TRUE triple, so `t_o.2.2 = o / 3 = i = t₀.2.2`, forcing `t_o = t₀`.
  obtain ⟨w, _, ht_og⟩ := List.mem_flatMap.mp (hMsub t_o ht_oM)
  have ht_otrue : t_o ∈ trueTriples (varOccs φ w) := by
    rcases List.mem_append.mp ht_og with htr | hfl
    · exact htr
    · obtain ⟨_, _, g, _, ht_o_eq⟩ := mem_falseTriples.mp hfl
      have : t_o.2.2 = m + g := by rw [ht_o_eq]
      omega
  obtain ⟨o', _, ht_o_eq⟩ := mem_trueTriples.mp ht_otrue
  have ho'_eq : o' = o := by
    have : t_o.1 = o' := by rw [ht_o_eq]
    exact this.symm.trans ht_o1
  have ht_o3 : t_o.2.2 = i := by rw [ht_o_eq, ho'_eq, ho_div]
  have heq_t : t_o = t₀ := eq_of_nodup_map hMnd3 ht_oM ht₀M (ht_o3.trans ht₀3.symm)
  have ho_eq : o = o₀ := by
    have h1 : t_o.1 = t₀.1 := congrArg Prod.fst heq_t
    have h2 : t₀.1 = o₀ := by rw [ht₀_eq]
    omega
  rw [← ho_var, ho_eq, ho₀_var]

private theorem perm_cycle_succ (O : List ℕ) :
    ((List.range O.length).map fun j => O.getD ((j + 1) % O.length) 0).Perm O := by
  cases O with
  | nil => simp
  | cons a t =>
    have hlen : (a :: t).length = t.length + 1 := rfl
    rw [hlen, List.range_succ, List.map_append, List.map_singleton]
    have hlast : (a :: t).getD ((t.length + 1) % (t.length + 1)) 0 = a := by
      simp [Nat.mod_self]
    rw [hlast]
    have hinit :
        (List.range t.length).map (fun j => (a :: t).getD ((j + 1) % (t.length + 1)) 0) = t := by
      apply List.ext_getElem (by simp)
      intro j hj _
      simp only [List.length_map, List.length_range] at hj
      simp only [List.getElem_map, List.getElem_range,
        Nat.mod_eq_of_lt (by omega : j + 1 < t.length + 1)]
      rw [List.getD_eq_getElem (a :: t) 0 (by simp; omega)]
      simp
    rw [hinit]
    simpa only [List.singleton_append] using List.perm_append_comm (l₁ := t) (l₂ := [a])

private theorem perm_filter_append_not {α : Type*} (l : List α) (p : α → Bool) :
    (l.filter p ++ l.filter fun x => !p x).Perm l := by
  induction l with
  | nil => simp
  | cons a t ih =>
    cases hp : p a
    · simp only [List.filter_cons, hp, Bool.not_false, ↓reduceIte, Bool.false_eq_true]
      exact List.perm_middle.trans (ih.cons a)
    · simp only [List.filter_cons, hp, Bool.not_true, ↓reduceIte, Bool.false_eq_true,
        List.cons_append]
      exact ih.cons a

private theorem perm_flatMap_of_perm {α β : Type*} (L : List α) (f g : α → List β)
    (h : ∀ a ∈ L, (f a).Perm (g a)) :
    (L.flatMap f).Perm (L.flatMap g) := by
  induction L with
  | nil => simp
  | cons a t ih =>
    simp only [List.flatMap_cons]
    exact (h a List.mem_cons_self).append (ih fun b hb => h b (List.mem_cons_of_mem _ hb))

private theorem flatMap_congr_left {α β : Type*} {L : List α} {f g : α → List β}
    (h : ∀ a ∈ L, f a = g a) : L.flatMap f = L.flatMap g := by
  induction L with
  | nil => rfl
  | cons a t ih =>
    simp only [List.flatMap_cons, h a List.mem_cons_self,
      ih fun b hb => h b (List.mem_cons_of_mem _ hb)]

private theorem map_getD_range_eq (O : List ℕ) :
    (List.range O.length).map (fun j => O.getD j 0) = O := by
  apply List.ext_getElem (by simp)
  intro j hj _
  simp only [List.length_map, List.length_range] at hj
  simp only [List.getElem_map, List.getElem_range, List.getD_eq_getElem O 0 hj]

/-- **Exact-one assignments give 3-dimensional matchings.** -/
private theorem mem_of_oneSatisfiable {φ : CNF ℕ}
    (hs : PositiveOneInExactThreeSATThree.syntaxCheck φ = true) (h : φ.OneSatisfiable) :
    reduce φ ∈ ThreeDM := by
  classical
  obtain ⟨hcl, hpos, -⟩ := (PositiveOneInExactThreeSATThree.syntaxCheck_iff φ).mp hs
  rw [OneSAT.positiveCheck_iff] at hpos
  obtain ⟨σ, hσ⟩ := h
  set m := φ.length with hm
  have hone : ∀ i (hi : i < m), (φ[i].map Prod.fst).countP σ = 1 := fun i hi => by
    have := List.all_eq_true.mp hσ _ (List.getElem_mem hi)
    simpa [Clause.evalOne, countP_eval_eq (hpos _ (List.getElem_mem hi))] using this
  let T_occ := (List.range (3 * m)).filter fun o => σ (occVar φ o)
  let F_occ := (List.range (3 * m)).filter fun o => !σ (occVar φ o)
  have hT_nodup : T_occ.Nodup := List.nodup_range.filter _
  have hF_nodup : F_occ.Nodup := List.nodup_range.filter _
  -- `o ↦ o / 3` maps `T_occ` bijectively to `List.range m`.
  have hT_map_perm : (T_occ.map (· / 3)).Perm (List.range m) := by
    refine perm_range_iff_count.mpr ⟨fun x hx => ?_, fun i hi => ?_⟩
    · obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hx
      have hlt : o < 3 * m := List.mem_range.mp (List.mem_filter.mp ho).1
      omega
    · have hcl3 : φ[i].length = 3 := (hcl _ (List.getElem_mem hi)).1
      obtain ⟨v, hv, hσv, huniq⟩ := existsUnique_of_countP_eq_one (hone i hi)
      obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hv
      obtain ⟨p, hp, rfl⟩ := List.getElem_of_mem hl
      set o₀ := 3 * i + p
      have ho₀_lt : o₀ < 3 * m := by omega
      have ho₀_var : occVar φ o₀ = (φ[i][p]).1 := occVar_eq hcl hi (by omega) rfl
      have ho₀_T : o₀ ∈ T_occ :=
        List.mem_filter.mpr ⟨List.mem_range.mpr ho₀_lt, by rw [ho₀_var]; exact hσv⟩
      rw [count_map_eq_card_filter_toFinset hT_nodup (· / 3) i]
      refine Finset.card_eq_one.mpr ⟨o₀, Finset.ext fun o => ?_⟩
      simp only [Finset.mem_filter, List.mem_toFinset, Finset.mem_singleton]
      refine ⟨fun ⟨hoT, hdiv⟩ => ?_, fun h => h ▸ ⟨ho₀_T, by omega⟩⟩
      have ho_lt : o < 3 * m := List.mem_range.mp (List.mem_filter.mp hoT).1
      have hσo : σ (occVar φ o) = true := (List.mem_filter.mp hoT).2
      have heq : occVar φ o = (φ[i][o % 3]'(by omega)).1 :=
        occVar_eq hcl hi (by omega) (by omega)
      have hv_mem : occVar φ o ∈ φ[i].map Prod.fst := by
        rw [heq]
        exact List.mem_map.mpr ⟨φ[i][o % 3]'(by omega), List.getElem_mem (by omega), rfl⟩
      have hveq : occVar φ o = (φ[i][p]).1 := huniq _ hv_mem hσo
      have hmod_eq : o % 3 = p := by
        rw [heq] at hveq
        have hnd : (φ[i].map Prod.fst).Nodup := (hcl _ (List.getElem_mem hi)).2
        have hget : (φ[i].map Prod.fst)[o % 3]'(by simp [hcl3]; omega) =
            (φ[i].map Prod.fst)[p]'(by simp [hcl3]; omega) := by
          simpa only [List.getElem_map] using hveq
        exact (List.Nodup.getElem_inj_iff hnd).mp hget
      omega
  have hT_len : T_occ.length = m := by
    simpa only [List.length_map, List.length_range] using hT_map_perm.length_eq
  have hF_len : F_occ.length = 2 * m := by
    have hperm := perm_filter_append_not (List.range (3 * m)) (fun o => σ (occVar φ o))
    have hlen := hperm.length_eq
    rw [List.length_append, List.length_range] at hlen
    change T_occ.length + F_occ.length = 3 * m at hlen
    omega
  -- `o ↦ m + F_occ.idxOf o` maps `F_occ` bijectively to `(List.range (2 * m)).map (m + ·)`.
  have hF_map_perm :
      (F_occ.map fun o => m + F_occ.idxOf o).Perm ((List.range (2 * m)).map (m + ·)) := by
    have hidx : F_occ.map F_occ.idxOf = List.range F_occ.length := by
      apply List.ext_getElem (by simp)
      intro j hj _
      simp only [List.length_map] at hj
      simp only [List.getElem_map, List.getElem_range]
      simp [hF_nodup.idxOf_getElem]
    rw [show (F_occ.map fun o => m + F_occ.idxOf o) = (F_occ.map F_occ.idxOf).map (m + ·) by
      simp [List.map_map, Function.comp_def], hidx, hF_len]
  -- Construct the matching `M` by choosing TRUE or FALSE triples for each variable `v`.
  let varMatch (v : ℕ) : List (ℕ × ℕ × ℕ) :=
    let O := varOccs φ v
    if σ v then trueTriples O
    else (List.range O.length).map fun j =>
      (O.getD j 0, O.getD ((j + 1) % O.length) 0, m + F_occ.idxOf (O.getD j 0))
  let M := φ.distinctVars.flatMap varMatch
  refine ⟨fun t ht => by
      have := lt_size_of_mem_reduce hs ht
      simpa only [reduce_of_syntaxCheck hs] using this, M, ?_⟩
  rw [isThreeDM_iff, reduce_of_syntaxCheck hs]
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- Every triple of `M` belongs to `(reduce φ).triples`.
    intro t ht
    obtain ⟨v, hv, htv⟩ := List.mem_flatMap.mp ht
    refine List.mem_flatMap.mpr ⟨v, hv, ?_⟩
    dsimp only [varMatch] at htv
    split_ifs at htv with hσv
    · exact List.mem_append_left _ htv
    · refine List.mem_append_right _ ?_
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp htv
      have hj_lt : j < (varOccs φ v).length := List.mem_range.mp hj
      have hOj_mem : (varOccs φ v).getD j 0 ∈ varOccs φ v := by
        rw [List.getD_eq_getElem _ _ hj_lt]; exact List.getElem_mem hj_lt
      have hOj_F : (varOccs φ v).getD j 0 ∈ F_occ := by
        refine List.mem_filter.mpr ⟨List.mem_range.mpr (mem_varOccs.mp hOj_mem).1, ?_⟩
        rw [(mem_varOccs.mp hOj_mem).2]
        simp [hσv]
      exact mem_falseTriples.mpr ⟨j, hj_lt, F_occ.idxOf ((varOccs φ v).getD j 0),
        hF_len ▸ List.idxOf_lt_length_of_mem hOj_F, rfl⟩
  · -- First coordinate: `M.map Prod.fst` is `(φ.distinctVars.map (varOccs φ)).flatten`.
    have hfst : M.map Prod.fst = (φ.distinctVars.map (varOccs φ)).flatten := by
      rw [List.map_flatMap, List.flatten_eq_flatMap, List.flatMap_map]
      refine flatMap_congr_left fun v _ => ?_
      dsimp only [varMatch, Function.comp_def, id_eq]
      split_ifs
      · simp [trueTriples, List.map_map, Function.comp_def]
      · simp only [List.map_map, Function.comp_def, map_getD_range_eq]
    rw [hfst]
    exact perm_flatten_varOccs hcl
  · -- Second coordinate: each `varMatch v` maps coordinate 2 to a permutation of `varOccs φ v`.
    have hsnd : (M.map fun t => t.2.1).Perm ((φ.distinctVars.map (varOccs φ)).flatten) := by
      rw [List.map_flatMap, List.flatten_eq_flatMap, List.flatMap_map]
      refine perm_flatMap_of_perm φ.distinctVars _ _ fun v _ => ?_
      dsimp only [varMatch, Function.comp_def, id_eq]
      split_ifs
      · simp [trueTriples, List.map_map, Function.comp_def]
      · simpa only [List.map_map, Function.comp_def] using perm_cycle_succ (varOccs φ v)
    exact hsnd.trans (perm_flatten_varOccs hcl)
  · -- Third coordinate: `M.map (·.2.2)` equals
    -- `((φ.distinctVars.map (varOccs φ)).flatten).map yOf`.
    let yOf : ℕ → ℕ := fun o => if σ (occVar φ o) then o / 3 else m + F_occ.idxOf o
    have htrd : M.map (fun t => t.2.2) = ((φ.distinctVars.map (varOccs φ)).flatten).map yOf := by
      rw [List.map_flatMap, List.map_flatten, List.map_map, List.flatten_eq_flatMap,
        List.flatMap_map]
      refine flatMap_congr_left fun v _ => ?_
      dsimp only [varMatch, Function.comp_def, id_eq]
      split_ifs with hσv
      · simp only [trueTriples, List.map_map, Function.comp_def]
        refine List.map_congr_left fun o ho => ?_
        simp only [yOf, (mem_varOccs.mp ho).2, hσv, ↓reduceIte]
      · simp only [List.map_map, Function.comp_def]
        conv_rhs => rw [← map_getD_range_eq (varOccs φ v), List.map_map]
        refine List.map_congr_left fun j hj => ?_
        have hj_lt : j < (varOccs φ v).length := List.mem_range.mp hj
        have hmem : (varOccs φ v).getD j 0 ∈ varOccs φ v := by
          rw [List.getD_eq_getElem _ _ hj_lt]; exact List.getElem_mem hj_lt
        simp only [Function.comp_def, yOf, (mem_varOccs.mp hmem).2, hσv, Bool.false_eq_true,
          ↓reduceIte]
    rw [htrd]
    have h1 : (((φ.distinctVars.map (varOccs φ)).flatten).map yOf).Perm
        ((List.range (3 * m)).map yOf) := (perm_flatten_varOccs hcl).map yOf
    have h2 : ((List.range (3 * m)).map yOf).Perm ((T_occ ++ F_occ).map yOf) :=
      (perm_filter_append_not (List.range (3 * m)) (fun o => σ (occVar φ o))).symm.map yOf
    have hT_yOf : T_occ.map yOf = T_occ.map (· / 3) :=
      List.map_congr_left fun o ho => by simp [yOf, (List.mem_filter.mp ho).2]
    have hF_yOf : F_occ.map yOf = F_occ.map fun o => m + F_occ.idxOf o :=
      List.map_congr_left fun o ho => by
        have hnot : σ (occVar φ o) = false := by simpa using (List.mem_filter.mp ho).2
        simp [yOf, hnot]
    have h3 : ((T_occ ++ F_occ).map yOf).Perm (List.range (3 * m)) := by
      rw [List.map_append, hT_yOf, hF_yOf,
        show 3 * m = m + 2 * m by omega, List.range_add]
      exact hT_map_perm.append hF_map_perm
    exact (h1.trans h2).trans h3

private theorem noInstance_notMem : noInstance ∉ ThreeDM := by
  rintro ⟨-, M, hM⟩
  have hlen : M.length = 1 := hM.length_eq
  obtain ⟨t, ht⟩ := List.exists_mem_of_length_pos (by omega : 0 < M.length)
  exact List.not_mem_nil (hM.subset_triples t ht)

/-- **Correctness of the reduction from `PositiveOneInExactThreeSATThree` to `ThreeDM`.** -/
theorem reduce_mem_iff (φ : CNF ℕ) :
    reduce φ ∈ ThreeDM ↔ φ ∈ PositiveOneInExactThreeSATThree := by
  rw [PositiveOneInExactThreeSATThree.mem_iff_syntaxCheck]
  by_cases hs : PositiveOneInExactThreeSATThree.syntaxCheck φ = true
  · exact ⟨fun h => ⟨hs, oneSatisfiable_of_mem hs h⟩, fun h => mem_of_oneSatisfiable hs h.2⟩
  · simpa [reduce, hs] using noInstance_notMem

end ThreeDM

/-- `ThreeDM` belongs to NP under unary encoding. -/
theorem ThreeDM_mem_NP : ThreeDM ∈ NP encThreeDM := by
  classical
  convert mem_NP_of_subsetWitness (enc := encThreeDM)
    (encγ := encPair encUnary (encPair encUnary encUnary))
    (vs := ThreeDMInstance.triples) (check := ThreeDM.check)
    (P := fun inst S =>
      (∀ t ∈ inst.triples, t.1 < inst.size ∧ t.2.1 < inst.size ∧ t.2.2 < inst.size) ∧
      (∀ u < inst.size, (S.filter fun t => t.1 = u).card = 1) ∧
      (∀ u < inst.size, (S.filter fun t => t.2.1 = u).card = 1) ∧
      (∀ u < inst.size, (S.filter fun t => t.2.2 = u).card = 1))
    (encThreeDM_triples_polyTime id')
    ThreeDM.computableInPolyTime_check
    (fun inst l hl _ => ThreeDM.check_iff inst l hl) using 1
  ext inst
  simp only [ThreeDM, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hbounds, M, hM⟩
    refine ⟨M.toFinset, fun t ht => hM.subset_triples t (List.mem_toFinset.mp ht), hbounds,
      fun u hu => ?_, fun u hu => ?_, fun u hu => ?_⟩
    · rw [← ThreeDM.count_map_eq_card_filter_toFinset hM.nodup Prod.fst u]
      exact (perm_range_iff_count.mp hM.perm_fst).2 u hu
    · rw [← ThreeDM.count_map_eq_card_filter_toFinset hM.nodup (fun t => t.2.1) u]
      exact (perm_range_iff_count.mp hM.perm_snd_fst).2 u hu
    · rw [← ThreeDM.count_map_eq_card_filter_toFinset hM.nodup (fun t => t.2.2) u]
      exact (perm_range_iff_count.mp hM.perm_snd_snd).2 u hu
  · rintro ⟨S, hS, hbounds, hc1, hc2, hc3⟩
    refine ⟨hbounds, S.toList, fun t ht => hS t (Finset.mem_toList.mp ht), ?_, ?_, ?_⟩
    · refine perm_range_iff_count.mpr
        ⟨fun x hx => by
          obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
          exact (hbounds t (hS t (Finset.mem_toList.mp ht))).1, fun u hu => ?_⟩
      rw [ThreeDM.count_map_eq_card_filter_toFinset S.nodup_toList Prod.fst u,
        Finset.toList_toFinset]
      exact hc1 u hu
    · refine perm_range_iff_count.mpr
        ⟨fun x hx => by
          obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
          exact (hbounds t (hS t (Finset.mem_toList.mp ht))).2.1, fun u hu => ?_⟩
      rw [ThreeDM.count_map_eq_card_filter_toFinset S.nodup_toList (fun t => t.2.1) u,
        Finset.toList_toFinset]
      exact hc2 u hu
    · refine perm_range_iff_count.mpr
        ⟨fun x hx => by
          obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
          exact (hbounds t (hS t (Finset.mem_toList.mp ht))).2.2, fun u hu => ?_⟩
      rw [ThreeDM.count_map_eq_card_filter_toFinset S.nodup_toList (fun t => t.2.2) u,
        Finset.toList_toFinset]
      exact hc3 u hu

/-- `PositiveOneInExactThreeSATThree` reduces to `ThreeDM` in polynomial time. -/
theorem polyTimeReducible_PositiveOneInExactThreeSATThree_ThreeDM :
    PolyTimeReducible encCNF encThreeDM PositiveOneInExactThreeSATThree ThreeDM :=
  ⟨ThreeDM.reduce, ThreeDM.computableInPolyTime_reduce,
    fun φ => (ThreeDM.reduce_mem_iff φ).symm⟩

/-- `ThreeDM` is NP-hard under unary encoding. -/
theorem ThreeDM_npHard : NPHard encThreeDM ThreeDM :=
  PositiveOneInExactThreeSATThree_npHard.trans
    polyTimeReducible_PositiveOneInExactThreeSATThree_ThreeDM

/-- **3-Dimensional Matching is NP-complete** under unary encoding. -/
theorem ThreeDM_npComplete : NPComplete encThreeDM ThreeDM :=
  ⟨ThreeDM_mem_NP, ThreeDM_npHard⟩

end Cslib.Complexity
