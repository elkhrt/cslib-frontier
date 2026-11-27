/-
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import CslibFrontier.Computability.Complexity.Problems.OneInThreeSAT.Reduction
public import CslibFrontier.Computability.Complexity.Classes.NP.Witness
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.EraseDupsBy
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Foundations.Data.List.Counting
import CslibFrontier.Foundations.Data.List.EraseDupsBy
import Mathlib.Data.List.GetD

/-!
# Restricted Exact Cover by 3-Sets (RXC3)

An instance of *Restricted Exact Cover by 3-Sets* (RXC3) of size `n ≥ 1` consists of `3 * n`
elements `{0, …, 3 * n - 1}` and `3 * n` distinct 3-element subsets (clauses) such that every
element occurs in exactly three clauses. It is a yes-instance when a subset of `n` clauses
partitions the `3 * n` elements.

We prove that `RXC3` is `NP`-complete under standard Lean axioms by a
direct polynomial-time reduction from `Cslib.Complexity.PositiveOneInExactThreeSATThree` using a
3-copy construction and a 6-element, 5-clause 3-regular choice gadget, and also establish
`NP`-completeness when the size parameter `n` is restricted to multiples of any fixed `k ≥ 1` with
a lower bound `N₀ ≤ n`.

## Main definitions

* `CslibFrontier.Complexity.RXC3Instance`: an instance `(n, clauses)` of RXC3.
* `CslibFrontier.Complexity.encRXC3`: binary encoding of `RXC3Instance`.
* `CslibFrontier.Complexity.RXC3Instance.IsWellFormed`: structural validity of an RXC3 instance.
* `CslibFrontier.Complexity.RXC3Instance.IsExactCover`: an exact cover of `{0, …, 3 * n - 1}`.
* `CslibFrontier.Complexity.RXC3`: the decision.
* `CslibFrontier.Complexity.RXC3Scaled`: RXC3 restricted to `k ∣ n` and `N₀ ≤ n`.

## Main results

* `CslibFrontier.Complexity.RXC3_mem_NP`: `RXC3 ∈ NP encRXC3`.
* `CslibFrontier.Complexity.RXC3_npHard`: `NPHard encRXC3 RXC3`.
* `CslibFrontier.Complexity.RXC3_npComplete`: `NPComplete encRXC3 RXC3`.
* `CslibFrontier.Complexity.RXC3Scaled_npComplete`: `NPComplete encRXC3 (RXC3Scaled k N₀)` for
  `1 ≤ k`.
-/

public section

namespace CslibFrontier.Complexity

open Cslib.Complexity Cslib.Logic.PL Turing.MultiTapeTM ComputableInPolyTime

/-- An instance of Restricted Exact Cover by 3-Sets (RXC3): a size parameter `n` representing the
element set `{0, …, 3 * n - 1}` and a list of `3 * n` clauses, each a list of 3 elements. -/
@[ext]
structure RXC3Instance where
  /-- Size parameter `n`; the element universe has `3 * n` elements `0, …, 3 * n - 1`. -/
  n : ℕ
  /-- The list of `3 * n` clauses, each a 3-element subset of `{0, …, 3 * n - 1}`. -/
  clauses : List (List ℕ)
  deriving DecidableEq, Repr

/-- List encoding of clauses for `enc_structure`. -/
abbrev encClauseList : List (List ℕ) ↪ List Bool := encList (encList encNat)

/-- Binary encoding of an `RXC3Instance` as `(n, clauses)`. -/
enc_structure encRXC3 : RXC3Instance where
  n : encNat, clauses : encClauseList

attribute [fun_prop] encRXC3_n_polyTime encRXC3_clauses_polyTime encRXC3_mk_polyTime

/-- A well-formed RXC3 instance has `1 ≤ n`, `3 * n` pairwise distinct clauses, each consisting of
three distinct elements `< 3 * n`,
  and every element `< 3 * n` occurring in exactly three clauses. -/
@[expose]
def RXC3Instance.IsWellFormed (x : RXC3Instance) : Prop :=
  1 ≤ x.n ∧
    x.clauses.length = 3 * x.n ∧
    x.clauses.Nodup ∧
    (∀ c ∈ x.clauses, c.length = 3 ∧ c.Nodup ∧ ∀ u ∈ c, u < 3 * x.n) ∧
    (∀ u < 3 * x.n, (x.clauses.filter (fun c => decide (u ∈ c))).length = 3)

/-- `D` is an exact cover of the RXC3 instance `x`: every clause in `D` belongs to `x.clauses`,
and every element `u < 3 * x.n` belongs to exactly one clause in `D`. -/
@[expose]
def RXC3Instance.IsExactCover (x : RXC3Instance) (D : Finset (List ℕ)) : Prop :=
  (∀ c ∈ D, c ∈ x.clauses) ∧ ∀ u < 3 * x.n, (D.filter (u ∈ ·)).card = 1

/-- The decision problem **RXC3** (Restricted Exact Cover by 3-Sets): well-formed instances
admitting an exact cover. -/
@[expose]
def RXC3 : Set RXC3Instance :=
  {x | x.IsWellFormed ∧ ∃ D : Finset (List ℕ), x.IsExactCover D}

/-- **RXC3** restricted to instances whose size parameter `n` satisfies `k ∣ n` and `N₀ ≤ n`. -/
@[expose]
def RXC3Scaled (k N₀ : ℕ) : Set RXC3Instance :=
  {x | x ∈ RXC3 ∧ k ∣ x.n ∧ N₀ ≤ x.n}

namespace RXC3

/-! ### Executable well-formedness check and NP membership -/

/-- Executable check that a list has 3 distinct elements strictly less than `m`. -/
private def isTripleLt (m : ℕ) (c : List ℕ) : Bool :=
  (c.length == 3) &&
    (c.getD 0 0 != c.getD 1 0) &&
    (c.getD 0 0 != c.getD 2 0) &&
    (c.getD 1 0 != c.getD 2 0) &&
    decide (c.getD 0 0 < m) &&
    decide (c.getD 1 0 < m) &&
    decide (c.getD 2 0 < m)

private theorem isTripleLt_iff (m : ℕ) (c : List ℕ) :
    isTripleLt m c = true ↔ c.length = 3 ∧ c.Nodup ∧ ∀ u ∈ c, u < m := by
  rcases c with _ | ⟨a, _ | ⟨b, _ | ⟨d, _ | ⟨e, t⟩⟩⟩⟩
  all_goals
    simp only [isTripleLt, List.length_nil, List.length_cons, List.getD_eq_getElem?_getD,
      List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil, Option.getD_some,
      Option.getD_none, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, decide_eq_true_eq,
      List.nodup_nil, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Nat.reduceEqDiff, false_and, true_and, and_true,
      Nat.reduceAdd, ne_eq]
  · tauto

/-- Executable well-formedness check for `RXC3Instance`. -/
def wellFormedBool (x : RXC3Instance) : Bool :=
  decide (1 ≤ x.n) &&
    (x.clauses.length == 3 * x.n) &&
    decide (x.clauses.Nodup) &&
    x.clauses.all (isTripleLt (3 * x.n)) &&
    (List.range x.clauses.length).all fun u =>
      (x.clauses.filter (fun c => decide (u ∈ c))).length == 3

theorem wellFormedBool_eq_true_iff (x : RXC3Instance) :
    wellFormedBool x = true ↔ x.IsWellFormed := by
  simp only [wellFormedBool, RXC3Instance.IsWellFormed, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq, List.all_eq_true, List.mem_range, isTripleLt_iff]
  constructor
  · rintro ⟨⟨⟨⟨h1, hlen⟩, hnd⟩, htri⟩, hdeg⟩
    refine ⟨h1, hlen, hnd, htri, fun u hu => ?_⟩
    exact hdeg u (hlen.symm ▸ hu)
  · rintro ⟨h1, hlen, hnd, htri, hdeg⟩
    refine ⟨⟨⟨⟨h1, hlen⟩, hnd⟩, htri⟩, fun u hu => ?_⟩
    exact hdeg u (hlen ▸ hu)

private theorem computableInPolyTime_isTripleLt :
    ComputableInPolyTime (fun p : ℕ × List ℕ => isTripleLt p.1 p.2)
      (encPair encNat (encList encNat)) encBool := by
  unfold isTripleLt
  fun_prop

theorem computableInPolyTime_wellFormedBool :
    ComputableInPolyTime wellFormedBool encRXC3 encBool := by
  have hlen : ComputableInPolyTime (fun x : RXC3Instance => x.clauses.length) encRXC3 encUnary := by
    fun_prop
  have hn_unary : ComputableInPolyTime (fun x : RXC3Instance => 3 * x.n) encRXC3 encNat := by
    fun_prop
  have h1 : ComputableInPolyTime (fun x : RXC3Instance => decide (1 ≤ x.n)) encRXC3 encBool := by
    fun_prop
  have h2 : ComputableInPolyTime (fun x : RXC3Instance => x.clauses.length == 3 * x.n)
      encRXC3 encBool := by
    have hl : ComputableInPolyTime (fun x : RXC3Instance => x.clauses.length) encRXC3 encNat :=
      ComputableInPolyTime.unary_to_binary.comp hlen
    exact (ComputableInPolyTime.decide_eq' hl hn_unary).of_enc_eq fun x => by
      cases h : (x.clauses.length == 3 * x.n) <;> simp_all
  have h3 : ComputableInPolyTime (fun x : RXC3Instance => decide x.clauses.Nodup)
      encRXC3 encBool :=
    ComputableInPolyTime.decide_nodup (encRXC3_clauses_polyTime id')
  have h4 : ComputableInPolyTime
      (fun x : RXC3Instance => x.clauses.all (isTripleLt (3 * x.n))) encRXC3 encBool :=
    ComputableInPolyTime.allWith computableInPolyTime_isTripleLt hn_unary
      (encRXC3_clauses_polyTime id')
  have h5 : ComputableInPolyTime
      (fun x : RXC3Instance =>
        (List.range x.clauses.length).all fun u =>
          (x.clauses.filter (fun c => decide (u ∈ c))).length == 3)
      encRXC3 encBool := by
    have hrange : ComputableInPolyTime (fun x : RXC3Instance => List.range x.clauses.length)
        encRXC3 (encList encNat) := by
      have hr : ComputableInPolyTime (fun x : RXC3Instance => List.range x.clauses.length)
          encRXC3 (encList encUnary) := by fun_prop
      exact ((ComputableInPolyTime.map (encA := encUnary) (encB := encNat)
        ComputableInPolyTime.unary_to_binary).comp hr).of_enc_eq fun x => by
        simp only [Function.comp_apply, List.map_id']
    have hstep : ComputableInPolyTime
        (fun p : List (List ℕ) × ℕ => (p.1.filter (fun c => decide (p.2 ∈ c))).length == 3)
        (encPair (encList (encList encNat)) encNat) encBool := by
      have hmem : ComputableInPolyTime (fun q : ℕ × List ℕ => decide (q.1 ∈ q.2))
          (encPair encNat (encList encNat)) encBool := by fun_prop
      have hf : ComputableInPolyTime
          (fun p : List (List ℕ) × ℕ => p.1.filter (fun c => decide (p.2 ∈ c)))
          (encPair (encList (encList encNat)) encNat) (encList (encList encNat)) :=
        ComputableInPolyTime.filterWith hmem
          (ComputableInPolyTime.snd _ _) (ComputableInPolyTime.fst _ _)
      have hfl : ComputableInPolyTime
          (fun p : List (List ℕ) × ℕ => (p.1.filter (fun c => decide (p.2 ∈ c))).length)
          (encPair (encList (encList encNat)) encNat) encUnary :=
        (ComputableInPolyTime.length_list (encList encNat)).comp hf
      have hflb : ComputableInPolyTime
          (fun p : List (List ℕ) × ℕ => (p.1.filter (fun c => decide (p.2 ∈ c))).length)
          (encPair (encList (encList encNat)) encNat) encNat :=
        ComputableInPolyTime.unary_to_binary.comp hfl
      fun_prop
    exact ComputableInPolyTime.allWith hstep (encRXC3_clauses_polyTime id') hrange
  unfold wellFormedBool
  fun_prop

/-- Executable verifier check for a selected sublist `p.2` of clauses of `p.1`. -/
def checkCover (p : RXC3Instance × List (List ℕ)) : Bool :=
  wellFormedBool p.1 &&
    (List.range p.1.clauses.length).all fun u =>
      (p.2.filter (fun c => decide (u ∈ c))).length == 1

theorem computableInPolyTime_checkCover :
    ComputableInPolyTime checkCover (encPair encRXC3 (encList (encList encNat))) encBool := by
  have hw : ComputableInPolyTime (fun p : RXC3Instance × List (List ℕ) => wellFormedBool p.1)
      (encPair encRXC3 (encList (encList encNat))) encBool :=
    computableInPolyTime_wellFormedBool.comp (ComputableInPolyTime.fst _ _)
  have hrange : ComputableInPolyTime
      (fun p : RXC3Instance × List (List ℕ) => List.range p.1.clauses.length)
      (encPair encRXC3 (encList (encList encNat))) (encList encNat) := by
    have hr : ComputableInPolyTime
        (fun p : RXC3Instance × List (List ℕ) => List.range p.1.clauses.length)
        (encPair encRXC3 (encList (encList encNat))) (encList encUnary) := by fun_prop
    exact ((ComputableInPolyTime.map (encA := encUnary) (encB := encNat)
      ComputableInPolyTime.unary_to_binary).comp hr).of_enc_eq fun p => by
      simp only [Function.comp_apply, List.map_id']
  have hstep : ComputableInPolyTime
      (fun q : List (List ℕ) × ℕ => (q.1.filter (fun c => decide (q.2 ∈ c))).length == 1)
      (encPair (encList (encList encNat)) encNat) encBool := by
    have hmem : ComputableInPolyTime (fun r : ℕ × List ℕ => decide (r.1 ∈ r.2))
        (encPair encNat (encList encNat)) encBool := by fun_prop
    have hf : ComputableInPolyTime
        (fun q : List (List ℕ) × ℕ => q.1.filter (fun c => decide (q.2 ∈ c)))
        (encPair (encList (encList encNat)) encNat) (encList (encList encNat)) :=
      ComputableInPolyTime.filterWith hmem
        (ComputableInPolyTime.snd _ _) (ComputableInPolyTime.fst _ _)
    have hfl : ComputableInPolyTime
        (fun q : List (List ℕ) × ℕ => (q.1.filter (fun c => decide (q.2 ∈ c))).length)
        (encPair (encList (encList encNat)) encNat) encNat :=
      ComputableInPolyTime.unary_to_binary.comp
        ((ComputableInPolyTime.length_list (encList encNat)).comp hf)
    fun_prop
  have hall : ComputableInPolyTime
      (fun p : RXC3Instance × List (List ℕ) =>
        (List.range p.1.clauses.length).all fun u =>
          (p.2.filter (fun c => decide (u ∈ c))).length == 1)
      (encPair encRXC3 (encList (encList encNat))) encBool :=
    ComputableInPolyTime.allWith hstep (ComputableInPolyTime.snd _ _) hrange
  unfold checkCover
  fun_prop

theorem checkCover_iff (x : RXC3Instance) (l : List (List ℕ)) (hl : l.Nodup) :
    checkCover (x, l) = true ↔
      x.IsWellFormed ∧ ∀ u < 3 * x.n, (l.toFinset.filter (u ∈ ·)).card = 1 := by
  simp only [checkCover, Bool.and_eq_true, wellFormedBool_eq_true_iff, List.all_eq_true,
    List.mem_range, beq_iff_eq]
  constructor
  · rintro ⟨hw, hcov⟩
    refine ⟨hw, fun u hu => ?_⟩
    have h1 := hcov u (hw.2.1.symm ▸ hu)
    have hset : l.toFinset.filter (u ∈ ·) = (l.filter (fun c => decide (u ∈ c))).toFinset := by
      ext c; simp
    rw [hset, List.toFinset_card_of_nodup (hl.filter _)]
    exact h1
  · rintro ⟨hw, hcov⟩
    refine ⟨hw, fun u hu => ?_⟩
    have h1 := hcov u (hw.2.1 ▸ hu)
    have hset : l.toFinset.filter (u ∈ ·) = (l.filter (fun c => decide (u ∈ c))).toFinset := by
      ext c; simp
    rw [hset, List.toFinset_card_of_nodup (hl.filter _)] at h1
    exact h1

theorem getD_mem_of_lt {α : Type*} {l : List α} {i : ℕ} {d : α} (h : i < l.length) :
    l.getD i d ∈ l := by
  rw [List.getD_eq_getElem _ d h]; exact List.getElem_mem h

theorem map_getD_range {α : Type*} (l : List α) (d : α) :
    (List.range l.length).map (fun i => l.getD i d) = l :=
  List.ext_getElem (by simp) fun i hi _ => by
    have hi' : i < l.length := by simpa using hi
    simp [List.getElem?_eq_getElem hi']

/-- Fixed well-formed YES-instance of RXC3 of size `n = 2` (6 elements, 6 distinct clauses). -/
@[expose]
def yesInstance : RXC3Instance :=
  ⟨2, [[0, 1, 2], [3, 4, 5], [0, 1, 3], [0, 2, 4], [1, 3, 5], [2, 4, 5]]⟩

/-- Fixed well-formed NO-instance of RXC3 of size `n = 2` (6 elements, 6 intersecting clauses). -/
@[expose]
def noInstance : RXC3Instance :=
  ⟨2, [[0, 1, 2], [0, 1, 3], [0, 4, 5], [1, 4, 5], [2, 3, 4], [2, 3, 5]]⟩

theorem yesInstance_mem : yesInstance ∈ RXC3 := by
  refine ⟨?_, {[0, 1, 2], [3, 4, 5]}, ?_, ?_⟩
  · rw [← wellFormedBool_eq_true_iff]; decide
  · intro c hc; simp only [Finset.mem_insert, Finset.mem_singleton] at hc
    rcases hc with rfl | rfl <;> simp [yesInstance]
  · intro u hu
    have : u ∈ ({0, 1, 2, 3, 4, 5} : Finset ℕ) := by
      simp only [yesInstance] at hu
      simp only [Finset.mem_insert, Finset.mem_singleton]; omega
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem noInstance_notMem : noInstance ∉ RXC3 := by
  rintro ⟨-, D, hDsub, hDcov⟩
  have hmem : ∀ c ∈ D, c ∈ noInstance.clauses := hDsub
  have h0 : ∃ c ∈ D, 0 ∈ c := by
    have := hDcov 0 (by simp [noInstance])
    obtain ⟨c, hc⟩ := Finset.card_eq_one.mp this
    have hm : c ∈ D.filter (fun c => 0 ∈ c) := hc ▸ Finset.mem_singleton_self c
    exact ⟨c, (Finset.mem_filter.mp hm).1, (Finset.mem_filter.mp hm).2⟩
  obtain ⟨c0, hc0D, h0c0⟩ := h0
  have hc0 : c0 = [0, 1, 2] ∨ c0 = [0, 1, 3] ∨ c0 = [0, 4, 5] := by
    have := hmem c0 hc0D
    simp only [noInstance, List.mem_cons, List.not_mem_nil, or_false] at this
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
  have hdisj : ∀ a ∈ D, ∀ b ∈ D, a ≠ b → ∀ u, u ∈ a → u ∉ b := by
    intro a ha b hb hab u hua hub
    have hcard := hDcov u (by
      have := hmem a ha
      simp only [noInstance, List.mem_cons, List.not_mem_nil, or_false] at this
      rcases this with rfl | rfl | rfl | rfl | rfl | rfl <;>
        (simp only [List.mem_cons, List.not_mem_nil, or_false] at hua;
         simp only [noInstance]; omega))
    have hsub : ({a, b} : Finset (List ℕ)) ⊆ D.filter (u ∈ ·) := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> exact Finset.mem_filter.mpr ⟨by assumption, by assumption⟩
    have h2 := Finset.card_le_card hsub
    rw [Finset.card_pair hab, hcard] at h2
    omega
  rcases hc0 with rfl | rfl | rfl
  · have h3 := hDcov 3 (by simp [noInstance])
    obtain ⟨c3, hc3⟩ := Finset.card_eq_one.mp h3
    have hm3 : c3 ∈ D.filter (fun c => 3 ∈ c) := hc3 ▸ Finset.mem_singleton_self c3
    have hc3D : c3 ∈ D := (Finset.mem_filter.mp hm3).1
    have h3c3 : 3 ∈ c3 := (Finset.mem_filter.mp hm3).2
    have hne : [0, 1, 2] ≠ c3 := fun h => by rw [← h] at h3c3; simp at h3c3
    have hcl := hmem c3 hc3D
    simp only [noInstance, List.mem_cons, List.not_mem_nil, or_false] at hcl
    rcases hcl with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hne rfl
    · exact hdisj _ hc0D _ hc3D hne 0 (by simp) (by simp)
    · simp at h3c3
    · simp at h3c3
    · exact hdisj _ hc0D _ hc3D hne 2 (by simp) (by simp)
    · exact hdisj _ hc0D _ hc3D hne 2 (by simp) (by simp)
  · have h2 := hDcov 2 (by simp [noInstance])
    obtain ⟨c2, hc2⟩ := Finset.card_eq_one.mp h2
    have hm2 : c2 ∈ D.filter (fun c => 2 ∈ c) := hc2 ▸ Finset.mem_singleton_self c2
    have hc2D : c2 ∈ D := (Finset.mem_filter.mp hm2).1
    have h2c2 : 2 ∈ c2 := (Finset.mem_filter.mp hm2).2
    have hne : [0, 1, 3] ≠ c2 := fun h => by rw [← h] at h2c2; simp at h2c2
    have hcl := hmem c2 hc2D
    simp only [noInstance, List.mem_cons, List.not_mem_nil, or_false] at hcl
    rcases hcl with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hdisj _ hc0D _ hc2D hne 0 (by simp) (by simp)
    · exact hne rfl
    · simp at h2c2
    · simp at h2c2
    · exact hdisj _ hc0D _ hc2D hne 3 (by simp) (by simp)
    · exact hdisj _ hc0D _ hc2D hne 3 (by simp) (by simp)
  · have h1 := hDcov 1 (by simp [noInstance])
    obtain ⟨c1, hc1⟩ := Finset.card_eq_one.mp h1
    have hm1 : c1 ∈ D.filter (fun c => 1 ∈ c) := hc1 ▸ Finset.mem_singleton_self c1
    have hc1D : c1 ∈ D := (Finset.mem_filter.mp hm1).1
    have h1c1 : 1 ∈ c1 := (Finset.mem_filter.mp hm1).2
    have hne : [0, 4, 5] ≠ c1 := fun h => by rw [← h] at h1c1; simp at h1c1
    have hcl := hmem c1 hc1D
    simp only [noInstance, List.mem_cons, List.not_mem_nil, or_false] at hcl
    rcases hcl with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hdisj _ hc0D _ hc1D hne 0 (by simp) (by simp)
    · exact hdisj _ hc0D _ hc1D hne 0 (by simp) (by simp)
    · exact hne rfl
    · exact hdisj _ hc0D _ hc1D hne 4 (by simp) (by simp)
    · simp at h1c1
    · simp at h1c1

/-! ### Reduction from `PositiveOneInExactThreeSATThree` to `RXC3` -/

/-- The 5 clauses of the 6-element choice gadget `H₃` with base offset `b`:
exposed ports `b, b + 1, b + 2` (degree 2 inside `H₃`) and internal elements
`b + 3, b + 4, b + 5` (degree 3 inside `H₃`). -/
@[expose]
def choiceGadget (b : ℕ) : List (List ℕ) :=
  [[b, b + 1, b + 2], [b + 3, b + 4, b + 5],
   [b, b + 3, b + 4], [b + 1, b + 4, b + 5], [b + 2, b + 5, b + 3]]

/-- Clause indices in `φ` containing variable `v`. -/
@[expose]
def occIndices (φ : CNF ℕ) (v : ℕ) : List ℕ :=
  (List.range φ.length).filter fun i =>
    decide (v ∈ ((φ.getD i []).map Prod.fst))

/-- Number of `H₃` gadgets needed for a variable with `s` occurrences:
`2` if `s = 1`, `1` if `s = 2`, `3` if `s = 3` (and `0` otherwise). -/
@[expose]
def gadgetCount (s : ℕ) : ℕ :=
  if s = 1 then 2 else if s = 2 then 1 else if s = 3 then 3 else 0

/-- Clauses emitted for a variable occurring at indices `occ`, using `H₃` gadgets starting at
`base` (each of width 6), with `m = φ.length` total clauses in `φ`. -/
@[expose]
def varClauses (_m base : ℕ) (occ : List ℕ) : List (List ℕ) :=
  if occ.length = 1 then
    let i0 := occ.getD 0 0
    [[3 * i0, base, base + 6],
     [3 * i0 + 1, base + 1, base + 7],
     [3 * i0 + 2, base + 2, base + 8]] ++
      choiceGadget base ++ choiceGadget (base + 6)
  else if occ.length = 2 then
    let i0 := occ.getD 0 0
    let i1 := occ.getD 1 0
    [[3 * i0, 3 * i1, base],
     [3 * i0 + 1, 3 * i1 + 1, base + 1],
     [3 * i0 + 2, 3 * i1 + 2, base + 2]] ++
      choiceGadget base
  else if occ.length = 3 then
    let i0 := occ.getD 0 0
    let i1 := occ.getD 1 0
    let i2 := occ.getD 2 0
    [[3 * i0, 3 * i1, base], [3 * i2, base + 1, base + 2],
     [3 * i0 + 1, 3 * i1 + 1, base + 6], [3 * i2 + 1, base + 7, base + 8],
     [3 * i0 + 2, 3 * i1 + 2, base + 12], [3 * i2 + 2, base + 13, base + 14]] ++
      choiceGadget base ++ choiceGadget (base + 6) ++ choiceGadget (base + 12)
  else
    []

/-- Prefix sum of gadget counts for variables `vs.take k`. -/
@[expose]
def gadgetPrefix (φ : CNF ℕ) (vs : List ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => gadgetPrefix φ vs k + gadgetCount (occIndices φ (vs.getD k 0)).length

/-- Distinct variables of `φ` obtained by erasing duplicates in polynomial time. -/
@[expose]
def distinctVars (φ : CNF ℕ) : List ℕ :=
  φ.vars.eraseDupsBy (fun a b => decide (a = b))

/-- Total number of `H₃` gadgets emitted for `φ`. -/
@[expose]
def totalGadgets (φ : CNF ℕ) : ℕ :=
  let vs := distinctVars φ
  gadgetPrefix φ vs vs.length

/-- Reduction from `PositiveOneInExactThreeSATThree` to `RXC3`. -/
@[expose]
def reduce (φ : CNF ℕ) : RXC3Instance :=
  if PositiveOneInExactThreeSATThree.syntaxCheck φ then
    if φ.isEmpty then
      yesInstance
    else
      let vs := distinctVars φ
      let m := φ.length
      let G := gadgetPrefix φ vs vs.length
      let clauses := (List.range vs.length).flatMap fun k =>
        varClauses m (3 * m + 6 * gadgetPrefix φ vs k) (occIndices φ (vs.getD k 0))
      ⟨m + 2 * G, clauses⟩
  else
    noInstance

private theorem length_choiceGadget (b : ℕ) : (choiceGadget b).length = 5 := rfl

private theorem length_varClauses (m base : ℕ) (occ : List ℕ) (h1 : 1 ≤ occ.length)
    (h3 : occ.length ≤ 3) :
    (varClauses m base occ).length =
      (if occ.length = 3 then 6 else 3) + 5 * gadgetCount occ.length := by
  unfold varClauses gadgetCount
  have : occ.length = 1 ∨ occ.length = 2 ∨ occ.length = 3 := by omega
  rcases this with h | h | h <;> simp [h, choiceGadget]

private theorem gadgetCount_eq (s : ℕ) (h1 : 1 ≤ s) (h3 : s ≤ 3) :
    6 * gadgetCount s = (if s = 3 then 6 else 3) + 5 * gadgetCount s - s := by
  unfold gadgetCount
  have : s = 1 ∨ s = 2 ∨ s = 3 := by omega
  rcases this with rfl | rfl | rfl <;> decide

theorem count_occIndices_eq (φ : CNF ℕ) (v : ℕ)
    (hnd : ∀ c ∈ φ, (c.map Prod.fst).Nodup) :
    (occIndices φ v).length = φ.vars.count v := by
  classical
  unfold occIndices
  induction φ with
  | nil => simp [CNF.vars]
  | cons c cs ih =>
    have hnd_c : (c.map Prod.fst).Nodup := hnd c (List.mem_cons_self ..)
    have hnd_cs : ∀ c' ∈ cs, (c'.map Prod.fst).Nodup := fun c' hc' =>
      hnd c' (List.mem_cons_of_mem _ hc')
    simp only [List.length_cons, CNF.vars, List.flatten_cons, List.map_append, List.count_append]
    change _ = (c.map Prod.fst).count v + (CNF.vars cs).count v
    rw [← ih hnd_cs]
    rw [List.range_succ_eq_map, List.filter_cons, List.filter_map]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_cons_zero, Option.getD_some]
    have hcount_c : List.count v (c.map Prod.fst) = if v ∈ c.map Prod.fst then 1 else 0 := by
      by_cases hv : v ∈ c.map Prod.fst
      · simp [hv, List.Nodup.count hnd_c]
      · simp [hv, List.count_eq_zero.mpr hv]
    have hfilter_eq :
        (List.filter ((fun i => decide (v ∈ ((c :: cs)[i]?.getD []).map Prod.fst)) ∘ Nat.succ)
          (List.range cs.length)).length =
        (List.filter (fun i => decide (v ∈ (cs[i]?.getD []).map Prod.fst))
          (List.range cs.length)).length := rfl
    by_cases hv : v ∈ c.map Prod.fst
    · simp only [hv, decide_true, ↓reduceIte, List.length_cons, hcount_c, List.length_map]
      rw [hfilter_eq, Nat.add_comm]
    · simp only [hv, decide_false, Bool.false_eq_true, ↓reduceIte, hcount_c, Nat.zero_add,
        List.length_map]
      exact hfilter_eq

theorem mem_occIndices_iff {φ : CNF ℕ} {v i : ℕ} :
    i ∈ occIndices φ v ↔ i < φ.length ∧ v ∈ ((φ.getD i []).map Prod.fst) := by
  simp [occIndices]

theorem nodup_occIndices (φ : CNF ℕ) (v : ℕ) : (occIndices φ v).Nodup :=
  List.nodup_range.filter _

private theorem mem_choiceGadget_iff {b : ℕ} {c : List ℕ} :
    c ∈ choiceGadget b ↔
      c = [b, b + 1, b + 2] ∨ c = [b + 3, b + 4, b + 5] ∨
        c = [b, b + 3, b + 4] ∨ c = [b + 1, b + 4, b + 5] ∨ c = [b + 2, b + 5, b + 3] := by
  simp [choiceGadget]

theorem choiceGadget_elem_range {b : ℕ} {c : List ℕ} (hc : c ∈ choiceGadget b)
    {u : ℕ} (hu : u ∈ c) : b ≤ u ∧ u < b + 6 := by
  rw [mem_choiceGadget_iff] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu <;>
    rcases hu with rfl | rfl | rfl <;> omega

private theorem choiceGadget_nodup (b : ℕ) : (choiceGadget b).Nodup := by
  simp only [choiceGadget, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    List.cons.injEq, and_true, List.nodup_nil]
  grind

private theorem choiceGadget_isTriple (b : ℕ) :
    ∀ c ∈ choiceGadget b, c.length = 3 ∧ c.Nodup := by
  intro c hc
  rw [mem_choiceGadget_iff] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;>
    refine ⟨rfl, ?_⟩ <;>
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, List.nodup_nil] <;>
    grind

private theorem choiceGadget_port_count (b : ℕ) (r : ℕ) (hr : r < 3) :
    ((choiceGadget b).filter (fun c => decide (b + r ∈ c))).length = 2 := by
  have : r = 0 ∨ r = 1 ∨ r = 2 := by omega
  rcases this with rfl | rfl | rfl <;> simp [choiceGadget]

private theorem choiceGadget_internal_count (b : ℕ) (r : ℕ) (hr : r < 3) :
    ((choiceGadget b).filter (fun c => decide (b + 3 + r ∈ c))).length = 3 := by
  have : r = 0 ∨ r = 1 ∨ r = 2 := by omega
  rcases this with rfl | rfl | rfl
  · simp [choiceGadget]
  · simp [choiceGadget, show b + 3 + 1 = b + 4 by omega]
  · simp [choiceGadget, show b + 3 + 2 = b + 5 by omega]

/-- In any exact cover of the internal elements `{b + 3, b + 4, b + 5}` (and some subset of the
ports `{b, b + 1, b + 2}`) using subsets of `choiceGadget b`, either all three ports are covered
by `choiceGadget b` or none of them are. -/
theorem choiceGadget_sync {b : ℕ} {D : Finset (List ℕ)} :
    let Dg := D.filter (· ∈ choiceGadget b)
    (∀ r < 3, (Dg.filter (b + r ∈ ·)).card ≤ 1) →
    (∀ r < 3, (Dg.filter (b + 3 + r ∈ ·)).card = 1) →
    ((∀ r < 3, (Dg.filter (b + r ∈ ·)).card = 1) ∨
      (∀ r < 3, (Dg.filter (b + r ∈ ·)).card = 0)) := by
  intro Dg hport hint
  have hsum : ∑ c ∈ Dg, c.length =
      ∑ r ∈ Finset.range 3, (Dg.filter (b + r ∈ ·)).card +
      ∑ r ∈ Finset.range 3, (Dg.filter (b + 3 + r ∈ ·)).card := by
    have hcard_c : ∀ c ∈ Dg, c.length =
        ((Finset.range 3).filter (fun r => b + r ∈ c)).card +
        ((Finset.range 3).filter (fun r => b + 3 + r ∈ c)).card := by
      intro c hc
      have hcg : c ∈ choiceGadget b := (Finset.mem_filter.mp hc).2
      rw [mem_choiceGadget_iff] at hcg
      rcases hcg with rfl | rfl | rfl | rfl | rfl
      · have h1 : (Finset.range 3).filter (fun r => b + r ∈ [b, b + 1, b + 2]) = {0, 1, 2} := by
          ext r; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert,
            Finset.mem_singleton, List.mem_cons, List.not_mem_nil, or_false]; omega
        have h2 : (Finset.range 3).filter (fun r => b + 3 + r ∈ [b, b + 1, b + 2]) = ∅ := by
          ext r; simp only [Finset.mem_filter, Finset.mem_range, Finset.notMem_empty, iff_false,
            List.mem_cons, List.not_mem_nil, or_false]; omega
        rw [h1, h2]; simp
      · have h1 : (Finset.range 3).filter (fun r => b + r ∈ [b + 3, b + 4, b + 5]) = ∅ := by
          ext r; simp only [Finset.mem_filter, Finset.mem_range, Finset.notMem_empty, iff_false,
            List.mem_cons, List.not_mem_nil, or_false]; omega
        have h2 : (Finset.range 3).filter (fun r => b + 3 + r ∈ [b + 3, b + 4, b + 5]) =
            {0, 1, 2} := by
          ext r; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert,
            Finset.mem_singleton, List.mem_cons, List.not_mem_nil, or_false]; omega
        rw [h1, h2]; simp
      · have h1 : (Finset.range 3).filter (fun r => b + r ∈ [b, b + 3, b + 4]) = {0} := by
          ext r; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton,
            List.mem_cons, List.not_mem_nil, or_false]; omega
        have h2 : (Finset.range 3).filter (fun r => b + 3 + r ∈ [b, b + 3, b + 4]) = {0, 1} := by
          ext r; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert,
            Finset.mem_singleton, List.mem_cons, List.not_mem_nil, or_false]; omega
        rw [h1, h2]; simp
      · have h1 : (Finset.range 3).filter (fun r => b + r ∈ [b + 1, b + 4, b + 5]) = {1} := by
          ext r; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton,
            List.mem_cons, List.not_mem_nil, or_false]; omega
        have h2 : (Finset.range 3).filter (fun r => b + 3 + r ∈ [b + 1, b + 4, b + 5]) =
            {1, 2} := by
          ext r; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert,
            Finset.mem_singleton, List.mem_cons, List.not_mem_nil, or_false]; omega
        rw [h1, h2]; simp
      · have h1 : (Finset.range 3).filter (fun r => b + r ∈ [b + 2, b + 5, b + 3]) = {2} := by
          ext r; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton,
            List.mem_cons, List.not_mem_nil, or_false]; omega
        have h2 : (Finset.range 3).filter (fun r => b + 3 + r ∈ [b + 2, b + 5, b + 3]) =
            {0, 2} := by
          ext r; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert,
            Finset.mem_singleton, List.mem_cons, List.not_mem_nil, or_false]; omega
        rw [h1, h2]; simp
    calc
      ∑ c ∈ Dg, c.length =
          ∑ c ∈ Dg, (((Finset.range 3).filter (fun r => b + r ∈ c)).card +
            ((Finset.range 3).filter (fun r => b + 3 + r ∈ c)).card) :=
        Finset.sum_congr rfl hcard_c
      _ = ∑ c ∈ Dg, ((Finset.range 3).filter (fun r => b + r ∈ c)).card +
          ∑ c ∈ Dg, ((Finset.range 3).filter (fun r => b + 3 + r ∈ c)).card :=
        Finset.sum_add_distrib
      _ = ∑ r ∈ Finset.range 3, (Dg.filter (b + r ∈ ·)).card +
          ∑ r ∈ Finset.range 3, (Dg.filter (b + 3 + r ∈ ·)).card := by
        congr 1
        · simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
          rw [Finset.sum_comm]
        · simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
          rw [Finset.sum_comm]
  have hlen3 : ∑ c ∈ Dg, c.length = 3 * Dg.card := by
    rw [Finset.sum_congr rfl fun c hc => (choiceGadget_isTriple b c (Finset.mem_filter.mp hc).2).1,
      Finset.sum_const, smul_eq_mul, mul_comm]
  have hint3 : ∑ r ∈ Finset.range 3, (Dg.filter (b + 3 + r ∈ ·)).card = 3 := by
    rw [Finset.sum_congr rfl fun r hr => hint r (Finset.mem_range.mp hr)]
    simp
  have hport_sum : ∑ r ∈ Finset.range 3, (Dg.filter (b + r ∈ ·)).card =
      (Dg.filter (b ∈ ·)).card + (Dg.filter (b + 1 ∈ ·)).card + (Dg.filter (b + 2 ∈ ·)).card := by
    simp [Finset.sum_range_succ]
  have h0le : (Dg.filter (b ∈ ·)).card ≤ 1 := by simpa using hport 0 (by omega)
  have h1le := hport 1 (by omega)
  have h2le := hport 2 (by omega)
  have hmod : (Dg.filter (b ∈ ·)).card + (Dg.filter (b + 1 ∈ ·)).card +
      (Dg.filter (b + 2 ∈ ·)).card + 3 = 3 * Dg.card := by
    omega
  have hcases : ((Dg.filter (b ∈ ·)).card = 1 ∧ (Dg.filter (b + 1 ∈ ·)).card = 1 ∧
      (Dg.filter (b + 2 ∈ ·)).card = 1) ∨
      ((Dg.filter (b ∈ ·)).card = 0 ∧ (Dg.filter (b + 1 ∈ ·)).card = 0 ∧
      (Dg.filter (b + 2 ∈ ·)).card = 0) := by omega
  rcases hcases with ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩
  · left; intro r hr
    have : r = 0 ∨ r = 1 ∨ r = 2 := by omega
    rcases this with rfl | rfl | rfl
    · simpa using ha
    · exact hb
    · exact hc
  · right; intro r hr
    have : r = 0 ∨ r = 1 ∨ r = 2 := by omega
    rcases this with rfl | rfl | rfl
    · simpa using ha
    · exact hb
    · exact hc

theorem gadgetPrefix_mono (φ : CNF ℕ) (vs : List ℕ) {i j : ℕ} (hij : i ≤ j) :
    gadgetPrefix φ vs i ≤ gadgetPrefix φ vs j := by
  induction hij with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (Nat.le_add_right _ _)

theorem gadgetPrefix_succ_le (φ : CNF ℕ) (vs : List ℕ) {k : ℕ} (hk : k < vs.length) :
    gadgetPrefix φ vs k + gadgetCount (occIndices φ (vs.getD k 0)).length ≤
      gadgetPrefix φ vs vs.length := by
  have : gadgetPrefix φ vs (k + 1) ≤ gadgetPrefix φ vs vs.length :=
    gadgetPrefix_mono φ vs hk
  simpa only [gadgetPrefix] using this

theorem varClauses_elem_lt {m base : ℕ} {occ : List ℕ}
    (hocc : ∀ i ∈ occ, i < m) {c : List ℕ} (hc : c ∈ varClauses m base occ)
    {u : ℕ} (hu : u ∈ c) : u < 3 * m ∨ (base ≤ u ∧ u < base + 6 * gadgetCount occ.length) := by
  unfold varClauses at hc
  unfold gadgetCount
  split_ifs at hc with h1 h2 h3
  · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rw [h1]; simp only [↓reduceIte]
    have hi0 : occ.getD 0 0 < m := hocc _ (getD_mem_of_lt (by omega))
    rcases hc with ((rfl | rfl | rfl) | hcg) | hcg
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl | rfl <;> omega
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl | rfl <;> omega
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl | rfl <;> omega
    · right; have := choiceGadget_elem_range hcg hu; omega
    · right; have := choiceGadget_elem_range hcg hu; omega
  · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rw [h2]; simp only [show (2 : ℕ) ≠ 1 by decide, ↓reduceIte]
    have hi0 : occ.getD 0 0 < m := hocc _ (getD_mem_of_lt (by omega))
    have hi1 : occ.getD 1 0 < m := hocc _ (getD_mem_of_lt (by omega))
    rcases hc with (rfl | rfl | rfl) | hcg
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl | rfl <;> omega
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl | rfl <;> omega
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl | rfl <;> omega
    · right; have := choiceGadget_elem_range hcg hu; omega
  · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rw [h3]; simp only [show (3 : ℕ) ≠ 1 by decide, show (3 : ℕ) ≠ 2 by decide, ↓reduceIte]
    have hi0 : occ.getD 0 0 < m := hocc _ (getD_mem_of_lt (by omega))
    have hi1 : occ.getD 1 0 < m := hocc _ (getD_mem_of_lt (by omega))
    have hi2 : occ.getD 2 0 < m := hocc _ (getD_mem_of_lt (by omega))
    rcases hc with (((rfl | rfl | rfl | rfl | rfl | rfl) | hcg) | hcg) | hcg
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl | rfl <;> omega
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl | rfl <;> omega
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl | rfl <;> omega
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl | rfl <;> omega
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl | rfl <;> omega
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl | rfl <;> omega
    · right; have := choiceGadget_elem_range hcg hu; omega
    · right; have := choiceGadget_elem_range hcg hu; omega
    · right; have := choiceGadget_elem_range hcg hu; omega
  · simp at hc

private theorem varClauses_isTriple {m base : ℕ} {occ : List ℕ}
    (hbase : 3 * m ≤ base) (hnd : occ.Nodup) (hocc : ∀ i ∈ occ, i < m)
    {c : List ℕ} (hc : c ∈ varClauses m base occ) :
    c.length = 3 ∧ c.Nodup := by
  unfold varClauses at hc
  split_ifs at hc with h1 h2 h3
  · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    have hi0 : occ.getD 0 0 < m := hocc _ (getD_mem_of_lt (by omega))
    rcases hc with ((rfl | rfl | rfl) | hcg) | hcg
    · refine ⟨rfl, ?_⟩; simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
        List.nodup_nil]; grind
    · refine ⟨rfl, ?_⟩; simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
        List.nodup_nil]; grind
    · refine ⟨rfl, ?_⟩; simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
        List.nodup_nil]; grind
    · exact choiceGadget_isTriple _ _ hcg
    · exact choiceGadget_isTriple _ _ hcg
  · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    have hi0 : occ.getD 0 0 < m := hocc _ (getD_mem_of_lt (by omega))
    have hi1 : occ.getD 1 0 < m := hocc _ (getD_mem_of_lt (by omega))
    have hne : occ.getD 0 0 ≠ occ.getD 1 0 := by
      have := (List.nodup_iff_injective_getElem.mp hnd) (a₁ := ⟨0, by omega⟩) (a₂ := ⟨1, by omega⟩)
      simp only [List.getD_eq_getElem _ 0 (by omega : 0 < occ.length),
        List.getD_eq_getElem _ 0 (by omega : 1 < occ.length)]
      intro heq; have := this heq; simp at this
    rcases hc with (rfl | rfl | rfl) | hcg
    · refine ⟨rfl, ?_⟩; simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
        List.nodup_nil]; grind
    · refine ⟨rfl, ?_⟩; simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
        List.nodup_nil]; grind
    · refine ⟨rfl, ?_⟩; simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
        List.nodup_nil]; grind
    · exact choiceGadget_isTriple _ _ hcg
  · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    have hi0 : occ.getD 0 0 < m := hocc _ (getD_mem_of_lt (by omega))
    have hi1 : occ.getD 1 0 < m := hocc _ (getD_mem_of_lt (by omega))
    have hi2 : occ.getD 2 0 < m := hocc _ (getD_mem_of_lt (by omega))
    have hne01 : occ.getD 0 0 ≠ occ.getD 1 0 := by
      have := (List.nodup_iff_injective_getElem.mp hnd) (a₁ := ⟨0, by omega⟩) (a₂ := ⟨1, by omega⟩)
      simp only [List.getD_eq_getElem _ 0 (by omega : 0 < occ.length),
        List.getD_eq_getElem _ 0 (by omega : 1 < occ.length)]
      intro heq; have := this heq; simp at this
    rcases hc with (((rfl | rfl | rfl | rfl | rfl | rfl) | hcg) | hcg) | hcg
    · refine ⟨rfl, ?_⟩; simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
        List.nodup_nil]; grind
    · refine ⟨rfl, ?_⟩; simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
        List.nodup_nil]; grind
    · refine ⟨rfl, ?_⟩; simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
        List.nodup_nil]; grind
    · refine ⟨rfl, ?_⟩; simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
        List.nodup_nil]; grind
    · refine ⟨rfl, ?_⟩; simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
        List.nodup_nil]; grind
    · refine ⟨rfl, ?_⟩; simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
        List.nodup_nil]; grind
    · exact choiceGadget_isTriple _ _ hcg
    · exact choiceGadget_isTriple _ _ hcg
    · exact choiceGadget_isTriple _ _ hcg
  · simp at hc

private theorem varClauses_nodup {m base : ℕ} {occ : List ℕ}
    (hbase : 3 * m ≤ base) (hocc : ∀ i ∈ occ, i < m) :
    (varClauses m base occ).Nodup := by
  unfold varClauses
  split_ifs with h1 h2 h3
  · have hi0 : occ.getD 0 0 < m := hocc _ (getD_mem_of_lt (by omega))
    rw [List.nodup_append, List.nodup_append]
    refine ⟨⟨?_, choiceGadget_nodup _, ?_⟩, choiceGadget_nodup _, ?_⟩
    · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, List.cons.injEq,
        and_true, List.nodup_nil]
      grind
    · intro c hc c' hc' heq; subst heq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · have := (choiceGadget_elem_range hc' (by simp : 3 * occ.getD 0 0 ∈ _)).1; omega
      · have := (choiceGadget_elem_range hc' (by simp : 3 * occ.getD 0 0 + 1 ∈ _)).1; omega
      · have := (choiceGadget_elem_range hc' (by simp : 3 * occ.getD 0 0 + 2 ∈ _)).1; omega
    · intro c hc c' hc' heq; subst heq
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with (rfl | rfl | rfl) | hcg
      · have := (choiceGadget_elem_range hc' (by simp : 3 * occ.getD 0 0 ∈ _)).1; omega
      · have := (choiceGadget_elem_range hc' (by simp : 3 * occ.getD 0 0 + 1 ∈ _)).1; omega
      · have := (choiceGadget_elem_range hc' (by simp : 3 * occ.getD 0 0 + 2 ∈ _)).1; omega
      · rw [mem_choiceGadget_iff] at hcg
        rcases hcg with rfl | rfl | rfl | rfl | rfl <;>
          (have hlo := (choiceGadget_elem_range hc' List.mem_cons_self).1; omega)
  · have hi0 : occ.getD 0 0 < m := hocc _ (getD_mem_of_lt (by omega))
    have hi1 : occ.getD 1 0 < m := hocc _ (getD_mem_of_lt (by omega))
    rw [List.nodup_append]
    refine ⟨?_, choiceGadget_nodup _, ?_⟩
    · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, List.cons.injEq,
        and_true, List.nodup_nil]
      grind
    · intro c hc c' hc' heq; subst heq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · have := (choiceGadget_elem_range hc' (by simp : 3 * occ.getD 0 0 ∈ _)).1; omega
      · have := (choiceGadget_elem_range hc' (by simp : 3 * occ.getD 0 0 + 1 ∈ _)).1; omega
      · have := (choiceGadget_elem_range hc' (by simp : 3 * occ.getD 0 0 + 2 ∈ _)).1; omega
  · have hi0 : occ.getD 0 0 < m := hocc _ (getD_mem_of_lt (by omega))
    have hi1 : occ.getD 1 0 < m := hocc _ (getD_mem_of_lt (by omega))
    have hi2 : occ.getD 2 0 < m := hocc _ (getD_mem_of_lt (by omega))
    have hCG (a b : ℕ) (hab : a + 6 ≤ b) :
        ∀ c ∈ choiceGadget a, ∀ c' ∈ choiceGadget b, c ≠ c' := by
      intro c hc c' hc' heq; subst heq
      rw [mem_choiceGadget_iff] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl <;>
        (have hlo := (choiceGadget_elem_range hc' List.mem_cons_self).1; omega)
    have hV_CG (b : ℕ) (hb : 3 * m ≤ b) :
        ∀ c ∈ [[3 * occ.getD 0 0, 3 * occ.getD 1 0, base],
               [3 * occ.getD 2 0, base + 1, base + 2],
               [3 * occ.getD 0 0 + 1, 3 * occ.getD 1 0 + 1, base + 6],
               [3 * occ.getD 2 0 + 1, base + 7, base + 8],
               [3 * occ.getD 0 0 + 2, 3 * occ.getD 1 0 + 2, base + 12],
               [3 * occ.getD 2 0 + 2, base + 13, base + 14]],
        ∀ c' ∈ choiceGadget b, c ≠ c' := by
      intro c hc c' hc' heq; subst heq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;>
        (have hlo := (choiceGadget_elem_range hc' List.mem_cons_self).1; omega)
    rw [List.nodup_append, List.nodup_append, List.nodup_append]
    refine ⟨⟨⟨?_, choiceGadget_nodup _, hV_CG _ (by omega)⟩, choiceGadget_nodup _, ?_⟩,
      choiceGadget_nodup _, ?_⟩
    · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, List.cons.injEq,
        and_true, List.nodup_nil]
      grind
    · intro c hc c' hc' heq
      simp only [List.mem_append] at hc
      rcases hc with hv | hcg
      · exact hV_CG _ (by omega) c hv c' hc' heq
      · exact hCG _ _ (by omega) c hcg c' hc' heq
    · intro c hc c' hc' heq
      simp only [List.mem_append] at hc
      rcases hc with (hv | hcg1) | hcg2
      · exact hV_CG _ (by omega) c hv c' hc' heq
      · exact hCG _ _ (by omega) c hcg1 c' hc' heq
      · exact hCG _ _ (by omega) c hcg2 c' hc' heq
  · exact List.nodup_nil

theorem varClauses_clause_count {m base : ℕ} {occ : List ℕ}
    (hbase : 3 * m ≤ base) (hnd : occ.Nodup) (hocc : ∀ i ∈ occ, i < m)
    (h1 : 1 ≤ occ.length) (h3 : occ.length ≤ 3) {i r : ℕ} (hi : i < m) (hr : r < 3) :
    ((varClauses m base occ).filter (fun c => decide (3 * i + r ∈ c))).length =
      if i ∈ occ then 1 else 0 := by
  have hmem_cg : ∀ b, 3 * m ≤ b →
      ((choiceGadget b).filter (fun c => decide (3 * i + r ∈ c))).length = 0 := by
    intro b hb
    rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
    intro c hc
    simp only [decide_eq_true_eq]
    intro hmem
    have := (choiceGadget_elem_range hc hmem).1
    omega
  have hcount_iff : ∀ (a : ℕ) (L : List (List ℕ)),
      (L.filter (fun c => decide (a ∈ c))).length =
        ((L.map (fun c => if a ∈ c then 1 else 0)).sum) := by
    intro a L
    induction L with
    | nil => simp
    | cons c cs ih =>
      by_cases h : a ∈ c <;> simp [h, ih, Nat.add_comm]
  unfold varClauses
  have hlen : occ.length = 1 ∨ occ.length = 2 ∨ occ.length = 3 := by omega
  rcases hlen with hl | hl | hl
  · have hget0 : occ = [occ.getD 0 0] := by
      rcases occ with _ | ⟨a, _ | ⟨b, t⟩⟩ <;> simp_all
    have hi0 : occ.getD 0 0 < m := by
      rw [hget0] at hocc; exact hocc _ (by simp)
    simp only [hl, ↓reduceIte, List.filter_append, List.length_append,
      hmem_cg base hbase, hmem_cg (base + 6) (by omega), Nat.add_zero]
    have hmem_iff : i ∈ occ ↔ i = occ.getD 0 0 := by nth_rw 1 [hget0]; exact List.mem_singleton
    have : r = 0 ∨ r = 1 ∨ r = 2 := by omega
    by_cases heq : i = occ.getD 0 0
    · simp only [hmem_iff.mpr heq, ↓reduceIte]; subst heq
      rcases this with rfl | rfl | rfl <;>
        (rw [hcount_iff]; simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
          List.mem_cons, List.not_mem_nil,
            or_false]; grind)
    · simp only [show ¬ i ∈ occ from fun h => heq (hmem_iff.mp h), ↓reduceIte]
      rcases this with rfl | rfl | rfl <;>
        (rw [hcount_iff]; simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
          List.mem_cons, List.not_mem_nil,
            or_false]; grind)
  · have hget : occ = [occ.getD 0 0, occ.getD 1 0] := by
      rcases occ with _ | ⟨a, _ | ⟨b, _ | ⟨d, t⟩⟩⟩ <;> simp_all
    have hi0 : occ.getD 0 0 < m := by rw [hget] at hocc; exact hocc _ (by simp)
    have hi1 : occ.getD 1 0 < m := by rw [hget] at hocc; exact hocc _ (by simp)
    have hne : occ.getD 0 0 ≠ occ.getD 1 0 := by rw [hget] at hnd; simpa using hnd
    simp only [hl, show (2 : ℕ) ≠ 1 by decide, ↓reduceIte, List.filter_append, List.length_append,
      hmem_cg base hbase, Nat.add_zero]
    have hmem_iff : i ∈ occ ↔ i = occ.getD 0 0 ∨ i = occ.getD 1 0 := by
      nth_rw 1 [hget]; simp
    have : r = 0 ∨ r = 1 ∨ r = 2 := by omega
    by_cases heq0 : i = occ.getD 0 0
    · simp only [hmem_iff.mpr (Or.inl heq0), ↓reduceIte]; subst heq0
      rcases this with rfl | rfl | rfl <;>
        (rw [hcount_iff]; simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
          List.mem_cons, List.not_mem_nil,
            or_false]; grind)
    · by_cases heq1 : i = occ.getD 1 0
      · simp only [hmem_iff.mpr (Or.inr heq1), ↓reduceIte]; subst heq1
        rcases this with rfl | rfl | rfl <;>
          (rw [hcount_iff]; simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
            List.mem_cons, List.not_mem_nil,
              or_false]; grind)
      · simp only [show ¬ i ∈ occ from fun h => by
        rcases hmem_iff.mp h with h0 | h1 <;> contradiction,
          ↓reduceIte]
        rcases this with rfl | rfl | rfl <;>
          (rw [hcount_iff]; simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
            List.mem_cons, List.not_mem_nil,
              or_false]; grind)
  · have hget : occ = [occ.getD 0 0, occ.getD 1 0, occ.getD 2 0] := by
      rcases occ with _ | ⟨a, _ | ⟨b, _ | ⟨d, _ | ⟨e, t⟩⟩⟩⟩ <;> simp_all
    have hi0 : occ.getD 0 0 < m := by rw [hget] at hocc; exact hocc _ (by simp)
    have hi1 : occ.getD 1 0 < m := by rw [hget] at hocc; exact hocc _ (by simp)
    have hi2 : occ.getD 2 0 < m := by rw [hget] at hocc; exact hocc _ (by simp)
    have hne01 : occ.getD 0 0 ≠ occ.getD 1 0 := by
      rw [hget] at hnd; simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
        or_false, not_or] at hnd; exact hnd.1.1
    have hne02 : occ.getD 0 0 ≠ occ.getD 2 0 := by
      rw [hget] at hnd; simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
        or_false, not_or] at hnd; exact hnd.1.2
    have hne12 : occ.getD 1 0 ≠ occ.getD 2 0 := by
      rw [hget] at hnd; simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
        or_false, not_or] at hnd; exact hnd.2.1
    simp only [hl, show (3 : ℕ) ≠ 1 by decide, show (3 : ℕ) ≠ 2 by decide, ↓reduceIte,
      List.filter_append, List.length_append, hmem_cg base hbase, hmem_cg (base + 6) (by omega),
      hmem_cg (base + 12) (by omega), Nat.add_zero]
    have hmem_iff : i ∈ occ ↔ i = occ.getD 0 0 ∨ i = occ.getD 1 0 ∨ i = occ.getD 2 0 := by
      nth_rw 1 [hget]; simp
    have : r = 0 ∨ r = 1 ∨ r = 2 := by omega
    by_cases heq0 : i = occ.getD 0 0
    · simp only [hmem_iff.mpr (Or.inl heq0), ↓reduceIte]; subst heq0
      rcases this with rfl | rfl | rfl <;>
        (rw [hcount_iff]; simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
          List.mem_cons, List.not_mem_nil,
            or_false]; grind)
    · by_cases heq1 : i = occ.getD 1 0
      · simp only [hmem_iff.mpr (Or.inr (Or.inl heq1)), ↓reduceIte]; subst heq1
        rcases this with rfl | rfl | rfl <;>
          (rw [hcount_iff]; simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
            List.mem_cons, List.not_mem_nil,
              or_false]; grind)
      · by_cases heq2 : i = occ.getD 2 0
        · simp only [hmem_iff.mpr (Or.inr (Or.inr heq2)), ↓reduceIte]; subst heq2
          rcases this with rfl | rfl | rfl <;>
            (rw [hcount_iff]; simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
              List.mem_cons, List.not_mem_nil,
                or_false]; grind)
        · simp only [show ¬ i ∈ occ from fun h => by
              rcases hmem_iff.mp h with h0 | h1 | h2 <;> contradiction, ↓reduceIte]
          rcases this with rfl | rfl | rfl <;>
            (rw [hcount_iff]; simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
              List.mem_cons, List.not_mem_nil,
                or_false]; grind)

theorem varClauses_dummy_count {m base : ℕ} {occ : List ℕ}
    (hbase : 3 * m ≤ base) (hocc : ∀ i ∈ occ, i < m)
    (h1 : 1 ≤ occ.length) (h3 : occ.length ≤ 3) {u : ℕ}
    (hu_lo : base ≤ u) (hu_hi : u < base + 6 * gadgetCount occ.length) :
    ((varClauses m base occ).filter (fun c => decide (u ∈ c))).length = 3 := by
  have hcount_iff : ∀ (a : ℕ) (L : List (List ℕ)),
      (L.filter (fun c => decide (a ∈ c))).length =
        ((L.map (fun c => if a ∈ c then 1 else 0)).sum) := by
    intro a L; induction L with
    | nil => simp
    | cons c cs ih => by_cases h : a ∈ c <;> simp [h, ih, Nat.add_comm]
  have hmem_cg_zero : ∀ b, (u < b ∨ b + 6 ≤ u) →
      ((choiceGadget b).filter (fun c => decide (u ∈ c))).length = 0 := by
    intro b hb
    rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
    intro c hc; simp only [decide_eq_true_eq]; intro hmem
    have := choiceGadget_elem_range hc hmem; omega
  have hcg_hit : ∀ b, b ≤ u → u < b + 6 →
      ((choiceGadget b).filter (fun c => decide (u ∈ c))).length =
        if u < b + 3 then 2 else 3 := by
    intro b hlo hhi
    by_cases hlt : u < b + 3
    · simp only [hlt, ↓reduceIte]
      have := choiceGadget_port_count b (u - b) (by omega)
      simpa [show b + (u - b) = u by omega] using this
    · simp only [hlt, ↓reduceIte]
      have := choiceGadget_internal_count b (u - (b + 3)) (by omega)
      simpa [show b + 3 + (u - (b + 3)) = u by omega] using this
  unfold varClauses
  unfold gadgetCount at hu_hi
  have hlen : occ.length = 1 ∨ occ.length = 2 ∨ occ.length = 3 := by omega
  rcases hlen with hl | hl | hl
  · have hi0 : occ.getD 0 0 < m := hocc _ (getD_mem_of_lt (by omega))
    simp only [hl, ↓reduceIte, List.filter_append, List.length_append] at hu_hi ⊢
    by_cases hlt6 : u < base + 6
    · rw [hmem_cg_zero (base + 6) (Or.inl (by omega)), hcg_hit base hu_lo hlt6]
      have : u = base ∨ u = base + 1 ∨ u = base + 2 ∨ base + 3 ≤ u := by omega
      rcases this with rfl | rfl | rfl | hge
      · rw [hcount_iff]; simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        List.mem_cons, List.not_mem_nil,
          or_false]; grind
      · rw [hcount_iff]; simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        List.mem_cons, List.not_mem_nil,
          or_false]; grind
      · rw [hcount_iff]; simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        List.mem_cons, List.not_mem_nil,
          or_false]; grind
      · rw [hcount_iff]; simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        List.mem_cons, List.not_mem_nil,
          or_false]; grind
    · rw [hmem_cg_zero base (Or.inr (by omega)),
        hcg_hit (base + 6) (by omega) (by omega)]
      have : u = base + 6 ∨ u = base + 7 ∨ u = base + 8 ∨ base + 9 ≤ u := by omega
      rcases this with rfl | rfl | rfl | hge
      · rw [hcount_iff]; simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        List.mem_cons, List.not_mem_nil,
          or_false]; grind
      · rw [hcount_iff]; simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        List.mem_cons, List.not_mem_nil,
          or_false]; grind
      · rw [hcount_iff]; simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        List.mem_cons, List.not_mem_nil,
          or_false]; grind
      · rw [hcount_iff]; simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        List.mem_cons, List.not_mem_nil,
          or_false]; grind
  · have hi0 : occ.getD 0 0 < m := hocc _ (getD_mem_of_lt (by omega))
    have hi1 : occ.getD 1 0 < m := hocc _ (getD_mem_of_lt (by omega))
    simp only [hl, show (2 : ℕ) ≠ 1 by decide, ↓reduceIte, List.filter_append,
      List.length_append] at hu_hi ⊢
    rw [hcg_hit base hu_lo (by omega)]
    have : u = base ∨ u = base + 1 ∨ u = base + 2 ∨ base + 3 ≤ u := by omega
    rcases this with rfl | rfl | rfl | hge
    · rw [hcount_iff]; simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      List.mem_cons, List.not_mem_nil,
        or_false]; grind
    · rw [hcount_iff]; simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      List.mem_cons, List.not_mem_nil,
        or_false]; grind
    · rw [hcount_iff]; simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      List.mem_cons, List.not_mem_nil,
        or_false]; grind
    · rw [hcount_iff]; simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      List.mem_cons, List.not_mem_nil,
        or_false]; grind
  · have hi0 : occ.getD 0 0 < m := hocc _ (getD_mem_of_lt (by omega))
    have hi1 : occ.getD 1 0 < m := hocc _ (getD_mem_of_lt (by omega))
    have hi2 : occ.getD 2 0 < m := hocc _ (getD_mem_of_lt (by omega))
    simp only [hl, show (3 : ℕ) ≠ 1 by decide, show (3 : ℕ) ≠ 2 by decide, ↓reduceIte,
      List.filter_append, List.length_append] at hu_hi ⊢
    by_cases hlt6 : u < base + 6
    · rw [hmem_cg_zero (base + 6) (Or.inl (by omega)),
        hmem_cg_zero (base + 12) (Or.inl (by omega)), hcg_hit base hu_lo hlt6]
      have : u = base ∨ u = base + 1 ∨ u = base + 2 ∨ base + 3 ≤ u := by omega
      rcases this with rfl | rfl | rfl | hge
      · rw [hcount_iff]; simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        List.mem_cons, List.not_mem_nil,
          or_false]; grind
      · rw [hcount_iff]; simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        List.mem_cons, List.not_mem_nil,
          or_false]; grind
      · rw [hcount_iff]; simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        List.mem_cons, List.not_mem_nil,
          or_false]; grind
      · rw [hcount_iff]; simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        List.mem_cons, List.not_mem_nil,
          or_false]; grind
    · by_cases hlt12 : u < base + 12
      · rw [hmem_cg_zero base (Or.inr (by omega)),
          hmem_cg_zero (base + 12) (Or.inl (by omega)), hcg_hit (base + 6) (by omega) hlt12]
        have : u = base + 6 ∨ u = base + 7 ∨ u = base + 8 ∨ base + 9 ≤ u := by omega
        rcases this with rfl | rfl | rfl | hge
        · rw [hcount_iff]; simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
          List.mem_cons, List.not_mem_nil,
            or_false]; grind
        · rw [hcount_iff]; simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
          List.mem_cons, List.not_mem_nil,
            or_false]; grind
        · rw [hcount_iff]; simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
          List.mem_cons, List.not_mem_nil,
            or_false]; grind
        · rw [hcount_iff]; simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
          List.mem_cons, List.not_mem_nil,
            or_false]; grind
      · rw [hmem_cg_zero base (Or.inr (by omega)),
          hmem_cg_zero (base + 6) (Or.inr (by omega)), hcg_hit (base + 12) (by omega) (by omega)]
        have : u = base + 12 ∨ u = base + 13 ∨ u = base + 14 ∨ base + 15 ≤ u := by omega
        rcases this with rfl | rfl | rfl | hge
        · rw [hcount_iff]; simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
          List.mem_cons, List.not_mem_nil,
            or_false]; grind
        · rw [hcount_iff]; simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
          List.mem_cons, List.not_mem_nil,
            or_false]; grind
        · rw [hcount_iff]; simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
          List.mem_cons, List.not_mem_nil,
            or_false]; grind
        · rw [hcount_iff]; simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
          List.mem_cons, List.not_mem_nil,
            or_false]; grind

private theorem sum_length_flatMap_range {α : Type*} (n : ℕ) (f : ℕ → List α) :
    ((List.range n).flatMap f).length = ((List.range n).map (fun k => (f k).length)).sum := by
  rw [List.length_flatMap]

theorem reduce_isWellFormed {φ : CNF ℕ}
    (hs : PositiveOneInExactThreeSATThree.syntaxCheck φ = true) (hne : φ.isEmpty = false) :
    (reduce φ).IsWellFormed := by
  have ⟨hexact, hpos, hcnt⟩ := (PositiveOneInExactThreeSATThree.syntaxCheck_iff φ).mp hs
  set vs := distinctVars φ with hvs_def
  set m := φ.length with hm_def
  set G := gadgetPrefix φ vs vs.length with hG_def
  have hm_pos : 1 ≤ m := by
    cases h : φ with
    | nil => simp [h] at hne
    | cons _ _ => simp [hm_def, h]
  have hvs_mem : ∀ k < vs.length, vs.getD k 0 ∈ φ.vars := fun k hk => by
    have : vs.getD k 0 ∈ vs := by simp [List.getD_eq_getElem?_getD, hk]
    exact List.mem_eraseDupsBy_eq.mp this
  have hocc_bounds : ∀ k < vs.length,
      1 ≤ (occIndices φ (vs.getD k 0)).length ∧ (occIndices φ (vs.getD k 0)).length ≤ 3 := by
    intro k hk
    rw [count_occIndices_eq φ _ (fun c hc => (hexact c hc).2)]
    exact ⟨Nat.succ_le_of_lt (List.count_pos_iff.mpr (hvs_mem k hk)), hcnt _⟩
  have hocc_lt : ∀ k, ∀ i ∈ occIndices φ (vs.getD k 0), i < m := fun k i hi =>
    (mem_occIndices_iff.mp hi).1
  have hred : reduce φ = ⟨m + 2 * G, (List.range vs.length).flatMap fun k =>
      varClauses m (3 * m + 6 * gadgetPrefix φ vs k) (occIndices φ (vs.getD k 0))⟩ := by
    simp [reduce, hs, hne, hvs_def, hm_def, hG_def]
  rw [hred]
  have hbase_lt : ∀ k < vs.length,
      3 * m + 6 * gadgetPrefix φ vs k + 6 * gadgetCount (occIndices φ (vs.getD k 0)).length ≤
        3 * (m + 2 * G) := by
    intro k hk
    have := gadgetPrefix_succ_le φ vs hk
    omega
  refine ⟨by dsimp only; omega, ?_, ?_, ?_, ?_⟩
  · -- Length = 3 * (m + 2 * G)
    dsimp only
    rw [List.length_flatMap]
    have hsum_occ :
        ((List.range vs.length).map fun k => (occIndices φ (vs.getD k 0)).length).sum = 3 * m := by
      have hcount_sum :
          ((List.range vs.length).map fun k => φ.vars.count (vs.getD k 0)).sum =
            φ.vars.length := by
        have hmap : (List.range vs.length).map (fun k => φ.vars.count (vs.getD k 0)) =
            vs.map (fun v => φ.vars.count v) := by
          conv_rhs => rw [← map_getD_range vs 0, List.map_map]
          rfl
        rw [hmap]
        have hperm : ∀ (l : List ℕ),
            ((l.eraseDupsBy (fun a b => decide (a = b))).map (fun v => l.count v)).sum =
              l.length := by
          intro l
          have h1 : ∀ (s : List ℕ), s.Nodup → (∀ v ∈ l, v ∈ s) →
              (s.map (fun v => l.count v)).sum = l.length := by
            intro s hnd hs_mem
            induction l with
            | nil => simp
            | cons a t ih =>
              have ha : a ∈ s := hs_mem a (List.mem_cons_self ..)
              have ht : ∀ v ∈ t, v ∈ s := fun v hv => hs_mem v (List.mem_cons_of_mem _ hv)
              simp only [List.length_cons, List.count_cons]
              rw [← ih ht]
              have hsum_add : (s.map fun v => t.count v + (if a == v then 1 else 0)).sum =
                  (s.map fun v => t.count v).sum +
                    (s.map fun v => if a == v then 1 else 0).sum := by
                clear ih ht hs_mem hnd ha
                induction s with
                | nil => simp
                | cons x xs ihs => simp only [List.map_cons, List.sum_cons, ihs]; omega
              rw [hsum_add]
              have h1s : (s.map fun v => if a == v then 1 else 0).sum = 1 := by
                clear ih ht hs_mem hsum_add
                induction s with
                | nil => simp at ha
                | cons x xs ihs =>
                  rw [List.nodup_cons] at hnd
                  simp only [List.mem_cons] at ha
                  rcases ha with rfl | hxa
                  · have h0 : (xs.map fun v => if a == v then 1 else 0).sum = 0 := by
                      rw [List.sum_eq_zero_iff]
                      intro y hy
                      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hy
                      have : a ≠ v := fun h => hnd.1 (h ▸ hv)
                      simp [this]
                    simp only [List.map_cons, List.sum_cons, beq_self_eq_true, ↓reduceIte, h0]
                  · have hne_xa : a ≠ x := fun h => hnd.1 (h ▸ hxa)
                    simp only [List.map_cons, List.sum_cons, beq_false_of_ne hne_xa,
                      Bool.false_eq_true, ↓reduceIte, ihs hnd.2 hxa, Nat.zero_add]
              omega
          exact h1 _ (List.nodup_eraseDupsBy_eq l) (fun v hv => List.mem_eraseDupsBy_eq.mpr hv)
        exact hperm φ.vars
      have hlen_vars : φ.vars.length = 3 * m := by
        simp only [CNF.vars, List.length_map, List.length_flatten]
        have hmap3 : φ.map List.length = φ.map (fun _ => 3) :=
          List.map_congr_left fun c hc => (hexact c hc).1
        rw [hmap3]
        have hsum3 : ∀ l : List (Clause ℕ), (l.map fun _ => 3).sum = 3 * l.length := by
          intro l; induction l with
          | nil => simp
          | cons _ _ ih => simp only [List.map_cons, List.sum_cons, List.length_cons, ih]; omega
        exact hsum3 φ
      rw [← hlen_vars, ← hcount_sum]
      refine congrArg List.sum (List.map_congr_left fun k hk => ?_)
      exact count_occIndices_eq φ _ (fun c hc => (hexact c hc).2)
    have hmain : ∀ n ≤ vs.length,
        ((List.range n).map fun k =>
          (varClauses m (3 * m + 6 * gadgetPrefix φ vs k)
            (occIndices φ (vs.getD k 0))).length).sum =
        ((List.range n).map fun k => (occIndices φ (vs.getD k 0)).length).sum +
          6 * gadgetPrefix φ vs n := by
      intro n hn
      induction n with
      | zero => simp [gadgetPrefix]
      | succ k ih =>
        have hk : k < vs.length := by omega
        have hb := hocc_bounds k hk
        simp only [List.range_succ, List.map_append, List.sum_append, List.map_singleton,
          List.sum_singleton, gadgetPrefix]
        have hvc := length_varClauses m (3 * m + 6 * gadgetPrefix φ vs k)
          (occIndices φ (vs.getD k 0)) hb.1 hb.2
        have hgc := gadgetCount_eq (occIndices φ (vs.getD k 0)).length hb.1 hb.2
        have ih' := ih (by omega)
        split_ifs at hvc hgc <;> omega
    have hfull := hmain vs.length le_rfl
    rw [hsum_occ] at hfull
    omega
  · -- Nodup of clauses
    dsimp only
    rw [List.nodup_flatMap]
    refine ⟨fun k hk => varClauses_nodup (by omega) (hocc_lt k), ?_⟩
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    simp only [List.getElem_range]
    intro c hc1 hc2
    have hdisj : ∀ a b, a < b → b < vs.length →
        ∀ c ∈ varClauses m (3 * m + 6 * gadgetPrefix φ vs a) (occIndices φ (vs.getD a 0)),
        c ∉ varClauses m (3 * m + 6 * gadgetPrefix φ vs b) (occIndices φ (vs.getD b 0)) := by
      intro a b hab hb c hca hcb
      have hba : 3 * m + 6 * gadgetPrefix φ vs a +
          6 * gadgetCount (occIndices φ (vs.getD a 0)).length ≤
          3 * m + 6 * gadgetPrefix φ vs b := by
        have := gadgetPrefix_mono φ vs hab
        simp only [gadgetPrefix] at this
        omega
      have hhas_dummy : ∃ u ∈ c,
          3 * m + 6 * gadgetPrefix φ vs a ≤ u ∧
            u < 3 * m + 6 * gadgetPrefix φ vs a +
              6 * gadgetCount (occIndices φ (vs.getD a 0)).length := by
        set ba := 3 * m + 6 * gadgetPrefix φ vs a
        unfold varClauses at hca
        unfold gadgetCount
        split_ifs at hca with h1 h2 h3
        · rw [h1]; simp only [↓reduceIte]
          simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hca
          rcases hca with ((rfl | rfl | rfl) | hcg) | hcg
          · exact ⟨ba, by simp, by omega, by omega⟩
          · exact ⟨ba + 1, by simp, by omega, by omega⟩
          · exact ⟨ba + 2, by simp, by omega, by omega⟩
          · rw [mem_choiceGadget_iff] at hcg
            rcases hcg with rfl | rfl | rfl | rfl | rfl <;>
              exact ⟨_, List.mem_cons_self, by omega, by omega⟩
          · rw [mem_choiceGadget_iff] at hcg
            rcases hcg with rfl | rfl | rfl | rfl | rfl <;>
              exact ⟨_, List.mem_cons_self, by omega, by omega⟩
        · rw [h2]; simp only [show (2 : ℕ) ≠ 1 by decide, ↓reduceIte]
          simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hca
          rcases hca with (rfl | rfl | rfl) | hcg
          · exact ⟨ba, by simp, by omega, by omega⟩
          · exact ⟨ba + 1, by simp, by omega, by omega⟩
          · exact ⟨ba + 2, by simp, by omega, by omega⟩
          · rw [mem_choiceGadget_iff] at hcg
            rcases hcg with rfl | rfl | rfl | rfl | rfl <;>
              exact ⟨_, List.mem_cons_self, by omega, by omega⟩
        · rw [h3]; simp only [show (3 : ℕ) ≠ 1 by decide, show (3 : ℕ) ≠ 2 by decide, ↓reduceIte]
          simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hca
          rcases hca with (((rfl | rfl | rfl | rfl | rfl | rfl) | hcg) | hcg) | hcg
          · exact ⟨ba, by simp, by omega, by omega⟩
          · exact ⟨ba + 1, by simp, by omega, by omega⟩
          · exact ⟨ba + 6, by simp, by omega, by omega⟩
          · exact ⟨ba + 7, by simp, by omega, by omega⟩
          · exact ⟨ba + 12, by simp, by omega, by omega⟩
          · exact ⟨ba + 13, by simp, by omega, by omega⟩
          · rw [mem_choiceGadget_iff] at hcg
            rcases hcg with rfl | rfl | rfl | rfl | rfl <;>
              exact ⟨_, List.mem_cons_self, by omega, by omega⟩
          · rw [mem_choiceGadget_iff] at hcg
            rcases hcg with rfl | rfl | rfl | rfl | rfl <;>
              exact ⟨_, List.mem_cons_self, by omega, by omega⟩
          · rw [mem_choiceGadget_iff] at hcg
            rcases hcg with rfl | rfl | rfl | rfl | rfl <;>
              exact ⟨_, List.mem_cons_self, by omega, by omega⟩
        · simp at hca
      obtain ⟨u, huc, hlo, hhi⟩ := hhas_dummy
      rcases varClauses_elem_lt (hocc_lt b) hcb huc with hlt | ⟨hlo2, _⟩ <;> omega
    exact hdisj i j hij (by simpa using hj) c hc1 hc2
  · -- Each clause is a triple < 3 * (m + 2 * G)
    dsimp only
    intro c hc
    obtain ⟨k, hk, hck⟩ := List.mem_flatMap.mp hc
    rw [List.mem_range] at hk
    have htri := varClauses_isTriple (by omega) (nodup_occIndices φ _) (hocc_lt k) hck
    refine ⟨htri.1, htri.2, fun u hu => ?_⟩
    rcases varClauses_elem_lt (hocc_lt k) hck hu with hlt | ⟨_, hhi⟩
    · omega
    · exact lt_of_lt_of_le hhi (hbase_lt k hk)
  · -- Every element < 3 * (m + 2 * G) appears in exactly 3 clauses
    dsimp only
    intro u hu
    have hflat_filter : ∀ (L : List ℕ) (f : ℕ → List (List ℕ)),
        ((L.flatMap f).filter (fun c => decide (u ∈ c))).length =
          (L.map fun k => ((f k).filter (fun c => decide (u ∈ c))).length).sum := by
      intro L f
      induction L with
      | nil => simp
      | cons a t ih => simp [List.filter_append, ih]
    rw [hflat_filter]
    by_cases hum : u < 3 * m
    · -- Clause element u = 3 * i + r
      set i := u / 3
      set r := u % 3
      have hi : i < m := by omega
      have hr : r < 3 := by omega
      have hu_eq : u = 3 * i + r := by omega
      rw [hu_eq]
      have hmap_eq :
          ((List.range vs.length).map fun k =>
            ((varClauses m (3 * m + 6 * gadgetPrefix φ vs k)
              (occIndices φ (vs.getD k 0))).filter (fun c => decide (3 * i + r ∈ c))).length) =
          (List.range vs.length).map fun k =>
            if i ∈ occIndices φ (vs.getD k 0) then 1 else 0 := by
        refine List.map_congr_left fun k hk => ?_
        rw [List.mem_range] at hk
        exact varClauses_clause_count (by omega) (nodup_occIndices φ _) (hocc_lt k)
          (hocc_bounds k hk).1 (hocc_bounds k hk).2 hi hr
      rw [hmap_eq]
      -- Count variables in vs occurring in clause i = 3
      have hci : φ.getD i [] ∈ φ := getD_mem_of_lt hi
      have hlen_ci : ((φ.getD i []).map Prod.fst).length = 3 := by
        rw [List.length_map]; exact (hexact _ hci).1
      have hnd_ci : ((φ.getD i []).map Prod.fst).Nodup := (hexact _ hci).2
      have hsub_ci : ∀ v ∈ (φ.getD i []).map Prod.fst, v ∈ vs := fun v hv => by
        rw [hvs_def, distinctVars, List.mem_eraseDupsBy_eq]
        obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hv
        exact List.mem_map.mpr ⟨l, List.mem_flatten.mpr ⟨_, hci, hl⟩, rfl⟩
      have hsum_vs : ∀ (s : List ℕ), s.Nodup → (∀ v ∈ (φ.getD i []).map Prod.fst, v ∈ s) →
          ((List.range s.length).map fun k =>
            if s.getD k 0 ∈ (φ.getD i []).map Prod.fst then 1 else 0).sum = 3 := by
        intro s hnds hs_sub
        set tgt := (φ.getD i []).map Prod.fst
        have hmap2 :
            ((List.range s.length).map fun k => if s.getD k 0 ∈ tgt then 1 else 0) =
            s.map fun v => if v ∈ tgt then 1 else 0 := by
          conv_rhs => rw [← map_getD_range s 0, List.map_map]
          rfl
        rw [hmap2]
        have hfilt : (s.map fun v => if v ∈ tgt then 1 else 0).sum =
            (s.filter (fun v => decide (v ∈ tgt))).length := by
          clear hnds hs_sub hmap2
          induction s with
          | nil => simp
          | cons x xs ih =>
            by_cases hx : x ∈ tgt <;> simp [hx, ih, Nat.add_comm]
        rw [hfilt]
        have hperm : (s.filter (fun v => decide (v ∈ tgt))).length = tgt.length := by
          have hset : (s.filter (fun v => decide (v ∈ tgt))).toFinset = tgt.toFinset := by
            ext v
            simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq, and_iff_right_iff_imp]
            exact hs_sub v
          have h1 := List.toFinset_card_of_nodup (hnds.filter fun v => decide (v ∈ tgt))
          have h2 := List.toFinset_card_of_nodup hnd_ci
          rw [← h1, hset, h2]
        rw [hperm, hlen_ci]
      have hmap_occ :
          ((List.range vs.length).map fun k =>
            if i ∈ occIndices φ (vs.getD k 0) then 1 else 0) =
          ((List.range vs.length).map fun k =>
            if vs.getD k 0 ∈ (φ.getD i []).map Prod.fst then 1 else 0) := by
        refine List.map_congr_left fun k _ => ?_
        have hiff : i ∈ occIndices φ (vs.getD k 0) ↔ vs.getD k 0 ∈ (φ.getD i []).map Prod.fst :=
          ⟨fun hm => (mem_occIndices_iff.mp hm).2, fun hm => mem_occIndices_iff.mpr ⟨hi, hm⟩⟩
        exact if_congr hiff rfl rfl
      rw [hmap_occ]
      exact hsum_vs vs (List.nodup_eraseDupsBy_eq _) hsub_ci
    · -- Dummy element u ∈ [3 * m, 3 * m + 6 * G)
      have hexists_k : ∃ k < vs.length,
          3 * m + 6 * gadgetPrefix φ vs k ≤ u ∧
            u < 3 * m + 6 * gadgetPrefix φ vs (k + 1) := by
        have hfind : ∀ n ≤ vs.length, 3 * m ≤ u → u < 3 * m + 6 * gadgetPrefix φ vs n →
            ∃ k < n, 3 * m + 6 * gadgetPrefix φ vs k ≤ u ∧
              u < 3 * m + 6 * gadgetPrefix φ vs (k + 1) := by
          intro n
          induction n with
          | zero => intro _ _ hhi; simp [gadgetPrefix] at hhi; omega
          | succ n' ih =>
            intro hn' hlo hhi
            by_cases hlt : u < 3 * m + 6 * gadgetPrefix φ vs n'
            · obtain ⟨k, hk, h1, h2⟩ := ih (by omega) hlo hlt
              exact ⟨k, by omega, h1, h2⟩
            · exact ⟨n', Nat.lt_succ_self _, by omega, hhi⟩
        exact hfind vs.length le_rfl (by omega) (by omega)
      obtain ⟨k₀, hk₀, hlo₀, hhi₀⟩ := hexists_k
      have honly : ∀ k < vs.length, k ≠ k₀ →
          ((varClauses m (3 * m + 6 * gadgetPrefix φ vs k)
            (occIndices φ (vs.getD k 0))).filter (fun c => decide (u ∈ c))).length = 0 := by
        intro k hk hne
        rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
        intro c hc; simp only [decide_eq_true_eq]; intro huc
        rcases varClauses_elem_lt (hocc_lt k) hc huc with hlt | ⟨hlo, hhi⟩
        · omega
        · by_cases hlt_k : k < k₀
          · have := gadgetPrefix_mono φ vs (show k + 1 ≤ k₀ by omega)
            simp only [gadgetPrefix] at this; omega
          · have := gadgetPrefix_mono φ vs (show k₀ + 1 ≤ k by omega)
            omega
      have hsum_single : ∀ (n : ℕ) (f : ℕ → ℕ), k₀ < n → (∀ k < n, k ≠ k₀ → f k = 0) →
          ((List.range n).map f).sum = f k₀ := by
        intro n f hk0 hz
        induction n with
        | zero => omega
        | succ n' ih =>
          rw [List.range_succ, List.map_append, List.sum_append, List.map_singleton,
            List.sum_singleton]
          by_cases heq : k₀ = n'
          · subst heq
            have h0 : ((List.range k₀).map f).sum = 0 :=
              List.sum_eq_zero fun x hx => by
                obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
                exact hz j (by rw [List.mem_range] at hj; omega)
                  (by rw [List.mem_range] at hj; omega)
            omega
          · rw [hz n' (Nat.lt_succ_self _) (Ne.symm heq),
            ih (by omega) (fun k hk => hz k (by omega))]
            omega
      rw [hsum_single vs.length _ hk₀ honly]
      exact varClauses_dummy_count (by omega) (hocc_lt k₀) (hocc_bounds k₀ hk₀).1
        (hocc_bounds k₀ hk₀).2 hlo₀ (by simp only [gadgetPrefix] at hhi₀; omega)


end RXC3

end CslibFrontier.Complexity
