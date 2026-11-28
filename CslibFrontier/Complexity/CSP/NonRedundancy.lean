/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FormalPapers Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Finset.Card

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# CSP Non-Redundancy, Chain Length, Conditional Lifting, and Linear Zero-Locus Bounds

For a constraint satisfaction problem specified by an arity-`r` relation `R ⊆ D^r` over domain `D`,
an ordered family of `m` constraint scopes `S : Fin m → (Fin r → Fin n)` on `n` variables is:
- **non-redundant** (`IsNonRedundant R S`) if for every `i`, some assignment `φ : Fin n → D`
  satisfies all `S j` (`j ≠ i`) while falsifying `S i`;
- a **chain-length witness** (`IsChainLengthWitness R S`) if for every `i`, some assignment
  `φ : Fin n → D` satisfies all preceding `S j` (`j < i`) while falsifying `S i`.

The extremal quantities `nonRedundancy R n` and `chainLength R n` govern the space complexity of
streaming CSP decidability, unweighted and weighted CSP sparsification, kernelization, and query
learnability. Analogous conditional notions `condNonRedundancy P Q n` and `condChainLength P Q n`
for nested relations `P ⊆ Q ⊆ D^r` require satisfying assignments to land in `P` and witnessing
falsifications to land in `Q \ P`.

## Main definitions

* `CslibFrontier.Complexity.CSP.evalScope`: evaluate an assignment `φ : V → D` along an arity-`r`
  scope `S : Fin r → V`.
* `CslibFrontier.Complexity.CSP.IsNonRedundant`, `CslibFrontier.Complexity.CSP.nonRedundancy`:
  non-redundant CSP families and maximum non-redundancy on `n` variables.
* `CslibFrontier.Complexity.CSP.IsChainLengthWitness`, `CslibFrontier.Complexity.CSP.chainLength`:
  ordered chain-length witnesses and maximum chain length on `n` variables.
* `CslibFrontier.Complexity.CSP.IsCondNonRedundant`,
  `CslibFrontier.Complexity.CSP.condNonRedundancy`,
  `CslibFrontier.Complexity.CSP.IsCondChainLengthWitness`,
  `CslibFrontier.Complexity.CSP.condChainLength`: conditional CSP counterparts for `P ∣ Q`.
* `CslibFrontier.Complexity.CSP.prodSetRel`, `CslibFrontier.Complexity.CSP.liftRel`: arity-`(r + 1)`
  Cartesian extension `Q × A` and conditional-to-unconditional gadget `(P × {a}) ∪ (Q × {b})`.

## Main results

* `CslibFrontier.Complexity.CSP.nonRedundancy_le_chainLength`:
  `nonRedundancy R n ≤ chainLength R n`.
* `CslibFrontier.Complexity.CSP.condNonRedundancy_le_condChainLength`:
  `condNonRedundancy P Q n ≤ condChainLength P Q n`.
* `CslibFrontier.Complexity.CSP.nonRedundancy_liftRel_le`: conditional-to-unconditional lifting
  upper bound `nonRedundancy (liftRel P Q a b) n ≤ n * condNonRedundancy P Q n +
  nonRedundancy (prodSetRel Q {a, b}) n` for `P ⊆ Q` and `a ≠ b`.
* `CslibFrontier.Complexity.CSP.chainLength_liftRel_ge`: conditional-to-unconditional lifting lower
  bound `n₂ * condChainLength P Q n₁ ≤ chainLength (liftRel P Q a b) (n₁ + n₂)` for `P ⊆ Q` and
  `a ≠ b`.
* `CslibFrontier.Complexity.CSP.chainLength_le_of_linear_zero_locus` and
  `CslibFrontier.Complexity.CSP.nonRedundancy_le_of_linear_zero_locus`: if `R₀` is cut out as the
  zero locus of linear forms over a `Fintype` feature basis `ι` over a field `K`, then
  `nonRedundancy R₀ n ≤ chainLength R₀ n ≤ Fintype.card ι`.
-/

public section

namespace CslibFrontier.Complexity.CSP

open Finset

section Basic

variable {r m n : ℕ} {V D : Type*}

/-- Evaluate an assignment `φ : V → D` along an arity-`r` variable scope `S : Fin r → V`. -/
@[expose] def evalScope (φ : V → D) (S : Fin r → V) : Fin r → D :=
  φ ∘ S

@[simp]
theorem evalScope_apply (φ : V → D) (S : Fin r → V) (k : Fin r) :
    evalScope φ S k = φ (S k) :=
  rfl

/-- A family of `m` scopes `S : Fin m → (Fin r → Fin n)` is non-redundant for `R ⊆ D^r` if each
constraint can be uniquely falsified while satisfying all other constraints. -/
def IsNonRedundant (R : Set (Fin r → D)) (S : Fin m → (Fin r → Fin n)) : Prop :=
  ∀ i : Fin m, ∃ φ : Fin n → D, (∀ j : Fin m, j ≠ i → evalScope φ (S j) ∈ R) ∧
    evalScope φ (S i) ∉ R

/-- A family of `m` scopes `S : Fin m → (Fin r → Fin n)` is a valid chain-length witness for
`R ⊆ D^r` if each constraint can be falsified while satisfying all preceding constraints. -/
def IsChainLengthWitness (R : Set (Fin r → D)) (S : Fin m → (Fin r → Fin n)) : Prop :=
  ∀ i : Fin m, ∃ φ : Fin n → D, (∀ j : Fin m, j < i → evalScope φ (S j) ∈ R) ∧
    evalScope φ (S i) ∉ R

/-- Every non-redundant constraint family is a valid chain-length witness. -/
theorem IsNonRedundant.isChainLengthWitness {R : Set (Fin r → D)}
    {S : Fin m → (Fin r → Fin n)} (h : IsNonRedundant R S) :
    IsChainLengthWitness R S := by
  intro i
  obtain ⟨φ, hsat, hunsat⟩ := h i
  exact ⟨φ, fun j hj ↦ hsat j hj.ne, hunsat⟩

/-- Every valid chain-length witness consists of pairwise distinct constraint scopes. -/
theorem IsChainLengthWitness.injective {R : Set (Fin r → D)}
    {S : Fin m → (Fin r → Fin n)} (h : IsChainLengthWitness R S) :
    Function.Injective S := by
  intro i j hij
  by_contra hne
  rcases lt_trichotomy i j with hlt | rfl | hgt
  · obtain ⟨φ, hprev, hunsat⟩ := h j
    exact hunsat (hij ▸ hprev i hlt)
  · exact hne rfl
  · obtain ⟨φ, hprev, hunsat⟩ := h i
    exact hunsat (hij.symm ▸ hprev j hgt)

/-- Any chain-length witness of arity `r` on `n` variables has size at most `n ^ r`. -/
theorem IsChainLengthWitness.card_le_pow {R : Set (Fin r → D)}
    {S : Fin m → (Fin r → Fin n)} (h : IsChainLengthWitness R S) :
    m ≤ n ^ r := by
  have hle : Fintype.card (Fin m) ≤ Fintype.card (Fin r → Fin n) :=
    Fintype.card_le_of_injective S h.injective
  simpa using hle

/-- Any non-redundant family of arity `r` on `n` variables has size at most `n ^ r`. -/
theorem IsNonRedundant.card_le_pow {R : Set (Fin r → D)}
    {S : Fin m → (Fin r → Fin n)} (h : IsNonRedundant R S) :
    m ≤ n ^ r :=
  h.isChainLengthWitness.card_le_pow

open scoped Classical in
/-- Maximum size of a non-redundant instance of `CSP(R)` on `n` variables. -/
noncomputable def nonRedundancy (R : Set (Fin r → D)) (n : ℕ) : ℕ :=
  Nat.findGreatest (fun m ↦ ∃ S : Fin m → (Fin r → Fin n), IsNonRedundant R S) (n ^ r)

open scoped Classical in
/-- Maximum size of a chain-length witness of `CSP(R)` on `n` variables. -/
noncomputable def chainLength (R : Set (Fin r → D)) (n : ℕ) : ℕ :=
  Nat.findGreatest (fun m ↦ ∃ S : Fin m → (Fin r → Fin n), IsChainLengthWitness R S) (n ^ r)

/-- Any non-redundant family of `m` constraints certifies `m ≤ nonRedundancy R n`. -/
theorem IsNonRedundant.le_nonRedundancy {R : Set (Fin r → D)}
    {S : Fin m → (Fin r → Fin n)} (h : IsNonRedundant R S) :
    m ≤ nonRedundancy R n := by
  classical
  exact Nat.le_findGreatest h.card_le_pow ⟨S, h⟩

/-- Any chain-length witness of `m` constraints certifies `m ≤ chainLength R n`. -/
theorem IsChainLengthWitness.le_chainLength {R : Set (Fin r → D)}
    {S : Fin m → (Fin r → Fin n)} (h : IsChainLengthWitness R S) :
    m ≤ chainLength R n := by
  classical
  exact Nat.le_findGreatest h.card_le_pow ⟨S, h⟩

/-- Attainment of `nonRedundancy R n` by a concrete non-redundant constraint family. -/
theorem exists_isNonRedundant_eq_nonRedundancy (R : Set (Fin r → D)) (n : ℕ) :
    ∃ S : Fin (nonRedundancy R n) → (Fin r → Fin n), IsNonRedundant R S := by
  classical
  exact Nat.findGreatest_spec
    (P := fun m ↦ ∃ S : Fin m → (Fin r → Fin n), IsNonRedundant R S)
    (Nat.zero_le _) ⟨Fin.elim0, fun i ↦ Fin.elim0 i⟩

/-- Attainment of `chainLength R n` by a concrete chain-length witness. -/
theorem exists_isChainLengthWitness_eq_chainLength (R : Set (Fin r → D)) (n : ℕ) :
    ∃ S : Fin (chainLength R n) → (Fin r → Fin n), IsChainLengthWitness R S := by
  classical
  exact Nat.findGreatest_spec
    (P := fun m ↦ ∃ S : Fin m → (Fin r → Fin n), IsChainLengthWitness R S)
    (Nat.zero_le _) ⟨Fin.elim0, fun i ↦ Fin.elim0 i⟩

/-- Upper-bound principle for `nonRedundancy R n`. -/
theorem nonRedundancy_le_of_forall {R : Set (Fin r → D)} {n B : ℕ}
    (hB : ∀ (m : ℕ) (S : Fin m → (Fin r → Fin n)), IsNonRedundant R S → m ≤ B) :
    nonRedundancy R n ≤ B := by
  obtain ⟨S, hS⟩ := exists_isNonRedundant_eq_nonRedundancy R n
  exact hB (nonRedundancy R n) S hS

/-- Upper-bound principle for `chainLength R n`. -/
theorem chainLength_le_of_forall {R : Set (Fin r → D)} {n B : ℕ}
    (hB : ∀ (m : ℕ) (S : Fin m → (Fin r → Fin n)), IsChainLengthWitness R S → m ≤ B) :
    chainLength R n ≤ B := by
  obtain ⟨S, hS⟩ := exists_isChainLengthWitness_eq_chainLength R n
  exact hB (chainLength R n) S hS

/-- Non-redundancy never exceeds chain length. -/
theorem nonRedundancy_le_chainLength (R : Set (Fin r → D)) (n : ℕ) :
    nonRedundancy R n ≤ chainLength R n := by
  obtain ⟨S, hS⟩ := exists_isNonRedundant_eq_nonRedundancy R n
  exact hS.isChainLengthWitness.le_chainLength

/-- Conditional non-redundancy property for a pair of relations `(P, Q)` on `D^r`. -/
def IsCondNonRedundant (P Q : Set (Fin r → D)) (S : Fin m → (Fin r → Fin n)) : Prop :=
  ∀ i : Fin m, ∃ φ : Fin n → D, (∀ j : Fin m, j ≠ i → evalScope φ (S j) ∈ P) ∧
    evalScope φ (S i) ∈ Q \ P

/-- Conditional chain-length witness property for a pair of relations `(P, Q)` on `D^r`. -/
def IsCondChainLengthWitness (P Q : Set (Fin r → D)) (S : Fin m → (Fin r → Fin n)) : Prop :=
  ∀ i : Fin m, ∃ φ : Fin n → D, (∀ j : Fin m, j < i → evalScope φ (S j) ∈ P) ∧
    evalScope φ (S i) ∈ Q \ P

/-- Every conditionally non-redundant family is a conditional chain-length witness. -/
theorem IsCondNonRedundant.isCondChainLengthWitness {P Q : Set (Fin r → D)}
    {S : Fin m → (Fin r → Fin n)} (h : IsCondNonRedundant P Q S) :
    IsCondChainLengthWitness P Q S := by
  intro i
  obtain ⟨φ, hsat, hunsat⟩ := h i
  exact ⟨φ, fun j hj ↦ hsat j hj.ne, hunsat⟩

/-- Every conditional chain-length witness for `(P, Q)` is an unconditional witness for `P`. -/
theorem IsCondChainLengthWitness.isChainLengthWitness_strong {P Q : Set (Fin r → D)}
    {S : Fin m → (Fin r → Fin n)} (h : IsCondChainLengthWitness P Q S) :
    IsChainLengthWitness P S := by
  intro i
  obtain ⟨φ, hprev, hdiff⟩ := h i
  exact ⟨φ, hprev, hdiff.2⟩

/-- Any conditional chain-length witness has size at most `n ^ r`. -/
theorem IsCondChainLengthWitness.card_le_pow {P Q : Set (Fin r → D)}
    {S : Fin m → (Fin r → Fin n)} (h : IsCondChainLengthWitness P Q S) :
    m ≤ n ^ r :=
  h.isChainLengthWitness_strong.card_le_pow

/-- Any conditionally non-redundant family has size at most `n ^ r`. -/
theorem IsCondNonRedundant.card_le_pow {P Q : Set (Fin r → D)}
    {S : Fin m → (Fin r → Fin n)} (h : IsCondNonRedundant P Q S) :
    m ≤ n ^ r :=
  h.isCondChainLengthWitness.card_le_pow

open scoped Classical in
/-- Maximum size of a conditionally non-redundant family for `(P, Q)` on `n` variables. -/
noncomputable def condNonRedundancy (P Q : Set (Fin r → D)) (n : ℕ) : ℕ :=
  Nat.findGreatest (fun m ↦ ∃ S : Fin m → (Fin r → Fin n), IsCondNonRedundant P Q S) (n ^ r)

open scoped Classical in
/-- Maximum size of a conditional chain-length witness for `(P, Q)` on `n` variables. -/
noncomputable def condChainLength (P Q : Set (Fin r → D)) (n : ℕ) : ℕ :=
  Nat.findGreatest
    (fun m ↦ ∃ S : Fin m → (Fin r → Fin n), IsCondChainLengthWitness P Q S) (n ^ r)

/-- Any conditionally non-redundant family certifies `m ≤ condNonRedundancy P Q n`. -/
theorem IsCondNonRedundant.le_condNonRedundancy {P Q : Set (Fin r → D)}
    {S : Fin m → (Fin r → Fin n)} (h : IsCondNonRedundant P Q S) :
    m ≤ condNonRedundancy P Q n := by
  classical
  exact Nat.le_findGreatest h.card_le_pow ⟨S, h⟩

/-- Any conditional chain-length witness certifies `m ≤ condChainLength P Q n`. -/
theorem IsCondChainLengthWitness.le_condChainLength {P Q : Set (Fin r → D)}
    {S : Fin m → (Fin r → Fin n)} (h : IsCondChainLengthWitness P Q S) :
    m ≤ condChainLength P Q n := by
  classical
  exact Nat.le_findGreatest h.card_le_pow ⟨S, h⟩

/-- Attainment of `condNonRedundancy P Q n`. -/
theorem exists_isCondNonRedundant_eq_condNonRedundancy (P Q : Set (Fin r → D)) (n : ℕ) :
    ∃ S : Fin (condNonRedundancy P Q n) → (Fin r → Fin n), IsCondNonRedundant P Q S := by
  classical
  exact Nat.findGreatest_spec
    (P := fun m ↦ ∃ S : Fin m → (Fin r → Fin n), IsCondNonRedundant P Q S)
    (Nat.zero_le _) ⟨Fin.elim0, fun i ↦ Fin.elim0 i⟩

/-- Attainment of `condChainLength P Q n`. -/
theorem exists_isCondChainLengthWitness_eq_condChainLength (P Q : Set (Fin r → D)) (n : ℕ) :
    ∃ S : Fin (condChainLength P Q n) → (Fin r → Fin n), IsCondChainLengthWitness P Q S := by
  classical
  exact Nat.findGreatest_spec
    (P := fun m ↦ ∃ S : Fin m → (Fin r → Fin n), IsCondChainLengthWitness P Q S)
    (Nat.zero_le _) ⟨Fin.elim0, fun i ↦ Fin.elim0 i⟩

/-- Conditional non-redundancy never exceeds conditional chain length. -/
theorem condNonRedundancy_le_condChainLength (P Q : Set (Fin r → D)) (n : ℕ) :
    condNonRedundancy P Q n ≤ condChainLength P Q n := by
  obtain ⟨S, hS⟩ := exists_isCondNonRedundant_eq_condNonRedundancy P Q n
  exact hS.isCondChainLengthWitness.le_condChainLength

end Basic

/-! ### Conditional-to-Unconditional Lifting -/

section Lifting

/-- Truncate an `(r + 1)`-tuple to its first `r` coordinates. -/
@[expose] def initTuple {r : ℕ} {X : Type*} (t : Fin (r + 1) → X) : Fin r → X :=
  fun k ↦ t k.castSucc

@[simp]
theorem initTuple_apply {r : ℕ} {X : Type*} (t : Fin (r + 1) → X) (k : Fin r) :
    initTuple t k = t k.castSucc :=
  rfl

/-- Cartesian extension `Q × A ⊆ D^(r + 1)` of an arity-`r` relation `Q` with a unary set `A`. -/
def prodSetRel {r : ℕ} {D : Type*} (Q : Set (Fin r → D)) (A : Set D) : Set (Fin (r + 1) → D) :=
  { t | initTuple t ∈ Q ∧ t (Fin.last r) ∈ A }

theorem mem_prodSetRel_iff {r : ℕ} {D : Type*} {Q : Set (Fin r → D)} {A : Set D}
    {t : Fin (r + 1) → D} :
    t ∈ prodSetRel Q A ↔ initTuple t ∈ Q ∧ t (Fin.last r) ∈ A :=
  Iff.rfl

/-- Conditional-to-unconditional lifting relation `(P × {a}) ∪ (Q × {b}) ⊆ D^(r + 1)`. -/
def liftRel {r : ℕ} {D : Type*} (P Q : Set (Fin r → D)) (a b : D) : Set (Fin (r + 1) → D) :=
  prodSetRel P {a} ∪ prodSetRel Q {b}

theorem mem_liftRel_iff {r : ℕ} {D : Type*} {P Q : Set (Fin r → D)} {a b : D}
    {t : Fin (r + 1) → D} :
    t ∈ liftRel P Q a b ↔
      (initTuple t ∈ P ∧ t (Fin.last r) = a) ∨ (initTuple t ∈ Q ∧ t (Fin.last r) = b) :=
  Iff.rfl

/-- **Conditional-to-unconditional non-redundancy upper bound**:
for any `P ⊆ Q ⊆ D^r` and `a ≠ b ∈ D`,
`nonRedundancy (liftRel P Q a b) n ≤ n * condNonRedundancy P Q n +
nonRedundancy (prodSetRel Q {a, b}) n`. -/
theorem nonRedundancy_liftRel_le {r : ℕ} {D : Type*}
    {P Q : Set (Fin r → D)} (hPQ : P ⊆ Q) {a b : D} (hab : a ≠ b) (n : ℕ) :
    nonRedundancy (liftRel P Q a b) n ≤
      n * condNonRedundancy P Q n + nonRedundancy (prodSetRel Q {a, b}) n := by
  classical
  refine nonRedundancy_le_of_forall fun m S hS ↦ ?_
  let φ : Fin m → (Fin n → D) := fun i ↦ Classical.choose (hS i)
  have hφ_sat : ∀ i j : Fin m, j ≠ i → evalScope (φ i) (S j) ∈ liftRel P Q a b :=
    fun i ↦ (Classical.choose_spec (hS i)).1
  have hφ_unsat : ∀ i : Fin m, evalScope (φ i) (S i) ∉ liftRel P Q a b :=
    fun i ↦ (Classical.choose_spec (hS i)).2
  have hlift_sub : liftRel P Q a b ⊆ prodSetRel Q {a, b} := by
    intro t ht
    rcases mem_liftRel_iff.mp ht with ⟨hP, ha⟩ | ⟨hQ, hb⟩
    · exact ⟨hPQ hP, by simp [ha]⟩
    · exact ⟨hQ, by simp [hb]⟩
  let I_in := univ.filter fun i : Fin m ↦ evalScope (φ i) (S i) ∈ prodSetRel Q {a, b}
  let I_out := (univ : Finset (Fin m)) \ I_in
  have hpart : #I_in + #I_out = m := by
    have hs := card_sdiff_add_card_inter (univ : Finset (Fin m)) I_in
    rw [inter_eq_right.mpr (subset_univ _), card_univ, Fintype.card_fin] at hs
    dsimp only [I_out]
    omega
  have hout_le : #I_out ≤ nonRedundancy (prodSetRel Q {a, b}) n := by
    let eOut : Fin #I_out ≃ I_out :=
      (Fintype.equivFinOfCardEq (Fintype.card_coe I_out)).symm
    let S_out : Fin #I_out → (Fin (r + 1) → Fin n) := fun u ↦ S (eOut u).1
    have hS_out : IsNonRedundant (prodSetRel Q {a, b}) S_out := by
      intro u
      have hnot_in : evalScope (φ (eOut u).1) (S (eOut u).1) ∉ prodSetRel Q {a, b} :=
        fun h ↦ (mem_sdiff.mp (eOut u).2).2 (mem_filter.mpr ⟨mem_univ _, h⟩)
      refine ⟨φ (eOut u).1, fun v hvu ↦ ?_, hnot_in⟩
      have hne : (eOut v).1 ≠ (eOut u).1 := fun h ↦ hvu (eOut.injective (Subtype.ext h))
      exact hlift_sub (hφ_sat (eOut u).1 (eOut v).1 hne)
    exact hS_out.le_nonRedundancy
  have hin_spec : ∀ i ∈ I_in,
      evalScope (φ i) (initTuple (S i)) ∈ Q \ P ∧ (φ i) (S i (Fin.last r)) = a := by
    intro i hi
    have hprod := mem_prodSetRel_iff.mp (mem_filter.mp hi).2
    have hnot := hφ_unsat i
    rw [mem_liftRel_iff] at hnot
    have hlast : evalScope (φ i) (S i) (Fin.last r) = a := by
      rcases hprod.2 with ha | hb
      · exact ha
      · exfalso; exact hnot (Or.inr ⟨hprod.1, hb⟩)
    exact ⟨⟨hprod.1, fun hP ↦ hnot (Or.inl ⟨hP, hlast⟩)⟩, hlast⟩
  let fiber : Fin n → Finset (Fin m) := fun u ↦ I_in.filter fun i ↦ S i (Fin.last r) = u
  have hfiber_le : ∀ u : Fin n, #(fiber u) ≤ condNonRedundancy P Q n := by
    intro u
    let eFib : Fin #(fiber u) ≃ fiber u :=
      (Fintype.equivFinOfCardEq (Fintype.card_coe (fiber u))).symm
    let S_fib : Fin #(fiber u) → (Fin r → Fin n) := fun x ↦ initTuple (S (eFib x).1)
    have hS_fib : IsCondNonRedundant P Q S_fib := by
      intro x
      have hx_mem := mem_filter.mp (eFib x).2
      have hspec := hin_spec (eFib x).1 hx_mem.1
      refine ⟨φ (eFib x).1, fun y hyx ↦ ?_, hspec.1⟩
      have hne : (eFib y).1 ≠ (eFib x).1 := fun h ↦ hyx (eFib.injective (Subtype.ext h))
      have hy_mem := mem_filter.mp (eFib y).2
      have hlast_y : evalScope (φ (eFib x).1) (S (eFib y).1) (Fin.last r) = a := by
        simp only [evalScope_apply, hy_mem.2, ← hx_mem.2]
        exact hspec.2
      rcases mem_liftRel_iff.mp (hφ_sat (eFib x).1 (eFib y).1 hne) with ⟨hP, _⟩ | ⟨_, hb⟩
      · exact hP
      · exact absurd (hlast_y.symm.trans hb) hab
    exact hS_fib.le_condNonRedundancy
  have hin_eq_sum : #I_in = ∑ u : Fin n, #(fiber u) := by
    have hbi : (univ : Finset (Fin n)).biUnion fiber = I_in := by
      ext i
      simp only [fiber, mem_biUnion, mem_univ, true_and, mem_filter]
      exact ⟨fun ⟨_, hi, _⟩ ↦ hi, fun hi ↦ ⟨S i (Fin.last r), hi, rfl⟩⟩
    have hdisj : ((univ : Finset (Fin n)) : Set (Fin n)).PairwiseDisjoint fiber := by
      intro u₁ _ u₂ _ hne
      rw [Function.onFun, Finset.disjoint_left]
      intro i hi₁ hi₂
      exact hne ((mem_filter.mp hi₁).2.symm.trans (mem_filter.mp hi₂).2)
    rw [← hbi, card_biUnion hdisj]
  have hin_le : #I_in ≤ n * condNonRedundancy P Q n := by
    rw [hin_eq_sum]
    calc ∑ u : Fin n, #(fiber u)
        ≤ ∑ _u : Fin n, condNonRedundancy P Q n := Finset.sum_le_sum fun u _ ↦ hfiber_le u
      _ = n * condNonRedundancy P Q n := by
          rw [Finset.sum_const, card_univ, Fintype.card_fin, Nat.nsmul_eq_mul]
  omega

/-- **Conditional-to-unconditional chain-length lower bound**:
for any `P ⊆ Q ⊆ D^r` and `a ≠ b ∈ D`,
`n₂ * condChainLength P Q n₁ ≤ chainLength (liftRel P Q a b) (n₁ + n₂)`. -/
theorem chainLength_liftRel_ge {r : ℕ} {D : Type*}
    {P Q : Set (Fin r → D)} (hPQ : P ⊆ Q) {a b : D} (hab : a ≠ b) (n₁ n₂ : ℕ) :
    n₂ * condChainLength P Q n₁ ≤ chainLength (liftRel P Q a b) (n₁ + n₂) := by
  by_cases hn₂0 : n₂ = 0
  · simp [hn₂0]
  have hn₂ : 0 < n₂ := Nat.pos_of_ne_zero hn₂0
  let m := condChainLength P Q n₁
  obtain ⟨S, hS⟩ : ∃ S : Fin m → (Fin r → Fin n₁), IsCondChainLengthWitness P Q S :=
    exists_isCondChainLengthWitness_eq_condChainLength P Q n₁
  change n₂ * m ≤ _
  rw [Nat.mul_comm n₂ m]
  let jOf : Fin (m * n₂) → Fin m := fun idx ↦
    ⟨idx.1 / n₂, by
      by_contra h
      push Not at h
      have hmul : m * n₂ ≤ (idx.1 / n₂) * n₂ := Nat.mul_le_mul_right n₂ h
      rw [Nat.mul_comm (idx.1 / n₂) n₂] at hmul
      have hdiv := Nat.div_add_mod idx.1 n₂
      have hi := idx.2
      omega⟩
  let kOf : Fin (m * n₂) → Fin n₂ := fun idx ↦ ⟨idx.1 % n₂, Nat.mod_lt idx.1 hn₂⟩
  have hlex : ∀ {idx' idx : Fin (m * n₂)}, idx' < idx →
      jOf idx' < jOf idx ∨ (jOf idx' = jOf idx ∧ (kOf idx').1 < (kOf idx).1) := by
    intro idx' idx hlt_idx
    have hlt_val : idx'.1 < idx.1 := hlt_idx
    rcases lt_trichotomy (jOf idx') (jOf idx) with hlt | heq | hgt
    · exact Or.inl hlt
    · right
      refine ⟨heq, ?_⟩
      have hval_eq : idx'.1 / n₂ = idx.1 / n₂ := congrArg Fin.val heq
      have h1 := Nat.div_add_mod idx'.1 n₂
      have h2 := Nat.div_add_mod idx.1 n₂
      dsimp only [kOf]
      rw [hval_eq] at h1
      omega
    · exfalso
      have hsucc : (jOf idx).1 + 1 ≤ (jOf idx').1 := hgt
      have hmul : n₂ * ((jOf idx).1 + 1) ≤ n₂ * (jOf idx').1 := Nat.mul_le_mul_left n₂ hsucc
      have h1 := Nat.div_add_mod idx'.1 n₂
      have h2 := Nat.div_add_mod idx.1 n₂
      have h3 := Nat.mod_lt idx.1 hn₂
      dsimp only [jOf] at hmul
      have hexp : n₂ * (idx.1 / n₂ + 1) = n₂ * (idx.1 / n₂) + n₂ := by ring
      omega
  let S' : Fin (m * n₂) → (Fin (r + 1) → Fin (n₁ + n₂)) := fun idx c ↦
    if hc : c.1 < r then
      ⟨(S (jOf idx) ⟨c.1, hc⟩).1, by have := (S (jOf idx) ⟨c.1, hc⟩).2; omega⟩
    else
      ⟨n₁ + (kOf idx).1, by have := (kOf idx).2; omega⟩
  have hwit' : IsChainLengthWitness (liftRel P Q a b) S' := by
    intro idx
    obtain ⟨fj, hfj_prev, hfj_curr⟩ := hS (jOf idx)
    let g : Fin (n₁ + n₂) → D := fun v ↦
      if hv : v.1 < n₁ then fj ⟨v.1, hv⟩
      else if v.1 - n₁ < (kOf idx).1 then b else a
    have hinit_eval : ∀ idx' : Fin (m * n₂),
        initTuple (evalScope g (S' idx')) = evalScope fj (S (jOf idx')) := by
      intro idx'
      ext c
      have hc : (c.castSucc).1 < r := c.2
      have hc_eq : (⟨(c.castSucc).1, hc⟩ : Fin r) = c := rfl
      have hsv : (S (jOf idx') c).1 < n₁ := (S (jOf idx') c).2
      simp only [initTuple_apply, evalScope_apply, S', hc, ↓reduceDIte, hc_eq, g, hsv, Fin.eta]
    have hlast_eval : ∀ idx' : Fin (m * n₂),
        evalScope g (S' idx') (Fin.last r) =
          if (kOf idx').1 < (kOf idx).1 then b else a := by
      intro idx'
      have hnr : ¬ (Fin.last r).1 < r := by simp
      have hge : ¬ (n₁ + (kOf idx').1 < n₁) := by omega
      have hsub : n₁ + (kOf idx').1 - n₁ = (kOf idx').1 := by omega
      simp only [evalScope_apply, S', hnr, ↓reduceDIte, g, hge, hsub]
    refine ⟨g, fun idx' hlt ↦ ?_, ?_⟩
    · rw [mem_liftRel_iff, hinit_eval, hlast_eval]
      rcases hlex hlt with hlt_j | ⟨heq_j, hlt_k⟩
      · by_cases hk_lt : (kOf idx').1 < (kOf idx).1
        · exact Or.inr ⟨hPQ (hfj_prev (jOf idx') hlt_j), by simp [hk_lt]⟩
        · exact Or.inl ⟨hfj_prev (jOf idx') hlt_j, by simp [hk_lt]⟩
      · rw [heq_j]
        exact Or.inr ⟨hfj_curr.1, by simp [hlt_k]⟩
    · rw [mem_liftRel_iff, hinit_eval, hlast_eval]
      simp only [lt_self_iff_false, ↓reduceIte]
      rintro (⟨hP, _⟩ | ⟨_, hba⟩)
      · exact hfj_curr.2 hP
      · exact hab hba
  exact hwit'.le_chainLength

end Lifting

/-! ### Linear-Span Zero-Locus Dimension Bound -/

section LinearZeroLocus

private lemma card_le_of_triangular_sum {K : Type*} [Field K] {ι : Type*} :
    ∀ (d : ℕ) (s : Finset ι), #s = d →
      ∀ (m : ℕ) (c f : Fin m → ι → K),
        (∀ i j : Fin m, j < i → ∑ b ∈ s, c j b * f i b = 0) →
        (∀ i : Fin m, ∑ b ∈ s, c i b * f i b ≠ 0) →
        m ≤ d := by
  classical
  intro d
  induction d with
  | zero =>
      intro s hs m c f _ hdiag
      rw [card_eq_zero] at hs
      subst hs
      rcases m with _ | m'
      · exact Nat.zero_le 0
      · exfalso
        exact hdiag 0 (by simp)
  | succ d ih =>
      intro s hs m c f htri hdiag
      rcases m with _ | m'
      · exact Nat.zero_le _
      · have hex : ∃ b₀ ∈ s, c 0 b₀ * f 0 b₀ ≠ 0 := by
          by_contra hall
          push Not at hall
          exact hdiag 0 (Finset.sum_eq_zero hall)
        obtain ⟨b₀, hb₀, hb₀_nz⟩ := hex
        have hc0_nz : c 0 b₀ ≠ 0 := left_ne_zero_of_mul hb₀_nz
        let s' := s.erase b₀
        have hs'_card : #s' = d := by
          have hins := card_insert_of_notMem (a := b₀) (s := s')
            (fun h ↦ (mem_erase.mp h).1 rfl)
          rw [insert_erase hb₀, hs] at hins
          omega
        have hsplit : ∀ g : ι → K, ∑ b ∈ s, g b = g b₀ + ∑ b ∈ s', g b := fun g ↦ by
          rw [← insert_erase hb₀, sum_insert (fun h ↦ (mem_erase.mp h).1 rfl)]
        let c' : Fin m' → ι → K := fun j b ↦
          c j.succ b - (c j.succ b₀ / c 0 b₀) * c 0 b
        let f' : Fin m' → ι → K := fun i b ↦ f i.succ b
        have hsum_eq : ∀ i j : Fin m',
            ∑ b ∈ s', c' j b * f' i b = ∑ b ∈ s, c j.succ b * f i.succ b := by
          intro i j
          have h0_i : ∑ b ∈ s, c 0 b * f i.succ b = 0 := htri i.succ 0 (Fin.succ_pos i)
          have hlin :
              ∑ b ∈ s, c' j b * f' i b =
                (∑ b ∈ s, c j.succ b * f i.succ b) -
                  (c j.succ b₀ / c 0 b₀) * (∑ b ∈ s, c 0 b * f i.succ b) := by
            simp only [c', f', sub_mul, mul_assoc, Finset.sum_sub_distrib, ← Finset.mul_sum]
          rw [h0_i, mul_zero, sub_zero] at hlin
          rw [hsplit] at hlin
          have hb₀_zero : c' j b₀ * f' i b₀ = 0 := by
            dsimp only [c', f']
            rw [div_mul_cancel₀ _ hc0_nz, sub_self, zero_mul]
          rw [hb₀_zero, zero_add] at hlin
          exact hlin
        have hle := ih s' hs'_card m' c' f'
          (fun i j hji ↦ (hsum_eq i j).trans
            (htri i.succ j.succ (Fin.succ_lt_succ_iff.mpr hji)))
          (fun i ↦ by rw [hsum_eq i i]; exact hdiag i.succ)
        omega

/-- **Linear-span zero-locus upper bound on chain length**:
if `R₀ ⊆ D^r` is cut out over a field `K` as the zero locus
`evalScope φ s ∈ R₀ ↔ ∑ b : ι, coeff s b * feat φ b = 0` for a finite feature index type `ι`, then
`chainLength R₀ n ≤ Fintype.card ι`. -/
theorem chainLength_le_of_linear_zero_locus {K : Type*} [Field K] {ι : Type*} [Fintype ι]
    {r n : ℕ} {D : Type*} {R₀ : Set (Fin r → D)}
    (coeff : (Fin r → Fin n) → ι → K)
    (feat : (Fin n → D) → ι → K)
    (hlocus : ∀ (φ : Fin n → D) (s : Fin r → Fin n),
      evalScope φ s ∈ R₀ ↔ ∑ b : ι, coeff s b * feat φ b = 0) :
    chainLength R₀ n ≤ Fintype.card ι := by
  classical
  refine chainLength_le_of_forall fun m S hS ↦ ?_
  let φ : Fin m → (Fin n → D) := fun i ↦ Classical.choose (hS i)
  have htri : ∀ i j : Fin m, j < i → ∑ b ∈ (univ : Finset ι), coeff (S j) b * feat (φ i) b = 0 :=
    fun i j hji ↦ (hlocus (φ i) (S j)).mp ((Classical.choose_spec (hS i)).1 j hji)
  have hdiag : ∀ i : Fin m, ∑ b ∈ (univ : Finset ι), coeff (S i) b * feat (φ i) b ≠ 0 :=
    fun i h0 ↦ (Classical.choose_spec (hS i)).2 ((hlocus (φ i) (S i)).mpr h0)
  exact card_le_of_triangular_sum (Fintype.card ι) univ card_univ m
    (fun j ↦ coeff (S j)) (fun i ↦ feat (φ i)) htri hdiag

/-- **Linear-span zero-locus upper bound on non-redundancy**:
if `R₀ ⊆ D^r` is cut out over a field `K` as the zero locus
`evalScope φ s ∈ R₀ ↔ ∑ b : ι, coeff s b * feat φ b = 0` for a finite feature index type `ι`, then
`nonRedundancy R₀ n ≤ Fintype.card ι`. -/
theorem nonRedundancy_le_of_linear_zero_locus {K : Type*} [Field K] {ι : Type*} [Fintype ι]
    {r n : ℕ} {D : Type*} {R₀ : Set (Fin r → D)}
    (coeff : (Fin r → Fin n) → ι → K)
    (feat : (Fin n → D) → ι → K)
    (hlocus : ∀ (φ : Fin n → D) (s : Fin r → Fin n),
      evalScope φ s ∈ R₀ ↔ ∑ b : ι, coeff s b * feat φ b = 0) :
    nonRedundancy R₀ n ≤ Fintype.card ι :=
  (nonRedundancy_le_chainLength R₀ n).trans
    (chainLength_le_of_linear_zero_locus coeff feat hlocus)

end LinearZeroLocus

end CslibFrontier.Complexity.CSP
