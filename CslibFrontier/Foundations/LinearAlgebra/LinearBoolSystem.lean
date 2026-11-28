module

public import CslibFrontier.Init
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Card

/-!
# Monotone Fixed-Point Solver for Linear Boolean Equations

A finite system of linear equations over the Boolean semiring `(Bool, ||, &&)` consists of
homogeneous disjunction equalities `⋁_{i ∈ I} X_i = ⋁_{j ∈ J} X_j` (which include zero-constraints
`⋁_{i ∈ I} X_i = false` by taking `J = ∅`) and inhomogeneous unit constraints
`⋁_{i ∈ I} X_i = true`.

Because every homogeneous equation is preserved under componentwise disjunction, the set of
solutions to the homogeneous equations has a unique componentwise greatest element. Starting from
the all-`true` assignment and repeatedly clearing any variable whose presence on one side of a
homogeneous equation is unsupported by the opposite side yields a monotone decreasing sequence that
stabilizes in at most `|ι|` iterations. The full system is satisfiable if and only if this greatest
homogeneous solution satisfies all inhomogeneous constraints.

## Main definitions

* `CslibFrontier.Foundations.LinearAlgebra.LinearBoolSystem`: finite systems of homogeneous and
  inhomogeneous linear equations over `Bool`.
* `CslibFrontier.Foundations.LinearAlgebra.LinearBoolSystem.SatisfiesHom`,
  `CslibFrontier.Foundations.LinearAlgebra.LinearBoolSystem.Satisfies`: satisfaction predicates.
* `CslibFrontier.Foundations.LinearAlgebra.linearBoolStep`: one monotone elimination step.
* `CslibFrontier.Foundations.LinearAlgebra.linearBoolIter`: iterated elimination from all-`true`.

## Main results

* `CslibFrontier.Foundations.LinearAlgebra.linear_bool_system_greatest_solution`: iterating
  `linearBoolStep` for `Fintype.card ι` steps computes the unique greatest homogeneous solution and
  decides satisfiability of the full linear boolean system.
-/

public section

namespace CslibFrontier.Foundations.LinearAlgebra

/-- A finite system of linear equations over the Boolean semiring on variables `ι`: homogeneous
equations `(I, J)` encoding `⋁_{i ∈ I} X_i = ⋁_{j ∈ J} X_j` (including `⋁_{i ∈ I} X_i = false`
when `J = ∅`) and inhomogeneous equations `I` encoding `⋁_{i ∈ I} X_i = true`. -/
structure LinearBoolSystem (ι : Type*) where
  /-- Homogeneous equations `(I, J)` encoding `⋁_{i ∈ I} X_i = ⋁_{j ∈ J} X_j`. -/
  homEqs : List (Finset ι × Finset ι)
  /-- Inhomogeneous equations `I` encoding `⋁_{i ∈ I} X_i = true`. -/
  oneEqs : List (Finset ι)

/-- Satisfaction of all homogeneous equations of a linear boolean system. -/
def LinearBoolSystem.SatisfiesHom {ι : Type*} (S : LinearBoolSystem ι) (X : ι → Bool) : Prop :=
  ∀ eq ∈ S.homEqs, (∃ i ∈ eq.1, X i = true) ↔ (∃ j ∈ eq.2, X j = true)

/-- Satisfaction of all homogeneous and inhomogeneous equations of a linear boolean system. -/
def LinearBoolSystem.Satisfies {ι : Type*} (S : LinearBoolSystem ι) (X : ι → Bool) : Prop :=
  S.SatisfiesHom X ∧ ∀ I ∈ S.oneEqs, ∃ i ∈ I, X i = true

/-- One monotone elimination step: retain `X i = true` iff no homogeneous equation forces
`X i = false` because its opposite side currently evaluates to `false`. -/
def linearBoolStep {ι : Type*} [DecidableEq ι] (S : LinearBoolSystem ι) (X : ι → Bool) :
    ι → Bool :=
  fun i =>
    X i &&
    S.homEqs.all fun eq =>
      (!(i ∈ eq.1) || decide (∃ j ∈ eq.2, X j = true)) &&
      (!(i ∈ eq.2) || decide (∃ j ∈ eq.1, X j = true))

/-- Iterating `linearBoolStep` `n` times starting from the all-`true` assignment. -/
def linearBoolIter {ι : Type*} [DecidableEq ι] (S : LinearBoolSystem ι) : ℕ → (ι → Bool)
  | 0 => fun _ => true
  | n + 1 => linearBoolStep S (linearBoolIter S n)

private theorem linearBoolStep_le {ι : Type*} [DecidableEq ι]
    (S : LinearBoolSystem ι) (X : ι → Bool) (i : ι) :
    linearBoolStep S X i = true → X i = true := by
  simp only [linearBoolStep, Bool.and_eq_true]
  exact And.left

private theorem linearBoolStep_ge_of_satisfiesHom {ι : Type*} [DecidableEq ι]
    {S : LinearBoolSystem ι} {X Y : ι → Bool}
    (hY : S.SatisfiesHom Y) (hle : ∀ i, Y i = true → X i = true) (i : ι) :
    Y i = true → linearBoolStep S X i = true := by
  intro hYi
  simp only [linearBoolStep, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true,
    Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq]
  refine ⟨hle i hYi, fun eq heq => ⟨?_, ?_⟩⟩
  · by_cases hi : i ∈ eq.1
    · right
      obtain ⟨j, hj, hYj⟩ := (hY eq heq).1 ⟨i, hi, hYi⟩
      exact ⟨j, hj, hle j hYj⟩
    · exact Or.inl hi
  · by_cases hi : i ∈ eq.2
    · right
      obtain ⟨j, hj, hYj⟩ := (hY eq heq).2 ⟨i, hi, hYi⟩
      exact ⟨j, hj, hle j hYj⟩
    · exact Or.inl hi

private theorem linearBoolIter_stabilizes {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : LinearBoolSystem ι) :
    linearBoolStep S (linearBoolIter S (Fintype.card ι)) = linearBoolIter S (Fintype.card ι) := by
  have hdec : ∀ n : ℕ, linearBoolStep S (linearBoolIter S n) ≠ linearBoolIter S n →
      (Finset.univ.filter fun i => linearBoolIter S (n + 1) i = true).card <
        (Finset.univ.filter fun i => linearBoolIter S n i = true).card := by
    intro n hne
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_subset_ne]
    refine ⟨fun i hi => Finset.mem_filter.2 ⟨Finset.mem_univ _,
      linearBoolStep_le S _ i (Finset.mem_filter.1 hi).2⟩, fun hEq => hne ?_⟩
    funext i
    apply Bool.eq_iff_iff.2
    have hmem := Finset.ext_iff.1 hEq i
    change (i ∈ Finset.univ.filter fun j => linearBoolStep S (linearBoolIter S n) j = true) ↔
      (i ∈ Finset.univ.filter fun j => linearBoolIter S n j = true) at hmem
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hmem
  by_contra hne
  have hstrict : ∀ m ≤ Fintype.card ι + 1,
      (Finset.univ.filter fun i => linearBoolIter S m i = true).card + m ≤ Fintype.card ι := by
    intro m
    induction m with
    | zero =>
      intro _
      simp only [linearBoolIter, Nat.add_zero]
      exact Finset.card_le_univ _
    | succ m ih =>
      intro hm
      have hnem : linearBoolStep S (linearBoolIter S m) ≠ linearBoolIter S m := by
        intro heq
        have hconst : ∀ d : ℕ, linearBoolIter S (m + d) = linearBoolIter S m := by
          intro d; induction d with
          | zero => rfl
          | succ d ihd => change linearBoolStep S (linearBoolIter S (m + d)) = _; rw [ihd, heq]
        have hstep1 := hconst (Fintype.card ι - m)
        have hadd : m + (Fintype.card ι - m) = Fintype.card ι := by omega
        rw [hadd] at hstep1
        exact hne (by rw [hstep1, heq])
      have hlt := hdec m hnem
      have hih := ih (by omega)
      omega
  have := hstrict (Fintype.card ι + 1) le_rfl
  omega

/-- On a finite variable set `ι`, iterating `linearBoolStep` for `Fintype.card ι` steps from
`fun _ => true` produces the unique greatest solution to the homogeneous equations of `S`; hence
`S` is satisfiable if and only if this computable fixed point satisfies every `oneEqs`
constraint. -/
theorem linear_bool_system_greatest_solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : LinearBoolSystem ι) :
    let Xstar := linearBoolIter S (Fintype.card ι)
    S.SatisfiesHom Xstar ∧
    (∀ Y, S.SatisfiesHom Y → ∀ i, Y i = true → Xstar i = true) ∧
    ((∃ Y, S.Satisfies Y) ↔ S.Satisfies Xstar) := by
  intro Xstar
  have hfix : linearBoolStep S Xstar = Xstar := linearBoolIter_stabilizes S
  have hhom : S.SatisfiesHom Xstar := by
    intro eq heq
    constructor
    · rintro ⟨i, hi, hXi⟩
      rw [← hfix] at hXi
      simp only [linearBoolStep, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true,
        Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq] at hXi
      exact ((hXi.2 eq heq).1).resolve_left (not_not.2 hi)
    · rintro ⟨j, hj, hXj⟩
      rw [← hfix] at hXj
      simp only [linearBoolStep, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true,
        Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq] at hXj
      exact ((hXj.2 eq heq).2).resolve_left (not_not.2 hj)
  have hgreatest : ∀ Y, S.SatisfiesHom Y → ∀ i, Y i = true → Xstar i = true := by
    intro Y hY
    have hall : ∀ n i, Y i = true → linearBoolIter S n i = true := by
      intro n
      induction n with
      | zero => intro _ _; rfl
      | succ n ih => exact fun i hYi => linearBoolStep_ge_of_satisfiesHom hY ih i hYi
    exact hall (Fintype.card ι)
  refine ⟨hhom, hgreatest, ⟨?_, fun h => ⟨Xstar, h⟩⟩⟩
  rintro ⟨Y, hYhom, hYone⟩
  refine ⟨hhom, fun I hI => ?_⟩
  obtain ⟨i, hi, hYi⟩ := hYone I hI
  exact ⟨i, hi, hgreatest Y hYhom i hYi⟩

end CslibFrontier.Foundations.LinearAlgebra
