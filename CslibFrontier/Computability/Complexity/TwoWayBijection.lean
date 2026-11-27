/-
Copyright (c) 2026 Matteo Palazzo, Luca Roversi (original mathematics, CC BY 4.0); FormalPapers
contributors (Lean 4 formalization). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FormalPapers contributors
-/
module

-- upstream: candidate

public import Cslib.Computability.Machines.Turing.SingleTape.Deterministic
public import Mathlib.Algebra.Polynomial.Eval.Defs

import Cslib.Foundations.Data.Polynomial.Monotone
import Mathlib.Algebra.Polynomial.Eval.Irreducible
import Mathlib.Data.Nat.Log

/-!
# Polynomially Honest Functions and Two-Way Bijections

This module formalizes polynomially length-bounded word functions, polynomially honest word
functions, and two-way bijections relative to function complexity classes and deterministic
polynomial-time single-tape Turing machines (`Cslib.Turing.SingleTapeTM.PolyTimeComputable`).

## Main definitions

- `CslibFrontier.Complexity.IsPolyLengthBounded`: polynomial upper bound on output word length in
  terms of input word length.
- `CslibFrontier.Complexity.IsPolynomiallyHonest`: polynomial upper bound on input word length in
  terms of output word length (polynomial honesty).
- `CslibFrontier.Complexity.IsTwoWayBijectionWrt`: bijections `f : List α → List α` such that both
  `f` and `f⁻¹` are polynomially honest and belong to `InClass`.
- `CslibFrontier.Complexity.IsSingleTapeTwoWayBijection`: two-way bijections on `List Symbol` with
  respect to `Cslib.Turing.SingleTapeTM.PolyTimeComputable`.

## Main results

- `CslibFrontier.Complexity.IsPolyLengthBounded.of_polyTimeComputable`: polynomial
  length-boundedness of single-tape polynomial-time computable word functions.
- `CslibFrontier.Complexity.IsPolyLengthBounded.isPolynomiallyHonest_of_leftInverse`: automatic
  polynomial honesty from a polynomially length-bounded left inverse.
- `CslibFrontier.Complexity.isTwoWayBijectionWrt_iff_inClass`: redundancy of explicit polynomial
  honesty hypotheses for length-bounded function classes.
- `CslibFrontier.Complexity.IsTwoWayBijectionWrt.id`,
  `CslibFrontier.Complexity.IsTwoWayBijectionWrt.of_inverse`,
  `CslibFrontier.Complexity.IsTwoWayBijectionWrt.comp`: group closure of two-way bijections.
- `CslibFrontier.Complexity.isSingleTapeTwoWayBijection_iff`: characterization of single-tape
  polynomial-time two-way bijections.
-/

public section

open Function Polynomial

namespace CslibFrontier.Complexity

section WordBounds

variable {α β γ : Type*}

/-- A word function `f : List α → List β` is *polynomially length-bounded* if there exists a
polynomial `p : Polynomial ℕ` such that `(f x).length ≤ p.eval x.length` for every input `x`. -/
@[expose]
def IsPolyLengthBounded (f : List α → List β) : Prop :=
  ∃ p : Polynomial ℕ, ∀ x : List α, (f x).length ≤ p.eval x.length

/-- Characterization of `IsPolyLengthBounded` by an explicit polynomial length upper bound. -/
theorem isPolyLengthBounded_iff {f : List α → List β} :
    IsPolyLengthBounded f ↔
      ∃ p : Polynomial ℕ, ∀ x : List α, (f x).length ≤ p.eval x.length :=
  Iff.rfl

/-- The identity function on words is polynomially length-bounded (by `X`). -/
@[simp]
theorem IsPolyLengthBounded.id : IsPolyLengthBounded (fun x : List α ↦ x) :=
  ⟨X, fun x ↦ by simp⟩

/-- Composition preserves polynomial length-boundedness via polynomial composition over `ℕ`. -/
theorem IsPolyLengthBounded.comp {g : List β → List γ} {f : List α → List β}
    (hg : IsPolyLengthBounded g) (hf : IsPolyLengthBounded f) :
    IsPolyLengthBounded (g ∘ f) := by
  rcases hg with ⟨pg, hpg⟩
  rcases hf with ⟨pf, hpf⟩
  refine ⟨pg.comp pf, fun x ↦ ?_⟩
  rw [Function.comp_apply, eval_comp]
  exact (hpg (f x)).trans (pg.monotone_eval (hpf x))

/-- Any constant word function is polynomially length-bounded. -/
@[simp]
theorem IsPolyLengthBounded.const (w : List β) :
    IsPolyLengthBounded (fun _ : List α ↦ w) :=
  ⟨C w.length, fun _ ↦ by simp⟩

/-- Every single-tape polynomial-time computable word function is polynomially length-bounded,
since a `t`-step single-tape Turing machine writes at most `max 1 |x| + t` symbols. -/
theorem IsPolyLengthBounded.of_polyTimeComputable {Symbol : Type} [Inhabited Symbol]
    [Fintype Symbol] {f : List Symbol → List Symbol}
    (hf : Nonempty (Cslib.Turing.SingleTapeTM.PolyTimeComputable f)) :
    IsPolyLengthBounded f := by
  rcases hf with ⟨M⟩
  refine ⟨1 + X + M.poly, fun x ↦ ?_⟩
  have hlen := Cslib.Turing.SingleTapeTM.output_length_le_input_length_add_time
    M.tm x (f x) (M.timeBound x.length) (M.outputsFunInTime x)
  have hb := M.bounds x.length
  simp only [eval_add, eval_one, eval_X]
  omega

/-- A word function `f : List α → List β` is *polynomially honest* if there exists a polynomial
`q : Polynomial ℕ` such that `x.length ≤ q.eval (f x).length` for every input word `x`, so `f`
never shrinks inputs super-polynomially. -/
@[expose]
def IsPolynomiallyHonest (f : List α → List β) : Prop :=
  ∃ q : Polynomial ℕ, ∀ x : List α, x.length ≤ q.eval (f x).length

/-- Characterization of `IsPolynomiallyHonest` by an explicit polynomial lower-growth witness. -/
theorem isPolynomiallyHonest_iff {f : List α → List β} :
    IsPolynomiallyHonest f ↔
      ∃ q : Polynomial ℕ, ∀ x : List α, x.length ≤ q.eval (f x).length :=
  Iff.rfl

/-- The identity function on words is polynomially honest (with witness `X`). -/
@[simp]
theorem IsPolynomiallyHonest.id : IsPolynomiallyHonest (fun x : List α ↦ x) :=
  ⟨X, fun x ↦ by simp⟩

/-- Composition of polynomially honest word functions is polynomially honest. -/
theorem IsPolynomiallyHonest.comp {g : List β → List γ} {f : List α → List β}
    (hg : IsPolynomiallyHonest g) (hf : IsPolynomiallyHonest f) :
    IsPolynomiallyHonest (g ∘ f) := by
  rcases hf with ⟨qf, hqf⟩
  rcases hg with ⟨qg, hqg⟩
  refine ⟨qf.comp qg, fun x ↦ ?_⟩
  rw [Function.comp_apply, eval_comp]
  exact (hqf x).trans (qf.monotone_eval (hqg (f x)))

/-- If `f` admits a left inverse `g` that is polynomially length-bounded, then `f` is
automatically polynomially honest. -/
theorem IsPolyLengthBounded.isPolynomiallyHonest_of_leftInverse
    {f : List α → List β} {g : List β → List α}
    (hg : IsPolyLengthBounded g) (hinv : LeftInverse g f) :
    IsPolynomiallyHonest f := by
  rcases hg with ⟨p, hp⟩
  refine ⟨p, fun x ↦ ?_⟩
  simpa only [hinv x] using hp (f x)

/-- Every length-nondecreasing word function (`x.length ≤ (f x).length`) is polynomially honest.
-/
theorem IsPolynomiallyHonest.of_length_le {f : List α → List β}
    (hle : ∀ x : List α, x.length ≤ (f x).length) :
    IsPolynomiallyHonest f :=
  ⟨X, fun x ↦ by simpa using hle x⟩

end WordBounds

section TwoWayBijection

variable {α : Type*}

/-- Relative to a function class `InClass : (List α → List α) → Prop`, a map `f : List α → List α`
is a *two-way bijection* if `f` is bijective and both `f` and its inverse `g` are polynomially
honest and belong to `InClass`. -/
@[expose]
def IsTwoWayBijectionWrt (InClass : (List α → List α) → Prop)
    (f : List α → List α) : Prop :=
  ∃ g : List α → List α,
    LeftInverse g f ∧ RightInverse g f ∧
      IsPolynomiallyHonest f ∧ IsPolynomiallyHonest g ∧ InClass f ∧ InClass g

/-- Every two-way bijection with respect to `InClass` is bijective. -/
theorem IsTwoWayBijectionWrt.bijective {InClass : (List α → List α) → Prop}
    {f : List α → List α} (hf : IsTwoWayBijectionWrt InClass f) : Bijective f := by
  rcases hf with ⟨g, hL, hR, -, -, -, -⟩
  exact ⟨hL.injective, hR.surjective⟩

/-- Every two-way bijection with respect to `InClass` belongs to `InClass`. -/
theorem IsTwoWayBijectionWrt.inClass {InClass : (List α → List α) → Prop}
    {f : List α → List α} (hf : IsTwoWayBijectionWrt InClass f) : InClass f := by
  rcases hf with ⟨_, -, -, -, -, hfC, -⟩
  exact hfC

/-- Every two-way bijection with respect to `InClass` is polynomially honest. -/
theorem IsTwoWayBijectionWrt.honest {InClass : (List α → List α) → Prop}
    {f : List α → List α} (hf : IsTwoWayBijectionWrt InClass f) : IsPolynomiallyHonest f := by
  rcases hf with ⟨_, -, -, hHon, -, -, -⟩
  exact hHon

/-- Any two-sided inverse `g` of a two-way bijection `f` belongs to `InClass` and is itself a
two-way bijection with respect to `InClass`. -/
theorem IsTwoWayBijectionWrt.of_inverse {InClass : (List α → List α) → Prop}
    {f g : List α → List α} (hf : IsTwoWayBijectionWrt InClass f)
    (hL : LeftInverse g f) (hR : RightInverse g f) :
    IsTwoWayBijectionWrt InClass g := by
  rcases hf with ⟨g', hL', _hR', hHonF, hHonG', hfC, hg'C⟩
  have hgg' : g = g' := funext fun y ↦ by rw [← hR y, hL (g y), hL' (g y)]
  subst hgg'
  exact ⟨f, hR, hL, hHonG', hHonF, hg'C, hfC⟩

/-- For an equivalence `e : List α ≃ List α`, `e` is a two-way bijection iff `e.symm` is. -/
@[simp]
theorem isTwoWayBijectionWrt_symm_iff {InClass : (List α → List α) → Prop}
    (e : List α ≃ List α) :
    IsTwoWayBijectionWrt InClass e.symm ↔ IsTwoWayBijectionWrt InClass e :=
  ⟨fun h ↦ h.of_inverse e.right_inv e.left_inv, fun h ↦ h.of_inverse e.left_inv e.right_inv⟩

/-- When every function in `InClass` is polynomially length-bounded, polynomial honesty of `f` and
`f⁻¹` is redundant: a map `f` is a two-way bijection with respect to `InClass` if and only if it
admits a two-sided inverse `g` with both `f ∈ InClass` and `g ∈ InClass`. -/
theorem isTwoWayBijectionWrt_iff_inClass {InClass : (List α → List α) → Prop}
    (hBound : ∀ h : List α → List α, InClass h → IsPolyLengthBounded h)
    {f : List α → List α} :
    IsTwoWayBijectionWrt InClass f ↔
      ∃ g : List α → List α,
        LeftInverse g f ∧ RightInverse g f ∧ InClass f ∧ InClass g := by
  constructor
  · rintro ⟨g, hL, hR, -, -, hfC, hgC⟩
    exact ⟨g, hL, hR, hfC, hgC⟩
  · rintro ⟨g, hL, hR, hfC, hgC⟩
    exact ⟨g, hL, hR,
      (hBound g hgC).isPolynomiallyHonest_of_leftInverse hL,
      (hBound f hfC).isPolynomiallyHonest_of_leftInverse hR,
      hfC, hgC⟩

/-- Characterization of `IsTwoWayBijectionWrt` for a known bijection `f` (`Function.Bijective f`)
via `(Equiv.ofBijective f hbij).symm`. -/
theorem isTwoWayBijectionWrt_of_bijective_iff {InClass : (List α → List α) → Prop}
    {f : List α → List α} (hbij : Bijective f) :
    IsTwoWayBijectionWrt InClass f ↔
      IsPolynomiallyHonest f ∧
        IsPolynomiallyHonest (Equiv.ofBijective f hbij).symm ∧
        InClass f ∧
        InClass (Equiv.ofBijective f hbij).symm := by
  let e := Equiv.ofBijective f hbij
  constructor
  · rintro ⟨g, hL, _hR, hHonF, hHonG, hfC, hgC⟩
    have hge : g = e.symm := funext fun y ↦ by
      have hy : f (e.symm y) = y := e.apply_symm_apply y
      calc g y = g (f (e.symm y)) := congrArg g hy.symm
        _ = e.symm y := hL (e.symm y)
    subst hge
    exact ⟨hHonF, hHonG, hfC, hgC⟩
  · rintro ⟨hHonF, hHonG, hfC, hgC⟩
    exact ⟨e.symm, e.left_inv, e.right_inv, hHonF, hHonG, hfC, hgC⟩

/-- The identity on `List α` is a two-way bijection whenever `InClass` contains the identity. -/
theorem IsTwoWayBijectionWrt.id {InClass : (List α → List α) → Prop}
    (hid : InClass (fun x : List α ↦ x)) :
    IsTwoWayBijectionWrt InClass (fun x : List α ↦ x) :=
  ⟨fun x ↦ x, fun _ ↦ rfl, fun _ ↦ rfl, .id, .id, hid, hid⟩

/-- Two-way bijections with respect to `InClass` are closed under composition whenever `InClass`
is closed under composition. -/
theorem IsTwoWayBijectionWrt.comp {InClass : (List α → List α) → Prop}
    (hcomp : ∀ {g f : List α → List α}, InClass g → InClass f → InClass (g ∘ f))
    {g f : List α → List α}
    (hg : IsTwoWayBijectionWrt InClass g) (hf : IsTwoWayBijectionWrt InClass f) :
    IsTwoWayBijectionWrt InClass (g ∘ f) := by
  rcases hg with ⟨ginv, hgL, hgR, hHonG, hHonGinv, hgC, hginvC⟩
  rcases hf with ⟨finv, hfL, hfR, hHonF, hHonFinv, hfC, hfinvC⟩
  refine ⟨finv ∘ ginv,
    fun x ↦ by simp [Function.comp_apply, hgL (f x), hfL x],
    fun y ↦ by simp [Function.comp_apply, hfR (ginv y), hgR y],
    hHonG.comp hHonF, hHonFinv.comp hHonGinv,
    hcomp hgC hfC, hcomp hfinvC hginvC⟩

/-- Two-way bijections on `List Symbol` with respect to single-tape polynomial-time Turing machine
computability (`Cslib.Turing.SingleTapeTM.PolyTimeComputable`). -/
@[expose]
def IsSingleTapeTwoWayBijection {Symbol : Type} [Inhabited Symbol] [Fintype Symbol]
    (f : List Symbol → List Symbol) : Prop :=
  IsTwoWayBijectionWrt
    (fun h ↦ Nonempty (Cslib.Turing.SingleTapeTM.PolyTimeComputable h)) f

/-- Characterization of single-tape polynomial-time two-way bijections: polynomial honesty of both
`f` and `f⁻¹` follows automatically from two-sided polynomial-time computability. -/
theorem isSingleTapeTwoWayBijection_iff {Symbol : Type} [Inhabited Symbol] [Fintype Symbol]
    {f : List Symbol → List Symbol} :
    IsSingleTapeTwoWayBijection f ↔
      ∃ g : List Symbol → List Symbol,
        LeftInverse g f ∧ RightInverse g f ∧
          Nonempty (Cslib.Turing.SingleTapeTM.PolyTimeComputable f) ∧
          Nonempty (Cslib.Turing.SingleTapeTM.PolyTimeComputable g) :=
  isTwoWayBijectionWrt_iff_inClass (fun _ ↦ IsPolyLengthBounded.of_polyTimeComputable)

/-- The identity on `List Symbol` is a single-tape two-way bijection. -/
theorem IsSingleTapeTwoWayBijection.id {Symbol : Type} [Inhabited Symbol] [Fintype Symbol] :
    IsSingleTapeTwoWayBijection (fun x : List Symbol ↦ x) :=
  IsTwoWayBijectionWrt.id ⟨Cslib.Turing.SingleTapeTM.PolyTimeComputable.id⟩

/-- Single-tape two-way bijections are closed under two-sided inversion. -/
theorem IsSingleTapeTwoWayBijection.of_inverse {Symbol : Type} [Inhabited Symbol]
    [Fintype Symbol] {f g : List Symbol → List Symbol}
    (hf : IsSingleTapeTwoWayBijection f) (hL : LeftInverse g f) (hR : RightInverse g f) :
    IsSingleTapeTwoWayBijection g :=
  IsTwoWayBijectionWrt.of_inverse hf hL hR

/-- Single-tape two-way bijections are closed under composition. -/
theorem IsSingleTapeTwoWayBijection.comp {Symbol : Type} [Inhabited Symbol] [Fintype Symbol]
    {g f : List Symbol → List Symbol}
    (hg : IsSingleTapeTwoWayBijection g) (hf : IsSingleTapeTwoWayBijection f) :
    IsSingleTapeTwoWayBijection (g ∘ f) :=
  IsTwoWayBijectionWrt.comp (fun ⟨h1⟩ ⟨h2⟩ ↦ ⟨h2.comp h1⟩) hg hf

end TwoWayBijection

end CslibFrontier.Complexity
