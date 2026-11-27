/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Google DeepMind
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.Algebraic.PolynomialCalculus.Proof
public import Mathlib.RingTheory.Nullstellensatz

import Mathlib.RingTheory.Nilpotent.Defs
import Mathlib.Tactic.Ring

/-!
# Radical Polynomial Calculus (`PC^rad`)

**Radical Polynomial Calculus** ($\mathsf{PC}^{\mathrm{rad}}$) extends Polynomial Calculus
(`Cslib.Logic.PL.PC.IsProof`) by the **radical inference rule** $p^2 = 0 \vdash p = 0$
(`Cslib.Logic.PL.PCRad.IsProof.rad`), together with the constant-$0$ axiom (`zero`) so that every
element of the radical ideal $\sqrt{\langle F \rangle}$ is derivable even when `F` is empty.

* **Soundness** (`Cslib.Logic.PL.PCRad.IsProof.eval_eq_zero`): over any reduced commutative semiring
  (`[CommSemiring R] [IsReduced R]`), every line of a $\mathsf{PC}^{\mathrm{rad}}$ proof vanishes at
  every common zero of the inputs `F`.
* **Radical ideal closure** (`Cslib.Logic.PL.PCRad.exists_derivableInDegree_of_mem_radical`): over
  any commutative ring `R`, every polynomial in `(Ideal.span {f | f ∈ F}).radical` has a
  $\mathsf{PC}^{\mathrm{rad}}$ derivation in some finite degree.
* **Implicational completeness**
  (`Cslib.Logic.PL.PCRad.exists_derivableInDegree_iff_forall_eval_eq_zero`):
  over any algebraically closed field `K` and finite variable type `V`, a polynomial `q` is
  derivable from `F` in $\mathsf{PC}^{\mathrm{rad}}$ in some degree if and only if `q` vanishes at
  every common zero of `F` in `V → K`.

## Main definitions

* `Cslib.Logic.PL.PCRad.IsProof`: Radical Polynomial Calculus derivations from an input list `F`.
* `Cslib.Logic.PL.PCRad.DerivableInDegree`: derivability of a target polynomial `q` within degree
  `d`.
* `Cslib.Logic.PL.PCRad.RefutableInSize`, `Cslib.Logic.PL.PCRad.RefutableInDegree`: refutability
  (`1 ∈ ls`) within a size or degree bound.

## Main results

* `Cslib.Logic.PL.PCRad.IsProof.of_pc`: every `PC.IsProof` lifts to `PCRad.IsProof`.
* `Cslib.Logic.PL.PCRad.IsProof.eval_eq_zero`,
  `Cslib.Logic.PL.PCRad.IsProof.exists_eval_ne_zero`: semantic soundness over reduced semirings.
* `Cslib.Logic.PL.PCRad.exists_derivableInDegree_of_mem_span`,
  `Cslib.Logic.PL.PCRad.exists_derivableInDegree_of_mem_radical`: derivability of all elements of
  `Ideal.span` and its radical.
* `Cslib.Logic.PL.PCRad.exists_derivableInDegree_iff_forall_eval_eq_zero`: implicational
  completeness over algebraically closed fields via Hilbert's Nullstellensatz.
* `Cslib.Logic.PL.PCRad.exists_refutableInDegree_iff_not_exists_eval_eq_zero`: refutational
  completeness over algebraically closed fields.
-/

public section

namespace Cslib.Logic.PL.PCRad

open MvPolynomial

section Semiring

variable {V R : Type*} [CommSemiring R]

/-- A **Radical Polynomial Calculus (`PC^rad`) proof** from an input list `F`, listed from its last
line to its first: every line is `0`, an input from `F`, a scalar linear combination of two earlier
lines, an earlier line multiplied by a variable, or `p` deduced from an earlier line `p ^ 2`. -/
inductive IsProof (F : List (MvPolynomial V R)) : List (MvPolynomial V R) → Prop
  /-- The empty proof. -/
  | nil : IsProof F []
  /-- The zero polynomial `0 = 0`. -/
  | zero {ls} (h : IsProof F ls) : IsProof F (0 :: ls)
  /-- An input polynomial from `F`. -/
  | mem {ls p} (h : IsProof F ls) (hp : p ∈ F) : IsProof F (p :: ls)
  /-- A scalar linear combination of two earlier lines. -/
  | linear {ls p q} (a b : R) (h : IsProof F ls) (hp : p ∈ ls) (hq : q ∈ ls) :
      IsProof F ((C a * p + C b * q) :: ls)
  /-- Multiplication of an earlier line by a variable. -/
  | mulVar {ls p} (v : V) (h : IsProof F ls) (hp : p ∈ ls) :
      IsProof F ((X v * p) :: ls)
  /-- Radical rule: from `p ^ 2` deduce `p`. -/
  | rad {ls p} (h : IsProof F ls) (hp2 : p ^ 2 ∈ ls) :
      IsProof F (p :: ls)

/-- `DerivableInDegree F q d` holds when some `PCRad` proof from `F` of degree at most `d` contains
`q`. -/
@[expose] def DerivableInDegree (F : List (MvPolynomial V R)) (q : MvPolynomial V R) (d : ℕ) :
    Prop :=
  ∃ ls, IsProof F ls ∧ q ∈ ls ∧ PC.degree ls ≤ d

/-- `RefutableInSize F s` holds when some `PCRad` refutation of `F` (`1 ∈ ls`) has support size at
most `s`. -/
@[expose] def RefutableInSize (F : List (MvPolynomial V R)) (s : ℕ) : Prop :=
  ∃ ls, IsProof F ls ∧ (1 : MvPolynomial V R) ∈ ls ∧ PC.size ls ≤ s

/-- `RefutableInDegree F d` holds when some `PCRad` refutation of `F` (`1 ∈ ls`) has degree at most
`d`. -/
@[expose] def RefutableInDegree (F : List (MvPolynomial V R)) (d : ℕ) : Prop :=
  DerivableInDegree F 1 d

namespace IsProof

/-- Every standard Polynomial Calculus proof (`PC.IsProof`) is a `PCRad` proof. -/
theorem of_pc {F ls : List (MvPolynomial V R)} (h : PC.IsProof F ls) : IsProof F ls := by
  induction h with
  | nil => exact .nil
  | mem _ hp ih => exact .mem ih hp
  | linear a b _ hp hq ih => exact .linear a b ih hp hq
  | mulVar v _ hp ih => exact .mulVar v ih hp

/-- Concatenation of two `PCRad` proofs from the same input list `F`. -/
theorem append {F ls ls' : List (MvPolynomial V R)}
    (h : IsProof F ls) (h' : IsProof F ls') : IsProof F (ls ++ ls') := by
  induction h with
  | nil => exact h'
  | zero _ ih => exact .zero ih
  | mem _ hp ih => exact .mem ih hp
  | linear a b _ hp hq ih =>
    exact .linear a b ih (List.mem_append_left _ hp) (List.mem_append_left _ hq)
  | mulVar v _ hp ih => exact .mulVar v ih (List.mem_append_left _ hp)
  | rad _ hp2 ih => exact .rad ih (List.mem_append_left _ hp2)

/-- Monotonicity of `IsProof` in the input list `F`. -/
theorem mono {F G ls : List (MvPolynomial V R)} (h : IsProof F ls)
    (hFG : ∀ f ∈ F, f ∈ G) : IsProof G ls := by
  induction h with
  | nil => exact .nil
  | zero _ ih => exact .zero ih
  | mem _ hp ih => exact .mem ih (hFG _ hp)
  | linear a b _ hp hq ih => exact .linear a b ih hp hq
  | mulVar v _ hp ih => exact .mulVar v ih hp
  | rad _ hp2 ih => exact .rad ih hp2

/-- **Soundness.** Over any reduced commutative semiring (`[IsReduced R]`), every line of a `PCRad`
proof vanishes at every common zero of `F`. -/
theorem eval_eq_zero [IsReduced R] {F ls : List (MvPolynomial V R)} (h : IsProof F ls) {x : V → R}
    (hx : ∀ f ∈ F, eval x f = 0) : ∀ p ∈ ls, eval x p = 0 := by
  induction h with
  | nil => simp
  | zero _ ih => exact List.forall_mem_cons.mpr ⟨by simp, ih⟩
  | mem _ hp ih => exact List.forall_mem_cons.mpr ⟨hx _ hp, ih⟩
  | linear a b _ hp hq ih =>
    exact List.forall_mem_cons.mpr ⟨by simp [ih _ hp, ih _ hq], ih⟩
  | mulVar v _ hp ih => exact List.forall_mem_cons.mpr ⟨by simp [ih _ hp], ih⟩
  | @rad _ p _ hp2 ih =>
    refine List.forall_mem_cons.mpr ⟨?_, ih⟩
    have hsq : (eval x p) ^ 2 = 0 := by simpa [map_pow] using ih (p ^ 2) hp2
    exact IsNilpotent.eq_zero ⟨2, hsq⟩

/-- Over a nontrivial reduced commutative semiring, a `PCRad` refutation rules out common zeros of
`F`. -/
theorem exists_eval_ne_zero [Nontrivial R] [IsReduced R] {F ls : List (MvPolynomial V R)}
    (h : IsProof F ls) (h1 : (1 : MvPolynomial V R) ∈ ls) (x : V → R) :
    ∃ f ∈ F, eval x f ≠ 0 := by
  by_contra! hx
  simpa using h.eval_eq_zero hx 1 h1

end IsProof

end Semiring

section CommRing

variable {V R : Type*} [CommRing R]

private theorem degree_append (ls₁ ls₂ : List (MvPolynomial V R)) :
    PC.degree (ls₁ ++ ls₂) = max (PC.degree ls₁) (PC.degree ls₂) := by
  induction ls₁ with
  | nil => simp
  | cons p ls₁ ih => simp [PC.degree_cons, ih, max_assoc]

private theorem derivableInDegree_add {F : List (MvPolynomial V R)} {p₁ p₂ : MvPolynomial V R}
    {d₁ d₂ : ℕ} (h₁ : DerivableInDegree F p₁ d₁) (h₂ : DerivableInDegree F p₂ d₂) :
    DerivableInDegree F (p₁ + p₂) (max d₁ d₂) := by
  obtain ⟨ls₁, hls₁, hm₁, hd₁⟩ := h₁
  obtain ⟨ls₂, hls₂, hm₂, hd₂⟩ := h₂
  have heq : p₁ + p₂ = C 1 * p₁ + C 1 * p₂ := by simp
  refine ⟨(p₁ + p₂) :: (ls₁ ++ ls₂),
    heq ▸ .linear 1 1 (hls₁.append hls₂) (List.mem_append_left _ hm₁)
      (List.mem_append_right _ hm₂),
    List.mem_cons_self, ?_⟩
  rw [PC.degree_cons, degree_append, max_le_iff]
  refine ⟨(totalDegree_add _ _).trans (max_le
      ((PC.degree_le_iff.mp hd₁ _ hm₁).trans (le_max_left _ _))
      ((PC.degree_le_iff.mp hd₂ _ hm₂).trans (le_max_right _ _))),
    max_le (hd₁.trans (le_max_left _ _)) (hd₂.trans (le_max_right _ _))⟩

private theorem exists_derivableInDegree_mul_left {F : List (MvPolynomial V R)}
    {p : MvPolynomial V R} {d : ℕ} (hp : DerivableInDegree F p d) (g : MvPolynomial V R) :
    ∃ d', DerivableInDegree F (g * p) d' := by
  induction g using MvPolynomial.induction_on with
  | C c =>
    obtain ⟨ls, hls, hm, hd⟩ := hp
    have heq : C c * p = C c * p + C 0 * p := by simp
    exact ⟨max (C c * p).totalDegree d, (C c * p) :: ls, heq ▸ .linear c 0 hls hm hm,
      List.mem_cons_self, by rw [PC.degree_cons]; exact max_le_max le_rfl hd⟩
  | add g₁ g₂ ih₁ ih₂ =>
    obtain ⟨d₁, h₁⟩ := ih₁
    obtain ⟨d₂, h₂⟩ := ih₂
    rw [add_mul]
    exact ⟨max d₁ d₂, derivableInDegree_add h₁ h₂⟩
  | mul_X g₁ v ih =>
    obtain ⟨d₁, ls₁, hls₁, hm₁, hd₁⟩ := ih
    have heq : (g₁ * X v) * p = X v * (g₁ * p) := by ring
    exact ⟨max ((g₁ * X v) * p).totalDegree d₁, ((g₁ * X v) * p) :: ls₁,
      heq ▸ .mulVar v hls₁ hm₁, List.mem_cons_self,
      by rw [PC.degree_cons]; exact max_le_max le_rfl hd₁⟩

/-- Every polynomial in `Ideal.span {f | f ∈ F}` is derivable from `F` in `PCRad` in some finite
degree. -/
theorem exists_derivableInDegree_of_mem_span {F : List (MvPolynomial V R)} {q : MvPolynomial V R}
    (hq : q ∈ Ideal.span {f : MvPolynomial V R | f ∈ F}) :
    ∃ d, DerivableInDegree F q d := by
  induction hq using Submodule.span_induction with
  | mem p hp =>
    exact ⟨p.totalDegree, [p], .mem .nil hp, List.mem_cons_self, by simp⟩
  | zero =>
    exact ⟨0, [0], .zero .nil, List.mem_cons_self, by simp⟩
  | add p₁ p₂ _ _ ih₁ ih₂ =>
    obtain ⟨d₁, h₁⟩ := ih₁
    obtain ⟨d₂, h₂⟩ := ih₂
    exact ⟨max d₁ d₂, derivableInDegree_add h₁ h₂⟩
  | smul r p _ ih =>
    obtain ⟨d, hdp⟩ := ih
    rw [smul_eq_mul]
    exact exists_derivableInDegree_mul_left hdp r

private theorem exists_derivableInDegree_of_pow_two_pow {F : List (MvPolynomial V R)}
    {q : MvPolynomial V R} :
    ∀ (m d : ℕ), DerivableInDegree F (q ^ (2 ^ m)) d → ∃ d', DerivableInDegree F q d' := by
  intro m
  induction m with
  | zero =>
    intro d h
    exact ⟨d, by simpa using h⟩
  | succ m ih =>
    intro d ⟨ls, hls, hmem, hdeg⟩
    have hpow : (q ^ (2 ^ m)) ^ 2 = q ^ (2 ^ (m + 1)) := by ring
    exact ih (max (q ^ (2 ^ m)).totalDegree d) ⟨q ^ (2 ^ m) :: ls,
      .rad hls (hpow ▸ hmem), List.mem_cons_self,
      by rw [PC.degree_cons]; exact max_le_max le_rfl hdeg⟩

/-- Every polynomial in `(Ideal.span {f | f ∈ F}).radical` is derivable from `F` in `PCRad` in some
finite degree. -/
theorem exists_derivableInDegree_of_mem_radical {F : List (MvPolynomial V R)} {q : MvPolynomial V R}
    (hq : q ∈ (Ideal.span {f : MvPolynomial V R | f ∈ F}).radical) :
    ∃ d, DerivableInDegree F q d := by
  obtain ⟨k, hk⟩ := hq
  have hk_le : k ≤ 2 ^ k := Nat.le_of_lt k.lt_two_pow_self
  have hpow2 : q ^ (2 ^ k) ∈ Ideal.span {f : MvPolynomial V R | f ∈ F} := by
    have heq : q ^ (2 ^ k) = q ^ (2 ^ k - k) * q ^ k := by
      rw [← pow_add, Nat.sub_add_cancel hk_le]
    rw [heq]
    exact Ideal.mul_mem_left _ _ hk
  obtain ⟨d, hd⟩ := exists_derivableInDegree_of_mem_span hpow2
  exact exists_derivableInDegree_of_pow_two_pow k d hd

end CommRing

section AlgClosed

variable {V K : Type*} [Field K] [IsAlgClosed K] [Finite V]

/-- **Implicational completeness of `PC^rad` over algebraically closed fields**: over an
algebraically closed field `K` and finite variable type `V`, `q` is derivable from `F` in `PCRad` in
some degree if and only if `q` vanishes at every common zero of `F` in `V → K`. -/
theorem exists_derivableInDegree_iff_forall_eval_eq_zero
    (F : List (MvPolynomial V K)) (q : MvPolynomial V K) :
    (∃ d, DerivableInDegree F q d) ↔
      ∀ x : V → K, (∀ f ∈ F, eval x f = 0) → eval x q = 0 := by
  refine ⟨fun ⟨d, ls, hls, hq, _⟩ x hx => hls.eval_eq_zero hx q hq, fun hent => ?_⟩
  have hvan :
      q ∈ MvPolynomial.vanishingIdeal K
        (MvPolynomial.zeroLocus K (Ideal.span {f : MvPolynomial V K | f ∈ F})) := by
    rw [MvPolynomial.mem_vanishingIdeal_iff]
    intro x hx
    rw [MvPolynomial.zeroLocus_span] at hx
    simpa [MvPolynomial.aeval_def] using
      hent x fun p hp => by simpa [MvPolynomial.aeval_def] using hx p hp
  rw [MvPolynomial.vanishingIdeal_zeroLocus_eq_radical] at hvan
  exact exists_derivableInDegree_of_mem_radical hvan

/-- **Refutational completeness of `PC^rad` over algebraically closed fields**: `F` has a `PCRad`
refutation in some degree if and only if `F` has no common zero in `V → K`. -/
theorem exists_refutableInDegree_iff_not_exists_eval_eq_zero (F : List (MvPolynomial V K)) :
    (∃ d, RefutableInDegree F d) ↔ ¬ ∃ x : V → K, ∀ f ∈ F, eval x f = 0 := by
  dsimp only [RefutableInDegree]
  rw [exists_derivableInDegree_iff_forall_eval_eq_zero]
  simp

end AlgClosed

end Cslib.Logic.PL.PCRad
