module

public import CslibFrontier.Foundations.Data.BitString.Basic
public import CslibFrontier.Foundations.Data.BitString.Sign
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Bent Boolean Functions, Walsh–Hadamard Duals, and Maiorana–McFarland Constructions

This module formalizes bent Boolean functions over finite-dimensional binary vector spaces, their
Walsh–Hadamard duals, the Walsh–Hadamard transform of hidden shifts of bent functions, and the
Maiorana–McFarland construction of bent functions from arbitrary permutations.

## Main definitions

* `CslibFrontier.BooleanAnalysis.walshCoeff`: normalized Walsh–Hadamard coefficient
  `2^{-|ι|} ∑_x (-1)^{g(x) + x · α}` over `ℝ`.
* `CslibFrontier.BooleanAnalysis.IsBent`: predicate asserting `|walshCoeff g α| = 2^{-|ι|/2}` for
  every frequency `α`.
* `CslibFrontier.BooleanAnalysis.bentDual`: dual Boolean function recording the sign of each
  Walsh–Hadamard coefficient.
* `CslibFrontier.BooleanAnalysis.maioranaMcFarland`: Maiorana–McFarland Boolean function
  `(u, w) ↦ u · π(w)` induced by a permutation `π` of `ι → Bool`.

## Main results

* `CslibFrontier.BooleanAnalysis.walshCoeff_eq_bentDual`: sign decomposition of Walsh–Hadamard
  coefficients of a bent function via its dual.
* `CslibFrontier.BooleanAnalysis.walshCoeff_shift_eq`: Walsh–Hadamard transform of a shifted bent
  function `x ↦ g(x + s)`.
* `CslibFrontier.BooleanAnalysis.isBent_maioranaMcFarland` and
  `CslibFrontier.BooleanAnalysis.bentDual_maioranaMcFarland`: bentness and explicit dual formula
  `(α, β) ↦ β · π⁻¹(α)` for every Maiorana–McFarland function.
-/

public section

namespace CslibFrontier

namespace BooleanAnalysis

open Finset Cslib.BitString

/-- Normalized Walsh–Hadamard coefficient of a Boolean function `g : (ι → Bool) → Bool` at
`α : ι → Bool`, defined as `2^{-|ι|} ∑_x (-1)^{g(x) ⊕ (x · α)}`. -/
@[expose] noncomputable def walshCoeff {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : (ι → Bool) → Bool) (α : ι → Bool) : ℝ :=
  (2 : ℝ) ^ (-(Fintype.card ι : ℝ)) *
    ∑ x : ι → Bool, signVal (g x ^^ (x ⬝ᵥ α))

/-- A Boolean function `g` on `𝔽₂^ι` is **bent** if every normalized Walsh–Hadamard coefficient has
magnitude `2^{-|ι|/2}`. -/
@[expose] def IsBent {ι : Type*} [Fintype ι] [DecidableEq ι] (g : (ι → Bool) → Bool) : Prop :=
  ∀ α : ι → Bool, |walshCoeff g α| = (2 : ℝ) ^ (-(Fintype.card ι : ℝ) / 2)

/-- The **dual** of a bent function `g`: `bentDual g α = true` iff `walshCoeff g α < 0`. -/
@[expose] noncomputable def bentDual {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : (ι → Bool) → Bool) (α : ι → Bool) : Bool := by
  classical
  exact decide (walshCoeff g α < 0)

/-- For a bent function `g`, the normalized Walsh–Hadamard coefficient at `α` equals
`2^{-|ι|/2} * (-1)^{g̃(α)}`. -/
theorem walshCoeff_eq_bentDual {ι : Type*} [Fintype ι] [DecidableEq ι] {g : (ι → Bool) → Bool}
    (hg : IsBent g) (α : ι → Bool) :
    walshCoeff g α = (2 : ℝ) ^ (-(Fintype.card ι : ℝ) / 2) * signVal (bentDual g α) := by
  classical
  have habs := hg α
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (-(Fintype.card ι : ℝ) / 2) := by positivity
  unfold bentDual signVal
  rcases abs_eq (le_of_lt hpos) |>.mp habs with h | h
  · have hlt : ¬(walshCoeff g α < 0) := by linarith
    rw [decide_eq_false hlt]
    simp [h]
  · have hlt : walshCoeff g α < 0 := by linarith
    rw [decide_eq_true hlt]
    simp [h]

/-- Unnormalized Walsh–Hadamard sum identity for a bent function `g`. -/
theorem sum_signVal_xor_eq_bentDual {ι : Type*} [Fintype ι] [DecidableEq ι]
    {g : (ι → Bool) → Bool} (hg : IsBent g) (α : ι → Bool) :
    ∑ x : ι → Bool, signVal (g x ^^ (x ⬝ᵥ α)) =
      (2 : ℝ) ^ ((Fintype.card ι : ℝ) / 2) * signVal (bentDual g α) := by
  have h := walshCoeff_eq_bentDual hg α
  unfold walshCoeff at h
  have hpow : (2 : ℝ) ^ (Fintype.card ι : ℝ) * (2 : ℝ) ^ (-(Fintype.card ι : ℝ)) = 1 := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2), add_neg_cancel, Real.rpow_zero]
  have hpow2 : (2 : ℝ) ^ (Fintype.card ι : ℝ) * (2 : ℝ) ^ (-(Fintype.card ι : ℝ) / 2) =
      (2 : ℝ) ^ ((Fintype.card ι : ℝ) / 2) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1; ring
  calc ∑ x : ι → Bool, signVal (g x ^^ (x ⬝ᵥ α))
      = (2 : ℝ) ^ (Fintype.card ι : ℝ) *
          ((2 : ℝ) ^ (-(Fintype.card ι : ℝ)) * ∑ x : ι → Bool, signVal (g x ^^ (x ⬝ᵥ α))) := by
        rw [← mul_assoc, hpow, one_mul]
    _ = (2 : ℝ) ^ (Fintype.card ι : ℝ) *
          ((2 : ℝ) ^ (-(Fintype.card ι : ℝ) / 2) * signVal (bentDual g α)) := by rw [h]
    _ = (2 : ℝ) ^ ((Fintype.card ι : ℝ) / 2) * signVal (bentDual g α) := by
        rw [← mul_assoc, hpow2]

/-- For any secret `s` and any frequency `α`, the normalized Walsh–Hadamard transform of the
shifted bent function `x ↦ g(x + s)` equals `2^{-|ι|/2} * (-1)^{s · α + g̃(α)}`. -/
theorem walshCoeff_shift_eq {ι : Type*} [Fintype ι] [DecidableEq ι] {g : (ι → Bool) → Bool}
    (hg : IsBent g) (s α : ι → Bool) :
    walshCoeff (fun x => g (x + s)) α =
      (2 : ℝ) ^ (-(Fintype.card ι : ℝ) / 2) * signVal ((s ⬝ᵥ α) ^^ bentDual g α) := by
  unfold walshCoeff
  have hbij : ∑ x : ι → Bool, signVal (g (x + s) ^^ (x ⬝ᵥ α)) =
      ∑ y : ι → Bool, signVal (g y ^^ ((y + s) ⬝ᵥ α)) := by
    refine Fintype.sum_equiv (Equiv.addRight s) _ _ fun x => ?_
    simp [add_assoc]
  rw [hbij]
  have hdot : ∀ y : ι → Bool, (y + s) ⬝ᵥ α = ((y ⬝ᵥ α) ^^ (s ⬝ᵥ α)) := by
    intro y
    rw [add_dotProduct]
    rfl
  simp_rw [hdot]
  have hsplit : ∀ y : ι → Bool,
      signVal (g y ^^ ((y ⬝ᵥ α) ^^ (s ⬝ᵥ α))) =
        signVal (s ⬝ᵥ α) * signVal (g y ^^ (y ⬝ᵥ α)) := by
    intro y
    rw [← Bool.xor_assoc, signVal_xor, mul_comm, signVal_xor, mul_comm (signVal (g y))]
  simp_rw [hsplit, ← Finset.mul_sum]
  have h1 := walshCoeff_eq_bentDual hg α
  unfold walshCoeff at h1
  rw [signVal_xor]
  calc (2 : ℝ) ^ (-(Fintype.card ι : ℝ)) *
        (signVal (s ⬝ᵥ α) * ∑ x : ι → Bool, signVal (g x ^^ (x ⬝ᵥ α)))
      = signVal (s ⬝ᵥ α) *
          ((2 : ℝ) ^ (-(Fintype.card ι : ℝ)) * ∑ x : ι → Bool, signVal (g x ^^ (x ⬝ᵥ α))) := by
        ring
    _ = signVal (s ⬝ᵥ α) * ((2 : ℝ) ^ (-(Fintype.card ι : ℝ) / 2) * signVal (bentDual g α)) := by
        rw [h1]
    _ = (2 : ℝ) ^ (-(Fintype.card ι : ℝ) / 2) * (signVal (s ⬝ᵥ α) * signVal (bentDual g α)) := by
        ring

/-- Unnormalized Walsh–Hadamard sum identity for a shifted bent function `x ↦ g(x + s)`. -/
theorem sum_signVal_shift_xor_eq {ι : Type*} [Fintype ι] [DecidableEq ι] {g : (ι → Bool) → Bool}
    (hg : IsBent g) (s α : ι → Bool) :
    ∑ x : ι → Bool, signVal (g (x + s) ^^ (x ⬝ᵥ α)) =
      (2 : ℝ) ^ ((Fintype.card ι : ℝ) / 2) * signVal ((s ⬝ᵥ α) ^^ bentDual g α) := by
  have h := walshCoeff_shift_eq hg s α
  unfold walshCoeff at h
  have hpow : (2 : ℝ) ^ (Fintype.card ι : ℝ) * (2 : ℝ) ^ (-(Fintype.card ι : ℝ)) = 1 := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2), add_neg_cancel, Real.rpow_zero]
  have hpow2 : (2 : ℝ) ^ (Fintype.card ι : ℝ) * (2 : ℝ) ^ (-(Fintype.card ι : ℝ) / 2) =
      (2 : ℝ) ^ ((Fintype.card ι : ℝ) / 2) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1; ring
  calc ∑ x : ι → Bool, signVal (g (x + s) ^^ (x ⬝ᵥ α))
      = (2 : ℝ) ^ (Fintype.card ι : ℝ) *
          ((2 : ℝ) ^ (-(Fintype.card ι : ℝ)) *
            ∑ x : ι → Bool, signVal (g (x + s) ^^ (x ⬝ᵥ α))) := by
        rw [← mul_assoc, hpow, one_mul]
    _ = (2 : ℝ) ^ (Fintype.card ι : ℝ) *
          ((2 : ℝ) ^ (-(Fintype.card ι : ℝ) / 2) *
            signVal ((s ⬝ᵥ α) ^^ bentDual g α)) := by rw [h]
    _ = (2 : ℝ) ^ ((Fintype.card ι : ℝ) / 2) * signVal ((s ⬝ᵥ α) ^^ bentDual g α) := by
        rw [← mul_assoc, hpow2]

/-- Reindexing a Boolean function along an equivalence preserves normalized Walsh–Hadamard
coefficients. -/
theorem walshCoeff_comp_equiv {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (e : κ ≃ ι) (g : (κ → Bool) → Bool) (α : ι → Bool) :
    walshCoeff (fun x => g (x ∘ e)) α = walshCoeff g (α ∘ e) := by
  unfold walshCoeff
  rw [Fintype.card_congr e]
  congr 1
  let eArr : (κ → Bool) ≃ (ι → Bool) := Equiv.arrowCongr e (Equiv.refl Bool)
  refine (Fintype.sum_equiv eArr _ _ fun x => ?_).symm
  have hcomp : eArr x ∘ e = x := by
    funext i; simp [eArr]
  have hdot : eArr x ⬝ᵥ α = x ⬝ᵥ (α ∘ e) := by
    unfold dotProduct
    rw [← Fintype.sum_equiv e _ _ fun _ => rfl]
    simp [eArr]
  dsimp only []
  rw [hcomp, hdot]

/-- Reindexing a Boolean function along an equivalence commutes with `bentDual`. -/
theorem bentDual_comp_equiv {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (e : κ ≃ ι) (g : (κ → Bool) → Bool) (α : ι → Bool) :
    bentDual (fun x => g (x ∘ e)) α = bentDual g (α ∘ e) := by
  classical
  unfold bentDual
  rw [walshCoeff_comp_equiv]

/-- **Maiorana–McFarland bent function**: for any permutation `π` of `𝔽₂^ι`, the Boolean function
`(u, w) ↦ u · π(w)` on `𝔽₂^ι × 𝔽₂^ι` (encoded on `ι ⊕ ι → Bool`). -/
@[expose] def maioranaMcFarland {ι : Type*} [Fintype ι]
    (π : Equiv.Perm (ι → Bool)) (x : (ι ⊕ ι) → Bool) : Bool :=
  (x ∘ Sum.inl) ⬝ᵥ π (x ∘ Sum.inr)

/-- Pointwise coordinate sum formula for `maioranaMcFarland`. -/
theorem maioranaMcFarland_eq_sum_and {ι : Type*} [Fintype ι]
    (π : Equiv.Perm (ι → Bool)) (x : (ι ⊕ ι) → Bool) :
    maioranaMcFarland π x = ∑ i : ι, (x (Sum.inl i) && π (x ∘ Sum.inr) i) := by
  simp only [maioranaMcFarland, dotProduct, Function.comp_apply, Bool.mul_eq_and]

/-- Orthogonality of inner-product signs on `𝔽₂^ι`: `∑_u (-1)^{u · v} = 2^{|ι|}` if `v = 0` and
`0` otherwise. -/
theorem sum_signVal_dotProduct {ι : Type*} [Fintype ι] [DecidableEq ι] (v : ι → Bool) :
    ∑ u : ι → Bool, signVal (u ⬝ᵥ v) = if v = 0 then (2 : ℝ) ^ Fintype.card ι else 0 := by
  by_cases hv : v = 0
  · subst hv
    simp [signVal]
  · simp only [hv, ↓reduceIte]
    have hex : ∃ i : ι, v i = true := by
      by_contra hall
      push Not at hall
      apply hv
      funext i
      cases hvi : v i
      · rfl
      · exact absurd hvi (hall i)
    obtain ⟨i, hi⟩ := hex
    let e : Equiv.Perm (ι → Bool) := Equiv.addRight (Pi.single i true)
    have hsum : ∑ u : ι → Bool, signVal (u ⬝ᵥ v) =
        ∑ u : ι → Bool, signVal (e u ⬝ᵥ v) := (Fintype.sum_equiv e _ _ fun _ => rfl).symm
    have hneg : ∀ u : ι → Bool, signVal (e u ⬝ᵥ v) = -signVal (u ⬝ᵥ v) := by
      intro u
      have hdot : e u ⬝ᵥ v = ((u ⬝ᵥ v) ^^ (Pi.single i true ⬝ᵥ v)) := by
        change (u + Pi.single i true) ⬝ᵥ v = _
        rw [add_dotProduct]; rfl
      have hsingle : (Pi.single i true : ι → Bool) ⬝ᵥ v = true := by
        unfold dotProduct
        rw [Finset.sum_eq_single i]
        · rw [Pi.single_eq_same, hi]; rfl
        · intro j _ hji
          rw [Pi.single_eq_of_ne hji]; rfl
        · intro h
          exact absurd (mem_univ i) h
      rw [hdot, hsingle, signVal_xor, signVal_true]
      ring
    simp_rw [hneg, Finset.sum_neg_distrib] at hsum
    linarith

/-- Explicit Walsh–Hadamard coefficient of a Maiorana–McFarland function. -/
theorem walshCoeff_maioranaMcFarland {ι : Type*} [Fintype ι] [DecidableEq ι]
    (π : Equiv.Perm (ι → Bool)) (γ : (ι ⊕ ι) → Bool) :
    walshCoeff (maioranaMcFarland π) γ =
      (2 : ℝ) ^ (-(Fintype.card (ι ⊕ ι) : ℝ) / 2) *
        signVal ((γ ∘ Sum.inr) ⬝ᵥ π.symm (γ ∘ Sum.inl)) := by
  unfold walshCoeff maioranaMcFarland
  let e : ((ι → Bool) × (ι → Bool)) ≃ ((ι ⊕ ι) → Bool) :=
    Equiv.sumArrowEquivProdArrow ι ι Bool |>.symm
  trans (2 : ℝ) ^ (-(Fintype.card (ι ⊕ ι) : ℝ)) *
      ∑ p : (ι → Bool) × (ι → Bool),
        signVal ((e p ∘ Sum.inl) ⬝ᵥ π (e p ∘ Sum.inr) ^^ (e p ⬝ᵥ γ))
  · congr 1
    exact (Fintype.sum_equiv e _ _ (fun _ => rfl)).symm
  rw [Fintype.sum_prod_type]
  have hcomp : ∀ (u w : ι → Bool),
      e (u, w) ∘ Sum.inl = u ∧ e (u, w) ∘ Sum.inr = w := fun u w => by
    constructor <;> funext i <;> rfl
  have hdot : ∀ (u w : ι → Bool),
      e (u, w) ⬝ᵥ γ = ((u ⬝ᵥ (γ ∘ Sum.inl)) ^^ (w ⬝ᵥ (γ ∘ Sum.inr))) := by
    intro u w
    unfold dotProduct
    rw [Fintype.sum_sum_type]
    rfl
  have hinner : ∀ w : ι → Bool,
      ∑ u : ι → Bool, signVal ((u ⬝ᵥ π w) ^^ ((u ⬝ᵥ (γ ∘ Sum.inl)) ^^ (w ⬝ᵥ (γ ∘ Sum.inr)))) =
        signVal (w ⬝ᵥ (γ ∘ Sum.inr)) *
          (if π w + γ ∘ Sum.inl = 0 then (2 : ℝ) ^ Fintype.card ι else 0) := by
    intro w
    have hrew : ∀ u : ι → Bool,
        signVal ((u ⬝ᵥ π w) ^^ ((u ⬝ᵥ (γ ∘ Sum.inl)) ^^ (w ⬝ᵥ (γ ∘ Sum.inr)))) =
          signVal (w ⬝ᵥ (γ ∘ Sum.inr)) * signVal (u ⬝ᵥ (π w + γ ∘ Sum.inl)) := by
      intro u
      have hadd : u ⬝ᵥ (π w + γ ∘ Sum.inl) = ((u ⬝ᵥ π w) ^^ (u ⬝ᵥ (γ ∘ Sum.inl))) := by
        rw [dotProduct_add]; rfl
      rw [hadd, ← Bool.xor_assoc, signVal_xor, signVal_xor, mul_comm]
    simp_rw [hrew, ← Finset.mul_sum, sum_signVal_dotProduct]
  have hrewrite : ∀ w : ι → Bool,
      (∑ u : ι → Bool, signVal ((e (u, w) ∘ Sum.inl) ⬝ᵥ π (e (u, w) ∘ Sum.inr) ^^
        (e (u, w) ⬝ᵥ γ))) =
        signVal (w ⬝ᵥ (γ ∘ Sum.inr)) *
          (if π w + γ ∘ Sum.inl = 0 then (2 : ℝ) ^ Fintype.card ι else 0) := by
    intro w
    trans ∑ u : ι → Bool,
        signVal ((u ⬝ᵥ π w) ^^ ((u ⬝ᵥ (γ ∘ Sum.inl)) ^^ (w ⬝ᵥ (γ ∘ Sum.inr))))
    · refine Finset.sum_congr rfl fun u _ => ?_
      rw [(hcomp u w).1, (hcomp u w).2, hdot u w]
    · exact hinner w
  rw [Finset.sum_comm]
  simp_rw [hrewrite]
  have hzero : ∀ w : ι → Bool, (π w + γ ∘ Sum.inl = 0) ↔ w = π.symm (γ ∘ Sum.inl) := by
    intro w
    constructor
    · intro h
      have h' : π w = γ ∘ Sum.inl := by
        funext i
        have hi := congrFun h i
        change (π w i ^^ (γ ∘ Sum.inl) i) = false at hi
        cases h1 : π w i <;> cases h2 : (γ ∘ Sum.inl) i <;> simp_all
      exact (Equiv.eq_symm_apply π).mpr h'
    · intro h
      subst h
      rw [Equiv.apply_symm_apply, Cslib.BitString.add_self]
  simp_rw [hzero]
  rw [Finset.sum_eq_single (π.symm (γ ∘ Sum.inl))]
  · simp only [↓reduceIte, Fintype.card_sum, Nat.cast_add]
    have hdot_comm : (π.symm (γ ∘ Sum.inl)) ⬝ᵥ (γ ∘ Sum.inr) =
        (γ ∘ Sum.inr) ⬝ᵥ π.symm (γ ∘ Sum.inl) := dotProduct_comm _ _
    rw [hdot_comm]
    have hpow : (2 : ℝ) ^ (-((Fintype.card ι : ℝ) + (Fintype.card ι : ℝ))) *
        ((2 : ℝ) ^ Fintype.card ι) =
          (2 : ℝ) ^ (-((Fintype.card ι : ℝ) + (Fintype.card ι : ℝ)) / 2) := by
      rw [← Real.rpow_natCast (2 : ℝ) (Fintype.card ι),
        ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 1; ring
    calc (2 : ℝ) ^ (-((Fintype.card ι : ℝ) + (Fintype.card ι : ℝ))) *
          (signVal ((γ ∘ Sum.inr) ⬝ᵥ π.symm (γ ∘ Sum.inl)) * (2 : ℝ) ^ Fintype.card ι)
        = ((2 : ℝ) ^ (-((Fintype.card ι : ℝ) + (Fintype.card ι : ℝ))) * (2 : ℝ) ^ Fintype.card ι) *
            signVal ((γ ∘ Sum.inr) ⬝ᵥ π.symm (γ ∘ Sum.inl)) := by ring
      _ = (2 : ℝ) ^ (-((Fintype.card ι : ℝ) + (Fintype.card ι : ℝ)) / 2) *
            signVal ((γ ∘ Sum.inr) ⬝ᵥ π.symm (γ ∘ Sum.inl)) := by rw [hpow]
  · intro w _ hne; simp [hne]
  · intro h; exact absurd (mem_univ _) h

/-- **Every Maiorana–McFarland function is bent.** -/
theorem isBent_maioranaMcFarland {ι : Type*} [Fintype ι] [DecidableEq ι]
    (π : Equiv.Perm (ι → Bool)) : IsBent (maioranaMcFarland π) := by
  intro γ
  rw [walshCoeff_maioranaMcFarland, abs_mul, abs_signVal, mul_one,
    abs_of_pos (by positivity)]

/-- **Dual of a Maiorana–McFarland bent function**: `g̃(α, β) = β · π⁻¹(α)`. -/
theorem bentDual_maioranaMcFarland {ι : Type*} [Fintype ι] [DecidableEq ι]
    (π : Equiv.Perm (ι → Bool)) (γ : (ι ⊕ ι) → Bool) :
    bentDual (maioranaMcFarland π) γ = (γ ∘ Sum.inr) ⬝ᵥ π.symm (γ ∘ Sum.inl) := by
  classical
  unfold bentDual
  rw [walshCoeff_maioranaMcFarland]
  cases hb : (γ ∘ Sum.inr) ⬝ᵥ π.symm (γ ∘ Sum.inl) <;> simp [signVal]

end BooleanAnalysis

end CslibFrontier
