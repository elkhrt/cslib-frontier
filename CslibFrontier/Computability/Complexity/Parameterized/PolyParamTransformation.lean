/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Papers Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Parameterized.CrossComposition
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Bounds
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Degree.Bounds
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Bounds
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.OPrimitives
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.ResourceFacts
import CslibFrontier.Foundations.Data.Nat.PolynomialBound.Closure

/-!
# Polynomial Parameter Transformations

A *polynomial parameter transformation* from a parameterized problem `(A, κA)` to `(B, κB)`

(`Cslib.Complexity.IsPolyParamTransformation`) is a polynomial-time many-one reduction `f` from `A`
to `B` such that `κB (f a) ≤ g (κA a)` for a polynomially bounded function `g`
(`Cslib.Complexity.PolyParamReducible`).

Polynomial parameter transformations transfer polynomial compressions and cross-composition lower
bounds:

* Composing a polynomial parameter transformation from `(A, κA)` to `(B, κB)` with a compression of
  `(B, κB)` yields a compression of `(A, κA)` with polynomially bounded size bound
  (`Cslib.Complexity.PolyParamReducible.hasPolyCompression`,
). Consequently, if `(A, κA)` has no polynomial compression, then
  `(B, κB)` has neither a polynomial compression nor a polynomial kernel.
* Composing an OR-cross-composition into `(Q₁, κ₁)` with a polynomial parameter transformation into
  `(Q₂, κ₂)` yields an OR-cross-composition into `(Q₂, κ₂)`
  (`Cslib.Complexity.ORCrossComposes.trans_polyParamReducible`).

## Main definitions

* `Cslib.Complexity.IsPolyParamTransformation`, `Cslib.Complexity.PolyParamReducible`.

## Main results

* `Cslib.Complexity.PolyParamReducible.fptReducible`: every polynomial parameter transformation is
  an fpt-reduction.
* `Cslib.Complexity.PolyParamReducible.refl`, `Cslib.Complexity.PolyParamReducible.trans`:
  polynomial parameter reducibility is a preorder.
* `Cslib.Complexity.PolyParamReducible.hasPolyCompression`: **Bodlaender–Thomassé–Yeo**
: polynomial compressions pull back along polynomial
  parameter transformations.
* `Cslib.Complexity.ORCrossComposes.trans_polyParamReducible`: OR-cross-compositions compose with
  polynomial parameter transformations.
* `Cslib.Complexity.not_hasPolyCompression_of_polyParamReducible`,
  `Cslib.Complexity.not_hasPolyKernel_of_polyParamReducible`: contrapositive kernelization lower
  bounds.
-/

public section

namespace Cslib.Complexity

open Cslib Turing.MultiTapeTM ComputableInPolyTime

section Defs

variable {α β : Type}

/-- `f` is a *polynomial parameter transformation* from `(A, κA)` to `(B, κB)` with parameter bound
`g`: it is computable in
polynomial time, preserves membership (`a ∈ A ↔ f a ∈ B`), and satisfies `κB (f a) ≤ g (κA a)`.
-/
structure IsPolyParamTransformation (encA : α ↪ List Bool) (encB : β ↪ List Bool)
    (κA : α → ℕ) (κB : β → ℕ) (A : Set α) (B : Set β) (f : α → β) (g : ℕ → ℕ) : Prop where
  /-- The reduction is computable in polynomial time. -/
  polyTime : ComputableInPolyTime f encA encB
  /-- The reduction preserves problem membership. -/
  mem_iff : ∀ a, a ∈ A ↔ f a ∈ B
  /-- The target parameter is bounded in terms of the source parameter. -/
  parameter_le : ∀ a, κB (f a) ≤ g (κA a)

/-- `(A, κA)` reduces to `(B, κB)` by a *polynomial parameter transformation*
: there exists a
polynomial parameter transformation with a polynomially bounded parameter bound `g`.
-/
@[expose] def PolyParamReducible (encA : α ↪ List Bool) (encB : β ↪ List Bool)
    (κA : α → ℕ) (κB : β → ℕ) (A : Set α) (B : Set β) : Prop :=
  ∃ (f : α → β) (g : ℕ → ℕ), PolynomiallyBounded g ∧
    IsPolyParamTransformation encA encB κA κB A B f g

end Defs

variable {α β γ δ : Type}
  {encA : α ↪ List Bool} {encB : β ↪ List Bool} {encC : γ ↪ List Bool}
  {κA : α → ℕ} {κB : β → ℕ} {κC : γ → ℕ}
  {A : Set α} {B : Set β} {C : Set γ}

/-- Every polynomial parameter transformation is a classical polynomial-time many-one reduction. -/
theorem IsPolyParamTransformation.polyTimeReducible {f : α → β} {g : ℕ → ℕ}
    (hf : IsPolyParamTransformation encA encB κA κB A B f g) :
    PolyTimeReducible encA encB A B :=
  ⟨f, hf.polyTime, hf.mem_iff⟩

/-- Every polynomial parameter transformation is an fpt-reduction. -/
theorem IsPolyParamTransformation.fptReducible {f : α → β} {g : ℕ → ℕ}
    (hf : IsPolyParamTransformation encA encB κA κB A B f g) :
    FPTReducible encA encB κA κB A B :=
  FPTReducible.of_computableInPolyTime hf.polyTime hf.parameter_le hf.mem_iff

/-- Polynomial parameter reducibility implies polynomial-time many-one reducibility. -/
theorem PolyParamReducible.polyTimeReducible
    (h : PolyParamReducible encA encB κA κB A B) :
    PolyTimeReducible encA encB A B :=
  let ⟨_, _, _, hf⟩ := h
  hf.polyTimeReducible

/-- Polynomial parameter reducibility implies fpt-reducibility. -/
theorem PolyParamReducible.fptReducible
    (h : PolyParamReducible encA encB κA κB A B) :
    FPTReducible encA encB κA κB A B :=
  let ⟨_, _, _, hf⟩ := h
  hf.fptReducible

/-- Polynomial parameter reducibility is reflexive. -/
theorem PolyParamReducible.refl (encA : α ↪ List Bool) (κA : α → ℕ) (A : Set α) :
    PolyParamReducible encA encA κA κA A A :=
  ⟨id, id, by fun_prop, ⟨id', fun _ => Iff.rfl, fun _ => le_rfl⟩⟩

/-- Polynomial parameter reducibility is transitive. -/
theorem PolyParamReducible.trans
    (hab : PolyParamReducible encA encB κA κB A B)
    (hbc : PolyParamReducible encB encC κB κC B C) :
    PolyParamReducible encA encC κA κC A C := by
  obtain ⟨f₁, g₁, hg₁, hf₁⟩ := hab
  obtain ⟨f₂, g₂, hg₂, hf₂⟩ := hbc
  obtain ⟨c₁, d₁, hc₁⟩ := polynomiallyBounded_iff_le.mp hg₁
  obtain ⟨c₂, d₂, hc₂⟩ := polynomiallyBounded_iff_le.mp hg₂
  refine ⟨f₂ ∘ f₁, fun k => c₂ * (c₁ * (k + 1) ^ d₁ + 1) ^ d₂, by fun_prop,
    ⟨hf₂.polyTime.comp hf₁.polyTime, fun a => (hf₁.mem_iff a).trans (hf₂.mem_iff (f₁ a)),
      fun a => ?_⟩⟩
  calc κC (f₂ (f₁ a))
      ≤ g₂ (κB (f₁ a)) := hf₂.parameter_le (f₁ a)
    _ ≤ c₂ * (κB (f₁ a) + 1) ^ d₂ := hc₂ _
    _ ≤ c₂ * (g₁ (κA a) + 1) ^ d₂ :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right (hf₁.parameter_le a) 1) _)
    _ ≤ c₂ * (c₁ * (κA a + 1) ^ d₁ + 1) ^ d₂ :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right (hc₁ _) 1) _)

/-- **Composing a polynomial parameter transformation with a compression.** Let `f` be a polynomial
parameter transformation from `(A, κA)` to `(B, κB)` with polynomially bounded `g`, and let `K` be
a compression of `(B, κB)` into `C` with polynomially bounded size bound `h`. Then `K ∘ f` is a
compression of `(A, κA)` into `C` with a polynomially bounded size bound. -/
theorem IsPolyParamTransformation.exists_isCompression_comp {f : α → β} {g : ℕ → ℕ}
    (hg : PolynomiallyBounded g) (hf : IsPolyParamTransformation encA encB κA κB A B f g)
    {K : β → γ} {h : ℕ → ℕ} (hh : PolynomiallyBounded h)
    (hK : IsCompression encB κB B encC C K h) :
    ∃ H : ℕ → ℕ, PolynomiallyBounded H ∧ IsCompression encA κA A encC C (K ∘ f) H := by
  obtain ⟨T, hT, hK'⟩ := hK.polyTime
  have hKO : ComputableInO K encB encC (fun b => T ((encB b).length + κB b))
      (fun b => T ((encB b).length + κB b)) := by
    obtain ⟨c, hc⟩ := hK'.exists_space_linear
    exact .of_bounds hc (c + 1) (fun b => by nlinarith) (fun b => by nlinarith)
      fun b => (hK'.length_le b).trans (by nlinarith)
  obtain ⟨df, ef, hfd⟩ := hf.polyTime.exists_degree
  obtain ⟨cO, hKf_ts, _⟩ := hKO.comp hfd.inO
  obtain ⟨cT, dT, hcT⟩ := polynomiallyBounded_iff_le.mp hT
  obtain ⟨cf, df', hcf⟩ := hf.polyTime.polyBounded_length.exists_le
  obtain ⟨cg, dg, hcg⟩ := polynomiallyBounded_iff_le.mp hg
  obtain ⟨ch, dh, hch⟩ := polynomiallyBounded_iff_le.mp hh
  let T_comp : ℕ → ℕ := fun m =>
    cO * ((m + 1) ^ df + (m + 1) ^ ef +
      cT * (cf * (m + 1) ^ df' + cg * (m + 1) ^ dg + 1) ^ dT + 1)
  let H : ℕ → ℕ := fun k => ch * (cg * (k + 1) ^ dg + 1) ^ dh
  refine ⟨H, by dsimp [H]; fun_prop,
    ⟨⟨T_comp, by dsimp [T_comp]; fun_prop, hKf_ts.mono (fun a => ?_) (fun a => ?_)⟩,
      fun a => (hK.mem_iff (f a)).trans (hf.mem_iff a).symm, fun a => ?_⟩⟩
  · set m := (encA a).length + κA a
    have hlenB : (encB (f a)).length ≤ cf * (m + 1) ^ df' :=
      (hcf a).trans (Nat.mul_le_mul_left cf (Nat.pow_le_pow_left (by omega) df'))
    have hparB : κB (f a) ≤ cg * (m + 1) ^ dg :=
      (hf.parameter_le a).trans
        ((hcg _).trans (Nat.mul_le_mul_left cg (Nat.pow_le_pow_left (by omega) dg)))
    have hTB : T ((encB (f a)).length + κB (f a)) ≤
        cT * (cf * (m + 1) ^ df' + cg * (m + 1) ^ dg + 1) ^ dT :=
      (hcT _).trans (Nat.mul_le_mul_left cT (Nat.pow_le_pow_left (by omega) dT))
    have hdf : ((encA a).length + 1) ^ df ≤ (m + 1) ^ df := Nat.pow_le_pow_left (by omega) df
    have hef : ((encA a).length + 1) ^ ef ≤ (m + 1) ^ ef := Nat.pow_le_pow_left (by omega) ef
    dsimp only [T_comp]
    exact Nat.mul_le_mul_left cO (by omega)
  · set m := (encA a).length + κA a
    have hlenB : (encB (f a)).length ≤ cf * (m + 1) ^ df' :=
      (hcf a).trans (Nat.mul_le_mul_left cf (Nat.pow_le_pow_left (by omega) df'))
    have hparB : κB (f a) ≤ cg * (m + 1) ^ dg :=
      (hf.parameter_le a).trans
        ((hcg _).trans (Nat.mul_le_mul_left cg (Nat.pow_le_pow_left (by omega) dg)))
    have hTB : T ((encB (f a)).length + κB (f a)) ≤
        cT * (cf * (m + 1) ^ df' + cg * (m + 1) ^ dg + 1) ^ dT :=
      (hcT _).trans (Nat.mul_le_mul_left cT (Nat.pow_le_pow_left (by omega) dT))
    have hdf : ((encA a).length + 1) ^ df ≤ (m + 1) ^ df := Nat.pow_le_pow_left (by omega) df
    have hef : ((encA a).length + 1) ^ ef ≤ (m + 1) ^ ef := Nat.pow_le_pow_left (by omega) ef
    dsimp only [T_comp]
    exact Nat.mul_le_mul_left cO (by omega)
  · dsimp only [H, Function.comp_apply]
    calc (encC (K (f a))).length
        ≤ h (κB (f a)) := hK.length_le (f a)
      _ ≤ ch * (κB (f a) + 1) ^ dh := hch _
      _ ≤ ch * (g (κA a) + 1) ^ dh :=
          Nat.mul_le_mul_left ch
            (Nat.pow_le_pow_left (Nat.add_le_add_right (hf.parameter_le a) 1) _)
      _ ≤ ch * (cg * (κA a + 1) ^ dg + 1) ^ dh :=
          Nat.mul_le_mul_left ch (Nat.pow_le_pow_left (Nat.add_le_add_right (hcg _) 1) _)

/-- **Bodlaender–Thomassé–Yeo**:
if `(A, κA)` reduces to `(B, κB)` by a polynomial parameter transformation and `(B, κB)` has a
polynomial compression, then `(A, κA)` has a polynomial compression.
-/
theorem PolyParamReducible.hasPolyCompression
    (hab : PolyParamReducible encA encB κA κB A B)
    (hB : HasPolyCompression encB κB B) :
    HasPolyCompression encA κA A := by
  obtain ⟨f, g, hg, hf⟩ := hab
  obtain ⟨Z, K, h, hh, hK⟩ := hB
  obtain ⟨H, hH, hcomp⟩ := hf.exists_isCompression_comp hg hh hK
  exact hcomp.hasPolyCompression hH

/-- Contrapositive compression lower bound along a polynomial parameter transformation. -/
theorem not_hasPolyCompression_of_polyParamReducible
    (hab : PolyParamReducible encA encB κA κB A B)
    (hA : ¬ HasPolyCompression encA κA A) :
    ¬ HasPolyCompression encB κB B :=
  fun hB => hA (hab.hasPolyCompression hB)

/-- Contrapositive polynomial-kernel lower bound along a polynomial parameter transformation
.
-/
theorem not_hasPolyKernel_of_polyParamReducible
    (hab : PolyParamReducible encA encB κA κB A B)
    (hA : ¬ HasPolyCompression encA κA A) :
    ¬ HasPolyKernel encB κB B :=
  fun hB => hA (hab.hasPolyCompression hB.hasPolyCompression)

/-- **Composing an OR-cross-composition with a polynomial parameter transformation.** If `A`
OR-cross-composes into `(B, κB)` and `(B, κB)` reduces to `(C, κC)` by a polynomial parameter
transformation, then `A` OR-cross-composes into `(C, κC)`. -/
theorem ORCrossComposes.trans_polyParamReducible
    (hAB : ORCrossComposes encA A encB κB B)
    (hBC : PolyParamReducible encB encC κB κC B C) :
    ORCrossComposes encA A encC κC C := by
  obtain ⟨r, F, g₁, hr, hg₁, hF⟩ := hAB
  obtain ⟨f, g₂, hg₂, hf⟩ := hBC
  obtain ⟨c₁, d₁, hc₁⟩ := polynomiallyBounded_iff_le.mp hg₁
  obtain ⟨c₂, d₂, hc₂⟩ := polynomiallyBounded_iff_le.mp hg₂
  refine ⟨r, f ∘ F, fun m => c₂ * (c₁ * (m + 1) ^ d₁ + 1) ^ d₂, hr, by fun_prop,
    ⟨hf.polyTime.comp hF.polyTime,
      fun l hl hrel => (hf.mem_iff (F l)).symm.trans (hF.mem_iff l hl hrel),
      fun n l hl hrel hlen => ?_⟩⟩
  calc κC (f (F l))
      ≤ g₂ (κB (F l)) := hf.parameter_le (F l)
    _ ≤ c₂ * (κB (F l) + 1) ^ d₂ := hc₂ _
    _ ≤ c₂ * (g₁ (n + Nat.log 2 l.length) + 1) ^ d₂ :=
        Nat.mul_le_mul_left c₂
          (Nat.pow_le_pow_left (Nat.add_le_add_right (hF.parameter_le n l hl hrel hlen) 1) _)
    _ ≤ c₂ * (c₁ * (n + Nat.log 2 l.length + 1) ^ d₁ + 1) ^ d₂ :=
        Nat.mul_le_mul_left c₂
          (Nat.pow_le_pow_left (Nat.add_le_add_right (hc₁ _) 1) _)

end Cslib.Complexity
