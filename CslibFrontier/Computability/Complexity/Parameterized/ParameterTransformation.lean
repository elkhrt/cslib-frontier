/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FormalPapers Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Parameterized.Compression
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Bounds
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Degree.Bounds
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Length
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.OPrimitives
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.ResourceFacts
import CslibFrontier.Foundations.Data.Nat.PolynomialBound.Closure

/-!
# Polynomial parameter transformations and quantitative compression lower bounds

A *polynomial parameter transformation* (`CslibFrontier.Complexity.IsPolyParamTransformation`) from
a parameterized problem `(A, κA)` to a parameterized problem `(B, κB)` maps each instance `a`, in
time and space polynomial in `|encA a| + κA a`, to an instance `f a` with `f a ∈ B ↔ a ∈ A` and
`κB (f a) ≤ p (κA a)` for a polynomially bounded function `p`. When `p` is affine
(`p k = c₁ * k + c₀`), `f` is a *linear parameter transformation*
(`CslibFrontier.Complexity.IsLinearParamTransformation`).

Composing a polynomial parameter transformation with a compression
(`Cslib.Complexity.IsCompression`) transfers polynomial compressions and polynomial kernelization
lower bounds contrapositively (`CslibFrontier.Complexity.PolyParamReducible.hasPolyCompression`,
`CslibFrontier.Complexity.PolyParamReducible.not_hasPolyKernel`). Furthermore, defining quantitative
`O(k ^ e)` compression bounds (`CslibFrontier.Complexity.HasCompressionOfSizeO`), degree-`d` and
linear parameter transformations transfer fine-grained `O(k ^ (b - ε))` compression lower bounds
(such as the Dell–van Melkebeek `b`-Hitting Set sparsification lower bound).

## Main definitions

* `CslibFrontier.Complexity.IsPolyParamTransformation`,
  `CslibFrontier.Complexity.PolyParamReducible`: polynomial parameter transformations.
* `CslibFrontier.Complexity.IsLinearParamTransformation`,
  `CslibFrontier.Complexity.LinearParamReducible`: linear (affine) parameter transformations.
* `CslibFrontier.Complexity.HasCompressionOfSizeO`: existence of a compression with output
  bit-length `h(k) = O(k ^ e)` as `k → ∞`.
* `CslibFrontier.Complexity.HittingSetInstance`,
  `CslibFrontier.Complexity.encHittingSetInstance`,
  `CslibFrontier.Complexity.bHittingSet`: `b`-Hitting Set parameterized by universe size `n`.

## Main results

* `CslibFrontier.Complexity.IsPolyParamTransformation.comp_compression`: left-composition of a
  compression with a polynomial parameter transformation.
* `CslibFrontier.Complexity.IsPolyParamTransformation.trans`,
  `CslibFrontier.Complexity.PolyParamReducible.trans`: transitivity of polynomial parameter
  transformations.
* `CslibFrontier.Complexity.PolyParamReducible.hasPolyCompression`,
  `CslibFrontier.Complexity.PolyParamReducible.not_hasPolyKernel`: transfer of polynomial
  compressions and kernelization lower bounds.
* `CslibFrontier.Complexity.IsPolyParamTransformation.hasCompressionOfSizeO_of_pow`,
  `CslibFrontier.Complexity.IsPolyParamTransformation.not_hasCompressionOfSizeO_sub_of_pow`:
  quantitative `O(k ^ (d * e))` compression and `O(k ^ (b - ε))` incompressibility transfer along
  degree-`d` parameter transformations.
* `CslibFrontier.Complexity.LinearParamReducible.not_hasCompressionOfSizeO_sub`: quantitative
  `O(k ^ (b - ε))` incompressibility transfer along linear parameter transformations.
-/

public section

namespace CslibFrontier.Complexity

open Cslib Cslib.Complexity Turing.MultiTapeTM Filter Asymptotics

section ParameterTransformations

variable {α β γ : Type}

/-- A map `f : α → β` is a *polynomial parameter transformation* from `(A, κA)` to `(B, κB)` with
parameter growth `p : ℕ → ℕ` if `p` is polynomially bounded, `f` is computable in time and space
polynomial in `(encA a).length + κA a`, `f a ∈ B ↔ a ∈ A`, and `κB (f a) ≤ p (κA a)`. -/
structure IsPolyParamTransformation (encA : α ↪ List Bool) (κA : α → ℕ) (A : Set α)
    (encB : β ↪ List Bool) (κB : β → ℕ) (B : Set β) (f : α → β) (p : ℕ → ℕ) : Prop where
  /-- The parameter bound is polynomially bounded. -/
  polyParam : PolynomiallyBounded p
  /-- The transformation runs in time and space polynomial in `|encA a| + κA a`. -/
  polyTime : ∃ T : ℕ → ℕ, PolynomiallyBounded T ∧
    ComputableInTimeAndSpace f encA encB (fun a ↦ T ((encA a).length + κA a))
      (fun a ↦ T ((encA a).length + κA a))
  /-- The transformation preserves yes-instances. -/
  mem_iff : ∀ a, f a ∈ B ↔ a ∈ A
  /-- The output parameter is bounded by `p (κA a)`. -/
  parameter_le : ∀ a, κB (f a) ≤ p (κA a)

/-- Existence of a polynomial parameter transformation from `(A, κA)` to `(B, κB)`. -/
def PolyParamReducible (encA : α ↪ List Bool) (κA : α → ℕ) (A : Set α)
    (encB : β ↪ List Bool) (κB : β → ℕ) (B : Set β) : Prop :=
  ∃ (f : α → β) (p : ℕ → ℕ), IsPolyParamTransformation encA κA A encB κB B f p

/-- Construct an `IsPolyParamTransformation` from an ordinary `ComputableInPolyTime` reduction
(running in time polynomial in `|encA a|` alone, hence in `|encA a| + κA a`). -/
theorem IsPolyParamTransformation.of_computableInPolyTime {encA : α ↪ List Bool} {κA : α → ℕ}
    {A : Set α} {encB : β ↪ List Bool} {κB : β → ℕ} {B : Set β} {f : α → β} {p : ℕ → ℕ}
    (hp : PolynomiallyBounded p) (hf : ComputableInPolyTime f encA encB)
    (hmem : ∀ a, f a ∈ B ↔ a ∈ A) (hparam : ∀ a, κB (f a) ≤ p (κA a)) :
    IsPolyParamTransformation encA κA A encB κB B f p := by
  obtain ⟨t, s, ht, hs, hf'⟩ := hf
  obtain ⟨c, d, hcd⟩ := polynomiallyBounded_iff_le.mp (ht.add hs)
  have hle (a : α) : t (encA a).length + s (encA a).length ≤
      c * ((encA a).length + κA a + 1) ^ d :=
    (hcd (encA a).length).trans (Nat.mul_le_mul_left c (Nat.pow_le_pow_left (by omega) d))
  refine ⟨hp, ⟨fun n ↦ c * (n + 1) ^ d, by fun_prop, hf'.mono (fun a ↦ ?_) (fun a ↦ ?_)⟩,
    hmem, hparam⟩
  · have := hle a; dsimp only; omega
  · have := hle a; dsimp only; omega

/-- A map `f : α → β` is a *linear parameter transformation* from `(A, κA)` to `(B, κB)` with
constants `(c₁, c₀)` if `f` runs in time and space polynomial in `|encA a| + κA a`, preserves
membership, and satisfies `κB (f a) ≤ c₁ * κA a + c₀`. -/
structure IsLinearParamTransformation (encA : α ↪ List Bool) (κA : α → ℕ) (A : Set α)
    (encB : β ↪ List Bool) (κB : β → ℕ) (B : Set β) (f : α → β) (c₁ c₀ : ℕ) : Prop where
  /-- The transformation runs in time and space polynomial in `|encA a| + κA a`. -/
  polyTime : ∃ T : ℕ → ℕ, PolynomiallyBounded T ∧
    ComputableInTimeAndSpace f encA encB (fun a ↦ T ((encA a).length + κA a))
      (fun a ↦ T ((encA a).length + κA a))
  /-- The transformation preserves yes-instances. -/
  mem_iff : ∀ a, f a ∈ B ↔ a ∈ A
  /-- The output parameter is at most `c₁ * κA a + c₀`. -/
  parameter_le : ∀ a, κB (f a) ≤ c₁ * κA a + c₀

/-- Existence of a linear parameter transformation from `(A, κA)` to `(B, κB)`. -/
def LinearParamReducible (encA : α ↪ List Bool) (κA : α → ℕ) (A : Set α)
    (encB : β ↪ List Bool) (κB : β → ℕ) (B : Set β) : Prop :=
  ∃ (f : α → β) (c₁ c₀ : ℕ), IsLinearParamTransformation encA κA A encB κB B f c₁ c₀

/-- Every linear parameter transformation is a polynomial parameter transformation. -/
theorem IsLinearParamTransformation.isPolyParamTransformation {encA : α ↪ List Bool}
    {κA : α → ℕ} {A : Set α} {encB : β ↪ List Bool} {κB : β → ℕ} {B : Set β} {f : α → β}
    {c₁ c₀ : ℕ} (hf : IsLinearParamTransformation encA κA A encB κB B f c₁ c₀) :
    IsPolyParamTransformation encA κA A encB κB B f (fun k ↦ c₁ * k + c₀) :=
  ⟨by fun_prop, hf.polyTime, hf.mem_iff, hf.parameter_le⟩

/-- Construct an `IsLinearParamTransformation` from an ordinary `ComputableInPolyTime` reduction. -/
theorem IsLinearParamTransformation.of_computableInPolyTime {encA : α ↪ List Bool} {κA : α → ℕ}
    {A : Set α} {encB : β ↪ List Bool} {κB : β → ℕ} {B : Set β} {f : α → β} {c₁ c₀ : ℕ}
    (hf : ComputableInPolyTime f encA encB) (hmem : ∀ a, f a ∈ B ↔ a ∈ A)
    (hparam : ∀ a, κB (f a) ≤ c₁ * κA a + c₀) :
    IsLinearParamTransformation encA κA A encB κB B f c₁ c₀ :=
  let h := IsPolyParamTransformation.of_computableInPolyTime
    (p := fun k ↦ c₁ * k + c₀) (by fun_prop) hf hmem hparam
  ⟨h.polyTime, h.mem_iff, h.parameter_le⟩

/-- Every linear parameter transformation witnesses `LinearParamReducible`. -/
theorem IsLinearParamTransformation.linearParamReducible {encA : α ↪ List Bool}
    {κA : α → ℕ} {A : Set α} {encB : β ↪ List Bool} {κB : β → ℕ} {B : Set β} {f : α → β}
    {c₁ c₀ : ℕ} (hf : IsLinearParamTransformation encA κA A encB κB B f c₁ c₀) :
    LinearParamReducible encA κA A encB κB B :=
  ⟨f, c₁, c₀, hf⟩

/-- Every linear parameter reduction is a polynomial parameter reduction. -/
theorem LinearParamReducible.polyParamReducible {encA : α ↪ List Bool} {κA : α → ℕ} {A : Set α}
    {encB : β ↪ List Bool} {κB : β → ℕ} {B : Set β}
    (h : LinearParamReducible encA κA A encB κB B) :
    PolyParamReducible encA κA A encB κB B :=
  let ⟨f, c₁, c₀, hf⟩ := h
  ⟨f, fun k ↦ c₁ * k + c₀, hf.isPolyParamTransformation⟩

/-- Reflexivity of `LinearParamReducible`. -/
theorem LinearParamReducible.refl (encA : α ↪ List Bool) (κA : α → ℕ) (A : Set α) :
    LinearParamReducible encA κA A encA κA A :=
  ⟨fun a ↦ a, 1, 0, .of_computableInPolyTime (by fun_prop) (fun _ ↦ Iff.rfl) (fun _ ↦ by omega)⟩

private theorem polyTimeWithParam_comp {encA : α ↪ List Bool} {κA : α → ℕ}
    {encB : β ↪ List Bool} {κB : β → ℕ} {encC : γ ↪ List Bool}
    {f : α → β} {g : β → γ} {p : ℕ → ℕ} (hp : PolynomiallyBounded p)
    (hf : ∃ T : ℕ → ℕ, PolynomiallyBounded T ∧
      ComputableInTimeAndSpace f encA encB (fun a ↦ T ((encA a).length + κA a))
        (fun a ↦ T ((encA a).length + κA a)))
    (hg : ∃ T : ℕ → ℕ, PolynomiallyBounded T ∧
      ComputableInTimeAndSpace g encB encC (fun b ↦ T ((encB b).length + κB b))
        (fun b ↦ T ((encB b).length + κB b)))
    (hparam : ∀ a, κB (f a) ≤ p (κA a)) :
    ∃ T : ℕ → ℕ, PolynomiallyBounded T ∧
      ComputableInTimeAndSpace (fun a ↦ g (f a)) encA encC
        (fun a ↦ T ((encA a).length + κA a)) (fun a ↦ T ((encA a).length + κA a)) := by
  obtain ⟨Tf, hTf, hfm⟩ := hf
  obtain ⟨Tg, hTg, hgm⟩ := hg
  obtain ⟨cf, df, hcfd⟩ := polynomiallyBounded_iff_le.mp hTf
  obtain ⟨cg, dg, hcgd⟩ := polynomiallyBounded_iff_le.mp hTg
  obtain ⟨cp, dp, hcpd⟩ := polynomiallyBounded_iff_le.mp hp
  have hfO : ComputableInO f encA encB
      (fun a ↦ cf * ((encA a).length + κA a + 1) ^ df)
      (fun a ↦ cf * ((encA a).length + κA a + 1) ^ df) :=
    .of_bounds hfm 1
      (fun a ↦ (hcfd _).trans (by omega))
      (fun a ↦ (hcfd _).trans (by omega))
      (fun a ↦ (hfm.length_le a).trans ((hcfd _).trans (by omega)))
  have hgO : ComputableInO g encB encC
      (fun b ↦ cg * ((encB b).length + κB b + 1) ^ dg)
      (fun b ↦ cg * ((encB b).length + κB b + 1) ^ dg) :=
    .of_bounds hgm 1
      (fun b ↦ (hcgd _).trans (by omega))
      (fun b ↦ (hcgd _).trans (by omega))
      (fun b ↦ (hgm.length_le b).trans ((hcgd _).trans (by omega)))
  obtain ⟨c₀, hts, _⟩ := hgO.comp hfO
  let M : ℕ → ℕ := fun n ↦ cf * (n + 1) ^ df + cp * (n + 1) ^ dp
  have hM_le (a : α) : (encB (f a)).length + κB (f a) ≤ M ((encA a).length + κA a) :=
    Nat.add_le_add ((hfm.length_le a).trans (hcfd _))
      ((hparam a).trans ((hcpd (κA a)).trans
        (Nat.mul_le_mul_left cp (Nat.pow_le_pow_left (by omega) dp))))
  let Bnd : ℕ → ℕ := fun n ↦ c₀ * (cf * (n + 1) ^ df + cg * (M n + 1) ^ dg + 1)
  have hBnd_poly : PolynomiallyBounded Bnd := by dsimp only [Bnd, M]; fun_prop
  have hle_bnd (a : α) :
      c₀ * (cf * ((encA a).length + κA a + 1) ^ df +
        cg * ((encB (f a)).length + κB (f a) + 1) ^ dg + 1) ≤
      Bnd ((encA a).length + κA a) := by
    have hpow := Nat.pow_le_pow_left (Nat.succ_le_succ (hM_le a)) dg
    exact Nat.mul_le_mul_left c₀
      (Nat.succ_le_succ (Nat.add_le_add_left (Nat.mul_le_mul_left cg hpow) _))
  exact ⟨Bnd, hBnd_poly, hts.mono hle_bnd hle_bnd⟩

/-- Upper-envelope `prefixMax h n = max_{j ≤ n} h j`, monotone in `n` and dominating `h`. -/
def prefixMax (h : ℕ → ℕ) (n : ℕ) : ℕ :=
  (Finset.range (n + 1)).sup h

/-- For `j ≤ n`, `h j ≤ prefixMax h n`. -/
theorem le_prefixMax_of_le {h : ℕ → ℕ} {j n : ℕ} (hj : j ≤ n) : h j ≤ prefixMax h n :=
  Finset.le_sup (f := h) (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))

/-- `prefixMax h` preserves polynomial boundedness. -/
theorem prefixMax_polynomiallyBounded {h : ℕ → ℕ} (hh : PolynomiallyBounded h) :
    PolynomiallyBounded (prefixMax h) := by
  obtain ⟨c, d, hcd⟩ := polynomiallyBounded_iff_le.mp hh
  refine PolynomiallyBounded.of_forall_le c d fun n ↦ ?_
  rw [prefixMax, Finset.sup_le_iff]
  intro j hj
  have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  exact (hcd j).trans (Nat.mul_le_mul_left c (Nat.pow_le_pow_left (by omega) d))

/-- Left-composing a compression with a polynomial parameter transformation yields a compression. -/
theorem IsPolyParamTransformation.comp_compression {encA : α ↪ List Bool} {κA : α → ℕ}
    {A : Set α} {encB : β ↪ List Bool} {κB : β → ℕ} {B : Set β} {encC : γ ↪ List Bool}
    {Z : Set γ} {f : α → β} {p h : ℕ → ℕ} {K : β → γ}
    (hf : IsPolyParamTransformation encA κA A encB κB B f p)
    (hK : IsCompression encB κB B encC Z K h) :
    IsCompression encA κA A encC Z (fun a ↦ K (f a)) (fun k ↦ prefixMax h (p k)) :=
  { polyTime := polyTimeWithParam_comp hf.polyParam hf.polyTime hK.polyTime hf.parameter_le
    mem_iff := fun a ↦ (hK.mem_iff (f a)).trans (hf.mem_iff a)
    length_le := fun a ↦ (hK.length_le (f a)).trans (le_prefixMax_of_le (hf.parameter_le a)) }

/-- Transitivity of `IsPolyParamTransformation`. -/
theorem IsPolyParamTransformation.trans {encA : α ↪ List Bool} {κA : α → ℕ} {A : Set α}
    {encB : β ↪ List Bool} {κB : β → ℕ} {B : Set β} {encC : γ ↪ List Bool} {κC : γ → ℕ}
    {C : Set γ} {f : α → β} {g : β → γ} {p q : ℕ → ℕ}
    (hf : IsPolyParamTransformation encA κA A encB κB B f p)
    (hg : IsPolyParamTransformation encB κB B encC κC C g q) :
    IsPolyParamTransformation encA κA A encC κC C (fun a ↦ g (f a))
      (fun k ↦ prefixMax q (p k)) :=
  { polyParam := (prefixMax_polynomiallyBounded hg.polyParam).comp hf.polyParam
    polyTime := polyTimeWithParam_comp hf.polyParam hf.polyTime hg.polyTime hf.parameter_le
    mem_iff := fun a ↦ (hg.mem_iff (f a)).trans (hf.mem_iff a)
    parameter_le := fun a ↦ (hg.parameter_le (f a)).trans (le_prefixMax_of_le (hf.parameter_le a)) }

/-- Transitivity of `PolyParamReducible`. -/
theorem PolyParamReducible.trans {encA : α ↪ List Bool} {κA : α → ℕ} {A : Set α}
    {encB : β ↪ List Bool} {κB : β → ℕ} {B : Set β} {encC : γ ↪ List Bool} {κC : γ → ℕ}
    {C : Set γ} (h₁ : PolyParamReducible encA κA A encB κB B)
    (h₂ : PolyParamReducible encB κB B encC κC C) :
    PolyParamReducible encA κA A encC κC C :=
  let ⟨_, _, hf⟩ := h₁; let ⟨_, _, hg⟩ := h₂; ⟨_, _, hf.trans hg⟩

/-- Polynomial parameter transformations transfer polynomial compressions backwards. -/
theorem PolyParamReducible.hasPolyCompression {encA : α ↪ List Bool} {κA : α → ℕ} {A : Set α}
    {encB : β ↪ List Bool} {κB : β → ℕ} {B : Set β}
    (hred : PolyParamReducible encA κA A encB κB B)
    (hcomp : HasPolyCompression encB κB B) :
    HasPolyCompression encA κA A := by
  obtain ⟨f, p, hf⟩ := hred
  obtain ⟨Z, K, h, hh, hK⟩ := hcomp
  exact (hf.comp_compression hK).hasPolyCompression
    ((prefixMax_polynomiallyBounded hh).comp hf.polyParam)

/-- Polynomial parameter transformations transfer polynomial kernelization lower bounds. -/
theorem PolyParamReducible.not_hasPolyKernel {encA : α ↪ List Bool} {κA : α → ℕ} {A : Set α}
    {encB : β ↪ List Bool} {κB : β → ℕ} {B : Set β}
    (hred : PolyParamReducible encA κA A encB κB B)
    (hno : ¬ HasPolyCompression encA κA A) :
    ¬ HasPolyKernel encB κB B :=
  fun hkern ↦ hno (hred.hasPolyCompression hkern.hasPolyCompression)

end ParameterTransformations

section QuantitativeCompressions

variable {α β : Type}

/-- The parameterized problem `(A, κ)` admits a *compression of size `O(k ^ e)`* (for real exponent
`e : ℝ`) if there exist a target bit-string language `Z`, a compression map `K`, and a size bound
`h : ℕ → ℕ` such that `IsCompression enc κ A encBits Z K h` and `h(k) = O(k ^ e)` as `k → ∞`. -/
def HasCompressionOfSizeO (enc : α ↪ List Bool) (κ : α → ℕ) (A : Set α) (e : ℝ) : Prop :=
  ∃ (Z : Set (List Bool)) (K : α → List Bool) (h : ℕ → ℕ),
    IsCompression enc κ A encBits Z K h ∧
      (fun k : ℕ ↦ (h k : ℝ)) =O[atTop] (fun k : ℕ ↦ (k : ℝ) ^ e)

/-- Monotonicity of `HasCompressionOfSizeO` in the exponent `e`. -/
theorem HasCompressionOfSizeO.mono {enc : α ↪ List Bool} {κ : α → ℕ} {A : Set α} {e₁ e₂ : ℝ}
    (hle : e₁ ≤ e₂) (hcomp : HasCompressionOfSizeO enc κ A e₁) :
    HasCompressionOfSizeO enc κ A e₂ := by
  obtain ⟨Z, K, h, hK, hO⟩ := hcomp
  refine ⟨Z, K, h, hK, hO.trans (IsBigO.of_bound 1 ?_)⟩
  filter_upwards [eventually_ge_atTop 1] with k hk
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  rw [one_mul, Real.norm_of_nonneg (Real.rpow_nonneg (by positivity) e₁),
    Real.norm_of_nonneg (Real.rpow_nonneg (by positivity) e₂)]
  exact Real.rpow_le_rpow_of_exponent_le hk1 hle

/-- Every polynomial compression is a compression of size `O(k ^ d)` for some `d : ℕ`. -/
theorem HasPolyCompression.exists_hasCompressionOfSizeO {enc : α ↪ List Bool} {κ : α → ℕ}
    {A : Set α} (hpoly : HasPolyCompression enc κ A) :
    ∃ d : ℕ, HasCompressionOfSizeO enc κ A (d : ℝ) := by
  obtain ⟨Z, K, h, hh, hK⟩ := hpoly
  obtain ⟨c, d, hcd⟩ := polynomiallyBounded_iff_le.mp hh
  refine ⟨d, Z, K, h, hK, IsBigO.of_bound ((c * 2 ^ d : ℕ) : ℝ) ?_⟩
  filter_upwards [eventually_ge_atTop 1] with k hk
  have hbound : h k ≤ c * 2 ^ d * k ^ d := calc
    h k ≤ c * (k + 1) ^ d := hcd k
    _ ≤ c * (2 * k) ^ d := Nat.mul_le_mul_left c (Nat.pow_le_pow_left (by omega) d)
    _ = c * 2 ^ d * k ^ d := by rw [Nat.mul_pow]; ring
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _),
    Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _), Real.rpow_natCast]
  exact_mod_cast hbound

/-- Every polynomial kernel gives a compression of size `O(k ^ d)` for some `d : ℕ`. -/
theorem HasPolyKernel.exists_hasCompressionOfSizeO {enc : α ↪ List Bool} {κ : α → ℕ} {A : Set α}
    (hkern : HasPolyKernel enc κ A) :
    ∃ d : ℕ, HasCompressionOfSizeO enc κ A (d : ℝ) :=
  HasPolyCompression.exists_hasCompressionOfSizeO hkern.hasPolyCompression

private theorem isBigO_prefixMax_comp_pow {h p : ℕ → ℕ} {e : ℝ} (he : 0 < e) {c₁ c₀ d : ℕ}
    (hd : 1 ≤ d) (hp : ∀ k, p k ≤ c₁ * k ^ d + c₀)
    (hO : (fun k : ℕ ↦ (h k : ℝ)) =O[atTop] (fun k : ℕ ↦ (k : ℝ) ^ e)) :
    (fun k : ℕ ↦ (prefixMax h (p k) : ℝ)) =O[atTop] (fun k : ℕ ↦ (k : ℝ) ^ ((d : ℝ) * e)) := by
  rw [isBigO_iff] at hO ⊢
  obtain ⟨C, hCev⟩ := hO
  obtain ⟨N, hN⟩ := eventually_atTop.mp hCev
  let C' : ℝ := max C 0
  let M₀ : ℕ := prefixMax h N
  let A : ℕ := c₁ + c₀ + 1
  refine ⟨(M₀ : ℝ) + C' * (A : ℝ) ^ e, eventually_atTop.mpr ⟨1, fun k hk ↦ ?_⟩⟩
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hde_pos : 0 < (d : ℝ) * e := mul_pos (by exact_mod_cast (by omega : 0 < d)) he
  have hpow_ge1 : (1 : ℝ) ≤ (k : ℝ) ^ ((d : ℝ) * e) := Real.one_le_rpow hk1 (le_of_lt hde_pos)
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _),
    Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
  obtain ⟨j, hj, heq⟩ := Finset.exists_mem_eq_sup (Finset.range (p k + 1))
    ⟨0, Finset.mem_range.mpr (Nat.succ_pos _)⟩ h
  have hjp : j ≤ p k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  change (prefixMax h (p k) : ℝ) ≤ _
  rw [show prefixMax h (p k) = h j from heq]
  have hnonneg_term : 0 ≤ C' * (A : ℝ) ^ e * (k : ℝ) ^ ((d : ℝ) * e) :=
    mul_nonneg (mul_nonneg (le_max_right _ _) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  by_cases hjN : j ≤ N
  · have h1 : (h j : ℝ) ≤ (M₀ : ℝ) := by exact_mod_cast le_prefixMax_of_le hjN
    calc (h j : ℝ) ≤ (M₀ : ℝ) * 1 := by linarith
      _ ≤ (M₀ : ℝ) * (k : ℝ) ^ ((d : ℝ) * e) :=
          mul_le_mul_of_nonneg_left hpow_ge1 (Nat.cast_nonneg _)
      _ ≤ ((M₀ : ℝ) + C' * (A : ℝ) ^ e) * (k : ℝ) ^ ((d : ℝ) * e) := by linarith
  · have hhj := hN j (by omega)
    rw [Real.norm_of_nonneg (Nat.cast_nonneg _),
      Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)] at hhj
    have hkd : 1 ≤ k ^ d := Nat.one_le_pow d k hk
    have hj_bound : j ≤ A * k ^ d := calc
      j ≤ p k := hjp
      _ ≤ c₁ * k ^ d + c₀ := hp k
      _ ≤ c₁ * k ^ d + c₀ * k ^ d + 1 * k ^ d := by nlinarith
      _ = A * k ^ d := by dsimp [A]; ring
    have hj_real : (j : ℝ) ≤ (A : ℝ) * (k : ℝ) ^ d := by exact_mod_cast hj_bound
    have hj_rpow : (j : ℝ) ^ e ≤ (A : ℝ) ^ e * (k : ℝ) ^ ((d : ℝ) * e) := calc
      (j : ℝ) ^ e ≤ ((A : ℝ) * (k : ℝ) ^ d) ^ e :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) hj_real (le_of_lt he)
      _ = (A : ℝ) ^ e * ((k : ℝ) ^ d) ^ e :=
        Real.mul_rpow (Nat.cast_nonneg _) (pow_nonneg (Nat.cast_nonneg _) _)
      _ = (A : ℝ) ^ e * (k : ℝ) ^ ((d : ℝ) * e) := by
        rw [← Real.rpow_natCast (k : ℝ) d, ← Real.rpow_mul (Nat.cast_nonneg _)]
    have hM_nonneg : 0 ≤ (M₀ : ℝ) * (k : ℝ) ^ ((d : ℝ) * e) :=
      mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    calc (h j : ℝ) ≤ C * (j : ℝ) ^ e := hhj
      _ ≤ C' * (j : ℝ) ^ e :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      _ ≤ C' * ((A : ℝ) ^ e * (k : ℝ) ^ ((d : ℝ) * e)) :=
          mul_le_mul_of_nonneg_left hj_rpow (le_max_right _ _)
      _ ≤ ((M₀ : ℝ) + C' * (A : ℝ) ^ e) * (k : ℝ) ^ ((d : ℝ) * e) := by linarith

/-- Quantitative compression transfer along degree-`d` polynomial parameter transformations. -/
theorem IsPolyParamTransformation.hasCompressionOfSizeO_of_pow {encA : α ↪ List Bool} {κA : α → ℕ}
    {A : Set α} {encB : β ↪ List Bool} {κB : β → ℕ} {B : Set β} {f : α → β} {p : ℕ → ℕ}
    (hf : IsPolyParamTransformation encA κA A encB κB B f p)
    {c₁ c₀ d : ℕ} (hd : 1 ≤ d) (hp : ∀ k, p k ≤ c₁ * k ^ d + c₀)
    {e : ℝ} (he : 0 < e) (hcomp : HasCompressionOfSizeO encB κB B e) :
    HasCompressionOfSizeO encA κA A ((d : ℝ) * e) := by
  obtain ⟨Z, K, h, hK, hO⟩ := hcomp
  exact ⟨Z, fun a ↦ K (f a), fun k ↦ prefixMax h (p k), hf.comp_compression hK,
    isBigO_prefixMax_comp_pow he hd hp hO⟩

/-- Quantitative `O(k ^ (b - ε))` incompressibility transfer along degree-`d` transformations. -/
theorem IsPolyParamTransformation.not_hasCompressionOfSizeO_sub_of_pow {encA : α ↪ List Bool}
    {κA : α → ℕ} {A : Set α} {encB : β ↪ List Bool} {κB : β → ℕ} {B : Set β} {f : α → β}
    {p : ℕ → ℕ} (hf : IsPolyParamTransformation encA κA A encB κB B f p)
    {c₁ c₀ d : ℕ} (hd : 1 ≤ d) (hp : ∀ k, p k ≤ c₁ * k ^ d + c₀)
    {b : ℝ} (hb : 1 ≤ b)
    (hno : ∀ ε' : ℝ, 0 < ε' → ¬ HasCompressionOfSizeO encA κA A ((d : ℝ) * b - ε'))
    {ε : ℝ} (hε : 0 < ε) :
    ¬ HasCompressionOfSizeO encB κB B (b - ε) := by
  intro hcomp
  let δ : ℝ := min ε (1 / 2)
  have hδ_pos : 0 < δ := lt_min hε (by norm_num)
  have hδ_le : δ ≤ ε := min_le_left _ _
  have hδ_half : δ ≤ 1 / 2 := min_le_right _ _
  have he_pos : 0 < b - δ := by linarith
  have hA := hf.hasCompressionOfSizeO_of_pow hd hp he_pos (hcomp.mono (by linarith))
  have hd_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
  rw [show (d : ℝ) * (b - δ) = (d : ℝ) * b - (d : ℝ) * δ by ring] at hA
  exact hno ((d : ℝ) * δ) (mul_pos hd_pos hδ_pos) hA

/-- Quantitative `O(k ^ (b - ε))` incompressibility transfer along linear parameter
transformations. -/
theorem LinearParamReducible.not_hasCompressionOfSizeO_sub {encA : α ↪ List Bool} {κA : α → ℕ}
    {A : Set α} {encB : β ↪ List Bool} {κB : β → ℕ} {B : Set β}
    (hred : LinearParamReducible encA κA A encB κB B) {b : ℝ} (hb : 1 ≤ b)
    (hno : ∀ ε' : ℝ, 0 < ε' → ¬ HasCompressionOfSizeO encA κA A (b - ε'))
    {ε : ℝ} (hε : 0 < ε) :
    ¬ HasCompressionOfSizeO encB κB B (b - ε) := by
  obtain ⟨f, c₁, c₀, hf⟩ := hred
  refine hf.isPolyParamTransformation.not_hasCompressionOfSizeO_sub_of_pow
    (c₁ := c₁) (c₀ := c₀) (d := 1) le_rfl (fun _ ↦ by simp) hb
    (fun ε' hε' ↦ by simpa only [Nat.cast_one, one_mul] using hno ε' hε') hε

end QuantitativeCompressions

section HittingSet

/-- An instance `(n, s, sets)` of `b`-Hitting Set parameterized by the universe size `n`. -/
@[ext]
structure HittingSetInstance where
  /-- The size `n` of the ground universe `{0, …, n - 1}` (also the parameter). -/
  n : ℕ
  /-- The maximum allowed cardinality `s` of a hitting set. -/
  s : ℕ
  /-- The collection of subsets `S₁, …, Sₘ` of `{0, …, n - 1}`. -/
  sets : List (List ℕ)
  deriving DecidableEq, Repr, Inhabited

/-- Encoding of `HittingSetInstance`: universe size `n` in unary (`encUnary`), budget `s` in binary
(`encNat`), and hyperedge family as a framed list of framed lists of binary vertex indices. -/
enc_structure encHittingSetInstance : HittingSetInstance where
  n : encUnary,
  s : encNat,
  sets : (encList (encList encNat))

/-- A `HittingSetInstance` is a valid `b`-uniform hypergraph on `{0, …, n - 1}` if every `S ∈ sets`
has exactly `b` distinct elements, all strictly less than `n`. -/
def HittingSetInstance.IsUniform (b : ℕ) (x : HittingSetInstance) : Prop :=
  ∀ S ∈ x.sets, S.toFinset.card = b ∧ ∀ i ∈ S, i < x.n

/-- The parameterized decision language `b`-Hitting Set (with parameter `HittingSetInstance.n`). -/
def bHittingSet (b : ℕ) : Set HittingSetInstance :=
  {x | x.IsUniform b ∧
    ∃ W : Finset ℕ, (∀ i ∈ W, i < x.n) ∧ W.card ≤ x.s ∧
      ∀ S ∈ x.sets, (W ∩ S.toFinset).Nonempty}

end HittingSet

end CslibFrontier.Complexity
