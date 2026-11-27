/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CslibFrontier.Computability.Complexity.Classes.SharpP.Closure
public import CslibFrontier.Computability.Complexity.Classes.SharpP.Completeness
public import CslibFrontier.Computability.Complexity.Classes.SharpP.Metric
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.IntBinary

/-!
# Parsimonious and Metric Reductions and `GapP`-Completeness

Develops parsimonious reductions, one-query metric reductions, and completeness for the
gap-definable counting class `Cslib.Complexity.GapP`,
extending `CslibFrontier.Computability.Complexity.Classes.SharpP.Completeness` and `.Metric`.

## Main definitions

* `Cslib.Complexity.GapPParsimoniousReducible`: polynomial-time exact-value (parsimonious)
  reduction between integer-valued functions `α → ℤ` and `β → ℤ`.
* `Cslib.Complexity.GapPHard`, `Cslib.Complexity.GapPComplete`: parsimonious `GapP`-hardness and
  `GapP`-completeness.
* `Cslib.Complexity.GapPMetricHard`, `Cslib.Complexity.GapPMetricComplete`: one-query metric
  `GapP`-hardness and `GapP`-completeness using `MetricReducible` and `encIntBin`.

## Main results

* `Cslib.Complexity.GapP.sub_mem`: `GapP` is closed under subtraction.
* `Cslib.Complexity.GapPParsimoniousReducible.refl`, `.trans`, `.mem_GapP`: parsimonious `GapP`
  reductions form a preorder preserving `GapP` membership.
* `Cslib.Complexity.GapPHard.trans`, `.gapPMetricHard`: hardness transfer and implication from
  parsimonious to metric `GapP`-hardness.
* `Cslib.Complexity.GapPMetricHard.computableInPolyTime`: polynomial-time computability of a
  metric `GapP`-hard function collapses `GapP` into `FP` (binary integer output).
* `Cslib.Complexity.SharpPHard.pair_sub_gapPHard`: any parsimoniously `#P`-hard function yields
  a parsimoniously `GapP`-hard pair difference `(a, b) ↦ g a - g b`.
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

section Core

variable {α β γ : Type}

/-- `f : α → ℤ` reduces parsimoniously to `g : β → ℤ`: some polynomial-time computable
`r : α → β` satisfies `f a = g (r a)` for every `a`. -/
@[expose] def GapPParsimoniousReducible (encA : α ↪ List Bool) (encB : β ↪ List Bool)
    (f : α → ℤ) (g : β → ℤ) : Prop :=
  ∃ r : α → β, ComputableInPolyTime r encA encB ∧ ∀ a, f a = g (r a)

/-- Every function in `GapP`, with any input encoding, reduces parsimoniously to `g`. -/
@[expose] def GapPHard (encB : β ↪ List Bool) (g : β → ℤ) : Prop :=
  HardUnder (fun enc => GapPParsimoniousReducible enc encB) @GapP g

/-- `g` lies in `GapP` and is `GapP`-hard under parsimonious reductions. -/
@[expose] def GapPComplete (encB : β ↪ List Bool) (g : β → ℤ) : Prop :=
  g ∈ GapP encB ∧ GapPHard encB g

/-- Every function in `GapP`, with any input encoding, reduces to `g` via a one-query metric
reduction (output encoded via `encIntBin` / `encZ`). -/
@[expose] def GapPMetricHard {Z : Type} (encB : β ↪ List Bool) (encZ : Z ↪ List Bool)
    (g : β → Z) : Prop :=
  HardUnder (fun enc => MetricReducible enc encB encIntBin encZ) @GapP g

/-- `g` lies in `GapP` and is `GapP`-hard under one-query metric reductions. -/
@[expose] def GapPMetricComplete (encB : β ↪ List Bool) (g : β → ℤ) : Prop :=
  g ∈ GapP encB ∧ GapPMetricHard encB encIntBin g

variable {encA : α ↪ List Bool} {encB : β ↪ List Bool} {encC : γ ↪ List Bool}
  {f : α → ℤ} {g : β → ℤ} {h : γ → ℤ}

/-- `GapP` is closed under subtraction. -/
theorem GapP.sub_mem {g₁ g₂ : α → ℤ} (h₁ : g₁ ∈ GapP encA) (h₂ : g₂ ∈ GapP encA) :
    g₁ - g₂ ∈ GapP encA :=
  GapP.sub_mem' h₁ h₂

/-- `GapP`-hardness is `HardUnder` for `GapPParsimoniousReducible`. -/
theorem gapPHard_iff_hardUnder :
    GapPHard encB g ↔ HardUnder (fun enc => GapPParsimoniousReducible enc encB) @GapP g := Iff.rfl

/-- `GapP`-completeness is `CompleteUnder` for `GapPParsimoniousReducible`. -/
theorem gapPComplete_iff_completeUnder :
    GapPComplete encB g ↔
      CompleteUnder (fun enc => GapPParsimoniousReducible enc encB) @GapP encB g := Iff.rfl

/-- Every integer-valued function reduces parsimoniously to itself via `id`. -/
@[refl]
theorem GapPParsimoniousReducible.refl (encA : α ↪ List Bool) (f : α → ℤ) :
    GapPParsimoniousReducible encA encA f f :=
  ⟨id, ComputableInPolyTime.id', fun _ => rfl⟩

/-- Parsimonious `GapP` reductions compose. -/
@[trans]
theorem GapPParsimoniousReducible.trans (hfg : GapPParsimoniousReducible encA encB f g)
    (hgh : GapPParsimoniousReducible encB encC g h) :
    GapPParsimoniousReducible encA encC f h :=
  let ⟨r, hr, hfg⟩ := hfg
  let ⟨s, hs, hgh⟩ := hgh
  ⟨s ∘ r, hs.comp hr, fun a => (hfg a).trans (hgh (r a))⟩

/-- `GapP` is closed under parsimonious reductions. -/
theorem GapPParsimoniousReducible.mem_GapP (hfg : GapPParsimoniousReducible encA encB f g)
    (hg : g ∈ GapP encB) : f ∈ GapP encA := by
  obtain ⟨r, hr, hfg⟩ := hfg
  have hcomp := GapP.comp_mem hg hr
  rwa [show g ∘ r = f from funext fun a => (hfg a).symm] at hcomp

/-- Parsimonious `GapP` reductions are metric reductions with output encoding `encIntBin`. -/
theorem GapPParsimoniousReducible.metricReducible
    (hfg : GapPParsimoniousReducible encA encB f g) :
    MetricReducible encA encB encIntBin encIntBin f g :=
  let ⟨r, hr, hfg⟩ := hfg
  ⟨r, Prod.snd, hr, by fun_prop, hfg⟩

/-- Parsimonious `GapP`-hardness transfers along a parsimonious reduction. -/
theorem GapPHard.trans (hg : GapPHard encB g) (hgh : GapPParsimoniousReducible encB encC g h) :
    GapPHard encC h :=
  HardUnder.trans (fun _ _ u v => u.trans v) hg hgh

/-- Parsimonious `GapP`-hardness implies metric `GapP`-hardness. -/
theorem GapPHard.gapPMetricHard (hg : GapPHard encB g) : GapPMetricHard encB encIntBin g :=
  fun _ _ _ hf => (hg _ _ hf).metricReducible

/-- Parsimonious `GapP`-completeness implies metric `GapP`-completeness. -/
theorem GapPComplete.gapPMetricComplete (hg : GapPComplete encB g) :
    GapPMetricComplete encB g :=
  ⟨hg.1, hg.2.gapPMetricHard⟩

/-- Metric `GapP`-hardness transfers along a metric reduction. -/
theorem GapPMetricHard.trans {Z W : Type} {encZ : Z ↪ List Bool} {encW : W ↪ List Bool}
    {g : β → Z} {h : γ → W} (hg : GapPMetricHard encB encZ g)
    (hgh : MetricReducible encB encC encZ encW g h) : GapPMetricHard encC encW h :=
  fun _ _ _ hf => (hg _ _ hf).trans hgh

/-- If a metric `GapP`-hard function is computable in polynomial time, then so is every function
in `GapP` (with output encoded in signed binary via `encIntBin`). -/
theorem GapPMetricHard.computableInPolyTime {Z : Type} {encZ : Z ↪ List Bool} {g : β → Z}
    (hg : GapPMetricHard encB encZ g) (hpoly : ComputableInPolyTime g encB encZ)
    (hf : f ∈ GapP encA) : ComputableInPolyTime f encA encIntBin := by
  obtain ⟨r, post, hr, hpost, hfg⟩ := hg _ _ hf
  have hgr : ComputableInPolyTime (fun a => g (r a)) encA encZ := hpoly.comp hr
  rw [show f = fun a => post (a, g (r a)) from funext hfg]
  exact hpost.comp (by fun_prop)

/-- Every `#P`-hard function under parsimonious reductions yields a `GapP`-hard difference
`(f₁, f₂) ↦ g f₁ - g f₂` (under `encPair`). -/
theorem SharpPHard.pair_sub_gapPHard (hg : SharpPHard encB (fun b => (g b).toNat))
    (hnonneg : ∀ b, 0 ≤ g b) :
    GapPHard (encPair encB encB) (fun p : β × β => g p.1 - g p.2) := by
  intro α encA f hf
  obtain ⟨f₁, hf₁, f₂, hf₂, hEq⟩ := mem_GapP.mp hf
  obtain ⟨r₁, hr₁, hfr₁⟩ := hg encA f₁ hf₁
  obtain ⟨r₂, hr₂, hfr₂⟩ := hg encA f₂ hf₂
  refine ⟨fun a => (r₁ a, r₂ a), hr₁.prod hr₂, fun a => ?_⟩
  have h1 : (f₁ a : ℤ) = g (r₁ a) := by
    have := congrArg (Nat.cast (R := ℤ)) (hfr₁ a)
    simpa [Int.toNat_of_nonneg (hnonneg (r₁ a))] using this
  have h2 : (f₂ a : ℤ) = g (r₂ a) := by
    have := congrArg (Nat.cast (R := ℤ)) (hfr₂ a)
    simpa [Int.toNat_of_nonneg (hnonneg (r₂ a))] using this
  rw [hEq a, h1, h2]

end Core

end Cslib.Complexity
