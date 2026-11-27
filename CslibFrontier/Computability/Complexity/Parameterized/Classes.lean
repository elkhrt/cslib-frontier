/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import CslibFrontier.Computability.Complexity.Classes.SharpP.Metric
public import CslibFrontier.Computability.Complexity.Parameterized.WHierarchy.XP
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Parameterized Complexity Classes: `coW[t]`, `para-K`, `XNP`, and `#W[t]`

This module extends the parameterized complexity infrastructure of `Cslib.Complexity`
(`FPT`, `XP`, `W`, `WP`, `FPTReducible`, `FPTHard`) with textbook parameterized decision
and counting classes:

- **Complementary W-hierarchy** (`coW`, `coWHard`, `coWComplete`) and completeness
  definitions (`WComplete`, `WPComplete`).
- **Parameterized classical classes** (`Para`, `ParaHard`, `ParaComplete`), together with the
  constant-slice hardness criterion.
- **Slicewise polynomial computability and `XNP`** (`ComputableInXPTime`, `XNP`), the
  nondeterministic counterpart of `XP`.
- **Parameterized counting complexity** (`SharpWCS`, `SharpWeightedCircuitSAT`,
  `FPTParsimoniousReducible`, `FPTMetricReducible`, `SharpW`, `SharpWHard`, `SharpWComplete`,
  `SharpWMetric`, `SharpWMetricHard`, `ParaSharpPHard`, `ParaSharpPComplete`), together with
  the unconditional polynomial upper bound on `#WCS[t, d]` that rules out FPT parsimonious
  reductions from exponentially growing counting problems on bounded-parameter slices.

All proofs use only standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`).

## Main definitions

* `Cslib.Complexity.coW`, `Cslib.Complexity.coWHard`, `Cslib.Complexity.coWComplete`,
  `Cslib.Complexity.WComplete`, `Cslib.Complexity.WPComplete`.
* `Cslib.Complexity.Para`, `Cslib.Complexity.ParaHard`, `Cslib.Complexity.ParaComplete`.
* `Cslib.Complexity.ComputableInXPTime`, `Cslib.Complexity.XNP`.
* `Cslib.Complexity.SharpWCS`, `Cslib.Complexity.SharpWeightedCircuitSAT`,
  `Cslib.Complexity.FPTParsimoniousReducible`, `Cslib.Complexity.FPTMetricReducible`,
  `Cslib.Complexity.SharpW`, `Cslib.Complexity.SharpWHard`,
  `Cslib.Complexity.SharpWComplete`, `Cslib.Complexity.SharpWMetric`,
  `Cslib.Complexity.SharpWMetricHard`, `Cslib.Complexity.ParaSharpPHard`,
  `Cslib.Complexity.ParaSharpPComplete`.

## Main results

* `Cslib.Complexity.FPTReducible.mem_coW`, `Cslib.Complexity.FPT_subset_coW`,
  `Cslib.Complexity.coW_subset_XP`: closure and inclusions for `coW[t]`.
* `Cslib.Complexity.Para.mem_of_mem`, `Cslib.Complexity.ParaHard.of_slice_hard`:
  membership inheritance and Flum–Grohe constant-slice hardness for `para-𝒞`.
* `Cslib.Complexity.XP_subset_XNP`, `Cslib.Complexity.NP_subset_XNP`:
  inclusions into `XNP`.
* `Cslib.Complexity.sharpWCS_le_pow`, `Cslib.Complexity.not_mem_sharpW_of_two_pow_le`,
  `Cslib.Complexity.not_parsimonious_sharpWeightedCircuitSAT_of_two_pow_le`:
  polynomial upper bound on `#WCS[t, d]` and unconditional non-reducibility criteria.
-/

public section

namespace Cslib.Complexity

open Cslib Cslib.Complexity Cslib.Circuits Cslib.Circuits.Boolean Turing.MultiTapeTM

/-! ### Complementary W-hierarchy and completeness -/

section WHierarchy

variable {α β : Type}

/-- **The complementary class `coW[t]`**: parameterized problems whose complement belongs to
`W[t]`. -/
def coW (t : ℕ) (enc : α ↪ List Bool) (κ : α → ℕ) : Set (Set α) :=
  {A | Aᶜ ∈ W t enc κ}

/-- Complement membership characterization for `coW[t]`. -/
@[simp]
theorem compl_mem_coW {t : ℕ} {enc : α ↪ List Bool} {κ : α → ℕ} {A : Set α} :
    Aᶜ ∈ coW t enc κ ↔ A ∈ W t enc κ := by
  simp [coW]

/-- **`coW[t]`-hardness**: every problem in `coW[t]` fpt-reduces to `B`. -/
abbrev coWHard (t : ℕ) (enc : β ↪ List Bool) (κ : β → ℕ) (B : Set β) : Prop :=
  FPTHard (coW t) enc κ B

/-- **`W[t]`-completeness**: membership in `W[t]` together with `W[t]`-hardness. -/
def WComplete (t : ℕ) (enc : β ↪ List Bool) (κ : β → ℕ) (B : Set β) : Prop :=
  B ∈ W t enc κ ∧ WHard t enc κ B

/-- **`coW[t]`-completeness**: membership in `coW[t]` together with `coW[t]`-hardness. -/
def coWComplete (t : ℕ) (enc : β ↪ List Bool) (κ : β → ℕ) (B : Set β) : Prop :=
  B ∈ coW t enc κ ∧ coWHard t enc κ B

/-- **`W[P]`-completeness**: membership in `W[P]` together with `W[P]`-hardness. -/
def WPComplete (enc : β ↪ List Bool) (κ : β → ℕ) (B : Set β) : Prop :=
  B ∈ WP enc κ ∧ WPHard enc κ B

variable {encA : α ↪ List Bool} {encB : β ↪ List Bool} {κA : α → ℕ} {κB : β → ℕ}
  {A : Set α} {B : Set β} {t : ℕ}

/-- Membership characterization for `coW[t]`. -/
theorem mem_coW_iff : A ∈ coW t encA κA ↔ Aᶜ ∈ W t encA κA :=
  Iff.rfl

/-- **`coW[t]` is closed under fpt-reductions.** -/
theorem FPTReducible.mem_coW (hAB : FPTReducible encA encB κA κB A B)
    (hB : B ∈ coW t encB κB) : A ∈ coW t encA κA :=
  hAB.compl.mem_W hB

/-- **`FPT ⊆ coW[t]`** for every `t`. -/
theorem FPT_subset_coW (t : ℕ) : FPT encA κA ⊆ coW t encA κA := fun _ hA ↦
  FPT_subset_W t (compl_mem_FPT hA)

/-- **`coW[t] ⊆ XP`** for every `t`. -/
theorem coW_subset_XP (t : ℕ) : coW t encA κA ⊆ XP encA κA := fun A hA ↦ by
  have hAc : Aᶜ ∈ XP encA κA := W_subset_XP t hA
  simpa only [compl_compl] using compl_mem_XP hAc

/-- **`coW[t]`-hardness is equivalent to `W[t]`-hardness of the complement.** -/
theorem coWHard_iff_compl_wHard :
    coWHard t encB κB B ↔ WHard t encB κB Bᶜ := by
  constructor
  · intro h γ encC κC C hC
    have hCc : Cᶜ ∈ coW t encC κC := by simpa only [mem_coW_iff, compl_compl] using hC
    simpa only [compl_compl] using (h encC κC Cᶜ hCc).compl
  · intro h γ encC κC C hC
    simpa only [compl_compl] using (h encC κC Cᶜ hC).compl

/-- **`coW[t]`-completeness is equivalent to `W[t]`-completeness of the complement.** -/
theorem coWComplete_iff_compl_wComplete :
    coWComplete t encB κB B ↔ WComplete t encB κB Bᶜ :=
  and_congr Iff.rfl coWHard_iff_compl_wHard

end WHierarchy

/-! ### FPT-time pairing and parameterized classical classes (`para-𝒞`) -/

section Para

private theorem computableInFPTTime_exists_inO {α β : Type} {f : α → β}
    {encA : α ↪ List Bool} {encB : β ↪ List Bool} {κ : α → ℕ}
    (h : ComputableInFPTTime f encA encB κ) :
    ∃ (F : ℕ → ℕ) (c : ℕ), ComputableInO f encA encB
      (fun a ↦ F (κ a) * ((encA a).length + 1) ^ c)
      (fun a ↦ F (κ a) * ((encA a).length + 1) ^ c) :=
  let ⟨F, c, hc⟩ := h
  ⟨F, c, .of_bounds hc 1 (fun _ ↦ by omega) (fun _ ↦ by omega)
    fun a ↦ (hc.length_le a).trans (by omega)⟩

/-- **Pairing in fpt time**: if `f` and `g` are computable in fpt time with respect to `κ`,
then `a ↦ (f a, g a)` is computable in fpt time with respect to `κ`. -/
theorem computableInFPTTime_prod {α β₁ β₂ : Type} {f : α → β₁} {g : α → β₂}
    {encA : α ↪ List Bool} {enc₁ : β₁ ↪ List Bool} {enc₂ : β₂ ↪ List Bool} {κ : α → ℕ}
    (hf : ComputableInFPTTime f encA enc₁ κ) (hg : ComputableInFPTTime g encA enc₂ κ) :
    ComputableInFPTTime (fun a ↦ (f a, g a)) encA (encPair enc₁ enc₂) κ := by
  obtain ⟨F₁, c₁, hf'⟩ := computableInFPTTime_exists_inO hf
  obtain ⟨F₂, c₂, hg'⟩ := computableInFPTTime_exists_inO hg
  have hle (a : α) :
      F₁ (κ a) * ((encA a).length + 1) ^ c₁ + F₂ (κ a) * ((encA a).length + 1) ^ c₂ ≤
        (F₁ (κ a) + F₂ (κ a)) * ((encA a).length + 1) ^ (c₁ + c₂) := by
    have h₁ : ((encA a).length + 1) ^ c₁ ≤ ((encA a).length + 1) ^ (c₁ + c₂) :=
      Nat.pow_le_pow_right (Nat.succ_pos _) (Nat.le_add_right _ _)
    have h₂ : ((encA a).length + 1) ^ c₂ ≤ ((encA a).length + 1) ^ (c₁ + c₂) :=
      Nat.pow_le_pow_right (Nat.succ_pos _) (Nat.le_add_left _ _)
    rw [Nat.add_mul]
    exact Nat.add_le_add (Nat.mul_le_mul_left _ h₁) (Nat.mul_le_mul_left _ h₂)
  exact ComputableInO.computableInFPTTime (F := fun k ↦ F₁ k + F₂ k) (c := c₁ + c₂)
    ((hf'.prod hg').mono_le hle hle)

/-- **The parameterized class `para-𝒞`** [Flum and Grohe ]: `A ∈ Para 𝒞 enc κ` when there
exist a language `Q ∈ 𝒞 (encPair enc encBits)` and an fpt-time-computable parameter-only
precomputation `g : α → List Bool` such that `a ∈ A ↔ (a, g a) ∈ Q`.
-/
def Para (𝒞 : ∀ {α : Type}, (α ↪ List Bool) → Set (Set α)) {α : Type}
    (enc : α ↪ List Bool) (κ : α → ℕ) : Set (Set α) :=
  {A | ∃ (Q : Set (α × List Bool)) (g : α → List Bool),
    (∃ g₀ : ℕ → List Bool, ∀ a, g a = g₀ (κ a)) ∧
    ComputableInFPTTime g enc encBits κ ∧
    Q ∈ 𝒞 (encPair enc encBits) ∧
    ∀ a, a ∈ A ↔ (a, g a) ∈ Q}

/-- **`para-𝒞`-hardness** under fpt-reductions. -/
abbrev ParaHard (𝒞 : ∀ {α : Type}, (α ↪ List Bool) → Set (Set α)) {β : Type}
    (enc : β ↪ List Bool) (κ : β → ℕ) (B : Set β) : Prop :=
  FPTHard (Para 𝒞) enc κ B

/-- **`para-𝒞`-completeness**: membership in `para-𝒞` together with `para-𝒞`-hardness. -/
def ParaComplete (𝒞 : ∀ {α : Type}, (α ↪ List Bool) → Set (Set α)) {β : Type}
    (enc : β ↪ List Bool) (κ : β → ℕ) (B : Set β) : Prop :=
  B ∈ Para 𝒞 enc κ ∧ ParaHard 𝒞 enc κ B

/-- Membership characterization for `Para 𝒞`. -/
theorem mem_Para_iff {𝒞 : ∀ {α : Type}, (α ↪ List Bool) → Set (Set α)} {α : Type}
    {enc : α ↪ List Bool} {κ : α → ℕ} {A : Set α} :
    A ∈ Para 𝒞 enc κ ↔ ∃ (Q : Set (α × List Bool)) (g : α → List Bool),
      (∃ g₀ : ℕ → List Bool, ∀ a, g a = g₀ (κ a)) ∧
      ComputableInFPTTime g enc encBits κ ∧
      Q ∈ 𝒞 (encPair enc encBits) ∧
      ∀ a, a ∈ A ↔ (a, g a) ∈ Q :=
  Iff.rfl

/-- **Classical membership implies `para-𝒞` membership** whenever `𝒞` is closed under
polynomial-time many-one reductions. -/
theorem Para.mem_of_mem {𝒞 : ∀ {α : Type}, (α ↪ List Bool) → Set (Set α)}
    (hclosed : ∀ {α β : Type} {eA : α ↪ List Bool} {eB : β ↪ List Bool} {A : Set α} {B : Set β},
      PolyTimeReducible eA eB A B → B ∈ 𝒞 eB → A ∈ 𝒞 eA)
    {α : Type} {enc : α ↪ List Bool} {κ : α → ℕ} {A : Set α} (hA : A ∈ 𝒞 enc) :
    A ∈ Para 𝒞 enc κ := by
  refine ⟨{p | p.1 ∈ A}, fun _ ↦ [], ⟨fun _ ↦ [], fun _ ↦ rfl⟩,
    (ComputableInPolyTime.const ([] : List Bool)).computableInFPTTime κ, ?_, fun _ ↦ Iff.rfl⟩
  exact hclosed ⟨Prod.fst, ComputableInPolyTime.fst enc encBits, fun _ ↦ Iff.rfl⟩ hA

/-- **Flum–Grohe constant-slice hardness**: if every problem in `𝒞` reduces in polynomial time
to `B` with parameter bounded by a constant `K`, then `B` is `para-𝒞`-hard. -/
theorem ParaHard.of_slice_hard {𝒞 : ∀ {α : Type}, (α ↪ List Bool) → Set (Set α)}
    {β : Type} {encB : β ↪ List Bool} {κB : β → ℕ} {B : Set β} (K : ℕ)
    (hslice : ∀ ⦃α : Type⦄ (encA : α ↪ List Bool) (A : Set α), A ∈ 𝒞 encA →
      ∃ r : α → β, ComputableInPolyTime r encA encB ∧ (∀ a, κB (r a) ≤ K) ∧
        ∀ a, a ∈ A ↔ r a ∈ B) :
    ParaHard 𝒞 encB κB B := by
  intro α encA κA A ⟨Q, g, _, hg, hQ, hAQ⟩
  obtain ⟨r, hr, hK, hrQ⟩ := hslice (encPair encA encBits) Q hQ
  have hpair : ComputableInFPTTime (fun a : α ↦ (a, g a)) encA (encPair encA encBits) κA :=
    computableInFPTTime_prod (ComputableInPolyTime.id'.computableInFPTTime κA) hg
  refine ⟨fun a ↦ r (a, g a), ⟨?_, fun _ ↦ K, fun a ↦ hK (a, g a)⟩,
    fun a ↦ (hAQ a).trans (hrQ (a, g a))⟩
  exact (hr.computableInFPTTime (fun p : α × List Bool ↦ κA p.1)).comp hpair
    (h := id) (fun _ ↦ le_rfl)

/-- **Constant-slice hardness from a single `𝒞`-hard problem**: if `L` is `𝒞`-hard and reduces in
polynomial time to `B` with parameter bounded by a constant `K`, then `B` is `para-𝒞`-hard. -/
theorem ParaHard.of_polyTimeHard_slice {𝒞 : ∀ {α : Type}, (α ↪ List Bool) → Set (Set α)}
    {γ β : Type} {encL : γ ↪ List Bool} {encB : β ↪ List Bool} {κB : β → ℕ}
    {L : Set γ} {B : Set β} (hL : PolyTimeHard 𝒞 encL L) (K : ℕ)
    (r : γ → β) (hr : ComputableInPolyTime r encL encB) (hK : ∀ c, κB (r c) ≤ K)
    (hrB : ∀ c, c ∈ L ↔ r c ∈ B) : ParaHard 𝒞 encB κB B := by
  refine ParaHard.of_slice_hard K fun α encA A hA ↦ ?_
  obtain ⟨s, hs, hsL⟩ := hL encA A hA
  exact ⟨r ∘ s, hr.comp hs, fun a ↦ hK (s a), fun a ↦ (hsL a).trans (hrB (s a))⟩

end Para

/-! ### Slicewise polynomial computability and `XNP` -/

section XNP

/-- **Slicewise polynomial-time computability** (`XP`-time functions): `f` is computed within
time and space `F (κ a) * (|encA a| + 1) ^ G (κ a)` up to a constant factor. -/
def ComputableInXPTime {α β : Type} (f : α → β) (encA : α ↪ List Bool) (encB : β ↪ List Bool)
    (κ : α → ℕ) : Prop :=
  ∃ F G : ℕ → ℕ, ComputableInO f encA encB
    (fun a ↦ F (κ a) * ((encA a).length + 1) ^ G (κ a))
    (fun a ↦ F (κ a) * ((encA a).length + 1) ^ G (κ a))

/-- Every polynomial-time computable function is computable in `XP` time for every parameter. -/
theorem computableInXPTime_of_polyTime {α β : Type} {f : α → β} {encA : α ↪ List Bool}
    {encB : β ↪ List Bool} (hf : ComputableInPolyTime f encA encB) (κ : α → ℕ) :
    ComputableInXPTime f encA encB κ :=
  let ⟨d, _, hd⟩ := hf.exists_degree
  ⟨fun _ ↦ 1, fun _ ↦ d,
    hd.inO.mono_le (fun _ ↦ (one_mul _).ge) (fun _ ↦ (one_mul _).ge)⟩

/-- Every fpt-time computable function is computable in `XP` time. -/
theorem computableInXPTime_of_fptTime {α β : Type} {f : α → β} {encA : α ↪ List Bool}
    {encB : β ↪ List Bool} {κ : α → ℕ} (hf : ComputableInFPTTime f encA encB κ) :
    ComputableInXPTime f encA encB κ :=
  let ⟨F, c, hc⟩ := hf
  ⟨F, fun _ ↦ c, .of_bounds hc 1 (fun _ ↦ by dsimp only; omega) (fun _ ↦ by dsimp only; omega)
    fun a ↦ (hc.length_le a).trans (by dsimp only; omega)⟩

/-- **The class `XNP`** [de Haan and Szeider; Flum and Grohe ]: parameterized decision
problems verifiable nondeterministically in slicewise polynomial time, i.e., with a certificate
of length at most `F (κ a) * (|enc a| + 1) ^ G (κ a)` verified in `XP` time.
-/
def XNP {α : Type} (enc : α ↪ List Bool) (κ : α → ℕ) : Set (Set α) :=
  {A | ∃ (V : α × List Bool → Bool) (F G : ℕ → ℕ),
    ComputableInXPTime V (encPair enc encBits) encBool (fun p ↦ κ p.1) ∧
    ∀ a, a ∈ A ↔ ∃ w : List Bool, w.length ≤ F (κ a) * ((enc a).length + 1) ^ G (κ a) ∧
      V (a, w) = true}

/-- Membership characterization for `XNP`. -/
theorem mem_XNP_iff {α : Type} {enc : α ↪ List Bool} {κ : α → ℕ} {A : Set α} :
    A ∈ XNP enc κ ↔ ∃ (V : α × List Bool → Bool) (F G : ℕ → ℕ),
      ComputableInXPTime V (encPair enc encBits) encBool (fun p ↦ κ p.1) ∧
      ∀ a, a ∈ A ↔ ∃ w : List Bool, w.length ≤ F (κ a) * ((enc a).length + 1) ^ G (κ a) ∧
        V (a, w) = true :=
  Iff.rfl

/-- **`XP ⊆ XNP`**: every slicewise polynomial-time decidable problem lies in `XNP`. -/
theorem XP_subset_XNP {α : Type} {enc : α ↪ List Bool} {κ : α → ℕ} :
    XP enc κ ⊆ XNP enc κ := by
  intro A hA
  obtain ⟨g, F, G, hg, hgA⟩ := mem_XP_iff_exists_computableInO.mp hA
  have hV : ComputableInXPTime (fun p : α × List Bool ↦ g p.1)
      (encPair enc encBits) encBool (fun p ↦ κ p.1) := by
    have hfst : ComputableInO (Prod.fst : α × List Bool → α) (encPair enc encBits) enc
        (fun p ↦ (encPair enc encBits p).length) (fun p ↦ (encPair enc encBits p).length) :=
      ComputableInO.of_linear (ComputableInDegree.fst' ComputableInDegree.id')
    have hcomp := hg.comp hfst
    refine ⟨fun k ↦ F k + 1, fun k ↦ G k + 1, hcomp.mono_le (fun p ↦ ?_) (fun p ↦ ?_)⟩
    all_goals
      dsimp only
      have hlen : (enc p.1).length ≤ (encPair enc encBits p).length :=
        length_le_encPair_left enc encBits p
      have h1 : ((enc p.1).length + 1) ^ G (κ p.1) ≤
          ((encPair enc encBits p).length + 1) ^ (G (κ p.1) + 1) :=
        (Nat.pow_le_pow_left (Nat.add_le_add_right hlen 1) _).trans
          (Nat.pow_le_pow_right (Nat.succ_pos _) (Nat.le_succ _))
      have h2 : (encPair enc encBits p).length ≤
          ((encPair enc encBits p).length + 1) ^ (G (κ p.1) + 1) :=
        (Nat.le_succ _).trans (Nat.le_self_pow (Nat.succ_ne_zero _) _)
      have h3 := Nat.mul_le_mul_left (F (κ p.1)) h1
      rw [Nat.add_mul, Nat.one_mul]
      omega
  exact ⟨fun p ↦ g p.1, fun _ ↦ 0, fun _ ↦ 0, hV, fun a ↦ by
    rw [hgA a]
    exact ⟨fun h ↦ ⟨[], by simp, h⟩, fun ⟨_, _, h⟩ ↦ h⟩⟩

/-- **`NP ⊆ XNP`** for every parameter. -/
theorem NP_subset_XNP {α : Type} {enc : α ↪ List Bool} {κ : α → ℕ} :
    NP enc ⊆ XNP enc κ := by
  intro A ⟨p, V, hV, hAV⟩
  let c : ℕ := ∑ i ∈ p.support, p.coeff i
  let d : ℕ := p.natDegree
  have hp : ∀ n : ℕ, p.eval n ≤ c * (n + 1) ^ d := fun n ↦ by
    rw [Polynomial.eval_eq_sum]
    calc ∑ i ∈ p.support, p.coeff i * n ^ i
        ≤ ∑ i ∈ p.support, p.coeff i * (n + 1) ^ d := by
          refine Finset.sum_le_sum fun i hi ↦ Nat.mul_le_mul_left _ ?_
          exact (Nat.pow_le_pow_left (Nat.le_succ n) i).trans
            (Nat.pow_le_pow_right (Nat.succ_pos n) (Polynomial.le_natDegree_of_mem_supp i hi))
      _ = c * (n + 1) ^ d := by rw [← Finset.sum_mul]
  let V' : α × List Bool → Bool := fun x ↦
    decide (x.2.length = p.eval (enc x.1).length) && V x
  have hV' : ComputableInPolyTime V' (encPair enc encBits) encBool := by
    unfold V'
    fun_prop
  refine ⟨V', fun _ ↦ c, fun _ ↦ d, computableInXPTime_of_polyTime hV' _, fun a ↦ ?_⟩
  rw [hAV a]
  constructor
  · rintro ⟨w, hw, hVw⟩
    exact ⟨w, hw.le.trans (hp _), by simp [V', hw, hVw]⟩
  · rintro ⟨w, _, hVw⟩
    simp only [V', Bool.and_eq_true, decide_eq_true_eq] at hVw
    exact ⟨w, hVw.1, hVw.2⟩

end XNP

/-! ### Parameterized counting classes (`#W[t]`, `para-#P`) -/

section Counting

/-- **Counting weighted circuit satisfiability `#WCS[t, d]`**: the number of satisfying inputs of
Hamming weight `x.weight` for the bounded-weft, bounded-depth circuit `x.circuit`. -/
def SharpWCS (t d : ℕ) (x : WCSInstance t d) : ℕ :=
  (Finset.univ.filter fun w : BitString x.circuit.toCircuit.1 ↦
    BitString.weight w = x.weight ∧
      x.circuit.toCircuit.2.eval Unbounded.interpretation w 0 = true).card

/-- **Counting weighted circuit satisfiability (unbounded weft and depth)**: the number of
satisfying inputs of Hamming weight `x.weight` for `x.circuit`. -/
def SharpWeightedCircuitSAT (x : WeightedCircuitSATInstance) : ℕ :=
  (Finset.univ.filter fun w : BitString x.circuit.1 ↦
    BitString.weight w = x.weight ∧
      x.circuit.2.eval Unbounded.interpretation w 0 = true).card

/-- **FPT parsimonious reduction** between parameterized counting problems [Flum and Grohe ]:
an fpt-time map bounding the target parameter that preserves counts exactly.
-/
def FPTParsimoniousReducible {α β : Type} (encA : α ↪ List Bool) (encB : β ↪ List Bool)
    (κA : α → ℕ) (κB : β → ℕ) (f : α → ℕ) (g : β → ℕ) : Prop :=
  ∃ r : α → β, ComputableInFPTWithParam encA encB κA κB r ∧ ∀ a, f a = g (r a)

/-- **FPT metric reduction** between parameterized functions: an fpt-time query map `r` (bounding
the parameter) and an fpt-time recovery map `post` such that `f a = post (a, g (r a))`. -/
def FPTMetricReducible {α β Y Z : Type} (encA : α ↪ List Bool) (encB : β ↪ List Bool)
    (encY : Y ↪ List Bool) (encZ : Z ↪ List Bool) (κA : α → ℕ) (κB : β → ℕ)
    (f : α → Y) (g : β → Z) : Prop :=
  ∃ (r : α → β) (post : α × Z → Y),
    ComputableInFPTWithParam encA encB κA κB r ∧
    ComputableInFPTTime post (encPair encA encZ) encY (fun p ↦ κA p.1) ∧
    ∀ a, f a = post (a, g (r a))

/-- **The class `#W[t]`** [Flum and Grohe ]: parameterized counting problems that
fpt-parsimoniously reduce to `#WCS[t, d]` for some constant depth `d`.
-/
def SharpW (t : ℕ) {α : Type} (enc : α ↪ List Bool) (κ : α → ℕ) : Set (α → ℕ) :=
  {f | ∃ d, FPTParsimoniousReducible enc (encWCS t d) κ WCSInstance.weight f (SharpWCS t d)}

/-- **`#W[t]`-hardness** under FPT parsimonious reductions. -/
def SharpWHard (t : ℕ) {β : Type} (encB : β ↪ List Bool) (κB : β → ℕ) (g : β → ℕ) : Prop :=
  ∀ ⦃α : Type⦄ (encA : α ↪ List Bool) (κA : α → ℕ) (f : α → ℕ),
    f ∈ SharpW t encA κA → FPTParsimoniousReducible encA encB κA κB f g

/-- **`#W[t]`-completeness** under FPT parsimonious reductions. -/
def SharpWComplete (t : ℕ) {β : Type} (encB : β ↪ List Bool) (κB : β → ℕ) (g : β → ℕ) : Prop :=
  g ∈ SharpW t encB κB ∧ SharpWHard t encB κB g

/-- **The metric class `#W_m[t]`**: parameterized functions fpt-metric-reducible to
`#WCS[t, d]` for some constant depth `d`. -/
def SharpWMetric (t : ℕ) {α Y : Type} (enc : α ↪ List Bool) (encY : Y ↪ List Bool)
    (κ : α → ℕ) : Set (α → Y) :=
  {f | ∃ d, FPTMetricReducible enc (encWCS t d) encY encNat κ WCSInstance.weight f (SharpWCS t d)}

/-- **`#W[t]`-hardness under FPT metric reductions**: every problem in `#W[t]` reduces to `g`
by an FPT metric reduction. -/
def SharpWMetricHard (t : ℕ) {β Z : Type} (encB : β ↪ List Bool) (encZ : Z ↪ List Bool)
    (κB : β → ℕ) (g : β → Z) : Prop :=
  ∀ ⦃α : Type⦄ (encA : α ↪ List Bool) (κA : α → ℕ) (f : α → ℕ),
    f ∈ SharpW t encA κA → FPTMetricReducible encA encB encNat encZ κA κB f g

/-- **`para-#P`-hardness (metric)**: some constant-parameter slice of `g` is `#P`-hard under
polynomial-time metric reductions. -/
def ParaSharpPHard {β Z : Type} (encB : β ↪ List Bool) (encZ : Z ↪ List Bool)
    (κB : β → ℕ) (g : β → Z) : Prop :=
  ∃ K : ℕ, ∀ ⦃α : Type⦄ (encA : α ↪ List Bool) (f : α → ℕ), f ∈ SharpP encA →
    ∃ (r : α → β) (post : α × Z → ℕ),
      ComputableInPolyTime r encA encB ∧
      ComputableInPolyTime post (encPair encA encZ) encNat ∧
      (∀ a, κB (r a) ≤ K) ∧
      ∀ a, f a = post (a, g (r a))

/-- **`para-#P`-completeness (parsimonious)**: `g` lies in `#P` and has a constant-parameter
slice that is `#P`-hard under polynomial-time parsimonious reductions. -/
def ParaSharpPComplete {β : Type} (encB : β ↪ List Bool) (κB : β → ℕ) (g : β → ℕ) : Prop :=
  g ∈ SharpP encB ∧
    ∃ K : ℕ, ∀ ⦃α : Type⦄ (encA : α ↪ List Bool) (f : α → ℕ), f ∈ SharpP encA →
      ∃ r : α → β, ComputableInPolyTime r encA encB ∧ (∀ a, κB (r a) ≤ K) ∧
        ∀ a, f a = g (r a)

/-- FPT parsimonious reductions are reflexive. -/
@[refl]
theorem FPTParsimoniousReducible.refl {α : Type} (encA : α ↪ List Bool) (κA : α → ℕ)
    (f : α → ℕ) : FPTParsimoniousReducible encA encA κA κA f f :=
  ⟨id, ⟨ComputableInPolyTime.id'.computableInFPTTime κA, id, fun _ ↦ le_rfl⟩, fun _ ↦ rfl⟩

/-- FPT parsimonious reductions compose. -/
@[trans]
theorem FPTParsimoniousReducible.trans {α β γ : Type} {encA : α ↪ List Bool}
    {encB : β ↪ List Bool} {encC : γ ↪ List Bool} {κA : α → ℕ} {κB : β → ℕ} {κC : γ → ℕ}
    {f : α → ℕ} {g : β → ℕ} {h : γ → ℕ}
    (hfg : FPTParsimoniousReducible encA encB κA κB f g)
    (hgh : FPTParsimoniousReducible encB encC κB κC g h) :
    FPTParsimoniousReducible encA encC κA κC f h := by
  obtain ⟨r, ⟨hr, h₁, hκ₁⟩, hfg'⟩ := hfg
  obtain ⟨s, ⟨hs, h₂, hκ₂⟩, hgh'⟩ := hgh
  refine ⟨s ∘ r, ⟨hs.comp hr hκ₁,
    fun k ↦ ∑ j ∈ Finset.range (h₁ k + 1), h₂ j,
    fun a ↦ (hκ₂ (r a)).trans (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le (hκ₁ a))))⟩,
    fun a ↦ (hfg' a).trans (hgh' (r a))⟩

/-- FPT parsimonious reductions are FPT metric reductions. -/
theorem FPTParsimoniousReducible.fptMetricReducible {α β : Type} {encA : α ↪ List Bool}
    {encB : β ↪ List Bool} {κA : α → ℕ} {κB : β → ℕ} {f : α → ℕ} {g : β → ℕ}
    (h : FPTParsimoniousReducible encA encB κA κB f g) :
    FPTMetricReducible encA encB encNat encNat κA κB f g :=
  let ⟨r, hr, hfg⟩ := h
  ⟨r, Prod.snd, hr, (ComputableInPolyTime.snd encA encNat).computableInFPTTime _, hfg⟩

/-- **Polynomial upper bound on `#WCS[t, d]`**: a circuit on `n` inputs has at most `(n + 1) ^ k`
satisfying assignments of Hamming weight `k`. -/
theorem sharpWCS_le_pow (t d : ℕ) (x : WCSInstance t d) :
    SharpWCS t d x ≤ (x.circuit.toCircuit.1 + 1) ^ x.weight := by
  classical
  let n := x.circuit.toCircuit.1
  let k := x.weight
  let S : Finset (BitString n) := Finset.univ.filter fun w ↦
    BitString.weight w = k ∧
      x.circuit.toCircuit.2.eval Unbounded.interpretation w 0 = true
  have hsub : S.card ≤ (Finset.univ.filter fun w : BitString n ↦ BitString.weight w = k).card :=
    Finset.card_le_card fun w hw ↦ by
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
      exact hw.1
  refine hsub.trans ?_
  -- Map each `w : BitString n` of weight `k` injectively to a `k`-tuple in `Fin (n + 1)`
  -- by listing the indices where `w i = true` and padding; or simply note `#(weight = k) = n.choose
  -- k`.
  have hcard :
      (Finset.univ.filter fun w : BitString n ↦ BitString.weight w = k).card ≤ (n + 1) ^ k := by
    have hbij :
        (Finset.univ.filter fun w : BitString n ↦ BitString.weight w = k).card = n.choose k := by
      have heq :
          (Finset.univ.filter fun w : BitString n ↦ BitString.weight w = k).card =
            (Finset.powersetCard k (Finset.univ : Finset (Fin n))).card := by
        refine Finset.card_bij (fun w _ ↦ Finset.univ.filter fun i : Fin n ↦ w i = true)
          (fun w hw ↦ ?_) (fun w₁ _ w₂ _ h ↦ ?_) (fun s hs ↦ ?_)
        · simp only [Finset.mem_powersetCard, Finset.subset_univ, true_and]
          simpa [BitString.weight] using (Finset.mem_filter.mp hw).2
        · funext i
          have := Finset.ext_iff.mp h i
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
          exact Bool.eq_iff_iff.mpr this
        · refine ⟨fun i ↦ decide (i ∈ s), ?_, ?_⟩
          · rw [Finset.mem_filter]
            refine ⟨Finset.mem_univ _, ?_⟩
            simpa [BitString.weight] using (Finset.mem_powersetCard.mp hs).2
          · ext i; simp
      rw [heq, Finset.card_powersetCard, Finset.card_fin]
    rw [hbij]
    calc n.choose k ≤ n ^ k := Nat.choose_le_pow n k
      _ ≤ (n + 1) ^ k := Nat.pow_le_pow_left (Nat.le_succ n) k
  exact hcard

/-- **Polynomial upper bound on `SharpWeightedCircuitSAT`**: at most `(n + 1) ^ k` solutions. -/
theorem sharpWeightedCircuitSAT_le_pow (x : WeightedCircuitSATInstance) :
    SharpWeightedCircuitSAT x ≤ (x.circuit.1 + 1) ^ x.weight := by
  classical
  have hsub : SharpWeightedCircuitSAT x ≤
      (Finset.univ.filter fun w : BitString x.circuit.1 ↦ BitString.weight w = x.weight).card :=
    Finset.card_le_card fun w hw ↦ by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
      exact hw.1
  refine hsub.trans ?_
  have heq :
      (Finset.univ.filter fun w : BitString x.circuit.1 ↦ BitString.weight w = x.weight).card =
        (Finset.powersetCard x.weight (Finset.univ : Finset (Fin x.circuit.1))).card := by
    refine Finset.card_bij (fun w _ ↦ Finset.univ.filter fun i : Fin x.circuit.1 ↦ w i = true)
      (fun w hw ↦ ?_) (fun w₁ _ w₂ _ h ↦ ?_) (fun s hs ↦ ?_)
    · simp only [Finset.mem_powersetCard, Finset.subset_univ, true_and]
      simpa [BitString.weight] using (Finset.mem_filter.mp hw).2
    · funext i
      have := Finset.ext_iff.mp h i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
      exact Bool.eq_iff_iff.mpr this
    · refine ⟨fun i ↦ decide (i ∈ s), ?_, ?_⟩
      · rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        simpa [BitString.weight] using (Finset.mem_powersetCard.mp hs).2
      · ext i; simp
  rw [heq, Finset.card_powersetCard, Finset.card_fin]
  exact (Nat.choose_le_pow _ _).trans (Nat.pow_le_pow_left (Nat.le_succ _) _)

/-- Helper: `2 ^ n` eventually outgrows `C * (n + 1) ^ E` for every `C, E : ℕ`. -/
private theorem exists_pow_lt_two_pow (C E : ℕ) : ∃ n : ℕ, C * (n + 1) ^ E < 2 ^ n := by
  have hquad : ∀ t : ℕ, 5 ≤ t → t * t < 2 ^ t := by
    intro t ht
    induction t, ht using Nat.le_induction with
    | base => decide
    | succ t ht ih =>
      rw [Nat.pow_succ]
      have : 2 * t + 1 < t * t := by nlinarith
      nlinarith
  have hlin : ∀ k : ℕ, ∃ m : ℕ, k * (m + 1) < 2 ^ m := by
    intro k
    refine ⟨2 * k + 5, ?_⟩
    have hq := hquad (2 * k + 5) (by omega)
    exact (by nlinarith : k * (2 * k + 5 + 1) < (2 * k + 5) * (2 * k + 5)).trans hq
  obtain ⟨m, hm⟩ := hlin (max (C + 1) (E + 2))
  have hmC : (C + 1) * (m + 1) < 2 ^ m :=
    (Nat.mul_le_mul_right _ (le_max_left _ _)).trans_lt hm
  have hmE : (E + 2) * (m + 1) < 2 ^ m :=
    (Nat.mul_le_mul_right _ (le_max_right _ _)).trans_lt hm
  refine ⟨(E + 1) * m, ?_⟩
  have h1 : (E + 1) * m + 1 ≤ (E + 2) * (m + 1) := by nlinarith
  have h2 : ((E + 1) * m + 1) ^ E ≤ (2 ^ m) ^ E :=
    Nat.pow_le_pow_left (h1.trans hmE.le) E
  have hC : C < 2 ^ m := (Nat.le_mul_of_pos_right _ (Nat.succ_pos m)).trans_lt
    ((Nat.mul_le_mul_right _ (Nat.le_succ C)).trans_lt hmC)
  calc C * ((E + 1) * m + 1) ^ E
      < 2 ^ m * (2 ^ m) ^ E :=
        (Nat.mul_lt_mul_of_pos_right hC (Nat.pow_pos (Nat.succ_pos _))).trans_le
          (Nat.mul_le_mul_left _ h2)
    _ = 2 ^ ((E + 1) * m) := by
        rw [← Nat.pow_mul, ← Nat.pow_add]
        congr 1; ring

/-- **Unconditional non-membership in `#W[t]` (parsimonious)**: if a counting function `f` has a
family of instances with parameter bounded by `K`, encoding length bounded by `C * (n + 1) ^ e`,
and values at least `2 ^ n`, then `f ∉ SharpW t enc κ` for every `t`. -/
theorem not_mem_sharpW_of_two_pow_le {α : Type} {enc : α ↪ List Bool} {κ : α → ℕ} {f : α → ℕ}
    (t : ℕ) (K C e : ℕ) (a : ℕ → α)
    (hκ : ∀ n, κ (a n) ≤ K)
    (hlen : ∀ n, (enc (a n)).length ≤ C * (n + 1) ^ e)
    (hf : ∀ n, 2 ^ n ≤ f (a n)) : f ∉ SharpW t enc κ := by
  rintro ⟨d, r, ⟨⟨F, c, hr⟩, hparam, hbound⟩, hpres⟩
  let M : ℕ := ∑ j ∈ Finset.range (K + 1), F j
  let W : ℕ := ∑ j ∈ Finset.range (K + 1), hparam j
  have hM : ∀ n, F (κ (a n)) ≤ M := fun n ↦
    Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_range.mpr (Nat.lt_succ_of_le (hκ n)))
  have hW : ∀ n, (r (a n)).weight ≤ W := fun n ↦
    (hbound (a n)).trans (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le (hκ n))))
  -- Bound `(r (a n)).circuit.toCircuit.1` by `(encWCS t d (r (a n))).length`.
  have hnum_le_enc (x : WCSInstance t d) : x.circuit.toCircuit.1 ≤ (encWCS t d x).length := by
    rw [encWCS_apply]
    refine (Circuit.le_length_encCircuit Unbounded.encOp x.circuit.toCircuit).trans ?_
    change (encWeftCircuit t d x.circuit).length ≤
      (encPair (encWeftCircuit t d) encNat (x.circuit, x.weight)).length
    exact length_le_encPair_left (encWeftCircuit t d) encNat (x.circuit, x.weight)
  -- Bound `(encWCS t d (r (a n))).length` by a polynomial in `n + 1`.
  have hlen_r (n : ℕ) :
      (encWCS t d (r (a n))).length ≤ M * ((C + 1) * (n + 1) ^ e) ^ c + 1 := by
    have h1 := hr.length_le (a n)
    have h2 : (enc (a n)).length + 1 ≤ (C + 1) * (n + 1) ^ e := by
      have hp : 1 ≤ (n + 1) ^ e := Nat.one_le_pow e _ (Nat.succ_pos n)
      calc (enc (a n)).length + 1 ≤ C * (n + 1) ^ e + (n + 1) ^ e := Nat.add_le_add (hlen n) hp
        _ = (C + 1) * (n + 1) ^ e := by rw [Nat.add_mul, Nat.one_mul]
    have h3 := Nat.mul_le_mul (hM n) (Nat.pow_le_pow_left h2 c)
    exact h1.trans (h3.trans (Nat.le_succ _))
  -- Combine with `sharpWCS_le_pow` to get `2 ^ n ≤ D * (n + 1) ^ E`.
  let B : ℕ := M * (C + 1) ^ c + 2
  have hpoly (n : ℕ) : (r (a n)).circuit.toCircuit.1 + 1 ≤ B * (n + 1) ^ (e * c) := by
    have h1 := (hnum_le_enc (r (a n))).trans (hlen_r n)
    rw [Nat.mul_pow, ← Nat.pow_mul, ← Nat.mul_assoc] at h1
    have hp : 1 ≤ (n + 1) ^ (e * c) := Nat.one_le_pow _ _ (Nat.succ_pos n)
    calc (r (a n)).circuit.toCircuit.1 + 1
        ≤ M * (C + 1) ^ c * (n + 1) ^ (e * c) + 2 := Nat.add_le_add_right h1 1
      _ ≤ M * (C + 1) ^ c * (n + 1) ^ (e * c) + 2 * (n + 1) ^ (e * c) :=
          Nat.add_le_add_left (by simpa [two_mul] using Nat.add_le_add hp hp) _
      _ = B * (n + 1) ^ (e * c) := by rw [← Nat.add_mul]
  obtain ⟨n₀, hn₀⟩ := exists_pow_lt_two_pow (B ^ W) (e * c * W)
  have hup : 2 ^ n₀ ≤ B ^ W * (n₀ + 1) ^ (e * c * W) := by
    calc 2 ^ n₀ ≤ f (a n₀) := hf n₀
      _ = SharpWCS t d (r (a n₀)) := hpres (a n₀)
      _ ≤ ((r (a n₀)).circuit.toCircuit.1 + 1) ^ (r (a n₀)).weight := sharpWCS_le_pow t d _
      _ ≤ ((r (a n₀)).circuit.toCircuit.1 + 1) ^ W :=
          Nat.pow_le_pow_right (Nat.succ_pos _) (hW n₀)
      _ ≤ (B * (n₀ + 1) ^ (e * c)) ^ W := Nat.pow_le_pow_left (hpoly n₀) W
      _ = B ^ W * (n₀ + 1) ^ (e * c * W) := by rw [Nat.mul_pow, ← Nat.pow_mul]
  exact Nat.not_lt.mpr hup hn₀

/-- **Unconditional non-reducibility to `SharpWeightedCircuitSAT` (parsimonious)**: same
super-polynomial growth obstruction against unbounded-weft/depth `#W[P]` circuits. -/
theorem not_parsimonious_sharpWeightedCircuitSAT_of_two_pow_le {α : Type} {enc : α ↪ List Bool}
    {κ : α → ℕ} {f : α → ℕ} (K C e : ℕ) (a : ℕ → α)
    (hκ : ∀ n, κ (a n) ≤ K)
    (hlen : ∀ n, (enc (a n)).length ≤ C * (n + 1) ^ e)
    (hf : ∀ n, 2 ^ n ≤ f (a n)) :
    ¬ FPTParsimoniousReducible enc encWeightedCircuitSAT κ WeightedCircuitSATInstance.weight
        f SharpWeightedCircuitSAT := by
  rintro ⟨r, ⟨⟨F, c, hr⟩, hparam, hbound⟩, hpres⟩
  let M : ℕ := ∑ j ∈ Finset.range (K + 1), F j
  let W : ℕ := ∑ j ∈ Finset.range (K + 1), hparam j
  have hM : ∀ n, F (κ (a n)) ≤ M := fun n ↦
    Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_range.mpr (Nat.lt_succ_of_le (hκ n)))
  have hW : ∀ n, (r (a n)).weight ≤ W := fun n ↦
    (hbound (a n)).trans (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le (hκ n))))
  have hnum_le_enc (x : WeightedCircuitSATInstance) :
      x.circuit.1 ≤ (encWeightedCircuitSAT x).length := by
    rw [encWeightedCircuitSAT_apply]
    refine (Circuit.le_length_encCircuit Unbounded.encOp x.circuit).trans ?_
    change (Unbounded.encCircuit 1 x.circuit).length ≤
      (encPair (Unbounded.encCircuit 1) encNat (x.circuit, x.weight)).length
    exact length_le_encPair_left (Unbounded.encCircuit 1) encNat (x.circuit, x.weight)
  have hlen_r (n : ℕ) :
      (encWeightedCircuitSAT (r (a n))).length ≤ M * ((C + 1) * (n + 1) ^ e) ^ c + 1 := by
    have h1 := hr.length_le (a n)
    have h2 : (enc (a n)).length + 1 ≤ (C + 1) * (n + 1) ^ e := by
      have hp : 1 ≤ (n + 1) ^ e := Nat.one_le_pow e _ (Nat.succ_pos n)
      calc (enc (a n)).length + 1 ≤ C * (n + 1) ^ e + (n + 1) ^ e := Nat.add_le_add (hlen n) hp
        _ = (C + 1) * (n + 1) ^ e := by rw [Nat.add_mul, Nat.one_mul]
    have h3 := Nat.mul_le_mul (hM n) (Nat.pow_le_pow_left h2 c)
    exact h1.trans (h3.trans (Nat.le_succ _))
  let B : ℕ := M * (C + 1) ^ c + 2
  have hpoly (n : ℕ) : (r (a n)).circuit.1 + 1 ≤ B * (n + 1) ^ (e * c) := by
    have h1 := (hnum_le_enc (r (a n))).trans (hlen_r n)
    rw [Nat.mul_pow, ← Nat.pow_mul, ← Nat.mul_assoc] at h1
    have hp : 1 ≤ (n + 1) ^ (e * c) := Nat.one_le_pow _ _ (Nat.succ_pos n)
    calc (r (a n)).circuit.1 + 1
        ≤ M * (C + 1) ^ c * (n + 1) ^ (e * c) + 2 := Nat.add_le_add_right h1 1
      _ ≤ M * (C + 1) ^ c * (n + 1) ^ (e * c) + 2 * (n + 1) ^ (e * c) :=
          Nat.add_le_add_left (by simpa [two_mul] using Nat.add_le_add hp hp) _
      _ = B * (n + 1) ^ (e * c) := by rw [← Nat.add_mul]
  obtain ⟨n₀, hn₀⟩ := exists_pow_lt_two_pow (B ^ W) (e * c * W)
  have hup : 2 ^ n₀ ≤ B ^ W * (n₀ + 1) ^ (e * c * W) := by
    calc 2 ^ n₀ ≤ f (a n₀) := hf n₀
      _ = SharpWeightedCircuitSAT (r (a n₀)) := hpres (a n₀)
      _ ≤ ((r (a n₀)).circuit.1 + 1) ^ (r (a n₀)).weight := sharpWeightedCircuitSAT_le_pow _
      _ ≤ ((r (a n₀)).circuit.1 + 1) ^ W :=
          Nat.pow_le_pow_right (Nat.succ_pos _) (hW n₀)
      _ ≤ (B * (n₀ + 1) ^ (e * c)) ^ W := Nat.pow_le_pow_left (hpoly n₀) W
      _ = B ^ W * (n₀ + 1) ^ (e * c * W) := by rw [Nat.mul_pow, ← Nat.pow_mul]
  exact Nat.not_lt.mpr hup hn₀

end Counting

end Cslib.Complexity
