module

public import CslibFrontier.Computability.Complexity.Classes.DP
public import CslibFrontier.Computability.Complexity.Parameterized.Hardness
public import CslibFrontier.Computability.Complexity.Parameterized.WHierarchy
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic

/-!
# Parameterized Classical Complexity Classes (`para-C`) and `coW[t]`

This module defines the parameterized classical complexity classes `Para 𝒞` (instantiated as
`paraNP`, `paraCoNP`, `paraDP`, `paraCoDP`) and the complementary weft hierarchy `coW t`, together
with their FPT-hardness notions and transfer lemmas.

## Main definitions

- `Para`: the parameterized class `para-𝒞` for any classical class `𝒞`.
- `paraNP`, `paraCoNP`, `paraDP`, `paraCoDP`: `para-NP`, `para-coNP`, `para-DP`, `para-coDP`.
- `paraNPHard`, `paraCoNPHard`, `paraDPHard`, `paraCoDPHard`: FPT-hardness for `para-𝒞`.
- `coW`, `coWHard`: complementary weft hierarchy `coW[t]` and `coW[t]`-hardness.

## Main results

- `paraHard_of_polyTime_const_param`: a polynomial-time reduction from a `𝒞`-hard problem whose
  output parameter is bounded by a constant yields `para-𝒞`-hardness.
- `coWHard_iff_wHard_compl`: `coW[t]`-hardness of `B` is equivalent to `W[t]`-hardness of `Bᶜ`.
- `paraCoDPHard_iff_paraDPHard_compl`, `paraCoNPHard_iff_paraNPHard_compl`,
  `paraNPHard_iff_paraCoNPHard_compl`: complement duality for `para-𝒞`-hardness.
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

/-! ### Parameterized classical classes `para-C` -/

/-- The parameterized classical complexity class `para-𝒞`: a parameterized problem `(A, κ)`
belongs to `Para 𝒞` iff there exist a parameter precomputation `f : ℕ → List Bool` (such that
`a ↦ (a, f (κ a))` is computable in FPT time) and a language `L ∈ 𝒞` such that
`a ∈ A ↔ (a, f (κ a)) ∈ L`. -/
@[expose]
def Para (𝒞 : ∀ {α : Type}, (α ↪ List Bool) → Set (Set α))
    {α : Type} (enc : α ↪ List Bool) (κ : α → ℕ) : Set (Set α) :=
  {A | ∃ (f : ℕ → List Bool) (L : Set (α × List Bool)),
    ComputableInFPTTime (fun a => (a, f (κ a))) enc (encPair enc encBits) κ ∧
    L ∈ 𝒞 (encPair enc encBits) ∧
    ∀ a, a ∈ A ↔ (a, f (κ a)) ∈ L}

/-- The parameterized class `para-NP`. -/
abbrev paraNP {α : Type} (enc : α ↪ List Bool) (κ : α → ℕ) : Set (Set α) :=
  Para @NP enc κ

/-- The parameterized class `para-coNP`. -/
abbrev paraCoNP {α : Type} (enc : α ↪ List Bool) (κ : α → ℕ) : Set (Set α) :=
  Para @coNP enc κ

/-- The parameterized class `para-DP`. -/
abbrev paraDP {α : Type} (enc : α ↪ List Bool) (κ : α → ℕ) : Set (Set α) :=
  Para @DP enc κ

/-- The parameterized class `para-coDP`. -/
abbrev paraCoDP {α : Type} (enc : α ↪ List Bool) (κ : α → ℕ) : Set (Set α) :=
  Para @coDP enc κ

/-- `para-NP`-hardness under FPT-reductions. -/
abbrev paraNPHard {β : Type} (enc : β ↪ List Bool) (κ : β → ℕ) (B : Set β) : Prop :=
  FPTHard @paraNP enc κ B

/-- `para-coNP`-hardness under FPT-reductions. -/
abbrev paraCoNPHard {β : Type} (enc : β ↪ List Bool) (κ : β → ℕ) (B : Set β) : Prop :=
  FPTHard @paraCoNP enc κ B

/-- `para-DP`-hardness under FPT-reductions. -/
abbrev paraDPHard {β : Type} (enc : β ↪ List Bool) (κ : β → ℕ) (B : Set β) : Prop :=
  FPTHard @paraDP enc κ B

/-- `para-coDP`-hardness under FPT-reductions. -/
abbrev paraCoDPHard {β : Type} (enc : β ↪ List Bool) (κ : β → ℕ) (B : Set β) : Prop :=
  FPTHard @paraCoDP enc κ B

/-- **Slice-hardness criterion for `para-𝒞`**: a polynomial-time reduction from a `𝒞`-hard
problem `A₀` to `B` whose output parameter is bounded by a constant `c` proves `B` is
`para-𝒞`-hard. -/
theorem paraHard_of_polyTime_const_param
    {𝒞 : ∀ {α : Type}, (α ↪ List Bool) → Set (Set α)}
    {α β : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool}
    {κB : β → ℕ} {A₀ : Set α} {B : Set β}
    (hA₀ : PolyTimeHard 𝒞 encA A₀)
    {r : α → β} (hr : ComputableInPolyTime r encA encB)
    (hAB : ∀ a, a ∈ A₀ ↔ r a ∈ B)
    {c : ℕ} (hc : ∀ a, κB (r a) ≤ c) :
    FPTHard (Para 𝒞) encB κB B := by
  intro γ encG κG P hP
  obtain ⟨f, L, hf, hL, hPL⟩ := hP
  obtain ⟨g, hg, hLg⟩ := hA₀ (encPair encG encBits) L hL
  refine ⟨fun x => r (g (x, f (κG x))),
    ⟨(hr.comp hg).computableInFPTTime (fun _ => 0) |>.comp hf (h := fun _ => 0) (fun _ => le_rfl),
      fun _ => c, fun x => hc (g (x, f (κG x)))⟩,
    fun x => (hPL x).trans ((hLg _).trans (hAB _))⟩

/-- Complement duality for `Para`: when `𝒞'` is the complement class of `𝒞`,
`A ∈ Para 𝒞'` iff `Aᶜ ∈ Para 𝒞`. -/
theorem mem_Para_compl_iff
    {𝒞 𝒞' : ∀ {α : Type}, (α ↪ List Bool) → Set (Set α)}
    (hcompl : ∀ {α : Type} (enc : α ↪ List Bool) (L : Set α), L ∈ 𝒞' enc ↔ Lᶜ ∈ 𝒞 enc)
    {α : Type} {enc : α ↪ List Bool} {κ : α → ℕ} {A : Set α} :
    A ∈ Para 𝒞' enc κ ↔ Aᶜ ∈ Para 𝒞 enc κ := by
  constructor
  · rintro ⟨f, L, hf, hL, hAL⟩
    exact ⟨f, Lᶜ, hf, (hcompl _ L).mp hL, fun a => by simpa using not_congr (hAL a)⟩
  · rintro ⟨f, L, hf, hL, hAL⟩
    refine ⟨f, Lᶜ, hf, (hcompl _ Lᶜ).mpr (by simpa using hL), fun a => ?_⟩
    have := not_congr (hAL a)
    simpa using this

/-- `para-coNP`-hardness of `B` is equivalent to `para-NP`-hardness of `Bᶜ`. -/
theorem paraCoNPHard_iff_paraNPHard_compl
    {β : Type} {enc : β ↪ List Bool} {κ : β → ℕ} {B : Set β} :
    paraCoNPHard enc κ B ↔ paraNPHard enc κ Bᶜ := by
  constructor
  · intro h α encA κA A hA
    have hA' : Aᶜ ∈ paraCoNP encA κA :=
      (mem_Para_compl_iff (fun _ _ => mem_coNP)).mpr (by simpa using hA)
    simpa using (h encA κA Aᶜ hA').compl
  · intro h α encA κA A hA
    have hA' : Aᶜ ∈ paraNP encA κA := (mem_Para_compl_iff (fun _ _ => mem_coNP)).mp hA
    simpa using (h encA κA Aᶜ hA').compl

/-- `para-NP`-hardness of `B` is equivalent to `para-coNP`-hardness of `Bᶜ`. -/
theorem paraNPHard_iff_paraCoNPHard_compl
    {β : Type} {enc : β ↪ List Bool} {κ : β → ℕ} {B : Set β} :
    paraNPHard enc κ B ↔ paraCoNPHard enc κ Bᶜ := by
  rw [paraCoNPHard_iff_paraNPHard_compl, compl_compl]

/-- `para-coDP`-hardness of `B` is equivalent to `para-DP`-hardness of `Bᶜ`. -/
theorem paraCoDPHard_iff_paraDPHard_compl
    {β : Type} {enc : β ↪ List Bool} {κ : β → ℕ} {B : Set β} :
    paraCoDPHard enc κ B ↔ paraDPHard enc κ Bᶜ := by
  constructor
  · intro h α encA κA A hA
    have hA' : Aᶜ ∈ paraCoDP encA κA :=
      (mem_Para_compl_iff (fun _ _ => mem_coDP)).mpr (by simpa using hA)
    simpa using (h encA κA Aᶜ hA').compl
  · intro h α encA κA A hA
    have hA' : Aᶜ ∈ paraDP encA κA := (mem_Para_compl_iff (fun _ _ => mem_coDP)).mp hA
    simpa using (h encA κA Aᶜ hA').compl

/-! ### Complementary weft hierarchy `coW[t]` -/

/-- The complementary weft hierarchy class `coW[t]`. -/
@[expose]
def coW (t : ℕ) {α : Type} (enc : α ↪ List Bool) (κ : α → ℕ) : Set (Set α) :=
  {A | Aᶜ ∈ W t enc κ}

/-- `coW[t]`-hardness under FPT-reductions. -/
abbrev coWHard (t : ℕ) {β : Type} (enc : β ↪ List Bool) (κ : β → ℕ) (B : Set β) : Prop :=
  FPTHard (coW t) enc κ B

/-- `coW[t]`-hardness of `B` is equivalent to `W[t]`-hardness of `Bᶜ`. -/
theorem coWHard_iff_wHard_compl (t : ℕ) {β : Type} {enc : β ↪ List Bool} {κ : β → ℕ}
    {B : Set β} : coWHard t enc κ B ↔ WHard t enc κ Bᶜ := by
  constructor
  · intro h α encA κA A hA
    have hA' : Aᶜ ∈ coW t encA κA := by change (Aᶜ)ᶜ ∈ W t encA κA; simpa using hA
    simpa using (h encA κA Aᶜ hA').compl
  · intro h α encA κA A hA
    simpa using (h encA κA Aᶜ hA).compl

end Cslib.Complexity
