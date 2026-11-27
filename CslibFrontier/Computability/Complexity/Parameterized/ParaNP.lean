module

public import CslibFrontier.Computability.Complexity.Parameterized
public import CslibFrontier.Computability.Complexity.Reduction

/-!
# Para-NP and Para-NP-Hardness in Parameterized Complexity

Defines the parameterized complexity class `CslibFrontier.Complexity.ParaNP` and hardness
`CslibFrontier.Complexity.ParaNPHard` on `Cslib.Complexity` multi-tape Turing machine encodings,
proving closure under fpt-reductions, the constant-parameter slice NP-hardness criterion, and the
collapse `P = NP` whenever a para-NP-hard problem belongs to `XP` (or `FPT`).

## Main definitions

- `CslibFrontier.Complexity.ParaNP`: parameterized problems fpt-reducible to an `NP` problem with
  constant parameter `0`.
- `CslibFrontier.Complexity.ParaNPHard`: parameterized problems to which every `NP` problem (with
  constant parameter `0`) fpt-reduces.

## Main results

- `CslibFrontier.Complexity.ParaNPHard.trans`: para-NP-hardness transfers along fpt-reductions.
- `CslibFrontier.Complexity.ParaNPHard.of_slice_npHard`: if a constant-parameter slice
  `A ∩ {a | κ a = k₀}` is `NP`-hard, `{a | κ a = k₀} ∈ P`, and the slice contains a no-instance,
  then `A` is para-NP-hard.
- `CslibFrontier.Complexity.ParaNPHard.of_polyTimeReducible_bounded`: any `NP`-hard problem reducing
  in polynomial time to `A` with uniformly bounded output parameter makes `A` para-NP-hard.
- `CslibFrontier.Complexity.ParaNPHard.P_eq_NP_of_mem_XP`,
  `CslibFrontier.Complexity.ParaNPHard.P_eq_NP_of_mem_FPT`: placing a para-NP-hard problem in `XP`
  (or `FPT`) collapses `P = NP`.
-/

public section

namespace CslibFrontier.Complexity

open Cslib.Complexity Turing.MultiTapeTM

/-- A parameterized problem `(A, enc, κ)` lies in **`ParaNP`** if it fpt-reduces to some problem in
`NP` (with constant parameter `0`). -/
def ParaNP {α : Type} (enc : α ↪ List Bool) (κ : α → ℕ) : Set (Set α) :=
  {A | ∃ (β : Type) (encB : β ↪ List Bool) (B : Set β),
    B ∈ NP encB ∧ FPTReducible enc encB κ (fun _ ↦ 0) A B}

/-- A parameterized problem `(B, enc, κ)` is **`ParaNPHard`** if every problem in `NP` (equipped
with constant parameter `0`) fpt-reduces to `(B, enc, κ)`. -/
def ParaNPHard {β : Type} (enc : β ↪ List Bool) (κ : β → ℕ) (B : Set β) : Prop :=
  ∀ ⦃α : Type⦄ (encA : α ↪ List Bool) (A : Set α),
    A ∈ NP encA → FPTReducible encA enc (fun _ ↦ 0) κ A B

/-- Every `NP` problem (with any parameter) belongs to `ParaNP`. -/
theorem mem_ParaNP_of_mem_NP {α : Type} {enc : α ↪ List Bool} {κ : α → ℕ} {A : Set α}
    (hA : A ∈ NP enc) : A ∈ ParaNP enc κ :=
  ⟨α, enc, A, hA,
    FPTReducible.of_computableInPolyTime ComputableInPolyTime.id'
      (h := fun _ ↦ 0) (fun _ ↦ le_rfl) (fun _ ↦ Iff.rfl)⟩

/-- `ParaNP` is closed under fpt-reductions. -/
theorem FPTReducible.mem_ParaNP {α β : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool}
    {κA : α → ℕ} {κB : β → ℕ} {A : Set α} {B : Set β}
    (hAB : FPTReducible encA encB κA κB A B) (hB : B ∈ ParaNP encB κB) :
    A ∈ ParaNP encA κA := by
  rcases hB with ⟨γ, encC, C, hC, hBC⟩
  exact ⟨γ, encC, C, hC, hAB.trans hBC⟩

/-- `ParaNPHard` transfers along fpt-reductions. -/
theorem ParaNPHard.trans {α β : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool}
    {κA : α → ℕ} {κB : β → ℕ} {A : Set α} {B : Set β}
    (hA : ParaNPHard encA κA A) (hAB : FPTReducible encA encB κA κB A B) :
    ParaNPHard encB κB B :=
  fun _ encC C hC ↦ (hA encC C hC).trans hAB

/-- If a polynomial-time reduction from an `NP`-hard problem `A` to `B` maps all inputs to
instances of parameter at most `K`, then `(B, encB, κB)` is para-NP-hard. -/
theorem ParaNPHard.of_polyTimeReducible_bounded {α β : Type} {encA : α ↪ List Bool}
    {encB : β ↪ List Bool} {κB : β → ℕ} {A : Set α} {B : Set β}
    (hA : NPHard encA A) (f : α → β) (hf : ComputableInPolyTime f encA encB)
    (hfAB : ∀ a, a ∈ A ↔ f a ∈ B) {K : ℕ} (hK : ∀ a, κB (f a) ≤ K) :
    ParaNPHard encB κB B := by
  intro γ encC C hC
  have hCA : PolyTimeReducible encC encA C A := hA encC C hC
  have hCA_fpt : FPTReducible encC encA (fun _ ↦ 0) (fun _ ↦ 0) C A :=
    let ⟨r, hr, hrCA⟩ := hCA
    FPTReducible.of_computableInPolyTime hr (h := fun _ ↦ 0) (fun _ ↦ le_rfl) hrCA
  have hAB_fpt : FPTReducible encA encB (fun _ ↦ 0) κB A B :=
    FPTReducible.of_computableInPolyTime hf (h := fun _ ↦ K) hK hfAB
  exact hCA_fpt.trans hAB_fpt

/-- **Constant-parameter slice criterion for para-NP-hardness**: if the constant-parameter slice
`B ∩ {b | κB b = k₀}` is `NP`-hard, the slice `{b | κB b = k₀}` is decidable in `P`, and there
exists a no-instance `b₀ ∉ B` with `κB b₀ = k₀`, then `(B, encB, κB)` is para-NP-hard. -/
theorem ParaNPHard.of_slice_npHard {β : Type} {encB : β ↪ List Bool} {κB : β → ℕ} {B : Set β}
    {k₀ : ℕ} (hSlice : NPHard encB (B ∩ {b | κB b = k₀}))
    (hSliceP : {b | κB b = k₀} ∈ P encB) {b₀ : β} (hb₀ : b₀ ∉ B) (hκ₀ : κB b₀ = k₀) :
    ParaNPHard encB κB B := by
  rcases hSliceP with ⟨checkSlice, hcheckP, hcheckSpec⟩
  let f : β → β := fun b ↦ if checkSlice b then b else b₀
  have hf : ComputableInPolyTime f encB encB :=
    ComputableInPolyTime.ite hcheckP ComputableInPolyTime.id' (ComputableInPolyTime.const b₀)
  refine ParaNPHard.of_polyTimeReducible_bounded (K := k₀) hSlice f hf (fun b ↦ ?_) (fun b ↦ ?_)
  · dsimp only [f]
    by_cases hcb : checkSlice b = true
    · have hk : κB b = k₀ := (hcheckSpec b).mpr hcb
      simp [hcb, hk]
    · have hk : κB b ≠ k₀ := fun h ↦ hcb ((hcheckSpec b).mp h)
      simp [hcb, hk, hb₀]
  · dsimp only [f]
    by_cases hcb : checkSlice b = true
    · have hk : κB b = k₀ := (hcheckSpec b).mpr hcb
      simp [hcb, hk]
    · simp [hcb, hκ₀]

/-- **XP collapse**: if a para-NP-hard problem belongs to `XP`, then `P = NP` for every encoding. -/
theorem ParaNPHard.P_eq_NP_of_mem_XP {β : Type} {encB : β ↪ List Bool} {κB : β → ℕ} {B : Set β}
    (hHard : ParaNPHard encB κB B) (hXP : B ∈ XP encB κB)
    {α : Type} (encA : α ↪ List Bool) : P encA = NP encA := by
  refine subset_antisymm P_subset_NP fun A hA ↦ ?_
  have hAXP : A ∈ XP encA (fun _ ↦ 0) := (hHard encA A hA).mem_XP hXP
  rwa [XP_eq_P_of_le (K := 0) (fun _ ↦ le_rfl)] at hAXP

/-- **FPT collapse**: if a para-NP-hard problem belongs to `FPT`, then `P = NP` for every
encoding. -/
theorem ParaNPHard.P_eq_NP_of_mem_FPT {β : Type} {encB : β ↪ List Bool} {κB : β → ℕ} {B : Set β}
    (hHard : ParaNPHard encB κB B) (hFPT : B ∈ FPT encB κB)
    {α : Type} (encA : α ↪ List Bool) : P encA = NP encA :=
  hHard.P_eq_NP_of_mem_XP (FPT_subset_XP hFPT) encA

end CslibFrontier.Complexity
