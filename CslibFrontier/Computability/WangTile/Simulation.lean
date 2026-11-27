/-
Copyright (c) 2026 Formal Papers contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Papers contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WangTile.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Macrotile Simulations and Self-Simulation Aperiodicity for Wang Tiles

This module formalizes macrotile simulation between finite Wang tile palettes
(`List Cslib.WangTile`), Romashchenko, and Shen, proving under standard
Lean axioms:

1. **Plane tiling validity and aperiodicity (`IsValidPlaneTiling`, `IsAperiodic`)**:
   Explicit plane-tiling predicate for `f : ℤ → ℤ → Cslib.WangTile` matching
   `Cslib.WangTile.TilesPlane`, and aperiodicity (tiles the plane and admits no nonzero period
   `(px, py) ≠ (0, 0)`).
2. **Macrotile simulation (`MacrotileSimulation`)**:
   Simulation of palette `σ` by palette `τ` with zoom factor `N ≥ 1` via an injective `N × N`
   macrotile map `encode : { s // s ∈ σ } → (Fin N → Fin N → Cslib.WangTile)` preserving horizontal
   and vertical `2`-tile adjacency and enforcing a unique `N × N` macrotile grid on every valid
   `τ`-tiling.
3. **Plane-tiling transfer (`MacrotileSimulation.tilesPlane_iff`)**:
   If `τ` simulates `σ` with zoom factor `N ≥ 1`, then `Cslib.WangTile.TilesPlane τ ↔
   Cslib.WangTile.TilesPlane σ`.
4. **Tower and self-simulation aperiodicity (`isAperiodic_of_simulationTower`,
   `isAperiodic_of_selfSimulation`)**:
   Any plane-tiling Wang tile palette admitting an infinite simulation hierarchy with zoom factors
   `N k ≥ 2` (in particular, any self-simulating palette with zoom factor `N ≥ 2`) is aperiodic.

## Main definitions

* `CslibFrontier.WangTile.IsValidPlaneTiling`: valid `ℤ × ℤ` tiling for `τ : List Cslib.WangTile`.
* `CslibFrontier.WangTile.IsAperiodic`: `τ` tiles `ℤ × ℤ` and every valid tiling has no nonzero
  translation period.
* `CslibFrontier.WangTile.MacrotileSimulation`: macrotile simulation of `σ` by `τ` at zoom `N`.

## Main results

* `CslibFrontier.WangTile.MacrotileSimulation.tilesPlane_iff`: plane-tiling equivalence under
  macrotile simulation.
* `CslibFrontier.WangTile.isAperiodic_of_simulationTower`: aperiodicity of variable-zoom simulation
  towers with `N k ≥ 2`.
* `CslibFrontier.WangTile.isAperiodic_of_selfSimulation`: Durand–Romashchenko–Shen aperiodicity of
  self-simulating Wang tile sets with zoom factor `N ≥ 2`.
-/

public section

namespace CslibFrontier.WangTile

open Cslib

/-- A map `f : ℤ → ℤ → WangTile` is a valid plane tiling for palette `τ` if every cell belongs to
`τ` and adjacent horizontal and vertical edges match everywhere. -/
def IsValidPlaneTiling (τ : List WangTile) (f : ℤ → ℤ → WangTile) : Prop :=
  ∀ x y : ℤ,
    f x y ∈ τ ∧ (f x y).right = (f (x + 1) y).left ∧ (f x y).top = (f x (y + 1)).bottom

/-- `Cslib.WangTile.TilesPlane τ` holds iff there exists `f` satisfying `IsValidPlaneTiling τ f`. -/
theorem tilesPlane_iff_exists_isValidPlaneTiling (τ : List WangTile) :
    WangTile.TilesPlane τ ↔ ∃ f : ℤ → ℤ → WangTile, IsValidPlaneTiling τ f :=
  Iff.rfl

/-- A Wang tile palette `τ` is aperiodic if it tiles the plane and no valid `τ`-tiling admits a
nonzero translation period `(px, py) ≠ (0, 0)`. -/
def IsAperiodic (τ : List WangTile) : Prop :=
  WangTile.TilesPlane τ ∧
    ∀ f : ℤ → ℤ → WangTile, IsValidPlaneTiling τ f →
      ∀ px py : ℤ, (px, py) ≠ (0, 0) → ∃ x y : ℤ, f (x + px) (y + py) ≠ f x y

/-- An `w × h` block `B : Fin w → Fin h → WangTile` is locally valid over `τ` if all tiles belong to
`τ` and all internal horizontal and vertical edges match (i.e., `B` underlies a
`Cslib.WangTile.Rectangle τ w h`). -/
def IsValidPatch (τ : List WangTile) {w h : ℕ} (B : Fin w → Fin h → WangTile) : Prop :=
  (∀ (i : Fin w) (j : Fin h), B i j ∈ τ) ∧
    (∀ (i : Fin w) (j : Fin h) (hi : i.val + 1 < w),
      (B i j).right = (B ⟨i.val + 1, hi⟩ j).left) ∧
    (∀ (i : Fin w) (j : Fin h) (hj : j.val + 1 < h),
      (B i j).top = (B i ⟨j.val + 1, hj⟩).bottom)

/-- `IsValidPatch τ B` is equivalent to `Nonempty` of a `Cslib.WangTile.Rectangle τ w h` with tile
grid `B`. -/
theorem isValidPatch_iff_exists_rectangle (τ : List WangTile) {w h : ℕ}
    (B : Fin w → Fin h → WangTile) :
    IsValidPatch τ B ↔ ∃ R : WangTile.Rectangle τ w h, R.tile = B :=
  ⟨fun ⟨hm, hh, hv⟩ ↦ ⟨⟨B, hm, hh, hv⟩, rfl⟩,
   fun ⟨R, hR⟩ ↦ hR ▸ ⟨R.mem, R.horizontal, R.vertical⟩⟩

/-- Horizontal concatenation `B₁ B₂ : Fin (2 * N) → Fin N → WangTile` of two `N × N` macrotiles. -/
def horizConcatPatch {N : ℕ} (B₁ B₂ : Fin N → Fin N → WangTile) :
    Fin (2 * N) → Fin N → WangTile :=
  fun i j ↦
    if h : i.val < N then B₁ ⟨i.val, h⟩ j
    else B₂ ⟨i.val - N, by omega⟩ j

/-- Vertical concatenation `B₁ / B₂ : Fin N → Fin (2 * N) → WangTile` of two `N × N` macrotiles
(`B₁` on the south `[0, N - 1]`, `B₂` on the north `[N, 2N - 1]`). -/
def vertConcatPatch {N : ℕ} (B₁ B₂ : Fin N → Fin N → WangTile) :
    Fin N → Fin (2 * N) → WangTile :=
  fun i j ↦
    if h : j.val < N then B₁ i ⟨j.val, h⟩
    else B₂ i ⟨j.val - N, by omega⟩

/-- Extracts the `N × N` macrotile of `f` anchored at `(ox + i * N, oy + j * N)`. -/
def extractPatch (N : ℕ) (f : ℤ → ℤ → WangTile) (ox oy i j : ℤ) :
    Fin N → Fin N → WangTile :=
  fun a b ↦ f (ox + i * (N : ℤ) + a.val) (oy + j * (N : ℤ) + b.val)

/-- Macrotile simulation of Wang tile palette `σ` by `τ` with zoom factor `N ≥ 1`. -/
structure MacrotileSimulation (σ τ : List WangTile) (N : ℕ) where
  /-- Positive zoom factor `N ≥ 1`. -/
  zoom_pos : 1 ≤ N
  /-- Macrotile map `α : { s // s ∈ σ } → (Fin N → Fin N → WangTile)`. -/
  encode : { s : WangTile // s ∈ σ } → Fin N → Fin N → WangTile
  /-- `encode` is injective on `σ`. -/
  encode_injective : Function.Injective encode
  /-- Horizontal `2 × 1` matching equivalence between `σ` and `τ`. -/
  horiz_valid_iff : ∀ s₁ s₂ : { s : WangTile // s ∈ σ },
    s₁.1.right = s₂.1.left ↔ IsValidPatch τ (horizConcatPatch (encode s₁) (encode s₂))
  /-- Vertical `1 × 2` matching equivalence between `σ` and `τ`. -/
  vert_valid_iff : ∀ s₁ s₂ : { s : WangTile // s ∈ σ },
    s₁.1.top = s₂.1.bottom ↔ IsValidPatch τ (vertConcatPatch (encode s₁) (encode s₂))
  /-- Unique macrotile grid decomposition for every valid `τ`-tiling `f`. -/
  unique_grid : ∀ f : ℤ → ℤ → WangTile, IsValidPlaneTiling τ f →
    ∃! offset : Fin N × Fin N,
      ∀ i j : ℤ,
        extractPatch N f (offset.1.val : ℤ) (offset.2.val : ℤ) i j ∈ Set.range encode

/-- Assembles a configuration `g : ℤ → ℤ → { s // s ∈ σ }` into a plane map `ℤ → ℤ → WangTile`. -/
def MacrotileSimulation.assemble {σ τ : List WangTile} {N : ℕ}
    (sim : MacrotileSimulation σ τ N) (g : ℤ → ℤ → { s : WangTile // s ∈ σ }) :
    ℤ → ℤ → WangTile :=
  fun x y ↦
    have hN : (0 : ℤ) < N := by exact_mod_cast sim.zoom_pos
    let ri : Fin N := ⟨(x % (N : ℤ)).toNat, by
      have h0 := Int.emod_nonneg x hN.ne'
      have h1 := Int.emod_lt_of_pos x hN
      omega⟩
    let rj : Fin N := ⟨(y % (N : ℤ)).toNat, by
      have h0 := Int.emod_nonneg y hN.ne'
      have h1 := Int.emod_lt_of_pos y hN
      omega⟩
    sim.encode (g (x / (N : ℤ)) (y / (N : ℤ))) ri rj

/-- Decodes a valid `τ`-tiling `f` along its unique macrotile grid into a plane tiling over `σ`. -/
noncomputable def MacrotileSimulation.decode {σ τ : List WangTile} {N : ℕ}
    (sim : MacrotileSimulation σ τ N) {f : ℤ → ℤ → WangTile} (hf : IsValidPlaneTiling τ f) :
    ℤ → ℤ → WangTile :=
  have hgrid := (sim.unique_grid f hf).choose_spec.1
  fun i j ↦ (hgrid i j).choose.1

/-- Decoding any valid `τ`-tiling yields a valid `σ`-tiling. -/
theorem MacrotileSimulation.isValidPlaneTiling_decode {σ τ : List WangTile} {N : ℕ}
    (sim : MacrotileSimulation σ τ N) {f : ℤ → ℤ → WangTile} (hf : IsValidPlaneTiling τ f) :
    IsValidPlaneTiling σ (sim.decode hf) := by
  let offset := (sim.unique_grid f hf).choose
  have hgrid := (sim.unique_grid f hf).choose_spec.1
  let ox : ℤ := offset.1.val
  let oy : ℤ := offset.2.val
  let tileAt (i j : ℤ) : { s : WangTile // s ∈ σ } := (hgrid i j).choose
  have htile_eq : ∀ i j : ℤ, sim.encode (tileAt i j) = extractPatch N f ox oy i j :=
    fun i j ↦ (hgrid i j).choose_spec
  intro i j
  refine ⟨(tileAt i j).2, ?_, ?_⟩
  · apply (sim.horiz_valid_iff (tileAt i j) (tileAt (i + 1) j)).mpr
    rw [htile_eq, htile_eq]
    have hblock : ∀ (a : Fin (2 * N)) (b : Fin N),
        horizConcatPatch (extractPatch N f ox oy i j) (extractPatch N f ox oy (i + 1) j) a b =
          f (ox + i * (N : ℤ) + a.val) (oy + j * (N : ℤ) + b.val) := by
      intro a b
      dsimp only [horizConcatPatch, extractPatch]
      split_ifs with ha
      · rfl
      · have hx_eq : ox + (i + 1) * (N : ℤ) + ((a.val - N : ℕ) : ℤ) =
            ox + i * (N : ℤ) + a.val := by
          have ha_sub : ((a.val - N : ℕ) : ℤ) = (a.val : ℤ) - (N : ℤ) := by omega
          rw [ha_sub]; ring
        rw [hx_eq]
    refine ⟨fun a b ↦ by rw [hblock]; exact (hf _ _).1,
      fun a b ha ↦ ?_, fun a b hb ↦ ?_⟩
    · rw [hblock, hblock]
      have h := (hf (ox + i * (N : ℤ) + a.val) (oy + j * (N : ℤ) + b.val)).2.1
      have hEq : ox + i * (N : ℤ) + a.val + 1 = ox + i * (N : ℤ) + ((a.val + 1 : ℕ) : ℤ) := by
        push_cast; ring
      rwa [← hEq]
    · rw [hblock, hblock]
      have h := (hf (ox + i * (N : ℤ) + a.val) (oy + j * (N : ℤ) + b.val)).2.2
      have hEq : oy + j * (N : ℤ) + b.val + 1 = oy + j * (N : ℤ) + ((b.val + 1 : ℕ) : ℤ) := by
        push_cast; ring
      rwa [← hEq]
  · apply (sim.vert_valid_iff (tileAt i j) (tileAt i (j + 1))).mpr
    rw [htile_eq, htile_eq]
    have hblock : ∀ (a : Fin N) (b : Fin (2 * N)),
        vertConcatPatch (extractPatch N f ox oy i j) (extractPatch N f ox oy i (j + 1)) a b =
          f (ox + i * (N : ℤ) + a.val) (oy + j * (N : ℤ) + b.val) := by
      intro a b
      dsimp only [vertConcatPatch, extractPatch]
      split_ifs with hb
      · rfl
      · have hy_eq : oy + j * (N : ℤ) + a.val = oy + j * (N : ℤ) + a.val ∧
            oy + (j + 1) * (N : ℤ) + ((b.val - N : ℕ) : ℤ) = oy + j * (N : ℤ) + b.val := by
          refine ⟨rfl, ?_⟩
          have hb_sub : ((b.val - N : ℕ) : ℤ) = (b.val : ℤ) - (N : ℤ) := by omega
          rw [hb_sub]; ring
        rw [hy_eq.2]
    refine ⟨fun a b ↦ by rw [hblock]; exact (hf _ _).1,
      fun a b ha ↦ ?_, fun a b hb ↦ ?_⟩
    · rw [hblock, hblock]
      have h := (hf (ox + i * (N : ℤ) + a.val) (oy + j * (N : ℤ) + b.val)).2.1
      have hEq : ox + i * (N : ℤ) + a.val + 1 = ox + i * (N : ℤ) + ((a.val + 1 : ℕ) : ℤ) := by
        push_cast; ring
      rwa [← hEq]
    · rw [hblock, hblock]
      have h := (hf (ox + i * (N : ℤ) + a.val) (oy + j * (N : ℤ) + b.val)).2.2
      have hEq : oy + j * (N : ℤ) + b.val + 1 = oy + j * (N : ℤ) + ((b.val + 1 : ℕ) : ℤ) := by
        push_cast; ring
      rwa [← hEq]

/-- If `τ` simulates `σ` with zoom factor `N ≥ 1`, then `τ` tiles the plane iff `σ` tiles the
plane. -/
theorem MacrotileSimulation.tilesPlane_iff {σ τ : List WangTile} {N : ℕ}
    (sim : MacrotileSimulation σ τ N) :
    WangTile.TilesPlane τ ↔ WangTile.TilesPlane σ := by
  constructor
  · rintro ⟨f, hf⟩
    exact ⟨sim.decode hf, sim.isValidPlaneTiling_decode hf⟩
  · rintro ⟨g, hg⟩
    let gSub : ℤ → ℤ → { s : WangTile // s ∈ σ } := fun i j ↦ ⟨g i j, (hg i j).1⟩
    refine ⟨sim.assemble gSub, ?_⟩
    have hN : (0 : ℤ) < N := by exact_mod_cast sim.zoom_pos
    have hH_loc : ∀ i j : ℤ,
        IsValidPatch τ (horizConcatPatch (sim.encode (gSub i j)) (sim.encode (gSub (i + 1) j))) :=
      fun i j ↦ (sim.horiz_valid_iff _ _).mp (hg i j).2.1
    have hV_loc : ∀ i j : ℤ,
        IsValidPatch τ (vertConcatPatch (sim.encode (gSub i j)) (sim.encode (gSub i (j + 1)))) :=
      fun i j ↦ (sim.vert_valid_iff _ _).mp (hg i j).2.2
    intro x y
    let qi := x / (N : ℤ)
    let ri := (x % (N : ℤ)).toNat
    let qj := y / (N : ℤ)
    let rj := (y % (N : ℤ)).toNat
    have hri0 : 0 ≤ x % (N : ℤ) := Int.emod_nonneg x hN.ne'
    have hri1 : x % (N : ℤ) < N := Int.emod_lt_of_pos x hN
    have hrj0 : 0 ≤ y % (N : ℤ) := Int.emod_nonneg y hN.ne'
    have hrj1 : y % (N : ℤ) < N := Int.emod_lt_of_pos y hN
    have hri_lt : ri < N := by dsimp [ri]; omega
    have hrj_lt : rj < N := by dsimp [rj]; omega
    have hx_decomp : x = qi * (N : ℤ) + (ri : ℤ) := by
      have h1 : (ri : ℤ) = x % (N : ℤ) := Int.toNat_of_nonneg hri0
      dsimp only [qi]
      rw [h1, Int.emod_def]
      ring
    have hy_decomp : y = qj * (N : ℤ) + (rj : ℤ) := by
      have h1 : (rj : ℤ) = y % (N : ℤ) := Int.toNat_of_nonneg hrj0
      dsimp only [qj]
      rw [h1, Int.emod_def]
      ring
    refine ⟨?_, ?_, ?_⟩
    · dsimp only [MacrotileSimulation.assemble]
      have hmem := (hH_loc qi qj).1 ⟨ri, by omega⟩ ⟨rj, hrj_lt⟩
      dsimp only [horizConcatPatch] at hmem
      simpa only [hri_lt, ↓reduceDIte] using hmem
    · dsimp only [MacrotileSimulation.assemble]
      have hstep := (hH_loc qi qj).2.1 ⟨ri, by omega⟩ ⟨rj, hrj_lt⟩ (by dsimp; omega)
      dsimp only [horizConcatPatch] at hstep
      simp only [hri_lt, ↓reduceDIte] at hstep
      by_cases hwrap : ri + 1 < N
      · simp only [hwrap, ↓reduceDIte] at hstep
        have hq_eq : (x + 1) / (N : ℤ) = qi := by
          rw [hx_decomp]
          have : qi * (N : ℤ) + (ri : ℤ) + 1 = ((ri + 1 : ℕ) : ℤ) + qi * (N : ℤ) := by
            push_cast; ring
          rw [this, Int.add_mul_ediv_right _ _ hN.ne',
            Int.ediv_eq_zero_of_lt (by positivity) (by exact_mod_cast hwrap), zero_add]
        have hr_eq : ((x + 1) % (N : ℤ)).toNat = ri + 1 := by
          rw [hx_decomp]
          have : qi * (N : ℤ) + (ri : ℤ) + 1 = ((ri + 1 : ℕ) : ℤ) + qi * (N : ℤ) := by
            push_cast; ring
          rw [this, Int.add_mul_emod_self_right,
            Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hwrap)]
          omega
        simpa only [hq_eq, hr_eq] using hstep
      · simp only [hwrap, ↓reduceDIte] at hstep
        have hri_eq : ri + 1 = N := by omega
        have hq_eq : (x + 1) / (N : ℤ) = qi + 1 := by
          rw [hx_decomp]
          have : qi * (N : ℤ) + (ri : ℤ) + 1 = (qi + 1) * (N : ℤ) := by
            have : (ri : ℤ) + 1 = (N : ℤ) := by exact_mod_cast hri_eq
            linarith
          rw [this, Int.mul_ediv_cancel _ hN.ne']
        have hr_eq : ((x + 1) % (N : ℤ)).toNat = 0 := by
          rw [hx_decomp]
          have : qi * (N : ℤ) + (ri : ℤ) + 1 = (qi + 1) * (N : ℤ) := by
            have : (ri : ℤ) + 1 = (N : ℤ) := by exact_mod_cast hri_eq
            linarith
          rw [this, Int.mul_emod_left]; rfl
        have hsub0 : ri + 1 - N = 0 := by omega
        simpa only [hq_eq, hr_eq, hsub0] using hstep
    · dsimp only [MacrotileSimulation.assemble]
      have hstep := (hV_loc qi qj).2.2 ⟨ri, hri_lt⟩ ⟨rj, by omega⟩ (by dsimp; omega)
      dsimp only [vertConcatPatch] at hstep
      simp only [hrj_lt, ↓reduceDIte] at hstep
      by_cases hwrap : rj + 1 < N
      · simp only [hwrap, ↓reduceDIte] at hstep
        have hq_eq : (y + 1) / (N : ℤ) = qj := by
          rw [hy_decomp]
          have : qj * (N : ℤ) + (rj : ℤ) + 1 = ((rj + 1 : ℕ) : ℤ) + qj * (N : ℤ) := by
            push_cast; ring
          rw [this, Int.add_mul_ediv_right _ _ hN.ne',
            Int.ediv_eq_zero_of_lt (by positivity) (by exact_mod_cast hwrap), zero_add]
        have hr_eq : ((y + 1) % (N : ℤ)).toNat = rj + 1 := by
          rw [hy_decomp]
          have : qj * (N : ℤ) + (rj : ℤ) + 1 = ((rj + 1 : ℕ) : ℤ) + qj * (N : ℤ) := by
            push_cast; ring
          rw [this, Int.add_mul_emod_self_right,
            Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hwrap)]
          omega
        simpa only [hq_eq, hr_eq] using hstep
      · simp only [hwrap, ↓reduceDIte] at hstep
        have hrj_eq : rj + 1 = N := by omega
        have hq_eq : (y + 1) / (N : ℤ) = qj + 1 := by
          rw [hy_decomp]
          have : qj * (N : ℤ) + (rj : ℤ) + 1 = (qj + 1) * (N : ℤ) := by
            have : (rj : ℤ) + 1 = (N : ℤ) := by exact_mod_cast hrj_eq
            linarith
          rw [this, Int.mul_ediv_cancel _ hN.ne']
        have hr_eq : ((y + 1) % (N : ℤ)).toNat = 0 := by
          rw [hy_decomp]
          have : qj * (N : ℤ) + (rj : ℤ) + 1 = (qj + 1) * (N : ℤ) := by
            have : (rj : ℤ) + 1 = (N : ℤ) := by exact_mod_cast hrj_eq
            linarith
          rw [this, Int.mul_emod_left]; rfl
        have hsub0 : rj + 1 - N = 0 := by omega
        simpa only [hq_eq, hr_eq, hsub0] using hstep

private theorem period_divisible_of_macrotileSimulation {σ τ : List WangTile} {N : ℕ}
    (sim : MacrotileSimulation σ τ N) {f : ℤ → ℤ → WangTile} (hf : IsValidPlaneTiling τ f)
    {px py : ℤ} (hper : ∀ x y : ℤ, f (x + px) (y + py) = f x y) :
    (N : ℤ) ∣ px ∧ (N : ℤ) ∣ py ∧
      ∀ i j : ℤ, sim.decode hf (i + px / (N : ℤ)) (j + py / (N : ℤ)) = sim.decode hf i j := by
  have hN : (0 : ℤ) < N := by exact_mod_cast sim.zoom_pos
  let offset := (sim.unique_grid f hf).choose
  have hspec := (sim.unique_grid f hf).choose_spec
  let r₀ : Fin N := ⟨(((offset.1.val : ℤ) - px) % (N : ℤ)).toNat, by
    have h1 := Int.emod_nonneg ((offset.1.val : ℤ) - px) hN.ne'
    have h2 := Int.emod_lt_of_pos ((offset.1.val : ℤ) - px) hN
    omega⟩
  let r₁ : Fin N := ⟨(((offset.2.val : ℤ) - py) % (N : ℤ)).toNat, by
    have h1 := Int.emod_nonneg ((offset.2.val : ℤ) - py) hN.ne'
    have h2 := Int.emod_lt_of_pos ((offset.2.val : ℤ) - py) hN
    omega⟩
  let q₀ : ℤ := ((offset.1.val : ℤ) - px) / (N : ℤ)
  let q₁ : ℤ := ((offset.2.val : ℤ) - py) / (N : ℤ)
  have hr₀_eq : (r₀.val : ℤ) = ((offset.1.val : ℤ) - px) % (N : ℤ) :=
    Int.toNat_of_nonneg (Int.emod_nonneg _ hN.ne')
  have hr₁_eq : (r₁.val : ℤ) = ((offset.2.val : ℤ) - py) % (N : ℤ) :=
    Int.toNat_of_nonneg (Int.emod_nonneg _ hN.ne')
  have hdecomp0 : (offset.1.val : ℤ) - px = q₀ * (N : ℤ) + (r₀.val : ℤ) := by
    dsimp only [q₀]
    rw [hr₀_eq, Int.emod_def]
    ring
  have hdecomp1 : (offset.2.val : ℤ) - py = q₁ * (N : ℤ) + (r₁.val : ℤ) := by
    dsimp only [q₁]
    rw [hr₁_eq, Int.emod_def]
    ring
  have hshift_grid : ∀ i j : ℤ,
      extractPatch N f (r₀.val : ℤ) (r₁.val : ℤ) i j ∈ Set.range sim.encode := by
    intro i j
    have hEq : extractPatch N f (r₀.val : ℤ) (r₁.val : ℤ) i j =
        extractPatch N f (offset.1.val : ℤ) (offset.2.val : ℤ) (i - q₀) (j - q₁) := by
      funext a b
      dsimp only [extractPatch]
      have hx_eq : (r₀.val : ℤ) + i * (N : ℤ) + a.val + px =
          (offset.1.val : ℤ) + (i - q₀) * (N : ℤ) + a.val := by linarith
      have hy_eq : (r₁.val : ℤ) + j * (N : ℤ) + b.val + py =
          (offset.2.val : ℤ) + (j - q₁) * (N : ℤ) + b.val := by linarith
      rw [← hx_eq, ← hy_eq, hper]
    rw [hEq]
    exact hspec.1 (i - q₀) (j - q₁)
  have huniq : (r₀, r₁) = offset := hspec.2 (r₀, r₁) hshift_grid
  have hdvd0 : (N : ℤ) ∣ px := by
    refine ⟨-q₀, ?_⟩
    have : (r₀.val : ℤ) = (offset.1.val : ℤ) := congrArg (fun pr ↦ (pr.1.val : ℤ)) huniq
    linarith
  have hdvd1 : (N : ℤ) ∣ py := by
    refine ⟨-q₁, ?_⟩
    have : (r₁.val : ℤ) = (offset.2.val : ℤ) := congrArg (fun pr ↦ (pr.2.val : ℤ)) huniq
    linarith
  refine ⟨hdvd0, hdvd1, fun i j ↦ ?_⟩
  have hpx : px = (px / (N : ℤ)) * (N : ℤ) := by
    rcases hdvd0 with ⟨m, hm⟩
    rw [hm, Int.mul_ediv_cancel_left _ hN.ne', mul_comm]
  have hpy : py = (py / (N : ℤ)) * (N : ℤ) := by
    rcases hdvd1 with ⟨m, hm⟩
    rw [hm, Int.mul_ediv_cancel_left _ hN.ne', mul_comm]
  have hpatch_eq : extractPatch N f (offset.1.val : ℤ) (offset.2.val : ℤ)
      (i + px / (N : ℤ)) (j + py / (N : ℤ)) =
      extractPatch N f (offset.1.val : ℤ) (offset.2.val : ℤ) i j := by
    funext a b
    dsimp only [extractPatch]
    have hx_eq : (offset.1.val : ℤ) + (i + px / (N : ℤ)) * (N : ℤ) + a.val =
        (offset.1.val : ℤ) + i * (N : ℤ) + a.val + px := by linarith
    have hy_eq : (offset.2.val : ℤ) + (j + py / (N : ℤ)) * (N : ℤ) + b.val =
        (offset.2.val : ℤ) + j * (N : ℤ) + b.val + py := by linarith
    rw [hx_eq, hy_eq, hper]
  dsimp only [MacrotileSimulation.decode]
  have h1 := (hspec.1 (i + px / (N : ℤ)) (j + py / (N : ℤ))).choose_spec
  have h2 := (hspec.1 i j).choose_spec
  exact congrArg Subtype.val (sim.encode_injective (h1.trans (hpatch_eq.trans h2.symm)))

/-- Any infinite hierarchy `(τ k)_{k ≥ 0}` of Wang tile palettes where `τ k` simulates `τ (k + 1)`
with zoom factor `N k ≥ 2` and `τ 0` tiles the plane forces `τ 0` to be aperiodic. -/
theorem isAperiodic_of_simulationTower (τ : ℕ → List WangTile) (N : ℕ → ℕ)
    (hN : ∀ k : ℕ, 2 ≤ N k)
    (sim : ∀ k : ℕ, MacrotileSimulation (τ (k + 1)) (τ k) (N k))
    (htiles : WangTile.TilesPlane (τ 0)) :
    IsAperiodic (τ 0) := by
  refine ⟨htiles, fun f₀ hf₀ px py hne ↦ ?_⟩
  by_contra hper
  push Not at hper
  have htower : ∀ k : ℕ, ∃ (fk : ℤ → ℤ → WangTile) (pxk pyk : ℤ),
      IsValidPlaneTiling (τ k) fk ∧
      (∀ x y : ℤ, fk (x + pxk) (y + pyk) = fk x y) ∧
      ((∏ i ∈ Finset.range k, (N i : ℤ)) * pxk = px) ∧
      ((∏ i ∈ Finset.range k, (N i : ℤ)) * pyk = py) := by
    intro k
    induction k with
    | zero => exact ⟨f₀, px, py, hf₀, hper, by simp, by simp⟩
    | succ m ih =>
      rcases ih with ⟨fm, pxm, pym, hfm, hperm, hprodx, hprody⟩
      obtain ⟨hdvdx, hdvdy, hper_next⟩ := period_divisible_of_macrotileSimulation (sim m) hfm hperm
      have hNm_ne : (N m : ℤ) ≠ 0 := by have := hN m; omega
      refine ⟨(sim m).decode hfm, pxm / (N m : ℤ), pym / (N m : ℤ),
        (sim m).isValidPlaneTiling_decode hfm, hper_next, ?_, ?_⟩
      · rw [Finset.prod_range_succ, mul_assoc]
        rcases hdvdx with ⟨q, hq⟩
        rw [hq, Int.mul_ediv_cancel_left _ hNm_ne, ← hq, hprodx]
      · rw [Finset.prod_range_succ, mul_assoc]
        rcases hdvdy with ⟨q, hq⟩
        rw [hq, Int.mul_ediv_cancel_left _ hNm_ne, ← hq, hprody]
  have hcast_prod : ∀ m : ℕ,
      ((∏ i ∈ Finset.range m, N i : ℕ) : ℤ) = ∏ i ∈ Finset.range m, (N i : ℤ) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [Finset.prod_range_succ, Finset.prod_range_succ, Nat.cast_mul, ih]
  have hpx0 : px = 0 := by
    by_contra hpx_ne
    let k := px.natAbs + 1
    obtain ⟨_, pxk, _, _, _, hprodx, _⟩ := htower k
    let P : ℕ := ∏ i ∈ Finset.range k, N i
    have hP_cast : (P : ℤ) = ∏ i ∈ Finset.range k, (N i : ℤ) := hcast_prod k
    have h2pow : 2 ^ k ≤ P := by
      simpa [P] using Finset.prod_le_prod fun i (_ : i ∈ Finset.range k) ↦ hN i
    have hpxk_ne : pxk ≠ 0 := fun h0 ↦ by rw [h0, mul_zero] at hprodx; exact hpx_ne hprodx.symm
    have habs : P ≤ px.natAbs := by
      have hmul : px.natAbs = P * pxk.natAbs := by
        rw [← hprodx, ← hP_cast, Int.natAbs_mul, Int.natAbs_natCast]
      have hpos : 1 ≤ pxk.natAbs := Int.natAbs_pos.mpr hpxk_ne
      calc P = P * 1 := (mul_one P).symm
        _ ≤ P * pxk.natAbs := Nat.mul_le_mul_left P hpos
        _ = px.natAbs := hmul.symm
    have hlt : k < 2 ^ k := Nat.lt_two_pow_self
    omega
  have hpy0 : py = 0 := by
    by_contra hpy_ne
    let k := py.natAbs + 1
    obtain ⟨_, _, pyk, _, _, _, hprody⟩ := htower k
    let P : ℕ := ∏ i ∈ Finset.range k, N i
    have hP_cast : (P : ℤ) = ∏ i ∈ Finset.range k, (N i : ℤ) := hcast_prod k
    have h2pow : 2 ^ k ≤ P := by
      simpa [P] using Finset.prod_le_prod fun i (_ : i ∈ Finset.range k) ↦ hN i
    have hpyk_ne : pyk ≠ 0 := fun h0 ↦ by rw [h0, mul_zero] at hprody; exact hpy_ne hprody.symm
    have habs : P ≤ py.natAbs := by
      have hmul : py.natAbs = P * pyk.natAbs := by
        rw [← hprody, ← hP_cast, Int.natAbs_mul, Int.natAbs_natCast]
      have hpos : 1 ≤ pyk.natAbs := Int.natAbs_pos.mpr hpyk_ne
      calc P = P * 1 := (mul_one P).symm
        _ ≤ P * pyk.natAbs := Nat.mul_le_mul_left P hpos
        _ = py.natAbs := hmul.symm
    have hlt : k < 2 ^ k := Nat.lt_two_pow_self
    omega
  exact hne (Prod.ext hpx0 hpy0)

/-- Durand–Romashchenko–Shen self-simulation aperiodicity theorem: any Wang tile palette `τ` that
tiles the plane and simulates itself with zoom factor `N ≥ 2` is aperiodic. -/
theorem isAperiodic_of_selfSimulation {τ : List WangTile} {N : ℕ} (hN : 2 ≤ N)
    (sim : MacrotileSimulation τ τ N) (htiles : WangTile.TilesPlane τ) :
    IsAperiodic τ :=
  isAperiodic_of_simulationTower (fun _ ↦ τ) (fun _ ↦ N) (fun _ ↦ hN) (fun _ ↦ sim) htiles

end CslibFrontier.WangTile
