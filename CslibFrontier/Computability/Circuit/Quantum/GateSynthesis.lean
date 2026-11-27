/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FormalPapers Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Quantum.Basic
public import CslibFrontier.Foundations.LinearAlgebra.Tensor.Basic
public import CslibFrontier.Foundations.Quantum.Clifford
public import CslibFrontier.Foundations.Quantum.Pauli
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Data.ENat.Basic

import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Subgroup-Relative Gate Synthesis Counts and Multi-Qubit Pauli Transfer Lower Bounds

This module develops subgroup-relative `(H, W)`-gate synthesis counts `gateSynthesisCount` on
groups, general subadditive `H`-invariant resource-monotone lower bounds, their specialization to
quantum circuits (`Cslib.Quantum.Circuit`), and multi-qubit Pauli string transfer matrices on
`n`-qubit registers (`Fin n → Bool`):

1. Inductive `(H, W)`-realization predicate `HasSynthesisCount` and minimal synthesis count
   `gateSynthesisCount : WithTop ℕ`, with subadditivity, subgroup-zero characterization, left/right
   `H`-invariance, inversion invariance, homomorphism monotonicity, and circuit gate-count upper
   bounds `gateSynthesisCount_circuit_le_countP`.
2. General resource-monotone lower bound `div_le_gateSynthesisCount_of_subadditive`: any
   nonnegative `H`-invariant subadditive functional `ν : G → ℝ` bounded by `c > 0` on `W` satisfies
   `ν(g) / c ≤ t_W(g)` (and consequently bounds the number of non-`H` gates in any realizing
   `Cslib.Quantum.Circuit`).
3. Multi-qubit Pauli string matrices `pauliString` indexed by `Fin n → Fin 4` (built via
   `Cslib.Tensor.piKronecker` from `Cslib.Quantum.pauliX`, `Cslib.Quantum.pauliY`, and
   `Cslib.Quantum.pauliZ`), Hermiticity, involution, unitarity, trace orthogonality
   `trace_pauliString_mul`, unitary Pauli transfer entries `unitaryPauliTransfer`, and unitary
   stabilizer nullity `unitaryStabilizerNullity`.

## Main definitions

* `CslibFrontier.Computability.Circuit.Quantum.HasSynthesisCount`,
  `CslibFrontier.Computability.Circuit.Quantum.gateSynthesisCount`.
* `CslibFrontier.Computability.Circuit.Quantum.pauliSingle`,
  `CslibFrontier.Computability.Circuit.Quantum.pauliString`,
  `CslibFrontier.Computability.Circuit.Quantum.unitaryPauliTransfer`,
  `CslibFrontier.Computability.Circuit.Quantum.unitaryPauliOneCount`,
  `CslibFrontier.Computability.Circuit.Quantum.unitaryStabilizerNullity`.

## Main results

* `CslibFrontier.Computability.Circuit.Quantum.gateSynthesisCount_mul_le`,
  `CslibFrontier.Computability.Circuit.Quantum.gateSynthesisCount_eq_zero_iff`,
  `CslibFrontier.Computability.Circuit.Quantum.gateSynthesisCount_mul_left_of_mem`,
  `CslibFrontier.Computability.Circuit.Quantum.gateSynthesisCount_mul_right_of_mem`,
  `CslibFrontier.Computability.Circuit.Quantum.gateSynthesisCount_map_le`.
* `CslibFrontier.Computability.Circuit.Quantum.div_le_gateSynthesisCount_of_subadditive`,
  `CslibFrontier.Computability.Circuit.Quantum.gateSynthesisCount_circuit_le_countP`.
* `CslibFrontier.Computability.Circuit.Quantum.pauliString_isHermitian`,
  `CslibFrontier.Computability.Circuit.Quantum.pauliString_mul_self`,
  `CslibFrontier.Computability.Circuit.Quantum.pauliString_mem_unitaryGroup`,
  `CslibFrontier.Computability.Circuit.Quantum.trace_pauliString_mul`.
-/

public section

namespace CslibFrontier.Computability.Circuit.Quantum

open Cslib.Quantum Cslib.Tensor Finset Matrix

section GateSynthesis

/-- Inductive realization predicate for `(H, W)`-synthesis circuits of `W`-count `k`:
`HasSynthesisCount H W k g` holds when `g = c_k w_k ⋯ c_1 w_1 c_0` for `c_i ∈ H` and `w_i ∈ W`. -/
inductive HasSynthesisCount {G : Type*} [Group G] (H : Subgroup G) (W : Set G) : ℕ → G → Prop
  | zero {c : G} (hc : c ∈ H) : HasSynthesisCount H W 0 c
  | succ {k : ℕ} {g c w : G} (hg : HasSynthesisCount H W k g)
      (hw : w ∈ W) (hc : c ∈ H) : HasSynthesisCount H W (k + 1) (c * w * g)

/-- Zero-step `(H, W)`-synthesis coincides with membership in `H`. -/
@[simp]
theorem hasSynthesisCount_zero_iff {G : Type*} [Group G] (H : Subgroup G) (W : Set G) (g : G) :
    HasSynthesisCount H W 0 g ↔ g ∈ H :=
  ⟨by rintro ⟨hc⟩; exact hc, HasSynthesisCount.zero⟩

/-- Every generator `w ∈ W` has `(H, W)`-synthesis count `1`. -/
theorem HasSynthesisCount.of_mem_set {G : Type*} [Group G] {H : Subgroup G} {W : Set G} {w : G}
    (hw : w ∈ W) : HasSynthesisCount H W 1 w := by
  simpa using HasSynthesisCount.succ (HasSynthesisCount.zero H.one_mem) hw H.one_mem

/-- Left multiplication by `h ∈ H` preserves `(H, W)`-synthesis count `k`. -/
theorem HasSynthesisCount.mul_left_of_mem {G : Type*} [Group G] {H : Subgroup G} {W : Set G}
    {k : ℕ} {g h : G} (hh : h ∈ H) (hg : HasSynthesisCount H W k g) :
    HasSynthesisCount H W k (h * g) := by
  cases hg with
  | zero hc => exact .zero (H.mul_mem hh hc)
  | succ hg' hw hc =>
    rw [← mul_assoc, ← mul_assoc]
    exact .succ hg' hw (H.mul_mem hh hc)

/-- Right multiplication by `h ∈ H` preserves `(H, W)`-synthesis count `k`. -/
theorem HasSynthesisCount.mul_right_of_mem {G : Type*} [Group G] {H : Subgroup G} {W : Set G}
    {k : ℕ} {g h : G} (hg : HasSynthesisCount H W k g) (hh : h ∈ H) :
    HasSynthesisCount H W k (g * h) := by
  induction hg with
  | zero hc => exact .zero (H.mul_mem hc hh)
  | succ hg' hw hc ih =>
    rw [mul_assoc]
    exact .succ ih hw hc

/-- Multiplication adds `(H, W)`-synthesis counts. -/
theorem HasSynthesisCount.mul {G : Type*} [Group G] {H : Subgroup G} {W : Set G}
    {k₁ k₂ : ℕ} {g₁ g₂ : G} (hg₁ : HasSynthesisCount H W k₁ g₁)
    (hg₂ : HasSynthesisCount H W k₂ g₂) :
    HasSynthesisCount H W (k₁ + k₂) (g₁ * g₂) := by
  induction hg₁ with
  | zero hc =>
    rw [zero_add]
    exact hg₂.mul_left_of_mem hc
  | succ hg' hw hc ih =>
    rw [Nat.add_right_comm, mul_assoc]
    exact .succ ih hw hc

/-- Image of a `k`-step `(H₁, W₁)`-synthesis under a group homomorphism mapping `H₁` into `H₂`
and `W₁` into `W₂`. -/
theorem HasSynthesisCount.map {G₁ G₂ : Type*} [Group G₁] [Group G₂]
    {H₁ : Subgroup G₁} {H₂ : Subgroup G₂} {W₁ : Set G₁} {W₂ : Set G₂}
    (φ : G₁ →* G₂) (hH : ∀ h ∈ H₁, φ h ∈ H₂) (hW : ∀ w ∈ W₁, φ w ∈ W₂)
    {k : ℕ} {g : G₁} (hg : HasSynthesisCount H₁ W₁ k g) :
    HasSynthesisCount H₂ W₂ k (φ g) := by
  induction hg with
  | zero hc => exact .zero (hH _ hc)
  | succ _ hw hc ih =>
    rw [map_mul, map_mul]
    exact .succ ih (hW _ hw) (hH _ hc)

/-- Minimal `W`-gate count `t_W(g) ∈ ℕ ∪ {∞}` required to synthesize `g : G` using free operations
from `H : Subgroup G` and resource generators from `W : Set G`. -/
noncomputable def gateSynthesisCount {G : Type*} [Group G] (H : Subgroup G) (W : Set G)
    (g : G) : WithTop ℕ :=
  sInf {m : WithTop ℕ | ∃ k : ℕ, m = (k : WithTop ℕ) ∧ HasSynthesisCount H W k g}

/-- Any `k`-step `(H, W)`-realization bounds `gateSynthesisCount H W g` above by `k`. -/
theorem gateSynthesisCount_le_of_hasSynthesisCount {G : Type*} [Group G] {H : Subgroup G}
    {W : Set G} {k : ℕ} {g : G} (hg : HasSynthesisCount H W k g) :
    gateSynthesisCount H W g ≤ (k : WithTop ℕ) :=
  sInf_le ⟨k, rfl, hg⟩

private lemma exists_nat_of_sInf_eq_coe {S : Set (WithTop ℕ)} {k : ℕ}
    (hsInf : sInf S = (k : WithTop ℕ)) : (k : WithTop ℕ) ∈ S := by
  have hne : S.Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    simp [hemp] at hsInf
  have hmem := csInf_mem hne
  rwa [hsInf] at hmem

/-- If `gateSynthesisCount H W g = k` for `k : ℕ`, then `g` admits a `k`-step `(H, W)`-synthesis. -/
theorem exists_hasSynthesisCount_of_gateSynthesisCount_eq_coe {G : Type*} [Group G]
    {H : Subgroup G} {W : Set G} {g : G} {k : ℕ}
    (hk : gateSynthesisCount H W g = (k : WithTop ℕ)) :
    HasSynthesisCount H W k g := by
  obtain ⟨m, hm, hg⟩ := exists_nat_of_sInf_eq_coe hk
  exact Nat.cast_injective hm ▸ hg

/-- Subadditivity of `gateSynthesisCount` under group multiplication. -/
theorem gateSynthesisCount_mul_le {G : Type*} [Group G] (H : Subgroup G) (W : Set G)
    (g₁ g₂ : G) :
    gateSynthesisCount H W (g₁ * g₂) ≤ gateSynthesisCount H W g₁ + gateSynthesisCount H W g₂ := by
  cases h₁ : gateSynthesisCount H W g₁ with
  | top => simp
  | coe k₁ =>
    cases h₂ : gateSynthesisCount H W g₂ with
    | top => simp
    | coe k₂ =>
      rw [← WithTop.coe_add]
      exact gateSynthesisCount_le_of_hasSynthesisCount
        ((exists_hasSynthesisCount_of_gateSynthesisCount_eq_coe h₁).mul
          (exists_hasSynthesisCount_of_gateSynthesisCount_eq_coe h₂))

/-- `gateSynthesisCount H W g = 0` if and only if `g ∈ H`. -/
theorem gateSynthesisCount_eq_zero_iff {G : Type*} [Group G] (H : Subgroup G) (W : Set G)
    (g : G) :
    gateSynthesisCount H W g = 0 ↔ g ∈ H := by
  constructor
  · intro h0
    exact (hasSynthesisCount_zero_iff H W g).mp
      (exists_hasSynthesisCount_of_gateSynthesisCount_eq_coe (by simpa using h0))
  · intro hg
    have hle : gateSynthesisCount H W g ≤ (0 : ℕ) :=
      gateSynthesisCount_le_of_hasSynthesisCount (HasSynthesisCount.zero (W := W) hg)
    exact le_antisymm (by simpa using hle) bot_le

/-- Left `H`-invariance of `gateSynthesisCount`. -/
theorem gateSynthesisCount_mul_left_of_mem {G : Type*} [Group G] (H : Subgroup G) (W : Set G)
    {h : G} (hh : h ∈ H) (g : G) :
    gateSynthesisCount H W (h * g) = gateSynthesisCount H W g := by
  refine le_antisymm ?_ ?_
  · calc gateSynthesisCount H W (h * g)
        ≤ gateSynthesisCount H W h + gateSynthesisCount H W g := gateSynthesisCount_mul_le H W h g
      _ = gateSynthesisCount H W g := by
          rw [(gateSynthesisCount_eq_zero_iff H W h).mpr hh, zero_add]
  · calc gateSynthesisCount H W g
        = gateSynthesisCount H W (h⁻¹ * (h * g)) := by rw [inv_mul_cancel_left]
      _ ≤ gateSynthesisCount H W h⁻¹ + gateSynthesisCount H W (h * g) :=
          gateSynthesisCount_mul_le H W h⁻¹ (h * g)
      _ = gateSynthesisCount H W (h * g) := by
          rw [(gateSynthesisCount_eq_zero_iff H W h⁻¹).mpr (H.inv_mem hh), zero_add]

/-- Right `H`-invariance of `gateSynthesisCount`. -/
theorem gateSynthesisCount_mul_right_of_mem {G : Type*} [Group G] (H : Subgroup G) (W : Set G)
    (g : G) {h : G} (hh : h ∈ H) :
    gateSynthesisCount H W (g * h) = gateSynthesisCount H W g := by
  refine le_antisymm ?_ ?_
  · calc gateSynthesisCount H W (g * h)
        ≤ gateSynthesisCount H W g + gateSynthesisCount H W h := gateSynthesisCount_mul_le H W g h
      _ = gateSynthesisCount H W g := by
          rw [(gateSynthesisCount_eq_zero_iff H W h).mpr hh, add_zero]
  · calc gateSynthesisCount H W g
        = gateSynthesisCount H W ((g * h) * h⁻¹) := by rw [mul_inv_cancel_right]
      _ ≤ gateSynthesisCount H W (g * h) + gateSynthesisCount H W h⁻¹ :=
          gateSynthesisCount_mul_le H W (g * h) h⁻¹
      _ = gateSynthesisCount H W (g * h) := by
          rw [(gateSynthesisCount_eq_zero_iff H W h⁻¹).mpr (H.inv_mem hh), add_zero]

/-- Monotonicity of `gateSynthesisCount` under group homomorphisms. -/
theorem gateSynthesisCount_map_le {G₁ G₂ : Type*} [Group G₁] [Group G₂]
    {H₁ : Subgroup G₁} {H₂ : Subgroup G₂} {W₁ : Set G₁} {W₂ : Set G₂}
    (φ : G₁ →* G₂) (hH : ∀ h ∈ H₁, φ h ∈ H₂) (hW : ∀ w ∈ W₁, φ w ∈ W₂) (g : G₁) :
    gateSynthesisCount H₂ W₂ (φ g) ≤ gateSynthesisCount H₁ W₁ g := by
  cases h : gateSynthesisCount H₁ W₁ g with
  | top => exact le_top
  | coe k =>
    exact gateSynthesisCount_le_of_hasSynthesisCount
      ((exists_hasSynthesisCount_of_gateSynthesisCount_eq_coe h).map φ hH hW)

/-- **Resource-monotone synthesis lower bound**: any real-valued invariant `ν : G → ℝ` vanishing on
`H`, left-invariant under `H`, subadditive under multiplication, and bounded by `c > 0` on `W`
satisfies `ν(g) / c ≤ gateSynthesisCount H W g`. -/
theorem div_le_gateSynthesisCount_of_subadditive {G : Type*} [Group G]
    (H : Subgroup G) (W : Set G) (ν : G → ℝ) {c : ℝ} (hc_pos : 0 < c)
    (hH_zero : ∀ h ∈ H, ν h ≤ 0)
    (hH_left : ∀ h ∈ H, ∀ g : G, ν (h * g) ≤ ν g)
    (hsub : ∀ g₁ g₂ : G, ν (g₁ * g₂) ≤ ν g₁ + ν g₂)
    (hW : ∀ w ∈ W, ν w ≤ c) (g : G) :
    ((ν g / c : ℝ) : WithTop ℝ) ≤ (gateSynthesisCount H W g).map Nat.cast := by
  have hstep : ∀ {k : ℕ} {x : G}, HasSynthesisCount H W k x → ν x ≤ c * (k : ℝ) := by
    intro k x hx
    induction hx with
    | @zero h hh =>
      have h0 : ν h ≤ 0 := hH_zero h hh
      simpa using h0
    | @succ k x' h w _ hw hh ih =>
      calc ν (h * w * x')
          = ν (h * (w * x')) := by rw [mul_assoc]
        _ ≤ ν (w * x') := hH_left h hh (w * x')
        _ ≤ ν w + ν x' := hsub w x'
        _ ≤ c + c * (k : ℝ) := add_le_add (hW w hw) ih
        _ = c * ((k + 1 : ℕ) : ℝ) := by push_cast; ring
  cases h : gateSynthesisCount H W g with
  | top => simp
  | coe k =>
    rw [WithTop.map_coe, WithTop.coe_le_coe, div_le_iff₀ hc_pos, mul_comm]
    exact hstep (exists_hasSynthesisCount_of_gateSynthesisCount_eq_coe h)

/-- For any quantum circuit `C : Cslib.Quantum.Circuit n` whose placed gates all lie in `H ∪ W`, the
number of placed gates satisfying a Boolean resource filter `isResource` (where `¬isResource g`
implies `g.matrix ∈ H` and `isResource g` implies `g.matrix ∈ W`) upper-bounds the synthesis count
of `Circuit.matrix C`. -/
theorem gateSynthesisCount_circuit_le_countP {n : ℕ}
    (H : Subgroup (unitaryGroup (Fin n → Bool) ℂ))
    (W : Set (unitaryGroup (Fin n → Bool) ℂ))
    (isResource : PlacedGate n → Bool)
    (C : Circuit n)
    (hH : ∀ g ∈ C, isResource g = false → g.matrix ∈ H)
    (hW : ∀ g ∈ C, isResource g = true → g.matrix ∈ W) :
    gateSynthesisCount H W (Circuit.matrix C) ≤ (C.countP isResource : WithTop ℕ) := by
  refine gateSynthesisCount_le_of_hasSynthesisCount ?_
  induction C with
  | nil =>
    simp only [Circuit.matrix_nil, List.countP_nil]
    exact HasSynthesisCount.zero H.one_mem
  | cons g gs ih =>
    have ih' := ih
      (fun g' hg' => hH g' (List.mem_cons_of_mem g hg'))
      (fun g' hg' => hW g' (List.mem_cons_of_mem g hg'))
    rw [Circuit.matrix_cons, List.countP_cons]
    cases hrg : isResource g
    · simp only [Bool.false_eq_true, ↓reduceIte, add_zero]
      exact ih'.mul_right_of_mem (hH g List.mem_cons_self hrg)
    · simp only [↓reduceIte]
      have hg1 : HasSynthesisCount H W 1 g.matrix :=
        HasSynthesisCount.of_mem_set (hW g List.mem_cons_self hrg)
      exact ih'.mul hg1

end GateSynthesis

section MultiQubitPauliTransfer

/-- Indexed single-qubit Pauli matrix `0 ↦ I`, `1 ↦ X`, `2 ↦ Y`, `3 ↦ Z` on `Bool`. -/
noncomputable def pauliSingle : Fin 4 → Matrix Bool Bool ℂ
  | 0 => 1
  | 1 => pauliX
  | 2 => pauliY
  | 3 => pauliZ

/-- Every single-qubit Pauli matrix `pauliSingle a` is Hermitian. -/
theorem pauliSingle_isHermitian (a : Fin 4) : (pauliSingle a).IsHermitian := by
  fin_cases a
  · exact Matrix.isHermitian_one
  · exact pauliX_isHermitian
  · exact pauliY_isHermitian
  · exact pauliZ_isHermitian

/-- Every single-qubit Pauli matrix `pauliSingle a` squares to the identity matrix. -/
theorem pauliSingle_mul_self (a : Fin 4) : pauliSingle a * pauliSingle a = 1 := by
  fin_cases a
  · exact Matrix.one_mul 1
  · exact pauliX_mul_self
  · exact pauliY_mul_self
  · exact pauliZ_mul_self

/-- Multi-qubit Pauli string matrix `⨂_{i < n} σ_{u_i}` on `Fin n → Bool`. -/
noncomputable def pauliString {n : ℕ} (u : Fin n → Fin 4) :
    Matrix (Fin n → Bool) (Fin n → Bool) ℂ :=
  piKronecker fun i => pauliSingle (u i)

/-- Every multi-qubit Pauli string `pauliString u` is Hermitian. -/
theorem pauliString_isHermitian {n : ℕ} (u : Fin n → Fin 4) :
    (pauliString u).IsHermitian := by
  ext x y
  simp only [Matrix.conjTranspose_apply, pauliString, piKronecker_apply, star_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  simpa [Matrix.conjTranspose_apply] using
    congrFun (congrFun (pauliSingle_isHermitian (u i)).eq (x i)) (y i)

/-- Every multi-qubit Pauli string `pauliString u` squares to the identity matrix. -/
theorem pauliString_mul_self {n : ℕ} (u : Fin n → Fin 4) :
    pauliString u * pauliString u = 1 := by
  ext x z
  simp only [Matrix.mul_apply, pauliString, piKronecker_apply, ← Finset.prod_mul_distrib,
    ← Fintype.prod_sum fun i y => pauliSingle (u i) (x i) y * pauliSingle (u i) y (z i)]
  have hfactor (i : Fin n) :
      (∑ y : Bool, pauliSingle (u i) (x i) y * pauliSingle (u i) y (z i)) =
        if x i = z i then 1 else 0 := by
    have h := congrFun (congrFun (pauliSingle_mul_self (u i)) (x i)) (z i)
    simpa [Matrix.mul_apply, Matrix.one_apply] using h
  simp_rw [hfactor]
  rw [Matrix.one_apply]
  by_cases hxz : x = z
  · subst hxz; simp
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp hxz
    rw [ite_eq_right hxz]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

/-- Every multi-qubit Pauli string `pauliString u` belongs to `Matrix.unitaryGroup`. -/
theorem pauliString_mem_unitaryGroup {n : ℕ} (u : Fin n → Fin 4) :
    pauliString u ∈ unitaryGroup (Fin n → Bool) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, (pauliString_isHermitian u).eq,
    pauliString_mul_self]

/-- Hilbert–Schmidt trace orthogonality of multi-qubit Pauli strings:
`Tr(σ_u σ_v) = 2^n` if `u = v` and `0` otherwise. -/
theorem trace_pauliString_mul {n : ℕ} (u v : Fin n → Fin 4) :
    (pauliString u * pauliString v).trace = if u = v then (2 : ℂ) ^ n else 0 := by
  have hsingle (a b : Fin 4) :
      (pauliSingle a * pauliSingle b).trace = if a = b then (2 : ℂ) else 0 := by
    fin_cases a <;> fin_cases b <;>
      simp [pauliSingle, Matrix.trace, Matrix.mul_apply] <;> norm_num
  have hmul_kr : pauliString u * pauliString v =
      piKronecker fun i => pauliSingle (u i) * pauliSingle (v i) := by
    ext x z
    simp only [Matrix.mul_apply, pauliString, piKronecker_apply, ← Finset.prod_mul_distrib]
    exact (Fintype.prod_sum fun i y => pauliSingle (u i) (x i) y * pauliSingle (v i) y (z i)).symm
  have hprod : (pauliString u * pauliString v).trace =
      ∏ i : Fin n, (pauliSingle (u i) * pauliSingle (v i)).trace := by
    rw [hmul_kr]
    simp only [Matrix.trace, Matrix.diag_apply, piKronecker_apply]
    exact (Fintype.prod_sum fun i x => (pauliSingle (u i) * pauliSingle (v i)) x x).symm
  rw [hprod]
  simp_rw [hsingle]
  by_cases huv : u = v
  · subst huv; simp
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp huv
    rw [ite_eq_right huv]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

/-- Normalized real Pauli transfer matrix entry `P_U(u | v) = Re(Tr(σ_u U σ_v U†) / 2^n)`. -/
noncomputable def unitaryPauliTransfer {n : ℕ}
    (U : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) (u v : Fin n → Fin 4) : ℝ :=
  (((pauliString u * U * pauliString v * Uᴴ).trace) / ((2 : ℂ) ^ n)).re

/-- Number of `±1` entries in the Pauli transfer matrix of `U`. -/
noncomputable def unitaryPauliOneCount {n : ℕ}
    (U : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) : ℕ :=
  (Finset.univ.filter fun p : (Fin n → Fin 4) × (Fin n → Fin 4) =>
    unitaryPauliTransfer U p.1 p.2 = 1 ∨ unitaryPauliTransfer U p.1 p.2 = -1).card

/-- Unitary stabilizer nullity `v(U) = 2n - log₂ s(U)` [Jiang, Wang]. -/
noncomputable def unitaryStabilizerNullity {n : ℕ}
    (U : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) : ℝ :=
  2 * (n : ℝ) - Real.logb 2 (unitaryPauliOneCount U : ℝ)

end MultiQubitPauliTransfer

end CslibFrontier.Computability.Circuit.Quantum
