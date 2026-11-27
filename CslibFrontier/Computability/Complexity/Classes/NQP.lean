/-
Copyright (c) 2026 The CSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The CSLib contributors
-/
module

public import CslibFrontier.Computability.Complexity.Classes.BQP.Time
public import CslibFrontier.Computability.Complexity.Classes.CeqP
public import CslibFrontier.Computability.Complexity.Classes.Promise.Reduction

import CslibFrontier.Computability.Circuit.Quantum.HadamardLayer
import CslibFrontier.Computability.Complexity.Classes.BQP.Counting
import CslibFrontier.Computability.Complexity.Classes.QMA.NP
import CslibFrontier.Computability.Complexity.Classes.SharpP.Combinators
import CslibFrontier.Computability.Complexity.Problems.CircuitValue.Completeness
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary

/-!
# Nondeterministic Quantum Polynomial Time (`NQP = coC=P`) and Exact Amplitude Amplification

This module defines the quantum complexity class `NQP`
 over polynomial-time uniform families of Hadamard–Toffoli quantum
circuits (`Cslib.Quantum.UniformCircuitFamily`), proves the **Fenner–Green–Homer–Pruim Theorem**
`NQP = coC=P` (with corollaries `NP ⊆ NQP ⊆ PP` and closure of `NQP` and `promiseClass NQP`
under deterministic polynomial-time reductions), and proves Brassard–Høyer–Mosca–Tapp **exact
quantum amplitude amplification** on general complex Hilbert spaces together with its single-step
cubic polynomial law `p ↦ 2 p³ - 6 p² + 9 p / 2` attaining certainty at `p = 1 / 2`. All results
hold unconditionally under standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`).

## Main definitions

* `CslibFrontier.Computability.Complexity.NQP`: nondeterministic quantum polynomial time, the class
  of decision problems accepted with strictly positive probability by a polynomial-time uniform
  Hadamard–Toffoli quantum circuit family.
* `CslibFrontier.Computability.Complexity.PromiseNQP`: lift `promiseClass (NQP enc)` to promise
  problems.
* `CslibFrontier.Computability.Complexity.groverStep`: abstract Grover amplitude-amplification
  operator on a complex inner product space.

## Main results

* `CslibFrontier.Computability.Complexity.NQP_eq_iUnion_NQTIME`: `NQP = ⋃ k, NQTIME[n^k]`.
* `CslibFrontier.Computability.Complexity.NQP_subset_coCeqP`: `NQP ⊆ coC=P` via Fortnow–Rogers
  `GapP` path sums.
* `CslibFrontier.Computability.Complexity.coCeqP_subset_NQP`,
  `CslibFrontier.Computability.Complexity.NQP_eq_coCeqP`: Fenner–Green–Homer–Pruim theorem
  `NQP = coC=P`.
* `CslibFrontier.Computability.Complexity.NP_subset_NQP`,
  `CslibFrontier.Computability.Complexity.NQP_subset_PP`: `NP ⊆ NQP ⊆ PP`.
* `CslibFrontier.Computability.Complexity.groverStep_iterate`: after `j` Grover iterations from
  `sin θ • ψ₀ + cos θ • ψ₁`, the state equals `sin((2 j + 1) θ) • ψ₀ + cos((2 j + 1) θ) • ψ₁`.
* `CslibFrontier.Computability.Complexity.groverStep_one_half_prob`: single-step amplification from
  initial success probability `p / 2` achieves success probability `2 p³ - 6 p² + 9 p / 2`, equal
  to `1` iff `p = 1 / 2` (for `p ∈ [0, 1]`) and at most `1 - 2 (p - 1 / 2)²` throughout `[0, 1]`.

## Tags

NQP, coC=P, quantum complexity, counting complexity, amplitude amplification, Grover iteration
-/

public section

open Finset
open Cslib.Quantum Cslib.Quantum.GateCode Cslib.Complexity Turing.MultiTapeTM
open scoped BigOperators

namespace CslibFrontier.Computability.Complexity

/-! ### 1. Exact quantum amplitude amplification -/

section AmplitudeAmplification

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Orthogonal reflection `w ↦ w - 2 ⟪u, w⟫ u` reversing a unit vector `u` and fixing `uᗮ`. -/
noncomputable def reflectAlong (u : H) (w : H) : H :=
  w - ((2 : ℂ) * inner ℂ u w) • u

/-- Abstract Grover amplitude-amplification operator `G(ψ₀, φ) = -S_φ ∘ S_{ψ₀}`, where
`S_φ(v) = v - 2 ⟪φ, v⟫ φ` reflects across `φᗮ` and `S_{ψ₀}(v) = v - 2 ⟪ψ₀, v⟫ ψ₀` reflects across
the good state `ψ₀`. -/
noncomputable def groverStep (ψ₀ φ : H) (w : H) : H :=
  -reflectAlong φ (reflectAlong ψ₀ w)

@[simp]
theorem reflectAlong_zero (u : H) : reflectAlong u 0 = 0 := by
  simp [reflectAlong]

@[simp]
theorem groverStep_zero (ψ₀ φ : H) : groverStep ψ₀ φ 0 = 0 := by
  simp [groverStep]

theorem norm_reflectAlong {u : H} (hu : ‖u‖ = 1) (w : H) :
    ‖reflectAlong u w‖ = ‖w‖ := by
  have huu : inner ℂ u u = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hu]; norm_num
  have hsq : ‖reflectAlong u w‖ ^ 2 = ‖w‖ ^ 2 := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), norm_sq_eq_re_inner (𝕜 := ℂ), reflectAlong]
    simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right, huu, mul_one,
      map_mul, Complex.conj_ofNat, inner_conj_symm w u]
    congr 1
    ring
  nlinarith [norm_nonneg (reflectAlong u w), norm_nonneg w]

theorem norm_groverStep {ψ₀ φ : H} (hψ₀ : ‖ψ₀‖ = 1) (hφ : ‖φ‖ = 1) (w : H) :
    ‖groverStep ψ₀ φ w‖ = ‖w‖ := by
  rw [groverStep, norm_neg, norm_reflectAlong hφ, norm_reflectAlong hψ₀]

/-- Two-dimensional rotation action of `groverStep ψ₀ φ` on the invariant plane
`span {ψ₀, ψ₁}` for `φ = sin θ • ψ₀ + cos θ • ψ₁`: sends
`sin α • ψ₀ + cos α • ψ₁` to `sin(α + 2 θ) • ψ₀ + cos(α + 2 θ) • ψ₁`. -/
theorem groverStep_apply_plane {ψ₀ ψ₁ : H} (hψ₀ : ‖ψ₀‖ = 1) (hψ₁ : ‖ψ₁‖ = 1)
    (horth : inner ℂ ψ₀ ψ₁ = 0) (θ α : ℝ) :
    let φ := (Real.sin θ : ℂ) • ψ₀ + (Real.cos θ : ℂ) • ψ₁
    groverStep ψ₀ φ ((Real.sin α : ℂ) • ψ₀ + (Real.cos α : ℂ) • ψ₁) =
      (Real.sin (α + 2 * θ) : ℂ) • ψ₀ + (Real.cos (α + 2 * θ) : ℂ) • ψ₁ := by
  intro φ
  have h00 : inner ℂ ψ₀ ψ₀ = 1 := by rw [inner_self_eq_norm_sq_to_K, hψ₀]; norm_num
  have h11 : inner ℂ ψ₁ ψ₁ = 1 := by rw [inner_self_eq_norm_sq_to_K, hψ₁]; norm_num
  have h10 : inner ℂ ψ₁ ψ₀ = 0 := by rw [← inner_conj_symm, horth, map_zero]
  have hs0 : reflectAlong ψ₀ ((Real.sin α : ℂ) • ψ₀ + (Real.cos α : ℂ) • ψ₁) =
      (-(Real.sin α : ℂ)) • ψ₀ + (Real.cos α : ℂ) • ψ₁ := by
    simp only [reflectAlong, inner_add_right, inner_smul_right, h00, horth, mul_one, mul_zero,
      add_zero]
    module
  rw [groverStep, hs0]
  have hin : inner ℂ φ ((-(Real.sin α : ℂ)) • ψ₀ + (Real.cos α : ℂ) • ψ₁) =
      ((Real.cos θ * Real.cos α - Real.sin θ * Real.sin α : ℝ) : ℂ) := by
    simp only [φ, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
      h00, h11, horth, h10, Complex.conj_ofReal]
    push_cast; ring
  rw [reflectAlong, hin]
  dsimp only [φ]
  have hsin : Real.sin (α + 2 * θ) =
      Real.sin α + 2 * (Real.cos θ * Real.cos α - Real.sin θ * Real.sin α) * Real.sin θ := by
    rw [Real.sin_add, Real.sin_two_mul, Real.cos_two_mul]
    linear_combination 2 * Real.sin α * Real.sin_sq_add_cos_sq θ
  have hcos : Real.cos (α + 2 * θ) =
      2 * (Real.cos θ * Real.cos α - Real.sin θ * Real.sin α) * Real.cos θ - Real.cos α := by
    rw [Real.cos_add, Real.sin_two_mul, Real.cos_two_mul]
    ring
  rw [hsin, hcos]
  push_cast
  module

/-- **Exact Quantum Amplitude Amplification**:
for orthonormal states `ψ₀, ψ₁` and initial state `φ = sin θ • ψ₀ + cos θ • ψ₁` (initial good
probability `a = sin² θ`), `j` applications of `groverStep ψ₀ φ` yield
`sin((2 j + 1) θ) • ψ₀ + cos((2 j + 1) θ) • ψ₁`, with exact good probability
`sin²((2 j + 1) θ)`.
-/
theorem groverStep_iterate {ψ₀ ψ₁ : H} (hψ₀ : ‖ψ₀‖ = 1) (hψ₁ : ‖ψ₁‖ = 1)
    (horth : inner ℂ ψ₀ ψ₁ = 0) (θ : ℝ) (j : ℕ) :
    let φ := (Real.sin θ : ℂ) • ψ₀ + (Real.cos θ : ℂ) • ψ₁
    (groverStep ψ₀ φ)^[j] φ =
      (Real.sin ((2 * (j : ℝ) + 1) * θ) : ℂ) • ψ₀ +
        (Real.cos ((2 * (j : ℝ) + 1) * θ) : ℂ) • ψ₁ := by
  intro φ
  induction j with
  | zero => simp [φ]
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih, groverStep_apply_plane hψ₀ hψ₁ horth,
      show (2 * (j : ℝ) + 1) * θ + 2 * θ = (2 * ((j + 1 : ℕ) : ℝ) + 1) * θ by push_cast; ring]

/-- Squared overlap with the good state `ψ₀` after `j` Grover steps equals `sin²((2 j + 1) θ)`. -/
theorem norm_sq_inner_groverStep_iterate {ψ₀ ψ₁ : H} (hψ₀ : ‖ψ₀‖ = 1) (hψ₁ : ‖ψ₁‖ = 1)
    (horth : inner ℂ ψ₀ ψ₁ = 0) (θ : ℝ) (j : ℕ) :
    let φ := (Real.sin θ : ℂ) • ψ₀ + (Real.cos θ : ℂ) • ψ₁
    ‖inner ℂ ψ₀ ((groverStep ψ₀ φ)^[j] φ)‖ ^ 2 = Real.sin ((2 * (j : ℝ) + 1) * θ) ^ 2 := by
  intro φ
  have h00 : inner ℂ ψ₀ ψ₀ = 1 := by rw [inner_self_eq_norm_sq_to_K, hψ₀]; norm_num
  rw [groverStep_iterate hψ₀ hψ₁ horth θ j, inner_add_right, inner_smul_right, inner_smul_right,
    h00, horth, mul_one, mul_zero, add_zero, Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- **Single-step exact amplification identity**: when `sin² θ = p / 2` (obtained by combining an
algorithm of success probability `p` with a fair Hadamard coin), a single Grover iteration yields
exact success probability `sin²(3 θ) = 2 p³ - 6 p² + 9 p / 2 = 1 - 2 (2 - p) (p - 1 / 2)²`,
which equals `1` if and only if `p = 1 / 2` (for `p ∈ [0, 1]`) and has rejection probability
`1 - sin²(3 θ) ≥ 2 (p - 1 / 2)²`. -/
theorem groverStep_one_half_prob {θ p : ℝ} (hθ : Real.sin θ ^ 2 = p / 2) :
    Real.sin (3 * θ) ^ 2 = 2 * p ^ 3 - 6 * p ^ 2 + 9 * p / 2 ∧
    1 - Real.sin (3 * θ) ^ 2 = 2 * (2 - p) * (p - 1 / 2) ^ 2 := by
  have h3 : Real.sin (3 * θ) = 3 * Real.sin θ - 4 * Real.sin θ ^ 3 := Real.sin_three_mul θ
  have hsq : Real.sin (3 * θ) ^ 2 = Real.sin θ ^ 2 * (3 - 4 * Real.sin θ ^ 2) ^ 2 := by
    rw [h3]; ring
  rw [hsq, hθ]
  constructor <;> ring

theorem groverStep_one_reject_eq_zero_iff {p : ℝ} (hp1 : p ≤ 1) :
    1 - (2 * p ^ 3 - 6 * p ^ 2 + 9 * p / 2) = 0 ↔ p = 1 / 2 := by
  have hfac : 1 - (2 * p ^ 3 - 6 * p ^ 2 + 9 * p / 2) = 2 * (2 - p) * (p - 1 / 2) ^ 2 := by ring
  rw [hfac]
  refine ⟨fun h => ?_, fun h => by rw [h]; ring⟩
  have h2p : 0 < 2 * (2 - p) := by linarith
  have hsq0 : (p - 1 / 2) ^ 2 = 0 := (mul_eq_zero.mp h).resolve_left h2p.ne'
  nlinarith

theorem two_mul_sub_half_sq_le_groverStep_one_reject {p : ℝ} (hp1 : p ≤ 1) :
    2 * (p - 1 / 2) ^ 2 ≤ 1 - (2 * p ^ 3 - 6 * p ^ 2 + 9 * p / 2) := by
  have hfac : 1 - (2 * p ^ 3 - 6 * p ^ 2 + 9 * p / 2) - 2 * (p - 1 / 2) ^ 2 =
      2 * (1 - p) * (p - 1 / 2) ^ 2 := by ring
  nlinarith [sq_nonneg (p - 1 / 2)]

end AmplitudeAmplification

/-! ### 2. Nondeterministic quantum polynomial time and `NQP = coC=P` -/

section NQPClass

variable {α : Type} {enc : α ↪ List Bool}

/-- **Nondeterministic quantum polynomial time (`NQP`)**
: decision problems whose members are accepted with strictly
positive probability (and non-members with probability `0`) by a polynomial-time uniform family
of quantum circuits over `{H, NOT, CNOT, Toffoli}`.
-/
@[expose] def NQP (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ F : UniformCircuitFamily, ∀ a, a ∈ A ↔ 0 < F.acceptProb (enc a)}

/-- Promise lift `promiseClass (NQP enc)` of nondeterministic quantum polynomial time: promise
problems separated by an `NQP` language (equivalently, admitting a uniform quantum circuit family
accepting yes-instances with probability `> 0` and no-instances with probability `0`). -/
@[expose] def PromiseNQP (enc : α ↪ List Bool) : Set (PromiseProblem α) :=
  promiseClass (NQP enc)

theorem mem_PromiseNQP_iff {Q : PromiseProblem α} :
    Q ∈ PromiseNQP enc ↔ ∃ F : UniformCircuitFamily,
      (∀ a ∈ Q.yes, 0 < F.acceptProb (enc a)) ∧
      (∀ a ∈ Q.no, F.acceptProb (enc a) = 0) := by
  refine ⟨fun ⟨A, ⟨F, hF⟩, hyes, hno⟩ => ⟨F, fun a ha => (hF a).mp (hyes ha), fun a ha => ?_⟩,
    fun ⟨F, hyes, hno⟩ => ?_⟩
  · have hnot : ¬0 < F.acceptProb (enc a) :=
      fun hp => Set.disjoint_right.mp hno ha ((hF a).mpr hp)
    exact le_antisymm (not_lt.mp hnot) (F.acceptProb_nonneg _)
  · refine ⟨{a | 0 < F.acceptProb (enc a)}, ⟨F, fun _ => Iff.rfl⟩, hyes,
      Set.disjoint_right.mpr fun a ha hp => ?_⟩
    change 0 < F.acceptProb (enc a) at hp
    rw [hno a ha] at hp
    exact lt_irrefl 0 hp

theorem NQTIME_subset_NQP (t : ℕ → ℕ) : NQTIME enc t ⊆ NQP enc :=
  fun _ ⟨F, _, _, _, hF⟩ => ⟨F, hF⟩

/-- `NQP` is the union of the polynomial nondeterministic quantum time classes `NQTIME[n^k]`. -/
theorem NQP_eq_iUnion_NQTIME : NQP enc = ⋃ k : ℕ, NQTIME enc fun n => n ^ k := by
  refine Set.Subset.antisymm (fun A ⟨F, hF⟩ => ?_) (Set.iUnion_subset fun _ => NQTIME_subset_NQP _)
  obtain ⟨c, d, hc⟩ := F.computableInPolyTime_gates.polyBounded_length.exists_le
  refine Set.mem_iUnion.mpr ⟨d, F, c * 2 ^ d, c, fun n => ?_, hF⟩
  have h1 := (length_le_length_encList encGateCode (F.gates n)).trans (hc n)
  rw [encUnary_apply, List.length_replicate] at h1
  have h2 : (n + 1) ^ d ≤ 2 ^ d * n ^ d + 1 := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rcases Nat.eq_zero_or_pos d with rfl | hd
      · simp
      · simp [Nat.zero_pow hd]
    · calc (n + 1) ^ d ≤ (2 * n) ^ d := Nat.pow_le_pow_left (by omega) d
        _ = 2 ^ d * n ^ d := mul_pow 2 n d
        _ ≤ _ := Nat.le_succ _
  calc (F.gates n).length ≤ c * (n + 1) ^ d := h1
    _ ≤ c * (2 ^ d * n ^ d + 1) := Nat.mul_le_mul_left _ h2
    _ = c * 2 ^ d * n ^ d + c := by ring

/-- **`NQP ⊆ coC=P`**: the acceptance probability of
a uniform Hadamard–Toffoli family is `acceptGap / 2^h ≥ 0` with `acceptGap ∈ GapP`, hence is
strictly positive precisely when `acceptGap ≠ 0`.
-/
theorem NQP_subset_coCeqP : NQP enc ⊆ coCeqP enc := by
  rintro A ⟨F, hF⟩
  refine mem_coCeqP_iff_exists_GapP.mpr ⟨_, acceptGap_mem_GapP (enc := enc) F, fun a => ?_⟩
  rw [hF a]
  have hp : F.acceptProb (enc a) = _ :=
    acceptProb_eq_acceptGap _ (F.wellFormed (enc a).length) (enc a)
  set g := acceptGap (F.gates (enc a).length)
    (List.ofFn (inputState (F.width (enc a).length) (enc a)))
  set r := hadamardCount (F.gates (enc a).length)
  have hpos : (0 : ℝ) < (2 : ℝ) ^ r := by positivity
  have hnn : 0 ≤ F.acceptProb (enc a) := F.acceptProb_nonneg (enc a)
  rw [hp] at hnn ⊢
  refine ⟨fun hgt h0 => by simp [h0] at hgt, fun hne => div_pos ?_ hpos⟩
  have hgnn : (0 : ℝ) ≤ g := by
    have := (le_div_iff₀ hpos).mp hnn
    linarith
  have hgne : (g : ℝ) ≠ 0 := by exact_mod_cast hne
  exact lt_of_le_of_ne hgnn hgne.symm

/-! #### Reversible all-zero detector and phase-kickback circuit for `coC=P ⊆ NQP` -/

/-- Classical gate codes computing `∀ j < m, X[o + j] = false` onto fresh zero wire `a + m`, using
fresh zero ancillas `a, a + 1, …, a + m` (where `m ≥ 1` and `o + m ≤ a`). -/
private def allZeroCodes (o m a : ℕ) : List GateCode :=
  let flip := (List.range m).map fun j => (false, o + j, [])
  let init := [(false, a, [o])]
  let chain := (List.range (m - 1)).map fun j => (false, a + j + 1, [a + j, o + j + 1])
  flip ++ init ++ chain

private theorem isClassical_allZeroCodes {W o m a : ℕ} (hm : 1 ≤ m) (hoa : o + m ≤ a)
    (haW : a + m ≤ W) : IsClassical W (allZeroCodes o m a) := by
  simp only [allZeroCodes, IsClassical.append]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro g hg
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hg
    rw [List.mem_range] at hj
    exact ⟨rfl, by simp, by simp, by simp; omega⟩
  · intro g hg
    rw [List.mem_singleton] at hg; subst hg
    exact ⟨rfl, by simp, by simp; omega, by simp; omega⟩
  · intro g hg
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hg
    rw [List.mem_range] at hj
    exact ⟨rfl, by simp, by simp; omega, by simp; omega⟩

private theorem readBit_classicalRun_allZeroCodes {W o m a : ℕ} (hm : 1 ≤ m) (hoa : o + m ≤ a)
    (haW : a + m ≤ W) {X : Fin W → Bool} (hanc : ∀ j < m, readBit X (a + j) = false) :
    readBit (classicalRun (allZeroCodes o m a) X) (a + m - 1) =
      decide (∀ j : Fin m, X ⟨o + j, by omega⟩ = false) := by
  let flip := (List.range m).map fun j => ((false, o + j, []) : GateCode)
  let init := [((false, a, [o]) : GateCode)]
  let chain (t : ℕ) :=
    (List.range t).map fun j => ((false, a + j + 1, [a + j, o + j + 1]) : GateCode)
  change readBit (classicalRun (flip ++ init ++ chain (m - 1)) X) (a + m - 1) = _
  rw [classicalRun_append, classicalRun_append]
  set X₁ := classicalRun flip X
  have hX₁_block : ∀ j < m, readBit X₁ (o + j) = !readBit X (o + j) := by
    intro j hj
    have hmem : ((false, o + j, []) : GateCode) ∈ flip :=
      List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩
    have hnd : (flip.map target).Nodup := by
      simp only [flip, List.map_map, Function.comp_def, target_mk]
      exact List.nodup_range.map fun i₁ i₂ h => by omega
    rw [readBit_classicalRun_of_mem (fun g hg => by
        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hg; rw [List.mem_range] at hi; simp; omega)
      hnd (fun _ _ g' hg' => by obtain ⟨i, _, rfl⟩ := List.mem_map.mp hg'; simp) X hmem]
    simp
  have hX₁_anc : ∀ j < m, readBit X₁ (a + j) = false := by
    intro j hj
    rw [readBit_classicalRun_of_forall_ne (fun g hg => by
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hg; rw [List.mem_range] at hi; simp; omega)]
    exact hanc j hj
  set X₂ := classicalRun init X₁
  have hX₂_0 : readBit X₂ a = !readBit X o := by
    simp only [X₂, init, classicalRun_cons, classicalRun_nil, readBit_classicalStep, target_mk,
      controls_mk, List.all_cons, List.all_nil, Bool.and_true]
    have ha0 : readBit X₁ a = false := by simpa using hX₁_anc 0 (by omega)
    have ho0 : readBit X₁ o = !readBit X o := by simpa using hX₁_block 0 (by omega)
    simp [ha0, ho0, show a < W by omega]
  have hX₂_anc : ∀ j, 1 ≤ j → j < m → readBit X₂ (a + j) = false := by
    intro j hj1 hjm
    rw [readBit_classicalRun_of_forall_ne (fun g hg => by
      rw [List.mem_singleton] at hg; subst hg; simp; omega)]
    exact hX₁_anc j hjm
  have hX₂_block : ∀ j < m, readBit X₂ (o + j) = !readBit X (o + j) := by
    intro j hj
    rw [readBit_classicalRun_of_forall_ne (fun g hg => by
      rw [List.mem_singleton] at hg; subst hg; simp; omega)]
    exact hX₁_block j hj
  -- Induct on `t ≤ m - 1`: wire `a + t` holds `∀ j ≤ t, X[o + j] = false`, wires `> a + t` stay 0.
  have hchain : ∀ t ≤ m - 1,
      readBit (classicalRun (chain t) X₂) (a + t) =
        decide (∀ j ≤ t, readBit X (o + j) = false) ∧
      (∀ s, t < s → s < m → readBit (classicalRun (chain t) X₂) (a + s) = false) ∧
      (∀ j < m, readBit (classicalRun (chain t) X₂) (o + j) = !readBit X (o + j)) := by
    intro t ht
    induction t with
    | zero =>
      simp only [chain, List.range_zero, List.map_nil, classicalRun_nil, add_zero,
        Nat.le_zero, forall_eq, hX₂_0]
      refine ⟨by cases readBit X o <;> simp, fun s hs hsm => hX₂_anc s hs hsm, hX₂_block⟩
    | succ t ih =>
      obtain ⟨hprev, hrest, hblk⟩ := ih (by omega)
      have hsplit : chain (t + 1) = chain t ++ [(false, a + t + 1, [a + t, o + t + 1])] := by
        simp [chain, List.range_succ]
      rw [hsplit, classicalRun_append]
      set Y := classicalRun (chain t) X₂
      simp only [classicalRun_cons, classicalRun_nil]
      refine ⟨?_, ?_, ?_⟩
      · rw [readBit_classicalStep]
        have hlt : a + t + 1 < W := by omega
        have hY0 : readBit Y (a + (t + 1)) = false := hrest (t + 1) (by omega) (by omega)
        have hYblk : readBit Y (o + (t + 1)) = !readBit X (o + (t + 1)) := hblk (t + 1) (by omega)
        simp only [target_mk, controls_mk, show a + (t + 1) = a + t + 1 by omega,
          show o + (t + 1) = o + t + 1 by omega, hlt, and_self, decide_true, Bool.true_and,
          List.all_cons, List.all_nil, Bool.and_true] at hY0 hYblk ⊢
        rw [hY0, hprev, hYblk, Bool.false_xor]
        have hiff : ((∀ j ≤ t, readBit X (o + j) = false) ∧ readBit X (o + t + 1) = false) ↔
            ∀ j ≤ t + 1, readBit X (o + j) = false := by
          refine ⟨fun ⟨h1, h2⟩ j hj => ?_, fun h => ⟨fun j hj => h j (by omega),
            by simpa [Nat.add_assoc] using h (t + 1) le_rfl⟩⟩
          rcases Nat.of_le_succ hj with hjt | rfl
          · exact h1 j hjt
          · simpa [Nat.add_assoc] using h2
        cases hrb : readBit X (o + t + 1) <;>
          by_cases hall : ∀ j ≤ t, readBit X (o + j) = false <;>
          simp [← hiff, hrb, hall]
      · intro s hs hsm
        rw [readBit_classicalStep]
        simp [show a + s ≠ a + t + 1 by omega, hrest s (by omega) hsm]
      · intro j hjm
        rw [readBit_classicalStep]
        simp [show o + j ≠ a + t + 1 by omega, hblk j hjm]
  have hres := (hchain (m - 1) le_rfl).1
  rw [show a + (m - 1) = a + m - 1 by omega] at hres
  rw [hres]
  congr 1
  refine propext ⟨fun h ⟨j, hj⟩ => ?_, fun h j hj => ?_⟩
  · have := h j (by omega)
    rwa [readBit_of_lt _ (by omega)] at this
  · have := h ⟨j, by omega⟩
    rwa [readBit_of_lt _ (by omega)]

/-- General Hadamard layer evaluation on an arbitrary basis string `X` (not necessarily zero on the
block `o, …, o + m - 1`): applies `H^{\otimes m}` with Walsh–Hadamard sign
`(-1)^{∑_i X(o+i) ∧ r_i}`. -/
private theorem eval_hadamardCodes_ket_any {W o m : ℕ} (h : o + m ≤ W) (X : Fin W → Bool) :
    Circuit.eval (Circuit.ofCodes W (hadamardCodes o m)) (ket X) =
      ∑ r : Fin m → Bool,
        ((∏ i : Fin m, (if X (blockEmb o h i) && r i then (-1 : ℂ) else 1)) *
          (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) ^ m) • ket (glue (blockEmb o h) r X) := by
  induction m with
  | zero =>
    have hg (r : Fin 0 → Bool) : glue (blockEmb o h) r X = X := by
      funext i; rw [glue_blockEmb_apply]; exact dite_eq_right_iff.mpr fun h' => by omega
    simp [hadamardCodes, hg]
  | succ m ih =>
    have h' : o + m ≤ W := by omega
    have ht : o + m < W := by omega
    rw [hadamardCodes, List.range_succ, List.map_append, Circuit.ofCodes_append,
      Circuit.eval_append,
      show (List.range m).map (fun j => ((true, o + j, []) : GateCode)) = hadamardCodes o m
        from rfl, ih h']
    obtain ⟨g, hg⟩ : ∃ g, toPlacedGate? W (true, o + m, []) = some g :=
      Option.isSome_iff_exists.mp (isSome_toPlacedGate?_iff.mpr ⟨ht, rfl⟩)
    have hC : Circuit.ofCodes W [(true, o + m, [])] = [g] := by simp [Circuit.ofCodes, hg]
    simp only [List.map_cons, List.map_nil, hC, map_sum, map_smul, Circuit.eval_cons,
      Circuit.eval_nil, eval_toPlacedGate_hadamard_ket hg ht]
    have hlast (r : Fin m → Bool) :
        glue (blockEmb o h') r X ⟨o + m, ht⟩ = X (blockEmb o h (Fin.last m)) := by
      rw [glue_blockEmb_apply, dite_eq_right (by simp)]
      exact congrArg X (Fin.ext (by simp; omega))
    have hupd (r : Fin m → Bool) (c : Bool) :
        Function.update (glue (blockEmb o h') r X) ⟨o + m, ht⟩ c =
          glue (blockEmb o h) (Fin.snoc r c) X := by
      funext i
      by_cases hi : (i : ℕ) = o + m
      · rw [show i = ⟨o + m, ht⟩ from Fin.ext hi, Function.update_self, glue_blockEmb_apply,
          dite_eq_left (by simp)]
        simp [Fin.snoc]
      · rw [Function.update_of_ne (fun he => hi (congrArg Fin.val he)), glue_blockEmb_apply,
          glue_blockEmb_apply]
        by_cases hi' : o ≤ (i : ℕ) ∧ (i : ℕ) < o + m
        · have hi'' : o ≤ (i : ℕ) ∧ (i : ℕ) < o + (m + 1) := ⟨hi'.1, by omega⟩
          have hsub : (i : ℕ) - o < m := by omega
          rw [dite_eq_left hi', dite_eq_left hi'']
          exact (Fin.snoc_castSucc (α := fun _ => Bool) c r ⟨(i : ℕ) - o, hsub⟩).symm
        · rw [dite_eq_right hi', dite_eq_right (by omega)]
    simp only [hlast, hupd, smul_sum, smul_smul]
    rw [← (Fin.snocEquiv fun _ => Bool).sum_comp, Fintype.sum_prod_type, sum_comm]
    refine sum_congr rfl fun r _ => sum_congr rfl fun c _ => ?_
    congr 1
    simp only [Fin.snocEquiv_apply, Fin.prod_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last,
      pow_succ]
    have hcast : ∀ i : Fin m, X (blockEmb o h i.castSucc) = X (blockEmb o h' i) := fun i =>
      congrArg X (Fin.ext (by simp))
    simp_rw [hcast]
    ring

/-- Phase kickback on a single qubit initialized to `|-⟩ = (|0⟩ - |1⟩) / √2`: running any classical
circuit `gs` whose gates never read the kickback qubit `pk` and flip `pk` to `pk ^^ φ(X)` maps
`2^{-1/2} ∑_c (-1)^c |X[pk := c]⟩` to `(-1)^{φ(X)} · 2^{-1/2} ∑_c (-1)^c |Y[pk := c]⟩` where `Y`
is the action of `gs` on `X[pk := false]`. -/
private theorem classicalUnrun_eq_classicalRun_reverse {W : ℕ} (gs : List GateCode)
    (x : Fin W → Bool) : classicalUnrun gs x = classicalRun gs.reverse x := by
  rw [classicalUnrun, classicalRun, List.foldl_reverse]

private theorem isClassical_reverse {W : ℕ} {gs : List GateCode} (h : IsClassical W gs) :
    IsClassical W gs.reverse := fun g hg => h g (List.mem_reverse.mp hg)

private theorem readBit_classicalRun_shift {W N o : ℕ} (hM' : o + N ≤ W)
    (gs : List GateCode) (Z : Fin W → Bool)
    (hgs : ∀ gc ∈ gs, gc.1 = false ∧ WellFormed N gc) {k : ℕ} (hk : k < N) :
    readBit (classicalRun (gs.map (shift o)) Z) (o + k) =
      readBit (classicalRun gs (Z ∘ blockEmb o hM')) k := by
  induction gs generalizing Z with
  | nil =>
    rw [List.map_nil, classicalRun_nil, classicalRun_nil,
      readBit_of_lt _ (by omega), readBit_of_lt _ hk, Function.comp_apply]
    exact congrArg Z (Fin.ext (by simp [blockEmb_apply_val]; omega))
  | cons gc gs ih =>
    obtain ⟨⟨h1, h2⟩, hrest⟩ := List.forall_mem_cons.mp hgs
    rw [List.map_cons, classicalRun_cons, classicalRun_cons, ih _ hrest]
    congr 2
    obtain ⟨b, t, cs⟩ := gc; subst h1
    have ht : t < N := h2.2.2 t List.mem_cons_self
    funext i
    have hiW : o + (i : ℕ) < W := by omega
    have h1' := readBit_classicalStep (shift o (false, t, cs)) Z (o + i)
    have h2' := readBit_classicalStep (false, t, cs) (Z ∘ blockEmb o hM') i
    rw [readBit_of_lt _ hiW] at h1'
    rw [readBit_of_lt _ i.2] at h2'
    have hlhs : (classicalStep (shift o (false, t, cs)) Z ∘ blockEmb o hM') i =
        classicalStep (shift o (false, t, cs)) Z ⟨o + i, hiW⟩ :=
      congrArg (classicalStep (shift o (false, t, cs)) Z)
        (Fin.ext (by simp [blockEmb_apply_val]; omega))
    rw [hlhs, h1', h2']
    have hrb_i : readBit Z (o + i) = readBit (Z ∘ blockEmb o hM') i := by
      rw [readBit_of_lt _ hiW, readBit_of_lt _ i.2, Function.comp_apply]
      exact congrArg Z (Fin.ext (by simp [blockEmb_apply_val]; omega))
    have hall_c : ((controls (shift o (false, t, cs))).all (readBit Z)) =
        (cs.all (readBit (Z ∘ blockEmb o hM'))) := by
      apply Bool.eq_iff_iff.mpr
      simp only [shift, controls_mk, List.all_map, List.all_eq_true]
      refine forall_congr' fun u => imp_congr_right fun hu => ?_
      have hu_lt : u < N := h2.2.2 u (List.mem_cons_of_mem _ hu)
      have huW : u + o < W := by omega
      rw [Function.comp_apply, readBit_of_lt _ huW, readBit_of_lt _ hu_lt, Function.comp_apply]
      exact iff_of_eq (congrArg (fun b => b = true)
        (congrArg Z (Fin.ext (by simp [blockEmb_apply_val]))))
    rw [hrb_i, hall_c]
    congr 2
    have htW : o + t < W := by omega
    by_cases hit : (i : ℕ) = t
    · simp [shift, hit, htW, ht, Nat.add_comm]
    · have hit' : o + (i : ℕ) ≠ t + o := by omega
      simp [shift, hit, hit']

private theorem readBit_frame_and_codes {W n m : ℕ}
    (code : List (Cslib.Circuits.Boolean.Op × List ℕ) × List ℕ)
    (hW : (n + m) + (2 * n + 1 + m + code.1.length + 1) ≤ W)
    {x : List Bool} (hx : x.length = n) (z : Fin m → Bool) :
    readBit (classicalRun
      (NPVerifier.frameCodes n m (n + m) ++
        (Reversible.codes (2 * n + 1 + m) (2 * n + 1 + m + code.1.length) code.1).map
          (shift (n + m)))
      (inputState W (x ++ List.ofFn z)))
      (n + m + Reversible.outQubit (2 * n + 1 + m + code.1.length) (code.2.getD 0 0)) =
    Cslib.Circuits.Boolean.evalOutput (frame x ++ List.ofFn z) code.1 (code.2.getD 0 0) := by
  set M := 2 * n + 1 + m
  set Xf := classicalRun (NPVerifier.frameCodes n m (n + m)) (inputState W (x ++ List.ofFn z))
  set rk := Reversible.outQubit (M + code.1.length) (code.2.getD 0 0)
  have hrk_lt : rk < M + code.1.length + 1 := by dsimp only [rk, Reversible.outQubit]; omega
  rw [classicalRun_append,
    readBit_classicalRun_shift hW _ Xf (Reversible.isClassical_codes le_rfl (by omega)) hrk_lt]
  have hlen_fx : (frame x ++ List.ofFn z).length = M := by
    rw [List.length_append, length_frame, List.length_ofFn, hx]
  have hXf : ∀ k, readBit (Xf ∘ blockEmb (n + m) hW) k =
      (frame x ++ List.ofFn z).getD k false := fun k => by
    by_cases hk : k < M + code.1.length + 1
    · rw [readBit_of_lt _ hk, Function.comp_apply,
        show Xf (blockEmb (n + m) hW ⟨k, hk⟩) = readBit Xf (n + m + k) by
          rw [readBit_of_lt _ (by omega)]
          exact congrArg Xf (Fin.ext (by simp [blockEmb_apply_val]; omega))]
      exact NPVerifier.readBit_classicalRun_frameCodes (by omega) le_rfl hx z k
    · rw [readBit_of_le _ (not_lt.mp hk), List.getD_eq_getElem?_getD,
        List.getElem?_eq_none (by omega), Option.getD_none]
  rw [Reversible.readBit_classicalRun_codes le_rfl (by omega) hlen_fx hXf,
    Cslib.Circuits.Boolean.evalOutput]
  have hlen_ev : (Cslib.Circuits.evalCode Cslib.Circuits.Boolean.interpretation false
      (frame x ++ List.ofFn z) code.1).length = M + code.1.length := by simp [hlen_fx]
  dsimp only [rk, Reversible.outQubit]
  rcases le_or_gt (M + code.1.length) (code.2.getD 0 0) with hle | hlt
  · rw [min_eq_left hle, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]
  · rw [min_eq_right hlt.le]

private theorem eval_prep_minus {W p : ℕ} (hp : p < W) (X : Fin W → Bool)
    (hXp : X ⟨p, hp⟩ = false) :
    Circuit.eval (Circuit.ofCodes W [(false, p, []), (true, p, [])]) (ket X) =
      ∑ c : Bool, ((if c then (-1 : ℂ) else 1) * (((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) •
        ket (Function.update X ⟨p, hp⟩ c) := by
  have hcl1 : IsClassical W [(false, p, [])] := fun gc hgc => by
    rw [List.mem_singleton] at hgc; subst hgc
    exact ⟨rfl, by simp, by simp, by simp [hp]⟩
  have hsplit : [(false, p, []), ((true, p, []) : GateCode)] =
      [(false, p, [])] ++ [(true, p, [])] := rfl
  rw [hsplit, Circuit.ofCodes_append, Circuit.eval_append, Circuit.eval_ofCodes_ket hcl1]
  have hnot_eq : classicalRun [(false, p, [])] X = Function.update X ⟨p, hp⟩ true := by
    rw [classicalRun_cons, classicalRun_nil]
    refine funext_readBit fun r => ?_
    rw [readBit_classicalStep]
    by_cases hr : r = p
    · subst hr
      simp [hp, readBit_of_lt _ hp, hXp]
    · by_cases hrW : r < W
      · have hne : (⟨r, hrW⟩ : Fin W) ≠ ⟨p, hp⟩ := fun he => hr (congrArg Fin.val he)
        rw [readBit_of_lt _ hrW, readBit_of_lt _ hrW, Function.update_of_ne hne]
        simp [hr]
      · simp [hr, readBit_of_le _ (not_lt.mp hrW)]
  rw [hnot_eq]
  obtain ⟨gh, hgh⟩ : ∃ gh, toPlacedGate? W (true, p, []) = some gh :=
    Option.isSome_iff_exists.mp (isSome_toPlacedGate?_iff.mpr ⟨hp, rfl⟩)
  simp only [Circuit.ofCodes, List.filterMap_cons, List.filterMap_nil, hgh, Circuit.eval_cons,
    Circuit.eval_nil, eval_toPlacedGate_hadamard_ket hgh hp]
  refine sum_congr rfl fun c _ => ?_
  rw [Function.update_self, Bool.true_and, Function.update_idem]

private theorem computableInPolyTime_nqpGates
    (mLen : ℕ → ℕ) (hm_poly : ComputableInPolyTime mLen encUnary encUnary)
    (codeAt : ℕ → List (Cslib.Circuits.Boolean.Op × List ℕ) × List ℕ)
    (hcodeAt : ComputableInPolyTime codeAt encUnary Cslib.Circuits.Boolean.encCode) :
    let Mlen (n : ℕ) := 2 * n + 1 + mLen n
    let zqAt (n : ℕ) := (n + mLen n) + Mlen n + (codeAt n).1.length
    let oracleHalf (n : ℕ) : List GateCode :=
      NPVerifier.frameCodes n (mLen n) (n + mLen n) ++
        (Reversible.codes (Mlen n) (Mlen n + (codeAt n).1.length) (codeAt n).1).map
          (shift (n + mLen n))
    let outWire (n : ℕ) :=
      (n + mLen n) + Reversible.outQubit (Mlen n + (codeAt n).1.length) ((codeAt n).2.getD 0 0)
    let oracle (n : ℕ) : List GateCode :=
      oracleHalf n ++
        [(false, zqAt n + 1, [outWire n]), (false, zqAt n + 1, [n])] ++
        (oracleHalf n).reverse
    let post (n : ℕ) : List GateCode :=
      allZeroCodes n (mLen n) (zqAt n + 2) ++ swapCodes (zqAt n + 2 + mLen n - 1)
    ComputableInPolyTime
      (fun n => [(false, zqAt n + 1, []), (true, zqAt n + 1, [])] ++
        hadamardCodes n (mLen n) ++ oracle n ++ hadamardCodes n (mLen n) ++ post n)
      encUnary (encList encGateCode) := by
  intro Mlen zqAt oracleHalf outWire oracle post
  have hM_poly : ComputableInPolyTime Mlen encUnary encUnary := by dsimp only [Mlen]; fun_prop
  have hz_poly : ComputableInPolyTime zqAt encUnary encUnary := by dsimp only [zqAt]; fun_prop
  have hrc : ComputableInPolyTime
      (fun n => Reversible.codes (Mlen n) (Mlen n + (codeAt n).1.length) (codeAt n).1)
      encUnary (encList encGateCode) :=
    Reversible.computableInPolyTime_codes hM_poly (by fun_prop) (by fun_prop)
  have hshift : ComputableInPolyTime
      (fun n => (Reversible.codes (Mlen n) (Mlen n + (codeAt n).1.length) (codeAt n).1).map
        (shift (n + mLen n))) encUnary (encList encGateCode) := by
    change ComputableInPolyTime
      (fun n => (Reversible.codes (Mlen n) (Mlen n + (codeAt n).1.length) (codeAt n).1).map
        fun g => (g.1, g.2.1 + (n + mLen n), g.2.2.map fun u => u + (n + mLen n)))
      encUnary (encList encGateCode)
    fun_prop
  have hfr : ComputableInPolyTime
      (fun n => NPVerifier.frameCodes n (mLen n) (n + mLen n))
      encUnary (encList encGateCode) := by dsimp only [NPVerifier.frameCodes]; fun_prop
  have hhalf : ComputableInPolyTime oracleHalf encUnary (encList encGateCode) := by
    dsimp only [oracleHalf]; fun_prop
  have hc2 : ComputableInPolyTime (fun n => (codeAt n).2) encUnary (encList encNat) := by
    dsimp only [Cslib.Circuits.Boolean.encCode] at hcodeAt; fun_prop
  have hget : ComputableInPolyTime (fun n => (codeAt n).2.getD 0 0) encUnary encNat :=
    ComputableInPolyTime.listGetDWithInput hc2 (ComputableInPolyTime.const 0) 0
  have houtq : ComputableInPolyTime
      (fun n => Reversible.outQubit (Mlen n + (codeAt n).1.length) ((codeAt n).2.getD 0 0))
      encUnary encUnary := ComputableInPolyTime.binary_min_unary' (by fun_prop) hget
  have hout : ComputableInPolyTime outWire encUnary encUnary := by dsimp only [outWire]; fun_prop
  have hmid : ComputableInPolyTime
      (fun n => [((false, zqAt n + 1, [outWire n]) : GateCode), (false, zqAt n + 1, [n])])
      encUnary (encList encGateCode) := by fun_prop
  have hrev : ComputableInPolyTime (fun n => (oracleHalf n).reverse) encUnary
      (encList encGateCode) := by fun_prop
  have horacle1 : ComputableInPolyTime
      (fun n => oracleHalf n ++
        [((false, zqAt n + 1, [outWire n]) : GateCode), (false, zqAt n + 1, [n])])
      encUnary (encList encGateCode) := by fun_prop
  have horacle : ComputableInPolyTime oracle encUnary (encList encGateCode) := by
    dsimp only [oracle]; fun_prop
  have hhad : ComputableInPolyTime (fun n => hadamardCodes n (mLen n)) encUnary
      (encList encGateCode) := computableInPolyTime_hadamardCodes (by fun_prop) hm_poly
  have hpost : ComputableInPolyTime post encUnary (encList encGateCode) := by
    dsimp only [post, allZeroCodes, swapCodes, swapWireCodes]; fun_prop
  have hinit : ComputableInPolyTime
      (fun n => [((false, zqAt n + 1, []) : GateCode), (true, zqAt n + 1, [])])
      encUnary (encList encGateCode) := by fun_prop
  have hg1 : ComputableInPolyTime
      (fun n => [((false, zqAt n + 1, []) : GateCode), (true, zqAt n + 1, [])] ++
        hadamardCodes n (mLen n)) encUnary (encList encGateCode) := by fun_prop
  have hg2 : ComputableInPolyTime
      (fun n => ([((false, zqAt n + 1, []) : GateCode), (true, zqAt n + 1, [])] ++
        hadamardCodes n (mLen n)) ++ oracle n) encUnary (encList encGateCode) := by fun_prop
  have hg3 : ComputableInPolyTime
      (fun n => (([((false, zqAt n + 1, []) : GateCode), (true, zqAt n + 1, [])] ++
        hadamardCodes n (mLen n)) ++ oracle n) ++ hadamardCodes n (mLen n))
      encUnary (encList encGateCode) := by fun_prop
  fun_prop

/-- **`coC=P ⊆ NQP`**: every `GapP` difference
`g(a) = f₁(a) - f₂(a)` is simulated as an exact interference amplitude `-g(a) / 2^{p₁(n) + p₂(n)}`
by a polynomial-time uniform family of `{H, NOT, CNOT, Toffoli}` quantum circuits, accepting with
exact probability `(g(a) / 2^{p₁(n) + p₂(n)})² > 0 ↔ g(a) ≠ 0`.
-/
theorem coCeqP_subset_NQP : coCeqP enc ⊆ NQP enc := by
  intro A hA
  obtain ⟨g, ⟨f₁, ⟨p₁, V₁, hV₁, hf₁⟩, f₂, ⟨p₂, V₂, hV₂, hf₂⟩, hg⟩, hA⟩ :=
    mem_coCeqP_iff_exists_GapP.mp hA
  -- Combine `V₁` and `V₂` into `V = sumVerifier p₁ p₂ V₁ V₂` on certificates `b :: r` of length
  -- `q(n) = p₁(n) + p₂(n) + 1`, and compile `V` to uniform De Morgan circuits on `encPair enc
  -- encBits`.
  let q : Polynomial ℕ := p₁ + p₂ + 1
  let V : α × List Bool → Bool :=
    sumVerifier (fun a => p₁.eval (enc a).length) (fun a => p₂.eval (enc a).length) V₁ V₂
  have hV : ComputableInPolyTime V (encPair enc encBits) encBool := by dsimp [V]; fun_prop
  obtain ⟨circuits, hcode, hcorrect⟩ := CircuitValue.exists_uniformCircuits hV
  -- Register layout on input `x` of length `n`:
  -- * `0 .. n - 1`: input `x`
  -- * `n .. n + m - 1` (`m = q(n) ≥ 1`): uniform superposition over `z = b :: r ∈ {0,1}^m`
  -- * `o .. o + M - 1` (`o = n + m`, `M = 2 n + 1 + m`): framed input `frame x ++ z`
  -- * `o + M .. zq - 1` (`zq = o + M + G`, `G = (circuits M).code.1.length`): Boolean gate wires
  -- * `zq`: always-zero wire for `Reversible.codes`
  -- * `pk = zq + 1`: phase-kickback qubit in state `|-⟩ = H(NOT |0⟩)`
  -- * `anc .. anc + m - 1` (`anc = zq + 2`): `m` clean ancillas for `allZeroCodes n m anc`
  -- Total width: `W(n) = zq + 2 + m`.
  let mLen (n : ℕ) : ℕ := q.eval n
  let Mlen (n : ℕ) : ℕ := 2 * n + 1 + mLen n
  let codeAt (n : ℕ) := (circuits (Mlen n)).code
  let zqAt (n : ℕ) : ℕ := (n + mLen n) + Mlen n + (codeAt n).1.length
  let widthFn (n : ℕ) : ℕ := zqAt n + 2 + mLen n
  let oracleHalf (n : ℕ) : List GateCode :=
    NPVerifier.frameCodes n (mLen n) (n + mLen n) ++
      (Reversible.codes (Mlen n) (Mlen n + (codeAt n).1.length) (codeAt n).1).map
        (shift (n + mLen n))
  let outWire (n : ℕ) : ℕ :=
    (n + mLen n) +
      Reversible.outQubit (Mlen n + (codeAt n).1.length) ((codeAt n).2.getD 0 0)
  let oracle (n : ℕ) : List GateCode :=
    oracleHalf n ++
      [(false, zqAt n + 1, [outWire n]), (false, zqAt n + 1, [n])] ++
      (oracleHalf n).reverse
  let post (n : ℕ) : List GateCode :=
    allZeroCodes n (mLen n) (zqAt n + 2) ++ swapCodes (zqAt n + 2 + mLen n - 1)
  let gatesFn (n : ℕ) : List GateCode :=
    [(false, zqAt n + 1, []), (true, zqAt n + 1, [])] ++
      hadamardCodes n (mLen n) ++
      oracle n ++
      hadamardCodes n (mLen n) ++
      post n
  have hm_pos : ∀ n, 1 ≤ mLen n := fun n => by
    simp only [mLen, q, Polynomial.eval_add, Polynomial.eval_one]; omega
  have hcodeAt : ComputableInPolyTime codeAt encUnary Cslib.Circuits.Boolean.encCode :=
    hcode.comp (by dsimp [Mlen, mLen]; fun_prop)
  have hz_poly : ComputableInPolyTime zqAt encUnary encUnary := by
    have := hcodeAt; dsimp only [zqAt, Mlen, mLen]; fun_prop
  have hwidth_poly : ComputableInPolyTime widthFn encUnary encUnary := by
    have := hz_poly; dsimp only [widthFn, mLen]; fun_prop
  have hgates_poly : ComputableInPolyTime gatesFn encUnary (encList encGateCode) :=
    computableInPolyTime_nqpGates mLen (by dsimp [mLen]; fun_prop) codeAt hcodeAt
  have hhalf_cl : ∀ n, IsClassical (widthFn n) (oracleHalf n) := fun n => by
    refine IsClassical.append.mpr ⟨?_, ?_⟩
    · exact NPVerifier.isClassical_frameCodes
        (by dsimp [widthFn, zqAt, Mlen]; omega) le_rfl
    · intro gc hgc
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hgc
      have hcl := Reversible.isClassical_codes (W := Mlen n + (codeAt n).1.length + 1)
        (gates := (codeAt n).1) le_rfl (by omega) c hc
      exact ⟨hcl.1, hcl.2.shift (by dsimp [widthFn, zqAt]; omega)⟩
  have horacle_cl : ∀ n, IsClassical (widthFn n) (oracle n) := fun n => by
    have hm := hm_pos n
    refine IsClassical.append.mpr ⟨IsClassical.append.mpr ⟨hhalf_cl n, ?_⟩,
      isClassical_reverse (hhalf_cl n)⟩
    intro gc hgc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hgc
    have hout_lt : outWire n ≤ zqAt n := by
      dsimp [outWire, zqAt, Reversible.outQubit]; omega
    rcases hgc with rfl | rfl
    · exact ⟨rfl, by simp, by simp; omega, by simp [widthFn]; omega⟩
    · exact ⟨rfl, by simp, by simp [zqAt, Mlen]; omega, by simp [widthFn, zqAt, Mlen]; omega⟩
  have hpost_cl : ∀ n, IsClassical (widthFn n) (post n) := fun n => by
    have hm := hm_pos n
    refine IsClassical.append.mpr
      ⟨isClassical_allZeroCodes hm (by dsimp [zqAt, Mlen]; omega) (by dsimp [widthFn]; omega),
        isClassical_swapCodes (by omega) (by dsimp [widthFn]; omega)⟩
  let F : UniformCircuitFamily :=
    { width := widthFn
      gates := gatesFn
      computableInPolyTime_width := hwidth_poly
      computableInPolyTime_gates := hgates_poly
      le_width := fun n => by dsimp [widthFn, zqAt, Mlen]; omega
      width_pos := fun n => by dsimp [widthFn]; omega
      wellFormed := fun n gc hgc => by
        dsimp only [gatesFn] at hgc
        simp only [List.mem_append] at hgc
        rcases hgc with (((h1 | h2) | h3) | h4) | h5
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at h1
          rcases h1 with rfl | rfl
          · exact ⟨by simp, by simp, by simp [widthFn]; omega⟩
          · exact ⟨by dsimp [widthFn]; omega, rfl⟩
        · exact wellFormed_hadamardCodes (by dsimp [widthFn, zqAt, Mlen]; omega) gc h2
        · exact (horacle_cl n gc h3).2
        · exact wellFormed_hadamardCodes (by dsimp [widthFn, zqAt, Mlen]; omega) gc h4
        · exact (hpost_cl n gc h5).2 }
  refine ⟨F, fun a => ?_⟩
  rw [hA a, hg a]
  -- Evaluate `F.acceptProb (enc a) = ((f₁ a : ℝ) - (f₂ a : ℝ)) ^ 2 / 2 ^ (2 * (p₁(n) + p₂(n)))`.
  set x := enc a
  set n := x.length
  set m := mLen n
  set M := Mlen n
  set W := widthFn n
  set zq := zqAt n
  set pk : Fin W := ⟨zq + 1, by dsimp [W, widthFn]; omega⟩
  have hm1 : 1 ≤ m := hm_pos n
  have hnm : n + m ≤ W := by dsimp [W, widthFn, zqAt, Mlen]; omega
  set s : ℂ := (((Real.sqrt 2)⁻¹ : ℝ) : ℂ)
  -- Action of `oracle n` on `X_z_c = (glue (blockEmb n hnm) z (inputState W x))[pk := c]`:
  -- leaves all qubits except `pk` unchanged, and flips `pk` to `c ^^ V(a, ofFn z) ^^ z 0`!
  let base (z : Fin m → Bool) (c : Bool) : Fin W → Bool :=
    Function.update (glue (blockEmb n hnm) z (inputState W x)) pk c
  have horacle_run : ∀ (z : Fin m → Bool) (c : Bool),
      classicalRun (oracle n) (base z c) =
        base z (c ^^ V (a, List.ofFn z) ^^ z ⟨0, by omega⟩) := by
    intro z c
    -- First show `oracleHalf n` never touches or reads `pk` (all wires `≤ zq < pk`).
    have hhalf_lt : ∀ gc ∈ oracleHalf n, target gc ≤ zq ∧ ∀ u ∈ controls gc, u ≤ zq := by
      intro gc hgc
      rcases List.mem_append.mp hgc with hfr | hrc
      · rcases NPVerifier.mem_frameCodes.mp hfr with ⟨i, hi, rfl | rfl⟩ | ⟨j, hj, rfl⟩ <;>
          (simp; dsimp [zq, zqAt, Mlen, m, mLen] at *; omega)
      · obtain ⟨gc0, hgc0, rfl⟩ := List.mem_map.mp hrc
        have hcl := Reversible.isClassical_codes (W := M + (codeAt n).1.length + 1)
          (gates := (codeAt n).1) le_rfl (by omega) gc0 hgc0
        obtain ⟨b, t, cs⟩ := gc0
        have hb : b = false := hcl.1; subst hb
        have hlt := hcl.2.2.2
        refine ⟨by
          have := hlt t List.mem_cons_self
          simp [shift]; dsimp [zq, zqAt, M, m]; omega,
          fun u hu => ?_⟩
        simp only [controls_mk, shift, List.mem_map] at hu
        obtain ⟨u0, hu0, rfl⟩ := hu
        have := hlt u0 (List.mem_cons_of_mem _ hu0)
        dsimp [zq, zqAt, M, m]; omega
    -- Commute updating `pk` past any list of classical gates whose targets and controls are `≤ zq`.
    have run_update_pk : ∀ (gs : List GateCode),
        (∀ gc ∈ gs, target gc ≤ zq ∧ ∀ u ∈ controls gc, u ≤ zq) →
        ∀ (Y : Fin W → Bool) (b : Bool),
        classicalRun gs (Function.update Y pk b) =
          Function.update (classicalRun gs Y) pk b := by
      intro gs hgs Y b
      induction gs generalizing Y with
      | nil => rfl
      | cons gc gs ih =>
        obtain ⟨ht_le, hcs_le⟩ := hgs gc List.mem_cons_self
        rw [classicalRun_cons, classicalRun_cons, ← ih (fun g' hg' =>
          hgs g' (List.mem_cons_of_mem _ hg'))]
        congr 1
        refine funext_readBit fun r => ?_
        have hall_eq : (controls gc).all (readBit (Function.update Y pk b)) =
            (controls gc).all (readBit Y) := by
          apply Bool.eq_iff_iff.mpr
          simp only [List.all_eq_true]
          refine forall_congr' fun u => imp_congr_right fun hu => ?_
          have hu_le := hcs_le u hu
          have hu_lt : u < W := by dsimp [W, widthFn]; omega
          have hne_pk : (⟨u, hu_lt⟩ : Fin W) ≠ pk := fun he => by
            have hval := congrArg Fin.val he; simp [pk] at hval; omega
          rw [readBit_of_lt _ hu_lt, readBit_of_lt _ hu_lt, Function.update_of_ne hne_pk]
        rw [readBit_classicalStep, hall_eq]
        by_cases hr : r = zq + 1
        · subst hr
          have hlt : zq + 1 < W := pk.2
          have hne : zq + 1 ≠ target gc := by omega
          simp [hne, readBit_of_lt _ hlt, pk]
        · by_cases hrW : r < W
          · have hne_pk : (⟨r, hrW⟩ : Fin W) ≠ pk := fun he => hr (congrArg Fin.val he)
            rw [readBit_of_lt _ hrW, Function.update_of_ne hne_pk,
              readBit_of_lt _ hrW, Function.update_of_ne hne_pk,
              ← readBit_of_lt Y hrW, ← readBit_of_lt (classicalStep gc Y) hrW,
              readBit_classicalStep]
          · rw [readBit_of_le _ (not_lt.mp hrW), readBit_of_le _ (not_lt.mp hrW)]
            simp [show r ≠ target gc by intro he; subst he; apply hrW; dsimp [W, widthFn]; omega]
    set X₀ := glue (blockEmb n hnm) z (inputState W x)
    have hX₀_eq : X₀ = inputState W (x ++ List.ofFn z) := by
      funext i
      dsimp only [X₀]
      rw [glue_blockEmb_apply]
      split_ifs with hi
      · simp only [inputState, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (show x.length ≤ (i : ℕ) by dsimp [n] at hi; omega),
          List.getElem?_ofFn]
        simp only [show (i : ℕ) - x.length < m by dsimp [n] at hi; omega, ↓reduceDIte,
          Option.getD_some]
        rfl
      · simp only [inputState, List.getD_eq_getElem?_getD]
        by_cases hlt : (i : ℕ) < n
        · rw [List.getElem?_append_left hlt]
        · have hlen_le : (x ++ List.ofFn z).length ≤ (i : ℕ) := by
            rw [List.length_append, List.length_ofFn]; dsimp [n] at hi hlt; omega
          rw [List.getElem?_eq_none (show x.length ≤ (i : ℕ) by dsimp [n] at hlt; omega),
            List.getElem?_eq_none hlen_le]
    -- Value of `outWire n` and qubit `n` after running `oracleHalf n` on `X₀`.
    set Y₀ := classicalRun (oracleHalf n) X₀
    have hY₀_n : readBit Y₀ n = z ⟨0, by omega⟩ := by
      have hnt : ∀ gc ∈ oracleHalf n, target gc ≠ n := by
        intro gc hgc
        rcases List.mem_append.mp hgc with hfr | hrc
        · rcases NPVerifier.mem_frameCodes.mp hfr with ⟨i, hi, rfl | rfl⟩ | ⟨j, hj, rfl⟩ <;>
            simp <;> omega
        · obtain ⟨gc0, _, rfl⟩ := List.mem_map.mp hrc
          simp [shift]; omega
      rw [readBit_classicalRun_of_forall_ne hnt, readBit_of_lt _ (by omega)]
      dsimp only [X₀]
      rw [show (⟨n, by omega⟩ : Fin W) = blockEmb n hnm ⟨0, by omega⟩ from Fin.ext (by simp),
        glue_apply_emb]
    have hY₀_out : readBit Y₀ (outWire n) = V (a, List.ofFn z) := by
      dsimp only [Y₀, oracleHalf, outWire]
      rw [hX₀_eq]
      have hM' : (n + m) + (2 * n + 1 + m + (codeAt n).1.length + 1) ≤ W := by
        dsimp only [W, widthFn, zqAt, Mlen, m]; omega
      rw [readBit_frame_and_codes (codeAt n) hM' rfl z]
      have hpair : encPair enc encBits (a, List.ofFn z) = frame x ++ List.ofFn z := rfl
      have hc := hcorrect (a, List.ofFn z)
      rw [Cslib.Circuits.Circuit.eval_eq_evalOutput,
        show (List.ofFn fun i : Fin (encPair enc encBits (a, List.ofFn z)).length =>
          (encPair enc encBits (a, List.ofFn z))[i]) = encPair enc encBits (a, List.ofFn z)
          from List.ofFn_getElem] at hc
      have hM_eq : (encPair enc encBits (a, List.ofFn z)).length = Mlen n := by
        rw [hpair, List.length_append, length_frame, List.length_ofFn]
      dsimp only [codeAt]
      rw [← hM_eq, ← hpair]
      exact hc
    -- Combine forward `oracleHalf`, two CNOTs onto `pk`, and reverse `oracleHalf`!
    dsimp only [oracle, base]
    rw [classicalRun_append, classicalRun_append, run_update_pk _ hhalf_lt X₀ c]
    have hpk_lt : zq + 1 < W := pk.2
    have hkick : classicalRun [(false, zq + 1, [outWire n]), (false, zq + 1, [n])]
        (Function.update Y₀ pk c) =
        Function.update Y₀ pk (c ^^ V (a, List.ofFn z) ^^ z ⟨0, by omega⟩) := by
      simp only [classicalRun_cons, classicalRun_nil]
      refine funext_readBit fun r => ?_
      have hout_ne : outWire n ≠ zq + 1 := by
        dsimp [outWire, zq, zqAt, Reversible.outQubit]; omega
      have hout_lt : outWire n < W := by
        dsimp [outWire, W, widthFn, zqAt, Reversible.outQubit]; omega
      have hn_ne : n ≠ zq + 1 := by dsimp [zq, zqAt, Mlen]; omega
      have hn_lt : n < W := by omega
      rw [readBit_classicalStep, readBit_classicalStep]
      simp only [target_mk, controls_mk, hpk_lt, and_true, List.all_cons, List.all_nil,
        Bool.and_true]
      have hne_n : (⟨n, hn_lt⟩ : Fin W) ≠ pk := fun he =>
        hn_ne (by simpa [pk] using congrArg Fin.val he)
      have hne_o : (⟨outWire n, hout_lt⟩ : Fin W) ≠ pk := fun he =>
        hout_ne (by simpa [pk] using congrArg Fin.val he)
      have h1 : readBit (classicalStep (false, zq + 1, [outWire n]) (Function.update Y₀ pk c)) n =
          readBit Y₀ n := by
        rw [readBit_classicalStep]
        simp [hn_ne, readBit_of_lt _ hn_lt, Function.update_of_ne hne_n]
      have h2 : readBit (Function.update Y₀ pk c) (outWire n) = readBit Y₀ (outWire n) := by
        rw [readBit_of_lt _ hout_lt, readBit_of_lt _ hout_lt, Function.update_of_ne hne_o]
      rw [h1, h2, hY₀_out, hY₀_n]
      by_cases hr : r = zq + 1
      · subst hr
        simp only [decide_true, Bool.true_and, readBit_of_lt _ hpk_lt]
        have heq_pk : (⟨zq + 1, hpk_lt⟩ : Fin W) = pk := rfl
        rw [heq_pk, Function.update_self, Function.update_self]
      · by_cases hrW : r < W
        · have hne_r : (⟨r, hrW⟩ : Fin W) ≠ pk := fun he =>
            hr (by simpa [pk] using congrArg Fin.val he)
          simp [hr, readBit_of_lt _ hrW, Function.update_of_ne hne_r]
        · simp [hr, readBit_of_le _ (not_lt.mp hrW)]
    rw [hkick, run_update_pk _ (fun gc hgc => hhalf_lt gc (List.mem_reverse.mp hgc)),
      ← classicalUnrun_eq_classicalRun_reverse, classicalUnrun_classicalRun (hhalf_cl n)]
  -- Compute state right before `post n`:
  -- `s * (1 / 2^m) * ∑_{c, z, r} (-1)^c * (-1)^{V(a,z) ^^ z 0} * (-1)^{z · r} |base r c⟩`.
  have hprep_state :
      Circuit.eval (Circuit.ofCodes W
        ([(false, zq + 1, []), (true, zq + 1, [])] ++ hadamardCodes n m ++ oracle n ++
          hadamardCodes n m)) (ket (inputState W x)) =
      ∑ r : Fin m → Bool, ∑ c : Bool,
        ((if c then (-1 : ℂ) else 1) * s * (s ^ m * s ^ m) *
          ∑ z : Fin m → Bool,
            (if V (a, List.ofFn z) ^^ z ⟨0, by omega⟩ then (-1 : ℂ) else 1) *
              (∏ i : Fin m, if z i && r i then (-1 : ℂ) else 1)) •
          ket (base r c) := by
    simp only [Circuit.ofCodes_append, Circuit.eval_append]
    -- Step 1: `[(false, pk, []), (true, pk, [])]` prepares `|-⟩` on `pk`.
    have hinit : Circuit.eval (Circuit.ofCodes W [(false, zq + 1, []), (true, zq + 1, [])])
        (ket (inputState W x)) =
        ∑ c : Bool, ((if c then (-1 : ℂ) else 1) * s) •
          ket (Function.update (inputState W x) pk c) :=
      eval_prep_minus pk.2 (inputState W x) (by
        have hxlt : x.length ≤ zq + 1 := by dsimp only [zq, zqAt, Mlen, n]; omega
        rw [← readBit_fin (inputState W x)]
        exact readBit_inputState_of_le hxlt)
    -- Helper: `glue (blockEmb n hnm) r (base z c) = base r c`.
    have hglue_base : ∀ (z r : Fin m → Bool) (c : Bool),
        glue (blockEmb n hnm) r (base z c) = base r c := by
      intro z r c; funext i
      dsimp only [base]
      by_cases hi : i = pk
      · subst hi
        rw [Function.update_self, glue_blockEmb_apply,
          dite_eq_right (by simp [pk]; dsimp [zq, zqAt, Mlen]; omega), Function.update_self]
      · rw [Function.update_of_ne hi, glue_blockEmb_apply, glue_blockEmb_apply]
        split_ifs with hb
        · rfl
        · rw [Function.update_of_ne hi, glue_blockEmb_apply, dite_eq_right hb]
    have hglue_init : ∀ (r : Fin m → Bool) (c : Bool),
        glue (blockEmb n hnm) r (Function.update (inputState W x) pk c) = base r c := by
      intro r c; funext i
      dsimp only [base]
      by_cases hi : i = pk
      · subst hi
        rw [Function.update_self, glue_blockEmb_apply,
          dite_eq_right (by simp [pk]; dsimp [zq, zqAt, Mlen]; omega), Function.update_self]
      · rw [Function.update_of_ne hi, glue_blockEmb_apply, glue_blockEmb_apply]
        split_ifs with hb
        · rfl
        · rw [Function.update_of_ne hi]
    have hbase_emb : ∀ (z : Fin m → Bool) (c : Bool) (i : Fin m),
        base z c (blockEmb n hnm i) = z i := fun z c i => by
      dsimp only [base]
      rw [Function.update_of_ne (fun he => by
        have := congrArg Fin.val he; simp [pk] at this; dsimp [zq, zqAt, Mlen] at this; omega),
        glue_apply_emb]
    have hhad_init : ∀ c : Bool,
        Circuit.eval (Circuit.ofCodes W (hadamardCodes n m))
          (ket (Function.update (inputState W x) pk c)) =
        ∑ z : Fin m → Bool, s ^ m • ket (base z c) := fun c => by
      rw [eval_hadamardCodes_ket hnm _ fun i => by
        have hne : blockEmb n hnm i ≠ pk := fun he => by
          have hv := congrArg Fin.val he
          rw [blockEmb_apply_val] at hv
          change _ = zq + 1 at hv
          dsimp only [zq, zqAt, Mlen] at hv
          omega
        have hxlt : x.length ≤ (i : ℕ) + n := by dsimp only [n]; omega
        rw [Function.update_of_ne hne, ← readBit_fin (inputState W x), blockEmb_apply_val]
        exact readBit_inputState_of_le hxlt]
      refine sum_congr rfl fun z _ => by rw [hglue_init]
    rw [hinit, map_sum, map_sum, map_sum]
    have heval_or : ∀ X : Fin W → Bool,
        Circuit.eval (Circuit.ofCodes W (oracle n)) (ket X) = ket (classicalRun (oracle n) X) :=
      fun X => Circuit.eval_ofCodes_ket (horacle_cl n) X
    simp_rw [map_smul, hhad_init, map_sum, map_smul, heval_or, horacle_run]
    -- Re-index `c' = c ^^ phase(z)` so the sign moves from `ket` to the coefficient!
    have hreidx : ∀ (z : Fin m → Bool),
        (∑ c : Bool, ((if c then (-1 : ℂ) else 1) * s) •
          s ^ m • Circuit.eval (Circuit.ofCodes W (hadamardCodes n m))
            (ket (base z (c ^^ V (a, List.ofFn z) ^^ z ⟨0, by omega⟩)))) =
        ∑ c : Bool, ((if c then (-1 : ℂ) else 1) * s *
          (if V (a, List.ofFn z) ^^ z ⟨0, by omega⟩ then (-1 : ℂ) else 1) * s ^ m) •
          Circuit.eval (Circuit.ofCodes W (hadamardCodes n m)) (ket (base z c)) := by
      intro z
      simp_rw [Bool.xor_assoc]
      rcases V (a, List.ofFn z) ^^ z ⟨0, by omega⟩ with _ | _
      · rw [Fintype.sum_bool, Fintype.sum_bool]; simp [smul_smul]
      · rw [Fintype.sum_bool, Fintype.sum_bool]
        simp only [↓reduceIte, neg_mul, one_mul, bne_self_eq_false, neg_smul, Bool.false_eq_true,
          Bool.bne_true, Bool.not_false, mul_neg, mul_one, neg_neg, smul_smul]
        abel
    have hswap1 :
        (∑ c : Bool, ((if c then (-1 : ℂ) else 1) * s) •
          ∑ z : Fin m → Bool, s ^ m •
            Circuit.eval (Circuit.ofCodes W (hadamardCodes n m))
              (ket (base z (c ^^ V (a, List.ofFn z) ^^ z ⟨0, by omega⟩)))) =
        ∑ z : Fin m → Bool, ∑ c : Bool, ((if c then (-1 : ℂ) else 1) * s) •
          s ^ m • Circuit.eval (Circuit.ofCodes W (hadamardCodes n m))
            (ket (base z (c ^^ V (a, List.ofFn z) ^^ z ⟨0, by omega⟩))) := by
      simp_rw [smul_sum]; exact sum_comm
    rw [hswap1]
    simp_rw [hreidx, eval_hadamardCodes_ket_any hnm, hbase_emb, hglue_base, smul_sum, smul_smul]
    rw [sum_comm (s := (univ : Finset (Fin m → Bool)))]
    simp_rw [sum_comm (s := (univ : Finset Bool))]
    rw [sum_comm]
    refine sum_congr rfl fun r _ => ?_
    rw [sum_comm]
    refine sum_congr rfl fun c _ => ?_
    rw [← sum_smul, mul_sum]
    congr 1
    refine sum_congr rfl fun z _ => ?_
    change _ = _ * (s ^ m * s ^ m) * _
    ring
  -- Distinct pairs `(r, c)` give distinct basis strings `base r c`.
  have hbase_inj : Function.Injective (fun rc : (Fin m → Bool) × Bool => base rc.1 rc.2) := by
    rintro ⟨r₁, c₁⟩ ⟨r₂, c₂⟩ heq
    have hc : c₁ = c₂ := by
      have := congrFun heq pk; simpa [base] using this
    subst hc
    refine Prod.ext (funext fun i => ?_) rfl
    have hbi := congrFun heq (blockEmb n hnm i)
    change base r₁ c₁ (blockEmb n hnm i) = base r₂ c₁ (blockEmb n hnm i) at hbi
    have hb_emb : ∀ r : Fin m → Bool, base r c₁ (blockEmb n hnm i) = r i := fun r => by
      dsimp only [base]
      rw [Function.update_of_ne (fun he => by
        have hv := congrArg Fin.val he; simp [pk] at hv; dsimp [zq, zqAt, Mlen] at hv; omega),
        glue_apply_emb]
    rwa [hb_emb, hb_emb] at hbi
  -- On `base r c`, `post n` accepts iff `r = fun _ => false`!
  have hpost_acc : ∀ (r : Fin m → Bool) (c : Bool),
      classicalRun (post n) (base r c) ∈ accepting W ↔ r = fun _ => false := by
    intro r c
    rw [mem_accepting (by dsimp [W, widthFn]; omega),
      ← readBit_fin (classicalRun (post n) (base r c))]
    change readBit (classicalRun (allZeroCodes n m (zq + 2) ++ swapCodes (zq + 2 + m - 1))
      (base r c)) 0 = true ↔ _
    rw [classicalRun_append,
      readBit_classicalRun_swapCodes (by omega) (by dsimp [W, widthFn]; omega),
      readBit_classicalRun_allZeroCodes hm1 (by dsimp [zq, zqAt, Mlen]; omega)
        (by dsimp [W, widthFn]; omega) (fun j hj => by
          rw [readBit_of_lt _ (by dsimp [W, widthFn]; omega)]
          dsimp only [base]
          rw [Function.update_of_ne (fun he => by
              have := congrArg Fin.val he; simp [pk] at this; omega),
            glue_blockEmb_apply, dite_eq_right (by simp; dsimp [zq, zqAt, Mlen]; omega)]
          simp only [inputState, List.getD_eq_getElem?_getD]
          rw [List.getElem?_eq_none (show x.length ≤ zq + 2 + j by
            dsimp [n, zq, zqAt, Mlen] at *; omega)]
          rfl),
      decide_eq_true_eq, funext_iff]
    refine forall_congr' fun j => ?_
    have hbit : base r c ⟨n + j, by omega⟩ = r j := by
      rw [show (⟨n + j, by omega⟩ : Fin W) = blockEmb n hnm j from Fin.ext (by simp; omega)]
      dsimp only [base]
      rw [Function.update_of_ne (fun he => by
          have := congrArg Fin.val he; simp [pk] at this; dsimp [zq, zqAt, Mlen] at this; omega),
        glue_apply_emb]
    rw [hbit]
  -- Evaluate the Walsh–Hadamard sum at `r = 0`: `∑_z (-1)^{V(a, z) ^^ z 0} = 2 (f₂ a - f₁ a)`.
  have hwalsh : (∑ z : Fin m → Bool,
      (if V (a, List.ofFn z) ^^ z ⟨0, by omega⟩ then (-1 : ℂ) else 1)) =
      (2 : ℂ) * ((f₂ a : ℂ) - (f₁ a : ℂ)) := by
    set K := p₁.eval n + p₂.eval n
    have hm_eq : m = K + 1 := by
      simp only [m, mLen, q, K, Polynomial.eval_add, Polynomial.eval_one]
    let eK : (Bool × (Fin K → Bool)) ≃ (Fin m → Bool) :=
      (Fin.consEquiv fun _ => Bool).trans (Equiv.arrowCongr (finCongr hm_eq.symm) (Equiv.refl Bool))
    rw [← eK.sum_comp, Fintype.sum_prod_type, Fintype.sum_bool]
    have heK_0 : ∀ (b : Bool) (w : Fin K → Bool), (eK (b, w)) ⟨0, by omega⟩ = b := fun _ _ => rfl
    have heK_list : ∀ (b : Bool) (w : Fin K → Bool),
        List.ofFn (eK (b, w)) = b :: List.ofFn w := by
      intro b w
      apply List.ext_getElem (by simp [hm_eq])
      intro i hi1 hi2
      cases i with
      | zero => simp [eK]
      | succ j =>
        have hjl : j < K := by simp at hi2; omega
        simp only [List.getElem_ofFn, List.getElem_cons_succ, eK, Equiv.trans_apply,
          Equiv.arrowCongr_apply, Equiv.refl_apply, Function.comp_apply, finCongr_symm,
          finCongr_apply, Fin.consEquiv_apply]
        exact Fin.cons_succ _ _ ⟨j, hjl⟩
    simp_rw [heK_0, heK_list]
    -- Count `{w : Fin K → Bool | V(a, b :: ofFn w) = true}` for `b = false` and `b = true`.
    have hpm : ∀ P : (Fin K → Bool) → Bool,
        (∑ w : Fin K → Bool, (if P w then (-1 : ℂ) else 1)) =
          (2 : ℂ) ^ K - (2 : ℂ) * ((univ.filter fun w => P w = true).card : ℂ) := by
      intro P
      have hsplit : ∀ w : Fin K → Bool,
          (if P w then (-1 : ℂ) else 1) = (1 : ℂ) - (if P w = true then (2 : ℂ) else 0) :=
        fun w => by cases P w <;> norm_num
      simp_rw [hsplit, sum_sub_distrib, sum_const, card_univ, Fintype.card_fun, Fintype.card_fin,
        Fintype.card_bool, ← sum_filter]
      simp [mul_comm]
    have hnot_xor : ∀ b : Bool, (b ^^ true) = !b := fun b => by cases b <;> rfl
    have hfl_xor : ∀ b : Bool, (b ^^ false) = b := fun b => by cases b <;> rfl
    simp_rw [hfl_xor, hnot_xor]
    rw [hpm (fun w => V (a, false :: List.ofFn w)), hpm (fun w => !V (a, true :: List.ofFn w))]
    have hcard_not : (univ.filter fun w : Fin K →
      Bool => (!V (a, true :: List.ofFn w)) = true).card =
        2 ^ K - (univ.filter fun w : Fin K → Bool => V (a, true :: List.ofFn w) = true).card := by
      have htot := card_filter_add_card_filter_not
        (s := (univ : Finset (Fin K → Bool))) (p := fun w => V (a, true :: List.ofFn w) = true)
      simp only [card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool,
        Bool.not_eq_true, ← Bool.not_eq_true'] at htot
      omega
    have hle_card : (univ.filter fun w : Fin K → Bool => V (a, true :: List.ofFn w) = true).card ≤
        2 ^ K := by
      simpa using card_filter_le (univ : Finset (Fin K → Bool))
        (fun w => V (a, true :: List.ofFn w) = true)
    -- Relate the two `Fin K → Bool` filter cardinalities to `f₁ a` and `f₂ a` via `sumVerifier`.
    have hcard_false :
        (univ.filter fun w : Fin K → Bool => V (a, false :: List.ofFn w) = true).card = f₁ a := by
      have hac := acceptCount_andVerifier (fun a => p₁.eval (enc a).length) V₁
        allFalseVerifier a (p₂.eval n)
      rw [acceptCount_allFalseVerifier, mul_one, ← hf₁ a] at hac
      rw [← hac, acceptCount]
      rfl
    have hcard_true :
        (univ.filter fun w : Fin K → Bool => V (a, true :: List.ofFn w) = true).card = f₂ a := by
      have hac := acceptCount_andVerifier (fun a => p₂.eval (enc a).length) V₂
        allFalseVerifier a (p₁.eval n)
      rw [acceptCount_allFalseVerifier, mul_one, ← hf₂ a] at hac
      rw [← hac, acceptCount]
      have hcomm : p₂.eval n + p₁.eval n = K := add_comm _ _
      have hlist : ∀ (k₁ k₂ : ℕ) (hk : k₁ = k₂) (u : Fin k₂ → Bool),
          List.ofFn (u ∘ finCongr hk) = List.ofFn u := by
        rintro k₁ _ rfl u; rfl
      refine card_nbij' (fun w => w ∘ finCongr hcomm) (fun u => u ∘ finCongr hcomm.symm)
        (fun w hw => by
          simp only [mem_coe, mem_filter, mem_univ, true_and] at hw ⊢
          rwa [hlist _ _ hcomm w])
        (fun u hu => by
          simp only [mem_coe, mem_filter, mem_univ, true_and] at hu ⊢
          rwa [hlist _ _ hcomm.symm u])
        (fun w _ => funext fun i => by simp)
        (fun u _ => funext fun i => by simp)
    rw [hcard_not, Nat.cast_sub hle_card, Nat.cast_pow, Nat.cast_ofNat, hcard_false, hcard_true]
    ring
  -- Compute `F.acceptProb x` from `hprep_state`, `hpost_acc`, and `hwalsh`!
  have hprob : F.acceptProb x =
      ((f₁ a : ℝ) - (f₂ a : ℝ)) ^ 2 / (2 : ℝ) ^ (2 * (p₁.eval n + p₂.eval n)) := by
    change measureProb (Circuit.eval (Circuit.ofCodes W (gatesFn n)) (ket (inputState W x)))
      (accepting W) = _
    dsimp only [gatesFn]
    rw [Circuit.ofCodes_append, Circuit.eval_append,
      Circuit.measureProb_eval_ofCodes (hpost_cl n), hprep_state]
    set ψ := ∑ r : Fin m → Bool, ∑ c : Bool,
      ((if c then (-1 : ℂ) else 1) * s * (s ^ m * s ^ m) *
        ∑ z : Fin m → Bool,
          (if V (a, List.ofFn z) ^^ z ⟨0, by omega⟩ then (-1 : ℂ) else 1) *
            (∏ i : Fin m, if z i && r i then (-1 : ℂ) else 1)) • ket (base r c)
    have hcoeff : ∀ c : Bool, ψ.ofLp (base (fun _ => false) c) =
        (if c then (-1 : ℂ) else 1) * s * (s ^ m * s ^ m) *
          ((2 : ℂ) * ((f₂ a : ℂ) - (f₁ a : ℂ))) := by
      intro c
      simp only [ψ, WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply,
        ket_apply, smul_eq_mul]
      rw [sum_eq_single (fun _ => false) (fun r _ hr => sum_eq_zero fun c' _ => by
          have hne : base (fun _ => false) c ≠ base r c' :=
            fun he => hr (congrArg Prod.fst (@hbase_inj (fun _ => false, c) (r, c') he)).symm
          simp [hne]) (fun h => absurd (mem_univ _) h),
        sum_eq_single c (fun c' _ hc' => by
          have hne : base (fun _ => false) c ≠ base (fun _ => false) c' :=
            fun he => hc' (congrArg Prod.snd
              (@hbase_inj (fun _ => false, c) (fun _ => false, c') he)).symm
          simp [hne]) (fun h => absurd (mem_univ _) h)]
      simp only [↓reduceIte, Bool.and_false, Bool.false_eq_true, prod_const_one, mul_one]
      rw [hwalsh]
    have hzero_other : ∀ y : Fin W → Bool,
        classicalRun (post n) y ∈ accepting W →
        (∀ c : Bool, y ≠ base (fun _ => false) c) → ψ.ofLp y = 0 := by
      intro y hy hne
      simp only [ψ, WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply,
        ket_apply, smul_eq_mul]
      refine sum_eq_zero fun r _ => sum_eq_zero fun c _ => ?_
      by_cases he : y = base r c
      · subst he
        have hr0 : r = fun _ => false := (hpost_acc r c).mp hy
        subst hr0
        exact absurd rfl (hne c)
      · simp [he]
    have hsum_acc :
        (∑ y : Fin W → Bool, if classicalRun (post n) y ∈ accepting W then ‖ψ.ofLp y‖ ^ 2
          else 0) = ∑ c : Bool, ‖ψ.ofLp (base (fun _ => false) c)‖ ^ 2 := by
      have hinj_c : Function.Injective (fun c : Bool => base (fun _ => false) c) :=
        fun c₁ c₂ he => congrArg Prod.snd (@hbase_inj (fun _ => false, c₁) (fun _ => false, c₂) he)
      let S : Finset (Fin W → Bool) := univ.image (fun c : Bool => base (fun _ => false) c)
      rw [← sum_subset (subset_univ S) fun y _ hy => by
        simp only [S, mem_image, mem_univ, true_and, not_exists] at hy
        split_ifs with hacc
        · simp [hzero_other y hacc (fun c he => hy c he.symm)]
        · rfl]
      rw [sum_image fun c₁ _ c₂ _ he => hinj_c he]
      refine sum_congr rfl fun c _ => ?_
      rw [ite_eq_left ((hpost_acc (fun _ => false) c).mpr rfl)]
    rw [hsum_acc]
    simp_rw [hcoeff]
    have hs2 : ‖s‖ ^ 2 = 1 / 2 := by
      simp [s, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    have hsm2 : ‖s ^ m * s ^ m‖ ^ 2 = (1 / (2 : ℝ) ^ m) ^ 2 := by
      rw [norm_mul, mul_pow, norm_pow, ← pow_mul, mul_comm m 2, pow_mul, hs2, one_div, inv_pow]
      ring
    have hdiff_norm : ‖(2 : ℂ) * ((f₂ a : ℂ) - (f₁ a : ℂ))‖ ^ 2 =
        4 * ((f₁ a : ℝ) - (f₂ a : ℝ)) ^ 2 := by
      have hcast : (2 : ℂ) * ((f₂ a : ℂ) - (f₁ a : ℂ)) =
          ((2 * ((f₂ a : ℝ) - (f₁ a : ℝ)) : ℝ) : ℂ) := by push_cast; ring
      rw [hcast, Complex.norm_real, Real.norm_eq_abs, sq_abs]; ring
    have hterm_norm : ∀ c : Bool,
        ‖(if c then (-1 : ℂ) else 1) * s * (s ^ m * s ^ m) *
            ((2 : ℂ) * ((f₂ a : ℂ) - (f₁ a : ℂ)))‖ ^ 2 =
          (1 / 2 : ℝ) * (1 / (2 : ℝ) ^ m) ^ 2 * (4 * ((f₁ a : ℝ) - (f₂ a : ℝ)) ^ 2) := by
      intro c
      have hc1 : ‖(if c then (-1 : ℂ) else 1)‖ ^ 2 = 1 := by cases c <;> simp
      rw [norm_mul, mul_pow, norm_mul, mul_pow, norm_mul, mul_pow, hc1, one_mul, hs2, hsm2,
        hdiff_norm]
    simp_rw [hterm_norm]
    rw [Fintype.sum_bool]
    have hm_eq : m = (p₁.eval n + p₂.eval n) + 1 := by
      simp [m, mLen, q, Polynomial.eval_add, Polynomial.eval_one]
    rw [hm_eq, pow_succ, two_mul, pow_add]
    field_simp; ring
  rw [hprob]
  have hden : (0 : ℝ) < (2 : ℝ) ^ (2 * (p₁.eval n + p₂.eval n)) := by positivity
  refine ⟨fun hne => div_pos (sq_pos_of_ne_zero ?_) hden,
    fun hgt h0 => by
      have : (f₁ a : ℝ) - (f₂ a : ℝ) = 0 := by exact_mod_cast h0
      simp [this] at hgt⟩
  exact_mod_cast hne

/-- **Fenner–Green–Homer–Pruim Theorem**:
`NQP = coC=P` over polynomial-time uniform Hadamard–Toffoli quantum circuits.
-/
theorem NQP_eq_coCeqP : NQP enc = coCeqP enc :=
  Set.Subset.antisymm NQP_subset_coCeqP coCeqP_subset_NQP

/-- `PromiseNQP = promiseClass coC=P`. -/
theorem PromiseNQP_eq_promiseClass_coCeqP : PromiseNQP enc = promiseClass (coCeqP enc) := by
  rw [PromiseNQP, NQP_eq_coCeqP]

/-- `NP ⊆ NQP`. -/
theorem NP_subset_NQP : NP enc ⊆ NQP enc := by
  rw [NQP_eq_coCeqP]; exact NP_subset_coCeqP

/-- `NQP ⊆ PP`. -/
theorem NQP_subset_PP : NQP enc ⊆ PP enc := by
  rw [NQP_eq_coCeqP]; exact coCeqP_subset_PP

/-- `PromiseNQP ⊆ promiseClass PP`. -/
theorem PromiseNQP_subset_promiseClass_PP : PromiseNQP enc ⊆ promiseClass (PP enc) :=
  promiseClass_mono NQP_subset_PP

/-- `NQP` is closed under polynomial-time many-one reductions. -/
theorem mem_NQP_of_polyTimeReducible {β : Type} {encB : β ↪ List Bool} {A : Set α} {B : Set β}
    (h : Cslib.Complexity.PolyTimeReducible enc encB A B) (hB : B ∈ NQP encB) :
    A ∈ NQP enc := by
  rw [NQP_eq_coCeqP] at hB ⊢
  exact h.mem_coCeqP hB

/-- `PromiseNQP` is closed under polynomial-time promise reductions. -/
theorem mem_PromiseNQP_of_polyTimeReducible {β : Type} {encB : β ↪ List Bool}
    {X : PromiseProblem α} {Y : PromiseProblem β}
    (h : PromiseProblem.PolyTimeReducible enc encB X Y) (hY : Y ∈ PromiseNQP encB) :
    X ∈ PromiseNQP enc := by
  obtain ⟨B, hB, hyes, hno⟩ := hY
  obtain ⟨A, hAyes, hAno, hAB⟩ := h.exists_polyTimeReducible hyes hno
  exact ⟨A, mem_NQP_of_polyTimeReducible hAB hB, hAyes, hAno⟩

/-- `promiseClass PP` is closed under polynomial-time promise reductions. -/
theorem mem_promiseClass_PP_of_polyTimeReducible {β : Type} {encB : β ↪ List Bool}
    {X : PromiseProblem α} {Y : PromiseProblem β}
    (h : PromiseProblem.PolyTimeReducible enc encB X Y) (hY : Y ∈ promiseClass (PP encB)) :
    X ∈ promiseClass (PP enc) := by
  obtain ⟨B, hB, hyes, hno⟩ := hY
  obtain ⟨A, hAyes, hAno, hAB⟩ := h.exists_polyTimeReducible hyes hno
  exact ⟨A, hAB.mem_PP hB, hAyes, hAno⟩

end NQPClass

end CslibFrontier.Computability.Complexity
