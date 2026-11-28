/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PanMath Formalization Team (adapted from Kane, Ostuni, and Wu, CC-BY-4.0)
-/

module
-- upstream: candidate
public import Cslib.Computability.Circuit.Basic
public import Cslib.Probability.PMF
public import CslibFrontier.Foundations.BooleanAnalysis.LowDegree
public import CslibFrontier.Foundations.Data.BitString.Weight
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Logic.Function.DependsOn
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

import Cslib.Computability.Circuit.Depth
import CslibFrontier.Computability.Circuit.FanIn
import CslibFrontier.Computability.Circuit.Support
import CslibFrontier.Foundations.Data.Finset.Expect
import Mathlib.Algebra.CharP.Two
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Locally Computable Functions, Bounded-Depth Circuits, and $\mathbb{F}_2$ Reed–Muller Granularity

Defines `d`-local functions `f : (ι → α) → (κ → β)` whose output coordinates each depend on at most
`d` input coordinates, establishes that bounded-fan-in depth-`d` `Cslib.Circuits.Circuit`s compute
`(max 1 r ^ d)`-local functions, defines the canonical uniform Hamming-slice distribution on
Boolean cubes, and proves the `2 ^ (-d)` nonzero-density lower bound (Schwartz–Zippel /
Reed–Muller minimum distance) for nonzero degree-`d` polynomials over `ZMod 2`.

## Main definitions

* `CslibFrontier.Computability.IsLocal`: each output coordinate `j : κ` of `f : (ι → α) → (κ → β)`
  depends on a `Finset ι` of cardinality at most `d`.
* `CslibFrontier.Computability.uniformHammingSlice`: uniform distribution on
  `{x : κ → Bool | weight x = k}` for `k ≤ Fintype.card κ`.

## Main results

* `CslibFrontier.Computability.IsLocal.mono`, `CslibFrontier.Computability.isLocal_zero_iff`:
  monotonicity and `0`-locality characterization by constant functions.
* `CslibFrontier.Computability.isLocal_eval_of_fanInAtMost`: a circuit `c : Circuit σ m n` with
  fan-in at most `r` and depth at most `d` evaluates to a `(max 1 r ^ d)`-local function.
* `CslibFrontier.Computability.sum_mem_lowDegree_of_isLocal`: the sum of local Boolean output bits
  lies in `Cslib.BitString.lowDegree`.
* `CslibFrontier.Computability.two_inv_pow_le_dens_ne_zero_of_mem_lowDegree_zmod_two`: every nonzero
  `p ∈ lowDegree (ZMod 2) ι d` is nonzero on at least a `2 ^ (-d)` fraction of `ι → Bool`.
-/

public section

open Finset Function

namespace CslibFrontier.Computability

section Locality

variable {ι κ α β : Type*}

/-- A map `f : (ι → α) → (κ → β)` is `d`-local if every output coordinate `j : κ` depends on at most
`d` input coordinates. -/
def IsLocal (d : ℕ) (f : (ι → α) → (κ → β)) : Prop :=
  ∀ j : κ, ∃ S : Finset ι, #S ≤ d ∧ DependsOn (fun x ↦ f x j) (S : Set ι)

/-- Characterization of `IsLocal`. -/
theorem isLocal_iff {d : ℕ} {f : (ι → α) → (κ → β)} :
    IsLocal d f ↔ ∀ j : κ, ∃ S : Finset ι, #S ≤ d ∧ DependsOn (fun x ↦ f x j) (S : Set ι) :=
  Iff.rfl

/-- Monotonicity of `IsLocal` in the locality parameter `d`. -/
theorem IsLocal.mono {d d' : ℕ} {f : (ι → α) → (κ → β)} (hf : IsLocal d f) (hdd' : d ≤ d') :
    IsLocal d' f :=
  fun j ↦ let ⟨S, hS, hdep⟩ := hf j; ⟨S, hS.trans hdd', hdep⟩

/-- The identity map is `1`-local. -/
theorem isLocal_id : IsLocal 1 (id : (ι → α) → (ι → α)) :=
  fun j ↦ ⟨{j}, by simp, fun _ _ h ↦ h j (by simp)⟩

/-- Every constant map is `0`-local. -/
theorem isLocal_zero_const (y : κ → β) : IsLocal 0 (fun _ : ι → α ↦ y) :=
  fun _ ↦ ⟨∅, le_rfl, fun _ _ _ ↦ rfl⟩

/-- On a nonempty input alphabet, `f` is `0`-local iff `f` is constant. -/
theorem isLocal_zero_iff [Nonempty α] {f : (ι → α) → (κ → β)} :
    IsLocal 0 f ↔ ∃ y, ∀ x, f x = y := by
  constructor
  · intro hf
    inhabit α
    refine ⟨f default, fun x ↦ funext fun j ↦ ?_⟩
    obtain ⟨S, hS, hdep⟩ := hf j
    have hS0 : S = ∅ := card_eq_zero.mp (Nat.eq_zero_of_le_zero hS)
    subst hS0
    exact hdep fun _ hi ↦ False.elim (by simp at hi)
  · rintro ⟨y, hy⟩
    have : f = fun _ ↦ y := funext hy
    subst this
    exact isLocal_zero_const y

/-- Reparameterizing inputs where each coordinate depends on at most `1` new coordinate preserves
`d`-locality. -/
theorem IsLocal.comp_coordwise {ι' : Type*} {d : ℕ} {f : (ι → α) → (κ → β)}
    (hf : IsLocal d f) {g : (ι' → α) → (ι → α)}
    (hg : ∀ i : ι, ∃ T : Finset ι', #T ≤ 1 ∧ DependsOn (fun z ↦ g z i) (T : Set ι')) :
    IsLocal d (fun z ↦ f (g z)) := by
  classical
  intro j
  obtain ⟨S, hS, hdepS⟩ := hf j
  choose T hT_card hT_dep using hg
  refine ⟨S.biUnion T, ?_, ?_⟩
  · calc #(S.biUnion T) ≤ ∑ i ∈ S, #(T i) := card_biUnion_le
      _ ≤ ∑ _i ∈ S, 1 := sum_le_sum fun i _ ↦ hT_card i
      _ = #S := by simp
      _ ≤ d := hS
  · intro z₁ z₂ hz
    apply hdepS
    intro i hi
    apply hT_dep i
    intro k hk
    exact hz k (mem_biUnion.mpr ⟨i, hi, hk⟩)

/-- Every circuit `c : Cslib.Circuits.Circuit σ m n` of fan-in at most `r` and depth at most `d`
computes a `(max 1 r ^ d)`-local function. -/
theorem isLocal_eval_of_fanInAtMost {σ : Cslib.Circuits.Signature} {U : Type*} {m n r d : ℕ}
    (c : Cslib.Circuits.Circuit σ m n) (I : Cslib.Circuits.Interpretation σ U)
    (hfan : c.FanInAtMost r) (hdepth : c.depth ≤ d) :
    IsLocal (max 1 r ^ d) (c.eval I) := by
  intro j
  refine ⟨c.outputSupport j, ?_, ?_⟩
  · have hw := Cslib.Circuits.Program.card_wireSupport_le_pow hfan (c.outputs j)
    have hwd : c.program.wireDepths (c.outputs j) ≤ d :=
      (c.outputDepths_le_depth j).trans hdepth
    exact hw.trans (Nat.pow_le_pow_right (le_max_left 1 r) hwd)
  · intro x₁ x₂ hagree
    exact c.program.trace_congr I x₁ x₂ (c.outputs j) hagree

end Locality

section HammingSlice

/-- Canonical uniform distribution over the weight-`k` Hamming slice of `κ → Bool` for
`k ≤ Fintype.card κ`. -/
noncomputable def uniformHammingSlice (κ : Type*) [Fintype κ] [DecidableEq κ] (k : ℕ)
    (hk : k ≤ Fintype.card κ) : PMF (κ → Bool) :=
  Cslib.Probability.PMF.uniformOfFinset
    (univ.filter fun x : κ → Bool ↦ Cslib.BitString.weight x = k) (by
      rw [← card_pos, Cslib.BitString.card_filter_weight_eq]
      exact Nat.choose_pos hk)

/-- Probability mass assigned by `uniformHammingSlice κ k hk` to `x : κ → Bool`. -/
theorem uniformHammingSlice_apply {κ : Type*} [Fintype κ] [DecidableEq κ] {k : ℕ}
    (hk : k ≤ Fintype.card κ) (x : κ → Bool) :
    uniformHammingSlice κ k hk x =
      if Cslib.BitString.weight x = k then ((Fintype.card κ).choose k : ENNReal)⁻¹ else 0 := by
  rw [uniformHammingSlice, Cslib.Probability.PMF.uniformOfFinset_apply]
  simp only [mem_filter, mem_univ, true_and, Cslib.BitString.card_filter_weight_eq]

/-- Support of `uniformHammingSlice κ k hk`. -/
theorem mem_support_uniformHammingSlice {κ : Type*} [Fintype κ] [DecidableEq κ] {k : ℕ}
    (hk : k ≤ Fintype.card κ) {x : κ → Bool} :
    x ∈ (uniformHammingSlice κ k hk).support ↔ Cslib.BitString.weight x = k := by
  rw [uniformHammingSlice, Cslib.Probability.PMF.mem_support_uniformOfFinset_iff]
  simp

end HammingSlice

section PolynomialDegreeAndReedMuller

/-- A Boolean coordinate function depending on a finset `S : Finset ι` of size `#S ≤ d` has
multilinear polynomial degree at most `d` over any commutative ring `R`. -/
theorem bitVal_comp_mem_lowDegree_of_dependsOn {ι : Type*}
    (R : Type*) [CommRing R] {d : ℕ} {g : (ι → Bool) → Bool} {S : Finset ι} (hS : #S ≤ d)
    (hdep : DependsOn g (S : Set ι)) :
    (fun x ↦ Cslib.BitString.bitVal R (g x)) ∈ Cslib.BitString.lowDegree R ι d := by
  classical
  let indicatorS : (S → Bool) → (ι → Bool) → R := fun a x ↦
    ∏ i ∈ S.attach, if a i = true then Cslib.BitString.bitVal R (x i.1)
      else 1 - Cslib.BitString.bitVal R (x i.1)
  have hind_mem : ∀ a : S → Bool, indicatorS a ∈ Cslib.BitString.lowDegree R ι d := by
    intro a
    have hprod : (∏ i ∈ S.attach, fun x : ι → Bool ↦
        if a i = true then Cslib.BitString.bitVal R (x i.1)
        else 1 - Cslib.BitString.bitVal R (x i.1)) ∈
        Cslib.BitString.lowDegree R ι (#S.attach * 1) := by
      refine Cslib.BitString.prod_mem_lowDegree S.attach fun i _ ↦ ?_
      by_cases ha : a i = true
      · simp only [ha, ↓reduceIte]
        exact Cslib.BitString.bitVal_mem_lowDegree i.1
      · simp only [ha, Bool.false_eq_true, ↓reduceIte]
        exact Cslib.BitString.one_sub_mem_lowDegree (Cslib.BitString.bitVal_mem_lowDegree i.1)
    have heq_ind : indicatorS a = ∏ i ∈ S.attach, fun x : ι → Bool ↦
        if a i = true then Cslib.BitString.bitVal R (x i.1)
        else 1 - Cslib.BitString.bitVal R (x i.1) := by
      ext x
      simp [indicatorS, Finset.prod_apply]
    rw [heq_ind]
    exact Cslib.BitString.lowDegree_mono (by simpa using hS) hprod
  let extendA : (S → Bool) → (ι → Bool) := fun a j ↦
    if hj : j ∈ S then a ⟨j, hj⟩ else false
  have heq : (fun x ↦ Cslib.BitString.bitVal R (g x)) =
      ∑ a : S → Bool, Cslib.BitString.bitVal R (g (extendA a)) • indicatorS a := by
    ext x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    let ax : S → Bool := fun i ↦ x i.1
    rw [sum_eq_single ax]
    · have hind_one : indicatorS ax x = 1 := by
        refine prod_eq_one fun i _ ↦ ?_
        by_cases hx : x i.1 = true
        · simp [ax, hx, Cslib.BitString.bitVal]
        · have hxf : x i.1 = false := by cases h : x i.1 <;> simp_all
          simp [ax, hxf, Cslib.BitString.bitVal]
      have hg_eq : g (extendA ax) = g x := by
        apply hdep
        intro j hj
        have hjS : j ∈ S := hj
        simp [extendA, hjS, ax]
      rw [hind_one, mul_one, hg_eq]
    · intro a _ hne
      have hex : ∃ i : {j // j ∈ S}, a i ≠ x i.1 := by
        by_contra! hall
        exact hne (funext hall)
      obtain ⟨i, hi_ne⟩ := hex
      have hzero : indicatorS a x = 0 := by
        refine prod_eq_zero (mem_attach S i) ?_
        cases ha : a i <;> cases hx : x i.1 <;> simp_all [Cslib.BitString.bitVal]
      rw [hzero, mul_zero]
    · intro hax
      exact absurd (mem_univ ax) hax
  rw [heq]
  exact Submodule.sum_mem _ fun a _ ↦ Submodule.smul_mem _ _ (hind_mem a)

/-- If `f : (ι → Bool) → (κ → Bool)` is `d`-local, then for any commutative ring `R`, the sum of
output bits `∑ j, bitVal R (f x j)` belongs to `Cslib.BitString.lowDegree R ι d`. -/
theorem sum_mem_lowDegree_of_isLocal {ι κ : Type*} [Fintype κ]
    (R : Type*) [CommRing R] {d : ℕ} {f : (ι → Bool) → (κ → Bool)} (hf : IsLocal d f) :
    (fun x ↦ ∑ j : κ, Cslib.BitString.bitVal R (f x j)) ∈ Cslib.BitString.lowDegree R ι d := by
  have hterm : ∀ j : κ, (fun x ↦ Cslib.BitString.bitVal R (f x j)) ∈
      Cslib.BitString.lowDegree R ι d := by
    intro j
    obtain ⟨S, hS, hdep⟩ := hf j
    exact bitVal_comp_mem_lowDegree_of_dependsOn R hS hdep
  have heq : (fun x ↦ ∑ j : κ, Cslib.BitString.bitVal R (f x j)) =
      ∑ j : κ, fun x ↦ Cslib.BitString.bitVal R (f x j) := by
    ext x
    simp [Finset.sum_apply]
  rw [heq]
  exact Submodule.sum_mem (Cslib.BitString.lowDegree R ι d) fun j _ ↦ hterm j

private lemma lowDegree_cons_sub_mem {m d : ℕ} {R : Type*} [CommRing R]
    {p : (Fin (m + 1) → Bool) → R} (hp : p ∈ Cslib.BitString.lowDegree R (Fin (m + 1)) (d + 1)) :
    (fun y : Fin m → Bool ↦ p (Fin.cons true y) - p (Fin.cons false y)) ∈
      Cslib.BitString.lowDegree R (Fin m) d := by
  refine Submodule.span_induction
    (p := fun p _ ↦ (fun y : Fin m → Bool ↦ p (Fin.cons true y) - p (Fin.cons false y)) ∈
      Cslib.BitString.lowDegree R (Fin m) d) ?_ ?_ ?_ ?_ hp
  · rintro _ ⟨M, hM_card, rfl⟩
    have hM : #M ≤ d + 1 := by simpa using hM_card
    by_cases h0 : (0 : Fin (m + 1)) ∈ M
    · let M' : Finset (Fin m) := univ.filter fun i ↦ i.succ ∈ M
      have hM'_card : #M' ≤ d := by
        have hinj : ∀ i ∈ M', i.succ ∈ M.erase 0 := by
          intro i hi
          exact mem_erase.mpr ⟨Fin.succ_ne_zero i, (mem_filter.mp hi).2⟩
        have hle : #M' ≤ #(M.erase 0) :=
          card_le_card_of_injOn Fin.succ hinj fun _ _ _ _ h ↦ Fin.succ_injective _ h
        have herase : #(M.erase 0) = #M - 1 := card_erase_of_mem h0
        omega
      have heval : (fun y : Fin m → Bool ↦
          Cslib.BitString.monomial R M (Fin.cons true y) -
            Cslib.BitString.monomial R M (Fin.cons false y)) =
          Cslib.BitString.monomial R M' := by
        ext y
        have hnot_all : ¬ ∀ i ∈ M, (Fin.cons false y : Fin (m + 1) → Bool) i = true := by
          intro hall
          simpa using hall 0 h0
        have hfalse : Cslib.BitString.monomial R M (Fin.cons false y) = 0 := by
          rw [Cslib.BitString.monomial_apply]
          simp only [hnot_all, ↓reduceIte]
        rw [hfalse, sub_zero]
        simp only [Cslib.BitString.monomial_apply]
        congr 1
        refine propext ⟨fun hall i hi ↦ ?_, fun hall j hj ↦ ?_⟩
        · simpa using hall i.succ (mem_filter.mp hi).2
        · refine Fin.cases (by simp) (fun i hiM ↦ ?_) j hj
          exact hall i (mem_filter.mpr ⟨mem_univ i, hiM⟩)
      rw [heval]
      exact Cslib.BitString.monomial_mem_lowDegree hM'_card
    · have heval : (fun y : Fin m → Bool ↦
          Cslib.BitString.monomial R M (Fin.cons true y) -
            Cslib.BitString.monomial R M (Fin.cons false y)) = 0 := by
        ext y
        have hcongr : Cslib.BitString.monomial R M (Fin.cons true y) =
            Cslib.BitString.monomial R M (Fin.cons false y) := by
          simp only [Cslib.BitString.monomial_apply]
          congr 1
          refine propext ⟨fun hall j hj ↦ ?_, fun hall j hj ↦ ?_⟩
          · refine Fin.cases (fun h0M ↦ False.elim (h0 h0M)) (fun i hiM ↦ hall i.succ hiM) j hj
          · refine Fin.cases (fun h0M ↦ False.elim (h0 h0M)) (fun i hiM ↦ hall i.succ hiM) j hj
        simp [hcongr]
      rw [heval]
      exact Submodule.zero_mem _
  · have hz : (fun y : Fin m → Bool ↦
        (0 : (Fin (m + 1) → Bool) → R) (Fin.cons true y) -
          (0 : (Fin (m + 1) → Bool) → R) (Fin.cons false y)) = 0 := by
      ext; simp
    rw [hz]
    exact Submodule.zero_mem _
  · intro f g _ _ hf hg
    convert Submodule.add_mem _ hf hg using 1
    ext y; simp only [Pi.add_apply]; ring
  · intro c f _ hf
    convert Submodule.smul_mem _ c hf using 1
    ext y; simp only [Pi.smul_apply, smul_eq_mul]; ring

private lemma lowDegree_cons_mem {m d : ℕ} {R : Type*} [CommRing R] (b : Bool)
    {p : (Fin (m + 1) → Bool) → R} (hp : p ∈ Cslib.BitString.lowDegree R (Fin (m + 1)) d) :
    (fun y : Fin m → Bool ↦ p (Fin.cons b y)) ∈ Cslib.BitString.lowDegree R (Fin m) d := by
  refine Submodule.span_induction
    (p := fun p _ ↦ (fun y : Fin m → Bool ↦ p (Fin.cons b y)) ∈
      Cslib.BitString.lowDegree R (Fin m) d) ?_ ?_ ?_ ?_ hp
  · rintro _ ⟨M, hM_card, rfl⟩
    have hM : #M ≤ d := by simpa using hM_card
    by_cases h0 : (0 : Fin (m + 1)) ∈ M ∧ b = false
    · have hzero : (fun y : Fin m → Bool ↦ Cslib.BitString.monomial R M (Fin.cons b y)) = 0 := by
        ext y
        rcases h0 with ⟨h0M, rfl⟩
        have hnot_all : ¬ ∀ i ∈ M, (Fin.cons false y : Fin (m + 1) → Bool) i = true := by
          intro hall; simpa using hall 0 h0M
        rw [Cslib.BitString.monomial_apply]
        simp only [hnot_all, ↓reduceIte]
        rfl
      rw [hzero]
      exact Submodule.zero_mem _
    · let M' : Finset (Fin m) := univ.filter fun i ↦ i.succ ∈ M
      have hM'_card : #M' ≤ d := by
        have hle : #M' ≤ #M :=
          card_le_card_of_injOn Fin.succ (fun i hi ↦ (mem_filter.mp hi).2)
            fun _ _ _ _ h ↦ Fin.succ_injective _ h
        exact hle.trans hM
      have heval : (fun y : Fin m → Bool ↦ Cslib.BitString.monomial R M (Fin.cons b y)) =
          Cslib.BitString.monomial R M' := by
        ext y
        simp only [Cslib.BitString.monomial_apply]
        congr 1
        refine propext ⟨fun hall i hi ↦ ?_, fun hall j hj ↦ ?_⟩
        · simpa using hall i.succ (mem_filter.mp hi).2
        · refine Fin.cases (fun h0M ↦ ?_) (fun i hiM ↦ ?_) j hj
          · cases b with
            | false => exact False.elim (h0 ⟨h0M, rfl⟩)
            | true => rfl
          · exact hall i (mem_filter.mpr ⟨mem_univ i, hiM⟩)
      rw [heval]
      exact Cslib.BitString.monomial_mem_lowDegree hM'_card
  · exact Submodule.zero_mem _
  · intro f g _ _ hf hg; exact Submodule.add_mem _ hf hg
  · intro c f _ hf; exact Submodule.smul_mem _ c hf

private lemma reed_muller_fin : ∀ (m d : ℕ) (p : (Fin m → Bool) → ZMod 2),
    p ∈ Cslib.BitString.lowDegree (ZMod 2) (Fin m) d → p ≠ 0 →
    (2 : ℝ) ^ m * ((2 : ℝ)⁻¹ ^ d) ≤ (#(univ.filter fun x : Fin m → Bool ↦ p x ≠ 0) : ℝ)
  | 0, d, p, _, hp0 => by
    have hx : p default ≠ 0 := by
      intro h; apply hp0; ext x; rw [Subsingleton.elim x default, h]; rfl
    have hcard : #(univ.filter fun x : Fin 0 → Bool ↦ p x ≠ 0) = 1 := by
      rw [card_eq_one]
      refine ⟨default, ?_⟩
      ext x
      simp only [mem_filter, mem_univ, true_and, mem_singleton]
      exact ⟨fun _ ↦ Subsingleton.elim x default, fun h ↦ h ▸ hx⟩
    rw [hcard]
    simp only [pow_zero, one_mul, Nat.cast_one]
    exact pow_le_one₀ (by positivity) (by norm_num)
  | m + 1, 0, p, hp, hp0 => by
    have hconst : ∃ c : ZMod 2, ∀ x, p x = c := by
      refine Submodule.span_induction (p := fun p _ ↦ ∃ c : ZMod 2, ∀ x, p x = c) ?_ ?_ ?_ ?_ hp
      · rintro _ ⟨M, hM, rfl⟩
        have hM0 : M = ∅ := card_eq_zero.mp (Nat.eq_zero_of_le_zero (by simpa using hM))
        subst hM0
        exact ⟨1, fun x ↦ by simp [Cslib.BitString.monomial_apply]⟩
      · exact ⟨0, fun _ ↦ rfl⟩
      · rintro f g _ _ ⟨cf, hcf⟩ ⟨cg, hcg⟩
        exact ⟨cf + cg, fun x ↦ by simp [hcf x, hcg x]⟩
      · rintro a f _ ⟨cf, hcf⟩
        exact ⟨a * cf, fun x ↦ by simp [hcf x]⟩
    obtain ⟨c, hc⟩ := hconst
    have hc0 : c ≠ 0 := by
      intro h; apply hp0; ext x; simp [hc x, h]
    have hcard : #(univ.filter fun x : Fin (m + 1) → Bool ↦ p x ≠ 0) = 2 ^ (m + 1) := by
      rw [filter_true_of_mem fun x _ ↦ by simp [hc x, hc0]]
      simp
    rw [hcard]
    simp
  | m + 1, d + 1, p, hp, hp0 => by
    let p₀ : (Fin m → Bool) → ZMod 2 := fun y ↦ p (Fin.cons false y)
    let p₁ : (Fin m → Bool) → ZMod 2 := fun y ↦ p (Fin.cons true y)
    have hsplit : #(univ.filter fun x : Fin (m + 1) → Bool ↦ p x ≠ 0) =
        #(univ.filter fun y : Fin m → Bool ↦ p₀ y ≠ 0) +
          #(univ.filter fun y : Fin m → Bool ↦ p₁ y ≠ 0) := by
      simp only [card_eq_sum_ones, sum_filter]
      rw [Fin.sum_univ_cons_bool]
    by_cases heq : p₀ = p₁
    · have hp₀_ne' : p₀ ≠ 0 := by
        intro h0; apply hp0; ext x
        have hx : x = Fin.cons (x 0) (Fin.tail x) := (Fin.cons_self_tail x).symm
        rw [hx]
        cases x 0 with
        | false => exact congrFun h0 (Fin.tail x)
        | true => exact congrFun (heq.symm.trans h0) (Fin.tail x)
      have hp₀_mem : p₀ ∈ Cslib.BitString.lowDegree (ZMod 2) (Fin m) (d + 1) :=
        lowDegree_cons_mem false hp
      have ih := reed_muller_fin m (d + 1) p₀ hp₀_mem hp₀_ne'
      rw [hsplit, ← heq, Nat.cast_add]
      have hpow : (2 : ℝ) ^ (m + 1) * (2 : ℝ)⁻¹ ^ (d + 1) =
          2 * ((2 : ℝ) ^ m * (2 : ℝ)⁻¹ ^ (d + 1)) := by ring
      linarith
    · have hdiff_ne : (fun y ↦ p₁ y - p₀ y) ≠ 0 := by
        intro h0; apply heq; ext y
        exact (sub_eq_zero.mp (congrFun h0 y)).symm
      have hdiff_mem : (fun y ↦ p₁ y - p₀ y) ∈ Cslib.BitString.lowDegree (ZMod 2) (Fin m) d :=
        lowDegree_cons_sub_mem hp
      have ih := reed_muller_fin m d (fun y ↦ p₁ y - p₀ y) hdiff_mem hdiff_ne
      have hpt : #(univ.filter fun y : Fin m → Bool ↦ p₁ y - p₀ y ≠ 0) ≤
          #(univ.filter fun y : Fin m → Bool ↦ p₀ y ≠ 0) +
            #(univ.filter fun y : Fin m → Bool ↦ p₁ y ≠ 0) := by
        calc #(univ.filter fun y : Fin m → Bool ↦ p₁ y - p₀ y ≠ 0)
            ≤ #((univ.filter fun y : Fin m → Bool ↦ p₀ y ≠ 0) ∪
                (univ.filter fun y : Fin m → Bool ↦ p₁ y ≠ 0)) := by
              refine card_le_card fun y hy ↦ ?_
              have hne := (mem_filter.mp hy).2
              rw [mem_union, mem_filter, mem_filter]
              by_contra! hall
              exact hne (by simp [hall.1 (mem_univ y), hall.2 (mem_univ y)])
          _ ≤ _ := card_union_le _ _
      rw [hsplit]
      have hcast : (#(univ.filter fun y : Fin m → Bool ↦ p₁ y - p₀ y ≠ 0) : ℝ) ≤
          (#(univ.filter fun y : Fin m → Bool ↦ p₀ y ≠ 0) +
            #(univ.filter fun y : Fin m → Bool ↦ p₁ y ≠ 0) : ℕ) := by exact_mod_cast hpt
      have hpow : (2 : ℝ) ^ (m + 1) * (2 : ℝ)⁻¹ ^ (d + 1) =
          (2 : ℝ) ^ m * (2 : ℝ)⁻¹ ^ d := by ring
      linarith

/-- **Schwartz–Zippel / Reed–Muller Minimum Distance over `𝔽₂`**: any nonzero polynomial
`p ∈ Cslib.BitString.lowDegree (ZMod 2) ι d` takes a nonzero value on at least a `2 ^ (-d)`
fraction of `ι → Bool`. -/
theorem two_inv_pow_le_dens_ne_zero_of_mem_lowDegree_zmod_two {ι : Type*} [Fintype ι]
    [DecidableEq ι] {d : ℕ} {p : (ι → Bool) → ZMod 2}
    (hp : p ∈ Cslib.BitString.lowDegree (ZMod 2) ι d) (hp0 : p ≠ 0) :
    (2 : ℝ) ^ Fintype.card ι * (2 : ℝ)⁻¹ ^ d ≤ #(univ.filter fun x : ι → Bool ↦ p x ≠ 0) := by
  classical
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let q : (Fin (Fintype.card ι) → Bool) → ZMod 2 := fun y ↦ p (y ∘ e)
  have hq_mem : q ∈ Cslib.BitString.lowDegree (ZMod 2) (Fin (Fintype.card ι)) d := by
    refine Submodule.span_induction
      (p := fun f _ ↦ (fun y : Fin (Fintype.card ι) → Bool ↦ f (y ∘ e)) ∈
        Cslib.BitString.lowDegree (ZMod 2) (Fin (Fintype.card ι)) d) ?_ ?_ ?_ ?_ hp
    · rintro _ ⟨M, hM, rfl⟩
      have hM_le : #(M.map e.toEmbedding) ≤ d := by
        rw [card_map]
        simpa using hM
      have heval : (fun y : Fin (Fintype.card ι) → Bool ↦
          Cslib.BitString.monomial (ZMod 2) M (y ∘ e)) =
          Cslib.BitString.monomial (ZMod 2) (M.map e.toEmbedding) := by
        ext y
        simp only [Cslib.BitString.monomial_apply]
        congr 1
        refine propext ⟨fun h j hj ↦ ?_, fun h i hi ↦ ?_⟩
        · rcases mem_map.mp hj with ⟨i, hi, rfl⟩
          exact h i hi
        · exact h (e i) (mem_map.mpr ⟨i, hi, rfl⟩)
      rw [heval]
      exact Cslib.BitString.monomial_mem_lowDegree hM_le
    · exact Submodule.zero_mem _
    · intro f g _ _ hf hg; exact Submodule.add_mem _ hf hg
    · intro c f _ hf; exact Submodule.smul_mem _ c hf
  have hq_ne : q ≠ 0 := by
    intro h0; apply hp0; ext x
    have hx : x = (x ∘ e.symm) ∘ e := by ext i; simp
    rw [hx]; exact congrFun h0 (x ∘ e.symm)
  have hfin := reed_muller_fin (Fintype.card ι) d q hq_mem hq_ne
  have hcard_eq : #(univ.filter fun y : Fin (Fintype.card ι) → Bool ↦ q y ≠ 0) =
      #(univ.filter fun x : ι → Bool ↦ p x ≠ 0) := by
    refine card_bij (fun y _ ↦ y ∘ e) ?_ ?_ ?_
    · intro y hy
      exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hy).2⟩
    · intro y₁ _ y₂ _ heq
      ext j
      have := congrFun heq (e.symm j)
      simpa using this
    · intro x hx
      refine ⟨x ∘ e.symm, mem_filter.mpr ⟨mem_univ _, ?_⟩, by ext i; simp⟩
      have hpx := (mem_filter.mp hx).2
      have hcomp : (x ∘ e.symm) ∘ e = x := by ext i; simp
      dsimp [q]; rwa [hcomp]
  rwa [← hcard_eq]

end PolynomialDegreeAndReedMuller

end CslibFrontier.Computability
