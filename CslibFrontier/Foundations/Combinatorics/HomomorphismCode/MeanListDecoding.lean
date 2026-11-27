/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import Cslib.Probability.PMF
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.Probability.ProbabilityMassFunction.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Monad
public import CslibFrontier.Foundations.Combinatorics.HomomorphismCode.Basic

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Basic.ENNReal.BigOperators
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Bipartite Covering, Mean-List-Decoding, Irrelevant Quotients, and `Hom` vs `aHom`

This module formalizes the bipartite covering framework and its coding-theoretic applications:

- **Bipartite covering lemma**: double-counting upper bound `|W| ≤ L / δ` and probabilistic
  covering bound via `s` independent random trials (both finite counting and `PMF` formulations);
- **Mean-list-decoding**: mean agreement, mean-lists `L(C, F, λ)`, `r`-mean-list size `ℓ_{r,m}`,
  maximum mean-list size `ℓ_m`, repeated codes `C * r`, Markov degradation, concentration of
  mean-lists (`ℓ_m(C, λ + δ) ≤ (1 / δ) ℓ(C, λ)`), and equivalence of `CombEcon` and `CombEconM`;
- **Irrelevant quotients and quasivarieties**: identification of `aHom(G, H)` lists with
  `aHom(G/N, H)` mean-lists for any `(G, H)`-irrelevant normal subgroup `N ◁ G`, the irrelevant
  normal subgroup lemma, and the domain-relaxation principle for quasivarieties;
- **`Hom` versus `aHom`**: concentration of `aHom` lists into translated `Hom` lists, yielding
  `ℓ(aHom(G, H), λ) ≤ (1 / λ) ℓ(Hom(G, H), λ)` and `CombEcon` equivalence.

All results are proved under standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`).

## Main definitions

- `CslibFrontier.HomomorphismCode.iidPMF`: `s`-fold i.i.d. product of a `PMF`.
- `CslibFrontier.HomomorphismCode.meanAgreement`, `CslibFrontier.HomomorphismCode.meanListAgr`:
  mean agreement and mean-lists.
- `CslibFrontier.HomomorphismCode.maxRMeanListSize`,
  `CslibFrontier.HomomorphismCode.maxMeanListSize`: `ℓ_{r,m}` and `ℓ_m`.
- `CslibFrontier.HomomorphismCode.repeatCode`: the `r`-fold repetition code `C * r`.
- `CslibFrontier.HomomorphismCode.IsCombEconMeanClass`: combinatorial economical
  mean-list-decodability.
- `CslibFrontier.HomomorphismCode.IsQuasivariety`: closure of a class of groups under subgroups
  and products.
- `CslibFrontier.HomomorphismCode.translateReceived`: left-translated received word `f^a(g) =
  f(a)⁻¹ * f(a * g)`.

## Main results

- `CslibFrontier.HomomorphismCode.bipartite_double_counting`: `|W| ≤ L / δ`.
- `CslibFrontier.HomomorphismCode.bipartite_covering_iidPMF`: probabilistic bipartite covering
  bound via `PMF`.
- `CslibFrontier.HomomorphismCode.markov_degradation`: Markov degradation for mean agreement.
- `CslibFrontier.HomomorphismCode.maxMeanListSize_le_div_mul_maxListSize`: `ℓ_m(C, λ + δ) ≤ (1 /
  δ) ℓ(C, λ)`.
- `CslibFrontier.HomomorphismCode.maxListSize_aHom_eq_maxRMeanListSize_quotient`:
  `ℓ(aHom(G, H), λ) = ℓ_{|N|,m}(aHom(G/N, H), λ)` for irrelevant `N ◁ G`.
- `CslibFrontier.HomomorphismCode.irrelevant_normal_subgroup_bound`:
  `ℓ(aHom(G, H), Λ + ε) ≤ (2 / ε) ℓ(aHom(G/N, H), Λ + ε/2)`.
- `CslibFrontier.HomomorphismCode.maxListSize_aHom_le_div_mul_hom`:
  `ℓ(aHom(G, H), λ) ≤ (1 / λ) ℓ(Hom(G, H), λ)`.
-/

public section

namespace CslibFrontier.HomomorphismCode

open scoped BigOperators ENNReal

/-! ### Bipartite Covering Lemma -/

section Bipartite

/-- Double-counting lemma: in a bipartite graph `(V, W; E)` with `V` finite nonempty, `W` finite,
`deg(v) ≤ L` for all `v ∈ V`, and `deg(w) ≥ δ |V|` for all `w ∈ W` (`δ > 0`), we have
`|W| ≤ L / δ`. -/
theorem bipartite_double_counting {V W : Type*} [Fintype V] [Nonempty V] [Fintype W]
    (E : V → W → Prop) [DecidableRel E] {L δ : ℝ} (hδ : 0 < δ)
    (hV : ∀ v : V, ((Finset.univ.filter (fun w => E v w)).card : ℝ) ≤ L)
    (hW : ∀ w : W, δ * (Fintype.card V : ℝ) ≤ ((Finset.univ.filter (fun v => E v w)).card : ℝ)) :
    (Fintype.card W : ℝ) ≤ L / δ := by
  have hVpos : (0 : ℝ) < Fintype.card V := Nat.cast_pos.mpr Fintype.card_pos
  have hswap :
      (∑ w : W, (Finset.univ.filter (fun v => E v w)).card) =
        ∑ v : V, (Finset.univ.filter (fun w => E v w)).card := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  have hlow : δ * (Fintype.card V : ℝ) * (Fintype.card W : ℝ) ≤
      ∑ w : W, ((Finset.univ.filter (fun v => E v w)).card : ℝ) := by
    calc
      δ * (Fintype.card V : ℝ) * (Fintype.card W : ℝ)
          = ∑ _w : W, (δ * (Fintype.card V : ℝ)) := by
            simp [Finset.sum_const, nsmul_eq_mul, mul_comm]
      _ ≤ ∑ w : W, ((Finset.univ.filter (fun v => E v w)).card : ℝ) :=
            Finset.sum_le_sum fun w _ => hW w
  have hhigh : ∑ v : V, ((Finset.univ.filter (fun w => E v w)).card : ℝ) ≤
      (Fintype.card V : ℝ) * L := by
    calc
      ∑ v : V, ((Finset.univ.filter (fun w => E v w)).card : ℝ)
          ≤ ∑ _v : V, L := Finset.sum_le_sum fun v _ => hV v
      _ = (Fintype.card V : ℝ) * L := by simp [Finset.sum_const, nsmul_eq_mul]
  have hswapR :
      (∑ w : W, ((Finset.univ.filter (fun v => E v w)).card : ℝ)) =
        ∑ v : V, ((Finset.univ.filter (fun w => E v w)).card : ℝ) := by
    exact_mod_cast hswap
  have hmul : δ * (Fintype.card W : ℝ) ≤ L := by
    have hcomb : (Fintype.card V : ℝ) * (δ * (Fintype.card W : ℝ)) ≤ (Fintype.card V : ℝ) * L := by
      linarith
    exact le_of_mul_le_mul_left hcomb hVpos
  exact (le_div_iff₀ hδ).mpr (by linarith)

/-- `s`-fold i.i.d. product of a probability mass function `p : PMF α`. -/
noncomputable def iidPMF {α : Type*} (p : PMF α) : (s : ℕ) → PMF (Fin s → α)
  | 0 => PMF.pure Fin.elim0
  | s + 1 => p.bind fun a => (iidPMF p s).map fun t => Fin.cons a t

/-- Zero-sample base case for `iidPMF`. -/
@[simp]
theorem iidPMF_zero {α : Type*} (p : PMF α) : iidPMF p 0 = PMF.pure Fin.elim0 := by
  rfl

/-- Inductive step for `iidPMF`. -/
@[simp]
theorem iidPMF_succ {α : Type*} (p : PMF α) (s : ℕ) :
    iidPMF p (s + 1) = p.bind fun a => (iidPMF p s).map fun t => Fin.cons a t := by
  rfl

/-- Exact probability of a coordinatewise event under `iidPMF`. -/
theorem iidPMF_prob_forall {α : Type*} (p : PMF α) (P : α → Prop) [DecidablePred P] (s : ℕ) :
    (∑' t : Fin s → α, if ∀ i, P (t i) then iidPMF p s t else 0) =
      (∑' a : α, if P a then p a else 0) ^ s := by
  classical
  induction s with
  | zero =>
    simp [iidPMF, PMF.pure_apply, tsum_fintype, Subsingleton.elim (default : Fin 0 → α) Fin.elim0]
  | succ s ih =>
    simp only [iidPMF, PMF.bind_apply, PMF.map_apply]
    have hsplit : ∀ t : Fin (s + 1) → α,
        (if ∀ i, P (t i) then
            ∑' a : α, p a * ∑' u : Fin s → α, if t = Fin.cons a u then iidPMF p s u else 0
          else 0) =
        ∑' a : α, (if P a then p a else 0) *
          ∑' u : Fin s → α, if t = Fin.cons a u then
            (if ∀ j, P (u j) then iidPMF p s u else 0) else 0 := by
      intro t
      by_cases hP : ∀ i, P (t i)
      · rw [ite_eq_left_of_eq_true _ _ (eq_true hP)]
        refine tsum_congr fun a => ?_
        by_cases ha : P a
        · rw [ite_eq_left_of_eq_true _ _ (eq_true ha)]
          congr 1
          refine tsum_congr fun u => ?_
          by_cases htu : t = Fin.cons a u
          · subst htu
            have hu : ∀ j, P (u j) := fun j => by simpa using hP j.succ
            simp [hu]
          · simp [htu]
        · rw [ite_eq_right_of_eq_false _ _ (eq_false ha), zero_mul]
          have h0 : ∀ u : Fin s → α, t ≠ Fin.cons a u := by
            intro u htu
            apply ha
            have := hP 0
            rw [htu] at this
            simpa using this
          have htsum0 : (∑' u : Fin s → α, if t = Fin.cons a u then iidPMF p s u else 0) = 0 :=
            tsum_eq_zero_iff.mpr fun u => by simp [h0 u]
          rw [htsum0, mul_zero]
      · rw [ite_eq_right_of_eq_false _ _ (eq_false hP)]
        symm
        refine tsum_eq_zero_iff.mpr fun a => ?_
        by_cases ha : P a
        · rw [ite_eq_left_of_eq_true _ _ (eq_true ha)]
          have hinner : (∑' u : Fin s → α, if t = Fin.cons a u then
              (if ∀ j, P (u j) then iidPMF p s u else 0) else 0) = 0 := by
            refine tsum_eq_zero_iff.mpr fun u => ?_
            by_cases htu : t = Fin.cons a u
            · rw [ite_eq_left_of_eq_true _ _ (eq_true htu)]
              have hnotu : ¬ ∀ j, P (u j) := by
                intro hu
                apply hP
                intro i
                rw [htu]
                cases i using Fin.cases with
                | zero => simpa using ha
                | succ j => simpa using hu j
              simp [hnotu]
            · simp [htu]
          rw [hinner, mul_zero]
        · rw [ite_eq_right_of_eq_false _ _ (eq_false ha), zero_mul]
    have hswap2 : ∀ a : α,
        (∑' t : Fin (s + 1) → α, (if P a then p a else 0) *
          ∑' u : Fin s → α, if t = Fin.cons a u then
            (if ∀ j, P (u j) then iidPMF p s u else 0) else 0) =
        (if P a then p a else 0) *
          (∑' u : Fin s → α, if ∀ j, P (u j) then iidPMF p s u else 0) := by
      intro a
      rw [ENNReal.tsum_mul_left]
      congr 1
      rw [tsum_comm]
      refine tsum_congr fun u => ?_
      rw [tsum_ite_eq]
    calc
      _ = ∑' t : Fin (s + 1) → α, ∑' a : α, (if P a then p a else 0) *
            ∑' u : Fin s → α, if t = Fin.cons a u then
              (if ∀ j, P (u j) then iidPMF p s u else 0) else 0 :=
            tsum_congr fun t => by convert hsplit t
      _ = ∑' a : α, ∑' t : Fin (s + 1) → α, (if P a then p a else 0) *
            ∑' u : Fin s → α, if t = Fin.cons a u then
              (if ∀ j, P (u j) then iidPMF p s u else 0) else 0 := tsum_comm
      _ = ∑' a : α, (if P a then p a else 0) *
            (∑' u : Fin s → α, if ∀ j, P (u j) then iidPMF p s u else 0) :=
            tsum_congr hswap2
      _ = (∑' a : α, if P a then p a else 0) ^ (s + 1) := by
            rw [ENNReal.tsum_mul_right, pow_succ']
            congr 1

/-- For any `PMF` over sets `S : Set W`, if every `w ∈ W` is covered by a single draw with
probability at least `γ`, then `s` i.i.d. draws fail to cover `W` with probability at most
`|W| * (1 - γ)^s`. -/
theorem union_bound_iidPMF_uncovered {Ω W : Type*} [Fintype W]
    (p : PMF Ω) (D : Ω → Set W) [∀ ω, DecidablePred (· ∈ D ω)] {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (hcov : ∀ w : W, ENNReal.ofReal γ ≤ ∑' ω : Ω, if w ∈ D ω then p ω else 0) (s : ℕ) :
    (∑' t : Fin s → Ω, if ¬ ∀ w : W, ∃ i, w ∈ D (t i) then iidPMF p s t else 0) ≤
      (Fintype.card W : ℝ≥0∞) * (ENNReal.ofReal (1 - γ)) ^ s := by
  classical
  have htsum_finset : ∀ (S : Finset W) (F : W → (Fin s → Ω) → ℝ≥0∞),
      (∑ w ∈ S, ∑' t, F w t) = ∑' t, ∑ w ∈ S, F w t := by
    intro S F
    induction S using Finset.induction_on with
    | empty => simp
    | @insert w₀ S hw₀ ih =>
      rw [Finset.sum_insert hw₀, ih, ← tsum_add]
      exact tsum_congr fun t => (Finset.sum_insert (f := fun w => F w t) hw₀).symm
  have hle_sum :
      (∑' t : Fin s → Ω, if ¬ ∀ w : W, ∃ i, w ∈ D (t i) then iidPMF p s t else 0) ≤
        ∑ w : W, (∑' t : Fin s → Ω, if ∀ i, w ∉ D (t i) then iidPMF p s t else 0) := by
    rw [htsum_finset]
    refine tsum_le_tsum fun t => ?_
    by_cases h : ∀ w : W, ∃ i, w ∈ D (t i)
    · simp [h]
    · simp only [h, not_false_eq_true, ↓reduceIte]
      push Not at h
      obtain ⟨w₀, hw₀⟩ := h
      exact le_trans (by simp [hw₀])
        (Finset.single_le_sum (fun _ _ => bot_le) (Finset.mem_univ w₀))
  refine hle_sum.trans ?_
  calc
    ∑ w : W, (∑' t : Fin s → Ω, if ∀ i, w ∉ D (t i) then iidPMF p s t else 0)
        = ∑ w : W, (∑' ω : Ω, if w ∉ D ω then p ω else 0) ^ s := by
          refine Finset.sum_congr rfl fun w _ => iidPMF_prob_forall p (fun ω => w ∉ D ω) s
    _ ≤ ∑ _w : W, (ENNReal.ofReal (1 - γ)) ^ s := by
          refine Finset.sum_le_sum fun w _ => ?_
          gcongr
          have hpart :
              (∑' ω : Ω, if w ∈ D ω then p ω else 0) +
                (∑' ω : Ω, if w ∉ D ω then p ω else 0) = 1 := by
            rw [← tsum_add]
            have heq : (fun ω : Ω => (if w ∈ D ω then p ω else 0) +
                (if w ∉ D ω then p ω else 0)) = fun ω => p ω := by
              funext ω; by_cases hw : w ∈ D ω <;> simp [hw]
            rw [heq, p.tsum_coe]
          have hsub : (∑' ω : Ω, if w ∉ D ω then p ω else 0) ≤ 1 - ENNReal.ofReal γ := by
            have h1 := hcov w
            have hle1 : ENNReal.ofReal γ ≤ 1 := by
              rw [← ENNReal.ofReal_one]
              exact ENNReal.ofReal_le_ofReal hγ1
            have hne : ENNReal.ofReal γ ≠ ⊤ := ENNReal.ofReal_ne_top
            exact (ENNReal.le_sub_iff_add_le_left hne hle1).mpr
              (le_trans (add_le_add_left h1 _) (le_of_eq hpart))
          rw [ENNReal.ofReal_sub 1 hγ0, ENNReal.ofReal_one]
          exact hsub
    _ = (Fintype.card W : ℝ≥0∞) * (ENNReal.ofReal (1 - γ)) ^ s := by
          simp [Finset.sum_const, nsmul_eq_mul]

/-- Quantitative exponential bound: `(1 - γ)^s ≤ exp (-γ * s)` and when
`s ≥ (1 / γ) * log (M / η)` with `0 < γ ≤ 1`, `0 < η`, `0 ≤ M`, we have `M * (1 - γ)^s ≤ η`. -/
theorem mul_one_sub_pow_le_of_log_le {M γ η : ℝ} {s : ℕ} (hM : 0 ≤ M) (hγ : 0 < γ)
    (hγ1 : γ ≤ 1) (hη : 0 < η) (hs : (1 / γ) * Real.log (M / η) ≤ (s : ℝ)) :
    M * (1 - γ) ^ s ≤ η := by
  by_cases hM0 : M = 0
  · subst hM0; simp [hη.le]
  have hMpos : 0 < M := lt_of_le_of_ne hM (Ne.symm hM0)
  have h1sub : 1 - γ ≤ Real.exp (-γ) := by
    linarith [Real.add_one_le_exp (-γ)]
  have hpow : (1 - γ) ^ s ≤ Real.exp (-γ * (s : ℝ)) := by
    calc
      (1 - γ) ^ s ≤ (Real.exp (-γ)) ^ s := pow_le_pow_left₀ (by linarith) h1sub s
      _ = Real.exp ((s : ℝ) * (-γ)) := (Real.exp_nat_mul (-γ) s).symm
      _ = Real.exp (-γ * (s : ℝ)) := by ring_nf
  have hexp_le : Real.exp (-γ * (s : ℝ)) ≤ η / M := by
    have hlog : Real.log (M / η) ≤ γ * (s : ℝ) := by
      have := (mul_le_mul_iff_right₀ hγ).mpr hs
      have hsimp : γ * ((1 / γ) * Real.log (M / η)) = Real.log (M / η) := by
        field_simp [hγ.ne']
      linarith
    have hneg : -γ * (s : ℝ) ≤ Real.log (η / M) := by
      rw [Real.log_div hMpos.ne' hη.ne'] at hlog
      rw [Real.log_div hη.ne' hMpos.ne']
      linarith
    calc
      Real.exp (-γ * (s : ℝ)) ≤ Real.exp (Real.log (η / M)) := Real.exp_le_exp.mpr hneg
      _ = η / M := Real.exp_log (div_pos hη hMpos)
  calc
    M * (1 - γ) ^ s ≤ M * Real.exp (-γ * (s : ℝ)) :=
      mul_le_mul_of_nonneg_left hpow hM
    _ ≤ M * (η / M) := mul_le_mul_of_nonneg_left hexp_le hM
    _ = η := mul_div_cancel₀ η hMpos.ne'

/-- Bipartite covering lemma (probabilistic part):
given a finite bipartite graph `(V, W; E)` with `deg(v) ≤ L` and `deg(w) ≥ δ |V|`, and a
family of randomized procedures `D v : PMF (Set W)` each outputting a superset of `N(v)` with
probability at least `r` (e.g. `r = 3 / 4`), drawing `s` independent uniform `v_i ∈ V` and
running `D v_i` covers all of `W` with failure probability at most
`(L / δ) * (1 - r * δ)^s` (hence `≤ η` whenever `s ≥ (1 / (r * δ)) * log (L / (η * δ))`). -/
theorem bipartite_covering_iidPMF {V W Ω : Type*} [Fintype V] [Nonempty V] [Fintype W]
    (E : V → W → Prop) [DecidableRel E] {L δ r : ℝ} (hL : 0 ≤ L) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hr : 0 < r) (hr1 : r ≤ 1)
    (hV : ∀ v : V, ((Finset.univ.filter (fun w => E v w)).card : ℝ) ≤ L)
    (hW : ∀ w : W, δ * (Fintype.card V : ℝ) ≤ ((Finset.univ.filter (fun v => E v w)).card : ℝ))
    (D : V → PMF Ω) (out : V → Ω → Set W) [∀ v ω, DecidablePred (· ∈ out v ω)]
    (hD : ∀ v : V, ENNReal.ofReal r ≤
      ∑' ω : Ω, if (∀ w : W, E v w → w ∈ out v ω) then D v ω else 0)
    (s : ℕ) :
    let stepPMF : PMF (V × Ω) :=
      (Cslib.Probability.PMF.uniformOfFintype V).bind fun v => (D v).map (fun ω => (v, ω))
    (∑' t : Fin s → V × Ω,
        if ¬ ∀ w : W, ∃ i, w ∈ out (t i).1 (t i).2 then iidPMF stepPMF s t else 0) ≤
      ENNReal.ofReal ((L / δ) * (1 - r * δ) ^ s) := by
  classical
  intro stepPMF
  have hWle : (Fintype.card W : ℝ) ≤ L / δ := bipartite_double_counting E hδ hV hW
  have hrδ0 : 0 ≤ r * δ := by positivity
  have hrδ1 : r * δ ≤ 1 := by nlinarith
  have hcov_single : ∀ w : W,
      ENNReal.ofReal (r * δ) ≤
        ∑' p : V × Ω, if w ∈ out p.1 p.2 then stepPMF p else 0 := by
    intro w
    have hcalc :
        (∑' p : V × Ω, if w ∈ out p.1 p.2 then stepPMF p else 0) =
          ∑ v : V, (Fintype.card V : ℝ≥0∞)⁻¹ *
            (∑' ω : Ω, if w ∈ out v ω then D v ω else 0) := by
      rw [tsum_prod', tsum_fintype]
      refine Finset.sum_congr rfl fun v _ => ?_
      have hstep : ∀ ω : Ω,
          (if w ∈ out v ω then stepPMF (v, ω) else 0) =
            (Fintype.card V : ℝ≥0∞)⁻¹ * (if w ∈ out v ω then D v ω else 0) := by
        intro ω
        by_cases hw : w ∈ out v ω
        · simp only [hw, ↓reduceIte, stepPMF, PMF.bind_apply, PMF.map_apply,
            Cslib.Probability.PMF.uniformOfFintype_apply]
          rw [tsum_fintype, Finset.sum_eq_single v]
          · congr 1
            refine (tsum_eq_single ω ?_).trans (by simp)
            intro ω' hω'; simp [hω'.symm]
          · intro v' _ hv'
            rw [mul_eq_zero]
            exact Or.inr (tsum_eq_zero_iff.mpr fun a => by simp [hv'.symm])
          · intro hv; exact absurd (Finset.mem_univ v) hv
        · simp [hw]
      simp_rw [hstep, ENNReal.tsum_mul_left]
    rw [hcalc]
    let S : Finset V := Finset.univ.filter (fun v => E v w)
    have hge_S :
        ∑ v ∈ S, (Fintype.card V : ℝ≥0∞)⁻¹ * ENNReal.ofReal r ≤
          ∑ v : V, (Fintype.card V : ℝ≥0∞)⁻¹ *
            (∑' ω : Ω, if w ∈ out v ω then D v ω else 0) := by
      refine le_trans ?_ (Finset.sum_le_univ_sum_of_nonneg (s := S) (fun _ => bot_le))
      refine Finset.sum_le_sum fun v hv => ?_
      have hEvw : E v w := (Finset.mem_filter.mp hv).2
      gcongr
      refine le_trans (hD v) (tsum_le_tsum fun ω => ?_)
      by_cases h1 : ∀ w' : W, E v w' → w' ∈ out v ω
      · rw [ite_eq_left_of_eq_true _ _ (eq_true h1),
          ite_eq_left_of_eq_true _ _ (eq_true (h1 w hEvw))]
      · rw [ite_eq_right_of_eq_false _ _ (eq_false h1)]
        exact bot_le
    refine le_trans ?_ hge_S
    rw [Finset.sum_const, nsmul_eq_mul]
    have hVpos : (0 : ℝ) < Fintype.card V := Nat.cast_pos.mpr Fintype.card_pos
    have hSge : δ * (Fintype.card V : ℝ) ≤ (S.card : ℝ) := hW w
    have hcast :
        (S.card : ℝ≥0∞) * ((Fintype.card V : ℝ≥0∞)⁻¹ * ENNReal.ofReal r) =
          ENNReal.ofReal (((S.card : ℝ) / (Fintype.card V : ℝ)) * r) := by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_div_of_pos hVpos,
        ENNReal.ofReal_natCast, ENNReal.ofReal_natCast, div_eq_mul_inv, mul_assoc]
    rw [hcast]
    refine ENNReal.ofReal_le_ofReal ?_
    have hdiv : δ ≤ (S.card : ℝ) / (Fintype.card V : ℝ) := (le_div_iff₀ hVpos).mpr hSge
    nlinarith
  have hunion := union_bound_iidPMF_uncovered stepPMF (fun p => out p.1 p.2) hrδ0 hrδ1 hcov_single s
  refine hunion.trans ?_
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by linarith)]
  gcongr
  rw [← ENNReal.ofReal_natCast]
  exact ENNReal.ofReal_le_ofReal hWle

end Bipartite

/-! ### Mean-List-Decoding -/

section MeanList

variable {α β ι : Type*}

/-- Mean agreement `(1 / |ι|) ∑ i, agr(φ, f i)` of a function `φ` with a finite family `f`. -/
@[expose]
noncomputable def meanAgreement [Fintype α] [Fintype ι] (φ : α → β) (f : ι → α → β) : ℝ :=
  (∑ i : ι, agreement φ (f i)) / (Fintype.card ι : ℝ)

/-- Mean-list `L(C, f, lam)` of codewords having mean agreement at least `lam` with `f`. -/
@[expose]
def meanListAgr [Fintype α] [Fintype ι] (C : Set (α → β)) (f : ι → α → β) (lam : ℝ) :
    Set (α → β) :=
  {w ∈ C | lam ≤ meanAgreement w f}

theorem mem_meanListAgr_iff [Fintype α] [Fintype ι] {C : Set (α → β)} {f : ι → α → β}
    {lam : ℝ} {w : α → β} :
    w ∈ meanListAgr C f lam ↔ w ∈ C ∧ lam ≤ meanAgreement w f :=
  Iff.rfl

/-- Maximum mean-list size over families indexed by a given finite type `ι`. -/
@[expose]
noncomputable def maxMeanListSizeOf [Fintype α] (C : Set (α → β)) (ι : Type*) [Fintype ι]
    (lam : ℝ) : ℕ∞ :=
  ⨆ f : ι → α → β, (meanListAgr C f lam).encard

/-- Maximum `r`-mean-list size `ℓ_{r,m}(C, lam)`. -/
@[expose]
noncomputable def maxRMeanListSize [Fintype α] (C : Set (α → β)) (r : ℕ) (lam : ℝ) : ℕ∞ :=
  maxMeanListSizeOf C (Fin r) lam

/-- Maximum mean-list size `ℓ_m(C, lam) = ⨆_{r ≥ 1} ℓ_{r,m}(C, lam)`. -/
@[expose]
noncomputable def maxMeanListSize [Fintype α] (C : Set (α → β)) (lam : ℝ) : ℕ∞ :=
  ⨆ (r : ℕ) (_ : 0 < r), maxRMeanListSize C r lam

/-- The `r`-fold repetition code `C * r` on `α × Fin r`. -/
@[expose]
def repeatCode (C : Set (α → β)) (r : ℕ) : Set (α × Fin r → β) :=
  {g | ∃ w ∈ C, g = fun p => w p.1}

/-- A class of codes is `CombEconM` if `ℓ_m(C, Λ_C + ε)` is uniformly bounded by a polynomial in
`1 / ε`. -/
@[expose]
def IsCombEconMeanClass {κ : Type*}
    (C : κ → Σ (α : Type*) (β : Type*), Fintype α × Set (α → β)) : Prop :=
  ∃ (K : ℝ) (d : ℕ), 0 < K ∧
    ∀ (i : κ) (ε : ℝ), 0 < ε →
      @maxMeanListSize (C i).1 (C i).2.1 (C i).2.2.1 (C i).2.2.2
        (@codeMaxAgreement (C i).1 (C i).2.1 (C i).2.2.1 (C i).2.2.2 + ε) ≤
        (Nat.floor (K * (1 / ε) ^ d) : ℕ∞)

theorem meanAgreement_nonneg [Fintype α] [Fintype ι] (φ : α → β) (f : ι → α → β) :
    0 ≤ meanAgreement φ f := by
  unfold meanAgreement
  exact div_nonneg (Finset.sum_nonneg fun i _ => agreement_nonneg φ (f i)) (Nat.cast_nonneg _)

theorem meanAgreement_le_one [Fintype α] [Fintype ι] (φ : α → β) (f : ι → α → β) :
    meanAgreement φ f ≤ 1 := by
  unfold meanAgreement
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp [Fintype.card_eq_zero]
  · have hpos : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
    rw [div_le_one hpos]
    calc
      ∑ i : ι, agreement φ (f i) ≤ ∑ _i : ι, (1 : ℝ) :=
        Finset.sum_le_sum fun i _ => agreement_le_one φ (f i)
      _ = (Fintype.card ι : ℝ) := by simp

theorem meanAgreement_const [Fintype α] [Fintype ι] [Nonempty ι] (φ g : α → β) :
    meanAgreement φ (fun _ : ι => g) = agreement φ g := by
  have hpos : (Fintype.card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp [meanAgreement, Finset.sum_const, nsmul_eq_mul, hpos]

/-- Sharp non-strict Markov degradation valid for all `lam < 1`:
`δ / (1 - lam) ≤ density {i : ι | lam < agreement φ (f i)}`. -/
theorem markov_degradation_le [Fintype α] [Fintype ι] [Nonempty ι] {φ : α → β} {f : ι → α → β}
    {lam δ : ℝ} (hlam1 : lam < 1) (hmean : lam + δ ≤ meanAgreement φ f) :
    δ / (1 - lam) ≤ density {i : ι | lam < agreement φ (f i)} := by
  classical
  have hIpos : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  have h1m_pos : 0 < 1 - lam := by linarith
  let S : Finset ι := Finset.univ.filter (fun i => lam < agreement φ (f i))
  have hdens : density {i : ι | lam < agreement φ (f i)} = (S.card : ℝ) / (Fintype.card ι : ℝ) := by
    rw [← density_coe S]
    congr 1; ext i; simp [S]
  rw [hdens]
  have hsum_le : ∑ i : ι, agreement φ (f i) ≤
      (S.card : ℝ) * 1 + ((Fintype.card ι : ℝ) - (S.card : ℝ)) * lam := by
    have hsplit := Finset.sum_filter_add_sum_filter_not (s := Finset.univ)
      (p := fun i => lam < agreement φ (f i)) (f := fun i => agreement φ (f i))
    rw [← hsplit]
    have h1 : ∑ i ∈ S, agreement φ (f i) ≤ (S.card : ℝ) * 1 :=
      (Finset.sum_le_sum fun i _ => agreement_le_one φ (f i)).trans_eq (by simp)
    have h2 : ∑ i ∈ Finset.univ.filter (fun i => ¬ lam < agreement φ (f i)), agreement φ (f i) ≤
        ((Fintype.card ι : ℝ) - (S.card : ℝ)) * lam := by
      have hcard : ((Finset.univ.filter (fun i => ¬ lam < agreement φ (f i))).card : ℝ) =
          (Fintype.card ι : ℝ) - (S.card : ℝ) := by
        have hp := Finset.card_filter_add_card_filter_not (s := Finset.univ)
          (p := fun i : ι => lam < agreement φ (f i))
        have hpR : (S.card : ℝ) +
            ((Finset.univ.filter (fun i => ¬ lam < agreement φ (f i))).card : ℝ) =
            (Fintype.card ι : ℝ) := by
          simpa only [Finset.card_univ, Nat.cast_add] using congrArg (Nat.cast (R := ℝ)) hp
        linarith
      calc
        ∑ i ∈ Finset.univ.filter (fun i => ¬ lam < agreement φ (f i)), agreement φ (f i)
            ≤ ∑ _i ∈ Finset.univ.filter (fun i => ¬ lam < agreement φ (f i)), lam :=
              Finset.sum_le_sum fun i hi => not_lt.mp (Finset.mem_filter.mp hi).2
        _ = ((Finset.univ.filter (fun i => ¬ lam < agreement φ (f i))).card : ℝ) * lam := by
              simp [Finset.sum_const, nsmul_eq_mul]
        _ = ((Fintype.card ι : ℝ) - (S.card : ℝ)) * lam := by rw [hcard]
    linarith
  have hmul_le : (lam + δ) * (Fintype.card ι : ℝ) ≤ ∑ i : ι, agreement φ (f i) :=
    (le_div_iff₀ hIpos).mp hmean
  have h1 : δ * (Fintype.card ι : ℝ) ≤ (1 - lam) * (S.card : ℝ) := by linarith
  have h2 := (div_le_div_iff_of_pos_right hIpos).mpr h1
  rw [mul_div_cancel_right₀ _ hIpos.ne', mul_div_assoc] at h2
  exact (div_le_iff₀ h1m_pos).mpr (by linarith)

/-- Markov degradation (Lemma `lemma:mean-markov-degredation`):
if `meanAgreement φ f ≥ lam + δ` with `0 < lam < 1` and `0 < δ`, then the fraction of `i : ι` with
`lam < agreement φ (f i)` is strictly greater than `δ`. -/
theorem markov_degradation [Fintype α] [Fintype ι] [Nonempty ι] {φ : α → β} {f : ι → α → β}
    {lam δ : ℝ} (hlam0 : 0 < lam) (hlam1 : lam < 1) (hδ : 0 < δ)
    (hmean : lam + δ ≤ meanAgreement φ f) :
    δ < density {i : ι | lam < agreement φ (f i)} := by
  have h1m_pos : 0 < 1 - lam := by linarith
  have hdiv_ge := markov_degradation_le hlam1 hmean
  have hstrict : δ < δ / (1 - lam) := by
    rw [lt_div_iff₀ h1m_pos]
    nlinarith
  exact lt_of_lt_of_le hstrict hdiv_ge

/-- Concentration of mean-lists, part (i) (Lemma `lemma:mean-central-meanlist-relationship`(i)):
for any finite nonempty `ι`, `lam ≥ 0`, `lam < 1`, `δ > 0`, and any `f : ι → α → β`,
`|meanListAgr C f (lam + δ)| ≤ ℓ(C, lam) / δ` (in fact `((1 - lam) / δ) * ℓ(C, lam)`). -/
theorem meanListAgr_encard_le_div_mul_maxListSize [Fintype α] [Fintype ι] [Nonempty ι]
    (C : Set (α → β)) (f : ι → α → β) {lam δ : ℝ} (hlam0 : 0 ≤ lam) (hlam1 : lam < 1) (hδ : 0 < δ)
    {M : ℝ} (hM : 0 ≤ M) (hlist : maxListSize C lam ≤ (Nat.floor M : ℕ∞)) :
    (meanListAgr C f (lam + δ)).encard ≤ (Nat.floor (M / δ) : ℕ∞) := by
  classical
  rw [encard_le_floor_iff (by positivity)]
  intro B hB
  let E : ι → B → Prop := fun i w => lam < agreement w.1 (f i)
  have hV : ∀ i : ι, ((Finset.univ.filter (fun w : B => E i w)).card : ℝ) ≤ M := by
    intro i
    let T : Finset (α → β) := B.filter (fun w => lam < agreement w (f i))
    have hcard : (Finset.univ.filter (fun w : B => E i w)).card = T.card := by
      refine Finset.card_bij (fun w _ => w.1) ?_ ?_ ?_
      · intro w hw; exact Finset.mem_filter.mpr ⟨w.2, (Finset.mem_filter.mp hw).2⟩
      · intro w₁ _ w₂ _ h; exact Subtype.ext h
      · intro w hw
        exact ⟨⟨w, (Finset.mem_filter.mp hw).1⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hw).2⟩, rfl⟩
    rw [hcard]
    have hTsub : (T : Set (α → β)) ⊆ codeListAgr C (f i) lam := by
      intro w hw
      have hw' := Finset.mem_filter.mp hw
      exact ⟨(hB hw'.1).1, hw'.2.le⟩
    exact (maxListSize_le_floor_iff C lam hM).mp hlist (f i) T hTsub
  have hW : ∀ w : B, δ * (Fintype.card ι : ℝ) ≤
      ((Finset.univ.filter (fun i : ι => E i w)).card : ℝ) := by
    intro w
    have hmark := markov_degradation_le hlam1 (hB w.2).2
    have h1m : 1 - lam ≤ 1 := by linarith
    have h1m_pos : 0 < 1 - lam := by linarith
    have hδ_le : δ ≤ density {i : ι | lam < agreement w.1 (f i)} :=
      le_trans ((le_div_iff₀ h1m_pos).mpr (by nlinarith)) hmark
    have hIpos : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
    have hdens : density {i : ι | lam < agreement w.1 (f i)} =
        ((Finset.univ.filter (fun i : ι => E i w)).card : ℝ) / (Fintype.card ι : ℝ) := by
      rw [← density_coe]
      congr 1; ext i; simp [E]
    rw [hdens] at hδ_le
    exact (le_div_iff₀ hIpos).mp hδ_le
  have h := bipartite_double_counting E hδ hV hW
  simpa only [Fintype.card_coe] using h

/-- Maximum mean-list size bound: `ℓ_m(C, lam + δ) ≤ (1 / δ) * ℓ(C, lam)`. -/
theorem maxMeanListSize_le_div_mul_maxListSize [Fintype α] (C : Set (α → β))
    {lam δ : ℝ} (hlam0 : 0 ≤ lam) (hlam1 : lam < 1) (hδ : 0 < δ) {M : ℝ} (hM : 0 ≤ M)
    (hlist : maxListSize C lam ≤ (Nat.floor M : ℕ∞)) :
    maxMeanListSize C (lam + δ) ≤ (Nat.floor (M / δ) : ℕ∞) := by
  refine iSup₂_le fun r hr => iSup_le fun f => ?_
  have : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  exact meanListAgr_encard_le_div_mul_maxListSize C f hlam0 hlam1 hδ hM hlist

theorem maxListSize_le_maxRMeanListSize [Fintype α] (C : Set (α → β)) (r : ℕ) (hr : 0 < r)
    (lam : ℝ) :
    maxListSize C lam ≤ maxRMeanListSize C r lam := by
  have : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  refine iSup_le fun f => ?_
  have heq : meanListAgr C (fun _ : Fin r => f) lam = codeListAgr C f lam := by
    ext w
    simp [mem_meanListAgr_iff, mem_codeListAgr_iff, meanAgreement_const]
  rw [← heq]
  exact le_iSup (fun g : Fin r → α → β => (meanListAgr C g lam).encard) (fun _ => f)

theorem maxListSize_le_maxMeanListSize [Fintype α] (C : Set (α → β)) (lam : ℝ) :
    maxListSize C lam ≤ maxMeanListSize C lam :=
  (maxListSize_le_maxRMeanListSize C 1 one_pos lam).trans
    (le_iSup₂ (f := fun (r : ℕ) (_ : 0 < r) => maxRMeanListSize C r lam) 1 one_pos)

/-- Equivalence of `CombEcon` and `CombEconM` for classes of finite-domain codes. -/
theorem isCombEconMeanClass_iff_isCombEconClass {κ : Type*}
    (C : κ → Σ (α : Type*) (β : Type*), Fintype α × Set (α → β)) :
    IsCombEconMeanClass C ↔ IsCombEconClass C := by
  constructor
  · rintro ⟨K, d, hK, h⟩
    refine ⟨K, d, hK, fun i ε hε => ?_⟩
    let _ := (C i).2.2.1
    exact (maxListSize_le_maxMeanListSize _ _).trans (h i ε hε)
  · rintro ⟨K, d, hK, h⟩
    refine ⟨2 * K * (2 : ℝ) ^ d, d + 1, by positivity, fun i ε hε => ?_⟩
    let _ := (C i).2.2.1
    set Λ := codeMaxAgreement (C i).2.2.2
    by_cases hbig : 1 ≤ Λ + ε / 2
    · -- When `Λ + ε / 2 ≥ 1`, `Λ + ε > 1`, so every mean-list is empty.
      have hgt1 : 1 < Λ + ε := by linarith
      have h0 : maxMeanListSize (C i).2.2.2 (Λ + ε) = 0 := by
        rw [← le_zero_iff]
        refine iSup₂_le fun r hr => iSup_le fun f => ?_
        have hemp : meanListAgr (C i).2.2.2 f (Λ + ε) = ∅ := by
          ext w
          simp only [meanListAgr, Set.mem_sep_iff, Set.mem_empty_iff_false, iff_false, not_and]
          intro _
          linarith [meanAgreement_le_one w f]
        simp [hemp]
      rw [h0]
      exact bot_le
    · push Not at hbig
      have hΛ0 : 0 ≤ Λ := codeMaxAgreement_nonneg _
      have h1 := maxMeanListSize_le_div_mul_maxListSize (C i).2.2.2 (lam := Λ + ε / 2)
        (δ := ε / 2) (by linarith) hbig (by linarith) (by positivity) (h i (ε / 2) (by linarith))
      have hrew : Λ + ε / 2 + ε / 2 = Λ + ε := by ring
      rw [hrew] at h1
      refine h1.trans (Nat.cast_le.mpr (Nat.floor_mono ?_))
      have heq : K * (1 / (ε / 2)) ^ d / (ε / 2) = 2 * K * (2 : ℝ) ^ d * (1 / ε) ^ (d + 1) := by
        have h1e : 1 / (ε / 2) = 2 * (1 / ε) := by field_simp [hε.ne']
        rw [h1e, mul_pow, pow_succ]
        field_simp [hε.ne']
      rw [heq]

/-- Agreement with a repeated code equals mean agreement (Remark `rmk:mean-identification`). -/
theorem agreement_repeatCode [Fintype α] {r : ℕ} (w : α → β)
    (f : Fin r → α → β) :
    agreement (fun p : α × Fin r => w p.1) (fun p : α × Fin r => f p.2 p.1) =
      meanAgreement w f := by
  classical
  have hcard : Fintype.card (α × Fin r) = Fintype.card α * r := by
    simp [Fintype.card_prod]
  have hncard : (equalizer (fun p : α × Fin r => w p.1) (fun p : α × Fin r => f p.2 p.1)).ncard =
      ∑ i : Fin r, (equalizer w (f i)).ncard := by
    simp_rw [Set.ncard_eq_toFinset_card']
    rw [← Finset.card_sigma]
    refine Finset.card_bij (fun p _ => ⟨p.2, p.1⟩) ?_ ?_ ?_
    · intro p hp
      refine Finset.mem_sigma.mpr ⟨Finset.mem_univ _, Set.mem_toFinset.mpr ?_⟩
      simpa [mem_equalizer_iff] using Set.mem_toFinset.mp hp
    · intro p₁ _ p₂ _ h
      cases p₁; cases p₂; simp only [Sigma.mk.inj_iff] at h
      exact Prod.ext (eq_of_heq h.2) h.1
    · rintro ⟨i, x⟩ hix
      refine ⟨(x, i), Set.mem_toFinset.mpr ?_, rfl⟩
      have hx := Set.mem_toFinset.mp (Finset.mem_sigma.mp hix).2
      simpa [mem_equalizer_iff] using hx
  simp only [agreement_eq_ncard_div, meanAgreement]
  rw [hncard, hcard, Nat.cast_mul, Nat.cast_sum, Fintype.card_fin, ← div_div, Finset.sum_div]

/-- `maxRMeanListSize C r lam = maxListSize (repeatCode C r) lam` for `r > 0`. -/
theorem maxRMeanListSize_eq_maxListSize_repeatCode [Fintype α] (C : Set (α → β))
    {r : ℕ} (hr : 0 < r) (lam : ℝ) :
    maxRMeanListSize C r lam = maxListSize (repeatCode C r) lam := by
  have hle1 : maxRMeanListSize C r lam ≤ maxListSize (repeatCode C r) lam := by
    refine iSup_le fun f => ?_
    let g : α × Fin r → β := fun p => f p.2 p.1
    refine le_trans ?_ (codeListAgr_encard_le_maxListSize (repeatCode C r) g lam)
    let emb : (α → β) → (α × Fin r → β) := fun w p => w p.1
    have hemb : Function.Injective emb := by
      intro w₁ w₂ heq
      funext x
      exact congrFun heq (x, ⟨0, hr⟩)
    rw [← hemb.encard_image _]
    refine Set.encard_le_encard ?_
    rintro _ ⟨w, ⟨hwC, hagr⟩, rfl⟩
    refine ⟨⟨w, hwC, rfl⟩, ?_⟩
    rwa [agreement_repeatCode]
  have hle2 : maxListSize (repeatCode C r) lam ≤ maxRMeanListSize C r lam := by
    refine iSup_le fun g => ?_
    let f : Fin r → α → β := fun i x => g (x, i)
    refine le_trans ?_
      (le_iSup (fun f' : Fin r → α → β => (meanListAgr C f' lam).encard) f)
    let emb : (α → β) → (α × Fin r → β) := fun w p => w p.1
    have hemb : Function.Injective emb := by
      intro w₁ w₂ heq
      funext x
      exact congrFun heq (x, ⟨0, hr⟩)
    have hsub : codeListAgr (repeatCode C r) g lam ⊆ emb '' meanListAgr C f lam := by
      rintro _ ⟨⟨w, hwC, rfl⟩, hagr⟩
      refine ⟨w, ⟨hwC, ?_⟩, rfl⟩
      rw [← agreement_repeatCode w f]
      exact hagr
    exact (Set.encard_le_encard hsub).trans (Set.encard_image_le emb _)
  exact le_antisymm hle1 hle2

end MeanList

/-! ### Irrelevant Normal Subgroups and Quasivarieties -/

section Irrelevant

variable {G H : Type*} [Group G] [Group H]

omit [Group H] in
/-- Identification of `aHom(G, H)` lists with `aHom(G ⧸ N, H)` mean-lists for any
`(G, H)`-irrelevant normal subgroup `N ◁ G`. -/
theorem agreement_quotient_eq_meanAgreement [Fintype G] (N : Subgroup G) [N.Normal]
    (φ : (G ⧸ N) → H) (f : G → H) :
    let _ := Fintype.ofFinite (G ⧸ N)
    let _ := Fintype.ofFinite N
    let s : (G ⧸ N) → G := Function.surjInv (QuotientGroup.mk'_surjective N)
    agreement (fun g : G => φ (QuotientGroup.mk' N g)) f =
      meanAgreement φ (fun (n : N) (q : G ⧸ N) => f (s q * (n : G))) := by
  classical
  let _ := Fintype.ofFinite (G ⧸ N)
  let _ := Fintype.ofFinite N
  let s : (G ⧸ N) → G := Function.surjInv (QuotientGroup.mk'_surjective N)
  have hs : ∀ q : G ⧸ N, QuotientGroup.mk' N (s q) = q :=
    Function.surjInv_eq (QuotientGroup.mk'_surjective N)
  let e : (G ⧸ N) × N ≃ G :=
    { toFun := fun p => s p.1 * (p.2 : G)
      invFun := fun g =>
        (QuotientGroup.mk' N g, ⟨(s (QuotientGroup.mk' N g))⁻¹ * g, by
          rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_mul, map_inv, hs,
            inv_mul_cancel]⟩)
      left_inv := fun ⟨q, n⟩ => by
        have hmk : QuotientGroup.mk' N (s q * (n : G)) = q := by
          rw [map_mul, hs, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff (n : G)).mpr n.2,
            mul_one]
        apply Prod.ext hmk
        apply Subtype.ext
        dsimp only
        rw [hmk]
        group
      right_inv := fun g => by simp }
  have hcard : Fintype.card G = Fintype.card (G ⧸ N) * Fintype.card N := by
    rw [← Fintype.card_prod]
    exact Fintype.card_congr e.symm
  have hncard : (equalizer (fun g : G => φ (QuotientGroup.mk' N g)) f).ncard =
      ∑ n : N, (equalizer φ (fun q : G ⧸ N => f (s q * (n : G)))).ncard := by
    simp_rw [Set.ncard_eq_toFinset_card']
    rw [← Finset.card_sigma]
    refine Finset.card_bij (fun g _ => ⟨(e.symm g).2, (e.symm g).1⟩) ?_ ?_ ?_
    · intro g hg
      refine Finset.mem_sigma.mpr ⟨Finset.mem_univ _, ?_⟩
      have hEq : φ (QuotientGroup.mk' N g) = f g := by
        simpa [mem_equalizer_iff] using Set.mem_toFinset.mp hg
      have hge : s (e.symm g).1 * ((e.symm g).2 : G) = g := e.apply_symm_apply g
      refine Set.mem_toFinset.mpr ?_
      change φ (e.symm g).1 = f (s (e.symm g).1 * ((e.symm g).2 : G))
      rw [hge]
      exact hEq
    · intro g₁ _ g₂ _ h
      have h1 : (e.symm g₁).2 = (e.symm g₂).2 := (Sigma.mk.inj_iff.mp h).1
      have h2 : (e.symm g₁).1 = (e.symm g₂).1 := eq_of_heq (Sigma.mk.inj_iff.mp h).2
      exact e.symm.injective (Prod.ext h2 h1)
    · rintro ⟨n, q⟩ hnq
      have hq : φ q = f (s q * (n : G)) := by
        simpa [mem_equalizer_iff] using Set.mem_toFinset.mp (Finset.mem_sigma.mp hnq).2
      refine ⟨e (q, n), Set.mem_toFinset.mpr ?_, by simp⟩
      have hmk : QuotientGroup.mk' N (e (q, n)) = q := by
        change QuotientGroup.mk' N (s q * (n : G)) = q
        rw [map_mul, hs, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff (n : G)).mpr n.2,
          mul_one]
      change φ (QuotientGroup.mk' N (e (q, n))) = f (e (q, n))
      rw [hmk]
      exact hq
  dsimp only
  simp only [agreement_eq_ncard_div, meanAgreement]
  rw [hncard, hcard, Nat.cast_mul, Nat.cast_sum, ← div_div, Finset.sum_div]

/-- For any `(G, H)`-irrelevant normal subgroup `N ◁ G`,
`ℓ(aHom(G, H), lam) = ℓ_{|N|,m}(aHom(G ⧸ N, H), lam)`. -/
theorem maxListSize_aHom_eq_maxRMeanListSize_quotient [Fintype G] (N : Subgroup G) [N.Normal]
    (hN : IsIrrelevant G H N) (lam : ℝ) :
    let _ := Fintype.ofFinite (G ⧸ N)
    let _ := Fintype.ofFinite N
    maxListSize (aHomCode G H) lam =
      maxRMeanListSize (aHomCode (G ⧸ N) H) (Fintype.card N) lam := by
  classical
  let _ := Fintype.ofFinite (G ⧸ N)
  let _ := Fintype.ofFinite N
  let s : (G ⧸ N) → G := Function.surjInv (QuotientGroup.mk'_surjective N)
  have hs : ∀ q : G ⧸ N, QuotientGroup.mk' N (s q) = q :=
    Function.surjInv_eq (QuotientGroup.mk'_surjective N)
  -- Bijection between `AffineMonoidHom (G ⧸ N) H` and `AffineMonoidHom G H`.
  let liftAff : AffineMonoidHom (G ⧸ N) H → AffineMonoidHom G H := fun φ =>
    { toFun := fun g => φ (QuotientGroup.mk' N g)
      map_affine' := fun a b c => by
        simp only [map_mul, map_inv]
        exact φ.map_affine _ _ _ }
  have hlift_bij : Function.Bijective liftAff := by
    constructor
    · intro φ₁ φ₂ h
      ext q
      obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N q
      exact DFunLike.congr_fun h g
    · intro ψ
      let ψ₀bar : (G ⧸ N) →* H :=
        QuotientGroup.lift N ψ.baseHom (fun x hx => isIrrelevant_iff.mp hN ψ.baseHom hx)
      refine ⟨AffineMonoidHom.mkOfHom (ψ 1) ψ₀bar, ?_⟩
      ext g
      change (AffineMonoidHom.mkOfHom (ψ 1) ψ₀bar) (QuotientGroup.mk' N g) = ψ g
      rw [AffineMonoidHom.mkOfHom_apply]
      exact ψ.mul_baseHom_apply g
  let eN : Fin (Fintype.card N) ≃ N := (Fintype.equivFin N).symm
  have hle1 : maxListSize (aHomCode G H) lam ≤
      maxRMeanListSize (aHomCode (G ⧸ N) H) (Fintype.card N) lam := by
    refine iSup_le fun f => ?_
    let F : Fin (Fintype.card N) → (G ⧸ N) → H := fun i q => f (s q * (eN i : G))
    refine le_trans ?_
      (le_iSup (fun F' : Fin (Fintype.card N) → (G ⧸ N) → H =>
        (meanListAgr (aHomCode (G ⧸ N) H) F' lam).encard) F)
    let emb : ((G ⧸ N) → H) → (G → H) := fun φ g => φ (QuotientGroup.mk' N g)
    have hemb : Function.Injective emb := by
      intro φ₁ φ₂ h; funext q
      obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N q
      exact congrFun h g
    have hsub : codeListAgr (aHomCode G H) f lam ⊆
        emb '' meanListAgr (aHomCode (G ⧸ N) H) F lam := by
      rintro _ ⟨⟨ψ, rfl⟩, hagr⟩
      obtain ⟨φ, rfl⟩ := hlift_bij.2 ψ
      refine ⟨(φ : (G ⧸ N) → H), ⟨⟨φ, rfl⟩, ?_⟩, rfl⟩
      have hEq := agreement_quotient_eq_meanAgreement N (φ : (G ⧸ N) → H) f
      have hmeanEq : meanAgreement (φ : (G ⧸ N) → H) F =
          meanAgreement (φ : (G ⧸ N) → H) (fun (n : N) (q : G ⧸ N) => f (s q * (n : G))) := by
        unfold meanAgreement
        rw [Fintype.card_fin]
        congr 1
        exact Equiv.sum_comp eN
          (fun n : N => agreement (φ : (G ⧸ N) → H) (fun q => f (s q * (n : G))))
      rw [hmeanEq, ← hEq]
      exact hagr
    exact (Set.encard_le_encard hsub).trans (Set.encard_image_le emb _)
  have hle2 : maxRMeanListSize (aHomCode (G ⧸ N) H) (Fintype.card N) lam ≤
      maxListSize (aHomCode G H) lam := by
    refine iSup_le fun F => ?_
    let f : G → H := fun g =>
      F (eN.symm ⟨(s (QuotientGroup.mk' N g))⁻¹ * g, by
        rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_mul, map_inv, hs,
          inv_mul_cancel]⟩) (QuotientGroup.mk' N g)
    refine le_trans ?_ (codeListAgr_encard_le_maxListSize (aHomCode G H) f lam)
    let emb : ((G ⧸ N) → H) → (G → H) := fun φ g => φ (QuotientGroup.mk' N g)
    have hemb : Function.Injective emb := by
      intro φ₁ φ₂ h; funext q
      obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N q
      exact congrFun h g
    rw [← hemb.encard_image _]
    refine Set.encard_le_encard ?_
    rintro _ ⟨_, ⟨⟨φ, rfl⟩, hagr⟩, rfl⟩
    refine ⟨⟨liftAff φ, rfl⟩, ?_⟩
    have hEq := agreement_quotient_eq_meanAgreement N (φ : (G ⧸ N) → H) f
    have hf_recover : (fun (n : N) (q : G ⧸ N) => f (s q * (n : G))) =
        fun (n : N) (q : G ⧸ N) => F (eN.symm n) q := by
      funext n q
      have hmk : QuotientGroup.mk' N (s q * (n : G)) = q := by
        rw [map_mul, hs, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff (n : G)).mpr n.2,
          mul_one]
      simp only [f, hmk]
      congr 1
      apply congrArg eN.symm
      apply Subtype.ext
      dsimp only
      group
    have hmeanEq : meanAgreement (φ : (G ⧸ N) → H) (fun (n : N) (q : G ⧸ N) => f (s q * (n : G))) =
        meanAgreement (φ : (G ⧸ N) → H) F := by
      rw [hf_recover]
      unfold meanAgreement
      rw [Fintype.card_fin]
      congr 1
      exact Equiv.sum_comp eN.symm (fun i => agreement (φ : (G ⧸ N) → H) (F i))
    change lam ≤ agreement (fun g => φ (QuotientGroup.mk' N g)) f
    rw [hEq, hmeanEq]
    exact hagr
  exact le_antisymm hle1 hle2

/-- Irrelevant normal subgroup lemma (Lemma `lemma:irr-normal-subgroup`):
for any `(G, H)`-irrelevant normal subgroup `N ◁ G` and `ε > 0`,
`ℓ(aHom(G, H), Λ_{G, H} + ε) ≤ (2 / ε) ℓ(aHom(G ⧸ N, H), Λ_{G, H} + ε / 2)`. -/
theorem irrelevant_normal_subgroup_bound [Fintype G] (N : Subgroup G) [N.Normal]
    (hN : IsIrrelevant G H N) {ε : ℝ} (hε : 0 < ε) {M : ℝ} (hM : 0 ≤ M)
    (hlist : let _ := Fintype.ofFinite (G ⧸ N)
      maxListSize (aHomCode (G ⧸ N) H) (homMaxAgreement G H + ε / 2) ≤ (Nat.floor M : ℕ∞)) :
    maxListSize (aHomCode G H) (homMaxAgreement G H + ε) ≤
      (Nat.floor (M / (ε / 2)) : ℕ∞) := by
  let _ := Fintype.ofFinite (G ⧸ N)
  let _ := Fintype.ofFinite N
  by_cases hbig : 1 ≤ homMaxAgreement G H + ε / 2
  · rw [maxListSize_eq_zero_of_one_lt _ (by linarith)]
    exact bot_le
  · push Not at hbig
    have hΛ0 : 0 ≤ homMaxAgreement G H := codeMaxAgreement_nonneg _
    have h1 := maxListSize_aHom_eq_maxRMeanListSize_quotient N hN (homMaxAgreement G H + ε)
    have hNpos : 0 < Fintype.card N := Fintype.card_pos
    have h2 : maxRMeanListSize (aHomCode (G ⧸ N) H) (Fintype.card N) (homMaxAgreement G H + ε) ≤
        maxMeanListSize (aHomCode (G ⧸ N) H) (homMaxAgreement G H + ε) :=
      le_iSup₂ (f := fun (r : ℕ) (_ : 0 < r) =>
        maxRMeanListSize (aHomCode (G ⧸ N) H) r (homMaxAgreement G H + ε))
        (Fintype.card N) hNpos
    have h3 := maxMeanListSize_le_div_mul_maxListSize (aHomCode (G ⧸ N) H)
      (lam := homMaxAgreement G H + ε / 2) (δ := ε / 2) (by linarith) hbig (by linarith) hM hlist
    have hrew : homMaxAgreement G H + ε / 2 + ε / 2 = homMaxAgreement G H + ε := by ring
    rw [hrew] at h3
    exact h1.le.trans (h2.trans h3)

end Irrelevant

/-- A predicate `Q` on finite groups (in a fixed universe `u`) is a quasivariety if it is closed
under subgroups and finite direct products (equivalently, subdirect products of a single member). -/
@[expose]
def IsQuasivariety.{u} (Q : ∀ (A : Type u) [Group A] [Fintype A], Prop) : Prop :=
  (∀ (A : Type u) [Group A] [Fintype A] (B : Type u) [Group B] [Fintype B]
      (f : A →* B), Function.Injective f → Q B → Q A) ∧
  (∀ (A : Type u) [Group A] [Fintype A] (ι : Type u) [Fintype ι] [DecidableEq ι],
      Q A → Q (ι → A))

/-- Domain relaxation for quasivarieties:
if `Q` is a quasivariety of finite groups and `aHom(G, H)` is `CombEcon` for all `G, H ∈ Q`, then
`aHom(G, H)` is `CombEcon` for every finite group `G` and every `H ∈ Q`. -/
theorem combEcon_of_quasivariety.{u}
    {Q : ∀ (A : Type u) [Group A] [Fintype A], Prop} (hQ : IsQuasivariety Q)
    {K : ℝ} {d : ℕ} (hK : 0 < K)
    (hComb : ∀ (A : Type u) [Group A] [Fintype A] (B : Type u) [Group B] [Fintype B],
      Q A → Q B → ∀ ε : ℝ, 0 < ε →
        maxListSize (aHomCode A B) (homMaxAgreement A B + ε) ≤
          (Nat.floor (K * (1 / ε) ^ d) : ℕ∞))
    (G : Type u) [Group G] [Fintype G] (H : Type u) [Group H] [Fintype H] (hH : Q H)
    {ε : ℝ} (hε : 0 < ε) :
    maxListSize (aHomCode G H) (homMaxAgreement G H + ε) ≤
      (Nat.floor (2 * K * (2 : ℝ) ^ d * (1 / ε) ^ (d + 1)) : ℕ∞) := by
  classical
  let N := irrelevantKernel G H
  let _ : Fintype (G ⧸ N) := Fintype.ofFinite (G ⧸ N)
  have hQ_quot : Q (G ⧸ N) := by
    let ψ : G →* ((G →* H) → H) :=
      { toFun := fun g φ => φ g
        map_one' := by funext φ; exact map_one φ
        map_mul' := fun a b => by funext φ; exact map_mul φ a b }
    have hker : ψ.ker = N := by
      ext g; simp [ψ, N, MonoidHom.mem_ker, funext_iff, mem_irrelevantKernel_iff]
    let e : (G ⧸ N) ≃* ψ.range :=
      (QuotientGroup.quotientMulEquivOfEq hker.symm).trans (QuotientGroup.quotientKerEquivRange ψ)
    let inj : (G ⧸ N) →* ((G →* H) → H) := ψ.range.subtype.comp e.toMonoidHom
    have hinj : Function.Injective inj := Subtype.val_injective.comp e.injective
    have : Finite (G →* H) :=
      Finite.of_injective (fun φ : G →* H => (φ : G → H)) DFunLike.coe_injective
    have : Fintype (G →* H) := Fintype.ofFinite (G →* H)
    exact hQ.1 (G ⧸ N) ((G →* H) → H) inj hinj (hQ.2 H (G →* H) hH)
  have hlist := hComb (G ⧸ N) H hQ_quot hH (ε / 2) (by linarith)
  have hΛ : homMaxAgreement (G ⧸ N) H = homMaxAgreement G H :=
    homMaxAgreement_quotient_eq N le_rfl
  rw [hΛ] at hlist
  have h1 := irrelevant_normal_subgroup_bound N le_rfl hε (by positivity) hlist
  refine h1.trans (Nat.cast_le.mpr (Nat.floor_mono ?_))
  have h1e : 1 / (ε / 2) = 2 * (1 / ε) := by field_simp [hε.ne']
  rw [h1e, mul_pow, pow_succ]
  field_simp [hε.ne']
  ring_nf
  exact le_rfl

/-! ### `Hom` versus `aHom` -/

section HomVsAHom

variable {G H : Type*} [Group G] [Group H]

/-- Left-translated received word `f^a(g) = f(a)⁻¹ * f(a * g)`. -/
@[expose]
def translateReceived (f : G → H) (a : G) : G → H :=
  fun g => (f a)⁻¹ * f (a * g)

theorem translateReceived_apply (f : G → H) (a g : G) :
    translateReceived f a g = (f a)⁻¹ * f (a * g) :=
  rfl

/-- If `f a = φ a`, then `agr(f, φ) = agr(f^a, φ.baseHom)`. -/
theorem agreement_translateReceived_eq [Fintype G] {f : G → H} {φ : AffineMonoidHom G H}
    {a : G} (ha : f a = φ a) :
    agreement (φ.baseHom : G → H) (translateReceived f a) = agreement (φ : G → H) f := by
  rw [agreement_eq_ncard_div, agreement_eq_ncard_div]
  congr 1
  have himg : equalizer (φ : G → H) f =
      (fun x => a * x) '' equalizer (φ.baseHom : G → H) (translateReceived f a) := by
    ext x
    simp only [mem_equalizer_iff, Set.mem_image]
    constructor
    · intro hx
      refine ⟨a⁻¹ * x, ?_, mul_inv_cancel_left a x⟩
      change φ.baseHom (a⁻¹ * x) = (f a)⁻¹ * f (a * (a⁻¹ * x))
      rw [mul_inv_cancel_left, ← φ.baseHom_eq_of_eq a (a⁻¹ * x), mul_inv_cancel_left, ha, hx]
    · rintro ⟨g, hg, rfl⟩
      change φ.baseHom g = (f a)⁻¹ * f (a * g) at hg
      rw [φ.eq_mul_baseHom a (a * g), inv_mul_cancel_left, hg, ha, mul_inv_cancel_left]
  rw [himg, Set.ncard_image_of_injective _ (mul_right_injective a)]

/-- Concentration of `aHom` lists, part (i) (Lemma `lemma:mean-central-aHom-relationship`(i)):
for `lam > 0`, `ℓ(aHom(G, H), lam) ≤ (1 / lam) * ℓ(Hom(G, H), lam)`. -/
theorem maxListSize_aHom_le_div_mul_hom [Fintype G] {lam : ℝ} (hlam : 0 < lam) {M : ℝ} (hM : 0 ≤ M)
    (hlist : maxListSize (homCode G H) lam ≤ (Nat.floor M : ℕ∞)) :
    maxListSize (aHomCode G H) lam ≤ (Nat.floor (M / lam) : ℕ∞) := by
  classical
  rw [maxListSize_le_floor_iff _ _ (by positivity)]
  intro f B hB
  -- Choose `AffineMonoidHom` representatives for `B`.
  have hBaff : ∀ w ∈ B, ∃ φ : AffineMonoidHom G H, (φ : G → H) = w :=
    fun w hw => (hB hw).1
  let E : G → B → Prop := fun a w => f a = w.1 a
  have hV : ∀ a : G, ((Finset.univ.filter (fun w : B => E a w)).card : ℝ) ≤ M := by
    intro a
    let T : Finset (G → H) :=
      (B.filter (fun w => f a = w a)).image (fun w =>
        if h : w ∈ B then ((hBaff w h).choose.baseHom : G → H) else fun _ => 1)
    have hinj : Set.InjOn (fun w =>
        if h : w ∈ B then ((hBaff w h).choose.baseHom : G → H) else fun _ => 1)
        (B.filter (fun w => f a = w a) : Set (G → H)) := by
      intro w₁ hw₁ w₂ hw₂ heq
      have h1 := Finset.mem_filter.mp hw₁
      have h2 := Finset.mem_filter.mp hw₂
      simp only [h1.1, h2.1, ↓reduceDIte] at heq
      set φ₁ := (hBaff w₁ h1.1).choose
      set φ₂ := (hBaff w₂ h2.1).choose
      have hφ₁ : (φ₁ : G → H) = w₁ := (hBaff w₁ h1.1).choose_spec
      have hφ₂ : (φ₂ : G → H) = w₂ := (hBaff w₂ h2.1).choose_spec
      rw [← hφ₁, ← hφ₂]
      funext x
      have hbase : φ₁.baseHom = φ₂.baseHom := DFunLike.coe_injective heq
      rw [φ₁.eq_mul_baseHom a x, φ₂.eq_mul_baseHom a x, hbase]
      have ha1 : φ₁ a = f a := (congrFun hφ₁ a).trans h1.2.symm
      have ha2 : φ₂ a = f a := (congrFun hφ₂ a).trans h2.2.symm
      rw [ha1, ha2]
    have hcard : (Finset.univ.filter (fun w : B => E a w)).card = T.card := by
      rw [Finset.card_image_of_injOn hinj]
      refine Finset.card_bij (fun w _ => w.1) ?_ ?_ ?_
      · intro w hw; exact Finset.mem_filter.mpr ⟨w.2, (Finset.mem_filter.mp hw).2⟩
      · intro w₁ _ w₂ _ h; exact Subtype.ext h
      · intro w hw
        exact ⟨⟨w, (Finset.mem_filter.mp hw).1⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hw).2⟩, rfl⟩
    rw [hcard]
    have hTsub : (T : Set (G → H)) ⊆ codeListAgr (homCode G H) (translateReceived f a) lam := by
      rintro _ hmem
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hmem)
      have hw' := Finset.mem_filter.mp hw
      simp only [hw'.1, ↓reduceDIte]
      set φ := (hBaff w hw'.1).choose
      have hφ : (φ : G → H) = w := (hBaff w hw'.1).choose_spec
      refine ⟨⟨φ.baseHom, rfl⟩, ?_⟩
      have ha : f a = φ a := hw'.2.trans (congrFun hφ.symm a)
      rw [agreement_translateReceived_eq ha, hφ]
      exact (hB hw'.1).2
    exact (maxListSize_le_floor_iff _ _ hM).mp hlist (translateReceived f a) T hTsub
  have hW : ∀ w : B, lam * (Fintype.card G : ℝ) ≤
      ((Finset.univ.filter (fun a : G => E a w)).card : ℝ) := by
    intro w
    have hagr : lam ≤ agreement w.1 f := (hB w.2).2
    have hGpos : (0 : ℝ) < Fintype.card G := Nat.cast_pos.mpr Fintype.card_pos
    have hdens : agreement w.1 f =
        ((Finset.univ.filter (fun a : G => E a w)).card : ℝ) / (Fintype.card G : ℝ) := by
      rw [agreement_comm, agreement_eq_density_equalizer, ← density_coe]
      congr 1; ext a; simp [E, mem_equalizer_iff]
    rw [hdens] at hagr
    exact (le_div_iff₀ hGpos).mp hagr
  have h := bipartite_double_counting E hlam hV hW
  simpa only [Fintype.card_coe] using h

end HomVsAHom

end CslibFrontier.HomomorphismCode
