/-
Copyright (c) 2026 The FormalPapers contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.FineGrained
public import CslibFrontier.Computability.PolyTime.CSP.ToCNF
public import CslibFrontier.Logics.Propositional.CSP

import CslibFrontier.Computability.Complexity.FineGrained.Bounds
import CslibFrontier.Computability.Complexity.FineGrained.Reduction
import CslibFrontier.Computability.Complexity.Problems.SAT.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.OCombinators
import CslibFrontier.Computability.PolyTime.CSP.Vars

/-!
# Base-Exponential Parameterized Time Bounds and Lampis's $q$-CSP-$B$ Reduction

This module introduces parameterized base-exponential running-time bounds
`Cslib.Complexity.DecidableInBaseExpTime` ($\mathcal{O}^*(b^{\mu(x)})$) on multi-tape Turing
machines, proves closure under monotonicity, finite intersections, and additive or linear
polynomial-time reductions, and establishes Lampis's fine-grained block-grouping reduction
from `KSAT k` to explicit-table $q$-CSP-$B$ (`Cslib.Complexity.QCSPB q B`).

## Main definitions

* `Cslib.Complexity.baseExpFactor`, `Cslib.Complexity.DecidableInBaseExpTime`: parameterized time
  $\mathcal{O}(\max(1, \max(0, b)^{\mu(x)}) \cdot (|x| + 1)^e)$.
* `Cslib.Complexity.finTableSem`, `Cslib.Complexity.QCSPB`, `Cslib.Complexity.encTableCSP`:
  explicit allowed-tuple table CSP over domain `Fin B` and its framed binary encoding.
* `Cslib.Complexity.cnfToQCSP`: Lampis's block-grouping polynomial-time compiler from `k`-CNF to
  `(k * p)`-CSP-`B`.

## Main results

* `Cslib.Complexity.DecidableInBaseExpTime.mono`,
  `Cslib.Complexity.DecidableInBaseExpTime.inter`,
  `Cslib.Complexity.DecidableInBaseExpTime.iInter_fin`
* `Cslib.Complexity.DecidableInBaseExpTime.of_addReduction`,
  `Cslib.Complexity.DecidableInBaseExpTime.of_linearReduction`
* `Cslib.Complexity.exists_ksat_to_qcspb_reduction`
* `Cslib.Complexity.SETH.exists_not_decidableInBaseExpTime_qcspb`
-/

public section

namespace Cslib.Complexity

open Cslib.Logic.PL Turing.MultiTapeTM

section BaseExpTime

variable {α β : Type*} {enc : α ↪ List Bool} {A A₁ A₂ : Set α} {μ μ' : α → ℕ}

/-- Envelope factor `max 1 ((max 0 b) ^ n)` guarding nonpositive or sub-unit bases so that
$\mathcal{O}^*(b^{\mu(x)})$ agrees with $b^{\mu(x)} \cdot \mathrm{poly}(|x|)$ for all $b \ge 1$ and
degrades cleanly to polynomial time $\mathrm{poly}(|x|)$ when $b \le 1$. -/
@[expose]
noncomputable def baseExpFactor (b : ℝ) (n : ℕ) : ℝ :=
  max 1 ((max 0 b) ^ n)

theorem one_le_baseExpFactor (b : ℝ) (n : ℕ) : 1 ≤ baseExpFactor b n :=
  le_max_left 1 _

@[simp]
theorem baseExpFactor_zero (b : ℝ) : baseExpFactor b 0 = 1 := by
  simp [baseExpFactor]

theorem baseExpFactor_nonneg (b : ℝ) (n : ℕ) : 0 ≤ baseExpFactor b n :=
  zero_le_one.trans (one_le_baseExpFactor b n)

theorem baseExpFactor_eq_pow_of_one_le {b : ℝ} (hb : 1 ≤ b) (n : ℕ) :
    baseExpFactor b n = b ^ n := by
  have hb0 : 0 ≤ b := zero_le_one.trans hb
  rw [baseExpFactor, max_eq_right hb0, max_eq_right (one_le_pow₀ hb)]

theorem baseExpFactor_eq_one_of_le_one {b : ℝ} (hb : b ≤ 1) (n : ℕ) :
    baseExpFactor b n = 1 := by
  have hle : (max 0 b) ^ n ≤ 1 := pow_le_one₀ (le_max_left 0 b) (max_le zero_le_one hb)
  exact max_eq_left hle

theorem baseExpFactor_mono {b₁ b₂ : ℝ} (hb : b₁ ≤ b₂) (n : ℕ) :
    baseExpFactor b₁ n ≤ baseExpFactor b₂ n := by
  unfold baseExpFactor
  exact max_le_max_left 1
    (pow_le_pow_left₀ (le_max_left 0 b₁) (max_le_max_left 0 hb) n)

/-- `A` is decidable in parameterized base-exponential time $\mathcal{O}^*(b^{\mu(a)})$ if some
multi-tape Turing machine decides `A` within time
$\mathcal{O}(\max(1, \max(0, b)^{\mu(a)}) \cdot (|\mathrm{enc}(a)| + 1)^e)$. -/
@[expose]
def DecidableInBaseExpTime (A : Set α) (enc : α ↪ List Bool) (μ : α → ℕ) (b : ℝ) : Prop :=
  ∃ e : ℕ, DecidableInTimeO A enc fun a ↦ baseExpFactor b (μ a) * ((enc a).length + 1) ^ e

/-- For `1 ≤ b`, `DecidableInBaseExpTime A enc μ b` unfolds to time
`O(b ^ μ a * ((enc a).length + 1) ^ e)`. -/
theorem decidableInBaseExpTime_iff_of_one_le {b : ℝ} (hb : 1 ≤ b) :
    DecidableInBaseExpTime A enc μ b ↔
      ∃ e : ℕ, DecidableInTimeO A enc fun a ↦ b ^ μ a * ((enc a).length + 1) ^ e := by
  simp only [DecidableInBaseExpTime, baseExpFactor_eq_pow_of_one_le hb]

/-- For `b ≤ 1`, `DecidableInBaseExpTime A enc μ b` coincides with polynomial time
`DecidableInExpTime A enc μ 0`. -/
theorem decidableInBaseExpTime_iff_of_le_one {b : ℝ} (hb : b ≤ 1) :
    DecidableInBaseExpTime A enc μ b ↔ DecidableInExpTime A enc μ 0 := by
  simp only [DecidableInBaseExpTime, DecidableInExpTime, baseExpFactor_eq_one_of_le_one hb,
    zero_mul, Real.rpow_zero]

/-- For `1 ≤ b`, `DecidableInBaseExpTime A enc μ b` is equivalent to
`DecidableInExpTime A enc μ (Real.log b / Real.log 2)`. -/
theorem decidableInBaseExpTime_iff_decidableInExpTime_logb {b : ℝ} (hb : 1 ≤ b) :
    DecidableInBaseExpTime A enc μ b ↔
      DecidableInExpTime A enc μ (Real.log b / Real.log 2) := by
  rw [decidableInBaseExpTime_iff_of_one_le hb, DecidableInExpTime]
  have hlog2_ne : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  have hpow : ∀ n : ℕ, (2 : ℝ) ^ ((Real.log b / Real.log 2) * n) = b ^ n := by
    intro n
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hmul : Real.log 2 * (Real.log b / Real.log 2 * (n : ℝ)) = Real.log b * n := by
      field_simp [hlog2_ne]
    rw [hmul, ← Real.rpow_def_of_pos (zero_lt_one.trans_le hb), Real.rpow_natCast]
  simp only [hpow]

/-- Monotonicity of `DecidableInBaseExpTime` in the exponential base `b`. -/
theorem DecidableInBaseExpTime.mono {b₁ b₂ : ℝ} (h : DecidableInBaseExpTime A enc μ b₁)
    (hb : b₁ ≤ b₂) : DecidableInBaseExpTime A enc μ b₂ := by
  obtain ⟨e, hO⟩ := h
  refine ⟨e, hO.mono 1 (fun a ↦ ?_)
    fun a ↦ mul_nonneg (baseExpFactor_nonneg b₂ (μ a)) (by positivity)⟩
  have hm := mul_le_mul_of_nonneg_right (baseExpFactor_mono hb (μ a))
    (by positivity : (0 : ℝ) ≤ ((enc a).length + 1) ^ e)
  push_cast
  linarith

/-- Monotonicity of `DecidableInBaseExpTime` under an additive parameter bound `μ a ≤ μ' a + c`. -/
theorem DecidableInBaseExpTime.mono_add_measure {c : ℕ} (hμ : ∀ a, μ a ≤ μ' a + c) {b : ℝ}
    (h : DecidableInBaseExpTime A enc μ b) : DecidableInBaseExpTime A enc μ' b := by
  by_cases hb : 1 ≤ b
  · rw [decidableInBaseExpTime_iff_of_one_le hb] at h ⊢
    obtain ⟨e, hO⟩ := h
    let K : ℕ := ⌈b ^ c⌉₊
    refine ⟨e, hO.mono K (fun a ↦ ?_)
      fun a ↦ mul_nonneg (pow_nonneg (zero_le_one.trans hb) _) (by positivity)⟩
    have hpow : b ^ μ a ≤ (K : ℝ) * b ^ μ' a := by
      calc b ^ μ a ≤ b ^ (μ' a + c) := pow_le_pow_right₀ hb (hμ a)
        _ = b ^ c * b ^ μ' a := by rw [pow_add, mul_comm]
        _ ≤ (K : ℝ) * b ^ μ' a :=
          mul_le_mul_of_nonneg_right (Nat.le_ceil _) (pow_nonneg (zero_le_one.trans hb) _)
    have hm := mul_le_mul_of_nonneg_right hpow
      (by positivity : (0 : ℝ) ≤ ((enc a).length + 1) ^ e)
    nlinarith [(Nat.cast_nonneg K : (0 : ℝ) ≤ K)]
  · push Not at hb
    rw [decidableInBaseExpTime_iff_of_le_one hb.le] at h ⊢
    simp only [DecidableInExpTime, zero_mul] at h ⊢
    exact h

end BaseExpTime

section MachineCombinators

variable {α β : Type} {enc : α ↪ List Bool} {encA : α ↪ List Bool} {encB : β ↪ List Bool}
  {A A₁ A₂ : Set α} {B : Set β} {μ μA : α → ℕ} {μB : β → ℕ}

/-- Every polynomial-time decidable set belongs to `DecidableInBaseExpTime` for every base `b`. -/
theorem DecidableInBaseExpTime.of_computableInPolyTime {p : α → Bool}
    (hp : ComputableInPolyTime p enc encBool) (hA : ∀ a, a ∈ A ↔ p a = true) (μ : α → ℕ)
    (b : ℝ) : DecidableInBaseExpTime A enc μ b := by
  by_cases hb : b ≤ 1
  · exact (decidableInBaseExpTime_iff_of_le_one hb).mpr
      (DecidableInExpTime.of_computableInPolyTime hp hA)
  · push Not at hb
    exact ((decidableInBaseExpTime_iff_of_le_one le_rfl).mpr
      (DecidableInExpTime.of_computableInPolyTime hp hA)).mono hb.le

/-- Construct `DecidableInBaseExpTime` directly from a `ComputableInO` Boolean decider. -/
theorem DecidableInBaseExpTime.of_computableInO {b : ℝ} {g : α → Bool} {t S : α → ℕ}
    (hg : ComputableInO g enc encBool t S) (hA : ∀ a, a ∈ A ↔ g a = true)
    (c e : ℕ) (ht : ∀ a, (t a : ℝ) ≤ c * (baseExpFactor b (μ a) * ((enc a).length + 1) ^ e)) :
    DecidableInBaseExpTime A enc μ b :=
  ⟨e, (DecidableInTimeO.of_computableInO hg hA ht).mono c
    (fun _ ↦ le_add_of_nonneg_right (Nat.cast_nonneg c))
    fun a ↦ mul_nonneg (baseExpFactor_nonneg b (μ a)) (by positivity)⟩

/-- Binary intersection preserves `DecidableInBaseExpTime` at the same base `b`. -/
theorem DecidableInBaseExpTime.inter {b : ℝ}
    (h₁ : DecidableInBaseExpTime A₁ enc μ b) (h₂ : DecidableInBaseExpTime A₂ enc μ b) :
    DecidableInBaseExpTime (A₁ ∩ A₂) enc μ b := by
  obtain ⟨e₁, hO₁⟩ := h₁
  obtain ⟨e₂, hO₂⟩ := h₂
  obtain ⟨g₁, t₁, c₁, hg₁, hgA₁, ht₁⟩ := hO₁.exists_computableInO
  obtain ⟨g₂, t₂, c₂, hg₂, hgA₂, ht₂⟩ := hO₂.exists_computableInO
  obtain ⟨dAnd, _, hAnd⟩ := ComputableInPolyTime.bool_and.exists_degree
  have hcomb := hAnd.inO.comp (hg₁.prod hg₂)
  let e : ℕ := max e₁ e₂
  let M : ℕ := 5 ^ dAnd + 1
  have hcomb' : ComputableInO (fun a ↦ g₁ a && g₂ a) enc encBool
      (fun a ↦ t₁ a + t₂ a + 1) (fun a ↦ t₁ a + t₂ a + 1) := by
    refine (hcomb.mono M (fun a ↦ ?_) (fun a ↦ ?_)).of_enc_eq fun _ ↦ rfl <;>
    · simp only [show ∀ p : Bool × Bool, (encPair encBool encBool p).length = 4 from
        fun _ ↦ by simp]
      dsimp [M]
      calc t₁ a + t₂ a + 5 ^ dAnd
          ≤ (t₁ a + t₂ a + 1) + 5 ^ dAnd * 1 := by omega
        _ ≤ 1 * (t₁ a + t₂ a + 1) + 5 ^ dAnd * (t₁ a + t₂ a + 1) :=
            Nat.add_le_add (by omega) (Nat.mul_le_mul_left _ (by omega))
        _ ≤ (5 ^ dAnd + 1) * (t₁ a + t₂ a + 1) + (5 ^ dAnd + 1) := by ring_nf; omega
  refine DecidableInBaseExpTime.of_computableInO hcomb'
    (fun a ↦ by simp [Set.mem_inter_iff, hgA₁, hgA₂])
    (2 * c₁ + 2 * c₂ + 1) e fun a ↦ ?_
  have hF1 : 1 ≤ baseExpFactor b (μ a) * ((enc a).length + 1) ^ e₁ :=
    one_le_mul_of_one_le_of_one_le (one_le_baseExpFactor b (μ a))
      (one_le_pow₀ (by linarith [(Nat.cast_nonneg (enc a).length : (0 : ℝ) ≤ _)]))
  have hF2 : 1 ≤ baseExpFactor b (μ a) * ((enc a).length + 1) ^ e₂ :=
    one_le_mul_of_one_le_of_one_le (one_le_baseExpFactor b (μ a))
      (one_le_pow₀ (by linarith [(Nat.cast_nonneg (enc a).length : (0 : ℝ) ≤ _)]))
  have hFe : 1 ≤ baseExpFactor b (μ a) * ((enc a).length + 1) ^ e :=
    one_le_mul_of_one_le_of_one_le (one_le_baseExpFactor b (μ a))
      (one_le_pow₀ (by linarith [(Nat.cast_nonneg (enc a).length : (0 : ℝ) ≤ _)]))
  have hm1 : baseExpFactor b (μ a) * ((enc a).length + 1) ^ e₁ ≤
      baseExpFactor b (μ a) * ((enc a).length + 1) ^ e :=
    mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ (by linarith [(Nat.cast_nonneg (enc a).length : (0 : ℝ) ≤ _)])
        (le_max_left e₁ e₂))
      (baseExpFactor_nonneg b (μ a))
  have hm2 : baseExpFactor b (μ a) * ((enc a).length + 1) ^ e₂ ≤
      baseExpFactor b (μ a) * ((enc a).length + 1) ^ e :=
    mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ (by linarith [(Nat.cast_nonneg (enc a).length : (0 : ℝ) ≤ _)])
        (le_max_right e₁ e₂))
      (baseExpFactor_nonneg b (μ a))
  have hb1 : (t₁ a : ℝ) ≤ 2 * c₁ * (baseExpFactor b (μ a) * ((enc a).length + 1) ^ e) :=
    le_two_mul_mul_of_le_mul_add (ht₁ a) hm1 hFe
  have hb2 : (t₂ a : ℝ) ≤ 2 * c₂ * (baseExpFactor b (μ a) * ((enc a).length + 1) ^ e) :=
    le_two_mul_mul_of_le_mul_add (ht₂ a) hm2 hFe
  push_cast
  linarith

/-- Finite indexed intersection over `Fin m` preserves `DecidableInBaseExpTime` under any common
upper bound `B` on the component bases `b i`. -/
theorem DecidableInBaseExpTime.iInter_fin :
    ∀ {m : ℕ} {F : Fin m → Set α} {b : Fin m → ℝ} {B : ℝ},
      (∀ i, b i ≤ B) →
      (∀ i, DecidableInBaseExpTime (F i) enc μ (b i)) →
      DecidableInBaseExpTime (⋂ i, F i) enc μ B
  | 0, F, _, B, _, _ => by
      have huniv : (⋂ i : Fin 0, F i) = Set.univ := by simp
      rw [huniv]
      exact DecidableInBaseExpTime.of_computableInPolyTime (ComputableInPolyTime.const true)
        (fun _ ↦ by simp) μ B
  | m + 1, F, b, B, hbB, hdec => by
      have heq : (⋂ i : Fin (m + 1), F i) = F 0 ∩ ⋂ i : Fin m, F i.succ := by
        ext a
        simp [Fin.forall_fin_succ]
      rw [heq]
      exact ((hdec 0).mono (hbB 0)).inter
        (DecidableInBaseExpTime.iInter_fin (fun i ↦ hbB i.succ) (fun i ↦ hdec i.succ))

/-- **Additive-parameter reduction transfer**: if `f` reduces `A` to `B` in polynomial time with
`μB (f a) ≤ μA a + c` for a constant `c`, then `DecidableInBaseExpTime B encB μB b` transfers to
`DecidableInBaseExpTime A encA μA b` with the exact same base `b`. -/
theorem DecidableInBaseExpTime.of_addReduction {f : α → β}
    (hf : ComputableInPolyTime f encA encB) (hfA : ∀ a, a ∈ A ↔ f a ∈ B) {c : ℕ}
    (hμ : ∀ a, μB (f a) ≤ μA a + c) {b : ℝ}
    (h : DecidableInBaseExpTime B encB μB b) : DecidableInBaseExpTime A encA μA b := by
  by_cases hb : 1 ≤ b
  · rw [decidableInBaseExpTime_iff_decidableInExpTime_logb hb] at h ⊢
    obtain ⟨e, hO⟩ := h
    obtain ⟨g, t, k, hg, hgB, ht⟩ := hO.exists_computableInO
    obtain ⟨d, _, hfd⟩ := hf.exists_degree
    obtain ⟨l, hl⟩ := hfd.inO.length_le_time
    let δ : ℝ := Real.log b / Real.log 2
    have hδ : 0 ≤ δ :=
      div_nonneg (Real.log_nonneg hb) (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
    refine DecidableInExpTime.of_computableInO (hg.comp hfd.inO)
      (fun a ↦ (hfA a).trans (hgB (f a)))
      ⌈(1 + k * 2 ^ (δ * c) * (2 * l + 1) ^ e + k : ℝ)⌉₊ (d * (e + 1)) fun a ↦ ?_
    have hexp : (2 : ℝ) ^ (δ * μB (f a)) ≤ 2 ^ (δ * c) * 2 ^ (δ * μA a) := by
      rw [← Real.rpow_add (by norm_num)]
      refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
      have hμ' : (μB (f a) : ℝ) ≤ μA a + c := by exact_mod_cast hμ a
      nlinarith
    have key := reduction_add_time_le (P := ((encA a).length + 1 : ℝ) ^ d)
      (C := (2 : ℝ) ^ (δ * c))
      (one_le_pow₀ (le_add_of_nonneg_left (Nat.cast_nonneg _)))
      (Real.one_le_rpow (by norm_num) (by positivity)) (by positivity)
      (by exact_mod_cast hl a) hexp (ht (f a))
    push_cast
    rw [pow_mul]
    exact key.trans (mul_le_mul_of_nonneg_right (Nat.le_ceil _) (by positivity))
  · push Not at hb
    rw [decidableInBaseExpTime_iff_of_le_one hb.le] at h ⊢
    have hlin : ∀ a, μB (f a) ≤ (c + 1) * μA a + (c + 1) := fun a ↦ by
      have := hμ a
      nlinarith
    simpa using h.of_reduction hf hfA hlin le_rfl

/-- **Linear-parameter reduction transfer**: if `f` reduces `A` to `B` in polynomial time with
`t * μB (f a) ≤ p * μA a + c` (`1 ≤ t`, `1 ≤ b`), then `DecidableInBaseExpTime B encB μB b` implies
`DecidableInExpTime A encA μA ((p / t) * (Real.log b / Real.log 2))`. -/
theorem DecidableInBaseExpTime.of_linearReduction {f : α → β}
    (hf : ComputableInPolyTime f encA encB) (hfA : ∀ a, a ∈ A ↔ f a ∈ B)
    {p t c : ℕ} (ht : 0 < t) (hμ : ∀ a, t * μB (f a) ≤ p * μA a + c)
    {b : ℝ} (hb : 1 ≤ b) (h : DecidableInBaseExpTime B encB μB b) :
    DecidableInExpTime A encA μA (((p : ℝ) / t) * (Real.log b / Real.log 2)) := by
  rw [decidableInBaseExpTime_iff_decidableInExpTime_logb hb] at h
  obtain ⟨e, hO⟩ := h
  obtain ⟨g, tm, k, hg, hgB, htm⟩ := hO.exists_computableInO
  obtain ⟨d, _, hfd⟩ := hf.exists_degree
  obtain ⟨l, hl⟩ := hfd.inO.length_le_time
  let δ : ℝ := Real.log b / Real.log 2
  have hδ : 0 ≤ δ :=
    div_nonneg (Real.log_nonneg hb) (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  refine DecidableInExpTime.of_computableInO (hg.comp hfd.inO)
    (fun a ↦ (hfA a).trans (hgB (f a)))
    ⌈(1 + k * 2 ^ (δ * ((c : ℝ) / t)) * (2 * l + 1) ^ e + k : ℝ)⌉₊ (d * (e + 1)) fun a ↦ ?_
  have hexp : (2 : ℝ) ^ (δ * μB (f a)) ≤
      2 ^ (δ * ((c : ℝ) / t)) * 2 ^ ((((p : ℝ) / t) * δ) * μA a) := by
    rw [← Real.rpow_add (by norm_num)]
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    have hμR : (t : ℝ) * μB (f a) ≤ p * μA a + c := by exact_mod_cast hμ a
    have hdiv : (μB (f a) : ℝ) ≤ ((p : ℝ) / t) * μA a + (c : ℝ) / t := by
      have : (μB (f a) : ℝ) = ((t : ℝ) * μB (f a)) / t := by field_simp
      rw [this]
      calc ((t : ℝ) * μB (f a)) / t ≤ (p * μA a + c) / t := div_le_div_of_nonneg_right
              (by exact_mod_cast hμ a) htR.le
        _ = ((p : ℝ) / t) * μA a + (c : ℝ) / t := by ring
    nlinarith
  have key := reduction_add_time_le (P := ((encA a).length + 1 : ℝ) ^ d)
    (C := (2 : ℝ) ^ (δ * ((c : ℝ) / t)))
    (one_le_pow₀ (le_add_of_nonneg_left (Nat.cast_nonneg _)))
    (Real.one_le_rpow (by norm_num) (by positivity)) (by positivity)
    (by exact_mod_cast hl a) hexp (htm (f a))
  push_cast
  rw [pow_mul]
  exact key.trans (mul_le_mul_of_nonneg_right (Nat.le_ceil _) (by positivity))

end MachineCombinators

/-! ### 2. Explicit-Table $q$-CSP-$B$ and Lampis's $k$-SAT Block-Grouping Reduction -/

section LampisQCSPB

/-- Explicit allowed-tuple table semantics over domain `Fin B`: a constraint `⟨rel, scope⟩` holds
under `γ : ℕ → Fin B` iff `(scope.map γ).map Fin.val ∈ rel`. -/
@[expose]
def finTableSem (B : ℕ) (rel : List (List ℕ)) (vals : List (Fin B)) : Bool :=
  decide (vals.map Fin.val ∈ rel)

@[simp]
theorem finTableSem_eq_true_iff {B : ℕ} {rel : List (List ℕ)} {vals : List (Fin B)} :
    finTableSem B rel vals = true ↔ vals.map Fin.val ∈ rel :=
  decide_eq_true_iff

/-- The $q$-arity explicit-table CSP decision problem over domain `Fin B`: instances `F` where every
constraint scope has length at most `q` and some assignment `γ : ℕ → Fin B` satisfies `F`. -/
@[expose]
def QCSPB (q B : ℕ) : Set (CSP (List (List ℕ)) ℕ) :=
  CSP.KCSP q (finTableSem B)

/-- Framed binary encoding of explicit-table CSP instances `CSP (List (List ℕ)) ℕ`. -/
abbrev encTableCSP : CSP (List (List ℕ)) ℕ ↪ List Bool :=
  encCSP (encList (encList encNat)) encNat

/-- Enumerate all length-`r` lists of natural numbers in `{0, …, B - 1}`. -/
def enumTuples (B : ℕ) : ℕ → List (List ℕ)
  | 0 => [[]]
  | r + 1 => (List.range B).flatMap fun d ↦ (enumTuples B r).map (d :: ·)

private theorem mem_enumTuples_iff {B : ℕ} :
    ∀ {r : ℕ} {ds : List ℕ},
      ds ∈ enumTuples B r ↔ ds.length = r ∧ ∀ d ∈ ds, d < B
  | 0, [] => by simp [enumTuples]
  | 0, _ :: _ => by simp [enumTuples]
  | r + 1, [] => by simp [enumTuples]
  | r + 1, d :: ds => by
      simp only [enumTuples, List.mem_flatMap, List.mem_range, List.mem_map, List.cons.injEq,
        List.length_cons, List.mem_cons]
      constructor
      · rintro ⟨d', hd', ds', hds', ⟨rfl, rfl⟩⟩
        obtain ⟨hlen, hall⟩ := mem_enumTuples_iff.mp hds'
        exact ⟨by omega, fun x hx ↦ hx.elim (fun h ↦ h ▸ hd') (hall x)⟩
      · rintro ⟨hlen, hall⟩
        refine ⟨d, hall d (Or.inl rfl), ds, mem_enumTuples_iff.mpr ⟨by omega,
          fun x hx ↦ hall x (Or.inr hx)⟩, rfl, rfl⟩

/-- Little-endian base-`B` evaluation of a digit list. -/
def baseBDecode (B : ℕ) : List ℕ → ℕ
  | [] => 0
  | d :: ds => d + B * baseBDecode B ds

/-- Little-endian length-`p` base-`B` digit expansion of `N : ℕ`. -/
def baseBEncode (B : ℕ) : ℕ → ℕ → List ℕ
  | 0, _ => []
  | p + 1, N => (N % B) :: baseBEncode B p (N / B)

private theorem length_baseBEncode (B : ℕ) :
    ∀ (p N : ℕ), (baseBEncode B p N).length = p
  | 0, _ => rfl
  | p + 1, N => congrArg Nat.succ (length_baseBEncode B p (N / B))

private theorem baseBEncode_lt {B : ℕ} (hB : 0 < B) :
    ∀ {p N d : ℕ}, d ∈ baseBEncode B p N → d < B
  | 0, _, _, h => by simp [baseBEncode] at h
  | p + 1, N, d, h => by
      rcases List.mem_cons.mp h with rfl | h'
      · exact Nat.mod_lt N hB
      · exact baseBEncode_lt hB h'

private theorem baseBDecode_baseBEncode (B : ℕ) :
    ∀ (p N : ℕ), N < B ^ p → baseBDecode B (baseBEncode B p N) = N
  | 0, N, hN => by
      have h0 : N = 0 := by simpa using hN
      subst h0; rfl
  | p + 1, N, hN => by
      have hB : 0 < B := by
        by_contra h0
        simp [Nat.eq_zero_of_not_pos h0, pow_succ] at hN
      have hdiv : N / B < B ^ p := by
        rw [Nat.div_lt_iff_lt_mul hB, ← pow_succ]
        exact hN
      simp only [baseBEncode, baseBDecode, baseBDecode_baseBEncode B p (N / B) hdiv]
      exact Nat.mod_add_div N B

private def litAt (i : ℕ) (c : Clause ℕ) : Literal ℕ :=
  (c.drop i).headD (0, false)

private theorem litAt_eq_getElem :
    ∀ {i : ℕ} {c : Clause ℕ} (hi : i < c.length), litAt i c = c[i]
  | 0, _ :: _, _ => rfl
  | _ + 1, _ :: _, hi => litAt_eq_getElem (Nat.lt_of_succ_lt_succ hi)

private def chunkDecodeBits (B t p i : ℕ) (ds : List ℕ) : List Bool :=
  let val := baseBDecode B ((ds.drop (i * p)).take p)
  (List.range t).map val.testBit

private def tupleValidForClause (B t p len : ℕ) (ds : List ℕ) : Bool :=
  (List.range len).all fun i ↦ decide (baseBDecode B ((ds.drop (i * p)).take p) < 2 ^ t)

private def tupleSatisfiesAt (B t p len : ℕ) (ds : List ℕ) (dvars : List ℕ) (c : Clause ℕ) : Bool :=
  tupleValidForClause B t p len ds &&
    (List.range len).any fun i ↦
      let lit := litAt i c
      let off := (dvars.idxOf lit.1) % t
      (chunkDecodeBits B t p i ds).getD off false == lit.2

private def compileClauseAt (B t p len : ℕ) (dvars : List ℕ) (c : Clause ℕ) :
    Constraint (List (List ℕ)) ℕ where
  rel := (enumTuples B (len * p)).filter fun ds ↦ tupleSatisfiesAt B t p len ds dvars c
  scope := (List.range len).flatMap fun i ↦
    let blk := (dvars.idxOf (litAt i c).1) / t
    (List.range p).map fun r ↦ p * blk + r

private def compileClauseBounded (B t p : ℕ) :
    ℕ → List ℕ → Clause ℕ → Constraint (List (List ℕ)) ℕ
  | 0, dvars, c =>
      if c.length == 0 then compileClauseAt B t p 0 dvars c else ⟨[], []⟩
  | k + 1, dvars, c =>
      if c.length == k + 1 then compileClauseAt B t p (k + 1) dvars c
      else compileClauseBounded B t p k dvars c

private theorem compileClauseBounded_eq_at {B t p : ℕ} :
    ∀ {k : ℕ} {dvars : List ℕ} {c : Clause ℕ}, c.length ≤ k →
      compileClauseBounded B t p k dvars c = compileClauseAt B t p c.length dvars c
  | 0, dvars, c, hle => by
      have h0 : c.length = 0 := Nat.eq_zero_of_le_zero hle
      simp [compileClauseBounded, h0]
  | k + 1, dvars, c, hle => by
      by_cases htop : c.length = k + 1
      · simp [compileClauseBounded, htop]
      · have hle' : c.length ≤ k := by omega
        simp [compileClauseBounded, htop, compileClauseBounded_eq_at hle']

/-- Block-grouping compiler mapping a `k`-CNF formula `φ` into an explicit-table `(k * p)`-CSP-`B`
instance. Formulas having any clause of width `> k` map to `[⟨[], []⟩]`. -/
def cnfToQCSP (B k t p : ℕ) (φ : CNF ℕ) : CSP (List (List ℕ)) ℕ :=
  if φ.all (fun c ↦ decide (c.length ≤ k)) then
    let dvars := φ.distinctVars
    φ.map (compileClauseBounded B t p k dvars)
  else
    [⟨[], []⟩]

section PolyTimeCompiler

open ComputableInPolyTime

private theorem computableInPolyTime_litAt (i : ℕ) :
    ComputableInPolyTime (litAt i) (encList (encPair encNat encBool)) (encPair encNat encBool) := by
  unfold litAt
  exact listHeadDWithInput (listDropWithInput id' (const i)) (const (0, false))

private theorem computableInPolyTime_compileClauseAt_unary (B t p len : ℕ) :
    ComputableInPolyTime (fun q : List ℕ × Clause ℕ ↦ compileClauseAt B t p len q.1 q.2)
      (encPair (encList encNat) (encList (encPair encNat encBool)))
      (encConstraint (encList (encList encNat)) encUnary) := by
  let encIn := encPair (encList encNat) (encList (encPair encNat encBool))
  have hrel : ComputableInPolyTime
      (fun q : List ℕ × Clause ℕ ↦
        (enumTuples B (len * p)).filter fun ds ↦ tupleSatisfiesAt B t p len ds q.1 q.2)
      encIn (encList (encList encNat)) := by
    have hmf := @mapFilterConst (List ℕ) (List ℕ × Clause ℕ)
      (encList encNat) encIn (List ℕ) (enumTuples B (len * p))
      (fun q ds ↦ tupleSatisfiesAt B t p len ds q.1 q.2)
      (fun _ ds ↦ ds)
      (fun ds _ ↦ by
        unfold tupleSatisfiesAt
        refine bool_and.comp
          (((const (tupleValidForClause B t p len ds) :
              ComputableInPolyTime _ encIn encBool)).prod ?_)
        refine anyConst (List.range len) fun i _ ↦ ?_
        have hlit : ComputableInPolyTime (fun q : List ℕ × Clause ℕ ↦ litAt i q.2)
            encIn (encPair encNat encBool) :=
          (computableInPolyTime_litAt i).comp (snd _ _)
        have hidx : ComputableInPolyTime
            (fun q : List ℕ × Clause ℕ ↦ q.1.idxOf (litAt i q.2).1)
            encIn encUnary :=
          idxOfWithInput (fst _ _) hlit.fst'
        have hoff : ComputableInPolyTime
            (fun q : List ℕ × Clause ℕ ↦ (q.1.idxOf (litAt i q.2).1) % t)
            encIn encUnary :=
          unary_mod' hidx (const t)
        have hbit : ComputableInPolyTime
            (fun q : List ℕ × Clause ℕ ↦
              (chunkDecodeBits B t p i ds).getD ((q.1.idxOf (litAt i q.2).1) % t) false)
            encIn encBool :=
          bitsGetDWithInput (const (chunkDecodeBits B t p i ds)) hoff false
        exact ComputableInPolyTime.beq hbit hlit.snd')
      (fun ds _ ↦ const ds)
    simpa only [List.map_id'] using hmf
  have hscope : ComputableInPolyTime
      (fun q : List ℕ × Clause ℕ ↦
        (List.range len).flatMap fun i ↦
          let blk := (q.1.idxOf (litAt i q.2).1) / t
          (List.range p).map fun r ↦ p * blk + r)
      encIn (encList encUnary) := by
    refine flatMapConst (List.range len) fun i _ ↦ ?_
    refine mapConst (List.range p) fun r _ ↦ ?_
    have hlit : ComputableInPolyTime (fun q : List ℕ × Clause ℕ ↦ litAt i q.2)
        encIn (encPair encNat encBool) :=
      (computableInPolyTime_litAt i).comp (snd _ _)
    have hidx : ComputableInPolyTime
        (fun q : List ℕ × Clause ℕ ↦ q.1.idxOf (litAt i q.2).1)
        encIn encUnary :=
      idxOfWithInput (fst _ _) hlit.fst'
    have hblk : ComputableInPolyTime
        (fun q : List ℕ × Clause ℕ ↦ (q.1.idxOf (litAt i q.2).1) / t)
        encIn encUnary :=
      unary_div' hidx (const t)
    fun_prop
  exact encConstraint_mk_polyTime hrel hscope

private theorem computableInPolyTime_compileClauseBounded_unary (B t p : ℕ) :
    ∀ k : ℕ,
      ComputableInPolyTime (fun q : List ℕ × Clause ℕ ↦ compileClauseBounded B t p k q.1 q.2)
        (encPair (encList encNat) (encList (encPair encNat encBool)))
        (encConstraint (encList (encList encNat)) encUnary)
  | 0 => by
      unfold compileClauseBounded
      have hlen : ComputableInPolyTime (fun q : List ℕ × Clause ℕ ↦ q.2.length == 0)
          (encPair (encList encNat) (encList (encPair encNat encBool))) encBool := by
        exact unary_beq ((length_list (encPair encNat encBool)).comp (snd _ _)) (const 0)
      exact hlen.ite' (computableInPolyTime_compileClauseAt_unary B t p 0)
        (const (⟨[], []⟩ : Constraint (List (List ℕ)) ℕ))
  | k + 1 => by
      unfold compileClauseBounded
      have hlen : ComputableInPolyTime (fun q : List ℕ × Clause ℕ ↦ q.2.length == k + 1)
          (encPair (encList encNat) (encList (encPair encNat encBool))) encBool := by
        exact unary_beq ((length_list (encPair encNat encBool)).comp (snd _ _)) (const (k + 1))
      exact hlen.ite' (computableInPolyTime_compileClauseAt_unary B t p (k + 1))
        (computableInPolyTime_compileClauseBounded_unary B t p k)

/-- `cnfToQCSP B k t p` is computable in polynomial time on multi-tape Turing machines. -/
theorem computableInPolyTime_cnfToQCSP (B k t p : ℕ) :
    ComputableInPolyTime (cnfToQCSP B k t p) encCNF encTableCSP := by
  let encCl := encList (encPair encNat encBool)
  have hunary : ComputableInPolyTime
      (fun φ : CNF ℕ ↦ φ.map (compileClauseBounded B t p k φ.distinctVars))
      encCNF (encCSP (encList (encList encNat)) encUnary) := by
    have hdvars := SAT.computableInPolyTime_distinctVars
    have hclauses : ComputableInPolyTime (fun φ : CNF ℕ ↦ φ) encCNF (encList encCl) :=
      of_eq fun _ ↦ rfl
    have harg : ComputableInPolyTime
        (fun p0 : CNF ℕ × Clause ℕ ↦ (p0.1.distinctVars, p0.2))
        (encPair encCNF encCl) (encPair (encList encNat) encCl) :=
      ((hdvars.comp (fst encCNF encCl)).of_enc_eq fun _ ↦ rfl).prod (snd encCNF encCl)
    have hbody : ComputableInPolyTime
        (fun p0 : CNF ℕ × Clause ℕ ↦ compileClauseBounded B t p k p0.1.distinctVars p0.2)
        (encPair encCNF encCl) (encConstraint (encList (encList encNat)) encUnary) :=
      ((computableInPolyTime_compileClauseBounded_unary B t p k).comp harg).of_enc_eq fun _ ↦ rfl
    exact (mapWithInput hclauses hbody).of_enc_eq fun _ ↦ rfl
  have hbin : ComputableInPolyTime
      (fun φ : CNF ℕ ↦ φ.map (compileClauseBounded B t p k φ.distinctVars))
      encCNF encTableCSP :=
    ((Cslib.Complexity.CSP.computableInPolyTime_unary_to_binary
      (encList (encList encNat))).comp hunary).of_enc_eq fun _ ↦ rfl
  have hcond : ComputableInPolyTime
      (fun φ : CNF ℕ ↦ φ.all (fun c ↦ decide (c.length ≤ k))) encCNF encBool :=
    computableInPolyTime_all_length_le k
  have hfb : ComputableInPolyTime (fun _ : CNF ℕ ↦ ([⟨[], []⟩] : CSP (List (List ℕ)) ℕ))
      encCNF encTableCSP :=
    const ([(⟨[], []⟩ : Constraint (List (List ℕ)) ℕ)])
  exact (hcond.ite' hbin hfb).of_enc_eq fun _ ↦ rfl

end PolyTimeCompiler

private theorem take_drop_flatMap_eq {α β : Type*} (p : ℕ) :
    ∀ (l : List α) (f : α → List β), (∀ x ∈ l, (f x).length = p) → ∀ (i : ℕ) (hi : i < l.length),
      (((l.flatMap f).drop (i * p)).take p) = f l[i]
  | a :: l, f, hf, 0, _ => by
      simp only [List.flatMap_cons, Nat.zero_mul, List.drop_zero, List.getElem_cons_zero]
      rw [List.take_append_of_le_length (le_of_eq (hf a (List.mem_cons_self ..)).symm),
        List.take_of_length_le (le_of_eq (hf a (List.mem_cons_self ..)))]
  | a :: l, f, hf, i + 1, hi => by
      simp only [List.flatMap_cons, List.getElem_cons_succ]
      have hfa : (f a).length = p := hf a (List.mem_cons_self ..)
      have hmul : (i + 1) * p = (f a).length + i * p := by rw [hfa]; ring
      rw [hmul, List.drop_append]
      simp only [List.drop_of_length_le (Nat.le_add_right (f a).length (i * p)), List.nil_append,
        Nat.add_sub_cancel_left]
      exact take_drop_flatMap_eq p l f (fun x hx ↦ hf x (List.mem_cons_of_mem a hx)) i
        (Nat.lt_of_succ_lt_succ hi)

private theorem sum_two_pow_lt (P : ℕ → Bool) :
    ∀ t : ℕ, (∑ r ∈ Finset.range t, if P r then 2 ^ r else 0) < 2 ^ t
  | 0 => by simp
  | t + 1 => by
      have ih := sum_two_pow_lt P t
      rw [Finset.sum_range_succ, pow_succ]
      split_ifs <;> omega

private def packBlockBits (σ : ℕ → Bool) (dvars : List ℕ) (t blk : ℕ) : ℕ :=
  ∑ r ∈ Finset.range t, if σ (dvars.getD (blk * t + r) 0) then 2 ^ r else 0

private theorem packBlockBits_lt (σ : ℕ → Bool) (dvars : List ℕ) (t blk : ℕ) :
    packBlockBits σ dvars t blk < 2 ^ t :=
  sum_two_pow_lt (fun r ↦ σ (dvars.getD (blk * t + r) 0)) t

private theorem testBit_sum_two_pow (P : ℕ → Bool) :
    ∀ (t off : ℕ), off < t →
      (∑ r ∈ Finset.range t, if P r then 2 ^ r else 0).testBit off = P off
  | 0, _, hoff => absurd hoff (Nat.not_lt_zero _)
  | t + 1, off, hoff => by
      rw [Finset.sum_range_succ]
      let S := ∑ r ∈ Finset.range t, if P r then 2 ^ r else 0
      have hS_lt : S < 2 ^ t := sum_two_pow_lt P t
      by_cases htop : off = t
      · subst htop
        cases hPt : P off
        · simp only [Bool.false_eq_true, ↓reduceIte, add_zero]
          exact Nat.testBit_lt_two_pow hS_lt
        · simp only [↓reduceIte]
          have hdiv : (S + 2 ^ off) / 2 ^ off = 1 := by
            have hpos : 0 < 2 ^ off := Nat.two_pow_pos off
            rw [Nat.add_div_right S hpos, Nat.div_eq_of_lt hS_lt, zero_add]
          rw [Nat.testBit, Nat.shiftRight_eq_div_pow, hdiv]
          rfl
      · have hoff' : off < t := by omega
        have ih := testBit_sum_two_pow P t off hoff'
        cases hPt : P t
        · simpa [S, hPt] using ih
        · simp only [↓reduceIte]
          have hmod : (S + 2 ^ t) % 2 ^ (off + 1) = S % 2 ^ (off + 1) := by
            have hdvd : 2 ^ (off + 1) ∣ 2 ^ t := Nat.pow_dvd_pow 2 (by omega)
            obtain ⟨m, hm⟩ := hdvd
            rw [hm, Nat.add_mul_mod_self_left]
          have hbit_eq : ∀ x : ℕ, x.testBit off = decide ((x % 2 ^ (off + 1)) / 2 ^ off = 1) := by
            intro x
            have hlt2 : (x / 2 ^ off) % 2 < 2 := Nat.mod_lt _ (by norm_num)
            have hmod_div : (x % (2 ^ off * 2)) / 2 ^ off = (x / 2 ^ off) % 2 := by
              set P := 2 ^ off
              have hP : 0 < P := Nat.two_pow_pos off
              have h1 := Nat.div_add_mod x (P * 2)
              have h2 := Nat.div_add_mod (x % (P * 2)) P
              have hlt_rem : x % (P * 2) < P * 2 := Nat.mod_lt x (by positivity)
              have hq_lt : (x % (P * 2)) / P < 2 :=
                (Nat.div_lt_iff_lt_mul hP).mpr (hlt_rem.trans_eq (Nat.mul_comm P 2))
              have hrem_P : (x % (P * 2)) % P < P := Nat.mod_lt _ hP
              have hlin : (2 * (x / (P * 2)) + (x % (P * 2)) / P) * P + (x % (P * 2)) % P = x := by
                have hring : (2 * (x / (P * 2)) + (x % (P * 2)) / P) * P =
                    P * 2 * (x / (P * 2)) + P * ((x % (P * 2)) / P) := by ring
                omega
              have hx_div : x / P = 2 * (x / (P * 2)) + (x % (P * 2)) / P := by
                apply Nat.div_eq_of_lt_le
                · omega
                · have hring : (2 * (x / (P * 2)) + (x % (P * 2)) / P + 1) * P =
                      (2 * (x / (P * 2)) + (x % (P * 2)) / P) * P + P := by ring
                  omega
              rw [hx_div, Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt hq_lt]
            rw [Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.and_comm, Nat.and_one_is_mod,
              pow_succ, hmod_div]
            rcases (by omega : (x / 2 ^ off) % 2 = 0 ∨ (x / 2 ^ off) % 2 = 1) with h0 | h1
            · simp [h0]
            · simp [h1]
          rw [hbit_eq, hmod, ← hbit_eq]
          exact ih

/-- **Unconditional block-grouping reduction (`KSAT k → QCSPB q B`)**: for any $B \ge 2$, $k$,
$t \ge 1$, $p \ge 1$, and $q \ge \max(2, k \cdot p)$ with $2^t \le B^p$, `cnfToQCSP B k t p`
reduces `KSAT k` to `QCSPB q B` in polynomial time with variable bound
`t * (cnfToQCSP B k t p φ).numVars ≤ p * φ.numVars + p * t`. -/
theorem exists_ksat_to_qcspb_reduction {B k t p q : ℕ} (hB : 2 ≤ B) (ht : 0 < t) (hp : 0 < p)
    (hpow : 2 ^ t ≤ B ^ p) (hq : k * p ≤ q) :
    ComputableInPolyTime (cnfToQCSP B k t p) encCNF encTableCSP ∧
      (∀ φ : CNF ℕ, φ ∈ KSAT k ↔ cnfToQCSP B k t p φ ∈ QCSPB q B) ∧
      (∀ φ : CNF ℕ, t * (cnfToQCSP B k t p φ).numVars ≤ p * φ.numVars + p * t) := by
  have hBpos : 0 < B := by omega
  have : NeZero B := ⟨by omega⟩
  refine ⟨computableInPolyTime_cnfToQCSP B k t p, fun φ ↦ ?_, fun φ ↦ ?_⟩
  · by_cases hall : ∀ c ∈ φ, c.length ≤ k
    · have hall_b : (φ.all fun c ↦ decide (c.length ≤ k)) = true := by simpa using hall
      simp only [cnfToQCSP, hall_b, ↓reduceIte, QCSPB, CSP.KCSP, Set.mem_ofPred_eq]
      have hscopes : ∀ c' ∈ φ.map (compileClauseBounded B t p k φ.distinctVars),
          c'.scope.length ≤ q := by
        intro c' hc'
        obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hc'
        rw [compileClauseBounded_eq_at (hall c hc)]
        simp only [compileClauseAt, List.length_flatMap, List.length_map, List.length_range,
          List.map_const', List.sum_replicate, smul_eq_mul]
        exact (Nat.mul_le_mul_right p (hall c hc)).trans hq
      rw [and_iff_right hscopes]
      constructor
      · rintro ⟨_, hsat⟩
        obtain ⟨σ, hσ⟩ := hsat
        let γ : ℕ → Fin B := fun y ↦
          let blk := y / p
          let r := y % p
          let N := packBlockBits σ φ.distinctVars t blk
          ⟨(baseBEncode B p N).getD r 0, by
            have hr : r < (baseBEncode B p N).length := by
              rw [length_baseBEncode]
              exact Nat.mod_lt y hp
            have hget : (baseBEncode B p N).getD r 0 = (baseBEncode B p N)[r]'hr := by
              simp [List.getD_eq_getElem?_getD, hr]
            rw [hget]
            exact baseBEncode_lt hBpos (List.getElem_mem hr)⟩
        refine ⟨γ, ?_⟩
        rw [CSP.eval, List.all_eq_true]
        intro c' hc'
        obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hc'
        rw [compileClauseBounded_eq_at (hall c hc)]
        simp only [Constraint.eval, finTableSem, compileClauseAt, decide_eq_true_eq,
          List.mem_filter]
        let ds : List ℕ :=
          (((List.range c.length).flatMap fun i ↦
              (List.range p).map fun r ↦ p * ((φ.distinctVars.idxOf (litAt i c).1) / t) + r).map
            γ).map Fin.val
        have hds_len : ds.length = c.length * p := by
          simp [ds, List.length_flatMap, List.sum_replicate]
        have hds_lt : ∀ d ∈ ds, d < B := by
          intro d hd
          obtain ⟨x, _, rfl⟩ := List.mem_map.mp hd
          exact x.isLt
        have hds_enum : ds ∈ enumTuples B (c.length * p) :=
          mem_enumTuples_iff.mpr ⟨hds_len, hds_lt⟩
        refine ⟨hds_enum, ?_⟩
        have hchunk : ∀ i (hi : i < c.length),
            ((ds.drop (i * p)).take p) =
              baseBEncode B p
                (packBlockBits σ φ.distinctVars t ((φ.distinctVars.idxOf (litAt i c).1) / t)) := by
          intro i hi
          have hflat : ds = (List.range c.length).flatMap fun j ↦
              (List.range p).map fun r ↦
                (γ (p * ((φ.distinctVars.idxOf (litAt j c).1) / t) + r)).val := by
            simp [ds, List.map_flatMap, List.map_map, Function.comp_def]
          rw [hflat]
          have htake := take_drop_flatMap_eq p (List.range c.length)
            (fun j ↦ (List.range p).map fun r ↦
              (γ (p * ((φ.distinctVars.idxOf (litAt j c).1) / t) + r)).val)
            (fun _ _ ↦ by simp) i (by simpa using hi)
          simp only [List.getElem_range] at htake
          rw [htake]
          set blk := (φ.distinctVars.idxOf (litAt i c).1) / t
          apply List.ext_getElem (by simp [length_baseBEncode])
          intro r hr1 hr2
          simp only [List.getElem_map, List.getElem_range]
          have hr_lt : r < p := by simpa using hr1
          have hdiv : (p * blk + r) / p = blk := by
            rw [Nat.mul_add_div hp, Nat.div_eq_of_lt hr_lt, add_zero]
          have hmod : (p * blk + r) % p = r := by
            rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hr_lt]
          change ((baseBEncode B p (packBlockBits σ φ.distinctVars t ((p * blk + r) / p))).getD
            ((p * blk + r) % p) 0) = _
          rw [hdiv, hmod, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hr2,
            Option.getD_some]
        unfold tupleSatisfiesAt tupleValidForClause
        rw [Bool.and_eq_true, List.all_eq_true, List.any_eq_true]
        refine ⟨fun i hi ↦ ?_, ?_⟩
        · have hi' : i < c.length := List.mem_range.mp hi
          rw [decide_eq_true_eq, hchunk i hi',
            baseBDecode_baseBEncode B p _
              ((packBlockBits_lt σ φ.distinctVars t _).trans_le hpow)]
          exact packBlockBits_lt σ φ.distinctVars t _
        · have hc_sat : Clause.eval σ c = true := by
            rw [CNF.eval, List.all_eq_true] at hσ
            exact hσ c hc
          rw [Clause.eval, List.any_eq_true] at hc_sat
          obtain ⟨lit, hlit_mem, hlit_eval⟩ := hc_sat
          obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hlit_mem
          refine ⟨i, List.mem_range.mpr hi, ?_⟩
          have hlit_eq : litAt i c = c[i] := litAt_eq_getElem hi
          have hv_mem : c[i].1 ∈ φ.distinctVars :=
            CNF.mem_distinctVars.mpr (CNF.mem_vars.mpr ⟨c, hc, c[i].2, by simp⟩)
          let idx := φ.distinctVars.idxOf c[i].1
          have hidx_lt : idx < φ.distinctVars.length := List.idxOf_lt_length_iff.mpr hv_mem
          have hgetD_idx : φ.distinctVars.getD idx 0 = c[i].1 := by
            simp [idx, List.getD_eq_getElem?_getD, hidx_lt]
          have hoff_lt : idx % t < t := Nat.mod_lt idx ht
          have hblk_off : (idx / t) * t + idx % t = idx := by
            rw [Nat.mul_comm, Nat.div_add_mod]
          unfold chunkDecodeBits
          rw [hchunk i hi, hlit_eq,
            baseBDecode_baseBEncode B p _
              ((packBlockBits_lt σ φ.distinctVars t _).trans_le hpow)]
          have hbit : (packBlockBits σ φ.distinctVars t (idx / t)).testBit (idx % t) =
              σ c[i].1 := by
            unfold packBlockBits
            rw [testBit_sum_two_pow _ t (idx % t) hoff_lt, hblk_off, hgetD_idx]
          simp only [List.getD_eq_getElem?_getD, List.length_map, List.length_range, hoff_lt,
            List.getElem?_eq_getElem, Option.getD_some, List.getElem_map, List.getElem_range,
            idx, hbit]
          simpa [Literal.eval] using hlit_eval
      · rintro ⟨γ, hγ⟩
        refine ⟨hall, ?_⟩
        let σ : ℕ → Bool := fun v ↦
          let idx := φ.distinctVars.idxOf v
          let blk := idx / t
          let off := idx % t
          let digits := (List.range p).map fun r ↦ (γ (p * blk + r)).val
          (baseBDecode B digits).testBit off
        refine ⟨σ, ?_⟩
        rw [CNF.eval, List.all_eq_true]
        intro c hc
        rw [CSP.eval, List.all_eq_true] at hγ
        have hc_eval := hγ _ (List.mem_map_of_mem hc)
        rw [compileClauseBounded_eq_at (hall c hc)] at hc_eval
        simp only [Constraint.eval, finTableSem, compileClauseAt, decide_eq_true_eq,
          List.mem_filter] at hc_eval
        obtain ⟨_, hsat⟩ := hc_eval
        unfold tupleSatisfiesAt at hsat
        rw [Bool.and_eq_true, List.any_eq_true] at hsat
        obtain ⟨_, i, hi_mem, hi_ok⟩ := hsat
        have hi : i < c.length := List.mem_range.mp hi_mem
        have hchunk_eq :
            (((((List.range c.length).flatMap fun j ↦
                (List.range p).map fun r ↦
                  p * ((φ.distinctVars.idxOf (litAt j c).1) / t) + r).map γ).map Fin.val).drop
              (i * p)).take p =
              (List.range p).map fun r ↦
                (γ (p * ((φ.distinctVars.idxOf (litAt i c).1) / t) + r)).val := by
          have hflat : ((((List.range c.length).flatMap fun j ↦
                (List.range p).map fun r ↦
                  p * ((φ.distinctVars.idxOf (litAt j c).1) / t) + r).map γ).map Fin.val) =
              (List.range c.length).flatMap fun j ↦
                (List.range p).map fun r ↦
                  (γ (p * ((φ.distinctVars.idxOf (litAt j c).1) / t) + r)).val := by
            simp [List.map_flatMap, List.map_map, Function.comp_def]
          rw [hflat]
          have htk := take_drop_flatMap_eq p (List.range c.length)
            (fun j ↦ (List.range p).map fun r ↦
              (γ (p * ((φ.distinctVars.idxOf (litAt j c).1) / t) + r)).val)
            (fun _ _ ↦ by simp) i (by simpa using hi)
          simp only [List.getElem_range] at htk
          exact htk
        unfold chunkDecodeBits at hi_ok
        rw [hchunk_eq, litAt_eq_getElem hi] at hi_ok
        have hoff_lt : (φ.distinctVars.idxOf c[i].1) % t < t := Nat.mod_lt _ ht
        simp only [List.getD_eq_getElem?_getD, List.length_map, List.length_range, hoff_lt,
          List.getElem?_eq_getElem, Option.getD_some, List.getElem_map, List.getElem_range,
          beq_iff_eq] at hi_ok
        rw [Clause.eval, List.any_eq_true]
        exact ⟨c[i], List.getElem_mem hi, by simpa [Literal.eval, σ] using hi_ok⟩
    · have hall_b : (φ.all fun c ↦ decide (c.length ≤ k)) = false := by
        rw [Bool.eq_false_iff]
        simpa using hall
      simp only [cnfToQCSP, hall_b, Bool.false_eq_true, ↓reduceIte, QCSPB, CSP.KCSP,
        Set.mem_ofPred_eq]
      constructor
      · intro hksat
        exact absurd hksat.1 hall
      · rintro ⟨_, γ, hγ⟩
        simp [CSP.eval, Constraint.eval, finTableSem] at hγ
  · by_cases hall : (φ.all fun c ↦ decide (c.length ≤ k)) = true
    · simp only [cnfToQCSP, hall, ↓reduceIte]
      have hsub : (CSP.vars (φ.map (compileClauseBounded B t p k φ.distinctVars))).toFinset ⊆
          Finset.range (p * (φ.numVars / t + 1)) := by
        intro y hy
        rw [List.mem_toFinset, CSP.vars, List.mem_flatMap] at hy
        obtain ⟨c', hc', hy_sc⟩ := hy
        obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hc'
        have hle : c.length ≤ k := by
          rw [List.all_eq_true] at hall
          exact of_decide_eq_true (hall c hc)
        rw [compileClauseBounded_eq_at hle] at hy_sc
        simp only [compileClauseAt, List.mem_flatMap, List.mem_range, List.mem_map] at hy_sc
        obtain ⟨i, hi, r, hr, rfl⟩ := hy_sc
        rw [litAt_eq_getElem hi, Finset.mem_range]
        have hv_mem : c[i].1 ∈ φ.distinctVars :=
          CNF.mem_distinctVars.mpr
            (CNF.mem_vars.mpr ⟨c, hc, c[i].2, by simp⟩)
        have hidx_lt : φ.distinctVars.idxOf c[i].1 < φ.numVars := by
          rw [← φ.length_distinctVars]
          exact List.idxOf_lt_length_iff.mpr hv_mem
        have hdiv_le : (φ.distinctVars.idxOf c[i].1) / t ≤ φ.numVars / t :=
          Nat.div_le_div_right hidx_lt.le
        nlinarith
      have hcard : CSP.numVars (φ.map (compileClauseBounded B t p k φ.distinctVars)) ≤
          p * (φ.numVars / t + 1) :=
        (Finset.card_le_card hsub).trans_eq (Finset.card_range _)
      have hmul : t * (φ.numVars / t) ≤ φ.numVars := Nat.mul_div_le φ.numVars t
      nlinarith
    · rw [Bool.not_eq_true] at hall
      simp [cnfToQCSP, hall, CSP.numVars, CSP.vars]

/-- **Lampis's Fine-Grained $q$-CSP-$B$ Hardness Theorem**: assuming `Cslib.Complexity.SETH`, for
every integer $B \ge 2$ and every $\varepsilon > 0$, there exists an arity $q \ge 2$ such that
`QCSPB q B` cannot be decided in time $\mathcal{O}^*((B - \varepsilon)^{\mathrm{numVars}})$. -/
theorem SETH.exists_not_decidableInBaseExpTime_qcspb (hSETH : SETH) {B : ℕ} (hB : 2 ≤ B)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ q : ℕ, 2 ≤ q ∧ ¬ DecidableInBaseExpTime (QCSPB q B) encTableCSP CSP.numVars (B - ε) := by
  let ε' : ℝ := min ε (1 / 2)
  have hε'_pos : 0 < ε' := lt_min hε (by norm_num)
  have hε'_le : ε' ≤ 1 / 2 := min_le_right ε (1 / 2)
  let b : ℝ := (B : ℝ) - ε'
  have hB_real : (2 : ℝ) ≤ B := by exact_mod_cast hB
  have hb_gt_one : 1 < b := by dsimp [b]; linarith
  have hb_lt_B : b < B := by dsimp [b]; linarith
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  let log2B : ℝ := Real.log B / Real.log 2
  let log2b : ℝ := Real.log b / Real.log 2
  have hlogB_ge_one : 1 ≤ log2B := by
    dsimp [log2B]
    rw [le_div_iff₀ hlog2_pos, one_mul]
    exact Real.log_le_log (by norm_num) hB_real
  have hlogB_pos : 0 < log2B := zero_lt_one.trans_le hlogB_ge_one
  have hlogb_lt : log2b < log2B :=
    div_lt_div_of_pos_right (Real.log_lt_log (by linarith) hb_lt_B) hlog2_pos
  have hlogb_pos : 0 < log2b := div_pos (Real.log_pos hb_gt_one) hlog2_pos
  let η : ℝ := (1 - log2b / log2B) / 2
  have hη_pos : 0 < η := by
    dsimp [η]
    have hdiv_lt : log2b / log2B < 1 := (div_lt_one hlogB_pos).mpr hlogb_lt
    linarith
  have hη_lt_half : η < 1 / 2 := by
    dsimp [η]
    have hdiv_pos : 0 < log2b / log2B := div_pos hlogb_pos hlogB_pos
    linarith
  obtain ⟨k, hkSETH⟩ := hSETH η hη_pos
  let p : ℕ := ⌈(1 : ℝ) / (η * log2B)⌉₊ + 2
  have hp_pos : 0 < p := by positivity
  let t : ℕ := ⌊(p : ℝ) * log2B⌋₊
  have hp_ge_two : (2 : ℝ) ≤ p := by dsimp [p]; exact_mod_cast Nat.le_add_left 2 _
  have ht_pos : 0 < t := by
    dsimp [t]
    rw [Nat.floor_pos]
    nlinarith
  have ht_le : (t : ℝ) ≤ p * log2B :=
    Nat.floor_le (by positivity)
  have ht_gt : (p : ℝ) * log2B - 1 < t :=
    Nat.sub_one_lt_floor _
  have hpow : 2 ^ t ≤ B ^ p := by
    have hpow_real : ((2 ^ t : ℕ) : ℝ) ≤ ((B ^ p : ℕ) : ℝ) := by
      rw [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast 2 t,
        Nat.cast_pow, ← Real.rpow_natCast (B : ℝ) p]
      have hB_eq : (B : ℝ) = (2 : ℝ) ^ log2B := by
        dsimp [log2B]
        rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
        have : Real.log 2 * (Real.log B / Real.log 2) = Real.log B := by
          field_simp [hlog2_pos.ne']
        rw [this, Real.exp_log (by linarith)]
      calc (2 : ℝ) ^ (t : ℝ) ≤ 2 ^ ((p : ℝ) * log2B) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) ht_le
        _ = ((2 : ℝ) ^ log2B) ^ (p : ℝ) := by
            rw [mul_comm, Real.rpow_mul (by norm_num)]
        _ = (B : ℝ) ^ (p : ℝ) := by rw [← hB_eq]
    exact_mod_cast hpow_real
  have hrate : ((p : ℝ) / t) * log2b ≤ 1 - η := by
    have htR_pos : (0 : ℝ) < t := by exact_mod_cast ht_pos
    rw [div_mul_eq_mul_div, div_le_iff₀ htR_pos]
    have hp_bound : 1 / (η * log2B) ≤ (p : ℝ) := by
      dsimp [p]
      exact (Nat.le_ceil _).trans (by norm_cast; omega)
    have hpη : 1 ≤ (p : ℝ) * (η * log2B) := by
      rwa [div_le_iff₀ (mul_pos hη_pos hlogB_pos)] at hp_bound
    have hlog_id : log2b = (1 - 2 * η) * log2B := by
      dsimp [η]
      field_simp
      ring
    have h1mη_pos : 0 < 1 - η := by linarith
    have hmul_gt : (1 - η) * ((p : ℝ) * log2B - 1) < (1 - η) * t :=
      mul_lt_mul_of_pos_left ht_gt h1mη_pos
    rw [hlog_id]
    nlinarith
  let q : ℕ := max 2 (k * p)
  refine ⟨q, le_max_left 2 (k * p), fun hdec ↦ ?_⟩
  have hdec_b : DecidableInBaseExpTime (QCSPB q B) encTableCSP CSP.numVars b :=
    hdec.mono (by dsimp [b, ε']; linarith [min_le_left ε (1 / 2)])
  obtain ⟨hf_poly, hf_corr, hf_vars⟩ :=
    exists_ksat_to_qcspb_reduction hB ht_pos hp_pos hpow (le_max_right 2 (k * p))
  have hksat_exp : DecidableInExpTime (KSAT k) encCNF CNF.numVars
      (((p : ℝ) / t) * log2b) :=
    hdec_b.of_linearReduction hf_poly hf_corr ht_pos hf_vars hb_gt_one.le
  exact hkSETH (hksat_exp.mono hrate)

end LampisQCSPB

-- Private non-vacuity check on `baseExpFactor`
example : baseExpFactor 6 3 = 216 := by
  rw [baseExpFactor_eq_pow_of_one_le (by norm_num)]
  norm_num

end Cslib.Complexity
