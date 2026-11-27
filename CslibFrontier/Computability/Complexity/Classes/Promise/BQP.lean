/-
Copyright (c) 2026 The CslibFrontier contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The CslibFrontier contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.BPP
public import CslibFrontier.Computability.Complexity.Classes.BQP
public import CslibFrontier.Computability.Complexity.Classes.Promise.Reduction

import CslibFrontier.Computability.Complexity.Classes.BQP.Classical
import CslibFrontier.Computability.Complexity.Classes.BQP.ConstantGap
import CslibFrontier.Computability.Complexity.Classes.QMA.MA
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Foundations.Analysis.SpecialFunctions.ExpBounds

/-!
# Bounded-error quantum polynomial time on promise and gap problems

We define the promise-problem complexity class `PromiseBQP`, polynomial-time many-one
`BQPHard` and `BQPComplete` predicates for promise and gap problems, constant-gap amplification
for `PromiseBQP`, closure of `PromiseBPP` under deterministic polynomial-time promise reductions,
the collapse consequence `BPP = BQP` whenever a `BQP`-hard promise problem lies in `PromiseBPP`,
and gap-preserving perturbation reductions transferring `BQP`-hardness across bounded additive
perturbations of real-valued objectives.

## Main definitions

* `Cslib.Complexity.PromiseBQP`: promise problems solved with bounded error (`2 / 3` vs. `1 / 3`)
  by polynomial-time uniform families of quantum circuits (`Cslib.Quantum.UniformCircuitFamily`).
* `Cslib.Complexity.PromiseProblem.BQPHard`: polynomial-time many-one hardness of a promise
  problem for `Cslib.Complexity.BQP`.
* `Cslib.Complexity.PromiseProblem.BQPComplete`: membership in `PromiseBQP` together with
  `PromiseProblem.BQPHard`.
* `Cslib.Complexity.PromiseProblem.IsAdditiveApproxOn`: pointwise additive `ε`-approximation of a
  real-valued objective on a domain of instances.

## Main results

* `Cslib.Complexity.ofSet_mem_PromiseBQP`: decision problems belong to `PromiseBQP` if and only if
  they belong to `BQP`.
* `Cslib.Complexity.compl_mem_PromiseBQP`: `PromiseBQP` is closed under complement.
* `Cslib.Complexity.mem_PromiseBQP_of_gap`, `Cslib.Complexity.mem_PromiseBQP_iff_exists_gap`:
  constant-gap amplification for `PromiseBQP`.
* `Cslib.Complexity.PromiseP_subset_PromiseBQP`: deterministic polynomial-time promise problems
  lie in `PromiseBQP`.
* `Cslib.Complexity.PromiseProblem.PolyTimeReducible.mem_PromiseBPP`: `PromiseBPP` is closed under
  deterministic polynomial-time promise reductions.
* `Cslib.Complexity.PromiseProblem.BQPHard.BPP_eq_BQP_of_mem_PromiseBPP`: if a `BQP`-hard promise
  problem belongs to `PromiseBPP`, then `BPP enc = BQP enc` for every encoding `enc`.
* `Cslib.Complexity.PromiseProblem.polyTimeReducible_gapMax_of_abs_sub_le`,
  `Cslib.Complexity.PromiseProblem.BQPHard.gapMax_of_abs_sub_le`: bounded additive perturbations
  of a real-valued objective induce gap-preserving polynomial-time reductions and transfer
  `BQP`-hardness.
* `Cslib.Complexity.PromiseProblem.solvedBy_gapMax_of_isAdditiveApproxOn`: any additive
  `ε`-estimator separates yes- and no-instances of a gap problem with gap exceeding `2 * ε`.
-/

@[expose] public section

namespace Cslib.Complexity

open Cslib.Complexity.PromiseProblem Cslib.Quantum Turing.MultiTapeTM

section PromiseBQPClass

variable {α : Type} {enc : α ↪ List Bool} {Q : PromiseProblem α} {A : Set α}

/-- The class `PromiseBQP` of promise problems solved with bounded error by polynomial-time uniform
families of quantum circuits over Hadamard, NOT, CNOT, and Toffoli gates: yes-instances are
accepted with probability at least `2 / 3`, and no-instances with probability at most `1 / 3`. -/
def PromiseBQP (enc : α ↪ List Bool) : Set (PromiseProblem α) :=
  {Q | ∃ F : UniformCircuitFamily, ∀ a,
    (a ∈ Q.yes → 2 / 3 ≤ F.acceptProb (enc a)) ∧
      (a ∈ Q.no → F.acceptProb (enc a) ≤ 1 / 3)}

/-- Membership characterization for `PromiseBQP`. -/
theorem mem_PromiseBQP_iff :
    Q ∈ PromiseBQP enc ↔ ∃ F : UniformCircuitFamily, ∀ a,
      (a ∈ Q.yes → 2 / 3 ≤ F.acceptProb (enc a)) ∧
        (a ∈ Q.no → F.acceptProb (enc a) ≤ 1 / 3) :=
  Iff.rfl

/-- A decision problem belongs to `PromiseBQP` if and only if it belongs to `BQP`. -/
@[simp]
theorem ofSet_mem_PromiseBQP : ofSet A ∈ PromiseBQP enc ↔ A ∈ BQP enc :=
  Iff.rfl

/-- `PromiseBQP` is closed under complement: appending a final NOT gate on qubit `0` exchanges
acceptance and rejection probabilities. -/
theorem compl_mem_PromiseBQP (hQ : Q ∈ PromiseBQP enc) : Qᶜ ∈ PromiseBQP enc := by
  obtain ⟨F, hF⟩ := hQ
  refine ⟨F.appendNot, fun a ↦ ⟨fun ha ↦ ?_, fun ha ↦ ?_⟩⟩
  · have hno := (hF a).2 ha
    rw [UniformCircuitFamily.acceptProb_appendNot]
    linarith
  · have hyes := (hF a).1 ha
    rw [UniformCircuitFamily.acceptProb_appendNot]
    linarith

/-- `PromiseBQP` from any constant gap: if a polynomial-time uniform quantum circuit family accepts
every yes-instance with probability at least `c` and every no-instance with probability at most
`s`, for constants `s < c`, then the promise problem belongs to `PromiseBQP`. -/
theorem mem_PromiseBQP_of_gap {s c : ℝ} (hsc : s < c) (F : UniformCircuitFamily)
    (hF : ∀ a, (a ∈ Q.yes → c ≤ F.acceptProb (enc a)) ∧
      (a ∈ Q.no → F.acceptProb (enc a) ≤ s)) :
    Q ∈ PromiseBQP enc := by
  rcases lt_or_ge s 0 with hs | hs
  · have hno_empty : ∀ a, a ∉ Q.no := fun a ha ↦ by
      linarith [(hF a).2 ha, F.acceptProb_nonneg (enc a)]
    have h0 : ComputableInPolyTime (fun _ : ℕ ↦ (0 : ℕ)) encUnary encUnary := .const _
    refine ⟨(F.threshold (fun _ ↦ 0) (fun _ ↦ 0) h0 h0).appendNot,
      fun a ↦ ⟨fun _ ↦ ?_, fun ha ↦ absurd ha (hno_empty a)⟩⟩
    rw [UniformCircuitFamily.acceptProb_appendNot,
      UniformCircuitFamily.acceptProb_threshold_eq_sum_choose]
    norm_num [Finset.filter_singleton]
  set δ := (c - s) / 2 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  set K : ℕ := ⌈1 / δ ^ 2⌉₊
  set T : ℕ := ⌊(K : ℝ) * ((s + c) / 2)⌋₊
  have hKδ : 1 ≤ (K : ℝ) * δ ^ 2 := (div_le_iff₀ (by positivity)).mp (Nat.le_ceil (1 / δ ^ 2))
  have hexp : Real.exp (-2 * (K : ℝ) * δ ^ 2) ≤ 1 / 3 :=
    (Real.exp_le_exp.mpr (by nlinarith)).trans Real.exp_neg_two_le_one_third
  have hK : ComputableInPolyTime (fun _ : ℕ ↦ K) encUnary encUnary := .const _
  have hT : ComputableInPolyTime (fun _ : ℕ ↦ T) encUnary encUnary := .const _
  refine ⟨F.threshold (fun _ ↦ K) (fun _ ↦ T) hK hT, fun a ↦ ⟨fun ha ↦ ?_, fun ha ↦ ?_⟩⟩
  · have hacc := F.one_sub_exp_le_acceptProb_threshold hK hT (enc a) hδ0.le <| by
      have hfl := Nat.floor_le (mul_nonneg (Nat.cast_nonneg K) (by linarith : 0 ≤ (s + c) / 2))
      nlinarith [(hF a).1 ha, (Nat.cast_nonneg K : (0 : ℝ) ≤ K)]
    linarith
  · refine (F.acceptProb_threshold_le_exp hK hT (enc a) hδ0.le ?_).trans hexp
    have hfl := Nat.lt_floor_add_one ((K : ℝ) * ((s + c) / 2))
    nlinarith [(hF a).2 ha, (Nat.cast_nonneg K : (0 : ℝ) ≤ K)]

/-- Constant-gap characterization of `PromiseBQP`. -/
theorem mem_PromiseBQP_iff_exists_gap :
    Q ∈ PromiseBQP enc ↔ ∃ s c : ℝ, s < c ∧ ∃ F : UniformCircuitFamily, ∀ a,
      (a ∈ Q.yes → c ≤ F.acceptProb (enc a)) ∧
        (a ∈ Q.no → F.acceptProb (enc a) ≤ s) :=
  ⟨fun ⟨F, hF⟩ ↦ ⟨1 / 3, 2 / 3, by norm_num, F, hF⟩,
    fun ⟨_, _, hsc, F, hF⟩ ↦ mem_PromiseBQP_of_gap hsc F hF⟩

/-- Every promise problem in `PromiseP` belongs to `PromiseBQP`. -/
theorem PromiseP_subset_PromiseBQP : PromiseP enc ⊆ PromiseBQP enc := by
  intro Q hQ
  obtain ⟨f, hf, hyes, hno⟩ := mem_PromiseP_iff.mp hQ
  obtain ⟨F, hF⟩ := exists_uniformCircuitFamily hf
  refine ⟨F, fun a ↦ ⟨fun ha ↦ ?_, fun ha ↦ ?_⟩⟩
  · rw [hF, hyes a ha]; norm_num
  · rw [hF, hno a ha]; norm_num

end PromiseBQPClass

namespace PromiseProblem

/-- `PromiseBPP` is closed under deterministic polynomial-time promise reductions. -/
theorem PolyTimeReducible.mem_PromiseBPP {α β : Type}
    {encA : α ↪ List Bool} {encB : β ↪ List Bool}
    {X : PromiseProblem α} {Y : PromiseProblem β}
    (hXY : PolyTimeReducible encA encB X Y)
    (hY : Y ∈ PromiseBPP encB) : X ∈ PromiseBPP encA := by
  obtain ⟨f, hf, hfyes, hfno⟩ := hXY
  obtain ⟨p, V, hV, hsol⟩ := mem_PromiseBPP_iff.mp hY
  obtain ⟨c, d, hlen⟩ := hf.polyBounded_length.exists_le
  let q : Polynomial ℕ := p.comp (Polynomial.C c * (Polynomial.X + 1) ^ d)
  let W : α × List Bool → Bool :=
    fun x ↦ V (f x.1, x.2.take (p.eval (encB (f x.1)).length))
  have hW : ComputableInPolyTime W (encPair encA encBits) encBool := by
    dsimp only [W]
    have hf1 : ComputableInPolyTime (fun x : α × List Bool ↦ f x.1)
        (encPair encA encBits) encB := hf.comp (.fst encA encBits)
    have hp_eval : ComputableInPolyTime
        (fun x : α × List Bool ↦ p.eval (encB (f x.1)).length)
        (encPair encA encBits) encUnary :=
      (ComputableInPolyTime.unary_eval p).comp
        ((ComputableInPolyTime.encoding_length encB).comp hf1)
    have htake : ComputableInPolyTime
        (fun x : α × List Bool ↦ x.2.take (p.eval (encB (f x.1)).length))
        (encPair encA encBits) encBits := by
      fun_prop
    exact hV.comp (hf1.prod htake)
  have hle_q : ∀ a : α, p.eval (encB (f a)).length ≤ q.eval (encA a).length := by
    intro a
    simp only [q, Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]
    have hmono : ∀ r : Polynomial ℕ, Monotone (fun n : ℕ ↦ r.eval n) := by
      intro r
      induction r using Polynomial.induction_on' with
      | add p₁ p₂ ih₁ ih₂ =>
        intro m n hmn
        simp only [Polynomial.eval_add]
        exact Nat.add_le_add (ih₁ hmn) (ih₂ hmn)
      | monomial k s =>
        intro m n hmn
        simp only [Polynomial.eval_monomial]
        exact Nat.mul_le_mul_left s (Nat.pow_le_pow_left hmn k)
    exact hmono p (hlen a)
  have hcount : ∀ (a : α) (b : Bool),
      BoundedErrorAt encB p V (f a) b → BoundedErrorAt encA q W a b := by
    intro a b hb
    set m := p.eval (encB (f a)).length
    set M := q.eval (encA a).length
    have hmM : m ≤ M := hle_q a
    let split : (Fin M → Bool) ≃ (Fin m → Bool) × (Fin (M - m) → Bool) :=
      (Equiv.arrowCongr (finCongr (Nat.add_sub_of_le hmM).symm) (Equiv.refl Bool)).trans
        (Fin.appendEquiv m (M - m)).symm
    have htake_eq : ∀ r : Fin M → Bool,
        (List.ofFn r).take m = List.ofFn (split r).1 := by
      intro r
      apply List.ext_getElem
      · simp [hmM]
      · intro i hi₁ hi₂
        simp only [List.length_ofFn] at hi₂
        simp [split, Fin.appendEquiv, Fin.castAdd]
    have hcard : (Finset.univ.filter fun r : Fin M → Bool ↦ W (a, List.ofFn r) = b).card =
        (Finset.univ.filter fun r₁ : Fin m → Bool ↦ V (f a, List.ofFn r₁) = b).card *
          2 ^ (M - m) := by
      let S₁ := Finset.univ.filter fun r₁ : Fin m → Bool ↦ V (f a, List.ofFn r₁) = b
      let S₂ : Finset (Fin (M - m) → Bool) := Finset.univ
      have hbij : (Finset.univ.filter fun r : Fin M → Bool ↦ W (a, List.ofFn r) = b).card =
          (S₁ ×ˢ S₂).card := by
        refine Finset.card_bij (fun r _ ↦ split r) (fun r hr ↦ ?_)
          (fun _ _ _ _ h ↦ split.injective h) fun p hp ↦ ?_
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr
          have hr' : V (f a, List.ofFn (split r).1) = b := by
            change V (f a, (List.ofFn r).take m) = b at hr
            rwa [htake_eq r] at hr
          exact Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr'⟩,
            Finset.mem_univ _⟩
        · refine ⟨split.symm p, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩,
            split.apply_symm_apply p⟩
          have hp₁ : V (f a, List.ofFn p.1) = b :=
            (Finset.mem_filter.mp (Finset.mem_product.mp hp).1).2
          change V (f a, (List.ofFn (split.symm p)).take m) = b
          rw [htake_eq (split.symm p), split.apply_symm_apply]
          exact hp₁
      rw [hbij, Finset.card_product]
      simp [S₁, S₂]
    change 2 * 2 ^ M ≤ 3 * (Finset.univ.filter fun r : Fin M → Bool ↦ W (a, List.ofFn r) = b).card
    rw [hcard, show 2 ^ M = 2 ^ m * 2 ^ (M - m) by rw [← pow_add, Nat.add_sub_of_le hmM]]
    have hb' : 2 * 2 ^ m ≤
        3 * (Finset.univ.filter fun r₁ : Fin m → Bool ↦ V (f a, List.ofFn r₁) = b).card := hb
    calc 2 * (2 ^ m * 2 ^ (M - m)) = (2 * 2 ^ m) * 2 ^ (M - m) := by ring
      _ ≤ (3 * (Finset.univ.filter fun r₁ : Fin m → Bool ↦
            V (f a, List.ofFn r₁) = b).card) * 2 ^ (M - m) :=
          Nat.mul_le_mul_right _ hb'
      _ = 3 * ((Finset.univ.filter fun r₁ : Fin m → Bool ↦
            V (f a, List.ofFn r₁) = b).card * 2 ^ (M - m)) := by ring
  exact ⟨q, W, hW, fun a ↦
    ⟨fun ha ↦ hcount a true ((hsol (f a)).1 (hfyes ha)),
      fun ha ↦ hcount a false ((hsol (f a)).2 (hfno ha))⟩⟩

variable {α β : Type*} {encA : α ↪ List Bool} {encB : β ↪ List Bool}

/-- A promise problem `Y` is `BQP`-hard under deterministic polynomial-time many-one reductions
when every decision problem in `BQP`, under every instance encoding, reduces in polynomial time to
`Y`. -/
def BQPHard (encB : β ↪ List Bool) (Y : PromiseProblem β) : Prop :=
  HardUnder (fun enc A Y ↦ PolyTimeReducible enc encB (ofSet A) Y) @BQP Y

/-- A promise problem `Y` is `BQP`-complete when it belongs to `PromiseBQP` and is `BQPHard`. -/
def BQPComplete {β : Type} (encB : β ↪ List Bool) (Y : PromiseProblem β) : Prop :=
  Y ∈ PromiseBQP encB ∧ BQPHard encB Y

/-- Explicit quantifier characterization of `BQPHard`. -/
theorem bqpHard_iff {Y : PromiseProblem β} :
    BQPHard encB Y ↔ ∀ {α : Type} (enc : α ↪ List Bool) (A : Set α),
      A ∈ BQP enc → PolyTimeReducible enc encB (ofSet A) Y :=
  Iff.rfl

/-- On decision problems, `PromiseProblem.BQPHard` agrees with `PolyTimeHard @BQP`. -/
theorem bqpHard_ofSet_iff {B : Set β} :
    BQPHard encB (ofSet B) ↔ Complexity.PolyTimeHard @BQP encB B :=
  ⟨fun h _ enc A hA ↦ polyTimeReducible_ofSet_iff.mp (h enc A hA),
    fun h _ enc A hA ↦ polyTimeReducible_ofSet_iff.mpr (h enc A hA)⟩

/-- `BQP`-hardness transfers along deterministic polynomial-time promise reductions. -/
theorem BQPHard.trans {X : PromiseProblem α} {Y : PromiseProblem β}
    (hX : BQPHard encA X) (hXY : PolyTimeReducible encA encB X Y) :
    BQPHard encB Y :=
  HardUnder.trans (fun _ _ h₁ h₂ ↦ h₁.trans h₂) hX hXY

/-- Enlarging yes- and no-sets preserves `BQP`-hardness. -/
theorem BQPHard.mono {Y Y' : PromiseProblem β} (hY : BQPHard encB Y)
    (hyes : Y.yes ⊆ Y'.yes) (hno : Y.no ⊆ Y'.no) : BQPHard encB Y' :=
  hY.trans (.of_subset hyes hno)

/-- Every language separating the yes- and no-instances of a `BQP`-hard promise problem is
`BQP`-hard. -/
theorem BQPHard.bqpHard_of_subset {Y : PromiseProblem β} (hY : BQPHard encB Y)
    {B : Set β} (hyes : Y.yes ⊆ B) (hno : Disjoint B Y.no) :
    Complexity.PolyTimeHard @BQP encB B :=
  bqpHard_ofSet_iff.mp (hY.mono hyes (Set.subset_compl_iff_disjoint_left.mpr hno))

/-- If a `BQP`-hard promise problem belongs to `PromiseBPP`, then `BQP ⊆ BPP` for every instance
encoding. -/
theorem BQPHard.BQP_subset_BPP_of_mem_PromiseBPP {β : Type} {encB : β ↪ List Bool}
    {Y : PromiseProblem β} (hY : BQPHard encB Y) (hBPP : Y ∈ PromiseBPP encB)
    {α : Type} (enc : α ↪ List Bool) : BQP enc ⊆ BPP enc :=
  fun A hA ↦ ofSet_mem_PromiseBPP.mp ((hY enc A hA).mem_PromiseBPP hBPP)

/-- If a `BQP`-hard promise problem belongs to `PromiseBPP`, then `BPP = BQP` for every instance
encoding. -/
theorem BQPHard.BPP_eq_BQP_of_mem_PromiseBPP {β : Type} {encB : β ↪ List Bool}
    {Y : PromiseProblem β} (hY : BQPHard encB Y) (hBPP : Y ∈ PromiseBPP encB)
    {α : Type} (enc : α ↪ List Bool) : BPP enc = BQP enc :=
  BPP_subset_BQP.antisymm (hY.BQP_subset_BPP_of_mem_PromiseBPP hBPP enc)

/-- Unless `BPP = BQP`, no `BQP`-hard promise problem belongs to `PromiseBPP`. -/
theorem BQPHard.notMem_PromiseBPP {β : Type} {encB : β ↪ List Bool}
    {Y : PromiseProblem β} (hY : BQPHard encB Y) {α : Type} {enc : α ↪ List Bool}
    (hne : BPP enc ≠ BQP enc) : Y ∉ PromiseBPP encB :=
  fun hBPP ↦ hne (hY.BPP_eq_BQP_of_mem_PromiseBPP hBPP enc)

/-- Gap-preserving reduction under bounded additive perturbation: if a polynomial-time map
`f : α → β` relates two real-valued objectives `val` and `val'` with
`|val' (f a) - val a| ≤ δ a` and preserves strictly separated completeness and soundness
thresholds, then `f` is a polynomial-time promise reduction from `gapMax val c s` to
`gapMax val' c' s'`. -/
theorem polyTimeReducible_gapMax_of_abs_sub_le
    {val c s δ : α → ℝ} {val' c' s' : β → ℝ} {f : α → β}
    (hf : ComputableInPolyTime f encA encB)
    (hpert : ∀ a, |val' (f a) - val a| ≤ δ a)
    (hc : ∀ a, c a ≤ val a → c' (f a) ≤ c a - δ a)
    (hs : ∀ a, s a < c a → s a + δ a ≤ s' (f a) ∧ s' (f a) < c' (f a)) :
    PolyTimeReducible encA encB (gapMax val c s) (gapMax val' c' s') := by
  refine ⟨f, hf, fun a ha ↦ ?_, fun a ha ↦ ?_⟩
  · simp only [mem_yes_gapMax] at ha ⊢
    have hp := (abs_le.mp (hpert a)).1
    linarith [hc a ha]
  · simp only [mem_no_gapMax] at ha ⊢
    have hp := (abs_le.mp (hpert a)).2
    obtain ⟨hs₁, hs₂⟩ := hs a ha.2
    exact ⟨by linarith [ha.1], hs₂⟩

/-- Transfer of `BQP`-hardness across bounded additive objective perturbations. -/
theorem BQPHard.gapMax_of_abs_sub_le
    {val c s δ : α → ℝ} {val' c' s' : β → ℝ} {f : α → β}
    (hhard : BQPHard encA (gapMax val c s))
    (hf : ComputableInPolyTime f encA encB)
    (hpert : ∀ a, |val' (f a) - val a| ≤ δ a)
    (hc : ∀ a, c a ≤ val a → c' (f a) ≤ c a - δ a)
    (hs : ∀ a, s a < c a → s a + δ a ≤ s' (f a) ∧ s' (f a) < c' (f a)) :
    BQPHard encB (gapMax val' c' s') :=
  hhard.trans (polyTimeReducible_gapMax_of_abs_sub_le hf hpert hc hs)

/-- Pointwise additive `ε`-approximation of a real-valued objective `val` on a domain `S`. -/
def IsAdditiveApproxOn (val ε est : β → ℝ) (S : Set β) : Prop :=
  ∀ b ∈ S, |est b - val b| ≤ ε b

/-- Any additive `ε`-approximation on the promise of `gapMax val c s` with gap
`c b - s b > 2 * ε b` decides `gapMax val c s` via midpoint thresholding. -/
theorem solvedBy_gapMax_of_isAdditiveApproxOn
    {val c s ε est : β → ℝ}
    (hest : IsAdditiveApproxOn val ε est (gapMax val c s).promise)
    (hgap : ∀ b ∈ (gapMax val c s).promise, s b + 2 * ε b < c b) :
    ∃ dec : β → Bool, (gapMax val c s).SolvedBy dec := by
  classical
  refine ⟨fun b ↦ decide ((c b + s b) / 2 ≤ est b), fun b hb ↦ ?_, fun b hb ↦ ?_⟩
  · have hmem : b ∈ (gapMax val c s).promise := Or.inl hb
    have hap := (abs_le.mp (hest b hmem)).1
    have hg := hgap b hmem
    simp only [mem_yes_gapMax] at hb
    exact decide_eq_true (by linarith)
  · have hmem : b ∈ (gapMax val c s).promise := Or.inr hb
    have hap := (abs_le.mp (hest b hmem)).2
    have hg := hgap b hmem
    simp only [mem_no_gapMax] at hb
    exact decide_eq_false (by linarith [hb.1])

end PromiseProblem

end Cslib.Complexity
