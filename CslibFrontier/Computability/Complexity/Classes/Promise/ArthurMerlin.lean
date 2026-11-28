/-
Copyright (c) 2026 Google DeepMind. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Google DeepMind
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.ArthurMerlin
public import CslibFrontier.Computability.Complexity.Classes.Promise.Reduction
public import CslibFrontier.Computability.Complexity.Classes.QMA
import CslibFrontier.Computability.Complexity.Classes.QMA.MA
import CslibFrontier.Computability.Complexity.Classes.TruncatedVerifier
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# Promise Merlin–Arthur complexity (`PromiseMA`)

The public-coin Merlin–Arthur class `Cslib.Complexity.MA` lifts to promise problems
(`Cslib.Complexity.PromiseProblem`) by requiring two-thirds completeness on yes-instances and
one-third soundness on no-instances, leaving instances outside the promise unconstrained
[Goldreich], [Bravyi and Terhal]:

* `PromiseProblem.IsMerlinArthurVerifier` and `PromiseMA` extend `IsMerlinArthurVerifier` and `MA`
  so that `ofSet A ∈ PromiseMA enc ↔ A ∈ MA enc` holds definitionally (`ofSet_mem_PromiseMA`).
* `PromiseNP_subset_PromiseMA`, `PromiseBPP_subset_PromiseMA` and `PromiseMA_subset_PromiseQMA`
  extend the containments `NP ⊆ MA`, `BPP ⊆ MA` and `MA ⊆ QMA` to promise problems.
* `PromiseProblem.PolyTimeReducible.mem_PromiseMA` proves closure of `PromiseMA` under
  deterministic polynomial-time promise reductions.
* `PromiseProblem.MAHard` and `PromiseProblem.MAComplete` formalize `MA`-hardness and
  `MA`-completeness of promise problems (such as Stoquastic Local Hamiltonian), and
  `PromiseProblem.MAHard.MA_eq_NP_of_mem_PromiseNP` proves that placing an `MA`-hard promise
  problem in `PromiseNP` collapses `MA = NP`.

## Main definitions

* `Cslib.Complexity.PromiseProblem.IsMerlinArthurVerifier`, `Cslib.Complexity.PromiseMA`.
* `Cslib.Complexity.PromiseProblem.MAHard`, `Cslib.Complexity.PromiseProblem.MAComplete`.

## Main results

* `Cslib.Complexity.ofSet_mem_PromiseMA`: `ofSet A ∈ PromiseMA enc ↔ A ∈ MA enc`.
* `Cslib.Complexity.PromiseNP_subset_PromiseMA`, `Cslib.Complexity.PromiseBPP_subset_PromiseMA`,
  `Cslib.Complexity.PromiseMA_subset_PromiseQMA`.
* `Cslib.Complexity.PromiseProblem.PolyTimeReducible.mem_PromiseMA`: closure under reductions.
* `Cslib.Complexity.PromiseProblem.MAHard.MA_eq_NP_of_mem_PromiseNP`: `MA = NP` from an `MA`-hard
  promise problem in `PromiseNP`.
-/

public section

namespace Cslib.Complexity

open Finset Turing.MultiTapeTM Quantum PromiseProblem

section PromiseMA

variable {α β : Type} {enc : α ↪ List Bool} {encB : β ↪ List Bool}
  {Q : PromiseProblem α} {Y : PromiseProblem β} {A : Set α}

/-- `V` is a Merlin–Arthur verifier for the promise problem `Q`, with proofs of length `q` and
random strings of length `p`, both evaluated at the length of the encoded instance: on every
yes-instance some proof makes at least two thirds of the random strings accepted, and on every
no-instance every proof leaves at least two thirds of the random strings rejected. -/
@[expose] def PromiseProblem.IsMerlinArthurVerifier (enc : α ↪ List Bool) (q p : Polynomial ℕ)
    (V : α × List Bool → Bool) (Q : PromiseProblem α) : Prop :=
  ∀ a, (a ∈ Q.yes → ∃ y : Fin (q.eval (enc a).length) → Bool,
      BoundedErrorAt enc p (fun z => V (z.1, List.ofFn y ++ z.2)) a true) ∧
    (a ∈ Q.no → ∀ y : Fin (q.eval (enc a).length) → Bool,
      BoundedErrorAt enc p (fun z => V (z.1, List.ofFn y ++ z.2)) a false)

/-- The promise problems with polynomial-time Merlin–Arthur verifiers, with polynomially long
proofs and random strings, with respect to the encoding `enc` of instances. -/
@[expose] def PromiseMA (enc : α ↪ List Bool) : Set (PromiseProblem α) :=
  {Q | ∃ (q p : Polynomial ℕ) (V : α × List Bool → Bool),
    ComputableInPolyTime V (encPair enc encBits) encBool ∧ Q.IsMerlinArthurVerifier enc q p V}

/-- Membership in `PromiseMA` unfolded. -/
theorem mem_PromiseMA_iff : Q ∈ PromiseMA enc ↔ ∃ (q p : Polynomial ℕ) (V : α × List Bool → Bool),
    ComputableInPolyTime V (encPair enc encBits) encBool ∧ Q.IsMerlinArthurVerifier enc q p V :=
  Iff.rfl

/-- A decision problem, as a promise problem, is in `PromiseMA` exactly when it is in `MA`. -/
@[simp]
theorem ofSet_mem_PromiseMA : ofSet A ∈ PromiseMA enc ↔ A ∈ MA enc :=
  Iff.rfl

private theorem two_mul_two_pow_le_card_filter_of_eq_zero {m : ℕ} (hm : m = 0)
    (g : (Fin m → Bool) → Prop) [DecidablePred g] (h : ∀ r, g r) :
    2 * 2 ^ m ≤ 3 * (univ.filter g).card := by
  subst hm
  rw [filter_true_of_mem fun r _ => h r]
  simp

/-- **`PromiseNP ⊆ PromiseMA`**: a `PromiseNP` verifier is a Merlin–Arthur verifier flipping no
coins. -/
theorem PromiseNP_subset_PromiseMA : PromiseNP enc ⊆ PromiseMA enc := by
  intro Q hQ
  obtain ⟨p, V, hV, hyes, hno⟩ := mem_PromiseNP_iff.mp hQ
  refine ⟨p, 0, V, hV, fun a => ⟨fun ha => ?_, fun ha y => ?_⟩⟩
  · obtain ⟨w, hw, hVw⟩ := hyes a ha
    refine ⟨BitString.ofList _ w, two_mul_two_pow_le_card_filter_of_eq_zero
      Polynomial.eval_zero _ fun r => ?_⟩
    dsimp only
    rw [BitString.ofFn_ofList hw,
      List.eq_nil_of_length_eq_zero (by simp : (List.ofFn r).length = 0), List.append_nil, hVw]
  · refine two_mul_two_pow_le_card_filter_of_eq_zero Polynomial.eval_zero _ fun r => ?_
    dsimp only
    rw [List.eq_nil_of_length_eq_zero (by simp : (List.ofFn r).length = 0), List.append_nil]
    exact hno a ha (List.ofFn y) List.length_ofFn

/-- **`PromiseBPP ⊆ PromiseMA`**: a bounded-error promise solver is a Merlin–Arthur verifier
reading no proof. -/
theorem PromiseBPP_subset_PromiseMA : PromiseBPP enc ⊆ PromiseMA enc := by
  rintro Q ⟨p, V, hV, hQ⟩
  have hnil (a : α) (y : Fin ((0 : Polynomial ℕ).eval (enc a).length) → Bool) :
      List.ofFn y = [] :=
    List.eq_nil_of_length_eq_zero (by simp)
  refine ⟨0, p, V, hV, fun a => ⟨fun ha => ⟨fun _ => false, ?_⟩, fun ha y => ?_⟩⟩
  · simpa only [hnil, List.nil_append] using (hQ a).1 ha
  · simpa only [hnil, List.nil_append] using (hQ a).2 ha

private theorem two_thirds_le_div {m c : ℕ} (h : 2 * 2 ^ m ≤ 3 * c) :
    (2 / 3 : ℝ) ≤ c / 2 ^ m := by
  rw [le_div_iff₀ (by positivity)]
  linarith [show (2 * 2 ^ m : ℝ) ≤ 3 * c from mod_cast h]

private theorem div_le_one_third {m : ℕ} (g : (Fin m → Bool) → Bool)
    (h : 2 * 2 ^ m ≤ 3 * (univ.filter fun r => g r = false).card) :
    ((univ.filter fun r => g r = true).card / 2 ^ m : ℝ) ≤ 1 / 3 := by
  have hsum := card_filter_add_card_filter_not (s := univ) fun r => g r = true
  simp only [Bool.not_eq_true, card_univ, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_bool] at hsum
  rw [div_le_iff₀ (by positivity)]
  linarith [show (2 * 2 ^ m : ℝ) ≤ 3 * #(univ.filter fun r => g r = false) from mod_cast h,
    show (#(univ.filter fun r => g r = true) : ℝ) + #(univ.filter fun r => g r = false) = 2 ^ m
      from mod_cast hsum]

/-- **`PromiseMA ⊆ PromiseQMA`**: simulating Arthur's coins with Hadamard gates gives a quantum
Merlin–Arthur verifier for every promise problem in `PromiseMA`. -/
theorem PromiseMA_subset_PromiseQMA :
    PromiseMA enc ⊆ PromiseQMA (fun _ => 2 / 3) (fun _ => 1 / 3) enc := by
  rintro Q ⟨q, p, V, hV, hQ⟩
  obtain ⟨F, hF⟩ := exists_uniformCircuitFamily hV
  refine ⟨UniformVerifierFamily.ofMA F q p, fun a => ⟨fun ha => ?_, fun ha ψ hψ => ?_⟩⟩
  · obtain ⟨y, hy⟩ := (hQ a).1 ha
    exact ⟨ket y, norm_ket _, (two_thirds_le_div hy).trans_eq
      (UniformVerifierFamily.acceptProb_ofMA_ket F q p (enc a) _ (fun w _ => hF (a, w)) y).symm⟩
  · exact UniformVerifierFamily.acceptProb_ofMA_le F q p (enc a) _ (fun w _ => hF (a, w))
      (fun y => div_le_one_third _ ((hQ a).2 ha y)) ψ hψ

private theorem exists_truncated_verifier_two_blocks {f : α → β}
    (hf : ComputableInPolyTime f enc encB) (p₁ p₂ : Polynomial ℕ)
    {V : β × List Bool → Bool}
    (hV : ComputableInPolyTime V (encPair encB encBits) encBool) :
    ∃ (P₁ P₂ : Polynomial ℕ) (V' : α × List Bool → Bool),
      ComputableInPolyTime V' (encPair enc encBits) encBool ∧
      (∀ a, p₁.eval (encB (f a)).length ≤ P₁.eval (enc a).length) ∧
      (∀ a, p₂.eval (encB (f a)).length ≤ P₂.eval (enc a).length) ∧
      ∀ (a : α) (u : Fin (P₁.eval (enc a).length) → Bool)
        (v : Fin (P₂.eval (enc a).length) → Bool),
        V' (a, List.ofFn u ++ List.ofFn v) =
          V (f a, (List.ofFn u).take (p₁.eval (encB (f a)).length) ++
            (List.ofFn v).take (p₂.eval (encB (f a)).length)) := by
  obtain ⟨P₁, T₁, hT₁, hP₁, hT₁e⟩ := exists_truncated_verifier hf p₁ (.snd encB encBits)
  obtain ⟨P₂, T₂, hT₂, hP₂, hT₂e⟩ := exists_truncated_verifier hf p₂ (.snd encB encBits)
  have hP₁u : ComputableInPolyTime (fun a => P₁.eval (enc a).length) enc encUnary :=
    (ComputableInPolyTime.unary_eval P₁).comp (ComputableInPolyTime.encoding_length enc)
  refine ⟨P₁, P₂, fun x => V (f x.1, T₁ x ++ T₂ (x.1, x.2.drop (P₁.eval (enc x.1).length))),
    hV.comp ((hf.comp (.fst enc encBits)).prod (.bitsAppend hT₁
      (hT₂.comp ((ComputableInPolyTime.fst enc encBits).prod
        (.bitsDropWithInput (.snd enc encBits) (hP₁u.comp (.fst enc encBits))))))),
    hP₁, hP₂, fun a u v => ?_⟩
  simp only [hT₁e, hT₂e]
  rw [List.take_append_of_le_length (by simpa using hP₁ a), List.drop_left' List.length_ofFn]

/-- **`PromiseMA` is closed under polynomial-time promise reductions.** -/
theorem PromiseProblem.PolyTimeReducible.mem_PromiseMA
    (h : PromiseProblem.PolyTimeReducible enc encB Q Y) (hY : Y ∈ PromiseMA encB) :
    Q ∈ PromiseMA enc := by
  obtain ⟨f, hf, hyes, hno⟩ := h
  obtain ⟨q, p, V, hV, hVY⟩ := hY
  obtain ⟨Q', P', V', hV', hQe, hPe, hsplit⟩ := exists_truncated_verifier_two_blocks hf q p hV
  refine ⟨Q', P', V', hV', fun a => ?_⟩
  dsimp only [BoundedErrorAt]
  simp only [hsplit]
  refine ⟨fun ha => ?_, fun ha y => ?_⟩
  · obtain ⟨y, hy⟩ := (hVY (f a)).1 (hyes ha)
    refine ⟨BitString.ofList _ (List.ofFn y), ?_⟩
    rw [BitString.take_ofFn_ofList (hQe a)]
    exact BitString.mul_two_pow_le_mul_card_filter_take (hPe a)
      (fun w => V (f a, List.ofFn y ++ w) = true) hy
  · have hy := (hVY (f a)).2 (hno ha)
      (BitString.ofList _ ((List.ofFn y).take (q.eval (encB (f a)).length)))
    rw [BitString.ofFn_ofList (by simp [hQe a])] at hy
    exact BitString.mul_two_pow_le_mul_card_filter_take (hPe a)
      (fun w => V (f a, (List.ofFn y).take (q.eval (encB (f a)).length) ++ w) = false) hy

end PromiseMA

namespace PromiseProblem

variable {β γ : Type*} {encB : β ↪ List Bool} {encC : γ ↪ List Bool}
  {Y Y' : PromiseProblem β} {Z : PromiseProblem γ}

/-- A promise problem is **`MA`-hard** when every decision problem in `MA`, with any encoding of
its instances, reduces in polynomial time via `ofSet` to `Y`. -/
@[expose] def MAHard (encB : β ↪ List Bool) (Y : PromiseProblem β) : Prop :=
  HardUnder (fun enc A Y => PolyTimeReducible enc encB (ofSet A) Y) @MA Y

/-- On decision problems, `MA`-hardness as a promise problem is `PolyTimeHard @MA`. -/
theorem maHard_ofSet_iff {B : Set β} :
    MAHard encB (ofSet B) ↔ PolyTimeHard @MA encB B :=
  ⟨fun h _ enc A hA => polyTimeReducible_ofSet_iff.mp (h enc A hA),
    fun h _ enc A hA => polyTimeReducible_ofSet_iff.mpr (h enc A hA)⟩

/-- `MA`-hardness transfers along polynomial-time promise reductions. -/
theorem MAHard.trans (hY : MAHard encB Y) (hYZ : PolyTimeReducible encB encC Y Z) :
    MAHard encC Z :=
  HardUnder.trans (fun _ _ h₁ h₂ => h₁.trans h₂) hY hYZ

/-- Enlarging the promise preserves `MA`-hardness. -/
theorem MAHard.mono (hY : MAHard encB Y) (hyes : Y.yes ⊆ Y'.yes) (hno : Y.no ⊆ Y'.no) :
    MAHard encB Y' :=
  hY.trans (.of_subset hyes hno)

/-- A promise problem is **`MA`-complete** when it belongs to `PromiseMA` and is `MA`-hard. -/
@[expose] def MAComplete {β : Type} (encB : β ↪ List Bool) (Y : PromiseProblem β) : Prop :=
  Y ∈ PromiseMA encB ∧ Y.MAHard encB

/-- If an `MA`-hard promise problem belongs to `PromiseNP`, then `MA ⊆ NP` for every encoding of
instances. -/
theorem MAHard.MA_subset_NP_of_mem_PromiseNP {β : Type} {encB : β ↪ List Bool}
    {Y : PromiseProblem β} (hY : Y.MAHard encB) (h : Y ∈ PromiseNP encB)
    {α : Type} (enc : α ↪ List Bool) : MA enc ⊆ NP enc :=
  fun A hA => ofSet_mem_PromiseNP.mp ((hY enc A hA).mem_PromiseNP h)

/-- **An `MA`-hard promise problem in `PromiseNP` collapses `MA = NP`**, for every encoding of
instances. -/
theorem MAHard.MA_eq_NP_of_mem_PromiseNP {β : Type} {encB : β ↪ List Bool}
    {Y : PromiseProblem β} (hY : Y.MAHard encB) (h : Y ∈ PromiseNP encB)
    {α : Type} (enc : α ↪ List Bool) : MA enc = NP enc :=
  Set.Subset.antisymm (hY.MA_subset_NP_of_mem_PromiseNP h enc) NP_subset_MA

end PromiseProblem

end Cslib.Complexity
