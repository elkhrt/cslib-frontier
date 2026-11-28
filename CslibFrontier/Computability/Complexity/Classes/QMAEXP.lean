/-
Copyright (c) 2026 The FormalPapers contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalPapers contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Complexity.Classes.EXP
public import CslibFrontier.Computability.Complexity.Classes.Promise.Reduction
public import CslibFrontier.Computability.Complexity.Classes.QMA

import CslibFrontier.Computability.Circuit.Quantum.Parallel
import CslibFrontier.Computability.Complexity.Classes.QMA.NP
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.FunProp
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Mathlib.Data.List.GetD
import Mathlib.Tactic.Ring

/-!
# The class `QMA_EXP`

`QMA_EXP` (exponential-time quantum Merlin–Arthur) is the exponential-time analogue of `QMA`: an
exponential-time (`O(2 ^ |x| ^ k)`) uniform family of quantum circuits over the universal gate set
`{H, NOT, CNOT, Toffoli}` receives an exponential-size pure quantum witness state `ψ`, accepting
every yes-instance on some unit witness with probability at least `2 / 3` and accepting every
no-instance on every unit witness with probability at most `1 / 3`
.

## Main definitions

* `Cslib.Complexity.ExpVerifierSpec`: specification `(width, witnessLength, gates)` of an
  instance-indexed family of quantum verifier circuits.
* `Cslib.Complexity.ExpVerifierSpec.IsExpUniform`: deterministic `O(2 ^ |enc a| ^ k)` uniformity
  and well-formedness predicate.
* `Cslib.Complexity.ExpVerifierSpec.acceptProb`: acceptance probability on an instance and pure
  witness state.
* `Cslib.Complexity.PromiseProblem.IsQMAEXPVerifier`: completeness and soundness specification on
  a promise problem.
* `Cslib.Complexity.PromiseQMAEXP`, `Cslib.Complexity.PromiseQMAEXPStd`,
  `Cslib.Complexity.QMAEXP`: promise and decision classes.

## Main results

* `Cslib.Complexity.PromiseQMAEXP_mono`: weakening completeness and soundness bounds.
* `Cslib.Complexity.PromiseProblem.PolyTimeReducible.mem_PromiseQMAEXP`,
  `Cslib.Complexity.PolyTimeReducible.mem_QMAEXP`: closure under deterministic polynomial-time
  reductions.
* `Cslib.Complexity.EXP_subset_QMAEXP`, `Cslib.Complexity.P_ssubset_QMAEXP`: `EXP ⊆ QMAEXP` and
  unconditional strict separation `P ⊂ QMAEXP`.
* `Cslib.Complexity.PromiseQMA_subset_PromiseQMAEXP`, `Cslib.Complexity.QMA_subset_QMAEXP`,
  `Cslib.Complexity.BQP_subset_QMAEXP`, `Cslib.Complexity.NP_subset_QMAEXP`: containment of
  polynomial-time quantum and classical classes.
-/

public section

namespace Cslib.Complexity

open Cslib.Quantum Finset Turing.MultiTapeTM

/-- Specification of an instance-indexed family of quantum verifier circuits over the Hadamard,
NOT, CNOT, and Toffoli gate set (`Cslib.Quantum.GateCode`). -/
structure ExpVerifierSpec (α : Type) where
  /-- Total number of register qubits of the circuit `Q_a` on instance `a`. -/
  width : α → ℕ
  /-- Number of witness qubits read by `Q_a` on instance `a`. -/
  witnessLength : α → ℕ
  /-- Gate codes of `Q_a`, applied first to last. -/
  gates : α → List GateCode

namespace ExpVerifierSpec

variable {α : Type}

/-- Effective register width `max (V.width a) (V.witnessLength a)`. -/
@[expose] def regWidth (V : ExpVerifierSpec α) (a : α) : ℕ :=
  max (V.width a) (V.witnessLength a)

theorem witnessLength_le_regWidth (V : ExpVerifierSpec α) (a : α) :
    V.witnessLength a ≤ V.regWidth a :=
  le_max_right _ _

theorem regWidth_eq_width {V : ExpVerifierSpec α} {a : α} (h : V.witnessLength a ≤ V.width a) :
    V.regWidth a = V.width a :=
  max_eq_left h

/-- Deterministic exponential-time (`O(2 ^ |enc a| ^ k)`) uniformity and circuit well-formedness. -/
def IsExpUniform (enc : α ↪ List Bool) (V : ExpVerifierSpec α) : Prop :=
  (∃ k : ℕ,
    ComputableInO V.width enc encUnary
      (fun a => 2 ^ (enc a).length ^ k) (fun a => 2 ^ (enc a).length ^ k) ∧
    ComputableInO V.witnessLength enc encUnary
      (fun a => 2 ^ (enc a).length ^ k) (fun a => 2 ^ (enc a).length ^ k) ∧
    ComputableInO V.gates enc (encList encGateCode)
      (fun a => 2 ^ (enc a).length ^ k) (fun a => 2 ^ (enc a).length ^ k)) ∧
  (∀ a, 0 < V.width a) ∧
  (∀ a, V.witnessLength a ≤ V.width a) ∧
  ∀ a, ∀ g ∈ V.gates a, g.WellFormed (V.width a)

/-- Acceptance probability of `V` on instance `a` and pure witness state `ψ`. -/
noncomputable def acceptProb (V : ExpVerifierSpec α) (a : α)
    (ψ : Qubits (V.witnessLength a)) : ℝ :=
  measureProb (Circuit.eval (Circuit.ofCodes (V.regWidth a) (V.gates a))
    (embedState (blockEmb 0 (by simpa using V.witnessLength_le_regWidth a))
      (fun _ => false) ψ))
    (accepting (V.regWidth a))

theorem acceptProb_nonneg (V : ExpVerifierSpec α) (a : α) (ψ : Qubits (V.witnessLength a)) :
    0 ≤ V.acceptProb a ψ :=
  measureProb_nonneg _ _

theorem acceptProb_le_norm_sq (V : ExpVerifierSpec α) (a : α) (ψ : Qubits (V.witnessLength a)) :
    V.acceptProb a ψ ≤ ‖ψ‖ ^ 2 := by
  refine (measureProb_le_measureProb_univ _ _).trans_eq ?_
  rw [measureProb_univ, LinearIsometryEquiv.norm_map, LinearIsometry.norm_map]

theorem acceptProb_smul (V : ExpVerifierSpec α) (a : α) (c : ℂ)
    (ψ : Qubits (V.witnessLength a)) :
    V.acceptProb a (c • ψ) = ‖c‖ ^ 2 * V.acceptProb a ψ := by
  rw [acceptProb, map_smul, map_smul, measureProb_smul, acceptProb]

/-- Pull an `ExpVerifierSpec` back along `f : α → β`. -/
@[expose] def comap {β : Type} (f : α → β) (V : ExpVerifierSpec β) : ExpVerifierSpec α where
  width a := V.width (f a)
  witnessLength a := V.witnessLength (f a)
  gates a := V.gates (f a)

@[simp]
theorem acceptProb_comap {β : Type} (f : α → β) (V : ExpVerifierSpec β) (a : α)
    (ψ : Qubits (V.witnessLength (f a))) :
    (V.comap f).acceptProb a ψ = V.acceptProb (f a) ψ := by
  rfl

end ExpVerifierSpec

/-- `V` decides the promise problem `Q` in `QMA_EXP(c, s)`. -/
def PromiseProblem.IsQMAEXPVerifier {α : Type} (enc : α ↪ List Bool) (c s : ℕ → ℝ)
    (V : ExpVerifierSpec α) (Q : PromiseProblem α) : Prop :=
  V.IsExpUniform enc ∧
    ∀ a, (a ∈ Q.yes → ∃ ψ : Qubits (V.witnessLength a), ‖ψ‖ = 1 ∧
        c (enc a).length ≤ V.acceptProb a ψ) ∧
      (a ∈ Q.no → ∀ ψ : Qubits (V.witnessLength a), ‖ψ‖ = 1 →
        V.acceptProb a ψ ≤ s (enc a).length)

/-- **`QMA_EXP(c, s)`** for promise problems. -/
def PromiseQMAEXP {α : Type} (c s : ℕ → ℝ) (enc : α ↪ List Bool) : Set (PromiseProblem α) :=
  {Q | ∃ V : ExpVerifierSpec α, Q.IsQMAEXPVerifier enc c s V}

/-- Standard **`PromiseQMAEXP`** with completeness `2 / 3` and soundness `1 / 3`. -/
noncomputable abbrev PromiseQMAEXPStd {α : Type} (enc : α ↪ List Bool) : Set (PromiseProblem α) :=
  PromiseQMAEXP (fun _ => 2 / 3) (fun _ => 1 / 3) enc

/-- **`QMA_EXP`** for decision problems. -/
def QMAEXP {α : Type} (enc : α ↪ List Bool) : Set (Set α) :=
  {A | PromiseProblem.ofSet A ∈ PromiseQMAEXPStd enc}

theorem mem_QMAEXP {α : Type} {enc : α ↪ List Bool} {A : Set α} :
    A ∈ QMAEXP enc ↔ PromiseProblem.ofSet A ∈ PromiseQMAEXPStd enc :=
  Iff.rfl

/-- Weakening completeness and soundness thresholds enlarges `PromiseQMAEXP`. -/
theorem PromiseQMAEXP_mono {α : Type} {enc : α ↪ List Bool} {c c' s s' : ℕ → ℝ}
    (hc : ∀ n, c' n ≤ c n) (hs : ∀ n, s n ≤ s' n) :
    PromiseQMAEXP c s enc ⊆ PromiseQMAEXP c' s' enc := by
  rintro Q ⟨V, huni, hV⟩
  refine ⟨V, huni, fun a => ⟨fun ha => ?_, fun ha ψ hψ => ((hV a).2 ha ψ hψ).trans (hs _)⟩⟩
  obtain ⟨ψ, hψ, hacc⟩ := (hV a).1 ha
  exact ⟨ψ, hψ, (hc _).trans hacc⟩

private lemma poly_le_const_mul_two_pow_sq (c d n : ℕ) :
    c * (n + 1) ^ d ≤ (c * 2 ^ (d * d) + 1) * (2 ^ n ^ 2 + 1) := by
  have hn1 : (n + 1) ^ d ≤ 2 ^ (n * d) := by
    calc (n + 1) ^ d ≤ (2 ^ n) ^ d := Nat.pow_le_pow_left Nat.lt_two_pow_self d
      _ = 2 ^ (n * d) := (Nat.pow_mul 2 n d).symm
  by_cases hnd : n < d
  · have hmul : n * d ≤ d * d := Nat.mul_le_mul_right d hnd.le
    have hpow : 2 ^ (n * d) ≤ 2 ^ (d * d) := Nat.pow_le_pow_right (by decide) hmul
    calc c * (n + 1) ^ d ≤ c * 2 ^ (n * d) := Nat.mul_le_mul_left c hn1
      _ ≤ c * 2 ^ (d * d) := Nat.mul_le_mul_left c hpow
      _ ≤ (c * 2 ^ (d * d) + 1) * 1 := by omega
      _ ≤ (c * 2 ^ (d * d) + 1) * (2 ^ n ^ 2 + 1) :=
        Nat.mul_le_mul_left _ (Nat.le_add_left 1 (2 ^ n ^ 2))
  · have hnd' : d ≤ n := not_lt.mp hnd
    have hmul : n * d ≤ n ^ 2 := by rw [sq]; exact Nat.mul_le_mul_left n hnd'
    have hpow : 2 ^ (n * d) ≤ 2 ^ n ^ 2 := Nat.pow_le_pow_right (by decide) hmul
    calc c * (n + 1) ^ d ≤ c * 2 ^ (n * d) := Nat.mul_le_mul_left c hn1
      _ ≤ c * 2 ^ n ^ 2 := Nat.mul_le_mul_left c hpow
      _ ≤ (c * 2 ^ (d * d) + 1) * (2 ^ n ^ 2 + 1) := by
        have hpos : 1 ≤ 2 ^ (d * d) := Nat.one_le_two_pow
        have hc_le : c ≤ c * 2 ^ (d * d) + 1 :=
          (Nat.le_mul_of_pos_right c hpos).trans (Nat.le_succ _)
        exact (Nat.mul_le_mul_right _ hc_le).trans
          (Nat.mul_le_mul_left _ (Nat.le_succ _))

private lemma computableInO_exp_of_polyTime {α β : Type} {encIn : α ↪ List Bool}
    {encOut : β ↪ List Bool} {f : α → β} (hf : ComputableInPolyTime f encIn encOut) :
    ComputableInO f encIn encOut
      (fun a => 2 ^ (encIn a).length ^ 2) (fun a => 2 ^ (encIn a).length ^ 2) := by
  obtain ⟨T, S, hT, hS, hfO⟩ := hf.exists_computableInO
  obtain ⟨cT, dT, hcT⟩ := hT.exists_le
  obtain ⟨cS, dS, hcS⟩ := hS.exists_le
  let K := max (cT * 2 ^ (dT * dT) + 1) (cS * 2 ^ (dS * dS) + 1)
  refine hfO.mono K (fun a => ?_) (fun a => ?_)
  · exact (hcT a).trans ((poly_le_const_mul_two_pow_sq cT dT _).trans
      (Nat.mul_le_mul_right _ (le_max_left _ _)))
  · exact (hcS a).trans ((poly_le_const_mul_two_pow_sq cS dS _).trans
      (Nat.mul_le_mul_right _ (le_max_right _ _)))

theorem ExpVerifierSpec.IsExpUniform.comap_of_polyTime {α β : Type}
    {encA : α ↪ List Bool} {encB : β ↪ List Bool} {f : α → β} {V : ExpVerifierSpec β}
    (hf : ComputableInPolyTime f encA encB) (hV : V.IsExpUniform encB) :
    (V.comap f).IsExpUniform encA := by
  obtain ⟨⟨k, hw, hwl, hg⟩, hw_pos, hwl_le, hwf⟩ := hV
  obtain ⟨Tf, Sf, hTf, hSf, hfO⟩ := hf.exists_computableInO
  obtain ⟨c, d, hcd⟩ := ((hTf.add hSf).add hf.polyBounded_length).exists_le
  let N₀ : ℕ := max (c + c ^ k + 2) 2
  let E : ℕ := 2 * d * k + 2 * d + 2
  let K₀ : ℕ := c * (N₀ + 1) ^ d + 2 ^ (c ^ k * (N₀ + 1) ^ (d * k)) + 1
  have hbound (a : α) :
      Tf a + Sf a + 2 ^ (encB (f a)).length ^ k ≤ K₀ * (2 ^ (encA a).length ^ E + 1) := by
    let n := (encA a).length
    have hca : Tf a + Sf a + (encB (f a)).length ≤ c * (n + 1) ^ d := hcd a
    have hTS : Tf a + Sf a ≤ c * (n + 1) ^ d := by omega
    have hlen : (encB (f a)).length ≤ c * (n + 1) ^ d := by omega
    have hpow_len : (encB (f a)).length ^ k ≤ c ^ k * (n + 1) ^ (d * k) := by
      calc (encB (f a)).length ^ k ≤ (c * (n + 1) ^ d) ^ k := Nat.pow_le_pow_left hlen k
        _ = c ^ k * (n + 1) ^ (d * k) := by rw [mul_pow, ← pow_mul]
    by_cases hn : n < N₀
    · have hn_le : n + 1 ≤ N₀ + 1 := by omega
      have h1 : Tf a + Sf a ≤ c * (N₀ + 1) ^ d :=
        hTS.trans (Nat.mul_le_mul_left c (Nat.pow_le_pow_left hn_le d))
      have h2 : 2 ^ (encB (f a)).length ^ k ≤ 2 ^ (c ^ k * (N₀ + 1) ^ (d * k)) :=
        Nat.pow_le_pow_right (by decide)
          (hpow_len.trans (Nat.mul_le_mul_left (c ^ k) (Nat.pow_le_pow_left hn_le (d * k))))
      calc Tf a + Sf a + 2 ^ (encB (f a)).length ^ k
          ≤ K₀ := by dsimp [K₀]; omega
        _ = K₀ * 1 := (Nat.mul_one K₀).symm
        _ ≤ K₀ * (2 ^ n ^ E + 1) :=
          Nat.mul_le_mul_left K₀ (Nat.le_add_left 1 (2 ^ n ^ E))
    · have hn_ge : N₀ ≤ n := not_lt.mp hn
      have hn2 : 2 ≤ n := le_trans (le_max_right _ _) hn_ge
      have hcn : c + c ^ k + 2 ≤ n := le_trans (le_max_left _ _) hn_ge
      have hn1_sq : n + 1 ≤ n ^ 2 := by nlinarith
      have hterm1_exp : c * (n + 1) ^ d + 1 ≤ n ^ E := by
        have hcd_le : c * (n + 1) ^ d ≤ n * (n ^ 2) ^ d :=
          Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left hn1_sq d)
        have heq : n * (n ^ 2) ^ d = n ^ (2 * d + 1) := by rw [← pow_mul, ← pow_succ']
        have hlt_pow : n ^ (2 * d + 1) < n ^ E :=
          Nat.pow_lt_pow_right (by omega) (by dsimp [E]; omega)
        omega
      have hterm2_exp : c ^ k * (n + 1) ^ (d * k) + 1 ≤ n ^ E := by
        have hck_le : c ^ k * (n + 1) ^ (d * k) ≤ n * (n ^ 2) ^ (d * k) :=
          Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left hn1_sq (d * k))
        have heq : n * (n ^ 2) ^ (d * k) = n ^ (2 * d * k + 1) := by
          rw [← pow_mul, ← mul_assoc 2 d k, ← pow_succ']
        have hlt_pow : n ^ (2 * d * k + 1) < n ^ E :=
          Nat.pow_lt_pow_right (by omega) (by dsimp [E]; omega)
        omega
      have hnE_pos : 1 ≤ n ^ E := Nat.one_le_pow E n (by omega)
      have h1 : Tf a + Sf a ≤ 2 ^ (n ^ E - 1) := by
        calc Tf a + Sf a ≤ c * (n + 1) ^ d := hTS
          _ ≤ n ^ E - 1 := by omega
          _ ≤ 2 ^ (n ^ E - 1) := Nat.lt_two_pow_self.le
      have h2 : 2 ^ (encB (f a)).length ^ k ≤ 2 ^ (n ^ E - 1) :=
        Nat.pow_le_pow_right (by decide) (by omega)
      have hsum : Tf a + Sf a + 2 ^ (encB (f a)).length ^ k ≤ 2 ^ n ^ E := by
        calc Tf a + Sf a + 2 ^ (encB (f a)).length ^ k
            ≤ 2 ^ (n ^ E - 1) + 2 ^ (n ^ E - 1) := Nat.add_le_add h1 h2
          _ = 2 * 2 ^ (n ^ E - 1) := (two_mul _).symm
          _ = 2 ^ ((n ^ E - 1) + 1) := (pow_succ' 2 (n ^ E - 1)).symm
          _ = 2 ^ n ^ E := by rw [Nat.sub_add_cancel hnE_pos]
      have hK₀_pos : 1 ≤ K₀ := Nat.le_add_left 1 _
      calc Tf a + Sf a + 2 ^ (encB (f a)).length ^ k
          ≤ 2 ^ n ^ E := hsum
        _ ≤ 1 * (2 ^ n ^ E + 1) := by simp
        _ ≤ K₀ * (2 ^ n ^ E + 1) := Nat.mul_le_mul_right _ hK₀_pos
  refine ⟨⟨E, ?_, ?_, ?_⟩, fun a => hw_pos (f a), fun a => hwl_le (f a), fun a => hwf (f a)⟩
  · exact (hw.comp' hfO).mono K₀
      (fun a => by have := hbound a; omega) (fun a => by have := hbound a; omega)
  · exact (hwl.comp' hfO).mono K₀
      (fun a => by have := hbound a; omega) (fun a => by have := hbound a; omega)
  · exact (hg.comp' hfO).mono K₀
      (fun a => by have := hbound a; omega) (fun a => by have := hbound a; omega)

/-- **`PromiseQMAEXP` (with constant thresholds) is closed under deterministic polynomial-time
promise reductions.** -/
theorem PromiseProblem.PolyTimeReducible.mem_PromiseQMAEXP {α β : Type}
    {encA : α ↪ List Bool} {encB : β ↪ List Bool} {c₀ s₀ : ℝ}
    {X : PromiseProblem α} {Y : PromiseProblem β}
    (hXY : PromiseProblem.PolyTimeReducible encA encB X Y)
    (hY : Y ∈ PromiseQMAEXP (fun _ => c₀) (fun _ => s₀) encB) :
    X ∈ PromiseQMAEXP (fun _ => c₀) (fun _ => s₀) encA := by
  obtain ⟨f, hf, hyes, hno⟩ := hXY
  obtain ⟨V, hVuni, hV⟩ := hY
  refine ⟨V.comap f, hVuni.comap_of_polyTime hf, fun a => ?_⟩
  exact ⟨fun ha => (hV (f a)).1 (hyes ha), fun ha => (hV (f a)).2 (hno ha)⟩

/-- **`QMAEXP` is closed under deterministic polynomial-time many-one reductions.** -/
theorem PolyTimeReducible.mem_QMAEXP {α β : Type}
    {encA : α ↪ List Bool} {encB : β ↪ List Bool} {A : Set α} {B : Set β}
    (hAB : PolyTimeReducible encA encB A B) (hB : B ∈ QMAEXP encB) :
    A ∈ QMAEXP encA :=
  (PromiseProblem.polyTimeReducible_ofSet_iff.mpr hAB).mem_PromiseQMAEXP hB

private def constBoolVerifier {α : Type} (f : α → Bool) : ExpVerifierSpec α where
  width _ := 1
  witnessLength _ := 0
  gates a := if f a then [(false, 0, [])] else []

private lemma acceptProb_constBoolVerifier_ket {α : Type} (f : α → Bool) (a : α) :
    (constBoolVerifier f).acceptProb a (ket default) = if f a then 1 else 0 := by
  have hemb : embedState (blockEmb 0 (show 0 + 0 ≤ 1 by decide))
      (fun _ : Fin 1 => false) (ket (default : Fin 0 → Bool)) = ket (fun _ : Fin 1 => false) := by
    rw [embedState_ket]
    apply congrArg ket
    funext i
    exact glue_of_not _ _ _ fun j _ => Fin.elim0 j
  change measureProb (Circuit.eval (Circuit.ofCodes 1 (if f a then [(false, 0, [])] else []))
    (embedState (blockEmb 0 (show 0 + 0 ≤ 1 by decide))
      (fun _ : Fin 1 => false) (ket (default : Fin 0 → Bool))))
    (accepting 1) = if f a then 1 else 0
  rw [hemb]
  by_cases hfa : f a = true
  · simp only [hfa, ↓reduceIte]
    have hcls : GateCode.IsClassical 1 [(false, 0, [])] := by
      intro g hg
      rw [List.mem_singleton.mp hg]
      exact ⟨rfl, by simp [GateCode.WellFormed]⟩
    have hrun : GateCode.classicalRun [(false, 0, [])] (fun _ : Fin 1 => false) =
        fun _ : Fin 1 => true := by
      funext i
      have hi : i = ⟨0, by decide⟩ := Subsingleton.elim i _
      subst hi
      rfl
    rw [Circuit.eval_ofCodes_ket hcls, hrun, measureProb]
    have hmem : (fun _ : Fin 1 => true) ∈ accepting 1 := (mem_accepting (by decide)).mpr rfl
    rw [Finset.sum_eq_single (fun _ : Fin 1 => true)
      (fun b _ hb => by simp [ket_apply, hb])
      (fun hnot => (hnot hmem).elim)]
    simp [ket_apply]
  · have hff : f a = false := Bool.eq_false_iff.mpr hfa
    simp only [hff, Bool.false_eq_true, ↓reduceIte, Circuit.ofCodes_nil, Circuit.eval_nil,
      measureProb]
    refine Finset.sum_eq_zero fun y hy => ?_
    have hy0 : y ⟨0, by decide⟩ = true := (mem_accepting (by decide)).mp hy
    have hne : y ≠ (fun _ : Fin 1 => false) := fun h => by
      have h0 : y ⟨0, by decide⟩ = false := congrFun h ⟨0, by decide⟩
      exact Bool.noConfusion (hy0.symm.trans h0)
    rw [ket_apply, ite_eq_right_iff.mpr fun h => (hne h).elim]
    norm_num

/-- Every promise problem separated by an `EXP` language belongs to `PromiseQMAEXP (1, 0)`. -/
theorem promiseClass_EXP_subset_PromiseQMAEXP {α : Type} {enc : α ↪ List Bool} :
    promiseClass (EXP enc) ⊆ PromiseQMAEXP (fun _ => 1) (fun _ => 0) enc := by
  rintro Q ⟨A, hA, hyes, hno⟩
  obtain ⟨k, hk⟩ := mem_EXP_iff.mp hA
  have hind := computableInO_indicator_of_mem_DTIME hk
  let V := constBoolVerifier (indicator A)
  have hpow_le (a : α) :
      2 ^ (enc a).length ^ 2 ≤ 2 * 2 ^ (enc a).length ^ (k + 2) ∧
        2 ^ (enc a).length ^ k ≤ 2 * 2 ^ (enc a).length ^ (k + 2) := by
    set m := (enc a).length
    by_cases hm0 : m = 0
    · rw [hm0, Nat.zero_pow (by omega : 0 < k + 2)]
      rcases eq_or_ne k 0 with rfl | hk0
      · simp
      · simp [Nat.zero_pow (Nat.pos_of_ne_zero hk0)]
    · have hm1 : 1 ≤ m := Nat.pos_of_ne_zero hm0
      have h1 : 2 ^ m ^ 2 ≤ 2 ^ m ^ (k + 2) :=
        Nat.pow_le_pow_right (by decide) (Nat.pow_le_pow_right hm1 (by omega))
      have h2 : 2 ^ m ^ k ≤ 2 ^ m ^ (k + 2) :=
        Nat.pow_le_pow_right (by decide) (Nat.pow_le_pow_right hm1 (by omega))
      omega
  have huni : V.IsExpUniform enc := by
    refine ⟨⟨k + 2, ?_, ?_, ?_⟩, fun _ => Nat.zero_lt_one, fun _ => Nat.zero_le 1, fun a g hg => ?_⟩
    · exact (computableInO_exp_of_polyTime (ComputableInPolyTime.const 1)).mono 2
        (fun a => by have := (hpow_le a).1; omega)
        (fun a => by have := (hpow_le a).1; omega)
    · exact (computableInO_exp_of_polyTime (ComputableInPolyTime.const 0)).mono 2
        (fun a => by have := (hpow_le a).1; omega)
        (fun a => by have := (hpow_le a).1; omega)
    · dsimp [V, constBoolVerifier]
      refine .mono (by fun_prop) 4
        (fun a => by
          simp only [ite_self]
          have h1 := (hpow_le a).2
          have h2 : (enc a).length ≤ 2 ^ (enc a).length ^ (k + 2) :=
            (Nat.le_self_pow (by omega) _).trans Nat.lt_two_pow_self.le
          omega)
        (fun a => by
          simp only [ite_self]
          have h1 := (hpow_le a).2
          have h2 : (enc a).length ≤ 2 ^ (enc a).length ^ (k + 2) :=
            (Nat.le_self_pow (by omega) _).trans Nat.lt_two_pow_self.le
          omega)
    · dsimp [V, constBoolVerifier] at hg ⊢
      split_ifs at hg with hi
      · rw [List.mem_singleton.mp hg]
        simp [GateCode.WellFormed]
      · simp at hg
  refine ⟨V, huni, fun a => ⟨fun ha => ?_, fun ha => ?_⟩⟩
  · have haA : indicator A a = true := by simp [indicator, hyes ha]
    dsimp only [V]
    refine ⟨ket (default : Fin ((constBoolVerifier (indicator A)).witnessLength a) → Bool),
      norm_ket _, ?_⟩
    have hacc := acceptProb_constBoolVerifier_ket (indicator A) a
    simp only [haA, ↓reduceIte] at hacc
    exact le_of_eq hacc.symm
  · have haA : indicator A a = false := by
      have hnotA : a ∉ A := Set.disjoint_right.mp hno ha
      simp [indicator, hnotA]
    dsimp only [V]
    intro ψ _
    let z₀ : Fin ((constBoolVerifier (indicator A)).witnessLength a) → Bool := default
    have : Subsingleton (Fin ((constBoolVerifier (indicator A)).witnessLength a) → Bool) := by
      dsimp [constBoolVerifier]; infer_instance
    have hψ_eq : ψ = ψ.ofLp z₀ • ket z₀ := by
      ext z
      rw [Subsingleton.elim z z₀]
      simp
    rw [hψ_eq, ExpVerifierSpec.acceptProb_smul]
    dsimp only [z₀]
    rw [acceptProb_constBoolVerifier_ket, haA]
    simp

/-- **`EXP ⊆ QMAEXP`**. -/
theorem EXP_subset_QMAEXP {α : Type} {enc : α ↪ List Bool} :
    EXP enc ⊆ QMAEXP enc := by
  intro A hA
  exact PromiseQMAEXP_mono (fun _ => by norm_num) (fun _ => by norm_num)
    (promiseClass_EXP_subset_PromiseQMAEXP (ofSet_mem_promiseClass.mpr hA))

/-- **`P ⊂ QMAEXP`** on binary words. -/
theorem P_ssubset_QMAEXP : P encBits ⊂ QMAEXP encBits :=
  P_ssubset_EXP.trans_subset EXP_subset_QMAEXP

private def swapPrefix (source count : ℕ) : List GateCode :=
  (List.range count).flatMap fun j => GateCode.swapWireCodes j (source + j)

private lemma isClassical_swapPrefix {source count width : ℕ} (hdisjoint : count ≤ source)
    (hfit : source + count ≤ width) :
    GateCode.IsClassical width (swapPrefix source count) := by
  intro g hg
  obtain ⟨j, hj, hg⟩ := List.mem_flatMap.mp hg
  have hj' := List.mem_range.mp hj
  exact GateCode.isClassical_swapWireCodes (by omega) (by omega) (by omega) g hg

private lemma readBit_classicalRun_swapWireCodes_right {left right width : ℕ} (hne : left ≠ right)
    (hleft : left < width) (hright : right < width) (x : Fin width → Bool) :
    readBit (GateCode.classicalRun (GateCode.swapWireCodes left right) x) right =
      readBit x left := by
  have hneq : right ≠ left := hne.symm
  simp only [GateCode.swapWireCodes, GateCode.classicalRun_cons, GateCode.classicalRun_nil,
    GateCode.readBit_classicalStep, GateCode.target_mk, GateCode.controls_mk, List.all_cons,
    List.all_nil, Bool.and_true]
  simp only [hneq, hleft, hright, and_self, false_and, decide_true, decide_false,
    Bool.true_and, Bool.false_and, Bool.xor_false]
  cases readBit x left <;> cases readBit x right <;> rfl

private lemma readBit_classicalRun_swapPrefix_all {source count width : ℕ}
    (hdisjoint : count ≤ source) (hfit : source + count ≤ width)
    (x : Fin width → Bool) (q : ℕ) :
    readBit (GateCode.classicalRun (swapPrefix source count) x) q =
      if q < count then readBit x (source + q)
      else if source ≤ q ∧ q < source + count then readBit x (q - source)
      else readBit x q := by
  induction count generalizing x q with
  | zero =>
    have h0 : swapPrefix source 0 = [] := rfl
    rw [h0, GateCode.classicalRun_nil]
    have h1 : ¬ (q < 0) := by omega
    have h2 : ¬ (source ≤ q ∧ q < source + 0) := by omega
    simp only [h1, h2, ↓reduceIte]
  | succ count ih =>
    have hstep : swapPrefix source (count + 1) =
        swapPrefix source count ++ GateCode.swapWireCodes count (source + count) := by
      simp [swapPrefix, List.range_succ]
    rw [hstep, GateCode.classicalRun_append]
    by_cases hq_c : q = count
    · subst hq_c
      rw [GateCode.readBit_classicalRun_swapWireCodes (by omega) (by omega) (by omega),
        ih (by omega) (by omega)]
      have h1 : ¬ (source + q < q) := by omega
      have h2 : ¬ (source ≤ source + q ∧ source + q < source + q) := by omega
      have h3 : q < q + 1 := by omega
      simp only [h1, h2, h3, ↓reduceIte]
    · by_cases hq_sc : q = source + count
      · subst hq_sc
        rw [readBit_classicalRun_swapWireCodes_right (by omega) (by omega) (by omega),
          ih (by omega) (by omega)]
        have h1 : ¬ (count < count) := by omega
        have h2 : ¬ (source ≤ count ∧ count < source + count) := by omega
        have h3 : ¬ (source + count < count + 1) := by omega
        have h4 : source ≤ source + count ∧ source + count < source + (count + 1) := by omega
        simp only [h1, h2, h3, h4.1, h4.2, and_self, ↓reduceIte, Nat.add_sub_cancel_left]
      · rw [GateCode.readBit_classicalRun_swapWireCodes_of_ne hq_c hq_sc,
          ih (by omega) (by omega)]
        by_cases h1 : q < count
        · have h1' : q < count + 1 := by omega
          simp only [h1, h1', ↓reduceIte]
        · have h1' : ¬ (q < count + 1) := by omega
          by_cases h2 : source ≤ q ∧ q < source + count
          · have h2' : source ≤ q ∧ q < source + (count + 1) := ⟨h2.1, by omega⟩
            simp only [h1, h1', h2, h2', ↓reduceIte]
          · have h2' : ¬ (source ≤ q ∧ q < source + (count + 1)) := by omega
            simp only [h1, h1', h2, h2', ↓reduceIte]

private def writeInputCodes (o : ℕ) (x : List Bool) : List GateCode :=
  ((List.range x.length).filter fun i => x.getD i false).map fun i => (false, o + i, [])

private lemma mem_writeInputCodes {o : ℕ} {x : List Bool} {g : GateCode} :
    g ∈ writeInputCodes o x ↔
      ∃ i < x.length, x.getD i false = true ∧ g = (false, o + i, []) := by
  simp only [writeInputCodes, List.mem_map, List.mem_filter, List.mem_range]
  exact ⟨fun ⟨i, ⟨hi, hbit⟩, hg⟩ => ⟨i, hi, hbit, hg.symm⟩,
    fun ⟨i, hi, hbit, hg⟩ => ⟨i, ⟨hi, hbit⟩, hg.symm⟩⟩

private lemma isClassical_writeInputCodes {o N : ℕ} {x : List Bool} (hfit : o + x.length ≤ N) :
    GateCode.IsClassical N (writeInputCodes o x) := by
  intro g hg
  obtain ⟨i, hi, -, rfl⟩ := mem_writeInputCodes.mp hg
  exact ⟨rfl, by simp [GateCode.WellFormed]; omega⟩

private lemma nodup_writeInputCodes (o : ℕ) (x : List Bool) :
    ((writeInputCodes o x).map GateCode.target).Nodup := by
  unfold writeInputCodes
  rw [List.map_map]
  refine ((List.nodup_range).sublist List.filter_sublist).map ?_
  intro i j h
  dsimp [GateCode.target] at h
  omega

private lemma readBit_classicalRun_writeInputCodes {o N : ℕ} {x : List Bool}
    (hfit : o + x.length ≤ N) (X : Fin N → Bool)
    (hzero : ∀ i < x.length, readBit X (o + i) = false) (q : ℕ) :
    readBit (GateCode.classicalRun (writeInputCodes o x) X) q =
      if o ≤ q ∧ q < o + x.length then x.getD (q - o) false else readBit X q := by
  by_cases hq : o ≤ q ∧ q < o + x.length
  · simp only [hq.1, hq.2, and_self, ↓reduceIte]
    set i := q - o
    have hi : i < x.length := by omega
    have hqi : q = o + i := by omega
    rw [hqi]
    by_cases hbit : x.getD i false = true
    · have hg : (false, o + i, []) ∈ writeInputCodes o x :=
        mem_writeInputCodes.mpr ⟨i, hi, hbit, rfl⟩
      have hmem := GateCode.readBit_classicalRun_of_mem
        (fun g hg' => by obtain ⟨j, hj, -, rfl⟩ := mem_writeInputCodes.mp hg'; simp; omega)
        (nodup_writeInputCodes o x)
        (fun g hg' g' hg'' => by
          obtain ⟨_, _, -, rfl⟩ := mem_writeInputCodes.mp hg''
          simp)
        X hg
      simp only [GateCode.target_mk, GateCode.controls_mk, List.all_nil, hzero i hi,
        Bool.false_xor] at hmem
      rw [hmem, hbit]
    · have hbit_f : x.getD i false = false := Bool.eq_false_iff.mpr hbit
      have hne_all : ∀ g ∈ writeInputCodes o x, g.target ≠ o + i := by
        intro g hg
        obtain ⟨j, _, hbj, rfl⟩ := mem_writeInputCodes.mp hg
        simp only [GateCode.target_mk, ne_eq]
        intro heq
        have hji : j = i := by omega
        subst hji
        exact hbit hbj
      rw [hbit_f, GateCode.readBit_classicalRun_of_forall_ne hne_all X, hzero i hi]
  · simp only [hq, ↓reduceIte]
    have hne_all : ∀ g ∈ writeInputCodes o x, g.target ≠ q := by
      intro g hg
      obtain ⟨j, hj, -, rfl⟩ := mem_writeInputCodes.mp hg
      simp only [GateCode.target_mk, ne_eq]
      omega
    exact GateCode.readBit_classicalRun_of_forall_ne hne_all X

private lemma wellFormed_shift_of_le {m o N : ℕ} {g : GateCode}
    (hfit : o + m ≤ N) (hg : g.WellFormed m) :
    (GateCode.shift o g).WellFormed N := by
  rcases g with ⟨b, t, cs⟩
  cases b
  · dsimp [GateCode.WellFormed] at hg
    obtain ⟨hlen, hnd, hall⟩ := hg
    refine ⟨by simp [hlen], ?_, ?_⟩
    · change ((t :: cs).map (· + o)).Nodup
      exact hnd.map fun i j hij => by omega
    · intro i hi
      change i ∈ (t :: cs).map (· + o) at hi
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
      have := hall j hj
      omega
  · dsimp [GateCode.WellFormed] at hg
    obtain ⟨ht, rfl⟩ := hg
    exact ⟨by dsimp [GateCode.shift]; omega, rfl⟩

/-- Lift a polynomial-time `UniformVerifierFamily` to an `ExpVerifierSpec`. -/
private def ExpVerifierSpec.ofUniform {α : Type} (enc : α ↪ List Bool)
    (U : UniformVerifierFamily) : ExpVerifierSpec α where
  width a := U.witnessLength (enc a).length + 1 + U.width (enc a).length
  witnessLength a := U.witnessLength (enc a).length
  gates a :=
    let x := enc a
    let n := x.length
    let w := U.witnessLength n
    let o := w + 1
    (swapPrefix (o + n) w ++ writeInputCodes o x) ++
      ((U.gates n).map (GateCode.shift o) ++ GateCode.swapCodes o)

private theorem isExpUniform_ofUniform {α : Type} (enc : α ↪ List Bool)
    (U : UniformVerifierFamily) :
    (ExpVerifierSpec.ofUniform enc U).IsExpUniform enc := by
  have henc : ComputableInPolyTime (fun a : α => enc a) enc encBits :=
    (ComputableInPolyTime.id' (encIn := enc)).of_enc_eq fun _ => rfl
  have hn : ComputableInPolyTime (fun a : α => (enc a).length) enc encUnary :=
    ComputableInPolyTime.encoding_length enc
  have hw : ComputableInPolyTime (fun a : α => U.witnessLength (enc a).length) enc encUnary :=
    U.computableInPolyTime_witnessLength.comp hn
  have hm : ComputableInPolyTime (fun a : α => U.width (enc a).length) enc encUnary :=
    U.computableInPolyTime_width.comp hn
  have hwidth : ComputableInPolyTime (ExpVerifierSpec.ofUniform enc U).width enc encUnary := by
    unfold ExpVerifierSpec.ofUniform
    fun_prop
  have hpSwap : ComputableInPolyTime
      (fun a : α => swapPrefix
        (U.witnessLength (enc a).length + 1 + (enc a).length)
        (U.witnessLength (enc a).length)) enc (encList encGateCode) := by
    unfold swapPrefix GateCode.swapWireCodes
    have hrng : ComputableInPolyTime (fun a : α => List.range (U.witnessLength (enc a).length))
        enc (encList encUnary) := ComputableInPolyTime.range.comp hw
    have hp1 : ComputableInPolyTime (fun p : α × ℕ => p.1) (encPair enc encUnary) enc :=
      .fst enc encUnary
    have hj : ComputableInPolyTime (fun p : α × ℕ => p.2) (encPair enc encUnary) encUnary :=
      .snd enc encUnary
    have hsrc : ComputableInPolyTime
        (fun p : α × ℕ => U.witnessLength (enc p.1).length + 1 + (enc p.1).length + p.2)
        (encPair enc encUnary) encUnary :=
      ComputableInPolyTime.unary_add'
        (ComputableInPolyTime.unary_add'
          (ComputableInPolyTime.unary_add' (hw.comp hp1) (.const 1)) (hn.comp hp1)) hj
    have hg1 : ComputableInPolyTime
        (fun p : α × ℕ => ((false, p.2, [U.witnessLength (enc p.1).length + 1 +
          (enc p.1).length + p.2]) : GateCode))
        (encPair enc encUnary) encGateCode :=
      (ComputableInPolyTime.const false).prod
        (hj.prod (ComputableInPolyTime.cons' hsrc (ComputableInPolyTime.const [])))
    have hg2 : ComputableInPolyTime
        (fun p : α × ℕ => ((false, U.witnessLength (enc p.1).length + 1 +
          (enc p.1).length + p.2, [p.2]) : GateCode))
        (encPair enc encUnary) encGateCode :=
      (ComputableInPolyTime.const false).prod
        (hsrc.prod (ComputableInPolyTime.cons' hj (ComputableInPolyTime.const [])))
    exact ComputableInPolyTime.flatMapWithInput hrng
      (ComputableInPolyTime.cons' hg1
        (ComputableInPolyTime.cons' hg2
          (ComputableInPolyTime.cons' hg1 (ComputableInPolyTime.const []))))
  have hwrite : ComputableInPolyTime
      (fun a : α => writeInputCodes (U.witnessLength (enc a).length + 1) (enc a))
      enc (encList encGateCode) := by
    unfold writeInputCodes
    have hbit : ComputableInPolyTime
        (fun p : α × ℕ => (enc p.1).getD p.2 false) (encPair enc encUnary) encBool :=
      ComputableInPolyTime.bitsGetDWithInput (henc.comp (.fst _ _)) (.snd _ _) false
    have hflt : ComputableInPolyTime
        (fun a : α => (List.range (enc a).length).filter fun i => (enc a).getD i false)
        enc (encList encUnary) :=
      ComputableInPolyTime.filterWithInput (ComputableInPolyTime.range.comp hn) hbit
    have hp1w : ComputableInPolyTime (fun p : α × ℕ => p.1) (encPair enc encUnary) enc :=
      .fst enc encUnary
    have hjw : ComputableInPolyTime (fun p : α × ℕ => p.2) (encPair enc encUnary) encUnary :=
      .snd enc encUnary
    have htar : ComputableInPolyTime
        (fun p : α × ℕ => U.witnessLength (enc p.1).length + 1 + p.2)
        (encPair enc encUnary) encUnary :=
      ComputableInPolyTime.unary_add'
        (ComputableInPolyTime.unary_add' (hw.comp hp1w) (.const 1)) hjw
    exact ComputableInPolyTime.mapWithInput hflt
      ((ComputableInPolyTime.const false).prod (htar.prod (ComputableInPolyTime.const [])))
  have hUgates : ComputableInPolyTime
      (fun a : α => (U.gates (enc a).length).map
        (GateCode.shift (U.witnessLength (enc a).length + 1)))
      enc (encList encGateCode) := by
    have hUg := U.computableInPolyTime_gates.comp hn
    have hp1g : ComputableInPolyTime (fun p : α × GateCode => p.1)
        (encPair enc encGateCode) enc := .fst enc encGateCode
    have ho : ComputableInPolyTime
        (fun p : α × GateCode => U.witnessLength (enc p.1).length + 1)
        (encPair enc encGateCode) encUnary :=
      ComputableInPolyTime.unary_add' (hw.comp hp1g) (.const 1)
    have hg_proj : ComputableInPolyTime (fun p : α × GateCode => p.2)
        (encPair enc encGateCode) encGateCode := .snd _ _
    have hg_flag : ComputableInPolyTime (fun p : α × GateCode => p.2.1)
        (encPair enc encGateCode) encBool :=
      (ComputableInPolyTime.fst encBool (encPair encUnary (encList encUnary))).comp hg_proj
    have hg_rest : ComputableInPolyTime (fun p : α × GateCode => p.2.2)
        (encPair enc encGateCode) (encPair encUnary (encList encUnary)) :=
      (ComputableInPolyTime.snd encBool (encPair encUnary (encList encUnary))).comp hg_proj
    have hg_t : ComputableInPolyTime (fun p : α × GateCode => p.2.2.1)
        (encPair enc encGateCode) encUnary :=
      (ComputableInPolyTime.fst encUnary (encList encUnary)).comp hg_rest
    have hg_cs : ComputableInPolyTime (fun p : α × GateCode => p.2.2.2)
        (encPair enc encGateCode) (encList encUnary) :=
      (ComputableInPolyTime.snd encUnary (encList encUnary)).comp hg_rest
    have hcs_shift : ComputableInPolyTime
        (fun p : α × GateCode => p.2.2.2.map (· + (U.witnessLength (enc p.1).length + 1)))
        (encPair enc encGateCode) (encList encUnary) :=
      ComputableInPolyTime.mapWithInput hg_cs
        (ComputableInPolyTime.unary_add' (.snd _ _) (ho.comp (.fst _ _)))
    have hbody : ComputableInPolyTime
        (fun p : α × GateCode =>
          GateCode.shift (U.witnessLength (enc p.1).length + 1) p.2)
        (encPair enc encGateCode) encGateCode :=
      hg_flag.prod ((ComputableInPolyTime.unary_add' hg_t ho).prod hcs_shift)
    exact ComputableInPolyTime.mapWithInput hUg hbody
  have hswap : ComputableInPolyTime
      (fun a : α => GateCode.swapCodes (U.witnessLength (enc a).length + 1))
      enc (encList encGateCode) := by
    unfold GateCode.swapCodes GateCode.swapWireCodes
    have ho1 : ComputableInPolyTime (fun a : α => U.witnessLength (enc a).length + 1)
        enc encUnary := by fun_prop
    have hz : ComputableInPolyTime (fun _ : α => 0) enc encUnary := .const 0
    have hs1 : ComputableInPolyTime
        (fun a : α => ((false, 0, [U.witnessLength (enc a).length + 1]) : GateCode))
        enc encGateCode :=
      (ComputableInPolyTime.const false).prod
        (hz.prod (ComputableInPolyTime.cons' ho1 (ComputableInPolyTime.const [])))
    have hs2 : ComputableInPolyTime
        (fun a : α => ((false, U.witnessLength (enc a).length + 1, [0]) : GateCode))
        enc encGateCode :=
      (ComputableInPolyTime.const false).prod
        (ho1.prod (ComputableInPolyTime.cons' hz (ComputableInPolyTime.const [])))
    exact ComputableInPolyTime.cons' hs1
      (ComputableInPolyTime.cons' hs2
        (ComputableInPolyTime.cons' hs1 (ComputableInPolyTime.const [])))
  have hgates : ComputableInPolyTime (ExpVerifierSpec.ofUniform enc U).gates
      enc (encList encGateCode) := by
    exact ComputableInPolyTime.listAppend'
      (ComputableInPolyTime.listAppend' hpSwap hwrite)
      (ComputableInPolyTime.listAppend' hUgates hswap)
  refine ⟨⟨2, computableInO_exp_of_polyTime hwidth, computableInO_exp_of_polyTime hw,
    computableInO_exp_of_polyTime hgates⟩,
    fun a => by dsimp [ExpVerifierSpec.ofUniform]; have := U.width_pos (enc a).length; omega,
    fun a => by dsimp [ExpVerifierSpec.ofUniform]; omega,
    fun a g hg => ?_⟩
  dsimp [ExpVerifierSpec.ofUniform] at hg ⊢
  have hnw : (enc a).length + U.witnessLength (enc a).length ≤ U.width (enc a).length :=
    U.add_witnessLength_le (enc a).length
  have hm_pos : 0 < U.width (enc a).length := U.width_pos (enc a).length
  rcases List.mem_append.mp hg with hg1 | hg2
  · rcases List.mem_append.mp hg1 with hps | hwr
    · exact (isClassical_swapPrefix (by omega) (by omega) g hps).2
    · exact (isClassical_writeInputCodes (by omega) g hwr).2
  · rcases List.mem_append.mp hg2 with hsh | hsw
    · obtain ⟨g₀, hg₀, rfl⟩ := List.mem_map.mp hsh
      exact wellFormed_shift_of_le (by omega) (U.wellFormed (enc a).length g₀ hg₀)
    · exact (GateCode.isClassical_swapCodes (by omega) (by omega) g hsw).2

private theorem acceptProb_ofUniform {α : Type} (enc : α ↪ List Bool)
    (U : UniformVerifierFamily) (a : α) (ψ : Qubits (U.witnessLength (enc a).length)) :
    (ExpVerifierSpec.ofUniform enc U).acceptProb a ψ = U.acceptProb (enc a) ψ := by
  let x := enc a
  let n := x.length
  let w := U.witnessLength n
  let m := U.width n
  let o := w + 1
  let N := o + m
  have hnw : n + w ≤ m := U.add_witnessLength_le n
  have hm_pos : 0 < m := U.width_pos n
  have hreg : (ExpVerifierSpec.ofUniform enc U).regWidth a = N := by
    dsimp [ExpVerifierSpec.regWidth, ExpVerifierSpec.ofUniform, N, o, w, m, n, x]
    omega
  obtain ⟨prep, hprep_def⟩ :
      ∃ prep, prep = swapPrefix (o + n) w ++ writeInputCodes o x := ⟨_, rfl⟩
  have hprep_cls : GateCode.IsClassical N prep := by
    rw [hprep_def]
    exact GateCode.IsClassical.append.mpr
      ⟨isClassical_swapPrefix (by omega) (by omega),
       isClassical_writeInputCodes (by omega)⟩
  let baseX : Fin N → Bool := glue (blockEmb o (le_refl N)) (inputState m x) (fun _ => false)
  have hprep_run : ∀ z : Fin w → Bool,
      GateCode.classicalRun prep
        (glue (blockEmb 0 (show 0 + w ≤ N by omega)) z (fun _ => false)) =
      glue (blockEmb (o + n) (show (o + n) + w ≤ N by omega)) z baseX := by
    intro z
    let Y₀ : Fin N → Bool := glue (blockEmb 0 (show 0 + w ≤ N by omega)) z (fun _ => false)
    have hY₀ (q : ℕ) : readBit Y₀ q = if hq : q < w then z ⟨q, hq⟩ else false := by
      by_cases hqw : q < w
      · simp only [hqw, ↓reduceDIte]
        rw [readBit_of_lt _ (by omega)]
        have heq_fin : (⟨q, by omega⟩ : Fin N) =
            blockEmb 0 (show 0 + w ≤ N by omega) ⟨q, hqw⟩ :=
          Fin.ext (by simp [blockEmb_apply_val])
        rw [heq_fin]
        exact glue_apply_emb (blockEmb 0 (show 0 + w ≤ N by omega)) z (fun _ => false) ⟨q, hqw⟩
      · simp only [hqw, ↓reduceDIte]
        by_cases hqN : q < N
        · rw [readBit_of_lt _ hqN]
          refine glue_of_not _ _ _ fun j hj => ?_
          have : (j : ℕ) = q := by simpa [blockEmb_apply_val] using congrArg Fin.val hj
          omega
        · exact readBit_of_le _ (not_lt.mp hqN)
    let Y₁ := GateCode.classicalRun (swapPrefix (o + n) w) Y₀
    have hY₁ (q : ℕ) : readBit Y₁ q =
        if hq : o + n ≤ q ∧ q < o + n + w then z ⟨q - (o + n), by omega⟩ else false := by
      dsimp [Y₁]
      rw [readBit_classicalRun_swapPrefix_all (by omega) (by omega) Y₀ q]
      by_cases h1 : q < w
      · have hnot2 : ¬ (o + n ≤ q ∧ q < o + n + w) := by omega
        have hnot3 : ¬ (o + n + q < w) := by omega
        simp only [h1, hnot2, ↓reduceIte, ↓reduceDIte, hY₀, hnot3]
      · by_cases h2 : o + n ≤ q ∧ q < o + n + w
        · have hlt_w : q - (o + n) < w := by omega
          simp only [h1, h2.1, h2.2, and_self, ↓reduceIte, ↓reduceDIte, hY₀, hlt_w]
        · simp only [h1, h2, ↓reduceIte, ↓reduceDIte, hY₀]
    have hzero_o : ∀ i < n, readBit Y₁ (o + i) = false := by
      intro i hi
      have hnot : ¬ (o + n ≤ o + i ∧ o + i < o + n + w) := by omega
      rw [hY₁]
      simp only [hnot, ↓reduceDIte]
    refine funext_readBit fun q => ?_
    rw [hprep_def, GateCode.classicalRun_append,
      readBit_classicalRun_writeInputCodes (by omega) Y₁ hzero_o q, hY₁]
    by_cases hqN : q < N
    · rw [readBit_of_lt _ hqN]
      by_cases hzw : o + n ≤ q ∧ q < o + n + w
      · have hnot_on : ¬ (o ≤ q ∧ q < o + x.length) := by
          have : x.length = n := rfl
          omega
        simp only [hnot_on, hzw.1, hzw.2, and_self, ↓reduceIte, ↓reduceDIte]
        have heq : (⟨q, hqN⟩ : Fin N) =
            blockEmb (o + n) (show (o + n) + w ≤ N by omega) ⟨q - (o + n), by omega⟩ :=
          Fin.ext (by simp [blockEmb_apply_val]; omega)
        rw [heq, glue_apply_emb]
      · simp only [hzw, ↓reduceDIte]
        have hnot_z : ∀ j : Fin w,
            blockEmb (o + n) (show (o + n) + w ≤ N by omega) j ≠ ⟨q, hqN⟩ := by
          intro j hj
          have hval := congrArg Fin.val hj
          simp only [blockEmb_apply_val] at hval
          omega
        rw [glue_of_not _ _ _ hnot_z]
        dsimp [baseX]
        by_cases hqo : o ≤ q
        · have hqm : q - o < m := by omega
          have heq : (⟨q, hqN⟩ : Fin N) = blockEmb o (le_refl N) ⟨q - o, hqm⟩ :=
            Fin.ext (by simp [blockEmb_apply_val]; omega)
          rw [heq, glue_apply_emb]
          have hinp : inputState m x ⟨q - o, hqm⟩ = x.getD (q - o) false := rfl
          rw [hinp]
          by_cases hqn : q < o + x.length
          · simp only [hqo, hqn, and_self, ↓reduceIte]
          · have hnboth : ¬ (o ≤ q ∧ q < o + x.length) := by omega
            simp only [hnboth, ↓reduceIte]
            exact (List.getD_eq_default x false (by omega)).symm
        · have hnboth : ¬ (o ≤ q ∧ q < o + x.length) := by omega
          simp only [hnboth, ↓reduceIte]
          have hnot_o : ∀ j : Fin m, blockEmb o (le_refl N) j ≠ ⟨q, hqN⟩ := by
            intro j hj
            have hval := congrArg Fin.val hj
            simp only [blockEmb_apply_val] at hval
            omega
          rw [glue_of_not _ _ _ hnot_o]
    · have hnboth : ¬ (o ≤ q ∧ q < o + x.length) := by
        have : x.length = n := rfl
        omega
      have hnz : ¬ (o + n ≤ q ∧ q < o + n + w) := by omega
      simp only [hnboth, hnz, ↓reduceIte, ↓reduceDIte]
      exact (readBit_of_le _ (not_lt.mp hqN)).symm
  have hemb_nest :
      embedState (blockEmb (o + n) (show (o + n) + w ≤ N by omega)) baseX ψ =
      embedState (blockEmb o (le_refl N)) (fun _ => false)
        (embedState (U.witnessQubits n) (inputState m x) ψ) := by
    conv_lhs => rw [← sum_smul_ket ψ]
    conv_rhs => rw [← sum_smul_ket ψ]
    simp only [map_sum, map_smul, embedState_ket]
    refine Finset.sum_congr rfl fun z _ => congrArg (ψ.ofLp z • ·) (congrArg ket ?_)
    refine funext_readBit fun q => ?_
    by_cases hqN : q < N
    · rw [readBit_of_lt _ hqN, readBit_of_lt _ hqN]
      by_cases hqo : o ≤ q
      · have hqm : q - o < m := by omega
        have heq_o : (⟨q, hqN⟩ : Fin N) = blockEmb o (le_refl N) ⟨q - o, hqm⟩ :=
          Fin.ext (by simp [blockEmb_apply_val]; omega)
        rw [heq_o, glue_apply_emb]
        by_cases hzw : o + n ≤ q ∧ q < o + n + w
        · have heq_w : blockEmb o (le_refl N) ⟨q - o, hqm⟩ =
              blockEmb (o + n) (show (o + n) + w ≤ N by omega) ⟨q - (o + n), by omega⟩ :=
            Fin.ext (by simp [blockEmb_apply_val]; omega)
          have heq_in : (⟨q - o, hqm⟩ : Fin m) = U.witnessQubits n ⟨q - (o + n), by omega⟩ :=
            Fin.ext (by simp [UniformVerifierFamily.witnessQubits, blockEmb_apply_val]; omega)
          rw [heq_w, glue_apply_emb, heq_in, glue_apply_emb]
        · have hnot1 : ∀ j : Fin w,
              blockEmb (o + n) (show (o + n) + w ≤ N by omega) j ≠
                blockEmb o (le_refl N) ⟨q - o, hqm⟩ := by
            intro j hj
            have hval := congrArg Fin.val hj
            simp only [blockEmb_apply_val] at hval
            omega
          have hnot2 : ∀ j : Fin w, U.witnessQubits n j ≠ ⟨q - o, hqm⟩ := by
            intro j hj
            have hval := congrArg Fin.val hj
            simp only [UniformVerifierFamily.witnessQubits, blockEmb_apply_val] at hval
            omega
          rw [glue_of_not _ _ _ hnot1, glue_of_not _ _ _ hnot2]
          dsimp [baseX]
          rw [glue_apply_emb]
      · have hnot_z : ∀ j : Fin w,
            blockEmb (o + n) (show (o + n) + w ≤ N by omega) j ≠ ⟨q, hqN⟩ := by
          intro j hj
          have hval := congrArg Fin.val hj
          simp only [blockEmb_apply_val] at hval
          omega
        have hnot_o : ∀ j : Fin m, blockEmb o (le_refl N) j ≠ ⟨q, hqN⟩ := by
          intro j hj
          have hval := congrArg Fin.val hj
          simp only [blockEmb_apply_val] at hval
          omega
        rw [glue_of_not _ _ _ hnot_z, glue_of_not _ _ _ hnot_o]
        dsimp [baseX]
        rw [glue_of_not _ _ _ hnot_o]
    · rw [readBit_of_le _ (not_lt.mp hqN), readBit_of_le _ (not_lt.mp hqN)]
  have lhs_eq : (ExpVerifierSpec.ofUniform enc U).acceptProb a ψ =
      measureProb (Circuit.eval (Circuit.ofCodes N
          ((prep ++ (U.gates n).map (GateCode.shift o)) ++ GateCode.swapCodes o))
        (embedState (blockEmb 0 (show 0 + w ≤ N by omega)) (fun _ => false) ψ)) (accepting N) := by
    have hcast : ∀ (M : ℕ) (h0w : 0 + w ≤ M), M = N →
        measureProb (Circuit.eval (Circuit.ofCodes M
            ((prep ++ (U.gates n).map (GateCode.shift o)) ++ GateCode.swapCodes o))
          (embedState (blockEmb 0 h0w) (fun _ => false) ψ)) (accepting M) =
        measureProb (Circuit.eval (Circuit.ofCodes N
            ((prep ++ (U.gates n).map (GateCode.shift o)) ++ GateCode.swapCodes o))
          (embedState (blockEmb 0 (show 0 + w ≤ N by omega)) (fun _ => false) ψ))
          (accepting N) := by
      rintro M h0w rfl
      rfl
    unfold ExpVerifierSpec.acceptProb ExpVerifierSpec.regWidth ExpVerifierSpec.ofUniform
    dsimp only []
    rw [← hprep_def, ← List.append_assoc prep]
    exact hcast (max (w + 1 + m) w) _ (by dsimp [N, o]; omega)
  rw [lhs_eq, Circuit.ofCodes_append, Circuit.ofCodes_append,
    Circuit.eval_append, Circuit.eval_append,
    Circuit.eval_ofCodes_embedState hprep_cls _ _ _ _ hprep_run ψ,
    hemb_nest, Circuit.ofCodes_map_shift (le_refl N) (U.wellFormed n),
    Circuit.eval_mapWires_embedState,
    Circuit.measureProb_eval_ofCodes (GateCode.isClassical_swapCodes (by omega) (by omega))]
  set Φ := Circuit.eval (Circuit.ofCodes m (U.gates n))
    (embedState (U.witnessQubits n) (inputState m x) ψ)
  have hterm (Y : Fin N → Bool) :
      (if GateCode.classicalRun (GateCode.swapCodes o) Y ∈ accepting N then
        ‖(embedState (blockEmb o (le_refl N)) (fun _ => false) Φ).ofLp Y‖ ^ 2 else 0) =
      if AgreeOff (blockEmb o (le_refl N)) Y (fun _ => false) then
        (if Y ∘ blockEmb o (le_refl N) ∈ accepting m then
          ‖Φ.ofLp (Y ∘ blockEmb o (le_refl N))‖ ^ 2 else 0)
      else 0 := by
    have hacc : GateCode.classicalRun (GateCode.swapCodes o) Y ∈ accepting N ↔
        Y ∘ blockEmb o (le_refl N) ∈ accepting m := by
      rw [mem_accepting (by omega), mem_accepting hm_pos, Function.comp_apply,
        ← readBit_fin (GateCode.classicalRun _ Y)]
      change readBit _ 0 = true ↔ _
      rw [GateCode.readBit_classicalRun_swapCodes (by omega) (by omega),
        readBit_of_lt _ (by omega)]
      exact Iff.of_eq (congrArg (· = true) (congrArg Y (Fin.ext (by simp))))
    rw [if_congr hacc rfl rfl, embedState_apply]
    split_ifs <;> simp
  simp only [hterm]
  rw [sum_agreeOff_comp (blockEmb o (le_refl N)) (fun _ => false)
    (fun z => if z ∈ accepting m then ‖Φ.ofLp z‖ ^ 2 else 0),
    UniformVerifierFamily.acceptProb, measureProb, ← sum_filter, filter_mem_eq_inter, univ_inter]

/-- **`PromiseQMA(c, s) ⊆ PromiseQMAEXP(c, s)`**. -/
theorem PromiseQMA_subset_PromiseQMAEXP {α : Type} {enc : α ↪ List Bool} {c s : ℕ → ℝ} :
    PromiseQMA c s enc ⊆ PromiseQMAEXP c s enc := by
  rintro Q ⟨U, hU⟩
  refine ⟨ExpVerifierSpec.ofUniform enc U, isExpUniform_ofUniform enc U,
    fun a => ⟨fun ha => ?_, fun ha => ?_⟩⟩
  · obtain ⟨ψ, hψ, hacc⟩ := (hU a).1 ha
    refine ⟨ψ, hψ, ?_⟩
    rwa [acceptProb_ofUniform enc U a ψ]
  · change ∀ ψ : Qubits (U.witnessLength (enc a).length), ‖ψ‖ = 1 →
      (ExpVerifierSpec.ofUniform enc U).acceptProb a ψ ≤ s (enc a).length
    intro ψ hψ
    rw [acceptProb_ofUniform enc U a ψ]
    exact (hU a).2 ha ψ hψ

/-- **`QMA ⊆ QMAEXP`**. -/
theorem QMA_subset_QMAEXP {α : Type} {enc : α ↪ List Bool} :
    QMA enc ⊆ QMAEXP enc :=
  fun _ hA => PromiseQMA_subset_PromiseQMAEXP hA

/-- **`BQP ⊆ QMAEXP`**. -/
theorem BQP_subset_QMAEXP {α : Type} {enc : α ↪ List Bool} :
    BQP enc ⊆ QMAEXP enc :=
  BQP_subset_QMA.trans QMA_subset_QMAEXP

/-- **`NP ⊆ QMAEXP`**. -/
theorem NP_subset_QMAEXP {α : Type} {enc : α ↪ List Bool} :
    NP enc ⊆ QMAEXP enc :=
  NP_subset_QMA.trans QMA_subset_QMAEXP

end Cslib.Complexity
