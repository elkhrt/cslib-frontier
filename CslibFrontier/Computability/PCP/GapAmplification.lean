/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Papers Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Cslib.Computability.Circuit.Boolean.Basic
public import CslibFrontier.Computability.PCP.Amplification
public import CslibFrontier.Computability.PCP.LocalTest.Repetition
public import Mathlib.InformationTheory.Hamming
public import Mathlib.Logic.Equiv.Fin.Basic
import CslibFrontier.Foundations.Data.Hamming
import CslibFrontier.Tactic.LinarithCast
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sigma
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Constraint graph gap amplification, robust assignment testers, and alphabet reduction

This module develops the combinatorial gap-amplification framework for constraint satisfaction
graphs and probabilistically checkable proofs, complementing the existing constraint-graph,
preprocessing, expander-powering, and assignment-tester infrastructure in `Cslib.PCP`:

1. **Relative Hamming distance and error-correcting code robustization**: normalized Hamming
   distance `relHammingDist`, unique decoding within half the minimum relative distance
   (`unique_half_distance_decoding`, `decodeCodeword`), and block-level distance lifting
   (`ecc_robustization`, `ecc_robustization_decode`) showing that a tuple of received codewords
   whose unique decoding violates a constraint is far in flattened bit-distance from every encoded
   satisfying tuple.
2. **Robust assignment testers and single-step composition**: local circuit-tester systems
   `RobustTester` over De Morgan Boolean circuits (`Cslib.Circuits.Circuit`), robust soundness
   `RobustTester.IsValidFor`, constructive single-step composition `RobustTester.compose` reducing
   the alphabet to the inner alphabet while preserving completeness `1`
   (`RobustTester.compose_complete`) and achieving the sharp inclusion-exclusion soundness bound
   `ε₁ + ε₂ - ε₁ * ε₂` (`RobustTester.compose_isValidFor`, `RobustTester.compose_sound`), and a
   bridge `RobustTester.toBinaryAssignmentTester` compiling an ECC-robustized robust assignment
   tester into a binary-constraint `Cslib.PCP.AssignmentTester` for `ConstraintGraph` alphabet
   reduction.
3. **General tester-parameterized gap amplification**: `ConstraintGraph.amplifyWithTester`
   combining expander preprocessing, killed-walk powering, and composition with an arbitrary
   complete and sound `AssignmentTester` (rather than a single fixed tester); parameter existence
   `exists_amplification_params` proving that every positive composition loss, finite alphabet,
   positive expander degree, and spectral bound `μ < 1` yield a killing rate `q`, walk length `T`,
   and threshold `γ ∈ (0, 1]` with doubling gain at least `2`; and the resulting general
   `Amplifier` constructor `amplifierOfTester` and existence theorem
   `exists_amplifier_of_testerFamily`.
4. **Edge-sampling local tests and exponential soundness amplification**: the two-query edge test
   `ConstraintGraph.edgeLocalTest`, its exact acceptance probability `1 - G.unsatFrac σ`,
   independent repetition `LocalTest.repeatAll` achieving soundness `(1 - γ) ^ t`
   (`soundness_amplification_repeatAll`), and end-to-end compilation from any `Amplifier` into a
   constant-query `LocalTest` with completeness `1` and arbitrary constant soundness error
   (`gap_amplification_to_localTest`).
5. **Concrete non-vacuity and sharpness witnesses**: exact unsatisfiability value `1 / 3` for
   `2`-coloring on `K₃` versus satisfiability of `3`-coloring, distance-`1` repetition-code
   robustization, a sharp concrete composition of two `4`-check robust testers attaining exact
   soundness `7 / 16 = 1 / 4 + 1 / 4 - (1 / 4) * (1 / 4)`, and concrete instantiation of
   `exists_amplifier_of_testerFamily` with the full Hadamard assignment tester.

## Main definitions

* `Cslib.PCP.relHammingDist`: normalized Hamming distance on a finite domain.
* `Cslib.PCP.HasRelativeDistance`, `Cslib.PCP.decodeCodeword`: relative-distance codes and unique
  half-distance decoding.
* `Cslib.PCP.RobustTester`, `Cslib.PCP.RobustTester.IsValidFor`: robust assignment-tester systems
  over Boolean circuits.
* `Cslib.PCP.RobustTester.compose`: single-step composition of two robust assignment testers.
* `Cslib.PCP.RobustTester.toBinaryAssignmentTester`: compiling an ECC-robustized robust assignment
  tester into a binary `AssignmentTester`.
* `Cslib.PCP.ConstraintGraph.amplifyWithTester`: preprocessing, powering, and composition with an
  arbitrary assignment tester.
* `Cslib.PCP.amplifierOfTester`: constructing a `Cslib.PCP.Amplifier` from any expander family and
  assignment tester with gain at least `2`.
* `Cslib.PCP.ConstraintGraph.edgeLocalTest`: the two-query edge-sampling local test of a
  constraint graph.

## Main results

* `Cslib.PCP.unique_half_distance_decoding`, `Cslib.PCP.ecc_robustization`,
  `Cslib.PCP.ecc_robustization_decode`: unique decoding and block robustization for error-correcting
  codes.
* `Cslib.PCP.RobustTester.compose_complete`, `Cslib.PCP.RobustTester.compose_isValidFor`,
  `Cslib.PCP.RobustTester.compose_sound`: completeness, preserved robustness, and
  inclusion-exclusion soundness `ε₁ + ε₂ - ε₁ * ε₂` of single-step composition.
* `Cslib.PCP.isComplete_toBinaryAssignmentTester`, `Cslib.PCP.sound_toBinaryAssignmentTester`:
  completeness and `1 - ε` soundness of the robust-tester-to-graph composition bridge.
* `Cslib.PCP.ConstraintGraph.satisfiable_amplifyWithTester_iff`,
  `Cslib.PCP.ConstraintGraph.le_unsatVal_amplifyWithTester`,
  `Cslib.PCP.ConstraintGraph.min_le_unsatVal_amplifyWithTester`: satisfiability preservation and
  quantitative gap amplification for arbitrary expanders and assignment testers.
* `Cslib.PCP.exists_amplification_params`, `Cslib.PCP.exists_amplifier_of_testerFamily`:
  existence of doubling amplification parameters and gap amplifiers for arbitrary expanders and
  assignment-tester families.
* `Cslib.PCP.ConstraintGraph.soundness_amplification_repeatAll`,
  `Cslib.PCP.gap_amplification_to_localTest`: exponential soundness amplification and
  constant-query local tests from any gap amplifier.
-/

@[expose] public section

namespace Cslib.PCP

open Finset Cslib.Circuits
open scoped BigOperators

/-! ### Relative Hamming distance and error-correcting code robustization -/

section RelativeHamming

variable {ι α β : Type*} [Fintype ι] [DecidableEq β]

/-- The **relative Hamming distance** between two functions on a finite domain `ι`: the fraction of
coordinates on which they disagree, and `0` when `ι` is empty. -/
noncomputable def relHammingDist (f g : ι → β) : ℝ :=
  (hammingDist f g : ℝ) / Fintype.card ι

@[simp]
theorem relHammingDist_self (f : ι → β) : relHammingDist f f = 0 := by
  simp [relHammingDist]

theorem relHammingDist_symm (f g : ι → β) : relHammingDist f g = relHammingDist g f := by
  rw [relHammingDist, relHammingDist, hammingDist_comm]

theorem relHammingDist_nonneg (f g : ι → β) : 0 ≤ relHammingDist f g := by
  unfold relHammingDist
  positivity

theorem relHammingDist_le_one (f g : ι → β) : relHammingDist f g ≤ 1 :=
  div_le_one_of_le₀ (by exact_mod_cast hammingDist_le_card_fintype) (Nat.cast_nonneg _)

theorem relHammingDist_triangle (f g h : ι → β) :
    relHammingDist f h ≤ relHammingDist f g + relHammingDist g h := by
  unfold relHammingDist
  rw [← add_div]
  refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
  exact_mod_cast hammingDist_triangle f g h

/-- Reindexing the domain along an equivalence preserves relative Hamming distance. -/
theorem relHammingDist_comp_equiv {ι' : Type*} [Fintype ι'] (e : ι' ≃ ι) (f g : ι → β) :
    relHammingDist (f ∘ e) (g ∘ e) = relHammingDist f g := by
  unfold relHammingDist
  rw [Fintype.card_congr e]
  congr 1
  norm_cast
  unfold hammingDist
  refine Finset.card_bij (fun i _ => e i) (fun i hi => ?_) (fun _ _ _ _ h => e.injective h)
    (fun j hj => ?_)
  · simp only [mem_filter, mem_univ, true_and, Function.comp_apply] at hi ⊢
    exact hi
  · refine ⟨e.symm j, ?_, e.apply_symm_apply j⟩
    simp only [mem_filter, mem_univ, true_and, Function.comp_apply, e.apply_symm_apply] at hj ⊢
    exact hj

/-- An encoding `enc : α → ι → β` has **minimum relative distance at least `δ`** when distinct
symbols map to codewords at relative Hamming distance at least `δ`. -/
def HasRelativeDistance (enc : α → ι → β) (δ : ℝ) : Prop :=
  ∀ u v : α, u ≠ v → δ ≤ relHammingDist (enc u) (enc v)

/-- **Unique half-distance decoding**: distinct codewords of a code with minimum relative distance
at least `δ` have disjoint open relative Hamming balls of radius `δ / 2`. -/
theorem unique_half_distance_decoding {enc : α → ι → β} {δ : ℝ}
    (hcode : HasRelativeDistance enc δ) {u v : α} {r : ι → β}
    (hu : relHammingDist r (enc u) < δ / 2)
    (hv : relHammingDist r (enc v) < δ / 2) : u = v := by
  by_contra hne
  have hdist := hcode u v hne
  have htri := relHammingDist_triangle (enc u) r (enc v)
  rw [relHammingDist_symm (enc u) r] at htri
  linarith

open Classical in
/-- Canonical unique-ball decoder for a code `enc` with minimum relative distance `δ`: returns the
unique symbol whose codeword lies within relative Hamming distance `< δ / 2` of `r`, or an
arbitrary symbol when no such codeword exists. -/
noncomputable def decodeCodeword [Nonempty α] (enc : α → ι → β) (δ : ℝ) (r : ι → β) : α :=
  if h : ∃ u : α, relHammingDist r (enc u) < δ / 2 then h.choose else Classical.arbitrary α

/-- A received word within relative Hamming distance `< δ / 2` of `enc u` decodes to `u`. -/
theorem decodeCodeword_eq_of_lt [Nonempty α] {enc : α → ι → β} {δ : ℝ}
    (hcode : HasRelativeDistance enc δ) {r : ι → β} {u : α}
    (h : relHammingDist r (enc u) < δ / 2) :
    decodeCodeword enc δ r = u := by
  have hex : ∃ v : α, relHammingDist r (enc v) < δ / 2 := ⟨u, h⟩
  rw [decodeCodeword, dite_eq_left hex]
  exact unique_half_distance_decoding hcode hex.choose_spec h

/-- Any codeword decodes back to its original symbol when the minimum relative distance is
positive. -/
theorem decodeCodeword_encode [Nonempty α] {enc : α → ι → β} {δ : ℝ}
    (hcode : HasRelativeDistance enc δ) (hδ : 0 < δ) (u : α) :
    decodeCodeword enc δ (enc u) = u :=
  decodeCodeword_eq_of_lt hcode (by rw [relHammingDist_self]; linarith)

/-- **Error-correcting code robustization**: let `enc : α → W → β` have minimum relative distance
at least `δ`. If a received tuple `y : L → W → β` has no tuple `x : L → α` satisfying `P x` whose
codewords all lie within relative Hamming distance `< δ / 2` of `y`, then the flattened word
`Function.uncurry y : L × W → β` is at relative Hamming distance at least `δ / (2 * |L|)` from the
flattened encoding of every tuple satisfying `P`. -/
theorem ecc_robustization {L W : Type*} [Fintype L] [Nonempty L] [Fintype W] [Nonempty W]
    {enc : α → W → β} {δ : ℝ} (hcode : HasRelativeDistance enc δ)
    (P : (L → α) → Prop) (y : L → W → β)
    (hfar : ¬ ∃ x : L → α, P x ∧ ∀ j : L, relHammingDist (y j) (enc (x j)) < δ / 2) :
    (∀ {u v : α} {r : W → β},
      relHammingDist r (enc u) < δ / 2 → relHammingDist r (enc v) < δ / 2 → u = v) ∧
    (∀ x' : L → α, P x' →
      δ / (2 * (Fintype.card L : ℝ)) ≤
        relHammingDist (Function.uncurry y) (Function.uncurry (enc ∘ x'))) := by
  refine ⟨fun hu hv => unique_half_distance_decoding hcode hu hv, fun x' hx' => ?_⟩
  have hex : ∃ j₀ : L, δ / 2 ≤ relHammingDist (y j₀) (enc (x' j₀)) := by
    by_contra hall
    push Not at hall
    exact hfar ⟨x', hx', hall⟩
  obtain ⟨j₀, hj₀⟩ := hex
  have hdis : hammingDist (y j₀) (enc (x' j₀)) ≤
      hammingDist (Function.uncurry y) (Function.uncurry (enc ∘ x')) := by
    let emb : W ↪ L × W := ⟨fun w => (j₀, w), fun _ _ h => (Prod.mk.inj h).2⟩
    unfold hammingDist
    rw [← Finset.card_map emb]
    refine Finset.card_le_card fun p hp => ?_
    obtain ⟨w, hw, rfl⟩ := Finset.mem_map.mp hp
    rw [Finset.mem_filter] at hw ⊢
    exact ⟨Finset.mem_univ _, hw.2⟩
  have hL_pos : (0 : ℝ) < Fintype.card L := Nat.cast_pos.mpr Fintype.card_pos
  have hW_pos : (0 : ℝ) < Fintype.card W := Nat.cast_pos.mpr Fintype.card_pos
  have hLW_pos : (0 : ℝ) < Fintype.card L * Fintype.card W := mul_pos hL_pos hW_pos
  have hj₀' : (δ / 2) * (Fintype.card W : ℝ) ≤ (hammingDist (y j₀) (enc (x' j₀)) : ℝ) :=
    (le_div_iff₀ hW_pos).mp hj₀
  unfold relHammingDist
  rw [Fintype.card_prod, Nat.cast_mul, le_div_iff₀ hLW_pos]
  calc
    δ / (2 * (Fintype.card L : ℝ)) * ((Fintype.card L : ℝ) * (Fintype.card W : ℝ))
        = (δ / 2) * (Fintype.card W : ℝ) := by field_simp
    _ ≤ (hammingDist (y j₀) (enc (x' j₀)) : ℝ) := hj₀'
    _ ≤ (hammingDist (Function.uncurry y) (Function.uncurry (enc ∘ x')) : ℝ) := by
          exact_mod_cast hdis

/-- **ECC robustization via unique decoding**: if the symbol-by-symbol decoded tuple
`fun j => decodeCodeword enc δ (y j)` violates `P`, then the flattened word `Function.uncurry y`
is at relative Hamming distance at least `δ / (2 * |L|)` from every encoded satisfying tuple. -/
theorem ecc_robustization_decode [Nonempty α] {L W : Type*} [Fintype L] [Nonempty L]
    [Fintype W] [Nonempty W] {enc : α → W → β} {δ : ℝ}
    (hcode : HasRelativeDistance enc δ) (P : (L → α) → Prop) (y : L → W → β)
    (hviol : ¬ P (fun j => decodeCodeword enc δ (y j))) :
    ∀ x' : L → α, P x' →
      δ / (2 * (Fintype.card L : ℝ)) ≤
        relHammingDist (Function.uncurry y) (Function.uncurry (enc ∘ x')) := by
  refine (ecc_robustization hcode P y ?_).2
  rintro ⟨x, hx, hclose⟩
  have heq : (fun j => decodeCodeword enc δ (y j)) = x :=
    funext fun j => decodeCodeword_eq_of_lt hcode (hclose j)
  exact hviol (heq ▸ hx)

end RelativeHamming

/-! ### Robust assignment testers and single-step composition -/

section RobustTesters

/-- Evaluate a single-output De Morgan Boolean circuit on a bit-string assignment. -/
def evalBoolCircuit {n : ℕ} (c : Circuit Boolean.signature n 1) (x : Fin n → Bool) : Bool :=
  c.eval Boolean.interpretation x 0

@[simp]
theorem evalBoolCircuit_mapInputs {n₁ n₂ : ℕ}
    (c : Circuit Boolean.signature n₁ 1) (f : Fin n₁ → Fin n₂) (x : Fin n₂ → Bool) :
    evalBoolCircuit (c.mapInputs f) x = evalBoolCircuit c (x ∘ f) := by
  simp only [evalBoolCircuit, Circuit.eval_mapInputs]

/-- A **robust assignment-tester system** of `R` local De Morgan Boolean circuits inspecting an
`numX`-bit primary assignment together with `numY` auxiliary `w`-bit proof symbols. Each check
reads `ℓX` primary bits and `ℓY` auxiliary symbols (`ℓX + ℓY * w` bits in total). -/
structure RobustTester (numX numY R ℓX ℓY w : ℕ) where
  /-- The `ℓX` primary input bits queried by check `i`. -/
  varsX : Fin R → Fin ℓX → Fin numX
  /-- The `ℓY` auxiliary `w`-bit proof symbols queried by check `i`. -/
  varsY : Fin R → Fin ℓY → Fin numY
  /-- The local Boolean acceptance circuit evaluated by check `i`. -/
  checkCircuit : Fin R → Circuit Boolean.signature (ℓX + ℓY * w) 1

namespace RobustTester

/-- Assemble the `(ℓX + ℓY * w)`-bit local view read by check `i` from primary assignment `σ`
and auxiliary `w`-bit proof `τ`. -/
def localView {numX numY R ℓX ℓY w : ℕ} (S : RobustTester numX numY R ℓX ℓY w)
    (σ : Fin numX → Bool) (τ : Fin numY → Fin w → Bool) (i : Fin R) :
    Fin (ℓX + ℓY * w) → Bool :=
  Fin.addCases
    (fun a => σ (S.varsX i a))
    (fun idx =>
      let p := finProdFinEquiv.symm idx
      τ (S.varsY i p.1) p.2)

/-- Check `i` is `ρ`-far from satisfiability when its local view has relative Hamming distance at
least `ρ` from every assignment accepted by `S.checkCircuit i`. -/
def IsLocalCheckFar {numX numY R ℓX ℓY w : ℕ} (S : RobustTester numX numY R ℓX ℓY w)
    (σ : Fin numX → Bool) (τ : Fin numY → Fin w → Bool) (ρ : ℝ) (i : Fin R) : Prop :=
  ∀ z : Fin (ℓX + ℓY * w) → Bool,
    evalBoolCircuit (S.checkCircuit i) z = true →
    ρ ≤ relHammingDist (S.localView σ τ i) z

/-- A primary assignment `σ` is `δ`-far from satisfiability of a Boolean circuit `φ` when its
relative Hamming distance to every satisfying assignment of `φ` is at least `δ`. -/
def IsFarFromCircuitSat {numX : ℕ} (φ : Circuit Boolean.signature numX 1)
    (δ : ℝ) (σ : Fin numX → Bool) : Prop :=
  ∀ σ' : Fin numX → Bool, evalBoolCircuit φ σ' = true → δ ≤ relHammingDist σ σ'

open Classical in
/-- `S` is a **`(δ, ε, ρ)`-robust assignment tester** for `φ`:
- completeness `1`: every satisfying assignment `σ` of `φ` has an auxiliary proof `τ` passing
  all `R` local checks;
- `(δ, ε, ρ)`-robust soundness: whenever `σ` is `δ`-far from every satisfying assignment of `φ`,
  for every auxiliary proof `τ` at most `ε * R` checks fail to be `ρ`-far from satisfiability. -/
def IsValidFor {numX numY R ℓX ℓY w : ℕ} (S : RobustTester numX numY R ℓX ℓY w)
    (φ : Circuit Boolean.signature numX 1) (δ ε ρ : ℝ) : Prop :=
  (∀ σ : Fin numX → Bool, evalBoolCircuit φ σ = true →
    ∃ τ : Fin numY → Fin w → Bool,
      ∀ i : Fin R, evalBoolCircuit (S.checkCircuit i) (S.localView σ τ i) = true) ∧
  (∀ σ : Fin numX → Bool, IsFarFromCircuitSat φ δ σ →
    ∀ τ : Fin numY → Fin w → Bool,
      (#(Finset.univ.filter fun i : Fin R => ¬ S.IsLocalCheckFar σ τ ρ i) : ℝ) ≤ ε * R)

/-- The wire-relabeling map used by single-step composition to embed an inner check's
`ℓX₂ + ℓY₂ * w₂` input wires into the composed check's `ℓX₂ + (ℓX₂ + ℓY₂) * w₂` input wires. -/
def composeWireMap {ℓX₁ ℓY₁ w₁ numY₂ R₂ ℓX₂ ℓY₂ w₂ : ℕ}
    (hw₂ : 1 ≤ w₂)
    (T₂ : RobustTester (ℓX₁ + ℓY₁ * w₁) numY₂ R₂ ℓX₂ ℓY₂ w₂) (j : Fin R₂) :
    Fin (ℓX₂ + ℓY₂ * w₂) → Fin (ℓX₂ + (ℓX₂ + ℓY₂) * w₂) :=
  Fin.addCases
    (fun a : Fin ℓX₂ =>
      if (T₂.varsX j a).val < ℓX₁ then
        Fin.castAdd ((ℓX₂ + ℓY₂) * w₂) a
      else
        Fin.natAdd ℓX₂ (finProdFinEquiv (Fin.castAdd ℓY₂ a, ⟨0, hw₂⟩)))
    (fun kw : Fin (ℓY₂ * w₂) =>
      let pq := finProdFinEquiv.symm kw
      Fin.natAdd ℓX₂ (finProdFinEquiv (Fin.natAdd ℓX₂ pq.1, pq.2)))

/-- The wire-relabeling map of single-step composition is injective: distinct inner input bits are
routed to distinct composed check wires. -/
theorem composeWireMap_injective {ℓX₁ ℓY₁ w₁ numY₂ R₂ ℓX₂ ℓY₂ w₂ : ℕ}
    (hw₂ : 1 ≤ w₂)
    (T₂ : RobustTester (ℓX₁ + ℓY₁ * w₁) numY₂ R₂ ℓX₂ ℓY₂ w₂) (j : Fin R₂) :
    Function.Injective (composeWireMap hw₂ T₂ j) := by
  intro u₁ u₂
  refine Fin.addCases (fun a₁ => ?_) (fun kw₁ => ?_) u₁ <;>
    refine Fin.addCases (fun a₂ => ?_) (fun kw₂ => ?_) u₂ <;>
    intro h
  · simp only [composeWireMap, Fin.addCases_left] at h
    split_ifs at h with h₁ h₂
    · exact congrArg (Fin.castAdd _) (Fin.ext (by simpa [Fin.val_castAdd] using congrArg Fin.val h))
    · exfalso
      have hlt := (Fin.castAdd ((ℓX₂ + ℓY₂) * w₂) a₁).isLt
      have heq := congrArg Fin.val h
      simp only [Fin.val_castAdd, Fin.val_natAdd] at heq hlt
      omega
    · exfalso
      have hlt := (Fin.castAdd ((ℓX₂ + ℓY₂) * w₂) a₂).isLt
      have heq := congrArg Fin.val h
      simp only [Fin.val_castAdd, Fin.val_natAdd] at heq hlt
      omega
    · have hnat : finProdFinEquiv (Fin.castAdd ℓY₂ a₁, (⟨0, hw₂⟩ : Fin w₂)) =
          finProdFinEquiv (Fin.castAdd ℓY₂ a₂, (⟨0, hw₂⟩ : Fin w₂)) :=
        Fin.ext (by have := congrArg Fin.val h; simp only [Fin.val_natAdd] at this; omega)
      have hp := Prod.mk.inj (finProdFinEquiv.injective hnat)
      exact congrArg (Fin.castAdd _)
        (Fin.ext (by simpa [Fin.val_castAdd] using congrArg Fin.val hp.1))
  · simp only [composeWireMap, Fin.addCases_left, Fin.addCases_right] at h
    split_ifs at h with h₁
    · exfalso
      have heq := congrArg Fin.val h
      simp only [Fin.val_castAdd, Fin.val_natAdd] at heq
      omega
    · exfalso
      have hnat : finProdFinEquiv (Fin.castAdd ℓY₂ a₁, (⟨0, hw₂⟩ : Fin w₂)) =
          finProdFinEquiv (Fin.natAdd ℓX₂ (finProdFinEquiv.symm kw₂).1,
            (finProdFinEquiv.symm kw₂).2) :=
        Fin.ext (by have := congrArg Fin.val h; simp only [Fin.val_natAdd] at this; omega)
      have hp := congrArg Fin.val (Prod.mk.inj (finProdFinEquiv.injective hnat)).1
      simp only [Fin.val_castAdd, Fin.val_natAdd] at hp
      omega
  · simp only [composeWireMap, Fin.addCases_left, Fin.addCases_right] at h
    split_ifs at h with h₂
    · exfalso
      have heq := congrArg Fin.val h
      simp only [Fin.val_castAdd, Fin.val_natAdd] at heq
      omega
    · exfalso
      have hnat : finProdFinEquiv (Fin.natAdd ℓX₂ (finProdFinEquiv.symm kw₁).1,
            (finProdFinEquiv.symm kw₁).2) =
          finProdFinEquiv (Fin.castAdd ℓY₂ a₂, (⟨0, hw₂⟩ : Fin w₂)) :=
        Fin.ext (by have := congrArg Fin.val h; simp only [Fin.val_natAdd] at this; omega)
      have hp := congrArg Fin.val (Prod.mk.inj (finProdFinEquiv.injective hnat)).1
      simp only [Fin.val_castAdd, Fin.val_natAdd] at hp
      omega
  · simp only [composeWireMap, Fin.addCases_right] at h
    have hnat : finProdFinEquiv (Fin.natAdd ℓX₂ (finProdFinEquiv.symm kw₁).1,
          (finProdFinEquiv.symm kw₁).2) =
        finProdFinEquiv (Fin.natAdd ℓX₂ (finProdFinEquiv.symm kw₂).1,
          (finProdFinEquiv.symm kw₂).2) :=
      Fin.ext (by have := congrArg Fin.val h; simp only [Fin.val_natAdd] at this; omega)
    have hp := Prod.mk.inj (finProdFinEquiv.injective hnat)
    have h1 : (finProdFinEquiv.symm kw₁).1 = (finProdFinEquiv.symm kw₂).1 :=
      Fin.ext (by have := congrArg Fin.val hp.1; simp only [Fin.val_natAdd] at this; omega)
    have hpair : finProdFinEquiv.symm kw₁ = finProdFinEquiv.symm kw₂ :=
      Prod.ext h1 hp.2
    exact congrArg (Fin.natAdd ℓX₂) (finProdFinEquiv.symm.injective hpair)

/-- **Constructive single-step composition of two robust assignment testers**: given an outer
tester `S₁` with `R₁` checks over `w₁`-bit symbols and an inner family `T₂` of testers for the
check circuits of `S₁` with `R₂` checks over `w₂`-bit symbols (`1 ≤ w₂`), produces a single
composed tester with `R₁ * R₂` checks, reduced alphabet width `w₂`, and query counts
`(ℓX₂, ℓX₂ + ℓY₂)`. -/
def compose {numX numY₁ R₁ ℓX₁ ℓY₁ w₁ numY₂ R₂ ℓX₂ ℓY₂ w₂ : ℕ}
    (hw₂ : 1 ≤ w₂)
    (S₁ : RobustTester numX numY₁ R₁ ℓX₁ ℓY₁ w₁)
    (T₂ : Fin R₁ → RobustTester (ℓX₁ + ℓY₁ * w₁) numY₂ R₂ ℓX₂ ℓY₂ w₂)
    (dfltX : Fin numX) :
    RobustTester numX ((numX + numY₁ * w₁) + R₁ * numY₂)
      (R₁ * R₂) ℓX₂ (ℓX₂ + ℓY₂) w₂ where
  varsX ij a :=
    let i := (finProdFinEquiv.symm ij).1
    let j := (finProdFinEquiv.symm ij).2
    let pos := (T₂ i).varsX j a
    if hlt : pos.val < ℓX₁ then S₁.varsX i ⟨pos.val, hlt⟩ else dfltX
  varsY ij b :=
    let i := (finProdFinEquiv.symm ij).1
    let j := (finProdFinEquiv.symm ij).2
    Fin.addCases
      (fun a : Fin ℓX₂ =>
        let pos := (T₂ i).varsX j a
        if hlt : pos.val < ℓX₁ then
          Fin.castAdd (R₁ * numY₂) (Fin.castAdd (numY₁ * w₁) (S₁.varsX i ⟨pos.val, hlt⟩))
        else
          let p := finProdFinEquiv.symm ⟨pos.val - ℓX₁, by omega⟩
          Fin.castAdd (R₁ * numY₂)
            (Fin.natAdd numX (finProdFinEquiv (S₁.varsY i p.1, p.2))))
      (fun b₂ : Fin ℓY₂ =>
        Fin.natAdd (numX + numY₁ * w₁) (finProdFinEquiv (i, (T₂ i).varsY j b₂)))
      b
  checkCircuit ij :=
    let i := (finProdFinEquiv.symm ij).1
    let j := (finProdFinEquiv.symm ij).2
    ((T₂ i).checkCircuit j).mapInputs (composeWireMap hw₂ (T₂ i) j)

/-- Extract the outer auxiliary proof `τ₁` encoded in bit `0` of the first block of a composed
auxiliary proof `τ₃`. -/
def extractOuterProof {numX numY₁ R₁ w₁ numY₂ w₂ : ℕ} (hw₂ : 1 ≤ w₂)
    (τ₃ : Fin ((numX + numY₁ * w₁) + R₁ * numY₂) → Fin w₂ → Bool) :
    Fin numY₁ → Fin w₁ → Bool :=
  fun y₁ b₁ =>
    τ₃ (Fin.castAdd (R₁ * numY₂) (Fin.natAdd numX (finProdFinEquiv (y₁, b₁)))) ⟨0, hw₂⟩

/-- Extract the `i`-th inner auxiliary proof `τ₂ i` from the second block of a composed auxiliary
proof `τ₃`. -/
def extractInnerProof {numX numY₁ R₁ w₁ numY₂ w₂ : ℕ}
    (τ₃ : Fin ((numX + numY₁ * w₁) + R₁ * numY₂) → Fin w₂ → Bool) :
    Fin R₁ → (Fin numY₂ → Fin w₂ → Bool) :=
  fun i y₂ =>
    τ₃ (Fin.natAdd (numX + numY₁ * w₁) (finProdFinEquiv (i, y₂)))

/-- The composed local view precomposed with `composeWireMap` equals the inner local view on the
outer local view and the extracted proofs. -/
theorem localView_compose_comp_wireMap
    {numX numY₁ R₁ ℓX₁ ℓY₁ w₁ numY₂ R₂ ℓX₂ ℓY₂ w₂ : ℕ}
    (hw₂ : 1 ≤ w₂) (S₁ : RobustTester numX numY₁ R₁ ℓX₁ ℓY₁ w₁)
    (T₂ : Fin R₁ → RobustTester (ℓX₁ + ℓY₁ * w₁) numY₂ R₂ ℓX₂ ℓY₂ w₂)
    (dfltX : Fin numX)
    (σ : Fin numX → Bool)
    (τ₃ : Fin ((numX + numY₁ * w₁) + R₁ * numY₂) → Fin w₂ → Bool)
    (ij : Fin (R₁ * R₂)) :
    let i := (finProdFinEquiv.symm ij).1
    let j := (finProdFinEquiv.symm ij).2
    (S₁.compose hw₂ T₂ dfltX).localView σ τ₃ ij ∘ composeWireMap hw₂ (T₂ i) j =
      (T₂ i).localView (S₁.localView σ (extractOuterProof hw₂ τ₃) i)
        (extractInnerProof τ₃ i) j := by
  intro i j
  funext u
  refine Fin.addCases (fun a => ?_) (fun kw => ?_) u
  · dsimp only [Function.comp_apply, compose, localView, composeWireMap, i, j]
    simp only [Fin.addCases_left]
    set pos := (T₂ (finProdFinEquiv.symm ij).1).varsX (finProdFinEquiv.symm ij).2 a
    by_cases hlt : pos.val < ℓX₁
    · have hpos : pos = Fin.castAdd (ℓY₁ * w₁) ⟨pos.val, hlt⟩ := Fin.ext rfl
      rw [ite_eq_left hlt, Fin.addCases_left, dite_eq_left hlt, hpos, Fin.addCases_left]
    · have hpos : pos = Fin.natAdd ℓX₁ ⟨pos.val - ℓX₁, by omega⟩ := by
        apply Fin.ext
        simp only [Fin.val_natAdd]
        omega
      rw [ite_eq_right hlt, Fin.addCases_right, hpos, Fin.addCases_right,
        finProdFinEquiv.symm_apply_apply, Fin.addCases_left]
      have hlt' : ¬ ((T₂ (finProdFinEquiv.symm ij).1).varsX
          (finProdFinEquiv.symm ij).2 a).val < ℓX₁ := hlt
      rw [dite_eq_right hlt']
      rfl
  · simp only [Function.comp_apply, compose, localView, composeWireMap,
      Fin.addCases_right, finProdFinEquiv.symm_apply_apply, extractInnerProof, i, j]

/-- Evaluating a composed check circuit equals evaluating the corresponding inner check circuit on
the outer local view and extracted proofs. -/
theorem eval_compose_checkCircuit
    {numX numY₁ R₁ ℓX₁ ℓY₁ w₁ numY₂ R₂ ℓX₂ ℓY₂ w₂ : ℕ}
    (hw₂ : 1 ≤ w₂) (S₁ : RobustTester numX numY₁ R₁ ℓX₁ ℓY₁ w₁)
    (T₂ : Fin R₁ → RobustTester (ℓX₁ + ℓY₁ * w₁) numY₂ R₂ ℓX₂ ℓY₂ w₂)
    (dfltX : Fin numX)
    (σ : Fin numX → Bool)
    (τ₃ : Fin ((numX + numY₁ * w₁) + R₁ * numY₂) → Fin w₂ → Bool)
    (ij : Fin (R₁ * R₂)) :
    let i := (finProdFinEquiv.symm ij).1
    let j := (finProdFinEquiv.symm ij).2
    evalBoolCircuit ((S₁.compose hw₂ T₂ dfltX).checkCircuit ij)
        ((S₁.compose hw₂ T₂ dfltX).localView σ τ₃ ij) =
      evalBoolCircuit ((T₂ i).checkCircuit j)
        ((T₂ i).localView (S₁.localView σ (extractOuterProof hw₂ τ₃) i)
          (extractInnerProof τ₃ i) j) := by
  intro i j
  change evalBoolCircuit (((T₂ i).checkCircuit j).mapInputs (composeWireMap hw₂ (T₂ i) j)) _ = _
  rw [evalBoolCircuit_mapInputs, localView_compose_comp_wireMap]

/-- **Completeness of single-step composition**: composing complete outer and inner testers
preserves perfect completeness `1`. -/
theorem compose_complete
    {numX numY₁ R₁ ℓX₁ ℓY₁ w₁ numY₂ R₂ ℓX₂ ℓY₂ w₂ : ℕ}
    (hw₂ : 1 ≤ w₂) (dfltX : Fin numX)
    {φ : Circuit Boolean.signature numX 1}
    {S₁ : RobustTester numX numY₁ R₁ ℓX₁ ℓY₁ w₁}
    {T₂ : Fin R₁ → RobustTester (ℓX₁ + ℓY₁ * w₁) numY₂ R₂ ℓX₂ ℓY₂ w₂}
    (hS₁ : ∀ σ : Fin numX → Bool, evalBoolCircuit φ σ = true →
      ∃ τ₁ : Fin numY₁ → Fin w₁ → Bool,
        ∀ i : Fin R₁, evalBoolCircuit (S₁.checkCircuit i) (S₁.localView σ τ₁ i) = true)
    (hT₂ : ∀ (i : Fin R₁) (v : Fin (ℓX₁ + ℓY₁ * w₁) → Bool),
      evalBoolCircuit (S₁.checkCircuit i) v = true →
      ∃ τ₂ : Fin numY₂ → Fin w₂ → Bool,
        ∀ j : Fin R₂, evalBoolCircuit ((T₂ i).checkCircuit j) ((T₂ i).localView v τ₂ j) = true) :
    ∀ σ : Fin numX → Bool, evalBoolCircuit φ σ = true →
      ∃ τ₃ : Fin ((numX + numY₁ * w₁) + R₁ * numY₂) → Fin w₂ → Bool,
        ∀ ij : Fin (R₁ * R₂),
          evalBoolCircuit ((S₁.compose hw₂ T₂ dfltX).checkCircuit ij)
            ((S₁.compose hw₂ T₂ dfltX).localView σ τ₃ ij) = true := by
  intro σ hsat
  obtain ⟨τ₁, hτ₁⟩ := hS₁ σ hsat
  choose τ₂ hτ₂ using fun i : Fin R₁ => hT₂ i (S₁.localView σ τ₁ i) (hτ₁ i)
  let τ₃ : Fin ((numX + numY₁ * w₁) + R₁ * numY₂) → Fin w₂ → Bool :=
    Fin.addCases
      (Fin.addCases
        (fun x _ => σ x)
        (fun yw k =>
          if k.val = 0 then τ₁ (finProdFinEquiv.symm yw).1 (finProdFinEquiv.symm yw).2
          else false))
      (fun iy => τ₂ (finProdFinEquiv.symm iy).1 (finProdFinEquiv.symm iy).2)
  have hex₁ : extractOuterProof hw₂ τ₃ = τ₁ := by
    funext y₁ b₁
    dsimp only [extractOuterProof, τ₃]
    rw [Fin.addCases_left, Fin.addCases_right]
    dsimp only
    rw [ite_eq_left rfl, finProdFinEquiv.symm_apply_apply]
  have hex₂ : extractInnerProof τ₃ = τ₂ := by
    funext i y₂
    dsimp only [extractInnerProof, τ₃]
    rw [Fin.addCases_right, finProdFinEquiv.symm_apply_apply]
  refine ⟨τ₃, fun ij => ?_⟩
  rw [eval_compose_checkCircuit, hex₁, hex₂]
  exact hτ₂ _ _

/-- Inclusion-exclusion counting helper for single-step composition: partitioning `Fin R₁` into
outer-robust (`Good₁`) and non-robust (`Bad₁`) indices bounds any per-index count `f : Fin R₁ → ℝ`
bounded by `ε₂ * R₂` on `Good₁` and by `R₂` on `Bad₁`. -/
private theorem sum_partition_inclusion_exclusion {R₁ R₂ : ℕ} {ε₁ ε₂ : ℝ}
    (hε₁ : ε₁ ≤ 1) (p : Fin R₁ → Prop) [DecidablePred p]
    (hBad : (#(Finset.univ.filter fun i : Fin R₁ => ¬ p i) : ℝ) ≤ ε₁ * R₁)
    (f : Fin R₁ → ℝ)
    (hGood : ∀ i : Fin R₁, p i → f i ≤ ε₂ * R₂)
    (hAll : ∀ i : Fin R₁, f i ≤ R₂) :
    ∑ i : Fin R₁, f i ≤ (ε₁ + ε₂ - ε₁ * ε₂) * ((R₁ * R₂ : ℕ) : ℝ) := by
  let Good₁ := Finset.univ.filter p
  let Bad₁ := Finset.univ.filter fun i : Fin R₁ => ¬ p i
  have hpart : Good₁.card + Bad₁.card = R₁ := by
    simpa only [Good₁, Bad₁, Finset.card_univ, Fintype.card_fin] using
      Finset.card_filter_add_card_filter_not (s := Finset.univ) p
  have hpart_r : (Good₁.card : ℝ) + (Bad₁.card : ℝ) = (R₁ : ℝ) := by exact_mod_cast hpart
  have hsplit : ∑ i : Fin R₁, f i = (∑ i ∈ Good₁, f i) + ∑ i ∈ Bad₁, f i :=
    (Finset.sum_filter_add_sum_filter_not Finset.univ p f).symm
  have hsum_good : ∑ i ∈ Good₁, f i ≤ (Good₁.card : ℝ) * (ε₂ * (R₂ : ℝ)) := by
    calc
      ∑ i ∈ Good₁, f i ≤ ∑ _i ∈ Good₁, ε₂ * (R₂ : ℝ) :=
        Finset.sum_le_sum fun i hi => hGood i (Finset.mem_filter.mp hi).2
      _ = (Good₁.card : ℝ) * (ε₂ * (R₂ : ℝ)) := by simp
  have hsum_bad : ∑ i ∈ Bad₁, f i ≤ (Bad₁.card : ℝ) * (R₂ : ℝ) := by
    calc
      ∑ i ∈ Bad₁, f i ≤ ∑ _i ∈ Bad₁, (R₂ : ℝ) :=
        Finset.sum_le_sum fun i _ => hAll i
      _ = (Bad₁.card : ℝ) * (R₂ : ℝ) := by simp
  rw [hsplit, Nat.cast_mul]
  rcases le_or_gt 0 (1 - ε₂) with h1m | h1m
  · have hid : (Good₁.card : ℝ) * (ε₂ * (R₂ : ℝ)) + (Bad₁.card : ℝ) * (R₂ : ℝ) =
        ε₂ * ((R₁ : ℝ) * (R₂ : ℝ)) + (1 - ε₂) * (Bad₁.card : ℝ) * (R₂ : ℝ) := by
      have hg : (Good₁.card : ℝ) = (R₁ : ℝ) - (Bad₁.card : ℝ) := by linarith
      rw [hg]
      ring
    have hbad_term : (1 - ε₂) * (Bad₁.card : ℝ) * (R₂ : ℝ) ≤
        (1 - ε₂) * (ε₁ * (R₁ : ℝ)) * (R₂ : ℝ) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hBad h1m) (Nat.cast_nonneg R₂)
    calc
      (∑ i ∈ Good₁, f i) + ∑ i ∈ Bad₁, f i
          ≤ (Good₁.card : ℝ) * (ε₂ * (R₂ : ℝ)) + (Bad₁.card : ℝ) * (R₂ : ℝ) :=
            add_le_add hsum_good hsum_bad
      _ = ε₂ * ((R₁ : ℝ) * (R₂ : ℝ)) + (1 - ε₂) * (Bad₁.card : ℝ) * (R₂ : ℝ) := hid
      _ ≤ ε₂ * ((R₁ : ℝ) * (R₂ : ℝ)) + (1 - ε₂) * (ε₁ * (R₁ : ℝ)) * (R₂ : ℝ) := by linarith
      _ = (ε₁ + ε₂ - ε₁ * ε₂) * ((R₁ : ℝ) * (R₂ : ℝ)) := by ring
  · have hge1 : (1 : ℝ) ≤ ε₁ + ε₂ - ε₁ * ε₂ := by
      have : 0 ≤ (1 - ε₁) * (ε₂ - 1) := mul_nonneg (by linarith) (by linarith)
      nlinarith
    have hgood_all : ∑ i ∈ Good₁, f i ≤ (Good₁.card : ℝ) * (R₂ : ℝ) := by
      calc
        ∑ i ∈ Good₁, f i ≤ ∑ _i ∈ Good₁, (R₂ : ℝ) :=
          Finset.sum_le_sum fun i _ => hAll i
        _ = (Good₁.card : ℝ) * (R₂ : ℝ) := by simp
    calc
      (∑ i ∈ Good₁, f i) + ∑ i ∈ Bad₁, f i
          ≤ (Good₁.card : ℝ) * (R₂ : ℝ) + (Bad₁.card : ℝ) * (R₂ : ℝ) :=
            add_le_add hgood_all hsum_bad
      _ = ((Good₁.card : ℝ) + (Bad₁.card : ℝ)) * (R₂ : ℝ) := (add_mul _ _ _).symm
      _ = 1 * ((R₁ : ℝ) * (R₂ : ℝ)) := by rw [hpart_r, one_mul]
      _ ≤ (ε₁ + ε₂ - ε₁ * ε₂) * ((R₁ : ℝ) * (R₂ : ℝ)) :=
            mul_le_mul_of_nonneg_right hge1 (by positivity)

/-- **Single-step robust assignment-tester composition preserves robustness**: composing a
`(δ₁, ε₁, ρ₁)`-robust outer tester `S₁` with a family `T₂` of `(δ₂, ε₂, ρ₂)`-robust inner testers
satisfying `δ₂ ≤ ρ₁` and `ε₁ ≤ 1` yields a
`(δ₁, ε₁ + ε₂ - ε₁ * ε₂, ρ₂ * (ℓX₂ + ℓY₂ * w₂) / (ℓX₂ + (ℓX₂ + ℓY₂) * w₂))`-robust tester for `φ`,
enabling iterated composition. -/
theorem compose_isValidFor
    {numX numY₁ R₁ ℓX₁ ℓY₁ w₁ numY₂ R₂ ℓX₂ ℓY₂ w₂ : ℕ}
    (hw₂ : 1 ≤ w₂) (dfltX : Fin numX)
    {φ : Circuit Boolean.signature numX 1}
    {S₁ : RobustTester numX numY₁ R₁ ℓX₁ ℓY₁ w₁}
    {T₂ : Fin R₁ → RobustTester (ℓX₁ + ℓY₁ * w₁) numY₂ R₂ ℓX₂ ℓY₂ w₂}
    {δ₁ ε₁ ρ₁ δ₂ ε₂ ρ₂ : ℝ}
    (hε₁ : ε₁ ≤ 1) (hρ : δ₂ ≤ ρ₁)
    (hS₁ : S₁.IsValidFor φ δ₁ ε₁ ρ₁)
    (hT₂ : ∀ i : Fin R₁, (T₂ i).IsValidFor (S₁.checkCircuit i) δ₂ ε₂ ρ₂) :
    (S₁.compose hw₂ T₂ dfltX).IsValidFor φ δ₁ (ε₁ + ε₂ - ε₁ * ε₂)
      (ρ₂ * ((ℓX₂ + ℓY₂ * w₂ : ℝ) / (ℓX₂ + (ℓX₂ + ℓY₂) * w₂))) := by
  classical
  set S₃ := S₁.compose hw₂ T₂ dfltX
  set scale : ℝ := (ℓX₂ + ℓY₂ * w₂ : ℝ) / (ℓX₂ + (ℓX₂ + ℓY₂) * w₂)
  set ρ₃ : ℝ := ρ₂ * scale
  refine ⟨compose_complete hw₂ dfltX hS₁.1 (fun i => (hT₂ i).1), fun σ hfar τ₃ => ?_⟩
  let τ₁ := extractOuterProof hw₂ τ₃
  let τ₂ := extractInnerProof τ₃
  have hcard_eq :
      #(Finset.univ.filter fun ij : Fin (R₁ * R₂) => ¬ S₃.IsLocalCheckFar σ τ₃ ρ₃ ij) =
      ∑ i : Fin R₁,
        #(Finset.univ.filter fun j : Fin R₂ =>
            ¬ S₃.IsLocalCheckFar σ τ₃ ρ₃ (finProdFinEquiv (i, j))) := by
    have hbij :
        #(Finset.univ.filter fun ij : Fin (R₁ * R₂) => ¬ S₃.IsLocalCheckFar σ τ₃ ρ₃ ij) =
        #(Finset.univ.filter fun p : Fin R₁ × Fin R₂ =>
            ¬ S₃.IsLocalCheckFar σ τ₃ ρ₃ (finProdFinEquiv p)) := by
      refine Finset.card_bij (fun ij _ => finProdFinEquiv.symm ij)
        (fun ij hij => ?_) (fun _ _ _ _ h => finProdFinEquiv.symm.injective h)
        (fun p hp => ?_)
      · rw [Finset.mem_filter] at hij ⊢
        simpa only [Finset.mem_univ, true_and, finProdFinEquiv.apply_symm_apply] using hij.2
      · rw [Finset.mem_filter] at hp
        refine ⟨finProdFinEquiv p, ?_, finProdFinEquiv.symm_apply_apply p⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp.2⟩
    rw [hbij]
    simp only [Finset.card_filter, Fintype.sum_prod_type]
  rw [hcard_eq, Nat.cast_sum]
  refine sum_partition_inclusion_exclusion hε₁ (fun i => S₁.IsLocalCheckFar σ τ₁ ρ₁ i)
    (hS₁.2 σ hfar τ₁)
    (fun i => (#(Finset.univ.filter fun j : Fin R₂ =>
      ¬ S₃.IsLocalCheckFar σ τ₃ ρ₃ (finProdFinEquiv (i, j))) : ℝ))
    (fun i hi => ?_)
    (fun i => by exact_mod_cast (Finset.card_filter_le _ _).trans (by simp))
  have hfar₂ : IsFarFromCircuitSat (S₁.checkCircuit i) δ₂ (S₁.localView σ τ₁ i) :=
    fun z hz => hρ.trans (hi z hz)
  refine le_trans ?_ ((hT₂ i).2 (S₁.localView σ τ₁ i) hfar₂ (τ₂ i))
  exact_mod_cast Finset.card_le_card fun j hj => by
    rw [Finset.mem_filter] at hj ⊢
    refine ⟨Finset.mem_univ _, fun hinner => hj.2 ?_⟩
    intro z hz
    have hw_inj := composeWireMap_injective hw₂ (T₂ i) j
    have hsat_in : evalBoolCircuit ((T₂ i).checkCircuit j)
        (z ∘ composeWireMap hw₂ (T₂ i) j) = true := by
      have hz' := hz
      simp only [S₃, RobustTester.compose, finProdFinEquiv.symm_apply_apply,
        evalBoolCircuit_mapInputs] at hz'
      exact hz'
    have hdist_in : ρ₂ ≤ relHammingDist ((T₂ i).localView (S₁.localView σ τ₁ i) (τ₂ i) j)
        (z ∘ composeWireMap hw₂ (T₂ i) j) := hinner _ hsat_in
    have hview := localView_compose_comp_wireMap hw₂ S₁ T₂ dfltX σ τ₃ (finProdFinEquiv (i, j))
    simp only [finProdFinEquiv.symm_apply_apply] at hview
    rw [← hview] at hdist_in
    have hham_le :
        hammingDist (S₃.localView σ τ₃ (finProdFinEquiv (i, j)) ∘ composeWireMap hw₂ (T₂ i) j)
          (z ∘ composeWireMap hw₂ (T₂ i) j) ≤
        hammingDist (S₃.localView σ τ₃ (finProdFinEquiv (i, j))) z := by
      let emb : Fin (ℓX₂ + ℓY₂ * w₂) ↪ Fin (ℓX₂ + (ℓX₂ + ℓY₂) * w₂) :=
        ⟨composeWireMap hw₂ (T₂ i) j, hw_inj⟩
      unfold hammingDist
      rw [← Finset.card_map emb]
      refine Finset.card_le_card fun idx hidx => ?_
      obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp hidx
      rw [Finset.mem_filter] at hu ⊢
      exact ⟨Finset.mem_univ _, hu.2⟩
    rcases Nat.eq_zero_or_pos (ℓX₂ + ℓY₂ * w₂) with hzero | hpos
    · have hsc0 : scale = 0 := by
        dsimp only [scale]
        have hz0 : (ℓX₂ + ℓY₂ * w₂ : ℝ) = 0 := by exact_mod_cast hzero
        rw [hz0, zero_div]
      rw [show ρ₃ = 0 by simp [ρ₃, hsc0]]
      exact relHammingDist_nonneg _ _
    · have hpos₁ : (0 : ℝ) < (ℓX₂ + ℓY₂ * w₂ : ℝ) := by exact_mod_cast hpos
      have hpos₂ : (0 : ℝ) < (ℓX₂ + (ℓX₂ + ℓY₂) * w₂ : ℝ) := by
        have hle : ℓX₂ + ℓY₂ * w₂ ≤ ℓX₂ + (ℓX₂ + ℓY₂) * w₂ := by
          gcongr
          exact Nat.le_add_left _ _
        exact_mod_cast Nat.lt_of_lt_of_le hpos hle
      have hsc_nn : 0 ≤ scale := div_nonneg hpos₁.le hpos₂.le
      have hham_r :
          (hammingDist (S₃.localView σ τ₃ (finProdFinEquiv (i, j)) ∘
              composeWireMap hw₂ (T₂ i) j) (z ∘ composeWireMap hw₂ (T₂ i) j) : ℝ) ≤
          (hammingDist (S₃.localView σ τ₃ (finProdFinEquiv (i, j))) z : ℝ) := by
        exact_mod_cast hham_le
      calc
        ρ₃ = ρ₂ * scale := rfl
        _ ≤ relHammingDist (S₃.localView σ τ₃ (finProdFinEquiv (i, j)) ∘
              composeWireMap hw₂ (T₂ i) j) (z ∘ composeWireMap hw₂ (T₂ i) j) * scale :=
            mul_le_mul_of_nonneg_right hdist_in hsc_nn
        _ = (hammingDist (S₃.localView σ τ₃ (finProdFinEquiv (i, j)) ∘
              composeWireMap hw₂ (T₂ i) j) (z ∘ composeWireMap hw₂ (T₂ i) j) : ℝ) /
              (ℓX₂ + (ℓX₂ + ℓY₂) * w₂ : ℝ) := by
            unfold relHammingDist
            simp only [Fintype.card_fin, Nat.cast_add, Nat.cast_mul, scale]
            field_simp [hpos₁.ne', hpos₂.ne']
        _ ≤ (hammingDist (S₃.localView σ τ₃ (finProdFinEquiv (i, j))) z : ℝ) /
              (ℓX₂ + (ℓX₂ + ℓY₂) * w₂ : ℝ) :=
            div_le_div_of_nonneg_right hham_r hpos₂.le
        _ = relHammingDist (S₃.localView σ τ₃ (finProdFinEquiv (i, j))) z := by
            unfold relHammingDist
            simp only [Fintype.card_fin, Nat.cast_add, Nat.cast_mul]

/-- **Soundness of single-step composition**: when `σ` is `δ₁`-far from `Sat(φ)`, `δ₂ ≤ ρ₁`,
`ε₁ ≤ 1`, and `0 < ρ₂`, at most `(ε₁ + ε₂ - ε₁ * ε₂) * (R₁ * R₂)` composed checks accept any
composed auxiliary proof `τ₃`. -/
theorem compose_sound
    {numX numY₁ R₁ ℓX₁ ℓY₁ w₁ numY₂ R₂ ℓX₂ ℓY₂ w₂ : ℕ}
    (hw₂ : 1 ≤ w₂) (dfltX : Fin numX)
    {φ : Circuit Boolean.signature numX 1}
    {S₁ : RobustTester numX numY₁ R₁ ℓX₁ ℓY₁ w₁}
    {T₂ : Fin R₁ → RobustTester (ℓX₁ + ℓY₁ * w₁) numY₂ R₂ ℓX₂ ℓY₂ w₂}
    {δ₁ ε₁ ρ₁ δ₂ ε₂ ρ₂ : ℝ}
    (hε₁ : ε₁ ≤ 1) (hρ₂ : 0 < ρ₂) (hρ : δ₂ ≤ ρ₁)
    (hS₁ : S₁.IsValidFor φ δ₁ ε₁ ρ₁)
    (hT₂ : ∀ i : Fin R₁, (T₂ i).IsValidFor (S₁.checkCircuit i) δ₂ ε₂ ρ₂)
    {σ : Fin numX → Bool} (hfar : IsFarFromCircuitSat φ δ₁ σ)
    (τ₃ : Fin ((numX + numY₁ * w₁) + R₁ * numY₂) → Fin w₂ → Bool) :
    (#(Finset.univ.filter fun ij : Fin (R₁ * R₂) =>
        evalBoolCircuit ((S₁.compose hw₂ T₂ dfltX).checkCircuit ij)
          ((S₁.compose hw₂ T₂ dfltX).localView σ τ₃ ij) = true) : ℝ) ≤
      (ε₁ + ε₂ - ε₁ * ε₂) * ((R₁ * R₂ : ℕ) : ℝ) := by
  classical
  set S₃ := S₁.compose hw₂ T₂ dfltX
  let τ₁ := extractOuterProof hw₂ τ₃
  let τ₂ := extractInnerProof τ₃
  have hacc_eq :
      #(Finset.univ.filter fun ij : Fin (R₁ * R₂) =>
          evalBoolCircuit (S₃.checkCircuit ij) (S₃.localView σ τ₃ ij) = true) =
      ∑ i : Fin R₁,
        #(Finset.univ.filter fun j : Fin R₂ =>
            evalBoolCircuit ((T₂ i).checkCircuit j)
              ((T₂ i).localView (S₁.localView σ τ₁ i) (τ₂ i) j) = true) := by
    have hbij :
        #(Finset.univ.filter fun ij : Fin (R₁ * R₂) =>
            evalBoolCircuit (S₃.checkCircuit ij) (S₃.localView σ τ₃ ij) = true) =
        #(Finset.univ.filter fun p : Fin R₁ × Fin R₂ =>
            evalBoolCircuit ((T₂ p.1).checkCircuit p.2)
              ((T₂ p.1).localView (S₁.localView σ τ₁ p.1) (τ₂ p.1) p.2) = true) := by
      refine Finset.card_bij (fun ij _ => finProdFinEquiv.symm ij)
        (fun ij hij => ?_) (fun _ _ _ _ h => finProdFinEquiv.symm.injective h)
        (fun p hp => ?_)
      · rw [Finset.mem_filter] at hij ⊢
        refine ⟨Finset.mem_univ _, ?_⟩
        have hev := eval_compose_checkCircuit hw₂ S₁ T₂ dfltX σ τ₃ ij
        dsimp only at hev
        rw [← hev]
        exact hij.2
      · rw [Finset.mem_filter] at hp
        refine ⟨finProdFinEquiv p, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩,
          finProdFinEquiv.symm_apply_apply p⟩
        have hev := eval_compose_checkCircuit hw₂ S₁ T₂ dfltX σ τ₃ (finProdFinEquiv p)
        simp only [finProdFinEquiv.symm_apply_apply] at hev
        rw [hev]
        exact hp.2
    rw [hbij]
    simp only [Finset.card_filter, Fintype.sum_prod_type]
  rw [hacc_eq, Nat.cast_sum]
  refine sum_partition_inclusion_exclusion hε₁ (fun i => S₁.IsLocalCheckFar σ τ₁ ρ₁ i)
    (hS₁.2 σ hfar τ₁)
    (fun i => (#(Finset.univ.filter fun j : Fin R₂ =>
      evalBoolCircuit ((T₂ i).checkCircuit j)
        ((T₂ i).localView (S₁.localView σ τ₁ i) (τ₂ i) j) = true) : ℝ))
    (fun i hi => ?_)
    (fun i => by exact_mod_cast (Finset.card_filter_le _ _).trans (by simp))
  have hfar₂ : IsFarFromCircuitSat (S₁.checkCircuit i) δ₂ (S₁.localView σ τ₁ i) :=
    fun z hz => hρ.trans (hi z hz)
  refine le_trans ?_ ((hT₂ i).2 (S₁.localView σ τ₁ i) hfar₂ (τ₂ i))
  exact_mod_cast Finset.card_le_card fun j hj => by
    rw [Finset.mem_filter] at hj ⊢
    refine ⟨Finset.mem_univ _, fun hfar_j => ?_⟩
    have hself := hfar_j _ hj.2
    rw [relHammingDist_self] at hself
    linarith

end RobustTester

/-! ### Compiling an ECC-robustized robust tester into a binary `AssignmentTester` -/

/-- Flatten a pair of `w'`-bit tables into a single `2 * w'`-bit assignment. -/
def flattenPairBits {w' : ℕ} (t : Fin 2 → Fin w' → Bool) : Fin (2 * w') → Bool :=
  fun idx =>
    let p := finProdFinEquiv.symm idx
    t p.1 p.2

/-- Relative Hamming distance on flattened pairs coincides with relative Hamming distance on
`Fin 2 × Fin w'`. -/
theorem relHammingDist_flattenPairBits {w' : ℕ} (t₁ t₂ : Fin 2 → Fin w' → Bool) :
    relHammingDist (flattenPairBits t₁) (flattenPairBits t₂) =
      relHammingDist (Function.uncurry t₁) (Function.uncurry t₂) :=
  relHammingDist_comp_equiv finProdFinEquiv.symm (Function.uncurry t₁) (Function.uncurry t₂)

open Classical in
/-- Compile a family of robust assignment testers `tester C` for circuits `circuit C` recognizing
codeword-encoded satisfying pairs of binary constraints `C` into a `Cslib.PCP.AssignmentTester`
whose composition performs alphabet reduction on any `ConstraintGraph`. -/
noncomputable def RobustTester.toBinaryAssignmentTester {α : Type*} {w' numY R ℓX ℓY w : ℕ}
    (enc : α → Fin w' → Bool)
    (circuit : (α → α → Prop) → Circuit Boolean.signature (2 * w') 1)
    (tester : (α → α → Prop) → RobustTester (2 * w') numY R ℓX ℓY w)
    (hcircuit_sat : ∀ C (a b : α), C a b →
      evalBoolCircuit (circuit C) (flattenPairBits ![enc a, enc b]) = true)
    (hcomplete : ∀ C (σ : Fin (2 * w') → Bool), evalBoolCircuit (circuit C) σ = true →
      ∃ τ : Fin numY → Fin w → Bool,
        ∀ r : Fin R, evalBoolCircuit ((tester C).checkCircuit r)
          ((tester C).localView σ τ r) = true) :
    AssignmentTester α (Fin w') (Fin numY × Fin w) (Fin R) (Fin (ℓX + ℓY * w)) Bool where
  test C :=
    { query := fun r q =>
        Fin.addCases
          (fun a => Sum.inl (finProdFinEquiv.symm ((tester C).varsX r a)))
          (fun idx =>
            let p := finProdFinEquiv.symm idx
            Sum.inr ((tester C).varsY r p.1, p.2))
          q
      Accepts := fun r ans => evalBoolCircuit ((tester C).checkCircuit r) ans = true }
  encode := enc
  auxiliary C σ :=
    if h : C (σ 0) (σ 1) then
      let τ := (hcomplete C (flattenPairBits ![enc (σ 0), enc (σ 1)])
        (hcircuit_sat C (σ 0) (σ 1) h)).choose
      fun p => τ p.1 p.2
    else
      fun _ => false

/-- Reading the queries of `toBinaryAssignmentTester` from a proof `π` yields the `localView` of
the underlying `RobustTester`. -/
private theorem toBinaryAssignmentTester_read_eq_localView
    {α : Type*} {w' numY R ℓX ℓY w : ℕ}
    (enc : α → Fin w' → Bool)
    (circuit : (α → α → Prop) → Circuit Boolean.signature (2 * w') 1)
    (tester : (α → α → Prop) → RobustTester (2 * w') numY R ℓX ℓY w)
    (hcircuit_sat : ∀ C (a b : α), C a b →
      evalBoolCircuit (circuit C) (flattenPairBits ![enc a, enc b]) = true)
    (hcomplete : ∀ C (σ : Fin (2 * w') → Bool), evalBoolCircuit (circuit C) σ = true →
      ∃ τ : Fin numY → Fin w → Bool,
        ∀ r : Fin R, evalBoolCircuit ((tester C).checkCircuit r)
          ((tester C).localView σ τ r) = true)
    (C : α → α → Prop) (π : (Fin 2 × Fin w') ⊕ (Fin numY × Fin w) → Bool) (r : Fin R) :
    (fun q => π (((RobustTester.toBinaryAssignmentTester enc circuit tester hcircuit_sat
        hcomplete).test C).query r q)) =
      (tester C).localView
        (flattenPairBits (fun b i => π (.inl (b, i))))
        (fun y k => π (.inr (y, k))) r := by
  funext q
  refine Fin.addCases (fun a => ?_) (fun idx => ?_) q
  · simp [RobustTester.toBinaryAssignmentTester, RobustTester.localView, flattenPairBits]
  · simp [RobustTester.toBinaryAssignmentTester, RobustTester.localView]

/-- **Completeness of the robust-tester-to-binary-assignment-tester bridge.** -/
theorem isComplete_toBinaryAssignmentTester {α : Type*} {w' numY R ℓX ℓY w : ℕ}
    (enc : α → Fin w' → Bool)
    (circuit : (α → α → Prop) → Circuit Boolean.signature (2 * w') 1)
    (tester : (α → α → Prop) → RobustTester (2 * w') numY R ℓX ℓY w)
    (hcircuit_sat : ∀ C (a b : α), C a b →
      evalBoolCircuit (circuit C) (flattenPairBits ![enc a, enc b]) = true)
    (hcomplete : ∀ C (σ : Fin (2 * w') → Bool), evalBoolCircuit (circuit C) σ = true →
      ∃ τ : Fin numY → Fin w → Bool,
        ∀ r : Fin R, evalBoolCircuit ((tester C).checkCircuit r)
          ((tester C).localView σ τ r) = true) :
    (RobustTester.toBinaryAssignmentTester enc circuit tester hcircuit_sat
      hcomplete).IsComplete := by
  intro C σ hσ r
  change evalBoolCircuit ((tester C).checkCircuit r) _ = true
  rw [toBinaryAssignmentTester_read_eq_localView]
  have hfst :
      flattenPairBits (fun b i =>
        (RobustTester.toBinaryAssignmentTester enc circuit tester hcircuit_sat
          hcomplete).honestProof C σ (.inl (b, i))) =
      flattenPairBits ![enc (σ 0), enc (σ 1)] := by
    funext idx
    dsimp only [flattenPairBits, AssignmentTester.honestProof,
      RobustTester.toBinaryAssignmentTester, Sum.elim_inl]
    generalize (finProdFinEquiv.symm idx).1 = b
    fin_cases b <;> rfl
  have hsnd :
      (fun y k => (RobustTester.toBinaryAssignmentTester enc circuit tester hcircuit_sat
        hcomplete).honestProof C σ (.inr (y, k))) =
      (hcomplete C (flattenPairBits ![enc (σ 0), enc (σ 1)])
        (hcircuit_sat C (σ 0) (σ 1) hσ)).choose := by
    funext y k
    simp [AssignmentTester.honestProof, RobustTester.toBinaryAssignmentTester, hσ]
  rw [hfst, hsnd]
  exact (hcomplete C (flattenPairBits ![enc (σ 0), enc (σ 1)])
    (hcircuit_sat C (σ 0) (σ 1) hσ)).choose_spec r

/-- **Soundness of the robust-tester-to-binary-assignment-tester bridge**: combining an ECC of
minimum relative distance `δ_ecc` with a `(δ_ecc / 4, ε, ρ)`-robust tester (`0 < ρ`) yields a
binary `AssignmentTester` with soundness `1 - ε` relative to `decodeCodeword enc δ_ecc`. -/
theorem sound_toBinaryAssignmentTester {α : Type*} [Nonempty α] {w' numY R ℓX ℓY w : ℕ}
    [NeZero w'] [NeZero R]
    (enc : α → Fin w' → Bool) {δ_ecc ε ρ : ℝ}
    (hcode : HasRelativeDistance enc δ_ecc) (hρ : 0 < ρ)
    (circuit : (α → α → Prop) → Circuit Boolean.signature (2 * w') 1)
    (tester : (α → α → Prop) → RobustTester (2 * w') numY R ℓX ℓY w)
    (hcircuit_iff : ∀ C (x : Fin (2 * w') → Bool),
      evalBoolCircuit (circuit C) x = true ↔
        ∃ a b : α, C a b ∧ x = flattenPairBits ![enc a, enc b])
    (hvalid : ∀ C, (tester C).IsValidFor (circuit C) (δ_ecc / 4) ε ρ) :
    (RobustTester.toBinaryAssignmentTester enc circuit tester
        (fun C a b hab => (hcircuit_iff C _).2 ⟨a, b, hab, rfl⟩)
        (fun C => (hvalid C).1)).Sound (decodeCodeword enc δ_ecc) (1 - ε) := by
  classical
  intro C π hviol
  let y : Fin 2 → Fin w' → Bool := fun b i => π (.inl (b, i))
  let σ : Fin (2 * w') → Bool := flattenPairBits y
  let τ : Fin numY → Fin w → Bool := fun j k => π (.inr (j, k))
  have hfar : RobustTester.IsFarFromCircuitSat (circuit C) (δ_ecc / 4) σ := by
    intro z hz
    obtain ⟨a, b, hab, rfl⟩ := (hcircuit_iff C z).1 hz
    have hrob := ecc_robustization_decode hcode (fun x : Fin 2 → α => C (x 0) (x 1)) y hviol
      ![a, b] hab
    simp only [Fintype.card_fin, Nat.cast_ofNat] at hrob
    have h4 : δ_ecc / (2 * 2) = δ_ecc / 4 := by ring
    rw [h4] at hrob
    have hcmp : (enc ∘ ![a, b]) = ![enc a, enc b] := by
      funext i
      fin_cases i <;> rfl
    rw [hcmp, ← relHammingDist_flattenPairBits] at hrob
    exact hrob
  have hbad := (hvalid C).2 σ hfar τ
  have hacc_le :
      (#(Finset.univ.filter fun r : Fin R =>
          ((RobustTester.toBinaryAssignmentTester enc circuit tester
              (fun C a b hab => (hcircuit_iff C _).2 ⟨a, b, hab, rfl⟩)
              (fun C => (hvalid C).1)).test C).Passes π r) : ℝ) ≤ ε * R := by
    refine le_trans ?_ hbad
    exact_mod_cast Finset.card_le_card fun r hr => by
      rw [Finset.mem_filter] at hr ⊢
      refine ⟨Finset.mem_univ _, fun hfar_r => ?_⟩
      have hpass : evalBoolCircuit ((tester C).checkCircuit r) ((tester C).localView σ τ r) =
          true := by
        have hp := hr.2
        change evalBoolCircuit ((tester C).checkCircuit r) _ = true at hp
        rwa [toBinaryAssignmentTester_read_eq_localView] at hp
      have hself := hfar_r _ hpass
      rw [relHammingDist_self] at hself
      linarith
  have hR_pos : (0 : ℝ) < R := Nat.cast_pos.mpr (NeZero.pos R)
  have hprob_le :
      ((RobustTester.toBinaryAssignmentTester enc circuit tester
          (fun C a b hab => (hcircuit_iff C _).2 ⟨a, b, hab, rfl⟩)
          (fun C => (hvalid C).1)).test C).acceptProb π ≤ ε := by
    rw [LocalTest.acceptProb_eq_card_div, Fintype.card_fin]
    exact (div_le_iff₀ hR_pos).2 hacc_le
  linarith

end RobustTesters

/-! ### General gap amplification with arbitrary expanders and assignment testers -/

section GeneralAmplification

universe u

namespace ConstraintGraph

variable {V : Type*} {E : Type u} {α D I P R Q Γ : Type*}
  [Fintype E] [DecidableEq V] [Fintype D]
  (G : ConstraintGraph V E α) {μ : ℝ} (X : G.PreprocessExpanders D μ)

/-- **General gap amplification round** parameterized by supplied expander rotations `X`,
killed-walk parameters `(T, q)`, and an arbitrary binary-constraint `AssignmentTester` `AT`
reducing the powered alphabet back to `Γ × (Q → Γ)`. -/
def amplifyWithTester (T q : ℕ) [NeZero q]
    (AT : AssignmentTester (WalkLabels (PreprocessLabel D) T → α) I P R Q Γ) :
    ConstraintGraph
      (AssignmentTester.ComposePos (E × Bool) (Amplification.Dart D E T q) I P ⊕
        Amplification.Dart D E T q × R)
      ((Amplification.Dart D E T q × R) × Q)
      (Γ × (Q → Γ)) :=
  AT.compose ((G.preprocessWith X).power T q).toConstraintGraph

/-- **Completeness and qualitative soundness** of a tester-parameterized amplification round:
satisfiability is preserved whenever the expander has spectral gap `μ < 1`, `1 ≤ T`, `2 ≤ q`, and
`AT` is complete and sound with positive rejection probability `δ`. -/
theorem satisfiable_amplifyWithTester_iff
    [Nonempty α] [Nonempty D] [Fintype R] [Nonempty R]
    [Finite Q] [Nonempty Q] [Nonempty Γ]
    {T q : ℕ} [NeZero q]
    {AT : AssignmentTester (WalkLabels (PreprocessLabel D) T → α) I P R Q Γ}
    {decode : (I → Γ) → WalkLabels (PreprocessLabel D) T → α} {δ : ℝ}
    (hμ : μ < 1) (hT : 1 ≤ T) (hq : 2 ≤ q)
    (hcomplete : AT.IsComplete) (hsound : AT.Sound decode δ) (hδ : 0 < δ) :
    (G.amplifyWithTester X T q AT).Satisfiable ↔ G.Satisfiable := by
  rw [amplifyWithTester, AssignmentTester.satisfiable_compose_iff hcomplete hsound hδ,
    RegularConstraintGraph.satisfiable_power_iff _ _ _ hT hq,
    G.satisfiable_preprocessWith_iff X hμ]

/-- **Quantitative amplification bound** for an arbitrary expander family and assignment tester:
preprocessing retains `Amplification.retention |D| μ`, powering gains linearly in `q - 1`, and
composition loses at most `|Q| / δ`. -/
theorem le_unsatVal_amplifyWithTester
    [Fintype α] [Nonempty α] [Nonempty D] [Fintype R] [Nonempty R]
    [Fintype Q] [Nonempty Q] [Nonempty Γ]
    {T q : ℕ} [NeZero q]
    {AT : AssignmentTester (WalkLabels (PreprocessLabel D) T → α) I P R Q Γ}
    {decode : (I → Γ) → WalkLabels (PreprocessLabel D) T → α} {δ : ℝ}
    (hμ : μ < 1) (hq : 2 ≤ q) (hT : T = 4 * Fintype.card α * (q - 1))
    (hsound : AT.Sound decode δ) (hδ : 0 < δ) :
    ((q : ℝ) - 1) /
        Amplification.denominator (Fintype.card Q / δ) (Fintype.card α) (Fintype.card D) μ *
        min (Amplification.retention (Fintype.card D) μ * G.unsatVal) (1 / (T : ℝ) ^ 2) ≤
      (G.amplifyWithTester X T q AT).unsatVal :=
  (G.le_div_unsatVal_power_preprocessWith X (Fintype.card Q / δ)
      (div_pos (Nat.cast_pos.mpr Fintype.card_pos) hδ) hμ hq hT).trans
    (AssignmentTester.le_unsatVal_compose hsound hδ _)

/-- **Gap doubling up to threshold `γ`** for an arbitrary expander family and assignment tester
whenever `Amplification.gain (|Q| / δ) |α| |D| T q μ γ ≥ 2`. -/
theorem min_le_unsatVal_amplifyWithTester
    [Fintype α] [Nonempty α] [Nonempty D] [Fintype R] [Nonempty R]
    [Fintype Q] [Nonempty Q] [Nonempty Γ]
    {T q : ℕ} [NeZero q]
    {AT : AssignmentTester (WalkLabels (PreprocessLabel D) T → α) I P R Q Γ}
    {decode : (I → Γ) → WalkLabels (PreprocessLabel D) T → α} {δ γ : ℝ}
    (hμ : μ < 1) (hq : 2 ≤ q) (hT : T = 4 * Fintype.card α * (q - 1))
    (hγ : 0 ≤ γ)
    (hgain : 2 ≤ Amplification.gain (Fintype.card Q / δ) (Fintype.card α) (Fintype.card D)
      T q μ γ)
    (hsound : AT.Sound decode δ) (hδ : 0 < δ) :
    min (2 * G.unsatVal) γ ≤ (G.amplifyWithTester X T q AT).unsatVal :=
  (G.min_le_div_unsatVal_power_preprocessWith X (Fintype.card Q / δ)
      (div_pos (Nat.cast_pos.mpr Fintype.card_pos) hδ) hμ hq hT hγ hgain).trans
    (AssignmentTester.le_unsatVal_compose hsound hδ _)

/-- Exact vertex count of a tester-parameterized amplification round: linear in `|E|`, with factor
depending only on `|D|`, `T`, `q`, `|I|`, `|P|`, and `|R|`. -/
theorem card_vertices_amplifyWithTester [Fintype I] [Fintype P] [Fintype R] (T q : ℕ) :
    Fintype.card
        (AssignmentTester.ComposePos (E × Bool) (Amplification.Dart D E T q) I P ⊕
          Amplification.Dart D E T q × R) =
      (2 * Fintype.card I +
        2 * ((2 * Fintype.card D + 2) * q) ^ T * (Fintype.card P + Fintype.card R)) *
        Fintype.card E := by
  simp only [AssignmentTester.ComposePos, Fintype.card_sum, Fintype.card_prod, Fintype.card_bool,
    Fintype.card_fun, Fintype.card_unit, Fintype.card_fin, mul_pow]
  ring

/-- Exact edge count of a tester-parameterized amplification round: linear in `|E|`, with factor
depending only on `|D|`, `T`, `q`, `|R|`, and `|Q|`. -/
theorem card_edges_amplifyWithTester [Fintype R] [Fintype Q] (T q : ℕ) :
    Fintype.card ((Amplification.Dart D E T q × R) × Q) =
      (2 * ((2 * Fintype.card D + 2) * q) ^ T * Fintype.card R * Fintype.card Q) *
        Fintype.card E := by
  simp only [Fintype.card_prod, Fintype.card_bool, Fintype.card_fun, card_label_preprocess,
    Fintype.card_fin, mul_pow]
  ring

end ConstraintGraph

/-- **Existence of gap-doubling amplification parameters**: for every positive composition loss,
positive alphabet size `K`, positive expander degree `d`, and spectral bound `μ < 1`, there exist
a killing rate `q ≥ 2`, walk length `T = 4 * K * (q - 1)`, and threshold `γ ∈ (0, 1]` achieving
scalar amplification gain at least `2`. -/
theorem exists_amplification_params {loss : ℝ} {K d : ℕ} {μ : ℝ}
    (hloss : 0 < loss) (hK : 0 < K) (hd : 0 < d) (hμ : μ < 1) :
    ∃ (q T : ℕ) (γ : ℝ),
      2 ≤ q ∧ T = 4 * K * (q - 1) ∧ 0 < γ ∧ γ ≤ 1 ∧
      2 ≤ ConstraintGraph.Amplification.gain loss K d T q μ γ := by
  set r : ℝ := ConstraintGraph.Amplification.retention d μ
  have hr : 0 < r := ConstraintGraph.Amplification.retention_pos hd hμ
  have hK' : (0 : ℝ) < K := Nat.cast_pos.mpr hK
  have hd' : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  set s : ℝ := (1 - μ) * d / (2 * d + 2)
  have hs : 0 < s := div_pos (mul_pos (sub_pos.mpr hμ) hd') (by positivity)
  set M : ℝ := loss * (2 + 32 * (K : ℝ) ^ 3 / s)
  have hM : 0 < M := by dsimp only [M]; positivity
  obtain ⟨q, hq_gt⟩ := exists_nat_gt (1 + 8 * (K : ℝ) ^ 2 * M / r)
  have hq1 : (1 : ℝ) < q := by
    have : 0 < 8 * (K : ℝ) ^ 2 * M / r := by positivity
    linarith
  have hq : 2 ≤ q := by
    have : 1 < q := by exact_mod_cast hq1
    omega
  set T : ℕ := 4 * K * (q - 1)
  have hT_pos : (0 : ℝ) < T := by
    have : 0 < T := Nat.mul_pos (Nat.mul_pos (by decide) hK) (by omega)
    exact_mod_cast this
  have hT_cast : (T : ℝ) = 4 * (K : ℝ) * ((q : ℝ) - 1) := by
    dsimp only [T]
    push_cast [Nat.cast_sub (by omega : 1 ≤ q)]
    ring
  set c : ℝ := ((q : ℝ) - 1) / (4 * (K : ℝ) ^ 2)
  have hc_pos : 0 < c := div_pos (by linarith) (by positivity)
  have hMc : 2 * M ≤ r * c := by
    have hq_sub : 8 * (K : ℝ) ^ 2 * M / r < (q : ℝ) - 1 := by linarith
    have hmul := (div_lt_iff₀ hr).mp hq_sub
    have : 2 * M * (4 * (K : ℝ) ^ 2) < r * ((q : ℝ) - 1) := by linarith
    dsimp only [c]
    rw [mul_div_assoc', le_div_iff₀ (by positivity)]
    linarith
  set γ : ℝ := min 1 (2 * c / ((T : ℝ) ^ 2 * r))
  have hγ_pos : 0 < γ := lt_min zero_lt_one (by positivity)
  have hγ_le : γ ≤ 1 := min_le_left _ _
  have hterm : (T : ℝ) ^ 2 * (r * γ / 2) ≤ c := by
    calc
      (T : ℝ) ^ 2 * (r * γ / 2)
          ≤ (T : ℝ) ^ 2 * (r * (2 * c / ((T : ℝ) ^ 2 * r)) / 2) := by
            gcongr
            exact min_le_right _ _
      _ = c := by
            field_simp [hT_pos.ne', hr.ne']
  have h2T : 2 * (T : ℝ) / s = (32 * (K : ℝ) ^ 3 / s) * c := by
    rw [hT_cast]
    dsimp only [c]
    field_simp [hK'.ne', hs.ne']
    ring
  refine ⟨q, T, γ, hq, rfl, hγ_pos, hγ_le, ?_⟩
  unfold ConstraintGraph.Amplification.gain
  change 2 ≤ r * c ^ 2 / (loss * (c + (T : ℝ) ^ 2 * (r * γ / 2) + 2 * (T : ℝ) / s))
  have hden_pos : 0 < loss * (c + (T : ℝ) ^ 2 * (r * γ / 2) + 2 * (T : ℝ) / s) := by
    positivity
  have hden_le : loss * (c + (T : ℝ) ^ 2 * (r * γ / 2) + 2 * (T : ℝ) / s) ≤ M * c := by
    calc
      loss * (c + (T : ℝ) ^ 2 * (r * γ / 2) + 2 * (T : ℝ) / s)
          ≤ loss * (c + c + (32 * (K : ℝ) ^ 3 / s) * c) := by
            rw [h2T]
            gcongr
      _ = M * c := by dsimp only [M]; ring
  rw [le_div_iff₀ hden_pos]
  calc
    2 * (loss * (c + (T : ℝ) ^ 2 * (r * γ / 2) + 2 * (T : ℝ) / s))
        ≤ 2 * (M * c) := by gcongr
    _ = (2 * M) * c := by ring
    _ ≤ (r * c) * c := mul_le_mul_of_nonneg_right hMc hc_pos.le
    _ = r * c ^ 2 := by ring

/-- **Construct a `Cslib.PCP.Amplifier` from any expander family and complete, sound
`AssignmentTester`** whose scalar gain is at least `2`. -/
noncomputable def amplifierOfTester
    {D Q Γ I P R : Type} [Fintype D] [Nonempty D]
    [Fintype Q] [DecidableEq Q] [Nonempty Q] [Fintype Γ] [Nonempty Γ]
    [Fintype I] [Fintype P] [Fintype R] [Nonempty R]
    {μ : ℝ} (X : RotationMap.ExpanderFamily.{u} D μ) (hμ : μ < 1)
    (T q : ℕ) [NeZero q] (hq : 2 ≤ q)
    (hT : T = 4 * Fintype.card (Γ × (Q → Γ)) * (q - 1))
    {γ δ : ℝ} (hγ_pos : 0 < γ) (hγ_le : γ ≤ 1) (hδ : 0 < δ)
    (AT : AssignmentTester (WalkLabels (ConstraintGraph.PreprocessLabel D) T → Γ × (Q → Γ))
      I P R Q Γ)
    (hcomplete : AT.IsComplete)
    (decode : (I → Γ) → WalkLabels (ConstraintGraph.PreprocessLabel D) T → Γ × (Q → Γ))
    (hsound : AT.Sound decode δ)
    (hgain : 2 ≤ ConstraintGraph.Amplification.gain (Fintype.card Q / δ)
      (Fintype.card (Γ × (Q → Γ))) (Fintype.card D) T q μ γ) :
    Amplifier.{u} (Γ × (Q → Γ)) :=
  have hT₁ : 1 ≤ T := by
    rw [hT]
    exact Nat.mul_pos (Nat.mul_pos (by decide) Fintype.card_pos) (by omega)
  let vFac := 2 * Fintype.card I +
    2 * ((2 * Fintype.card D + 2) * q) ^ T * (Fintype.card P + Fintype.card R)
  let eFac := 2 * ((2 * Fintype.card D + 2) * q) ^ T * Fintype.card R * Fintype.card Q
  { toFun := fun G =>
      letI := Classical.decEq G.V
      ⟨AssignmentTester.ComposePos (G.E × Bool)
          (ConstraintGraph.Amplification.Dart D G.E T q) I P ⊕
          ConstraintGraph.Amplification.Dart D G.E T q × R,
        (ConstraintGraph.Amplification.Dart D G.E T q × R) × Q,
        G.graph.amplifyWithTester (.ofFamily G.graph X) T q AT⟩
    factor := vFac + eFac
    gap := γ
    gap_pos := hγ_pos
    gap_le_one := hγ_le
    card_vertices_le := fun G => by
      simpa only [vFac] using
        (ConstraintGraph.card_vertices_amplifyWithTester
            (D := D) (E := G.E) (I := I) (P := P) (R := R) T q).trans_le
          (Nat.mul_le_mul_right _ (Nat.le_add_right _ _))
    card_edges_le := fun G => by
      simpa only [eFac] using
        (ConstraintGraph.card_edges_amplifyWithTester
            (D := D) (E := G.E) (R := R) (Q := Q) T q).trans_le
          (Nat.mul_le_mul_right _ (Nat.le_add_left _ _))
    satisfiable_iff := fun G =>
      letI := Classical.decEq G.V
      G.graph.satisfiable_amplifyWithTester_iff (.ofFamily G.graph X) hμ hT₁ hq
        hcomplete hsound hδ
    min_le_unsatVal := fun G =>
      letI := Classical.decEq G.V
      G.graph.min_le_unsatVal_amplifyWithTester (.ofFamily G.graph X) hμ hq hT
        hγ_pos.le hgain hsound hδ }

/-- **Universal existence of a gap amplifier**: any expander family with spectral bound `μ < 1`
together with any family of complete, uniformly `δ`-sound (`0 < δ`) assignment testers reducing
every powered alphabet back to `Γ × (Q → Γ)` yields a `Cslib.PCP.Amplifier` over `Γ × (Q → Γ)`. -/
theorem exists_amplifier_of_testerFamily
    {D Q Γ : Type} [Fintype D] [Nonempty D]
    [Finite Q] [Nonempty Q] [Finite Γ] [Nonempty Γ]
    {μ δ : ℝ} (X : RotationMap.ExpanderFamily.{u} D μ) (hμ : μ < 1) (hδ : 0 < δ)
    (I P R : ℕ → Type) [∀ T, Finite (I T)] [∀ T, Finite (P T)]
    [∀ T, Fintype (R T)] [∀ T, Nonempty (R T)]
    (AT : (T : ℕ) →
      AssignmentTester (WalkLabels (ConstraintGraph.PreprocessLabel D) T → Γ × (Q → Γ))
        (I T) (P T) (R T) Q Γ)
    (hcomplete : ∀ T, (AT T).IsComplete)
    (decode : (T : ℕ) → (I T → Γ) → WalkLabels (ConstraintGraph.PreprocessLabel D) T → Γ × (Q → Γ))
    (hsound : ∀ T, (AT T).Sound (decode T) δ) :
    Nonempty (Amplifier.{u} (Γ × (Q → Γ))) := by
  classical
  let := Fintype.ofFinite Q
  let := Fintype.ofFinite Γ
  obtain ⟨q, T, γ, hq, hT, hγ_pos, hγ_le, hgain⟩ :=
    exists_amplification_params (loss := Fintype.card Q / δ)
      (K := Fintype.card (Γ × (Q → Γ))) (d := Fintype.card D) (μ := μ)
      (div_pos (Nat.cast_pos.mpr Fintype.card_pos) hδ) Fintype.card_pos Fintype.card_pos hμ
  have : NeZero q := ⟨by omega⟩
  let := Fintype.ofFinite (I T)
  let := Fintype.ofFinite (P T)
  exact ⟨amplifierOfTester X hμ T q hq hT hγ_pos hγ_le hδ (AT T) (hcomplete T)
    (decode T) (hsound T) hgain⟩

end GeneralAmplification

/-! ### Edge-sampling local test and exponential soundness amplification -/

section EdgeLocalTest

namespace ConstraintGraph

variable {V E α : Type*} (G : ConstraintGraph V E α)

/-- The **two-query edge-sampling local test** of a constraint graph: pick a uniformly random edge,
query the labels of its two endpoints, and accept when they satisfy its constraint. -/
def edgeLocalTest : LocalTest V E (Fin 2) α where
  query e := G.ends e
  Accepts e a := G.rel e (a 0) (a 1)

@[simp]
theorem passes_edgeLocalTest {σ : V → α} {e : E} :
    G.edgeLocalTest.Passes σ e ↔ G.Satisfies σ e :=
  Iff.rfl

/-- The acceptance probability of the edge-sampling test is `1 - G.unsatFrac σ`. -/
theorem acceptProb_edgeLocalTest [Fintype E] [Nonempty E] (σ : V → α) :
    G.edgeLocalTest.acceptProb σ = 1 - G.unsatFrac σ := by
  classical
  have h := LocalTest.one_sub_acceptProb G.edgeLocalTest σ
  have hunsat : G.unsatFrac σ = (#{e | ¬ G.edgeLocalTest.Passes σ e} : ℝ) / Fintype.card E := by
    rfl
  linarith

/-- Running `t` independent edge samples accepts a labelling `σ` with probability
`(1 - G.unsatFrac σ) ^ t`. -/
theorem acceptProb_repeatAll_edgeLocalTest [Fintype E] [Nonempty E] (t : ℕ) (σ : V → α) :
    (G.edgeLocalTest.repeatAll t).acceptProb σ = (1 - G.unsatFrac σ) ^ t := by
  rw [LocalTest.acceptProb_repeatAll, G.acceptProb_edgeLocalTest]

/-- **Completeness of repeated edge sampling**: a satisfying labelling passes all `t` independent
edge samples on every random tuple, and achieves acceptance probability `1` whenever `E` is
nonempty. -/
theorem completeness_repeatAll_edgeLocalTest {σ : V → α} (hσ : ∀ e, G.Satisfies σ e) (t : ℕ) :
    (∀ r : Fin t → E, (G.edgeLocalTest.repeatAll t).Passes σ r) ∧
      ([Fintype E] → [Nonempty E] → (G.edgeLocalTest.repeatAll t).acceptProb σ = 1) := by
  refine ⟨fun r j => hσ (r j), ?_⟩
  exact (LocalTest.acceptProb_eq_one_iff _).2 fun r j => hσ (r j)

/-- **Exponential soundness amplification by independent repetition**: if `γ ≤ G.unsatVal`, then
`t` independent edge checks accept every labelling with probability at most `(1 - γ) ^ t`. -/
theorem soundness_amplification_repeatAll [Fintype E] [Nonempty E] {γ : ℝ}
    (hγ : γ ≤ G.unsatVal) (t : ℕ) (σ : V → α) :
    (G.edgeLocalTest.repeatAll t).acceptProb σ ≤ (1 - γ) ^ t := by
  rw [G.acceptProb_repeatAll_edgeLocalTest]
  exact pow_le_pow_left₀ (sub_nonneg.2 (G.unsatFrac_le_one σ))
    (sub_le_sub_left (hγ.trans (G.unsatVal_le σ)) 1) t

/-- For any positive unsatisfiability gap `γ` and any target soundness error `ε > 0`, a universal
constant number `t` of independent edge samples reduces acceptance probability to at most `ε` on
every constraint graph of value at least `γ`. -/
theorem exists_repetition_soundness_le {γ ε : ℝ} (hγ : 0 < γ) (hε : 0 < ε) :
    ∃ t : ℕ, ∀ {V E α : Type*} [Fintype E] [Nonempty E] (G : ConstraintGraph V E α),
      γ ≤ G.unsatVal → ∀ σ : V → α, (G.edgeLocalTest.repeatAll t).acceptProb σ ≤ ε := by
  set γ' : ℝ := min γ 1
  have hγ'_pos : 0 < γ' := lt_min hγ zero_lt_one
  obtain ⟨t, ht⟩ := exists_pow_lt_of_lt_one hε (show 1 - γ' < 1 by linarith)
  refine ⟨t, fun G hG σ => ?_⟩
  have hG' : γ' ≤ G.unsatVal := (min_le_left _ _).trans hG
  exact (G.soundness_amplification_repeatAll hG' t σ).trans ht.le

end ConstraintGraph

/-- **End-to-end gap amplification to a constant-query local test**: given any `Amplifier` `A`
over a nonempty alphabet `α` and any target soundness error `ε > 0`, there is a universal constant
`t` such that iterating `A` for `⌈log₂ |E|⌉` rounds and running `t` independent edge checks gives a
`2 * t`-query local test with completeness `1`, soundness error at most `ε` on every unsatisfiable
graph, and polynomial vertex/edge blowup. -/
theorem gap_amplification_to_localTest.{u, v} {α : Type v} [Nonempty α]
    (A : Amplifier.{u} α) {ε : ℝ} (hε : 0 < ε) :
    ∃ t : ℕ, ∀ G : FinConstraintGraph.{u} α,
      let H := A.iter (Nat.clog 2 (Fintype.card G.E)) G
      let T := H.graph.edgeLocalTest.repeatAll t
      (G.graph.Satisfiable → ∃ σ : H.V → α, ∀ r, T.Passes σ r) ∧
      (¬ G.graph.Satisfiable → ∀ σ : H.V → α, T.acceptProb σ ≤ ε) ∧
      Fintype.card (Fin t × Fin 2) = 2 * t ∧
      Fintype.card H.E ≤
        2 ^ Nat.clog 2 A.factor * Fintype.card G.E ^ (Nat.clog 2 A.factor + 1) := by
  obtain ⟨t, ht⟩ := ConstraintGraph.exists_repetition_soundness_le A.gap_pos hε
  refine ⟨t, fun G => ?_⟩
  dsimp only
  set k := Nat.clog 2 (Fintype.card G.E)
  set H := A.iter k G
  refine ⟨fun hsat => ?_, fun hunsat σ => ?_, ?_, A.card_edges_iter_clog_le G⟩
  · obtain ⟨σ, hσ⟩ := (A.satisfiable_iter_iff k G).2 hsat
    exact ⟨σ, fun r j => hσ (r j)⟩
  · have hgap : A.gap ≤ H.graph.unsatVal :=
      A.gap_le_unsatVal_iter hunsat (Nat.le_pow_clog one_lt_two _)
    have : Nonempty H.E := by
      by_contra hempty
      have : IsEmpty H.E := not_nonempty_iff.mp hempty
      have h0 : H.graph.unsatVal = 0 := H.graph.unsatVal_of_isEmpty
      linarith [A.gap_pos]
    exact ht H.graph hgap σ
  · simp [Fintype.card_prod, mul_comm]

end EdgeLocalTest

/-! ### Concrete non-vacuity and sharpness witnesses -/

section Witnesses

/-- The triangle `K₃` as a `2`-coloring constraint graph over `Bool`. -/
def triangleTwoColor : ConstraintGraph (Fin 3) (Fin 3) Bool where
  src i := i
  dst i := i + 1
  rel _ a b := a ≠ b

/-- The triangle `K₃` as a `3`-coloring constraint graph over `Fin 3`. -/
def triangleThreeColor : ConstraintGraph (Fin 3) (Fin 3) (Fin 3) where
  src i := i
  dst i := i + 1
  rel _ a b := a ≠ b

/-- `K₃` is not `2`-colorable. -/
theorem not_satisfiable_triangleTwoColor : ¬ triangleTwoColor.Satisfiable := by
  rintro ⟨σ, hσ⟩
  have h0 : σ 0 ≠ σ 1 := hσ 0
  have h1 : σ 1 ≠ σ 2 := hσ 1
  have h2 : σ 2 ≠ σ 0 := hσ 2
  cases h0' : σ 0 <;> cases h1' : σ 1 <;> cases h2' : σ 2 <;> simp_all

/-- Exact unsatisfiability value `1 / 3` for `2`-coloring on `K₃`. -/
theorem unsatVal_triangleTwoColor : triangleTwoColor.unsatVal = 1 / 3 := by
  refine le_antisymm ?_ ?_
  · let σ : Fin 3 → Bool := ![false, true, false]
    have hcard : #(triangleTwoColor.unsatEdges σ) = 1 := by
      have hset : triangleTwoColor.unsatEdges σ = {2} := by
        ext e
        fin_cases e <;> simp [triangleTwoColor, ConstraintGraph.Satisfies, σ]
      rw [hset, Finset.card_singleton]
    have hfrac : triangleTwoColor.unsatFrac σ = 1 / 3 := by
      rw [ConstraintGraph.unsatFrac, hcard]
      norm_num
    exact (triangleTwoColor.unsatVal_le σ).trans_eq hfrac
  · simpa only [Fintype.card_fin, Nat.cast_ofNat, one_div] using
      triangleTwoColor.inv_card_le_unsatVal not_satisfiable_triangleTwoColor

/-- `K₃` is `3`-colorable, so its `3`-coloring constraint graph has unsatisfiability value `0`. -/
theorem satisfiable_triangleThreeColor :
    triangleThreeColor.Satisfiable ∧ triangleThreeColor.unsatVal = 0 := by
  have hsat : triangleThreeColor.Satisfiable :=
    ⟨id, fun e => by fin_cases e <;> simp [triangleThreeColor, ConstraintGraph.Satisfies]⟩
  exact ⟨hsat, (ConstraintGraph.unsatVal_eq_zero_iff _).2 hsat⟩

/-- The `3`-bit binary repetition code. -/
def rep3Code : Bool → Fin 3 → Bool :=
  fun b _ => b

/-- The `3`-bit repetition code has minimum relative Hamming distance `1`. -/
theorem hasRelativeDistance_rep3Code : HasRelativeDistance rep3Code 1 := by
  intro u v huv
  have hcard : hammingDist (rep3Code u) (rep3Code v) = 3 := by
    cases u <;> cases v
    · exact absurd rfl huv
    · decide
    · decide
    · exact absurd rfl huv
  unfold relHammingDist
  rw [hcard, Fintype.card_fin]
  norm_num

/-- Concrete `ECC` robustization witness: any `2`-symbol word over `Fin 3 → Bool` whose unique
decoding under `rep3Code` fails equality is at relative Hamming distance at least `1 / 4` from
every encoded equal pair. -/
theorem rep3Code_equality_robustization (y : Fin 2 → Fin 3 → Bool)
    (hviol : decodeCodeword rep3Code 1 (y 0) ≠ decodeCodeword rep3Code 1 (y 1)) (b : Bool) :
    (1 / 4 : ℝ) ≤
      relHammingDist (Function.uncurry y) (Function.uncurry (rep3Code ∘ fun _ : Fin 2 => b)) := by
  have h := ecc_robustization_decode hasRelativeDistance_rep3Code
    (fun x : Fin 2 → Bool => x 0 = x 1) y hviol (fun _ => b) rfl
  simp only [Fintype.card_fin, Nat.cast_ofNat] at h
  linarith

/-- One-input Boolean circuit that accepts `x 0 = true` (zero gates). -/
def idBoolCircuit : Circuit Boolean.signature 1 1 :=
  Circuit.wiring Boolean.signature (fun _ => 0)

/-- One-input Boolean circuit that always outputs `true` (one constant gate). -/
def constTrueBoolCircuit : Circuit Boolean.signature 1 1 where
  size := 1
  program := Program.empty.gate ⟨.const true, Fin.elim0⟩
  outputs := fun _ => .gate 0

@[simp]
theorem evalBoolCircuit_idBoolCircuit (x : Fin 1 → Bool) :
    evalBoolCircuit idBoolCircuit x = x 0 :=
  rfl

@[simp]
theorem evalBoolCircuit_constTrueBoolCircuit (x : Fin 1 → Bool) :
    evalBoolCircuit constTrueBoolCircuit x = true :=
  rfl

/-- A concrete `4`-check `(1, 1 / 4, 1)`-robust tester for `idBoolCircuit`: three checks test
`idBoolCircuit` directly and the fourth check always accepts. -/
def quarterErrorTester : RobustTester 1 0 4 1 0 1 where
  varsX _ _ := 0
  varsY _ j := Fin.elim0 j
  checkCircuit i := if i.val < 3 then idBoolCircuit else constTrueBoolCircuit

/-- `quarterErrorTester` is a valid `(1, 1 / 4, 1)`-robust assignment tester for
`idBoolCircuit`. -/
theorem quarterErrorTester_isValidFor :
    quarterErrorTester.IsValidFor idBoolCircuit 1 (1 / 4) 1 := by
  classical
  refine ⟨fun σ hσ => ⟨Fin.elim0, fun i => ?_⟩, fun σ hfar τ => ?_⟩
  · have hview : quarterErrorTester.localView σ Fin.elim0 i = σ := by
      funext k
      fin_cases k
      rfl
    rw [hview]
    dsimp only [quarterErrorTester]
    split_ifs <;> simp [hσ]
  · have hσ0 : σ 0 = false := by
      cases h : σ 0 with
      | false => rfl
      | true =>
        have h1 := hfar σ (by simp [h])
        rw [relHammingDist_self] at h1
        linarith
    have hsub : (Finset.univ.filter fun i : Fin 4 =>
        ¬ quarterErrorTester.IsLocalCheckFar σ τ 1 i) ⊆ {3} := by
      intro i hi
      rw [Finset.mem_filter] at hi
      rw [Finset.mem_singleton]
      by_contra hne
      apply hi.2
      intro z hz
      have hlt : i.val < 3 := by omega
      have hz0 : z 0 = true := by
        simpa [quarterErrorTester, hlt] using hz
      have hv0 : quarterErrorTester.localView σ τ i 0 = false := by
        have h0 : (0 : Fin (1 + 0 * 1)) = Fin.castAdd (0 * 1) 0 := rfl
        rw [h0, RobustTester.localView, Fin.addCases_left]
        exact hσ0
      have hhd : hammingDist (quarterErrorTester.localView σ τ i) z = 1 := by
        unfold hammingDist
        have heq : (Finset.univ.filter fun k : Fin 1 =>
            quarterErrorTester.localView σ τ i k ≠ z k) = {0} := by
          ext k
          fin_cases k
          simp [hv0, hz0]
        rw [heq, Finset.card_singleton]
      unfold relHammingDist
      rw [hhd, Fintype.card_fin]
      norm_num
    have hle : #(Finset.univ.filter fun i : Fin 4 =>
        ¬ quarterErrorTester.IsLocalCheckFar σ τ 1 i) ≤ 1 :=
      (Finset.card_le_card hsub).trans (by simp)
    norm_num
    exact hle

/-- Concrete **sharpness witness for single-step composition**: composing `quarterErrorTester`
with an inner family of `quarterErrorTester` (on the first `3` checks) and always-true checks (on
the `4`-th check) produces a `16`-check tester whose composition bound is `7 / 16 < 1 / 2`, and
on `σ = fun _ => false` attains **exact equality**: `7` of `16` checks accept. -/
theorem sharp_single_composition_witness :
    let T₂ : Fin 4 → RobustTester 1 0 4 1 0 1 := fun i =>
      if i.val < 3 then quarterErrorTester
      else
        { varsX := fun _ _ => 0
          varsY := fun _ j => Fin.elim0 j
          checkCircuit := fun _ => constTrueBoolCircuit }
    let S₃ := quarterErrorTester.compose (by decide : 1 ≤ 1) T₂ 0
    (∀ σ : Fin 1 → Bool, evalBoolCircuit idBoolCircuit σ = true →
      ∃ τ₃, ∀ ij : Fin (4 * 4),
        evalBoolCircuit (S₃.checkCircuit ij) (S₃.localView σ τ₃ ij) = true) ∧
    (∀ τ₃,
      (#(Finset.univ.filter fun ij : Fin (4 * 4) =>
          evalBoolCircuit (S₃.checkCircuit ij) (S₃.localView (fun _ => false) τ₃ ij) = true) :
          ℝ) =
        ((1 / 4 : ℝ) + 1 / 4 - (1 / 4) * (1 / 4)) * 16) ∧
    ((1 / 4 : ℝ) + 1 / 4 - (1 / 4) * (1 / 4) = 7 / 16 ∧ (7 / 16 : ℝ) < 1 / 2) := by
  classical
  intro T₂ S₃
  have hT₂_valid : ∀ i : Fin 4,
      (T₂ i).IsValidFor (quarterErrorTester.checkCircuit i) 1 (1 / 4) 1 := by
    intro i
    dsimp only [T₂, quarterErrorTester]
    split_ifs with hi
    · exact quarterErrorTester_isValidFor
    · refine ⟨fun _ _ => ⟨Fin.elim0, fun _ => rfl⟩, fun σ hfar _ => ?_⟩
      have hcontra := hfar σ rfl
      rw [relHammingDist_self] at hcontra
      linarith
  refine ⟨RobustTester.compose_complete (by decide) 0 quarterErrorTester_isValidFor.1
      (fun i => (hT₂_valid i).1),
    fun τ₃ => ?_, by norm_num⟩
  have hcnt :
      #(Finset.univ.filter fun ij : Fin (4 * 4) =>
          evalBoolCircuit (S₃.checkCircuit ij) (S₃.localView (fun _ => false) τ₃ ij) = true) =
      7 := by
    have hbij :
        #(Finset.univ.filter fun ij : Fin (4 * 4) =>
            evalBoolCircuit (S₃.checkCircuit ij) (S₃.localView (fun _ => false) τ₃ ij) = true) =
        #(Finset.univ.filter fun p : Fin 4 × Fin 4 =>
            p.1.val = 3 ∨ p.2.val = 3) := by
      refine Finset.card_bij (fun ij _ => finProdFinEquiv.symm ij)
        (fun ij hij => ?_) (fun _ _ _ _ h => finProdFinEquiv.symm.injective h)
        (fun p hp => ?_)
      · rw [Finset.mem_filter] at hij ⊢
        refine ⟨Finset.mem_univ _, ?_⟩
        have hev := RobustTester.eval_compose_checkCircuit (by decide) quarterErrorTester T₂ 0
          (fun _ => false) τ₃ ij
        dsimp only at hev
        rw [hev] at hij
        set i := (finProdFinEquiv.symm ij).1
        set j := (finProdFinEquiv.symm ij).2
        by_cases hi : i.val < 3
        · right
          by_contra hjne
          have hjlt : j.val < 3 := by omega
          have hfalse : evalBoolCircuit ((T₂ i).checkCircuit j)
              ((T₂ i).localView
                (quarterErrorTester.localView (fun _ => false)
                  (RobustTester.extractOuterProof (by decide) τ₃) i)
                (RobustTester.extractInnerProof τ₃ i) j) = false := by
            have h0 : (0 : Fin (1 + 0 * 1)) = Fin.castAdd (0 * 1) 0 := rfl
            simp only [T₂, hi, ite_true, quarterErrorTester, hjlt, evalBoolCircuit_idBoolCircuit,
              RobustTester.localView]
            rw [h0, Fin.addCases_left, h0, Fin.addCases_left]
          exact Bool.false_ne_true (hfalse.symm.trans hij.2)
        · left
          omega
      · rw [Finset.mem_filter] at hp
        refine ⟨finProdFinEquiv p, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩,
          finProdFinEquiv.symm_apply_apply p⟩
        have hev := RobustTester.eval_compose_checkCircuit (by decide) quarterErrorTester T₂ 0
          (fun _ => false) τ₃ (finProdFinEquiv p)
        simp only [finProdFinEquiv.symm_apply_apply] at hev
        rw [hev]
        rcases hp.2 with hp1 | hp2
        · have hnot : ¬ p.1.val < 3 := by omega
          simp [T₂, hnot]
        · by_cases hi : p.1.val < 3
          · have hnot : ¬ p.2.val < 3 := by omega
            simp [T₂, hi, quarterErrorTester, hnot]
          · simp [T₂, hi]
    rw [hbij]
    decide
  rw [hcnt]
  norm_num

/-- **Concrete instantiation of `exists_amplifier_of_testerFamily`**: combining the `120`-regular
expander family `RotationMap.expanderFamily` with the full `17`-query Hadamard assignment tester
(`HadamardTester.assignmentTester`, soundness `1 / 28`, composition loss `476`) yields a genuine
gap amplifier over `Bool × (HadamardTester.Query → Bool)`. -/
theorem exists_hadamard_amplifier.{u} :
    Nonempty (Amplifier.{u} (Bool × (HadamardTester.Query → Bool))) := by
  classical
  let hβ : Fintype (Bool × (HadamardTester.Query → Bool)) :=
    @instFintypeProd _ _ inferInstance (@Pi.instFintype _ _ _ inferInstance _)
  let hA (T : ℕ) : Fintype (WalkLabels (ConstraintGraph.PreprocessLabel (Fin 120)) T →
      Bool × (HadamardTester.Query → Bool)) :=
    @Pi.instFintype _ _ _ (@Sigma.instFintype _ _ _ _) (fun _ => hβ)
  exact @exists_amplifier_of_testerFamily.{u}
    (Fin 120) HadamardTester.Query Bool _ _ _ _ _ _ _ _
    (RotationMap.expanderFamily.{u}) (by norm_num) (by norm_num : (0 : ℝ) < 1 / 28)
    (fun T => (WalkLabels (ConstraintGraph.PreprocessLabel (Fin 120)) T →
      Bool × (HadamardTester.Query → Bool)) → Bool)
    (fun T =>
      HadamardTester.LinPos (WalkLabels (ConstraintGraph.PreprocessLabel (Fin 120)) T →
        Bool × (HadamardTester.Query → Bool)) ⊕
      HadamardTester.QuadPos (WalkLabels (ConstraintGraph.PreprocessLabel (Fin 120)) T →
        Bool × (HadamardTester.Query → Bool)))
    (fun T =>
      HadamardTester.Rand (WalkLabels (ConstraintGraph.PreprocessLabel (Fin 120)) T →
        Bool × (HadamardTester.Query → Bool)))
    (fun T => let := hA T; inferInstance)
    (fun T => let := hA T; inferInstance)
    (fun T => let := hA T; inferInstance)
    (fun T => let := hA T; inferInstance)
    (fun T => let := hA T; HadamardTester.assignmentTester)
    (fun T => let := hA T; HadamardTester.isComplete_assignmentTester)
    (fun T => let := hA T; ConstraintGraph.decodeLabel)
    (fun T => let := hA T; HadamardTester.sound_assignmentTester)

end Witnesses

end Cslib.PCP
