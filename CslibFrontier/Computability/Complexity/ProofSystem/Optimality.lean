/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Papers Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.ProofSystem
import Cslib.Foundations.Data.Polynomial.Monotone
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder

/-!
# Optimal proof systems and family extensions

A proof system `P` for `L` is *optimal* when it simulates every proof
system for `L`, and *p-optimal* when it p-simulates every proof system for `L`. Adjoining a unary
polynomial-time family `τ : ℕ → α` of members of `L` to `P` produces a proof system
`P.adjoinFamily hτ hmem` that p-simulates `P` and proves `τ n` in `n + 3` bits. A proof system `P`
simulates `P.adjoinFamily hτ hmem` exactly when `τ` already has polynomial-length proofs in `P`.

## Main definitions

* `Cslib.Complexity.ProofSystem.IsOptimal`, `Cslib.Complexity.ProofSystem.IsPOptimal`: optimal and
  p-optimal proof systems.
* `Cslib.Complexity.ProofSystem.HasPolyProofs`: polynomial-length proofs for an indexed family.
* `Cslib.Complexity.ProofSystem.adjoinFamily`: adjoining a unary polynomial-time family to a proof
  system.

## Main results

* `Cslib.Complexity.ProofSystem.IsPOptimal.isOptimal`: p-optimal proof systems are optimal.
* `Cslib.Complexity.ProofSystem.PolynomiallyBounded.isOptimal`: polynomially bounded proof systems
  are optimal.
* `Cslib.Complexity.ProofSystem.simulates_adjoinFamily_iff_hasPolyProofs`: `P` simulates
  `P.adjoinFamily hτ hmem` exactly when `τ` has polynomial-length proofs in `P`.
* `Cslib.Complexity.ProofSystem.psimulates_adjoinFamily_of_generator`: a unary polynomial-time proof
  generator for `τ` in `P` gives a p-simulation of `P.adjoinFamily hτ hmem` by `P`.
-/

public section

namespace Cslib.Complexity.ProofSystem

open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime

variable {α : Type} {enc : α ↪ List Bool} {L : Set α}

/-- `P` is **optimal**: `P` simulates every proof system for `L`. -/
@[expose]
def IsOptimal (P : ProofSystem enc L) : Prop :=
  ∀ Q : ProofSystem enc L, P.Simulates Q

/-- `P` is **p-optimal**: `P` p-simulates every proof system for `L`. -/
@[expose]
def IsPOptimal (P : ProofSystem enc L) : Prop :=
  ∀ Q : ProofSystem enc L, P.PSimulates Q

/-- Every p-optimal proof system is optimal. -/
theorem IsPOptimal.isOptimal {P : ProofSystem enc L} (hP : P.IsPOptimal) : P.IsOptimal :=
  fun Q => (hP Q).simulates

/-- Simulation transfers optimality. -/
theorem IsOptimal.of_simulates {P Q : ProofSystem enc L} (hP : P.IsOptimal)
    (hQP : Q.Simulates P) : Q.IsOptimal :=
  fun R => hQP.trans (hP R)

/-- p-simulation transfers p-optimality. -/
theorem IsPOptimal.of_psimulates {P Q : ProofSystem enc L} (hP : P.IsPOptimal)
    (hQP : Q.PSimulates P) : Q.IsPOptimal :=
  fun R => hQP.trans (hP R)

/-- Every polynomially bounded proof system is optimal. -/
theorem PolynomiallyBounded.isOptimal {P : ProofSystem enc L} (hP : P.PolynomiallyBounded) :
    P.IsOptimal := by
  intro Q
  obtain ⟨p, hp⟩ := hP
  obtain ⟨c, d, hr⟩ := Q.computable.polyBounded_length.exists_le
  let r : Polynomial ℕ := .C c * (.X + 1) ^ d
  refine ⟨p.comp r, fun π => ?_⟩
  obtain ⟨π', hπ', hlen'⟩ := hp (Q π) (Q.mem π)
  refine ⟨π', hπ', ?_⟩
  rw [Polynomial.eval_comp]
  have hlenQ : (enc (Q π)).length ≤ r.eval π.length := by simpa [r] using hr π
  exact hlen'.trans (p.eval_mono hlenQ)

/-- An optimal proof system for a language with a polynomially bounded proof system is polynomially
bounded. -/
theorem PolynomiallyBounded.of_isOptimal {P Q : ProofSystem enc L} (hP : P.IsOptimal)
    (hQ : Q.PolynomiallyBounded) : P.PolynomiallyBounded :=
  hQ.of_simulates (hP Q)

/-- An indexed family `τ : ℕ → α` has **polynomial-length proofs** in `P`: for a polynomial `q`,
every `τ n` has a `P`-proof of length at most `q n`. -/
@[expose]
def HasPolyProofs (P : ProofSystem enc L) (τ : ℕ → α) : Prop :=
  ∃ q : Polynomial ℕ, ∀ n : ℕ, ∃ π : List Bool, P π = τ n ∧ π.length ≤ q.eval n

/-- Simulation transfers polynomial-length proofs of an indexed family. -/
theorem HasPolyProofs.of_simulates {P Q : ProofSystem enc L} {τ : ℕ → α}
    (hτ : P.HasPolyProofs τ) (hQP : Q.Simulates P) : Q.HasPolyProofs τ := by
  obtain ⟨q, hq⟩ := hτ
  obtain ⟨p, hp⟩ := hQP
  refine ⟨p.comp q, fun n => ?_⟩
  obtain ⟨π, hπ, hlen⟩ := hq n
  obtain ⟨π', hπ', hlen'⟩ := hp π
  refine ⟨π', hπ'.trans hπ, ?_⟩
  rw [Polynomial.eval_comp]
  exact hlen'.trans (p.eval_mono hlen)

/-- In a polynomially bounded proof system, every unary polynomial-time family of members of `L`
admits polynomial-length proofs. -/
theorem PolynomiallyBounded.hasPolyProofs {P : ProofSystem enc L} {τ : ℕ → α}
    (hP : P.PolynomiallyBounded) (hτ : ComputableInPolyTime τ encUnary enc)
    (hmem : ∀ n, τ n ∈ L) : P.HasPolyProofs τ := by
  obtain ⟨p, hp⟩ := hP
  obtain ⟨c, d, hr⟩ := hτ.polyBounded_length.exists_le
  let r : Polynomial ℕ := .C c * (.X + 1) ^ d
  refine ⟨p.comp r, fun n => ?_⟩
  obtain ⟨π, hπ, hlen⟩ := hp (τ n) (hmem n)
  refine ⟨π, hπ, ?_⟩
  rw [Polynomial.eval_comp]
  have henc : (enc (τ n)).length ≤ r.eval n := by
    simpa only [r, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
      Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one, encUnary_apply,
      List.length_replicate] using hr n
  exact hlen.trans (p.eval_mono henc)

/-- The proof system obtained by adjoining a unary polynomial-time family `τ : ℕ → α` of members of
`L` to `P`. -/
def adjoinFamily (P : ProofSystem enc L) {τ : ℕ → α}
    (hτ : ComputableInPolyTime τ encUnary enc) (hmem : ∀ n, τ n ∈ L) :
    ProofSystem enc L where
  toFun π := if (Turing.MultiTapeTM.unframe π).headD false then
      τ (Turing.MultiTapeTM.dropFrame π).length
    else
      P (Turing.MultiTapeTM.dropFrame π)
  computable :=
    (Decoder.bool.computableInPolyTime.comp ComputableInPolyTime.unframe).ite'
      (hτ.comp (Decoder.unary.computableInPolyTime.comp ComputableInPolyTime.dropFrame))
      (P.computable.comp ComputableInPolyTime.dropFrame)
  range_eq := by
    refine Set.Subset.antisymm ?_ fun a ha => ?_
    · rintro _ ⟨π, rfl⟩
      dsimp only
      split_ifs
      · exact hmem _
      · exact P.mem _
    · obtain ⟨π₀, rfl⟩ := P.exists_eq ha
      refine ⟨Turing.MultiTapeTM.frame [false] ++ π₀, ?_⟩
      simp only [unframe_frame_append, List.headD_cons, Bool.false_eq_true, ↓reduceIte,
        dropFrame_frame_append]

/-- The empty word delegates to `P []` in `P.adjoinFamily hτ hmem`. -/
@[simp]
theorem adjoinFamily_nil (P : ProofSystem enc L) {τ : ℕ → α}
    (hτ : ComputableInPolyTime τ encUnary enc) (hmem : ∀ n, τ n ∈ L) :
    P.adjoinFamily hτ hmem [] = P [] := by
  dsimp only [adjoinFamily]
  simp only [Turing.MultiTapeTM.unframe, List.headD_nil, Bool.false_eq_true, ↓reduceIte,
    Turing.MultiTapeTM.dropFrame]

/-- Words beginning with delimiter `false` delegate to `P` on the tail in
`P.adjoinFamily hτ hmem`. -/
@[simp]
theorem adjoinFamily_false_cons (P : ProofSystem enc L) {τ : ℕ → α}
    (hτ : ComputableInPolyTime τ encUnary enc) (hmem : ∀ n, τ n ∈ L) (π : List Bool) :
    P.adjoinFamily hτ hmem (false :: π) = P π := by
  dsimp only [adjoinFamily]
  simp only [Turing.MultiTapeTM.unframe, List.headD_nil, Bool.false_eq_true, ↓reduceIte,
    Turing.MultiTapeTM.dropFrame]

/-- Words prefixed by `frame [false]` delegate to `P` in `P.adjoinFamily hτ hmem`. -/
theorem adjoinFamily_frame_false_append (P : ProofSystem enc L) {τ : ℕ → α}
    (hτ : ComputableInPolyTime τ encUnary enc) (hmem : ∀ n, τ n ∈ L) (π : List Bool) :
    P.adjoinFamily hτ hmem (Turing.MultiTapeTM.frame [false] ++ π) = P π := by
  dsimp only [adjoinFamily]
  simp only [unframe_frame_append, List.headD_cons, Bool.false_eq_true, ↓reduceIte,
    dropFrame_frame_append]

/-- Words prefixed by `frame [true]` followed by `n` bits prove `τ n` in
`P.adjoinFamily hτ hmem`. -/
theorem adjoinFamily_frame_true_append_replicate (P : ProofSystem enc L) {τ : ℕ → α}
    (hτ : ComputableInPolyTime τ encUnary enc) (hmem : ∀ n, τ n ∈ L) (n : ℕ) (b : Bool) :
    P.adjoinFamily hτ hmem (Turing.MultiTapeTM.frame [true] ++ List.replicate n b) = τ n := by
  dsimp only [adjoinFamily]
  simp only [unframe_frame_append, List.headD_cons, ↓reduceIte, dropFrame_frame_append,
    List.length_replicate]

/-- `P.adjoinFamily hτ hmem` p-simulates `P`. -/
theorem psimulates_adjoinFamily_self (P : ProofSystem enc L) {τ : ℕ → α}
    (hτ : ComputableInPolyTime τ encUnary enc) (hmem : ∀ n, τ n ∈ L) :
    (P.adjoinFamily hτ hmem).PSimulates P :=
  ⟨fun π => Turing.MultiTapeTM.frame [false] ++ π,
    bitsAppend (const (Turing.MultiTapeTM.frame [false])) id',
    adjoinFamily_frame_false_append P hτ hmem⟩

/-- `P.adjoinFamily hτ hmem` proves `τ n` in `n + 3` bits. -/
theorem hasPolyProofs_adjoinFamily (P : ProofSystem enc L) {τ : ℕ → α}
    (hτ : ComputableInPolyTime τ encUnary enc) (hmem : ∀ n, τ n ∈ L) :
    (P.adjoinFamily hτ hmem).HasPolyProofs τ := by
  refine ⟨Polynomial.X + 3, fun n => ⟨Turing.MultiTapeTM.frame [true] ++ List.replicate n false,
    adjoinFamily_frame_true_append_replicate P hτ hmem n false, ?_⟩⟩
  simp only [List.length_append, length_frame, List.length_cons, List.length_nil,
    List.length_replicate, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_ofNat]
  omega

/-- `P` simulates `P.adjoinFamily hτ hmem` exactly when `τ` has polynomial-length proofs in `P`. -/
theorem simulates_adjoinFamily_iff_hasPolyProofs (P : ProofSystem enc L) {τ : ℕ → α}
    (hτ : ComputableInPolyTime τ encUnary enc) (hmem : ∀ n, τ n ∈ L) :
    P.Simulates (P.adjoinFamily hτ hmem) ↔ P.HasPolyProofs τ := by
  refine ⟨fun hsim => (hasPolyProofs_adjoinFamily P hτ hmem).of_simulates hsim, fun ⟨q, hq⟩ => ?_⟩
  refine ⟨q + Polynomial.X, fun π => ?_⟩
  have hdrop : (Turing.MultiTapeTM.dropFrame π).length ≤ π.length := length_dropFrame_le π
  by_cases htag : (Turing.MultiTapeTM.unframe π).headD false = true
  · obtain ⟨π', hπ', hlen'⟩ := hq (Turing.MultiTapeTM.dropFrame π).length
    refine ⟨π', ?_, ?_⟩
    · dsimp only [adjoinFamily]
      simp only [htag, ↓reduceIte, hπ']
    · rw [Polynomial.eval_add, Polynomial.eval_X]
      exact (hlen'.trans (q.eval_mono hdrop)).trans (Nat.le_add_right _ _)
  · refine ⟨Turing.MultiTapeTM.dropFrame π, ?_, ?_⟩
    · dsimp only [adjoinFamily]
      simp only [htag, Bool.false_eq_true, ↓reduceIte]
    · rw [Polynomial.eval_add, Polynomial.eval_X]
      exact hdrop.trans (Nat.le_add_left _ _)

/-- If `g : ℕ → List Bool` generates `P`-proofs of `τ n` in unary polynomial time, then `P`
p-simulates `P.adjoinFamily hτ hmem`. -/
theorem psimulates_adjoinFamily_of_generator (P : ProofSystem enc L) {τ : ℕ → α}
    (hτ : ComputableInPolyTime τ encUnary enc) (hmem : ∀ n, τ n ∈ L) {g : ℕ → List Bool}
    (hg : ComputableInPolyTime g encUnary encBits) (hPg : ∀ n, P (g n) = τ n) :
    P.PSimulates (P.adjoinFamily hτ hmem) := by
  refine ⟨fun π => if (Turing.MultiTapeTM.unframe π).headD false then
      g (Turing.MultiTapeTM.dropFrame π).length
    else
      Turing.MultiTapeTM.dropFrame π,
    (Decoder.bool.computableInPolyTime.comp ComputableInPolyTime.unframe).ite'
      (hg.comp (Decoder.unary.computableInPolyTime.comp ComputableInPolyTime.dropFrame))
      ComputableInPolyTime.dropFrame,
    fun π => ?_⟩
  dsimp only [adjoinFamily]
  split_ifs
  · exact hPg _
  · rfl

end Cslib.Complexity.ProofSystem
