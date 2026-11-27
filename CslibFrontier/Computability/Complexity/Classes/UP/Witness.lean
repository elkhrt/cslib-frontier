/-
Copyright (c) 2026 The PanMath contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The PanMath contributors
-/
module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.UP
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# Unambiguous Polynomial-Time Membership from Unique Witness Relations

This module establishes unambiguous witness-relation criteria for membership in the complexity
classes `UP`, `coUP`, and `UP ∩ coUP` (`Cslib.Complexity.UP`, `Cslib.Complexity.coUP`) under
standard Lean axioms, complementing `Cslib.Complexity.mem_NP_of_witness`.

Given an encoded witness type `β` with a linear-space decoder `D : Turing.MultiTapeTM.Decoder encW`
and a polynomial-time Boolean predicate `check : α × β → Bool`, the canonical unambiguous verifier
`Cslib.Complexity.unambiguousWitnessVerifier` accepts a certificate `w` of prescribed polynomial
length `(2 * p + 1).eval |enc a|` if and only if `w` splits as `frame (encW b) ++ false^k` for a
witness `b` satisfying `check (a, b) = true`. Fixing all padding bits to `false` guarantees that
each valid witness `b` admits at most one accepted certificate of any fixed length, so uniqueness
of `b` directly yields `acceptCount ≤ 1` and places the language in `UP` (and, when a unique
total witness decides both acceptance and rejection, in `UP ∩ coUP` and hence `NP ∩ coNP`).

## Main definitions

* `Cslib.Complexity.unambiguousWitnessVerifier`: canonical zero-padded framed-witness verifier
  accepting at most one padded bit-string per decoded witness.

## Main results

* `Cslib.Complexity.unambiguousWitnessVerifier_eq_true_iff`: exact characterization of accepted
  certificates as `frame (encW b) ++ List.replicate k false` with `check (a, b) = true`.
* `Cslib.Complexity.computableInPolyTime_unambiguousWitnessVerifier`: polynomial-time
  computability of `unambiguousWitnessVerifier` (registered with `@[fun_prop]`).
* `Cslib.Complexity.acceptCount_unambiguousWitnessVerifier_le_one`: when `check (a, ·)` accepts
  at most one witness `b`, at most one certificate of any length `n` is accepted.
* `Cslib.Complexity.mem_UP_of_uniqueWitness`: a sound, complete, polynomial-time check with at
  most one valid witness per instance and polynomial witness length places a language in `UP`.
* `Cslib.Complexity.mem_UP_inter_coUP_of_totalUniqueWitness`: a polynomial-time check admitting
  a unique polynomially bounded witness for every instance, together with a polynomial-time
  decision predicate on that witness, places a language in `UP ∩ coUP`.
* `Cslib.Complexity.mem_NP_inter_coNP_of_totalUniqueWitness`: corollary placing any language
  with a total unique polynomial-time witness scheme in `NP ∩ coNP`.
-/

public section

namespace Cslib.Complexity

open Cslib.Complexity Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime

section Verifier

variable {α β : Type} {enc : α ↪ List Bool} {encW : β ↪ List Bool}

/-- Canonical zero-padded verifier for an unambiguous witness relation decided by `check`. On input
`(a, w)`, it decodes the framed prefix `unframe w` via `D`, verifies that `w` consists of
`frame (encW b)` followed solely by `false` padding bits, and evaluates `check (a, b)`. -/
def unambiguousWitnessVerifier (D : Decoder encW) (check : α × β → Bool)
    (x : α × List Bool) : Bool :=
  decide (frame (encW (D.decode (unframe x.2))) ++
      List.replicate (dropFrame x.2).length false = x.2) &&
    check (x.1, D.decode (unframe x.2))

/-- `unambiguousWitnessVerifier D check` accepts `(a, w)` if and only if `w` is the framed encoding
of a witness `b` accepted by `check (a, ·)`, padded with `false` bits. -/
theorem unambiguousWitnessVerifier_eq_true_iff {D : Decoder encW} {check : α × β → Bool}
    {a : α} {w : List Bool} :
    unambiguousWitnessVerifier D check (a, w) = true ↔
      ∃ (b : β) (k : ℕ),
        w = frame (encW b) ++ List.replicate k false ∧ check (a, b) = true := by
  simp only [unambiguousWitnessVerifier, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨hw, hcheck⟩
    exact ⟨D.decode (unframe w), (dropFrame w).length, hw.symm, hcheck⟩
  · rintro ⟨b, k, rfl, hcheck⟩
    simpa only [unframe_frame_append, D.decode_enc, dropFrame_frame_append,
      List.length_replicate, true_and] using hcheck

/-- Evaluating `unambiguousWitnessVerifier` on a framed witness followed by `false` padding reduces
to `check`. -/
@[simp]
theorem unambiguousWitnessVerifier_frame_append_replicate (D : Decoder encW)
    (check : α × β → Bool) (a : α) (b : β) (k : ℕ) :
    unambiguousWitnessVerifier D check (a, frame (encW b) ++ List.replicate k false) =
      check (a, b) := by
  simp only [unambiguousWitnessVerifier, unframe_frame_append, D.decode_enc,
    dropFrame_frame_append, List.length_replicate, decide_true, Bool.true_and]

/-- Two equal-length certificates accepted by `unambiguousWitnessVerifier` are identical whenever
`check (a, ·)` accepts at most one witness. -/
theorem eq_of_unambiguousWitnessVerifier_eq_true {D : Decoder encW} {check : α × β → Bool}
    {a : α} (huniq : ∀ b₁ b₂, check (a, b₁) = true → check (a, b₂) = true → b₁ = b₂)
    {w₁ w₂ : List Bool} (hlen : w₁.length = w₂.length)
    (h₁ : unambiguousWitnessVerifier D check (a, w₁) = true)
    (h₂ : unambiguousWitnessVerifier D check (a, w₂) = true) :
    w₁ = w₂ := by
  obtain ⟨b₁, k₁, rfl, hc₁⟩ := unambiguousWitnessVerifier_eq_true_iff.mp h₁
  obtain ⟨b₂, k₂, rfl, hc₂⟩ := unambiguousWitnessVerifier_eq_true_iff.mp h₂
  obtain rfl := huniq b₁ b₂ hc₁ hc₂
  have hk : k₁ = k₂ := by
    simp only [List.length_append, List.length_replicate] at hlen
    omega
  rw [hk]

/-- If `check (a, ·)` accepts at most one witness, then `unambiguousWitnessVerifier D check`
accepts at most one certificate of any given length `n`. -/
theorem acceptCount_unambiguousWitnessVerifier_le_one {D : Decoder encW} {check : α × β → Bool}
    {a : α} (huniq : ∀ b₁ b₂, check (a, b₁) = true → check (a, b₂) = true → b₁ = b₂) (n : ℕ) :
    acceptCount (unambiguousWitnessVerifier D check) a n ≤ 1 := by
  rw [acceptCount, Finset.card_le_one_iff]
  intro f₁ f₂ hf₁ hf₂
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf₁ hf₂
  apply List.ofFn_injective
  exact eq_of_unambiguousWitnessVerifier_eq_true huniq (by simp only [List.length_ofFn]) hf₁ hf₂

/-- If `check` is computable in polynomial time and `encW` has a decoder `D`, then
`unambiguousWitnessVerifier D check` is computable in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_unambiguousWitnessVerifier (D : Decoder encW) {check : α × β → Bool}
    (hcheck : ComputableInPolyTime check (encPair enc encW) encBool) :
    ComputableInPolyTime (unambiguousWitnessVerifier D check) (encPair enc encBits) encBool := by
  obtain ⟨_, _, hD⟩ := D.computable
  have hdecoder : ComputableInPolyTime D.decode encBits encW := hD.computableInPolyTime
  have hdecode : ComputableInPolyTime (fun x : α × List Bool => D.decode (unframe x.2))
      (encPair enc encBits) encW :=
    hdecoder.comp (unframe.comp (snd enc encBits))
  have hpad : ComputableInPolyTime
      (fun x : α × List Bool => List.replicate (dropFrame x.2).length false)
      (encPair enc encBits) encBits :=
    (bitsReplicate false).comp (length_bits.comp (dropFrame.comp (snd enc encBits)))
  exact bool_and'
    (decide_eq' (bitsAppend ((bitsFrame encW).comp hdecode) hpad) (snd enc encBits))
    (hcheck.comp ((fst enc encBits).prod hdecode))

/-- **Unambiguous polynomial-time membership from a unique witness relation.** If `check` runs in
polynomial time, accepts at most one witness per instance, accepts only for members of `A`, and
admits a witness of encoded length at most `p.eval |enc a|` for every `a ∈ A`, then `A ∈ UP enc`. -/
theorem mem_UP_of_uniqueWitness (D : Decoder encW) {p : Polynomial ℕ} {check : α × β → Bool}
    {A : Set α} (hcheck : ComputableInPolyTime check (encPair enc encW) encBool)
    (huniq : ∀ a b₁ b₂, check (a, b₁) = true → check (a, b₂) = true → b₁ = b₂)
    (hsound : ∀ a b, check (a, b) = true → a ∈ A)
    (hcomplete : ∀ a ∈ A, ∃ b, check (a, b) = true ∧ (encW b).length ≤ p.eval (enc a).length) :
    A ∈ UP enc := by
  refine mem_UP.mpr ⟨2 * p + 1, unambiguousWitnessVerifier D check,
    computableInPolyTime_unambiguousWitnessVerifier D hcheck,
    fun a => acceptCount_unambiguousWitnessVerifier_le_one (huniq a) _, fun a => ?_⟩
  have hle := acceptCount_unambiguousWitnessVerifier_le_one (D := D) (huniq a)
    ((2 * p + 1).eval (enc a).length)
  have hone_iff :
      acceptCount (unambiguousWitnessVerifier D check) a ((2 * p + 1).eval (enc a).length) = 1 ↔
        0 < acceptCount (unambiguousWitnessVerifier D check) a
          ((2 * p + 1).eval (enc a).length) := by
    omega
  rw [hone_iff, acceptCount_pos_iff]
  constructor
  · intro ha
    obtain ⟨b, hb, hblen⟩ := hcomplete a ha
    have hflen : (frame (encW b)).length ≤ (2 * p + 1).eval (enc a).length := by
      simp only [length_frame, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
        Polynomial.eval_one]
      omega
    refine ⟨frame (encW b) ++ List.replicate ((2 * p + 1).eval (enc a).length -
        (frame (encW b)).length) false, ?_, ?_⟩
    · rw [List.length_append, List.length_replicate, Nat.add_sub_cancel' hflen]
    · rwa [unambiguousWitnessVerifier_frame_append_replicate]
  · rintro ⟨w, -, hw⟩
    obtain ⟨b, -, -, hb⟩ := unambiguousWitnessVerifier_eq_true_iff.mp hw
    exact hsound a b hb

/-- **`UP ∩ coUP` membership from a total unique witness scheme.** If every instance `a : α` admits
a unique witness `b : β` passing a polynomial-time test `isWitness (a, b)` with encoded length at
most `p.eval |enc a|`, and membership `a ∈ A` is determined from `(a, b)` by a polynomial-time
predicate `accept (a, b)`, then `A ∈ UP enc ∩ coUP enc`. -/
theorem mem_UP_inter_coUP_of_totalUniqueWitness (D : Decoder encW) {p : Polynomial ℕ}
    {isWitness accept : α × β → Bool} {A : Set α}
    (hwit : ComputableInPolyTime isWitness (encPair enc encW) encBool)
    (hacc : ComputableInPolyTime accept (encPair enc encW) encBool)
    (huniq : ∀ a b₁ b₂, isWitness (a, b₁) = true → isWitness (a, b₂) = true → b₁ = b₂)
    (htotal : ∀ a, ∃ b, isWitness (a, b) = true ∧ (encW b).length ≤ p.eval (enc a).length)
    (hdecide : ∀ a b, isWitness (a, b) = true → (a ∈ A ↔ accept (a, b) = true)) :
    A ∈ UP enc ∩ coUP enc := by
  refine ⟨?_, ?_⟩
  · refine mem_UP_of_uniqueWitness D (p := p) (check := fun x => isWitness x && accept x)
      (bool_and' hwit hacc)
      (fun a b₁ b₂ h₁ h₂ => by
        simp only [Bool.and_eq_true] at h₁ h₂
        exact huniq a b₁ b₂ h₁.1 h₂.1)
      (fun a b h => by
        simp only [Bool.and_eq_true] at h
        exact (hdecide a b h.1).mpr h.2)
      (fun a ha => by
        obtain ⟨b, hb, hlen⟩ := htotal a
        exact ⟨b, Bool.and_eq_true_iff.mpr ⟨hb, (hdecide a b hb).mp ha⟩, hlen⟩)
  · rw [mem_coUP]
    refine mem_UP_of_uniqueWitness D (p := p) (check := fun x => isWitness x && !accept x)
      (bool_and' hwit (bool_not.comp hacc))
      (fun a b₁ b₂ h₁ h₂ => by
        simp only [Bool.and_eq_true] at h₁ h₂
        exact huniq a b₁ b₂ h₁.1 h₂.1)
      (fun a b h => by
        simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
        rw [Set.mem_compl_iff, hdecide a b h.1, h.2]
        exact Bool.false_ne_true)
      (fun a ha => by
        obtain ⟨b, hb, hlen⟩ := htotal a
        have hfalse : accept (a, b) = false :=
          Bool.eq_false_iff.mpr fun ht => ha ((hdecide a b hb).mpr ht)
        exact ⟨b, by simp only [hb, hfalse, Bool.not_false, Bool.and_self], hlen⟩)

/-- Any language with a total unique polynomial-time witness scheme lies in `NP ∩ coNP`. -/
theorem mem_NP_inter_coNP_of_totalUniqueWitness (D : Decoder encW) {p : Polynomial ℕ}
    {isWitness accept : α × β → Bool} {A : Set α}
    (hwit : ComputableInPolyTime isWitness (encPair enc encW) encBool)
    (hacc : ComputableInPolyTime accept (encPair enc encW) encBool)
    (huniq : ∀ a b₁ b₂, isWitness (a, b₁) = true → isWitness (a, b₂) = true → b₁ = b₂)
    (htotal : ∀ a, ∃ b, isWitness (a, b) = true ∧ (encW b).length ≤ p.eval (enc a).length)
    (hdecide : ∀ a b, isWitness (a, b) = true → (a ∈ A ↔ accept (a, b) = true)) :
    A ∈ NP enc ∩ coNP enc := by
  obtain ⟨hUP, hcoUP⟩ :=
    mem_UP_inter_coUP_of_totalUniqueWitness D (p := p) hwit hacc huniq htotal hdecide
  exact ⟨UP_subset_NP hUP, coUP_subset_coNP hcoUP⟩

/-- Concrete non-vacuity check: the parity-free singleton language `{true}` on `Bool` lies in
`UP encBool ∩ coUP encBool` via the identity bit witness. -/
example : ({true} : Set Bool) ∈ UP encBool ∩ coUP encBool :=
  mem_UP_inter_coUP_of_totalUniqueWitness
    (D := Decoder.bool) (p := 1)
    (isWitness := fun x : Bool × Bool => decide (x.2 = x.1))
    (accept := fun x : Bool × Bool => x.2)
    (of_finite _) (of_finite _)
    (fun _ _ _ h₁ h₂ => by
      simp only [decide_eq_true_eq] at h₁ h₂
      exact h₁.trans h₂.symm)
    (fun a => ⟨a, by simp only [decide_true], by simp only [encBool_apply, List.length_singleton,
      Polynomial.eval_one, le_refl]⟩)
    (fun a b hb => by
      simp only [decide_eq_true_eq] at hb
      simp only [Set.mem_singleton_iff, hb])

end Verifier

end Cslib.Complexity
