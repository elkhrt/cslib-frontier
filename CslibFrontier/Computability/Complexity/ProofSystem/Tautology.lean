/-
Copyright (c) 2026 Google DeepMind. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Google DeepMind
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.ProofSystem
public import CslibFrontier.Computability.Complexity.Problems.Tautology
import CslibFrontier.Computability.Complexity.Classes.Oracle.TQBF
import CslibFrontier.Computability.Complexity.Classes.NP.Closure
import CslibFrontier.Computability.Complexity.Classes.P.Finite
import CslibFrontier.Computability.Complexity.Classes.P.Closure
import CslibFrontier.Computability.Complexity.ProofSystem.Exhaustive
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# Cook–Reckhow Proof Systems for Propositional Tautologies

Provides a total polynomial-time decoder `Cslib.Complexity.qbfDecoder` for `encQBF`, derives the
Cook–Reckhow characterization of `NP = coNP` directly for `Cslib.Complexity.TAUTOLOGY`, and
establishes the cofinite refinement: `NP ≠ coNP` holds if and only if in every proof system for
`TAUTOLOGY` and for every polynomial bound, infinitely many tautologies lack a proof within that
bound.

## Main definitions

* `Cslib.Complexity.qbfDecoder`: total polynomial-time decoder for `encQBF`.

## Main results

* `Cslib.Complexity.ProofSystem.NP_eq_coNP_iff_exists_polynomiallyBounded_TAUTOLOGY`: `NP = coNP`
  iff some Cook–Reckhow proof system for `TAUTOLOGY` is polynomially bounded.
* `Cslib.Complexity.ProofSystem.exists_polynomiallyBounded_iff_cofinite_short_proofs`:
  existence of a polynomially bounded proof system is equivalent to cofinite polynomial proof
  size.
* `Cslib.Complexity.ProofSystem.NP_neq_coNP_iff_forall_infinite_hard_TAUTOLOGY`: `NP ≠ coNP`
  iff every proof system for `TAUTOLOGY` has infinitely many hard tautologies for every
  polynomial bound.
-/

public section

namespace Cslib.Complexity

open Cslib.Logic.PL Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime

/-- Total polynomial-time decoder for `encQBF`. -/
noncomputable def qbfDecoder : Decoder encQBF where
  decode := TQBF.decodeQBF
  decode_enc := TQBF.decodeQBF_encQBF
  computable := TQBF.decodeQBF_pt.exists_degree

namespace ProofSystem

private theorem top_mem_TAUTOLOGY : (QBF.top : QBF ℕ) ∈ TAUTOLOGY :=
  mem_TAUTOLOGY.mpr ⟨QBF.quantifierFree_top, fun _ => rfl⟩

/-- **Cook–Reckhow theorem for `TAUTOLOGY`**: `NP = coNP` across all encodings iff some proof
system for `TAUTOLOGY` is polynomially bounded. -/
theorem NP_eq_coNP_iff_exists_polynomiallyBounded_TAUTOLOGY :
    (∀ {γ : Type} (encC : γ ↪ List Bool), NP encC = coNP encC) ↔
      ∃ P : ProofSystem encQBF TAUTOLOGY, P.PolynomiallyBounded := by
  rw [NP_eq_coNP_iff_coNP_subset_NP]
  exact coNP_subset_NP_iff_exists_polynomiallyBounded
    TAUTOLOGY_coNPComplete qbfDecoder ⟨.top, top_mem_TAUTOLOGY⟩

/-- Existence of a polynomially bounded proof system is equivalent to existence of a proof system
and polynomial leaving only finitely many members without a short proof. -/
theorem exists_polynomiallyBounded_iff_cofinite_short_proofs {α : Type} {enc : α ↪ List Bool}
    {L : Set α} (D : Decoder enc) (hne : L.Nonempty) :
    (∃ P : ProofSystem enc L, P.PolynomiallyBounded) ↔
      ∃ (P : ProofSystem enc L) (p : Polynomial ℕ),
        {a ∈ L | ∀ π, P π = a → p.eval (enc a).length < π.length}.Finite := by
  constructor
  · rintro ⟨P, p, hp⟩
    refine ⟨P, p, ?_⟩
    have hempty : {a ∈ L | ∀ π, P π = a → p.eval (enc a).length < π.length} = ∅ := by
      ext a
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and, not_forall,
        not_lt]
      intro ha
      obtain ⟨π, h1, h2⟩ := hp a ha
      exact ⟨π, h1, h2⟩
    rw [hempty]
    exact Set.finite_empty
  · rintro ⟨P, p, hfin⟩
    rw [exists_polynomiallyBounded_iff_mem_NP D hne]
    let L' : Set α := {a | ∃ π : List Bool, P π = a ∧ π.length ≤ p.eval (enc a).length}
    have hL'_NP : L' ∈ NP enc := by
      classical
      have hlenCheck : ComputableInPolyTime
          (fun x : α × List Bool => decide (x.2.length ≤ p.eval (enc x.1).length))
          (encPair enc encBits) encBool :=
        unary_le' (length_bits.comp (snd enc encBits))
          ((unary_eval p).comp ((encoding_length enc).comp (fst enc encBits)))
      have hcheck : ComputableInPolyTime
          (fun x : α × List Bool =>
            decide (x.2.length ≤ p.eval (enc x.1).length) && decide (P x.2 = x.1))
          (encPair enc encBits) encBool :=
        bool_and' hlenCheck (decide_eq' (P.computable.comp (snd enc encBits)) (fst enc encBits))
      refine mem_NP_of_check (p := p) Decoder.bits hcheck ?_ ?_
      · rintro a π h
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        exact ⟨π, h.2, h.1⟩
      · rintro a ⟨π, hπ, hlen⟩
        exact ⟨π, by simp [hπ, hlen], hlen⟩
    have hsub : L' ⊆ L := by
      rintro a ⟨π, rfl, _⟩
      exact P.mem π
    have h1 : (L \ L').Finite := by
      refine hfin.subset ?_
      intro a ha
      simp only [Set.mem_sdiff, Set.mem_ofPred_eq, L', not_exists, not_and, not_le] at ha ⊢
      exact ha
    have h2 : (L' \ L).Finite := by
      have : L' \ L = ∅ := Set.sdiff_eq_empty.mpr hsub
      rw [this]
      exact Set.finite_empty
    have heq : L = (L' ∩ (L' \ L)ᶜ) ∪ (L \ L') := by
      ext a
      by_cases ha : a ∈ L <;> by_cases ha' : a ∈ L' <;> simp [ha, ha']
    rw [heq]
    exact union_mem_NP (inter_mem_NP hL'_NP (P_subset_NP (compl_mem_P h2.mem_P)))
      (P_subset_NP h1.mem_P)

/-- **Cofinite Cook–Reckhow characterization of `NP ≠ coNP` for `TAUTOLOGY`**: `NP ≠ coNP` iff
in every proof system for `TAUTOLOGY` and for every polynomial `p`, infinitely many tautologies
lack a proof of length `≤ p(|enc α|)`. -/
theorem NP_neq_coNP_iff_forall_infinite_hard_TAUTOLOGY :
    ¬(∀ {γ : Type} (encC : γ ↪ List Bool), NP encC = coNP encC) ↔
      ∀ (P : ProofSystem encQBF TAUTOLOGY) (p : Polynomial ℕ),
        {a ∈ TAUTOLOGY | ∀ π, P π = a → p.eval (encQBF a).length < π.length}.Infinite := by
  rw [NP_eq_coNP_iff_exists_polynomiallyBounded_TAUTOLOGY,
    exists_polynomiallyBounded_iff_cofinite_short_proofs qbfDecoder ⟨.top, top_mem_TAUTOLOGY⟩]
  simp only [not_exists, Set.Infinite]

end ProofSystem

end Cslib.Complexity
