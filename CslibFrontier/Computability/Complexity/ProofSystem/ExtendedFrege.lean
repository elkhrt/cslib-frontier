module

public import CslibFrontier.Logics.Propositional.Frege
public import CslibFrontier.Computability.Complexity.ProofSystem.Propositional
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Sum
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Length
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Frege Completeness, Extended Frege, and Strong Propositional Proof Systems

Building on `CslibFrontier.Computability.Complexity.ProofSystem.Propositional`, this module
establishes under standard Lean axioms:

1. **Substitution invariance and truth-table completeness** of Hilbert-style Frege
   (`Cslib.Logic.PL.Frege`) over `Formula`, together with constant-size tautology schema
   instantiation (`exists_frege_schema_proof`).
2. **Extended Frege augmented by extra polynomial-time axioms** (`EFStep`, `extendedFregeWith`,
   `extendedFrege`, `IsStrongPPS`): verified polynomial-time proof evaluation for Frege axiom
   schemes, modus ponens, fresh extension definitions `q ↔ ψ`, and arbitrary substitution instances
   of axioms from a polynomial-time subset `A ⊆ TAUT`, with one-step linear-size proofs of all
   substitution instances (`extendedFregeWith_extraAx_proof`).
3. **Closure of Cook–Reckhow proof systems under atom shifts, substitution, and Frege deduction**
   (`closeUnderSubstFrege`), allowing polynomial-size Frege post-processing of any proof system.

## Main definitions

* `CslibFrontier.ProofComplexity.EFStep`: verified step certificates for Extended Frege with extra
  substitution axioms.
* `CslibFrontier.ProofComplexity.buildFregeAxiom`, `CslibFrontier.ProofComplexity.efStep`,
  `CslibFrontier.ProofComplexity.runEFProof`: polynomial-time verifier for `EF + A` derivations.
* `CslibFrontier.ProofComplexity.encEFStep`, `CslibFrontier.ProofComplexity.efStepDecoder`:
  injective binary encoding and total polynomial-time decoder for `EFStep`.
* `CslibFrontier.ProofComplexity.extendedFregeWith`, `CslibFrontier.ProofComplexity.extendedFrege`:
  Extended Frege augmented by a polynomial-time set `A ⊆ TAUT` of extra axioms, and plain `EF`.
* `CslibFrontier.ProofComplexity.IsStrongPPS`: strong propositional proof systems (`EF + A` for
  polynomial-time `A ⊆ TAUT`).
* `CslibFrontier.ProofComplexity.closeUnderSubstFrege`: canonical Cook–Reckhow extension closing any
  propositional proof system under atom shifts, finite substitutions, and verified Frege modus
  ponens.

## Main results

* `CslibFrontier.ProofComplexity.fregeIsProof_subst`,
  `CslibFrontier.ProofComplexity.frege_complete`,
  `CslibFrontier.ProofComplexity.exists_frege_schema_proof`: substitution invariance, truth-table
  completeness, and constant-line schema proofs in `Frege`.
* `CslibFrontier.ProofComplexity.runEFProof_mem_taut`: soundness of Extended Frege with extra
  tautology axioms `A ⊆ TAUT`.
* `CslibFrontier.ProofComplexity.exists_runEFProof_of_fregeIsProof`: compilation of any
  hypothesis-free `Frege` proof into a verified `EF` proof with linear encoded-size bound.
* `CslibFrontier.ProofComplexity.extendedFregeWith_extraAx_proof`: linear-size one-step proofs of
  all substitution instances of axioms in `A`.
* `CslibFrontier.ProofComplexity.closeUnderSubstFrege_derive`: linear-overhead derivation in
  `closeUnderSubstFrege R` via atom shift, substitution, and verified Frege implication.


-/

public section

namespace CslibFrontier.ProofComplexity

open Finset
open Cslib Cslib.Logic.PL Cslib.Complexity
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime

/-! ### Substitution invariance and truth-table completeness of Hilbert-style Frege -/

/-- `Frege.Formula.imps Δ φ` (`δ₁ → ⋯ → δₖ → φ`) is computable in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_imps :
    ComputableInPolyTime (fun p : List Formula × Formula => Frege.Formula.imps p.1 p.2)
      (encPair (encList encFormula) encFormula) encFormula := by
  have heq (p : List Formula × Formula) :
      Frege.Formula.imps p.1 p.2 = p.1.reverse.foldl (fun acc δ => .imp δ acc) p.2 := by
    rw [Frege.Formula.imps, ← List.foldl_reverse]
  rw [show (fun p : List Formula × Formula => Frege.Formula.imps p.1 p.2) =
    fun p => p.1.reverse.foldl (fun acc δ => .imp δ acc) p.2 from funext heq]
  have hmem_len {l : List Formula} {α : Formula} (hα : α ∈ l) :
      (encFormula α).length ≤ (encList encFormula l).length := by
    induction l with
    | nil => cases hα
    | cons x xs ih =>
      simp only [encList_cons, List.length_append, length_frame]
      rcases List.mem_cons.1 hα with rfl | h
      · omega
      · have := ih h; omega
  let EP := encPair (encList encFormula) encFormula
  refine foldlWithInput_of_bounded_growth (encIn := EP) (encA := encFormula)
    (encL := encList encFormula) (encB := encFormula)
    (list := fun p => p.1.reverse) (init := Prod.snd) (step := fun _ acc δ => .imp δ acc)
    (snd _ _) ⟨(listReverse encFormula).comp (fst _ _),
      computableInPolyTime_imp.comp ((snd _ _).prod ((snd _ _).comp (fst _ _))),
      inferInstance, inferInstance⟩
    (growth := fun p => (encPair (encList encFormula) encFormula p).length + 20)
    ⟨PolyBounded.self.add (.const 20), fun p acc δ hδ => ?_⟩
  have hlen := hmem_len (List.mem_reverse.1 hδ)
  have hop3 : (frame (encFormTok (.inr 3))).length ≤ 14 := by decide
  simp only [encFormula_imp, List.length_append, length_encPair]
  omega

/-- Frege axiom instances are closed under arbitrary formula substitution. -/
theorem fregeIsAxiom_subst (f : ℕ → Formula) {φ : Formula} (h : Frege.IsAxiom φ) :
    Frege.IsAxiom (φ.subst f) := by
  cases h with
  | k A B => exact .k (A.subst f) (B.subst f)
  | s A B C => exact .s (A.subst f) (B.subst f) (C.subst f)
  | dne A => exact .dne (A.subst f)
  | andElimL A B => exact .andElimL (A.subst f) (B.subst f)
  | andElimR A B => exact .andElimR (A.subst f) (B.subst f)
  | andIntro A B => exact .andIntro (A.subst f) (B.subst f)
  | orIntroL A B => exact .orIntroL (A.subst f) (B.subst f)
  | orIntroR A B => exact .orIntroR (A.subst f) (B.subst f)
  | orElim A B C => exact .orElim (A.subst f) (B.subst f) (C.subst f)

/-- Frege proofs are closed under arbitrary formula substitution, preserving exact line count. -/
theorem fregeIsProof_subst (f : ℕ → Formula) {Γ L : List Formula} (h : Frege.IsProof Γ L) :
    Frege.IsProof (Γ.map (Proposition.subst f)) (L.map (Proposition.subst f)) := by
  induction h with
  | nil => exact .nil
  | hyp _ hmem ih => exact ih.hyp (List.mem_map_of_mem hmem)
  | ax _ hax ih => exact ih.ax (fregeIsAxiom_subst f hax)
  | @mp L A B _ hA hAB ih =>
    exact ih.mp (List.mem_map_of_mem hA) (List.mem_map_of_mem (f := Proposition.subst f) hAB)

/-- `Frege.DerivableInSize` is preserved under arbitrary formula substitution without increasing
the number of lines. -/
theorem fregeDerivableInSize_subst (f : ℕ → Formula) {Γ : List Formula} {φ : Formula} {s : ℕ}
    (h : Frege.DerivableInSize Γ φ s) :
    Frege.DerivableInSize (Γ.map (Proposition.subst f)) (φ.subst f) s := by
  obtain ⟨L, hL, hφ, hlen⟩ := h
  exact ⟨L.map (Proposition.subst f), fregeIsProof_subst f hL, List.mem_map_of_mem hφ,
    by simpa using hlen⟩

private theorem frege_exfalso (Γ : List Formula) (φ : Formula) :
    ∃ s, Frege.DerivableInSize Γ (.imp .falsum φ) s :=
  ⟨_, (Frege.DerivableInSize.ax (.k .falsum (.imp φ .falsum))).trans (.ax (.dne φ))⟩

private theorem frege_deduct {Γ : List Formula} {α φ : Formula}
    (h : ∃ s, Frege.DerivableInSize (Γ ++ [α]) φ s) :
    ∃ s, Frege.DerivableInSize Γ (.imp α φ) s := by
  obtain ⟨_, L, hL, hφ, _⟩ := h
  obtain ⟨L', hg, hmem⟩ := hL.deduction (L := []) .nil
  exact ⟨L'.length, L', hg.proof, hmem φ hφ, le_rfl⟩

private theorem frege_mono_hyp {Γ Γ' : List Formula} {φ : Formula} (hsub : Γ ⊆ Γ')
    (h : ∃ s, Frege.DerivableInSize Γ φ s) : ∃ s, Frege.DerivableInSize Γ' φ s :=
  let ⟨s, L, hL, hφ, hlen⟩ := h
  ⟨s, L, hL.mono hsub, hφ, hlen⟩

private theorem frege_mp {Γ : List Formula} {α β : Formula}
    (h1 : ∃ s, Frege.DerivableInSize Γ (.imp α β) s)
    (h2 : ∃ s, Frege.DerivableInSize Γ α s) : ∃ s, Frege.DerivableInSize Γ β s :=
  let ⟨_, d1⟩ := h1; let ⟨_, d2⟩ := h2; ⟨_, d1.mp d2⟩

private theorem frege_by_cases {Γ : List Formula} {α φ : Formula}
    (hpos : ∃ s, Frege.DerivableInSize (Γ ++ [α]) φ s)
    (hneg : ∃ s, Frege.DerivableInSize (Γ ++ [.imp α .falsum]) φ s) :
    ∃ s, Frege.DerivableInSize Γ φ s := by
  let nφ := Proposition.imp φ .falsum
  have hnα : ∃ s, Frege.DerivableInSize (Γ ++ [nφ]) (.imp α .falsum) s :=
    frege_deduct <| frege_mp ⟨1, .hyp (by simp [nφ])⟩
      (frege_mono_hyp (fun x hx => by simp at hx ⊢; tauto) hpos)
  have hnnα : ∃ s, Frege.DerivableInSize (Γ ++ [nφ]) (.imp (.imp α .falsum) .falsum) s :=
    frege_deduct <| frege_mp ⟨1, .hyp (by simp [nφ])⟩
      (frege_mono_hyp (fun x hx => by simp at hx ⊢; tauto) hneg)
  exact frege_mp ⟨1, .ax (.dne φ)⟩ (frege_deduct (frege_mp hnnα hnα))

private def signedAtom (σ : ℕ → Bool) (v : ℕ) : Formula :=
  if σ v then .atom v else .imp (.atom v) .falsum

private theorem frege_kalmar_eval (σ : ℕ → Bool) (φ : Formula) (Γ : List Formula)
    (hΓ : ∀ v ∈ formulaAtoms φ, signedAtom σ v ∈ Γ) :
    ∃ s, Frege.DerivableInSize Γ (if φ.eval σ then φ else .imp φ .falsum) s := by
  induction φ with
  | atom v =>
    have hmem := hΓ v (by simp)
    simp only [signedAtom, Proposition.eval_atom_bool] at hmem ⊢
    exact ⟨1, .hyp hmem⟩
  | falsum =>
    simp only [Proposition.eval_falsum_bool, Bool.false_eq_true, ↓reduceIte]
    exact ⟨5, .id .falsum⟩
  | and A B ihA ihB =>
    have dA := ihA fun v hv => hΓ v (by simp [hv])
    have dB := ihB fun v hv => hΓ v (by simp [hv])
    simp only [Proposition.eval_and_bool]
    by_cases hA : A.eval σ = true <;> by_cases hB : B.eval σ = true
    · simp only [hA, hB, Bool.and_self, ↓reduceIte] at dA dB ⊢
      exact frege_mp (frege_mp ⟨1, .ax (.andIntro A B)⟩ dA) dB
    · have hB' := Bool.eq_false_iff.2 hB
      simp only [hA, hB', Bool.and_false, Bool.false_eq_true, ↓reduceIte] at dA dB ⊢
      exact frege_deduct (frege_mp (frege_mono_hyp (by simp) dB)
        (frege_mp ⟨1, .ax (.andElimR A B)⟩ ⟨1, .hyp (by simp)⟩))
    · have hA' := Bool.eq_false_iff.2 hA
      simp only [hA', hB, Bool.false_and, Bool.false_eq_true, ↓reduceIte] at dA dB ⊢
      exact frege_deduct (frege_mp (frege_mono_hyp (by simp) dA)
        (frege_mp ⟨1, .ax (.andElimL A B)⟩ ⟨1, .hyp (by simp)⟩))
    · have hA' := Bool.eq_false_iff.2 hA; have hB' := Bool.eq_false_iff.2 hB
      simp only [hA', hB', Bool.and_self, Bool.false_eq_true, ↓reduceIte] at dA dB ⊢
      exact frege_deduct (frege_mp (frege_mono_hyp (by simp) dA)
        (frege_mp ⟨1, .ax (.andElimL A B)⟩ ⟨1, .hyp (by simp)⟩))
  | or A B ihA ihB =>
    have dA := ihA fun v hv => hΓ v (by simp [hv])
    have dB := ihB fun v hv => hΓ v (by simp [hv])
    simp only [Proposition.eval_or_bool]
    by_cases hA : A.eval σ = true <;> by_cases hB : B.eval σ = true
    · simp only [hA, hB, Bool.or_self, ↓reduceIte] at dA ⊢
      exact frege_mp ⟨1, .ax (.orIntroL A B)⟩ dA
    · have hB' := Bool.eq_false_iff.2 hB
      simp only [hA, hB', Bool.or_false, ↓reduceIte] at dA ⊢
      exact frege_mp ⟨1, .ax (.orIntroL A B)⟩ dA
    · have hA' := Bool.eq_false_iff.2 hA
      simp only [hA', hB, Bool.false_or, ↓reduceIte] at dB ⊢
      exact frege_mp ⟨1, .ax (.orIntroR A B)⟩ dB
    · have hA' := Bool.eq_false_iff.2 hA; have hB' := Bool.eq_false_iff.2 hB
      simp only [hA', hB', Bool.or_self, Bool.false_eq_true, ↓reduceIte] at dA dB ⊢
      exact frege_mp (frege_mp ⟨1, .ax (.orElim A B .falsum)⟩ dA) dB
  | imp A B ihA ihB =>
    have dA := ihA fun v hv => hΓ v (by simp [hv])
    have dB := ihB fun v hv => hΓ v (by simp [hv])
    simp only [Proposition.eval_imp_bool]
    by_cases hA : A.eval σ = true <;> by_cases hB : B.eval σ = true
    · simp only [hA, hB, Bool.not_true, Bool.false_or, ↓reduceIte] at dB ⊢
      exact frege_mp ⟨1, .ax (.k B A)⟩ dB
    · have hB' := Bool.eq_false_iff.2 hB
      simp only [hA, hB', Bool.not_true, Bool.or_self, Bool.false_eq_true, ↓reduceIte] at dA dB ⊢
      exact frege_deduct (frege_mp (frege_mono_hyp (by simp) dB)
        (frege_mp ⟨1, .hyp (by simp)⟩ (frege_mono_hyp (by simp) dA)))
    · have hA' := Bool.eq_false_iff.2 hA
      simp only [hA', hB, Bool.not_false, Bool.or_self, ↓reduceIte] at dB ⊢
      exact frege_mp ⟨1, .ax (.k B A)⟩ dB
    · have hA' := Bool.eq_false_iff.2 hA; have hB' := Bool.eq_false_iff.2 hB
      simp only [hA', hB', Bool.not_false, Bool.true_or, Bool.false_eq_true, ↓reduceIte] at dA ⊢
      exact frege_deduct (frege_mp (frege_exfalso _ B)
        (frege_mp (frege_mono_hyp (by simp) dA) ⟨1, .hyp (by simp)⟩))

private theorem frege_complete_aux {φ : Formula} (hφ : φ ∈ TAUT) :
    ∀ (vs : List ℕ) (σ : ℕ → Bool) (Γ : List Formula),
      (∀ u ∈ formulaAtoms φ, u ∉ vs → signedAtom σ u ∈ Γ) →
      ∃ s, Frege.DerivableInSize Γ φ s
  | [], σ, Γ, hΓ => by
    have hd := frege_kalmar_eval σ φ Γ fun u hu => hΓ u hu (by simp)
    simp only [hφ σ, ↓reduceIte] at hd; exact hd
  | v :: vs, σ, Γ, hΓ => by
    let σT : ℕ → Bool := Function.update σ v true
    let σF : ℕ → Bool := Function.update σ v false
    refine frege_by_cases (α := .atom v)
      (frege_complete_aux hφ vs σT (Γ ++ [.atom v]) fun u hu huvs => ?_)
      (frege_complete_aux hφ vs σF (Γ ++ [.imp (.atom v) .falsum]) fun u hu huvs => ?_)
    · by_cases huv : u = v
      · subst huv; simp [signedAtom, σT]
      · have hsame : signedAtom σT u = signedAtom σ u := by simp [signedAtom, σT, huv]
        exact hsame ▸ List.mem_append_left _ (hΓ u hu (by simp [huv, huvs]))
    · by_cases huv : u = v
      · subst huv; simp [signedAtom, σF]
      · have hsame : signedAtom σF u = signedAtom σ u := by simp [signedAtom, σF, huv]
        exact hsame ▸ List.mem_append_left _ (hΓ u hu (by simp [huv, huvs]))

/-- **Completeness of Hilbert-style Frege**: every classical propositional tautology
`φ ∈ TAUT` has a hypothesis-free `Frege` derivation. -/
theorem frege_complete {φ : Formula} (hφ : φ ∈ TAUT) :
    ∃ L : List Formula, Frege.IsProof [] L ∧ φ ∈ L := by
  classical
  obtain ⟨_, L, hL, hmem, _⟩ := frege_complete_aux hφ (formulaAtoms φ).toList (fun _ => false) []
    fun u hu hnot => absurd (Finset.mem_toList.2 hu) hnot
  exact ⟨L, hL, hmem⟩

/-- Constant-size Frege schema instantiation: every substitution instance `ψ.subst f` of a fixed
tautology schema `ψ ∈ TAUT` is derivable in `Frege` via a fixed template `L₀ : List Formula`
independent of `f` and `Γ`. -/
theorem exists_frege_schema_proof {ψ : Formula} (hψ : ψ ∈ TAUT) :
    ∃ L₀ : List Formula, Frege.IsProof [] L₀ ∧ ψ ∈ L₀ ∧
      ∀ (Γ : List Formula) (f : ℕ → Formula),
        Frege.IsProof Γ (L₀.map (Proposition.subst f)) ∧
        ψ.subst f ∈ L₀.map (Proposition.subst f) := by
  obtain ⟨L₀, hL₀, hmem⟩ := frege_complete hψ
  exact ⟨L₀, hL₀, hmem, fun Γ f =>
    ⟨(fregeIsProof_subst f hL₀).mono (by simp), List.mem_map_of_mem hmem⟩⟩

/-! ### Polynomial-time Extended Frege verifier and strong proof systems -/

/-- Tagged step certificate for Extended Frege augmented by an extra axiom set `A`. -/
inductive EFStep where
  /-- Frege axiom scheme `tag ∈ Fin 9` applied to formula arguments `(φ, ψ, χ)`. -/
  | fregeAx (tag : Fin 9) (φ ψ χ : Formula)
  /-- Modus ponens deriving `ψ` from line `i` (`φ`) and line `j` (`φ → ψ`). -/
  | mp (i j : ℕ)
  /-- Fresh extension definition introducing atom `q ↔ ψ` as `(q → ψ) ∧ (ψ → q)`. -/
  | ext (q : ℕ) (ψ : Formula)
  /-- Substitution instance `α.subst (listSubst pairs)` of an extra axiom `α ∈ A`. -/
  | extraAx (α : Formula) (pairs : List (ℕ × Formula))

/-- Build the `Frege.IsAxiom` formula for scheme index `tag : Fin 9` and arguments `(φ, ψ, χ)`. -/
def buildFregeAxiom (tag : Fin 9) (φ ψ χ : Formula) : Formula :=
  match tag with
  | ⟨0, _⟩ => .imp φ (.imp ψ φ)
  | ⟨1, _⟩ => .imp (.imp φ (.imp ψ χ)) (.imp (.imp φ ψ) (.imp φ χ))
  | ⟨2, _⟩ => .imp (.imp (.imp φ .falsum) .falsum) φ
  | ⟨3, _⟩ => .imp (.and φ ψ) φ
  | ⟨4, _⟩ => .imp (.and φ ψ) ψ
  | ⟨5, _⟩ => .imp φ (.imp ψ (.and φ ψ))
  | ⟨6, _⟩ => .imp φ (.or φ ψ)
  | ⟨7, _⟩ => .imp ψ (.or φ ψ)
  | ⟨8, _⟩ => .imp (.imp φ χ) (.imp (.imp ψ χ) (.imp (.or φ ψ) χ))

/-- Every output of `buildFregeAxiom` is a valid `Frege.IsAxiom`. -/
theorem isAxiom_buildFregeAxiom (tag : Fin 9) (φ ψ χ : Formula) :
    Frege.IsAxiom (buildFregeAxiom tag φ ψ χ) := by
  fin_cases tag
  exacts [.k φ ψ, .s φ ψ χ, .dne φ, .andElimL φ ψ, .andElimR φ ψ, .andIntro φ ψ,
    .orIntroL φ ψ, .orIntroR φ ψ, .orElim φ ψ χ]

/-- Every `Frege.IsAxiom` is realized by `buildFregeAxiom` with arguments strictly shorter than
the axiom formula itself (or `.falsum`). -/
theorem exists_buildFregeAxiom_of_isAxiom {θ : Formula} (h : Frege.IsAxiom θ) :
    ∃ (tag : Fin 9) (φ ψ χ : Formula), buildFregeAxiom tag φ ψ χ = θ ∧
      (encFormula φ).length ≤ (encFormula θ).length ∧
      (encFormula ψ).length ≤ (encFormula θ).length ∧
      (encFormula χ).length ≤ (encFormula θ).length := by
  have hbot' (α β : Formula) : (encFormula .falsum).length ≤ (encFormula (.imp α β)).length := by
    have h03 : ((encFinEnum (Fin 4)) 0).length ≤ ((encFinEnum (Fin 4)) 3).length := by decide
    have hle : (encFormula .falsum).length ≤ (frame (encFormTok (.inr 3))).length := by
      simp only [encFormula_apply, toPostfix_falsum, encList_cons, encList_nil, List.append_nil,
        length_frame, encFormTok_inr, encSum_inr, List.length_cons]; omega
    simp only [encFormula_imp, List.length_append]; omega
  cases h with
  | k φ ψ =>
    exact ⟨0, φ, ψ, .falsum, rfl, by simp [encFormula_imp],
      by simp only [encFormula_imp, List.length_append]; omega, hbot' _ _⟩
  | s φ ψ χ =>
    exact ⟨1, φ, ψ, χ, rfl,
      by simp only [encFormula_imp, List.length_append]; omega,
      by simp only [encFormula_imp, List.length_append]; omega,
      by simp only [encFormula_imp, List.length_append]; omega⟩
  | dne φ =>
    exact ⟨2, φ, .falsum, .falsum, rfl,
      by simp only [encFormula_imp, List.length_append]; omega, hbot' _ _, hbot' _ _⟩
  | andElimL φ ψ =>
    exact ⟨3, φ, ψ, .falsum, rfl,
      by simp only [encFormula_imp, encFormula_and, List.length_append]; omega,
      by simp only [encFormula_imp, encFormula_and, List.length_append]; omega, hbot' _ _⟩
  | andElimR φ ψ =>
    exact ⟨4, φ, ψ, .falsum, rfl,
      by simp only [encFormula_imp, encFormula_and, List.length_append]; omega,
      by simp only [encFormula_imp, encFormula_and, List.length_append]; omega, hbot' _ _⟩
  | andIntro φ ψ =>
    exact ⟨5, φ, ψ, .falsum, rfl,
      by simp only [encFormula_imp, encFormula_and, List.length_append]; omega,
      by simp only [encFormula_imp, encFormula_and, List.length_append]; omega, hbot' _ _⟩
  | orIntroL φ ψ =>
    exact ⟨6, φ, ψ, .falsum, rfl,
      by simp only [encFormula_imp, encFormula_or, List.length_append]; omega,
      by simp only [encFormula_imp, encFormula_or, List.length_append]; omega, hbot' _ _⟩
  | orIntroR φ ψ =>
    exact ⟨7, φ, ψ, .falsum, rfl,
      by simp only [encFormula_imp, encFormula_or, List.length_append]; omega,
      by simp only [encFormula_imp, encFormula_or, List.length_append]; omega, hbot' _ _⟩
  | orElim φ ψ χ =>
    exact ⟨8, φ, ψ, χ, rfl,
      by simp only [encFormula_imp, encFormula_or, List.length_append]; omega,
      by simp only [encFormula_imp, encFormula_or, List.length_append]; omega,
      by simp only [encFormula_imp, encFormula_or, List.length_append]; omega⟩

/-- Computable Boolean check whether atom `q` occurs in `φ`. -/
def occursIn (q : ℕ) (φ : Formula) : Bool :=
  (toPostfix φ).any fun | .inl v => v == q | .inr _ => false

/-- `occursIn q φ = true` iff `q ∈ formulaAtoms φ`. -/
@[simp]
theorem occursIn_eq_true_iff (q : ℕ) (φ : Formula) :
    occursIn q φ = true ↔ q ∈ formulaAtoms φ := by
  simp only [occursIn]
  induction φ with
  | atom v =>
    simp only [toPostfix_atom, List.any_cons, List.any_nil, Bool.or_false, beq_iff_eq,
      formulaAtoms_atom, mem_singleton]
    exact eq_comm
  | falsum => simp
  | and _ _ ihA ihB => simp [List.any_append, ihA, ihB]
  | or _ _ ihA ihB => simp [List.any_append, ihA, ihB]
  | imp _ _ ihA ihB => simp [List.any_append, ihA, ihB]

/-- Extract `(antecedent, consequent)` from an implication formula, if applicable. -/
def asImp : Formula → Option (Formula × Formula)
  | .imp a b => some (a, b)
  | _ => none

/-- Verified single step of an `EF + A` derivation (leaving `lines` unchanged on invalid steps). -/
def efStep (decA : Formula → Bool) (lines : List Formula) (s : EFStep) : List Formula :=
  match s with
  | .fregeAx tag φ ψ χ => buildFregeAxiom tag φ ψ χ :: lines
  | .mp i j =>
    if decide (i < lines.length) && decide (j < lines.length) then
      let a := lines.getD i .falsum
      match asImp (lines.getD j .falsum) with
      | some (a', b) => if a == a' then b :: lines else lines
      | none => lines
    else lines
  | .ext q ψ =>
    if !occursIn q ψ && lines.all (fun θ => !occursIn q θ) then
      .and (.imp (.atom q) ψ) (.imp ψ (.atom q)) :: lines
    else lines
  | .extraAx α pairs =>
    if decA α then α.subst (listSubst pairs) :: lines else lines

/-- Evaluate a verified `EF + A` derivation, rejecting any target formula that still mentions an
introduced extension atom (falling back to `⊤ = (⊥ → ⊥)`). -/
def runEFProof (decA : Formula → Bool) (steps : List EFStep) : Formula :=
  let lines := steps.foldl (efStep decA) []
  let target := lines.headD (.imp .falsum .falsum)
  let noExt := steps.all fun
    | .ext q _ => !occursIn q target
    | _ => true
  if noExt then target else .imp .falsum .falsum

/-- **Soundness of `runEFProof`**: every sequence of `EFStep`s evaluates to a tautology whenever
every formula accepted by `decA` belongs to `TAUT`. -/
theorem runEFProof_mem_taut {decA : Formula → Bool} (hA : ∀ α, decA α = true → α ∈ TAUT)
    (steps : List EFStep) : runEFProof decA steps ∈ TAUT := by
  let extAtoms : List EFStep → Finset ℕ := fun ss =>
    ss.foldr (fun s acc => match s with | .ext q _ => insert q acc | _ => acc) ∅
  have hext_sub (l : List EFStep) (s : EFStep) : extAtoms l ⊆ extAtoms (l ++ [s]) := by
    intro v hv; dsimp only [extAtoms] at hv ⊢
    induction l with
    | nil => simp at hv
    | cons x xs ihx =>
      cases x with
      | ext _ _ =>
        simp only [List.cons_append, List.foldr_cons, mem_insert] at hv ⊢
        exact hv.imp_right ihx
      | _ => simp only [List.cons_append, List.foldr_cons] at hv ⊢; exact ihx hv
  have hext_last (l : List EFStep) (q : ℕ) (ψ : Formula) : q ∈ extAtoms (l ++ [.ext q ψ]) := by
    dsimp only [extAtoms]
    induction l with
    | nil => simp
    | cons x _ ihx =>
      cases x with
      | ext _ _ => simp only [List.cons_append, List.foldr_cons, mem_insert]; exact Or.inr ihx
      | _ => simp only [List.cons_append, List.foldr_cons]; exact ihx
  have hext_mem : ∀ (l : List EFStep) {v : ℕ}, v ∈ extAtoms l → ∃ ψ, EFStep.ext v ψ ∈ l := by
    intro l
    induction l with
    | nil => intro v hv; simp [extAtoms] at hv
    | cons s ss ihs =>
      intro v hv
      cases s with
      | ext q ψ =>
        simp only [extAtoms, List.foldr_cons, mem_insert] at hv
        rcases hv with rfl | hv
        · exact ⟨ψ, List.mem_cons_self⟩
        · exact let ⟨ψ', hψ'⟩ := ihs hv; ⟨ψ', List.mem_cons_of_mem _ hψ'⟩
      | _ => exact let ⟨ψ', hψ'⟩ := ihs hv; ⟨ψ', List.mem_cons_of_mem _ hψ'⟩
  have hinv : ∀ (ss : List EFStep) (σ₀ : ℕ → Bool),
      ∃ σ : ℕ → Bool, (∀ v, v ∉ extAtoms ss → σ v = σ₀ v) ∧
        ∀ θ ∈ ss.foldl (efStep decA) [], θ.eval σ = true := by
    intro ss
    induction ss using List.reverseRecOn with
    | nil => exact fun σ₀ => ⟨σ₀, fun _ _ => rfl, by simp⟩
    | append_singleton pref s ih =>
      intro σ₀
      obtain ⟨σ, hσ_agree, hσ_sat⟩ := ih σ₀
      have hsub_ext : extAtoms pref ⊆ extAtoms (pref ++ [s]) := hext_sub pref s
      set lines := pref.foldl (efStep decA) []
      simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
      cases s with
      | fregeAx tag φ ψ χ =>
        refine ⟨σ, fun v hv => hσ_agree v fun h => hv (hsub_ext h), fun θ hθ => ?_⟩
        rcases List.mem_cons.1 hθ with rfl | hθ
        · exact (isAxiom_buildFregeAxiom tag φ ψ χ).eval σ
        · exact hσ_sat θ hθ
      | mp i j =>
        refine ⟨σ, fun v hv => hσ_agree v fun h => hv (hsub_ext h), fun θ hθ => ?_⟩
        dsimp only [efStep] at hθ
        split_ifs at hθ with hbounds
        · simp only [Bool.and_eq_true, decide_eq_true_eq] at hbounds
          obtain ⟨hi, hj⟩ := hbounds
          have hgi : lines.getD i .falsum = lines[i] := by
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
          have hgj : lines.getD j .falsum = lines[j] := by
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
          rw [hgi, hgj] at hθ
          have hi_sat := hσ_sat _ (List.getElem_mem hi)
          have hj_sat := hσ_sat _ (List.getElem_mem hj)
          cases hlj : lines[j] with
          | imp a' b =>
            rw [hlj] at hθ hj_sat
            dsimp only [asImp] at hθ
            split_ifs at hθ with heq
            · have ha_eq : lines[i] = a' := beq_iff_eq.1 heq
              rcases List.mem_cons.1 hθ with rfl | hθ
              · rw [ha_eq] at hi_sat; simpa [hi_sat] using hj_sat
              · exact hσ_sat θ hθ
            · exact hσ_sat θ hθ
          | _ => rw [hlj] at hθ; exact hσ_sat θ hθ
        · exact hσ_sat θ hθ
      | ext q ψ =>
        dsimp only [efStep]
        split_ifs with hfresh
        · simp only [Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true,
            ← Bool.not_eq_true, occursIn_eq_true_iff] at hfresh
          let σ' : ℕ → Bool := Function.update σ q (ψ.eval σ)
          have hq_mem : q ∈ extAtoms (pref ++ [.ext q ψ]) := hext_last pref q ψ
          refine ⟨σ', fun v hv => ?_, fun θ hθ => ?_⟩
          · have hvq : v ≠ q := fun h => hv (h ▸ hq_mem)
            simp [σ', hvq, hσ_agree v fun h => hv (hsub_ext h)]
          · have hψ_eq : ψ.eval σ' = ψ.eval σ :=
              eval_congr_atoms fun v hv =>
                Function.update_of_ne (fun h => hfresh.1 (by rwa [← h])) _ _
            rcases List.mem_cons.1 hθ with rfl | hθ
            · simp [hψ_eq, σ']
            · rw [eval_congr_atoms (σ₂ := σ) fun v hv =>
                Function.update_of_ne (fun h => hfresh.2 θ hθ (by rwa [← h])) _ _]
              exact hσ_sat θ hθ
        · exact ⟨σ, fun v hv => hσ_agree v fun h => hv (hsub_ext h), hσ_sat⟩
      | extraAx α pairs =>
        dsimp only [efStep]
        split_ifs with hdec
        · refine ⟨σ, fun v hv => hσ_agree v fun h => hv (hsub_ext h), fun θ hθ => ?_⟩
          rcases List.mem_cons.1 hθ with rfl | hθ
          · exact subst_mem_taut (hA α hdec) _ σ
          · exact hσ_sat θ hθ
        · exact ⟨σ, fun v hv => hσ_agree v fun h => hv (hsub_ext h), hσ_sat⟩
  intro σ₀
  dsimp only [runEFProof]
  split_ifs with hnoext
  · set lines := steps.foldl (efStep decA) []
    rcases hlines : lines with _ | ⟨target, rest⟩
    · exact verum_mem_taut σ₀
    · obtain ⟨σ, hσ_agree, hσ_sat⟩ := hinv steps σ₀
      have hdisj : ∀ v ∈ formulaAtoms target, v ∉ extAtoms steps := by
        simp only [hlines, List.headD_cons, List.all_eq_true] at hnoext
        intro v hv hmem
        obtain ⟨ψ, hψ⟩ := hext_mem steps hmem
        have hchk := hnoext (.ext v ψ) hψ
        simp only [Bool.not_eq_true', ← Bool.not_eq_true, occursIn_eq_true_iff] at hchk
        exact hchk hv
      rw [List.headD_cons, ← eval_congr_atoms (σ₁ := σ) (fun v hv => hσ_agree v (hdisj v hv))]
      exact hσ_sat target (by change target ∈ lines; rw [hlines]; exact List.mem_cons_self)
  · exact verum_mem_taut σ₀

private abbrev EFStepRaw : Type :=
  ((Fin 9 × (Formula × (Formula × Formula))) ⊕ (ℕ × ℕ)) ⊕
    ((ℕ × Formula) ⊕ (Formula × List (ℕ × Formula)))

private def efStepToRaw : EFStep → EFStepRaw
  | .fregeAx tag φ ψ χ => Sum.inl (Sum.inl (tag, (φ, (ψ, χ))))
  | .mp i j => Sum.inl (Sum.inr (i, j))
  | .ext q ψ => Sum.inr (Sum.inl (q, ψ))
  | .extraAx α pairs => Sum.inr (Sum.inr (α, pairs))

private def efStepFromRaw : EFStepRaw → EFStep
  | .inl (.inl (tag, (φ, (ψ, χ)))) => .fregeAx tag φ ψ χ
  | .inl (.inr (i, j)) => .mp i j
  | .inr (.inl (q, ψ)) => .ext q ψ
  | .inr (.inr (α, pairs)) => .extraAx α pairs

private def encEFStepRaw : EFStepRaw ↪ List Bool :=
  encSum
    (encSum (encPair (encFinEnum (Fin 9)) (encPair encFormula (encPair encFormula encFormula)))
      (encPair encUnary encUnary))
    (encSum (encPair encNat encFormula)
      (encPair encFormula (encList (encPair encNat encFormula))))

/-- Binary encoding of `EFStep` as a 4-way tagged sum. -/
def encEFStep : EFStep ↪ List Bool where
  toFun s := encEFStepRaw (efStepToRaw s)
  inj' s₁ s₂ h := by
    have hinj := congrArg efStepFromRaw (encEFStepRaw.injective h)
    rwa [show efStepFromRaw (efStepToRaw s₁) = s₁ by cases s₁ <;> rfl,
      show efStepFromRaw (efStepToRaw s₂) = s₂ by cases s₂ <;> rfl] at hinj

/-- Total polynomial-time decoder for `encEFStep`. -/
def efStepDecoder : Decoder encEFStep := by
  let D0 := Decoder.pair (finEnumDecoder 8)
    (Decoder.pair formulaDecoder (Decoder.pair formulaDecoder formulaDecoder))
  let D1 := Decoder.pair Decoder.unary Decoder.unary
  let D2 := Decoder.pair Decoder.nat formulaDecoder
  let D3 := Decoder.pair formulaDecoder (Decoder.list (Decoder.pair Decoder.nat formulaDecoder))
  let Draw : Decoder encEFStepRaw := Decoder.sum (Decoder.sum D0 D1) (Decoder.sum D2 D3)
  refine ⟨fun w => efStepFromRaw (Draw.decode w), fun s => ?_, ?_⟩
  · change efStepFromRaw (Draw.decode (encEFStepRaw (efStepToRaw s))) = s
    rw [Draw.decode_enc]; cases s <;> rfl
  · obtain ⟨_, _, hD⟩ := Draw.computable
    exact (hD.computableInPolyTime.of_enc_eq fun w => by
      rcases Draw.decode w with (⟨_, _, _, _⟩ | ⟨_, _⟩) | (⟨_, _⟩ | ⟨_, _⟩) <;> rfl).exists_degree

/-- Every hypothesis-free Frege proof `L` (`Frege.IsProof [] L`) compiles to a verified sequence of
`EFStep`s (with no `.ext` or `.extraAx` steps) executing to exact line stack `L`, with total
encoded length bounded by `32 * L.length * (M + L.length + 4)` whenever every line in `L` has
encoded length at most `M`. -/
theorem exists_efSteps_of_fregeIsProof {L : List Formula} (h : Frege.IsProof [] L)
    (decA : Formula → Bool) {M : ℕ} (hM : ∀ θ ∈ L, (encFormula θ).length ≤ M) :
    ∃ steps : List EFStep, steps.foldl (efStep decA) [] = L ∧
      (∀ s ∈ steps, match s with | .ext _ _ => False | _ => True) ∧
      (encList encEFStep steps).length ≤ 32 * L.length * (M + L.length + 4) := by
  induction h with
  | nil => exact ⟨[], rfl, by simp, by simp⟩
  | hyp _ hmem => cases hmem
  | @ax L θ _ hax ih =>
    obtain ⟨steps, hst, hno, hlen⟩ := ih fun α hα => hM α (List.mem_cons_of_mem _ hα)
    obtain ⟨tag, φ, ψ, χ, hbuild, hφ, hψ, hχ⟩ := exists_buildFregeAxiom_of_isAxiom hax
    have hθ := hM θ List.mem_cons_self
    refine ⟨steps ++ [.fregeAx tag φ ψ χ], ?_, fun s hs => ?_, ?_⟩
    · simp [List.foldl_append, hst, efStep, hbuild]
    · rcases List.mem_append.1 hs with hs | hs
      · exact hno s hs
      · simp only [List.mem_singleton] at hs; subst hs; trivial
    · have htag : ((encFinEnum (Fin 9)) tag).length ≤ 10 := by fin_cases tag <;> decide
      have hstep_len : (frame (encEFStep (.fregeAx tag φ ψ χ))).length ≤ 32 * (M + 4) := by
        simp only [length_frame, encEFStep, Function.Embedding.coeFn_mk, efStepToRaw, encEFStepRaw,
          encSum_inl, List.length_cons, length_encPair]
        omega
      simp only [encList_append, encList_cons, encList_nil, List.append_nil, List.length_append,
        List.length_cons]
      nlinarith
  | @mp L A B _ hA hAB ih =>
    obtain ⟨steps, hst, hno, hlen⟩ := ih fun α hα => hM α (List.mem_cons_of_mem _ hα)
    let i := L.idxOf A
    let j := L.idxOf (.imp A B)
    have hi : i < L.length := List.idxOf_lt_length_of_mem hA
    have hj : j < L.length := List.idxOf_lt_length_of_mem hAB
    refine ⟨steps ++ [.mp i j], ?_, fun s hs => ?_, ?_⟩
    · have hgetA : L.getD i .falsum = A := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
        exact List.getElem_idxOf hi
      have hgetAB : L.getD j .falsum = .imp A B := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
        exact List.getElem_idxOf hj
      simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, hst, efStep, hi, hj,
        decide_true, Bool.and_self, ↓reduceIte, hgetA, hgetAB, asImp, beq_self_eq_true]
    · rcases List.mem_append.1 hs with hs | hs
      · exact hno s hs
      · simp only [List.mem_singleton] at hs; subst hs; trivial
    · have hstep_len : (frame (encEFStep (.mp i j))).length ≤ 32 * (L.length + 4) := by
        simp only [length_frame, encEFStep, Function.Embedding.coeFn_mk, efStepToRaw, encEFStepRaw,
          encSum_inl, encSum_inr, List.length_cons, length_encPair, encUnary_apply,
          List.length_replicate]
        omega
      simp only [encList_append, encList_cons, encList_nil, List.append_nil, List.length_append,
        List.length_cons]
      nlinarith

/-- Compile any hypothesis-free Frege proof containing `φ` into a verified `EF` proof evaluating to
`φ`, with explicit encoded length bound. -/
theorem exists_runEFProof_of_fregeIsProof {L : List Formula} (hL : Frege.IsProof [] L)
    {φ : Formula} (hφ : φ ∈ L) (decA : Formula → Bool) {M : ℕ}
    (hM : ∀ θ ∈ L, (encFormula θ).length ≤ M) :
    ∃ steps : List EFStep, runEFProof decA steps = φ ∧
      (encList encEFStep steps).length ≤
        32 * (L.length + 6) * (9 * M + L.length + 160) := by
  let a1 : Formula := .imp φ (.imp (.imp φ φ) φ)
  let a2 : Formula := .imp φ (.imp φ φ)
  let a3 : Formula := .imp a1 (.imp a2 (.imp φ φ))
  let a4 : Formula := .imp a2 (.imp φ φ)
  let a5 : Formula := .imp φ φ
  have hfull : Frege.IsProof [] (φ :: a5 :: a4 :: a3 :: a2 :: a1 :: L) := by
    have p1 := hL.ax (Frege.IsAxiom.k φ (.imp φ φ))
    have p2 := p1.ax (Frege.IsAxiom.k φ φ)
    have p3 := p2.ax (Frege.IsAxiom.s φ (.imp φ φ) φ)
    have p4 := p3.mp (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
      List.mem_cons_self
    have p5 := p4.mp (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
      List.mem_cons_self
    exact p5.mp (by simp [hφ]) List.mem_cons_self
  have hφM : (encFormula φ).length ≤ M := hM φ hφ
  have hM' : ∀ θ ∈ (φ :: a5 :: a4 :: a3 :: a2 :: a1 :: L),
      (encFormula θ).length ≤ 9 * M + 150 := by
    have hop3 : (frame (encFormTok (.inr 3))).length ≤ 14 := by decide
    intro θ hθ
    simp only [List.mem_cons] at hθ
    rcases hθ with rfl | rfl | rfl | rfl | rfl | rfl | hθ
    · omega
    · simp only [a5, encFormula_imp, List.length_append]; omega
    · simp only [a4, a2, encFormula_imp, List.length_append]; omega
    · simp only [a3, a1, a2, encFormula_imp, List.length_append]; omega
    · simp only [a2, encFormula_imp, List.length_append]; omega
    · simp only [a1, encFormula_imp, List.length_append]; omega
    · exact (hM θ hθ).trans (by omega)
  obtain ⟨steps, hst, hno, hlen⟩ := exists_efSteps_of_fregeIsProof hfull decA hM'
  have hall : (steps.all fun | .ext q _ => !occursIn q φ | _ => true) = true :=
    List.all_eq_true.2 fun s hs => by
      cases s with
      | ext _ _ => exact (hno _ hs).elim
      | _ => rfl
  refine ⟨steps, by simp [runEFProof, hst, hall], hlen.trans (le_of_eq ?_)⟩
  simp only [List.length_cons]
  ring

private theorem computableInPolyTime_buildFregeAxiom :
    ComputableInPolyTime
      (fun p : Fin 9 × Formula × Formula × Formula =>
        buildFregeAxiom p.1 p.2.1 p.2.2.1 p.2.2.2)
      (encPair (encFinEnum (Fin 9)) (encPair encFormula (encPair encFormula encFormula)))
      encFormula := by
  let E := encPair (encFinEnum (Fin 9)) (encPair encFormula (encPair encFormula encFormula))
  have ht : ComputableInPolyTime Prod.fst E (encFinEnum (Fin 9)) := fst _ _
  have hφ : ComputableInPolyTime (fun p => p.2.1) E encFormula := (fst _ _).comp (snd _ _)
  have hψ : ComputableInPolyTime (fun p => p.2.2.1) E encFormula :=
    (fst _ _).comp ((snd _ _).comp (snd _ _))
  have hχ : ComputableInPolyTime (fun p => p.2.2.2) E encFormula :=
    (snd _ _).comp ((snd _ _).comp (snd _ _))
  let imp' {f g : _ → Formula} (hf : ComputableInPolyTime f E encFormula)
      (hg : ComputableInPolyTime g E encFormula) :=
    computableInPolyTime_imp.comp (hf.prod hg)
  let and' {f g : _ → Formula} (hf : ComputableInPolyTime f E encFormula)
      (hg : ComputableInPolyTime g E encFormula) :=
    computableInPolyTime_and.comp (hf.prod hg)
  let or' {f g : _ → Formula} (hf : ComputableInPolyTime f E encFormula)
      (hg : ComputableInPolyTime g E encFormula) :=
    computableInPolyTime_or.comp (hf.prod hg)
  have hchain :=
    ite_decide (decide_eq' ht (const 0)) (imp' hφ (imp' hψ hφ)) <|
    ite_decide (decide_eq' ht (const 1))
      (imp' (imp' hφ (imp' hψ hχ)) (imp' (imp' hφ hψ) (imp' hφ hχ))) <|
    ite_decide (decide_eq' ht (const 2))
      (imp' (imp' (imp' hφ (const .falsum)) (const .falsum)) hφ) <|
    ite_decide (decide_eq' ht (const 3)) (imp' (and' hφ hψ) hφ) <|
    ite_decide (decide_eq' ht (const 4)) (imp' (and' hφ hψ) hψ) <|
    ite_decide (decide_eq' ht (const 5)) (imp' hφ (imp' hψ (and' hφ hψ))) <|
    ite_decide (decide_eq' ht (const 6)) (imp' hφ (or' hφ hψ)) <|
    ite_decide (decide_eq' ht (const 7)) (imp' hψ (or' hφ hψ))
      (imp' (imp' hφ hχ) (imp' (imp' hψ hχ) (imp' (or' hφ hψ) hχ)))
  convert hchain using 1
  funext ⟨tag, φ, ψ, χ⟩
  fin_cases tag <;> rfl

private theorem computableInPolyTime_occursIn :
    ComputableInPolyTime (fun p : ℕ × Formula => occursIn p.1 p.2)
      (encPair encNat encFormula) encBool := by
  let E := encPair encNat encFormula
  let EM := encPair E encFormTok
  refine anyWithInput (computableInPolyTime_toPostfix.comp (snd encNat encFormula)) ?_
  exact (sumElimWithInput (eg := EM) (ea := encNat) (eb := encFinEnum (Fin 4))
    (left := fun (q : (ℕ × Formula) × FormTok) (v : ℕ) => v == q.1.1)
    (right := fun (_ : (ℕ × Formula) × FormTok) (_ : Fin 4) => false)
    (snd E encFormTok)
    (ComputableInPolyTime.beq (snd EM encNat)
      ((fst encNat encFormula).comp ((fst E encFormTok).comp (fst EM encNat))))
    (const false)).of_enc_eq fun q => by cases q.2 <;> rfl

private theorem computableInPolyTime_asImp :
    ComputableInPolyTime asImp encFormula (encOption (encPair encFormula encFormula)) := by
  let lastTok (toks : List FormTok) : Option FormTok := toks.reverse.head?
  have heq (φ : Formula) : asImp φ =
      if decide (lastTok (toPostfix φ) = some (.inr 3)) then
        let st := ((toPostfix φ).reverse.tail.reverse).foldl postfixStep []
        some (st.tail.headD .falsum, st.headD .falsum)
      else none := by
    cases φ <;> simp [asImp, lastTok, List.foldl_append, foldl_postfixStep_toPostfix]
  rw [show asImp = _ from funext heq]
  have hrev := (listReverse encFormTok).comp computableInPolyTime_toPostfix
  have hlast := (head? encFormTok).comp hrev
  have hdrop := (listReverse encFormTok).comp (listDropWithInput hrev (const 1))
  have hmem_len {toks : List FormTok} {t : FormTok} (ht : t ∈ toks) :
      (encFormTok t).length ≤ (encList encFormTok toks).length := by
    induction toks with
    | nil => cases ht
    | cons _ _ ih =>
      simp only [encList_cons, List.length_append, length_frame]
      rcases List.mem_cons.1 ht with rfl | h
      · omega
      · have := ih h; omega
  have hfold : ComputableInPolyTime
      (fun φ : Formula => ((toPostfix φ).reverse.tail.reverse).foldl postfixStep [])
      encFormula (encList encFormula) :=
    foldlWithInput_of_bounded_growth (encIn := encFormula) (encA := encFormTok)
      (encL := encList encFormTok) (encB := encList encFormula)
      (list := fun φ => (toPostfix φ).reverse.tail.reverse) (init := fun _ => [])
      (step := fun _ st t => postfixStep st t)
      (const []) ⟨hdrop.of_enc_eq fun φ => by
        change encList encFormTok (toPostfix φ).reverse.tail.reverse =
          encList encFormTok ((toPostfix φ).reverse.drop 1).reverse
        rw [List.drop_one],
        computableInPolyTime_postfixStep.comp
          (((snd _ _).comp (fst _ _)).prod (snd _ _)), inferInstance, inferInstance⟩
      (growth := fun φ => 4 * (encFormula φ).length + 30)
      ⟨(PolyBounded.self.mul (.const 4)).add (.const 30) |>.mono fun _ => by omega,
       fun φ st t ht => (length_postfixStep_le st t).trans <| by
        have hsub : t ∈ toPostfix φ :=
          List.mem_reverse.1 (List.mem_of_mem_tail (List.mem_reverse.1 ht))
        have := hmem_len hsub
        rw [encFormula_apply]; omega⟩
  have hb := listGetDWithInput hfold (const 0) (Proposition.falsum : Formula)
  have ha := listGetDWithInput hfold (const 1) (Proposition.falsum : Formula)
  have hres := ite_decide (decide_eq' hlast (const (some (Sum.inr 3 : FormTok))))
    ((optionSome (encPair encFormula encFormula)).comp (ha.prod hb))
    (const none)
  exact hres.of_enc_eq fun φ => by
    change encOption (encPair encFormula encFormula)
        (if decide ((toPostfix φ).reverse.head? = some (Sum.inr 3)) = true then
          let st := ((toPostfix φ).reverse.tail.reverse).foldl postfixStep []
          some (st.tail.headD .falsum, st.headD .falsum) else none) =
      encOption (encPair encFormula encFormula)
        (if (toPostfix φ).reverse.head? = some (Sum.inr 3) then
          let st := ((toPostfix φ).reverse.tail.reverse).foldl postfixStep []
          some (st.getD 1 .falsum, st.getD 0 .falsum) else none)
    congr 1
    by_cases hl : (toPostfix φ).reverse.head? = some (Sum.inr 3)
    · rw [ite_eq_left hl, ite_eq_left (decide_eq_true hl)]
      rcases ((toPostfix φ).reverse.tail.reverse).foldl postfixStep [] with
        _ | ⟨x, _ | ⟨y, zs⟩⟩ <;> rfl
    · rw [ite_eq_right hl, ite_eq_right (fun h => hl (of_decide_eq_true h))]

/-- Maximum encoded line length `10 * (N + 1) ^ 2` produced during an `EF + A` derivation of
total encoded length `N`: non-MP steps fit directly and MP only shrinks formulas. -/
private def efStepCapped (decA : Formula → Bool) (cap : ℕ) (lines : List Formula)
    (s : EFStep) : List Formula :=
  match s with
  | .mp i j =>
    if decide (i < lines.length) && decide (j < lines.length) then
      let a := lines.getD i .falsum
      match asImp (lines.getD j .falsum) with
      | some (a', b) =>
        if a == a' && decide ((encFormula b).length ≤ cap) then b :: lines else lines
      | none => lines
    else lines
  | other => efStep decA lines other

private theorem efStep_new_line_le (decA : Formula → Bool) {N : ℕ} {s : EFStep}
    (hs : (encEFStep s).length ≤ N) {lines : List Formula}
    (hlines : ∀ θ ∈ lines, (encFormula θ).length ≤ 10 * (N + 1) ^ 2 + 100) :
    efStepCapped decA (10 * (N + 1) ^ 2 + 100) lines s = efStep decA lines s ∧
      ∀ θ ∈ efStep decA lines s, (encFormula θ).length ≤ 10 * (N + 1) ^ 2 + 100 := by
  have hop_le (k : Fin 4) : (frame (encFormTok (.inr k))).length ≤ 14 := by
    fin_cases k <;> decide
  cases s with
  | fregeAx tag φ ψ χ =>
    refine ⟨rfl, fun θ hθ => ?_⟩
    rcases List.mem_cons.1 hθ with rfl | hθ
    · simp only [encEFStep, Function.Embedding.coeFn_mk, efStepToRaw, encEFStepRaw, encSum_inl,
        List.length_cons, length_encPair] at hs
      have := hop_le 1; have := hop_le 2; have := hop_le 3
      have hbot : (encFormula .falsum).length ≤ 14 := by decide
      have hb : (encFormula (buildFregeAxiom tag φ ψ χ)).length ≤ 4 * N + 100 := by
        fin_cases tag <;>
          simp only [buildFregeAxiom, encFormula_imp, encFormula_and, encFormula_or,
            List.length_append] <;> omega
      nlinarith
    · exact hlines θ hθ
  | mp i j =>
    dsimp only [efStepCapped, efStep]
    split_ifs with hbounds
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at hbounds
      have hgj : lines.getD j .falsum = lines[j] := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hbounds.2, Option.getD_some]
      rw [hgj]
      have hlj := hlines _ (List.getElem_mem hbounds.2)
      cases h : lines[j] with
      | imp a' b =>
        rw [h] at hlj
        have hb_le : (encFormula b).length ≤ 10 * (N + 1) ^ 2 + 100 := by
          simp only [encFormula_imp, List.length_append] at hlj; omega
        simp only [asImp, hb_le, decide_true, Bool.and_true]
        refine ⟨trivial, fun θ hθ => ?_⟩
        split_ifs at hθ
        · rcases List.mem_cons.1 hθ with rfl | hθ
          · exact hb_le
          · exact hlines θ hθ
        · exact hlines θ hθ
      | _ => exact ⟨rfl, hlines⟩
    · exact ⟨rfl, hlines⟩
  | ext q ψ =>
    refine ⟨rfl, fun θ hθ => ?_⟩
    dsimp only [efStep] at hθ
    split_ifs at hθ
    · rcases List.mem_cons.1 hθ with rfl | hθ
      · simp only [encEFStep, Function.Embedding.coeFn_mk, efStepToRaw, encEFStepRaw, encSum_inl,
          encSum_inr, List.length_cons, length_encPair] at hs
        have := hop_le 1; have := hop_le 3
        have hatom : (encFormula (.atom q)).length = 2 * ((encNat q).length + 1) + 1 := by
          simp only [encFormula_apply, toPostfix_atom, encList_cons, encList_nil, List.append_nil,
            length_frame, encFormTok_inl, encSum_inl, List.length_cons]
        simp only [encFormula_and, encFormula_imp, List.length_append, hatom]
        nlinarith
      · exact hlines θ hθ
    · exact hlines θ hθ
  | extraAx α pairs =>
    refine ⟨rfl, fun θ hθ => ?_⟩
    dsimp only [efStep] at hθ
    split_ifs at hθ
    · rcases List.mem_cons.1 hθ with rfl | hθ
      · simp only [encEFStep, Function.Embedding.coeFn_mk, efStepToRaw, encEFStepRaw, encSum_inr,
          List.length_cons, length_encPair] at hs
        have hval_le (v : ℕ) (hv : (frame (encFormTok (.inl v))).length ≤ N) :
            (encFormula (listSubst pairs v)).length ≤ N := by
          cases hf : pairs.find? (fun kv => kv.1 == v) with
          | none =>
            rw [listSubst_of_find?_eq_none hf]
            simpa only [encFormula_apply, toPostfix_atom, encList_cons, encList_nil,
              List.append_nil] using hv
          | some kv =>
            rw [listSubst_of_find?_eq_some hf]
            have hmem := List.mem_of_find?_eq_some hf
            have hkv_all : ∀ ps : List (ℕ × Formula), kv ∈ ps →
                (encFormula kv.2).length ≤ (encList (encPair encNat encFormula) ps).length := by
              intro ps
              induction ps with
              | nil => intro h; cases h
              | cons _ _ ih =>
                intro hm
                simp only [encList_cons, List.length_append, length_frame, length_encPair]
                rcases List.mem_cons.1 hm with rfl | h
                · omega
                · have := ih h; omega
            exact (hkv_all pairs hmem).trans (by omega)
        have hα_le : (encList encFormTok (toPostfix α)).length ≤ N := by
          change (encFormula α).length ≤ N; omega
        have htok_le : (toPostfix α).length ≤ N := by
          have htl : ∀ ts : List FormTok, ts.length ≤ (encList encFormTok ts).length := by
            intro ts
            induction ts with
            | nil => simp
            | cons _ _ ih =>
              simp only [List.length_cons, encList_cons, List.length_append, length_frame]; omega
          exact (htl (toPostfix α)).trans hα_le
        have hsub_le : ∀ ts : List FormTok, (encList encFormTok ts).length ≤ N →
            (encList encFormTok (ts.flatMap fun
              | .inl v => toPostfix (listSubst pairs v) | .inr op => [.inr op])).length ≤
              ts.length * N + (encList encFormTok ts).length := by
          intro ts
          induction ts with
          | nil => intro _; simp
          | cons t ts ih =>
            intro hts
            simp only [encList_cons, List.length_append] at hts
            have ihts := ih (by omega)
            cases t with
            | inl v =>
              have hv := hval_le v (by omega)
              rw [encFormula_apply] at hv
              simp only [List.flatMap_cons, encList_append, List.length_append, List.length_cons,
                encList_cons]; nlinarith
            | inr op =>
              simp only [List.flatMap_cons, encList_append, List.length_append, List.length_cons,
                encList_cons, encList_nil, List.append_nil]; nlinarith
        have hsub : (encFormula (α.subst (listSubst pairs))).length ≤
            (toPostfix α).length * N + (encList encFormTok (toPostfix α)).length := by
          rw [encFormula_apply, toPostfix_subst]; exact hsub_le (toPostfix α) hα_le
        nlinarith
      · exact hlines θ hθ
    · exact hlines θ hθ

private theorem foldl_efStepCapped_eq (decA : Formula → Bool) (ss : List EFStep) :
    ss.foldl (efStepCapped decA (10 * ((encList encEFStep ss).length + 1) ^ 2 + 100)) [] =
      ss.foldl (efStep decA) [] := by
  set N := (encList encEFStep ss).length
  have hmem_len {s : EFStep} (hs : s ∈ ss) : (encEFStep s).length ≤ N := by
    dsimp only [N]
    induction ss with
    | nil => cases hs
    | cons _ _ ih =>
      simp only [encList_cons, List.length_append, length_frame]
      rcases List.mem_cons.1 hs with rfl | h
      · omega
      · have := ih h; omega
  suffices ∀ (pref : List EFStep), (∀ s ∈ pref, (encEFStep s).length ≤ N) →
      pref.foldl (efStepCapped decA (10 * (N + 1) ^ 2 + 100)) [] =
        pref.foldl (efStep decA) [] ∧
      ∀ θ ∈ pref.foldl (efStep decA) [], (encFormula θ).length ≤ 10 * (N + 1) ^ 2 + 100 from
    (this ss fun _ hs => hmem_len hs).1
  intro pref
  induction pref using List.reverseRecOn with
  | nil => exact fun _ => ⟨rfl, by simp⟩
  | append_singleton p s ih =>
    intro hle
    obtain ⟨heq, hinv⟩ := ih fun x hx => hle x (List.mem_append_left _ hx)
    have hstep := efStep_new_line_le decA (hle s (by simp)) hinv
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, heq, hstep.1]
    exact ⟨trivial, hstep.2⟩

private theorem computableInPolyTime_mpStep (decA : Formula → Bool) :
    ComputableInPolyTime
      (fun p : (ℕ × List Formula) × (ℕ × ℕ) =>
        efStepCapped decA p.1.1 p.1.2 (.mp p.2.1 p.2.2))
      (encPair (encPair encUnary (encList encFormula)) (encPair encUnary encUnary))
      (encList encFormula) := by
  let EL := encPair encUnary (encList encFormula)
  let EU := encPair encUnary encUnary
  let E1 := encPair EL EU
  have hc : ComputableInPolyTime (fun p : (ℕ × List Formula) × (ℕ × ℕ) => p.1.1) E1 encUnary :=
    (fst encUnary (encList encFormula)).comp (fst EL EU)
  have hL : ComputableInPolyTime (fun p : (ℕ × List Formula) × (ℕ × ℕ) => p.1.2)
      E1 (encList encFormula) :=
    (snd encUnary (encList encFormula)).comp (fst EL EU)
  have hi : ComputableInPolyTime (fun p : (ℕ × List Formula) × (ℕ × ℕ) => p.2.1) E1 encUnary :=
    (fst encUnary encUnary).comp (snd EL EU)
  have hj : ComputableInPolyTime (fun p : (ℕ × List Formula) × (ℕ × ℕ) => p.2.2) E1 encUnary :=
    (snd encUnary encUnary).comp (snd EL EU)
  have hlenL := (length encFormula).comp hL
  have hok := bool_and' (unary_lt' hi hlenL) (unary_lt' hj hlenL)
  have ha := listGetDWithInput hL hi .falsum
  have hlj := computableInPolyTime_asImp.comp (listGetDWithInput hL hj .falsum)
  let EF2 := encPair encFormula encFormula
  have hb_to_bits : ComputableInPolyTime (fun φ : Formula => (encFormula φ : List Bool))
      encFormula encBits := ComputableInPolyTime.of_eq fun _ => rfl
  have hb_len := length_bits.comp (hb_to_bits.comp ((snd encFormula encFormula).comp (snd E1 EF2)))
  have hinner := bool_and'
    (ComputableInPolyTime.beq (ha.comp (fst E1 EF2))
      ((fst encFormula encFormula).comp (snd E1 EF2)))
    (unary_le' hb_len (hc.comp (fst E1 EF2)))
  have hmp := optionElimWithInput
    (body := fun (p : (ℕ × List Formula) × (ℕ × ℕ)) (ab : Formula × Formula) =>
      if (p.1.2.getD p.2.1 .falsum == ab.1) && decide ((encFormula ab.2).length ≤ p.1.1)
      then ab.2 :: p.1.2 else p.1.2)
    hlj hL
    ((ite_decide (decide_eq' hinner (const true))
      ((ComputableInPolyTime.cons encFormula).comp
        (((snd encFormula encFormula).comp (snd E1 EF2)).prod (hL.comp (fst E1 EF2))))
      (hL.comp (fst E1 EF2))).of_enc_eq fun _ => by congr 1)
  exact (ite_decide (decide_eq' hok (const true)) hmp hL).of_enc_eq fun p => by
    congr 1; dsimp only [efStepCapped, Function.comp_apply]
    by_cases h1 : p.2.1 < p.1.2.length <;> by_cases h2 : p.2.2 < p.1.2.length <;>
      (cases asImp (p.1.2.getD p.2.2 .falsum) <;> simp [h1, h2])

private theorem computableInPolyTime_extStep (decA : Formula → Bool) :
    ComputableInPolyTime
      (fun p : List Formula × (ℕ × Formula) => efStep decA p.1 (.ext p.2.1 p.2.2))
      (encPair (encList encFormula) (encPair encNat encFormula)) (encList encFormula) := by
  let ENF := encPair encNat encFormula
  let E2 := encPair (encList encFormula) ENF
  have hL : ComputableInPolyTime Prod.fst E2 (encList encFormula) := fst _ _
  have hq : ComputableInPolyTime (fun p : List Formula × (ℕ × Formula) => p.2.1) E2 encNat :=
    (fst encNat encFormula).comp (snd (encList encFormula) ENF)
  have hψ : ComputableInPolyTime (fun p : List Formula × (ℕ × Formula) => p.2.2) E2 encFormula :=
    (snd encNat encFormula).comp (snd (encList encFormula) ENF)
  have hqatom := computableInPolyTime_atom.comp hq
  have hform := computableInPolyTime_and.comp
    ((computableInPolyTime_imp.comp (hqatom.prod hψ)).prod
     (computableInPolyTime_imp.comp (hψ.prod hqatom)))
  have hfresh := bool_and'
    (bool_not.comp (computableInPolyTime_occursIn.comp (hq.prod hψ)))
    (allWithInput (test := fun p θ => !occursIn p.2.1 θ) hL
      ((bool_not.comp (computableInPolyTime_occursIn.comp
        ((hq.comp (fst E2 encFormula)).prod (snd E2 encFormula)))).of_enc_eq fun _ => rfl))
  exact (ite_decide (decide_eq' hfresh (const true))
    ((ComputableInPolyTime.cons encFormula).comp (hform.prod hL)) hL).of_enc_eq fun _ => by congr 1

private theorem computableInPolyTime_runEFProof {decA : Formula → Bool}
    (hdecA : ComputableInPolyTime decA encFormula encBool) :
    ComputableInPolyTime (runEFProof decA) (encList encEFStep) encFormula := by
  let enc0 := encPair (encFinEnum (Fin 9)) (encPair encFormula (encPair encFormula encFormula))
  let enc1 := encPair encUnary encUnary
  let enc2 := encPair encNat encFormula
  let enc3 := encPair encFormula (encList (encPair encNat encFormula))
  have htoRaw : ComputableInPolyTime efStepToRaw encEFStep encEFStepRaw :=
    ComputableInPolyTime.of_eq fun _ => rfl
  let cap (ss : List EFStep) : ℕ := 10 * ((encList encEFStep ss).length + 1) ^ 2 + 100
  have hcap : ComputableInPolyTime cap (encList encEFStep) encUnary := by
    have hlen : ComputableInPolyTime (fun ss : List EFStep => (encList encEFStep ss).length)
        (encList encEFStep) encUnary :=
      length_bits.comp (ComputableInPolyTime.of_eq fun _ => rfl)
    dsimp only [cap]; fun_prop
  let ES := encPair (encPair (encList encEFStep) (encList encFormula)) encEFStep
  have hssS : ComputableInPolyTime (fun p => p.1.1) ES (encList encEFStep) :=
    (fst _ _).comp (fst _ _)
  have hlinesS : ComputableInPolyTime (fun p => p.1.2) ES (encList encFormula) :=
    (snd _ _).comp (fst _ _)
  have hstep : ComputableInPolyTime (fun p : (List EFStep × List Formula) × EFStep =>
      efStepCapped decA (cap p.1.1) p.1.2 p.2) ES (encList encFormula) := by
    let p01 := (fst ES (encSum enc0 enc1)).comp (fst (encPair ES (encSum enc0 enc1)) enc0)
    let p11 := (fst ES (encSum enc0 enc1)).comp (fst (encPair ES (encSum enc0 enc1)) enc1)
    let p22 := (fst ES (encSum enc2 enc3)).comp (fst (encPair ES (encSum enc2 enc3)) enc2)
    let p33 := (fst ES (encSum enc2 enc3)).comp (fst (encPair ES (encSum enc2 enc3)) enc3)
    have h0 := (ComputableInPolyTime.cons encFormula).comp
      ((computableInPolyTime_buildFregeAxiom.comp (snd _ _)).prod (hlinesS.comp p01))
    have h1 := (computableInPolyTime_mpStep decA).comp
      (((hcap.comp (hssS.comp p11)).prod (hlinesS.comp p11)).prod (snd _ _))
    have h2 := (computableInPolyTime_extStep decA).comp ((hlinesS.comp p22).prod (snd _ _))
    have h3 : ComputableInPolyTime
        (fun q : ((_ × _) × _) × (Formula × List (ℕ × Formula)) =>
          efStep decA q.1.1.1.2 (.extraAx q.2.1 q.2.2))
        (encPair (encPair ES (encSum enc2 enc3)) enc3) (encList encFormula) := by
      have hL := hlinesS.comp p33
      have h23 := snd (encPair ES (encSum enc2 enc3)) enc3
      have hα := (fst encFormula (encList (encPair encNat encFormula))).comp h23
      have hp := (snd encFormula (encList (encPair encNat encFormula))).comp h23
      exact (ite_decide (hdecA.comp hα)
        ((ComputableInPolyTime.cons encFormula).comp
          ((computableInPolyTime_listSubst.comp (hp.prod hα)).prod hL)) hL).of_enc_eq fun _ => rfl
    have hL01 := sumElimWithInput
      (left := fun (p : ((List EFStep × List Formula) × EFStep) × _)
        (x : Fin 9 × (Formula × (Formula × Formula))) =>
        buildFregeAxiom x.1 x.2.1 x.2.2.1 x.2.2.2 :: p.1.1.2)
      (right := fun (p : ((List EFStep × List Formula) × EFStep) × _) (x : ℕ × ℕ) =>
        efStepCapped decA (cap p.1.1.1) p.1.1.2 (.mp x.1 x.2))
      (snd _ _) h0 h1
    have hR23 := sumElimWithInput
      (left := fun (p : ((List EFStep × List Formula) × EFStep) × _) (x : ℕ × Formula) =>
        efStep decA p.1.1.2 (.ext x.1 x.2))
      (right := fun (p : ((List EFStep × List Formula) × EFStep) × _)
        (x : Formula × List (ℕ × Formula)) =>
        efStep decA p.1.1.2 (.extraAx x.1 x.2))
      (snd _ _) h2 h3
    exact (sumElimWithInput
      (left := fun p s01 => Sum.elim
        (fun x : Fin 9 × (Formula × (Formula × Formula)) =>
          buildFregeAxiom x.1 x.2.1 x.2.2.1 x.2.2.2 :: p.1.2)
        (fun x : ℕ × ℕ => efStepCapped decA (cap p.1.1) p.1.2 (.mp x.1 x.2)) s01)
      (right := fun p s23 => Sum.elim
        (fun x : ℕ × Formula => efStep decA p.1.2 (.ext x.1 x.2))
        (fun x : Formula × List (ℕ × Formula) => efStep decA p.1.2 (.extraAx x.1 x.2)) s23)
      (htoRaw.comp (snd _ _))
      (hL01.of_enc_eq fun r => by cases r.2 <;> rfl)
      (hR23.of_enc_eq fun r => by cases r.2 <;> rfl)).of_enc_eq fun ⟨_, s⟩ => by cases s <;> rfl
  have hgrowth (ss : List EFStep) (lines : List Formula) (s : EFStep) (hs : s ∈ ss) :
      (encList encFormula (efStepCapped decA (cap ss) lines s)).length ≤
        (encList encFormula lines).length + (2 * cap ss + 1) := by
    have hs_len : (encEFStep s).length ≤ (encList encEFStep ss).length := by
      induction ss with
      | nil => cases hs
      | cons _ _ ih =>
        simp only [encList_cons, List.length_append, length_frame]
        rcases List.mem_cons.1 hs with rfl | h
        · omega
        · have := ih h; omega
    cases s with
    | mp i j =>
      dsimp only [efStepCapped]
      split_ifs with hb
      · cases asImp (lines.getD j .falsum) with
        | none => dsimp only; omega
        | some ab =>
          dsimp only
          split_ifs with hok
          · have hle : (encFormula ab.2).length ≤ cap ss :=
              of_decide_eq_true (Bool.and_eq_true_iff.1 hok).2
            simp only [encList_cons, List.length_append, length_frame]; omega
          · omega
      · omega
    | fregeAx tag φ ψ χ =>
      have hnew : (encFormula (buildFregeAxiom tag φ ψ χ)).length ≤ cap ss :=
        (efStep_new_line_le decA hs_len (lines := []) (by simp)).2
          (buildFregeAxiom tag φ ψ χ) List.mem_cons_self
      simp only [efStepCapped, efStep, encList_cons, List.length_append, length_frame]
      rw [add_comm _ (encList encFormula lines).length]
      exact Nat.add_le_add_left (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hnew) 1) _
    | ext q ψ =>
      dsimp only [efStepCapped, efStep]
      split_ifs with hf
      · simp only [Bool.and_eq_true] at hf
        have h0 : efStep decA [] (.ext q ψ) = [.and (.imp (.atom q) ψ) (.imp ψ (.atom q))] := by
          simp [efStep, hf.1]
        have hnew : (encFormula (.and (.imp (.atom q) ψ) (.imp ψ (.atom q)))).length ≤ cap ss :=
          (efStep_new_line_le decA hs_len (lines := []) (by simp)).2
            (.and (.imp (.atom q) ψ) (.imp ψ (.atom q))) (h0 ▸ List.mem_cons_self)
        simp only [encList_cons, List.length_append, length_frame]
        rw [add_comm _ (encList encFormula lines).length]
        exact Nat.add_le_add_left (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hnew) 1) _
      · omega
    | extraAx α pairs =>
      dsimp only [efStepCapped, efStep]
      split_ifs with hd
      · have h0 : efStep decA [] (.extraAx α pairs) = [α.subst (listSubst pairs)] := by
          simp [efStep, hd]
        have hnew : (encFormula (α.subst (listSubst pairs))).length ≤ cap ss :=
          (efStep_new_line_le decA hs_len (lines := []) (by simp)).2
            (α.subst (listSubst pairs)) (h0 ▸ List.mem_cons_self)
        simp only [encList_cons, List.length_append, length_frame]
        rw [add_comm _ (encList encFormula lines).length]
        exact Nat.add_le_add_left (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hnew) 1) _
      · omega
  have hfold_cap : ComputableInPolyTime
      (fun ss : List EFStep => ss.foldl (efStepCapped decA (cap ss)) [])
      (encList encEFStep) (encList encFormula) :=
    foldlWithInput_of_bounded_growth (encIn := encList encEFStep) (encA := encEFStep)
      (encL := encList encEFStep) (encB := encList encFormula)
      (list := id) (init := fun _ => [])
      (step := fun ss lines s => efStepCapped decA (cap ss) lines s)
      (const []) ⟨id', hstep, inferInstance, inferInstance⟩
      (growth := fun ss => 2 * cap ss + 1)
      ⟨by
        have hs : PolyBounded (fun ss : List EFStep => (encList encEFStep ss).length)
            (fun ss => (encList encEFStep ss).length + 1) := PolyBounded.self.add (.const 1)
        exact (((hs.mul hs).mul (.const 20)).add (.const 201)).mono fun _ => by
          dsimp only [cap]; ring_nf; omega,
       hgrowth⟩
  have hfold : ComputableInPolyTime (fun ss : List EFStep => ss.foldl (efStep decA) [])
      (encList encEFStep) (encList encFormula) :=
    hfold_cap.of_enc_eq fun ss => congrArg (encList encFormula) (foldl_efStepCapped_eq decA ss).symm
  let verumF : Formula := .imp .falsum .falsum
  have htarget : ComputableInPolyTime
      (fun ss : List EFStep => (ss.foldl (efStep decA) []).headD verumF)
      (encList encEFStep) encFormula :=
    (listGetDWithInput hfold (const 0) verumF).of_enc_eq fun ss => by
      cases ss.foldl (efStep decA) [] <;> rfl
  have hnoext : ComputableInPolyTime (fun ss : List EFStep => ss.all fun
      | .ext q _ => !occursIn q ((ss.foldl (efStep decA) []).headD verumF)
      | _ => true) (encList encEFStep) encBool := by
    refine allWithInput id' ?_
    let EA := encPair (encList encEFStep) encEFStep
    let ER := encPair EA (encSum enc2 enc3)
    have hinner := sumElimWithInput (eg := ER) (ea := enc2) (eb := enc3)
      (left := fun (r : (List EFStep × EFStep) × _) (x : ℕ × Formula) =>
        !occursIn x.1 ((r.1.1.foldl (efStep decA) []).headD verumF))
      (right := fun (_ : (List EFStep × EFStep) × _) (_ : Formula × List (ℕ × Formula)) => true)
      (snd EA (encSum enc2 enc3))
      (bool_not.comp (computableInPolyTime_occursIn.comp
        (((fst encNat encFormula).comp (snd ER enc2)).prod
          (htarget.comp ((fst (encList encEFStep) encEFStep).comp
            ((fst EA (encSum enc2 enc3)).comp (fst ER enc2)))))))
      (const true)
    exact (sumElimWithInput (eg := EA) (ea := encSum enc0 enc1) (eb := encSum enc2 enc3)
      (left := fun (_ : List EFStep × EFStep) _ => true)
      (right := fun (p : List EFStep × EFStep) s23 => Sum.elim
        (fun x : ℕ × Formula => !occursIn x.1 ((p.1.foldl (efStep decA) []).headD verumF))
        (fun _ => true) s23)
      (htoRaw.comp (snd (encList encEFStep) encEFStep)) (const true)
      (hinner.of_enc_eq fun r => by cases r.2 <;> rfl)).of_enc_eq
        fun ⟨_, s⟩ => by cases s <;> rfl
  exact ite_decide hnoext htarget (const verumF)

/-- **Extended Frege augmented by a polynomial-time extra axiom set `A ⊆ TAUT`**: a classical
Cook–Reckhow propositional proof system admitting all substitution instances of formulas in `A` as
additional axioms alongside Frege schemes, modus ponens, and fresh extension definitions. -/
noncomputable def extendedFregeWith (A : Set Formula) (hA : A ∈ P encFormula)
    (hsub : A ⊆ TAUT) : PropProofSystem where
  toFun π := runEFProof (Classical.choose (mem_P.1 hA)) ((Decoder.list efStepDecoder).decode π)
  computable := by
    obtain ⟨_, _, hD⟩ := (Decoder.list efStepDecoder).computable
    exact (computableInPolyTime_runEFProof (Classical.choose_spec (mem_P.1 hA)).1).comp
      hD.computableInPolyTime
  range_eq := by
    have hspec := Classical.choose_spec (mem_P.1 hA)
    refine Set.Subset.antisymm ?_ fun φ hφ => ?_
    · rintro _ ⟨π, rfl⟩
      exact runEFProof_mem_taut (fun α hα => hsub ((hspec.2 α).2 hα)) _
    · obtain ⟨L, hL, hmem⟩ := frege_complete hφ
      have hM_all : ∀ ls : List Formula, ∀ θ ∈ ls,
          (encFormula θ).length ≤ ls.foldr (fun θ acc => max (encFormula θ).length acc) 0 := by
        intro ls; induction ls with
        | nil => simp
        | cons _ _ ih =>
          intro θ hθ; rcases List.mem_cons.1 hθ with rfl | h
          · exact le_max_left _ _
          · exact (ih θ h).trans (le_max_right _ _)
      obtain ⟨steps, hrun, _⟩ := exists_runEFProof_of_fregeIsProof hL hmem _ (hM_all L)
      exact ⟨encList encEFStep steps, by
        change runEFProof _ ((Decoder.list efStepDecoder).decode (encList encEFStep steps)) = φ
        rw [(Decoder.list efStepDecoder).decode_enc, hrun]⟩

/-- The classical **Extended Frege** propositional proof system `EF` (`extendedFregeWith ∅`). -/
noncomputable def extendedFrege : PropProofSystem :=
  extendedFregeWith ∅ empty_mem_P (Set.empty_subset TAUT)

/-- A Cook–Reckhow propositional proof system `P` is **strong** iff it is Extended Frege `EF`
augmented by a polynomial-time subset `A ⊆ TAUT` of extra axioms closed under substitution
instances. -/
@[expose] def IsStrongPPS (P : PropProofSystem) : Prop :=
  ∃ (A : Set Formula) (hA : A ∈ Complexity.P encFormula) (hsub : A ⊆ TAUT),
    P = extendedFregeWith A hA hsub

/-- `extendedFregeWith A hA hsub` is a strong propositional proof system. -/
theorem isStrongPPS_extendedFregeWith (A : Set Formula) (hA : A ∈ Complexity.P encFormula)
    (hsub : A ⊆ TAUT) : IsStrongPPS (extendedFregeWith A hA hsub) :=
  ⟨A, hA, hsub, rfl⟩

/-- Classical Extended Frege `extendedFrege` is a strong propositional proof system. -/
theorem isStrongPPS_extendedFrege : IsStrongPPS extendedFrege :=
  isStrongPPS_extendedFregeWith ∅ empty_mem_P (Set.empty_subset TAUT)

/-- **One-step substitution-instance proofs in `extendedFregeWith A`.** For every `α ∈ A` and
every finite substitution `pairs : List (ℕ × Formula)`, the proof word encoding `[.extraAx α pairs]`
proves `α.subst (listSubst pairs)` in `extendedFregeWith A hA hsub` with linear length. -/
theorem extendedFregeWith_extraAx_proof (A : Set Formula) (hA : A ∈ Complexity.P encFormula)
    (hsub : A ⊆ TAUT) {α : Formula} (hα : α ∈ A) (pairs : List (ℕ × Formula)) :
    let π := encList encEFStep [.extraAx α pairs]
    extendedFregeWith A hA hsub π = α.subst (listSubst pairs) ∧
      π.length ≤ 4 * (encFormula α).length +
        4 * (encList (encPair encNat encFormula) pairs).length + 20 := by
  intro π
  let decA : Formula → Bool := Classical.choose (mem_P.1 hA)
  have hspec := Classical.choose_spec (mem_P.1 hA)
  have hdec : decA α = true := (hspec.2 α).1 hα
  refine ⟨?_, ?_⟩
  · have hfn : (extendedFregeWith A hA hsub).toFun π =
        runEFProof decA ((Decoder.list efStepDecoder).decode π) := rfl
    change (extendedFregeWith A hA hsub).toFun π = _
    rw [hfn, (Decoder.list efStepDecoder).decode_enc]
    simp [runEFProof, efStep, hdec]
  · simp only [π, encList_cons, encList_nil, List.append_nil, length_frame, encEFStep,
      Function.Embedding.coeFn_mk, efStepToRaw, encEFStepRaw, encSum_inr, List.length_cons,
      length_encPair]
    omega

/-- **Deriving `χ` in `extendedFregeWith A` from a substitution instance of `α ∈ A` and a pure
`EF` implication proof.** -/
theorem extendedFregeWith_extraAx_mp (A : Set Formula) (hA : A ∈ Complexity.P encFormula)
    (hsub : A ⊆ TAUT) {α χ : Formula} (hα : α ∈ A) (pairs : List (ℕ × Formula))
    (steps : List EFStep)
    (hrun : runEFProof (fun _ => false) steps = .imp (α.subst (listSubst pairs)) χ) :
    ∃ π : List Bool, extendedFregeWith A hA hsub π = χ ∧
      π.length ≤ 4 * (encFormula α).length +
        4 * (encList (encPair encNat encFormula) pairs).length +
        (encList encEFStep steps).length + 64 := by
  have h1step (heq : α.subst (listSubst pairs) = χ) :=
    let ⟨h1, h2⟩ := extendedFregeWith_extraAx_proof A hA hsub hα pairs
    (⟨_, h1.trans heq, by omega⟩ : ∃ π : List Bool, extendedFregeWith A hA hsub π = χ ∧
      π.length ≤ 4 * (encFormula α).length +
        4 * (encList (encPair encNat encFormula) pairs).length +
        (encList encEFStep steps).length + 64)
  let decA : Formula → Bool := Classical.choose (mem_P.1 hA)
  have hdec : decA α = true := ((Classical.choose_spec (mem_P.1 hA)).2 α).1 hα
  let isPure : EFStep → Bool := fun | .extraAx _ _ => false | _ => true
  have hpure_fold : ∀ (ls : List EFStep) (init : List Formula),
      (ls.filter isPure).foldl (efStep decA) init = ls.foldl (efStep (fun _ => false)) init := by
    intro ls; induction ls with
    | nil => intro _; rfl
    | cons s _ ih => intro init; cases s <;> simp [isPure, efStep, ih]
  have hpure_len : ∀ ls : List EFStep,
      (encList encEFStep (ls.filter isPure)).length ≤ (encList encEFStep ls).length := by
    intro ls; induction ls with
    | nil => exact le_rfl
    | cons s _ ih =>
      cases h : isPure s <;>
        simp only [List.filter, h, encList_cons, List.length_append, length_frame] <;> omega
  dsimp only [runEFProof] at hrun
  split_ifs at hrun with hnoext
  · rcases hL0 : steps.foldl (efStep (fun _ => false)) [] with _ | ⟨hd, tl⟩
    · rw [hL0, List.headD_nil] at hrun
      exact h1step ((Proposition.imp.inj hrun).1.symm.trans (Proposition.imp.inj hrun).2)
    · rw [hL0, List.headD_cons] at hrun hnoext
      let full := steps.filter isPure ++ [.extraAx α pairs, .mp 0 1]
      refine ⟨encList encEFStep full, ?_, ?_⟩
      · change runEFProof decA ((Decoder.list efStepDecoder).decode (encList encEFStep full)) = χ
        rw [(Decoder.list efStepDecoder).decode_enc]
        have hfold : full.foldl (efStep decA) [] =
            χ :: α.subst (listSubst pairs) :: (.imp (α.subst (listSubst pairs)) χ) :: tl := by
          simp [full, List.foldl_append, hpure_fold, hL0, hrun, efStep, hdec, asImp]
        have hall : (full.all fun | .ext q _ => !occursIn q χ | _ => true) = true :=
          List.all_eq_true.2 fun s hs => by
            rcases List.mem_append.1 hs with hs | hs
            · cases s with
              | ext q ψ =>
                have hq := List.all_eq_true.1 hnoext (.ext q ψ) (List.mem_of_mem_filter hs)
                rw [hrun] at hq
                simp only [Bool.not_eq_true', ← Bool.not_eq_true, occursIn_eq_true_iff,
                  formulaAtoms_imp, mem_union, not_or] at hq ⊢; exact hq.2
              | _ => rfl
            · simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
              rcases hs with rfl | rfl <;> rfl
        simp [runEFProof, hfold, hall]
      · have hmp : (frame (encEFStep (.mp 0 1))).length ≤ 40 := by decide
        have hcl := hpure_len steps
        have hex : (frame (encEFStep (.extraAx α pairs))).length ≤
            4 * (encFormula α).length +
              4 * (encList (encPair encNat encFormula) pairs).length + 20 := by
          simp only [length_frame, encEFStep, Function.Embedding.coeFn_mk, efStepToRaw,
            encEFStepRaw, encSum_inr, List.length_cons, length_encPair]; omega
        simp only [full, encList_append, encList_cons, encList_nil, List.append_nil,
          List.length_append]; omega
  · exact h1step ((Proposition.imp.inj hrun).1.symm.trans (Proposition.imp.inj hrun).2)

/-! ### Closure of an arbitrary Cook–Reckhow pps under atom shifts, substitution, and Frege MP -/

private def closeCertEnc :
    (List Bool × (ℕ × (List (ℕ × Formula) × List EFStep))) ↪ List Bool :=
  encPair encBits
    (encPair encNat (encPair (encList (encPair encNat encFormula)) (encList encEFStep)))

private def closeCertDecoder : Decoder closeCertEnc :=
  Decoder.pair Decoder.bits
    (Decoder.pair Decoder.nat
      (Decoder.pair (Decoder.list (Decoder.pair Decoder.nat formulaDecoder))
        (Decoder.list efStepDecoder)))

private def closeCertEval (R : PropProofSystem)
    (c : List Bool × (ℕ × (List (ℕ × Formula) × List EFStep))) : Formula :=
  let baseForm := (renameAtoms (· - c.2.1) (R c.1)).subst (listSubst c.2.2.1)
  match asImp (runEFProof (fun _ => false) c.2.2.2) with
  | some (a, b) => if a == baseForm then b else baseForm
  | none => baseForm

/-- Canonical extension `closeUnderSubstFrege R` of any Cook–Reckhow propositional proof system
`R`: stays a classical Cook–Reckhow pps and derives in linear overhead any formula `χ` obtained
from an `R`-proved formula `φ` by shifting atoms downward (`· - base`), applying a finite
substitution `listSubst pairs`, and applying modus ponens against a verified Frege proof of
`((renameAtoms (· - base) φ).subst (listSubst pairs)) → χ`. -/
noncomputable def closeUnderSubstFrege (R : PropProofSystem) : PropProofSystem where
  toFun w := closeCertEval R (closeCertDecoder.decode w)
  computable := by
    obtain ⟨_, _, hDC⟩ := closeCertDecoder.computable
    have hπ : ComputableInPolyTime Prod.fst closeCertEnc encBits := fst _ _
    have hbase : ComputableInPolyTime (fun c => c.2.1) closeCertEnc encNat :=
      (fst _ _).comp (snd _ _)
    have hpairs : ComputableInPolyTime (fun c => c.2.2.1) closeCertEnc
        (encList (encPair encNat encFormula)) := (fst _ _).comp ((snd _ _).comp (snd _ _))
    have hsteps : ComputableInPolyTime (fun c => c.2.2.2) closeCertEnc (encList encEFStep) :=
      (snd _ _).comp ((snd _ _).comp (snd _ _))
    have hbf := computableInPolyTime_listSubst.comp
      (hpairs.prod (computableInPolyTime_shiftDown.comp (hbase.prod (R.computable.comp hπ))))
    have himp := computableInPolyTime_asImp.comp
      ((computableInPolyTime_runEFProof (const false)).comp hsteps)
    have heval : ComputableInPolyTime (closeCertEval R) closeCertEnc encFormula :=
      (optionElimWithInput
        (body := fun (c : List Bool × (ℕ × (List (ℕ × Formula) × List EFStep)))
          (ab : Formula × Formula) =>
          let bf := (renameAtoms (· - c.2.1) (R c.1)).subst (listSubst c.2.2.1)
          if ab.1 == bf then ab.2 else bf)
        himp hbf
        ((ite_decide (ComputableInPolyTime.beq ((fst _ _).comp (snd _ _)) (hbf.comp (fst _ _)))
          ((snd _ _).comp (snd _ _))
          (hbf.comp (fst _ _))).of_enc_eq fun r => by
            dsimp only [Function.comp_apply]
            by_cases he : r.2.1 = (renameAtoms (· - r.1.2.1) (R r.1.1)).subst (listSubst r.1.2.2.1)
              <;> simp [he])).of_enc_eq fun c => by
        dsimp only [closeCertEval, Function.comp_apply]
        cases asImp (runEFProof (fun _ => false) c.2.2.2) <;> rfl
    exact heval.comp hDC.computableInPolyTime
  range_eq := by
    refine Set.Subset.antisymm ?_ fun φ hφ => ?_
    · rintro _ ⟨w, rfl⟩
      set c := closeCertDecoder.decode w
      have hbf : (renameAtoms (· - c.2.1) (R c.1)).subst (listSubst c.2.2.1) ∈ TAUT :=
        subst_mem_taut (renameAtoms_mem_taut (R.mem c.1) _) _
      have himp : runEFProof (fun _ => false) c.2.2.2 ∈ TAUT :=
        runEFProof_mem_taut (fun _ h => Bool.noConfusion h) _
      dsimp only [closeCertEval]
      cases h : runEFProof (fun _ => false) c.2.2.2 with
      | imp a b =>
        rw [h] at himp; dsimp only [asImp]
        split_ifs with heq
        · rw [beq_iff_eq.1 heq] at himp
          intro σ
          have hi := himp σ
          have htr := hbf σ
          rw [Proposition.eval_imp_bool, htr] at hi
          simpa using hi
        · exact hbf
      | _ => exact hbf
    · obtain ⟨π, rfl⟩ := R.exists_eq hφ
      refine ⟨closeCertEnc (π, (0, ([], []))), ?_⟩
      change closeCertEval R (closeCertDecoder.decode (closeCertEnc (π, (0, ([], []))))) = R π
      rw [closeCertDecoder.decode_enc]
      have hsub0 : listSubst [] = Proposition.atom := funext fun _ => rfl
      have hren0 : renameAtoms (· - 0) (R π) = R π :=
        toPostfix_injective (by
          rw [toPostfix_renameAtoms]
          exact (List.map_congr_left fun t _ => by cases t <;> rfl).trans (List.map_id _))
      have hbf0 : (renameAtoms (· - 0) (R π)).subst (listSubst []) = R π := by
        rw [hren0, hsub0, subst_atom]
      have hrun0 : runEFProof (fun _ => false) [] = .imp .falsum .falsum := rfl
      dsimp only [closeCertEval]
      rw [hrun0, hbf0]; dsimp only [asImp]
      by_cases he : Proposition.falsum = R π <;> simp [he]

/-- Deriving `χ` in `closeUnderSubstFrege R` from an `R`-proof `π`, a downward atom shift `base`,
a finite substitution `pairs`, and a verified Frege proof `steps` of
`((renameAtoms (· - base) (R π)).subst (listSubst pairs)) → χ`, with linear proof-length bound. -/
theorem closeUnderSubstFrege_derive (R : PropProofSystem) (π : List Bool) (base : ℕ)
    (pairs : List (ℕ × Formula)) {χ : Formula} (steps : List EFStep)
    (hrun : runEFProof (fun _ => false) steps =
      .imp ((renameAtoms (· - base) (R π)).subst (listSubst pairs)) χ) :
    ∃ π' : List Bool, closeUnderSubstFrege R π' = χ ∧
      π'.length ≤ 8 * π.length + 8 * (encNat base).length +
        8 * (encList (encPair encNat encFormula) pairs).length +
        8 * (encList encEFStep steps).length + 32 := by
  refine ⟨closeCertEnc (π, (base, (pairs, steps))), ?_, ?_⟩
  · change closeCertEval R (closeCertDecoder.decode (closeCertEnc (π, (base, (pairs, steps))))) = χ
    rw [closeCertDecoder.decode_enc]; simp [closeCertEval, hrun, asImp]
  · simp only [closeCertEnc, length_encPair, encBits_apply]; omega

/-- Shifting atoms downward from an `R`-proof `π` in `closeUnderSubstFrege R` with linear overhead
in `π.length` and `(encNat base).length`. -/
theorem closeUnderSubstFrege_shift (R : PropProofSystem) (π : List Bool) (base : ℕ) :
    ∃ π' : List Bool, closeUnderSubstFrege R π' = renameAtoms (· - base) (R π) ∧
      π'.length ≤ 8 * π.length + 8 * (encNat base).length + 32 := by
  refine ⟨closeCertEnc (π, (base, ([], []))), ?_, ?_⟩
  · change closeCertEval R (closeCertDecoder.decode (closeCertEnc (π, (base, ([], []))))) = _
    rw [closeCertDecoder.decode_enc]
    have hsub0 : listSubst [] = Proposition.atom := funext fun _ => rfl
    have hrun0 : runEFProof (fun _ => false) [] = .imp .falsum .falsum := rfl
    dsimp only [closeCertEval]
    rw [hrun0, hsub0, subst_atom]; dsimp only [asImp]
    by_cases he : Proposition.falsum = renameAtoms (· - base) (R π) <;> simp [he]
  · simp only [closeCertEnc, length_encPair, encBits_apply, encList_nil, List.length_nil]; omega

end CslibFrontier.ProofComplexity
