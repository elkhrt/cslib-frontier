module

public import Cslib.Logics.Propositional.Defs
public import CslibFrontier.Logics.Propositional.Semantics
public import CslibFrontier.Computability.Circuit.Boolean.Substitution
public import CslibFrontier.Computability.Circuit.Frontier.Nondeterministic
public import CslibFrontier.Computability.Complexity.ProofSystem
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Finite
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Sum
import Cslib.Foundations.Data.Polynomial.Monotone
import CslibFrontier.Computability.Circuit.Boolean.PolynomialTime
import CslibFrontier.Computability.Circuit.Synthesis
import CslibFrontier.Computability.Complexity.ProofSystem.Exhaustive
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Sum
import CslibFrontier.Computability.Machines.Turing.MultiTape.Deterministic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Length
import CslibFrontier.Computability.Machines.Turing.MultiTape.Universal.Clocked
import CslibFrontier.Computability.Machines.Turing.MultiTape.Universal.PolyTime
import CslibFrontier.Foundations.Data.BitString.List.Binary
import Mathlib.Data.Nat.Pairing
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Propositional Proof Systems, Advice, and Feasible Disjunction Properties

This module builds the foundational theory of Cook–Reckhow propositional proof systems over
`Cslib.Logic.PL.Proposition ℕ`, proved under standard Lean axioms:

1. **Formula semantics, variable-disjoint disjunctions, and postfix binary encoding**: truth-table
   tautologies (`TAUT`), atom supports (`formulaAtoms`), pairwise atom-disjoint disjunctions
   (`bigOr`, `AreAtomDisjoint`), and an injective reverse-Polish binary encoding `encFormula` with
   a total polynomial-time decoder and polynomial-time syntactic combinators.
2. **Cook–Reckhow propositional proof systems and feasible disjunction**: `PropProofSystem` as
   `Cslib.Complexity.ProofSystem encFormula TAUT`, the minimum lengths-of-proofs function
   `proofLength`, the binary feasible disjunction property (`HasFDP`), and the strong feasible
   disjunction property (`HasStrongFDP` and its polynomial-bound variant `HasStrongFDPPoly`).
3. **Propositional proof systems with advice and universal one-bit-advice simulation**:
   `PropProofSystemWithAdvice k`, existence of a propositional proof system with `1` bit of advice
   that uniformly p-simulates every Cook–Reckhow propositional proof system
   (`exists_pps_one_bit_advice_pSimulates_all`), and polynomial-size nondeterministic De Morgan
   circuits deciding short provability in a `1`-bit-advice proof system
   (`exists_nondetCircuit_adviceProofLength_le`).

## Main definitions

* `CslibFrontier.ProofComplexity.Formula`, `CslibFrontier.ProofComplexity.TAUT`: propositional
  formulas over `ℕ` and the set of classical propositional tautologies.
* `CslibFrontier.ProofComplexity.formulaAtoms`, `CslibFrontier.ProofComplexity.bigOr`,
  `CslibFrontier.ProofComplexity.AreAtomDisjoint`: atom supports and variable-disjoint disjunctions.
* `CslibFrontier.ProofComplexity.encFormula`, `CslibFrontier.ProofComplexity.formulaDecoder`:
  injective postfix binary encoding and total polynomial-time decoder for `Formula`.
* `CslibFrontier.ProofComplexity.PropProofSystem`, `CslibFrontier.ProofComplexity.proofLength`:
  Cook–Reckhow propositional proof systems and lengths of proofs.
* `CslibFrontier.ProofComplexity.HasFDP`, `CslibFrontier.ProofComplexity.HasStrongFDP`,
  `CslibFrontier.ProofComplexity.HasStrongFDPPoly`: binary and strong feasible disjunction
  properties.
* `CslibFrontier.ProofComplexity.PropProofSystemWithAdvice`: propositional proof systems with `k(n)`
  bits of advice on inputs of length `n`.

## Main results

* `CslibFrontier.ProofComplexity.bigOr_mem_taut_iff_of_areAtomDisjoint`: a pairwise atom-disjoint
  disjunction is a tautology iff at least one disjunct is a tautology.
* `CslibFrontier.ProofComplexity.taut_mem_coNP`: `TAUT` belongs to `coNP encFormula`.
* `CslibFrontier.ProofComplexity.exists_pps_one_bit_advice_pSimulates_all`: a propositional proof
  system with `1` bit of advice p-simulates all Cook–Reckhow propositional proof systems.
* `CslibFrontier.ProofComplexity.exists_nondetCircuit_adviceProofLength_le`: short provability in a
  `1`-bit-advice propositional proof system is decided by polynomial-size nondeterministic De
  Morgan circuits.


-/

public section

namespace CslibFrontier.ProofComplexity

open Finset
open Cslib Cslib.Logic Cslib.Logic.PL Cslib.Circuits Cslib.Circuits.Boolean Cslib.Complexity
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime

/-! ### Propositional formulas, tautologies, atoms, and disjoint disjunctions -/

/-- Classical propositional formulas over natural-number atoms (`Cslib.Logic.PL.Proposition ℕ`). -/
abbrev Formula : Type := Proposition ℕ

/-- The Boolean constant formula: `⊤` (`⊥ → ⊥`) for `true` and `⊥` for `false`. -/
@[expose]
def boolConst (b : Bool) : Formula :=
  if b then .imp .falsum .falsum else .falsum

/-- Evaluation of `boolConst b` equals `b` under every Boolean assignment. -/
@[simp]
theorem eval_boolConst (b : Bool) (σ : ℕ → Bool) : (boolConst b).eval σ = b := by
  cases b <;> simp [boolConst]

/-- The set `TAUT` of classical propositional tautologies over `ℕ`-indexed atoms. -/
@[expose]
def TAUT : Set Formula :=
  {φ | ∀ σ : ℕ → Bool, φ.eval σ = true}

/-- The canonical tautology `⊤ = (⊥ → ⊥)` belongs to `TAUT`. -/
theorem verum_mem_taut : (.imp .falsum .falsum : Formula) ∈ TAUT :=
  fun _ => by simp

/-- Falsum `⊥` is not a tautology. -/
theorem falsum_notMem_taut : (.falsum : Formula) ∉ TAUT :=
  fun h => Bool.false_ne_true (h fun _ => false)

/-- Substituting into an atomic formula evaluates the substitution at that atom. -/
theorem subst_var (f : ℕ → Formula) (v : ℕ) : (Proposition.atom v).subst f = f v := rfl

/-- Substituting into `⊥` yields `⊥`. -/
theorem subst_falsum (f : ℕ → Formula) : (Proposition.falsum : Formula).subst f = .falsum := rfl

/-- Substitution distributes over conjunction. -/
theorem subst_and (f : ℕ → Formula) (A B : Formula) :
    (Proposition.and A B).subst f = .and (A.subst f) (B.subst f) := rfl

/-- Substitution distributes over disjunction. -/
theorem subst_or (f : ℕ → Formula) (A B : Formula) :
    (Proposition.or A B).subst f = .or (A.subst f) (B.subst f) := rfl

/-- Substitution distributes over implication. -/
theorem subst_imp (f : ℕ → Formula) (A B : Formula) :
    (Proposition.imp A B).subst f = .imp (A.subst f) (B.subst f) := rfl

/-- Boolean evaluation commutes with formula substitution. -/
theorem eval_subst_bool (f : ℕ → Formula) (φ : Formula) (σ : ℕ → Bool) :
    (φ.subst f).eval σ = φ.eval (fun v => (f v).eval σ) := by
  induction φ with
  | atom _ | falsum => rfl
  | and _ _ ihA ihB => simp [subst_and, ihA, ihB]
  | or _ _ ihA ihB => simp [subst_or, ihA, ihB]
  | imp _ _ ihA ihB => simp [subst_imp, ihA, ihB]

/-- Every substitution instance of a tautology is a tautology. -/
theorem subst_mem_taut {φ : Formula} (hφ : φ ∈ TAUT) (f : ℕ → Formula) : φ.subst f ∈ TAUT :=
  fun σ => (eval_subst_bool f φ σ).trans (hφ _)

/-- Substituting `Proposition.atom` is the identity on formulas. -/
@[simp]
theorem subst_atom (φ : Formula) : φ.subst Proposition.atom = φ := by
  induction φ with
  | atom _ | falsum => rfl
  | and _ _ ihA ihB => simp [subst_and, ihA, ihB]
  | or _ _ ihA ihB => simp [subst_or, ihA, ihB]
  | imp _ _ ihA ihB => simp [subst_imp, ihA, ihB]

/-- Composition law for formula substitutions. -/
theorem subst_subst (f g : ℕ → Formula) (φ : Formula) :
    (φ.subst f).subst g = φ.subst (fun v => (f v).subst g) := by
  induction φ with
  | atom _ | falsum => rfl
  | and _ _ ihA ihB => simp [subst_and, ihA, ihB]
  | or _ _ ihA ihB => simp [subst_or, ihA, ihB]
  | imp _ _ ihA ihB => simp [subst_imp, ihA, ihB]

/-- Rename every atom `v` of a formula to `r v`. -/
@[expose]
def renameAtoms (r : ℕ → ℕ) (φ : Formula) : Formula :=
  φ.subst (fun v => .atom (r v))

/-- Substituting after `renameAtoms r` precomposes the substitution with `r`. -/
theorem subst_renameAtoms (r : ℕ → ℕ) (f : ℕ → Formula) (φ : Formula) :
    (renameAtoms r φ).subst f = φ.subst (fun v => f (r v)) :=
  subst_subst _ f φ

/-- Every atom renaming of a tautology is a tautology (even when `r` is not injective). -/
theorem renameAtoms_mem_taut {φ : Formula} (hφ : φ ∈ TAUT) (r : ℕ → ℕ) :
    renameAtoms r φ ∈ TAUT :=
  subst_mem_taut hφ _

/-- The finite set of propositional atoms occurring in a formula. -/
@[expose]
def formulaAtoms : Formula → Finset ℕ
  | .atom v => {v}
  | .falsum => ∅
  | .and A B | .or A B | .imp A B => formulaAtoms A ∪ formulaAtoms B

/-- Atoms of an atomic formula `atom v`. -/
@[simp] theorem formulaAtoms_atom (v : ℕ) : formulaAtoms (.atom v) = {v} := rfl
/-- `⊥` contains no atoms. -/
@[simp] theorem formulaAtoms_falsum : formulaAtoms .falsum = ∅ := rfl
/-- Atoms of a conjunction `A ∧ B`. -/
@[simp] theorem formulaAtoms_and (A B : Formula) :
    formulaAtoms (.and A B) = formulaAtoms A ∪ formulaAtoms B := rfl
/-- Atoms of a disjunction `A ∨ B`. -/
@[simp] theorem formulaAtoms_or (A B : Formula) :
    formulaAtoms (.or A B) = formulaAtoms A ∪ formulaAtoms B := rfl
/-- Atoms of an implication `A → B`. -/
@[simp] theorem formulaAtoms_imp (A B : Formula) :
    formulaAtoms (.imp A B) = formulaAtoms A ∪ formulaAtoms B := rfl
/-- Boolean constants `boolConst b` contain no atoms. -/
@[simp] theorem formulaAtoms_boolConst (b : Bool) : formulaAtoms (boolConst b) = ∅ := by
  cases b <;> simp [boolConst]

/-- Substitutions agreeing on `formulaAtoms φ` produce identical formulas. -/
theorem subst_congr {f g : ℕ → Formula} {φ : Formula}
    (h : ∀ v ∈ formulaAtoms φ, f v = g v) : φ.subst f = φ.subst g := by
  induction φ with
  | atom v => exact h v (by simp)
  | falsum => rfl
  | and _ _ ihA ihB | or _ _ ihA ihB | imp _ _ ihA ihB =>
    simp [subst_and, subst_or, subst_imp, ihA fun v hv => h v (by simp [hv]),
      ihB fun v hv => h v (by simp [hv])]

/-- Atoms of a substituted formula are the union of `formulaAtoms (f v)` across its atoms. -/
theorem formulaAtoms_subst (f : ℕ → Formula) (φ : Formula) :
    formulaAtoms (φ.subst f) = (formulaAtoms φ).biUnion fun v => formulaAtoms (f v) := by
  induction φ with
  | atom v => simp [subst_var]
  | falsum => simp [subst_falsum]
  | and _ _ ihA ihB | or _ _ ihA ihB | imp _ _ ihA ihB =>
    simp [subst_and, subst_or, subst_imp, ihA, ihB, Finset.union_biUnion]

/-- Boolean evaluation depends only on the assignment to atoms occurring in the formula. -/
theorem eval_congr_atoms {φ : Formula} {σ₁ σ₂ : ℕ → Bool}
    (h : ∀ v ∈ formulaAtoms φ, σ₁ v = σ₂ v) : φ.eval σ₁ = φ.eval σ₂ := by
  induction φ with
  | atom v => exact h v (by simp)
  | falsum => rfl
  | and _ _ ihA ihB | or _ _ ihA ihB | imp _ _ ihA ihB =>
    simp [ihA fun v hv => h v (by simp [hv]), ihB fun v hv => h v (by simp [hv])]

/-- Iterated disjunction `α₁ ∨ ⋯ ∨ αᵣ` of a list of formulas (defaulting to `⊥` on `[]`, and
associating right without an extra trailing `⊥` on nonempty lists). -/
@[expose]
def bigOr : List Formula → Formula
  | [] => .falsum
  | [α] => α
  | α :: β :: rest => .or α (bigOr (β :: rest))

/-- Empty disjunction is `⊥`. -/
@[simp] theorem bigOr_nil : bigOr [] = .falsum := rfl
/-- Singleton disjunction is the formula itself. -/
@[simp] theorem bigOr_singleton (α : Formula) : bigOr [α] = α := rfl
/-- Right-associated cons step of `bigOr` on a list of length at least `2`. -/
@[simp] theorem bigOr_cons_cons (α β : Formula) (rest : List Formula) :
    bigOr (α :: β :: rest) = .or α (bigOr (β :: rest)) := rfl
/-- Unfolding `bigOr (α :: rest)` when `rest ≠ []`. -/
theorem bigOr_cons_of_ne_nil (α : Formula) {rest : List Formula} (h : rest ≠ []) :
    bigOr (α :: rest) = .or α (bigOr rest) := by
  cases rest with | nil => exact absurd rfl h | cons _ _ => rfl

/-- Boolean evaluation of `bigOr αs` holds iff some disjunct in `αs` evaluates to `true`. -/
@[simp]
theorem eval_bigOr_bool (αs : List Formula) (σ : ℕ → Bool) :
    (bigOr αs).eval σ = αs.any (fun α => α.eval σ) := by
  induction αs with
  | nil => rfl
  | cons α rest ih =>
    cases rest with
    | nil => simp
    | cons β tail => simp only [bigOr_cons_cons, Proposition.eval_or_bool, ih, List.any_cons]

/-- Atoms of `bigOr αs` are the union of the atoms of its disjuncts. -/
theorem formulaAtoms_bigOr (αs : List Formula) :
    formulaAtoms (bigOr αs) = αs.foldr (fun α acc => formulaAtoms α ∪ acc) ∅ := by
  induction αs with
  | nil => rfl
  | cons α rest ih => cases rest with | nil => simp | cons _ _ => simp [ih]

/-- Substitution distributes over `bigOr`. -/
theorem subst_bigOr (f : ℕ → Formula) (αs : List Formula) :
    (bigOr αs).subst f = bigOr (αs.map (Proposition.subst f)) := by
  induction αs with
  | nil => rfl
  | cons α rest ih =>
    cases rest with
    | nil => rfl
    | cons β tail => simp only [List.map_cons, bigOr_cons_cons, subst_or, ih]

/-- A list of formulas is **pairwise atom-disjoint** if no two entries share an atom. -/
@[expose] def AreAtomDisjoint (αs : List Formula) : Prop :=
  αs.Pairwise fun α β => Disjoint (formulaAtoms α) (formulaAtoms β)

/-- A pairwise atom-disjoint disjunction is a tautology if and only if at least one of its
disjuncts is a tautology. -/
theorem bigOr_mem_taut_iff_of_areAtomDisjoint {αs : List Formula} (hdisj : AreAtomDisjoint αs) :
    bigOr αs ∈ TAUT ↔ ∃ α ∈ αs, α ∈ TAUT := by
  constructor
  · intro htaut
    by_contra hnone
    have hnone' : ∀ α ∈ αs, α ∉ TAUT := fun α hα hαt => hnone ⟨α, hα, hαt⟩
    have hfalse : ∃ σ : ℕ → Bool, ∀ α ∈ αs, α.eval σ = false := by
      clear htaut hnone
      induction αs with
      | nil => exact ⟨fun _ => false, by simp⟩
      | cons α rest ih =>
        rw [AreAtomDisjoint, List.pairwise_cons] at hdisj
        have hα : ∃ τ : ℕ → Bool, α.eval τ = false := by
          by_contra hall
          exact hnone' α List.mem_cons_self fun τ =>
            Bool.eq_true_of_not_eq_false fun h => hall ⟨τ, h⟩
        obtain ⟨τ, hτ⟩ := hα
        obtain ⟨σ₀, hσ₀⟩ := ih hdisj.2 fun β hβ => hnone' β (List.mem_cons_of_mem _ hβ)
        let σ : ℕ → Bool := fun v => if v ∈ formulaAtoms α then τ v else σ₀ v
        refine ⟨σ, fun β hβ => ?_⟩
        rcases List.mem_cons.1 hβ with rfl | hβ
        · rw [eval_congr_atoms (σ₂ := τ) fun v hv => ite_eq_left hv, hτ]
        · rw [eval_congr_atoms (σ₂ := σ₀) fun v hv =>
            ite_eq_right (Finset.disjoint_right.1 (hdisj.1 β hβ) hv), hσ₀ β hβ]
    obtain ⟨σ, hσ⟩ := hfalse
    have := htaut σ
    simp only [eval_bigOr_bool, List.any_eq_true] at this
    obtain ⟨α, hα, htrue⟩ := this
    exact Bool.false_ne_true ((hσ α hα).symm.trans htrue)
  · rintro ⟨α, hα, htaut⟩ σ
    simp only [eval_bigOr_bool, List.any_eq_true]
    exact ⟨α, hα, htaut σ⟩

/-! ### Reverse-Polish (postfix) binary encoding of propositional formulas -/

/-- Postfix tokens for serializing `Formula`: `.inl v` pushes `atom v`, while `.inr 0, 1, 2, 3`
encode `falsum`, `and`, `or`, and `imp` respectively. -/
abbrev FormTok : Type := ℕ ⊕ Fin 4

/-- Postfix token stream of a propositional formula. -/
@[expose]
def toPostfix : Formula → List FormTok
  | .atom v => [.inl v]
  | .falsum => [.inr 0]
  | .and A B => toPostfix A ++ toPostfix B ++ [.inr 1]
  | .or A B => toPostfix A ++ toPostfix B ++ [.inr 2]
  | .imp A B => toPostfix A ++ toPostfix B ++ [.inr 3]

/-- Postfix token stream of an atomic formula. -/
@[simp] theorem toPostfix_atom (v : ℕ) : toPostfix (.atom v) = [.inl v] := rfl
/-- Postfix token stream of `⊥`. -/
@[simp] theorem toPostfix_falsum : toPostfix .falsum = [.inr 0] := rfl
/-- Postfix token stream of a conjunction `A ∧ B`. -/
@[simp] theorem toPostfix_and (A B : Formula) :
    toPostfix (.and A B) = toPostfix A ++ toPostfix B ++ [.inr 1] := rfl
/-- Postfix token stream of a disjunction `A ∨ B`. -/
@[simp] theorem toPostfix_or (A B : Formula) :
    toPostfix (.or A B) = toPostfix A ++ toPostfix B ++ [.inr 2] := rfl
/-- Postfix token stream of an implication `A → B`. -/
@[simp] theorem toPostfix_imp (A B : Formula) :
    toPostfix (.imp A B) = toPostfix A ++ toPostfix B ++ [.inr 3] := rfl

/-- Single step of the postfix stack decoder for `Formula`. -/
@[expose]
def postfixStep (st : List Formula) : FormTok → List Formula
  | .inl v => .atom v :: st
  | .inr ⟨0, _⟩ => .falsum :: st
  | .inr ⟨1, _⟩ => match st with | B :: A :: rest => .and A B :: rest | _ => st
  | .inr ⟨2, _⟩ => match st with | B :: A :: rest => .or A B :: rest | _ => st
  | .inr ⟨3, _⟩ => match st with | B :: A :: rest => .imp A B :: rest | _ => st

/-- Evaluating `toPostfix φ` on any initial stack `st` pushes `φ` onto `st`. -/
theorem foldl_postfixStep_toPostfix (φ : Formula) :
    ∀ st : List Formula, (toPostfix φ).foldl postfixStep st = φ :: st := by
  induction φ with
  | atom _ | falsum => intro _; rfl
  | and _ _ ihA ihB | or _ _ ihA ihB | imp _ _ ihA ihB =>
    intro st
    simp only [toPostfix, List.foldl_append, ihA, ihB, List.foldl_cons, List.foldl_nil, postfixStep]

/-- Total decoder from postfix token lists to `Formula` (defaulting to `⊥`). -/
def ofPostfix (toks : List FormTok) : Formula :=
  (toks.foldl postfixStep []).headD .falsum

/-- `ofPostfix` left-inverts `toPostfix`. -/
@[simp]
theorem ofPostfix_toPostfix (φ : Formula) : ofPostfix (toPostfix φ) = φ := by
  simp [ofPostfix, foldl_postfixStep_toPostfix]

/-- `toPostfix` is injective. -/
theorem toPostfix_injective : Function.Injective toPostfix :=
  Function.LeftInverse.injective ofPostfix_toPostfix

/-- Binary encoding of a single postfix token `FormTok = ℕ ⊕ Fin 4`. -/
@[expose]
def encFormTok : FormTok ↪ List Bool :=
  encSum encNat (encFinEnum (Fin 4))

/-- Encoding an atom token `.inl v`. -/
@[simp] theorem encFormTok_inl (v : ℕ) :
    encFormTok (.inl v) = encSum encNat (encFinEnum (Fin 4)) (.inl v) := rfl
/-- Encoding a connective token `.inr op`. -/
@[simp] theorem encFormTok_inr (op : Fin 4) :
    encFormTok (.inr op) = encSum encNat (encFinEnum (Fin 4)) (.inr op) := rfl

/-- Total constant-time decoder for `encFinEnum (Fin (k + 1))`. -/
def finEnumDecoder (k : ℕ) : Decoder (encFinEnum (Fin (k + 1))) where
  decode w := ((List.finRange (k + 1)).find? fun i => decide (w = encFinEnum _ i)).getD 0
  decode_enc i := by
    let p : Fin (k + 1) → Bool := fun j => decide (encFinEnum _ i = encFinEnum _ j)
    cases hj : (List.finRange (k + 1)).find? p with
    | none =>
      have := List.find?_eq_none.1 hj i (List.mem_finRange i)
      simp [p] at this
    | some j =>
      have hpj : p j = true := List.find?_some hj
      exact ((encFinEnum (Fin (k + 1))).injective (of_decide_eq_true hpj)).symm
  computable := by
    suffices ∀ l : List (Fin (k + 1)),
        ComputableInPolyTime (fun w : List Bool =>
          (l.find? fun i => decide (w = encFinEnum _ i)).getD 0) encBits
          (encFinEnum (Fin (k + 1))) from (this (List.finRange (k + 1))).exists_degree
    intro l
    induction l with
    | nil => exact const 0
    | cons a ls ih =>
      have h := ite_decide (decide_eq' id' (const (encFinEnum _ a))) (const a) ih
      exact h.of_enc_eq fun w => by
        congr 1; rw [List.find?_cons]
        by_cases hw : w = encFinEnum _ a
        · simp [hw]
        · rw [ite_eq_right hw, decide_eq_false hw]

/-- Total polynomial-time decoder for `encFormTok`. -/
def formTokDecoder : Decoder encFormTok :=
  Decoder.sum Decoder.nat (finEnumDecoder 3)

/-- Canonical binary encoding `encFormula : Formula ↪ List Bool` via framed postfix tokens. -/
@[expose]
def encFormula : Formula ↪ List Bool where
  toFun φ := encList encFormTok (toPostfix φ)
  inj' _ _ h := toPostfix_injective ((encList encFormTok).injective h)

/-- Applying `encFormula` produces the framed list of postfix tokens. -/
theorem encFormula_apply (φ : Formula) : encFormula φ = encList encFormTok (toPostfix φ) := rfl

/-- Postfix tokens of a formula substitution are obtained by flat-mapping atom tokens. -/
theorem toPostfix_subst (f : ℕ → Formula) (φ : Formula) :
    toPostfix (φ.subst f) = (toPostfix φ).flatMap fun
      | .inl v => toPostfix (f v)
      | .inr op => [.inr op] := by
  induction φ with
  | atom v => simp [subst_var]
  | falsum => rfl
  | and _ _ ihA ihB => simp [subst_and, ihA, ihB, List.flatMap_append]
  | or _ _ ihA ihB => simp [subst_or, ihA, ihB, List.flatMap_append]
  | imp _ _ ihA ihB => simp [subst_imp, ihA, ihB, List.flatMap_append]

/-- Postfix tokens of an atom renaming are obtained by mapping `.inl v ↦ .inl (r v)`. -/
theorem toPostfix_renameAtoms (r : ℕ → ℕ) (φ : Formula) :
    toPostfix (renameAtoms r φ) = (toPostfix φ).map fun
      | .inl v => .inl (r v)
      | .inr op => .inr op := by
  rw [renameAtoms, toPostfix_subst]
  induction toPostfix φ with
  | nil => rfl
  | cons t ts ih => cases t <;> simp [List.flatMap_cons, toPostfix, ← ih]

/-- Every formula's binary encoding is nonempty. -/
theorem length_encFormula_pos (φ : Formula) : 1 ≤ (encFormula φ).length := by
  cases φ <;> simp [encFormula_apply, toPostfix, encList_append, encList_cons, length_frame]
  all_goals omega

/-- Encoding of `Proposition.and A B`. -/
theorem encFormula_and (A B : Formula) :
    encFormula (.and A B) = encFormula A ++ encFormula B ++ frame (encFormTok (.inr 1)) := by
  simp [encFormula_apply, toPostfix, encList_append, encList_cons, List.append_assoc]

/-- Encoding of `Proposition.or A B`. -/
theorem encFormula_or (A B : Formula) :
    encFormula (.or A B) = encFormula A ++ encFormula B ++ frame (encFormTok (.inr 2)) := by
  simp [encFormula_apply, toPostfix, encList_append, encList_cons, List.append_assoc]

/-- Encoding of `Proposition.imp A B`. -/
theorem encFormula_imp (A B : Formula) :
    encFormula (.imp A B) = encFormula A ++ encFormula B ++ frame (encFormTok (.inr 3)) := by
  simp [encFormula_apply, toPostfix, encList_append, encList_cons, List.append_assoc]

/-- Converting a formula to its postfix token list is computable in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_toPostfix :
    ComputableInPolyTime toPostfix encFormula (encList encFormTok) :=
  ComputableInPolyTime.of_eq fun _ => rfl

/-- Atomic formulas are constructed in polynomial time from binary atom indices. -/
@[fun_prop]
theorem computableInPolyTime_atom :
    ComputableInPolyTime Proposition.atom encNat encFormula := by
  have h1 : ComputableInPolyTime (fun v : ℕ => [(Sum.inl v : FormTok)]) encNat
      (encList encFormTok) :=
    (ComputableInPolyTime.cons encFormTok).comp
      ((sumInl encNat (encFinEnum (Fin 4))).prod (const []))
  exact h1.of_enc_eq fun _ => rfl

/-- Binary conjunction is computable in polynomial time under `encFormula`. -/
@[fun_prop]
theorem computableInPolyTime_and :
    ComputableInPolyTime (fun p : Formula × Formula => Proposition.and p.1 p.2)
      (encPair encFormula encFormula) encFormula := by
  have hL := computableInPolyTime_toPostfix.comp (fst encFormula encFormula)
  have hR := computableInPolyTime_toPostfix.comp (snd encFormula encFormula)
  have h := (listAppend encFormTok).comp
    (((listAppend encFormTok).comp (hL.prod hR)).prod (const [Sum.inr 1]))
  exact h.of_enc_eq fun _ => rfl

/-- Binary disjunction is computable in polynomial time under `encFormula`. -/
@[fun_prop]
theorem computableInPolyTime_or :
    ComputableInPolyTime (fun p : Formula × Formula => Proposition.or p.1 p.2)
      (encPair encFormula encFormula) encFormula := by
  have hL := computableInPolyTime_toPostfix.comp (fst encFormula encFormula)
  have hR := computableInPolyTime_toPostfix.comp (snd encFormula encFormula)
  have h := (listAppend encFormTok).comp
    (((listAppend encFormTok).comp (hL.prod hR)).prod (const [Sum.inr 2]))
  exact h.of_enc_eq fun _ => rfl

/-- Binary implication is computable in polynomial time under `encFormula`. -/
@[fun_prop]
theorem computableInPolyTime_imp :
    ComputableInPolyTime (fun p : Formula × Formula => Proposition.imp p.1 p.2)
      (encPair encFormula encFormula) encFormula := by
  have hL := computableInPolyTime_toPostfix.comp (fst encFormula encFormula)
  have hR := computableInPolyTime_toPostfix.comp (snd encFormula encFormula)
  have h := (listAppend encFormTok).comp
    (((listAppend encFormTok).comp (hL.prod hR)).prod (const [Sum.inr 3]))
  exact h.of_enc_eq fun _ => rfl

/-- `postfixStep` runs in polynomial time on a stack of formulas and a token. -/
theorem computableInPolyTime_postfixStep :
    ComputableInPolyTime (fun p : List Formula × FormTok => postfixStep p.1 p.2)
      (encPair (encList encFormula) encFormTok) (encList encFormula) := by
  let combine (op : Fin 4) (st : List Formula) : List Formula :=
    if op = 0 then .falsum :: st
    else if decide (2 ≤ st.length) then
      let b := st.headD .falsum
      let a := st.tail.headD .falsum
      let f := if op = 1 then .and a b else if op = 2 then .or a b else .imp a b
      f :: st.tail.tail
    else st
  have heq (st : List Formula) (tok : FormTok) :
      postfixStep st tok = match tok with
        | .inl v => .atom v :: st | .inr op => combine op st := by
    cases tok with
    | inl _ => rfl
    | inr op => fin_cases op <;> (rcases st with _ | ⟨b, _ | ⟨a, rest⟩⟩ <;> rfl)
  simp_rw [heq]
  let E := encPair (encList encFormula) encFormTok
  have hst : ComputableInPolyTime Prod.fst E (encList encFormula) := fst _ _
  have hleft : ComputableInPolyTime (fun p : (List Formula × FormTok) × ℕ =>
      Proposition.atom p.2 :: p.1.1) (encPair E encNat) (encList encFormula) :=
    (ComputableInPolyTime.cons encFormula).comp
      ((computableInPolyTime_atom.comp (snd _ _)).prod (hst.comp (fst _ _)))
  have hright : ComputableInPolyTime (fun p : (List Formula × FormTok) × Fin 4 =>
      combine p.2 p.1.1) (encPair E (encFinEnum (Fin 4))) (encList encFormula) := by
    let ER := encPair E (encFinEnum (Fin 4))
    have hS : ComputableInPolyTime (fun p => p.1.1) ER (encList encFormula) := hst.comp (fst _ _)
    have hO : ComputableInPolyTime Prod.snd ER (encFinEnum (Fin 4)) := snd _ _
    have hb := listGetDWithInput hS (const 0) (Proposition.falsum : Formula)
    have ha := listGetDWithInput hS (const 1) (Proposition.falsum : Formula)
    have hf := ite_decide (decide_eq' hO (const 1)) (computableInPolyTime_and.comp (ha.prod hb))
      (ite_decide (decide_eq' hO (const 2)) (computableInPolyTime_or.comp (ha.prod hb))
        (computableInPolyTime_imp.comp (ha.prod hb)))
    have hres := ite_decide (decide_eq' hO (const 0))
      ((ComputableInPolyTime.cons encFormula).comp
        ((const (Proposition.falsum : Formula)).prod hS))
      (ite_decide (unary_le' (const 2) ((length encFormula).comp hS))
        ((ComputableInPolyTime.cons encFormula).comp (hf.prod (listDropWithInput hS (const 2)))) hS)
    exact hres.of_enc_eq fun ⟨⟨st, _⟩, op⟩ => by
      dsimp only [combine]
      rcases st with _ | ⟨x, _ | ⟨y, zs⟩⟩ <;>
        (fin_cases op <;> simp [List.getD_eq_getElem?_getD, List.headD_eq_head?_getD])
  exact (sumElimWithInput (left := fun (p : List Formula × FormTok) (v : ℕ) => .atom v :: p.1)
    (right := fun (p : List Formula × FormTok) (op : Fin 4) => combine op p.1)
    (snd _ _) hleft hright).of_enc_eq fun p => by cases p.2 <;> rfl

/-- Each `postfixStep` increases the encoded stack length by at most `4 * |encTok| + 30`. -/
theorem length_postfixStep_le (st : List Formula) (tok : FormTok) :
    (encList encFormula (postfixStep st tok)).length ≤
      (encList encFormula st).length + (4 * (encFormTok tok).length + 30) := by
  have hop (k : Fin 4) : (frame (encFormTok (.inr k))).length ≤ 14 := by fin_cases k <;> decide
  cases tok with
  | inl v =>
    simp only [postfixStep, encList_cons, List.length_append, length_frame, encFormula_apply,
      toPostfix, encList_nil, List.append_nil]; omega
  | inr op =>
    fin_cases op
    · have h0 := hop 0; rw [length_frame] at h0
      simp only [postfixStep, encList_cons, List.length_append, length_frame, encFormula_apply,
        toPostfix, encList_nil, List.append_nil]; omega
    · have h1 := hop 1; rw [length_frame] at h1
      rcases st with _ | ⟨B, _ | ⟨A, rest⟩⟩ <;>
        (simp only [postfixStep, encList_cons, List.length_append, length_frame, encFormula_and]
         omega)
    · have h2 := hop 2; rw [length_frame] at h2
      rcases st with _ | ⟨B, _ | ⟨A, rest⟩⟩ <;>
        (simp only [postfixStep, encList_cons, List.length_append, length_frame, encFormula_or]
         omega)
    · have h3 := hop 3; rw [length_frame] at h3
      rcases st with _ | ⟨B, _ | ⟨A, rest⟩⟩ <;>
        (simp only [postfixStep, encList_cons, List.length_append, length_frame, encFormula_imp]
         omega)

/-- `ofPostfix` is computable in polynomial time from framed postfix token lists. -/
@[fun_prop]
theorem computableInPolyTime_ofPostfix :
    ComputableInPolyTime ofPostfix (encList encFormTok) encFormula := by
  have hmem_len {toks : List FormTok} {t : FormTok} (ht : t ∈ toks) :
      (encFormTok t).length ≤ (encList encFormTok toks).length := by
    induction toks with
    | nil => cases ht
    | cons x xs ih =>
      simp only [encList_cons, List.length_append, length_frame]
      rcases List.mem_cons.1 ht with rfl | h
      · omega
      · have := ih h; omega
  have hfold : ComputableInPolyTime
      (fun toks : List FormTok => toks.foldl postfixStep [])
      (encList encFormTok) (encList encFormula) :=
    foldlWithInput_of_bounded_growth (encIn := encList encFormTok) (encA := encFormTok)
      (encL := encList encFormTok) (encB := encList encFormula)
      (list := id) (init := fun _ => []) (step := fun _ st tok => postfixStep st tok)
      (const []) ⟨id', computableInPolyTime_postfixStep.comp
        (((snd _ _).comp (fst _ _)).prod (snd _ _)), inferInstance, inferInstance⟩
      (growth := fun toks => 4 * (encList encFormTok toks).length + 30)
      ⟨by
        have : PolyBounded (fun toks : List FormTok => (encList encFormTok toks).length)
            (fun toks => (encList encFormTok toks).length) := PolyBounded.self
        exact ((this.mul (.const 4)).add (.const 30)).mono fun _ => le_of_eq (by ring),
       fun toks st tok htok => (length_postfixStep_le st tok).trans
        (Nat.add_le_add_left (Nat.add_le_add_right (Nat.mul_le_mul_left 4 (hmem_len htok)) 30) _)⟩
  have hhd := listGetDWithInput hfold (const 0) (Proposition.falsum : Formula)
  exact hhd.of_enc_eq fun toks => by
    dsimp only [ofPostfix]
    cases toks.foldl postfixStep [] <;> simp [List.getD_eq_getElem?_getD, List.headD_eq_head?_getD]

/-- Total polynomial-time decoder for `encFormula`. -/
def formulaDecoder : Decoder encFormula where
  decode w := ofPostfix ((Decoder.list formTokDecoder).decode w)
  decode_enc φ := by
    change ofPostfix ((Decoder.list formTokDecoder).decode (encList encFormTok (toPostfix φ))) = φ
    rw [(Decoder.list formTokDecoder).decode_enc, ofPostfix_toPostfix]
  computable := by
    obtain ⟨_, _, hD⟩ := (Decoder.list formTokDecoder).computable
    exact (computableInPolyTime_ofPostfix.comp hD.computableInPolyTime).exists_degree

/-- `bigOr` is computable in polynomial time from a framed list of formulas. -/
@[fun_prop]
theorem computableInPolyTime_bigOr :
    ComputableInPolyTime bigOr (encList encFormula) encFormula := by
  let step (acc : Option Formula) (α : Formula) : Option Formula :=
    match acc with
    | none => some α
    | some β => some (.or α β)
  have hfold_eq : ∀ l : List Formula,
      (l.reverse.foldl step none).getD .falsum = bigOr l := by
    intro l
    induction l with
    | nil => rfl
    | cons α rest ih =>
      cases rest with
      | nil => rfl
      | cons β tail =>
        have hne : ∃ ψ, (β :: tail).reverse.foldl step none = some ψ := by
          suffices ∀ (xs : List Formula) (init : Formula),
              ∃ ψ, xs.foldl step (some init) = some ψ by
            rcases hrev : (β :: tail).reverse with _ | ⟨hd, tl⟩
            · exact absurd (congrArg List.length hrev) (by simp)
            · simpa only [List.foldl_cons, step] using this tl hd
          intro xs
          induction xs with
          | nil => exact fun init => ⟨init, rfl⟩
          | cons x xs ihx => exact fun init => ihx (.or x init)
        obtain ⟨ψ, hψ⟩ := hne
        rw [hψ, Option.getD_some] at ih
        have hcons : (α :: β :: tail).reverse = (β :: tail).reverse ++ [α] := List.reverse_cons
        rw [hcons, List.foldl_append, hψ, List.foldl_cons, List.foldl_nil]
        dsimp only [step, Option.getD_some, bigOr]
        rw [ih]
  have hstep : ComputableInPolyTime
      (fun p : (List Formula × Option Formula) × Formula => step p.1.2 p.2)
      (encPair (encPair (encList encFormula) (encOption encFormula)) encFormula)
      (encOption encFormula) := by
    let E := encPair (encPair (encList encFormula) (encOption encFormula)) encFormula
    have hacc : ComputableInPolyTime (fun p => p.1.2) E (encOption encFormula) :=
      (snd _ _).comp (fst _ _)
    have hα : ComputableInPolyTime Prod.snd E encFormula := snd _ _
    have hcomb := optionElimWithInput
      (body := fun (p : (List Formula × Option Formula) × Formula) (β : Formula) =>
        some (Proposition.or p.2 β))
      hacc ((optionSome encFormula).comp hα)
      ((optionSome encFormula).comp
        (computableInPolyTime_or.comp ((hα.comp (fst _ _)).prod (snd _ _))))
    exact hcomb.of_enc_eq fun p => by cases p.1.2 <;> rfl
  have hmem_len {l : List Formula} {α : Formula} (hα : α ∈ l) :
      (encFormula α).length ≤ (encList encFormula l).length := by
    induction l with
    | nil => cases hα
    | cons _ _ ih =>
      simp only [encList_cons, List.length_append, length_frame]
      rcases List.mem_cons.1 hα with rfl | h
      · omega
      · have := ih h; omega
  have hfold : ComputableInPolyTime (fun l : List Formula => l.reverse.foldl step none)
      (encList encFormula) (encOption encFormula) :=
    foldlWithInput_of_bounded_growth (encIn := encList encFormula) (encA := encFormula)
      (encL := encList encFormula) (encB := encOption encFormula)
      (list := List.reverse) (init := fun _ => none) (step := fun _ acc α => step acc α)
      (const none) ⟨listReverse encFormula, hstep, inferInstance, inferInstance⟩
      (growth := fun l => (encList encFormula l).length + 20)
      ⟨PolyBounded.self.add (.const 20),
       fun l acc α hα => by
        have hlen := hmem_len (List.mem_reverse.1 hα)
        have hop2 : (frame (encFormTok (.inr 2))).length ≤ 14 := by decide
        cases acc with
        | none =>
          change (true :: encFormula α).length ≤ ([] : List Bool).length + _
          simp only [List.length_cons, List.length_nil]; omega
        | some β =>
          change (true :: encFormula (.or α β)).length ≤ (true :: encFormula β).length + _
          simp only [List.length_cons, encFormula_or, List.length_append]; omega⟩
  simpa only [funext hfold_eq] using
    optionGetDWithInput hfold (const (Proposition.falsum : Formula))

/-- Shifting atoms downward by `v ↦ v - base` is computable in polynomial time (with `base` in
binary). -/
theorem computableInPolyTime_shiftDown :
    ComputableInPolyTime (fun p : ℕ × Formula => renameAtoms (· - p.1) p.2)
      (encPair encNat encFormula) encFormula := by
  let E := encPair encNat encFormula
  have htoks := computableInPolyTime_toPostfix.comp (snd encNat encFormula)
  have hmap : ComputableInPolyTime
      (fun p : ℕ × Formula => (toPostfix p.2).map fun
        | .inl v => (Sum.inl (v - p.1) : FormTok)
        | .inr op => Sum.inr op) E (encList encFormTok) := by
    refine mapWithInput htoks ?_
    let EM := encPair E encFormTok
    have hcomb := sumElimWithInput (eg := EM)
      (left := fun (q : (ℕ × Formula) × FormTok) (v : ℕ) => (Sum.inl (v - q.1.1) : FormTok))
      (right := fun (_ : (ℕ × Formula) × FormTok) (op : Fin 4) => (Sum.inr op : FormTok))
      (snd E encFormTok)
      ((sumInl encNat (encFinEnum (Fin 4))).comp
        (binary_sub.comp ((snd EM encNat).prod
          ((fst encNat encFormula).comp (fst E encFormTok |>.comp (fst EM encNat))))))
      ((sumInr encNat (encFinEnum (Fin 4))).comp (snd EM (encFinEnum (Fin 4))))
    exact hcomb.of_enc_eq fun q => by cases q.2 <;> rfl
  exact hmap.of_enc_eq fun p => by simp [encFormula_apply, toPostfix_renameAtoms]

/-- Finite substitution specified by an association list `pairs : List (ℕ × Formula)` (leaving
unlisted atoms unchanged). -/
@[expose]
def listSubst (pairs : List (ℕ × Formula)) (v : ℕ) : Formula :=
  match pairs.find? (fun kv => kv.1 == v) with
  | some (_, ψ) => ψ
  | none => .atom v

/-- Lookup miss in `listSubst` leaves atom `v` unchanged. -/
theorem listSubst_of_find?_eq_none {pairs : List (ℕ × Formula)} {v : ℕ}
    (h : pairs.find? (fun kv => kv.1 == v) = none) : listSubst pairs v = .atom v := by
  dsimp only [listSubst]; rw [h]

/-- Lookup hit in `listSubst` returns the associated formula. -/
theorem listSubst_of_find?_eq_some {pairs : List (ℕ × Formula)} {v : ℕ} {kv : ℕ × Formula}
    (h : pairs.find? (fun kv => kv.1 == v) = some kv) : listSubst pairs v = kv.2 := by
  dsimp only [listSubst]; rw [h]

/-- Skipping a prefix with no matching key in `listSubst`. -/
theorem listSubst_append_of_find?_eq_none {p₁ p₂ : List (ℕ × Formula)} {v : ℕ}
    (h : p₁.find? (fun kv => kv.1 == v) = none) :
    listSubst (p₁ ++ p₂) v = listSubst p₂ v := by
  dsimp only [listSubst]; rw [List.find?_append, h, Option.none_or]

/-- Applying a finite substitution `listSubst pairs` to `φ` runs in polynomial time. -/
theorem computableInPolyTime_listSubst :
    ComputableInPolyTime (fun p : List (ℕ × Formula) × Formula => p.2.subst (listSubst p.1))
      (encPair (encList (encPair encNat encFormula)) encFormula) encFormula := by
  let encKV := encPair encNat encFormula
  let E := encPair (encList encKV) encFormula
  have hlookup : ComputableInPolyTime (fun q : List (ℕ × Formula) × ℕ => listSubst q.1 q.2)
      (encPair (encList encKV) encNat) encFormula := by
    let EL := encPair (encList encKV) encNat
    have hfind : ComputableInPolyTime
        (fun q : List (ℕ × Formula) × ℕ => q.1.find? (fun kv => kv.1 == q.2))
        EL (encOption encKV) :=
      findWithInput (fst _ _)
        (ComputableInPolyTime.beq ((fst _ _).comp (snd _ _)) ((snd _ _).comp (fst _ _)))
    have hcomb := optionElimWithInput
      (body := fun (_ : List (ℕ × Formula) × ℕ) (kv : ℕ × Formula) => kv.2)
      hfind (computableInPolyTime_atom.comp (snd _ _)) ((snd _ _).comp (snd _ _))
    exact hcomb.of_enc_eq fun q => by dsimp only [listSubst]; cases q.1.find? _ <;> rfl
  have hflat : ComputableInPolyTime
      (fun p : List (ℕ × Formula) × Formula => (toPostfix p.2).flatMap fun
        | .inl v => toPostfix (listSubst p.1 v)
        | .inr op => [Sum.inr op]) E (encList encFormTok) := by
    refine flatMapWithInput
      (computableInPolyTime_toPostfix.comp (snd (encList encKV) encFormula)) ?_
    let EM := encPair E encFormTok
    have hcomb := sumElimWithInput (eg := EM)
      (left := fun (q : (List (ℕ × Formula) × Formula) × FormTok) (v : ℕ) =>
        toPostfix (listSubst q.1.1 v))
      (right := fun (_ : (List (ℕ × Formula) × Formula) × FormTok) (op : Fin 4) =>
        [(Sum.inr op : FormTok)])
      (snd E encFormTok)
      (computableInPolyTime_toPostfix.comp
        (hlookup.comp ((((fst (encList encKV) encFormula).comp
          ((fst E encFormTok).comp (fst EM encNat)))).prod (snd EM encNat))))
      ((ComputableInPolyTime.cons encFormTok).comp
        (((sumInr encNat (encFinEnum (Fin 4))).comp (snd EM (encFinEnum (Fin 4)))).prod
          (const [])))
    exact hcomb.of_enc_eq fun q => by cases q.2 <;> rfl
  exact hflat.of_enc_eq fun p => by simp [encFormula_apply, toPostfix_subst]

/-- `TAUT` belongs to `coNP encFormula`. -/
theorem taut_mem_coNP : TAUT ∈ coNP encFormula := by
  rw [mem_coNP]
  let atomsList (φ : Formula) : List ℕ :=
    (toPostfix φ).flatMap fun | .inl v => [v] | .inr _ => []
  have hmem_atoms (φ : Formula) (v : ℕ) : v ∈ formulaAtoms φ ↔ v ∈ atomsList φ := by
    dsimp only [atomsList]
    induction φ <;> simp [toPostfix, List.flatMap_append, *]
  have hlen_atoms (φ : Formula) : (atomsList φ).length ≤ (encFormula φ).length := by
    rw [encFormula_apply]; dsimp only [atomsList]
    induction toPostfix φ with
    | nil => simp
    | cons t ts ih =>
      cases t <;> simp only [List.flatMap_cons, encList_cons, List.length_append,
        List.length_cons, List.length_nil, length_frame] <;> omega
  let evalStep (al : List ℕ) (w st : List Bool) : FormTok → List Bool
    | .inl v => w.getD (al.idxOf v) false :: st
    | .inr ⟨0, _⟩ => false :: st
    | .inr ⟨1, _⟩ => match st with | b :: a :: r => (a && b) :: r | _ => st
    | .inr ⟨2, _⟩ => match st with | b :: a :: r => (a || b) :: r | _ => st
    | .inr ⟨3, _⟩ => match st with | b :: a :: r => (!a || b) :: r | _ => st
  have heval_fold (al : List ℕ) (w : List Bool) (φ : Formula) :
      ∀ st, (toPostfix φ).foldl (evalStep al w) st =
        φ.eval (fun v => w.getD (al.idxOf v) false) :: st := by
    induction φ <;> intro st <;> simp only [toPostfix, List.foldl_append, *, List.foldl_cons,
      List.foldl_nil, evalStep, Proposition.eval_and_bool, Proposition.eval_or_bool,
      Proposition.eval_imp_bool] <;> rfl
  let V (p : Formula × List Bool) : Bool :=
    !(((toPostfix p.1).foldl (evalStep (atomsList p.1) p.2) []).headD true)
  have hal_poly : ComputableInPolyTime atomsList encFormula (encList encNat) := by
    refine flatMapWithInput computableInPolyTime_toPostfix ?_
    let EA := encPair encFormula encFormTok
    exact (sumElimWithInput (eg := EA) (ea := encNat) (eb := encFinEnum (Fin 4))
      (left := fun (_ : Formula × FormTok) (v : ℕ) => [v])
      (right := fun (_ : Formula × FormTok) (_ : Fin 4) => ([] : List ℕ))
      (snd encFormula encFormTok)
      ((ComputableInPolyTime.cons encNat).comp ((snd EA encNat).prod (const [])))
      (const [])).of_enc_eq fun q => by cases q.2 <;> rfl
  have hV : ComputableInPolyTime V (encPair encFormula encBits) encBool := by
    let EV := encPair encFormula encBits
    let ES := encPair (encPair EV encBits) encFormTok
    let opStep (st : List Bool) (op : Fin 4) : List Bool :=
      if op = 0 then false :: st
      else if decide (2 ≤ st.length) then
        (if op = 1 then st.tail.headD false && st.headD false
         else if op = 2 then st.tail.headD false || st.headD false
         else !st.tail.headD false || st.headD false) :: st.tail.tail
      else st
    have hstep : ComputableInPolyTime
        (fun q : ((Formula × List Bool) × List Bool) × FormTok =>
          evalStep (atomsList q.1.1.1) q.1.1.2 q.1.2 q.2) ES encBits := by
      have hstep_eq' (q : ((Formula × List Bool) × List Bool) × FormTok) :
          evalStep (atomsList q.1.1.1) q.1.1.2 q.1.2 q.2 = match q.2 with
            | .inl v => q.1.1.2.getD ((atomsList q.1.1.1).idxOf v) false :: q.1.2
            | .inr op => opStep q.1.2 op := by
        cases q.2 with
        | inl _ => rfl
        | inr op => fin_cases op <;> (rcases q.1.2 with _ | ⟨b, _ | ⟨a, r⟩⟩ <;> rfl)
      rw [show (fun q : ((Formula × List Bool) × List Bool) × FormTok =>
        evalStep (atomsList q.1.1.1) q.1.1.2 q.1.2 q.2) = _ from funext hstep_eq']
      have hst : ComputableInPolyTime (fun q => q.1.2) ES encBits := (snd _ _).comp (fst _ _)
      have hleft : ComputableInPolyTime
          (fun r : (((Formula × List Bool) × List Bool) × FormTok) × ℕ =>
            r.1.1.1.2.getD ((atomsList r.1.1.1.1).idxOf r.2) false :: r.1.1.2)
          (encPair ES encNat) encBits := by
        let ELN := encPair ES encNat
        have hp : ComputableInPolyTime (fun r => r.1.1.1) ELN EV :=
          (fst EV encBits).comp ((fst (encPair EV encBits) encFormTok).comp (fst ES encNat))
        have hbit := bitsGetDWithInput ((snd encFormula encBits).comp hp)
          (idxOfWithInput (hal_poly.comp ((fst encFormula encBits).comp hp)) (snd ES encNat)) false
        exact (bitsAppend (hbit.of_enc_eq fun _ => rfl) (hst.comp (fst ES encNat))).of_enc_eq
          fun _ => rfl
      have hright : ComputableInPolyTime
          (fun r : (((Formula × List Bool) × List Bool) × FormTok) × Fin 4 =>
            opStep r.1.1.2 r.2) (encPair ES (encFinEnum (Fin 4))) encBits := by
        let ER := encPair ES (encFinEnum (Fin 4))
        have hS : ComputableInPolyTime (fun r => r.1.1.2) ER encBits := hst.comp (fst _ _)
        have hO : ComputableInPolyTime Prod.snd ER (encFinEnum (Fin 4)) := snd _ _
        have hb := bitsGetDWithInput hS (const 0) false
        have ha := bitsGetDWithInput hS (const 1) false
        have hval := ite_decide (decide_eq' hO (const 1)) (bool_and' ha hb)
          (ite_decide (decide_eq' hO (const 2)) (bool_or' ha hb)
            (bool_or' (bool_not.comp ha) hb))
        have hres := ite_decide (decide_eq' hO (const 0)) (bitsAppend (const [false]) hS)
          (ite_decide (unary_le' (const 2) (length_bits.comp hS))
            (bitsAppend (hval.of_enc_eq fun _ => rfl) (bitsDropWithInput hS (const 2))) hS)
        exact hres.of_enc_eq fun ⟨⟨⟨_, st⟩, _⟩, op⟩ => by
          rcases st with _ | ⟨x, _ | ⟨y, zs⟩⟩ <;> (fin_cases op <;> rfl)
      exact (sumElimWithInput
        (left := fun (q : ((Formula × List Bool) × List Bool) × FormTok) (v : ℕ) =>
          q.1.1.2.getD ((atomsList q.1.1.1).idxOf v) false :: q.1.2)
        (right := fun (q : ((Formula × List Bool) × List Bool) × FormTok) (op : Fin 4) =>
          opStep q.1.2 op) (snd _ _) hleft hright).of_enc_eq fun q => by cases q.2 <;> rfl
    have hfold : ComputableInPolyTime
        (fun p : Formula × List Bool => (toPostfix p.1).foldl (evalStep (atomsList p.1) p.2) [])
        EV encBits :=
      foldlWithInput_of_bounded_growth (encIn := EV) (encA := encFormTok)
        (encL := encList encFormTok) (encB := encBits)
        (list := fun p => toPostfix p.1) (init := fun _ => [])
        (step := fun p st t => evalStep (atomsList p.1) p.2 st t)
        (const []) ⟨computableInPolyTime_toPostfix.comp (fst _ _), hstep,
          inferInstance, inferInstance⟩
        (growth := fun _ => 1) ⟨.const 1, fun p st t _ => by
          cases t with
          | inl _ => simp [evalStep]
          | inr op => fin_cases op <;> (rcases st with _ | ⟨b, _ | ⟨a, r⟩⟩ <;> simp [evalStep])⟩
    have hhd := bitsGetDWithInput hfold (const 0) true
    exact (bool_not.comp hhd).of_enc_eq fun p => by
      dsimp only [V, Function.comp_apply, encBool]
      cases (toPostfix p.1).foldl (evalStep (atomsList p.1) p.2) [] <;> rfl
  refine ⟨Polynomial.X, V, hV, fun φ => ⟨fun hnot => ?_, fun ⟨w, _, hw⟩ => ?_⟩⟩
  · simp only [TAUT, Set.mem_compl_iff, Set.mem_ofPred_eq, not_forall, Bool.not_eq_true] at hnot
    obtain ⟨σ, hσ⟩ := hnot
    let al := atomsList φ
    let w := al.map σ ++ List.replicate ((encFormula φ).length - al.length) false
    have hw_len : w.length = (encFormula φ).length := by
      have : al.length ≤ (encFormula φ).length := hlen_atoms φ
      simp only [w, List.length_append, List.length_map, List.length_replicate]; omega
    refine ⟨w, by simpa using hw_len, ?_⟩
    simp only [V, heval_fold, List.headD_cons, Bool.not_eq_true']
    refine (eval_congr_atoms fun v hv => ?_).trans hσ
    have hmem : v ∈ al := (hmem_atoms φ v).1 hv
    have hlt : al.idxOf v < al.length := List.idxOf_lt_length_of_mem hmem
    have hlt' : al.idxOf v < (al.map σ).length := by simpa using hlt
    have hltw : al.idxOf v < w.length := by rw [hw_len]; exact lt_of_lt_of_le hlt (hlen_atoms φ)
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hltw, Option.getD_some,
      List.getElem_append_left hlt', List.getElem_map, List.getElem_idxOf hlt]
  · simp only [V, heval_fold, List.headD_cons, Bool.not_eq_true'] at hw
    exact fun htaut => Bool.false_ne_true (hw.symm.trans (htaut _))

/-! ### Cook–Reckhow propositional proof systems, lengths of proofs, and FDP -/

/-- A **Cook–Reckhow propositional proof system** (pps): a polynomial-time surjection from binary
words `List Bool` onto `TAUT`, reusing `Cslib.Complexity.ProofSystem encFormula TAUT`. -/
abbrev PropProofSystem : Type := ProofSystem encFormula TAUT

/-- The class of Cook–Reckhow propositional proof systems is nonempty (for instance, the
exhaustive truth-table proof system). -/
theorem nonempty_propProofSystem : Nonempty PropProofSystem :=
  ProofSystem.nonempty_of_mem_coNP formulaDecoder taut_mem_coNP ⟨_, verum_mem_taut⟩

/-- The **lengths-of-proofs function** `s_P(φ) := min { |π| | P(π) = φ }`. -/
noncomputable def proofLength (P : PropProofSystem) (φ : Formula) : ℕ :=
  sInf {k : ℕ | ∃ π : List Bool, P π = φ ∧ π.length = k}

/-- Every tautology `φ ∈ TAUT` has a `P`-proof of exact length `proofLength P φ`. -/
theorem exists_proof_of_proofLength (P : PropProofSystem) {φ : Formula} (hφ : φ ∈ TAUT) :
    ∃ π : List Bool, P π = φ ∧ π.length = proofLength P φ := by
  obtain ⟨π, hπ⟩ := P.exists_eq hφ
  exact Nat.sInf_mem (s := {k : ℕ | ∃ π : List Bool, P π = φ ∧ π.length = k}) ⟨π.length, π, hπ, rfl⟩

/-- Every `P`-proof `π` of `φ` bounds `proofLength P φ ≤ π.length`. -/
theorem proofLength_le (P : PropProofSystem) {π : List Bool} {φ : Formula} (hπ : P π = φ) :
    proofLength P φ ≤ π.length :=
  Nat.sInf_le ⟨π, hπ, rfl⟩

/-- `proofLength P φ ≤ s` for `φ ∈ TAUT` iff `φ` has a `P`-proof of length at most `s`. -/
theorem proofLength_le_iff (P : PropProofSystem) {φ : Formula} (hφ : φ ∈ TAUT) {s : ℕ} :
    proofLength P φ ≤ s ↔ ∃ π : List Bool, P π = φ ∧ π.length ≤ s := by
  refine ⟨fun h => ?_, fun ⟨π, hπ, hlen⟩ => (proofLength_le P hπ).trans hlen⟩
  obtain ⟨π, hπ, hlen⟩ := exists_proof_of_proofLength P hφ
  exact ⟨π, hπ, hlen ▸ h⟩

/-- Simulation `P.Simulates Q` bounds `s_P(φ) ≤ p(s_Q(φ))` for a fixed polynomial `p` and every
tautology `φ ∈ TAUT`. -/
theorem simulates_iff_proofLength {P Q : PropProofSystem} :
    P.Simulates Q ↔ ∃ p : Polynomial ℕ, ∀ φ ∈ TAUT, proofLength P φ ≤ p.eval (proofLength Q φ) := by
  constructor
  · rintro ⟨p, hp⟩
    refine ⟨p, fun φ hφ => ?_⟩
    obtain ⟨π, hπ, hlen⟩ := exists_proof_of_proofLength Q hφ
    obtain ⟨π', hπ', hlen'⟩ := hp π
    exact (proofLength_le P (hπ'.trans hπ)).trans (hlen ▸ hlen')
  · rintro ⟨p, hp⟩
    refine ⟨p, fun π => ?_⟩
    have hmem : Q π ∈ TAUT := Q.mem π
    obtain ⟨π', hπ', hlen'⟩ := (proofLength_le_iff P hmem).1
      ((hp (Q π) hmem).trans (p.eval_mono (proofLength_le Q rfl)))
    exact ⟨π', hπ', hlen'⟩

/-- The **feasible disjunction property** (fdp, binary case `r = 2`): there exists a constant
`c ≥ 1` such that whenever `α₁ ∨ α₂` (with `α₁, α₂` sharing no atoms) admits a `P`-proof of
size `s`, either `α₁` or `α₂` admits a `P`-proof of size at most `s ^ c`. -/
@[expose] def HasFDP (P : PropProofSystem) : Prop :=
  ∃ c : ℕ, 1 ≤ c ∧ ∀ (α₁ α₂ : Formula) (π : List Bool),
    Disjoint (formulaAtoms α₁) (formulaAtoms α₂) →
    P π = .or α₁ α₂ →
    ∃ π' : List Bool, (P π' = α₁ ∨ P π' = α₂) ∧ π'.length ≤ π.length ^ c

/-- The **strong feasible disjunction property** (strong fdp, arbitrary number `r ≥ 1` of
disjuncts): there exists a constant `c ≥ 1` such that whenever a pairwise atom-disjoint
disjunction `⋁_{1 ≤ i ≤ r} αᵢ` admits a `P`-proof of size `s`, some `αᵢ` admits a `P`-proof of
size at most `s ^ c`. -/
@[expose] def HasStrongFDP (P : PropProofSystem) : Prop :=
  ∃ c : ℕ, 1 ≤ c ∧ ∀ (αs : List Formula) (π : List Bool),
    αs ≠ [] → AreAtomDisjoint αs → P π = bigOr αs →
    ∃ α ∈ αs, ∃ π' : List Bool, P π' = α ∧ π'.length ≤ π.length ^ c

/-- Polynomial-bound formulation of the strong feasible disjunction property (allowing an additive
constant in `p(s)` to accommodate proofs of size `0` or `1`). -/
@[expose] def HasStrongFDPPoly (P : PropProofSystem) : Prop :=
  ∃ p : Polynomial ℕ, ∀ (αs : List Formula) (π : List Bool),
    αs ≠ [] → AreAtomDisjoint αs → P π = bigOr αs →
    ∃ α ∈ αs, ∃ π' : List Bool, P π' = α ∧ π'.length ≤ p.eval π.length

/-- The strong feasible disjunction property implies the binary feasible disjunction property. -/
theorem HasStrongFDP.hasFDP {P : PropProofSystem} (h : HasStrongFDP P) : HasFDP P := by
  obtain ⟨c, hc, hfdp⟩ := h
  refine ⟨c, hc, fun α₁ α₂ π hdisj hπ => ?_⟩
  have had : AreAtomDisjoint [α₁, α₂] := by simp [AreAtomDisjoint, hdisj]
  obtain ⟨α, hmem, π', hπ', hlen⟩ := hfdp [α₁, α₂] π (by simp) had hπ
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl
  · exact ⟨π', Or.inl hπ', hlen⟩
  · exact ⟨π', Or.inr hπ', hlen⟩

/-- `HasStrongFDP P` implies `HasStrongFDPPoly P` (with `p = X ^ c`). -/
theorem HasStrongFDP.toPoly {P : PropProofSystem} (h : HasStrongFDP P) : HasStrongFDPPoly P := by
  obtain ⟨c, -, hfdp⟩ := h
  exact ⟨Polynomial.X ^ c, fun αs π hne had hπ => by simpa using hfdp αs π hne had hπ⟩

/-! ### Propositional proof systems with advice and universal one-bit-advice simulation -/

/-- A **propositional proof system with `k(n)` bits of advice** (`pps/k(n)`):
a polynomial-time map `toFun : List Bool × List Bool → Formula` paired with an advice function
`advice : ℕ → List Bool` of length `|advice n| = k n` such that `π ↦ toFun (π, advice |π|)` has
range exactly `TAUT`. -/
structure PropProofSystemWithAdvice (k : ℕ → ℕ) where
  /-- The underlying polynomial-time proof evaluation map taking `(proof, advice)`. -/
  toFun : List Bool × List Bool → Formula
  /-- The non-uniform advice string supplied for each proof length `n`. -/
  advice : ℕ → List Bool
  /-- `toFun` is computable in polynomial time. -/
  computable : ComputableInPolyTime toFun (encPair encBits encBits) encFormula
  /-- On inputs of length `n`, the advice string has exact length `k n`. -/
  length_advice : ∀ n, (advice n).length = k n
  /-- The range of `π ↦ toFun (π, advice |π|)` is exactly `TAUT`. -/
  range_eq : Set.range (fun π => toFun (π, advice π.length)) = TAUT

/-- Evaluate a propositional proof system with advice on a proof word `π`. -/
@[expose]
def PropProofSystemWithAdvice.eval {k : ℕ → ℕ} (P : PropProofSystemWithAdvice k)
    (π : List Bool) : Formula :=
  P.toFun (π, P.advice π.length)

/-- Soundness of a propositional proof system with advice: every proof evaluates to a tautology. -/
theorem PropProofSystemWithAdvice.mem_taut {k : ℕ → ℕ} (P : PropProofSystemWithAdvice k)
    (π : List Bool) : P.eval π ∈ TAUT :=
  P.range_eq.subset ⟨π, rfl⟩

/-- Completeness of a propositional proof system with advice: every tautology admits a proof. -/
theorem PropProofSystemWithAdvice.exists_proof {k : ℕ → ℕ} (P : PropProofSystemWithAdvice k)
    {φ : Formula} (hφ : φ ∈ TAUT) : ∃ π : List Bool, P.eval π = φ :=
  P.range_eq.symm.subset hφ

/-- Lengths-of-proofs function `s_P(φ)` for a propositional proof system with advice. -/
noncomputable def PropProofSystemWithAdvice.proofLength {k : ℕ → ℕ}
    (P : PropProofSystemWithAdvice k) (φ : Formula) : ℕ :=
  sInf {s : ℕ | ∃ π : List Bool, P.eval π = φ ∧ π.length = s}

/-- Upper bound on `P.proofLength φ` from any proof `π` with `P.eval π = φ`. -/
theorem PropProofSystemWithAdvice.proofLength_le {k : ℕ → ℕ}
    (P : PropProofSystemWithAdvice k) {π : List Bool} {φ : Formula} (hπ : P.eval π = φ) :
    P.proofLength φ ≤ π.length :=
  Nat.sInf_le ⟨π, hπ, rfl⟩

/-- Characterization of `P.proofLength φ ≤ t` for tautologies, and soundness: any formula (even
without assuming `φ ∈ TAUT`) satisfying `P.proofLength φ ≤ t` when `∃ π, P.eval π = φ ∧ |π| ≤ t`
is a tautology. Specifically, `HasProofOfLengthLE P φ t` is `∃ π, P.eval π = φ ∧ π.length ≤ t`,
which coincides with `P.proofLength φ ≤ t` on `TAUT`. -/
theorem PropProofSystemWithAdvice.proofLength_le_iff {k : ℕ → ℕ}
    (P : PropProofSystemWithAdvice k) {φ : Formula} (hφ : φ ∈ TAUT) {t : ℕ} :
    P.proofLength φ ≤ t ↔ ∃ π : List Bool, P.eval π = φ ∧ π.length ≤ t := by
  refine ⟨fun h => ?_, fun ⟨π, hπ, hlen⟩ => (P.proofLength_le hπ).trans hlen⟩
  obtain ⟨π₀, hπ₀⟩ := P.exists_proof hφ
  obtain ⟨π, hπ, hlen⟩ := Nat.sInf_mem (s := {s | ∃ π, P.eval π = φ ∧ π.length = s})
    ⟨π₀.length, π₀, hπ₀, rfl⟩
  exact ⟨π, hπ, hlen ▸ h⟩

/-- A propositional proof system with advice `P` **p-simulates** a classical Cook–Reckhow pps `Q`
if some uniform polynomial-time function `f : List Bool → List Bool` satisfies `P(f(π)) = Q(π)`
for every proof `π`. -/
@[expose]
def PropProofSystemWithAdvice.PSimulates {k : ℕ → ℕ} (P : PropProofSystemWithAdvice k)
    (Q : PropProofSystem) : Prop :=
  ∃ f : List Bool → List Bool, ComputableInPolyTime f encBits encBits ∧
    ∀ π : List Bool, P.eval (f π) = Q π

/-- A propositional proof system with advice `P` **simulates** a classical Cook–Reckhow pps `Q` if
for some polynomial `p`, every `Q`-proof `π` admits a `P`-proof of the same tautology of length
at most `p |π|`. -/
@[expose]
def PropProofSystemWithAdvice.Simulates {k : ℕ → ℕ} (P : PropProofSystemWithAdvice k)
    (Q : PropProofSystem) : Prop :=
  ∃ p : Polynomial ℕ, ∀ π : List Bool, ∃ π' : List Bool,
    P.eval π' = Q π ∧ π'.length ≤ p.eval π.length

/-- P-simulation implies polynomial-size simulation for proof systems with advice. -/
theorem PropProofSystemWithAdvice.PSimulates.simulates {k : ℕ → ℕ}
    {P : PropProofSystemWithAdvice k} {Q : PropProofSystem} (h : P.PSimulates Q) :
    P.Simulates Q := by
  obtain ⟨f, hf, hPQ⟩ := h
  obtain ⟨c, d, hle⟩ := hf.polyBounded_length.exists_le
  exact ⟨.C c * (.X + 1) ^ d, fun π => ⟨f π, hPQ π, by simpa using hle π⟩⟩

/-- Unary integer square root is computable in polynomial time. -/
private theorem computableInPolyTime_unary_sqrt :
    ComputableInPolyTime Nat.sqrt encUnary encUnary := by
  have hstep : ∀ (k a : ℕ), a ≤ k →
      ((List.range (k + 1)).filter fun s => decide (s ≤ a)) = List.range (a + 1) := by
    intro k
    induction k with
    | zero => intro a ha; cases Nat.eq_zero_of_le_zero ha; rfl
    | succ k ihk =>
      intro a ha
      rw [List.range_succ, List.filter_append, List.filter_singleton]
      by_cases hka : a = k + 1
      · subst hka
        rw [List.filter_eq_self.2 fun s hs => by simp [Nat.le_of_lt (List.mem_range.1 hs)]]
        simp [List.range_succ]
      · simp [show ¬(k + 1 ≤ a) by omega, ihk a (by omega)]
  have heq (n : ℕ) : Nat.sqrt n =
      ((List.range (n + 1)).filter fun s => decide (s * s ≤ n)).length - 1 := by
    have hfilt : ((List.range (n + 1)).filter fun s => decide (s * s ≤ n)) =
        List.range (Nat.sqrt n + 1) :=
      (List.filter_congr fun s _ => by simp [Nat.le_sqrt]).trans (hstep n _ (Nat.sqrt_le_self n))
    rw [hfilt, List.length_range, Nat.add_sub_cancel]
  rw [show Nat.sqrt = fun n =>
    ((List.range (n + 1)).filter fun s => decide (s * s ≤ n)).length - 1 from funext heq]
  have hr : ComputableInPolyTime (fun n : ℕ => List.range (n + 1)) encUnary (encList encUnary) :=
    range.comp (by fun_prop)
  have hf : ComputableInPolyTime
      (fun n : ℕ => (List.range (n + 1)).filter fun s => decide (s * s ≤ n))
      encUnary (encList encUnary) :=
    filterWithInput hr
      (unary_le' (unary_mul' (snd encUnary encUnary) (snd encUnary encUnary))
        (fst encUnary encUnary))
  exact unary_sub' ((length encUnary).comp hf) (const 1)

/-- Cantor unpairing `Nat.unpair` is computable in polynomial time in unary. -/
private theorem computableInPolyTime_unary_unpair :
    ComputableInPolyTime Nat.unpair encUnary (encPair encUnary encUnary) := by
  have heq (n : ℕ) : Nat.unpair n =
      let s := Nat.sqrt n
      if decide (n - s * s < s) then (n - s * s, s) else (s, n - s * s - s) := by
    simp [Nat.unpair]
  rw [show Nat.unpair = _ from funext heq]
  have hs := computableInPolyTime_unary_sqrt
  have hd : ComputableInPolyTime (fun n : ℕ => n - Nat.sqrt n * Nat.sqrt n) encUnary encUnary :=
    unary_sub' id' (unary_mul' hs hs)
  exact ite_decide (unary_lt' hd hs) (hd.prod hs) (hs.prod (unary_sub' hd hs))

/-- Injection of bitstrings into `ℕ` by appending a sentinel `true` bit (little-endian). -/
private def wordToNat (w : List Bool) : ℕ :=
  (w ++ [true]).foldr Nat.bit 0

/-- Inverse of `wordToNat`: drop the trailing sentinel `true` from `encNat e`. -/
private def natToWord (e : ℕ) : List Bool :=
  (encNat e).dropLast

private theorem natToWord_wordToNat (w : List Bool) : natToWord (wordToNat w) = w := by
  have h : ∀ l : List Bool, ((l ++ [true]).foldr Nat.bit 0).bits = l ++ [true] ∧
      (l ++ [true]).foldr Nat.bit 0 ≠ 0 := by
    intro l
    induction l with
    | nil => decide
    | cons b bs ih =>
      simp only [List.cons_append, List.foldr_cons]
      have hne : Nat.bit b (List.foldr Nat.bit 0 (bs ++ [true])) ≠ 0 := by
        have := ih.2; cases b <;> (simp only [Nat.bit, Bool.cond_true, Bool.cond_false]; omega)
      exact ⟨by rw [Nat.bits_append_bit _ b fun h0 => (ih.2 h0).elim, ih.1], hne⟩
  have henc : encNat (wordToNat w) = w ++ [true] := (h w).1
  simp [natToWord, henc]

private theorem computableInPolyTime_natToWord :
    ComputableInPolyTime natToWord encUnary encBits := by
  have hbin : ComputableInPolyTime (fun e : ℕ => (encNat e : List Bool)) encUnary encBits :=
    unary_to_binary.of_enc_eq fun _ => rfl
  have heq (e : ℕ) : natToWord e = (encNat e).take ((encNat e).length - 1) :=
    List.dropLast_eq_take
  rw [show natToWord = _ from funext heq]
  exact bitsTakeWithInput hbin (unary_sub' (length_bits.comp hbin) (const 1))

/-- Unpack a proof length `n = Nat.pair e (Nat.pair t m)` into `(d, t, m)`. -/
private def ckUnpack (n : ℕ) : Universal.Desc × ℕ × ℕ :=
  let er := Nat.unpair n
  let tm := Nat.unpair er.2
  (Universal.decodeDesc (natToWord er.1), tm.1, tm.2)

/-- Simulate the clocked universal machine decoded from `π.length` on the prefix of `π`. -/
private def ckRunAt (π : List Bool) : Formula :=
  let p := ckUnpack π.length
  match Universal.runWord p.1 (π.take p.2.2) p.2.1 with
  | some o => formulaDecoder.decode o
  | none => .imp .falsum .falsum

/-- **Universal one-bit-advice propositional proof system.** There exists a propositional proof
system `P` with `1` bit of advice that uniformly p-simulates every classical Cook–Reckhow
propositional proof system `Q`. -/
theorem exists_pps_one_bit_advice_pSimulates_all :
    ∃ P : PropProofSystemWithAdvice (fun _ => 1), ∀ Q : PropProofSystem, P.PSimulates Q := by
  classical
  let advBit (n : ℕ) : Bool :=
    decide (∀ w : BitString (ckUnpack n).2.2,
      match Universal.runWord (ckUnpack n).1 (List.ofFn w) (ckUnpack n).2.1 with
      | some o => formulaDecoder.decode o ∈ TAUT
      | none => False)
  let toFun (pa : List Bool × List Bool) : Formula :=
    if pa.2.headD false then ckRunAt pa.1 else .imp .falsum .falsum
  have htoFun : ComputableInPolyTime toFun (encPair encBits encBits) encFormula := by
    let E := encPair encBits encBits
    have hπ : ComputableInPolyTime Prod.fst E encBits := fst _ _
    have hadv : ComputableInPolyTime Prod.snd E encBits := snd _ _
    have hn : ComputableInPolyTime (fun pa : List Bool × List Bool => pa.1.length) E encUnary :=
      length_bits.comp hπ
    have her := computableInPolyTime_unary_unpair.comp hn
    have htm := computableInPolyTime_unary_unpair.comp her.snd'
    have hd : ComputableInPolyTime (fun pa : List Bool × List Bool => (ckUnpack pa.1.length).1)
        E Universal.eDesc :=
      Universal.computableInPolyTime_decodeDesc.comp (computableInPolyTime_natToWord.comp her.fst')
    have ht : ComputableInPolyTime (fun pa : List Bool × List Bool => (ckUnpack pa.1.length).2.1)
        E encUnary := htm.fst'
    have hm : ComputableInPolyTime (fun pa : List Bool × List Bool => (ckUnpack pa.1.length).2.2)
        E encUnary := htm.snd'
    have hrun := Universal.computableInPolyTime_runWord hd (bitsTakeWithInput hπ hm) ht
    obtain ⟨_, _, hdec⟩ := formulaDecoder.computable
    have hrunAt : ComputableInPolyTime (fun pa : List Bool × List Bool => ckRunAt pa.1)
        E encFormula := by
      have hcomb := optionElimWithInput
        (body := fun (_ : List Bool × List Bool) (o : List Bool) => formulaDecoder.decode o)
        hrun (const (Proposition.imp .falsum .falsum : Formula))
        (hdec.computableInPolyTime.comp (snd _ _))
      exact hcomb.of_enc_eq fun pa => by dsimp only [ckRunAt]; cases Universal.runWord _ _ _ <;> rfl
    have hcond : ComputableInPolyTime (fun pa : List Bool × List Bool => pa.2.headD false)
        E encBool :=
      (bitsGetDWithInput hadv (const 0) false).of_enc_eq fun pa => by cases pa.2 <;> rfl
    exact ite_decide hcond hrunAt (const (Proposition.imp .falsum .falsum : Formula))
  have hsim : ∀ Q : PropProofSystem, ∃ f : List Bool → List Bool,
      ComputableInPolyTime f encBits encBits ∧
      ∀ π₀ : List Bool, toFun (f π₀, [advBit (f π₀).length]) = Q π₀ := by
    intro Q
    have hQbits : ComputableInPolyTime (fun π₀ => encFormula (Q π₀)) encBits encBits :=
      Q.computable.of_enc_eq fun _ => rfl
    obtain ⟨tQ, _, htQ, -, _, State, _, tm, htm⟩ := hQbits
    have := Fintype.ofFinite State
    let eS : State ↪ ℕ := (Fintype.equivFin State).toEmbedding.trans Fin.valEmbedding
    let d : Universal.Desc := Universal.desc eS Universal.eBit tm
    let e : ℕ := wordToNat (Universal.eDesc d)
    have hd_dec : Universal.decodeDesc (natToWord e) = d := by
      rw [natToWord_wordToNat, Universal.decodeDesc_eDesc]
    obtain ⟨c, deg, ht_le⟩ := polynomiallyBounded_iff_le.1 htQ
    let budget (m : ℕ) : ℕ := c * (m + 1) ^ deg
    let targetLen (m : ℕ) : ℕ := Nat.pair e (Nat.pair (budget m) m)
    have hm_le (m : ℕ) : m ≤ targetLen m :=
      (Nat.right_le_pair (budget m) m).trans (Nat.right_le_pair e _)
    let f (π₀ : List Bool) : List Bool :=
      π₀ ++ List.replicate (targetLen π₀.length - π₀.length) false
    have hf_len (π₀ : List Bool) : (f π₀).length = targetLen π₀.length := by
      have := hm_le π₀.length; simp [f]; omega
    have hf_poly : ComputableInPolyTime f encBits encBits := by
      have hm : ComputableInPolyTime List.length encBits encUnary := length_bits
      have hb : ComputableInPolyTime (fun π₀ : List Bool => budget π₀.length) encBits encUnary := by
        dsimp only [budget]; fun_prop
      have hp1 : ComputableInPolyTime
          (fun π₀ : List Bool => Nat.pair (budget π₀.length) π₀.length) encBits encUnary :=
        ite_decide (unary_lt' hb hm)
          (unary_add' (unary_mul' hm hm) hb)
          (unary_add' (unary_add' (unary_mul' hb hb) hb) hm)
      have htl : ComputableInPolyTime (fun π₀ : List Bool => targetLen π₀.length)
          encBits encUnary :=
        ite_decide (unary_lt' (const e) hp1)
          (unary_add' (unary_mul' hp1 hp1) (const e))
          (unary_add' (unary_add' (unary_mul' (const e) (const e)) (const e)) hp1)
      exact bitsAppend id' ((bitsReplicate false).comp (unary_sub' htl hm))
    have hrun_eq (w : List Bool) :
        Universal.runWord d w (budget w.length) = some (encFormula (Q w)) := by
      obtain ⟨⟨u, hhalt_u, hout_u⟩, htime, -⟩ := htm w
      have hhalt_t : (tm.runFrom (tm.initCfg w) (tQ w.length)).Halted :=
        runsInTime_iff_halted.1 htime
      have heq_cfg : tm.runFrom (tm.initCfg w) (tQ w.length) = tm.runFrom (tm.initCfg w) u :=
        (le_total (tQ w.length) u).elim (fun h => (runFrom_eq_of_halt tm _ h hhalt_t).symm)
          (fun h => runFrom_eq_of_halt tm _ h hhalt_u)
      have hres := Universal.runWord_desc_of_halted eS tm hhalt_t (ht_le w.length)
      have hout' : (tm.runFrom (tm.initCfg w) u).output = encFormula (Q w) := hout_u
      rwa [heq_cfg, hout'] at hres
    refine ⟨f, hf_poly, fun π₀ => ?_⟩
    set m := π₀.length
    have hunpack : ckUnpack (targetLen m) = (d, budget m, m) := by
      simp [ckUnpack, targetLen, Nat.unpair_pair, hd_dec]
    have hadv_true : advBit (targetLen m) = true := by
      dsimp only [advBit]; rw [hunpack]; simp only [decide_eq_true_eq]; intro w
      have hrunw := hrun_eq (List.ofFn w)
      rw [List.length_ofFn] at hrunw; rw [hrunw]; dsimp only
      rw [formulaDecoder.decode_enc]; exact Q.mem (List.ofFn w)
    change (if advBit (f π₀).length = true then ckRunAt (f π₀) else .imp .falsum .falsum) = Q π₀
    rw [hf_len, hadv_true]; simp only [ite_true]; unfold ckRunAt
    rw [hf_len, hunpack]; dsimp only
    rw [show (f π₀).take m = π₀ by simp [f, m], hrun_eq π₀]
    exact formulaDecoder.decode_enc (Q π₀)
  refine ⟨⟨toFun, fun n => [advBit n], htoFun, fun _ => rfl, ?_⟩, hsim⟩
  refine Set.Subset.antisymm ?_ fun φ hφ => ?_
  · rintro _ ⟨π, rfl⟩
    change (if advBit π.length = true then ckRunAt π else .imp .falsum .falsum) ∈ TAUT
    by_cases h : advBit π.length = true
    · rw [ite_eq_left h]
      have hm_le : (ckUnpack π.length).2.2 ≤ π.length :=
        (Nat.unpair_right_le _).trans (Nat.unpair_right_le π.length)
      let w : BitString (ckUnpack π.length).2.2 := fun i => π[i.val]'(by omega)
      have hw : List.ofFn w = π.take (ckUnpack π.length).2.2 :=
        List.ext_getElem (by simp [hm_le]) fun i _ _ => by simp [w]
      have hspec := (of_decide_eq_true h : ∀ w : BitString (ckUnpack π.length).2.2, _) w
      rw [hw] at hspec; unfold ckRunAt; dsimp only
      cases hres : Universal.runWord (ckUnpack π.length).1 (π.take (ckUnpack π.length).2.2)
          (ckUnpack π.length).2.1 with
      | none => rw [hres] at hspec; exact hspec.elim
      | some o => rwa [hres] at hspec
    · rw [ite_eq_right h]; exact verum_mem_taut
  · obtain ⟨Q₀⟩ := nonempty_propProofSystem
    obtain ⟨f, -, hf⟩ := hsim Q₀
    obtain ⟨π₀, rfl⟩ := Q₀.exists_eq hφ
    exact ⟨f π₀, hf π₀⟩

/-- **Nondeterministic circuits for short proofs in a proof system with `1` bit of advice.** For
every `P : PropProofSystemWithAdvice (fun _ => 1)`, there exist constants `C, d : ℕ` (depending
only on `P`) such that whenever a family of formulas `φ : BitString m → Formula` has fixed encoded
length `L` computed by an input-and-constant substitution `ρ : Fin L → Fin m ⊕ Bool`
(`∀ a, encFormula (φ a) = List.ofFn (substitute ρ a)`), and `t : ℕ` is any proof-length bound, the
set `S = {a : BitString m | ∃ π, P.eval π = φ a ∧ π.length ≤ t}` is nondeterministically decided
by a De Morgan circuit `D` of size at most `C * (L + t + 1) ^ d`, and every `a ∈ S` satisfies
`φ a ∈ TAUT`. -/
theorem exists_nondetCircuit_adviceProofLength_le (P : PropProofSystemWithAdvice (fun _ => 1)) :
    ∃ C d : ℕ, ∀ {m k L : ℕ} (φ : BitString m → Formula) (ext : BitString m → BitString k)
      (ρ : Fin L → Fin k ⊕ Bool),
      (∀ a : BitString m, encFormula (φ a) = List.ofFn (substitute ρ (ext a))) →
      ∀ t : ℕ, ∃ D : Circuit signature (k + t) 1,
        D.size ≤ C * (L + t + 1) ^ d ∧
        (∀ (a : BitString m), (∃ π : List Bool, P.eval π = φ a ∧ π.length ≤ t) ↔
          ∃ w : BitString t, D.eval interpretation (Fin.append (ext a) w) 0 = true) ∧
        ∀ a : BitString m, (∃ π : List Bool, P.eval π = φ a ∧ π.length ≤ t) → φ a ∈ TAUT := by
  classical
  let check (x : List Bool × (List Bool × List Bool)) : Bool :=
    decide (encFormula (P.toFun x.2) = x.1)
  have hcheck : ComputableInPolyTime check
      (encPair encBits (encPair encBits encBits)) encBool :=
    decide_eq' ((P.computable.comp (snd _ _)).of_enc_eq fun _ => rfl) (fst _ _)
  obtain ⟨Lcheck, hLpoly, hLiff⟩ := PPoly.exists_of_polyTime hcheck
  obtain ⟨c₀, d₀, hsz⟩ := polynomiallyBounded_iff_le.1 (mem_PPoly.1 hLpoly)
  refine ⟨(c₀ + 4) * 6 ^ d₀, d₀ + 1, fun {m k L} φ ext ρ hρ t => ?_⟩
  let testLen (ℓ : Fin (t + 1)) : BooleanFunction (k + t) := fun aw =>
    let a : BitString k := fun i => aw (Fin.castAdd t i)
    let π : List Bool := List.ofFn fun i : Fin ℓ.val =>
      aw (Fin.natAdd k ⟨i.val, by omega⟩)
    check (List.ofFn (substitute ρ a), (π, P.advice ℓ.val))
  have htest_syn (ℓ : Fin (t + 1)) :
      Synthesis interpretation (inputs (k + t)) {testLen ℓ}
        (c₀ * (2 * L + 2 * t + 6) ^ d₀ + 2) := by
    set Nℓ := 2 * L + 1 + (2 * ℓ.val + 1 + 1)
    let wire : Fin Nℓ → Fin (k + t) ⊕ Bool := fun j =>
      if h1 : j.val < 2 * L then
        if j.val % 2 = 0 then .inr true
        else (ρ ⟨j.val / 2, by omega⟩).map (Fin.castAdd t) id
      else if j.val = 2 * L then .inr false
      else
        let r := j.val - (2 * L + 1)
        if h2 : r < 2 * ℓ.val then
          if r % 2 = 0 then .inr true
          else .inl (Fin.natAdd k ⟨r / 2, by omega⟩)
        else if r = 2 * ℓ.val then .inr false
        else .inr ((P.advice ℓ.val).getD 0 false)
    have hwire (aw : BitString (k + t)) :
        List.ofFn (substitute wire aw) =
          encPair encBits (encPair encBits encBits)
            (List.ofFn (substitute ρ fun i => aw (Fin.castAdd t i)),
             (List.ofFn (fun i : Fin ℓ.val => aw (Fin.natAdd k ⟨i.val, by omega⟩)),
              P.advice ℓ.val)) := by
      have hadv1 : (P.advice ℓ.val).length = 1 := P.length_advice ℓ.val
      refine List.ext_getElem (by simp [encPair_apply, length_frame, hadv1, Nℓ]; omega)
        fun j h₁ h₂ => ?_
      simp only [List.length_ofFn] at h₁
      rw [List.getElem_ofFn]
      simp only [encPair_apply, encBits_apply]
      by_cases hj1 : j < 2 * L + 1
      · rw [List.getElem_append_left (by simp [length_frame]; omega), getElem_frame]
        by_cases hj1' : j < 2 * L
        · simp only [wire, substitute, hj1', dite_true, List.length_ofFn]
          split_ifs
          · rfl
          · simp only [List.getElem_ofFn, substitute]
            cases ρ ⟨j / 2, by omega⟩ <;> rfl
        · have hjeq : j = 2 * L := by omega
          subst hjeq
          simp [wire, substitute]
      · rw [List.getElem_append_right (by simp [length_frame]; omega)]
        simp only [length_frame, List.length_ofFn]
        set r := j - (2 * L + 1)
        by_cases hj2 : r < 2 * ℓ.val + 1
        · rw [List.getElem_append_left (by simp [length_frame]; omega), getElem_frame]
          by_cases hj2' : r < 2 * ℓ.val
          · simp only [wire, substitute, show ¬(j < 2 * L) by omega,
              show j ≠ 2 * L by omega, dite_false, ite_false, r, hj2', dite_true,
              List.length_ofFn]
            split_ifs <;> simp
          · have hreq : r = 2 * ℓ.val := by omega
            simp [wire, substitute, show ¬(j < 2 * L) by omega, show j ≠ 2 * L by omega, r, hreq]
        · rw [List.getElem_append_right (by simp [length_frame]; omega)]
          have h0 : j - (2 * L + 1) - (2 * ℓ.val + 1) = 0 := by omega
          have hnr : ¬(j - (2 * L + 1) < 2 * ℓ.val) := by omega
          have hne : j - (2 * L + 1) ≠ 2 * ℓ.val := by omega
          simp only [wire, substitute, show ¬(j < 2 * L) by omega, show j ≠ 2 * L by omega,
            hnr, hne, dite_false, ite_false, length_frame, List.length_ofFn, h0, Sum.elim_inr,
            id_eq]
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
    have heq_fn : testLen ℓ = fun aw => Lcheck.slice Nℓ (substitute wire aw) := by
      funext aw
      rw [Bool.eq_iff_iff, Language.slice_eq_true_iff, hwire, ← hLiff]
    have hcomp_le : complexity interpretation (single (testLen ℓ)) ≤
        c₀ * (2 * L + 2 * t + 6) ^ d₀ + 2 := by
      rw [heq_fn]
      refine (complexity_substitute_le wire (Lcheck.slice Nℓ)).trans (Nat.add_le_add_right ?_ 2)
      refine (hsz Nℓ).trans (Nat.mul_le_mul_left c₀ (Nat.pow_le_pow_left (by omega) d₀))
    obtain ⟨c, hc, hcsz⟩ := complexity_le_iff.1 hcomp_le
    exact (Synthesis.circuit (I := interpretation) (s := inputs (k + t)) c (fun i x => x i)
      (fun i => ⟨i, rfl⟩)).mono Set.Subset.rfl
      (Set.singleton_subset_iff.2 ⟨0, funext fun x => congrFun (hc x) 0⟩) hcsz
  obtain ⟨anyFn, hany_iff, hany_syn⟩ := Synthesis.exists_exists_mem (s := inputs (k + t))
    (univ : Finset (Fin (t + 1))) testLen (m := t + 1) (by simp)
    (fun ℓ _ => htest_syn ℓ)
  obtain ⟨D, hD, hDsz⟩ := hany_syn.exists_circuit
  refine ⟨D, ?_, fun a => ?_, fun _ ⟨π, hπ, _⟩ => hπ ▸ P.mem_taut π⟩
  · have hbound : (t + 1) * (c₀ * (2 * L + 2 * t + 6) ^ d₀ + 2 + 1) + 1 ≤
        (c₀ + 4) * 6 ^ d₀ * (L + t + 1) ^ (d₀ + 1) := by
      have h6 : 2 * L + 2 * t + 6 ≤ 6 * (L + t + 1) := by omega
      have hpow : (2 * L + 2 * t + 6) ^ d₀ ≤ 6 ^ d₀ * (L + t + 1) ^ d₀ :=
        (Nat.pow_le_pow_left h6 d₀).trans_eq (Nat.mul_pow 6 (L + t + 1) d₀)
      set P := 6 ^ d₀ * (L + t + 1) ^ d₀
      have h1d : 1 ≤ P :=
        Nat.mul_pos (Nat.pow_pos (by decide)) (Nat.pow_pos (by omega))
      calc (t + 1) * (c₀ * (2 * L + 2 * t + 6) ^ d₀ + 3) + 1
          ≤ (t + 1) * ((c₀ + 3) * P) + P :=
            Nat.add_le_add (Nat.mul_le_mul_left _ (by nlinarith)) h1d
        _ ≤ (L + t + 1) * ((c₀ + 3) * P) + (L + t + 1) * P :=
            Nat.add_le_add (Nat.mul_le_mul_right _ (by omega))
              (Nat.le_mul_of_pos_left P (by omega))
        _ = (c₀ + 4) * 6 ^ d₀ * (L + t + 1) ^ (d₀ + 1) := by dsimp only [P]; rw [pow_succ]; ring
    exact hDsz.trans hbound
  · constructor
    · rintro ⟨π, hπ, hlen⟩
      let w : BitString t := fun i => π.getD i.val false
      refine ⟨w, (congrFun (hD (Fin.append (ext a) w)) 0).trans ?_⟩
      simp only [single_apply]
      refine (hany_iff _).2 ⟨⟨π.length, Nat.lt_succ_of_le hlen⟩, mem_univ _, ?_⟩
      have hπ_eq : (List.ofFn fun i : Fin π.length =>
          Fin.append (ext a) w (Fin.natAdd k ⟨i.val, by omega⟩)) = π :=
        List.ext_getElem (by simp) fun i _ h₂ => by
          rw [List.getElem_ofFn, Fin.append_right]
          simp only [w, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h₂, Option.getD_some]
      have ha_eq : (fun i => Fin.append (ext a) w (Fin.castAdd t i)) = ext a := by funext i; simp
      simp only [testLen, check, ha_eq, hπ_eq, ← hρ a, decide_eq_true_eq]
      exact congrArg encFormula hπ
    · rintro ⟨w, hw⟩
      have htrue := (congrFun (hD (Fin.append (ext a) w)) 0).symm.trans hw
      obtain ⟨ℓ, -, hℓ⟩ := (hany_iff _).1 htrue
      have ha_eq : (fun i => Fin.append (ext a) w (Fin.castAdd t i)) = ext a := by funext i; simp
      simp only [testLen, check, ha_eq, ← hρ a, decide_eq_true_eq] at hℓ
      let π := List.ofFn fun i : Fin ℓ.val => w ⟨i.val, by omega⟩
      have hπ_eq : (List.ofFn fun i : Fin ℓ.val =>
          Fin.append (ext a) w (Fin.natAdd k ⟨i.val, by omega⟩)) = π := by
        simp only [π, Fin.append_right]
      rw [hπ_eq] at hℓ
      exact ⟨π, encFormula.injective (by simpa [PropProofSystemWithAdvice.eval, π] using hℓ),
        by simp [π]; omega⟩

end CslibFrontier.ProofComplexity
