/-
Copyright (c) 2026 FormalPapers contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FormalPapers contributors
-/
module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.ExistsReal
public import CslibFrontier.Computability.Complexity.Classes.Inclusions
public import CslibFrontier.Computability.Complexity.CookLevin.Completeness

import CslibFrontier.Logics.RealArithmetic.FormulaWordValidation
import CslibFrontier.Logics.RealArithmetic.TermTokenDecoding
import CslibFrontier.Computability.Complexity.Problems.SAT.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Sum
import Mathlib.Tactic.Linarith

/-!
# Universal Real Complexity Classes and Shor's Inclusion (`NP ⊆ ∃ℝ`)

Upstream `cslib-frontier` candidate establishing the universal real complexity classes `ForallReal`
(`∀ℝ`) and `ForallExistsReal` (`∀∃ℝ`), `∃ℝ`-completeness of `ETR` (`∀ℝ`-completeness of `ETRᶜ`),
Shor's inclusion `NP ⊆ ∃ℝ` (`SAT ≤_p ETR`), `coNP ⊆ ∀ℝ`, and `P ⊆ ∃ℝ ∩ ∀ℝ`.
-/

public section

namespace Cslib.Complexity

open Cslib.Logic.PL Cslib.Logic.RealArithmetic
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime

/-- The universal complexity class over the reals `∀ℝ` (`co-∃ℝ`), consisting of problems whose
complement lies in `ExistsReal enc`. -/
@[expose]
def ForallReal {α : Type} (enc : α ↪ List Bool) : Set (Set α) :=
  {L | Lᶜ ∈ ExistsReal enc}

/-- The universal–existential real complexity class `∀∃ℝ` (`co-∃∀ℝ`), consisting of problems whose
complement lies in `ExistsForallReal enc`. -/
@[expose]
def ForallExistsReal {α : Type} (enc : α ↪ List Bool) : Set (Set α) :=
  {L | Lᶜ ∈ ExistsForallReal enc}

/-- Membership in `ForallReal enc` is equivalent to polynomial-time many-one reducibility to
`ETRᶜ`. -/
theorem mem_ForallReal_iff {α : Type} {enc : α ↪ List Bool} {L : Set α} :
    L ∈ ForallReal enc ↔ PolyTimeReducible enc encBits L ETRᶜ :=
  ⟨fun h ↦ compl_compl L ▸ PolyTimeReducible.compl h,
   fun h ↦ (compl_compl ETR ▸ h.compl : PolyTimeReducible enc encBits Lᶜ ETR)⟩

/-- Complement involution between `ExistsReal` and `ForallReal`. -/
theorem compl_mem_ForallReal_iff {α : Type} {enc : α ↪ List Bool} {L : Set α} :
    Lᶜ ∈ ForallReal enc ↔ L ∈ ExistsReal enc := by
  simp [ForallReal]

/-- `ExistsReal` is closed downward under polynomial-time many-one reductions. -/
theorem PolyTimeReducible.mem_ExistsReal {α β : Type} {encA : α ↪ List Bool}
    {encB : β ↪ List Bool} {A : Set α} {B : Set β}
    (hred : PolyTimeReducible encA encB A B) (hB : B ∈ ExistsReal encB) :
    A ∈ ExistsReal encA :=
  hred.trans hB

/-- `ForallReal` is closed downward under polynomial-time many-one reductions. -/
theorem PolyTimeReducible.mem_ForallReal {α β : Type} {encA : α ↪ List Bool}
    {encB : β ↪ List Bool} {A : Set α} {B : Set β}
    (hred : PolyTimeReducible encA encB A B) (hB : B ∈ ForallReal encB) :
    A ∈ ForallReal encA :=
  hred.compl.trans hB

/-- **`ETR` is `∃ℝ`-complete** under polynomial-time many-one reductions. -/
theorem ETR_complete : PolyTimeComplete ExistsReal encBits ETR :=
  ⟨PolyTimeReducible.refl encBits ETR, fun _ _ _ h ↦ h⟩

/-- **`ETRᶜ` is `∀ℝ`-complete** under polynomial-time many-one reductions. -/
theorem compl_ETR_complete : PolyTimeComplete ForallReal encBits ETRᶜ :=
  ⟨compl_mem_ForallReal_iff.mpr (PolyTimeReducible.refl encBits ETR),
   fun _ _ _ h ↦ mem_ForallReal_iff.mp h⟩

private def cnfLiteralFormula (n : ℕ) (vars : List ℕ) (lit : Literal ℕ) : Formula n :=
  let idx := vars.idxOf lit.1
  if h : idx < n then
    if lit.2 then .eqZero (.add (.var ⟨idx, h⟩) (.const (-1))) else .eqZero (.var ⟨idx, h⟩)
  else .false

private def cnfClauseFormula (n : ℕ) (vars : List ℕ) : Clause ℕ → Formula n
  | [] => .false
  | l :: ls => .or (cnfLiteralFormula n vars l) (cnfClauseFormula n vars ls)

private def cnfToRealFormulaAux (n : ℕ) (vars : List ℕ) : CNF ℕ → Formula n
  | [] => .not .false
  | c :: cs => .and (cnfClauseFormula n vars c) (cnfToRealFormulaAux n vars cs)

private def cnfToRealFormula (φ : CNF ℕ) : Formula φ.vars.length :=
  cnfToRealFormulaAux φ.vars.length φ.vars φ

private def litTermWord (idx : ℕ) (pol : Bool) : List Bool :=
  if pol then encList encTermToken [.inr (.inr (.inl ())), .inr (.inl idx), .inl (-1)]
  else encList encTermToken [.inr (.inl idx)]

private def litFormulaTokens (vars : List ℕ) (lit : Literal ℕ) : List FormulaToken :=
  [.inr (.inr (.inr (.inr (.inr ())))), .inr (.inl (litTermWord (vars.idxOf lit.1) lit.2))]

private def clauseFormulaTokens (vars : List ℕ) (c : Clause ℕ) : List FormulaToken :=
  c.flatMap (litFormulaTokens vars) ++ [.inl ()]

private def cnfFormulaTokens (φ : CNF ℕ) : List FormulaToken :=
  φ.flatMap (fun c ↦ (.inr (.inr (.inr (.inr (.inl ())))) : FormulaToken) ::
    clauseFormulaTokens φ.vars c) ++ [.inr (.inr (.inr (.inl ()))), .inl ()]

private theorem encFormula_eq_encList_tokens {n : ℕ} (p : Formula n) :
    encFormula n p =
      encList encFormulaToken ((encFormula_tokens n p).map FormulaToken.encodeTerms) :=
  ((formulaTokensDecoder.decode_eq_some_iff _ _).mp (formulaTokensDecoder_decode_encFormula p)).symm

private theorem encTerm_eq_encList_tokens {n : ℕ} (t : Term n) :
    encTerm n t = encList encTermToken ((encTerm_tokens n t).map TermToken.ofFin) :=
  ((termTokensDecoder.decode_eq_some_iff _ _).mp (termTokensDecoder_decode_encTerm t)).symm

private theorem map_encodeTerms_cnfLiteral {n : ℕ} {vars : List ℕ} {lit : Literal ℕ}
    (hidx : vars.idxOf lit.1 < n) :
    (encFormula_tokens n (cnfLiteralFormula n vars lit)).map FormulaToken.encodeTerms =
      [.inr (.inl (litTermWord (vars.idxOf lit.1) lit.2))] := by
  unfold cnfLiteralFormula litTermWord
  simp only [hidx, ↓reduceDIte]
  cases lit.2 <;>
    simp [encFormula_tokens, FormulaToken.encodeTerms, encTerm_eq_encList_tokens,
      encTerm_tokens, TermToken.ofFin]

private theorem map_encodeTerms_cnfClause {n : ℕ} {vars : List ℕ} (c : Clause ℕ)
    (hc : ∀ l ∈ c, vars.idxOf l.1 < n) :
    (encFormula_tokens n (cnfClauseFormula n vars c)).map FormulaToken.encodeTerms =
      clauseFormulaTokens vars c := by
  induction c with
  | nil => simp [cnfClauseFormula, clauseFormulaTokens, encFormula_tokens, FormulaToken.encodeTerms]
  | cons l ls ih =>
    have hl : vars.idxOf l.1 < n := hc l (List.mem_cons_self ..)
    have hls := ih fun m hm ↦ hc m (List.mem_cons_of_mem _ hm)
    rw [cnfClauseFormula, encFormula_tokens, List.append_nil, List.map_cons, List.map_append,
      map_encodeTerms_cnfLiteral hl, hls]
    simp [FormulaToken.encodeTerms, clauseFormulaTokens, litFormulaTokens]

private theorem map_encodeTerms_cnfAux {n : ℕ} {vars : List ℕ} (cs : CNF ℕ)
    (hcs : ∀ c ∈ cs, ∀ l ∈ c, vars.idxOf l.1 < n) :
    (encFormula_tokens n (cnfToRealFormulaAux n vars cs)).map FormulaToken.encodeTerms =
      cs.flatMap (fun c ↦ (.inr (.inr (.inr (.inr (.inl ())))) : FormulaToken) ::
        clauseFormulaTokens vars c) ++ [.inr (.inr (.inr (.inl ()))), .inl ()] := by
  induction cs with
  | nil => simp [cnfToRealFormulaAux, encFormula_tokens, FormulaToken.encodeTerms]
  | cons c cs ih =>
    have hc := map_encodeTerms_cnfClause c (hcs c (List.mem_cons_self ..))
    have hrest := ih fun d hd ↦ hcs d (List.mem_cons_of_mem _ hd)
    rw [cnfToRealFormulaAux, encFormula_tokens, List.append_nil, List.map_cons, List.map_append,
      hc, hrest]
    simp [FormulaToken.encodeTerms, List.append_assoc]

private theorem encFormula_cnfToRealFormula (φ : CNF ℕ) :
    encFormula φ.vars.length (cnfToRealFormula φ) =
      encList encFormulaToken (cnfFormulaTokens φ) := by
  rw [encFormula_eq_encList_tokens]
  congr 1
  apply map_encodeTerms_cnfAux
  intro c hc l hl
  exact List.idxOf_lt_length_iff.mpr (CNF.mem_vars.mpr ⟨c, hc, l.2, hl⟩)

private theorem cnfFormulaTokens_polyTime :
    ComputableInPolyTime cnfFormulaTokens encCNF (encList encFormulaToken) := by
  let encLit := encPair encNat encBool
  let encCl := encList encLit
  have hterm : ComputableInPolyTime (fun p : ℕ × Bool ↦ litTermWord p.1 p.2)
      (encPair encUnary encBool) encBits := by
    have hidx : ComputableInPolyTime (fun p : ℕ × Bool ↦ (.inr (.inl p.1) : TermToken))
        (encPair encUnary encBool) encTermToken :=
      ((sumInr _ _).comp ((sumInl _ _).comp (fst encUnary encBool))).of_enc_eq fun _ ↦ rfl
    have hpos_list : ComputableInPolyTime
        (fun p : ℕ × Bool ↦ ([.inr (.inr (.inl ())), .inr (.inl p.1), .inl (-1)] : List TermToken))
        (encPair encUnary encBool) (encList encTermToken) :=
      ((cons encTermToken).comp ((const (.inr (.inr (.inl ())) : TermToken)).prod
        ((cons encTermToken).comp (hidx.prod (const ([.inl (-1)] : List TermToken)))))).of_enc_eq
        fun _ ↦ rfl
    have hneg_list : ComputableInPolyTime
        (fun p : ℕ × Bool ↦ ([.inr (.inl p.1)] : List TermToken))
        (encPair encUnary encBool) (encList encTermToken) :=
      ((cons encTermToken).comp (hidx.prod (const ([] : List TermToken)))).of_enc_eq fun _ ↦ rfl
    have hboth := ite' (snd encUnary encBool) hpos_list hneg_list
    exact ((of_eq (encIn := encList encTermToken) (encOut := encBits) fun _ ↦ rfl).comp
      hboth).of_enc_eq fun p ↦ by rcases p with ⟨_, _ | _⟩ <;> rfl
  let encCtx1 := encPair encCNF encCl
  let encCtx2 := encPair encCtx1 encLit
  have hvars2 := SAT.computableInPolyTime_vars.comp ((fst encCNF encCl).comp (fst encCtx1 encLit))
  have hlit_var := (fst encNat encBool).comp (snd encCtx1 encLit)
  have hlit_pol := (snd encNat encBool).comp (snd encCtx1 encLit)
  have hword2 := hterm.comp ((idxOfWithInput hvars2 hlit_var).prod hlit_pol)
  have heqTok2 : ComputableInPolyTime
      (fun q : (CNF ℕ × Clause ℕ) × Literal ℕ ↦
        (.inr (.inl (litTermWord (q.1.1.vars.idxOf q.2.1) q.2.2)) : FormulaToken))
      encCtx2 encFormulaToken :=
    ((sumInr _ _).comp ((sumInl _ _).comp hword2)).of_enc_eq fun _ ↦ rfl
  have hlitToks2 : ComputableInPolyTime
      (fun q : (CNF ℕ × Clause ℕ) × Literal ℕ ↦ litFormulaTokens q.1.1.vars q.2)
      encCtx2 (encList encFormulaToken) :=
    ((cons encFormulaToken).comp ((const (.inr (.inr (.inr (.inr (.inr ())))) : FormulaToken)).prod
      ((cons encFormulaToken).comp (heqTok2.prod (const []))))).of_enc_eq fun _ ↦ rfl
  have hclauseBody : ComputableInPolyTime
      (fun p : CNF ℕ × Clause ℕ ↦ clauseFormulaTokens p.1.vars p.2)
      encCtx1 (encList encFormulaToken) :=
    ((listAppend encFormulaToken).comp
      ((flatMapWithInput (f := fun (p : CNF ℕ × Clause ℕ) (l : Literal ℕ) ↦
          litFormulaTokens p.1.vars l) (snd encCNF encCl) hlitToks2).prod
        (const ([.inl ()] : List FormulaToken)))).of_enc_eq fun _ ↦ rfl
  have handClause : ComputableInPolyTime
      (fun p : CNF ℕ × Clause ℕ ↦
        (.inr (.inr (.inr (.inr (.inl ())))) : FormulaToken) :: clauseFormulaTokens p.1.vars p.2)
      encCtx1 (encList encFormulaToken) :=
    ((cons encFormulaToken).comp
      ((const (.inr (.inr (.inr (.inr (.inl ())))) : FormulaToken)).prod hclauseBody)).of_enc_eq
      fun _ ↦ rfl
  have hclauses : ComputableInPolyTime (fun φ : CNF ℕ ↦ φ) encCNF (encList encCl) :=
    of_eq fun _ ↦ rfl
  exact ((listAppend encFormulaToken).comp
    ((flatMapWithInput (f := fun (φ : CNF ℕ) (c : Clause ℕ) ↦
        (.inr (.inr (.inr (.inr (.inl ())))) : FormulaToken) :: clauseFormulaTokens φ.vars c)
        hclauses handClause).prod
      (const ([.inr (.inr (.inr (.inl ()))), .inl ()] : List FormulaToken)))).of_enc_eq fun _ ↦ rfl

private theorem mem_cnfClauseFormula_iff {n : ℕ} {vars : List ℕ} {c : Clause ℕ}
    (hc : ∀ l ∈ c, l.1 ∈ vars) (hn : vars.length = n) (x : Fin n → ℝ) :
    x ∈ (cnfClauseFormula n vars c).solutionSet ↔
      ∃ (l : Literal ℕ) (hl : l ∈ c),
        (l.2 = true → x ⟨vars.idxOf l.1, hn ▸ List.idxOf_lt_length_iff.mpr (hc l hl)⟩ = 1) ∧
        (l.2 = false → x ⟨vars.idxOf l.1, hn ▸ List.idxOf_lt_length_iff.mpr (hc l hl)⟩ = 0) := by
  induction c with
  | nil => simp [cnfClauseFormula, Formula.solutionSet]
  | cons l ls ih =>
    have hl_mem : l.1 ∈ vars := hc l (List.mem_cons_self ..)
    have hidx : vars.idxOf l.1 < n := hn ▸ List.idxOf_lt_length_iff.mpr hl_mem
    simp only [cnfClauseFormula, Formula.solutionSet, Set.mem_union,
      ih (fun m hm ↦ hc m (List.mem_cons_of_mem _ hm))]
    constructor
    · rintro (hl | ⟨m, hm, hmt, hmf⟩)
      · refine ⟨l, List.mem_cons_self .., fun hpol ↦ ?_, fun hpol ↦ ?_⟩
        · unfold cnfLiteralFormula at hl
          simp only [hidx, ↓reduceDIte, hpol, ↓reduceIte, Formula.solutionSet, Set.mem_ofPred_eq,
            Term.eval, Int.cast_neg, Int.cast_one] at hl
          linarith
        · unfold cnfLiteralFormula at hl
          simp only [hidx, ↓reduceDIte, hpol, Bool.false_eq_true, ↓reduceIte, Formula.solutionSet,
            Set.mem_ofPred_eq, Term.eval] at hl
          exact hl
      · exact ⟨m, List.mem_cons_of_mem _ hm, hmt, hmf⟩
    · rintro ⟨m, hm_cons, hmt, hmf⟩
      rcases List.mem_cons.mp hm_cons with rfl | hm_tail
      · left; unfold cnfLiteralFormula; simp only [hidx, ↓reduceDIte]
        cases hpol : m.2
        · simp [Formula.solutionSet, Term.eval, hmf hpol]
        · simp only [↓reduceIte, Formula.solutionSet, Set.mem_ofPred_eq, Term.eval,
            Int.cast_neg, Int.cast_one]
          linarith [hmt hpol]
      · exact Or.inr ⟨m, hm_tail, hmt, hmf⟩

private theorem mem_cnfToRealFormulaAux_iff {n : ℕ} {vars : List ℕ} (cs : CNF ℕ) :
    ∀ x : Fin n → ℝ,
      x ∈ (cnfToRealFormulaAux n vars cs).solutionSet ↔
        ∀ c ∈ cs, x ∈ (cnfClauseFormula n vars c).solutionSet := by
  induction cs with
  | nil => intro x; simp [cnfToRealFormulaAux, Formula.solutionSet]
  | cons c cs ih =>
    intro x
    simp only [cnfToRealFormulaAux, Formula.solutionSet, Set.mem_inter_iff, ih x,
      List.forall_mem_cons]

/-- Polynomial-time many-one reduction from propositional `SAT` to `ETR`. -/
theorem polyTimeReducible_SAT_ETR : PolyTimeReducible encCNF encBits SAT ETR := by
  let f : CNF ℕ → List Bool := fun φ ↦ encList encFormulaToken (cnfFormulaTokens φ)
  have hf : ComputableInPolyTime f encCNF encBits :=
    (of_eq (encIn := encList encFormulaToken) (encOut := encBits) fun _ ↦ rfl).comp
      cnfFormulaTokens_polyTime
  refine ⟨f, hf, fun φ ↦ ?_⟩
  dsimp only [f]
  rw [← encFormula_cnfToRealFormula φ, encFormula_mem_ETR, mem_SAT, CNF.Satisfiable]
  unfold cnfToRealFormula
  constructor
  · rintro ⟨σ, hσ⟩
    let x : Fin φ.vars.length → ℝ := fun i ↦ if σ (φ.vars[i.val]) then 1 else 0
    refine ⟨x, (mem_cnfToRealFormulaAux_iff φ x).mpr fun c hc ↦ ?_⟩
    have hc_eval : Clause.eval σ c = true := (List.all_eq_true.mp hσ) c hc
    obtain ⟨l, hl_mem, hl_eval⟩ := List.any_eq_true.mp hc_eval
    rw [Literal.eval, beq_iff_eq] at hl_eval
    have hl_var : l.1 ∈ φ.vars := CNF.mem_vars.mpr ⟨c, hc, l.2, hl_mem⟩
    refine (mem_cnfClauseFormula_iff (fun m hm ↦ CNF.mem_vars.mpr ⟨c, hc, m.2, hm⟩) rfl x).mpr
      ⟨l, hl_mem, fun hpol ↦ ?_, fun hpol ↦ ?_⟩
    · dsimp only [x]
      rw [List.getElem_idxOf (List.idxOf_lt_length_iff.mpr hl_var), hl_eval, hpol, ite_eq_left rfl]
    · dsimp only [x]
      rw [List.getElem_idxOf (List.idxOf_lt_length_iff.mpr hl_var), hl_eval, hpol]
      simp
  · rintro ⟨x, hx⟩
    let σ : ℕ → Bool := fun v ↦
      if h : φ.vars.idxOf v < φ.vars.length then decide (x ⟨φ.vars.idxOf v, h⟩ = 1) else false
    refine ⟨σ, List.all_eq_true.mpr fun c hc ↦ ?_⟩
    have hc_sol := (mem_cnfToRealFormulaAux_iff φ x).mp hx c hc
    obtain ⟨l, hl_mem, hlt, hlf⟩ :=
      (mem_cnfClauseFormula_iff (fun m hm ↦ CNF.mem_vars.mpr ⟨c, hc, m.2, hm⟩) rfl x).mp hc_sol
    refine List.any_eq_true.mpr ⟨l, hl_mem, ?_⟩
    rw [Literal.eval, beq_iff_eq]
    have hidx : φ.vars.idxOf l.1 < φ.vars.length :=
      List.idxOf_lt_length_iff.mpr (CNF.mem_vars.mpr ⟨c, hc, l.2, hl_mem⟩)
    dsimp only [σ]; simp only [hidx, ↓reduceDIte]
    cases hpol : l.2
    · simp [hlf hpol]
    · exact decide_eq_true (hlt hpol)

/-- **Shor's Inclusion (`NP ⊆ ∃ℝ`)**: every language in `NP enc` belongs to `ExistsReal enc`. -/
theorem NP_subset_ExistsReal {α : Type} (enc : α ↪ List Bool) :
    NP enc ⊆ ExistsReal enc :=
  fun L hL ↦ (CookLevin.SAT_npHard enc L hL).trans polyTimeReducible_SAT_ETR

/-- Dual inclusion `coNP ⊆ ∀ℝ`: every language in `coNP enc` belongs to `ForallReal enc`. -/
theorem coNP_subset_ForallReal {α : Type} (enc : α ↪ List Bool) :
    coNP enc ⊆ ForallReal enc :=
  fun _ hL ↦ NP_subset_ExistsReal enc (mem_coNP.mp hL)

/-- Deterministic polynomial time is contained in `ExistsReal`. -/
theorem P_subset_ExistsReal {α : Type} (enc : α ↪ List Bool) :
    P enc ⊆ ExistsReal enc :=
  P_subset_NP.trans (NP_subset_ExistsReal enc)

/-- Deterministic polynomial time is contained in `ForallReal`. -/
theorem P_subset_ForallReal {α : Type} (enc : α ↪ List Bool) :
    P enc ⊆ ForallReal enc :=
  P_subset_coNP.trans (coNP_subset_ForallReal enc)

end Cslib.Complexity
