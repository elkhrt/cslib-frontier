/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import CslibFrontier.Computability.Complexity.Classes.PH.Reduction
public import CslibFrontier.Computability.Complexity.Problems.SubsetSum
import CslibFrontier.Computability.Complexity.Classes.NP.Witness
import CslibFrontier.Computability.Complexity.Classes.PH.Projection
import CslibFrontier.Computability.Complexity.CookLevin.PolyTime
import CslibFrontier.Computability.Complexity.Problems.SAT.PolyTime
import CslibFrontier.Computability.Complexity.Problems.SubsetSum.Digits
import CslibFrontier.Computability.Complexity.Problems.ThreeSAT
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.NormalForm
import CslibFrontier.Foundations.Data.List.GetD
import CslibFrontier.Logics.Propositional.CNF.PolyTime
import CslibFrontier.Logics.Propositional.CNF.ThreeCNF.PolyTime
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Linarith

/-!
# Generalized Subset Sum (`GSSP`) and `∃∀ 3-CNF` Are `Σ₂ᴾ`-Complete

This module proves that the **Generalized Subset Sum Problem (`GSSP`)**
 and the bounded-quantifier problem **`Sigma2ThreeCNF`**
(`∃ x ∀ y, ¬ 3CNF(x, y)`) are `Σ₂ᴾ`-complete (`SigmaPComplete 2`) under polynomial-time
many-one reductions on the multi-tape Turing machine model of `Cslib.Complexity`.

- **`Sigma2ThreeCNF`**: given a list of existential variables `existVars` and a 3-CNF `φ`, asks
  whether there exists an assignment `x` to `existVars` such that no extension of `x` satisfies
  `φ` (equivalently, `∀ y, ¬φ(x, y)` holds, a `∃∀ 3-DNF` formula).
- **`GeneralizedSubsetSum` (`GSSP`)**: given lists of natural numbers `u, v` and target `T`, asks
  whether `∃ x ∈ {0, 1}^{|u|}, ∀ y ∈ {0, 1}^{|v|}, u · x + v · y ≠ T`.
- **`PosGeneralizedSubsetSum`**: the strictly positive restriction (`u_i > 0, v_j > 0, T > 0`
  and nonempty `u, v`), proved `Σ₂ᴾ`-complete by the same base-8 choice-forcing digit
  construction.

All proofs use only standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`).

## Main definitions

* `Cslib.Complexity.Sigma2CNFInstance`, `Cslib.Complexity.encSigma2CNF`,
  `Cslib.Complexity.Sigma2ThreeCNF`.
* `Cslib.Complexity.GeneralizedSubsetSumInstance`,
  `Cslib.Complexity.encGeneralizedSubsetSum`,
  `Cslib.Complexity.GeneralizedSubsetSum`,
  `Cslib.Complexity.PosGeneralizedSubsetSum`.

## Main results

* `Cslib.Complexity.Sigma2ThreeCNF_sigmaPComplete`: `Sigma2ThreeCNF` is `Σ₂ᴾ`-complete.
* `Cslib.Complexity.GeneralizedSubsetSum_sigmaPComplete`: `GSSP` is `Σ₂ᴾ`-complete.
* `Cslib.Complexity.PosGeneralizedSubsetSum_sigmaPComplete`: strictly positive `GSSP` is
  `Σ₂ᴾ`-complete.
-/

public section

namespace Cslib.Complexity

open Cslib.Complexity Cslib.Logic.PL Turing.MultiTapeTM ComputableInPolyTime
open scoped List

/-! ### `∃∀ 3-CNF` (`Sigma2ThreeCNF`) -/

/-- An instance `(existVars, formula)` of `∃∀ 3-CNF` (equivalently `∃∀ 3-DNF` by negation). -/
@[ext]
structure Sigma2CNFInstance where
  /-- Distinct variable indices bound by the outer existential quantifier. -/
  existVars : List ℕ
  /-- The inner 3-CNF formula whose satisfiability is universally negated. -/
  formula : CNF ℕ
  deriving DecidableEq, Repr

/-- Binary encoding of `Sigma2CNFInstance`. -/
enc_structure encSigma2CNF : Sigma2CNFInstance where
  existVars : (encList encNat), formula : encCNF

attribute [fun_prop] encSigma2CNF_existVars_polyTime encSigma2CNF_formula_polyTime
  encSigma2CNF_mk_polyTime

/-- **`∃∀ 3-CNF` (`Sigma2ThreeCNF`)**: `existVars` is duplicate-free, every clause of `formula`
has length at most `3`, and there exists an assignment to `existVars` with no satisfying extension
to `formula`. -/
def Sigma2ThreeCNF : Set Sigma2CNFInstance :=
  {inst | inst.existVars.Nodup ∧ (∀ c ∈ inst.formula, c.length ≤ 3) ∧
    ∃ x : Fin inst.existVars.length → Bool,
      ∀ σ : ℕ → Bool, (∀ i : Fin inst.existVars.length, σ inst.existVars[i] = x i) →
        inst.formula.eval σ = false}

/-- Membership characterization for `Sigma2ThreeCNF`. -/
theorem mem_Sigma2ThreeCNF_iff {inst : Sigma2CNFInstance} :
    inst ∈ Sigma2ThreeCNF ↔
      inst.existVars.Nodup ∧ (∀ c ∈ inst.formula, c.length ≤ 3) ∧
      ∃ x : Fin inst.existVars.length → Bool,
        ∀ σ : ℕ → Bool, (∀ i : Fin inst.existVars.length, σ inst.existVars[i] = x i) →
          inst.formula.eval σ = false :=
  Iff.rfl

/-- Executable assignment lookup from a list of variables and a parallel Boolean mask. -/
def maskAssign (vars : List ℕ) (bits : List Bool) (v : ℕ) : Bool :=
  bits.getD (vars.idxOf v) false

/-- `maskAssign` agrees with `bits[i]` on `vars[i]` when `vars` is duplicate-free and `bits`
has length `vars.length`. -/
theorem maskAssign_getElem {vars : List ℕ} {bits : List Bool} (hn : vars.Nodup)
    (hl : bits.length = vars.length) (i : Fin vars.length) :
    maskAssign vars bits vars[i] = bits[i.1]'(hl.symm ▸ i.2) := by
  have hib : i.1 < bits.length := hl.symm ▸ i.2
  have hidx : vars.idxOf vars[i.1] = i.1 := hn.idxOf_getElem i.1 i.2
  change bits.getD (vars.idxOf vars[i.1]) false = bits[i.1]'hib
  simp only [hidx, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hib, Option.getD_some]

private theorem computableInPolyTime_maskAssign_eval :
    ComputableInPolyTime
      (fun p : (CNF ℕ × List ℕ) × List Bool ↦
        p.1.1.eval (maskAssign p.1.2 p.2))
      (encPair (encPair encCNF (encList encNat)) encBits) encBool := by
  have hfn : (fun p : (CNF ℕ × List ℕ) × List Bool ↦ p.1.1.eval (maskAssign p.1.2 p.2)) =
      fun p ↦ p.1.1.all fun c ↦ c.any fun l ↦
        (p.2.getD (p.1.2.idxOf l.1) false == l.2) := by
    funext p
    unfold CNF.eval Clause.eval Literal.eval maskAssign
    rfl
  rw [hfn]
  let encQ := encPair (encPair (encPair (encPair encCNF (encList encNat)) encBits)
    (encList (encPair encNat encBool))) (encPair encNat encBool)
  have hvars : ComputableInPolyTime
      (fun q : (((CNF ℕ × List ℕ) × List Bool) × Clause ℕ) × Literal ℕ ↦ q.1.1.1.2)
      encQ (encList encNat) :=
    (snd encCNF (encList encNat)).comp ((fst _ _).comp ((fst _ _).comp (fst _ _)))
  have hbits : ComputableInPolyTime
      (fun q : (((CNF ℕ × List ℕ) × List Bool) × Clause ℕ) × Literal ℕ ↦ q.1.1.2)
      encQ encBits :=
    (snd _ _).comp ((fst _ _).comp (fst _ _))
  have hl1 : ComputableInPolyTime
      (fun q : (((CNF ℕ × List ℕ) × List Bool) × Clause ℕ) × Literal ℕ ↦ q.2.1)
      encQ encNat :=
    (fst encNat encBool).comp (snd _ _)
  have hl2 : ComputableInPolyTime
      (fun q : (((CNF ℕ × List ℕ) × List Bool) × Clause ℕ) × Literal ℕ ↦ q.2.2)
      encQ encBool :=
    (snd encNat encBool).comp (snd _ _)
  have hidx : ComputableInPolyTime
      (fun q : (((CNF ℕ × List ℕ) × List Bool) × Clause ℕ) × Literal ℕ ↦ q.1.1.1.2.idxOf q.2.1)
      encQ encUnary :=
    idxOfWithInput hvars hl1
  have hget : ComputableInPolyTime
      (fun q : (((CNF ℕ × List ℕ) × List Bool) × Clause ℕ) × Literal ℕ ↦
        q.1.1.2.getD (q.1.1.1.2.idxOf q.2.1) false) encQ encBool :=
    bitsGetDWithInput hbits hidx false
  have hlit : ComputableInPolyTime
      (fun q : (((CNF ℕ × List ℕ) × List Bool) × Clause ℕ) × Literal ℕ ↦
        (q.1.1.2.getD (q.1.1.1.2.idxOf q.2.1) false == q.2.2)) encQ encBool :=
    (of_finite (fun p : Bool × Bool ↦ p.1 == p.2)).comp (hget.prod hl2)
  have hclause : ComputableInPolyTime
      (fun q : ((CNF ℕ × List ℕ) × List Bool) × Clause ℕ ↦
        q.2.any fun l ↦ (q.1.2.getD (q.1.1.2.idxOf l.1) false == l.2))
      (encPair (encPair (encPair encCNF (encList encNat)) encBits)
        (encList (encPair encNat encBool)))
      encBool :=
    anyWithInput (snd _ _) hlit
  exact allWithInput ((fst encCNF (encList encNat)).comp (fst _ _)) hclause

/-- **`Sigma2ThreeCNF` belongs to `Σ₂ᴾ`.** -/
theorem Sigma2ThreeCNF_mem_SigmaP : Sigma2ThreeCNF ∈ SigmaP 2 encSigma2CNF := by
  -- Use `mem_SigmaP_of_exists_length` and `mem_PiP_of_forall_length`.
  have hinner :
      {p : Sigma2CNFInstance × List Bool |
        p.1.existVars.Nodup ∧ (∀ c ∈ p.1.formula, c.length ≤ 3) ∧
        ∀ w : List Bool, w.length = p.1.formula.distinctVars.length →
          p.1.formula.eval (maskAssign (p.1.existVars ++ p.1.formula.distinctVars)
            (p.2 ++ w)) = false} ∈ PiP 1 (encPair encSigma2CNF encBits) := by
    have hpred :
        {q : (Sigma2CNFInstance × List Bool) × List Bool |
          q.1.1.existVars.Nodup ∧ (∀ c ∈ q.1.1.formula, c.length ≤ 3) ∧
          q.1.1.formula.eval (maskAssign (q.1.1.existVars ++ q.1.1.formula.distinctVars)
            (q.1.2 ++ q.2)) = false} ∈ P (encPair (encPair encSigma2CNF encBits) encBits) := by
      let check : (Sigma2CNFInstance × List Bool) × List Bool → Bool := fun q ↦
        (q.1.1.existVars.all fun v ↦ decide (q.1.1.existVars.count v ≤ 1)) &&
        (q.1.1.formula.all fun c ↦ decide (c.length ≤ 3)) &&
        !(q.1.1.formula.eval (maskAssign (q.1.1.existVars ++ q.1.1.formula.distinctVars)
          (q.1.2 ++ q.2)))
      refine ⟨check, ?_, fun q ↦ ?_⟩
      · let encS := encPair (encPair encSigma2CNF encBits) encBits
        let Q := (Sigma2CNFInstance × List Bool) × List Bool
        have hinst : ComputableInPolyTime (fun q : Q ↦ q.1.1) encS encSigma2CNF :=
          (fst encSigma2CNF encBits).comp (fst _ _)
        have hex : ComputableInPolyTime (fun q : Q ↦ q.1.1.existVars) encS (encList encNat) :=
          encSigma2CNF_existVars_polyTime hinst
        have hform : ComputableInPolyTime (fun q : Q ↦ q.1.1.formula) encS encCNF :=
          encSigma2CNF_formula_polyTime hinst
        have hdv : ComputableInPolyTime (fun q : Q ↦ q.1.1.formula.distinctVars)
            encS (encList encNat) :=
          (CNF.computableInPolyTime_distinctVars encNat).comp hform
        have hvars : ComputableInPolyTime
            (fun q : Q ↦ q.1.1.existVars ++ q.1.1.formula.distinctVars) encS (encList encNat) :=
          (listAppend encNat).comp (hex.prod hdv)
        have hbits : ComputableInPolyTime (fun q : Q ↦ q.1.2 ++ q.2) encS encBits :=
          bitsAppend ((snd encSigma2CNF encBits).comp (fst _ _)) (snd _ _)
        have heval : ComputableInPolyTime
            (fun q : Q ↦ q.1.1.formula.eval (maskAssign
              (q.1.1.existVars ++ q.1.1.formula.distinctVars) (q.1.2 ++ q.2))) encS encBool :=
          computableInPolyTime_maskAssign_eval.comp ((hform.prod hvars).prod hbits)
        have hcheck_nd : ComputableInPolyTime
            (fun q : Q ↦ q.1.1.existVars.all fun v ↦ decide (q.1.1.existVars.count v ≤ 1))
            encS encBool := by
          refine allWithInput hex ?_
          have hcnt : ComputableInPolyTime (fun r : Q × ℕ ↦ r.1.1.1.existVars.count r.2)
              (encPair encS encNat) encUnary :=
            countWithInput (hex.comp (fst _ _)) (snd _ _)
          exact ComputableInPolyTime.unary_le.comp (hcnt.prod (const 1))
        have hcheck_w : ComputableInPolyTime
            (fun q : Q ↦ q.1.1.formula.all fun c ↦ decide (c.length ≤ 3)) encS encBool :=
          allWithInput hform (ComputableInPolyTime.unary_le.comp
            (((length_list (encPair encNat encBool)).comp (snd _ _)).prod (const 3)))
        exact ComputableInPolyTime.bool_and' (ComputableInPolyTime.bool_and' hcheck_nd hcheck_w)
          (ComputableInPolyTime.bool_not.comp heval)
      · have hnd_iff : (q.1.1.existVars.all fun v ↦ decide (q.1.1.existVars.count v ≤ 1)) = true ↔
            q.1.1.existVars.Nodup := by
          rw [List.all_eq_true, List.nodup_iff_count_le_one]
          exact ⟨fun h v ↦ if hv : v ∈ q.1.1.existVars then decide_eq_true_eq.mp (h v hv)
            else by simp [List.count_eq_zero.mpr hv], fun h v _ ↦ decide_eq_true (h v)⟩
        simp [check, Bool.and_eq_true, hnd_iff, List.all_eq_true, and_assoc]
    have hforall := mem_PiP_of_forall_length (k := 1) le_rfl
      (N := fun p : Sigma2CNFInstance × List Bool ↦ p.1.formula.distinctVars.length)
      (by fun_prop)
      (PiP_mono (Nat.zero_le 1) (PiP_zero ▸ hpred))
    refine (PolyTimeReducible.mem_PiP (k := 1) ⟨id, .id', fun p ↦ ?_⟩ hforall)
    constructor
    · rintro ⟨hn, hw, h⟩ w hwl
      exact ⟨hn, hw, h w hwl⟩
    · intro h
      have ⟨hn, hw, _⟩ := h (List.replicate p.1.formula.distinctVars.length false) (by simp)
      exact ⟨hn, hw, fun w hwl ↦ (h w hwl).2.2⟩
  have hexists := mem_SigmaP_of_exists_length (k := 2) (by omega)
    (N := fun inst : Sigma2CNFInstance ↦ inst.existVars.length)
    (by fun_prop)
    (PiP_subset_SigmaP_succ 1 hinner)
  refine (PolyTimeReducible.mem_SigmaP (k := 2) ⟨id, .id', fun inst ↦ ?_⟩ hexists)
  simp only [id, Set.mem_ofPred_eq, mem_Sigma2ThreeCNF_iff]
  constructor
  · rintro ⟨hn, hw, x, hx⟩
    refine ⟨List.ofFn x, List.length_ofFn, hn, hw, fun w hwl ↦ hx _ fun i ↦ ?_⟩
    have hidx : (inst.existVars ++ inst.formula.distinctVars).idxOf inst.existVars[i.1] = i.1 := by
      rw [List.idxOf_append_of_mem (List.getElem_mem i.2)]
      exact hn.idxOf_getElem i.1 i.2
    change (List.ofFn x ++ w).getD
      ((inst.existVars ++ inst.formula.distinctVars).idxOf inst.existVars[i.1]) false = x i
    simp only [hidx, List.getD_eq_getElem?_getD,
      List.getElem?_append_left (by simp : i.1 < (List.ofFn x).length),
      List.getElem?_eq_getElem (by simp : i.1 < (List.ofFn x).length), List.getElem_ofFn,
      Option.getD_some]
  · rintro ⟨u, hul, hn, hw, h⟩
    refine ⟨hn, hw, fun i ↦ u[i.1]'(hul.symm ▸ i.2), fun σ hσ ↦ ?_⟩
    let w : List Bool := inst.formula.distinctVars.map σ
    have hwl : w.length = inst.formula.distinctVars.length := List.length_map _
    have heq : inst.formula.eval σ =
        inst.formula.eval (maskAssign (inst.existVars ++ inst.formula.distinctVars) (u ++ w)) := by
      refine CNF.eval_congr fun v hv ↦ ?_
      have hdv : v ∈ inst.formula.distinctVars := CNF.mem_distinctVars.mpr hv
      by_cases hmem : v ∈ inst.existVars
      · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hmem
        have hidx : (inst.existVars ++ inst.formula.distinctVars).idxOf inst.existVars[i] = i := by
          rw [List.idxOf_append_of_mem hmem]
          exact hn.idxOf_getElem i hi
        have hiu : i < u.length := hul.symm ▸ hi
        simp only [maskAssign, hidx, List.getD_eq_getElem?_getD,
          List.getElem?_append_left hiu, List.getElem?_eq_getElem hiu, Option.getD_some]
        exact hσ ⟨i, hi⟩
      · have hidx : (inst.existVars ++ inst.formula.distinctVars).idxOf v =
            inst.existVars.length + inst.formula.distinctVars.idxOf v := by
          rw [List.idxOf_append_of_notMem hmem]
        have hlt : inst.formula.distinctVars.idxOf v < inst.formula.distinctVars.length :=
          List.idxOf_lt_length_iff.mpr hdv
        have hltw : inst.formula.distinctVars.idxOf v < w.length := hwl.symm ▸ hlt
        simp only [maskAssign, hidx, List.getD_eq_getElem?_getD, ← hul,
          List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
          List.getElem?_eq_getElem hltw, Option.getD_some, w, List.getElem_map,
          List.getElem_idxOf hlt]
    rw [heq]
    exact h w hwl

/-- **`Sigma2ThreeCNF` is `Σ₂ᴾ`-hard**: every problem in `Σ₂ᴾ` reduces in polynomial time to
`Sigma2ThreeCNF` via the Cook–Levin tableau and count-preserving 3-CNF splitting. -/
theorem Sigma2ThreeCNF_sigmaPHard : SigmaPHard 2 encSigma2CNF Sigma2ThreeCNF := by
  intro α enc A hA
  obtain ⟨p, V, hV, hAV⟩ := exists_replicate_of_mem_SigmaP hA
  let p' : Polynomial ℕ := p + 1
  have hp' : ∀ n, 1 ≤ p'.eval n := fun n ↦ by simp [p']
  let trim (x : α × List Bool) : List Bool :=
    (x.2.take (p.eval (enc x.1).length)) ++
      ((x.2.drop (p'.eval (enc x.1).length)).take (p.eval (enc x.1).length))
  -- Build a verifier `W` for the complemented predicate on two blocks of length `p'`.
  let W (x : α × List Bool) : Bool := !(V (x.1, trim x))
  have hW : ComputableInPolyTime W (encPair enc encBits) encBool := by
    have hlen : ComputableInPolyTime (fun x : α × List Bool ↦ (enc x.1).length)
        (encPair enc encBits) encUnary :=
      (ComputableInPolyTime.encoding_length enc).comp (ComputableInPolyTime.fst enc encBits)
    have hplen := (ComputableInPolyTime.unary_eval p).comp hlen
    have hp'len := (ComputableInPolyTime.unary_eval p').comp hlen
    have ht1 : ComputableInPolyTime (fun x : α × List Bool ↦ x.2.take (p.eval (enc x.1).length))
        (encPair enc encBits) encBits :=
      ComputableInPolyTime.bitsTakeWithInput (ComputableInPolyTime.snd enc encBits) hplen
    have ht2 : ComputableInPolyTime (fun x : α × List Bool ↦
        (x.2.drop (p'.eval (enc x.1).length)).take (p.eval (enc x.1).length))
        (encPair enc encBits) encBits :=
      ComputableInPolyTime.bitsTakeWithInput
        (ComputableInPolyTime.bitsDropWithInput (ComputableInPolyTime.snd enc encBits) hp'len)
        hplen
    have htrim : ComputableInPolyTime trim (encPair enc encBits) encBits :=
      ComputableInPolyTime.bitsAppend ht1 ht2
    exact ComputableInPolyTime.bool_not.comp
      (hV.comp ((ComputableInPolyTime.fst enc encBits).prod htrim))
  obtain ⟨c, d, k, State, hfin, tm, htm⟩ :=
    Turing.MultiTapeTM.Internal.NormalForm.polyTime hW
  have := Fintype.ofFinite State
  classical
  let m (a : α) : ℕ := p'.eval (enc a).length
  let q (a : α) : List Bool × ℕ × ℕ :=
    (frame (enc a), 2 * m a, c * (2 * (enc a).length + 1 + 2 * m a + 1) ^ d)
  let tab (a : α) : CNF ℕ :=
    ((CookLevin.tableau tm (q a).1 (q a).2.1 (q a).2.2).relabel CookLevin.Var.index)
  let red (a : α) : Sigma2CNFInstance :=
    ⟨(List.range (m a)).map (fun j ↦ 2 * Nat.pair 1 j), toThreeSAT (tab a)⟩
  have hm : ComputableInPolyTime m enc encUnary := by
    unfold m; fun_prop
  have hred : ComputableInPolyTime red enc encSigma2CNF := by
    have htab : ComputableInPolyTime tab enc encCNF := by
      have hq : ComputableInPolyTime q enc (encPair encBits (encPair encUnary encUnary)) := by
        have hlen := ComputableInPolyTime.encoding_length enc
        have hfr : ComputableInPolyTime (fun a ↦ frame (enc a)) enc encBits := by fun_prop
        have h2m : ComputableInPolyTime (fun a ↦ 2 * m a) enc encUnary :=
          ComputableInPolyTime.unary_mul.comp ((ComputableInPolyTime.const 2).prod hm)
        have htime : ComputableInPolyTime (fun a ↦ (q a).2.2) enc encUnary := by
          have harg : ComputableInPolyTime (fun a ↦ 2 * (enc a).length + 1 + 2 * m a + 1)
              enc encUnary := by
            have h2l : ComputableInPolyTime (fun a ↦ 2 * (enc a).length) enc encUnary :=
              ComputableInPolyTime.unary_mul.comp ((ComputableInPolyTime.const 2).prod hlen)
            have h1 := ComputableInPolyTime.unary_add.comp (h2l.prod (const 1))
            have h2 := ComputableInPolyTime.unary_add.comp (h1.prod h2m)
            exact ComputableInPolyTime.unary_add.comp (h2.prod (const 1))
          have hpow : ComputableInPolyTime (fun n : ℕ ↦ n ^ d) encUnary encUnary := by
            simpa only [Polynomial.eval_pow, Polynomial.eval_X] using
              ComputableInPolyTime.unary_eval (Polynomial.X ^ d)
          exact ComputableInPolyTime.unary_mul.comp ((const c).prod (hpow.comp harg))
        exact hfr.prod (h2m.prod htime)
      exact CookLevin.computableInPolyTime_relabel.comp
        ((CookLevin.computableInPolyTime_tableau tm).comp hq)
    have hex : ComputableInPolyTime (fun a ↦ (red a).existVars) enc (encList encNat) := by
      have hpair : ComputableInPolyTime (fun j : ℕ ↦ 2 * Nat.pair 1 j) encUnary encNat := by
        have hp1 : ComputableInPolyTime (fun j : ℕ ↦ Nat.pair 1 j) encUnary encUnary :=
          ComputableInPolyTime.unary_pair.comp ((const 1).prod id')
        have hp2 : ComputableInPolyTime (fun j : ℕ ↦ 2 * Nat.pair 1 j) encUnary encUnary :=
          ComputableInPolyTime.unary_mul.comp ((const 2).prod hp1)
        exact ComputableInPolyTime.unary_to_binary.comp hp2
      exact (ComputableInPolyTime.map hpair).comp (ComputableInPolyTime.range.comp hm)
    exact encSigma2CNF_mk_polyTime hex (computableInPolyTime_toThreeSAT.comp htab)
  refine ⟨red, hred, fun a ↦ ?_⟩
  -- Correctness of `red`: `a ∈ A` iff `∃ x (|x| = m a), ∀ y (|y| = m a), V(a, trim(x ++ y)) =
  -- true`.
  have hA' : a ∈ A ↔ ∃ u : List Bool, u.length = m a ∧
      ∀ v : List Bool, v.length = m a → W (a, u ++ v) = false := by
    rw [hAV a]
    simp only [List.replicate_succ, List.replicate_zero, List.map_cons, List.map_nil,
      alternation_true_cons, alternation_false_cons, alternation_nil, List.append_nil, W,
      Bool.not_eq_false']
    have hle : p.eval (enc a).length ≤ m a := by
      simp [m, p']
    constructor
    · rintro ⟨x, hx, h⟩
      refine ⟨x ++ List.replicate (m a - x.length) false, by simp [hx, hle], fun v hv ↦ ?_⟩
      have hlen1 : (x ++ List.replicate (m a - x.length) false).length = m a := by simp [hx, hle]
      have htrim : trim (a, (x ++ List.replicate (m a - x.length) false) ++ v) =
          x ++ v.take (p.eval (enc a).length) := by
        dsimp only [trim]
        have h1 : ((x ++ List.replicate (m a - x.length) false) ++ v).take (p.eval (enc a).length) =
            x := by
          rw [List.append_assoc, List.take_append_of_le_length (by omega),
            List.take_of_length_le hx.le]
        have h2 : ((x ++ List.replicate (m a - x.length) false) ++ v).drop (m a) = v :=
          List.drop_left' hlen1
        rw [h1, h2]
      rw [htrim]
      exact h (v.take (p.eval (enc a).length)) (by simp [hv, hle])
    · rintro ⟨u, hu, h⟩
      refine ⟨u.take (p.eval (enc a).length), by simp [hu, hle], fun y hy ↦ ?_⟩
      have hv := h (y ++ List.replicate (m a - y.length) false) (by simp [hy, hle])
      have htrim : trim (a, u ++ (y ++ List.replicate (m a - y.length) false)) =
          u.take (p.eval (enc a).length) ++ y := by
        dsimp only [trim]
        rw [List.take_append_of_le_length (hu.symm ▸ hle), List.drop_left' hu,
          List.take_append_of_le_length (by omega), List.take_of_length_le hy.le]
      rwa [htrim] at hv
  rw [hA', mem_Sigma2ThreeCNF_iff]
  have hnodup : (red a).existVars.Nodup := by
    refine List.Nodup.map (fun i j h ↦ ?_) List.nodup_range
    have h' : Nat.pair 1 i = Nat.pair 1 j := by omega
    exact (Nat.pair_eq_pair.mp h').2
  have hwidth : ∀ c ∈ (red a).formula, c.length ≤ 3 := fun c hc ↦ by
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
    simpa using CNF.length_le_three_of_mem_to3CNF hd
  rw [and_iff_right hnodup, and_iff_right hwidth]
  -- Match existential assignments `u : List Bool` of length `m a` with `x : Fin (m a) → Bool`.
  have hlen_ex : (red a).existVars.length = m a := by simp [red]
  have hrun (z : List Bool) (hz : z.length = 2 * m a) :
      (∃ τ, CookLevin.certWord τ (2 * m a) = z ∧
        (CookLevin.tableau tm (q a).1 (q a).2.1 (q a).2.2).eval τ = true) ↔
        W (a, z) = true := by
    have htm_run := (htm (a, z)).runFrom_initCfg
    have hlen_p : (encPair enc encBits (a, z)).length = 2 * (enc a).length + 1 + 2 * m a := by
      simp [encBits_apply, hz]
    rw [hlen_p, encPair_apply, encBits_apply] at htm_run
    dsimp only [q]
    rw [← hz, CookLevin.exists_eval_tableau_iff, hz, htm_run.2]
    simpa only [encBool_apply, List.cons.injEq, and_true] using and_iff_right htm_run.1
  constructor
  · rintro ⟨u, hu, h⟩
    refine ⟨fun i ↦ u[i.1]'(by omega), fun σ hσ ↦ ?_⟩
    by_contra hsat
    have hsat' : (toThreeSAT (tab a)).eval σ = true := Bool.eq_true_of_not_eq_false hsat
    have h1 : (tab a).to3CNF.eval (σ ∘ splitVarToNat) = true := by
      simpa [toThreeSAT, CNF.eval_relabel] using hsat'
    have htab_true : (tab a).eval (σ ∘ splitVarToNat ∘ Sum.inl) = true :=
      CNF.eval_comp_inl_of_eval_to3CNF h1
    let τ : CookLevin.Var k State → Bool :=
      (σ ∘ splitVarToNat ∘ Sum.inl) ∘ CookLevin.Var.index
    have hτ : (CookLevin.tableau tm (q a).1 (q a).2.1 (q a).2.2).eval τ = true := by
      simpa [tab, CNF.eval_relabel] using htab_true
    let z := CookLevin.certWord τ (2 * m a)
    have hz : z.length = 2 * m a := CookLevin.length_certWord τ (2 * m a)
    have hWz : W (a, z) = true := (hrun z hz).mp ⟨τ, rfl, hτ⟩
    have hz_eq : z = u ++ z.drop (m a) := by
      have htake : z.take (m a) = u := by
        refine List.ext_getElem (by simp [hz, hu]; omega) fun j hj1 hj2 ↦ ?_
        have hjm : j < m a := by omega
        have h1 : z[j] = σ (2 * Nat.pair 1 j) := by
          simp [z, CookLevin.certWord, τ, CookLevin.Var.index, splitVarToNat]
        have h2 := hσ ⟨j, by simpa [hlen_ex] using hjm⟩
        simp only [red] at h2
        simpa [List.getElem_take, h1] using h2
      rw [← htake, List.take_append_drop]
    have hv_len : (z.drop (m a)).length = m a := by simp [hz]; omega
    rw [hz_eq] at hWz
    exact absurd hWz (by rw [h _ hv_len]; decide)
  · rintro ⟨x, hx⟩
    refine ⟨List.ofFn (fun i : Fin (m a) ↦ x ⟨i.1, hlen_ex.symm ▸ i.2⟩), List.length_ofFn,
      fun v hv ↦ ?_⟩
    by_contra hWtrue
    have hWtrue' :
        W (a, List.ofFn (fun i : Fin (m a) ↦ x ⟨i.1, hlen_ex.symm ▸ i.2⟩) ++ v) = true :=
      Bool.eq_true_of_not_eq_false hWtrue
    have hlen_uv : (List.ofFn (fun i : Fin (m a) ↦ x ⟨i.1, hlen_ex.symm ▸ i.2⟩) ++ v).length =
        2 * m a := by simp [hv]; omega
    obtain ⟨τ, hτ_word, hτ_eval⟩ := (hrun _ hlen_uv).mpr hWtrue'
    let σ₀ : ℕ → Bool := fun n ↦
      if h : ∃ v : CookLevin.Var k State, v.index = n then τ h.choose else false
    have htab_eval : (tab a).eval σ₀ = true := by
      rw [CNF.eval_relabel]
      have hfn : σ₀ ∘ CookLevin.Var.index = τ := by
        funext v
        have hex : ∃ v' : CookLevin.Var k State, v'.index = v.index := ⟨v, rfl⟩
        simp only [Function.comp_apply, σ₀, dite_eq_left hex]
        exact congrArg τ (CookLevin.Var.index_injective hex.choose_spec)
      rwa [hfn]
    let τ₃ : ℕ ⊕ (ℕ × ℕ) → Bool := (tab a).to3CNFAssignment σ₀
    have hτ₃ : (tab a).to3CNF.eval τ₃ = true := CNF.eval_to3CNF_to3CNFAssignment htab_eval
    let σ : ℕ → Bool := fun n ↦
      τ₃ (if n % 2 = 0 then .inl (n / 2) else .inr (Nat.unpair (n / 2)))
    have hσ_comp : σ ∘ splitVarToNat = τ₃ := by
      funext s
      cases s with
      | inl v => simp [σ, splitVarToNat]
      | inr p =>
        have hodd : (2 * Nat.pair p.1 p.2 + 1) % 2 ≠ 0 := by omega
        change τ₃ (if (2 * Nat.pair p.1 p.2 + 1) % 2 = 0 then
            .inl ((2 * Nat.pair p.1 p.2 + 1) / 2) else
            .inr (Nat.unpair ((2 * Nat.pair p.1 p.2 + 1) / 2))) = τ₃ (.inr p)
        rw [ite_eq_right hodd, show (2 * Nat.pair p.1 p.2 + 1) / 2 = Nat.pair p.1 p.2 by omega,
          Nat.unpair_pair]
    have hsat : (toThreeSAT (tab a)).eval σ = true := by
      rw [toThreeSAT, CNF.eval_relabel, hσ_comp]
      exact hτ₃
    have hagree : ∀ i : Fin (red a).existVars.length, σ (red a).existVars[i] = x i := by
      intro i
      have him : i.1 < m a := hlen_ex ▸ i.2
      have hval : (red a).existVars[i] = 2 * Nat.pair 1 i.1 := by simp [red]
      rw [hval]
      have hσi : σ (2 * Nat.pair 1 i.1) = σ₀ (Nat.pair 1 i.1) := by
        simp [σ, τ₃, CNF.to3CNFAssignment_inl]
      rw [hσi]
      have hex : ∃ v : CookLevin.Var k State, v.index = Nat.pair 1 i.1 := ⟨.cert i.1, rfl⟩
      have hchoose : hex.choose = .cert i.1 :=
        CookLevin.Var.index_injective hex.choose_spec
      simp only [σ₀, dite_eq_left hex, hchoose]
      have hcw := congrArg (·[i.1]?) hτ_word
      have hget : (CookLevin.certWord τ (2 * m a))[i.1]? = some (τ (.cert i.1)) := by
        simp [CookLevin.certWord, show i.1 < 2 * m a by omega]
      rw [hget, List.getElem?_append_left (by simp [him]), List.getElem?_eq_getElem (by simp [him]),
        List.getElem_ofFn] at hcw
      exact Option.some.inj hcw
    exact absurd hsat (by rw [hx σ hagree]; decide)

/-- **`Sigma2ThreeCNF` is `Σ₂ᴾ`-complete.** -/
theorem Sigma2ThreeCNF_sigmaPComplete : SigmaPComplete 2 encSigma2CNF Sigma2ThreeCNF :=
  ⟨Sigma2ThreeCNF_mem_SigmaP, Sigma2ThreeCNF_sigmaPHard⟩

/-! ### Generalized Subset Sum (`GSSP`) and Strictly Positive `GSSP` -/

/-- An instance `(existNums, univNums, target)` of the Generalized Subset Sum Problem (`GSSP`). -/
@[ext]
structure GeneralizedSubsetSumInstance where
  /-- Numbers selected by the outer existential player. -/
  existNums : List ℕ
  /-- Numbers selected by the inner universal player. -/
  univNums : List ℕ
  /-- Target sum `T`. -/
  target : ℕ
  deriving DecidableEq, Repr

/-- Binary encoding of `GeneralizedSubsetSumInstance`. -/
enc_structure encGeneralizedSubsetSum : GeneralizedSubsetSumInstance where
  existNums : (encList encNat), univNums : (encList encNat), target : encNat

attribute [fun_prop] encGeneralizedSubsetSum_existNums_polyTime
  encGeneralizedSubsetSum_univNums_polyTime encGeneralizedSubsetSum_target_polyTime
  encGeneralizedSubsetSum_mk_polyTime

/-- Sum of the entries of `xs` selected by the Boolean mask `b`. -/
def maskedSum (xs : List ℕ) (b : Fin xs.length → Bool) : ℕ :=
  ∑ i : Fin xs.length, if b i then xs[i] else 0

/-- Semantic equation for `maskedSum`. -/
theorem maskedSum_eq (xs : List ℕ) (b : Fin xs.length → Bool) :
    maskedSum xs b = ∑ i : Fin xs.length, if b i then xs[i] else 0 := by
  rfl

/-- `maskedSum` agrees with `(maskSelect xs mask).sum` whenever `mask.length = xs.length`. -/
theorem sum_maskSelect_eq_maskedSum {xs : List ℕ} {mask : List Bool}
    (h : mask.length = xs.length) :
    (maskSelect xs mask).sum = maskedSum xs (fun i ↦ mask[i.1]'(h.symm ▸ i.2)) := by
  induction xs generalizing mask with
  | nil => simp [maskedSum, maskSelect]
  | cons a xs ih =>
    cases mask with
    | nil => simp at h
    | cons b bs =>
      have h' : bs.length = xs.length := by simpa using h
      simp only [maskedSum, List.length_cons, Fin.sum_univ_succ, List.getElem_cons_zero,
        List.getElem_cons_succ, Fin.val_zero, Fin.val_succ, maskSelect_cons, List.headD_cons,
        List.tail_cons, List.sum_append]
      have hih := ih h'
      simp only [maskedSum] at hih
      rw [hih]
      cases b <;> simp

/-- **Generalized Subset Sum (`GSSP`)**:
`∃ x ∈ {0,1}^{|u|}, ∀ y ∈ {0,1}^{|v|}, u · x + v · y ≠ T`. -/
def GeneralizedSubsetSum : Set GeneralizedSubsetSumInstance :=
  {inst | ∃ x : Fin inst.existNums.length → Bool,
    ∀ y : Fin inst.univNums.length → Bool,
      maskedSum inst.existNums x + maskedSum inst.univNums y ≠ inst.target}

/-- Membership characterization for `GeneralizedSubsetSum`. -/
theorem mem_GeneralizedSubsetSum_iff {inst : GeneralizedSubsetSumInstance} :
    inst ∈ GeneralizedSubsetSum ↔
      ∃ x : Fin inst.existNums.length → Bool,
        ∀ y : Fin inst.univNums.length → Bool,
          maskedSum inst.existNums x + maskedSum inst.univNums y ≠ inst.target :=
  Iff.rfl

/-- **Strictly positive Generalized Subset Sum (`PosGSSP`)**: `GSSP` restricted to nonempty lists
of strictly positive natural numbers and a strictly positive target. -/
def PosGeneralizedSubsetSum : Set GeneralizedSubsetSumInstance :=
  {inst | inst.existNums ≠ [] ∧ inst.univNums ≠ [] ∧
    (∀ a ∈ inst.existNums, 0 < a) ∧ (∀ b ∈ inst.univNums, 0 < b) ∧ 0 < inst.target ∧
    inst ∈ GeneralizedSubsetSum}

/-- Membership characterization for `PosGeneralizedSubsetSum`. -/
theorem mem_PosGeneralizedSubsetSum_iff {inst : GeneralizedSubsetSumInstance} :
    inst ∈ PosGeneralizedSubsetSum ↔
      inst.existNums ≠ [] ∧ inst.univNums ≠ [] ∧
      (∀ a ∈ inst.existNums, 0 < a) ∧ (∀ b ∈ inst.univNums, 0 < b) ∧ 0 < inst.target ∧
      inst ∈ GeneralizedSubsetSum :=
  Iff.rfl

/-- **`GeneralizedSubsetSum` belongs to `Σ₂ᴾ`.** -/
theorem GeneralizedSubsetSum_mem_SigmaP :
    GeneralizedSubsetSum ∈ SigmaP 2 encGeneralizedSubsetSum := by
  have hpred :
      {q : (GeneralizedSubsetSumInstance × List Bool) × List Bool |
        (maskSelect q.1.1.existNums q.1.2).sum + (maskSelect q.1.1.univNums q.2).sum ≠
          q.1.1.target} ∈ P (encPair (encPair encGeneralizedSubsetSum encBits) encBits) := by
    refine ⟨fun q ↦
      !decide ((maskSelect q.1.1.existNums q.1.2).sum +
        (maskSelect q.1.1.univNums q.2).sum = q.1.1.target), ?_, fun q ↦ by simp⟩
    fun_prop
  have hinner := mem_PiP_of_forall_length (k := 1) le_rfl
    (N := fun p : GeneralizedSubsetSumInstance × List Bool ↦ p.1.univNums.length)
    (by fun_prop)
    (PiP_mono (Nat.zero_le 1) (PiP_zero ▸ hpred))
  have hexists := mem_SigmaP_of_exists_length (k := 2) (by omega)
    (N := fun inst : GeneralizedSubsetSumInstance ↦ inst.existNums.length)
    (by fun_prop)
    (PiP_subset_SigmaP_succ 1 hinner)
  refine PolyTimeReducible.mem_SigmaP (k := 2) ⟨id, .id', fun inst ↦ ?_⟩ hexists
  simp only [id, Set.mem_ofPred_eq, mem_GeneralizedSubsetSum_iff]
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨List.ofFn x, List.length_ofFn, fun w hw ↦ ?_⟩
    rw [sum_maskSelect_eq_maskedSum List.length_ofFn, sum_maskSelect_eq_maskedSum hw]
    simpa only [List.getElem_ofFn] using hx (fun j ↦ w[j.1]'(hw.symm ▸ j.2))
  · rintro ⟨u, hu, h⟩
    refine ⟨fun i ↦ u[i.1]'(hu.symm ▸ i.2), fun y ↦ ?_⟩
    have := h (List.ofFn y) List.length_ofFn
    rw [sum_maskSelect_eq_maskedSum hu, sum_maskSelect_eq_maskedSum List.length_ofFn] at this
    simpa only [List.getElem_ofFn] using this

/-- **`PosGeneralizedSubsetSum` belongs to `Σ₂ᴾ`.** -/
theorem PosGeneralizedSubsetSum_mem_SigmaP :
    PosGeneralizedSubsetSum ∈ SigmaP 2 encGeneralizedSubsetSum := by
  let isPos (inst : GeneralizedSubsetSumInstance) : Bool :=
    !inst.existNums.isEmpty && !inst.univNums.isEmpty &&
    (inst.existNums.all fun a ↦ decide (0 < a)) &&
    (inst.univNums.all fun b ↦ decide (0 < b)) &&
    decide (0 < inst.target)
  have hisPos_iff (inst : GeneralizedSubsetSumInstance) :
      isPos inst = true ↔
        inst.existNums ≠ [] ∧ inst.univNums ≠ [] ∧
        (∀ a ∈ inst.existNums, 0 < a) ∧ (∀ b ∈ inst.univNums, 0 < b) ∧ 0 < inst.target := by
    simp [isPos, Bool.and_eq_true, List.all_eq_true, List.isEmpty_eq_false_iff, and_assoc]
  have hpred :
      {q : (GeneralizedSubsetSumInstance × List Bool) × List Bool |
        isPos q.1.1 = true ∧
        (maskSelect q.1.1.existNums q.1.2).sum + (maskSelect q.1.1.univNums q.2).sum ≠
          q.1.1.target} ∈ P (encPair (encPair encGeneralizedSubsetSum encBits) encBits) := by
    refine ⟨fun q ↦ isPos q.1.1 && !decide ((maskSelect q.1.1.existNums q.1.2).sum +
        (maskSelect q.1.1.univNums q.2).sum = q.1.1.target), ?_, fun q ↦ by simp⟩
    dsimp only [isPos]
    fun_prop
  have hinner := mem_PiP_of_forall_length (k := 1) le_rfl
    (N := fun p : GeneralizedSubsetSumInstance × List Bool ↦ p.1.univNums.length)
    (by fun_prop)
    (PiP_mono (Nat.zero_le 1) (PiP_zero ▸ hpred))
  have hexists := mem_SigmaP_of_exists_length (k := 2) (by omega)
    (N := fun inst : GeneralizedSubsetSumInstance ↦ inst.existNums.length)
    (by fun_prop)
    (PiP_subset_SigmaP_succ 1 hinner)
  refine PolyTimeReducible.mem_SigmaP (k := 2) ⟨id, .id', fun inst ↦ ?_⟩ hexists
  simp only [id, Set.mem_ofPred_eq, mem_PosGeneralizedSubsetSum_iff, mem_GeneralizedSubsetSum_iff]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, x, hx⟩
    have hp : isPos inst = true := (hisPos_iff inst).mpr ⟨h1, h2, h3, h4, h5⟩
    refine ⟨List.ofFn x, List.length_ofFn, fun w hw ↦ ⟨hp, ?_⟩⟩
    rw [sum_maskSelect_eq_maskedSum List.length_ofFn, sum_maskSelect_eq_maskedSum hw]
    simpa only [List.getElem_ofFn] using hx (fun j ↦ w[j.1]'(hw.symm ▸ j.2))
  · rintro ⟨u, hu, h⟩
    have ⟨hp, _⟩ := h (List.replicate inst.univNums.length false) (by simp)
    obtain ⟨h1, h2, h3, h4, h5⟩ := (hisPos_iff inst).mp hp
    refine ⟨h1, h2, h3, h4, h5, fun i ↦ u[i.1]'(hu.symm ▸ i.2), fun y ↦ ?_⟩
    have := (h (List.ofFn y) List.length_ofFn).2
    rw [sum_maskSelect_eq_maskedSum hu, sum_maskSelect_eq_maskedSum List.length_ofFn] at this
    simpa only [List.getElem_ofFn] using this

namespace GSSP

open Finset

/-- Combined duplicate-free variable list with `inst.existVars` as its prefix of length `p`. -/
def allVars (inst : Sigma2CNFInstance) : List ℕ :=
  inst.existVars ++ inst.formula.distinctVars.filter fun v ↦ !inst.existVars.any (fun e ↦ e == v)

/-- Semantic equation for `allVars`. -/
theorem allVars_eq (inst : Sigma2CNFInstance) :
    allVars inst = inst.existVars ++
      inst.formula.distinctVars.filter fun v ↦ !inst.existVars.any (fun e ↦ e == v) := by
  rfl

/-- Whether clause `j` of `inst.formula` contains the literal of sign `b` for variable `i` of
`allVars inst`. -/
def coversVar (inst : Sigma2CNFInstance) (i : ℕ) (b : Bool) (j : ℕ) : Bool :=
  (inst.formula.getD j []).any fun l ↦ (allVars inst).idxOf l.1 == i && l.2 == b

/-- Clause digit positions (shifted above `(allVars inst).length`) for literal `(i, b)`. -/
def clauseDigits (inst : Sigma2CNFInstance) (i : ℕ) (b : Bool) : List ℕ :=
  ((List.range inst.formula.length).filter (coversVar inst i b)).map
    ((allVars inst).length + ·)

/-- Positive existential numbers `u` for a nonempty-`existVars` instance: `u_i = 8 ^ i`. -/
def existBlock (inst : Sigma2CNFInstance) : List ℕ :=
  (List.range inst.existVars.length).map (8 ^ ·)

/-- Positive universal numbers `v` for a nonempty-`existVars` instance:
existential literal numbers (`8^i` for `true`, `2 * 8^i` for `false`), universal literal numbers
(`8^i` for both signs), and two slack numbers `8^(n + j)` per clause. -/
def univBlock (inst : Sigma2CNFInstance) : List ℕ :=
  let p := inst.existVars.length
  let n := (allVars inst).length
  ((List.range n).flatMap fun i ↦
      [8 ^ i + ThreeSAT.octal (clauseDigits inst i true),
       (if decide (i < p) then 2 else 1) * 8 ^ i + ThreeSAT.octal (clauseDigits inst i false)]) ++
    ((List.range inst.formula.length).flatMap fun j ↦ [8 ^ (n + j), 8 ^ (n + j)])

/-- Base-8 target for a nonempty-`existVars` instance: digit `2` at `i < p`, digit `1` at
`p ≤ i < n`, and digit `3` at `n + j` (`j < m`). -/
def targetBlock (inst : Sigma2CNFInstance) : ℕ :=
  let p := inst.existVars.length
  let n := (allVars inst).length
  ((List.range n).map fun i ↦ (if decide (i < p) then 2 else 1) * 8 ^ i).sum +
    ((List.range inst.formula.length).map fun j ↦ 3 * 8 ^ (n + j)).sum

/-- Polynomial-time reduction from `Sigma2ThreeCNF` to `PosGeneralizedSubsetSum` (and hence also
`GeneralizedSubsetSum`). -/
def fromSigma2ThreeCNF (inst : Sigma2CNFInstance) : GeneralizedSubsetSumInstance :=
  if inst.existVars.all (fun v ↦ decide (inst.existVars.count v ≤ 1)) &&
      (inst.formula.all fun c ↦ decide (c.length ≤ 3)) then
    if inst.existVars.isEmpty then
      if inst.formula.isEmpty then ⟨[1], [1], 1⟩
      else ⟨[1], 1 :: (ThreeSAT.digitNumbers inst.formula).map (8 * ·),
            1 + 8 * ThreeSAT.digitTarget inst.formula⟩
    else
      ⟨existBlock inst, univBlock inst, targetBlock inst⟩
  else
    ⟨[1], [1], 1⟩

@[local fun_prop]
private theorem eight_pow_poly : ComputableInPolyTime (fun p : ℕ ↦ 8 ^ p) encUnary encNat := by
  fun_prop

@[fun_prop]
theorem computableInPolyTime_allVars :
    ComputableInPolyTime allVars encSigma2CNF (encList encNat) := by
  unfold allVars
  fun_prop

@[fun_prop]
theorem computableInPolyTime_coversVar :
    ComputableInPolyTime
      (fun p : ((Sigma2CNFInstance × ℕ) × Bool) × ℕ ↦ coversVar p.1.1.1 p.1.1.2 p.1.2 p.2)
      (encPair (encPair (encPair encSigma2CNF encUnary) encBool) encUnary) encBool := by
  unfold coversVar
  fun_prop

@[fun_prop]
theorem computableInPolyTime_clauseDigits :
    ComputableInPolyTime (fun p : (Sigma2CNFInstance × ℕ) × Bool ↦ clauseDigits p.1.1 p.1.2 p.2)
      (encPair (encPair encSigma2CNF encUnary) encBool) (encList encUnary) := by
  unfold clauseDigits
  fun_prop

@[fun_prop]
theorem computableInPolyTime_clauseDigits' {α : Type} {input : α ↪ List Bool}
    {inst : α → Sigma2CNFInstance} {i : α → ℕ} {b : α → Bool}
    (hinst : ComputableInPolyTime inst input encSigma2CNF)
    (hi : ComputableInPolyTime i input encUnary)
    (hb : ComputableInPolyTime b input encBool) :
    ComputableInPolyTime (fun a ↦ clauseDigits (inst a) (i a) (b a)) input (encList encUnary) :=
  computableInPolyTime_clauseDigits.comp ((hinst.prod hi).prod hb)

@[fun_prop]
theorem computableInPolyTime_existBlock :
    ComputableInPolyTime existBlock encSigma2CNF (encList encNat) := by
  unfold existBlock
  fun_prop

@[fun_prop]
theorem computableInPolyTime_univBlock :
    ComputableInPolyTime univBlock encSigma2CNF (encList encNat) := by
  unfold univBlock
  apply listAppend' <;> exact flatMapWithInput (by fun_prop) (by fun_prop)

@[fun_prop]
theorem computableInPolyTime_targetBlock :
    ComputableInPolyTime targetBlock encSigma2CNF encNat := by
  unfold targetBlock
  fun_prop

/-- The reduction `fromSigma2ThreeCNF` is computable in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_fromSigma2ThreeCNF :
    ComputableInPolyTime fromSigma2ThreeCNF encSigma2CNF encGeneralizedSubsetSum := by
  unfold fromSigma2ThreeCNF
  fun_prop

private theorem nodup_allVars {inst : Sigma2CNFInstance} (hn : inst.existVars.Nodup) :
    (allVars inst).Nodup := by
  refine List.Nodup.append hn ((CNF.nodup_distinctVars inst.formula).filter _) ?_
  intro v hv hf
  simp only [List.mem_filter, Bool.not_eq_true', List.any_eq_false, beq_iff_eq] at hf
  exact hf.2 v hv rfl

private theorem mem_allVars_of_mem_clause {inst : Sigma2CNFInstance} {j : ℕ} {l : Literal ℕ}
    (hl : l ∈ inst.formula.getD j []) : l.1 ∈ allVars inst := by
  have hj : j < inst.formula.length := by
    by_contra h
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_lt h)] at hl
  have hdv : l.1 ∈ inst.formula.distinctVars :=
    CNF.mem_distinctVars.mpr (List.mem_map.mpr ⟨l, List.mem_flatten.mpr
      ⟨_, List.getD_mem [] hj, hl⟩, rfl⟩)
  by_cases he : l.1 ∈ inst.existVars
  · exact List.mem_append_left _ he
  · refine List.mem_append_right _ (List.mem_filter.mpr ⟨hdv, ?_⟩)
    simp only [Bool.not_eq_true', List.any_eq_false, beq_iff_eq]
    intro e he' hEq
    exact he (hEq ▸ he')

private theorem fixed_no_not_mem : (⟨[1], [1], 1⟩ : GeneralizedSubsetSumInstance) ∉
    GeneralizedSubsetSum := by
  rw [mem_GeneralizedSubsetSum_iff]
  rintro ⟨x, hx⟩
  have h0 := hx (fun _ ↦ !(x 0))
  have hsum : maskedSum [1] x + maskedSum [1] (fun _ ↦ !(x 0)) = 1 := by
    simp only [maskedSum, List.length_singleton, Fin.sum_univ_one]
    cases x 0 <;> simp
  exact h0 hsum

private theorem positive_of_fromSigma2ThreeCNF (inst : Sigma2CNFInstance) :
    let g := fromSigma2ThreeCNF inst
    g.existNums ≠ [] ∧ g.univNums ≠ [] ∧
    (∀ a ∈ g.existNums, 0 < a) ∧ (∀ b ∈ g.univNums, 0 < b) ∧ 0 < g.target := by
  dsimp only [fromSigma2ThreeCNF]
  split_ifs with hvalid hempty hformEmpty
  · exact ⟨by simp, by simp, by simp, by simp, by simp⟩
  · refine ⟨by simp, by simp, by simp, ?_, by dsimp; omega⟩
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb'
    · omega
    · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hb'
      have ha_pos : 0 < a := by
        simp only [ThreeSAT.digitNumbers, List.mem_append, List.mem_flatMap, List.mem_range,
          List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with ⟨i, -, rfl | rfl⟩ | ⟨j, -, rfl | rfl⟩
        · exact Nat.lt_of_lt_of_le (by positivity)
            (by simp [ThreeSAT.octal, ThreeSAT.literalDigits] :
              8 ^ i ≤ ThreeSAT.octal (ThreeSAT.literalDigits inst.formula i true))
        · exact Nat.lt_of_lt_of_le (by positivity)
            (by simp [ThreeSAT.octal, ThreeSAT.literalDigits] :
              8 ^ i ≤ ThreeSAT.octal (ThreeSAT.literalDigits inst.formula i false))
        · positivity
        · positivity
      omega
  · have hp : 0 < inst.existVars.length :=
      List.length_pos_of_ne_nil (List.isEmpty_eq_false_iff.mp (Bool.eq_false_iff.mpr hempty))
    have hn : 0 < (allVars inst).length := Nat.lt_of_lt_of_le hp (by simp [allVars])
    refine ⟨by simp only [existBlock, ne_eq, List.map_eq_nil_iff, List.range_eq_nil]; omega,
      fun h ↦ by
        simp only [univBlock, List.append_eq_nil_iff, List.flatMap_eq_nil_iff, List.mem_range] at h
        exact absurd (h.1 0 hn) (by simp),
      fun a ha ↦ by obtain ⟨i, -, rfl⟩ := List.mem_map.mp ha; positivity, ?_, ?_⟩
    · intro b hb
      simp only [univBlock, List.mem_append, List.mem_flatMap, List.mem_range, List.mem_cons,
        List.not_mem_nil, or_false] at hb
      rcases hb with ⟨i, -, rfl | rfl⟩ | ⟨j, -, rfl | rfl⟩ <;> positivity
    · have hmem : (if decide (0 < inst.existVars.length) then 2 else 1) * 8 ^ 0 ∈
          (List.range (allVars inst).length).map
            (fun i ↦ (if decide (i < inst.existVars.length) then 2 else 1) * 8 ^ i) :=
        List.mem_map.mpr ⟨0, List.mem_range.mpr hn, rfl⟩
      have hge := List.le_sum_of_mem hmem
      simp only [hp, decide_true, ↓reduceIte, pow_zero, mul_one] at hge
      dsimp only [targetBlock] at hge ⊢; omega
  · exact ⟨by simp, by simp, by simp, by simp, by simp⟩

/-- `∃ y, maskedSum xs y = S` iff some sublist of `xs` sums to `S`. -/
private theorem exists_maskedSum_eq_iff_sublist (xs : List ℕ) (S : ℕ) :
    (∃ y : Fin xs.length → Bool, maskedSum xs y = S) ↔ ∃ l, l <+ xs ∧ l.sum = S := by
  induction xs generalizing S with
  | nil =>
    exact ⟨fun ⟨_, h⟩ ↦ ⟨[], List.Sublist.slnil, h⟩,
      fun ⟨l, hl, h⟩ ↦ ⟨Fin.elim0, by obtain rfl := List.sublist_nil.mp hl; simp [maskedSum, ← h]⟩⟩
  | cons a xs ih =>
    constructor
    · rintro ⟨y, hy⟩
      simp only [maskedSum, List.length_cons, Fin.sum_univ_succ] at hy
      obtain ⟨l, hl, hlsum⟩ := (ih _).mp ⟨fun i ↦ y i.succ, rfl⟩
      cases hb : y 0
      · simp only [hb, Bool.false_eq_true, ↓reduceIte, zero_add] at hy
        exact ⟨l, hl.cons a, hlsum.trans hy⟩
      · simp only [hb, ↓reduceIte] at hy
        exact ⟨a :: l, hl.cons_cons a, by simp [hlsum]; simpa [maskedSum] using hy⟩
    · rintro ⟨l, hl, rfl⟩
      cases hl with
      | cons _ hl' =>
        obtain ⟨y, hy⟩ := (ih _).mpr ⟨_, hl', rfl⟩
        exact ⟨Fin.cons false y, by simpa [maskedSum, Fin.sum_univ_succ] using hy⟩
      | cons_cons _ hl' =>
        obtain ⟨y, hy⟩ := (ih _).mpr ⟨_, hl', rfl⟩
        exact ⟨Fin.cons true y, by simpa [maskedSum, Fin.sum_univ_succ] using hy⟩

/-- For a duplicate-free list `ys`, `∃ y, maskedSum (ys.map f) y = S` iff some `F ⊆ ys.toFinset`
has `∑ z ∈ F, f z = S`. -/
private theorem exists_maskedSum_map_eq_iff {ι : Type*} [DecidableEq ι] {ys : List ι}
    (hys : ys.Nodup) (f : ι → ℕ) (S : ℕ) :
    (∃ y : Fin (ys.map f).length → Bool, maskedSum (ys.map f) y = S) ↔
      ∃ F ⊆ ys.toFinset, ∑ z ∈ F, f z = S := by
  rw [exists_maskedSum_eq_iff_sublist]
  constructor
  · rintro ⟨s, hs, rfl⟩
    obtain ⟨zs, hzs, rfl⟩ := List.sublist_map_iff.mp hs
    exact ⟨zs.toFinset, fun x hx ↦ List.mem_toFinset.mpr (hzs.subset (List.mem_toFinset.mp hx)),
      List.sum_toFinset _ (hys.sublist hzs)⟩
  · rintro ⟨F, hF, rfl⟩
    refine ⟨(ys.filter (· ∈ F)).map f, List.filter_sublist.map f, ?_⟩
    rw [← List.sum_toFinset _ (hys.filter _)]
    refine congrArg (·.sum f) (Finset.ext fun x ↦ ?_)
    simpa using fun hx ↦ List.mem_toFinset.mp (hF hx)

private abbrev GSSPItem : Type := (ℕ × Bool) ⊕ (ℕ × Bool)

private def gsspItems (inst : Sigma2CNFInstance) : List GSSPItem :=
  ((List.range (allVars inst).length).flatMap fun i ↦ [.inl (i, true), .inl (i, false)]) ++
    ((List.range inst.formula.length).flatMap fun j ↦ [.inr (j, true), .inr (j, false)])

private def univItemVal (inst : Sigma2CNFInstance) : GSSPItem → ℕ
  | .inl (i, true) => 8 ^ i + ThreeSAT.octal (clauseDigits inst i true)
  | .inl (i, false) =>
      (if decide (i < inst.existVars.length) then 2 else 1) * 8 ^ i +
        ThreeSAT.octal (clauseDigits inst i false)
  | .inr (j, _) => 8 ^ ((allVars inst).length + j)

private theorem univBlock_eq_map (inst : Sigma2CNFInstance) :
    univBlock inst = (gsspItems inst).map (univItemVal inst) := by
  simp [univBlock, gsspItems, List.map_flatMap, univItemVal]

private theorem nodup_gsspItems (inst : Sigma2CNFInstance) : (gsspItems inst).Nodup := by
  refine List.Nodup.append ?_ ?_ (by simp [List.disjoint_left]) <;>
    exact List.nodup_flatMap.mpr ⟨by simp, List.nodup_range.pairwise_of_forall_ne
      fun _ _ _ _ h ↦ by simpa [Function.onFun] using h.symm⟩

private def gsspItemSet (inst : Sigma2CNFInstance) : Finset GSSPItem :=
  (range (allVars inst).length ×ˢ univ).disjSum (range inst.formula.length ×ˢ univ)

private theorem toFinset_gsspItems (inst : Sigma2CNFInstance) :
    (gsspItems inst).toFinset = gsspItemSet inst := by
  ext z
  rcases z with ⟨_, _ | _⟩ | ⟨_, _ | _⟩ <;> simp [gsspItems, gsspItemSet]

private theorem coversVar_eq_true_iff {inst : Sigma2CNFInstance} {i : ℕ} {b : Bool} {j : ℕ} :
    coversVar inst i b j = true ↔
      ∃ l ∈ inst.formula.getD j [], (allVars inst).idxOf l.1 = i ∧ l.2 = b := by
  simp [coversVar]

private theorem card_filter_coversVar_le {inst : Sigma2CNFInstance} (A : Finset (ℕ × Bool))
    (j : ℕ) : #{a ∈ A | coversVar inst a.1 a.2 j} ≤ (inst.formula.getD j []).length := by
  classical
  calc #{a ∈ A | coversVar inst a.1 a.2 j}
      ≤ #(((inst.formula.getD j []).map fun l ↦ ((allVars inst).idxOf l.1, l.2)).toFinset) := by
        refine card_le_card fun a ha ↦ ?_
        obtain ⟨l, hl, hi, hb⟩ := coversVar_eq_true_iff.mp (mem_filter.mp ha).2
        exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨l, hl, by rw [hi, hb]⟩)
    _ ≤ _ := (List.toFinset_card_le _).trans (List.length_map ..).le

private theorem card_filter_fst_le_two (A : Finset (ℕ × Bool)) (i : ℕ) :
    #{a ∈ A | a.1 = i} ≤ 2 := by
  calc #{a ∈ A | a.1 = i} ≤ #({(i, true), (i, false)} : Finset (ℕ × Bool)) :=
        card_le_card fun a ha ↦ by
          obtain ⟨a₁, a₂⟩ := a
          obtain rfl : a₁ = i := (mem_filter.mp ha).2
          cases a₂ <;> simp
    _ ≤ 2 := card_le_two

private theorem octal_clauseDigits_eq_sum {inst : Sigma2CNFInstance} {i : ℕ} {b : Bool} :
    ThreeSAT.octal (clauseDigits inst i b) =
      ∑ j ∈ (range inst.formula.length).filter (fun j ↦ coversVar inst i b j = true),
        8 ^ ((allVars inst).length + j) := by
  classical
  have hnd : (clauseDigits inst i b).Nodup :=
    ((List.nodup_range).filter _).map (fun _ _ h ↦ Nat.add_left_cancel h)
  rw [ThreeSAT.octal, ← List.sum_toFinset _ hnd]
  have hset : (clauseDigits inst i b).toFinset =
      ((range inst.formula.length).filter (fun j ↦ coversVar inst i b j = true)).image
        ((allVars inst).length + ·) := by
    ext r
    simp [clauseDigits]
  rw [hset, Finset.sum_image (fun _ _ _ _ h ↦ Nat.add_left_cancel h)]

private theorem sum_univItemVal_eq {inst : Sigma2CNFInstance}
    {A B : Finset (ℕ × Bool)}
    (hA : A ⊆ range (allVars inst).length ×ˢ univ)
    (hB : B ⊆ range inst.formula.length ×ˢ univ) :
    ∑ z ∈ A.disjSum B, univItemVal inst z =
      ∑ r ∈ range ((allVars inst).length + inst.formula.length),
        (if r < (allVars inst).length then
          (if (r, true) ∈ A then 1 else 0) +
            (if (r, false) ∈ A then (if r < inst.existVars.length then 2 else 1) else 0)
         else
          #{a ∈ A | coversVar inst a.1 a.2 (r - (allVars inst).length)} +
            #{c ∈ B | c.1 = r - (allVars inst).length}) * 8 ^ r := by
  classical
  let n := (allVars inst).length
  let m := inst.formula.length
  let p := inst.existVars.length
  rw [sum_disjSum, sum_range_add]
  have hA_split : ∑ a ∈ A, univItemVal inst (.inl a) =
      (∑ i ∈ range n,
        ((if (i, true) ∈ A then 1 else 0) +
          (if (i, false) ∈ A then (if i < p then 2 else 1) else 0)) * 8 ^ i) +
      (∑ j ∈ range m, #{a ∈ A | coversVar inst a.1 a.2 j} * 8 ^ (n + j)) := by
    have h1 : ∀ a ∈ A, univItemVal inst (.inl a) =
        ((if a.2 then 1 else (if a.1 < p then 2 else 1)) * 8 ^ a.1) +
          ∑ j ∈ (range m).filter (fun j ↦ coversVar inst a.1 a.2 j = true), 8 ^ (n + j) := by
      intro ⟨i, b⟩ _
      cases b <;> simp [univItemVal, octal_clauseDigits_eq_sum, p, n, m]
    rw [sum_congr rfl h1, sum_add_distrib]
    congr 1
    · have hvar : ∀ i ∈ range n,
          ((if (i, true) ∈ A then 1 else 0) +
            (if (i, false) ∈ A then (if i < p then 2 else 1) else 0)) * 8 ^ i =
          ∑ a ∈ A, if a.1 = i then (if a.2 then 1 else (if a.1 < p then 2 else 1)) * 8 ^ a.1
            else 0 := by
        intro i _
        rw [← sum_filter]
        have hfil : A.filter (fun a ↦ a.1 = i) =
            ({(i, true), (i, false)} : Finset (ℕ × Bool)).filter (· ∈ A) := by
          ext ⟨a₁, a₂⟩
          simp only [mem_filter, mem_insert, mem_singleton, Prod.mk.injEq]
          constructor
          · rintro ⟨hA, rfl⟩; cases a₂ <;> simp [hA]
          · rintro ⟨⟨rfl, rfl⟩ | ⟨rfl, rfl⟩, hA⟩ <;> exact ⟨hA, rfl⟩
        rw [hfil, sum_filter, sum_pair (by simp)]
        by_cases ht : (i, true) ∈ A <;> by_cases hf : (i, false) ∈ A <;>
          simp [ht, hf, add_mul]
      rw [sum_congr rfl hvar, sum_comm]
      refine sum_congr rfl fun a ha ↦ ?_
      have ha1 : a.1 ∈ range n := (mem_product.mp (hA ha)).1
      simp [ha1]
    · have hcl : ∀ a ∈ A,
          ∑ j ∈ (range m).filter (fun j ↦ coversVar inst a.1 a.2 j = true), 8 ^ (n + j) =
          ∑ j ∈ range m, if coversVar inst a.1 a.2 j = true then 8 ^ (n + j) else 0 := by
        intro a _; rw [sum_filter]
      rw [sum_congr rfl hcl, sum_comm]
      refine sum_congr rfl fun j _ ↦ ?_
      rw [← sum_filter, sum_const, smul_eq_mul]
  have hB_split : ∑ c ∈ B, univItemVal inst (.inr c) =
      ∑ j ∈ range m, #{c ∈ B | c.1 = j} * 8 ^ (n + j) := by
    have h1 : ∀ c ∈ B, univItemVal inst (.inr c) =
        ∑ j ∈ range m, if c.1 = j then 8 ^ (n + j) else 0 := by
      intro c hc
      have hc1 : c.1 ∈ range m := (mem_product.mp (hB hc)).1
      simp [univItemVal, hc1, n]
    rw [sum_congr rfl h1, sum_comm]
    refine sum_congr rfl fun j _ ↦ ?_
    rw [← sum_filter, sum_const, smul_eq_mul]
  rw [hA_split, hB_split, add_assoc, ← sum_add_distrib]
  congr 1
  · refine sum_congr rfl fun i hi ↦ ?_
    simp [mem_range.mp hi, p]
  · refine sum_congr rfl fun j _ ↦ ?_
    have hnot : ¬ (n + j < n) := by omega
    simp [hnot, add_mul, n]

private theorem length_existBlock (inst : Sigma2CNFInstance) :
    (existBlock inst).length = inst.existVars.length := by
  simp [existBlock]

private theorem sum_map_range_eq_sum_range (n : ℕ) (f : ℕ → ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, List.map_singleton,
      List.sum_singleton, ih, Finset.sum_range_succ]

private theorem maskedSum_existBlock_eq {inst : Sigma2CNFInstance}
    (x : Fin (existBlock inst).length → Bool) :
    maskedSum (existBlock inst) x =
      ∑ r ∈ range ((allVars inst).length + inst.formula.length),
        (if h : r < inst.existVars.length then
          (x ⟨r, (length_existBlock inst).symm ▸ h⟩).toNat else 0) * 8 ^ r := by
  let p := inst.existVars.length
  let n := (allVars inst).length
  let m := inst.formula.length
  have hp_le : p ≤ n := by simp [p, n, allVars]
  have hlen : (existBlock inst).length = p := length_existBlock inst
  rw [sum_range_add]
  have htail : ∑ j ∈ range m,
      (if h : n + j < p then (x ⟨n + j, (length_existBlock inst).symm ▸ h⟩).toNat else 0) *
        8 ^ (n + j) = 0 := by
    refine sum_eq_zero fun j _ ↦ ?_
    have : ¬ (n + j < p) := by omega
    simp [this]
  rw [htail, add_zero]
  have hnp : (allVars inst).length = p + (n - p) := by omega
  rw [hnp, sum_range_add]
  have hmid : ∑ k ∈ range (n - p),
      (if h : p + k < p then (x ⟨p + k, (length_existBlock inst).symm ▸ h⟩).toNat else 0) *
        8 ^ (p + k) = 0 := by
    refine sum_eq_zero fun k _ ↦ ?_
    have : ¬ (p + k < p) := by omega
    simp [this]
  rw [hmid, add_zero]
  simp only [maskedSum]
  have h1 : (∑ i : Fin (existBlock inst).length, if x i then (existBlock inst)[i] else 0) =
      ∑ i : Fin (existBlock inst).length,
        if h : (i : ℕ) < (existBlock inst).length then
          if x ⟨i, h⟩ then (existBlock inst)[(i : ℕ)] else 0 else 0 :=
    sum_congr rfl fun i _ ↦ by simp [i.2]
  rw [h1, Fin.sum_univ_eq_sum_range (fun i ↦ if h : i < (existBlock inst).length then
    if x ⟨i, h⟩ then (existBlock inst)[i] else 0 else 0)]
  rw [show Finset.range (existBlock inst).length = Finset.range p from congrArg Finset.range hlen]
  refine sum_congr rfl fun i hi ↦ ?_
  have hi' : i < inst.existVars.length := mem_range.mp hi
  have hi'' : i < (existBlock inst).length := by omega
  have hget : (existBlock inst)[i] = 8 ^ i := by simp [existBlock]
  simp only [hi', hi'', ↓reduceDIte, hget]
  cases x ⟨i, hi''⟩ <;> simp

private theorem targetBlock_eq (inst : Sigma2CNFInstance) :
    targetBlock inst =
      ∑ r ∈ range ((allVars inst).length + inst.formula.length),
        (if r < (allVars inst).length then
          (if r < inst.existVars.length then 2 else 1)
         else 3) * 8 ^ r := by
  rw [sum_range_add, targetBlock, sum_map_range_eq_sum_range, sum_map_range_eq_sum_range]
  congr 1
  · refine sum_congr rfl fun r hr ↦ ?_
    simp [mem_range.mp hr]
  · refine sum_congr rfl fun j _ ↦ ?_
    have : ¬ ((allVars inst).length + j < (allVars inst).length) := by omega
    simp [this]

/-- **Correctness of the `Sigma2ThreeCNF → PosGeneralizedSubsetSum` reduction.** -/
private theorem match_existBlock {inst : Sigma2CNFInstance}
    (hn : inst.existVars.Nodup) (hw : ∀ c ∈ inst.formula, c.length ≤ 3)
    (x : Fin (existBlock inst).length → Bool) :
    (∃ y : Fin (univBlock inst).length → Bool,
      maskedSum (existBlock inst) x + maskedSum (univBlock inst) y = targetBlock inst) ↔
    (∃ σ : ℕ → Bool,
      (∀ i : Fin inst.existVars.length,
        σ inst.existVars[i] = x ⟨i.1, (length_existBlock inst).symm ▸ i.2⟩) ∧
      inst.formula.eval σ = true) := by
  classical
  let p := inst.existVars.length
  let n := (allVars inst).length
  let m := inst.formula.length
  have hp_le : p ≤ n := by simp [p, n, allVars]
  have hnd_V : (allVars inst).Nodup := nodup_allVars hn
  have hlen_u : (existBlock inst).length = p := length_existBlock inst
  have h_sub : (∃ y : Fin (univBlock inst).length → Bool,
        maskedSum (existBlock inst) x + maskedSum (univBlock inst) y = targetBlock inst) ↔
      ∃ A ⊆ range n ×ˢ (univ : Finset Bool), ∃ B ⊆ range m ×ˢ (univ : Finset Bool),
        (∀ i (hi : i < p), (x ⟨i, hlen_u.symm ▸ hi⟩).toNat +
          (if (i, true) ∈ A then 1 else 0) + (if (i, false) ∈ A then 2 else 0) = 2) ∧
        (∀ i, p ≤ i → i < n →
          (if (i, true) ∈ A then 1 else 0) + (if (i, false) ∈ A then 1 else 0) = 1) ∧
        (∀ j < m, #{a ∈ A | coversVar inst a.1 a.2 j} + #{c ∈ B | c.1 = j} = 3) := by
    have hle_xt : maskedSum (existBlock inst) x ≤ targetBlock inst := by
      rw [maskedSum_existBlock_eq, targetBlock_eq]
      refine Finset.sum_le_sum fun r _ ↦ Nat.mul_le_mul_right _ ?_
      by_cases hrn : r < (allVars inst).length
      · by_cases hrp : r < inst.existVars.length
        · simp only [hrp, ↓reduceDIte, hrn, ↓reduceIte]
          exact (Bool.toNat_le _).trans (by omega)
        · simp only [hrp, ↓reduceDIte, hrn, ↓reduceIte]; omega
      · have hrp : ¬ (r < inst.existVars.length) := by omega
        simp only [hrp, ↓reduceDIte, hrn, ↓reduceIte]; omega
    have hmap : (∃ y : Fin (univBlock inst).length → Bool,
        maskedSum (existBlock inst) x + maskedSum (univBlock inst) y = targetBlock inst) ↔
        ∃ F ⊆ gsspItemSet inst,
          maskedSum (existBlock inst) x + ∑ z ∈ F, univItemVal inst z = targetBlock inst := by
      have h1 : (∃ y : Fin (univBlock inst).length → Bool,
          maskedSum (existBlock inst) x + maskedSum (univBlock inst) y = targetBlock inst) ↔
          ∃ y : Fin (univBlock inst).length → Bool,
            maskedSum (univBlock inst) y = targetBlock inst - maskedSum (existBlock inst) x :=
        exists_congr fun _ ↦ ⟨fun h ↦ by omega, fun h ↦ by omega⟩
      rw [h1]
      have htmp : (∃ y : Fin (univBlock inst).length → Bool,
          maskedSum (univBlock inst) y = targetBlock inst - maskedSum (existBlock inst) x) ↔
          ∃ F ⊆ gsspItemSet inst,
            ∑ z ∈ F, univItemVal inst z = targetBlock inst - maskedSum (existBlock inst) x := by
        rw [← toFinset_gsspItems, univBlock_eq_map]
        exact exists_maskedSum_map_eq_iff (nodup_gsspItems inst) (univItemVal inst) _
      rw [htmp]
      exact exists_congr fun _ ↦ and_congr_right fun _ ↦ ⟨fun h ↦ by omega, fun h ↦ by omega⟩
    rw [hmap]
    have hT_lt : ∀ r < n + m,
        (if r < n then (if r < p then 2 else 1) else 3) < 8 := fun r _ ↦ by
      split_ifs <;> omega
    constructor
    · rintro ⟨F, hF, hsum⟩
      obtain ⟨hA, hB⟩ := subset_disjSum.mp hF
      rw [← toLeft_disjSum_toRight (u := F), maskedSum_existBlock_eq,
        sum_univItemVal_eq hA hB, ← Finset.sum_add_distrib, targetBlock_eq] at hsum
      simp_rw [← add_mul] at hsum
      have hD_lt : ∀ r < n + m,
          ((if h : r < p then (x ⟨r, hlen_u.symm ▸ h⟩).toNat else 0) +
            (if r < n then
              (if (r, true) ∈ F.toLeft then 1 else 0) +
                (if (r, false) ∈ F.toLeft then (if r < p then 2 else 1) else 0)
             else
              #{a ∈ F.toLeft | coversVar inst a.1 a.2 (r - n)} +
                #{c ∈ F.toRight | c.1 = r - n})) < 8 := by
        intro r hr
        by_cases hrn : r < n
        · by_cases hrp : r < p
          · have := Bool.toNat_le (x ⟨r, hlen_u.symm ▸ hrp⟩)
            simp only [hrp, ↓reduceDIte, hrn, ↓reduceIte]
            split_ifs <;> omega
          · simp only [hrp, ↓reduceDIte, hrn, ↓reduceIte]
            split_ifs <;> omega
        · have hrp : ¬ (r < p) := by omega
          have hj : r - n < m := by omega
          have h1 := card_filter_coversVar_le (inst := inst) F.toLeft (r - n)
          have h2 := hw _ (List.getD_mem [] hj)
          have h3 := card_filter_fst_le_two F.toRight (r - n)
          simp only [hrp, ↓reduceDIte, hrn, ↓reduceIte]
          omega
      have hdig := (Nat.sum_range_mul_pow_inj hD_lt hT_lt).mp hsum
      refine ⟨F.toLeft, hA, F.toRight, hB, ?_, ?_, ?_⟩
      · intro i hi
        have := hdig i (by omega)
        have hin : i < n := by omega
        simpa [hi, hin, add_assoc] using this
      · intro i hpi hin
        have := hdig i (by omega)
        have hni : ¬ (i < p) := by omega
        simpa [hni, hin] using this
      · intro j hj
        have := hdig (n + j) (by omega)
        have hnp : ¬ (n + j < p) := by omega
        have hnn : ¬ (n + j < n) := by omega
        simpa [hnp, hnn] using this
    · rintro ⟨A, hA, B, hB, hE_dig, hU_dig, hC_dig⟩
      refine ⟨A.disjSum B, disjSum_mono hA hB, ?_⟩
      rw [maskedSum_existBlock_eq, sum_univItemVal_eq hA hB, ← Finset.sum_add_distrib,
        targetBlock_eq]
      simp_rw [← add_mul]
      refine Finset.sum_congr rfl fun r hr ↦ ?_
      have hr' := mem_range.mp hr
      congr 1
      by_cases hrn : r < (allVars inst).length
      · by_cases hrp : r < inst.existVars.length
        · simpa [hrp, hrn, add_assoc] using hE_dig r hrp
        · simpa [hrp, hrn] using hU_dig r (by omega) hrn
      · have hrp : ¬ (r < inst.existVars.length) := by omega
        have hj : r - (allVars inst).length < m := by omega
        simpa [hrp, hrn] using hC_dig (r - (allVars inst).length) hj
  rw [h_sub]
  constructor
  · rintro ⟨A, hA, B, -, hE_dig, hU_dig, hC_dig⟩
    have hnot : ∀ i, (i, false) ∈ A → (i, true) ∉ A := by
      intro i hf ht
      have hi : i < n := mem_range.mp (mem_product.mp (hA ht)).1
      by_cases hip : i < p
      · have h1 := hE_dig i hip
        have h2 := Bool.toNat_le (x ⟨i, hlen_u.symm ▸ hip⟩)
        simp only [ht, ↓reduceIte, hf] at h1
        omega
      · have h1 := hU_dig i (by omega) hi
        simp [ht, hf] at h1
    have hvar_ex : ∀ i (hi : i < p), ((i, true) ∈ A ↔ x ⟨i, hlen_u.symm ▸ hi⟩ = true) := by
      intro i hi
      have h := hE_dig i hi
      cases hb : x ⟨i, hlen_u.symm ▸ hi⟩ <;>
        by_cases ht : (i, true) ∈ A <;> by_cases hf : (i, false) ∈ A <;>
        simp [hb, ht, hf] at h ⊢
    refine ⟨fun v ↦ decide (((allVars inst).idxOf v, true) ∈ A), ?_, ?_⟩
    · intro i
      have hidx : (allVars inst).idxOf inst.existVars[i.1] = i.1 := by
        rw [allVars, List.idxOf_append_of_mem (List.getElem_mem i.2)]
        exact hn.idxOf_getElem i.1 i.2
      change decide (((allVars inst).idxOf inst.existVars[i.1], true) ∈ A) = _
      simp only [hidx]
      exact Bool.eq_iff_iff.mpr (by rw [decide_eq_true_iff, hvar_ex i.1 i.2])
    · refine (CNF.eval_eq_true_iff _ _).mpr fun c hc ↦ ?_
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hc
      have hpos : 0 < #{a ∈ A | coversVar inst a.1 a.2 j} := by
        have := hC_dig j hj
        have := card_filter_fst_le_two B j
        omega
      obtain ⟨⟨i, b⟩, ha⟩ := card_pos.mp hpos
      obtain ⟨l, hl, hi, hb⟩ := coversVar_eq_true_iff.mp (mem_filter.mp ha).2
      have hlj : l ∈ inst.formula[j] := by
        simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj] using hl
      refine (Clause.eval_eq_true_iff _ _).mpr ⟨l, hlj, ?_⟩
      cases b <;> simp [hi, hb, (mem_filter.mp ha).1, hnot i]
  · rintro ⟨σ, hσ, hsat⟩
    set b : ℕ → Bool := fun i ↦ σ ((allVars inst).getD i 0) with hb_def
    set A : Finset (ℕ × Bool) := (range n).image fun i ↦ (i, b i) with hA_def
    have hmemA : ∀ a, a ∈ A ↔ a.1 < n ∧ a.2 = b a.1 := by
      rintro ⟨i, c⟩
      simp only [hA_def, mem_image, mem_range, Prod.mk.injEq]
      exact ⟨fun ⟨i', hi', h1, h2⟩ ↦ ⟨h1 ▸ hi', h1 ▸ h2.symm⟩,
        fun ⟨hi, hc⟩ ↦ ⟨i, hi, rfl, hc.symm⟩⟩
    set cnt : ℕ → ℕ := fun j ↦ #{a ∈ A | coversVar inst a.1 a.2 j}
    set B : Finset (ℕ × Bool) := (range m ×ˢ univ).filter
      (fun c ↦ cnt c.1 + (!c.2).toNat ≤ 2) with hB_def
    refine ⟨A, fun a ha ↦ mem_product.mpr ⟨mem_range.mpr ((hmemA a).mp ha).1, mem_univ _⟩,
      B, filter_subset _ _, ?_, ?_, ?_⟩
    · intro i hi
      have hbi : b i = x ⟨i, hlen_u.symm ▸ hi⟩ := by
        have hget : (allVars inst).getD i 0 = inst.existVars[i] := by
          simp [allVars, List.getD_eq_getElem?_getD, List.getElem?_append_left hi,
            List.getElem?_eq_getElem hi]
        change σ ((allVars inst).getD i 0) = _
        rw [hget]; exact hσ ⟨i, hi⟩
      have hin : i < n := by omega
      cases hx : x ⟨i, hlen_u.symm ▸ hi⟩ <;> simp [hmemA, hin, hbi, hx]
    · intro i hpi hin
      cases hbi : b i <;> simp [hmemA, hin, hbi]
    · intro j hj
      have hle : cnt j ≤ 3 :=
        (card_filter_coversVar_le A j).trans (hw _ (List.getD_mem [] hj))
      have hpos : 1 ≤ cnt j := by
        obtain ⟨l, hl, hσl⟩ := (Clause.eval_eq_true_iff _ _).mp
          ((CNF.eval_eq_true_iff _ _).mp hsat _ (List.getD_mem [] hj))
        have hidx : (allVars inst).idxOf l.1 < n :=
          List.idxOf_lt_length_iff.mpr (mem_allVars_of_mem_clause hl)
        refine card_pos.mpr ⟨((allVars inst).idxOf l.1, l.2), mem_filter.mpr
          ⟨(hmemA _).mpr ⟨hidx, ?_⟩, coversVar_eq_true_iff.mpr ⟨l, hl, rfl, rfl⟩⟩⟩
        simp only [hb_def, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hidx,
          List.getElem_idxOf hidx, Option.getD_some, hσl]
      have hBj : ({c ∈ B | c.1 = j} : Finset (ℕ × Bool)) =
          ({c ∈ (univ : Finset Bool) | cnt j + (!c).toNat ≤ 2}).image (Prod.mk j) := by
        ext ⟨j', c⟩
        rcases eq_or_ne j j' with rfl | hne
        · simp [hB_def, hj]
        · simp [hB_def, hne, hne.symm]
      change cnt j + _ = 3
      rw [hBj, card_image_of_injective _ (Prod.mk_right_injective j),
        card_filter _ (univ : Finset Bool), Fintype.sum_bool]
      simp only [Bool.not_true, Bool.not_false, Bool.toNat_false, Bool.toNat_true]
      split_ifs <;> omega

/-- **Correctness of the `Sigma2ThreeCNF → PosGeneralizedSubsetSum` reduction.** -/
theorem fromSigma2ThreeCNF_mem_iff (inst : Sigma2CNFInstance) :
    fromSigma2ThreeCNF inst ∈ GeneralizedSubsetSum ↔ inst ∈ Sigma2ThreeCNF := by
  classical
  dsimp only [fromSigma2ThreeCNF]
  have hnd_iff : (inst.existVars.all fun v ↦ decide (inst.existVars.count v ≤ 1)) = true ↔
      inst.existVars.Nodup := by
    rw [List.all_eq_true, List.nodup_iff_count_le_one]
    constructor
    · intro h v
      by_cases hv : v ∈ inst.existVars
      · exact decide_eq_true_eq.mp (h v hv)
      · simp [List.count_eq_zero.mpr hv]
    · intro h v _
      exact decide_eq_true (h v)
  have hwd_iff : (inst.formula.all fun c ↦ decide (c.length ≤ 3)) = true ↔
      ∀ c ∈ inst.formula, c.length ≤ 3 := by
    simp [List.all_eq_true]
  split_ifs with hvalid hempty hformEmpty
  · -- Valid, `existVars = []`, `formula = []`: always satisfiable, so not in `Sigma2ThreeCNF`.
    refine iff_of_false fixed_no_not_mem ?_
    rw [mem_Sigma2ThreeCNF_iff]
    rintro ⟨_, _, x, hx⟩
    have hnil : inst.formula = [] := List.isEmpty_iff.mp hformEmpty
    have := hx (fun _ ↦ false) (fun i ↦ by
      have hE0 : inst.existVars = [] := List.isEmpty_iff.mp hempty
      exact Fin.elim0 ⟨i.1, by simpa [hE0] using i.2⟩)
    simp [hnil] at this
  · -- Valid, `existVars = []`, `formula ≠ []`: shifted 3SAT digit construction.
    obtain ⟨hn, hw⟩ : inst.existVars.Nodup ∧ ∀ c ∈ inst.formula, c.length ≤ 3 := by
      simpa [Bool.and_eq_true, hnd_iff, hwd_iff] using hvalid
    have hE : inst.existVars = [] := List.isEmpty_iff.mp hempty
    rw [mem_GeneralizedSubsetSum_iff, mem_Sigma2ThreeCNF_iff]
    rw [and_iff_right hn, and_iff_right hw]
    have hsat_iff : (∃ y : Fin (1 :: (ThreeSAT.digitNumbers inst.formula).map (8 * ·)).length →
        Bool, maskedSum [1] (fun _ ↦ false) +
          maskedSum (1 :: (ThreeSAT.digitNumbers inst.formula).map (8 * ·)) y =
          1 + 8 * ThreeSAT.digitTarget inst.formula) ↔ inst.formula.Satisfiable := by
      -- For `x = false`, `y 0` must be `true`, and remaining sum is `8 * digitTarget`.
      have hsub : (∃ y : Fin (1 :: (ThreeSAT.digitNumbers inst.formula).map (8 * ·)).length →
          Bool, maskedSum (1 :: (ThreeSAT.digitNumbers inst.formula).map (8 * ·)) y =
            1 + 8 * ThreeSAT.digitTarget inst.formula) ↔
          (⟨ThreeSAT.digitNumbers inst.formula, ThreeSAT.digitTarget inst.formula⟩ :
            SubsetSumInstance) ∈ SubsetSum := by
        rw [exists_maskedSum_eq_iff_sublist, mem_SubsetSum_iff_sublist]
        constructor
        · rintro ⟨l, hl, hlsum⟩
          cases hl with
          | cons _ hl' =>
            obtain ⟨s, hs, rfl⟩ := List.sublist_map_iff.mp hl'
            rw [List.sum_map_mul_left] at hlsum
            omega
          | cons_cons _ hl' =>
            obtain ⟨s, hs, rfl⟩ := List.sublist_map_iff.mp hl'
            rw [List.sum_cons, List.sum_map_mul_left, List.map_id'] at hlsum
            exact ⟨s, hs, by dsimp; omega⟩
        · rintro ⟨s, hs, hsum⟩
          dsimp at hsum
          refine ⟨1 :: s.map (8 * ·), (hs.map _).cons_cons 1, ?_⟩
          rw [List.sum_cons, List.sum_map_mul_left, List.map_id', hsum]
      have h0 : maskedSum [1] (fun _ ↦ false) = 0 := by simp [maskedSum]
      simp_rw [h0, zero_add]
      exact hsub.trans ((ThreeSAT.digit_mem_SubsetSum_iff_counts hw).trans
        (ThreeSAT.counts_iff_satisfiable hw))
    constructor
    · rintro ⟨x, hx⟩
      refine ⟨fun i ↦ Fin.elim0 ⟨i.1, by simpa [hE] using i.2⟩, fun σ _ ↦ ?_⟩
      by_contra hsat
      have hsat' : inst.formula.Satisfiable := ⟨σ, Bool.eq_true_of_not_eq_false hsat⟩
      have ⟨y0, hy0⟩ := hsat_iff.mpr hsat'
      have hx0 : ¬ ∃ y, maskedSum [1] x +
          maskedSum (1 :: (ThreeSAT.digitNumbers inst.formula).map (8 * ·)) y =
          1 + 8 * ThreeSAT.digitTarget inst.formula := fun ⟨y, hy⟩ ↦ hx y hy
      apply hx0
      cases hb : x 0
      · refine ⟨y0, ?_⟩
        have hxf : x = fun _ ↦ false := by funext i; fin_cases i; exact hb
        simpa [hxf] using hy0
      · have hms1 (z : Fin 1 → Bool) : maskedSum [1] z = if z 0 then 1 else 0 := by
          simp only [maskedSum, List.length_singleton, Fin.sum_univ_one]
          cases z 0 <;> simp
        have hcons (z : Fin (1 :: (ThreeSAT.digitNumbers inst.formula).map (8 * ·)).length → Bool) :
            maskedSum (1 :: (ThreeSAT.digitNumbers inst.formula).map (8 * ·)) z =
              (if z 0 then 1 else 0) +
              ∑ i : Fin ((ThreeSAT.digitNumbers inst.formula).map (8 * ·)).length,
                if z i.succ then ((ThreeSAT.digitNumbers inst.formula).map (8 * ·))[i] else 0 := by
          simp [maskedSum, Fin.sum_univ_succ]
        have hy0_head : y0 0 = true := by
          by_contra h0
          have h0' : y0 0 = false := Bool.eq_false_of_not_eq_true h0
          rw [hms1, hcons, h0'] at hy0
          have hdiv : 8 ∣ ∑ i : Fin ((ThreeSAT.digitNumbers inst.formula).map (8 * ·)).length,
              if y0 i.succ then ((ThreeSAT.digitNumbers inst.formula).map (8 * ·))[i] else 0 :=
            Finset.dvd_sum fun i _ ↦ by
              split_ifs
              · simp
              · exact dvd_zero 8
          rcases hdiv with ⟨q, hq⟩
          simp only [Bool.false_eq_true, ↓reduceIte, zero_add, hq] at hy0
          omega
        refine ⟨fun i ↦ if i.1 = 0 then false else y0 i, ?_⟩
        rw [hms1, hcons, hy0_head] at hy0
        rw [hms1, hcons, hb]
        simpa using hy0
    · rintro ⟨_, hx⟩
      refine ⟨fun _ ↦ false, fun y hy ↦ ?_⟩
      obtain ⟨σ, hσ⟩ := hsat_iff.mp ⟨y, hy⟩
      have := hx σ (fun i ↦ Fin.elim0 ⟨i.1, by simpa [hE] using i.2⟩)
      rw [hσ] at this
      exact absurd this (by decide)
  · obtain ⟨hn, hw⟩ : inst.existVars.Nodup ∧ ∀ c ∈ inst.formula, c.length ≤ 3 := by
      simpa [Bool.and_eq_true, hnd_iff, hwd_iff] using hvalid
    rw [mem_GeneralizedSubsetSum_iff, mem_Sigma2ThreeCNF_iff, and_iff_right hn, and_iff_right hw]
    have hlen_u : (existBlock inst).length = inst.existVars.length := length_existBlock inst
    constructor
    · rintro ⟨x, hx⟩
      refine ⟨fun i ↦ x ⟨i.1, hlen_u.symm ▸ i.2⟩, fun σ hσ ↦ ?_⟩
      by_contra hsat
      have ⟨y, hy⟩ := (match_existBlock hn hw x).mpr ⟨σ, hσ, Bool.eq_true_of_not_eq_false hsat⟩
      exact hx y hy
    · rintro ⟨x, hx⟩
      refine ⟨fun i ↦ x ⟨i.1, by dsimp at *; omega⟩, fun y hy ↦ ?_⟩
      obtain ⟨σ, hσ, hsat⟩ := (match_existBlock hn hw (fun i ↦ x ⟨i.1, by dsimp at *; omega⟩)).mp
        ⟨y, hy⟩
      have := hx σ hσ
      rw [hsat] at this
      exact absurd this (by decide)
  · -- Invalid `existVars.Nodup` or clause width > 3.
    refine iff_of_false fixed_no_not_mem ?_
    rw [mem_Sigma2ThreeCNF_iff]
    rintro ⟨hn, hw, _⟩
    exact hvalid ((Bool.and_eq_true _ _).mpr ⟨hnd_iff.mpr hn, hwd_iff.mpr hw⟩)

end GSSP

/-- **`GeneralizedSubsetSum` is `Σ₂ᴾ`-hard.** -/
theorem GeneralizedSubsetSum_sigmaPHard :
    SigmaPHard 2 encGeneralizedSubsetSum GeneralizedSubsetSum :=
  Sigma2ThreeCNF_sigmaPHard.trans
    ⟨GSSP.fromSigma2ThreeCNF, GSSP.computableInPolyTime_fromSigma2ThreeCNF,
      fun inst ↦ (GSSP.fromSigma2ThreeCNF_mem_iff inst).symm⟩

/-- **`PosGeneralizedSubsetSum` is `Σ₂ᴾ`-hard.** -/
theorem PosGeneralizedSubsetSum_sigmaPHard :
    SigmaPHard 2 encGeneralizedSubsetSum PosGeneralizedSubsetSum :=
  Sigma2ThreeCNF_sigmaPHard.trans
    ⟨GSSP.fromSigma2ThreeCNF, GSSP.computableInPolyTime_fromSigma2ThreeCNF, fun inst ↦ by
      obtain ⟨h1, h2, h3, h4, h5⟩ := GSSP.positive_of_fromSigma2ThreeCNF inst
      rw [mem_PosGeneralizedSubsetSum_iff, GSSP.fromSigma2ThreeCNF_mem_iff]
      exact ⟨fun h ↦ ⟨h1, h2, h3, h4, h5, h⟩, fun h ↦ h.2.2.2.2.2⟩⟩

/-- **`GeneralizedSubsetSum` is `Σ₂ᴾ`-complete.** -/
theorem GeneralizedSubsetSum_sigmaPComplete :
    SigmaPComplete 2 encGeneralizedSubsetSum GeneralizedSubsetSum :=
  ⟨GeneralizedSubsetSum_mem_SigmaP, GeneralizedSubsetSum_sigmaPHard⟩

/-- **`PosGeneralizedSubsetSum` is `Σ₂ᴾ`-complete.** -/
theorem PosGeneralizedSubsetSum_sigmaPComplete :
    SigmaPComplete 2 encGeneralizedSubsetSum PosGeneralizedSubsetSum :=
  ⟨PosGeneralizedSubsetSum_mem_SigmaP, PosGeneralizedSubsetSum_sigmaPHard⟩

end Cslib.Complexity
