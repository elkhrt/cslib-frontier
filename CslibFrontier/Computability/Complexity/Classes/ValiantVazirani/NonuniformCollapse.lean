/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CslibFrontier Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Balanced
public import CslibFrontier.Computability.Circuit.Boolean.Encoding
public import CslibFrontier.Computability.Circuit.Boolean.PPoly
public import CslibFrontier.Computability.Complexity.Classes.NP
public import CslibFrontier.Computability.Complexity.Classes.Promise.Circuit
public import CslibFrontier.Computability.Complexity.Problems.SAT
public import CslibFrontier.Computability.Complexity.Problems.USAT
public import CslibFrontier.Foundations.Data.BitString.List
public import CslibFrontier.Logics.Propositional.CNF
public import CslibFrontier.Logics.Propositional.CNF.ModelCount

import CslibFrontier.Computability.Circuit.Boolean.Advice
import CslibFrontier.Computability.Circuit.Boolean.BoundedError
import CslibFrontier.Computability.Circuit.Boolean.CodeComposition
import CslibFrontier.Computability.Circuit.Boolean.EncodingSize
import CslibFrontier.Computability.Circuit.Boolean.EvaluationTime
import CslibFrontier.Computability.Circuit.Boolean.PPoly.Closure
import CslibFrontier.Computability.Circuit.Boolean.PolynomialTime
import CslibFrontier.Computability.Circuit.Boolean.Substitution
import CslibFrontier.Computability.Circuit.Encoding.Combinators
import CslibFrontier.Computability.Complexity.Classes.ValiantVazirani.Reduction
import CslibFrontier.Computability.Complexity.CookLevin.Completeness
import CslibFrontier.Computability.Complexity.Problems.SAT.PolyTime
import CslibFrontier.Computability.Languages.Slice
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Iteration
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Foundations.Data.List.TakeQuantifiers
import Cslib.Foundations.Data.Polynomial.Monotone
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Nonuniform Valiant–Vazirani Collapse and Parsimonious CNF-to-Circuit Compilation

This module establishes nonuniform complexity and Boolean circuit encoding results around the
Valiant–Vazirani reduction and `PromiseUSAT`:

1. **`length_encCode_le_log`**: Sharp `O((s + m) log(n + s + 2))` serialized bit-length bound for
   De Morgan Boolean circuit codes `Boolean.encCode c.code`, exploiting binary wire indices.
2. **`valiantVazirani_nonuniform_collapse`**: Nonuniform Valiant–Vazirani collapse showing that if
   `PromiseUSAT` on CNF formulas is solvable in `promiseClass (Boolean.PPolyOn encCNF)`, then
   `Complexity.NP enc ⊆ Boolean.PPolyOn enc` for every instance encoding `enc`.
3. **`cnfToBooleanCircuit`**, **`card_solSet_cnfToBooleanCircuit`**, and
   **`computableInPolyTime_cnfToBooleanCircuit`**: Polynomial-time parsimonious (model-count
   preserving) compilation of any CNF formula `φ` over `ℕ` into a 1-output De Morgan Boolean circuit
   on `φ.distinctVars.length` inputs.
-/

public section

namespace CslibFrontier.Complexity.ValiantVazirani

open Cslib Cslib.Circuits Turing.MultiTapeTM ComputableInPolyTime

/-- Logarithmic bound on the serialized length of a De Morgan circuit code: because wire indices
are encoded in binary (`encNat`), every wire reference `< n + c.size` uses at most
`Nat.log 2 (n + c.size) + 1` bits. -/
theorem length_encCode_le_log {n m : ℕ} (c : Circuit Boolean.signature n m) :
    (Boolean.encCode c.code).length ≤
      2 * c.size * (23 + 8 * (Nat.log 2 (n + c.size) + 1)) + 1 +
        m * (2 * (Nat.log 2 (n + c.size) + 1) + 1) := by
  set L := Nat.log 2 (n + c.size) + 1
  have hlt_pow : n + c.size < 2 ^ L := Nat.lt_pow_succ_log_self (by decide) (n + c.size)
  have hwire_bound : ∀ k < n + c.size, (encNat k).length ≤ L := by
    intro k hk
    rw [encNat_apply, Nat.size_eq_bits_len]
    exact Nat.size_le.mpr (hk.trans hlt_pow)
  have _hgates := Boolean.length_encList_encGate_le c (L := L) fun w =>
    hwire_bound w.toNat (Wire.toNat_lt w)
  have _houtputs : (encList encNat c.code.2).length ≤ m * (2 * L + 1) := by
    have h := length_encList_le encNat c.code.2 (b := L) fun i hi => by
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hi
      exact hwire_bound (c.outputs j).toNat (Wire.toNat_lt (c.outputs j))
    simpa [Circuit.code] using h
  simp only [Boolean.encCode, length_encPair]
  nlinarith

/-- **Nonuniform Valiant–Vazirani collapse**: if `PromiseUSAT` on CNF formulas is separated by a
problem in `PPolyOn encCNF`, then `NP enc ⊆ PPolyOn enc` for every instance encoding `enc`. -/
theorem valiantVazirani_nonuniform_collapse
    (hUSAT : Complexity.PromiseUSAT ∈ Complexity.promiseClass (Boolean.PPolyOn Complexity.encCNF))
    {α : Type} (enc : α ↪ List Bool) :
    Complexity.NP enc ⊆ Boolean.PPolyOn enc := by
  classical
  suffices hSAT : Complexity.SAT ∈ Boolean.PPolyOn Complexity.encCNF by
    intro A hA
    exact (Complexity.CookLevin.SAT_npHard enc A hA).mem_PPolyOn hSAT
  obtain ⟨B, ⟨LB, hLB, hBLB⟩, hyesB, hnoB⟩ := hUSAT
  let queries : Logic.PL.CNF ℕ × List Bool → List (List Bool) := fun x =>
    let N := (Complexity.encCNF x.1).length
    (BitString.listRows (11 * (N + 3)) ((N + 2) ^ 2) x.2).map
      fun b => Complexity.encCNF (Complexity.ValiantVazirani.reduce (x.1, b))
  have hreduce := Complexity.ValiantVazirani.computableInPolyTime_reduce
  have hqueries_poly : ComputableInPolyTime queries
      (encPair Complexity.encCNF encBits) (encList encBits) := by
    dsimp only [queries]
    fun_prop
  obtain ⟨cr, dr, hred_len⟩ := hreduce.polyBounded_length.exists_le
  let QBound : Polynomial ℕ :=
    Polynomial.C cr * (2 * Polynomial.X + 1 + (Polynomial.X + 2) ^ 2 + 1) ^ dr
  have hq_len (φ : Logic.PL.CNF ℕ) (b : List Bool)
      (hb : b.length = ((Complexity.encCNF φ).length + 2) ^ 2) :
      (Complexity.encCNF (Complexity.ValiantVazirani.reduce (φ, b))).length ≤
        QBound.eval (Complexity.encCNF φ).length := by
    refine (hred_len (φ, b)).trans ?_
    simp only [length_encPair, encBits_apply, hb, QBound, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one,
      Polynomial.eval_ofNat]
    exact le_rfl
  obtain ⟨S, W, _, α_adv, -, hα_poly, h_eval⟩ := Boolean.PPoly.exists_evalAdvice hLB QBound
  let V_adv : List Bool × (Logic.PL.CNF ℕ × List Bool) → Bool := fun p =>
    let n := (Complexity.encCNF p.2.1).length
    (queries p.2).any fun w => Boolean.evalAdvice (S.eval n) (W.eval n) p.1 w
  have hV_adv : ComputableInPolyTime V_adv
      (encPair encBits (encPair Complexity.encCNF encBits)) encBool := by
    have hn_u : ComputableInPolyTime
        (fun p : List Bool × (Logic.PL.CNF ℕ × List Bool) => (Complexity.encCNF p.2.1).length)
        (encPair encBits (encPair Complexity.encCNF encBits)) encUnary := by fun_prop
    have hq_list : ComputableInPolyTime
        (fun p : List Bool × (Logic.PL.CNF ℕ × List Bool) => queries p.2)
        (encPair encBits (encPair Complexity.encCNF encBits)) (encList encBits) :=
      hqueries_poly.comp (snd _ _)
    refine anyWithInput hq_list ?_
    exact Boolean.computableInPolyTime_evalAdvice_eval S W
      (hn_u.comp (fst _ _)) ((fst _ _).comp (fst _ _)) (snd _ _)
  obtain ⟨L_V, hL_V, hLV_iff⟩ := Boolean.PPoly.exists_of_polyTime hV_adv
  let randLen : ℕ → ℕ := fun n => 11 * (n + 3) * (n + 2) ^ 2
  have hrand_poly : PolynomiallyBounded randLen := by dsimp only [randLen]; fun_prop
  let F_slice (n : ℕ) : BitString (n + randLen n) → Bool := fun y =>
    let u := frame (α_adv n)
    let a : Fin u.length → Bool := fun j => u[j]
    L_V.slice (u.length + (2 * n + 1 + randLen n))
      (Boolean.substitute (Boolean.prependInputs a)
        (Boolean.substitute (Boolean.frameWiring n (randLen n)) y))
  have hF_comp : PolynomiallyBounded fun n =>
      complexity Boolean.interpretation (single (F_slice n)) := by
    set qV := fun N => complexity Boolean.interpretation (single (L_V.slice N))
    have hqV : PolynomiallyBounded qV := hL_V
    refine PolynomiallyBounded.mono_of_le
      (g := fun n => qV (2 * (α_adv n).length + 1 + (2 * n + 1 + randLen n)) + 4)
      (by fun_prop) fun n => ?_
    dsimp only [F_slice]
    calc complexity Boolean.interpretation
          (single fun y => L_V.slice ((frame (α_adv n)).length + (2 * n + 1 + randLen n))
            (Boolean.substitute (Boolean.prependInputs fun j => (frame (α_adv n))[j])
              (Boolean.substitute (Boolean.frameWiring n (randLen n)) y)))
        ≤ complexity Boolean.interpretation
            (single fun z => L_V.slice ((frame (α_adv n)).length + (2 * n + 1 + randLen n))
              (Boolean.substitute (Boolean.prependInputs fun j => (frame (α_adv n))[j]) z)) + 2 :=
          Boolean.complexity_substitute_le (Boolean.frameWiring n (randLen n))
            (fun z => L_V.slice ((frame (α_adv n)).length + (2 * n + 1 + randLen n))
              (Boolean.substitute (Boolean.prependInputs fun j => (frame (α_adv n))[j]) z))
      _ ≤ (complexity Boolean.interpretation
            (single (L_V.slice ((frame (α_adv n)).length + (2 * n + 1 + randLen n)))) + 2) + 2 :=
          Nat.add_le_add_right
            (Boolean.complexity_substitute_le
              (Boolean.prependInputs fun j => (frame (α_adv n))[j])
              (L_V.slice ((frame (α_adv n)).length + (2 * n + 1 + randLen n)))) 2
      _ = qV (2 * (α_adv n).length + 1 + (2 * n + 1 + randLen n)) + 4 := by
          dsimp only [qV]
          rw [length_frame]
  have hF_eval {n : ℕ} {x : Fin n → Bool} {φ : Logic.PL.CNF ℕ}
      (hφ : Complexity.encCNF φ = List.ofFn x) (r : Fin (randLen n) → Bool) :
      F_slice n (Fin.append x r) = true ↔ V_adv (α_adv n, (φ, List.ofFn r)) = true := by
    dsimp only [F_slice]
    rw [Language.slice_eq_true_iff, Boolean.substitute_prependInputs, List.ofFn_fin_append]
    have ha_eq : (List.ofFn fun j : Fin (frame (α_adv n)).length => (frame (α_adv n))[j]) =
        frame (α_adv n) := by
      simpa only [Fin.getElem_fin] using List.ofFn_getElem (xs := frame (α_adv n))
    rw [ha_eq, Boolean.ofFn_substitute_frameWiring, ← hφ, hLV_iff]
    rfl
  obtain ⟨L_SAT, hL_SAT, hSAT_slice⟩ := Boolean.PPoly.exists_of_oneSidedError F_slice hF_comp
    (Language.encodes Complexity.encCNF)
    (Language.encodesMember Complexity.encCNF Complexity.SAT)
    (fun n x ⟨φ, hφ⟩ hx => by
      have hφSAT : φ ∈ Complexity.SAT := (Language.encodesMember_eq_true_iff hφ).mp hx
      have hn_eq : (Complexity.encCNF φ).length = n := by rw [hφ, List.length_ofFn]
      have hvars : φ.vars.length ≤ n := by
        rw [← hn_eq]
        exact Complexity.SAT.length_vars_le φ
      have hrb : Complexity.ValiantVazirani.randomBits φ ≤ (n + 2) ^ 2 :=
        (Complexity.ValiantVazirani.randomBits_le φ).trans
          (Nat.pow_le_pow_left (by omega) 2)
      have hvv := Complexity.ValiantVazirani.two_pow_le_two_mul_card_exists_row (M := n + 3)
        (by omega) (fun b => Complexity.ValiantVazirani.reduce (φ, b) ∈ Complexity.USAT)
        ((Complexity.ValiantVazirani.three_mul_two_pow_le_card_reduce_mem_USAT hφSAT hrb).trans
          (Nat.mul_le_mul_right _ (by omega)))
      refine hvv.trans (Nat.mul_le_mul_left 2 (Finset.card_le_card fun r hr => ?_))
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr ⊢
      obtain ⟨b, hb_mem, hb_usat⟩ := hr
      rw [hF_eval hφ r]
      dsimp only [V_adv, queries]
      rw [hn_eq, List.any_eq_true]
      have hb_len : b.length = (n + 2) ^ 2 := BitString.length_of_mem_listRows hb_mem
      have hq_bound : (Complexity.encCNF (Complexity.ValiantVazirani.reduce (φ, b))).length ≤
          QBound.eval n := by
        rw [← hn_eq]
        exact hq_len φ b (by rwa [hn_eq])
      refine ⟨Complexity.encCNF (Complexity.ValiantVazirani.reduce (φ, b)),
        List.mem_map.mpr ⟨b, hb_mem, rfl⟩, ?_⟩
      rw [h_eval n _ hq_bound, ← hBLB]
      exact hyesB hb_usat)
    (fun n x ⟨φ, hφ⟩ hx r => by
      have hφUNSAT : φ ∈ Complexity.UNSAT := fun hsat =>
        Bool.noConfusion
          (hx.symm.trans ((Language.encodesMember_eq_true_iff hφ).mpr hsat))
      have hn_eq : (Complexity.encCNF φ).length = n := by rw [hφ, List.length_ofFn]
      rw [Bool.eq_false_iff]
      intro htrue
      rw [hF_eval hφ r] at htrue
      dsimp only [V_adv, queries] at htrue
      rw [hn_eq, List.any_eq_true] at htrue
      obtain ⟨w, hw_mem, hw_eval⟩ := htrue
      obtain ⟨b, hb_mem, rfl⟩ := List.mem_map.mp hw_mem
      have hb_len : b.length = (n + 2) ^ 2 := BitString.length_of_mem_listRows hb_mem
      have hq_bound : (Complexity.encCNF (Complexity.ValiantVazirani.reduce (φ, b))).length ≤
          QBound.eval n := by
        rw [← hn_eq]
        exact hq_len φ b (by rwa [hn_eq])
      have hmemB : Complexity.ValiantVazirani.reduce (φ, b) ∈ B :=
        (hBLB _).mpr ((h_eval n _ hq_bound).mp hw_eval)
      have hmemUNSAT := Complexity.ValiantVazirani.reduce_mem_UNSAT hφUNSAT b
      exact Set.disjoint_left.mp hnoB hmemB hmemUNSAT)
  exact ⟨L_SAT, hL_SAT, Language.mem_iff_of_slice_eq_encodesMember hSAT_slice⟩

private def constGate1 (n : ℕ) (b : Bool) : Circuit Boolean.signature n 1 :=
  Circuit.oneGate (σ := Boolean.signature) (.const b) Fin.elim0

private def wireGate1 {n : ℕ} (i : Fin n) : Circuit Boolean.signature n 1 :=
  Circuit.wiring Boolean.signature fun _ => i

private def notGate1 {n : ℕ} (c : Circuit Boolean.signature n 1) : Circuit Boolean.signature n 1 :=
  (Circuit.oneGate (σ := Boolean.signature) .not id).comp c

private def andGate2 : Circuit Boolean.signature (1 + 1) 1 :=
  Circuit.oneGate (σ := Boolean.signature) .and id

private def orGate2 : Circuit Boolean.signature (1 + 1) 1 :=
  Circuit.oneGate (σ := Boolean.signature) .or id

private theorem eval_andGate2 (u v : Fin 1 → Bool) :
    andGate2.eval Boolean.interpretation (Fin.append u v) = fun _ => u 0 && v 0 := by
  funext j
  rw [Subsingleton.elim j 0]
  simp [andGate2, Circuit.eval_oneGate]
  rfl

private theorem eval_orGate2 (u v : Fin 1 → Bool) :
    orGate2.eval Boolean.interpretation (Fin.append u v) = fun _ => u 0 || v 0 := by
  funext j
  rw [Subsingleton.elim j 0]
  simp [orGate2, Circuit.eval_oneGate]
  rfl

private def balancedAndGate (n : ℕ) (cs : List (Circuit Boolean.signature n 1)) :
    Circuit Boolean.signature n 1 :=
  Circuit.balanced andGate2 (constGate1 n true) cs

private def balancedOrGate (n : ℕ) (cs : List (Circuit Boolean.signature n 1)) :
    Circuit Boolean.signature n 1 :=
  Circuit.balanced orGate2 (constGate1 n false) cs

private theorem eval_balancedAndGate (n : ℕ) (cs : List (Circuit Boolean.signature n 1))
    (x : BitString n) :
    (balancedAndGate n cs).eval Boolean.interpretation x 0 =
      cs.all fun c => c.eval Boolean.interpretation x 0 := by
  have heval := congrFun (Circuit.eval_balanced Boolean.interpretation andGate2
    (constGate1 n true) cs x) 0
  rw [balancedAndGate, heval]
  have hhom : (cs.balancedFold (fun u v : Fin 1 → Bool => fun _ => u 0 && v 0)
      (fun _ => true) (fun c => c.eval Boolean.interpretation x)) 0 =
      cs.balancedFold (· && ·) true (fun c => c.eval Boolean.interpretation x 0) :=
    List.balancedFold_hom (fun f : Fin 1 → Bool => f 0) (op' := (· && ·))
      (fun _ _ => rfl) cs
  simp only [eval_andGate2]
  have hunit : (constGate1 n true).eval Boolean.interpretation x = fun _ => true :=
    funext fun j => by rw [Subsingleton.elim j 0]; simp [constGate1, Circuit.eval_oneGate]; rfl
  rw [hunit, hhom, List.balancedFold_eq_foldr]
  clear heval hhom
  induction cs with
  | nil => rfl
  | cons c cs ih => simp [ih]

private theorem eval_balancedOrGate (n : ℕ) (cs : List (Circuit Boolean.signature n 1))
    (x : BitString n) :
    (balancedOrGate n cs).eval Boolean.interpretation x 0 =
      cs.any fun c => c.eval Boolean.interpretation x 0 := by
  have heval := congrFun (Circuit.eval_balanced Boolean.interpretation orGate2
    (constGate1 n false) cs x) 0
  rw [balancedOrGate, heval]
  have hhom : (cs.balancedFold (fun u v : Fin 1 → Bool => fun _ => u 0 || v 0)
      (fun _ => false) (fun c => c.eval Boolean.interpretation x)) 0 =
      cs.balancedFold (· || ·) false (fun c => c.eval Boolean.interpretation x 0) :=
    List.balancedFold_hom (fun f : Fin 1 → Bool => f 0) (op' := (· || ·))
      (fun _ _ => rfl) cs
  simp only [eval_orGate2]
  have hunit : (constGate1 n false).eval Boolean.interpretation x = fun _ => false :=
    funext fun j => by rw [Subsingleton.elim j 0]; simp [constGate1, Circuit.eval_oneGate]; rfl
  rw [hunit, hhom, List.balancedFold_eq_foldr]
  clear heval hhom
  induction cs with
  | nil => rfl
  | cons c cs ih => simp [ih]

private def cnfLitGate (vs : List ℕ) (lit : Logic.PL.Literal ℕ) :
    Circuit Boolean.signature vs.length 1 :=
  if h : vs.idxOf lit.1 < vs.length then
    if lit.2 then wireGate1 ⟨vs.idxOf lit.1, h⟩
    else notGate1 (wireGate1 ⟨vs.idxOf lit.1, h⟩)
  else constGate1 vs.length false

private def cnfClauseGate (vs : List ℕ) (cl : Logic.PL.Clause ℕ) :
    Circuit Boolean.signature vs.length 1 :=
  balancedOrGate vs.length (cl.map (cnfLitGate vs))

/-- Parsimonious De Morgan Boolean circuit compiled from `φ : Logic.PL.CNF ℕ` on its
`φ.distinctVars.length` distinct variables. -/
def cnfToBooleanCircuit (φ : Logic.PL.CNF ℕ) :
    Circuit Boolean.signature φ.distinctVars.length 1 :=
  balancedAndGate φ.distinctVars.length (φ.map (cnfClauseGate φ.distinctVars))

private def extendDistinctVars (φ : Logic.PL.CNF ℕ) (x : BitString φ.distinctVars.length)
    (v : ℕ) : Bool :=
  if h : φ.distinctVars.idxOf v < φ.distinctVars.length then
    x ⟨φ.distinctVars.idxOf v, h⟩
  else false

private theorem eval_cnfToBooleanCircuit (φ : Logic.PL.CNF ℕ)
    (x : BitString φ.distinctVars.length) :
    (cnfToBooleanCircuit φ).eval Boolean.interpretation x 0 =
      φ.eval (extendDistinctVars φ x) := by
  dsimp only [cnfToBooleanCircuit]
  rw [Bool.eq_iff_iff, eval_balancedAndGate, List.all_map, List.all_eq_true,
    Logic.PL.CNF.eval, List.all_eq_true]
  refine forall_congr' fun cl => imp_congr_right fun hcl => ?_
  dsimp only [Function.comp_apply, cnfClauseGate]
  rw [eval_balancedOrGate, List.any_map, List.any_eq_true,
    Logic.PL.Clause.eval, List.any_eq_true]
  refine exists_congr fun lit => and_congr_right fun hlit => ?_
  have hv_vars : lit.1 ∈ φ.vars := Logic.PL.CNF.mem_vars.mpr ⟨cl, hcl, lit.2, by
    rcases lit with ⟨v, b⟩; exact hlit⟩
  have hv_dist : lit.1 ∈ φ.distinctVars := Logic.PL.CNF.mem_distinctVars.mpr hv_vars
  have hlt : φ.distinctVars.idxOf lit.1 < φ.distinctVars.length :=
    List.idxOf_lt_length_iff.mpr hv_dist
  dsimp only [Function.comp_apply, cnfLitGate]
  rw [dite_eq_left_of_eq_true (eq_true hlt)]
  rcases lit with ⟨v, (_ | _)⟩ <;>
    simp [Logic.PL.Literal.eval, extendDistinctVars, hlt, wireGate1, notGate1, Circuit.eval_comp,
      Circuit.eval_oneGate, Circuit.eval_wiring]
  rfl

/-- `cnfToBooleanCircuit φ` has the exact same number of satisfying assignments as
`φ.modelCount`. -/
theorem card_solSet_cnfToBooleanCircuit (φ : Logic.PL.CNF ℕ) :
    ((Finset.univ : Finset (BitString φ.distinctVars.length)).filter fun x =>
      (cnfToBooleanCircuit φ).eval Boolean.interpretation x 0 = true).card = φ.modelCount := by
  symm
  let restrictVar (σ : ℕ → Bool) : BitString φ.distinctVars.length :=
    fun i => σ (φ.distinctVars[i.val]'(i.isLt))
  have hnodup := φ.nodup_distinctVars
  refine Logic.PL.CNF.modelCount_eq_card_filter restrictVar
    (fun x => (cnfToBooleanCircuit φ).eval Boolean.interpretation x 0 = true) ?_ ?_
  · intro σ τ _ _
    constructor
    · intro hEq v hv
      have hdist : v ∈ φ.distinctVars := Logic.PL.CNF.mem_distinctVars.mpr hv
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hdist
      exact congrFun hEq ⟨i, hi⟩
    · intro hall
      funext i
      have hmem : φ.distinctVars[i.val]'(i.isLt) ∈ φ.vars :=
        Logic.PL.CNF.mem_distinctVars.mp (List.getElem_mem i.isLt)
      exact hall _ hmem
  · intro x
    rw [eval_cnfToBooleanCircuit]
    constructor
    · intro hx
      refine ⟨extendDistinctVars φ x, hx, ?_⟩
      funext i
      dsimp only [restrictVar, extendDistinctVars]
      have hidx : φ.distinctVars.idxOf (φ.distinctVars[i.val]'(i.isLt)) = i.val :=
        List.Nodup.idxOf_getElem hnodup i.val i.isLt
      simp [hidx, i.isLt]
    · rintro ⟨σ, hσ, rfl⟩
      have hcongr : φ.eval (extendDistinctVars φ (restrictVar σ)) = φ.eval σ := by
        refine Logic.PL.CNF.eval_congr fun v hv => ?_
        have hdist : v ∈ φ.distinctVars := Logic.PL.CNF.mem_distinctVars.mpr hv
        have hlt : φ.distinctVars.idxOf v < φ.distinctVars.length :=
          List.idxOf_lt_length_iff.mpr hdist
        dsimp only [extendDistinctVars, restrictVar]
        rw [dite_eq_left_of_eq_true (eq_true hlt), List.getElem_idxOf hlt]
      rwa [hcongr]

/-- `φ ↦ Boolean.encCircuit 1 ⟨φ.distinctVars.length, cnfToBooleanCircuit φ⟩` is computable in
polynomial time. -/
theorem computableInPolyTime_cnfToBooleanCircuit :
    ComputableInPolyTime
      (fun φ : Logic.PL.CNF ℕ =>
        Boolean.encCircuit 1 ⟨φ.distinctVars.length, cnfToBooleanCircuit φ⟩)
      Complexity.encCNF encBits := by
  let litCode (vs : List ℕ) (lit : Logic.PL.Literal ℕ) : Complexity.CircuitCode :=
    let idx := vs.idxOf lit.1
    if idx < vs.length then
      if lit.2 then ([], [idx])
      else Boolean.compCode vs.length
        (Circuit.oneGate (σ := Boolean.signature) Boolean.Op.not id).code ([], [idx])
    else ([(.const false, [])], [vs.length])
  have hlit_eq (vs : List ℕ) (lit : Logic.PL.Literal ℕ) :
      (cnfLitGate vs lit).code = litCode vs lit := by
    by_cases hlt : vs.idxOf lit.1 < vs.length
    · by_cases hb : lit.2 = true
      · simp [cnfLitGate, litCode, hlt, hb, wireGate1, Circuit.code_wiring]
      · simp only [cnfLitGate, litCode, hlt, hb, ↓reduceDIte, Bool.false_eq_true, ↓reduceIte]
        rw [notGate1, ← Boolean.compCode_code]
        simp [wireGate1, Circuit.code_wiring]
    · simp [cnfLitGate, litCode, hlt, constGate1, Circuit.code_oneGate]
  let clauseCode (vs : List ℕ) (cl : Logic.PL.Clause ℕ) : Complexity.CircuitCode :=
    Circuit.balancedCode vs.length orGate2.code ([(.const false, [])], [vs.length])
      (cl.map (litCode vs))
  have hclause_eq (vs : List ℕ) (cl : Logic.PL.Clause ℕ) :
      (cnfClauseGate vs cl).code = clauseCode vs cl := by
    dsimp only [cnfClauseGate, balancedOrGate, clauseCode]
    rw [Circuit.code_balanced, List.map_map]
    simp only [constGate1, Circuit.code_oneGate, List.ofFn_zero]
    congr 2
    exact funext (hlit_eq vs)
  let fullCode (φ : Logic.PL.CNF ℕ) : Complexity.CircuitCode :=
    let vs := φ.distinctVars
    Circuit.balancedCode vs.length andGate2.code ([(.const true, [])], [vs.length])
      (φ.map (clauseCode vs))
  have hfull_eq (φ : Logic.PL.CNF ℕ) : (cnfToBooleanCircuit φ).code = fullCode φ := by
    dsimp only [cnfToBooleanCircuit, balancedAndGate, fullCode]
    rw [Circuit.code_balanced, List.map_map]
    simp only [constGate1, Circuit.code_oneGate, List.ofFn_zero]
    congr 2
    exact funext (hclause_eq φ.distinctVars)
  have hdistinct : ComputableInPolyTime (Logic.PL.CNF.distinctVars (V := ℕ))
      Complexity.encCNF (encList encNat) :=
    Complexity.SAT.computableInPolyTime_distinctVars
  have hn_unary : ComputableInPolyTime (fun φ : Logic.PL.CNF ℕ => φ.distinctVars.length)
      Complexity.encCNF encUnary := by
    simpa [Logic.PL.CNF.length_distinctVars] using Complexity.SAT.computableInPolyTime_numVars
  have hn_bin : ComputableInPolyTime (fun φ : Logic.PL.CNF ℕ => φ.distinctVars.length)
      Complexity.encCNF encNat := unary_to_binary.comp hn_unary
  have hlit_poly : ComputableInPolyTime
      (fun p : List ℕ × Logic.PL.Literal ℕ => litCode p.1 p.2)
      (encPair (encList encNat) (encPair encNat encBool)) Boolean.encCode := by
    have hidx_u : ComputableInPolyTime (fun p : List ℕ × Logic.PL.Literal ℕ => p.1.idxOf p.2.1)
        (encPair (encList encNat) (encPair encNat encBool)) encUnary :=
      idxOfWithInput (fst _ _) (fst _ _ |>.comp (snd _ _))
    have hlen_u : ComputableInPolyTime (fun p : List ℕ × Logic.PL.Literal ℕ => p.1.length)
        (encPair (encList encNat) (encPair encNat encBool)) encUnary := by fun_prop
    have hidx_b := unary_to_binary.comp hidx_u
    have hlen_b := unary_to_binary.comp hlen_u
    have hlt_b : ComputableInPolyTime
        (fun p : List ℕ × Logic.PL.Literal ℕ => decide (p.1.idxOf p.2.1 < p.1.length))
        (encPair (encList encNat) (encPair encNat encBool)) encBool :=
      binary_lt' hidx_b hlen_b
    have hwire_code : ComputableInPolyTime
        (fun p : List ℕ × Logic.PL.Literal ℕ =>
          (([] : List (Boolean.Op × List ℕ)), [p.1.idxOf p.2.1]))
        (encPair (encList encNat) (encPair encNat encBool)) Boolean.encCode :=
      (const []).prod (hidx_b.cons' (const []))
    have hnot_code : ComputableInPolyTime
        (fun p : List ℕ × Logic.PL.Literal ℕ =>
          Boolean.compCode p.1.length
            (Circuit.oneGate (σ := Boolean.signature) Boolean.Op.not id).code
            ([], [p.1.idxOf p.2.1]))
        (encPair (encList encNat) (encPair encNat encBool)) Boolean.encCode :=
      Boolean.computableInPolyTime_compCode hlen_b (const _) hwire_code
    have hfalse_code : ComputableInPolyTime
        (fun p : List ℕ × Logic.PL.Literal ℕ =>
          (([(Boolean.Op.const false, ([] : List ℕ))] : List (Boolean.Op × List ℕ)),
            [p.1.length]))
        (encPair (encList encNat) (encPair encNat encBool)) Boolean.encCode :=
      (const [(Boolean.Op.const false, ([] : List ℕ))]).prod (hlen_b.cons' (const []))
    have hinner := ((snd _ _).comp (snd _ _)).ite hwire_code hnot_code
    simpa only [litCode, Function.comp_apply, decide_eq_true_eq] using
      hlt_b.ite hinner hfalse_code
  have hclause_poly : ComputableInPolyTime
      (fun p : List ℕ × Logic.PL.Clause ℕ => clauseCode p.1 p.2)
      (encPair (encList encNat) (encList (encPair encNat encBool))) Boolean.encCode := by
    have hlen_b : ComputableInPolyTime
        (fun p : List ℕ × Logic.PL.Clause ℕ => p.1.length)
        (encPair (encList encNat) (encList (encPair encNat encBool))) encNat :=
      unary_to_binary.comp (by fun_prop)
    have hunit : ComputableInPolyTime
        (fun p : List ℕ × Logic.PL.Clause ℕ =>
          (([(Boolean.Op.const false, ([] : List ℕ))] : List (Boolean.Op × List ℕ)),
            [p.1.length]))
        (encPair (encList encNat) (encList (encPair encNat encBool))) Boolean.encCode :=
      (const [(Boolean.Op.const false, ([] : List ℕ))]).prod (hlen_b.cons' (const []))
    have hlits : ComputableInPolyTime
        (fun p : List ℕ × Logic.PL.Clause ℕ => p.2.map (litCode p.1))
        (encPair (encList encNat) (encList (encPair encNat encBool)))
        (encList Boolean.encCode) :=
      mapWith hlit_poly (fst _ _) (snd _ _)
    exact Circuit.computableInPolyTime_balancedCode hlen_b (const orGate2.code) hunit hlits
  have hclauses_list : ComputableInPolyTime
      (fun φ : Logic.PL.CNF ℕ => φ.map (clauseCode φ.distinctVars))
      Complexity.encCNF (encList Boolean.encCode) := by
    have hid_clauses : ComputableInPolyTime
        (fun φ : Logic.PL.CNF ℕ => (φ : List (Logic.PL.Clause ℕ)))
        Complexity.encCNF (encList (encList (encPair encNat encBool))) :=
      of_eq fun _ => rfl
    exact mapWith hclause_poly hdistinct hid_clauses
  have hfull_poly : ComputableInPolyTime fullCode Complexity.encCNF Boolean.encCode := by
    have hunit : ComputableInPolyTime
        (fun φ : Logic.PL.CNF ℕ =>
          (([(Boolean.Op.const true, ([] : List ℕ))] : List (Boolean.Op × List ℕ)),
            [φ.distinctVars.length]))
        Complexity.encCNF Boolean.encCode :=
      (const [(Boolean.Op.const true, ([] : List ℕ))]).prod (hn_bin.cons' (const []))
    exact Circuit.computableInPolyTime_balancedCode hn_bin (const andGate2.code)
      hunit hclauses_list
  have hraw : ComputableInPolyTime
      (fun φ : Logic.PL.CNF ℕ =>
        encPair encUnary Boolean.encCode (φ.distinctVars.length, fullCode φ))
      Complexity.encCNF encBits :=
    (of_eq (encOut := encBits) fun _ => rfl).comp (hn_unary.prod hfull_poly)
  refine hraw.of_enc_eq fun φ => ?_
  simp [Boolean.encCircuit_apply, hfull_eq]

end CslibFrontier.Complexity.ValiantVazirani
