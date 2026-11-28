module

public import CslibFrontier.Computability.Complexity.ProofSystem.TauFormula

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListToBits
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Uniform Polynomial-Time Universal De Morgan Circuit Evaluators

This module constructs a uniform polynomial-time family of De Morgan universal circuit evaluators
`univEvalCircuit k m S hk : Circuit signature (univDescLen k m S + k) m` built from one-hot
multiplexers and gated single-opcode branches, together with a canonical one-hot binary description
encoder `encodeCircuit` for arbitrary size-`≤ S` De Morgan circuits `c : Circuit signature k m`,
and proves uniform polynomial-time generation, uniform polynomial-time evaluation, and exact
evaluation soundness `(univEvalCircuit k m S hk).eval (encodeCircuit c S hS, u) = c.eval u`.

## Main definitions

* `CslibFrontier.ProofComplexity.muxGates`: one-hot multiplexer `RawGate` chain of length
  `2 * ws.length`.
* `CslibFrontier.ProofComplexity.univGateDescStride`, `CslibFrontier.ProofComplexity.univDescLen`,
  `CslibFrontier.ProofComplexity.univStepGateCount`,
  `CslibFrontier.ProofComplexity.univSimGateWire`: description-bit and gate-index parameters of the
  universal evaluator.
* `CslibFrontier.ProofComplexity.univAvailWires`, `CslibFrontier.ProofComplexity.univGateBlock`,
  `CslibFrontier.ProofComplexity.univOutBlock`, `CslibFrontier.ProofComplexity.univRawGates`,
  `CslibFrontier.ProofComplexity.univRawOuts`: uniform first-order `RawGate` representation of the
  universal De Morgan circuit evaluator.
* `CslibFrontier.ProofComplexity.univEvalCircuit`, `CslibFrontier.ProofComplexity.univEvalList`:
  typed De Morgan circuit and first-order list evaluator for `U_{k, m, S}`.
* `CslibFrontier.ProofComplexity.opToCode`, `CslibFrontier.ProofComplexity.lineArg0`,
  `CslibFrontier.ProofComplexity.lineArg1`, `CslibFrontier.ProofComplexity.encodeCircuit`: canonical
  one-hot binary encoding of any `c : Circuit signature k m` with `c.size ≤ S`.

## Main results

* `CslibFrontier.ProofComplexity.getElem_muxGates`: indexed gate structure of `muxGates`.
* `CslibFrontier.ProofComplexity.computableInPolyTime_univRawGates`,
  `CslibFrontier.ProofComplexity.computableInPolyTime_univRawOuts`,
  `CslibFrontier.ProofComplexity.computableInPolyTime_univEvalList`: uniform polynomial-time
  generation and evaluation of `U_{k, m, S}`.
* `CslibFrontier.ProofComplexity.encodeCircuit_op`,
  `CslibFrontier.ProofComplexity.encodeCircuit_arg0`,
  `CslibFrontier.ProofComplexity.encodeCircuit_arg1`,
  `CslibFrontier.ProofComplexity.encodeCircuit_out`: one-hot selector equations of `encodeCircuit`.
* `CslibFrontier.ProofComplexity.eval_univEvalCircuit`: exact simulation of any size-`≤ S` circuit
  `c`.


-/

public section

namespace CslibFrontier.ProofComplexity

open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime

/-! ### One-hot multiplexer `RawGate` primitive -/

/-- One-hot multiplexer gate chain of length `2 * ws.length`: starting from accumulator wire `acc`
at next gate index `cur`, computes `acc ∨ ⋁_{i < ws.length} (sel_{selBase + i} ∧ ws[i])`. -/
def muxGates (selBase cur acc : ℕ) : List ℕ → List RawGate
  | [] => []
  | w :: ws =>
    .and selBase w :: .or acc cur :: muxGates (selBase + 1) (cur + 2) (cur + 1) ws

/-- Exact length of `muxGates`: `2 * ws.length`. -/
@[simp]
theorem length_muxGates (selBase cur acc : ℕ) (ws : List ℕ) :
    (muxGates selBase cur acc ws).length = 2 * ws.length := by
  induction ws generalizing selBase cur acc with
  | nil => rfl
  | cons _ ws ih => simp [muxGates, ih, Nat.mul_succ]

/-- Indexed access into `muxGates selBase cur acc ws`. -/
theorem getElem_muxGates (selBase cur acc : ℕ) :
    ∀ (ws : List ℕ) (p : ℕ) (hp : p < 2 * ws.length),
      (muxGates selBase cur acc ws)[p]'(by simp [hp]) =
        let i := p / 2
        have hi : i < ws.length := by omega
        if p % 2 = 0 then .and (selBase + i) ws[i]
        else .or (if i = 0 then acc else cur + 2 * i - 1) (cur + 2 * i) := by
  intro ws; induction ws generalizing selBase cur acc with
  | nil => intro _ h; simp at h
  | cons w ws ih =>
    intro p hp
    cases p with
    | zero => simp [muxGates]
    | succ p =>
      cases p with
      | zero => simp [muxGates]
      | succ p =>
        simp only [muxGates, List.getElem_cons_succ]
        rw [ih (selBase + 1) (cur + 2) (cur + 1) p (by simp [Nat.mul_succ] at hp; omega)]
        have hd : (p + 2) / 2 = p / 2 + 1 := Nat.add_div_right p two_pos
        have hm : (p + 2) % 2 = p % 2 := Nat.add_mod_right p 2
        simp only [hd, hm, List.getElem_cons_succ, Nat.succ_ne_zero, ↓reduceIte]
        split_ifs with h1 h2
        · congr 1; omega
        · congr 1 <;> omega
        · congr 1 <;> omega

/-- Evaluating `muxGates` against a one-hot selector (`sel_{selBase + i} = decide (i = i₀)` with
`i₀ < ws.length`) and initial `acc = false` outputs `vals[ws[i₀]]` on its last wire. -/
private theorem eval_muxGates_oneHot :
    ∀ (ws : List ℕ) (selBase acc i₀ : ℕ) (vals : List Bool),
      (hi₀ : i₀ < ws.length) → acc < vals.length →
      (∀ i (hi : i < ws.length), selBase + i < vals.length ∧ ws[i] < vals.length) →
      (∀ i < ws.length, vals.getD (selBase + i) false = decide (i = i₀)) →
      (evalRawGates vals (muxGates selBase vals.length acc ws)).getD
        (vals.length + 2 * ws.length - 1) false =
        (vals.getD acc false || vals.getD ws[i₀] false) := by
  intro ws; induction ws with
  | nil => intro _ _ _ _ h; simp at h
  | cons w ws ih =>
    intro selBase acc i₀ vals hi₀ hacc hbd hsel
    set cur := vals.length
    have ⟨hs0, hw0⟩ := hbd 0 (by simp)
    simp only [add_zero, List.getElem_cons_zero] at hs0 hw0
    have hsel0 : vals.getD selBase false = decide (0 = i₀) := by
      simpa using hsel 0 (by simp)
    let bAnd := decide (0 = i₀) && vals.getD w false
    let bOr := vals.getD acc false || bAnd
    have hst1 : evalRawGate vals (.and selBase w) = bAnd := by
      rw [evalRawGate_and]
      have h1 : selBase < vals.length := hs0
      have h2 : w < vals.length := hw0
      simp only [h1, h2, decide_true, Bool.and_self, ↓reduceIte, hsel0, bAnd]
    set v1 := vals ++ [bAnd]
    have hv1_old {k : ℕ} (hk : k < cur) : v1.getD k false = vals.getD k false := by
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (by simp [v1]; omega), List.getElem?_eq_getElem hk,
        List.getElem_append_left hk]
    have hv1_cur : v1.getD cur false = bAnd := by simp [v1, cur, List.getD_eq_getElem?_getD]
    have hst2 : evalRawGate v1 (.or acc cur) = bOr := by
      have ha1 : acc < v1.length := by simp [v1]; omega
      have hc1 : cur < v1.length := by simp [v1, cur]
      rw [evalRawGate_or]
      simp only [ha1, hc1, decide_true, Bool.and_self, ↓reduceIte, hv1_old hacc, hv1_cur, bOr]
    set v2 := v1 ++ [bOr]
    have hv2_len : v2.length = cur + 2 := by simp [v2, v1, cur]
    have hv2_old {k : ℕ} (hk : k < cur) : v2.getD k false = vals.getD k false :=
      (by rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
            List.getElem?_eq_getElem (by rw [hv2_len]; omega),
            List.getElem?_eq_getElem (by simp [v1]; omega),
            List.getElem_append_left (by simp [v1]; omega)] :
          v2.getD k false = v1.getD k false).trans (hv1_old hk)
    have hv2_acc : v2.getD (cur + 1) false = bOr := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hv2_len]; omega),
        Option.getD_some, List.getElem_append_right (by simp [v1, cur])]
      simp [v1, cur]
    cases ws with
    | nil =>
      have hi00 : i₀ = 0 := by simp at hi₀; omega
      subst hi00
      simp only [muxGates, evalRawGates_cons, evalRawGates_nil, hst1]
      change (v1 ++ [evalRawGate v1 (.or acc cur)]).getD (cur + 1) false = _
      rw [hst2]; change v2.getD (cur + 1) false = _
      rw [hv2_acc]; simp [bOr, bAnd]
    | cons w₂ wt =>
      simp only [muxGates, evalRawGates_cons, hst1]
      change (evalRawGates (v1 ++ [evalRawGate v1 (.or acc cur)])
        (muxGates (selBase + 1) (cur + 2) (cur + 1) (w₂ :: wt))).getD
        (cur + 2 * (w :: w₂ :: wt).length - 1) false = _
      rw [hst2]
      change (evalRawGates v2 (muxGates (selBase + 1) (cur + 2) (cur + 1) (w₂ :: wt))).getD
        (cur + 2 * (w :: w₂ :: wt).length - 1) false = _
      have hidx_eq : cur + 2 * (w :: w₂ :: wt).length - 1 =
          v2.length + 2 * (w₂ :: wt).length - 1 := by rw [hv2_len]; simp [Nat.mul_succ]; omega
      rw [← hv2_len, hidx_eq]
      cases i₀ with
      | zero =>
        have hzero : ∀ (rs : List ℕ) (sb ac : ℕ) (vs : List Bool),
            ac < vs.length →
            (∀ j (hj : j < rs.length), sb + j < vs.length ∧ rs[j] < vs.length ∧
              vs.getD (sb + j) false = false) →
            (evalRawGates vs (muxGates sb vs.length ac rs)).getD
              (if rs = [] then ac else vs.length + 2 * rs.length - 1) false =
              vs.getD ac false := by
          intro rs; induction rs with
          | nil => intro _ _ _ _ _; simp [muxGates]
          | cons r rs' ihr =>
            intro sb ac vs hac hrs
            obtain ⟨hsb, hr0, hsf⟩ := hrs 0 (by simp)
            simp only [add_zero, List.getElem_cons_zero] at hsb hr0 hsf
            have he1 : evalRawGate vs (.and sb r) = false := by
              rw [evalRawGate_and]
              simp only [hsb, hr0, decide_true, Bool.and_self, ↓reduceIte, hsf, Bool.false_and]
            let u1 := vs ++ [false]
            have hu1o {k : ℕ} (hk : k < vs.length) : u1.getD k false = vs.getD k false := by
              rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
                List.getElem?_eq_getElem (by simp [u1]; omega), List.getElem?_eq_getElem hk,
                List.getElem_append_left hk]
            have hu1c : u1.getD vs.length false = false := by simp [u1, List.getD_eq_getElem?_getD]
            have he2 : evalRawGate u1 (.or ac vs.length) = vs.getD ac false := by
              have ha1 : ac < u1.length := by simp [u1]; omega
              have hc1 : vs.length < u1.length := by simp [u1]
              rw [evalRawGate_or]
              simp only [ha1, hc1, decide_true, Bool.and_self, ↓reduceIte, hu1o hac, hu1c,
                Bool.or_false]
            let u2 := u1 ++ [vs.getD ac false]
            have hu2l : u2.length = vs.length + 2 := by simp [u2, u1]
            have hu2a : u2.getD (vs.length + 1) false = vs.getD ac false := by
              rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hu2l]; omega),
                Option.getD_some, List.getElem_append_right (by simp [u1])]; simp [u1]
            have hu2o {k : ℕ} (hk : k < vs.length) : u2.getD k false = vs.getD k false := by
              rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hu2l]; omega),
                Option.getD_some, List.getElem_append_left (by simp [u1]; omega),
                List.getElem_append_left hk, List.getD_eq_getElem?_getD,
                List.getElem?_eq_getElem hk, Option.getD_some]
            have hrec := ihr (sb + 1) (vs.length + 1) u2 (by rw [hu2l]; omega) fun j hj => by
              obtain ⟨h1, h2, h3⟩ := hrs (j + 1) (by simp; omega)
              simp only [List.getElem_cons_succ,
                show sb + (j + 1) = sb + 1 + j by omega] at h1 h2 h3
              exact ⟨by rw [hu2l]; omega, by rw [hu2l]; omega, (hu2o h1).trans h3⟩
            rw [hu2a] at hrec
            simp only [muxGates, evalRawGates_cons, he1, List.cons_ne_nil, ↓reduceIte]
            change (evalRawGates (u1 ++ [evalRawGate u1 (.or ac vs.length)])
              (muxGates (sb + 1) (vs.length + 2) (vs.length + 1) rs')).getD _ false = _
            rw [he2]
            change (evalRawGates u2 (muxGates (sb + 1) (vs.length + 2) (vs.length + 1) rs')).getD
              _ false = _
            rw [← hu2l]
            cases rs' with
            | nil => simpa [muxGates, hu2l] using hu2a
            | cons r₂ rt =>
              simp only [List.cons_ne_nil, ↓reduceIte] at hrec
              rw [show vs.length + 2 * (r :: r₂ :: rt).length - 1 =
                u2.length + 2 * (r₂ :: rt).length - 1 by
                  rw [hu2l]; simp only [List.length_cons]; omega]
              exact hrec
        have hz := hzero (w₂ :: wt) (selBase + 1) (cur + 1) v2 (by rw [hv2_len]; omega)
          fun j hj => by
            have hj' : j + 1 < (w :: w₂ :: wt).length := by simp at hj ⊢; omega
            obtain ⟨h1, h2⟩ := hbd (j + 1) hj'
            have h3 := hsel (j + 1) hj'
            simp only [List.getElem_cons_succ,
              show selBase + (j + 1) = selBase + 1 + j by omega,
              Nat.succ_ne_zero, decide_false] at h1 h2 h3
            exact ⟨by rw [hv2_len]; omega, by rw [hv2_len]; omega, (hv2_old h1).trans h3⟩
        simp only [List.cons_ne_nil, ↓reduceIte] at hz
        rw [hz, hv2_acc]; simp [bOr, bAnd]
      | succ i₀' =>
        have hi₀' : i₀' < (w₂ :: wt).length := by simp only [List.length_cons] at hi₀ ⊢; omega
        rw [ih (selBase + 1) (cur + 1) i₀' v2 hi₀' (by rw [hv2_len]; omega)
          (fun j hj => by
            have hj' : j + 1 < (w :: w₂ :: wt).length := by simp at hj ⊢; omega
            obtain ⟨h1, h2⟩ := hbd (j + 1) hj'
            simp only [List.getElem_cons_succ, show selBase + (j + 1) = selBase + 1 + j by omega]
              at h1 h2
            exact ⟨by rw [hv2_len]; omega, by rw [hv2_len]; omega⟩)
          (fun j hj => by
            have hj' : j + 1 < (w :: w₂ :: wt).length := by simp at hj ⊢; omega
            have h1 := (hbd (j + 1) hj').1
            have h3 := hsel (j + 1) hj'
            simp only [show selBase + (j + 1) = selBase + 1 + j by omega] at h1 h3
            rw [hv2_old h1, h3]; simp)]
        rw [hv2_acc, hv2_old (by simpa using (hbd (i₀' + 1) hi₀).2)]
        simp [bOr, bAnd]

/-- `muxGates` is computable in uniform polynomial time. -/
private theorem computableInPolyTime_muxGates :
    ComputableInPolyTime
      (fun p : (ℕ × (ℕ × ℕ)) × List ℕ => muxGates p.1.1 p.1.2.1 p.1.2.2 p.2)
      (encPair (encPair encUnary (encPair encUnary encUnary)) (encList encUnary))
      (encList encRawGate) := by
  have heq_fn (sb cur acc : ℕ) (ws : List ℕ) :
      muxGates sb cur acc ws =
        ((List.range ws.length).map fun i =>
          let ac := if i = 0 then acc else cur + 2 * i - 1
          [RawGate.and (sb + i) (ws.getD i 0), RawGate.or ac (cur + 2 * i)]).flatten := by
    have h2len : ∀ (f : ℕ → List RawGate), (∀ i, (f i).length = 2) →
        ∀ k, (((List.range k).map f).flatten).length = 2 * k := by
      intro f hf k; induction k with
      | zero => simp
      | succ k ih =>
        rw [List.range_succ, List.map_append, List.flatten_append, List.length_append, ih]
        simp [hf]; omega
    refine List.ext_getElem (by rw [length_muxGates, h2len _ (fun _ => rfl)]) fun p h₁ _ => ?_
    rw [length_muxGates] at h₁
    rw [getElem_muxGates sb cur acc ws p h₁]
    have hfl : ∀ k (q : ℕ) (hq : q < 2 * k) (f : ℕ → RawGate × RawGate),
        (((List.range k).map fun i => [(f i).1, (f i).2]).flatten)[q]'(by
          rw [h2len _ (fun _ => rfl)]; exact hq) =
        if q % 2 = 0 then (f (q / 2)).1 else (f (q / 2)).2 := by
      intro k; induction k with
      | zero => intro _ h; omega
      | succ k ih =>
        intro q hq f
        have hlen := h2len (fun i => [(f i).1, (f i).2]) (fun _ => rfl)
        simp only [List.range_succ, List.map_append, List.flatten_append]
        by_cases hqk : q < 2 * k
        · rw [List.getElem_append_left (by rw [hlen]; exact hqk)]; exact ih q hqk f
        · rw [List.getElem_append_right (by rw [hlen]; omega)]
          simp only [hlen, List.map_singleton, List.flatten_cons, List.flatten_nil, List.append_nil]
          have hd : q / 2 = k := by omega
          rcases (show q - 2 * k = 0 ∨ q - 2 * k = 1 by omega) with h0 | h1
          · have hm : q % 2 = 0 := by omega
            simp [h0, hd, hm]
          · have hm : q % 2 = 1 := by omega
            simp [h1, hd, hm]
    rw [hfl ws.length p h₁ (fun i =>
      (RawGate.and (sb + i) (ws.getD i 0),
       RawGate.or (if i = 0 then acc else cur + 2 * i - 1) (cur + 2 * i)))]
    have hi : p / 2 < ws.length := by omega
    have hgd : ws.getD (p / 2) 0 = ws[p / 2] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
    rw [hgd]
  let EP := encPair encUnary (encPair encUnary encUnary)
  let E := encPair EP (encList encUnary)
  have hsb := (fst encUnary (encPair encUnary encUnary)).comp (fst EP (encList encUnary))
  have hcur := (fst encUnary encUnary).comp
    ((snd encUnary (encPair encUnary encUnary)).comp (fst EP (encList encUnary)))
  have hacc := (snd encUnary encUnary).comp
    ((snd encUnary (encPair encUnary encUnary)).comp (fst EP (encList encUnary)))
  have hws := snd EP (encList encUnary)
  have hmap : ComputableInPolyTime
      (fun p : (ℕ × (ℕ × ℕ)) × List ℕ => (List.range p.2.length).map fun i =>
        let ac := if i = 0 then p.1.2.2 else p.1.2.1 + 2 * i - 1
        [RawGate.and (p.1.1 + i) (p.2.getD i 0), RawGate.or ac (p.1.2.1 + 2 * i)])
      E (encList (encList encRawGate)) := by
    refine mapWithInput (range.comp ((length encUnary).comp hws)) ?_
    have hp := fst E encUnary; have hi := snd E encUnary
    have h2i := unary_mul' (const 2) hi
    have hc2i := unary_add' (hcur.comp hp) h2i
    have hac := ite_decide (unary_beq hi (const 0)) (hacc.comp hp) (unary_sub' hc2i (const 1))
    have hg1 := computableInPolyTime_rawGate_and.comp
      ((unary_add' (hsb.comp hp) hi).prod (listGetDWithInput (hws.comp hp) hi 0))
    have hg2 := computableInPolyTime_rawGate_or.comp (hac.prod hc2i)
    exact (cons encRawGate).comp (hg1.prod ((cons encRawGate).comp (hg2.prod (const []))))
  exact ((flatten encRawGate).comp hmap).of_enc_eq fun p => by
    dsimp only [Function.comp_apply]; rw [heq_fn]

/-! ### Universal De Morgan circuit evaluator construction -/

/-- Step chunk size in description bits for a single simulated gate in `univEvalCircuit k m S`. -/
@[expose] def univGateDescStride (k S : ℕ) : ℕ := 5 + 2 * (k + S)

/-- Total description bit length `ℓ(k, m, S)` of a `k`-input, `m`-output, size-`≤ S` circuit. -/
@[expose] def univDescLen (k m S : ℕ) : ℕ := S * univGateDescStride k S + m * (k + S)

/-- Gate count emitted for each simulated gate step `r < S` in `univRawGates`. -/
@[expose] def univStepGateCount (k S : ℕ) : ℕ := 4 * (k + S) + 20

/-- Raw wire index of simulated gate `r`'s output wire inside `univEvalCircuit k m S`. -/
@[expose] def univSimGateWire (k m S r : ℕ) : ℕ :=
  (univDescLen k m S + k) + 1 + (r + 1) * univStepGateCount k S - 1

/-- List of `k + S` selectable wire indices for simulated gate `r`. -/
@[expose] def univAvailWires (k m S r : ℕ) : List ℕ :=
  let ℓ := univDescLen k m S; let falseW := ℓ + k
  ((List.range k).map (ℓ + ·)) ++
    ((List.range S).map fun t => if t < r then univSimGateWire k m S t else falseW)

/-- Exact length of `univAvailWires k m S r`. -/
@[simp] theorem length_univAvailWires (k m S r : ℕ) :
    (univAvailWires k m S r).length = k + S := by simp [univAvailWires]

/-- Single simulated-gate block of exact length `univStepGateCount k S` for step `r < S`. -/
@[expose] def univGateBlock (k m S r : ℕ) : List RawGate :=
  let ℓ := univDescLen k m S; let falseW := ℓ + k
  let base := r * univGateDescStride k S; let opBase := base
  let s1Base := base + 5; let s2Base := s1Base + (k + S)
  let ws := univAvailWires k m S r
  let cur0 := falseW + 1 + r * univStepGateCount k S
  let mux1 := muxGates s1Base cur0 falseW ws
  let a1 := cur0 + 2 * (k + S) - 1; let cur1 := cur0 + 2 * (k + S)
  let mux2 := muxGates s2Base cur1 falseW ws
  let a2 := cur1 + 2 * (k + S) - 1; let b0 := cur1 + 2 * (k + S)
  let ops : List RawGate :=
    [ .const false, .const true, .and (opBase + 2) a1, .not (b0 + 2),
      .and (opBase + 3) a1, .and (opBase + 3) a2, .and (b0 + 4) (b0 + 5),
      .and (opBase + 4) a1, .and (opBase + 4) a2, .or (b0 + 7) (b0 + 8) ]
  let muxOp := muxGates opBase (b0 + 10) falseW [b0, b0 + 1, b0 + 3, b0 + 6, b0 + 9]
  mux1 ++ mux2 ++ ops ++ muxOp

/-- Exact gate count of `univGateBlock k m S r`. -/
@[simp] theorem length_univGateBlock (k m S r : ℕ) :
    (univGateBlock k m S r).length = univStepGateCount k S := by
  simp [univGateBlock, univStepGateCount]; omega

/-- Single output-selection mux block of exact length `2 * (k + S)` for output `j < m`. -/
@[expose] def univOutBlock (k m S j : ℕ) : List RawGate :=
  let ℓ := univDescLen k m S; let falseW := ℓ + k
  let selBase := S * univGateDescStride k S + j * (k + S)
  let cur := falseW + 1 + S * univStepGateCount k S + j * (2 * (k + S))
  muxGates selBase cur falseW (univAvailWires k m S S)

/-- Exact gate count of `univOutBlock k m S j`. -/
@[simp] theorem length_univOutBlock (k m S j : ℕ) :
    (univOutBlock k m S j).length = 2 * (k + S) := by simp [univOutBlock]

/-- Complete `RawGate` list for the universal De Morgan circuit evaluator on `(k, m, S)`. -/
@[expose] def univRawGates (k m S : ℕ) : List RawGate :=
  RawGate.const false ::
    (((List.range S).map (univGateBlock k m S)).flatten ++
     ((List.range m).map (univOutBlock k m S)).flatten)

/-- Exact gate count of `univRawGates k m S`. -/
@[simp] theorem length_univRawGates (k m S : ℕ) :
    (univRawGates k m S).length = 1 + S * univStepGateCount k S + m * (2 * (k + S)) := by
  have h1 : ∀ n, (((List.range n).map (univGateBlock k m S)).flatten).length =
      n * univStepGateCount k S := by
    intro n; induction n with
    | zero => simp
    | succ n ih =>
      rw [List.range_succ, List.map_append, List.flatten_append, List.length_append, ih]
      simp [Nat.succ_mul]
  have h2 : ∀ n, (((List.range n).map (univOutBlock k m S)).flatten).length =
      n * (2 * (k + S)) := by
    intro n; induction n with
    | zero => simp
    | succ n ih =>
      rw [List.range_succ, List.map_append, List.flatten_append, List.length_append, ih]
      simp [Nat.succ_mul]
  simp only [univRawGates, List.length_cons, List.length_append, h1, h2]; omega

/-- Output wire index list of length `m` for the universal De Morgan circuit evaluator. -/
@[expose] def univRawOuts (k m S : ℕ) : List ℕ :=
  let start := (univDescLen k m S + k) + 1 + S * univStepGateCount k S
  (List.range m).map fun j =>
    if k + S = 0 then univDescLen k m S + k else start + (j + 1) * (2 * (k + S)) - 1

/-- Exact output count of `univRawOuts k m S`. -/
@[simp] theorem length_univRawOuts (k m S : ℕ) : (univRawOuts k m S).length = m := by
  simp [univRawOuts]

/-- Every output wire index in `univRawOuts k m S` is strictly less than
`(univDescLen k m S + k) + (univRawGates k m S).length`. -/
theorem univRawOuts_lt (k m S : ℕ) (j : Fin (univRawOuts k m S).length) :
    (univRawOuts k m S)[j.val] < (univDescLen k m S + k) + (univRawGates k m S).length := by
  have hjm : j.val < m := by simpa using j.isLt
  simp only [univRawOuts, List.getElem_map, List.getElem_range, length_univRawGates]
  split_ifs with h0
  · omega
  · have : (j.val + 1) * (2 * (k + S)) ≤ m * (2 * (k + S)) := Nat.mul_le_mul_right _ hjm
    omega

/-- `univRawGates` is computable in uniform polynomial time from `(k, m, S)` in unary. -/
theorem computableInPolyTime_univRawGates :
    ComputableInPolyTime (fun p : ℕ × (ℕ × ℕ) => univRawGates p.1 p.2.1 p.2.2)
      (encPair encUnary (encPair encUnary encUnary)) (encList encRawGate) := by
  let E := encPair encUnary (encPair encUnary encUnary)
  have hk := fst encUnary (encPair encUnary encUnary)
  have hm := (fst encUnary encUnary).comp (snd encUnary (encPair encUnary encUnary))
  have hS := (snd encUnary encUnary).comp (snd encUnary (encPair encUnary encUnary))
  have hkS := unary_add' hk hS
  have hstride : ComputableInPolyTime (fun p : ℕ × (ℕ × ℕ) => univGateDescStride p.1 p.2.2)
      E encUnary := unary_add' (const 5) (unary_mul' (const 2) hkS)
  have hdesc : ComputableInPolyTime (fun p : ℕ × (ℕ × ℕ) => univDescLen p.1 p.2.1 p.2.2)
      E encUnary := unary_add' (unary_mul' hS hstride) (unary_mul' hm hkS)
  have hfw := unary_add' hdesc hk
  have hstepCnt : ComputableInPolyTime (fun p : ℕ × (ℕ × ℕ) => univStepGateCount p.1 p.2.2)
      E encUnary := unary_add' (unary_mul' (const 4) hkS) (const 20)
  let ER := encPair E encUnary
  have havail : ComputableInPolyTime
      (fun q : (ℕ × (ℕ × ℕ)) × ℕ => univAvailWires q.1.1 q.1.2.1 q.1.2.2 q.2)
      ER (encList encUnary) := by
    have hp := fst E encUnary; have hr := snd E encUnary
    have hpart1 : ComputableInPolyTime
        (fun q : (ℕ × (ℕ × ℕ)) × ℕ =>
          (List.range q.1.1).map (univDescLen q.1.1 q.1.2.1 q.1.2.2 + ·))
        ER (encList encUnary) :=
      mapWithInput (range.comp (hk.comp hp))
        (unary_add' ((hdesc.comp hp).comp (fst ER encUnary)) (snd ER encUnary))
    have hpart2 : ComputableInPolyTime
        (fun q : (ℕ × (ℕ × ℕ)) × ℕ => (List.range q.1.2.2).map fun t =>
          if t < q.2 then univSimGateWire q.1.1 q.1.2.1 q.1.2.2 t
          else univDescLen q.1.1 q.1.2.1 q.1.2.2 + q.1.1)
        ER (encList encUnary) := by
      refine mapWithInput (range.comp (hS.comp hp)) ?_
      have hq := fst ER encUnary; have ht := snd ER encUnary
      have hsimw := unary_sub'
        (unary_add' (unary_add' ((hfw.comp hp).comp hq) (const 1))
          (unary_mul' (unary_add' ht (const 1)) ((hstepCnt.comp hp).comp hq)))
        (const 1)
      exact ite_decide (unary_lt.comp (ht.prod (hr.comp hq))) hsimw ((hfw.comp hp).comp hq)
    exact (listAppend encUnary).comp (hpart1.prod hpart2)
  have hgblock : ComputableInPolyTime
      (fun q : (ℕ × (ℕ × ℕ)) × ℕ => univGateBlock q.1.1 q.1.2.1 q.1.2.2 q.2)
      ER (encList encRawGate) := by
    have hp := fst E encUnary; have hr := snd E encUnary
    have hfw' := hfw.comp hp; have hkS' := hkS.comp hp
    have h2kS := unary_mul' (const 2) hkS'
    have hopB := unary_mul' hr (hstride.comp hp)
    have hs1B := unary_add' hopB (const 5)
    have hs2B := unary_add' hs1B hkS'
    have hcur0 := unary_add' (unary_add' hfw' (const 1)) (unary_mul' hr (hstepCnt.comp hp))
    have ha1 := unary_sub' (unary_add' hcur0 h2kS) (const 1)
    have hcur1 := unary_add' hcur0 h2kS
    have ha2 := unary_sub' (unary_add' hcur1 h2kS) (const 1)
    have hb0 := unary_add' hcur1 h2kS
    have hmux1 := computableInPolyTime_muxGates.comp ((hs1B.prod (hcur0.prod hfw')).prod havail)
    have hmux2 := computableInPolyTime_muxGates.comp ((hs2B.prod (hcur1.prod hfw')).prod havail)
    let mkC (g : ((ℕ × (ℕ × ℕ)) × ℕ) → RawGate)
        (hg : ComputableInPolyTime g ER encRawGate)
        {rest : ((ℕ × (ℕ × ℕ)) × ℕ) → List RawGate}
        (hr : ComputableInPolyTime rest ER (encList encRawGate)) :
        ComputableInPolyTime (fun q => g q :: rest q) ER (encList encRawGate) :=
      (cons encRawGate).comp (hg.prod hr)
    have hand_mk (x y : ((ℕ × (ℕ × ℕ)) × ℕ) → ℕ)
        (hx : ComputableInPolyTime x ER encUnary) (hy : ComputableInPolyTime y ER encUnary) :=
      computableInPolyTime_rawGate_and.comp (hx.prod hy)
    have hor_mk (x y : ((ℕ × (ℕ × ℕ)) × ℕ) → ℕ)
        (hx : ComputableInPolyTime x ER encUnary) (hy : ComputableInPolyTime y ER encUnary) :=
      computableInPolyTime_rawGate_or.comp (hx.prod hy)
    have hops :=
      mkC _ (computableInPolyTime_rawGate_const.comp (const false)) <|
      mkC _ (computableInPolyTime_rawGate_const.comp (const true)) <|
      mkC _ (hand_mk _ _ (unary_add' hopB (const 2)) ha1) <|
      mkC _ (computableInPolyTime_rawGate_not.comp (unary_add' hb0 (const 2))) <|
      mkC _ (hand_mk _ _ (unary_add' hopB (const 3)) ha1) <|
      mkC _ (hand_mk _ _ (unary_add' hopB (const 3)) ha2) <|
      mkC _ (hand_mk _ _ (unary_add' hb0 (const 4)) (unary_add' hb0 (const 5))) <|
      mkC _ (hand_mk _ _ (unary_add' hopB (const 4)) ha1) <|
      mkC _ (hand_mk _ _ (unary_add' hopB (const 4)) ha2) <|
      mkC _ (hor_mk _ _ (unary_add' hb0 (const 7)) (unary_add' hb0 (const 8))) (const [])
    let mkU (u : _ → ℕ) (hu : ComputableInPolyTime u ER encUnary)
        {rest : _ → List ℕ} (hrest : ComputableInPolyTime rest ER (encList encUnary)) :
        ComputableInPolyTime (fun q => u q :: rest q) ER (encList encUnary) :=
      (cons encUnary).comp (hu.prod hrest)
    have hopWs := mkU _ hb0 <| mkU _ (unary_add' hb0 (const 1)) <|
      mkU _ (unary_add' hb0 (const 3)) <| mkU _ (unary_add' hb0 (const 6)) <|
      mkU _ (unary_add' hb0 (const 9)) (const [])
    have hmuxOp := computableInPolyTime_muxGates.comp
      ((hopB.prod ((unary_add' hb0 (const 10)).prod hfw')).prod hopWs)
    exact (listAppend encRawGate).comp
      (((listAppend encRawGate).comp
        (((listAppend encRawGate).comp (hmux1.prod hmux2)).prod hops)).prod hmuxOp)
  have hoblock : ComputableInPolyTime
      (fun q : (ℕ × (ℕ × ℕ)) × ℕ => univOutBlock q.1.1 q.1.2.1 q.1.2.2 q.2)
      ER (encList encRawGate) := by
    have hp := fst E encUnary; have hj := snd E encUnary
    have hfw' := hfw.comp hp; have hkS' := hkS.comp hp
    have hsb := unary_add' (unary_mul' (hS.comp hp) (hstride.comp hp)) (unary_mul' hj hkS')
    have hcur := unary_add'
      (unary_add' (unary_add' hfw' (const 1)) (unary_mul' (hS.comp hp) (hstepCnt.comp hp)))
      (unary_mul' hj (unary_mul' (const 2) hkS'))
    exact computableInPolyTime_muxGates.comp
      ((hsb.prod (hcur.prod hfw')).prod (havail.comp (hp.prod (hS.comp hp))))
  have hmbG : ComputableInPolyTime
      (fun p : ℕ × (ℕ × ℕ) => (List.range p.2.2).map (univGateBlock p.1 p.2.1 p.2.2))
      E (encList (encList encRawGate)) := mapWithInput (range.comp hS) hgblock
  have hmbO : ComputableInPolyTime
      (fun p : ℕ × (ℕ × ℕ) => (List.range p.2.1).map (univOutBlock p.1 p.2.1 p.2.2))
      E (encList (encList encRawGate)) := mapWithInput (range.comp hm) hoblock
  have hallG := (flatten encRawGate).comp hmbG
  have hallO := (flatten encRawGate).comp hmbO
  exact (cons encRawGate).comp
    ((computableInPolyTime_rawGate_const.comp (const false)).prod
      ((listAppend encRawGate).comp (hallG.prod hallO)))

/-- `univRawOuts` is computable in uniform polynomial time from `(k, m, S)` in unary. -/
theorem computableInPolyTime_univRawOuts :
    ComputableInPolyTime (fun p : ℕ × (ℕ × ℕ) => univRawOuts p.1 p.2.1 p.2.2)
      (encPair encUnary (encPair encUnary encUnary)) (encList encUnary) := by
  let E := encPair encUnary (encPair encUnary encUnary)
  have hk := fst encUnary (encPair encUnary encUnary)
  have hm := (fst encUnary encUnary).comp (snd encUnary (encPair encUnary encUnary))
  have hS := (snd encUnary encUnary).comp (snd encUnary (encPair encUnary encUnary))
  have hkS := unary_add' hk hS
  have hstride := unary_add' (const 5) (unary_mul' (const 2) hkS)
  have hfw := unary_add' (unary_add' (unary_mul' hS hstride) (unary_mul' hm hkS)) hk
  have hstart := unary_add' (unary_add' hfw (const 1))
    (unary_mul' hS (unary_add' (unary_mul' (const 4) hkS) (const 20)))
  refine mapWithInput (range.comp hm) ?_
  have hp := fst E encUnary; have hj := snd E encUnary
  exact ite_decide (unary_beq (hkS.comp hp) (const 0)) (hfw.comp hp)
    (unary_sub' (unary_add' (hstart.comp hp)
      (unary_mul' (unary_add' hj (const 1)) (unary_mul' (const 2) (hkS.comp hp)))) (const 1))

/-- **Universal De Morgan circuit evaluator** `U_{k, m, S}` (`1 ≤ k`): takes a
`univDescLen k m S`-bit circuit description `v` and a `k`-bit input `u`, outputting `m` bits. -/
@[expose]
def univEvalCircuit (k m S : ℕ) (hk : 1 ≤ k) : Circuit signature (univDescLen k m S + k) m :=
  let raw := buildRawCircuit (univDescLen k m S + k) (by omega) (univRawGates k m S)
    (univRawOuts k m S)
  { size := raw.size
    program := raw.program
    outputs := fun j => raw.outputs (j.cast (length_univRawOuts k m S).symm) }

/-- Exact gate size of `univEvalCircuit k m S hk`. -/
@[simp]
theorem size_univEvalCircuit (k m S : ℕ) (hk : 1 ≤ k) :
    (univEvalCircuit k m S hk).size = 1 + S * univStepGateCount k S + m * (2 * (k + S)) :=
  length_univRawGates k m S

/-- First-order list evaluator `(k, m, S, vu) ↦ U_{k, m, S}(vu)`. -/
def univEvalList (k m S : ℕ) (vu : List Bool) : List Bool :=
  let vals := evalRawGates vu (univRawGates k m S)
  (univRawOuts k m S).map fun idx => vals.getD idx false

/-- Exact output length of `univEvalList k m S vu`. -/
@[simp]
theorem length_univEvalList (k m S : ℕ) (vu : List Bool) :
    (univEvalList k m S vu).length = m := by
  simp [univEvalList]

/-- `univEvalList` agrees with `(univEvalCircuit k m S hk).eval` on every input bitstring. -/
theorem univEvalList_ofFn (k m S : ℕ) (hk : 1 ≤ k)
    (vu : BitString (univDescLen k m S + k)) :
    univEvalList k m S (List.ofFn vu) =
      List.ofFn ((univEvalCircuit k m S hk).eval interpretation vu) :=
  List.ext_getElem (by simp) fun j _ h₂ => by
    simp only [List.length_ofFn] at h₂
    have hjo : j < (univRawOuts k m S).length := by simp [h₂]
    simp only [univEvalList, List.getElem_map, List.getElem_ofFn]
    exact (eval_buildRawCircuit (univDescLen k m S + k) (by omega)
      (univRawGates k m S) (univRawOuts k m S) (univRawOuts_lt k m S) vu ⟨j, hjo⟩).symm

/-- `univEvalList` is computable in uniform polynomial time. -/
theorem computableInPolyTime_univEvalList :
    ComputableInPolyTime
      (fun p : (ℕ × (ℕ × ℕ)) × List Bool => univEvalList p.1.1 p.1.2.1 p.1.2.2 p.2)
      (encPair (encPair encUnary (encPair encUnary encUnary)) encBits) encBits := by
  let EP := encPair encUnary (encPair encUnary encUnary)
  let E := encPair EP encBits
  have hp := fst EP encBits; have hvu := snd EP encBits
  have hvals := computableInPolyTime_evalRawGates.comp
    (hvu.prod (computableInPolyTime_univRawGates.comp hp))
  exact listToBits.comp (mapWithInput (computableInPolyTime_univRawOuts.comp hp)
    (bitsGetDWithInput (hvals.comp (fst E encUnary)) (snd E encUnary) false))

/-! ### Canonical one-hot circuit encoding and evaluation soundness -/

/-- Opcode code in `0 .. 4` of a `Boolean.Op`. -/
@[expose] def opToCode : Boolean.Op → Fin 5
  | .const false => 0 | .const true => 1 | .not => 2 | .and => 3 | .or => 4

/-- First operand index `< k + g` of a De Morgan gate line (defaulting to `0` for nullary ops). -/
@[expose] def lineArg0 {k g : ℕ} (l : Line signature k g) : ℕ :=
  match l with
  | ⟨.const _, _⟩ => 0 | ⟨.not, ws⟩ => wireToNat (ws 0)
  | ⟨.and, ws⟩ => wireToNat (ws 0) | ⟨.or, ws⟩ => wireToNat (ws 0)

/-- `lineArg0` of a constant gate is `0`. -/
@[simp] theorem lineArg0_const {k g : ℕ} (b : Bool) (ws : Fin 0 → Wire k g) :
    lineArg0 ⟨.const b, ws⟩ = 0 := rfl

/-- Second operand index `< k + g` of a De Morgan gate line (defaulting to `0` for arity `< 2`). -/
@[expose] def lineArg1 {k g : ℕ} (l : Line signature k g) : ℕ :=
  match l with
  | ⟨.const _, _⟩ => 0 | ⟨.not, _⟩ => 0
  | ⟨.and, ws⟩ => wireToNat (ws 1) | ⟨.or, ws⟩ => wireToNat (ws 1)

/-- `lineArg1` of a constant gate is `0`. -/
@[simp] theorem lineArg1_const {k g : ℕ} (b : Bool) (ws : Fin 0 → Wire k g) :
    lineArg1 ⟨.const b, ws⟩ = 0 := rfl

/-- `lineArg1` of a negation gate is `0`. -/
@[simp] theorem lineArg1_not {k g : ℕ} (ws : Fin 1 → Wire k g) :
    lineArg1 ⟨.not, ws⟩ = 0 := rfl

private theorem lineArg0_lt {k g : ℕ} (hk : 1 ≤ k) (l : Line signature k g) :
    lineArg0 l < k + g := by
  rcases l with ⟨op, ws⟩
  cases op <;> first | (simp [lineArg0]; omega) | exact wireToNat_lt (ws 0)

private theorem lineArg1_lt {k g : ℕ} (hk : 1 ≤ k) (l : Line signature k g) :
    lineArg1 l < k + g := by
  rcases l with ⟨op, ws⟩
  cases op <;> first | (simp [lineArg1]; omega) | exact wireToNat_lt (ws 1)

/-- **Canonical one-hot description** `encodeCircuit c S hS : BitString (univDescLen k m S)` of any
De Morgan circuit `c : Circuit signature k m` with `c.size ≤ S` (padding unused gate slots
`c.size ≤ r < S` with `const false`). -/
def encodeCircuit {k m : ℕ} (c : Circuit signature k m) (S : ℕ) (_hS : c.size ≤ S) :
    BitString (univDescLen k m S) := fun pos =>
  let stride := univGateDescStride k S
  if pos.val < S * stride then
    let r := pos.val / stride
    let off := pos.val % stride
    let (opc, a0, a1) : ℕ × ℕ × ℕ :=
      if hr : r < c.size then
        let l := c.program.lines ⟨r, hr⟩
        ((opToCode l.op).val, lineArg0 l, lineArg1 l)
      else (0, 0, 0)
    if off < 5 then decide (off = opc)
    else if off < 5 + (k + S) then decide (off - 5 = a0)
    else decide (off - (5 + (k + S)) = a1)
  else
    let rem := pos.val - S * stride
    let j := rem / (k + S)
    let idx := rem % (k + S)
    if hj : j < m then decide (idx = wireToNat (c.outputs ⟨j, hj⟩))
    else false

private theorem encodeCircuit_gate_bit {k m : ℕ} (c : Circuit signature k m) (S : ℕ)
    (hS : c.size ≤ S) {r off : ℕ} (hr : r < S) (hoff : off < univGateDescStride k S) :
    encodeCircuit c S hS ⟨r * univGateDescStride k S + off, by
      have := Nat.mul_le_mul_right (univGateDescStride k S) hr
      rw [Nat.succ_mul] at this; dsimp [univDescLen] at *; omega⟩ =
      let p : ℕ × ℕ × ℕ :=
        if hrc : r < c.size then
          let l := c.program.lines ⟨r, hrc⟩
          ((opToCode l.op).val, lineArg0 l, lineArg1 l)
        else (0, 0, 0)
      if off < 5 then decide (off = p.1)
      else if off < 5 + (k + S) then decide (off - 5 = p.2.1)
      else decide (off - (5 + (k + S)) = p.2.2) := by
  set st := univGateDescStride k S
  have hlt : r * st + off < S * st := by
    have := Nat.mul_le_mul_right st hr; rw [Nat.succ_mul] at this; omega
  have hd : (r * st + off) / st = r := by
    rw [mul_comm r, Nat.mul_add_div (by omega), Nat.div_eq_of_lt hoff, add_zero]
  have hm : (r * st + off) % st = off := by
    rw [mul_comm r, Nat.mul_add_mod, Nat.mod_eq_of_lt hoff]
  dsimp only [encodeCircuit]
  change (if r * st + off < S * st then
    let r0 := (r * st + off) / st; let o0 := (r * st + off) % st
    let p : ℕ × ℕ × ℕ := if hr : r0 < c.size then
      let l := c.program.lines ⟨r0, hr⟩; ((opToCode l.op).val, lineArg0 l, lineArg1 l)
    else (0, 0, 0)
    if o0 < 5 then decide (o0 = p.1)
    else if o0 < 5 + (k + S) then decide (o0 - 5 = p.2.1)
    else decide (o0 - (5 + (k + S)) = p.2.2) else _) = _
  rw [ite_eq_left hlt]; simp only [hd, hm]

/-- Structural lemma `encodeCircuit_op`. -/
theorem encodeCircuit_op {k m : ℕ} (c : Circuit signature k m) (S : ℕ) (hS : c.size ≤ S)
    {r t : ℕ} (hr : r < S) (ht : t < 5) :
    encodeCircuit c S hS ⟨r * univGateDescStride k S + t, by
      have := Nat.mul_le_mul_right (univGateDescStride k S) hr
      rw [Nat.succ_mul] at this; dsimp [univDescLen, univGateDescStride] at *; omega⟩ =
      decide
        (t = if hrc : r < c.size then (opToCode (c.program.lines ⟨r, hrc⟩).op).val else 0) := by
  rw [encodeCircuit_gate_bit c S hS hr (by dsimp [univGateDescStride]; omega)]
  simp only [ht, ↓reduceIte]; split_ifs <;> rfl

/-- Structural lemma `encodeCircuit_arg0`. -/
theorem encodeCircuit_arg0 {k m : ℕ} (c : Circuit signature k m) (S : ℕ) (hS : c.size ≤ S)
    {r idx : ℕ} (hr : r < S) (hi : idx < k + S) :
    encodeCircuit c S hS ⟨r * univGateDescStride k S + 5 + idx, by
      have := Nat.mul_le_mul_right (univGateDescStride k S) hr
      rw [Nat.succ_mul] at this; dsimp [univDescLen, univGateDescStride] at *; omega⟩ =
      decide (idx = if hrc : r < c.size then lineArg0 (c.program.lines ⟨r, hrc⟩) else 0) := by
  refine (congrArg (encodeCircuit c S hS) (Fin.ext (b := ⟨r * univGateDescStride k S + (5 + idx), by
    have := Nat.mul_le_mul_right (univGateDescStride k S) hr
    rw [Nat.succ_mul] at this; dsimp [univDescLen, univGateDescStride] at *; omega⟩)
    (by dsimp; omega))).trans ?_
  rw [encodeCircuit_gate_bit c S hS hr (by dsimp [univGateDescStride]; omega)]
  simp only [show ¬(5 + idx < 5) by omega, show 5 + idx < 5 + (k + S) by omega, ↓reduceIte,
    Nat.add_sub_cancel_left]
  split_ifs <;> rfl

/-- Structural lemma `encodeCircuit_arg1`. -/
theorem encodeCircuit_arg1 {k m : ℕ} (c : Circuit signature k m) (S : ℕ) (hS : c.size ≤ S)
    {r idx : ℕ} (hr : r < S) (hi : idx < k + S) :
    encodeCircuit c S hS ⟨r * univGateDescStride k S + 5 + (k + S) + idx, by
      have := Nat.mul_le_mul_right (univGateDescStride k S) hr
      rw [Nat.succ_mul] at this; dsimp [univDescLen, univGateDescStride] at *; omega⟩ =
      decide (idx = if hrc : r < c.size then lineArg1 (c.program.lines ⟨r, hrc⟩) else 0) := by
  refine (congrArg (encodeCircuit c S hS)
    (Fin.ext (b := ⟨r * univGateDescStride k S + (5 + (k + S) + idx), by
      have := Nat.mul_le_mul_right (univGateDescStride k S) hr
      rw [Nat.succ_mul] at this; dsimp [univDescLen, univGateDescStride] at *; omega⟩)
      (by dsimp; omega))).trans ?_
  rw [encodeCircuit_gate_bit c S hS hr (by dsimp [univGateDescStride]; omega)]
  simp only [show ¬(5 + (k + S) + idx < 5) by omega,
    show ¬(5 + (k + S) + idx < 5 + (k + S)) by omega, ↓reduceIte, Nat.add_sub_cancel_left]
  split_ifs <;> rfl

/-- Structural lemma `encodeCircuit_out`. -/
theorem encodeCircuit_out {k m : ℕ} (c : Circuit signature k m) (S : ℕ) (hS : c.size ≤ S)
    (j : Fin m) {idx : ℕ} (hi : idx < k + S) :
    encodeCircuit c S hS ⟨S * univGateDescStride k S + j.val * (k + S) + idx, by
      have := Nat.mul_le_mul_right (k + S) j.isLt
      rw [Nat.succ_mul] at this; dsimp [univDescLen]; omega⟩ =
      decide (idx = wireToNat (c.outputs j)) := by
  set st := univGateDescStride k S
  have hnl : ¬(S * st + j.val * (k + S) + idx < S * st) := by omega
  have hrem : S * st + j.val * (k + S) + idx - S * st = j.val * (k + S) + idx := by omega
  have hd : (j.val * (k + S) + idx) / (k + S) = j.val := by
    rw [mul_comm j.val, Nat.mul_add_div (by omega), Nat.div_eq_of_lt hi, add_zero]
  have hm : (j.val * (k + S) + idx) % (k + S) = idx := by
    rw [mul_comm j.val, Nat.mul_add_mod, Nat.mod_eq_of_lt hi]
  simp [encodeCircuit, st, hnl, hrem, hd, hm, j.isLt]

/-- Structural lemma `getElem_univAvailWires`. -/
theorem getElem_univAvailWires (k m S r idx : ℕ) (hi : idx < k + S) :
    (univAvailWires k m S r)[idx]'(by simp [hi]) =
      if idx < k then univDescLen k m S + idx
      else if idx - k < r then univSimGateWire k m S (idx - k)
      else univDescLen k m S + k := by
  let a := (List.range k).map (univDescLen k m S + ·)
  let b := (List.range S).map fun t =>
    if t < r then univSimGateWire k m S t else univDescLen k m S + k
  change (a ++ b)[idx]'(by simp [a, b, hi]) = _
  by_cases hik : idx < k
  · rw [List.getElem_append_left (by simp [a, hik])]; simp [a, hik]
  · rw [List.getElem_append_right (by simp [a]; omega)]; simp [a, b, hik]

/-- Structural lemma `univAvailWires_lt`. -/
theorem univAvailWires_lt (k m S r idx : ℕ) (hi : idx < k + S) :
    (univAvailWires k m S r)[idx]'(by simp [hi]) <
      (univDescLen k m S + k) + 1 + r * univStepGateCount k S := by
  rw [getElem_univAvailWires k m S r idx hi]
  split_ifs with h1 h2
  · omega
  · dsimp only [univSimGateWire, univStepGateCount]
    have hmul : (idx - k + 1) * (4 * (k + S) + 20) ≤ r * (4 * (k + S) + 20) :=
      Nat.mul_le_mul_right (4 * (k + S) + 20) h2
    omega
  · omega

/-- Evaluating `pr : Program signature k g` at gate `idx` equals evaluating `pr.lines idx`. -/
private theorem program_eval_eq_lines {k g : ℕ} (pr : Program signature k g) (u : BitString k)
    (idx : Fin g) :
    pr.eval interpretation u idx =
      (pr.lines idx).eval interpretation u (pr.eval interpretation u) := by
  induction pr with
  | empty => exact idx.elim0
  | gate pr l ihp =>
    refine Fin.lastCases ?_ (fun j => ?_) idx
    · rw [Program.eval_gate_last, Program.lines_gate_last]
      dsimp only [Line.mapWires, Line.eval]
      congr 1; funext a; dsimp only [Function.comp_apply]
      cases l.wires a with
      | input _ => rfl
      | gate x => exact (Program.eval_gate_castSucc pr l interpretation u x).symm
    · rw [Program.eval_gate_castSucc, ihp j, Program.lines_gate_castSucc]
      dsimp only [Line.mapWires, Line.eval]
      congr 1; funext a; dsimp only [Function.comp_apply]
      cases (pr.lines j).wires a with
      | input _ => rfl
      | gate x => exact (Program.eval_gate_castSucc pr l interpretation u x).symm

/-- Every operand wire of `pr.lines idx` has `wireToNat < k + idx.val` (DAG acyclicity). -/
theorem program_lines_wireToNat_lt {k g : ℕ} (pr : Program signature k g) :
    ∀ (idx : Fin g) (a : Fin (signature.Arity (pr.lines idx).op)),
      wireToNat ((pr.lines idx).wires a) < k + idx.val := by
  induction pr with
  | empty => intro idx; exact idx.elim0
  | gate pr l ihp =>
    intro idx a
    by_cases hlast : idx = Fin.last _
    · subst hlast
      have hl := Program.lines_gate_last pr l
      have hw : ((pr.gate l).lines (Fin.last _)).wires a =
          Wire.Renaming.castSucc.apply (l.wires (a.cast (by rw [hl]; rfl))) := by
        generalize (pr.gate l).lines (Fin.last _) = lk at hl a ⊢; subst hl; rfl
      rw [hw, Fin.val_last]
      cases l.wires _ with
      | input i =>
        simp only [Wire.Renaming.apply, Wire.elim, wireToNat_input]
        have := i.isLt; omega
      | gate x =>
        simp only [Wire.Renaming.apply, Wire.Renaming.castSucc, Wire.elim, wireToNat_gate,
          Fin.val_castSucc]
        have := x.isLt; omega
    · obtain ⟨j, rfl⟩ := Fin.eq_castSucc_of_ne_last hlast
      have hl := Program.lines_gate_castSucc pr l j
      have hs := ihp j (a.cast (by rw [hl]; rfl))
      have hw : ((pr.gate l).lines j.castSucc).wires a =
          Wire.Renaming.castSucc.apply ((pr.lines j).wires (a.cast (by rw [hl]; rfl))) := by
        generalize (pr.gate l).lines j.castSucc = lk at hl a ⊢; subst hl; rfl
      rw [hw, Fin.val_castSucc]
      cases hwire : (pr.lines j).wires (a.cast (by rw [hl]; rfl)) <;>
        (rw [hwire] at hs
         simp only [Wire.Renaming.apply, Wire.Renaming.castSucc, Wire.elim, wireToNat_input,
           wireToNat_gate, Fin.val_castSucc] at hs ⊢
         omega)

/-- Evaluate the 10 candidate De Morgan opcode gates starting from wire list `vm` of length `b0`. -/
private theorem evalRawGates_tenOpGates (vm : List Bool) (opBase a1 a2 b0 opc : ℕ)
    (va1 va2 : Bool) (hlen : vm.length = b0) (ha1 : a1 < b0) (ha2 : a2 < b0)
    (hop_lt : ∀ t < 5, opBase + t < b0)
    (hop : ∀ t < 5, vm.getD (opBase + t) false = decide (t = opc))
    (hva1 : vm.getD a1 false = va1) (hva2 : vm.getD a2 false = va2) :
    evalRawGates vm
      [ .const false, .const true,
        .and (opBase + 2) a1, .not (b0 + 2),
        .and (opBase + 3) a1, .and (opBase + 3) a2, .and (b0 + 4) (b0 + 5),
        .and (opBase + 4) a1, .and (opBase + 4) a2, .or (b0 + 7) (b0 + 8) ] =
      vm ++
        [ false, true,
          decide (2 = opc) && va1, !(decide (2 = opc) && va1),
          decide (3 = opc) && va1, decide (3 = opc) && va2,
          (decide (3 = opc) && va1) && (decide (3 = opc) && va2),
          decide (4 = opc) && va1, decide (4 = opc) && va2,
          (decide (4 = opc) && va1) || (decide (4 = opc) && va2) ] := by
  have hext (xs : List Bool) (p : ℕ) (hp : p < b0) :
      (vm ++ xs).getD p false = vm.getD p false := by
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by simp [hlen]; omega),
      List.getElem?_eq_getElem (hlen ▸ hp), List.getElem_append_left (hlen ▸ hp)]
  have hnew (xs : List Bool) (d : ℕ) (hd : d < xs.length) :
      (vm ++ xs).getD (b0 + d) false = xs[d] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp [hlen]; omega),
      Option.getD_some, List.getElem_append_right (by rw [hlen]; omega)]
    simp [hlen]
  have step (xs : List Bool) (rg : RawGate) (b : Bool) (hb : evalRawGate (vm ++ xs) rg = b) :
      (vm ++ xs) ++ [evalRawGate (vm ++ xs) rg] = vm ++ (xs ++ [b]) := by
    rw [hb, List.append_assoc]
  have hop2 := hop_lt 2 (by omega)
  have hop3 := hop_lt 3 (by omega)
  have hop4 := hop_lt 4 (by omega)
  simp only [evalRawGates_cons, evalRawGates_nil]
  have s0 : vm ++ [evalRawGate vm (.const false)] = vm ++ [false] := rfl
  rw [s0]
  rw [step _ (.const true) true rfl]
  rw [step _ (.and (opBase + 2) a1) (decide (2 = opc) && va1) (by
    rw [evalRawGate_and]
    rw [ite_eq_left (by simp [hlen]; omega), hext _ _ hop2, hext _ _ ha1, hop 2 (by omega), hva1])]
  rw [step _ (.not (b0 + 2)) (!(decide (2 = opc) && va1)) (by
    rw [evalRawGate_not]
    rw [ite_eq_left (by simp [hlen]), hnew _ 2 (by simp)]; rfl)]
  rw [step _ (.and (opBase + 3) a1) (decide (3 = opc) && va1) (by
    rw [evalRawGate_and]
    rw [ite_eq_left (by simp [hlen]; omega), hext _ _ hop3, hext _ _ ha1, hop 3 (by omega), hva1])]
  rw [step _ (.and (opBase + 3) a2) (decide (3 = opc) && va2) (by
    rw [evalRawGate_and]
    rw [ite_eq_left (by simp [hlen]; omega), hext _ _ hop3, hext _ _ ha2, hop 3 (by omega), hva2])]
  rw [step _ (.and (b0 + 4) (b0 + 5))
      ((decide (3 = opc) && va1) && (decide (3 = opc) && va2)) (by
    rw [evalRawGate_and]
    rw [ite_eq_left (by simp [hlen]), hnew _ 4 (by simp), hnew _ 5 (by simp)]; rfl)]
  rw [step _ (.and (opBase + 4) a1) (decide (4 = opc) && va1) (by
    rw [evalRawGate_and]
    rw [ite_eq_left (by simp [hlen]; omega), hext _ _ hop4, hext _ _ ha1, hop 4 (by omega), hva1])]
  rw [step _ (.and (opBase + 4) a2) (decide (4 = opc) && va2) (by
    rw [evalRawGate_and]
    rw [ite_eq_left (by simp [hlen]; omega), hext _ _ hop4, hext _ _ ha2, hop 4 (by omega), hva2])]
  rw [step _ (.or (b0 + 7) (b0 + 8))
      ((decide (4 = opc) && va1) || (decide (4 = opc) && va2)) (by
    rw [evalRawGate_or]
    rw [ite_eq_left (by simp [hlen]), hnew _ 7 (by simp), hnew _ 8 (by simp)]; rfl)]
  rfl

/-- **Evaluation soundness of `univEvalCircuit`:** feeding `(encodeCircuit c S hS, u)` to
`univEvalCircuit k m S hk` computes `c.eval interpretation u`. -/
theorem eval_univEvalCircuit {k m : ℕ} (hk : 1 ≤ k) (c : Circuit signature k m) (S : ℕ)
    (hS : c.size ≤ S) (u : BitString k) :
    (univEvalCircuit k m S hk).eval interpretation (Fin.append (encodeCircuit c S hS) u) =
      c.eval interpretation u := by
  set ℓ := univDescLen k m S
  set v := encodeCircuit c S hS
  set falseW := ℓ + k
  set v0 := evalRawGates (List.ofFn (Fin.append v u)) [RawGate.const false]
  have hv0_eq : v0 = List.ofFn (Fin.append v u) ++ [false] := by simp [v0]
  have hv0_len : v0.length = falseW + 1 := by
    simp only [hv0_eq, List.length_append, List.length_ofFn, List.length_singleton, falseW, ℓ]
  have hv0_desc {pos : ℕ} (hp : pos < ℓ) : v0.getD pos false = v ⟨pos, hp⟩ := by
    rw [hv0_eq, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp; omega),
      Option.getD_some, List.getElem_append_left (by simp; omega), List.getElem_ofFn]
    exact Fin.append_left v u ⟨pos, hp⟩
  have hv0_in (i : Fin k) : v0.getD (ℓ + i.val) false = u i := by
    rw [hv0_eq, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp; omega),
      Option.getD_some, List.getElem_append_left (by simp; omega), List.getElem_ofFn]
    have hidx : (⟨ℓ + i.val, by dsimp [ℓ]; omega⟩ : Fin (univDescLen k m S + k)) =
        Fin.natAdd (univDescLen k m S) i := Fin.ext rfl
    rw [hidx]
    exact Fin.append_right v u i
  have hv0_fw : v0.getD falseW false = false := by
    rw [hv0_eq, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp [falseW, ℓ]),
      Option.getD_some, List.getElem_append_right (by simp [falseW, ℓ])]
    simp [falseW, ℓ]
  have hsteps : ∀ n : ℕ, n ≤ S →
      let vn := evalRawGates v0 (((List.range n).map (univGateBlock k m S)).flatten)
      vn.length = falseW + 1 + n * univStepGateCount k S ∧
      ∀ r < n, vn.getD (univSimGateWire k m S r) false =
        (if hrc : r < c.size then c.program.eval interpretation u ⟨r, hrc⟩ else false) := by
    intro n; induction n with
    | zero => intro _; simp [hv0_len]
    | succ r ih =>
      intro hrS
      obtain ⟨hvr_len, hvr_gate⟩ := ih (by omega)
      set vr := evalRawGates v0 (((List.range r).map (univGateBlock k m S)).flatten)
      have hfl : ((List.range (r + 1)).map (univGateBlock k m S)).flatten =
          ((List.range r).map (univGateBlock k m S)).flatten ++ univGateBlock k m S r := by
        simp [List.range_succ]
      refine ⟨by rw [hfl, evalRawGates_append, length_evalRawGates, hvr_len,
        length_univGateBlock, Nat.succ_mul, add_assoc], fun t htr => ?_⟩
      rw [hfl, evalRawGates_append]
      by_cases hlt : t < r
      · rw [getD_evalRawGates_lt vr _ (by
          rw [hvr_len]; dsimp only [univSimGateWire, univStepGateCount, falseW, ℓ]
          have hmul : (t + 1) * (4 * (k + S) + 20) ≤ r * (4 * (k + S) + 20) :=
            Nat.mul_le_mul_right (4 * (k + S) + 20) hlt
          omega)]
        exact hvr_gate t hlt
      · have hte : t = r := by omega
        subst t
        have hold_v0 {p : ℕ} (hp : p < falseW + 1) : vr.getD p false = v0.getD p false :=
          getD_evalRawGates_lt v0 _ (hv0_len ▸ hp)
        have hwire_val (w : Wire k r) (hrc : r < c.size) :
            vr.getD ((univAvailWires k m S r)[wireToNat w]'(by
              have := wireToNat_lt w; simp; omega)) false =
              Wire.elim u (c.program.eval interpretation u) (wireCastLE hrc.le w) := by
          have hwn : wireToNat w < k + S := (wireToNat_lt w).trans_le (by omega)
          rw [getElem_univAvailWires k m S r (wireToNat w) hwn]
          cases w with
          | input i =>
            simp only [wireToNat_input, i.isLt, ↓reduceIte, wireCastLE_input, Wire.elim]
            exact (hold_v0 (by dsimp [falseW]; omega)).trans (hv0_in i)
          | gate g =>
            simp only [wireToNat_gate, show ¬(k + g.val < k) by omega,
              Nat.add_sub_cancel_left, g.isLt, ↓reduceIte, wireCastLE_gate, Wire.elim]
            have hg := hvr_gate g.val g.isLt
            rw [dite_eq_left (show g.val < c.size by omega)] at hg
            exact hg
        set ws := univAvailWires k m S r
        set cur0 := falseW + 1 + r * univStepGateCount k S
        set opBase := r * univGateDescStride k S
        set s1Base := opBase + 5
        set s2Base := s1Base + (k + S)
        let i0 := if hrc : r < c.size then lineArg0 (c.program.lines ⟨r, hrc⟩) else 0
        let i1 := if hrc : r < c.size then lineArg1 (c.program.lines ⟨r, hrc⟩) else 0
        let opc := if hrc : r < c.size then (opToCode (c.program.lines ⟨r, hrc⟩).op).val else 0
        have hi0_lt : i0 < k + S := by
          dsimp only [i0]; split_ifs with hrc
          · exact (lineArg0_lt hk _).trans_le (by omega)
          · omega
        have hi1_lt : i1 < k + S := by
          dsimp only [i1]; split_ifs with hrc
          · exact (lineArg1_lt hk _).trans_le (by omega)
          · omega
        have hopc_lt : opc < 5 := by
          dsimp only [opc]; split_ifs with hrc
          · exact (opToCode _).isLt
          · omega
        have hst_bound : opBase + univGateDescStride k S ≤ ℓ := by
          have hmul := Nat.mul_le_mul_right (univGateDescStride k S) hrS
          rw [Nat.succ_mul] at hmul; dsimp only [opBase, ℓ, univDescLen]; omega
        set vm1 := evalRawGates vr (muxGates s1Base cur0 falseW ws)
        have hvm1_len : vm1.length = cur0 + 2 * (k + S) := by
          rw [length_evalRawGates, hvr_len, length_muxGates, length_univAvailWires]
        set a1 := cur0 + 2 * (k + S) - 1
        have ha1_val : vm1.getD a1 false = vr.getD (ws[i0]'(by simp [ws, hi0_lt])) false := by
          have hev := eval_muxGates_oneHot ws s1Base falseW i0 vr (by simp [ws, hi0_lt])
            (by rw [hvr_len]; dsimp only [cur0]; omega)
            (fun idx hidx => by
              have hidx' : idx < k + S := by simpa [ws] using hidx
              refine ⟨by rw [hvr_len]
                         dsimp only [cur0, falseW, s1Base, univGateDescStride] at *; omega,
                by rw [hvr_len]; exact univAvailWires_lt k m S r idx hidx'⟩)
            (fun idx hidx => by
              have hidx' : idx < k + S := by simpa [ws] using hidx
              have hp : s1Base + idx < ℓ := by
                dsimp only [s1Base, univGateDescStride] at *; omega
              rw [hold_v0 (by dsimp only [falseW]; omega), hv0_desc hp]
              exact encodeCircuit_arg0 c S hS hrS hidx')
          have hfw_r : vr.getD falseW false = false := (hold_v0 (by omega)).trans hv0_fw
          have ha1_eq : cur0 + 2 * ws.length - 1 = a1 := by simp [ws, a1]
          rw [hvr_len, ha1_eq, hfw_r, Bool.false_or] at hev
          exact hev
        set cur1 := cur0 + 2 * (k + S)
        set vm2 := evalRawGates vm1 (muxGates s2Base cur1 falseW ws)
        have hvm2_len : vm2.length = cur1 + 2 * (k + S) := by
          rw [length_evalRawGates, hvm1_len, length_muxGates, length_univAvailWires]
        set a2 := cur1 + 2 * (k + S) - 1
        have ha2_val : vm2.getD a2 false = vr.getD (ws[i1]'(by simp [ws, hi1_lt])) false := by
          have hold1 {p : ℕ} (hp : p < cur0) : vm1.getD p false = vr.getD p false :=
            getD_evalRawGates_lt vr _ (hvr_len ▸ hp)
          have hev := eval_muxGates_oneHot ws s2Base falseW i1 vm1 (by simp [ws, hi1_lt])
            (by rw [hvm1_len]; dsimp only [cur1, cur0]; omega)
            (fun idx hidx => by
              have hidx' : idx < k + S := by simpa [ws] using hidx
              refine ⟨by rw [hvm1_len]
                         dsimp only [cur1, cur0, falseW, s2Base, s1Base, univGateDescStride] at *
                         omega,
                by rw [hvm1_len]
                   exact (univAvailWires_lt k m S r idx hidx').trans
                     (by dsimp only [cur1, cur0]; omega)⟩)
            (fun idx hidx => by
              have hidx' : idx < k + S := by simpa [ws] using hidx
              have hp : s2Base + idx < ℓ := by
                dsimp only [s2Base, s1Base, univGateDescStride] at *; omega
              rw [hold1 (by dsimp only [cur0, falseW]; omega),
                hold_v0 (by dsimp only [falseW]; omega), hv0_desc hp]
              exact encodeCircuit_arg1 c S hS hrS hidx')
          have hfw_1 : vm1.getD falseW false = false :=
            (hold1 (by dsimp only [cur0]; omega)).trans ((hold_v0 (by omega)).trans hv0_fw)
          have hwi1 := hold1 (univAvailWires_lt k m S r i1 hi1_lt)
          have ha2_eq : cur1 + 2 * ws.length - 1 = a2 := by simp [ws, a2]
          rw [hvm1_len, ha2_eq, hfw_1, Bool.false_or] at hev
          exact hev.trans hwi1
        set b0 := cur1 + 2 * (k + S)
        let va1 := vr.getD (ws[i0]'(by simp [ws, hi0_lt])) false
        let va2 := vr.getD (ws[i1]'(by simp [ws, hi1_lt])) false
        let ops : List RawGate :=
          [ .const false, .const true,
            .and (opBase + 2) a1, .not (b0 + 2),
            .and (opBase + 3) a1, .and (opBase + 3) a2, .and (b0 + 4) (b0 + 5),
            .and (opBase + 4) a1, .and (opBase + 4) a2, .or (b0 + 7) (b0 + 8) ]
        set vop := evalRawGates vm2 ops
        have hop_bit (t : ℕ) (ht : t < 5) : vm2.getD (opBase + t) false = decide (t = opc) := by
          have hp : opBase + t < ℓ := by dsimp only [univGateDescStride] at hst_bound; omega
          rw [getD_evalRawGates_lt vm1 _ (by rw [hvm1_len]; dsimp only [cur1, cur0, falseW]; omega),
            getD_evalRawGates_lt vr _ (by rw [hvr_len]; dsimp only [cur0, falseW]; omega),
            hold_v0 (by dsimp only [falseW]; omega), hv0_desc hp]
          exact encodeCircuit_op c S hS hrS ht
        have hvm2_a1 : vm2.getD a1 false = va1 :=
          (getD_evalRawGates_lt vm1 _ (by rw [hvm1_len]; dsimp only [a1, cur1]; omega)).trans
            ha1_val
        have hvop_eq := evalRawGates_tenOpGates vm2 opBase a1 a2 b0 opc va1 va2 hvm2_len
          (by dsimp only [a1, b0, cur1]; omega) (by dsimp only [a2, b0]; omega)
          (fun t ht => by
            dsimp only [univGateDescStride] at hst_bound
            dsimp only [b0, cur1, cur0, falseW]; omega)
          hop_bit hvm2_a1 ha2_val
        have hvop_len : vop.length = b0 + 10 := by
          change (evalRawGates vm2 ops).length = _; rw [hvop_eq]; simp [hvm2_len]
        let bws : List ℕ := [b0, b0 + 1, b0 + 3, b0 + 6, b0 + 9]
        have hev_op := eval_muxGates_oneHot bws opBase falseW opc vop (by simp [bws, hopc_lt])
          (by rw [hvop_len]; dsimp only [b0, cur1, cur0]; omega)
          (fun idx hidx => by
            have hi5 : idx < 5 := by simpa [bws] using hidx
            have hp : opBase + idx < b0 := by
              dsimp only [univGateDescStride] at hst_bound
              dsimp only [b0, cur1, cur0, falseW]; omega
            refine ⟨by rw [hvop_len]; omega, by
              rw [hvop_len]
              rcases (show idx = 0 ∨ idx = 1 ∨ idx = 2 ∨ idx = 3 ∨ idx = 4 by omega)
                with rfl | rfl | rfl | rfl | rfl <;> simp [bws]⟩)
          (fun idx hidx => by
            have hi5 : idx < 5 := by simpa [bws] using hidx
            have hp : opBase + idx < b0 := by
              dsimp only [univGateDescStride] at hst_bound
              dsimp only [b0, cur1, cur0, falseW]; omega
            rw [getD_evalRawGates_lt vm2 _ (by rw [hvm2_len]; exact hp)]
            exact hop_bit idx hi5)
        rw [hvop_len] at hev_op
        have hfw_op : vop.getD falseW false = false := by
          rw [getD_evalRawGates_lt vm2 _ (by rw [hvm2_len]; dsimp only [b0, cur1, cur0]; omega),
            getD_evalRawGates_lt vm1 _ (by rw [hvm1_len]; dsimp only [cur1, cur0]; omega),
            getD_evalRawGates_lt vr _ (by rw [hvr_len]; dsimp only [cur0]; omega),
            hold_v0 (by omega), hv0_fw]
        rw [hfw_op, Bool.false_or] at hev_op
        have hfold_eq : evalRawGates vr (univGateBlock k m S r) =
            evalRawGates vop (muxGates opBase (b0 + 10) falseW bws) := by
          simp only [univGateBlock, evalRawGates_append, vop, vm2, vm1, bws, ops,
            b0, a2, cur1, a1, cur0, ws, s2Base, s1Base, opBase, falseW, ℓ]
        have hwire_eq : univSimGateWire k m S r = b0 + 10 + 2 * bws.length - 1 := by
          simp only [univSimGateWire, univStepGateCount, bws, List.length_cons, List.length_nil,
            b0, cur1, cur0, falseW, ℓ, Nat.succ_mul]; omega
        rw [hfold_eq, hwire_eq, hev_op]
        have hbr (d : ℕ) (hd : d < 10) : vop.getD (b0 + d) false =
            [ false, true, decide (2 = opc) && va1, !(decide (2 = opc) && va1),
              decide (3 = opc) && va1, decide (3 = opc) && va2,
              (decide (3 = opc) && va1) && (decide (3 = opc) && va2),
              decide (4 = opc) && va1, decide (4 = opc) && va2,
              (decide (4 = opc) && va1) || (decide (4 = opc) && va2) ][d] := by
          change (evalRawGates vm2 ops).getD (b0 + d) false = _
          rw [hvop_eq, List.getD_eq_getElem?_getD,
            List.getElem?_eq_getElem (by simp [hvm2_len]; omega), Option.getD_some,
            List.getElem_append_right (by rw [hvm2_len]; omega)]
          simp [hvm2_len]
        by_cases hrc : r < c.size
        · rw [dite_eq_left hrc, program_eval_eq_lines c.program u ⟨r, hrc⟩]
          have hwire_c (w : Wire k c.size) (hw : wireToNat w < k + r) :
              vr.getD (ws[wireToNat w]'(by have := wireToNat_lt w; simp [ws]; omega)) false =
                Wire.elim u (c.program.eval interpretation u) w := by
            cases w with
            | input a => exact hwire_val (.input a) hrc
            | gate g =>
              have hgr : g.val < r := by simp [wireToNat_gate] at hw; omega
              exact hwire_val (.gate ⟨g.val, hgr⟩) hrc
          have hopc_eq : opc = (opToCode (c.program.lines ⟨r, hrc⟩).op).val := dite_eq_left hrc
          have hi0_eq : i0 = lineArg0 (c.program.lines ⟨r, hrc⟩) := dite_eq_left hrc
          have hi1_eq : i1 = lineArg1 (c.program.lines ⟨r, hrc⟩) := dite_eq_left hrc
          have ha_r := program_lines_wireToNat_lt c.program ⟨r, hrc⟩
          generalize c.program.lines ⟨r, hrc⟩ = lr at hopc_eq hi0_eq hi1_eq ha_r ⊢
          rcases lr with ⟨op, lws⟩
          cases op with
          | const bv =>
            cases bv
            · simpa [hopc_eq, opToCode, bws, Line.eval, interpretation_const] using
                hbr 0 (by omega)
            · simpa [hopc_eq, opToCode, bws, Line.eval, interpretation_const] using
                hbr 1 (by omega)
          | not =>
            have h0v : va1 = Wire.elim u (c.program.eval interpretation u) (lws 0) := by
              dsimp only [va1]; simp_rw [hi0_eq, lineArg0]; exact hwire_c (lws 0) (ha_r 0)
            simpa [hopc_eq, opToCode, bws, h0v, Line.eval, interpretation_not] using
              hbr 3 (by omega)
          | and =>
            have h0v : va1 = Wire.elim u (c.program.eval interpretation u) (lws 0) := by
              dsimp only [va1]; simp_rw [hi0_eq, lineArg0]; exact hwire_c (lws 0) (ha_r 0)
            have h1v : va2 = Wire.elim u (c.program.eval interpretation u) (lws 1) := by
              dsimp only [va2]; simp_rw [hi1_eq, lineArg1]; exact hwire_c (lws 1) (ha_r 1)
            simpa [hopc_eq, opToCode, bws, h0v, h1v, Line.eval, interpretation_and] using
              hbr 6 (by omega)
          | or =>
            have h0v : va1 = Wire.elim u (c.program.eval interpretation u) (lws 0) := by
              dsimp only [va1]; simp_rw [hi0_eq, lineArg0]; exact hwire_c (lws 0) (ha_r 0)
            have h1v : va2 = Wire.elim u (c.program.eval interpretation u) (lws 1) := by
              dsimp only [va2]; simp_rw [hi1_eq, lineArg1]; exact hwire_c (lws 1) (ha_r 1)
            simpa [hopc_eq, opToCode, bws, h0v, h1v, Line.eval, interpretation_or] using
              hbr 9 (by omega)
        · have hopc0 : opc = 0 := dite_eq_right hrc
          rw [dite_eq_right hrc]
          simpa [hopc0, bws] using hbr 0 (by omega)
  obtain ⟨hvS_len, hvS_gate⟩ := hsteps S le_rfl
  set vS := evalRawGates v0 (((List.range S).map (univGateBlock k m S)).flatten)
  have houts : ∀ n : ℕ, n ≤ m →
      let vn := evalRawGates vS (((List.range n).map (univOutBlock k m S)).flatten)
      vn.length = falseW + 1 + S * univStepGateCount k S + n * (2 * (k + S)) ∧
      ∀ j : Fin m, j.val < n →
        vn.getD (falseW + 1 + S * univStepGateCount k S + (j.val + 1) * (2 * (k + S)) - 1) false =
          c.eval interpretation u j := by
    intro n; induction n with
    | zero => intro _; simp [hvS_len]
    | succ t ih =>
      intro htm
      obtain ⟨hvt_len, hvt_out⟩ := ih (by omega)
      set vt := evalRawGates vS (((List.range t).map (univOutBlock k m S)).flatten)
      have hfl : ((List.range (t + 1)).map (univOutBlock k m S)).flatten =
          ((List.range t).map (univOutBlock k m S)).flatten ++ univOutBlock k m S t := by
        simp [List.range_succ]
      refine ⟨by rw [hfl, evalRawGates_append, length_evalRawGates, hvt_len,
        length_univOutBlock]; ring, fun j hjt => ?_⟩
      rw [hfl, evalRawGates_append]
      by_cases hlt : j.val < t
      · rw [getD_evalRawGates_lt vt _ (by
          rw [hvt_len]
          have hmul : (j.val + 1) * (2 * (k + S)) ≤ t * (2 * (k + S)) :=
            Nat.mul_le_mul_right (2 * (k + S)) hlt
          omega)]
        exact hvt_out j hlt
      · have hje : t = j.val := by omega
        subst hje
        set i0 := wireToNat (c.outputs j)
        have hi0 : i0 < k + S := (wireToNat_lt (c.outputs j)).trans_le (by omega)
        set ws := univAvailWires k m S S
        set selBase := S * univGateDescStride k S + j.val * (k + S)
        have holdS {p : ℕ} (hp : p < vS.length) : vt.getD p false = vS.getD p false :=
          getD_evalRawGates_lt vS _ hp
        have hold0 {p : ℕ} (hp : p < falseW + 1) : vt.getD p false = v0.getD p false :=
          (holdS (hvS_len ▸ by omega)).trans (getD_evalRawGates_lt v0 _ (hv0_len ▸ hp))
        have hev := eval_muxGates_oneHot ws selBase falseW i0 vt (by simp [ws, hi0])
          (by rw [hvt_len]; omega)
          (fun idx hidx => by
            have hi' : idx < k + S := by simpa [ws] using hidx
            have hsb : selBase + idx < ℓ := by
              have hmul := Nat.mul_le_mul_right (k + S) htm; rw [Nat.succ_mul] at hmul
              dsimp only [selBase, ℓ, univDescLen]; omega
            exact ⟨by rw [hvt_len]; dsimp only [falseW]; omega,
              by rw [hvt_len]; exact (univAvailWires_lt k m S S idx hi').trans_le (by omega)⟩)
          (fun idx hidx => by
            have hi' : idx < k + S := by simpa [ws] using hidx
            have hsb : selBase + idx < ℓ := by
              have hmul := Nat.mul_le_mul_right (k + S) htm; rw [Nat.succ_mul] at hmul
              dsimp only [selBase, ℓ, univDescLen]; omega
            rw [hold0 (by dsimp only [falseW]; omega), hv0_desc hsb]
            exact encodeCircuit_out c S hS j hi')
        rw [hvt_len] at hev
        have hfw_t : vt.getD falseW false = false := (hold0 (by omega)).trans hv0_fw
        rw [hfw_t, Bool.false_or] at hev
        change (evalRawGates vt (muxGates selBase _ falseW ws)).getD _ false = _
        rw [show falseW + 1 + S * univStepGateCount k S + (j.val + 1) * (2 * (k + S)) - 1 =
          falseW + 1 + S * univStepGateCount k S + j.val * (2 * (k + S)) + 2 * ws.length - 1 by
            simp [ws, Nat.succ_mul, add_assoc], hev,
          holdS (hvS_len ▸ univAvailWires_lt k m S S i0 hi0)]
        rw [getElem_univAvailWires k m S S i0 hi0]
        cases hco : c.outputs j with
        | input a =>
          simp only [i0, hco, wireToNat_input, a.isLt, ↓reduceIte, Circuit.eval, Program.trace,
            Function.comp_apply, Wire.elim]
          exact (getD_evalRawGates_lt v0 _
            (by rw [hv0_len]; dsimp [falseW]; omega)).trans (hv0_in a)
        | gate g =>
          simp only [i0, hco, wireToNat_gate, show ¬(k + g.val < k) by omega,
            Nat.add_sub_cancel_left, show g.val < S by omega, ↓reduceIte, Circuit.eval,
            Program.trace, Function.comp_apply, Wire.elim]
          simpa [g.isLt] using hvS_gate g.val (by omega)
  have hfull := (houts m le_rfl).2
  funext j
  have hjo : j.val < (univRawOuts k m S).length := by simp
  have hev := eval_buildRawCircuit (ℓ + k) (by omega) (univRawGates k m S) (univRawOuts k m S)
    (univRawOuts_lt k m S) (Fin.append v u) ⟨j.val, hjo⟩
  exact hev.trans (by
    have hout_idx : (univRawOuts k m S)[j.val] =
        falseW + 1 + S * univStepGateCount k S + (j.val + 1) * (2 * (k + S)) - 1 := by
      simp only [univRawOuts, List.getElem_map, List.getElem_range,
        show ¬(k + S = 0) by omega, ↓reduceIte, falseW, ℓ]
    have hval_eq : evalRawGates (List.ofFn (Fin.append v u)) (univRawGates k m S) =
        evalRawGates vS (((List.range m).map (univOutBlock k m S)).flatten) := by
      have hug : univRawGates k m S =
          ([RawGate.const false] ++ ((List.range S).map (univGateBlock k m S)).flatten) ++
            ((List.range m).map (univOutBlock k m S)).flatten := by
        simp [univRawGates]
      rw [hug, evalRawGates_append, evalRawGates_append]
    rw [hout_idx, hval_eq]
    exact hfull j j.isLt)

/-! ### Public indexing, monotonicity, and bound API for `univEvalCircuit` -/

/-- Anchor gate `0` of `univRawGates k m S` is `RawGate.const false`. -/
@[simp]
theorem getElem_univRawGates_zero (k m S : ℕ) :
    (univRawGates k m S)[0]'(by simp) = .const false := rfl

/-- Indexing into `univRawGates k m S` at a positive gate offset `g' > 0`. -/
theorem getElem_univRawGates_of_pos (k m S : ℕ) {g' : ℕ} (hpos : 0 < g')
    (hlt : g' < (univRawGates k m S).length) :
    (univRawGates k m S)[g']'hlt =
      ((((List.range S).map (univGateBlock k m S)).flatten ++
        ((List.range m).map (univOutBlock k m S)).flatten))[g' - 1]'(by
          simp only [univRawGates, List.length_cons] at hlt; omega) := by
  obtain ⟨p, rfl⟩ : ∃ p, g' = p + 1 := ⟨g' - 1, by omega⟩; rfl

/-- Output wire index `j < m` in `univRawOuts k m S` when `0 < k + S`. -/
theorem getElem_univRawOuts_of_pos {k m S j : ℕ} (hks : 0 < k + S) (hj : j < m) :
    (univRawOuts k m S)[j]'(by simp [hj]) =
      (univDescLen k m S + k) + 1 + S * univStepGateCount k S + (j + 1) * (2 * (k + S)) - 1 := by
  simp only [univRawOuts, List.getElem_map, List.getElem_range, show ¬(k + S = 0) by omega,
    ↓reduceIte]

/-- Indexing into `univOutBlock k m S j`. -/
theorem getElem_univOutBlock (k m S j off : ℕ) (hoff : off < 2 * (k + S)) :
    (univOutBlock k m S j)[off]'(by simp [hoff]) =
      (muxGates (S * univGateDescStride k S + j * (k + S))
        ((univDescLen k m S + k) + (1 + S * univStepGateCount k S + j * (2 * (k + S))))
        (univDescLen k m S + k) (univAvailWires k m S S))[off]'(by simp [hoff]) := by
  dsimp only [univOutBlock]; congr 1; congr 1; omega

/-- Indexing into the first operand multiplexer (`off < 2 * (k + S)`) of `univGateBlock`. -/
theorem getElem_univGateBlock_mux1 (k m S r off : ℕ) (h1 : off < 2 * (k + S)) :
    (univGateBlock k m S r)[off]'(by rw [length_univGateBlock]; dsimp [univStepGateCount]; omega) =
      (muxGates (r * univGateDescStride k S + 5)
        ((univDescLen k m S + k) + (1 + r * univStepGateCount k S))
        (univDescLen k m S + k) (univAvailWires k m S r))[off]'(by simp [h1]) := by
  dsimp only [univGateBlock]; simp only [List.append_assoc]
  rw [List.getElem_append_left (by simp [h1])]; congr 1; congr 1; omega

/-- Indexing into the second operand multiplexer (`2 * (k + S) ≤ off < 4 * (k + S)`) of
`univGateBlock`. -/
theorem getElem_univGateBlock_mux2 (k m S r off : ℕ) (hge : ¬off < 2 * (k + S))
    (h2 : off < 4 * (k + S)) :
    (univGateBlock k m S r)[off]'(by rw [length_univGateBlock]; dsimp [univStepGateCount]; omega) =
      (muxGates (r * univGateDescStride k S + 5 + (k + S))
        ((univDescLen k m S + k) + (1 + r * univStepGateCount k S + 2 * (k + S)))
        (univDescLen k m S + k)
        (univAvailWires k m S r))[off - 2 * (k + S)]'(by simp; omega) := by
  dsimp only [univGateBlock]; simp only [List.append_assoc]
  rw [List.getElem_append_right (by simp; omega), List.getElem_append_left (by simp; omega)]
  congr 1
  · congr 1; omega
  · simp

/-- Indexing into the `10` opcode-branch gates (`4 * (k + S) ≤ off < 4 * (k + S) + 10`) of
`univGateBlock`. -/
theorem getElem_univGateBlock_ops {k : ℕ} (hks : 0 < k) (m S r off : ℕ) (hge : ¬off < 4 * (k + S))
    (h3 : off < 4 * (k + S) + 10) :
    let n' := univDescLen k m S + k
    let gs3 := 1 + r * univStepGateCount k S + 4 * (k + S)
    let opBase := r * univGateDescStride k S
    let a1w := n' + (1 + r * univStepGateCount k S + (2 * (k + S) - 1))
    let a2w := n' + (1 + r * univStepGateCount k S + (4 * (k + S) - 1))
    (univGateBlock k m S r)[off]'(by rw [length_univGateBlock]; dsimp [univStepGateCount]; omega) =
      ([ .const false, .const true,
         .and (opBase + 2) a1w, .not (n' + gs3 + 2),
         .and (opBase + 3) a1w, .and (opBase + 3) a2w, .and (n' + gs3 + 4) (n' + gs3 + 5),
         .and (opBase + 4) a1w, .and (opBase + 4) a2w,
         .or (n' + gs3 + 7) (n' + gs3 + 8) ] : List RawGate)[off - 4 * (k + S)]'(by
        simp; omega) := by
  intro n' gs3 opBase a1w a2w
  dsimp only [univGateBlock]; simp only [List.append_assoc]
  rw [List.getElem_append_right (by simp; omega), List.getElem_append_right (by simp; omega),
    List.getElem_append_left (by simp; omega)]
  congr 1
  · dsimp only [n', opBase, a1w, a2w, gs3]
    simp only [List.cons.injEq, RawGate.and.injEq, RawGate.not.injEq, RawGate.or.injEq,
      true_and, and_true]
    omega
  · simp; omega

/-- Indexing into the `5`-way opcode multiplexer (`4 * (k + S) + 10 ≤ off < univStepGateCount k S`)
of `univGateBlock`. -/
theorem getElem_univGateBlock_muxOp (k m S r off : ℕ) (hge : ¬off < 4 * (k + S) + 10)
    (hoff : off < univStepGateCount k S) :
    let n' := univDescLen k m S + k
    let gs3 := 1 + r * univStepGateCount k S + 4 * (k + S)
    let gs4 := gs3 + 10
    let bws : List ℕ := [n' + gs3, n' + gs3 + 1, n' + gs3 + 3, n' + gs3 + 6, n' + gs3 + 9]
    (univGateBlock k m S r)[off]'(by rw [length_univGateBlock]; exact hoff) =
      (muxGates (r * univGateDescStride k S) (n' + gs4) n'
        bws)[off - (4 * (k + S) +
          10)]'(by dsimp [univStepGateCount] at hoff; simp [bws]; omega) := by
  intro n' gs3 gs4 bws
  dsimp only [univGateBlock]; simp only [List.append_assoc]
  rw [List.getElem_append_right (by simp; omega), List.getElem_append_right (by simp; omega),
    List.getElem_append_right (by simp; omega)]
  congr 1
  · dsimp only [n', bws, gs4, gs3]
    congr 1
    · omega
    · simp only [List.cons.injEq, and_true]; omega
  · simp; omega

/-- Expressing `univSimGateWire` as the last wire of step `t`. -/
theorem univSimGateWire_eq_step_last (k m S t : ℕ) :
    univSimGateWire k m S t =
      (univDescLen k m S + k) +
        (1 + t * univStepGateCount k S + (univStepGateCount k S - 1)) := by
  dsimp [univSimGateWire, univStepGateCount]; rw [Nat.succ_mul]; omega

/-- `buildTauFormulaRaw` specialized to `univEvalCircuit k m S hk`. -/
theorem buildTauFormulaRaw_univEvalCircuit {k m S : ℕ} (hk : 1 ≤ k)
    (wAtom : Wire (univDescLen k m S + k) (univRawGates k m S).length → ℕ) (b : BitString m) :
    let atoms := (List.ofFn fun a => wAtom (.input a)) ++ (List.ofFn fun r => wAtom (.gate r))
    buildTauFormulaRaw atoms (univDescLen k m S + k) (univRawGates k m S) (univRawOuts k m S)
      (List.ofFn b) = tauFormulaWith (univEvalCircuit k m S hk) wAtom b := by
  intro atoms
  have hm := length_univRawOuts k m S
  let b' : BitString (univRawOuts k m S).length := fun j => b (j.cast hm)
  have hb' : List.ofFn b = List.ofFn b' := List.ext_getElem (by simp) fun _ _ _ => by simp [b']
  rw [hb', buildTauFormulaRaw_eq (univDescLen k m S + k) (by omega) _ _ wAtom b']
  exact (tauFormulaWith_reindexOutputs
    (buildRawCircuit (univDescLen k m S + k) (by omega) (univRawGates k m S) (univRawOuts k m S))
    hm wAtom b).symm

/-- Strict positivity of `univDescLen k m S` when `1 ≤ k` and `1 ≤ m`. -/
theorem univDescLen_pos_of_pos {k m S : ℕ} (hk : 1 ≤ k) (hm : 1 ≤ m) :
    0 < univDescLen k m S := by
  have : 1 ≤ m * (k + S) := Nat.mul_pos hm (by omega)
  dsimp [univDescLen]; omega

/-- Monotonicity of `univDescLen` in all three parameters. -/
@[gcongr] theorem univDescLen_mono {k₁ k₂ m₁ m₂ S₁ S₂ : ℕ} (hk : k₁ ≤ k₂) (hm : m₁ ≤ m₂)
    (hS : S₁ ≤ S₂) : univDescLen k₁ m₁ S₁ ≤ univDescLen k₂ m₂ S₂ := by
  dsimp [univDescLen, univGateDescStride]
  exact Nat.add_le_add (Nat.mul_le_mul hS (by omega)) (Nat.mul_le_mul hm (by omega))

/-- Output-selector bits `m * (k + S)` are bounded by `univDescLen k m S`. -/
theorem right_mul_le_univDescLen (k m S : ℕ) : m * (k + S) ≤ univDescLen k m S :=
  Nat.le_add_left _ _

/-- Gate-description bits `S * univGateDescStride k S` are bounded by `univDescLen k m S`. -/
theorem mul_univGateDescStride_le_univDescLen (k m S : ℕ) :
    S * univGateDescStride k S ≤ univDescLen k m S := Nat.le_add_right _ _

/-- Output selector index lies below `univDescLen k m S` whenever `j < m` and `idx < k + S`. -/
theorem add_mul_lt_univDescLen {k m S j idx : ℕ} (hj : j < m) (hi : idx < k + S) :
    S * univGateDescStride k S + j * (k + S) + idx < univDescLen k m S := by
  have := Nat.mul_le_mul_right (k + S) hj; rw [Nat.succ_mul] at this; dsimp [univDescLen]; omega

/-- `univGateDescStride k S` is at least `5 + (k + S) + (k + S)`. -/
theorem univGateDescStride_ge (k S : ℕ) : 5 + (k + S) + (k + S) ≤ univGateDescStride k S := by
  dsimp [univGateDescStride]; omega

/-- `4 * (k + S) + 10` is strictly less than `univStepGateCount k S`. -/
theorem four_mul_add_ten_lt_univStepGateCount (k S : ℕ) :
    4 * (k + S) + 10 < univStepGateCount k S := by dsimp [univStepGateCount]; omega

/-- Tail opcode-mux width `univStepGateCount k S - (4 * (k + S) + 10) = 10`. -/
theorem univStepGateCount_sub_four_mul_add_ten (k S : ℕ) :
    univStepGateCount k S - (4 * (k + S) + 10) = 10 := by dsimp [univStepGateCount]; omega

/-- Quadratic upper bound on `univDescLen k m S`. -/
theorem univDescLen_le_eight_mul_sq (k m S : ℕ) :
    univDescLen k m S ≤ 8 * (k + m + S + 4) ^ 2 := by
  dsimp [univDescLen, univGateDescStride]; nlinarith

/-- Quadratic upper bound on `(univRawGates k m S).length`. -/
theorem univRawGates_len_le_ten_mul_sq (k m S : ℕ) :
    1 + S * univStepGateCount k S + m * (2 * (k + S)) ≤ 10 * (k + m + S + 4) ^ 2 := by
  dsimp [univStepGateCount]; nlinarith

/-- Upper bound on `univDescLen k m S` from parameter bounds `S ≤ B`, `m ≤ M`, `k + S ≤ K`. -/
theorem univDescLen_le_of_le {k m S B M K : ℕ} (hS : S ≤ B) (hm : m ≤ M) (hkS : k + S ≤ K) :
    univDescLen k m S ≤ B * (5 + 2 * K) + M * K := by
  dsimp [univDescLen, univGateDescStride]
  exact Nat.add_le_add (Nat.mul_le_mul hS (Nat.add_le_add le_rfl (Nat.mul_le_mul_left 2 hkS)))
    (Nat.mul_le_mul hm hkS)

/-- Upper bound on `(univEvalCircuit k m S hk).size` from `S ≤ B`, `m ≤ M`, `k + S ≤ K`. -/
theorem size_univEvalCircuit_le_of_le {k m S B M K : ℕ} (hk : 1 ≤ k) (hS : S ≤ B) (hm : m ≤ M)
    (hkS : k + S ≤ K) :
    (univEvalCircuit k m S hk).size ≤ 1 + B * (4 * K + 20) + 2 * M * K := by
  rw [size_univEvalCircuit]; dsimp [univStepGateCount]
  refine Nat.add_le_add (Nat.add_le_add le_rfl
    (Nat.mul_le_mul hS (Nat.add_le_add (Nat.mul_le_mul_left 4 hkS) le_rfl))) ?_
  rw [mul_comm m (2 * (k + S)), mul_right_comm]
  exact Nat.mul_le_mul (Nat.mul_le_mul_left 2 hm) hkS

end CslibFrontier.ProofComplexity
