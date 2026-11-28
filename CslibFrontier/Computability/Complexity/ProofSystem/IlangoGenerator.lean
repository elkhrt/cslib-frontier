module

public import CslibFrontier.Computability.Complexity.ProofSystem.ShiftedGenerator

import Cslib.Foundations.Data.Polynomial.Monotone
import CslibFrontier.Foundations.Data.Nat.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Hard Non-Uniform Proof Complexity Generators from Demi-Bits

This module proves that the `DemiBitConjecture` implies the existence of a
single `P/poly` proof complexity generator simultaneously hard for every Cook–Reckhow propositional
proof system (`HardGeneratorConjecture`), via the simplified proof combining stretched demi-bit
generators (`n → n + ⌈log₂ n⌉ + 1`), a universal `1`-bit-advice proof system,
XOR shift-covering, and the polynomial-size Frege specialization of
`ilangoCircuit`.

## Main definitions

* `CslibFrontier.ProofComplexity.ilangoThreshold`: super-polynomial, sub-exponential proof-length
  threshold `n ↦ n ^ ⌊log₂(⌊log₂(n + 4)⌋ + 2)⌋`.

## Main results

* `CslibFrontier.ProofComplexity.exists_frege_reduce_ilangoCircuit`: uniform polynomial-size
  verified Frege proof reducing a substituted `τ(ilangoCircuit c q r hr s)_{a ⊕ s_j}` to `τ(c)_a`.
* `CslibFrontier.ProofComplexity.ilango_claim_hard`: covering the complements of short
  `pps/1`-provable non-outputs by XOR shifts yields circuits hard for all Cook–Reckhow proof
  systems.
* `CslibFrontier.ProofComplexity.exists_hard_oneBitStretch_of_demiBit`: `DemiBitConjecture` yields a
  polynomial-size one-bit-stretching circuit family `n + ⌈log₂ n⌉ → n + ⌈log₂ n⌉ + 1` hard for all
  Cook–Reckhow proof systems.
* `CslibFrontier.ProofComplexity.exists_hard_ppolyGenerator_of_demiBit`: `DemiBitConjecture` yields
  a full `P/poly` generator `g : PPolyGenerator m` (with `m(K) ∈ {K + 1, K + 2}` for every `K : ℕ`)
  hard for all Cook–Reckhow proof systems.
* `CslibFrontier.ProofComplexity.hardGeneratorConjecture_of_demiBit`:
  `DemiBitConjecture → HardGeneratorConjecture`.


-/

public section

namespace CslibFrontier.ProofComplexity

open CslibFrontier.Computability
open Cslib Cslib.Circuits Cslib.Circuits.Boolean Cslib.Logic.PL Cslib.Complexity
open Turing.MultiTapeTM
open Filter Finset

/-! ### Polynomial-size Frege specialization of `ilangoCircuit` and shift-covering hardness -/

/-- **Polynomial-size verified Frege reduction for `ilangoCircuit`.** There is an absolute constant
`C ≥ 1` such that for any circuit `c : Circuit signature n m` (`1 ≤ n`), `r ≤ 2 ^ q` shifts
`s : Fin r → BitString m`, index `j₀ : Fin r`, and target `a : BitString m`, fixing the `q` index
bits to `j₀` reduces `tauFormula 0 (ilangoCircuit c q r hr s) (bitXor a (s j₀))` to
`tauFormula 0 c a` in polynomial encoded substitution and EF-proof length. -/
theorem exists_frege_reduce_ilangoCircuit :
    ∃ C : ℕ, 1 ≤ C ∧
      ∀ {n m : ℕ}, 1 ≤ n → ∀ (c : Circuit signature n m) (q r : ℕ) (hr : 1 ≤ r),
        r ≤ 2 ^ q → ∀ (s : Fin r → BitString m) (j₀ : Fin r) (a : BitString m),
        let c' := ilangoCircuit c q r hr s
        ∃ (pairs : List (ℕ × Formula)) (steps : List EFStep),
          runEFProof (fun _ => false) steps =
            .imp ((tauFormula 0 c' (bitXor a (s j₀))).subst (listSubst pairs))
              (tauFormula 0 c a) ∧
          (encList (encPair encNat encFormula) pairs).length +
            (encList encEFStep steps).length ≤
            C * (n + q + c'.size + m + 20) ^ 6 := by
  obtain ⟨C₀, hC₀, hred⟩ := exists_frege_reduce_tauFormula
  refine ⟨(C₀ + 40) * 2 ^ 6, Nat.mul_pos (by omega) (Nat.pow_pos (by decide)),
    fun {n m} hn c q r hr hrq s j₀ a => ?_⟩
  set c' := ilangoCircuit c q r hr s
  let gsLen := 2 + q + r * q + m * (r + 6)
  have hc'_sz : c'.size = c.size + gsLen := size_ilangoCircuit c q r hr s
  let base0 := (n + q) + c.size
  let negBase := base0 + 2
  let eqBase := negBase + q
  let outBase := eqBase + r * q
  let eqMatch (j tBound : ℕ) : Bool :=
    (List.range tBound).all fun t => j₀.val.testBit t == j.testBit t
  let diffAcc (i : Fin m) (jBound : ℕ) : Bool :=
    (List.range jBound).any fun j =>
      if hj : j < r then (s ⟨j, hj⟩ i != s ⟨0, hr⟩ i) && decide (j = j₀.val) else false
  let sim : Wire (n + q) c'.size → WireSim n c.size
    | .input idx =>
      if h : idx.val < n then .inr (false, .input ⟨idx.val, h⟩)
      else .inl (j₀.val.testBit (idx.val - n))
    | .gate k' =>
      if hk : k'.val < c.size then .inr (false, .gate ⟨k'.val, hk⟩)
      else
        let e := k'.val - c.size
        if e = 0 then .inl false
        else if e = 1 then .inl true
        else if e < 2 + q then .inl (!j₀.val.testBit (e - 2))
        else if e < 2 + q + r * q then
          let p := e - (2 + q)
          .inl (eqMatch (p / q) (p % q + 1))
        else
          let p := e - (2 + q + r * q)
          let ia := p / (r + 6)
          let off := p % (r + 6)
          if hia : ia < m then
            let i : Fin m := ⟨ia, hia⟩
            let sj := s j₀ i
            if off < r then .inl (diffAcc i (off + 1))
            else if off = r then .inl sj
            else if off = r + 1 then .inl (!sj)
            else if off = r + 2 then .inr (true, c.outputs i)
            else if off = r + 3 then if sj then .inl false else .inr (false, c.outputs i)
            else if off = r + 4 then if sj then .inr (true, c.outputs i) else .inl false
            else .inr (sj, c.outputs i)
          else .inl false
  let cv (idx : ℕ) : Bool :=
    match natToWire (n + q) c'.size idx with
    | some w => match sim w with | .inl bv => bv | .inr _ => false
    | none => false
  have hsim_const {idx : ℕ} {bv : Bool} (hlt : idx < (n + q) + c'.size)
      (h : ∀ w, natToWire (n + q) c'.size idx = some w → sim w = .inl bv) :
      (∀ (k' : Fin c'.size), idx < (n + q) + k'.val → ∀ u,
        natToWire (n + q) k'.val idx = some u →
        sim (wireCastLE k'.isLt.le u) = .inl (cv idx)) ∧ cv idx = bv := by
    obtain ⟨w, hw, -⟩ := isSome_natToWire_of_lt hlt
    have hsw := h w hw
    have hcve : cv idx = bv := by simp [cv, hw, hsw]
    refine ⟨fun k' hk u hu => ?_, hcve⟩
    have hnw : natToWire (n + q) c'.size idx = some (wireCastLE k'.isLt.le u) := by
      by_cases h1 : idx < n + q
      · rw [natToWire_of_lt _ h1, Option.some.injEq] at hu; subst hu
        rw [wireCastLE_input]; exact natToWire_of_lt _ h1
      · have h2 : idx - (n + q) < k'.val := by omega
        rw [natToWire_of_ge_of_lt h1 h2, Option.some.injEq] at hu; subst hu
        rw [wireCastLE_gate]; exact natToWire_of_ge_of_lt h1 (by omega)
    rw [hcve]; exact h _ hnw
  have hgate_nw {e : ℕ} (he : e < gsLen) :
      natToWire (n + q) c'.size (base0 + e) =
        some (.gate ⟨c.size + e, by rw [hc'_sz]; omega⟩) := by
    have h1 : ¬(base0 + e < n + q) := by dsimp [base0]; omega
    have h2 : base0 + e - (n + q) = c.size + e := by dsimp [base0]; omega
    have h3 : base0 + e - (n + q) < c'.size := by rw [h2, hc'_sz]; omega
    rw [natToWire_of_ge_of_lt h1 h3]; congr 2; exact Fin.ext h2
  have hsim_extra {e : ℕ} (he : e < gsLen) :
      sim (.gate ⟨c.size + e, by rw [hc'_sz]; omega⟩) =
        (if e = 0 then .inl false
         else if e = 1 then .inl true
         else if e < 2 + q then .inl (!j₀.val.testBit (e - 2))
         else if e < 2 + q + r * q then
           .inl (eqMatch ((e - (2 + q)) / q) ((e - (2 + q)) % q + 1))
         else
           let p := e - (2 + q + r * q)
           let ia := p / (r + 6); let off := p % (r + 6)
           if hia : ia < m then
             let i : Fin m := ⟨ia, hia⟩; let sj := s j₀ i
             if off < r then .inl (diffAcc i (off + 1))
             else if off = r then .inl sj
             else if off = r + 1 then .inl (!sj)
             else if off = r + 2 then .inr (true, c.outputs i)
             else if off = r + 3 then if sj then .inl false else .inr (false, c.outputs i)
             else if off = r + 4 then if sj then .inr (true, c.outputs i) else .inl false
             else .inr (sj, c.outputs i)
           else .inl false) := by
    dsimp only [sim]
    rw [dite_eq_right (show ¬(c.size + e < c.size) by omega)]
    simp only [Nat.add_sub_cancel_left]
  have hfw_c := hsim_const (idx := base0) (bv := false)
    (by rw [hc'_sz]; dsimp [base0, gsLen]; omega)
    (fun w hw => by
      have he0 : 0 < gsLen := by dsimp [gsLen]; omega
      have h0 := hgate_nw he0; simp only [add_zero] at h0
      cases hw.symm.trans h0; exact hsim_extra he0)
  have htw_c := hsim_const (idx := base0 + 1) (bv := true)
    (by rw [hc'_sz]; dsimp [base0, gsLen]; omega)
    (fun w hw => by
      have he1 : 1 < gsLen := by dsimp [gsLen]; omega
      cases hw.symm.trans (hgate_nw he1); exact hsim_extra he1)
  have hin_c (t : ℕ) (ht : t < q) := hsim_const (idx := n + t) (bv := j₀.val.testBit t)
    (by omega)
    (fun w hw => by
      have h0 : natToWire (n + q) c'.size (n + t) = some (.input ⟨n + t, by omega⟩) :=
        natToWire_of_lt _ (by omega)
      cases hw.symm.trans h0; simp [sim, show ¬(n + t < n) by omega])
  have hneg_c (t : ℕ) (ht : t < q) := hsim_const (idx := negBase + t) (bv := !j₀.val.testBit t)
    (by rw [hc'_sz]; dsimp [negBase, base0, gsLen]; omega)
    (fun w hw => by
      have he : 2 + t < gsLen := by dsimp [gsLen]; omega
      have h0 := hgate_nw he
      rw [show base0 + (2 + t) = negBase + t by dsimp [negBase]; omega] at h0
      cases hw.symm.trans h0
      simpa [show 2 + t ≠ 1 by omega, ht] using hsim_extra he)
  let eqW (j : ℕ) : ℕ := if q = 0 then base0 + 1 else eqBase + (j + 1) * q - 1
  have heqW_c (j : ℕ) (hj : j < r) :
      eqW j < outBase ∧
      (∀ k' : Fin c'.size, eqW j < (n + q) + k'.val →
        ∀ u, natToWire (n + q) k'.val (eqW j) = some u →
        sim (wireCastLE k'.isLt.le u) = .inl (cv (eqW j))) ∧
      cv (eqW j) = decide (j = j₀.val) := by
    by_cases hq0 : q = 0
    · have hr1 : r = 1 := by have : 2 ^ q = 1 := by subst hq0; rfl
                             omega
      have hj0 : j = 0 := by omega
      have hj0' : j₀.val = 0 := by have := j₀.isLt; omega
      dsimp only [eqW]; rw [ite_eq_left hq0]
      exact ⟨by dsimp [outBase, eqBase, negBase]; omega, htw_c.1,
        htw_c.2.trans (by simp [hj0, hj0'])⟩
    · have hq1 : 1 ≤ q := by omega
      have hmul : (j + 1) * q ≤ r * q := Nat.mul_le_mul_right q hj
      have hp : j * q + (q - 1) < r * q := by rw [Nat.succ_mul] at hmul; omega
      have he : 2 + q + (j * q + (q - 1)) < gsLen := by dsimp [gsLen]; omega
      have hidx : eqW j = base0 + (2 + q + (j * q + (q - 1))) := by
        simp only [eqW, hq0, ↓reduceIte, eqBase, negBase, Nat.succ_mul]; omega
      have hdiv : (j * q + (q - 1)) / q = j := by
        rw [mul_comm j q, Nat.mul_add_div hq1, Nat.div_eq_of_lt (by omega), add_zero]
      have hmod : (j * q + (q - 1)) % q + 1 = q := by
        rw [mul_comm j q, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]; omega
      have hem : eqMatch j q = decide (j = j₀.val) := by
        rw [Bool.eq_iff_iff]; simp only [eqMatch, List.all_eq_true, List.mem_range, beq_iff_eq,
          decide_eq_true_eq]
        refine ⟨fun h => (eq_of_lt_two_pow_of_testBit_eq (lt_of_lt_of_le j₀.isLt hrq)
          (lt_of_lt_of_le hj hrq) fun t => h t.val t.isLt).symm, fun h t _ => by rw [h]⟩
      have hsc := hsim_const (idx := eqW j) (bv := decide (j = j₀.val))
        (by rw [hidx, hc'_sz]; dsimp [base0, gsLen]; omega)
        (fun w hw => by
          rw [hidx] at hw; cases hw.symm.trans (hgate_nw he)
          have hs := hsim_extra he
          simp only [show 2 + q + (j * q + (q - 1)) ≠ 0 by omega,
            show 2 + q + (j * q + (q - 1)) ≠ 1 by omega,
            show ¬(2 + q + (j * q + (q - 1)) < 2 + q) by omega,
            show 2 + q + (j * q + (q - 1)) < 2 + q + r * q by omega,
            Nat.add_sub_cancel_left, hdiv, hmod, hem, ↓reduceIte] at hs
          exact hs)
      exact ⟨by rw [hidx]; dsimp [outBase, eqBase, negBase]; omega, hsc.1, hsc.2⟩
  have hgates (k' : Fin c'.size) : IsGateSim c' c sim k' := by
    by_cases hk : k'.val < c.size
    · have hl := lines_ilangoCircuit_lt c q r hr s k' hk
      have hop_eq : (c'.program.lines k').op = (c.program.lines ⟨k'.val, hk⟩).op := by
        dsimp only [c']; rw [hl]; rfl
      refine isGateSim_of_preserve ⟨k'.val, hk⟩ hop_eq (by simp [sim, hk]) fun a => ?_
      have hw_eq : sim (((c.program.lines ⟨k'.val, hk⟩).mapInputs (Fin.castAdd q) |>.mapWires
          (wireCastLE (by rw [size_ilangoCircuit]; omega))).wires
            (a.cast (by dsimp only [c']; rw [hl]))) =
          .inr (false, (c.program.lines ⟨k'.val, hk⟩).wires
            (a.cast (congrArg signature.Arity hop_eq))) := by
        dsimp only [Line.mapWires, Line.mapInputs, Function.comp_apply]
        cases (c.program.lines ⟨k'.val, hk⟩).wires _ with
        | input idx => simp [Wire.mapInputs, Fin.val_castAdd, sim, idx.isLt]
        | gate g => simp [Wire.mapInputs, sim, g.isLt]
      have hcast : ∀ (l₁ l₂ : Line signature (n + q) c'.size) (h : l₁ = l₂)
          (i : Fin (signature.Arity l₁.op)),
          l₁.wires i = l₂.wires (i.cast (by rw [h])) := by rintro l₁ _ rfl _; rfl
      rw [hcast (c'.program.lines k') _ hl a]; exact hw_eq
    · set e := k'.val - c.size
      have he_lt : e < gsLen := by have h := k'.isLt.trans_eq hc'_sz; omega
      have hke : k'.val = c.size + e := by omega
      have hce_lt : c.size + e < c'.size := by omega
      have hfin : k' = ⟨c.size + e, hce_lt⟩ := Fin.ext hke
      have hsim_k : sim (.gate k') = sim (.gate ⟨c.size + e, hce_lt⟩) :=
        congrArg (fun x => sim (.gate x)) hfin
      have hlk : c'.program.lines k' =
          (rawGateToLine (n + q) k'.val (ilangoExtraGate c q r hr s e)).mapWires
            (wireCastLE k'.isLt.le) := lines_ilangoCircuit_ge c q r hr s k' hk
      by_cases he0 : e = 0
      · have hrg : ilangoExtraGate c q r hr s e = .const false := by simp [he0]
        have hl : c'.program.lines k' = ⟨.const false, Fin.elim0⟩ := by
          rw [hlk, hrg,
            rawGateToLine_const]; dsimp [Line.mapWires]; congr 1; funext x; exact x.elim0
        exact isGateSim_of_oneVar (.input ⟨0, hn⟩) (.inl false) (.inl false) (.inl false)
          (by rw [hsim_k, hsim_extra he_lt]; simp [he0])
          (fun x => by rw [hl] at x; exact x.elim0) (by rw [hl]; exact fun _ => rfl)
      · by_cases he1 : e = 1
        · have hrg : ilangoExtraGate c q r hr s e = .const true := by simp [he1]
          have hl : c'.program.lines k' = ⟨.const true, Fin.elim0⟩ := by
            rw [hlk, hrg, rawGateToLine_const]; dsimp [Line.mapWires]; congr 1; funext x
            exact x.elim0
          exact isGateSim_of_oneVar (.input ⟨0, hn⟩) (.inl true) (.inl false) (.inl false)
            (by rw [hsim_k, hsim_extra he_lt]; simp [he1])
            (fun x => by rw [hl] at x; exact x.elim0) (by rw [hl]; exact fun _ => rfl)
        · by_cases heq_neg : e < 2 + q
          · set t := e - 2
            have htq : t < q := by omega
            have hrg : ilangoExtraGate c q r hr s e = .not (n + t) :=
              ilangoExtraGate_of_lt_neg c q r hr s he0 he1 heq_neg
            have hnt_lt : n + t < (n + q) + k'.val := by omega
            obtain ⟨u₀, hu₀, -⟩ := isSome_natToWire_of_lt hnt_lt
            have hl : c'.program.lines k' = ⟨.not, fun _ => wireCastLE k'.isLt.le u₀⟩ := by
              rw [hlk, hrg, rawGateToLine_not_of_eq hu₀]; rfl
            exact isGateSim_of_oneVar (.input ⟨0, hn⟩) (.inl (!j₀.val.testBit t))
              (.inl (j₀.val.testBit t)) (.inl false)
              (by rw [hsim_k, hsim_extra he_lt]; simp [he0, he1, heq_neg, t])
              (fun x => by
                generalize c'.program.lines k' = lk at hl x ⊢; subst hl
                fin_cases x
                exact ((hin_c t htq).1 k' hnt_lt u₀ hu₀).trans (by rw [(hin_c t htq).2]; rfl))
              (by rw [hl]; intro _; cases j₀.val.testBit t <;> rfl)
          · by_cases heq_ch : e < 2 + q + r * q
            · set p := e - (2 + q)
              have hprq : p < r * q := by omega
              have hq1 : 1 ≤ q := by
                by_contra h; have h0 : q = 0 := by omega
                rw [h0, mul_zero] at hprq; omega
              set a_j := p / q; set t := p % q
              have htq : t < q := Nat.mod_lt p hq1
              let acc := if t = 0 then base0 + 1 else eqBase + a_j * q + t - 1
              let lit := if a_j.testBit t then n + t else negBase + t
              have hrg : ilangoExtraGate c q r hr s e = .and acc lit :=
                ilangoExtraGate_of_lt_eqChain c q r hr s heq_neg heq_ch
              have hpt : a_j * q + t = p := by rw [mul_comm]; exact Nat.div_add_mod p q
              have hacc_lt : acc < (n + q) + k'.val := by
                dsimp only [acc]; split_ifs <;> (dsimp [eqBase, negBase, base0] at *; omega)
              have hlit_lt : lit < (n + q) + k'.val := by
                dsimp only [lit]; split_ifs <;> (dsimp [negBase, base0] at *; omega)
              obtain ⟨u₁, hu₁, -⟩ := isSome_natToWire_of_lt hacc_lt
              obtain ⟨u₂, hu₂, -⟩ := isSome_natToWire_of_lt hlit_lt
              have hl : c'.program.lines k' =
                  ⟨.and, ![wireCastLE k'.isLt.le u₁, wireCastLE k'.isLt.le u₂]⟩ := by
                rw [hlk, hrg, rawGateToLine_and_of_eq hu₁ hu₂]
                dsimp only [Line.mapWires]; congr 1; funext x; fin_cases x <;> rfl
              have hb1 : sim (wireCastLE k'.isLt.le u₁) = .inl (eqMatch a_j t) := by
                by_cases ht0 : t = 0
                · have hacc_eq : acc = base0 + 1 := ite_eq_left ht0
                  have h1 := htw_c.1 k' (hacc_eq ▸ hacc_lt) u₁ (hacc_eq ▸ hu₁)
                  rw [h1, htw_c.2, ht0]; simp [eqMatch]
                · have hacc_eq : acc = base0 + (2 + q + (p - 1)) := by
                    dsimp [acc, eqBase, negBase]; rw [ite_eq_right ht0]; omega
                  have hp1_eq : p - 1 = q * a_j + (t - 1) := by rw [mul_comm q a_j]; omega
                  have hp1_div : (p - 1) / q = a_j := by
                    rw [hp1_eq, Nat.mul_add_div hq1, Nat.div_eq_of_lt (by omega), add_zero]
                  have hp1_mod : (p - 1) % q + 1 = t := by
                    rw [hp1_eq, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]; omega
                  have he' : 2 + q + (p - 1) < gsLen := by dsimp [gsLen]; omega
                  have hsc := hsim_const (idx := acc) (bv := eqMatch a_j t)
                    (by rw [hc'_sz]; dsimp [gsLen] at *; omega)
                    (fun w hw => by
                      rw [hacc_eq] at hw; cases hw.symm.trans (hgate_nw he')
                      simpa [show 2 + q + (p - 1) ≠ 1 by omega,
                        show ¬(2 + q + (p - 1) < 2 + q) by omega,
                        show 2 + q + (p - 1) < 2 + q + r * q by omega,
                        hp1_div, hp1_mod] using hsim_extra he')
                  exact (hsc.1 k' hacc_lt u₁ hu₁).trans (by rw [hsc.2])
              let b2 := j₀.val.testBit t == a_j.testBit t
              have hb2 : sim (wireCastLE k'.isLt.le u₂) = .inl b2 := by
                by_cases htb : a_j.testBit t = true
                · have hle : lit = n + t := ite_eq_left htb
                  rw [(hin_c t htq).1 k' (hle ▸ hlit_lt) u₂ (hle ▸ hu₂), (hin_c t htq).2]
                  simp [b2, htb]
                · have hle : lit = negBase + t := ite_eq_right htb
                  rw [(hneg_c t htq).1 k' (hle ▸ hlit_lt) u₂ (hle ▸ hu₂), (hneg_c t htq).2]
                  have hf : a_j.testBit t = false := Bool.eq_false_iff.2 htb
                  simp [b2, hf]
              have hout : sim (.gate k') = .inl (eqMatch a_j t && b2) := by
                rw [hsim_k, hsim_extra he_lt]
                simp only [he0, he1, heq_neg, heq_ch, ↓reduceIte,
                  show e - (2 + q) = p from rfl, show p / q = a_j from rfl,
                  show p % q = t from rfl, eqMatch, List.range_succ, List.all_append,
                  List.all_cons, List.all_nil, Bool.and_true, b2]
              exact isGateSim_of_oneVar (.input ⟨0, hn⟩) (.inl (eqMatch a_j t && b2))
                (.inl (eqMatch a_j t)) (.inl b2) hout
                (fun x => by
                  generalize c'.program.lines k' = lk at hl x ⊢; subst hl
                  fin_cases x
                  · exact hb1
                  · exact hb2)
                (by rw [hl]; intro _; cases eqMatch a_j t <;> cases b2 <;> rfl)
            · set p := e - (2 + q + r * q)
              have hpm : p < m * (r + 6) := by dsimp [gsLen] at he_lt; omega
              set ia := p / (r + 6); set off := p % (r + 6)
              have hia : ia < m := Nat.div_lt_of_lt_mul (by rwa [mul_comm])
              have hoff : off < r + 6 := Nat.mod_lt p (by omega)
              let i : Fin m := ⟨ia, hia⟩
              let bc := outBase + ia * (r + 6)
              let s0 := s ⟨0, hr⟩ i
              let sj := s j₀ i
              let outWi := wireToNat ((c.outputs i).mapInputs (Fin.castAdd q))
              have hp_eq : ia * (r + 6) + off = p := by
                rw [mul_comm]; exact Nat.div_add_mod p (r + 6)
              have hbc_off : bc + off = (n + q) + k'.val := by
                dsimp [bc, outBase, eqBase, negBase, base0]; omega
              have hrg : ilangoExtraGate c q r hr s e =
                  (if hj : off < r then
                    .or (if off = 0 then base0 else bc + off - 1)
                      (if s ⟨off, hj⟩ i != s0 then eqW off else base0)
                   else if off = r then
                     if s0 then .not (bc + r - 1) else .or (bc + r - 1) base0
                   else if off = r + 1 then .not (bc + r)
                   else if off = r + 2 then .not outWi
                   else if off = r + 3 then .and outWi (bc + r + 1)
                   else if off = r + 4 then .and (bc + r + 2) (bc + r)
                   else .or (bc + r + 3) (bc + r + 4)) :=
                ilangoExtraGate_of_outBlock c q r hr s heq_ch hia
              have hsk_base : sim (.gate k') =
                  (if off < r then .inl (diffAcc i (off + 1))
                   else if off = r then .inl sj
                   else if off = r + 1 then .inl (!sj)
                   else if off = r + 2 then .inr (true, c.outputs i)
                   else if off = r + 3 then if sj then .inl false else .inr (false, c.outputs i)
                   else if off = r + 4 then if sj then .inr (true, c.outputs i) else .inl false
                   else .inr (sj, c.outputs i)) := by
                rw [hsim_k, hsim_extra he_lt]
                simp [he0, he1, heq_neg, heq_ch, show e - (2 + q + r * q) = p from rfl,
                  show p / (r + 6) = ia from rfl, show p % (r + 6) = off from rfl, hia, i, sj]
              have hdiff_wire (d : ℕ) (hd : d < r) (hlt_k : bc + d < (n + q) + k'.val) :
                  ∀ u, natToWire (n + q) k'.val (bc + d) = some u →
                    sim (wireCastLE k'.isLt.le u) = .inl (diffAcc i (d + 1)) := by
                let p' := ia * (r + 6) + d
                have he' : 2 + q + r * q + p' < gsLen := by
                  have : (ia + 1) * (r + 6) ≤ m * (r + 6) := Nat.mul_le_mul_right _ hia
                  rw [Nat.succ_mul] at this; dsimp [gsLen]; omega
                have hdiv' : p' / (r + 6) = ia := by
                  dsimp only [p']
                  rw [mul_comm ia, Nat.mul_add_div (by omega), Nat.div_eq_of_lt (by omega),
                    add_zero]
                have hmod' : p' % (r + 6) = d := by
                  dsimp only [p']
                  rw [mul_comm ia, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
                have hbcd : bc + d = base0 + (2 + q + r * q + p') := by
                  dsimp [bc, outBase, eqBase, negBase, p']; omega
                have hsc := hsim_const (idx := bc + d) (bv := diffAcc i (d + 1))
                  (by rw [hc'_sz]; dsimp [base0] at hbcd; omega)
                  (fun w hw => by
                    rw [hbcd] at hw; cases hw.symm.trans (hgate_nw he')
                    simpa [show 2 + q + r * q + p' ≠ 1 by omega,
                      show ¬(2 + q + r * q + p' < 2 + q) by omega,
                      show ¬(2 + q + r * q + p' < 2 + q + r * q) by omega,
                      hdiv', hmod', hia, hd] using hsim_extra he')
                exact fun u hu => (hsc.1 k' hlt_k u hu).trans (by rw [hsc.2])
              have haux_wire (d : ℕ) (hdr : r ≤ d) (hd6 : d < r + 6)
                  (hlt_k : bc + d < (n + q) + k'.val) :
                  ∀ u, natToWire (n + q) k'.val (bc + d) = some u →
                    sim (wireCastLE k'.isLt.le u) =
                      (if d = r then .inl sj
                       else if d = r + 1 then .inl (!sj)
                       else if d = r + 2 then .inr (true, c.outputs i)
                       else if d = r + 3 then if sj then .inl false else .inr (false, c.outputs i)
                       else if d = r + 4 then if sj then .inr (true, c.outputs i) else .inl false
                       else .inr (sj, c.outputs i)) := by
                intro u hu
                let p' := ia * (r + 6) + d
                have he' : 2 + q + r * q + p' < gsLen := by
                  have : (ia + 1) * (r + 6) ≤ m * (r + 6) := Nat.mul_le_mul_right _ hia
                  rw [Nat.succ_mul] at this; dsimp [gsLen]; omega
                have hdiv' : p' / (r + 6) = ia := by
                  dsimp only [p']
                  rw [mul_comm ia, Nat.mul_add_div (by omega), Nat.div_eq_of_lt hd6, add_zero]
                have hmod' : p' % (r + 6) = d := by
                  dsimp only [p']
                  rw [mul_comm ia, Nat.mul_add_mod, Nat.mod_eq_of_lt hd6]
                have hbcd : bc + d = base0 + (2 + q + r * q + p') := by
                  dsimp [bc, outBase, eqBase, negBase, p']; omega
                have hnw : natToWire (n + q) c'.size (bc + d) = some (wireCastLE k'.isLt.le u) := by
                  have h1 : ¬(bc + d < n + q) := by
                    dsimp [bc, outBase, eqBase, negBase, base0]; omega
                  have h2 : bc + d - (n + q) < k'.val := by omega
                  rw [natToWire_of_ge_of_lt h1 h2, Option.some.injEq] at hu; subst hu
                  rw [wireCastLE_gate]; exact natToWire_of_ge_of_lt h1 (by omega)
                rw [hbcd] at hnw
                rw [Option.some.inj (hnw.symm.trans (hgate_nw he'))]
                simpa [show 2 + q + r * q + p' ≠ 1 by omega,
                  show ¬(2 + q + r * q + p' < 2 + q) by omega,
                  show ¬(2 + q + r * q + p' < 2 + q + r * q) by omega,
                  hdiv', hmod', hia, show ¬(d < r) by omega] using hsim_extra he'
              have houtW_sim : outWi < (n + q) + k'.val ∧
                  ∀ u, natToWire (n + q) k'.val outWi = some u →
                    sim (wireCastLE k'.isLt.le u) = .inr (false, c.outputs i) := by
                cases hco : c.outputs i with
                | input a_in =>
                  have h0 : outWi = a_in.val := by simp [outWi, hco, Wire.mapInputs]
                  have hlt : outWi < (n + q) + k'.val := by rw [h0]; omega
                  refine ⟨hlt, fun u hu => ?_⟩
                  have h1 : a_in.val < n + q := by omega
                  rw [h0, natToWire_of_lt _ h1, Option.some.injEq] at hu; subst hu
                  simp [sim, a_in.isLt]
                | gate g_in =>
                  have h0 : outWi = n + q + g_in.val := by simp [outWi, hco, Wire.mapInputs]
                  have hlt : outWi < (n + q) + k'.val := by have := g_in.isLt; rw [h0]; omega
                  refine ⟨hlt, fun u hu => ?_⟩
                  have h1 : ¬(n + q + g_in.val < n + q) := by omega
                  have h2 : n + q + g_in.val - (n + q) < k'.val := by have := g_in.isLt; omega
                  rw [h0, natToWire_of_ge_of_lt h1 h2, Option.some.injEq] at hu; subst hu
                  simp [sim, g_in.isLt]
              by_cases hj : off < r
              · simp only [hj, ↓reduceDIte] at hrg
                let op1 := if off = 0 then base0 else bc + off - 1
                let op2 := if s ⟨off, hj⟩ i != s0 then eqW off else base0
                have h1lt : op1 < (n + q) + k'.val := by
                  dsimp [op1]
                  split_ifs <;> (dsimp [bc, outBase, eqBase, negBase, base0] at *; omega)
                have h2lt : op2 < (n + q) + k'.val := by
                  have := (heqW_c off hj).1; dsimp [op2]
                  split_ifs <;> (dsimp [bc, outBase, eqBase, negBase, base0] at *; omega)
                obtain ⟨u₁, hu₁, -⟩ := isSome_natToWire_of_lt h1lt
                obtain ⟨u₂, hu₂, -⟩ := isSome_natToWire_of_lt h2lt
                have hl : c'.program.lines k' =
                    ⟨.or, ![wireCastLE k'.isLt.le u₁, wireCastLE k'.isLt.le u₂]⟩ := by
                  rw [hlk, hrg, rawGateToLine_or_of_eq hu₁ hu₂]
                  dsimp only [Line.mapWires]; congr 1; funext x; fin_cases x <;> rfl
                have hs1 : sim (wireCastLE k'.isLt.le u₁) = .inl (diffAcc i off) := by
                  by_cases h0 : off = 0
                  · have he1' : op1 = base0 := ite_eq_left h0
                    rw [hfw_c.1 k' (he1' ▸ h1lt) u₁ (he1' ▸ hu₁), hfw_c.2, h0]; simp [diffAcc]
                  · have he1' : op1 = bc + (off - 1) := by dsimp [op1]; rw [ite_eq_right h0]; omega
                    simpa [show off - 1 + 1 = off by omega] using
                      hdiff_wire (off - 1) (by omega) (he1' ▸ h1lt) u₁ (he1' ▸ hu₁)
                let b2 := (s ⟨off, hj⟩ i != s0) && decide (off = j₀.val)
                have hs2 : sim (wireCastLE k'.isLt.le u₂) = .inl b2 := by
                  by_cases hd : (s ⟨off, hj⟩ i != s0) = true
                  · have he2' : op2 = eqW off := ite_eq_left hd
                    rw [(heqW_c off hj).2.1 k' (he2' ▸ h2lt) u₂ (he2' ▸ hu₂), (heqW_c off hj).2.2]
                    simp [b2, hd]
                  · have he2' : op2 = base0 := ite_eq_right hd
                    rw [hfw_c.1 k' (he2' ▸ h2lt) u₂ (he2' ▸ hu₂), hfw_c.2]
                    have hf : (s ⟨off, hj⟩ i != s0) = false := Bool.eq_false_iff.2 hd
                    simp [b2, hf]
                have hout : sim (.gate k') = .inl (diffAcc i off || b2) := by
                  rw [hsk_base, ite_eq_left hj]
                  simp [diffAcc, List.range_succ, List.any_append, hj, b2, s0]
                exact isGateSim_of_oneVar (.input ⟨0, hn⟩) (.inl (diffAcc i off || b2))
                  (.inl (diffAcc i off)) (.inl b2) hout
                  (fun x => by
                    generalize c'.program.lines k' = lk at hl x ⊢; subst hl
                    fin_cases x
                    · exact hs1
                    · exact hs2)
                  (by rw [hl]; intro _; cases diffAcc i off <;> cases b2 <;> rfl)
              · have hdiff_r : diffAcc i r = (sj != s0) := by
                  dsimp only [diffAcc, sj, s0]
                  cases hne : (s j₀ i != s ⟨0, hr⟩ i)
                  · rw [List.any_eq_false]; intro j hjr
                    have hjr' := List.mem_range.1 hjr
                    by_cases hje : j = j₀.val
                    · subst hje
                      simp only [j₀.isLt, ↓reduceDIte, hne, Bool.false_and, Bool.false_eq_true,
                        not_false_eq_true]
                    · simp only [hjr', ↓reduceDIte, hje, decide_false, Bool.and_false,
                        Bool.false_eq_true, not_false_eq_true]
                  · rw [List.any_eq_true]
                    exact ⟨j₀.val, List.mem_range.2 j₀.isLt,
                      by simp only [j₀.isLt, ↓reduceDIte, hne, decide_true, Bool.and_true]⟩
                let wi := c.outputs i
                let gExtra := ilangoExtraGate c q r hr s e
                have h1not {idx : ℕ} (hlt : idx < (n + q) + k'.val) (hgr : gExtra = .not idx)
                    (eOut e0 : OneVarSim) (ho : sim (.gate k') = liftOneVar wi eOut)
                    (ha : ∀ u, natToWire (n + q) k'.val idx = some u →
                      sim (wireCastLE k'.isLt.le u) = liftOneVar wi e0)
                    (ht : oneVarGateTemplate .not eOut e0 (.inl false) ∈ TAUT) :
                    IsGateSim c' c sim k' := by
                  obtain ⟨u, hu, -⟩ := isSome_natToWire_of_lt hlt
                  have hl : c'.program.lines k' = ⟨.not, fun _ => wireCastLE k'.isLt.le u⟩ := by
                    rw [hlk]; change (rawGateToLine _ _ gExtra).mapWires _ = _
                    rw [hgr, rawGateToLine_not_of_eq hu]; rfl
                  exact isGateSim_of_oneVar wi eOut e0 (.inl false) ho
                    (fun x => by
                      generalize c'.program.lines k' = lk at hl x ⊢; subst hl
                      fin_cases x; exact ha u hu)
                    (by rw [hl]; exact ht)
                have h2and {i₁ i₂ : ℕ}
                    (h1 : i₁ < (n + q) + k'.val) (h2 : i₂ < (n + q) + k'.val)
                    (hgr : gExtra = .and i₁ i₂)
                    (eOut e0 e1 : OneVarSim) (ho : sim (.gate k') = liftOneVar wi eOut)
                    (ha0 : ∀ u, natToWire (n + q) k'.val i₁ = some u →
                      sim (wireCastLE k'.isLt.le u) = liftOneVar wi e0)
                    (ha1 : ∀ u, natToWire (n + q) k'.val i₂ = some u →
                      sim (wireCastLE k'.isLt.le u) = liftOneVar wi e1)
                    (ht : oneVarGateTemplate .and eOut e0 e1 ∈ TAUT) :
                    IsGateSim c' c sim k' := by
                  obtain ⟨u₁, hu₁, -⟩ := isSome_natToWire_of_lt h1
                  obtain ⟨u₂, hu₂, -⟩ := isSome_natToWire_of_lt h2
                  have hl : c'.program.lines k' =
                      ⟨.and, ![wireCastLE k'.isLt.le u₁, wireCastLE k'.isLt.le u₂]⟩ := by
                    rw [hlk]; change (rawGateToLine _ _ gExtra).mapWires _ = _
                    rw [hgr, rawGateToLine_and_of_eq hu₁ hu₂]
                    dsimp only [Line.mapWires]; congr 1; funext x; fin_cases x <;> rfl
                  exact isGateSim_of_oneVar wi eOut e0 e1 ho
                    (fun x => by
                      generalize c'.program.lines k' = lk at hl x ⊢; subst hl
                      fin_cases x
                      · exact ha0 u₁ hu₁
                      · exact ha1 u₂ hu₂)
                    (by rw [hl]; exact ht)
                have h2or {i₁ i₂ : ℕ}
                    (h1 : i₁ < (n + q) + k'.val) (h2 : i₂ < (n + q) + k'.val)
                    (hgr : gExtra = .or i₁ i₂)
                    (eOut e0 e1 : OneVarSim) (ho : sim (.gate k') = liftOneVar wi eOut)
                    (ha0 : ∀ u, natToWire (n + q) k'.val i₁ = some u →
                      sim (wireCastLE k'.isLt.le u) = liftOneVar wi e0)
                    (ha1 : ∀ u, natToWire (n + q) k'.val i₂ = some u →
                      sim (wireCastLE k'.isLt.le u) = liftOneVar wi e1)
                    (ht : oneVarGateTemplate .or eOut e0 e1 ∈ TAUT) :
                    IsGateSim c' c sim k' := by
                  obtain ⟨u₁, hu₁, -⟩ := isSome_natToWire_of_lt h1
                  obtain ⟨u₂, hu₂, -⟩ := isSome_natToWire_of_lt h2
                  have hl : c'.program.lines k' =
                      ⟨.or, ![wireCastLE k'.isLt.le u₁, wireCastLE k'.isLt.le u₂]⟩ := by
                    rw [hlk]; change (rawGateToLine _ _ gExtra).mapWires _ = _
                    rw [hgr, rawGateToLine_or_of_eq hu₁ hu₂]
                    dsimp only [Line.mapWires]; congr 1; funext x; fin_cases x <;> rfl
                  exact isGateSim_of_oneVar wi eOut e0 e1 ho
                    (fun x => by
                      generalize c'.program.lines k' = lk at hl x ⊢; subst hl
                      fin_cases x
                      · exact ha0 u₁ hu₁
                      · exact ha1 u₂ hu₂)
                    (by rw [hl]; exact ht)
                change gExtra = _ at hrg
                rw [dite_eq_right hj] at hrg
                rw [ite_eq_right hj] at hsk_base
                rcases (show off = r ∨ off = r + 1 ∨ off = r + 2 ∨ off = r + 3 ∨
                    off = r + 4 ∨ off = r + 5 by omega) with ho | ho | ho | ho | ho | ho
                · simp only [ho, ↓reduceIte] at hrg hsk_base
                  have hdlt : bc + (r - 1) < (n + q) + k'.val := by omega
                  have hd_eq : bc + r - 1 = bc + (r - 1) := by omega
                  have hda : ∀ u, natToWire (n + q) k'.val (bc + r - 1) = some u →
                      sim (wireCastLE k'.isLt.le u) = .inl (sj != s0) := fun u hu => by
                    simpa [show r - 1 + 1 = r by omega, hdiff_r] using
                      hdiff_wire (r - 1) (by omega) hdlt u (hd_eq ▸ hu)
                  cases hs0v : s0
                  · simp only [show s0 = false from hs0v, Bool.false_eq_true, ↓reduceIte] at hrg
                    refine h2or (hd_eq.symm ▸ hdlt)
                      (by dsimp [bc, outBase, eqBase, negBase] at hbc_off; omega)
                      hrg (.inl sj) (.inl (sj != s0)) (.inl false) hsk_base hda
                      (fun u hu => (hfw_c.1 k'
                        (by dsimp [bc, outBase, eqBase, negBase] at hbc_off; omega) u hu).trans
                        (by rw [hfw_c.2]; rfl)) ?_
                    exact oneVarGateTemplate_mem_taut_of_eq _ _ _ _ fun _ => by
                      rw [hs0v]; cases sj <;> rfl
                  · simp only [show s0 = true from hs0v, ↓reduceIte] at hrg
                    refine h1not (hd_eq.symm ▸ hdlt) hrg (.inl sj) (.inl (sj != s0))
                      hsk_base hda ?_
                    exact oneVarGateTemplate_mem_taut_of_eq _ _ _ _ fun _ => by
                      rw [hs0v]; cases sj <;> rfl
                · simp only [ho, show r + 1 ≠ r by omega, ↓reduceIte] at hrg hsk_base
                  exact h1not (by omega) hrg (.inl (!sj)) (.inl sj) hsk_base
                    (fun u hu => by
                      simpa using haux_wire r le_rfl (by omega) (by omega) u hu)
                    (oneVarGateTemplate_mem_taut_of_eq _ _ _ _ fun _ => by cases sj <;> rfl)
                · simp only [ho, show r + 2 ≠ r by omega,
                    show r + 2 ≠ r + 1 by omega, ↓reduceIte] at hrg hsk_base
                  exact h1not houtW_sim.1 hrg (.inr true) (.inr false) hsk_base houtW_sim.2
                    (oneVarGateTemplate_mem_taut_of_eq _ _ _ _ fun v => by cases v <;> rfl)
                · simp only [ho, show r + 3 ≠ r by omega,
                    show r + 3 ≠ r + 1 by omega, show r + 3 ≠ r + 2 by omega,
                    ↓reduceIte] at hrg hsk_base
                  let eOut : OneVarSim := if sj then .inl false else .inr false
                  refine h2and houtW_sim.1 (by omega) hrg eOut (.inr false) (.inl (!sj))
                    (by rw [hsk_base]; dsimp only [eOut]; cases sj <;> rfl)
                    houtW_sim.2
                    (fun u hu => by
                      simpa [show r + 1 ≠ r by omega] using
                        haux_wire (r + 1) (by omega) (by omega) (by omega) u
                          (by rw [← add_assoc]; exact hu))
                    (oneVarGateTemplate_mem_taut_of_eq _ _ _ _ fun v => by
                      dsimp only [eOut]; cases sj <;> cases v <;> rfl)
                · simp only [ho, show r + 4 ≠ r by omega,
                    show r + 4 ≠ r + 1 by omega, show r + 4 ≠ r + 2 by omega,
                    show r + 4 ≠ r + 3 by omega, ↓reduceIte] at hrg hsk_base
                  let eOut : OneVarSim := if sj then .inr true else .inl false
                  refine h2and (by omega) (by omega) hrg eOut (.inr true) (.inl sj)
                    (by rw [hsk_base]; dsimp only [eOut]; cases sj <;> rfl)
                    (fun u hu => by
                      simpa [show r + 2 ≠ r by omega, show r + 2 ≠ r + 1 by omega] using
                        haux_wire (r + 2) (by omega) (by omega) (by omega) u
                          (by rw [← add_assoc]; exact hu))
                    (fun u hu => by
                      simpa using haux_wire r le_rfl (by omega) (by omega) u hu)
                    (oneVarGateTemplate_mem_taut_of_eq _ _ _ _ fun v => by
                      dsimp only [eOut]; cases sj <;> cases v <;> rfl)
                · simp only [ho, show r + 5 ≠ r by omega,
                    show r + 5 ≠ r + 1 by omega, show r + 5 ≠ r + 2 by omega,
                    show r + 5 ≠ r + 3 by omega, show r + 5 ≠ r + 4 by omega,
                    ↓reduceIte] at hrg hsk_base
                  let e0 : OneVarSim := if sj then .inl false else .inr false
                  let e1 : OneVarSim := if sj then .inr true else .inl false
                  refine h2or (by omega) (by omega) hrg (.inr sj) e0 e1 hsk_base
                    (fun u hu => by
                      have h0 := haux_wire (r + 3) (by omega) (by omega) (by omega) u
                        (by rw [← add_assoc]; exact hu)
                      simp only [show r + 3 ≠ r by omega, show r + 3 ≠ r + 1 by omega,
                        show r + 3 ≠ r + 2 by omega, ↓reduceIte] at h0
                      rw [h0]; dsimp only [e0]; cases sj <;> rfl)
                    (fun u hu => by
                      have h0 := haux_wire (r + 4) (by omega) (by omega) (by omega) u
                        (by rw [← add_assoc]; exact hu)
                      simp only [show r + 4 ≠ r by omega, show r + 4 ≠ r + 1 by omega,
                        show r + 4 ≠ r + 2 by omega, show r + 4 ≠ r + 3 by omega,
                        ↓reduceIte] at h0
                      rw [h0]; dsimp only [e1]; cases sj <;> rfl)
                    (oneVarGateTemplate_mem_taut_of_eq _ _ _ _ fun v => by
                      dsimp only [e0, e1]; cases sj <;> cases v <;> rfl)
  have houts : IsOutputSim c' c sim (bitXor a (s j₀)) a := by
    intro i
    let e := 2 + q + r * q + (i.val + 1) * (r + 6) - 1
    have hmul : (i.val + 1) * (r + 6) ≤ m * (r + 6) := Nat.mul_le_mul_right _ i.isLt
    have hpos : 1 ≤ (i.val + 1) * (r + 6) := Nat.mul_pos (Nat.succ_pos _) (by omega)
    have he_lt : e < gsLen := by dsimp [e, gsLen]; omega
    have hso : sim (c'.outputs i) = .inr (s j₀ i, c.outputs i) := by
      rw [show c'.outputs i = .gate ⟨c.size + e, by rw [hc'_sz]; omega⟩ from
        outputs_ilangoCircuit c q r hr s i, hsim_extra he_lt]
      have hp : e - (2 + q + r * q) = i.val * (r + 6) + (r + 5) := by
        dsimp [e]; rw [Nat.succ_mul]; omega
      have hdiv : (i.val * (r + 6) + (r + 5)) / (r + 6) = i.val := by
        rw [mul_comm i.val, Nat.mul_add_div (by omega), Nat.div_eq_of_lt (by omega), add_zero]
      have hmod : (i.val * (r + 6) + (r + 5)) % (r + 6) = r + 5 := by
        rw [mul_comm i.val, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
      simp [show e ≠ 0 by dsimp [e]; omega, show e ≠ 1 by dsimp [e]; omega,
        show ¬(e < 2 + q) by dsimp [e]; omega,
        show ¬(e < 2 + q + r * q) by dsimp [e]; omega,
        hp, hdiv, hmod, i.isLt, show ¬(r + 5 < r) by omega]
    rw [hso]
    cases hsj : s j₀ i
    · exact Or.inr (Or.inl ⟨rfl, bitXor_of_false_right a (s j₀) hsj⟩)
    · exact Or.inr (Or.inr ⟨rfl, bitXor_of_true_right a (s j₀) hsj⟩)
  obtain ⟨steps, hrun, hst_len⟩ := hred c' c sim (bitXor a (s j₀)) a hgates houts
  refine ⟨wireSimPairs sim, steps, hrun, ?_⟩
  have hp_len := length_wireSimPairs_le sim
  have hcs_le : c.size ≤ c'.size := by rw [hc'_sz]; omega
  set M := n + q + c'.size + m + 20
  have hN : (n + q) + c'.size + n + c.size + m + 2 ≤ 2 * M := by dsimp [M]; omega
  have hp_M : (encList (encPair encNat encFormula) (wireSimPairs sim)).length ≤
    40 * (2 * M) ^ 6 := by
    have h1 : n + q + c'.size + 1 ≤ 2 * M := by dsimp [M]; omega
    have h2 : n + c.size + (n + q) + c'.size + 20 ≤ 2 * M := by dsimp [M]; omega
    have h3 : (2 * M) ^ 2 ≤ (2 * M) ^ 6 := Nat.pow_le_pow_right (by dsimp [M]; omega) (by decide)
    calc _ ≤ 40 * (2 * M) * (2 * M) :=
          hp_len.trans (Nat.mul_le_mul (Nat.mul_le_mul_left 40 h1) h2)
      _ = 40 * (2 * M) ^ 2 := by rw [sq, mul_assoc]
      _ ≤ 40 * (2 * M) ^ 6 := Nat.mul_le_mul_left 40 h3
  have hs_M : (encList encEFStep steps).length ≤ C₀ * (2 * M) ^ 6 :=
    hst_len.trans (Nat.mul_le_mul_left C₀ (Nat.pow_le_pow_left hN 6))
  calc _ ≤ 40 * (2 * M) ^ 6 + C₀ * (2 * M) ^ 6 := Nat.add_le_add hp_M hs_M
    _ = (C₀ + 40) * (2 * M) ^ 6 := by rw [← Nat.add_mul, add_comm 40 C₀]
    _ = (C₀ + 40) * 2 ^ 6 * M ^ 6 := by rw [Nat.mul_pow, ← mul_assoc]

/-- Super-polynomial growth function `n ↦ n ^ ⌊log₂(⌊log₂(n + 4)⌋ + 2)⌋`: dominates `n ^ e` for
every constant `e : ℕ`, while remaining strictly below `2 ^ (n ^ δ)` for every constant `δ > 0`. -/
def ilangoThreshold (n : ℕ) : ℕ :=
  n ^ Nat.log 2 (Nat.log 2 (n + 4) + 2)

private theorem eventually_pow_le_ilangoThreshold (e : ℕ) :
    ∀ᶠ n : ℕ in atTop, n ^ e ≤ ilangoThreshold n := by
  let N := max 2 (2 ^ (2 ^ (e + 1)))
  filter_upwards [eventually_ge_atTop N] with n hn
  have h1 : 2 ^ (e + 1) ≤ Nat.log 2 (n + 4) + 2 := by
    have : 2 ^ (2 ^ (e + 1)) ≤ n + 4 := by dsimp [N] at hn; omega
    have hlg := Nat.le_log_of_pow_le one_lt_two this
    omega
  have h2 : e ≤ Nat.log 2 (Nat.log 2 (n + 4) + 2) :=
    (Nat.le_succ e).trans (Nat.le_log_of_pow_le one_lt_two h1)
  exact Nat.pow_le_pow_right (by dsimp [N] at hn; omega) h2

/-- Sub-exponential domination of any polynomial in `ilangoThreshold n` by `2 ^ (n ^ δ)`. -/
private theorem eventually_ilango_size_lt_subexp {δ : ℝ} (hδ : 0 < δ) (C A d : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      (C : ℝ) * (((n : ℝ) + 20) ^ A + (ilangoThreshold n : ℝ) + 1) ^ d + 16 <
        (2 : ℝ) ^ ((n : ℝ) ^ δ) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlog : ∀ᶠ n : ℕ in atTop,
      ((Real.log (n : ℝ)) ^ 2 / Real.log 2) ≤ (Real.log 2 / (2 * ((d : ℝ) + 1))) * (n : ℝ) ^ δ := by
    have hev := (isLittleO_log_rpow_rpow_atTop (2 : ℝ) hδ).bound
      (show (0 : ℝ) < (Real.log 2) ^ 2 / (2 * ((d : ℝ) + 1)) by positivity)
    filter_upwards [hev.natCast_atTop, eventually_ge_atTop 2] with n hn _
    rw [Real.rpow_two, Real.norm_of_nonneg (sq_nonneg _),
      Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) δ)] at hn
    rw [div_le_iff₀ hlog2]
    calc Real.log (n : ℝ) ^ 2
        ≤ (Real.log 2) ^ 2 / (2 * ((d : ℝ) + 1)) * (n : ℝ) ^ δ := hn
      _ = Real.log 2 / (2 * ((d : ℝ) + 1)) * (n : ℝ) ^ δ * Real.log 2 := by ring
  have hconst : ∀ᶠ n : ℕ in atTop,
      Real.log ((C : ℝ) + 20) + 4 * ((d : ℝ) + 1) < (Real.log 2 / 2) * (n : ℝ) ^ δ := by
    have ht := (tendsto_rpow_atTop hδ).comp tendsto_natCast_atTop_atTop
    filter_upwards [ht.eventually_gt_atTop
      ((Real.log ((C : ℝ) + 20) + 4 * ((d : ℝ) + 1)) / (Real.log 2 / 2))] with n hn
    dsimp only [Function.comp_apply] at hn
    have h1 := (div_lt_iff₀ (by positivity)).1 hn
    linarith
  filter_upwards [hlog, hconst, eventually_ge_atTop (max 24 (2 ^ (2 ^ (2 * A + 1))))]
    with n hln hcn hnmax
  have hn24 : 24 ≤ n := (le_max_left _ _).trans hnmax
  set e := Nat.log 2 (Nat.log 2 (n + 4) + 2)
  have hAe : 2 * A ≤ e := by
    have h1 : 2 ^ (2 * A + 1) ≤ Nat.log 2 (n + 4) + 2 := by
      have hpow : 2 ^ (2 ^ (2 * A + 1)) ≤ n + 4 :=
        ((le_max_right _ _).trans hnmax).trans (by omega)
      have := Nat.le_log_of_pow_le one_lt_two hpow; omega
    exact (Nat.le_succ _).trans (Nat.le_log_of_pow_le one_lt_two h1)
  have he_le : (e : ℝ) ≤ Real.log (n : ℝ) / Real.log 2 := by
    have h1 : 2 ^ e ≤ Nat.log 2 (n + 4) + 2 := Nat.pow_log_le_self 2 (by omega)
    have h2 : n + 4 < 2 ^ (n - 2) := by
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 24 := ⟨n - 24, by omega⟩
      have hk : ∀ k, k + 28 < 2 ^ (k + 22) := fun k => by
        induction k with
        | zero => norm_num
        | succ k ih => rw [Nat.add_right_comm k 1 22, pow_succ]; omega
      simpa using hk k
    have h3 : Nat.log 2 (n + 4) < n - 2 := (Nat.log_lt_iff_lt_pow one_lt_two (by omega)).2 h2
    have h4 := Real.log_le_log (by positivity) (show (2 : ℝ) ^ e ≤
      n by exact_mod_cast (by omega : 2 ^ e ≤ n))
    rw [Real.log_pow] at h4
    exact (le_div_iff₀ hlog2).2 h4
  have htn1 : (1 : ℝ) ≤ (ilangoThreshold n : ℝ) := by
    exact_mod_cast (Nat.pow_pos (by omega) : 1 ≤ n ^ e)
  have htn_log : Real.log (ilangoThreshold n : ℝ) ≤ (Real.log (n : ℝ)) ^ 2 / Real.log 2 := by
    change Real.log (((n ^ e : ℕ) : ℝ)) ≤ _
    rw [Nat.cast_pow, Real.log_pow]
    calc (e : ℝ) * Real.log (n : ℝ)
        ≤ (Real.log (n : ℝ) / Real.log 2) * Real.log (n : ℝ) :=
          mul_le_mul_of_nonneg_right he_le (Real.log_nonneg (by norm_num; omega))
      _ = (Real.log (n : ℝ)) ^ 2 / Real.log 2 := by ring
  have hA_tn : ((n : ℝ) + 20) ^ A ≤ (ilangoThreshold n : ℝ) := by
    have : (n + 20) ^ A ≤ n ^ e :=
      ((Nat.pow_le_pow_left (by nlinarith : n + 20 ≤ n ^ 2) A).trans_eq
        (pow_mul n 2 A).symm).trans (Nat.pow_le_pow_right (by omega) hAe)
    exact_mod_cast this
  have hlhs : (C : ℝ) * (((n : ℝ) + 20) ^ A + (ilangoThreshold n : ℝ) + 1) ^ d + 16 ≤
      ((C : ℝ) + 20) * (3 * (ilangoThreshold n : ℝ)) ^ d := by
    have h3 : (1 : ℝ) ≤ (3 * (ilangoThreshold n : ℝ)) ^ d := one_le_pow₀ (by linarith)
    calc _ ≤ (C : ℝ) * (3 * (ilangoThreshold n : ℝ)) ^ d + 20 * (3 * (ilangoThreshold n : ℝ)) ^ d :=
          add_le_add (mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (by positivity) (by linarith) d) (by positivity)) (by linarith)
      _ = _ := by ring
  refine lt_of_le_of_lt hlhs ?_
  rw [← Real.log_lt_log_iff (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_pow,
    Real.log_mul (by positivity) (by positivity), Real.log_rpow two_pos]
  have hlog3 : Real.log 3 ≤ 4 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num); linarith
  have hd_mul : (d : ℝ) * Real.log (ilangoThreshold n : ℝ) ≤ (Real.log 2 / 2) * (n : ℝ) ^ δ :=
    calc (d : ℝ) * Real.log (ilangoThreshold n : ℝ)
        ≤ ((d : ℝ) + 1) * ((Real.log (n : ℝ)) ^ 2 / Real.log 2) :=
          mul_le_mul (by linarith) htn_log (Real.log_nonneg htn1) (by positivity)
      _ ≤ ((d : ℝ) + 1) * (Real.log 2 / (2 * ((d : ℝ) + 1)) * (n : ℝ) ^ δ) :=
          mul_le_mul_of_nonneg_left hln (by positivity)
      _ = (Real.log 2 / 2) * (n : ℝ) ^ δ := by
          have hne : (d : ℝ) + 1 ≠ 0 := by positivity
          field_simp
  nlinarith

/-- For every `G` of stretch `n + ⌈log₂ n⌉ + 1` with subexponential demi-hardness `2 ^ (n ^ δ)`
and universal `pps/1` `Pstar`, all sufficiently large `n` have covering shifts for any `r ≥ n - 1`
with `r ≤ n` (`CoversByXorShifts (A n) s`). -/
private theorem eventually_exists_ilangoShifts
    (G : PPolyGenerator (fun n => n + Nat.clog 2 n + 1)) {δ : ℝ} (hδ : 0 < δ)
    (hG : ∀ᶠ n : ℕ in atTop, (2 : ℝ) ^ ((n : ℝ) ^ δ) ≤ (demiHardness (G.eval n) : ℝ))
    (Pstar : PropProofSystemWithAdvice (fun _ => 1)) :
    let m (n : ℕ) := n + Nat.clog 2 n + 1
    let A (n : ℕ) : Set (BitString (m n)) :=
      {a | ∀ π : List Bool, Pstar.eval π = tauFormula 0 (G.circuit n) a →
        ilangoThreshold n < π.length}
    ∀ᶠ n : ℕ in atTop, ∀ r : ℕ, n - 1 ≤ r → 1 ≤ r →
      ∃ s : Fin r → BitString (m n), CoversByXorShifts (A n) s := by
  intro m A
  obtain ⟨Cnd, dnd, hCnd1, hdnd1, hnd⟩ :=
    exists_nondetCircuit_adviceProofLength_tauFormula Pstar
  obtain ⟨pg, hpg⟩ := G.size_poly
  obtain ⟨eg, heg1, hpeg⟩ := exists_pow_bound_poly pg
  let Aexp := 4 * eg + 4
  have hsub := eventually_ilango_size_lt_subexp hδ Cnd Aexp dnd
  filter_upwards [hG, hsub, eventually_ge_atTop 8] with n hdemi hlt hn8 r hr_ge hr1
  have hclog_n : Nat.clog 2 n ≤ n :=
    (Nat.clog_le_iff_le_pow one_lt_two).2 Nat.lt_two_pow_self.le
  have hmn_le : m n ≤ 2 * n + 1 := by dsimp [m]; omega
  set B : Set (BitString (m n)) :=
    {a | ∃ π : List Bool, Pstar.eval π = tauFormula 0 (G.circuit n) a ∧
      π.length ≤ ilangoThreshold n}
  obtain ⟨D, hDsz, hDdec, hBdisj⟩ := hnd (G.circuit n) (ilangoThreshold n)
  set sb := max 8 (Cnd * ((n + (G.circuit n).size + m n + 12) ^ 2 + ilangoThreshold n + 1) ^ dnd)
  have hsb_lt : sb < demiHardness (G.eval n) := by
    have hcs : n + (G.circuit n).size + m n + 12 ≤ (n + 20) ^ (2 * eg + 2) := by
      have h1 : (G.circuit n).size ≤ (n ^ 2) ^ eg :=
        (hpg n).trans ((hpeg (m n)).trans (Nat.pow_le_pow_left (by nlinarith) eg))
      have h2 : (G.circuit n).size ≤ (n + 20) ^ (2 * eg) :=
        (h1.trans_eq (pow_mul n 2 eg).symm).trans (Nat.pow_le_pow_left (by omega) _)
      have h3 : 1 ≤ (n + 20) ^ (2 * eg) := Nat.pow_pos (by omega)
      calc n + (G.circuit n).size + m n + 12
          ≤ (3 * n + 14) * (n + 20) ^ (2 * eg) := by nlinarith
        _ ≤ (n + 20) ^ 2 * (n + 20) ^ (2 * eg) :=
            Nat.mul_le_mul_right _ (by nlinarith)
        _ = (n + 20) ^ (2 * eg + 2) := by rw [← pow_add, add_comm 2]
    have hsq : (n + (G.circuit n).size + m n + 12) ^ 2 ≤ (n + 20) ^ Aexp :=
      (Nat.pow_le_pow_left hcs 2).trans_eq (by dsimp [Aexp]; rw [← pow_mul]; ring_nf)
    have hnat : sb ≤ Cnd * ((n + 20) ^ Aexp + ilangoThreshold n + 1) ^ dnd + 16 := by
      dsimp [sb]; apply max_le (by omega)
      exact (Nat.mul_le_mul_left Cnd
        (Nat.pow_le_pow_left (Nat.add_le_add (Nat.add_le_add hsq le_rfl) le_rfl) dnd)).trans
        (Nat.le_add_right _ 16)
    have hreal : (sb : ℝ) < (demiHardness (G.eval n) : ℝ) :=
      lt_of_le_of_lt (by exact_mod_cast hnat) (hlt.trans_le hdemi)
    exact_mod_cast hreal
  have hBdens : (B.ncard : ℝ) / (2 : ℝ) ^ m n < (1 : ℝ) / 8 := by
    have hd := density_lt_inv_of_lt_demiHardness (by dsimp [sb]; omega) hsb_lt
      (hDsz.trans (le_max_right _ _)) hDdec hBdisj
    refine hd.trans_le ?_
    rw [one_div]; exact inv_anti₀ (by norm_num) (by exact_mod_cast le_max_left 8 _)
  have hAB : A n = Bᶜ := by ext a; simp [A, B]
  have hAdens : 1 - (1 : ℝ) / 8 ≤ ((A n).ncard : ℝ) / (2 : ℝ) ^ m n := by
    have hpart : (A n).ncard + B.ncard = 2 ^ m n := by
      rw [hAB, add_comm]
      simpa [Set.ncard_univ, Nat.card_eq_fintype_card, BitString.card] using
        Set.ncard_add_ncard_compl B
    have hp' : ((A n).ncard : ℝ) = (2 : ℝ) ^ m n - (B.ncard : ℝ) := by
      have : ((A n).ncard : ℝ) + (B.ncard : ℝ) = (2 : ℝ) ^ m n := by exact_mod_cast hpart
      linarith
    rw [hp', sub_div, div_self (by positivity)]; linarith
  have hprob : ((1 : ℝ) / 8) ^ r * (2 : ℝ) ^ m n < 1 := by
    have h3r : m n < 3 * r := by omega
    have h2lt : (2 : ℝ) ^ m n < (2 : ℝ) ^ (3 * r) := pow_lt_pow_right₀ one_lt_two h3r
    have h8 : ((1 : ℝ) / 8) ^ r = ((2 : ℝ) ^ (3 * r))⁻¹ := by
      rw [pow_mul, show (2 : ℝ) ^ 3 = 8 by norm_num, one_div, inv_pow]
    rw [h8, inv_mul_lt_iff₀ (by positivity), mul_one]; exact h2lt
  exact exists_coversByXorShifts (A n) (by norm_num) hAdens hprob

/-- **Ilango's shift-covering hardness claim**: given a universal
`1`-bit-advice proof system `Pstar` p-simulating all Cook–Reckhow proof systems, whenever `G` is a
polynomial-size base circuit family and `s n` covers `{0, 1}^{m(n)}` by XOR translates of
`{a | Pstar.proofLength (τ(G_n)_a) > ilangoThreshold (seed n)}` (for all sufficiently large `n`),
every Cook–Reckhow propositional proof system `P` requires super-polynomial proofs of
`τ(ilangoCircuit (G_n) (q n) (r n) (hr n) (s n))_b`. -/
theorem ilango_claim_hard {seed m q r : ℕ → ℕ}
    (Pstar : PropProofSystemWithAdvice (fun _ => 1))
    (hPstar : ∀ Q : PropProofSystem, Pstar.PSimulates Q)
    (G : (n : ℕ) → Circuit signature (seed n) (m n))
    (hr : ∀ n, 1 ≤ r n) (hrq : ∀ᶠ n in atTop, r n ≤ 2 ^ q n)
    (hseed_pos : ∀ᶠ n in atTop, 1 ≤ seed n)
    (hpoly_params : ∃ p : Polynomial ℕ, ∀ n,
      seed n + q n + (G n).size + m n + r n ≤ p.eval (seed n))
    (hseed_tend : Tendsto seed atTop atTop)
    (s : (n : ℕ) → Fin (r n) → BitString (m n))
    (hcover : ∀ᶠ n in atTop, CoversByXorShifts
      {a : BitString (m n) | ∀ π : List Bool, Pstar.eval π = tauFormula 0 (G n) a →
        ilangoThreshold (seed n) < π.length} (s n)) :
    ∀ (P : PropProofSystem) (c : ℕ), 1 ≤ c → ∀ᶠ n : ℕ in atTop,
      ∀ b : BitString (m n),
        b ∉ Set.range ((ilangoCircuit (G n) (q n) (r n) (hr n) (s n)).eval interpretation) →
        (encFormula (tauFormula 0 (ilangoCircuit (G n) (q n) (r n) (hr n) (s n)) b)).length ^ c <
          proofLength P (tauFormula 0 (ilangoCircuit (G n) (q n) (r n) (hr n) (s n)) b) := by
  obtain ⟨Cred, hCred1, hred⟩ := exists_frege_reduce_ilangoCircuit
  obtain ⟨pp, hpp⟩ := hpoly_params
  obtain ⟨ep, hep1, hpep⟩ := exists_pow_bound_poly pp
  intro P c hc
  let P' := closeUnderSubstFrege P
  obtain ⟨f, hf_poly, hf_eq⟩ := hPstar P'
  obtain ⟨cf, df, hf_bd⟩ := exists_output_length_le hf_poly
  let E_all : ℕ := ((4 * ep + 4) * (2 * c + 6) + 2 * c + 8) * df + cf + 8
  have hthr := hseed_tend.eventually (eventually_pow_le_ilangoThreshold E_all)
  have hsge := hseed_tend.eventually (eventually_ge_atTop (max 4 (Cred + cf + 200)))
  filter_upwards [hrq, hseed_pos, hcover, hthr, hsge] with n hrqn hs1 hcov htn hsbig b hb
  by_contra hle
  let sd := seed n
  let gn := ilangoCircuit (G n) (q n) (r n) (hr n) (s n)
  change b ∉ Set.range (gn.eval interpretation) at hb
  change ¬(encFormula (tauFormula 0 gn b)).length ^ c < proofLength P (tauFormula 0 gn b) at hle
  have hsd4 : 4 ≤ sd := (le_max_left _ _).trans hsbig
  have hsdC : Cred + cf + 200 ≤ sd := (le_max_right _ _).trans hsbig
  have htaut : tauFormula 0 gn b ∈ TAUT := (tauFormula_mem_taut_iff 0 gn b).2 hb
  obtain ⟨π, hπ, hπlen⟩ := (proofLength_le_iff P htaut).1 (le_of_not_gt hle)
  obtain ⟨j₀, a, haA, rfl⟩ := hcov b
  obtain ⟨pairs, steps, hrun, hps_len⟩ :=
    hred hs1 (G n) (q n) (r n) (hr n) hrqn (s n) j₀ a
  have hren0 : renameAtoms (· - 0) (P π) = tauFormula 0 gn (bitXor a (s n j₀)) := by
    rw [hπ]
    exact toPostfix_injective (by
      rw [toPostfix_renameAtoms]
      exact (List.map_congr_left fun t _ => by cases t <;> rfl).trans (List.map_id _))
  obtain ⟨π', hπ', hπ'len⟩ :=
    closeUnderSubstFrege_derive P π 0 pairs steps (by rwa [hren0])
  have hPstar_eq : Pstar.eval (f π') = tauFormula 0 (G n) a := (hf_eq π').trans hπ'
  -- Bound `(f π').length ≤ sd ^ E_all ≤ ilangoThreshold sd`, contradicting `haA`!
  have hpar : sd + q n + (G n).size + m n + r n ≤ sd ^ (2 * ep) := by
    have hsq : sd + 2 ≤ sd ^ 2 := by nlinarith only [hsd4]
    exact (hpp n).trans ((hpep sd).trans
      ((Nat.pow_le_pow_left hsq ep).trans_eq (pow_mul sd 2 ep).symm))
  have hM : sd + q n + gn.size + m n + 20 ≤ sd ^ (4 * ep + 4) := by
    set X := sd ^ (2 * ep)
    have hX : 16 ≤ X :=
      (show 16 = 4 ^ 2 by norm_num) ▸
        (Nat.pow_le_pow_left hsd4 2).trans (Nat.pow_le_pow_right (by omega) (by omega))
    have hX2 : X ≤ X ^ 2 := Nat.le_self_pow (by decide) X
    dsimp only [gn]; rw [size_ilangoCircuit]
    have hrq_le : r n * q n ≤ X ^ 2 :=
      (Nat.mul_le_mul (by omega : r n ≤ X) (by omega : q n ≤ X)).trans_eq (sq X).symm
    have hmr_le : m n * (r n + 6) ≤ X ^ 2 + 6 * X :=
      (Nat.mul_le_mul (by omega : m n ≤ X) (by omega : r n + 6 ≤ X + 6)).trans_eq (by ring)
    have hsd16 : 16 ≤ sd ^ 4 :=
      (show 16 ≤ 4 ^ 4 by decide).trans (Nat.pow_le_pow_left hsd4 4)
    calc sd + q n + ((G n).size + (2 + q n + r n * q n + m n * (r n + 6))) + m n + 20
        ≤ 16 * X ^ 2 := by omega
      _ ≤ sd ^ 4 * X ^ 2 := Nat.mul_le_mul_right _ hsd16
      _ = sd ^ (4 * ep + 4) := by dsimp [X]; rw [← pow_mul, ← pow_add]; ring_nf
  have hτ_le : (encFormula (tauFormula 0 gn (bitXor a (s n j₀)))).length ≤
      sd ^ (2 * (4 * ep + 4) + 2) := by
    have h0 := length_encFormula_tauFormula_zero_le gn (bitXor a (s n j₀))
    have h20 : 20 ≤ sd ^ 2 := by nlinarith only [hsdC]
    have hM12 : sd + q n + gn.size + m n + 12 ≤ sd ^ (4 * ep + 4) := by omega
    calc _ ≤ 20 * (sd ^ (4 * ep + 4)) ^ 2 :=
          h0.trans (Nat.mul_le_mul_left 20 (Nat.pow_le_pow_left hM12 2))
      _ ≤ sd ^ 2 * (sd ^ (4 * ep + 4)) ^ 2 := Nat.mul_le_mul_right _ h20
      _ = sd ^ (2 * (4 * ep + 4) + 2) := by rw [← pow_mul, ← pow_add]; ring_nf
  have hπ_sd : π.length ≤ sd ^ ((2 * (4 * ep + 4) + 2) * c) :=
    hπlen.trans ((Nat.pow_le_pow_left hτ_le c).trans_eq (pow_mul _ _ _).symm)
  have hps_sd : (encList (encPair encNat encFormula) pairs).length +
      (encList encEFStep steps).length ≤ sd ^ (6 * (4 * ep + 4) + 1) :=
    calc _ ≤ Cred * (sd ^ (4 * ep + 4)) ^ 6 :=
          hps_len.trans (Nat.mul_le_mul_left Cred (Nat.pow_le_pow_left hM 6))
      _ ≤ sd * sd ^ (6 * (4 * ep + 4)) := by
          rw [← pow_mul, mul_comm _ 6]; exact Nat.mul_le_mul_right _ (by omega)
      _ = sd ^ (6 * (4 * ep + 4) + 1) := by rw [← pow_succ']
  let K1 := max ((2 * (4 * ep + 4) + 2) * c) (6 * (4 * ep + 4) + 1)
  have hπ'_sd : π'.length + 1 ≤ sd ^ (K1 + 2) := by
    have h0 := length_encNat_le_self 0
    have h1 : π.length ≤ sd ^ K1 := hπ_sd.trans (Nat.pow_le_pow_right (by omega) (le_max_left _ _))
    have h2 : (encList (encPair encNat encFormula) pairs).length +
        (encList encEFStep steps).length ≤ sd ^ K1 :=
      hps_sd.trans (Nat.pow_le_pow_right (by omega) (le_max_right _ _))
    have h3 : 1 ≤ sd ^ K1 := Nat.pow_pos (by omega)
    calc π'.length + 1 ≤ 60 * sd ^ K1 := by omega
      _ ≤ sd ^ 2 * sd ^ K1 := Nat.mul_le_mul_right _ (by nlinarith only [hsdC])
      _ = sd ^ (K1 + 2) := by rw [← pow_add, add_comm]
  have hf_sd : (f π').length ≤ ilangoThreshold sd := by
    have h1 : (f π').length ≤ cf * (π'.length + 1) ^ df :=
      (hf_bd π').trans_eq (by simp [encBits])
    have h2 : (f π').length ≤ sd ^ ((K1 + 2) * df + 1) :=
      calc (f π').length ≤ sd * (sd ^ (K1 + 2)) ^ df :=
            h1.trans (Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left hπ'_sd df))
        _ = sd ^ ((K1 + 2) * df + 1) := by rw [← pow_mul, ← pow_succ']
    exact h2.trans ((Nat.pow_le_pow_right (by omega) (by
      have hK1_le : K1 ≤ (4 * ep + 4) * (2 * c + 6) + 2 * c + 1 :=
        max_le (by nlinarith only [hep1, hc]) (by nlinarith only [hep1, hc])
      dsimp only [E_all]; nlinarith only [hK1_le])).trans htn)
  exact not_lt_of_ge hf_sd (haA (f π') hPstar_eq)

/-- **Hard one-bit-stretching circuit family (`n + ⌈log₂ n⌉ → n + ⌈log₂ n⌉ + 1`)**: assuming
`DemiBitConjecture`, there exist a polynomial `p` and a family of De Morgan circuits
`g n : Circuit signature (n + ⌈log₂ n⌉) (n + ⌈log₂ n⌉ + 1)` of size at most `p(n)` such that for
every Cook–Reckhow propositional proof system `P` and every `c ≥ 1`, for all sufficiently large `n`
and every `b ∉ Set.range (g n)`, every `P`-proof of `τ(g_n)_b` has length strictly greater than
`|τ(g_n)_b| ^ c`. -/
theorem exists_hard_oneBitStretch_of_demiBit (hRud : DemiBitConjecture) :
    ∃ (p : Polynomial ℕ)
      (g : (n : ℕ) → Circuit signature (n + Nat.clog 2 n) (n + Nat.clog 2 n + 1)),
      (∀ n, (g n).size ≤ p.eval (n + Nat.clog 2 n + 1)) ∧
      ∀ (P : PropProofSystem) (c : ℕ), 1 ≤ c → ∀ᶠ n : ℕ in atTop,
        ∀ b : BitString (n + Nat.clog 2 n + 1),
          b ∉ Set.range ((g n).eval interpretation) →
          (encFormula (tauFormula 0 (g n) b)).length ^ c <
            proofLength P (tauFormula 0 (g n) b) := by
  classical
  obtain ⟨G, δ, hδ, hG⟩ := exists_stretched_demiBit_clog hRud
  obtain ⟨Pstar, hPstar⟩ := exists_pps_one_bit_advice_pSimulates_all
  have hex := eventually_exists_ilangoShifts G hδ hG Pstar
  let m (n : ℕ) := n + Nat.clog 2 n + 1
  let r (n : ℕ) := max n 1
  let A (n : ℕ) : Set (BitString (m n)) :=
    {a | ∀ π : List Bool, Pstar.eval π = tauFormula 0 (G.circuit n) a →
      ilangoThreshold n < π.length}
  let s (n : ℕ) : Fin (r n) → BitString (m n) :=
    if h : ∃ sn : Fin (r n) → BitString (m n), CoversByXorShifts (A n) sn then
      Classical.choose h
    else fun _ _ => false
  let g (n : ℕ) : Circuit signature (n + Nat.clog 2 n) (m n) :=
    ilangoCircuit (G.circuit n) (Nat.clog 2 n) (r n) (le_max_right n 1) (s n)
  obtain ⟨pg, hpg⟩ := G.size_poly
  let p : Polynomial ℕ :=
    pg + Polynomial.C 2 + Polynomial.X + Polynomial.X ^ 2 +
      Polynomial.X * (Polynomial.X + Polynomial.C 6)
  refine ⟨p, g, fun n => ?_, ?_⟩
  · have hrm : r n ≤ m n := by dsimp [r, m]; omega
    have hqm : Nat.clog 2 n ≤ m n := by dsimp [m]; omega
    simp only [g, size_ilangoCircuit, p, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X, sq]
    have h1 := hpg n
    have h2 : r n * Nat.clog 2 n ≤ m n * m n := Nat.mul_le_mul hrm hqm
    have h3 : m n * (r n + 6) ≤ m n * (m n + 6) := Nat.mul_le_mul_left _ (by omega)
    dsimp only [m] at *
    omega
  · refine ilango_claim_hard (seed := id) (m := m) (q := Nat.clog 2) (r := r)
      Pstar hPstar G.circuit (fun n => le_max_right n 1) ?_ (eventually_ge_atTop 1) ?_
      tendsto_id s ?_
    · filter_upwards [eventually_ge_atTop 1] with n hn1
      simpa [r, max_eq_left hn1] using Nat.le_pow_clog one_lt_two n
    · refine ⟨pg.comp (Polynomial.C 2 * Polynomial.X + Polynomial.C 2) +
        Polynomial.C 6 * Polynomial.X + Polynomial.C 4, fun n => ?_⟩
      have hcl : Nat.clog 2 n ≤ n :=
        (Nat.clog_le_iff_le_pow one_lt_two).2 Nat.lt_two_pow_self.le
      have hmn : m n ≤ 2 * n + 2 := by dsimp [m]; omega
      have h1 : (G.circuit n).size ≤ pg.eval (2 * n + 2) := (hpg n).trans (pg.eval_mono hmn)
      simp only [id_eq, Polynomial.eval_add, Polynomial.eval_comp, Polynomial.eval_mul,
        Polynomial.eval_C, Polynomial.eval_X]
      dsimp [r, m] at *; omega
    · filter_upwards [hex, eventually_ge_atTop 1] with n hn hn1
      have hexn : ∃ sn : Fin (r n) → BitString (m n), CoversByXorShifts (A n) sn :=
        hn (r n) (by dsimp [r]; omega) (le_max_right n 1)
      dsimp only [s]; rw [dite_eq_left hexn]; exact Classical.choose_spec hexn

/-- Largest `n ≤ K` satisfying `n + Nat.clog 2 n ≤ K`. -/
private def ilangoBaseSeed (K : ℕ) : ℕ :=
  ((List.range (K + 1)).filter fun n => decide (n + Nat.clog 2 n ≤ K)).getLastD 0

private theorem ilangoBaseSeed_spec {K : ℕ} (hK : 2 ≤ K) :
    let n := ilangoBaseSeed K
    1 ≤ n ∧
    ((K = n + Nat.clog 2 n) ∨
     (K = n + Nat.clog 2 n + 1 ∧ Nat.clog 2 (n + 1) = Nat.clog 2 n + 1)) := by
  intro n
  have hmono : StrictMono (fun x : ℕ => x + Nat.clog 2 x) := fun a b hab =>
    Nat.add_lt_add_of_lt_of_le hab (Nat.clog_mono_right 2 hab.le)
  let flt := (List.range (K + 1)).filter fun x => decide (x + Nat.clog 2 x ≤ K)
  have hlast_eq : ∀ (xs : List ℕ) (d : ℕ) (h : xs ≠ []), xs.getLastD d = xs.getLast h := by
    intro xs; induction xs with
    | nil => intro _ h; exact (h rfl).elim
    | cons x xs ih =>
      intro d _; cases xs with
      | nil => rfl
      | cons y ys => exact ih x (List.cons_ne_nil y ys)
  have h1_mem : 1 ∈ flt := by simp [flt]; omega
  have hne : flt ≠ [] := List.ne_nil_of_mem h1_mem
  have hn_mem : n ∈ flt := by
    change flt.getLastD 0 ∈ flt
    rw [hlast_eq flt 0 hne]; exact List.getLast_mem hne
  have hn_le : n + Nat.clog 2 n ≤ K := by
    simpa [flt] using (List.mem_filter.1 hn_mem).2
  have hmax : ∀ x, x + Nat.clog 2 x ≤ K → x ≤ n := by
    intro x hx
    have hx_mem : x ∈ flt := List.mem_filter.2 ⟨List.mem_range.2 (by omega), by simp [hx]⟩
    have hpw : flt.Pairwise (· < ·) := List.pairwise_lt_range.filter _
    rw [List.pairwise_iff_getElem] at hpw
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hx_mem
    have hlast : n = flt[flt.length - 1]'(Nat.sub_lt (List.length_pos_of_ne_nil hne) one_pos) := by
      change flt.getLastD 0 = _
      rw [hlast_eq flt 0 hne, List.getLast_eq_getElem]
    rw [hlast]
    by_cases hie : i = flt.length - 1
    · subst hie; exact le_rfl
    · exact (hpw i (flt.length - 1) hi _ (by omega)).le
  have hn1 : 1 ≤ n := hmax 1 (by simp; omega)
  have hgt : K < (n + 1) + Nat.clog 2 (n + 1) := by
    by_contra hle; have := hmax (n + 1) (le_of_not_gt hle); omega
  have hclog_step : Nat.clog 2 (n + 1) ≤ Nat.clog 2 n + 1 := by
    rw [Nat.clog_le_iff_le_pow one_lt_two, pow_succ]
    have := Nat.le_pow_clog one_lt_two n; omega
  have hclog_ge : Nat.clog 2 n ≤ Nat.clog 2 (n + 1) := Nat.clog_mono_right 2 (Nat.le_succ n)
  exact ⟨hn1, by omega⟩

/-- **Ilango's Theorem (`P/poly` proof complexity generator from demi-bits)**:
assuming Rudich's `DemiBitConjecture`, there exist a monotone stretch function `m : ℕ → ℕ` (with
`m(K) ∈ {K + 1, K + 2}` for every input length `K`) and a `P/poly` generator `g : PPolyGenerator m`
that is simultaneously hard for every Cook–Reckhow propositional proof system `P`. In particular,
`DemiBitConjecture → HardGeneratorConjecture`. -/
theorem exists_hard_ppolyGenerator_of_demiBit (hRud : DemiBitConjecture) :
    ∃ (m : ℕ → ℕ) (g : PPolyGenerator m),
      Monotone m ∧ (∀ K, m K = K + 1 ∨ m K = K + 2) ∧
      ∀ P : PropProofSystem, IsHardFor g P := by
  classical
  obtain ⟨G, δ, hδ, hG⟩ := exists_stretched_demiBit_clog hRud
  obtain ⟨Pstar, hPstar⟩ := exists_pps_one_bit_advice_pSimulates_all
  have hex := eventually_exists_ilangoShifts G hδ hG Pstar
  let mG (sd : ℕ) := sd + Nat.clog 2 sd + 1
  let nBase := ilangoBaseSeed
  let exact (K : ℕ) : Bool := decide (K = nBase K + Nat.clog 2 (nBase K))
  let seed (K : ℕ) : ℕ := if K ≤ 1 then K else if exact K then nBase K else nBase K + 1
  let q (K : ℕ) : ℕ := if K ≤ 1 then 0 else Nat.clog 2 (nBase K)
  let r (K : ℕ) : ℕ := max (nBase K) 1
  have hin_eq (K : ℕ) : seed K + q K = K := by
    by_cases hK : K ≤ 1
    · simp only [seed, q, hK, ↓reduceIte, add_zero]
    · obtain ⟨_, hcases⟩ := ilangoBaseSeed_spec (show 2 ≤ K by omega)
      simp only [seed, q, hK, ↓reduceIte, exact]
      rcases hcases with he | ⟨he, _⟩
      · dsimp only [nBase] at *; rw [ite_eq_left (decide_eq_true he)]; exact he.symm
      · have hne : K ≠ nBase K + Nat.clog 2 (nBase K) := by dsimp [nBase]; omega
        simp only [hne, decide_false, Bool.false_eq_true, ↓reduceIte]; dsimp [nBase]; omega
  let m (K : ℕ) : ℕ := if K ≤ 1 then K + 1 else mG (seed K)
  have hm_vals (K : ℕ) : m K = K + 1 ∨ m K = K + 2 := by
    by_cases hK : K ≤ 1
    · exact Or.inl (by simp only [m, hK, ↓reduceIte])
    · obtain ⟨_, hcases⟩ := ilangoBaseSeed_spec (show 2 ≤ K by omega)
      simp only [m, hK, ↓reduceIte, seed, exact, mG]
      rcases hcases with he | ⟨he, hcl⟩
      · left; dsimp only [nBase] at *; rw [ite_eq_left (decide_eq_true he), ← he]
      · right
        have hne : K ≠ nBase K + Nat.clog 2 (nBase K) := by dsimp [nBase]; omega
        simp only [hne, decide_false, Bool.false_eq_true, ↓reduceIte]
        dsimp [nBase] at *; omega
  have hm_mono : Monotone m := monotone_nat_of_le_succ fun K => by
    rcases hm_vals K with h1 | h1 <;> rcases hm_vals (K + 1) with h2 | h2 <;> omega
  let A (sd : ℕ) : Set (BitString (mG sd)) :=
    {a | ∀ π : List Bool, Pstar.eval π = tauFormula 0 (G.circuit sd) a →
      ilangoThreshold sd < π.length}
  let s (K : ℕ) : Fin (r K) → BitString (mG (seed K)) :=
    if h : ∃ sk : Fin (r K) → BitString (mG (seed K)), CoversByXorShifts (A (seed K)) sk then
      Classical.choose h
    else fun _ _ => false
  let castIn {a b out : ℕ} (h : a = b) (c : Circuit signature a out) : Circuit signature b out :=
    h ▸ c
  let circ (K : ℕ) : Circuit signature K (m K) :=
    if hK : K ≤ 1 then
      { size := 1
        program := Program.empty.gate ⟨.const false, Fin.elim0⟩
        outputs := fun _ => .gate 0 }
    else
      circuitCastOut (ite_eq_right hK).symm
        (castIn (hin_eq K) (ilangoCircuit (G.circuit (seed K)) (q K) (r K)
          (le_max_right _ 1) (s K)))
  obtain ⟨pg, hpg⟩ := G.size_poly
  let p : Polynomial ℕ :=
    pg + Polynomial.C 3 + Polynomial.X + Polynomial.X ^ 2 +
      Polynomial.X * (Polynomial.X + Polynomial.C 6)
  have hsz (K : ℕ) : (circ K).size ≤ p.eval (m K) := by
    by_cases hK : K ≤ 1
    · simp only [circ, hK, ↓reduceDIte, p, Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_C, Polynomial.eval_X, sq]; omega
    · have hcast_sz : ∀ {a b out : ℕ} (h : a = b) (c : Circuit signature a out),
          (castIn h c).size = c.size := by rintro a _ _ rfl _; rfl
      simp only [circ, hK, ↓reduceDIte, size_circuitCastOut, hcast_sz, size_ilangoCircuit,
        m, ↓reduceIte, p, Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_C, Polynomial.eval_X, sq]
      have h1 := hpg (seed K)
      have hrm : r K ≤ mG (seed K) := by
        obtain ⟨hn1, _⟩ := ilangoBaseSeed_spec (show 2 ≤ K by omega)
        simp only [r, mG, seed, hK, ↓reduceIte, exact]
        split_ifs <;> (dsimp [nBase] at *; omega)
      have hqm : q K ≤ mG (seed K) := by
        have hle : nBase K ≤ seed K := by
          simp only [seed, hK, ↓reduceIte]; split_ifs <;> omega
        have hcl : q K ≤ Nat.clog 2 (seed K) := by
          simp only [q, hK, ↓reduceIte]; exact Nat.clog_mono_right 2 hle
        dsimp [mG]; omega
      have h2 := Nat.mul_le_mul hrm hqm
      have h3 := Nat.mul_le_mul_left (mG (seed K)) (show r K + 6 ≤ mG (seed K) + 6 by omega)
      dsimp only [mG] at *; omega
  let gen : PPolyGenerator m :=
    ⟨circ, fun K => by rcases hm_vals K with h | h <;> omega, p, hsz⟩
  have hseed_tend : Tendsto seed atTop atTop := by
    rw [tendsto_atTop_atTop]; intro B
    refine ⟨2 * B + 4, fun K hK => ?_⟩
    have hK2 : ¬(K ≤ 1) := by omega
    obtain ⟨hn1, hc⟩ := ilangoBaseSeed_spec (show 2 ≤ K by omega)
    have hcl : Nat.clog 2 (nBase K) ≤ nBase K :=
      (Nat.clog_le_iff_le_pow one_lt_two).2 Nat.lt_two_pow_self.le
    have hnb : B ≤ nBase K := by dsimp [nBase] at *; omega
    simp only [seed, hK2, ↓reduceIte]; split_ifs <;> omega
  have hraw := ilango_claim_hard (seed := seed) (m := fun K => mG (seed K)) (q := q) (r := r)
    Pstar hPstar (fun K => G.circuit (seed K)) (fun K => le_max_right _ 1)
    (by filter_upwards [eventually_ge_atTop 2] with K hK
        obtain ⟨hn1, _⟩ := ilangoBaseSeed_spec hK
        have hK1 : ¬(K ≤ 1) := by omega
        simpa only [q, hK1, ↓reduceIte, r, nBase, max_eq_left hn1] using
          Nat.le_pow_clog one_lt_two (ilangoBaseSeed K))
    (hseed_tend.eventually (eventually_ge_atTop 1))
    (⟨pg.comp (Polynomial.C 2 * Polynomial.X + Polynomial.C 2) +
        Polynomial.C 6 * Polynomial.X + Polynomial.C 4, fun K => by
      have hcl : Nat.clog 2 (seed K) ≤ seed K :=
        (Nat.clog_le_iff_le_pow one_lt_two).2 Nat.lt_two_pow_self.le
      have h1 : (G.circuit (seed K)).size ≤ pg.eval (2 * seed K + 2) :=
        (hpg (seed K)).trans (pg.eval_mono (by omega))
      have hqr : q K ≤ seed K ∧ r K ≤ seed K + 1 := by
        by_cases hK : K ≤ 1
        · have hnb1 : nBase K ≤ 1 := by
            rcases (show K = 0 ∨ K = 1 by omega) with rfl | rfl <;> decide
          simp only [q, r, seed, hK, ↓reduceIte]; omega
        · obtain ⟨hn1, _⟩ := ilangoBaseSeed_spec (show 2 ≤ K by omega)
          have hclb : Nat.clog 2 (nBase K) ≤ nBase K :=
            (Nat.clog_le_iff_le_pow one_lt_two).2 Nat.lt_two_pow_self.le
          simp only [q, r, seed, hK, ↓reduceIte]; split_ifs <;> (dsimp [nBase] at *; omega)
      simp only [Polynomial.eval_add, Polynomial.eval_comp, Polynomial.eval_mul,
        Polynomial.eval_C, Polynomial.eval_X]
      dsimp [mG] at *; omega⟩)
    hseed_tend s
    (by filter_upwards [hseed_tend.eventually hex, eventually_ge_atTop 2] with K hK hK2
        obtain ⟨hn1, _⟩ := ilangoBaseSeed_spec hK2
        have hsr : seed K - 1 ≤ r K := by
          simp only [seed, show ¬(K ≤ 1) by omega, ↓reduceIte, r]
          split_ifs <;> (dsimp [nBase] at *; omega)
        have hexK := hK (r K) hsr (le_max_right _ 1)
        dsimp only [s]; rw [dite_eq_left hexK]; exact Classical.choose_spec hexK)
  refine ⟨m, gen, hm_mono, hm_vals, fun P => (isHardFor_iff_eventually gen P).2 fun c hc => ?_⟩
  filter_upwards [hraw P c hc, eventually_ge_atTop 2] with K hK hK2 b hb
  have hKlt : ¬(K ≤ 1) := by omega
  have hcast_eq : ∀ {a₁ a₂ m₁ m₂ : ℕ} (ha : a₁ = a₂) (hm : m₁ = m₂)
      (c₀ : Circuit signature a₁ m₁) (b₀ : BitString m₂),
      b₀ ∉ Set.range ((circuitCastOut hm (castIn ha c₀)).eval interpretation) →
      let b₁ : BitString m₁ := fun i => b₀ (i.cast hm)
      b₁ ∉ Set.range (c₀.eval interpretation) ∧
      tauFormula 0 (circuitCastOut hm (castIn ha c₀)) b₀ = tauFormula 0 c₀ b₁ := by
    rintro a₁ _ m₁ _ rfl rfl c₀ b₀ hb₀; exact ⟨hb₀, rfl⟩
  have hcirc : gen.circuit K = circuitCastOut (ite_eq_right hKlt).symm
      (castIn (hin_eq K) (ilangoCircuit (G.circuit (seed K)) (q K) (r K)
        (le_max_right _ 1) (s K))) := dite_eq_right hKlt
  obtain ⟨hb₁, hτ_eq⟩ := hcast_eq (hin_eq K) (ite_eq_right hKlt).symm _ b (by
    change b ∉ Set.range ((gen.circuit K).eval interpretation) at hb; rwa [hcirc] at hb)
  rw [hcirc, hτ_eq]
  exact hK _ hb₁

/-- **Corollary:** Rudich's `DemiBitConjecture` implies `HardGeneratorConjecture`. -/
theorem hardGeneratorConjecture_of_demiBit (hRud : DemiBitConjecture) :
    HardGeneratorConjecture :=
  let ⟨m, g, _, _, hg⟩ := exists_hard_ppolyGenerator_of_demiBit hRud
  ⟨m, g, hg⟩

end CslibFrontier.ProofComplexity
