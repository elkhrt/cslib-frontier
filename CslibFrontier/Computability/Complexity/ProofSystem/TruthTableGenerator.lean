module

public import CslibFrontier.Computability.Complexity.ProofSystem.TauFormula
public import CslibFrontier.Computability.Complexity.ProofSystem.UniversalEval

/-!
# The Truth-Table Proof Complexity Generator

This module defines the canonical truth-table proof complexity generator `truthTableCircuit k s hk`
(`tt_{s, k}`), which maps a `univDescLen k 1 s`-bit description of a `k`-input, size-`≤ s` De Morgan
circuit to the `2 ^ k`-bit truth table of the Boolean function it computes, and establishes the
circuit-size lower-bound semantics of the range-avoidance formula `τ(tt_{s, k})_b`.

## Main definitions

* `CslibFrontier.ProofComplexity.indexToBitString`: `k`-bit input string indexed by `t < 2 ^ k`.
* `CslibFrontier.ProofComplexity.truthTableCircuit`: truth-table generator circuit `tt_{s, k}`
  mapping a `univDescLen k 1 s`-bit circuit description to its `2 ^ k`-bit truth table.

## Main results

* `CslibFrontier.ProofComplexity.size_truthTableCircuit`: exact gate count of `truthTableCircuit`.
* `CslibFrontier.ProofComplexity.eval_truthTableCircuit` and
  `CslibFrontier.ProofComplexity.eval_truthTableCircuit_encodeCircuit`: evaluation semantics of
  `tt_{s, k}` via `univEvalCircuit` and `encodeCircuit`.
* `CslibFrontier.ProofComplexity.size_gt_of_tauFormula_truthTableCircuit_mem_taut`: tautologicity of
  `τ(tt_{s, k})_b` certifies circuit-size lower bound `c.size > s` for every De Morgan circuit `c`
  computing the Boolean function with truth table `b`.


-/

public section

namespace CslibFrontier.ProofComplexity

open Cslib Cslib.Circuits Cslib.Circuits.Boolean

/-! ### The truth-table proof complexity generator `tt_{s, k}` -/

/-- Input bitstring indexed by `t < 2 ^ k`: `i ↦ t.testBit i.val`. -/
@[expose]
def indexToBitString (k t : ℕ) : BitString k := fun i => t.testBit i.val

/-- Relabel the input and gate indices of a `RawGate` occurring inside copy `t` of
`univRawGates k 1 s` when fixing its `k` data inputs to constant wires `falseW` / `trueW`. -/
private def shiftCopyGate (ℓ k falseW trueW copyBase : ℕ) (t : ℕ) : RawGate → RawGate :=
  let tr (w : ℕ) : ℕ :=
    if w < ℓ then w
    else if w < ℓ + k then if t.testBit (w - ℓ) then trueW else falseW
    else copyBase + (w - (ℓ + k))
  fun
    | .const bv => .const bv
    | .not w => .not (tr w)
    | .and w₁ w₂ => .and (tr w₁) (tr w₂)
    | .or w₁ w₂ => .or (tr w₁) (tr w₂)

/-- `RawGate` list for the truth-table generator `tt_{s, k}` evaluating `univEvalCircuit k 1 s` in
parallel at all `2 ^ k` inputs `indexToBitString k t` (`t < 2 ^ k`). -/
private def truthTableGates (k s : ℕ) : List RawGate :=
  let ℓ := univDescLen k 1 s
  let ug := univRawGates k 1 s
  RawGate.const false :: RawGate.const true ::
    ((List.range (2 ^ k)).map fun t =>
      ug.map (shiftCopyGate ℓ k ℓ (ℓ + 1) (ℓ + 2 + t * ug.length) t)).flatten

/-- Output wire index list of length `2 ^ k` for `truthTableCircuit k s`. -/
private def truthTableOuts (k s : ℕ) : List ℕ :=
  let ℓ := univDescLen k 1 s
  let ug := univRawGates k 1 s
  let uout := (univRawOuts k 1 s).getD 0 (ℓ + k)
  (List.range (2 ^ k)).map fun t => ℓ + 2 + t * ug.length + (uout - (ℓ + k))

/-- **Truth-table proof complexity generator circuit `tt_{s, k}`**: maps a `univDescLen k 1 s`-bit
description of a `k`-input, size-`≤ s` De Morgan circuit to the `2 ^ k`-bit truth table
`(C(indexToBitString k t))_{t < 2 ^ k}` of the Boolean function it computes. -/
def truthTableCircuit (k s : ℕ) (hk : 1 ≤ k) : Circuit signature (univDescLen k 1 s) (2 ^ k) :=
  let raw := buildRawCircuit (univDescLen k 1 s) (univDescLen_pos_of_pos hk le_rfl)
    (truthTableGates k s) (truthTableOuts k s)
  { size := raw.size
    program := raw.program
    outputs := fun j => raw.outputs (j.cast (by simp [truthTableOuts])) }

/-- Exact gate size of `truthTableCircuit k s hk`:
`2 + 2 ^ k * (1 + s * (4 * (k + s) + 20) + 2 * (k + s))`. -/
theorem size_truthTableCircuit (k s : ℕ) (hk : 1 ≤ k) :
    (truthTableCircuit k s hk).size =
      2 + 2 ^ k * (1 + s * univStepGateCount k s + 2 * (k + s)) := by
  change (truthTableGates k s).length = _
  have hfl : ∀ n (L : ℕ) (f : ℕ → List RawGate), (∀ t, (f t).length = L) →
      (((List.range n).map f).flatten).length = n * L := by
    intro n L f hf; induction n with
    | zero => simp
    | succ n ih => rw [List.range_succ, List.map_append, List.flatten_append,
        List.length_append, ih]; simp [hf, Nat.succ_mul]
  simp only [truthTableGates, List.length_cons]
  rw [hfl (2 ^ k) (univRawGates k 1 s).length _ (fun _ => by simp)]
  simp only [length_univRawGates, one_mul]; omega

/-- Evaluating `truthTableCircuit k s hk` on a description `v` at coordinate `t : Fin (2 ^ k)`
equals evaluating `univEvalCircuit k 1 s hk` on `(v, indexToBitString k t.val)`. -/
theorem eval_truthTableCircuit {k s : ℕ} (hk : 1 ≤ k)
    (v : BitString (univDescLen k 1 s)) (t : Fin (2 ^ k)) :
    (truthTableCircuit k s hk).eval interpretation v t =
      (univEvalCircuit k 1 s hk).eval interpretation
        (Fin.append v (indexToBitString k t.val)) 0 := by
  let ℓ := univDescLen k 1 s
  let ug := univRawGates k 1 s
  let uout := (univRawOuts k 1 s)[0]'(by simp)
  have huout_ge : ℓ + k ≤ uout := by
    have h0 := getElem_univRawOuts_of_pos (m := 1) (j := 0) (k := k) (S := s) (by omega) zero_lt_one
    dsimp only [uout, ℓ]; rw [h0]; omega
  have huout_lt : uout < (ℓ + k) + ug.length :=
    univRawOuts_lt k 1 s ⟨0, by simp⟩
  have hcopy : ∀ (gs : List RawGate) (t0 : ℕ) (vs us : List Bool) (cb : ℕ),
      ℓ + 2 ≤ cb → vs.length = cb + us.length - (ℓ + k) → ℓ + k ≤ us.length →
      (∀ (i : ℕ) (hi : i < ℓ), vs.getD i false = v ⟨i, hi⟩ ∧ us.getD i false = v ⟨i, hi⟩) →
      vs.getD ℓ false = false → vs.getD (ℓ + 1) false = true →
      (∀ i < k, us.getD (ℓ + i) false = t0.testBit i) →
      (∀ d < us.length - (ℓ + k), vs.getD (cb + d) false = us.getD (ℓ + k + d) false) →
      let vs' := evalRawGates vs (gs.map (shiftCopyGate ℓ k ℓ (ℓ + 1) cb t0))
      let us' := evalRawGates us gs
      ∀ d < us'.length - (ℓ + k), vs'.getD (cb + d) false = us'.getD (ℓ + k + d) false := by
    intro gs; induction gs with
    | nil => intro _ _ _ _ _ _ _ _ _ _ _ h; exact h
    | cons rg rest ih =>
      intro t0 vs us cb hcb hvlen hulen hdesc hvf hvt hin hgd
      let tr (w : ℕ) : ℕ :=
        if w < ℓ then w
        else if w < ℓ + k then if t0.testBit (w - ℓ) then ℓ + 1 else ℓ
        else cb + (w - (ℓ + k))
      have htr (w : ℕ) : (tr w < vs.length ↔ w < us.length) ∧
          (w < us.length → vs.getD (tr w) false = us.getD w false) := by
        dsimp only [tr]
        by_cases h1 : w < ℓ
        · simp only [h1, ↓reduceIte]
          exact ⟨by omega, fun _ => (hdesc w h1).1.trans (hdesc w h1).2.symm⟩
        · by_cases h2 : w < ℓ + k
          · simp only [h1, h2, ↓reduceIte]
            refine ⟨by split_ifs <;> omega, fun _ => ?_⟩
            have hi := hin (w - ℓ) (by omega)
            rw [show ℓ + (w - ℓ) = w by omega] at hi
            rw [hi]; cases t0.testBit (w - ℓ) <;> [exact hvf; exact hvt]
          · simp only [h1, h2, ↓reduceIte]
            refine ⟨by omega, fun hw => ?_⟩
            simpa [show ℓ + k + (w - (ℓ + k)) = w by omega] using hgd (w - (ℓ + k)) (by omega)
      have hstep : evalRawGate vs (shiftCopyGate ℓ k ℓ (ℓ + 1) cb t0 rg) = evalRawGate us rg := by
        cases rg with
        | const bv => rfl
        | not w =>
          dsimp only [shiftCopyGate]; rw [evalRawGate_not, evalRawGate_not]
          by_cases hw : w < us.length
          · rw [ite_eq_left ((htr w).1.2 hw), ite_eq_left hw, (htr w).2 hw]
          · rw [ite_eq_right (mt (htr w).1.1 hw), ite_eq_right hw]
        | and w₁ w₂ =>
          dsimp only [shiftCopyGate]; rw [evalRawGate_and, evalRawGate_and]
          by_cases h12 : w₁ < us.length ∧ w₂ < us.length
          · rcases h12 with ⟨h1, h2⟩
            have hc1 : (decide (tr w₁ < vs.length) && decide (tr w₂ < vs.length)) = true := by
              simp only [Bool.and_eq_true, decide_eq_true_eq]
              exact ⟨(htr w₁).1.2 h1, (htr w₂).1.2 h2⟩
            have hc2 : (decide (w₁ < us.length) && decide (w₂ < us.length)) = true := by
              simp only [Bool.and_eq_true, decide_eq_true_eq]; exact ⟨h1, h2⟩
            rw [ite_eq_left hc1, ite_eq_left hc2, (htr w₁).2 h1, (htr w₂).2 h2]
          · have hf1 : ¬((decide (tr w₁ < vs.length) && decide (tr w₂ < vs.length)) = true) := by
              simp only [Bool.and_eq_true, decide_eq_true_eq, (htr w₁).1, (htr w₂).1]; exact h12
            have hf2 : ¬((decide (w₁ < us.length) && decide (w₂ < us.length)) = true) := by
              simp only [Bool.and_eq_true, decide_eq_true_eq]; exact h12
            rw [ite_eq_right hf1, ite_eq_right hf2]
        | or w₁ w₂ =>
          dsimp only [shiftCopyGate]; rw [evalRawGate_or, evalRawGate_or]
          by_cases h12 : w₁ < us.length ∧ w₂ < us.length
          · rcases h12 with ⟨h1, h2⟩
            have hc1 : (decide (tr w₁ < vs.length) && decide (tr w₂ < vs.length)) = true := by
              simp only [Bool.and_eq_true, decide_eq_true_eq]
              exact ⟨(htr w₁).1.2 h1, (htr w₂).1.2 h2⟩
            have hc2 : (decide (w₁ < us.length) && decide (w₂ < us.length)) = true := by
              simp only [Bool.and_eq_true, decide_eq_true_eq]; exact ⟨h1, h2⟩
            rw [ite_eq_left hc1, ite_eq_left hc2, (htr w₁).2 h1, (htr w₂).2 h2]
          · have hf1 : ¬((decide (tr w₁ < vs.length) && decide (tr w₂ < vs.length)) = true) := by
              simp only [Bool.and_eq_true, decide_eq_true_eq, (htr w₁).1, (htr w₂).1]; exact h12
            have hf2 : ¬((decide (w₁ < us.length) && decide (w₂ < us.length)) = true) := by
              simp only [Bool.and_eq_true, decide_eq_true_eq]; exact h12
            rw [ite_eq_right hf1, ite_eq_right hf2]
      set bnew := evalRawGate us rg
      have hold_app {xs : List Bool} {idx : ℕ} (hi : idx < xs.length) :
          (xs ++ [bnew]).getD idx false = xs.getD idx false := by
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem (by simp; omega), List.getElem?_eq_getElem hi,
          List.getElem_append_left hi]
      simp only [List.map_cons, evalRawGates_cons, hstep]
      exact ih t0 (vs ++ [bnew]) (us ++ [bnew]) cb hcb (by simp; omega) (by simp; omega)
        (fun i hi => ⟨(hold_app (by omega)).trans (hdesc i hi).1,
          (hold_app (by omega)).trans (hdesc i hi).2⟩)
        ((hold_app (by omega)).trans hvf) ((hold_app (by omega)).trans hvt)
        (fun i hi => (hold_app (by omega)).trans (hin i hi))
        (fun d hd => by
          simp only [List.length_append, List.length_singleton] at hd
          by_cases hlt : d < us.length - (ℓ + k)
          · rw [hold_app (by omega), hold_app (by omega)]; exact hgd d hlt
          · have h1 : cb + d = vs.length := by omega
            have h2 : ℓ + k + d = us.length := by omega
            simp [h1, h2, List.getD_eq_getElem?_getD])
  set v0 := List.ofFn v ++ [false, true]
  have hall : ∀ n : ℕ, n ≤ 2 ^ k →
      let vn := evalRawGates v0 (((List.range n).map fun t0 =>
        ug.map (shiftCopyGate ℓ k ℓ (ℓ + 1) (ℓ + 2 + t0 * ug.length) t0)).flatten)
      vn.length = ℓ + 2 + n * ug.length ∧
      ∀ t0 < n, vn.getD (ℓ + 2 + t0 * ug.length + (uout - (ℓ + k))) false =
        (evalRawGates (List.ofFn (Fin.append v (indexToBitString k t0))) ug).getD uout false := by
    intro n; induction n with
    | zero => intro _; simp [v0, ℓ]
    | succ n ih =>
      intro hn
      obtain ⟨hvn_len, hvn_t⟩ := ih (by omega)
      set vn := evalRawGates v0 (((List.range n).map fun t0 =>
        ug.map (shiftCopyGate ℓ k ℓ (ℓ + 1) (ℓ + 2 + t0 * ug.length) t0)).flatten)
      simp only [List.range_succ, List.map_append, List.flatten_append, List.map_singleton,
        List.flatten_cons, List.flatten_nil, List.append_nil, evalRawGates_append]
      refine ⟨by rw [length_evalRawGates, hvn_len, List.length_map, Nat.succ_mul, add_assoc],
        fun t0 ht0 => ?_⟩
      by_cases hlt : t0 < n
      · rw [getD_evalRawGates_lt vn _ (by
          rw [hvn_len]; have := Nat.mul_le_mul_right ug.length hlt
          rw [Nat.succ_mul] at this; omega)]
        exact hvn_t t0 hlt
      · have hte : t0 = n := by omega
        subst hte
        let us0 := List.ofFn (Fin.append v (indexToBitString k t0))
        have hold0 {p : ℕ} (hp : p < ℓ + 2) : vn.getD p false = v0.getD p false :=
          getD_evalRawGates_lt v0 _
            (by simp only [v0, List.length_append, List.length_ofFn, List.length_cons,
                  List.length_nil]; exact hp)
        have hc := hcopy ug t0 vn us0 (ℓ + 2 + t0 * ug.length) (by omega)
          (by simp [us0, hvn_len, ℓ]) (by simp [us0, ℓ])
          (fun i hi => ⟨(hold0 (by omega)).trans (by
              rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp [v0]; omega),
                Option.getD_some, List.getElem_append_left (by simp [hi, ℓ]), List.getElem_ofFn]),
            by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp [us0]; omega),
                Option.getD_some, List.getElem_ofFn]; exact Fin.append_left v _ ⟨i, hi⟩⟩)
          ((hold0 (by omega)).trans (by simp [v0, ℓ, List.getD_eq_getElem?_getD]))
          ((hold0 (by omega)).trans (by
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp [v0, ℓ]),
              Option.getD_some, List.getElem_append_right (by simp [ℓ])]; simp [ℓ]))
          (fun i hi => by
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp [us0, ℓ]; omega),
              Option.getD_some, List.getElem_ofFn]
            exact Fin.append_right v (indexToBitString k t0) ⟨i, hi⟩)
          (fun d hd => by simp [us0, ℓ] at hd)
          (uout - (ℓ + k)) (by simp [us0, ℓ]; omega)
        rwa [show ℓ + k + (uout - (ℓ + k)) = uout by omega] at hc
  have ht_out_lt : ∀ j : Fin (truthTableOuts k s).length,
      (truthTableOuts k s)[j.val] < ℓ + (truthTableGates k s).length := by
    intro j
    have hj : j.val < 2 ^ k := by simpa [truthTableOuts] using j.isLt
    have hsz : (truthTableGates k s).length = 2 + 2 ^ k * ug.length := by
      have := size_truthTableCircuit k s hk
      change (truthTableGates k s).length = _ at this
      rw [this]; simp [ug]
    have hgd : (univRawOuts k 1 s).getD 0 (ℓ + k) = uout := by
      simp [uout, List.getD_eq_getElem?_getD]
    simp only [truthTableOuts, List.getElem_map, List.getElem_range]
    change ℓ + 2 + j.val * ug.length + ((univRawOuts k 1 s).getD 0 (ℓ + k) - (ℓ + k)) <
      ℓ + (truthTableGates k s).length
    rw [hgd, hsz]
    have := Nat.mul_le_mul_right ug.length hj; rw [Nat.succ_mul] at this
    omega
  have ht_idx : t.val < (truthTableOuts k s).length := by simp [truthTableOuts]
  have hev1 := eval_buildRawCircuit ℓ (univDescLen_pos_of_pos hk le_rfl)
    (truthTableGates k s) (truthTableOuts k s) ht_out_lt v ⟨t.val, ht_idx⟩
  have hev2 := eval_buildRawCircuit (ℓ + k) (by omega) ug (univRawOuts k 1 s)
    (univRawOuts_lt k 1 s) (Fin.append v (indexToBitString k t.val)) ⟨0, by simp⟩
  change (buildRawCircuit ℓ _ (truthTableGates k s) (truthTableOuts k s)).eval
    interpretation v ⟨t.val, ht_idx⟩ =
    (buildRawCircuit (ℓ + k) _ ug (univRawOuts k 1 s)).eval
      interpretation (Fin.append v (indexToBitString k t.val)) ⟨0, by simp⟩
  rw [hev1, hev2]
  have hgd : (univRawOuts k 1 s).getD 0 (ℓ + k) = uout := by
    simp [uout, List.getD_eq_getElem?_getD]
  have hout_eq : (truthTableOuts k s)[t.val]'ht_idx =
      ℓ + 2 + t.val * ug.length + (uout - (ℓ + k)) := by
    simp only [truthTableOuts, List.getElem_map, List.getElem_range]
    change ℓ + 2 + t.val * ug.length + ((univRawOuts k 1 s).getD 0 (ℓ + k) - (ℓ + k)) = _
    rw [hgd]
  have htg_eq : evalRawGates (List.ofFn v) (truthTableGates k s) =
      evalRawGates v0 (((List.range (2 ^ k)).map fun t0 =>
        ug.map (shiftCopyGate ℓ k ℓ (ℓ + 1) (ℓ + 2 + t0 * ug.length) t0)).flatten) := by
    change evalRawGates (List.ofFn v) ([.const false, .const true] ++ _) = _
    rw [evalRawGates_append]; congr 1
    simp [v0, List.append_assoc]
  rw [hout_eq, htg_eq]
  exact (hall (2 ^ k) le_rfl).2 t.val t.isLt

/-- Evaluating `truthTableCircuit k s hk` on `encodeCircuit c s hs` outputs the exact truth table
`t ↦ c.eval interpretation (indexToBitString k t.val) 0` of `c`. -/
theorem eval_truthTableCircuit_encodeCircuit {k s : ℕ} (hk : 1 ≤ k)
    (c : Circuit signature k 1) (hs : c.size ≤ s) (t : Fin (2 ^ k)) :
    (truthTableCircuit k s hk).eval interpretation (encodeCircuit c s hs) t =
      c.eval interpretation (indexToBitString k t.val) 0 := by
  rw [eval_truthTableCircuit hk, eval_univEvalCircuit hk c s hs]

/-- **Circuit-size lower-bound semantics of `τ(tt_{s, k})_b`:** whenever
`tauFormula 0 (truthTableCircuit k s hk) b ∈ TAUT`, every De Morgan circuit
`c : Circuit signature k 1` computing the Boolean function with truth table `b`
(`∀ t, c(indexToBitString k t) = b t`) has gate size strictly greater than `s`. -/
theorem size_gt_of_tauFormula_truthTableCircuit_mem_taut {k s : ℕ} (hk : 1 ≤ k)
    (b : BitString (2 ^ k)) (htaut : tauFormula 0 (truthTableCircuit k s hk) b ∈ TAUT)
    (c : Circuit signature k 1)
    (hc : ∀ t : Fin (2 ^ k), c.eval interpretation (indexToBitString k t.val) 0 = b t) :
    s < c.size := by
  by_contra hle
  have hs : c.size ≤ s := le_of_not_gt hle
  refine (tauFormula_mem_taut_iff 0 (truthTableCircuit k s hk) b).1 htaut
    ⟨encodeCircuit c s hs, funext fun t => ?_⟩
  rw [eval_truthTableCircuit_encodeCircuit hk c hs t, hc t]

end CslibFrontier.ProofComplexity
