module

public import CslibFrontier.Computability.Complexity.ProofSystem.Generators

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# XOR-Shifted Circuit Generators

Given a base De Morgan circuit `c : Circuit signature n m` and a tuple of `r ≤ 2 ^ q` shift strings
`s : Fin r → BitString m`, this module constructs XOR-shifted circuit
`ilangoCircuit c q r hr s : Circuit signature (n + q) m` mapping `(u, y)` to `c(u) ⊕ s_{idx(y)}`,
proves its exact gate-size formula, evaluation semantics, and shifted-range decomposition, and
records the closed-form gate table `ilangoExtraGate` for downstream Frege specialization.

## Main definitions

* `CslibFrontier.ProofComplexity.ilangoCircuit`: De Morgan circuit computing `(u, y) ↦ c(u) ⊕
  s_{idx(y)}` by appending equality decoders, one-hot shift selectors, and output XOR blocks to `c`.
* `CslibFrontier.ProofComplexity.ilangoShiftIdx`: decoded shift index `Fin r` of `y : BitString q`
  (defaulting out-of-range codes `≥ r` to `0`).
* `CslibFrontier.ProofComplexity.ilangoExtraGate`: closed-form `RawGate` formula for the `e`-th
  appended gate of `ilangoCircuit`.

## Main results

* `CslibFrontier.ProofComplexity.size_ilangoCircuit`: exact gate count
  `c.size + (2 + q + r * q + m * (r + 6))`.
* `CslibFrontier.ProofComplexity.eval_ilangoCircuit`: exact evaluation
  `(u, y) ↦ bitXor (c(u)) (s (ilangoShiftIdx q r hr y))` when `r ≤ 2 ^ q`.
* `CslibFrontier.ProofComplexity.range_ilangoCircuit`: range equals `⋃ j : Fin r, {c(u) ⊕ s_j | u}`.
* `CslibFrontier.ProofComplexity.lines_ilangoCircuit_lt` and
  `CslibFrontier.ProofComplexity.lines_ilangoCircuit_ge`: exact gate-line decomposition of
  `ilangoCircuit`.


-/

public section

namespace CslibFrontier.ProofComplexity

open CslibFrontier.Computability
open Cslib Cslib.Circuits Cslib.Circuits.Boolean

/-! ### Shifted-generator circuit and its gate-table semantics -/

/-- `q`-gate conjunction chain starting from `acc` against input bits `n .. n + q - 1` (or their
negations `negBase .. negBase + q - 1`) matching the first `q` bits of `jVal`. -/
private def eqChainGates (n negBase jVal cur acc : ℕ) : List ℕ → List RawGate
  | [] => []
  | t :: ts =>
    let lit := if jVal.testBit t then n + t else negBase + t
    .and acc lit :: eqChainGates n negBase jVal (cur + 1) cur ts

@[simp]
private theorem length_eqChainGates (n negBase jVal cur acc : ℕ) (ts : List ℕ) :
    (eqChainGates n negBase jVal cur acc ts).length = ts.length := by
  induction ts generalizing cur acc with
  | nil => rfl
  | cons _ _ ih => simp [eqChainGates, ih]

/-- Concatenate `r` equality-check chains of length `q` each. -/
private def allEqChains (n q negBase trueW cur : ℕ) : List ℕ → List RawGate
  | [] => []
  | j :: js =>
    eqChainGates n negBase j cur trueW (List.range q) ++
      allEqChains n q negBase trueW (cur + q) js

@[simp]
private theorem length_allEqChains (n q negBase trueW cur : ℕ) (js : List ℕ) :
    (allEqChains n q negBase trueW cur js).length = js.length * q := by
  induction js generalizing cur with
  | nil => simp [allEqChains]
  | cons _ js ih => simp [allEqChains, ih, Nat.succ_mul, add_comm]

/-- `r`-gate OR chain computing `⋁_{j ∈ js : diff j} eqW j`. -/
private def orDiffChain (falseW : ℕ) (eqW : ℕ → ℕ) (diff : ℕ → Bool) (cur acc : ℕ) :
    List ℕ → List RawGate
  | [] => []
  | j :: js =>
    .or acc (if diff j then eqW j else falseW) ::
      orDiffChain falseW eqW diff (cur + 1) cur js

@[simp]
private theorem length_orDiffChain (falseW : ℕ) (eqW : ℕ → ℕ) (diff : ℕ → Bool)
    (cur acc : ℕ) (js : List ℕ) :
    (orDiffChain falseW eqW diff cur acc js).length = js.length := by
  induction js generalizing cur acc with
  | nil => rfl
  | cons _ _ ih => simp [orDiffChain, ih]

/-- Per-output `(r + 6)`-gate block computing `sel_i` (via `r` ORs + 1 polarity gate) followed by
the 5-gate XOR `(out_i ∧ ¬sel_i) ∨ (¬out_i ∧ sel_i)`. -/
private def outXorBlock (r falseW : ℕ) (eqW : ℕ → ℕ) (outW : ℕ) (s0 : Bool)
    (sj : ℕ → Bool) (cur : ℕ) : List RawGate :=
  let chain := orDiffChain falseW eqW (fun j => sj j != s0) cur falseW (List.range r)
  let diffW := if r = 0 then falseW else cur + r - 1
  let selG : RawGate := if s0 then .not diffW else .or diffW falseW
  let selW := cur + r
  let nselW := cur + r + 1
  let noutW := cur + r + 2
  let t1W := cur + r + 3
  let t2W := cur + r + 4
  chain ++ [selG, .not selW, .not outW, .and outW nselW, .and noutW selW, .or t1W t2W]

@[simp]
private theorem length_outXorBlock (r falseW : ℕ) (eqW : ℕ → ℕ) (outW : ℕ) (s0 : Bool)
    (sj : ℕ → Bool) (cur : ℕ) :
    (outXorBlock r falseW eqW outW s0 sj cur).length = r + 6 := by
  simp [outXorBlock]

/-- Concatenate the `m` output XOR blocks. -/
private def allOutXorBlocks {m r : ℕ} (falseW : ℕ) (eqW : ℕ → ℕ) (outW : Fin m → ℕ)
    (hr : 1 ≤ r) (s : Fin r → BitString m) (cur : ℕ) : List (Fin m) → List RawGate
  | [] => []
  | i :: is =>
    outXorBlock r falseW eqW (outW i) (s ⟨0, hr⟩ i)
      (fun j => if hj : j < r then s ⟨j, hj⟩ i else false) cur ++
      allOutXorBlocks falseW eqW outW hr s (cur + (r + 6)) is

@[simp]
private theorem length_allOutXorBlocks {m r : ℕ} (falseW : ℕ) (eqW : ℕ → ℕ)
    (outW : Fin m → ℕ) (hr : 1 ≤ r) (s : Fin r → BitString m) (cur : ℕ) (is : List (Fin m)) :
    (allOutXorBlocks falseW eqW outW hr s cur is).length = is.length * (r + 6) := by
  induction is generalizing cur with
  | nil => simp [allOutXorBlocks]
  | cons _ _ ih => simp [allOutXorBlocks, ih, Nat.succ_mul, add_comm]

/-- Full list of extra `RawGate`s appended to `c.program` in `ilangoCircuit`. -/
private def ilangoExtraGates {n m : ℕ} (c : Circuit signature n m) (q r : ℕ) (hr : 1 ≤ r)
    (s : Fin r → BitString m) : List RawGate :=
  let base0 := (n + q) + c.size
  let falseW := base0
  let trueW := base0 + 1
  let negBase := base0 + 2
  let eqBase := negBase + q
  let eqW (j : ℕ) : ℕ := if q = 0 then trueW else eqBase + (j + 1) * q - 1
  let outBase := eqBase + r * q
  let outW (i : Fin m) : ℕ := wireToNat ((c.outputs i).mapInputs (Fin.castAdd q))
  [.const false, .const true] ++
    ((List.range q).map fun t => RawGate.not (n + t)) ++
    allEqChains n q negBase trueW eqBase (List.range r) ++
    allOutXorBlocks falseW eqW outW hr s outBase (List.finRange m)

private theorem length_ilangoExtraGates {n m : ℕ} (c : Circuit signature n m) (q r : ℕ)
    (hr : 1 ≤ r) (s : Fin r → BitString m) :
    (ilangoExtraGates c q r hr s).length = 2 + q + r * q + m * (r + 6) := by
  simp only [ilangoExtraGates, List.length_append, List.length_cons, List.length_nil,
    List.length_map, List.length_range, length_allEqChains, length_allOutXorBlocks,
    List.length_finRange]

/-- **Shifted-generator circuit**: given a base circuit
`c : Circuit signature n m`, `q` shift-index bits, and `r ≥ 1` shifts `s : Fin r → BitString m`
(with `r ≤ 2 ^ q`), maps `(u, y) ∈ BitString n × BitString q` to `c(u) ⊕ s_{idx(y)}`, defaulting
out-of-range indices `idx(y) ≥ r` to `s_0`. -/
def ilangoCircuit {n m : ℕ} (c : Circuit signature n m) (q r : ℕ) (hr : 1 ≤ r)
    (s : Fin r → BitString m) : Circuit signature (n + q) m where
  size := c.size + (ilangoExtraGates c q r hr s).length
  program := appendRawGates (c.program.mapInputs (Fin.castAdd q)) (ilangoExtraGates c q r hr s)
  outputs i :=
    have hlt : c.size + (2 + q + r * q + (i.val + 1) * (r + 6) - 1) <
        c.size + (ilangoExtraGates c q r hr s).length := by
      rw [length_ilangoExtraGates]
      have h1 : (i.val + 1) * (r + 6) ≤ m * (r + 6) := Nat.mul_le_mul_right _ i.isLt
      have h2 : 1 ≤ (i.val + 1) * (r + 6) := Nat.mul_pos (Nat.succ_pos _) (by omega)
      omega
    .gate ⟨c.size + (2 + q + r * q + (i.val + 1) * (r + 6) - 1), hlt⟩

/-- Exact gate size of `ilangoCircuit`. -/
theorem size_ilangoCircuit {n m : ℕ} (c : Circuit signature n m) (q r : ℕ) (hr : 1 ≤ r)
    (s : Fin r → BitString m) :
    (ilangoCircuit c q r hr s).size = c.size + (2 + q + r * q + m * (r + 6)) := by
  change c.size + (ilangoExtraGates c q r hr s).length = _
  rw [length_ilangoExtraGates]

/-- Output wire `i` of `ilangoCircuit c q r hr s` is gate
`c.size + (2 + q + r * q + (i.val + 1) * (r + 6) - 1)`. -/
theorem outputs_ilangoCircuit {n m : ℕ} (c : Circuit signature n m) (q r : ℕ) (hr : 1 ≤ r)
    (s : Fin r → BitString m) (i : Fin m) :
    (ilangoCircuit c q r hr s).outputs i =
      .gate ⟨c.size + (2 + q + r * q + (i.val + 1) * (r + 6) - 1), by
        rw [size_ilangoCircuit]
        have h1 : (i.val + 1) * (r + 6) ≤ m * (r + 6) := Nat.mul_le_mul_right _ i.isLt
        have h2 : 1 ≤ (i.val + 1) * (r + 6) := Nat.mul_pos (Nat.succ_pos _) (by omega)
        omega⟩ := by
  rfl

/-- Evaluation of `Program.mapInputs` commutes with precomposing the input vector. -/
private theorem eval_program_mapInputs {n n' g : ℕ} (p : Program signature n g)
    (f : Fin n → Fin n') (x : BitString n') :
    (p.mapInputs f).eval interpretation x = p.eval interpretation (x ∘ f) := by
  induction p with
  | empty => funext k; exact k.elim0
  | gate p l ih =>
    rw [Program.mapInputs_gate]
    funext k; refine Fin.lastCases ?_ (fun j => ?_) k
    · simp only [Program.eval_gate_last, ih, Line.mapInputs, Line.eval]
      congr 1; funext a; dsimp only [Function.comp_apply]
      cases l.wires a <;> rfl
    · simp only [Program.eval_gate_castSucc, ih]

/-- Lines of `Program.mapInputs`. -/
private theorem lines_program_mapInputs {n n' g : ℕ} (p : Program signature n g)
    (f : Fin n → Fin n') (k : Fin g) :
    (p.mapInputs f).lines k = (p.lines k).mapInputs f := by
  induction p with
  | empty => exact k.elim0
  | gate p l ih =>
    rw [Program.mapInputs_gate]
    refine Fin.lastCases ?_ (fun j => ?_) k
    · rw [Program.lines_gate_last, Program.lines_gate_last]
      dsimp only [Line.mapInputs, Line.mapWires]
      congr 1; funext a; dsimp only [Function.comp_apply, Wire.Renaming.apply,
        Wire.Renaming.castSucc]
      cases l.wires a <;> rfl
    · rw [Program.lines_gate_castSucc, ih, Program.lines_gate_castSucc]
      dsimp only [Line.mapInputs, Line.mapWires]
      congr 1; funext a; dsimp only [Function.comp_apply, Wire.Renaming.apply,
        Wire.Renaming.castSucc]
      cases (p.lines j).wires a <;> rfl

/-- Selecting the shift index `Fin r` corresponding to `y : BitString q` (falling back to `0`). -/
def ilangoShiftIdx (q r : ℕ) (hr : 1 ≤ r) (y : BitString q) : Fin r :=
  if h : bitStringToNat y < r then ⟨bitStringToNat y, h⟩ else ⟨0, hr⟩

/-- Evaluating `eqChainGates` computes the conjunction with `∀ t ∈ ts, y_t = j.testBit t`. -/
private theorem eval_eqChainGates (n q negBase jVal : ℕ) (y : BitString q) :
    ∀ (ts : List ℕ) (vals : List Bool) (acc : ℕ),
      acc < vals.length →
      (∀ s ∈ ts, ∃ hs : s < q, n + s < vals.length ∧ negBase + s < vals.length ∧
        vals.getD (n + s) false = y ⟨s, hs⟩ ∧ vals.getD (negBase + s) false = !y ⟨s, hs⟩) →
      ts ≠ [] →
      (evalRawGates vals (eqChainGates n negBase jVal vals.length acc ts)).getD
        (vals.length + ts.length - 1) false =
        (vals.getD acc false && ts.all fun s =>
          if hs : s < q then y ⟨s, hs⟩ == jVal.testBit s else true) := by
  intro ts; induction ts with
  | nil => intro _ _ _ _ h; exact (h rfl).elim
  | cons s rs' ihr =>
    intro vs ac hac hrs _
    obtain ⟨hsq, hns, hngs, hvn, hvng⟩ := hrs s List.mem_cons_self
    let lt := if jVal.testBit s then n + s else negBase + s
    have hlt1 : lt < vs.length := by dsimp only [lt]; split_ifs <;> assumption
    have hlt2 : vs.getD lt false = (y ⟨s, hsq⟩ == jVal.testBit s) := by
      dsimp only [lt]
      cases hjb : jVal.testBit s
      · simp only [Bool.false_eq_true, ↓reduceIte, hvng]; cases y ⟨s, hsq⟩ <;> rfl
      · simp only [↓reduceIte, hvn]; cases y ⟨s, hsq⟩ <;> rfl
    let nb := vs.getD ac false && (y ⟨s, hsq⟩ == jVal.testBit s)
    have hst : evalRawGate vs (.and ac lt) = nb := by
      rw [evalRawGate_and]
      simp only [hac, hlt1, decide_true, Bool.and_self, ↓reduceIte, hlt2, nb]
    let vs' := vs ++ [nb]
    have hvl : vs'.length = vs.length + 1 := by simp [vs']
    have hvlast : vs'.getD vs.length false = nb := by simp [vs', List.getD_eq_getElem?_getD]
    cases rs' with
    | nil =>
      rw [eqChainGates, eqChainGates, evalRawGates_cons, evalRawGates_nil, hst]
      change vs'.getD vs.length false = _
      rw [hvlast]; simp [hsq, nb]
    | cons s₂ st =>
      have ho {k : ℕ} (hk : k < vs.length) : vs'.getD k false = vs.getD k false := by
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem (by simp [vs']; omega), List.getElem?_eq_getElem hk,
          List.getElem_append_left hk]
      have hrec := ihr vs' vs.length (by simp [vs']) (fun u hu => by
        obtain ⟨huq, h1, h2, h3, h4⟩ := hrs u (List.mem_cons_of_mem _ hu)
        exact ⟨huq, by simp [vs']; omega, by simp [vs']; omega,
          (ho h1).trans h3, (ho h2).trans h4⟩) (List.cons_ne_nil _ _)
      rw [eqChainGates, evalRawGates_cons, hst]
      change (evalRawGates vs'
        (eqChainGates n negBase jVal (vs.length + 1) vs.length (s₂ :: st))).getD _ false = _
      rw [← hvl, show vs.length + (s :: s₂ :: st).length - 1 =
        vs'.length + (s₂ :: st).length - 1 by simp [vs']; omega, hrec, hvlast]
      simp [List.all_cons, hsq, nb, Bool.and_assoc]

/-- Evaluating `orDiffChain` computes `vals[acc] || js.any (fun j => diff j && vals[eqW j])`. -/
private theorem eval_orDiffChain (falseW : ℕ) (eqW : ℕ → ℕ) (diff : ℕ → Bool) :
    ∀ (js : List ℕ) (vals : List Bool) (acc : ℕ),
      acc < vals.length → falseW < vals.length → vals.getD falseW false = false →
      (∀ j ∈ js, eqW j < vals.length) → js ≠ [] →
      (evalRawGates vals (orDiffChain falseW eqW diff vals.length acc js)).getD
        (vals.length + js.length - 1) false =
        (vals.getD acc false || js.any fun j => diff j && vals.getD (eqW j) false) := by
  intro js; induction js with
  | nil => intro _ _ _ _ _ _ h; exact (h rfl).elim
  | cons j rest ih =>
    intro vals acc hacc hfw hfw0 hjs _
    have hjlt : eqW j < vals.length := hjs j List.mem_cons_self
    let op2 := if diff j then eqW j else falseW
    have hop2_lt : op2 < vals.length := by dsimp only [op2]; split_ifs <;> assumption
    have hop2_v : vals.getD op2 false = (diff j && vals.getD (eqW j) false) := by
      dsimp only [op2]
      cases diff j
      · simp only [Bool.false_eq_true, ↓reduceIte, hfw0, Bool.false_and]
      · simp only [↓reduceIte, Bool.true_and]
    let nb := vals.getD acc false || (diff j && vals.getD (eqW j) false)
    have hst : evalRawGate vals (.or acc op2) = nb := by
      rw [evalRawGate_or]
      simp only [hacc, hop2_lt, decide_true, Bool.and_self, ↓reduceIte, hop2_v, nb]
    let vals₁ := vals ++ [nb]
    have hv1_len : vals₁.length = vals.length + 1 := by simp [vals₁]
    have hv1_last : vals₁.getD vals.length false = nb := by
      simp [vals₁, List.getD_eq_getElem?_getD]
    have hold {k : ℕ} (hk : k < vals.length) : vals₁.getD k false = vals.getD k false := by
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (by simp [vals₁]; omega), List.getElem?_eq_getElem hk,
        List.getElem_append_left hk]
    cases rest with
    | nil =>
      rw [orDiffChain, orDiffChain, evalRawGates_cons, evalRawGates_nil, hst]
      change vals₁.getD vals.length false = _
      rw [hv1_last]; simp [nb]
    | cons j₂ jtail =>
      rw [orDiffChain, evalRawGates_cons, hst]
      change (evalRawGates vals₁
        (orDiffChain falseW eqW diff (vals.length + 1) vals.length (j₂ :: jtail))).getD _ false = _
      rw [← hv1_len, show vals.length + (j :: j₂ :: jtail).length - 1 =
        vals₁.length + (j₂ :: jtail).length - 1 by simp [vals₁]; omega,
        ih vals₁ vals.length (by simp [vals₁]) (by simp [vals₁]; omega)
          ((hold hfw).trans hfw0)
          (fun u hu => by have := hjs u (List.mem_cons_of_mem _ hu); simp [vals₁]; omega)
          (List.cons_ne_nil _ _), hv1_last]
      dsimp only [nb]; conv_rhs => rw [List.any_cons, ← Bool.or_assoc]
      suffices h : List.any (j₂ :: jtail) (fun j => diff j && vals₁.getD (eqW j) false) =
          List.any (j₂ :: jtail) (fun j => diff j && vals.getD (eqW j) false) by rw [h]
      rw [Bool.eq_iff_iff]; simp only [List.any_eq_true]
      exact ⟨fun ⟨u, hu, h⟩ => ⟨u, hu, by rwa [hold (hjs u (List.mem_cons_of_mem _ hu))] at h⟩,
        fun ⟨u, hu, h⟩ => ⟨u, hu, by rwa [hold (hjs u (List.mem_cons_of_mem _ hu))]⟩⟩

/-- Evaluating `outXorBlock` computes `xor (vals[outW]) (s j_y i)`. -/
private theorem eval_outXorBlock (r falseW : ℕ) (hr : 1 ≤ r) (eqW : ℕ → ℕ) (outW : ℕ)
    (s0 : Bool) (sj : ℕ → Bool) (jy : Fin r) (matched : Bool) (vals : List Bool)
    (hfw : falseW < vals.length) (hfw0 : vals.getD falseW false = false)
    (hout : outW < vals.length) (heq_lt : ∀ j < r, eqW j < vals.length)
    (heq_val : ∀ j < r, vals.getD (eqW j) false = (matched && decide (j = jy.val)))
    (hnomatch : matched = false → jy.val = 0) (hs0 : sj 0 = s0) :
    (evalRawGates vals (outXorBlock r falseW eqW outW s0 sj vals.length)).getD
      (vals.length + (r + 6) - 1) false = xor (vals.getD outW false) (sj jy.val) := by
  set cur := vals.length
  set chain := orDiffChain falseW eqW (fun j => sj j != s0) cur falseW (List.range r)
  set v1 := evalRawGates vals chain
  have hv1_len : v1.length = cur + r := by simp [v1, chain, cur]
  have hold1 {k : ℕ} (hk : k < cur) : v1.getD k false = vals.getD k false :=
    getD_evalRawGates_lt vals chain hk
  have hr_ne : List.range r ≠ [] := by intro h; simp at h; omega
  have hdiff_val : v1.getD (cur + r - 1) false = (sj jy.val != s0) := by
    have hev := eval_orDiffChain falseW eqW (fun j => sj j != s0) (List.range r) vals falseW
      hfw hfw hfw0 (fun j hj => heq_lt j (List.mem_range.1 hj)) hr_ne
    simp only [List.length_range, hfw0, Bool.false_or] at hev
    change v1.getD (cur + r - 1) false = _ at hev
    rw [hev]
    cases hm : matched
    · rw [hnomatch hm, hs0]; simp only [bne_self_eq_false, List.any_eq_false]
      intro j hj; rw [heq_val j (List.mem_range.1 hj), hm]; simp
    · cases hne : (sj jy.val != s0)
      · rw [List.any_eq_false]; intro j hj
        rw [heq_val j (List.mem_range.1 hj), hm, Bool.true_and]
        by_cases hje : j = jy.val <;> simp [hje, hne]
      · rw [List.any_eq_true]
        refine ⟨jy.val, List.mem_range.2 jy.isLt, ?_⟩
        rw [heq_val jy.val jy.isLt, hm, hne]; simp
  have hr0 : ¬(r = 0) := by omega
  let selG : RawGate := if s0 then .not (cur + r - 1) else .or (cur + r - 1) falseW
  have hsel_ev : evalRawGate v1 selG = sj jy.val := by
    have hdlt : cur + r - 1 < v1.length := by omega
    have hflt : falseW < v1.length := by omega
    dsimp only [selG]
    cases hs0v : s0
    · simp only [Bool.false_eq_true, ↓reduceIte, evalRawGate_or, hdlt, hflt, decide_true,
        Bool.and_self, hdiff_val, hold1 hfw, hfw0, Bool.or_false]
      cases sj jy.val <;> simp [hs0v]
    · simp only [↓reduceIte, evalRawGate_not, hdlt, hdiff_val]
      cases sj jy.val <;> simp [hs0v]
  let bOut := vals.getD outW false
  let bSel := sj jy.val
  have ho1 : v1.getD outW false = bOut := hold1 hout
  have hout_v1 : outW < cur + r := by omega
  have hext (xs : List Bool) (p : ℕ) (hp : p < cur + r) :
      (v1 ++ xs).getD p false = v1.getD p false := by
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by simp [hv1_len]; omega),
      List.getElem?_eq_getElem (hv1_len ▸ hp), List.getElem_append_left (hv1_len ▸ hp)]
  have hnew (xs : List Bool) (d : ℕ) (hd : d < xs.length) :
      (v1 ++ xs).getD (cur + r + d) false = xs[d] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp [hv1_len]; omega),
      Option.getD_some, List.getElem_append_right (by rw [hv1_len]; omega)]
    simp [hv1_len]
  have step (xs : List Bool) (rg : RawGate) (b : Bool) (hb : evalRawGate (v1 ++ xs) rg = b) :
      (v1 ++ xs) ++ [evalRawGate (v1 ++ xs) rg] = v1 ++ (xs ++ [b]) := by
    rw [hb, List.append_assoc]
  dsimp only [outXorBlock]; rw [ite_eq_right hr0, evalRawGates_append]
  have h6 : evalRawGates v1 [selG, .not (cur + r), .not outW, .and outW (cur + r + 1),
      .and (cur + r + 2) (cur + r), .or (cur + r + 3) (cur + r + 4)] =
      v1 ++ [bSel, !bSel, !bOut, bOut && !bSel, !bOut && bSel,
        (bOut && !bSel) || (!bOut && bSel)] := by
    simp only [evalRawGates_cons, evalRawGates_nil]
    have s0' : v1 ++ [evalRawGate v1 selG] = v1 ++ [bSel] := by rw [hsel_ev]
    rw [s0']
    rw [step _ (.not (cur + r)) (!bSel) (by
      rw [evalRawGate_not, ite_eq_left (by simp [hv1_len]),
        show cur + r = cur + r + 0 by omega, hnew _ 0 (by simp)]; rfl)]
    rw [step _ (.not outW) (!bOut) (by
      rw [evalRawGate_not, ite_eq_left (by simp [hv1_len]; omega), hext _ _ hout_v1, ho1])]
    rw [step _ (.and outW (cur + r + 1)) (bOut && !bSel) (by
      rw [evalRawGate_and, ite_eq_left (by simp [hv1_len]; omega), hext _ _ hout_v1, ho1,
        hnew _ 1 (by simp)]; rfl)]
    rw [step _ (.and (cur + r + 2) (cur + r)) (!bOut && bSel) (by
      rw [evalRawGate_and, ite_eq_left (by simp [hv1_len]), hnew _ 2 (by simp),
        show cur + r = cur + r + 0 by omega, hnew _ 0 (by simp)]; rfl)]
    rw [step _ (.or (cur + r + 3) (cur + r + 4)) ((bOut && !bSel) || (!bOut && bSel)) (by
      rw [evalRawGate_or, ite_eq_left (by simp [hv1_len]), hnew _ 3 (by simp),
        hnew _ 4 (by simp)]; rfl)]
    simp only [List.cons_append, List.nil_append]
  change (evalRawGates v1 [selG, .not (cur + r), .not outW, .and outW (cur + r + 1),
    .and (cur + r + 2) (cur + r), .or (cur + r + 3) (cur + r + 4)]).getD
    (cur + (r + 6) - 1) false = xor bOut bSel
  rw [h6, show cur + (r + 6) - 1 = cur + r + 5 by omega, hnew _ 5 (by simp)]
  change ((bOut && !bSel) || (!bOut && bSel)) = xor bOut bSel
  cases bOut <;> cases bSel <;> rfl

/-- Exact evaluation semantics of `ilangoCircuit`: on input `(u, y)` with `r ≤ 2 ^ q`, computes
`bitXor (c.eval interpretation u) (s (ilangoShiftIdx q r hr y))`. -/
theorem eval_ilangoCircuit {n m : ℕ} (c : Circuit signature n m) (q r : ℕ) (hr : 1 ≤ r)
    (hrq : r ≤ 2 ^ q) (s : Fin r → BitString m) (u : BitString n) (y : BitString q) :
    (ilangoCircuit c q r hr s).eval interpretation (Fin.append u y) =
      bitXor (c.eval interpretation u) (s (ilangoShiftIdx q r hr y)) := by
  let xy := Fin.append u y
  have hcomp : xy ∘ Fin.castAdd q = u := funext fun i => Fin.append_left u y i
  set base0 := (n + q) + c.size
  set falseW := base0; set trueW := base0 + 1; set negBase := base0 + 2
  set eqBase := negBase + q
  let eqW (j : ℕ) : ℕ := if q = 0 then trueW else eqBase + (j + 1) * q - 1
  set outBase := eqBase + r * q
  let outW (i : Fin m) : ℕ := wireToNat ((c.outputs i).mapInputs (Fin.castAdd q))
  set v0 := List.ofFn xy ++ List.ofFn (c.program.eval interpretation u)
  have hv0_len : v0.length = base0 := by
    rw [List.length_append, List.length_ofFn, List.length_ofFn]
  have hv0_in (t : Fin q) : v0.getD (n + t.val) false = y t := by
    rw [List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by rw [hv0_len]; dsimp [base0]; omega),
      Option.getD_some, List.getElem_append_left (by simp [xy]), List.getElem_ofFn]
    have hidx : (⟨n + t.val, by omega⟩ : Fin (n + q)) = Fin.natAdd n t := Fin.ext rfl
    rw [hidx]
    exact Fin.append_right u y t
  have hv0_out (i : Fin m) : v0.getD (outW i) false = c.eval interpretation u i ∧
      outW i < base0 := by
    cases hw : c.outputs i with
    | input a =>
      refine ⟨?_, by
        have := a.isLt; dsimp only [outW, base0]; rw [hw]
        simp only [Wire.mapInputs, wireToNat_input, Fin.val_castAdd]; omega⟩
      simp only [outW, hw, Wire.mapInputs, wireToNat_input, Circuit.eval, Program.trace,
        Function.comp_apply, Wire.elim, Fin.val_castAdd]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by
          have := a.isLt; rw [hv0_len]; dsimp [base0]; omega),
        Option.getD_some, List.getElem_append_left (by have := a.isLt; simp [xy]; omega),
        List.getElem_ofFn]
      exact Fin.append_left u y a
    | gate k =>
      refine ⟨?_, by
        have := k.isLt; dsimp only [outW, base0]; rw [hw]
        simp only [Wire.mapInputs, wireToNat_gate]; omega⟩
      simp only [outW, hw, Wire.mapInputs, wireToNat_gate, Circuit.eval, Program.trace,
        Function.comp_apply, Wire.elim]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by
          have := k.isLt; rw [hv0_len]; dsimp [base0]; omega),
        Option.getD_some, List.getElem_append_right (by simp [xy])]
      simp [xy]
  set v1 := evalRawGates v0 ([.const false, .const true] ++
    (List.range q).map fun t => RawGate.not (n + t))
  have hv1_eq : v1 = v0 ++ [false, true] ++ (List.ofFn fun t : Fin q => !y t) := by
    change evalRawGates v0 ([.const false, .const true] ++ _) = _
    rw [evalRawGates_append]
    have hc2 : evalRawGates v0 [.const false, .const true] = v0 ++ [false, true] := by
      simp [List.append_assoc]
    rw [hc2]
    have hneg : ∀ k : ℕ, k ≤ q →
        evalRawGates (v0 ++ [false, true]) ((List.range k).map fun t => RawGate.not (n + t)) =
          (v0 ++ [false, true]) ++ (List.range k).map
            (fun t => if ht : t < q then !y ⟨t, ht⟩ else false) := by
      intro k; induction k with
      | zero => intro _; simp
      | succ k ih =>
        intro hkq
        rw [List.range_succ, List.map_append, evalRawGates_append, ih (by omega)]
        simp only [List.map_singleton, evalRawGates_cons, evalRawGates_nil,
          evalRawGate_not, List.length_append, hv0_len, List.length_cons, List.length_nil,
          List.length_map, List.length_range]
        have hlt : n + k < base0 + (0 + 1 + 1) + k := by dsimp only [base0]; omega
        have hgd : (v0 ++ [false, true] ++
            (List.range k).map fun t => if ht : t < q then !y ⟨t, ht⟩ else false).getD
            (n + k) false = y ⟨k, hkq⟩ := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by
              simp [hv0_len]; dsimp [base0]; omega),
            Option.getD_some, List.getElem_append_left (by simp [hv0_len]; dsimp [base0]; omega),
            List.getElem_append_left (by rw [hv0_len]; dsimp [base0]; omega)]
          have := hv0_in ⟨k, hkq⟩
          rwa [List.getD_eq_getElem?_getD,
            List.getElem?_eq_getElem (by rw [hv0_len]; dsimp [base0]; omega),
            Option.getD_some] at this
        rw [ite_eq_left hlt, hgd, List.map_append, List.map_singleton,
          dite_eq_left (show k < q from hkq), List.append_assoc]
    rw [hneg q le_rfl]; congr 1
    exact List.ext_getElem (by simp) fun t _ h₂ => by
      simp only [List.length_ofFn] at h₂
      simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn, dite_eq_left h₂]
  have hv1_len : v1.length = eqBase := by simp [hv1_eq, hv0_len, eqBase, negBase]; omega
  have hv1_fw : v1.getD falseW false = false := by
    simp [hv1_eq, List.getD_eq_getElem?_getD, falseW, ← hv0_len, List.append_assoc]
  have hv1_tw : v1.getD trueW false = true := by
    rw [hv1_eq, List.append_assoc, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by simp [hv0_len, trueW]), Option.getD_some,
      List.getElem_append_right (by rw [hv0_len]; dsimp [trueW]; omega)]
    simp [hv0_len, trueW]
  have hv1_neg (t : Fin q) : v1.getD (negBase + t.val) false = !y t := by
    have htlt := t.isLt
    rw [hv1_eq, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by simp [hv0_len, negBase]; omega), Option.getD_some,
      List.getElem_append_right (by simp [hv0_len, negBase])]
    simp [hv0_len, negBase]
  set v2 := evalRawGates v1 (allEqChains n q negBase trueW eqBase (List.range r))
  have hv2_len : v2.length = outBase := by simp [v2, hv1_len, outBase]
  let jy := ilangoShiftIdx q r hr y
  let matched : Bool := decide (bitStringToNat y < r)
  have hnomatch : matched = false → jy.val = 0 := by
    intro hm; simp only [matched, decide_eq_false_iff_not] at hm
    simp [jy, ilangoShiftIdx, hm]
  have hv2_eq (j : ℕ) (hjr : j < r) :
      eqW j < outBase ∧ v2.getD (eqW j) false = (matched && decide (j = jy.val)) := by
    have hmatch_iff : (∀ t : Fin q, y t = j.testBit t.val) ↔
        (bitStringToNat y < r ∧ j = jy.val) := by
      constructor
      · intro hall
        have hjeq : bitStringToNat y = j :=
          eq_of_lt_two_pow_of_testBit_eq (bitStringToNat_lt y) (lt_of_lt_of_le hjr hrq)
            fun t => (testBit_bitStringToNat y t).trans (hall t)
        have hlt : bitStringToNat y < r := hjeq ▸ hjr
        exact ⟨hlt, by dsimp [jy, ilangoShiftIdx]; rw [dite_eq_left hlt]; exact hjeq.symm⟩
      · rintro ⟨hlt, rfl⟩ t
        dsimp only [jy, ilangoShiftIdx]; rw [dite_eq_left hlt, testBit_bitStringToNat]
    by_cases hq0 : q = 0
    · have hr1 : r = 1 := by have : 2 ^ q = 1 := by subst hq0; rfl
                             omega
      have h1 : j = 0 := by omega
      have h2 : bitStringToNat y = 0 := by have := bitStringToNat_lt y; subst hq0; omega
      have hlt : bitStringToNat y < r := by omega
      have hjy0 : jy.val = 0 := by have := jy.isLt; omega
      refine ⟨by dsimp [eqW, outBase, eqBase, negBase, trueW]; rw [ite_eq_left hq0]; omega, ?_⟩
      dsimp only [eqW]; rw [ite_eq_left hq0]
      change (evalRawGates v1 _).getD trueW false = _
      rw [getD_evalRawGates_lt v1 _ (by rw [hv1_len]; dsimp [eqBase, negBase, trueW]; omega),
        hv1_tw]
      simp [matched, hlt, hjy0, h1]
    · have hq1 : 1 ≤ q := by omega
      have hlt_out : eqW j < outBase := by
        simp only [eqW, hq0, ↓reduceIte, outBase]
        have hmul : (j + 1) * q ≤ r * q := Nat.mul_le_mul_right q hjr
        have hpos : 1 ≤ (j + 1) * q := Nat.mul_pos (Nat.succ_pos _) hq1
        omega
      refine ⟨hlt_out, ?_⟩
      have hsplit : ∀ k : ℕ, k ≤ r →
          let vk := evalRawGates v1 (allEqChains n q negBase trueW eqBase (List.range k))
          vk.length = eqBase + k * q ∧
          ∀ i < k, vk.getD (eqBase + (i + 1) * q - 1) false =
            ((List.range q).all fun t => if ht : t < q then y ⟨t,
              ht⟩ == i.testBit t else true) := by
        intro k; induction k with
        | zero => intro _; simp [allEqChains, hv1_len]
        | succ k ih =>
          intro hkr
          obtain ⟨hklen, hkih⟩ := ih (by omega)
          have hch : allEqChains n q negBase trueW eqBase (List.range (k + 1)) =
              allEqChains n q negBase trueW eqBase (List.range k) ++
                eqChainGates n negBase k (eqBase + k * q) trueW (List.range q) := by
            have aux : ∀ xs ys cur, allEqChains n q negBase trueW cur (xs ++ ys) =
                allEqChains n q negBase trueW cur xs ++
                  allEqChains n q negBase trueW (cur + xs.length * q) ys := by
              intro xs; induction xs with
              | nil => intro _ _; simp [allEqChains]
              | cons _ xs ihx =>
                intro ys cur
                simp only [List.cons_append, allEqChains, ihx, List.append_assoc,
                  List.length_cons, Nat.succ_mul]
                rw [show cur + q + xs.length * q = cur + (xs.length * q + q) by omega]
            rw [List.range_succ, aux]; simp [allEqChains]
          set vk := evalRawGates v1 (allEqChains n q negBase trueW eqBase (List.range k))
          refine ⟨by rw [hch, evalRawGates_append, length_evalRawGates, hklen,
            length_eqChainGates, List.length_range, Nat.succ_mul, add_assoc], fun i hik => ?_⟩
          rw [hch, evalRawGates_append]
          by_cases hik' : i < k
          · rw [getD_evalRawGates_lt vk _ (by
              rw [hklen]
              have hmul : (i + 1) * q ≤ k * q := Nat.mul_le_mul_right q hik'
              have hpos : 1 ≤ (i + 1) * q := Nat.mul_pos (Nat.succ_pos _) hq1
              omega)]
            exact hkih i hik'
          · have hie : i = k := by omega
            subst hie
            have htw_lt : trueW < vk.length := by
              rw [hklen]; dsimp only [eqBase, negBase, trueW]; omega
            have hev := eval_eqChainGates n q negBase i y (List.range q) vk trueW htw_lt
              (fun t ht => by
                have htq := List.mem_range.1 ht
                have h1 : n + t < eqBase := by dsimp [eqBase, negBase, base0]; omega
                have h2 : negBase + t < eqBase := by dsimp [eqBase]; omega
                exact ⟨htq, by rw [hklen]; omega, by rw [hklen]; omega,
                  (getD_evalRawGates_lt v1 _ (hv1_len ▸ h1)).trans
                    ((getD_evalRawGates_lt v0 _ (by rw [hv0_len]; dsimp [base0]; omega)).trans
                      (hv0_in ⟨t, htq⟩)),
                  (getD_evalRawGates_lt v1 _ (hv1_len ▸ h2)).trans (hv1_neg ⟨t, htq⟩)⟩)
              (by intro h; simp at h; omega)
            rw [hklen] at hev
            have hidx_eq : eqBase + (i + 1) * q - 1 =
                eqBase + i * q + (List.range q).length - 1 := by
              rw [List.length_range, Nat.succ_mul]; omega
            rw [hidx_eq, hev]
            have htwv : vk.getD trueW false = true :=
              (getD_evalRawGates_lt v1 _
                (by rw [hv1_len]; dsimp only [eqBase, negBase, trueW]; omega)).trans hv1_tw
            rw [htwv, Bool.true_and]
      have hval := (hsplit r le_rfl).2 j hjr
      simp only [eqW, hq0, ↓reduceIte]
      change v2.getD _ false = _ at hval
      rw [hval, Bool.eq_iff_iff]
      simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, matched, decide_eq_true_eq]
      refine ⟨fun h => hmatch_iff.1 fun t => ?_, fun h t ht => ?_⟩
      · simpa [t.isLt] using h t.val t.isLt
      · simp [ht, hmatch_iff.2 h ⟨t, ht⟩]
  set v3 := evalRawGates v2 (allOutXorBlocks falseW eqW outW hr s outBase (List.finRange m))
  have hblocks : ∀ k : ℕ, k ≤ m →
      let is := (List.finRange m).take k
      let vk := evalRawGates v2 (allOutXorBlocks falseW eqW outW hr s outBase is)
      vk.length = outBase + k * (r + 6) ∧
      ∀ i : Fin m, i.val < k →
        vk.getD (outBase + (i.val + 1) * (r + 6) - 1) false =
          xor (c.eval interpretation u i) (s jy i) := by
    have happ_bl : ∀ xs ys cur, allOutXorBlocks falseW eqW outW hr s cur (xs ++ ys) =
        allOutXorBlocks falseW eqW outW hr s cur xs ++
          allOutXorBlocks falseW eqW outW hr s (cur + xs.length * (r + 6)) ys := by
      intro xs; induction xs with
      | nil => intro _ _; simp [allOutXorBlocks]
      | cons _ xs ihx =>
        intro ys cur
        simp only [List.cons_append, allOutXorBlocks, ihx, List.append_assoc,
          List.length_cons, Nat.succ_mul]
        rw [show cur + (r + 6) + xs.length * (r + 6) = cur + (xs.length * (r + 6) + (r + 6)) by
          omega]
    intro k; induction k with
    | zero => intro _; simp [allOutXorBlocks, hv2_len]
    | succ k ih =>
      intro hkm
      obtain ⟨hklen, hkih⟩ := ih (by omega)
      let ik : Fin m := ⟨k, hkm⟩
      have htake : (List.finRange m).take (k + 1) = (List.finRange m).take k ++ [ik] := by
        rw [List.take_add_one, List.getElem?_eq_getElem (by simp; omega)]
        simp [ik]
      set vk := evalRawGates v2 (allOutXorBlocks falseW eqW outW hr s outBase
        ((List.finRange m).take k))
      have hlen_tk : ((List.finRange m).take k).length = k := by simp; omega
      refine ⟨by rw [htake, happ_bl, hlen_tk, allOutXorBlocks, allOutXorBlocks, List.append_nil,
        evalRawGates_append, length_evalRawGates, hklen, length_outXorBlock, Nat.succ_mul,
        add_assoc], fun i hik => ?_⟩
      rw [htake, happ_bl, hlen_tk, allOutXorBlocks, allOutXorBlocks, List.append_nil,
        evalRawGates_append]
      by_cases hik' : i.val < k
      · rw [getD_evalRawGates_lt vk _ (by
          rw [hklen]
          have hmul : (i.val + 1) * (r + 6) ≤ k * (r + 6) := Nat.mul_le_mul_right _ hik'
          have hpos : 1 ≤ (i.val + 1) * (r + 6) := Nat.mul_pos (Nat.succ_pos _) (by omega)
          omega)]
        exact hkih i hik'
      · have hie : i = ik := Fin.ext (by dsimp [ik]; omega)
        subst hie
        have hprev {idx : ℕ} (h : idx < outBase) : vk.getD idx false = v2.getD idx false :=
          getD_evalRawGates_lt v2 _ (hv2_len ▸ h)
        have hfw_lt : falseW < outBase := by dsimp [outBase, eqBase, negBase, falseW]; omega
        have hout_lt : outW ik < outBase :=
          (hv0_out ik).2.trans (by dsimp [outBase, eqBase, negBase]; omega)
        have hev := eval_outXorBlock r falseW hr eqW (outW ik) (s ⟨0, hr⟩ ik)
          (fun j => if hj : j < r then s ⟨j, hj⟩ ik else false) jy matched vk
          (hklen ▸ hfw_lt.trans_le (Nat.le_add_right _ _))
          ((hprev hfw_lt).trans ((getD_evalRawGates_lt v1 _ (by
            rw [hv1_len]; dsimp [eqBase, negBase, falseW]; omega)).trans hv1_fw))
          (hklen ▸ hout_lt.trans_le (Nat.le_add_right _ _))
          (fun j hj => hklen ▸ (hv2_eq j hj).1.trans_le (Nat.le_add_right _ _))
          (fun j hj => (hprev (hv2_eq j hj).1).trans (hv2_eq j hj).2)
          hnomatch (dite_eq_left hr)
        rw [hklen] at hev
        have hvo : vk.getD (outW ik) false = c.eval interpretation u ik :=
          (hprev hout_lt).trans ((getD_evalRawGates_lt v1 _ (by
            rw [hv1_len]; have := (hv0_out ik).2; dsimp [eqBase, negBase]; omega)).trans
            ((getD_evalRawGates_lt v0 _ (hv0_len ▸ (hv0_out ik).2)).trans (hv0_out ik).1))
        simp only [jy.isLt, ↓reduceDIte, hvo] at hev
        simpa only [ik, Nat.succ_mul, add_assoc] using hev
  have htr : List.ofFn xy ++
      List.ofFn ((ilangoCircuit c q r hr s).program.eval interpretation xy) = v3 := by
    have h0 := ofFn_eval_appendRawGates (c.program.mapInputs (Fin.castAdd q))
      (ilangoExtraGates c q r hr s) xy
    rw [eval_program_mapInputs, hcomp] at h0
    change List.ofFn xy ++ List.ofFn ((appendRawGates _ _).eval interpretation xy) = _
    rw [h0]
    have heg : ilangoExtraGates c q r hr s =
        (([.const false, .const true] ++ ((List.range q).map fun t => RawGate.not (n + t))) ++
          allEqChains n q negBase trueW eqBase (List.range r)) ++
          allOutXorBlocks falseW eqW outW hr s outBase (List.finRange m) := by
      simp [ilangoExtraGates, falseW, trueW, negBase, eqBase, eqW, outBase, outW, base0]
    rw [heg, evalRawGates_append, evalRawGates_append]
  have hfull := (hblocks m le_rfl).2
  rw [List.take_of_length_le (by simp)] at hfull
  refine eq_bitXor_of_forall fun i => ?_
  have hi := hfull i i.isLt
  change v3.getD (outBase + (i.val + 1) * (r + 6) - 1) false = _ at hi
  have hmul_i : (i.val + 1) * (r + 6) ≤ m * (r + 6) := Nat.mul_le_mul_right _ i.isLt
  have hpos_i : 1 ≤ (i.val + 1) * (r + 6) := Nat.mul_pos (Nat.succ_pos _) (by omega)
  rw [← htr, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (by
      simp only [List.length_append, List.length_ofFn, size_ilangoCircuit]
      dsimp only [outBase, eqBase, negBase, base0]; omega),
    Option.getD_some,
    List.getElem_append_right (by simp [xy]; dsimp [outBase, eqBase, negBase, base0]; omega),
    List.getElem_ofFn] at hi
  have hidx_fin : (⟨outBase + (i.val + 1) * (r + 6) - 1 - (List.ofFn xy).length,
      by simp only [List.length_ofFn, size_ilangoCircuit]
         dsimp only [outBase, eqBase, negBase, base0]; omega⟩ :
      Fin (ilangoCircuit c q r hr s).size) =
      ⟨c.size + (2 + q + r * q + (i.val + 1) * (r + 6) - 1),
        by rw [size_ilangoCircuit]; omega⟩ := by
    ext; simp [xy]; dsimp [outBase, eqBase, negBase, base0]; omega
  rw [hidx_fin] at hi
  simpa only [Circuit.eval, Program.trace, Function.comp_apply, outputs_ilangoCircuit,
    Wire.elim] using hi

/-- The range of `ilangoCircuit c q r hr s` (for `r ≤ 2 ^ q`) is the exact union of shifted ranges
`⋃ j : Fin r, {c(u) ⊕ s_j | u : BitString n}`. -/
theorem range_ilangoCircuit {n m : ℕ} (c : Circuit signature n m) (q r : ℕ) (hr : 1 ≤ r)
    (hrq : r ≤ 2 ^ q) (s : Fin r → BitString m) :
    Set.range ((ilangoCircuit c q r hr s).eval interpretation) =
      ⋃ j : Fin r, Set.range (fun u : BitString n => bitXor (c.eval interpretation u) (s j)) := by
  ext b; simp only [Set.mem_range, Set.mem_iUnion]
  constructor
  · rintro ⟨xy, rfl⟩
    let u : BitString n := fun i => xy (Fin.castAdd q i)
    let y : BitString q := fun t => xy (Fin.natAdd n t)
    have hxy : Fin.append u y = xy :=
      funext fun i => Fin.addCases (fun _ => by simp [u]) (fun _ => by simp [y]) i
    rw [← hxy, eval_ilangoCircuit c q r hr hrq s u y]
    exact ⟨ilangoShiftIdx q r hr y, u, rfl⟩
  · rintro ⟨j, u, rfl⟩
    let y : BitString q := fun t => j.val.testBit t.val
    have hy : bitStringToNat y = j.val :=
      eq_of_lt_two_pow_of_testBit_eq (bitStringToNat_lt y) (lt_of_lt_of_le j.isLt hrq)
        fun t => testBit_bitStringToNat y t
    have hidx : ilangoShiftIdx q r hr y = j := by
      simp [ilangoShiftIdx, hy, j.isLt]
    exact ⟨Fin.append u y, (eval_ilangoCircuit c q r hr hrq s u y).trans (by rw [hidx])⟩

/-- Helper indexing into `allEqChains`. -/
private theorem getElem_allEqChains (n q negBase trueW cur : ℕ) (hq : 1 ≤ q) :
    ∀ (js : List ℕ) (p : ℕ) (hp : p < js.length * q),
      (allEqChains n q negBase trueW cur js)[p]'(by simp [hp]) =
        let a := p / q; let t := p % q
        let j := js[a]'(Nat.div_lt_of_lt_mul (by rwa [mul_comm]))
        let acc := if t = 0 then trueW else cur + a * q + t - 1
        let lit := if j.testBit t then n + t else negBase + t
        RawGate.and acc lit := by
  have hchain : ∀ (j c0 ac : ℕ) (ts : List ℕ) (t : ℕ) (ht : t < ts.length),
      (eqChainGates n negBase j c0 ac ts)[t]'(by simp [ht]) =
        RawGate.and (if t = 0 then ac else c0 + t - 1)
          (if j.testBit ts[t] then n + ts[t] else negBase + ts[t]) := by
    intro j c0 ac ts; induction ts generalizing c0 ac with
    | nil => intro _ h; simp at h
    | cons x xs ih =>
      intro t ht; cases t with
      | zero => simp [eqChainGates]
      | succ t =>
        simp only [eqChainGates, List.getElem_cons_succ,
          ih (c0 + 1) c0 t (by simp at ht; omega), Nat.succ_ne_zero, ↓reduceIte]
        congr 1; split_ifs <;> omega
  intro js; induction js generalizing cur with
  | nil => intro _ h; simp at h
  | cons j js ih =>
    intro p hp
    let ch := eqChainGates n negBase j cur trueW (List.range q)
    let rest := allEqChains n q negBase trueW (cur + q) js
    change (ch ++ rest)[p]'(by
      dsimp only [ch, rest]
      rw [List.length_append, length_eqChainGates, List.length_range, length_allEqChains]
      rw [List.length_cons, Nat.succ_mul] at hp; omega) = _
    by_cases hpq : p < q
    · rw [List.getElem_append_left (by simp [ch, hpq]),
        hchain j cur trueW (List.range q) p (by simp [hpq])]
      simp [Nat.div_eq_of_lt hpq, Nat.mod_eq_of_lt hpq]
    · rw [List.getElem_append_right (by simp [ch]; omega)]
      simp only [ch, length_eqChainGates, List.length_range]
      have hsub : p - q < js.length * q := by simp [Nat.succ_mul] at hp; omega
      rw [ih (cur + q) (p - q) hsub]
      have hdiv : p / q = (p - q) / q + 1 := by
        conv_lhs => rw [show p = (p - q) + q by omega]
        exact Nat.add_div_right _ hq
      have hmod : (p - q) % q = p % q := by
        conv_rhs => rw [show p = (p - q) + q by omega, Nat.add_mod_right]
      simp only [hdiv, List.getElem_cons_succ, hmod]; congr 1
      split_ifs with hm
      · rfl
      · rw [Nat.add_mul, one_mul]; omega

/-- Helper indexing into `allOutXorBlocks`. -/
private theorem getElem_allOutXorBlocks {m r : ℕ} (falseW : ℕ) (eqW : ℕ → ℕ)
    (outW : Fin m → ℕ) (hr : 1 ≤ r) (s : Fin r → BitString m) :
    ∀ (is : List (Fin m)) (cur p : ℕ) (hp : p < is.length * (r + 6)),
      (allOutXorBlocks falseW eqW outW hr s cur is)[p]'(by simp [hp]) =
        let a := p / (r + 6); let off := p % (r + 6)
        let i := is[a]'(Nat.div_lt_of_lt_mul (by rwa [mul_comm]))
        let bc := cur + a * (r + 6)
        let s0 := s ⟨0, hr⟩ i
        if hj : off < r then
          .or (if off = 0 then falseW else bc + off - 1)
            (if s ⟨off, hj⟩ i != s0 then eqW off else falseW)
        else if off = r then
          if s0 then .not (bc + r - 1) else .or (bc + r - 1) falseW
        else if off = r + 1 then .not (bc + r)
        else if off = r + 2 then .not (outW i)
        else if off = r + 3 then .and (outW i) (bc + r + 1)
        else if off = r + 4 then .and (bc + r + 2) (bc + r)
        else .or (bc + r + 3) (bc + r + 4) := by
  have hor : ∀ (diff : ℕ → Bool) (c0 ac : ℕ) (js : List ℕ) (t : ℕ) (ht : t < js.length),
      (orDiffChain falseW eqW diff c0 ac js)[t]'(by simp [ht]) =
        .or (if t = 0 then ac else c0 + t - 1) (if diff js[t] then eqW js[t] else falseW) := by
    intro diff c0 ac js; induction js generalizing c0 ac with
    | nil => intro _ h; simp at h
    | cons j js ih =>
      intro t ht; cases t with
      | zero => simp [orDiffChain]
      | succ t =>
        simp only [orDiffChain, List.getElem_cons_succ, ih (c0 + 1) c0 t (by simp at ht; omega),
          Nat.succ_ne_zero, ↓reduceIte]; congr 1; split_ifs <;> omega
  intro is; induction is with
  | nil => intro _ _ h; simp at h
  | cons i is ih =>
    intro cur p hp
    let blk := outXorBlock r falseW eqW (outW i) (s ⟨0, hr⟩ i)
      (fun j => if hj : j < r then s ⟨j, hj⟩ i else false) cur
    let rest := allOutXorBlocks falseW eqW outW hr s (cur + (r + 6)) is
    change (blk ++ rest)[p]'(by
      dsimp only [blk, rest]
      rw [List.length_append, length_outXorBlock, length_allOutXorBlocks]
      rw [List.length_cons, Nat.succ_mul] at hp; omega) = _
    by_cases hpr : p < r + 6
    · rw [List.getElem_append_left (by simp [blk, hpr])]
      simp only [Nat.div_eq_of_lt hpr, Nat.mod_eq_of_lt hpr, List.getElem_cons_zero, zero_mul,
        add_zero]
      let ch := orDiffChain falseW eqW
        (fun j => (if hj : j < r then s ⟨j, hj⟩ i else false) != s ⟨0, hr⟩ i) cur falseW
        (List.range r)
      let tail6 : List RawGate :=
        [if s ⟨0, hr⟩ i then .not (if r = 0 then falseW else cur + r - 1)
         else .or (if r = 0 then falseW else cur + r - 1) falseW,
         .not (cur + r), .not (outW i), .and (outW i) (cur + r + 1),
         .and (cur + r + 2) (cur + r), .or (cur + r + 3) (cur + r + 4)]
      change (ch ++ tail6)[p]'(by simp [ch, tail6, hpr]) = _
      by_cases h1 : p < r
      · rw [List.getElem_append_left (by simp [ch, h1]),
          hor _ cur falseW (List.range r) p (by simp [h1])]
        simp [h1]
      · rw [List.getElem_append_right (by simp [ch]; omega)]
        simp only [ch, length_orDiffChain, List.length_range, h1, ↓reduceDIte,
          show r ≠ 0 by omega, ↓reduceIte, tail6]
        rcases (show p = r ∨ p = r + 1 ∨ p = r + 2 ∨ p = r + 3 ∨ p = r + 4 ∨ p = r + 5 by omega)
          with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
    · rw [List.getElem_append_right (by simp [blk]; omega)]
      simp only [blk, length_outXorBlock]
      have hsub : p - (r + 6) < is.length * (r + 6) := by simp [Nat.succ_mul] at hp; omega
      rw [ih (cur + (r + 6)) (p - (r + 6)) hsub]
      have hdiv : p / (r + 6) = (p - (r + 6)) / (r + 6) + 1 := by
        conv_lhs => rw [show p = (p - (r + 6)) + (r + 6) by omega]
        exact Nat.add_div_right _ (by omega)
      have hmod : (p - (r + 6)) % (r + 6) = p % (r + 6) := by
        conv_rhs => rw [show p = (p - (r + 6)) + (r + 6) by omega, Nat.add_mod_right]
      have hbc : cur + (r + 6) + (p - (r + 6)) / (r + 6) * (r + 6) =
          cur + p / (r + 6) * (r + 6) := by rw [hdiv, Nat.add_mul, one_mul]; omega
      simp only [hdiv, List.getElem_cons_succ, hmod, hbc]

/-- Explicit closed-form `RawGate` description of the `e`-th appended gate in `ilangoCircuit`. -/
@[expose]
def ilangoExtraGate {n m : ℕ} (c : Circuit signature n m) (q r : ℕ) (hr : 1 ≤ r)
    (s : Fin r → BitString m) (e : ℕ) : RawGate :=
  let base0 := (n + q) + c.size
  let negBase := base0 + 2
  let eqBase := negBase + q
  let eqW (j : ℕ) : ℕ := if q = 0 then base0 + 1 else eqBase + (j + 1) * q - 1
  let outBase := eqBase + r * q
  let outW (i : Fin m) : ℕ := wireToNat ((c.outputs i).mapInputs (Fin.castAdd q))
  if e = 0 then .const false
  else if e = 1 then .const true
  else if e < 2 + q then .not (n + (e - 2))
  else if e < 2 + q + r * q then
    let p := e - (2 + q)
    let a := p / q
    let t := p % q
    let acc := if t = 0 then base0 + 1 else eqBase + a * q + t - 1
    let lit := if a.testBit t then n + t else negBase + t
    .and acc lit
  else
    let p := e - (2 + q + r * q)
    let a := p / (r + 6)
    let off := p % (r + 6)
    if ha : a < m then
      let i : Fin m := ⟨a, ha⟩
      let bc := outBase + a * (r + 6)
      let s0 := s ⟨0, hr⟩ i
      if hj : off < r then
        .or (if off = 0 then base0 else bc + off - 1)
          (if s ⟨off, hj⟩ i != s0 then eqW off else base0)
      else if off = r then
        if s0 then .not (bc + r - 1) else .or (bc + r - 1) base0
      else if off = r + 1 then .not (bc + r)
      else if off = r + 2 then .not (outW i)
      else if off = r + 3 then .and (outW i) (bc + r + 1)
      else if off = r + 4 then .and (bc + r + 2) (bc + r)
      else .or (bc + r + 3) (bc + r + 4)
    else .const false

private theorem getElem_ilangoExtraGates {n m : ℕ} (c : Circuit signature n m) (q r : ℕ)
    (hr : 1 ≤ r) (s : Fin r → BitString m) (e : ℕ)
    (he : e < 2 + q + r * q + m * (r + 6)) :
    (ilangoExtraGates c q r hr s)[e]'(by rw [length_ilangoExtraGates]; exact he) =
      ilangoExtraGate c q r hr s e := by
  dsimp only [ilangoExtraGates, ilangoExtraGate]
  by_cases he0 : e = 0
  · subst he0; simp
  · by_cases he1 : e = 1
    · subst he1; simp
    · obtain ⟨d, rfl⟩ : ∃ d, e = d + 2 := ⟨e - 2, by omega⟩
      simp only [List.cons_append, List.nil_append, List.getElem_cons_succ]
      by_cases heq_neg : d + 2 < 2 + q
      · have hdq : d < q := by omega
        rw [List.getElem_append_left (by simp; omega),
          List.getElem_append_left (by simp [hdq])]
        rw [ite_eq_right he0, ite_eq_right he1, ite_eq_left heq_neg]; simp
      · by_cases heq_ch : d + 2 < 2 + q + r * q
        · have hd_ge : q ≤ d := by omega
          have hprq : d - q < r * q := by omega
          have hq1 : 1 ≤ q := by
            by_contra h; have h0 : q = 0 := by omega
            rw [h0, mul_zero] at hprq; omega
          rw [List.getElem_append_left (by simp; omega),
            List.getElem_append_right (by simp; omega)]
          rw [ite_eq_right he0, ite_eq_right he1, ite_eq_right heq_neg, ite_eq_left heq_ch]
          simp only [List.length_map, List.length_range,
            show d + 2 - (2 + q) = d - q by omega]
          rw [getElem_allEqChains n q _ _ _ hq1 (List.range r) (d - q) (by simp [hprq])]
          simp
        · have hd_ge : q + r * q ≤ d := by omega
          have hpm : d - (q + r * q) < m * (r + 6) := by omega
          have ha : (d - (q + r * q)) / (r + 6) < m :=
            Nat.div_lt_of_lt_mul (by rw [mul_comm (r + 6)]; exact hpm)
          rw [List.getElem_append_right (by simp; omega)]
          rw [ite_eq_right he0, ite_eq_right he1, ite_eq_right heq_neg, ite_eq_right heq_ch]
          simp only [List.length_append, List.length_map, List.length_range, length_allEqChains,
            show d + 2 - (2 + q + r * q) = d - (q + r * q) by omega, ha, ↓reduceDIte]
          rw [getElem_allOutXorBlocks _ _ _ hr s (List.finRange m) _
            (d - (q + r * q)) (by simp; omega)]
          simp

/-- Gate lines `k'.val < c.size` of `ilangoCircuit` copy `c.program.lines`. -/
theorem lines_ilangoCircuit_lt {n m : ℕ} (c : Circuit signature n m) (q r : ℕ) (hr : 1 ≤ r)
    (s : Fin r → BitString m) (k' : Fin (ilangoCircuit c q r hr s).size) (hk : k'.val < c.size) :
    (ilangoCircuit c q r hr s).program.lines k' =
      ((c.program.lines ⟨k'.val, hk⟩).mapInputs (Fin.castAdd q)).mapWires
        (wireCastLE (by rw [size_ilangoCircuit]; omega)) := by
  have hl := lines_appendRawGates (c.program.mapInputs (Fin.castAdd q))
    (ilangoExtraGates c q r hr s) k'
  rw [dite_eq_left hk, lines_program_mapInputs] at hl
  exact hl

/-- Gate lines `c.size ≤ k'.val` of `ilangoCircuit` realize `ilangoExtraGate`. -/
theorem lines_ilangoCircuit_ge {n m : ℕ} (c : Circuit signature n m) (q r : ℕ) (hr : 1 ≤ r)
    (s : Fin r → BitString m) (k' : Fin (ilangoCircuit c q r hr s).size)
    (hk : ¬(k'.val < c.size)) :
    (ilangoCircuit c q r hr s).program.lines k' =
      (rawGateToLine (n + q) k'.val (ilangoExtraGate c q r hr s (k'.val - c.size))).mapWires
        (wireCastLE k'.isLt.le) := by
  have hlt : k'.val < c.size + (2 + q + r * q + m * (r + 6)) :=
    k'.isLt.trans_eq (size_ilangoCircuit c q r hr s)
  have he : k'.val - c.size < 2 + q + r * q + m * (r + 6) := by omega
  have hl := lines_appendRawGates (c.program.mapInputs (Fin.castAdd q))
    (ilangoExtraGates c q r hr s) k'
  rw [dite_eq_right hk, getElem_ilangoExtraGates c q r hr s _ he] at hl
  have heq : c.size + (k'.val - c.size) = k'.val := by omega
  have aux : ∀ {a b d : ℕ} (hab : a = b) (ha : a ≤ d) (hb : b ≤ d) (g0 : RawGate),
      (rawGateToLine (n + q) a g0).mapWires (wireCastLE ha) =
        (rawGateToLine (n + q) b g0).mapWires (wireCastLE hb) := by rintro a _ _ rfl _ _ _; rfl
  exact hl.trans (aux heq _ _ _)

/-- Appended gate `0` of `ilangoCircuit` is `const false`. -/
@[simp]
theorem ilangoExtraGate_zero {n m : ℕ} (c : Circuit signature n m) (q r : ℕ) (hr : 1 ≤ r)
    (s : Fin r → BitString m) :
    ilangoExtraGate c q r hr s 0 = .const false := rfl

/-- Appended gate `1` of `ilangoCircuit` is `const true`. -/
@[simp]
theorem ilangoExtraGate_one {n m : ℕ} (c : Circuit signature n m) (q r : ℕ) (hr : 1 ≤ r)
    (s : Fin r → BitString m) :
    ilangoExtraGate c q r hr s 1 = .const true := rfl

/-- Appended negation gates `2 ≤ e < 2 + q` of `ilangoCircuit`. -/
theorem ilangoExtraGate_of_lt_neg {n m : ℕ} (c : Circuit signature n m) (q r : ℕ) (hr : 1 ≤ r)
    (s : Fin r → BitString m) {e : ℕ} (he0 : e ≠ 0) (he1 : e ≠ 1) (he : e < 2 + q) :
    ilangoExtraGate c q r hr s e = .not (n + (e - 2)) := by
  simp [ilangoExtraGate, he0, he1, he]

/-- Appended equality-chain gates `2 + q ≤ e < 2 + q + r * q` of `ilangoCircuit`. -/
theorem ilangoExtraGate_of_lt_eqChain {n m : ℕ} (c : Circuit signature n m) (q r : ℕ) (hr : 1 ≤ r)
    (s : Fin r → BitString m) {e : ℕ} (he_ge : ¬e < 2 + q) (he : e < 2 + q + r * q) :
    let base0 := (n + q) + c.size
    let negBase := base0 + 2
    let eqBase := negBase + q
    let p := e - (2 + q)
    let a := p / q
    let t := p % q
    ilangoExtraGate c q r hr s e =
      .and (if t = 0 then base0 + 1 else eqBase + a * q + t - 1)
        (if a.testBit t then n + t else negBase + t) := by
  simp [ilangoExtraGate, show e ≠ 0 by omega, show e ≠ 1 by omega, he_ge, he]

/-- Appended output-XOR gates `e ≥ 2 + q + r * q` (with block index `< m`) of `ilangoCircuit`. -/
theorem ilangoExtraGate_of_outBlock {n m : ℕ} (c : Circuit signature n m) (q r : ℕ) (hr : 1 ≤ r)
    (s : Fin r → BitString m) {e : ℕ} (he_ge : ¬e < 2 + q + r * q)
    (ha : (e - (2 + q + r * q)) / (r + 6) < m) :
    let base0 := (n + q) + c.size
    let eqBase := base0 + 2 + q
    let eqW (j : ℕ) : ℕ := if q = 0 then base0 + 1 else eqBase + (j + 1) * q - 1
    let outBase := eqBase + r * q
    let p := e - (2 + q + r * q)
    let a := p / (r + 6)
    let off := p % (r + 6)
    let i : Fin m := ⟨a, ha⟩
    let bc := outBase + a * (r + 6)
    let s0 := s ⟨0, hr⟩ i
    let outWi := wireToNat ((c.outputs i).mapInputs (Fin.castAdd q))
    ilangoExtraGate c q r hr s e =
      (if hj : off < r then
        .or (if off = 0 then base0 else bc + off - 1)
          (if s ⟨off, hj⟩ i != s0 then eqW off else base0)
       else if off = r then
         if s0 then .not (bc + r - 1) else .or (bc + r - 1) base0
       else if off = r + 1 then .not (bc + r)
       else if off = r + 2 then .not outWi
       else if off = r + 3 then .and outWi (bc + r + 1)
       else if off = r + 4 then .and (bc + r + 2) (bc + r)
       else .or (bc + r + 3) (bc + r + 4)) := by
  simp [ilangoExtraGate, show e ≠ 0 by omega, show e ≠ 1 by omega,
    show ¬(e < 2 + q) by omega, he_ge, ha]

end CslibFrontier.ProofComplexity
