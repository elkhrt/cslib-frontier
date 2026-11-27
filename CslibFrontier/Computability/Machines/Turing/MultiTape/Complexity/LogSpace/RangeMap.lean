/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Papers Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.LogSpace

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.Cases
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.Composition.SmallSpace
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.CounterProgram.Words
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.QueryMachine
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Frame
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.NatLength
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Unbounded-Range Logspace Batch Evaluation and List Mapping

Proves that deterministic logarithmic space (`Turing.MultiTapeTM.ComputableInLogSpace`) is closed
under unbounded-range batch evaluation (`computableInLogSpace_map_range`,
`computableInLogSpace_map_range'`, `computableInLogSpace_mapToBits_range`) and parameterized list
mapping (`computableInLogSpace_listMap`) via a 4-phase `QueryMachine` driving the space-bounded
universal simulator `Universal.stepWith`.

## Main results

- `CslibFrontier.LogSpace.computableInLogSpace_map_range`
- `CslibFrontier.LogSpace.computableInLogSpace_map_range'`
- `CslibFrontier.LogSpace.computableInLogSpace_mapToBits_range`
- `CslibFrontier.LogSpace.computableInLogSpace_listMap`
-/

public section

namespace CslibFrontier.LogSpace

open Turing Turing.MultiTapeTM

/-! ### 1. Unbounded-Range Batch Evaluation in Logarithmic Space -/

section RangeMap

private abbrev RSt := ℕ × ℕ × ℕ × ℕ × Universal.SCfg

private abbrev encRSt : RSt ↪ List Bool :=
  encPair encNat (encPair encNat (encPair encNat (encPair encNat Universal.eCfg)))

private def symOf (s : RSt) (b : Option Bool) : Option ℕ :=
  if s.2.2.2.2.inputPos = 0 ∨ s.2.1 + s.2.2.2.1 < s.2.2.2.2.inputPos then none
  else b.map Universal.eBit

private def emitSym (o : Option ℕ) : List Bool :=
  o.elim [] fun n ↦ [true, decide (n ≠ 0)]

private def rangeQM (d : Universal.Desc) : QueryMachine RSt where
  init := (0, 0, 0, 0, Universal.init d)
  query s :=
    if s.1 = 0 then s.2.1 + s.2.1
    else if s.1 = 1 then s.2.1 + s.2.2.1
    else s.2.2.2.2.inputPos - 1
  next p :=
    let s := p.1
    let b := p.2
    if s.1 = 0 then
      if b = some true then (0, s.2.1 + 1, 0, 0, Universal.init d)
      else (1, s.2.1 + s.2.1 + 1, 0, 0, Universal.init d)
    else if s.1 = 1 then
      if b = some true then (1, s.2.1, s.2.2.1 + 1, 0, Universal.init d)
      else if s.2.2.1 = 0 then (3, s.2.1, 0, 0, Universal.init d)
      else (2, s.2.1, s.2.2.1, 0, Universal.init d)
    else if s.1 = 2 then
      if s.2.2.2.2.state.isNone then
        if s.2.2.2.1 + 1 < s.2.2.1 then (2, s.2.1, s.2.2.1, s.2.2.2.1 + 1, Universal.init d)
        else (3, s.2.1, s.2.2.1, s.2.2.2.1 + 1, Universal.init d)
      else
        (2, s.2.1, s.2.2.1, s.2.2.2.1, (Universal.stepWith d s.2.2.2.2 (symOf s b)).1)
    else s
  emit p :=
    let s := p.1
    let b := p.2
    if s.1 = 2 then
      if s.2.2.2.2.state.isNone then [false]
      else emitSym (Universal.stepWith d s.2.2.2.2 (symOf s b)).2
    else []
  halted s := decide (s.1 = 3)
  finish _ := []

private lemma cfgInputPos_inSpace :
    ComputableInSpace Universal.SCfg.inputPos Universal.eCfg encNat
      fun c ↦ (Universal.eCfg c).length :=
  ComputableInSpace.fst' (ComputableInSpace.snd'
    ((ComputableInSpace.of_inO (ComputableInDegree.id' (enc := Universal.eCfg)).inO_one).of_enc_eq
      (encC := Universal.eCfgFields) (g := fun c ↦ (c.state, c.inputPos, c.workTapes))
      fun _ ↦ rfl))

private lemma inSpace_congr_fun {α β : Type} {encA : α ↪ List Bool}
    {encB : β ↪ List Bool} {S : α → ℕ} {f g : α → β}
    (hf : ComputableInSpace f encA encB S) (h : ∀ x, g x = f x) :
    ComputableInSpace g encA encB S :=
  hf.of_enc_eq fun x ↦ congrArg encB (h x)

private lemma cfgHalted_inSpace :
    ComputableInSpace (fun c : Universal.SCfg ↦ c.state.isNone) Universal.eCfg encBool
      fun c ↦ (Universal.eCfg c).length := by
  have hst : ComputableInSpace Universal.SCfg.state Universal.eCfg Universal.eSym
      fun c ↦ (Universal.eCfg c).length :=
    ComputableInSpace.fst'
      ((ComputableInSpace.of_inO (ComputableInDegree.id' (enc := Universal.eCfg)).inO_one).of_enc_eq
        (encC := Universal.eCfgFields) (g := fun c ↦ (c.state, c.inputPos, c.workTapes))
        fun _ ↦ rfl)
  refine inSpace_congr_fun (ComputableInSpace.budget_comp_linear (encC := encBool)
    (ComputableInSpace.optionElim (encA := encUnary) (encE := encBool) true
      (ComputableInSpace.budget_const (encB := encBool) false))
    hst) fun c ↦ ?_
  cases c.state <;> rfl

private lemma optMapBit_inSpace :
    ComputableInSpace (fun b : Option Bool ↦ b.map Universal.eBit) (encOption encBool)
      Universal.eSym fun b ↦ (encOption encBool b).length := by
  have hsome : ComputableInSpace (fun bit : Bool ↦ (some (Universal.eBit bit) : Option ℕ))
      encBool Universal.eSym fun bit ↦ (encBool bit).length :=
    ComputableInSpace.budget_comp_linear
      (ComputableInSpace.of_inO
        (ComputableInDegree.optionSome (enc₁ := encUnary) (enc := Universal.eSym)).inO_one)
      (ComputableInSpace.of_finite Universal.eBit)
  refine inSpace_congr_fun (ComputableInSpace.optionElim none hsome) fun b ↦ ?_
  cases b <;> rfl

private lemma emitSym_inSpace :
    ComputableInSpace emitSym Universal.eSym encBits fun o ↦ (Universal.eSym o).length := by
  have hz : ComputableInSpace (fun n : ℕ ↦ [true, decide (n ≠ 0)]) encUnary encBits
      fun n ↦ (encUnary n).length :=
    inSpace_congr_fun (ComputableInSpace.budget_comp_linear (encC := encBits)
      (ComputableInSpace.of_finite (encB := encBits) fun z : Bool ↦ [true, !z])
      (ComputableInSpace.of_inO (.of_linear
        (.of_isEmpty (encIn := encUnary) (f := fun n ↦ decide (n = 0))
          fun n ↦ by cases n <;> simp))))
      fun n ↦ by cases n <;> simp
  exact ComputableInSpace.optionElim (encA := encUnary) [] hz

private lemma rangeQM_query_inSpace (d : Universal.Desc) :
    ComputableInSpace (rangeQM d).query encRSt encNat fun s ↦ (encRSt s).length := by
  open ComputableInSpace in
  have hph := fst encNat (encPair encNat (encPair encNat (encPair encNat Universal.eCfg)))
  have hs1 := snd encNat (encPair encNat (encPair encNat (encPair encNat Universal.eCfg)))
  have hk := fst' hs1; have hm := fst' (snd' hs1); have hcfg := snd' (snd' (snd' hs1))
  have hip := budget_comp_linear cfgInputPos_inSpace hcfg
  refine inSpace_congr_fun (budget_ite (budget_natEq hph (budget_const 0)) (budget_natAdd hk hk)
    (budget_ite (budget_natEq hph (budget_const 1)) (budget_natAdd hk hm)
      (budget_natPred hip))) fun s ↦ ?_
  simp only [rangeQM]; by_cases h0 : s.1 = 0 <;> by_cases h1 : s.1 = 1 <;> simp [h0, h1]

private lemma symOf_inSpace :
    ComputableInSpace (fun p : RSt × Option Bool ↦ symOf p.1 p.2)
      (QueryMachine.encStateRead encRSt) Universal.eSym
      fun p ↦ (QueryMachine.encStateRead encRSt p).length := by
  open ComputableInSpace in
  have hs := fst encRSt (encOption encBool); have hb := snd encRSt (encOption encBool)
  have hk := fst' (snd' hs); have hi := fst' (snd' (snd' (snd' hs)))
  have hcfg := snd' (snd' (snd' (snd' hs)))
  have hip := budget_comp_linear cfgInputPos_inSpace hcfg
  have hlt := budget_comp_lin natLt linear_succ (budget_prod (budget_natAdd hk hi) hip)
  have hcond := budget_finite (encC := encBool) (fun q : Bool × Bool ↦ q.1 || q.2)
    (budget_prod (budget_natIsZero hip) hlt)
  refine inSpace_congr_fun
    (budget_ite hcond (budget_const none) (budget_comp_linear optMapBit_inSpace hb)) fun p ↦ ?_
  simp only [symOf]
  by_cases hp0 : p.1.2.2.2.2.inputPos = 0 <;>
    by_cases hki : p.1.2.1 + p.1.2.2.2.1 < p.1.2.2.2.2.inputPos <;> simp [hp0, hki]

private lemma rangeQM_next_inSpace (d : Universal.Desc) :
    ComputableInSpace (rangeQM d).next (QueryMachine.encStateRead encRSt) encRSt
      fun p ↦ (QueryMachine.encStateRead encRSt p).length := by
  open ComputableInSpace in
  let bud (p : RSt × Option Bool) : ℕ := (QueryMachine.encStateRead encRSt p).length
  have hs := fst encRSt (encOption encBool)
  have hb := snd encRSt (encOption encBool)
  have hph := fst' hs; have hk := fst' (snd' hs); have hm := fst' (snd' (snd' hs))
  have hi := fst' (snd' (snd' (snd' hs))); have hcfg := snd' (snd' (snd' (snd' hs)))
  have hbTrue : ComputableInSpace (fun p : RSt × Option Bool ↦ decide (p.2 = some true))
      (QueryMachine.encStateRead encRSt) encBool bud :=
    budget_comp_linear (of_finite fun b : Option Bool ↦ decide (b = some true)) hb
  have hinit : ComputableInSpace (fun _ : RSt × Option Bool ↦ Universal.init d)
      (QueryMachine.encStateRead encRSt) Universal.eCfg bud :=
    budget_const (Universal.init d)
  let mkRSt {fph fk fm fi : RSt × Option Bool → ℕ} {fcfg : RSt × Option Bool → Universal.SCfg}
      (h1 : ComputableInSpace fph (QueryMachine.encStateRead encRSt) encNat bud)
      (h2 : ComputableInSpace fk (QueryMachine.encStateRead encRSt) encNat bud)
      (h3 : ComputableInSpace fm (QueryMachine.encStateRead encRSt) encNat bud)
      (h4 : ComputableInSpace fi (QueryMachine.encStateRead encRSt) encNat bud)
      (h5 : ComputableInSpace fcfg (QueryMachine.encStateRead encRSt) Universal.eCfg bud) :=
    budget_prod h1 (budget_prod h2 (budget_prod h3 (budget_prod h4 h5)))
  have hstep := fst' (budget_comp_linear (of_inO Universal.stepWith_inO)
    (budget_prod (budget_prod (budget_const (encB := Universal.eDesc) d) hcfg) symOf_inSpace))
  have hBr0 := budget_ite hbTrue
    (mkRSt (budget_const 0) (budget_natSucc hk) (budget_const 0) (budget_const 0) hinit)
    (mkRSt (budget_const 1) (budget_natSucc (budget_natAdd hk hk)) (budget_const 0)
      (budget_const 0) hinit)
  have hBr1 := budget_ite hbTrue
    (mkRSt (budget_const 1) hk (budget_natSucc hm) (budget_const 0) hinit)
    (budget_ite (budget_natIsZero hm)
      (mkRSt (budget_const 3) hk (budget_const 0) (budget_const 0) hinit)
      (mkRSt (budget_const 2) hk hm (budget_const 0) hinit))
  have hiSuccLt := budget_comp_lin natLt linear_succ (budget_prod (budget_natSucc hi) hm)
  have hBr2 := budget_ite (budget_comp_linear cfgHalted_inSpace hcfg)
    (budget_ite hiSuccLt
      (mkRSt (budget_const 2) hk hm (budget_natSucc hi) hinit)
      (mkRSt (budget_const 3) hk hm (budget_natSucc hi) hinit))
    (mkRSt (budget_const 2) hk hm hi hstep)
  refine inSpace_congr_fun (budget_ite (budget_natEq hph (budget_const 0)) hBr0
    (budget_ite (budget_natEq hph (budget_const 1)) hBr1
      (budget_ite (budget_natEq hph (budget_const 2)) hBr2 hs))) fun p ↦ ?_
  rcases p with ⟨⟨ph, k, m, i, cfg⟩, b⟩; simp only [rangeQM]
  by_cases h0 : ph = 0
  · subst h0; by_cases hb' : b = some true <;> simp [hb']
  · by_cases h1 : ph = 1
    · subst h1; by_cases hb' : b = some true
      · simp [hb']
      · by_cases hm0 : m = 0 <;> simp [hb', hm0]
    · by_cases h2 : ph = 2
      · subst h2; cases hnone : cfg.state.isNone
        · simp
        · by_cases hilt : i + 1 < m <;> simp [hilt]
      · simp [h0, h1, h2]

private lemma rangeQM_emit_inSpace (d : Universal.Desc) :
    ComputableInSpace (rangeQM d).emit (QueryMachine.encStateRead encRSt) encBits
      fun p ↦ (QueryMachine.encStateRead encRSt p).length := by
  open ComputableInSpace in
  have hs := fst encRSt (encOption encBool); have hph := fst' hs
  have hcfg := snd' (snd' (snd' (snd' hs)))
  have hout := snd' (budget_comp_linear (of_inO Universal.stepWith_inO)
    (budget_prod (budget_prod (budget_const (encB := Universal.eDesc) d) hcfg) symOf_inSpace))
  refine inSpace_congr_fun (budget_ite (budget_natEq hph (budget_const 2))
    (budget_ite (budget_comp_linear cfgHalted_inSpace hcfg) (budget_const (encB := encBits) [false])
      (budget_comp_linear emitSym_inSpace hout))
    (budget_const (encB := encBits) [])) fun p ↦ ?_
  rcases p with ⟨⟨ph, k, m, i, cfg⟩, b⟩; simp only [rangeQM]
  by_cases h2 : ph = 2
  · subst h2; cases cfg.state.isNone <;> simp
  · simp [h2]

private lemma rangeQM_halted_inSpace (d : Universal.Desc) :
    ComputableInSpace (rangeQM d).halted encRSt encBool fun s ↦ (encRSt s).length :=
  ComputableInSpace.budget_natEq
    (ComputableInSpace.fst encNat _) (ComputableInSpace.budget_const 3)

private lemma symOf_eq_inputSymbol (w : List Bool) (m i : ℕ) (hi : i ≤ m) (cfg : Universal.SCfg) :
    let W := frame w ++ List.replicate m true
    let L := 2 * w.length + 1
    let xi := frame w ++ List.replicate i true
    symOf (2, L, m, i, cfg) W[cfg.inputPos - 1]? =
      Universal.inputSymbol (xi.map Universal.eBit) cfg.inputPos := by
  intro W L xi
  have hL : (frame w).length = L := length_frame w
  have hxiLen : xi.length = L + i := by simp [xi, hL]
  have hTake : W.take (L + i) = xi := by simp [W, xi, List.take_append, hL, Nat.min_eq_left hi]
  unfold symOf Universal.inputSymbol; dsimp only
  rcases Nat.eq_zero_or_pos cfg.inputPos with hp0 | hpPos
  · simp [hp0]
  · simp only [hpPos.ne', false_or]
    by_cases hgt : L + i < cfg.inputPos
    · simp only [hgt, ↓reduceIte]; symm
      rw [List.head?_eq_none_iff, List.drop_eq_nil_iff, List.length_map, hxiLen]; omega
    · simp only [hgt, ↓reduceIte]; rw [List.head?_drop, List.getElem?_map]
      rw [← hTake, List.getElem?_take_of_lt (by omega : cfg.inputPos - 1 < L + i)]

private lemma runFrom_output_add {σ : Type} (M : QueryMachine σ) (W : List Bool)
    (s : σ) (T₁ T₂ : ℕ) :
    ((List.range (T₁ + T₂)).map fun t ↦
        M.emit (M.runFrom W s t, M.read W (M.runFrom W s t))).flatten =
      ((List.range T₁).map fun t ↦
          M.emit (M.runFrom W s t, M.read W (M.runFrom W s t))).flatten ++
        ((List.range T₂).map fun t ↦
          M.emit (M.runFrom W (M.runFrom W s T₁) t,
            M.read W (M.runFrom W (M.runFrom W s T₁) t))).flatten := by
  rw [List.range_add, List.map_append, List.flatten_append]; congr 1
  rw [List.map_map]; congr 1
  exact List.map_congr_left fun t _ ↦ by simp only [Function.comp_apply, QueryMachine.runFrom_add]

/-- **Unbounded-range batch evaluation in logarithmic space**: if `f : α × ℕ → β` is computable in
logarithmic space with unary second argument, then `(a, m) ↦ (List.range m).map (fun i ↦ f (a, i))`
is computable in logarithmic space. -/
theorem computableInLogSpace_map_range {α β : Type} {encIn : α ↪ List Bool}
    {encOut : β ↪ List Bool} {f : α × ℕ → β}
    (hf : ComputableInLogSpace f (encPair encIn encUnary) encOut) :
    ComputableInLogSpace (fun p : α × ℕ ↦ (List.range p.2).map fun i ↦ f (p.1, i))
      (encPair encIn encUnary) (encList encOut) := by
  obtain ⟨tf, cf, kf, Sf, hfinSf, tmf, htmf⟩ := hf
  let _ : Fintype Sf := Fintype.ofFinite Sf
  obtain ⟨ef, hef⟩ := Countable.exists_injective_nat Sf
  set d : Universal.Desc := Universal.desc ⟨ef, hef⟩ Universal.eBit tmf
  let M := rangeQM d
  choose uf huf_le huf using fun p : α × ℕ ↦ exists_haltsAt_of_runsInTime (htmf p).2.1
  let W_of (p : α × ℕ) : List Bool := encPair encIn encUnary p
  let L_of (a : α) : ℕ := 2 * (encIn a).length + 1
  have hW_eq (a : α) (m : ℕ) : W_of (a, m) = frame (encIn a) ++ List.replicate m true := rfl
  have hW_len (a : α) (m : ℕ) : (W_of (a, m)).length = L_of a + m := by
    simp [W_of, L_of, length_frame]
  have hPhase0 (a : α) (m : ℕ) :
      ∀ j ≤ (encIn a).length,
        M.runFrom (W_of (a, m)) M.init j = (0, j, 0, 0, Universal.init d) ∧
        (∀ t < j, M.halted (M.runFrom (W_of (a, m)) M.init t) = false) ∧
        ((List.range j).map fun t ↦
          M.emit (M.runFrom (W_of (a, m)) M.init t,
            M.read (W_of (a, m)) (M.runFrom (W_of (a, m)) M.init t))).flatten = [] := by
    intro j hj; induction j with
    | zero => simp [M, rangeQM]
    | succ j ih =>
      obtain ⟨hrun, hnh, hout⟩ := ih (by omega)
      have hread : M.read (W_of (a, m)) (0, j, 0, 0, Universal.init d) = some true := by
        simp only [M, QueryMachine.read, rangeQM, ↓reduceIte, hW_eq]
        rw [List.getElem?_append_left (by rw [length_frame]; omega), show j + j = 2 * j by omega]
        exact getElem?_frame_two_mul (by omega)
      have hstep : M.step (W_of (a, m)) (0, j, 0, 0, Universal.init d) =
          (0, j + 1, 0, 0, Universal.init d) := by rw [QueryMachine.step, hread]; rfl
      refine ⟨by rw [QueryMachine.runFrom_succ, hrun, hstep], fun t ht ↦ ?_, ?_⟩
      · rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp ht) with hlt | rfl
        · exact hnh t hlt
        · rw [hrun]; rfl
      · rw [List.range_succ, List.map_append, List.flatten_append, hout, List.map_singleton,
          List.flatten_singleton, hrun]; rfl
  have hPhase0End (a : α) (m : ℕ) :
      M.runFrom (W_of (a, m)) M.init ((encIn a).length + 1) =
        (1, L_of a, 0, 0, Universal.init d) ∧
      (∀ t < (encIn a).length + 1, M.halted (M.runFrom (W_of (a, m)) M.init t) = false) ∧
      ((List.range ((encIn a).length + 1)).map fun t ↦
        M.emit (M.runFrom (W_of (a, m)) M.init t,
          M.read (W_of (a, m)) (M.runFrom (W_of (a, m)) M.init t))).flatten = [] := by
    obtain ⟨hrun, hnh, hout⟩ := hPhase0 a m (encIn a).length le_rfl
    have hread : M.read (W_of (a, m)) (0, (encIn a).length, 0, 0, Universal.init d) =
        some false := by
      simp only [M, QueryMachine.read, rangeQM, ↓reduceIte, hW_eq]
      rw [List.getElem?_append_left (by rw [length_frame]; omega),
        show (encIn a).length + (encIn a).length = 2 * (encIn a).length by omega]
      exact getElem?_frame_two_mul_length (encIn a)
    have hstep : M.step (W_of (a, m)) (0, (encIn a).length, 0, 0, Universal.init d) =
        (1, L_of a, 0, 0, Universal.init d) := by
      rw [QueryMachine.step, hread]; simp [M, rangeQM, L_of, two_mul]
    refine ⟨by rw [QueryMachine.runFrom_succ, hrun, hstep], fun t ht ↦ ?_, ?_⟩
    · rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp ht) with hlt | rfl
      · exact hnh t hlt
      · rw [hrun]; rfl
    · rw [List.range_succ, List.map_append, List.flatten_append, hout, List.map_singleton,
        List.flatten_singleton, hrun]; rfl
  have hPhase1 (a : α) (m : ℕ) : ∀ j ≤ m,
      M.runFrom (W_of (a, m)) (1, L_of a, 0, 0, Universal.init d) j =
        (1, L_of a, j, 0, Universal.init d) ∧
      (∀ t < j,
        M.halted (M.runFrom (W_of (a, m)) (1, L_of a, 0, 0, Universal.init d) t) = false) ∧
      ((List.range j).map fun t ↦
        M.emit (M.runFrom (W_of (a, m)) (1, L_of a, 0, 0, Universal.init d) t,
          M.read (W_of (a, m))
            (M.runFrom (W_of (a, m)) (1, L_of a, 0, 0, Universal.init d) t))).flatten = [] := by
    intro j hj; induction j with
    | zero => simp [M, rangeQM]
    | succ j ih =>
      obtain ⟨hrun, hnh, hout⟩ := ih (by omega)
      have hread : M.read (W_of (a, m)) (1, L_of a, j, 0, Universal.init d) = some true := by
        simp only [M, QueryMachine.read, rangeQM, Nat.one_ne_zero, ↓reduceIte, hW_eq]
        rw [List.getElem?_append_right (by rw [length_frame]; dsimp [L_of]; omega)]
        simp [length_frame, L_of, show j < m by omega]
      have hstep : M.step (W_of (a, m)) (1, L_of a, j, 0, Universal.init d) =
          (1, L_of a, j + 1, 0, Universal.init d) := by rw [QueryMachine.step, hread]; rfl
      refine ⟨by rw [QueryMachine.runFrom_succ, hrun, hstep], fun t ht ↦ ?_, ?_⟩
      · rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp ht) with hlt | rfl
        · exact hnh t hlt
        · rw [hrun]; rfl
      · rw [List.range_succ, List.map_append, List.flatten_append, hout, List.map_singleton,
          List.flatten_singleton, hrun]; rfl
  have hRound (a : α) (m i : ℕ) (hi : i < m) :
      let xi := W_of (a, i)
      let T := uf (a, i)
      (∀ r ≤ T,
        M.runFrom (W_of (a, m)) (2, L_of a, m, i, Universal.init d) r =
          (2, L_of a, m, i, Universal.run d (xi.map Universal.eBit) r)) ∧
      M.runFrom (W_of (a, m)) (2, L_of a, m, i, Universal.init d) (T + 1) =
        (if i + 1 < m then 2 else 3, L_of a, m, i + 1, Universal.init d) ∧
      (∀ r < T + 1,
        M.halted (M.runFrom (W_of (a, m)) (2, L_of a, m, i, Universal.init d) r) = false) ∧
      ((List.range (T + 1)).map fun r ↦
        M.emit (M.runFrom (W_of (a, m)) (2, L_of a, m, i, Universal.init d) r,
          M.read (W_of (a, m))
            (M.runFrom (W_of (a, m)) (2, L_of a, m, i, Universal.init d) r))).flatten =
        frame (encOut (f (a, i))) := by
    intro xi T
    have hhalt_iff := Universal.run_desc_halted ⟨ef, hef⟩ tmf xi (huf (a, i))
    have hSimRun : ∀ r ≤ T,
        M.runFrom (W_of (a, m)) (2, L_of a, m, i, Universal.init d) r =
          (2, L_of a, m, i, Universal.run d (xi.map Universal.eBit) r) := by
      intro r hr; induction r with
      | zero => rfl
      | succ r ih =>
        rw [QueryMachine.runFrom_succ, ih (by omega)]
        have hnh : (Universal.run d (xi.map Universal.eBit) r).state.isNone = false := by
          rw [Bool.eq_false_iff, ne_eq, Option.isNone_iff_eq_none, hhalt_iff]; omega
        have hsym := symOf_eq_inputSymbol (encIn a) m i hi.le
          (Universal.run d (xi.map Universal.eBit) r)
        have hSt : M.step (W_of (a, m))
            (2, L_of a, m, i, Universal.run d (xi.map Universal.eBit) r) =
            (2, L_of a, m, i, (Universal.stepWith d (Universal.run d (xi.map Universal.eBit) r)
              (symOf (2, 2 * (encIn a).length + 1, m, i,
                Universal.run d (xi.map Universal.eBit) r)
                (frame (encIn a) ++ List.replicate m true)[
                  (Universal.run d (xi.map Universal.eBit) r).inputPos - 1]?)).1) := by
          change (if (Universal.run d (xi.map Universal.eBit) r).state.isNone = true then
            (if i + 1 < m then (2, L_of a, m, i + 1, Universal.init d)
             else (3, L_of a, m, i + 1, Universal.init d))
            else (2, L_of a, m, i, _)) = _; rw [hnh]; rfl
        have hxi_def : frame (encIn a) ++ List.replicate i true = xi := rfl
        rw [hSt, hsym, hxi_def, ← Universal.step_eq_stepWith, ← Universal.run_succ]
    have hEnd : M.runFrom (W_of (a, m)) (2, L_of a, m, i, Universal.init d) (T + 1) =
        (if i + 1 < m then 2 else 3, L_of a, m, i + 1, Universal.init d) := by
      rw [QueryMachine.runFrom_succ, hSimRun T le_rfl]
      have hh : (Universal.run d (xi.map Universal.eBit) T).state.isNone = true :=
        Option.isNone_iff_eq_none.mpr ((hhalt_iff T).mpr le_rfl)
      change (if (Universal.run d (xi.map Universal.eBit) T).state.isNone = true then
        (if i + 1 < m then (2, L_of a, m, i + 1, Universal.init d)
         else (3, L_of a, m, i + 1, Universal.init d))
        else (2, L_of a, m, i,
          (Universal.stepWith d (Universal.run d (xi.map Universal.eBit) T)
            (symOf (2, L_of a, m, i, Universal.run d (xi.map Universal.eBit) T)
              (M.read (W_of (a, m))
                (2, L_of a, m, i, Universal.run d (xi.map Universal.eBit) T)))).1)) = _
      rw [hh]; simp only [↓reduceIte]; split_ifs <;> rfl
    have hNotHalt : ∀ r < T + 1,
        M.halted (M.runFrom (W_of (a, m)) (2, L_of a, m, i, Universal.init d) r) = false := by
      intro r hr; rw [hSimRun r (Nat.lt_succ_iff.mp hr)]; rfl
    have hOut : ((List.range (T + 1)).map fun r ↦
        M.emit (M.runFrom (W_of (a, m)) (2, L_of a, m, i, Universal.init d) r,
          M.read (W_of (a, m))
            (M.runFrom (W_of (a, m)) (2, L_of a, m, i, Universal.init d) r))).flatten =
        frame (encOut (f (a, i))) := by
      rw [List.range_succ, List.map_append, List.flatten_append]
      have hLast : M.emit (M.runFrom (W_of (a, m)) (2, L_of a, m, i, Universal.init d) T,
          M.read (W_of (a, m))
            (M.runFrom (W_of (a, m)) (2, L_of a, m, i, Universal.init d) T)) = [false] := by
        rw [hSimRun T le_rfl]
        have hh : (Universal.run d (xi.map Universal.eBit) T).state.isNone = true :=
          Option.isNone_iff_eq_none.mpr ((hhalt_iff T).mpr le_rfl)
        change (if (Universal.run d (xi.map Universal.eBit) T).state.isNone = true then [false]
          else emitSym _) = [false]; rw [hh]; rfl
      have hBody : ((List.range T).map fun r ↦
          M.emit (M.runFrom (W_of (a, m)) (2, L_of a, m, i, Universal.init d) r,
            M.read (W_of (a, m))
              (M.runFrom (W_of (a, m)) (2, L_of a, m, i, Universal.init d) r))).flatten =
          doubled (encOut (f (a, i))) := by
        have hMapEq : ((List.range T).map fun r ↦
            M.emit (M.runFrom (W_of (a, m)) (2, L_of a, m, i, Universal.init d) r,
              M.read (W_of (a, m))
                (M.runFrom (W_of (a, m)) (2, L_of a, m, i, Universal.init d) r))) =
            (List.range T).map fun r ↦ emitSym (Universal.step d (xi.map Universal.eBit)
              (Universal.run d (xi.map Universal.eBit) r)).2 := by
          refine List.map_congr_left fun r hr ↦ ?_
          rw [hSimRun r (List.mem_range.mp hr).le]
          have hnh : (Universal.run d (xi.map Universal.eBit) r).state.isNone = false := by
            rw [Bool.eq_false_iff, ne_eq, Option.isNone_iff_eq_none, hhalt_iff]
            have := List.mem_range.mp hr; omega
          have hsym := symOf_eq_inputSymbol (encIn a) m i hi.le
            (Universal.run d (xi.map Universal.eBit) r)
          have hxi_def : frame (encIn a) ++ List.replicate i true = xi := rfl
          change (if (Universal.run d (xi.map Universal.eBit) r).state.isNone = true then [false]
            else emitSym (Universal.stepWith d (Universal.run d (xi.map Universal.eBit) r)
              (symOf (2, 2 * (encIn a).length + 1, m, i,
                Universal.run d (xi.map Universal.eBit) r)
                (frame (encIn a) ++ List.replicate m true)[
                  (Universal.run d (xi.map Universal.eBit) r).inputPos - 1]?)).2) = _
          rw [hnh]; simp only [Bool.false_eq_true, ↓reduceIte]
          rw [hsym, hxi_def, ← Universal.step_eq_stepWith]
        rw [hMapEq]
        have hFlatSym : ∀ os : List (Option ℕ), (os.map emitSym).flatten =
            (os.map Option.toList).flatten.flatMap fun n ↦ [true, decide (n ≠ 0)] := fun os ↦ by
          induction os with | nil => rfl | cons o os ih => cases o <;> simp [emitSym, ih]
        have hCompMap : ((List.range T).map fun r ↦ emitSym (Universal.step d
            (xi.map Universal.eBit) (Universal.run d (xi.map Universal.eBit) r)).2) =
            ((List.range T).map fun r ↦ (Universal.step d (xi.map Universal.eBit)
              (Universal.run d (xi.map Universal.eBit) r)).2).map emitSym := by
          rw [List.map_map]; rfl
        rw [hCompMap, hFlatSym, List.map_map]
        have hSimEq : ((List.range T).map (Option.toList ∘ fun r ↦
            (Universal.step d (xi.map Universal.eBit)
              (Universal.run d (xi.map Universal.eBit) r)).2)).flatten =
            (encOut (f (a, i))).map Universal.eBit :=
          (congrArg Prod.fst (Universal.simulate_eq d (xi.map Universal.eBit) T)).symm.trans
            (Universal.simulate_desc_output ⟨ef, hef⟩ tmf xi (htmf (a, i)).1 (huf (a, i)))
        rw [hSimEq, List.flatMap_map]; unfold doubled
        exact List.flatMap_congr fun bit _ ↦ by cases bit <;> rfl
      rw [hBody, List.map_singleton, List.flatten_singleton, hLast, ← frame_eq_doubled]
    exact ⟨hSimRun, hEnd, hNotHalt, hOut⟩
  let initLen := (Universal.eCfg (Universal.init d)).length
  let K_cfg := (12 * Universal.descLen d + 40) * (2 * cf + 3) + initLen + 1
  have hCfgBound (a : α) (m i : ℕ) (hi : i ≤ m) (r : ℕ) :
      (Universal.eCfg (Universal.run d ((W_of (a, i)).map Universal.eBit) r)).length ≤
        K_cfg * (Nat.log2 (W_of (a, m)).length + 1) := by
    have hxiLen : (W_of (a, i)).length ≤ (W_of (a, m)).length := by
      rw [hW_len, hW_len]; omega
    have h1 := Universal.length_eCfg_le_cfgSpace d ((W_of (a, i)).map Universal.eBit) (le_refl r)
    have h2 := Universal.cfgSpace_desc_le ⟨ef, hef⟩ tmf (W_of (a, i)) (htmf (a, i)).2.2 r
    have hlog1 : (encNat ((W_of (a, i)).length + 1)).length ≤
        Nat.log2 (W_of (a, m)).length + 2 :=
      length_encNat_le_log2_add_two (Nat.add_le_add_right hxiLen 1)
    have hlog2 : Nat.log2 (W_of (a, i)).length + 1 ≤
        (encNat ((W_of (a, i)).length + 1)).length :=
      log2_succ_le_length_encNat _
    have h3 : cf * (Nat.log2 (W_of (a, i)).length + 1) +
        (encNat ((W_of (a, i)).length + 1)).length + 1 ≤
        (2 * cf + 3) * (Nat.log2 (W_of (a, m)).length + 1) := by nlinarith
    calc (Universal.eCfg (Universal.run d ((W_of (a, i)).map Universal.eBit) r)).length
        ≤ (12 * Universal.descLen d + 40) *
            (cf * (Nat.log2 (W_of (a, i)).length + 1) +
              (encNat ((W_of (a, i)).length + 1)).length + 1) := h1.trans h2
      _ ≤ (12 * Universal.descLen d + 40) *
            ((2 * cf + 3) * (Nat.log2 (W_of (a, m)).length + 1)) := Nat.mul_le_mul_left _ h3
      _ ≤ K_cfg * (Nat.log2 (W_of (a, m)).length + 1) := by dsimp [K_cfg]; nlinarith
  let stateBound (a : α) (m : ℕ) : ℕ :=
    (64 + 16 * K_cfg) * (Nat.log2 (W_of (a, m)).length + 1)
  have hEncRStBound (a : α) (m : ℕ) {ph k m' i : ℕ} {cfg : Universal.SCfg}
      (hph : ph ≤ 3) (hk : k ≤ (W_of (a, m)).length) (hm' : m' ≤ (W_of (a, m)).length)
      (hi : i ≤ (W_of (a, m)).length)
      (hcfg : (Universal.eCfg cfg).length ≤ K_cfg * (Nat.log2 (W_of (a, m)).length + 1)) :
      (encRSt (ph, k, m', i, cfg)).length ≤ stateBound a m := by
    have hphL := length_encNat_le_of_lt_two_pow (by omega : ph < 2 ^ 2)
    have hkL := length_encNat_le_log2 hk; have hmL := length_encNat_le_log2 hm'
    have hiL := length_encNat_le_log2 hi
    simp only [encRSt, length_encPair]
    change _ ≤ (64 + 16 * K_cfg) * (Nat.log2 (W_of (a, m)).length + 1); nlinarith
  have hInitCfgLe (a : α) (m : ℕ) :
      (Universal.eCfg (Universal.init d)).length ≤ K_cfg * (Nat.log2 (W_of (a, m)).length + 1) :=
    (Nat.le_add_left initLen _).trans
      ((Nat.le_add_right _ 1).trans (Nat.le_mul_of_pos_right _ (Nat.succ_pos _)))
  have hAllRuns (p : α × ℕ) : ∃ T : ℕ, M.halted (M.run (W_of p) T) = true ∧
      (∀ t < T, M.halted (M.run (W_of p) t) = false) ∧
      encList encOut ((List.range p.2).map fun i ↦ f (p.1, i)) = M.output (W_of p) T ∧
      (∀ t ≤ T, (encRSt (M.run (W_of p) t)).length ≤ stateBound p.1 p.2) := by
    rcases p with ⟨a, m⟩
    obtain ⟨hP0Run, hP0NH, hP0Out⟩ := hPhase0End a m
    have hP0Space : ∀ t ≤ (encIn a).length + 1,
        (encRSt (M.runFrom (W_of (a, m)) M.init t)).length ≤ stateBound a m := fun t ht ↦ by
      rcases lt_or_eq_of_le ht with hlt | rfl
      · rw [(hPhase0 a m t (Nat.lt_succ_iff.mp hlt)).1]
        exact hEncRStBound a m (by omega) (by rw [hW_len]; dsimp [L_of]; omega)
          (Nat.zero_le _) (Nat.zero_le _) (hInitCfgLe a m)
      · rw [hP0Run]
        exact hEncRStBound a m (by omega) (by rw [hW_len]; omega)
          (Nat.zero_le _) (Nat.zero_le _) (hInitCfgLe a m)
    rcases Nat.eq_zero_or_pos m with rfl | hmPos
    · have hread1 : M.read (W_of (a, 0)) (1, L_of a, 0, 0, Universal.init d) = none := by
        simp only [M, QueryMachine.read, rangeQM, Nat.one_ne_zero, ↓reduceIte]
        exact List.getElem?_eq_none (by rw [hW_len])
      let T := (encIn a).length + 1 + 1
      have hRunT : M.run (W_of (a, 0)) T = (3, L_of a, 0, 0, Universal.init d) := by
        change M.runFrom (W_of (a, 0)) M.init T = _
        rw [QueryMachine.runFrom_add, hP0Run, QueryMachine.runFrom_succ, QueryMachine.runFrom_zero,
          QueryMachine.step, hread1]; rfl
      have hNHT : ∀ t < T, M.halted (M.run (W_of (a, 0)) t) = false := fun t ht ↦ by
        rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp ht) with hlt | rfl
        · exact hP0NH t hlt
        · change M.halted (M.runFrom (W_of (a, 0)) M.init ((encIn a).length + 1)) = false
          rw [hP0Run]; rfl
      refine ⟨T, by rw [hRunT]; rfl, hNHT, ?_, fun t ht ↦ ?_⟩
      · rw [M.output_eq_of_not_halted _ hNHT]
        change [] = ((List.range T).map fun i ↦ M.emit (M.runFrom (W_of (a, 0)) M.init i,
          M.read (W_of (a, 0)) (M.runFrom (W_of (a, 0)) M.init i))).flatten ++
          M.finish (M.run (W_of (a, 0)) T)
        rw [runFrom_output_add M (W_of (a, 0)) M.init ((encIn a).length + 1) 1, hP0Out, hP0Run]
        rfl
      · rcases lt_or_eq_of_le ht with hlt | rfl
        · exact hP0Space t (Nat.lt_succ_iff.mp hlt)
        · rw [hRunT]
          exact hEncRStBound a 0 le_rfl (by rw [hW_len]) (Nat.zero_le _) (Nat.zero_le _)
            (hInitCfgLe a 0)
    · obtain ⟨hP1Run, hP1NH, hP1Out⟩ := hPhase1 a m m le_rfl
      have hread1 : M.read (W_of (a, m)) (1, L_of a, m, 0, Universal.init d) = none := by
        simp only [M, QueryMachine.read, rangeQM, Nat.one_ne_zero, ↓reduceIte]
        exact List.getElem?_eq_none (by rw [hW_len])
      have hP1EndRun : M.runFrom (W_of (a, m)) (1, L_of a, 0, 0, Universal.init d) (m + 1) =
          (2, L_of a, m, 0, Universal.init d) := by
        rw [QueryMachine.runFrom_succ, hP1Run, QueryMachine.step, hread1]
        simp [M, rangeQM, hmPos.ne']
      have hP1EndNH : ∀ t < m + 1,
          M.halted (M.runFrom (W_of (a, m)) (1, L_of a, 0, 0, Universal.init d) t) = false :=
        fun t ht ↦ by
          rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp ht) with hlt | rfl
          · exact hP1NH t hlt
          · rw [hP1Run]; rfl
      have hP1EndOut : ((List.range (m + 1)).map fun t ↦
          M.emit (M.runFrom (W_of (a, m)) (1, L_of a, 0, 0, Universal.init d) t,
            M.read (W_of (a, m))
              (M.runFrom (W_of (a, m)) (1, L_of a, 0, 0, Universal.init d) t))).flatten = [] := by
        rw [List.range_succ, List.map_append, List.flatten_append, hP1Out, List.map_singleton,
          List.flatten_singleton, hP1Run]; rfl
      have hP1EndSpace : ∀ t ≤ m + 1,
          (encRSt (M.runFrom (W_of (a, m)) (1, L_of a, 0, 0, Universal.init d) t)).length ≤
            stateBound a m := fun t ht ↦ by
        rcases lt_or_eq_of_le ht with hlt | rfl
        · rw [(hPhase1 a m t (Nat.lt_succ_iff.mp hlt)).1]
          exact hEncRStBound a m (by omega) (by rw [hW_len]; omega)
            (by rw [hW_len]; omega) (Nat.zero_le _) (hInitCfgLe a m)
        · rw [hP1EndRun]
          exact hEncRStBound a m (by omega) (by rw [hW_len]; omega)
            (by rw [hW_len]; omega) (Nat.zero_le _) (hInitCfgLe a m)
      have hLoop : ∀ k ≤ m, ∃ Tk : ℕ,
          M.runFrom (W_of (a, m)) (2, L_of a, m, 0, Universal.init d) Tk =
            (if k = 0 ∨ k < m then 2 else 3, L_of a, m, k, Universal.init d) ∧
          (∀ t < Tk,
            M.halted (M.runFrom (W_of (a, m)) (2, L_of a, m, 0, Universal.init d) t) = false) ∧
          ((List.range Tk).map fun t ↦
            M.emit (M.runFrom (W_of (a, m)) (2, L_of a, m, 0, Universal.init d) t,
              M.read (W_of (a, m))
                (M.runFrom (W_of (a, m)) (2, L_of a, m, 0, Universal.init d) t))).flatten =
            encList encOut ((List.range k).map fun i ↦ f (a, i)) ∧
          (∀ t ≤ Tk,
            (encRSt (M.runFrom (W_of (a, m)) (2, L_of a, m, 0, Universal.init d) t)).length ≤
              stateBound a m) := by
        intro k hk
        induction k with
        | zero =>
          refine ⟨0, by simp, fun _ h ↦ absurd h (by omega), rfl, fun t ht ↦ ?_⟩
          obtain rfl : t = 0 := by omega
          exact hEncRStBound a m (by omega) (by rw [hW_len]; omega)
            (by rw [hW_len]; omega) (Nat.zero_le _) (hInitCfgLe a m)
        | succ k ih =>
          obtain ⟨Tk, hTkRun, hTkNH, hTkOut, hTkSpace⟩ := ih (by omega)
          have hkm : k < m := by omega
          have hIfEq : (if k = 0 ∨ k < m then 2 else 3) = 2 := by simp [hkm]
          rw [hIfEq] at hTkRun
          obtain ⟨hRSim, hREnd, hRNH, hROut⟩ := hRound a m k hkm
          refine ⟨Tk + (uf (a, k) + 1), ?_, fun t ht ↦ ?_, ?_, fun t ht ↦ ?_⟩
          · rw [QueryMachine.runFrom_add, hTkRun, hREnd]
            simp
          · rcases lt_or_ge t Tk with hlt | hge
            · exact hTkNH t hlt
            · rw [show t = Tk + (t - Tk) by omega, QueryMachine.runFrom_add, hTkRun]
              exact hRNH (t - Tk) (by omega)
          · rw [runFrom_output_add M (W_of (a, m)) _ Tk (uf (a, k) + 1), hTkOut, hTkRun, hROut,
              List.range_succ, List.map_append, List.map_singleton, encList_append, encList_cons,
              encList_nil, List.append_nil]
          · rcases le_or_gt t Tk with hle | hgt
            · exact hTkSpace t hle
            · rw [show t = Tk + (t - Tk) by omega, QueryMachine.runFrom_add, hTkRun]
              rcases lt_or_eq_of_le (show t - Tk ≤ uf (a, k) + 1 by omega) with hlt | heq
              · rw [hRSim (t - Tk) (Nat.lt_succ_iff.mp hlt)]
                exact hEncRStBound a m (by omega) (by rw [hW_len]; omega)
                  (by rw [hW_len]; omega) (by rw [hW_len]; omega)
                  (hCfgBound a m k hkm.le (t - Tk))
              · rw [heq, hREnd]
                exact hEncRStBound a m (by split_ifs <;> omega) (by rw [hW_len]; omega)
                  (by rw [hW_len]; omega) (by rw [hW_len]; omega) (hInitCfgLe a m)
      obtain ⟨Tm, hTmRun, hTmNH, hTmOut, hTmSpace⟩ := hLoop m le_rfl
      rw [show (if m = 0 ∨ m < m then 2 else 3) = 3 by simp [hmPos.ne']] at hTmRun
      let T0 := (encIn a).length + 1; let T1 := m + 1; let T := T0 + T1 + Tm
      have hPre01Run : M.runFrom (W_of (a, m)) M.init (T0 + T1) =
          (2, L_of a, m, 0, Universal.init d) := by
        rw [QueryMachine.runFrom_add, hP0Run, hP1EndRun]
      have hPre01NH : ∀ t < T0 + T1, M.halted (M.runFrom (W_of (a, m)) M.init t) = false :=
        fun t ht ↦ by
          rcases lt_or_ge t T0 with hlt | hge
          · exact hP0NH t hlt
          · rw [show t = T0 + (t - T0) by omega, QueryMachine.runFrom_add, hP0Run]
            exact hP1EndNH (t - T0) (by omega)
      have hPre01Out : ((List.range (T0 + T1)).map fun t ↦
          M.emit (M.runFrom (W_of (a, m)) M.init t,
            M.read (W_of (a, m)) (M.runFrom (W_of (a, m)) M.init t))).flatten = [] := by
        rw [runFrom_output_add M (W_of (a, m)) M.init T0 T1, hP0Out, hP0Run, hP1EndOut]; rfl
      have hRunTotal : M.run (W_of (a, m)) T = (3, L_of a, m, m, Universal.init d) := by
        change M.runFrom (W_of (a, m)) M.init (T0 + T1 + Tm) = _
        rw [QueryMachine.runFrom_add, hPre01Run, hTmRun]
      have hNHTotal : ∀ t < T, M.halted (M.run (W_of (a, m)) t) = false := fun t ht ↦ by
        rcases lt_or_ge t (T0 + T1) with hlt | hge
        · exact hPre01NH t hlt
        · change M.halted (M.runFrom (W_of (a, m)) M.init t) = false
          rw [show t = (T0 + T1) + (t - (T0 + T1)) by omega, QueryMachine.runFrom_add, hPre01Run]
          exact hTmNH _ (by omega)
      refine ⟨T, by rw [hRunTotal]; rfl, hNHTotal, ?_, fun t ht ↦ ?_⟩
      · rw [M.output_eq_of_not_halted _ hNHTotal]
        change _ = ((List.range ((T0 + T1) + Tm)).map fun i ↦
          M.emit (M.runFrom (W_of (a, m)) M.init i,
            M.read (W_of (a, m)) (M.runFrom (W_of (a, m)) M.init i))).flatten ++
          M.finish (M.run (W_of (a, m)) T)
        rw [runFrom_output_add M (W_of (a, m)) M.init (T0 + T1) Tm, hPre01Out, hPre01Run, hTmOut]
        simp [M, rangeQM]
      · change (encRSt (M.runFrom (W_of (a, m)) M.init t)).length ≤ stateBound a m
        rcases le_or_gt t T0 with hle0 | hgt0
        · exact hP0Space t hle0
        · rcases le_or_gt t (T0 + T1) with hle1 | hgt1
          · rw [show t = T0 + (t - T0) by omega, QueryMachine.runFrom_add, hP0Run]
            exact hP1EndSpace (t - T0) (by omega)
          · rw [show t = (T0 + T1) + (t - (T0 + T1)) by omega, QueryMachine.runFrom_add, hPre01Run]
            exact hTmSpace (t - (T0 + T1)) (by omega)
  choose time hhalt hpre hout hspace using hAllRuns
  exact M.computableInLogSpace
    (rangeQM_query_inSpace d) (rangeQM_next_inSpace d) (rangeQM_emit_inSpace d)
    (rangeQM_halted_inSpace d) (ComputableInSpace.budget_const [])
    time hhalt hpre hout ⟨64 + 16 * K_cfg, fun p t ht ↦ hspace p t ht⟩

/-- Composed unbounded-range batch evaluation in logarithmic space. -/
theorem computableInLogSpace_map_range' {α β : Type} {encIn : α ↪ List Bool}
    {encOut : β ↪ List Bool} {r : α → ℕ} {f : α × ℕ → β}
    (hr : ComputableInLogSpace r encIn encUnary)
    (hf : ComputableInLogSpace f (encPair encIn encUnary) encOut) :
    ComputableInLogSpace (fun a : α ↦ (List.range (r a)).map fun i ↦ f (a, i))
      encIn (encList encOut) :=
  (computableInLogSpace_map_range hf).comp (ComputableInLogSpace.pair .id hr)

private def flattenFramedT : Transducer Bool Bool where
  q₀ := false
  step
    | false, true => (true, [])
    | false, false => (false, [])
    | true, b => (false, [b])
  final _ := []
  length_step_le q b := by cases q <;> cases b <;> simp
  length_final_le _ := by simp

private lemma flattenFramedT_run_frame (w rest : List Bool) :
    flattenFramedT.run false (frame w ++ rest) = w ++ flattenFramedT.run false rest := by
  induction w with
  | nil => rfl
  | cons b w ih => simpa [frame_cons, Transducer.run_cons, flattenFramedT] using ih

private lemma computableInLogSpace_listFlattenBits :
    ComputableInLogSpace List.flatten (encList encBits) encBits :=
  flattenFramedT.computableInLogSpace fun xss ↦ by
    induction xss with
    | nil => rfl
    | cons xs xss ih =>
      change xs ++ xss.flatten = flattenFramedT.run false (frame xs ++ encList encBits xss)
      rw [flattenFramedT_run_frame]
      exact congrArg (xs ++ ·) ih

private lemma computableInLogSpace_unframeBoolList :
    ComputableInLogSpace (fun bs : List Bool ↦ bs) (encList encBool) encBits :=
  flattenFramedT.computableInLogSpace fun bs ↦ by
    induction bs with
    | nil => rfl
    | cons b bs ih =>
      change b :: bs = flattenFramedT.run false (frame [b] ++ encList encBool bs)
      rw [flattenFramedT_run_frame]
      exact congrArg (b :: ·) ih

/-- Unbounded-range Boolean batch evaluation into a raw bit word in logarithmic space. -/
theorem computableInLogSpace_mapToBits_range {α : Type} {encIn : α ↪ List Bool}
    {r : α → ℕ} {f : α × ℕ → Bool}
    (hr : ComputableInLogSpace r encIn encUnary)
    (hf : ComputableInLogSpace f (encPair encIn encUnary) encBool) :
    ComputableInLogSpace (fun a : α ↦ (List.range (r a)).map fun i ↦ f (a, i))
      encIn encBits :=
  computableInLogSpace_unframeBoolList.comp (computableInLogSpace_map_range' hr hf)

/-- Parameterized list mapping in logarithmic space. -/
theorem computableInLogSpace_listMap {α β γ : Type} {encIn : α ↪ List Bool}
    {encB : β ↪ List Bool} {encOut : γ ↪ List Bool}
    {l : α → List β} {f : α × β → γ}
    (hl : ComputableInLogSpace l encIn (encList encB))
    (hf : ComputableInLogSpace f (encPair encIn encB) encOut) :
    ComputableInLogSpace (fun a : α ↦ (l a).map fun b ↦ f (a, b))
      encIn (encList encOut) := by
  let isNil : α → Bool := fun a ↦ (encList encB (l a)).isEmpty
  have hisNil : ComputableInLogSpace isNil encIn encBool :=
    (ComputableInLogSpace.of_isEmpty (encIn := encList encB) (f :=
      fun xs ↦ (encList encB xs).isEmpty)
      fun _ ↦ rfl).comp hl
  let NonNil := {a : α // isNil a = false}
  let encNonNil : NonNil ↪ List Bool := (Function.Embedding.subtype _).trans encIn
  have hNonempty : ∀ x : NonNil, l x.1 ≠ [] := fun ⟨a, ha⟩ hEq ↦ by
    simp [isNil, hEq] at ha
  let headOf : NonNil → β := fun x ↦
    match h : l x.1 with
    | b :: _ => b
    | [] => absurd h (hNonempty x)
  have hHead : ComputableInLogSpace headOf encNonNil encB :=
    (ComputableInLogSpace.of_unframe (encIn := encList encB) (encOut := encBits)
      (f := fun xs ↦ unframe (encList encB xs)) fun _ ↦ rfl).comp (hl.restrict _) |>.congr
      fun x ↦ by
        dsimp only [headOf, Function.comp_apply]
        split
        · rename_i b bs hEq
          simp [hEq]
        · rename_i hEq
          exact absurd hEq (hNonempty x)
  let elemAt : NonNil × ℕ → β := fun p ↦ ((l p.1.1)[p.2]?).getD (headOf p.1)
  have hOpt : ComputableInLogSpace (fun p : NonNil × ℕ ↦ (l p.1.1)[p.2]?)
      (encPair encNonNil encUnary) (encOption encB) :=
    ComputableInLogSpace.getElem?'
      ((hl.restrict _).comp (ComputableInLogSpace.fst encNonNil encUnary))
      (ComputableInLogSpace.snd encNonNil encUnary)
  have hOptEmpty : ComputableInLogSpace
      (fun p : NonNil × ℕ ↦ (encOption encB (l p.1.1)[p.2]?).isEmpty)
      (encPair encNonNil encUnary) encBool :=
    (ComputableInLogSpace.of_isEmpty (encIn := encOption encB)
      (f := fun o ↦ (encOption encB o).isEmpty) fun _ ↦ rfl).comp hOpt
  have hElemAt : ComputableInLogSpace elemAt (encPair encNonNil encUnary) encB := by
    refine (ComputableInLogSpace.ite_subtype (f := headOf ∘ Prod.fst) (g := elemAt) hOptEmpty
      ((hHead.comp (ComputableInLogSpace.fst encNonNil encUnary)).restrict _)
      (((ComputableInLogSpace.of_tail (encIn := encOption encB) (encOut := encBits)
        (f := fun o ↦ (encOption encB o).tail) fun _ ↦ rfl).comp (hOpt.restrict _)).congr
        fun ⟨p, hp⟩ ↦ ?_)).congr_fun fun p ↦ ?_
    · cases h : (l p.1.1)[p.2]? with
      | none => rw [h] at hp; simp at hp
      | some b => simp [h, elemAt]
    · cases h : (l p.1.1)[p.2]? <;> simp [h, elemAt]
  have hLen : ComputableInLogSpace (fun x : NonNil ↦ (l x.1).length) encNonNil encUnary :=
    ComputableInLogSpace.listLength.comp (hl.restrict _)
  have hCall : ComputableInLogSpace (fun p : NonNil × ℕ ↦ f (p.1.1, elemAt p))
      (encPair encNonNil encUnary) encOut :=
    hf.comp (ComputableInLogSpace.pair
      ((ComputableInLogSpace.of_eq (f := Subtype.val) fun _ ↦ rfl).comp
        (ComputableInLogSpace.fst encNonNil encUnary))
      hElemAt)
  have hBranchNonNil : ComputableInLogSpace
      (fun x : NonNil ↦ (l x.1).map fun b ↦ f (x.1, b)) encNonNil (encList encOut) :=
    (computableInLogSpace_map_range' hLen hCall).congr_fun fun x ↦ by
      refine List.ext_getElem (by simp) fun i h1 h2 ↦ ?_
      have hi : i < (l x.1).length := by simpa using h1
      simp [elemAt, List.getElem?_eq_getElem hi]
  refine (ComputableInLogSpace.ite_subtype (f := fun _ : α ↦ ([] : List γ))
    (g := fun a : α ↦ (l a).map fun b ↦ f (a, b)) hisNil
    ((ComputableInLogSpace.const ([] : List γ)).restrict _)
    hBranchNonNil).congr_fun fun a ↦ ?_
  by_cases h : isNil a = true
  · have hEq : l a = [] := by
      cases hla : l a
      · rfl
      · simp [isNil, hla] at h
    simp [h, hEq]
  · simp [Bool.eq_false_iff.mpr h]

end RangeMap

end CslibFrontier.LogSpace

end
