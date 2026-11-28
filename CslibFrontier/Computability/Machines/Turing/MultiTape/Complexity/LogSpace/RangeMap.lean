module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.Words
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.CounterProgram.Output
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.CounterProgram.Unary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.ConfigurationGraph.Expr
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.ConfigurationGraph.Bounds
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.ConfigurationGraph.Deterministic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Nondeterministic
import CslibFrontier.Computability.Machines.Turing.MultiTape.HaltsAt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Universal Log-Space Range-Map and Bounded Quantifier Combinators

This module constructs a universal 21-instruction `Turing.CounterProgram` simulating any
deterministic log-space `MultiTapeTM` over virtual inputs `encPair encIn encUnary (a, i)` for
`i = 0, …, bound a - 1`, where `bound : α → ℕ` is itself computable in logarithmic space with
unary output. Combining this universal range-map combinator with finite-state bit-word reductions
(`bitsAny`, `bitsAll`) yields closure of deterministic logarithmic space under unary-bounded
existential and universal quantification.

## Main results

* `CslibFrontier.Computability.LogSpace.computableInLogSpace_map_range_bool`: universal log-space
  range-map combinator `a ↦ (List.range (bound a)).map fun i => P (a, i)`.
* `CslibFrontier.Computability.LogSpace.computableInLogSpace_any_range`: log-space unary-bounded
  existential quantification over `0, …, bound a - 1`.
* `CslibFrontier.Computability.LogSpace.computableInLogSpace_all_range`: log-space unary-bounded
  universal quantification over `0, …, bound a - 1`.
-/

public section

namespace CslibFrontier.Computability.LogSpace

open Turing Turing.MultiTapeTM Turing.MultiTapeNTM Turing.MultiTapeNTM.ConfigurationGraph
open Turing.CounterProgram Turing.CounterProgram.Expr Turing.CounterProgram.Instr

section MapRangeBool

variable {k : ℕ} {State : Type} [Fintype State]

/-- Deterministic next-configuration ID expression on the compact configuration graph of `tm`. -/
private noncomputable def stepIDExpr (tm : MultiTapeTM k Bool State) (B L u sym : Expr) : Expr :=
  (instructions tm.toMultiTapeNTM).foldr
    (fun t acc =>
      iteB (matchesExpr L (readRegistersExpr B u) sym t)
        (packExpr B (nextExpr L (readRegistersExpr B u) t.2.2.2))
        acc)
    u

private theorem eval_foldr_stepID (ts : List (Instruction k State))
    (regs : List ℕ) (B L u sym : Expr) (g : Register k → ℕ) (symbol : Option Bool) (target : ℕ)
    (hr : ∀ i, (readRegistersExpr B u i).eval regs = g i)
    (hs : sym.eval regs = symbolCode symbol)
    (hmatch : ∀ t ∈ ts, matchesEntry (L.eval regs) g symbol t = true →
      Cslib.Radix.pack (B.eval regs) (nextRegisters (L.eval regs) g t.2.2.2) = target)
    (hex : ∃ t ∈ ts, matchesEntry (L.eval regs) g symbol t = true) :
    (ts.foldr
      (fun t acc =>
        iteB (matchesExpr L (readRegistersExpr B u) sym t)
          (packExpr B (nextExpr L (readRegistersExpr B u) t.2.2.2))
          acc)
      u).eval regs = target := by
  induction ts with
  | nil => obtain ⟨_, h, _⟩ := hex; exact absurd h (by simp)
  | cons t ts ih =>
    simp only [List.foldr_cons]
    rw [eval_iteB (eval_matchesExpr hr hs t)]
    by_cases hm : matchesEntry (L.eval regs) g symbol t = true
    · simp only [hm, ↓reduceIte]
      rw [eval_packExpr (eval_nextExpr hr _)]
      exact hmatch t List.mem_cons_self hm
    · simp only [hm, Bool.false_eq_true, ↓reduceIte]
      obtain ⟨t', ht', hm'⟩ := hex
      rcases List.mem_cons.mp ht' with rfl | ht'
      · exact absurd hm' hm
      · exact ih (fun x hx => hmatch x (List.mem_cons_of_mem _ hx)) ⟨t', ht', hm'⟩

private theorem eval_stepIDExpr (tm : MultiTapeTM k Bool State) {regs : List ℕ}
    {B L u sym : Expr} {B' : ℕ} {w : List Bool} {v v' : FiniteCfg k Bool State} {q : State}
    (hB : B.eval regs = B') (hL : L.eval regs = w.length) (hu : u.eval regs = vertexID B' v)
    (hvin : v.input = w) (hvs : v.state = some q)
    (hfit : Fits B' (registers v)) (hfit' : Fits B' (registers v'))
    (hstep : tm.toMultiTapeNTM.ViewStep v v')
    (hsym : sym.eval regs = symbolCode w[queryIndex (k := k) B' (vertexID B' v)]?) :
    (stepIDExpr tm B L u sym).eval regs = vertexID B' v' := by
  subst hvin
  have hr : ∀ i : Register k, (readRegistersExpr B u i).eval regs = registers v i := fun i => by
    rw [eval_readRegistersExpr, hB, hu, readRegisters_vertexID hfit]
  simp only [ViewStep, hvs] at hstep
  obtain ⟨a, ha, rfl⟩ := hstep
  have htarget : Cslib.Radix.pack B' (nextRegisters v.input.length (registers v) a) =
      vertexID B' (v.step a).summarizeOutput := by
    rw [← registers_step]; rfl
  refine eval_foldr_stepID (instructions tm.toMultiTapeNTM) regs B L u sym (registers v)
    v.input[queryIndex (k := k) B' (vertexID B' v)]? (vertexID B' (v.step a).summarizeOutput)
    hr hsym ?_ ?_
  · intro t ht hm
    rw [hL] at hm
    obtain ⟨h1, h2, h3⟩ := (matchesEntry_iff v _ t).mp hm
    rw [inputSymbol_query hfit] at h2
    have hq : t.1 = q := Option.some.inj (h1.symm.trans hvs)
    have htr : tm.toMultiTapeNTM.Tr q v.inputSymbol v.workTapeSymbols t.2.2.2 := by
      have hmem : tm.toMultiTapeNTM.Tr t.1 t.2.1 t.2.2.1 t.2.2.2 :=
        (mem_instructions tm.toMultiTapeNTM t).mp ht
      rwa [hq, ← h2, ← h3] at hmem
    have haeq : t.2.2.2 = a :=
      (tm.deterministic q v.inputSymbol v.workTapeSymbols).unique htr ha
    rw [hB, hL, haeq, htarget]
  · refine ⟨(q, v.inputSymbol, v.workTapeSymbols, a),
      (mem_instructions tm.toMultiTapeNTM _).mpr ha, ?_⟩
    rw [hL]
    exact (matchesEntry_iff v _ _).mpr ⟨hvs, inputSymbol_query hfit, rfl⟩

/-- Length expression `2 * reg 0 + 1 + reg 2` for virtual input `frame w ++ replicate i true`. -/
private def virtLenExpr : Expr :=
  add (add (mul (const 2) (reg 0)) (const 1)) (reg 2)

/-- 21-instruction counter program that reads `(w, N)` encoded as `frame w ++ replicate N true`
and emits `(List.range N).map (fun i => P (a, i))` by simulating `tm` on each prefix
`frame w ++ replicate i true`. -/
private noncomputable def mapBoolLoopProgram (tm : MultiTapeTM k Bool State) (D : ℕ) :
    CounterProgram where
  code := List.flatten [
    CounterProgram.Words.headerCode,
    forCode 4 2 (reg 1) 7 20,
    [assign 3 (radixExpr D virtLenExpr) 8,
     assign 4 (startIDExpr tm.toMultiTapeNTM (reg 3)) 9,
     lt (const 0)
       (eqB (readRegistersExpr (k := k) (reg 3) (reg 4) .control)
         (const (stateCode (none : Option State)))) 17 10,
     assign 5 (queryIndexExpr k (reg 3) (reg 4)) 11,
     lt (reg 5) virtLenExpr 12 13,
     read (reg 5) 14 15 13,
     assign 6 (const 0) 16,
     assign 6 (const 2) 16,
     assign 6 (const 1) 16,
     assign 4 (stepIDExpr tm (reg 3) virtLenExpr (reg 4) (reg 6)) 9,
     lt (const 0) (badExpr k State (reg 3) virtLenExpr (reg 4)) 18 19,
     emit true 6,
     emit false 6,
     halt []]]
  registers := 7

private theorem bounded7 {B a₀ a₁ a₂ a₃ a₄ a₅ a₆ : ℕ}
    (h₀ : a₀ ≤ B) (h₁ : a₁ ≤ B) (h₂ : a₂ ≤ B) (h₃ : a₃ ≤ B)
    (h₄ : a₄ ≤ B) (h₅ : a₅ ≤ B) (h₆ : a₆ ≤ B) :
    ∀ r ∈ [a₀, a₁, a₂, a₃, a₄, a₅, a₆], r ≤ B := by
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  omega

private theorem reachesOut_header7 {P : CounterProgram} {w : List Bool} {N B : ℕ}
    (hP : P.CodeAt 0 CounterProgram.Words.headerCode) (hB : 2 * w.length + 1 + N ≤ B) :
    P.ReachesOut (frame w ++ List.replicate N true) (P.Active B)
      (0, [0, 0, 0, 0, 0, 0, 0]) (4, [w.length, N, 0, 0, 0, 0, 0]) [] := by
  simp only [CounterProgram.Words.headerCode, codeAt_cons] at hP
  obtain ⟨h₀, h₁, h₂, h₃, -⟩ := hP
  have hmarker : ∀ j < w.length, (frame w ++ List.replicate N true)[2 * j]? = some true :=
    fun j hj => by
      rw [List.getElem?_append_left (by rw [length_frame]; omega), getElem?_frame_two_mul hj]
  have hend : (frame w ++ List.replicate N true)[2 * w.length]? = some false := by
    rw [List.getElem?_append_left (by rw [length_frame]; omega), getElem?_frame_two_mul_length]
  have hunary : ∀ j < N, (frame w ++ List.replicate N true)[2 * w.length + 1 + j]? = some true :=
    fun j hj => by
      rw [List.getElem?_append_right (by rw [length_frame]; omega)]
      simp [length_frame, hj]
  have scanN := reachesOut_count (B := B) (n := w.length) (fun j => [j, 0, 0, 0, 0, 0, 0]) h₀
    (by simpa using h₁) (by simp)
    (fun _ _ => bounded7 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega))
    (fun j hj => by simpa using hmarker j hj) (by simp [hend])
  have scanK := reachesOut_count (B := B) (n := N) (fun j => [w.length, j, 0, 0, 0, 0, 0])
    (by simpa using h₂) (by simpa using h₃) (by simp)
    (fun _ _ => bounded7 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega))
    (fun j hj => by simpa using hunary j hj) (by simp)
  exact (scanN 0 (Nat.zero_le _)).trans (scanK 0 (Nat.zero_le _))

private theorem virtual_getElem?_eq {w : List Bool} {i N q : ℕ} (hiN : i < N)
    (hq : q < 2 * w.length + 1 + i) :
    (frame w ++ List.replicate N true)[q]? = (frame w ++ List.replicate i true)[q]? := by
  by_cases h1 : q < (frame w).length
  · rw [List.getElem?_append_left h1, List.getElem?_append_left h1]
  · rw [length_frame] at h1
    rw [List.getElem?_append_right (by rw [length_frame]; omega),
      List.getElem?_append_right (by rw [length_frame]; omega)]
    simp only [length_frame]
    simp [show q - (2 * w.length + 1) < N by omega, show q - (2 * w.length + 1) < i by omega]

private theorem reachesOut_sim_body (tm : MultiTapeTM k Bool State) (c : ℕ)
    {w : List Bool} {N i Bprog t_run : ℕ} {b : Bool} (hiN : i < N)
    (hcomp : tm.ComputesInTimeAndSpace (frame w ++ List.replicate i true) (encBool b)
      t_run (c * (Nat.log2 (frame w ++ List.replicate i true).length + 1)))
    (hB_len : 2 * w.length + 1 + N + 2 ≤ Bprog)
    (hB_vb : vertexBound (k := k) (radix (radixExponent State c) (2 * w.length + 1 + i)) ≤ Bprog)
    {r3 r4 r5 r6 : ℕ} (hr3 : r3 ≤ Bprog) (hr4 : r4 ≤ Bprog) (hr5 : r5 ≤ Bprog)
    (hr6 : r6 ≤ Bprog) :
    ∃ r3' r4' r5' r6', r3' ≤ Bprog ∧ r4' ≤ Bprog ∧ r5' ≤ Bprog ∧ r6' ≤ Bprog ∧
      (mapBoolLoopProgram tm (radixExponent State c)).ReachesOut
        (frame w ++ List.replicate N true)
        ((mapBoolLoopProgram tm (radixExponent State c)).Active Bprog)
        (7, [w.length, N, i, r3, r4, r5, r6])
        (6, [w.length, N, i, r3', r4', r5', r6']) [b] := by
  set D := radixExponent State c
  set P := mapBoolLoopProgram tm D
  set X := frame w ++ List.replicate N true
  set wi := frame w ++ List.replicate i true
  have hwi_len : wi.length = 2 * w.length + 1 + i := by simp [wi, length_frame]
  set Bi := radix D (2 * w.length + 1 + i)
  have hBi_eq : Bi = radix D wi.length := by rw [hwi_len]
  have hBi_le_vb : Bi ≤ vertexBound (k := k) Bi := by
    have hpos : 0 < Bi := radix_pos D _
    have hc : 1 ≤ Fintype.card (Register k) := Fintype.card_pos_iff.mpr ⟨.inputPos⟩
    simpa [vertexBound] using Nat.le_self_pow (by omega : Fintype.card (Register k) ≠ 0) Bi
  have hBi_le : Bi ≤ Bprog := hBi_le_vb.trans hB_vb
  have hspace : tm.toMultiTapeNTM.RunsInSpace wi (c * (Nat.log2 wi.length + 1)) := hcomp.2.2
  have hw_B : w.length ≤ Bprog := by omega
  have hN_B : N ≤ Bprog := by omega
  have hi_B : i ≤ Bprog := by omega
  obtain ⟨u_halt, -, hu_halt⟩ := exists_haltsAt_of_runsInTime hcomp.2.1
  have hout_halt : (tm.runFrom (tm.initCfg wi) u_halt).output = encBool b :=
    output_haltsAt hcomp.1 hu_halt
  let vs : ℕ → FiniteCfg k Bool State := fun s =>
    Nat.rec (tm.toMultiTapeNTM.initView wi)
      (fun _ v => match v.state with
        | none => v
        | some q => (v.step (tm.tr q v.inputSymbol v.workTapeSymbols)).summarizeOutput) s
  have hvs_both : ∀ s,
      Relation.ReflTransGen tm.toMultiTapeNTM.ViewStep (tm.toMultiTapeNTM.initView wi) (vs s) ∧
      MultiTapeNTM.ViewRep (vs s) (tm.runFrom (tm.initCfg wi) s) := by
    intro s
    induction s with
    | zero => exact ⟨.refl, viewRep_init wi⟩
    | succ s ih =>
      obtain ⟨hreach, hrep⟩ := ih
      cases hst : (tm.runFrom (tm.initCfg wi) s).state with
      | none =>
        have hfs : (vs s).state = none := hrep.state.trans hst
        have hv : vs (s + 1) = vs s := by simp [vs, hfs]
        have hr : tm.runFrom (tm.initCfg wi) (s + 1) = tm.runFrom (tm.initCfg wi) s :=
          runFrom_eq_of_halt tm (tm.initCfg wi) (Nat.le_succ s) hst
        rw [hv, hr]; exact ⟨hreach, hrep⟩
      | some q =>
        have hfs : (vs s).state = some q := hrep.state.trans hst
        obtain ⟨hin, hwork⟩ := hrep.symbols
        have hv : vs (s + 1) =
            ((vs s).step (tm.tr q (vs s).inputSymbol (vs s).workTapeSymbols)).summarizeOutput := by
          simp [vs, hfs]
        have hstep_v : tm.toMultiTapeNTM.ViewStep (vs s) (vs (s + 1)) := by
          simp only [ViewStep, hfs]
          exact ⟨tm.tr q (vs s).inputSymbol (vs s).workTapeSymbols, tm.tr_iff.mpr rfl, hv⟩
        have hrun_succ : tm.runFrom (tm.initCfg wi) (s + 1) =
            tm.step (tm.runFrom (tm.initCfg wi) s) := MultiTapeTM.runFrom_succ _ _
        have htr := tm.step_iff.mpr hrun_succ.symm
        simp only [MultiTapeNTM.Step, hst] at htr
        obtain ⟨a, ha, heq_cfg⟩ := htr
        have ha_eq : a = tm.tr q (vs s).inputSymbol (vs s).workTapeSymbols := by
          rw [hin, hwork]; exact (tm.tr_iff.mp ha).symm
        refine ⟨hreach.tail hstep_v, ?_⟩
        rw [hv, heq_cfg, ha_eq]
        exact hrep.step _
  have hvs_reach : ∀ s, Relation.ReflTransGen tm.toMultiTapeNTM.ViewStep
      (tm.toMultiTapeNTM.initView wi) (vs s) := fun s => (hvs_both s).1
  have hvs_rep : ∀ s, MultiTapeNTM.ViewRep (vs s) (tm.runFrom (tm.initCfg wi) s) :=
    fun s => (hvs_both s).2
  have hvs_fit : ∀ s, Fits Bi (ConfigurationGraph.registers (vs s)) := fun s =>
    hBi_eq ▸ fits_of_runsInSpace c hspace (hvs_reach s)
  have hvs_id_lt : ∀ s, vertexID Bi (vs s) < vertexBound (k := k) Bi := fun s =>
    vertexID_lt (hvs_fit s)
  have hvs_in : ∀ s, (vs s).input = wi := fun s => (hvs_rep s).input
  have hvs_step : ∀ s < u_halt, tm.toMultiTapeNTM.ViewStep (vs s) (vs (s + 1)) := by
    intro s hs
    have hnot : ¬ (tm.runFrom (tm.initCfg wi) s).Halted := hu_halt.not_halted hs
    cases hst : (tm.runFrom (tm.initCfg wi) s).state with
    | none => exact absurd hst hnot
    | some q =>
      have hfs : (vs s).state = some q := (hvs_rep s).state.trans hst
      simp only [ViewStep, hfs]
      exact ⟨tm.tr q (vs s).inputSymbol (vs s).workTapeSymbols, tm.tr_iff.mpr rfl, by simp [vs,
        hfs]⟩
  have hloop : ∀ e s, u_halt - s = e → s ≤ u_halt → ∀ q0 y0, q0 ≤ Bprog → y0 ≤ Bprog →
      ∃ q1 y1, q1 ≤ Bprog ∧ y1 ≤ Bprog ∧
        P.ReachesOut X (P.Active Bprog)
          (9, [w.length, N, i, Bi, vertexID Bi (vs s), q0, y0])
          (17, [w.length, N, i, Bi, vertexID Bi (vs u_halt), q1, y1]) [] := by
    intro e
    induction e with
    | zero =>
      intro s he hs q0 y0 hq0 hy0
      obtain rfl : s = u_halt := by omega
      have hstate : (vs s).state = none := (hvs_rep s).state.trans hu_halt.halted
      have hb := bounded7 (B := Bprog) hw_B hN_B hi_B hBi_le
        ((hvs_id_lt s).le.trans hB_vb) hq0 hy0
      refine ⟨q0, y0, hq0, hy0, ReachesOut.lt (show P.instr 9 = _ from rfl) hb ?_⟩
      simp only [eval_const, eval_eqB, eval_readRegistersExpr, eval_reg, List.getD_cons_zero,
        List.getD_cons_succ, readRegisters_vertexID (hvs_fit s), ConfigurationGraph.registers,
        hstate, decide_true, Bool.toNat_true, Nat.zero_lt_one, ↓reduceIte]
      exact ReachesOut.refl _
    | succ e ih =>
      intro s he hs q0 y0 hq0 hy0
      have hs_lt : s < u_halt := by omega
      have hnot : ¬ (tm.runFrom (tm.initCfg wi) s).Halted := hu_halt.not_halted hs_lt
      cases hst : (tm.runFrom (tm.initCfg wi) s).state with
      | none => exact absurd hst hnot
      | some q =>
        have hfs : (vs s).state = some q := (hvs_rep s).state.trans hst
        have hne_ctrl : stateCode (vs s).state ≠ stateCode (none : Option State) := fun h => by
          have := stateCode_injective h; rw [hfs] at this; exact Option.some_ne_none q this
        have hu_le : vertexID Bi (vs s) ≤ Bprog := (hvs_id_lt s).le.trans hB_vb
        have hb0 := bounded7 (B := Bprog) hw_B hN_B hi_B hBi_le hu_le hq0 hy0
        set qIdx := queryIndex (k := k) Bi (vertexID Bi (vs s))
        have hqIdx_le : qIdx ≤ 2 * w.length + 1 + i + 1 := by
          have hpos : (vs s).inputPos.1 < wi.length + 2 := by
            rw [← hvs_in s]
            exact (vs s).inputPos.isLt
          rw [hwi_len] at hpos
          simp only [qIdx, queryIndex, readRegisters_vertexID (hvs_fit s),
            ConfigurationGraph.registers]
          omega
        have hqIdx_B : qIdx ≤ Bprog := by omega
        have hb1 := bounded7 (B := Bprog) hw_B hN_B hi_B hBi_le hu_le hqIdx_B hy0
        set symVal := symbolCode wi[qIdx]?
        have hsym_B : symVal ≤ Bprog := by
          have := symbolCode_lt wi[qIdx]?; omega
        have hb2 := bounded7 (B := Bprog) hw_B hN_B hi_B hBi_le hu_le hqIdx_B hsym_B
        have hread_sym : P.ReachesOut X (P.Active Bprog)
            (11, [w.length, N, i, Bi, vertexID Bi (vs s), qIdx, y0])
            (16, [w.length, N, i, Bi, vertexID Bi (vs s), qIdx, symVal]) [] := by
          refine ReachesOut.lt (show P.instr 11 = _ from rfl) hb1 ?_
          simp only [virtLenExpr, eval_add, eval_mul, eval_const, eval_reg, List.getD_cons_zero,
            List.getD_cons_succ]
          by_cases hltq : qIdx < 2 * w.length + 1 + i
          · simp only [hltq, ↓reduceIte]
            refine ReachesOut.read (show P.instr 12 = _ from rfl) hb1 ?_
            simp only [eval_reg, List.getD_cons_zero, List.getD_cons_succ]
            rw [show X[qIdx]? = wi[qIdx]? from virtual_getElem?_eq hiN hltq]
            cases hbit : wi[qIdx]? with
            | none =>
              refine ReachesOut.assign (show P.instr 13 = _ from rfl) hb1 ?_
              simpa [symVal, hbit, symbolCode] using ReachesOut.refl _
            | some bbit =>
              cases bbit with
              | false =>
                refine ReachesOut.assign (show P.instr 15 = _ from rfl) hb1 ?_
                simpa [symVal, hbit, symbolCode] using ReachesOut.refl _
              | true =>
                refine ReachesOut.assign (show P.instr 14 = _ from rfl) hb1 ?_
                simpa [symVal, hbit, symbolCode] using ReachesOut.refl _
          · simp only [hltq, ↓reduceIte]
            have hnone : wi[qIdx]? = none := List.getElem?_eq_none (by omega)
            refine ReachesOut.assign (show P.instr 13 = _ from rfl) hb1 ?_
            simpa [symVal, hnone, symbolCode] using ReachesOut.refl _
        have hstep_eval : (stepIDExpr tm (reg 3) virtLenExpr (reg 4) (reg 6)).eval
            [w.length, N, i, Bi, vertexID Bi (vs s), qIdx, symVal] = vertexID Bi (vs (s + 1)) :=
          eval_stepIDExpr tm (B' := Bi) (w := wi) (v := vs s) (v' := vs (s + 1)) (q := q)
            rfl (by simp [virtLenExpr, hwi_len]) rfl (hvs_in s) hfs (hvs_fit s) (hvs_fit (s + 1))
            (hvs_step s hs_lt) rfl
        obtain ⟨q1, y1, hq1, hy1, hrest⟩ := ih (s + 1) (by omega) hs_lt qIdx symVal hqIdx_B hsym_B
        refine ⟨q1, y1, hq1, hy1, ?_⟩
        refine ReachesOut.lt (show P.instr 9 = _ from rfl) hb0 ?_
        simp only [eval_const, eval_eqB, eval_readRegistersExpr, eval_reg, List.getD_cons_zero,
          List.getD_cons_succ, readRegisters_vertexID (hvs_fit s), ConfigurationGraph.registers,
          hne_ctrl, decide_false, Bool.toNat_false, lt_irrefl, ↓reduceIte]
        refine ReachesOut.assign (show P.instr 10 = _ from rfl) hb0 ?_
        simp only [eval_queryIndexExpr, eval_reg, List.getD_cons_zero, List.getD_cons_succ,
          List.set_cons_succ, List.set_cons_zero]
        exact hread_sym.trans (ReachesOut.assign (show P.instr 16 = _ from rfl) hb2
          (by simpa only [hstep_eval, List.set_cons_succ, List.set_cons_zero] using hrest))
  have hb_init := bounded7 (B := Bprog) hw_B hN_B hi_B hr3 hr4 hr5 hr6
  have hb_7 := bounded7 (B := Bprog) hw_B hN_B hi_B hBi_le hr4 hr5 hr6
  have hstart_eq : startID tm.toMultiTapeNTM Bi = vertexID Bi (vs 0) :=
    (vertexID_init tm.toMultiTapeNTM Bi wi).symm
  obtain ⟨q1, y1, hq1, hy1, hsim⟩ := hloop u_halt 0 (by omega) (Nat.zero_le _) r5 r6 hr5 hr6
  have hb_end := bounded7 (B := Bprog) hw_B hN_B hi_B hBi_le
    ((hvs_id_lt u_halt).le.trans hB_vb) hq1 hy1
  have hbad_eq : bad (k := k) (State := State) Bi (2 * w.length + 1 + i)
      (vertexID Bi (vs u_halt)) = b := by
    rw [← hwi_len, ← hvs_in u_halt]
    have hiff := bad_vertexID (hvs_fit u_halt)
    have hst : (vs u_halt).state = none := (hvs_rep u_halt).state.trans hu_halt.halted
    have hout : (vs u_halt).output = outputClass (encBool b) := by
      rw [(hvs_rep u_halt).output, hout_halt]
    cases b with
    | true => exact hiff.mpr ⟨hst, hout⟩
    | false =>
      cases hval : bad (k := k) (State := State) Bi (vs u_halt).input.length
          (vertexID Bi (vs u_halt)) with
      | false => rfl
      | true =>
        have hfalse := (hiff.mp hval).2
        rw [hout] at hfalse
        have h1 : outputClass (encBool false) = [false] := by
          simp [outputClass, encBool_apply]
        rw [h1] at hfalse
        exact absurd hfalse (by decide)
  refine ⟨Bi, vertexID Bi (vs u_halt), q1, y1, hBi_le, (hvs_id_lt u_halt).le.trans hB_vb,
    hq1, hy1, ?_⟩
  refine ReachesOut.assign (show P.instr 7 = _ from rfl) hb_init ?_
  simp only [eval_radixExpr, virtLenExpr, eval_add, eval_mul, eval_const, eval_reg,
    List.getD_cons_zero, List.getD_cons_succ, List.set_cons_succ, List.set_cons_zero]
  change P.ReachesOut X (P.Active Bprog) (8, [w.length, N, i, Bi, r4, r5, r6])
    (6, [w.length, N, i, Bi, vertexID Bi (vs u_halt), q1, y1]) [b]
  refine ReachesOut.assign (show P.instr 8 = _ from rfl) hb_7 ?_
  simp only [eval_startIDExpr, eval_reg, List.getD_cons_zero, List.getD_cons_succ, hstart_eq,
    List.set_cons_succ, List.set_cons_zero]
  have hstep17 : P.ReachesOut X (P.Active Bprog)
      (17, [w.length, N, i, Bi, vertexID Bi (vs u_halt), q1, y1])
      (6, [w.length, N, i, Bi, vertexID Bi (vs u_halt), q1, y1]) [b] := by
    refine ReachesOut.lt (show P.instr 17 = _ from rfl) hb_end ?_
    simp only [eval_const, eval_badExpr, virtLenExpr, eval_add, eval_mul, eval_reg,
      List.getD_cons_zero, List.getD_cons_succ, hbad_eq]
    cases b with
    | false =>
      simp only [Bool.toNat_false, lt_irrefl, ↓reduceIte]
      exact ReachesOut.emit (show P.instr 19 = _ from rfl) hb_end (ReachesOut.refl _)
    | true =>
      simp only [Bool.toNat_true, Nat.zero_lt_one, ↓reduceIte]
      exact ReachesOut.emit (show P.instr 18 = _ from rfl) hb_end (ReachesOut.refl _)
  exact (hsim.trans hstep17).of_eq (List.nil_append [b])

/-- Universal log-space range-map combinator: given a log-space unary bound `bound : α → ℕ` and
a log-space Boolean predicate `P : α × ℕ → Bool`, mapping `i ↦ P (a, i)` over `List.range (bound a)`
is computable in logarithmic space. -/
theorem computableInLogSpace_map_range_bool {α : Type} {encIn : α ↪ List Bool}
    {bound : α → ℕ} {P : α × ℕ → Bool}
    (hbound : ComputableInLogSpace bound encIn encUnary)
    (hP : ComputableInLogSpace P (encPair encIn encUnary) encBool) :
    ComputableInLogSpace (fun a => (List.range (bound a)).map fun i => P (a, i))
      encIn encBits := by
  suffices hpair : ComputableInLogSpace (fun p : α × ℕ => (List.range p.2).map fun i => P (p.1, i))
      (encPair encIn encUnary) encBits by
    exact hpair.comp (ComputableInLogSpace.pair .id hbound)
  obtain ⟨t, c, k, State, hfin, tm, htm⟩ := hP
  let : Fintype State := Fintype.ofFinite State
  set D := radixExponent State c
  set d := max 3 (2 * D * Fintype.card (Register k) + 2)
  refine (mapBoolLoopProgram tm D).computableInLogSpace_of_reachesOut d fun ⟨a, N⟩ => ?_
  set w := encIn a
  set X := frame w ++ List.replicate N true
  have hX_eq : encPair encIn encUnary (a, N) = X := rfl
  have hX_len : X.length = 2 * w.length + 1 + N := by simp [X, length_frame]
  set Bprog := (X.length + 1) ^ d
  have hX1_ge2 : 2 ≤ X.length + 1 := by omega
  have hB_len : 2 * w.length + 1 + N + 2 ≤ Bprog := by
    have h1 : X.length + 2 ≤ (X.length + 1) ^ 2 := by nlinarith
    have h2 : (X.length + 1) ^ 2 ≤ (X.length + 1) ^ d :=
      Nat.pow_le_pow_right (by omega) (by omega)
    omega
  have hB_vb : ∀ i < N,
      vertexBound (k := k) (radix D (2 * w.length + 1 + i)) ≤ Bprog := fun i hi => by
    rw [vertexBound_eq_pow]
    have hbase : 2 * w.length + 1 + i + 2 ≤ (X.length + 1) ^ 2 := by nlinarith
    calc (2 * w.length + 1 + i + 2) ^ (D * Fintype.card (Register k))
        ≤ ((X.length + 1) ^ 2) ^ (D * Fintype.card (Register k)) :=
          Nat.pow_le_pow_left hbase _
      _ = (X.length + 1) ^ (2 * D * Fintype.card (Register k)) := by
          rw [← pow_mul, Nat.mul_assoc]
      _ ≤ (X.length + 1) ^ d := Nat.pow_le_pow_right (by omega) (by omega)
  have hhead := reachesOut_header7 (P := mapBoolLoopProgram tm D) (w := w) (N := N) (B := Bprog)
    (codeAt_of_prefix ⟨_, rfl⟩) (by omega)
  have hfor : (mapBoolLoopProgram tm D).CodeAt 4 (forCode 4 2 (reg 1) 7 20) :=
    codeAt_of_prefix ⟨_, rfl⟩
  let Inv : ℕ → List ℕ → Prop := fun i regs =>
    ∃ r3 r4 r5 r6, regs = [w.length, N, i, r3, r4, r5, r6] ∧ i ≤ N ∧
      r3 ≤ Bprog ∧ r4 ≤ Bprog ∧ r5 ≤ Bprog ∧ r6 ≤ Bprog
  obtain ⟨regs, hloop, hinv⟩ := reachesOut_forCode (w := X) (B := Bprog) (N := N) hfor Inv
    (fun i => [P (a, i)]) (by omega)
    (by
      rintro i regs ⟨r3, r4, r5, r6, rfl, hi, hr3, hr4, hr5, hr6⟩
      exact ⟨rfl, rfl, by simp,
        bounded7 (by omega) (by omega) (by omega) hr3 hr4 hr5 hr6⟩)
    (by
      rintro i hi regs ⟨r3, r4, r5, r6, rfl, -, hr3, hr4, hr5, hr6⟩
      obtain ⟨r3', r4', r5', r6', hr3', hr4', hr5', hr6', hbody⟩ :=
        reachesOut_sim_body tm c hi (htm (a, i)) hB_len (hB_vb i hi) hr3 hr4 hr5 hr6
      refine ⟨[w.length, N, i, r3', r4', r5', r6'], hbody, rfl,
        bounded7 (by omega) (by omega) (by omega) hr3' hr4' hr5' hr6',
        r3', r4', r5', r6', by simp, hi, hr3', hr4', hr5', hr6'⟩)
    [w.length, N, 0, 0, 0, 0, 0]
    (bounded7 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))
    ⟨0, 0, 0, 0, by simp, Nat.zero_le _, by omega, by omega, by omega, by omega⟩
  obtain ⟨r3, r4, r5, r6, rfl, -, hr3, hr4, hr5, hr6⟩ := hinv
  refine ⟨(20, [w.length, N, N, r3, r4, r5, r6]),
    (List.range N).flatMap (fun i => [P (a, i)]), [],
    (hhead.trans hloop).of_eq (by simp), rfl, ?_,
    by
      rw [hX_eq]
      exact bounded7 (by omega) (by omega) (by omega) hr3 hr4 hr5 hr6⟩
  simp only [encBits_apply, List.append_nil]
  have hflat : ∀ L : List ℕ, L.map (fun i => P (a, i)) = L.flatMap (fun i => [P (a, i)]) := by
    intro L; induction L with
    | nil => rfl
    | cons x xs ih => simp [ih]
  exact hflat (List.range N)

/-- Log-space unary-bounded existential quantification over `0, …, bound a - 1`. -/
theorem computableInLogSpace_any_range {α : Type} {encIn : α ↪ List Bool}
    {bound : α → ℕ} {P : α × ℕ → Bool}
    (hbound : ComputableInLogSpace bound encIn encUnary)
    (hP : ComputableInLogSpace P (encPair encIn encUnary) encBool) :
    ComputableInLogSpace (fun a => (List.range (bound a)).any fun i => P (a, i))
      encIn encBool :=
  ((ComputableInLogSpace.bitsAny id).comp
    (computableInLogSpace_map_range_bool hbound hP)).congr_fun fun a => by
      simp [List.any_map]

/-- Log-space unary-bounded universal quantification over `0, …, bound a - 1`. -/
theorem computableInLogSpace_all_range {α : Type} {encIn : α ↪ List Bool}
    {bound : α → ℕ} {P : α × ℕ → Bool}
    (hbound : ComputableInLogSpace bound encIn encUnary)
    (hP : ComputableInLogSpace P (encPair encIn encUnary) encBool) :
    ComputableInLogSpace (fun a => (List.range (bound a)).all fun i => P (a, i))
      encIn encBool :=
  ((ComputableInLogSpace.bitsAll id).comp
    (computableInLogSpace_map_range_bool hbound hP)).congr_fun fun a => by
      simp [List.all_map]

end MapRangeBool

end CslibFrontier.Computability.LogSpace
