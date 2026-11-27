/-
Copyright (c) 2026 Google DeepMind. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.StoredLoop
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.Words
public import CslibFrontier.Logics.FirstOrder.Encoding

import CslibFrontier.Computability.Machines.ReadMachine.VirtualWord.Native
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Constructible
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.ListSlice
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.CounterProgram.Unary
import CslibFrontier.Computability.Machines.Turing.MultiTape.HaltsAt
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.NatLength
import Mathlib.Data.Nat.Size

/-!
# Logarithmic-Space Loops and Streaming Bit-Table Combinators

This module provides reusable deterministic logarithmic-space combinators built on `CslibFrontier`'s
`ComputableInSpace.loopWith` and `QueryMachine.computableInSpaceFrom`:
- `logSpace_anyRange`, `logSpace_allRange`, `logSpace_countRange`: bounded existential, universal,
  and counting loops over `0, …, N a - 1` for arbitrary `ComputableInLogSpace` predicates.
- `logSpace_streamBits`: streams `(List.range (N a)).map (fun i ↦ bit (i, a))` in logarithmic space
  without storing the output, for any polynomially bounded `N` and `ComputableInLogSpace` `bit`.
-/

namespace Turing.MultiTapeTM

open ComputableInSpace Universal

namespace StreamBits

/-- State of the logarithmic-space bit-streaming query machine. -/
structure State where
  /-- Current index `j`. -/
  idx : ℕ
  /-- Total number of bits `N a` to emit. -/
  bound : ℕ
  /-- Framed encoding `frame (encNat idx)` of the current index. -/
  pre : List Bool
  /-- Output bits accumulated for the current index. -/
  acc : List Bool
  /-- Configuration of the simulated `bit` machine. -/
  cfg : SCfg

private enc_structure encState : State where
  idx : encNat, bound : encNat, pre : encBits, acc : encBits, cfg : eCfg

/-- Virtual input head position of the simulated `bit` machine. -/
private def vpos (s : State) : ℕ := s.cfg.inputPos - 1

/-- Input bit queried by the streaming machine. -/
private def query (s : State) : ℕ := vpos s - s.pre.length

/-- Virtual input symbol seen by the simulated `bit` machine. -/
private def symbol (s : State) (b : Option Bool) : Option Bool :=
  if vpos s < s.pre.length then some (s.pre.getD (vpos s) false) else b

/-- Halt test: stop once `bound ≤ idx`. -/
private def halted (s : State) : Bool := decide (s.bound ≤ s.idx)

/-- Emission on each step: emit `acc` when the simulated `bit` machine halts. -/
private def emit (p : State × Option Bool) : List Bool :=
  if p.1.cfg.state.isNone then p.1.acc else []

/-- Transition on each step: simulate `bit`, or advance `idx` once `bit` halts. -/
private def next (d : Desc) (p : State × Option Bool) : State :=
  if p.1.cfg.state.isNone then
    ⟨p.1.idx + 1, p.1.bound, frame (encNat (p.1.idx + 1)), [], init d⟩
  else
    ⟨p.1.idx, p.1.bound, p.1.pre,
      p.1.acc ++ (VirtualWord.Native.machine d).emit (p.1.cfg, symbol p.1 p.2),
      (VirtualWord.Native.machine d).next (p.1.cfg, symbol p.1 p.2)⟩

/-- The streaming query machine for a `bit` machine descriptor `d`. -/
private def machine (d : Desc) : QueryMachine State where
  init := ⟨0, 0, frame (encNat 0), [], init d⟩
  query := query
  next := next d
  emit := emit
  halted := halted
  finish _ := []

private theorem bitsLength_inSpace : ComputableInSpace (fun l : List Bool ↦ l.length) encBits
    encNat fun l ↦ (encBits l).length :=
  of_inO ComputableInO.lengthNat

private theorem query_inSpace :
    ComputableInSpace query encState encNat fun s ↦ (encState s).length := by
  have hid := budget_id (enc := encState) (.refl _)
  exact budget_natSub (budget_natPred (eCfg_inputPos_budget (encState_cfg_budget hid)))
    (budget_comp_linear bitsLength_inSpace (encState_pre_budget hid))

private theorem halted_inSpace :
    ComputableInSpace halted encState encBool fun s ↦ (encState s).length := by
  have hid := budget_id (enc := encState) (.refl _)
  refine (budget_finite (encC := encBool) Bool.not
    (budget_natLt (encState_idx_budget hid) (encState_bound_budget hid))).of_enc_eq fun s ↦ ?_
  change encBool (decide (s.bound ≤ s.idx)) = encBool (!decide (s.idx < s.bound))
  by_cases h : s.idx < s.bound <;> simp [h, Nat.not_le.mpr, Nat.le_of_not_lt]

private theorem emit_inSpace :
    ComputableInSpace emit (QueryMachine.encStateRead encState) encBits
      fun p ↦ (QueryMachine.encStateRead encState p).length := by
  have hp := fst encState (encOption encBool)
  have hacc := encState_acc_budget hp
  have hcfg := encState_cfg_budget hp
  have hh : ComputableInSpace (fun c : SCfg ↦ c.state.isNone) eCfg encBool
      fun c ↦ (eCfg c).length :=
    (budget_finite (encC := encBool) Bool.not
      (budget_optionIsSome (eCfg_state_budget (budget_id (.refl _))))).of_enc_eq fun c ↦ by
        cases c.state <;> rfl
  exact (budget_ite (budget_comp_linear hh hcfg) hacc (budget_const [])).of_enc_eq fun _ ↦ rfl

private theorem next_inSpace (d : Desc) :
    ComputableInSpace (next d) (QueryMachine.encStateRead encState) encState
      fun p ↦ (QueryMachine.encStateRead encState p).length := by
  obtain ⟨-, hn, he, hh, -⟩ := VirtualWord.Native.components_inSpace d
  have hp := fst encState (encOption encBool)
  have hb := snd encState (encOption encBool)
  have hidx := encState_idx_budget hp
  have hbound := encState_bound_budget hp
  have hpre := encState_pre_budget hp
  have hacc := encState_acc_budget hp
  have hcfg := encState_cfg_budget hp
  have hvpos := budget_natPred (eCfg_inputPos_budget hcfg)
  have hlt := budget_natLt hvpos (budget_comp_linear bitsLength_inSpace hpre)
  have hsym : ComputableInSpace (fun p : State × Option Bool ↦ symbol p.1 p.2)
      (QueryMachine.encStateRead encState) (encOption encBool)
      fun p ↦ (QueryMachine.encStateRead encState p).length :=
    (budget_ite hlt (budget_optionSome (budget_comp_linear (bitsGetD false)
      (budget_prod hpre hvpos))) hb).of_enc_eq fun p ↦ by
        unfold symbol vpos
        by_cases h : p.1.cfg.inputPos - 1 < p.1.pre.length <;> simp [h]
  have hin := budget_prod hcfg hsym
  have happ : ComputableInSpace (fun p : State × Option Bool ↦
      p.1.acc ++ (VirtualWord.Native.machine d).emit (p.1.cfg, symbol p.1 p.2))
      (QueryMachine.encStateRead encState) encBits
      fun p ↦ (QueryMachine.encStateRead encState p).length :=
    (hacc.append (budget_comp_linear he hin) fun _ ↦ rfl).weaken (.add (.refl _) (.refl _))
  have hrun := encState_mk_budget hidx hbound hpre happ (budget_comp_linear hn hin)
  have hidx1 := budget_natSucc hidx
  have hpre1 := budget_comp_linear (ComputableInSpace.frame encBits)
    (hidx1.of_enc_eq fun _ ↦ rfl)
  have hadv := encState_mk_budget hidx1 hbound hpre1 (budget_const []) (budget_const (init d))
  exact (budget_ite (budget_comp_linear hh hcfg) hadv hrun).of_enc_eq fun _ ↦ rfl

private theorem finish_inSpace :
    ComputableInSpace (fun _ : State ↦ ([] : List Bool)) encState encBits
      fun s ↦ (encState s).length :=
  budget_const []

private theorem symbol_read (w : List Bool) (s : State) :
    symbol s (w[query s]?) = (s.pre ++ w)[vpos s]? := by
  unfold symbol query
  split_ifs with h
  · rw [List.getElem?_append_left h, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]; rfl
  · rw [List.getElem?_append_right (Nat.le_of_not_gt h)]

private theorem output_succ_native (d : Desc) (x : List Bool) (t : ℕ) :
    (VirtualWord.Native.machine d).output x (t + 1) =
      (VirtualWord.Native.machine d).output x t ++
        if (VirtualWord.Native.machine d).halted ((VirtualWord.Native.machine d).run x t) then []
        else (VirtualWord.Native.machine d).emit ((VirtualWord.Native.machine d).run x t,
          (VirtualWord.Native.machine d).read x ((VirtualWord.Native.machine d).run x t)) := by
  simp only [QueryMachine.output,
    show (VirtualWord.Native.machine d).finish = fun _ ↦ [] from rfl,
    List.append_nil, List.range_succ, List.map_append, List.flatten_append, List.map_singleton,
    List.flatten_singleton]

private theorem length_output_mono_native (d : Desc) (x : List Bool) {t u : ℕ} (h : t ≤ u) :
    ((VirtualWord.Native.machine d).output x t).length ≤
      ((VirtualWord.Native.machine d).output x u).length := by
  induction u, h using Nat.le_induction with
  | base => rfl
  | succ u _ ih => rw [output_succ_native, List.length_append]; omega

/-- Cumulative step count before round `j`. -/
private def timeBefore {α : Type} (τ : α → ℕ → ℕ) (a : α) : ℕ → ℕ
  | 0 => 0
  | j + 1 => timeBefore τ a j + (τ a j + 1)

private lemma length_encState (s : State) :
    (encState s).length =
      2 * (encNat s.idx).length + 1 + (2 * (encNat s.bound).length + 1 +
        (2 * s.pre.length + 1 + (2 * s.acc.length + 1 + (eCfg s.cfg).length))) := by
  change (encPair encNat (encPair encNat (encPair encBits (encPair encBits eCfg)))
    (s.idx, s.bound, s.pre, s.acc, s.cfg)).length = _
  simp only [length_encPair, encBits_apply]

end StreamBits

end Turing.MultiTapeTM

public section

namespace Turing.MultiTapeTM

open ComputableInSpace Universal

/-! ### Bounded logarithmic-space quantifier and counting loops -/

/-- Binary encoding length of a polynomially bounded natural number is `O(log₂ n + 1)`. -/
lemma length_encNat_le_of_poly {α : Type} {encA : α ↪ List Bool} {f : α → ℕ} {k : ℕ}
    (hf : ∀ a, f a ≤ ((encA a).length + 1) ^ k) :
    ∃ c, ∀ a, (encNat (f a)).length ≤ c * (Nat.log2 (encA a).length + 1) :=
  ⟨k + 1, fun a ↦ length_encNat_le_of_le_pow (hf a)⟩

private lemma length_encNat_mono' {a b : ℕ} (h : a ≤ b) :
    (encNat a).length ≤ (encNat b).length := by
  simp only [encNat_apply, Nat.size_eq_bits_len]
  exact Nat.size_le_size h

private lemma length_encNat_succ_le (n : ℕ) :
    (encNat (n + 1)).length ≤ (encNat n).length + 1 := by
  simp only [encNat_apply, Nat.size_eq_bits_len, Nat.size_le]
  have h : n < 2 ^ n.size := Nat.lt_size_self n
  rw [pow_succ]
  omega

/-- Helper: `Nat.log2` of a sum bound. -/
private lemma log2_add_le' (u v : ℕ) : Nat.log2 (u + v) ≤ u + Nat.log2 v + 1 := by
  rcases Nat.eq_zero_or_pos (u + v) with h | h
  · simp [h]
  · refine Nat.le_of_lt_succ ((Nat.log2_lt h.ne').mpr ?_)
    calc u + v < 2 ^ u + 2 ^ (Nat.log2 v + 1) := Nat.add_lt_add Nat.lt_two_pow_self Nat.lt_log2_self
      _ ≤ 2 ^ (u + Nat.log2 v + 1) + 2 ^ (u + Nat.log2 v + 1) :=
        Nat.add_le_add (Nat.pow_le_pow_right (by norm_num) (by omega))
          (Nat.pow_le_pow_right (by norm_num) (by omega))
      _ = 2 ^ (u + Nat.log2 v + 1 + 1) := by rw [pow_succ]; ring

/-- Bounded counting loop in logarithmic space: `count {i < N a | p (i, a) = true}`. -/
theorem logSpace_countRange {α : Type} {encA : α ↪ List Bool}
    {N : α → ℕ} {p : ℕ × α → Bool} {k : ℕ}
    (hN : ComputableInLogSpace N encA encNat)
    (hNpoly : ∀ a, N a ≤ ((encA a).length + 1) ^ k)
    (hp : ComputableInLogSpace p (encPair encNat encA) encBool) :
    ComputableInLogSpace
      (fun a ↦ ((List.range (N a)).filter fun i ↦ p (i, a)).length) encA encNat := by
  classical
  let encR : ℕ × ℕ × ℕ ↪ List Bool := encNat3
  let init : α → ℕ × ℕ × ℕ := fun a ↦ (0, N a, 0)
  let step : (ℕ × ℕ × ℕ) × α → Option (ℕ × ℕ × ℕ) := fun ⟨(i, n, acc), a⟩ ↦
    if i < n then
      some (i + 1, n, if p (i, a) then acc + 1 else acc)
    else none
  have hN_len : ∃ c, ∀ a, (encNat (N a)).length ≤ c * (Nat.log2 (encA a).length + 1) :=
    length_encNat_le_of_poly hNpoly
  have hinit_log : ComputableInLogSpace init encA encR := by
    have h0 : ComputableInLogSpace (fun _ : α ↦ (0 : ℕ)) encA encNat :=
      ComputableInLogSpace.const 0
    exact ComputableInLogSpace.pair h0 (ComputableInLogSpace.pair hN h0)
  have hinit : ComputableInSpace init encA encR (fun a ↦ Nat.log2 (encA a).length) := by
    refine hinit_log.inSpace_of_length_log ?_
    obtain ⟨c, hc⟩ := hN_len
    refine ⟨2 * c + 10, fun a ↦ ?_⟩
    simp only [init, encR, encNat3, length_encPair, encNat_apply]
    have hNa := hc a; simp only [encNat_apply] at hNa
    have h0 : (Nat.bits 0).length = 0 := rfl
    rw [h0]
    nlinarith
  have hstep : ComputableInSpace step (encPair encR encA) (encOption encR)
      (fun q ↦ (encR q.1).length + Nat.log2 (encA q.2).length) := by
    have hr : ComputableInSpace (fun q : (ℕ × ℕ × ℕ) × α ↦ q.1) (encPair encR encA) encR
        (fun q ↦ (encR q.1).length + Nat.log2 (encA q.2).length) :=
      (ComputableInLogSpace.fst encR encA).inSpace_context ⟨1, fun p ↦ by dsimp only; omega⟩
    have hi : ComputableInSpace (fun q : (ℕ × ℕ × ℕ) × α ↦ q.1.1) (encPair encR encA) encNat
        (fun q ↦ (encR q.1).length + Nat.log2 (encA q.2).length) :=
      budget_comp_linear (fst encNat (encPair encNat encNat)) hr
    have hn : ComputableInSpace (fun q : (ℕ × ℕ × ℕ) × α ↦ q.1.2.1) (encPair encR encA) encNat
        (fun q ↦ (encR q.1).length + Nat.log2 (encA q.2).length) :=
      budget_comp_linear (fst encNat encNat)
        (budget_comp_linear (snd encNat (encPair encNat encNat)) hr)
    have hacc : ComputableInSpace (fun q : (ℕ × ℕ × ℕ) × α ↦ q.1.2.2) (encPair encR encA) encNat
        (fun q ↦ (encR q.1).length + Nat.log2 (encA q.2).length) :=
      budget_comp_linear (snd encNat encNat)
        (budget_comp_linear (snd encNat (encPair encNat encNat)) hr)
    have hp_log : ComputableInLogSpace (fun q : (ℕ × ℕ × ℕ) × α ↦ p (q.1.1, q.2))
        (encPair encR encA) encBool :=
      hp.comp (ComputableInLogSpace.pair
        ((ComputableInLogSpace.fst encNat (encPair encNat encNat)).comp
          (ComputableInLogSpace.fst encR encA))
        (ComputableInLogSpace.snd encR encA))
    have hp_space : ComputableInSpace (fun q : (ℕ × ℕ × ℕ) × α ↦ p (q.1.1, q.2))
        (encPair encR encA) encBool
        (fun q ↦ (encR q.1).length + Nat.log2 (encA q.2).length) :=
      hp_log.inSpace_context ⟨2, fun _ ↦ by simp [encBool_apply]; omega⟩
    have hlt := budget_natLt hi hn
    have hacc' := budget_ite hp_space (budget_natSucc hacc) hacc
    have hsome := budget_optionSome (budget_prod (budget_natSucc hi) (budget_prod hn hacc'))
    exact (budget_ite hlt hsome (budget_const none)).of_enc_eq fun ⟨(i, n, acc), a⟩ ↦ by
      dsimp only [step]
      by_cases h : i < n
      · simp only [h, ↓reduceIte, decide_true]; rfl
      · simp only [h, ↓reduceIte, decide_false]; rfl
  let r : α → ℕ → ℕ × ℕ × ℕ := fun a j ↦
    (j, N a, ((List.range j).filter fun i ↦ p (i, a)).length)
  obtain ⟨cN, hcN⟩ := hN_len
  have hloop := ComputableInSpace.loopWith r N hinit hstep
    (fun _ ↦ rfl)
    (fun a j hj ↦ by
      simp only [r, step, hj, ↓reduceIte, List.range_succ, List.filter_append, List.length_append]
      cases hpj : p (j, a) <;> simp [hpj])
    (fun a ↦ by simp only [r, step, lt_irrefl, ↓reduceIte])
    (B := fun a ↦ (8 * cN + 20) * (Nat.log2 (encA a).length + 1))
    (fun a j hj ↦ by
      simp only [r, encR, encNat3, length_encPair]
      have hfilt : ((List.range j).filter fun i ↦ p (i, a)).length ≤ N a := by
        calc ((List.range j).filter fun i ↦ p (i, a)).length
            ≤ (List.range j).length := List.length_filter_le _ _
          _ = j := List.length_range
          _ ≤ N a := hj
      have hj_le := length_encNat_mono' hj
      have hf_le := length_encNat_mono' hfilt
      have hNa := hcN a
      nlinarith)
  have hproj : ComputableInSpace (fun a ↦ ((List.range (N a)).filter fun i ↦ p (i, a)).length)
      encA encNat (fun a ↦ Nat.log2 (encA a).length) := by
    have h1 := (ComputableInSpace.snd encNat encNat).comp
      ((ComputableInSpace.snd encNat (encPair encNat encNat)).comp hloop)
    refine h1.weaken ⟨20 * cN + 40, fun a ↦ ?_⟩
    dsimp only [r]
    simp only [length_encPair]
    have hfilt : ((List.range (N a)).filter fun i ↦ p (i, a)).length ≤ N a := by
      calc ((List.range (N a)).filter fun i ↦ p (i, a)).length
          ≤ (List.range (N a)).length := List.length_filter_le _ _
        _ = N a := List.length_range
    have hf_le := length_encNat_mono' hfilt
    have hNa := hcN a
    nlinarith
  exact hproj.computableInLogSpace

/-- Bounded existential loop in logarithmic space: `∃ i < N a, p (i, a) = true`. -/
theorem logSpace_anyRange {α : Type} {encA : α ↪ List Bool}
    {N : α → ℕ} {p : ℕ × α → Bool} {k : ℕ}
    (hN : ComputableInLogSpace N encA encNat)
    (hNpoly : ∀ a, N a ≤ ((encA a).length + 1) ^ k)
    (hp : ComputableInLogSpace p (encPair encNat encA) encBool) :
    ComputableInLogSpace (fun a ↦ (List.range (N a)).any fun i ↦ p (i, a)) encA encBool := by
  have hcnt := logSpace_countRange hN hNpoly hp
  have hpos : ComputableInLogSpace (fun m : ℕ ↦ decide (0 < m)) encNat encBool := by
    have hempty : ComputableInLogSpace (fun m : ℕ ↦ (encNat m).isEmpty) encNat encBool :=
      ComputableInLogSpace.of_isEmpty fun _ ↦ rfl
    refine (ComputableInLogSpace.bool_not hempty).congr_fun fun m ↦ ?_
    cases m with
    | zero => rfl
    | succ m =>
      have hne : (encNat (m + 1)).length ≠ 0 := by
        have := log2_succ_le_length_encNat m; omega
      have hnil : (encNat (m + 1)).isEmpty = false := by
        cases h : encNat (m + 1) with
        | nil => simp [h] at hne
        | cons _ _ => rfl
      change decide (0 < m + 1) = !(encNat (m + 1)).isEmpty
      rw [hnil]; rfl
  refine (hpos.comp hcnt).congr_fun fun a ↦ ?_
  dsimp only [Function.comp_apply]
  by_cases h : (List.range (N a)).any (fun i ↦ p (i, a)) = true
  · rw [h]; symm; rw [decide_eq_true_eq]
    rw [List.any_eq_true] at h
    obtain ⟨i, hi, hpi⟩ := h
    exact List.length_pos_of_mem (List.mem_filter.mpr ⟨hi, hpi⟩)
  · have hf : (List.range (N a)).any (fun i ↦ p (i, a)) = false := Bool.eq_false_iff.mpr h
    rw [hf]; symm; rw [decide_eq_false_iff_not, Nat.not_lt, Nat.le_zero]
    rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
    intro i hi hpi
    exact h (List.any_eq_true.mpr ⟨i, hi, hpi⟩)

/-- Bounded universal loop in logarithmic space: `∀ i < N a, p (i, a) = true`. -/
theorem logSpace_allRange {α : Type} {encA : α ↪ List Bool}
    {N : α → ℕ} {p : ℕ × α → Bool} {k : ℕ}
    (hN : ComputableInLogSpace N encA encNat)
    (hNpoly : ∀ a, N a ≤ ((encA a).length + 1) ^ k)
    (hp : ComputableInLogSpace p (encPair encNat encA) encBool) :
    ComputableInLogSpace (fun a ↦ (List.range (N a)).all fun i ↦ p (i, a)) encA encBool := by
  have hnotp : ComputableInLogSpace (fun q : ℕ × α ↦ !p q) (encPair encNat encA) encBool :=
    ComputableInLogSpace.bool_not hp
  have hany := logSpace_anyRange hN hNpoly hnotp
  refine (ComputableInLogSpace.bool_not hany).congr_fun fun a ↦ ?_
  by_cases h : (List.range (N a)).all (fun i ↦ p (i, a)) = true
  · rw [h]; symm; rw [Bool.not_eq_true', List.any_eq_false]
    rw [List.all_eq_true] at h; intro i hi; simp [h i hi]
  · have hf : (List.range (N a)).all (fun i ↦ p (i, a)) = false := Bool.eq_false_iff.mpr h
    rw [hf]; symm; rw [Bool.not_eq_false', List.any_eq_true]
    rw [List.all_eq_false] at hf
    obtain ⟨i, hi, hpi⟩ := hf
    exact ⟨i, hi, by simp [hpi]⟩

/-! ### Streaming bit-table writer in logarithmic space -/

/-- **Streaming bit-table writer in logarithmic space**: given a polynomially bounded length
function `N : α → ℕ` and a `ComputableInLogSpace` bit predicate `bit : ℕ × α → Bool`, the bit word
`(List.range (N a)).map (fun i ↦ bit (i, a))` is computable in logarithmic space without storing the
output. -/
theorem logSpace_streamBits {α : Type} {encA : α ↪ List Bool}
    {N : α → ℕ} {bit : ℕ × α → Bool} {k : ℕ}
    (hN : ComputableInLogSpace N encA encNat)
    (hNpoly : ∀ a, N a ≤ ((encA a).length + 1) ^ k)
    (hbit : ComputableInLogSpace bit (encPair encNat encA) encBool) :
    ComputableInLogSpace
      (fun a ↦ (List.range (N a)).map fun i ↦ bit (i, a)) encA encBits := by
  classical
  obtain ⟨tB, cB, ⟨mK, Q, _, tm, htm⟩⟩ := hbit
  let : Fintype Q := Fintype.ofFinite Q
  let eS : Q ↪ ℕ := (Fintype.equivFin Q).toEmbedding.trans Fin.valEmbedding
  let d : Desc := desc eS eBit tm
  let M : QueryMachine StreamBits.State := StreamBits.machine d
  choose τ _ hτ using fun a j ↦ exists_haltsAt_of_runsInTime (htm (j, a)).2.1
  let vinput (j : ℕ) (a : α) : List Bool := frame (encNat j) ++ encA a
  have hrun (a : α) (j t : ℕ) (ht : t < τ a j) :
      ((VirtualWord.Native.machine d).run (vinput j a) t).state.isNone = false :=
    (VirtualWord.Native.halted_native eS tm _ t).trans
      (Bool.eq_false_iff.mpr (Option.isNone_iff_eq_none.not.mpr ((hτ a j).not_halted ht)))
  have hhalt (a : α) (j : ℕ) :
      ((VirtualWord.Native.machine d).run (vinput j a) (τ a j)).state.isNone = true :=
    (VirtualWord.Native.halted_native eS tm _ (τ a j)).trans
      (Option.isNone_iff_eq_none.mpr (hτ a j).halted)
  have hfinal (a : α) (j : ℕ) :
      (VirtualWord.Native.machine d).output (vinput j a) (τ a j) = [bit (j, a)] := by
    rw [VirtualWord.Native.output_native]
    exact output_haltsAt (htm (j, a)).1 (hτ a j)
  let st (a : α) (j t : ℕ) : StreamBits.State :=
    ⟨j, N a, frame (encNat j), (VirtualWord.Native.machine d).output (vinput j a) t,
      (VirtualWord.Native.machine d).run (vinput j a) t⟩
  let roundSteps (a : α) (j : ℕ) : ℕ := τ a j + 1
  have hstep_run (a : α) (j t : ℕ) (ht : t < τ a j) (hj : j < N a) :
      M.step (encA a) (st a j t) = st a j (t + 1) := by
    have hnh : M.halted (st a j t) = false := by
      simp [M, StreamBits.machine, StreamBits.halted, st, Nat.not_le.mpr hj]
    have hnr := hrun a j t ht
    rw [QueryMachine.step, hnh]
    simp only [Bool.false_eq_true, ↓reduceIte, M, StreamBits.machine, StreamBits.next, st, hnr,
      QueryMachine.read, StreamBits.symbol_read, StreamBits.output_succ_native]
    have hh' : (VirtualWord.Native.machine d).halted
        ((VirtualWord.Native.machine d).run (vinput j a) t) = false := hnr
    rw [QueryMachine.run_succ, QueryMachine.step, hh']
    simp only [vinput, Bool.false_eq_true, ↓reduceIte, StreamBits.State.mk.injEq,
      List.append_cancel_left_eq, true_and]
    exact ⟨rfl, rfl⟩
  have hstep_adv (a : α) (j : ℕ) (hj : j < N a) :
      M.step (encA a) (st a j (τ a j)) = st a (j + 1) 0 := by
    have hnh : M.halted (st a j (τ a j)) = false := by
      simp [M, StreamBits.machine, StreamBits.halted, st, Nat.not_le.mpr hj]
    rw [QueryMachine.step, hnh]
    simp only [Bool.false_eq_true, ↓reduceIte, M, StreamBits.machine, StreamBits.next, st,
      hhalt a j, vinput]
    rfl
  have hrun_round (a : α) (j : ℕ) (hj : j < N a) (t : ℕ) (ht : t ≤ τ a j) :
      M.runFrom (encA a) (st a j 0) t = st a j t := by
    induction t with
    | zero => rfl
    | succ t ih =>
      rw [QueryMachine.runFrom_succ, ih (by omega), hstep_run a j t (by omega) hj]
  have hrun_before (a : α) (j : ℕ) (hj : j ≤ N a) :
      M.runFrom (encA a) (st a 0 0) (StreamBits.timeBefore τ a j) = st a j 0 := by
    induction j with
    | zero => rfl
    | succ j ih =>
      rw [StreamBits.timeBefore, QueryMachine.runFrom_add, ih (by omega),
        QueryMachine.runFrom_succ, hrun_round a j (by omega) (τ a j) le_rfl,
        hstep_adv a j (by omega)]
  have hpre_round (a : α) (j : ℕ) (hj : j < N a) (t : ℕ) (ht : t < roundSteps a j) :
      M.halted (M.runFrom (encA a) (st a j 0) t) = false := by
    rw [hrun_round a j hj t (by dsimp [roundSteps] at ht; omega)]
    simp [M, StreamBits.machine, StreamBits.halted, st, Nat.not_le.mpr hj]
  have hpre_before (a : α) (j : ℕ) (hj : j ≤ N a) (t : ℕ)
      (ht : t < StreamBits.timeBefore τ a j) :
      M.halted (M.runFrom (encA a) (st a 0 0) t) = false := by
    induction j generalizing t with
    | zero => exact absurd ht (Nat.not_lt_zero _)
    | succ j ih =>
      rw [StreamBits.timeBefore] at ht
      rcases lt_or_ge t (StreamBits.timeBefore τ a j) with hlt | hge
      · exact ih (by omega) t hlt
      · rw [show t = StreamBits.timeBefore τ a j + (t - StreamBits.timeBefore τ a j) by omega,
          QueryMachine.runFrom_add, hrun_before a j (by omega)]
        exact hpre_round a j (by omega) (t - StreamBits.timeBefore τ a j)
          (by dsimp only [roundSteps]; omega)
  have hout_round (a : α) (j : ℕ) (hj : j < N a) :
      ((List.range (roundSteps a j)).map fun i ↦
        if M.halted (M.runFrom (encA a) (st a j 0) i) then []
        else M.emit (M.runFrom (encA a) (st a j 0) i,
          M.read (encA a) (M.runFrom (encA a) (st a j 0) i))).flatten = [bit (j, a)] := by
    rw [show roundSteps a j = τ a j + 1 from rfl, List.range_succ, List.map_append,
      List.flatten_append, List.map_singleton, List.flatten_singleton]
    have hzero : ((List.range (τ a j)).map fun i ↦
        if M.halted (M.runFrom (encA a) (st a j 0) i) then []
        else M.emit (M.runFrom (encA a) (st a j 0) i,
          M.read (encA a) (M.runFrom (encA a) (st a j 0) i))).flatten = [] := by
      rw [List.flatten_eq_nil_iff]
      intro l hl
      rw [List.mem_map] at hl
      obtain ⟨i, hi, rfl⟩ := hl
      rw [List.mem_range] at hi
      rw [hrun_round a j hj i (by omega)]
      have hnh : M.halted (st a j i) = false := by
        simp [M, StreamBits.machine, StreamBits.halted, st, Nat.not_le.mpr hj]
      rw [hnh]
      simp [M, StreamBits.machine, StreamBits.emit, st, hrun a j i hi]
    rw [hzero, List.nil_append, hrun_round a j hj (τ a j) le_rfl]
    have hnh : M.halted (st a j (τ a j)) = false := by
      simp [M, StreamBits.machine, StreamBits.halted, st, Nat.not_le.mpr hj]
    rw [hnh]
    simp [M, StreamBits.machine, StreamBits.emit, st, hhalt a j, hfinal a j]
  have hout_before (a : α) (j : ℕ) (hj : j ≤ N a) :
      M.outputFrom (encA a) (st a 0 0) (StreamBits.timeBefore τ a j) =
        (List.range j).map fun i ↦ bit (i, a) := by
    induction j with
    | zero => rfl
    | succ j ih =>
      simp only [QueryMachine.outputFrom, QueryMachine.output, QueryMachine.run,
        show M.finish = fun _ ↦ [] from rfl, List.append_nil] at ih ⊢
      rw [StreamBits.timeBefore, List.range_add, List.map_append, List.flatten_append,
        ih (by omega), List.range_succ (n := j), List.map_append, List.map_singleton]
      congr 1
      rw [List.map_map]
      have hcongr : (List.range (roundSteps a j)).map (fun i ↦
          if M.halted (M.runFrom (encA a) (st a 0 0) (StreamBits.timeBefore τ a j + i)) then []
          else M.emit (M.runFrom (encA a) (st a 0 0) (StreamBits.timeBefore τ a j + i),
            M.read (encA a) (M.runFrom (encA a) (st a 0 0)
              (StreamBits.timeBefore τ a j + i)))) =
          (List.range (roundSteps a j)).map (fun i ↦
            if M.halted (M.runFrom (encA a) (st a j 0) i) then []
            else M.emit (M.runFrom (encA a) (st a j 0) i,
              M.read (encA a) (M.runFrom (encA a) (st a j 0) i))) := by
        refine List.map_congr_left fun i _ ↦ ?_
        rw [QueryMachine.runFrom_add, hrun_before a j (by omega)]
      have hstep_eq : ({ M with init := st a 0 0, finish := fun _ ↦ [] } :
          QueryMachine StreamBits.State).step (encA a) = M.step (encA a) := funext fun _ ↦ rfl
      have hread_eq : ({ M with init := st a 0 0, finish := fun _ ↦ [] } :
          QueryMachine StreamBits.State).read (encA a) = M.read (encA a) := funext fun _ ↦ rfl
      rw [hstep_eq, hread_eq]
      simp only [Function.comp_def]
      convert (congrArg List.flatten hcongr).trans (hout_round a j (by omega)) using 4
      rfl
  obtain ⟨cN, hcN⟩ := length_encNat_le_of_poly hNpoly
  obtain ⟨C, hC⟩ := VirtualWord.Native.budget_le eS tm
  have hinit_inSpace : ComputableInSpace (fun a ↦ st a 0 0) encA StreamBits.encState
      (fun a ↦ Nat.log2 (encA a).length + 1) := by
    have hinit_log : ComputableInLogSpace (fun a ↦ st a 0 0) encA StreamBits.encState := by
      have h0 : ComputableInLogSpace (fun _ : α ↦ (0 : ℕ)) encA encNat :=
        ComputableInLogSpace.const 0
      have hpre0 : ComputableInLogSpace (fun _ : α ↦ frame (encNat 0)) encA encBits :=
        ComputableInLogSpace.const _
      have hacc0 : ComputableInLogSpace (fun _ : α ↦ ([] : List Bool)) encA encBits :=
        ComputableInLogSpace.const []
      have hcfg0 : ComputableInLogSpace (fun _ : α ↦ init d) encA eCfg :=
        ComputableInLogSpace.const _
      have hmk : ComputableInLogSpace
          (fun p : ℕ × ℕ × List Bool × List Bool × SCfg ↦
            StreamBits.State.mk p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)
          (encPair encNat (encPair encNat (encPair encBits (encPair encBits eCfg))))
          StreamBits.encState :=
        ComputableInLogSpace.of_eq fun _ ↦ rfl
      exact hmk.comp (ComputableInLogSpace.pair h0
        (ComputableInLogSpace.pair hN
          (ComputableInLogSpace.pair hpre0 (ComputableInLogSpace.pair hacc0 hcfg0))))
    refine (hinit_log.inSpace_of_length_log ?_).mono_le (fun _ ↦ Nat.le_succ _)
    refine ⟨4 * cN + 20 + 2 * (eCfg (init d)).length + 10, fun a ↦ ?_⟩
    rw [StreamBits.length_encState]
    dsimp only [st]
    have hNa := hcN a
    have h0 : (encNat 0).length = 0 := rfl
    have hfr : (frame (encNat 0)).length = 1 := rfl
    have hnil : ((VirtualWord.Native.machine d).output (vinput 0 a) 0).length = 0 := rfl
    have hcfg0 : (eCfg ((VirtualWord.Native.machine d).run (vinput 0 a) 0)).length =
        (eCfg (init d)).length := rfl
    rw [h0, hfr, hnil, hcfg0]
    nlinarith
  have hsize : ∃ c, ∀ a, ∀ t ≤ StreamBits.timeBefore τ a (N a),
      (StreamBits.encState (M.runFrom (encA a) (st a 0 0) t)).length ≤
        c * (Nat.log2 (encA a).length + 1) := by
    refine ⟨10 * cN + 40 + 4 * C * ((cB + 1) * (2 * cN + 4)), fun a t ht ↦ ?_⟩
    have hex : ∃ j ≤ N a, ∃ u,
        M.runFrom (encA a) (st a 0 0) t = st a j u ∧ u ≤ τ a j := by
      have hgo : ∀ (k' : ℕ), k' ≤ N a → ∀ t ≤ StreamBits.timeBefore τ a k',
          ∃ j ≤ k', ∃ u, M.runFrom (encA a) (st a 0 0) t = st a j u ∧ u ≤ τ a j := by
        intro k'
        induction k' with
        | zero =>
          intro _ t ht
          have ht0 : t = 0 := Nat.le_zero.mp ht
          subst ht0; exact ⟨0, le_rfl, 0, rfl, Nat.zero_le _⟩
        | succ k' ih =>
          intro hk' t ht
          rcases le_or_gt t (StreamBits.timeBefore τ a k') with hle | hgt
          · obtain ⟨j, hj, u, heq, hu⟩ := ih (by omega) t hle
            exact ⟨j, by omega, u, heq, hu⟩
          · rw [StreamBits.timeBefore] at ht
            rcases lt_or_eq_of_le ht with hlt | heq
            · have hu : t - StreamBits.timeBefore τ a k' ≤ τ a k' := by omega
              refine ⟨k', by omega, t - StreamBits.timeBefore τ a k', ?_, hu⟩
              have hteq : t = StreamBits.timeBefore τ a k' +
                  (t - StreamBits.timeBefore τ a k') := by omega
              conv_lhs => rw [hteq]
              rw [QueryMachine.runFrom_add, hrun_before a k' (by omega),
                hrun_round a k' (by omega) _ hu]
            · subst heq
              exact ⟨k' + 1, le_rfl, 0, hrun_before a (k' + 1) hk', Nat.zero_le _⟩
      exact hgo (N a) le_rfl t ht
    obtain ⟨j, hj, u, hrun_eq, hu⟩ := hex
    rw [hrun_eq]
    have hj_len : (encNat j).length ≤ cN * (Nat.log2 (encA a).length + 1) :=
      (length_encNat_mono' hj).trans (hcN a)
    have hN_len : (encNat (N a)).length ≤ cN * (Nat.log2 (encA a).length + 1) := hcN a
    have hpre_len : (frame (encNat j)).length = 2 * (encNat j).length + 1 := length_frame _
    have hacc_len : ((VirtualWord.Native.machine d).output (vinput j a) u).length ≤ 1 :=
      (StreamBits.length_output_mono_native d _ hu).trans (by rw [hfinal a j]; simp)
    have hcfg_len := VirtualWord.Native.length_native_run_le_of_space eS tm (vinput j a) u
      (cB * (Nat.log2 (vinput j a).length + 1)) (htm (j, a)).2.2
    have hbud := hC (vinput j a).length (cB * (Nat.log2 (vinput j a).length + 1))
    have hlog := log2_add_le' (2 * (encNat j).length + 1) (encA a).length
    have hvlen : (vinput j a).length = 2 * (encNat j).length + 1 + (encA a).length := by
      simp [vinput, length_frame]
    rw [hvlen] at hbud hcfg_len
    have hL : 1 ≤ Nat.log2 (encA a).length + 1 := Nat.le_add_left _ _
    have hlog_le : Nat.log2 (2 * (encNat j).length + 1 + (encA a).length) + 1 ≤
        (2 * cN + 4) * (Nat.log2 (encA a).length + 1) := by nlinarith
    have hcfg_le : (eCfg ((VirtualWord.Native.machine d).run (vinput j a) u)).length ≤
        C * ((cB + 1) * (2 * cN + 4) * (Nat.log2 (encA a).length + 1)) := by
      refine (hcfg_len.trans hbud).trans (Nat.mul_le_mul_left C ?_)
      nlinarith
    rw [StreamBits.length_encState]
    dsimp only [st]
    nlinarith
  obtain ⟨tOut, cOut, hcomp⟩ := M.computableInSpaceFrom StreamBits.query_inSpace
    (StreamBits.next_inSpace d) StreamBits.emit_inSpace StreamBits.halted_inSpace
    StreamBits.finish_inSpace (fun a ↦ StreamBits.timeBefore τ a (N a))
    (fun a ↦ Nat.log2 (encA a).length + 1) hinit_inSpace
    (fun a ↦ by
      rw [hrun_before a (N a) le_rfl]
      simp [M, StreamBits.machine, StreamBits.halted, st])
    (fun a t ht ↦ hpre_before a (N a) le_rfl t ht)
    (fun a ↦ show encBits ((List.range (N a)).map fun i ↦ bit (i, a)) = _ from
      (hout_before a (N a) le_rfl).symm)
    (fun _ ↦ le_rfl) hsize
  exact ⟨tOut, cOut, hcomp⟩

end Turing.MultiTapeTM
