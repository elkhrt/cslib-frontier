/-
Copyright (c) 2026 The FormalPapers contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.BPP
public import CslibFrontier.Computability.Complexity.Classes.Promise.Probabilistic
public import CslibFrontier.Computability.Complexity.Problems.ThreeSAT
public import CslibFrontier.Computability.Complexity.Problems.USAT
public import CslibFrontier.Computability.Probabilistic.PPT
public import CslibFrontier.Logics.Propositional.CNF.ModelCount
public import CslibFrontier.Logics.Propositional.CNF.Vars

import CslibFrontier.Computability.Complexity.Classes.BPP.Amplification
import CslibFrontier.Computability.Complexity.Classes.ValiantVazirani.Reduction
import CslibFrontier.Computability.Complexity.CookLevin.Completeness
import CslibFrontier.Computability.Complexity.Problems.SAT.PolyTime
import CslibFrontier.Computability.Complexity.Problems.SharpThreeSAT
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Sum
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.OfBits
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeLoops
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Computability.Probabilistic.Repeat
import CslibFrontier.Computability.Probabilistic.Sampling
import CslibFrontier.Foundations.Data.BitString.Affine
import CslibFrontier.Foundations.Data.BitString.WordCount
import CslibFrontier.Foundations.Data.List.Lookup
import CslibFrontier.Logics.Propositional.CNF.PolyTime
import CslibFrontier.Probability.BitString.UniformSplit
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.EventBind
import Mathlib.Data.List.GetD
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Valiant–Vazirani `PromiseBPP` Collapse and 3SAT Isolation with Probability `1 / (8n)`

This module establishes two textbook Valiant–Vazirani consequences over standard multi-tape Turing
machine complexity classes:
1. If `PromiseUSAT` (or its width-3 restriction `PromiseThreeUSAT`) lies in `PromiseBPP encCNF`,
   then `NP enc ⊆ BPP enc` for every instance encoding `enc`.
2. A uniform probabilistic polynomial-time 3SAT isolation algorithm `valiantVazirani3SAT` mapping
   any width-3 formula `W` on `n ≥ 1` variables to a width-3 formula `W'` that is uniquely
   satisfiable with probability at least `1 / (8n)` when `W` is satisfiable, and unsatisfiable
   whenever `W` is unsatisfiable.

## Main definitions

* `CslibFrontier.Complexity.PromiseThreeUSAT`: promise problem restricting `PromiseUSAT` to formulas
  with clauses of length at most `3`.
* `CslibFrontier.Complexity.valiantVazirani3SAT`: randomized polynomial-time 3SAT-to-`Unique-SAT`
  isolation algorithm.

## Main results

* `CslibFrontier.Complexity.polyTimeReducible_promiseUSAT_promiseThreeUSAT`: deterministic
  polynomial-time promise reduction `PromiseUSAT ≤_p PromiseThreeUSAT`.
* `CslibFrontier.Complexity.NP_subset_BPP_of_PromiseUSAT_mem_PromiseBPP`:
  `PromiseUSAT ∈ PromiseBPP encCNF → NP enc ⊆ BPP enc`.
* `CslibFrontier.Complexity.NP_subset_BPP_of_PromiseThreeUSAT_mem_PromiseBPP`:
  `PromiseThreeUSAT ∈ PromiseBPP encCNF → NP enc ⊆ BPP enc`.
* `CslibFrontier.Complexity.valiantVazirani_threeSAT`: `IsPPTOn` runtime, `1 / (8n)` isolation lower
  bound on satisfiable 3SAT formulas, and zero false positives on unsatisfiable 3SAT formulas.
-/

public section

namespace CslibFrontier.Complexity

open Cslib Cslib.Complexity Cslib.Logic.PL Cslib.Probability
open Turing.MultiTapeTM

/-- Promise problem `PromiseThreeUSAT`: `Unique-SAT` restricted to 3SAT formulas (clauses of length
at most `3`). -/
def PromiseThreeUSAT : PromiseProblem (CNF ℕ) where
  yes := {φ | (∀ c ∈ φ, c.length ≤ 3) ∧ φ ∈ USAT}
  no := {φ | (∀ c ∈ φ, c.length ≤ 3) ∧ φ ∈ UNSAT}
  disjoint := Set.disjoint_left.mpr fun _ hy hn ↦ disjoint_USAT_UNSAT.le_bot ⟨hy.2, hn.2⟩

private lemma one_add_mul_mul_one_sub_pow_le_one {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    ∀ m : ℕ, (1 + (m : ℝ) * x) * (1 - x) ^ m ≤ 1
  | 0 => by simp
  | m + 1 => by
    have ih := one_add_mul_mul_one_sub_pow_le_one hx0 hx1 m
    have hpow_nn : 0 ≤ (1 - x) ^ m := pow_nonneg (by linarith) m
    have hstep : (1 + ((m + 1 : ℕ) : ℝ) * x) * (1 - x) ≤ 1 + (m : ℝ) * x := by
      push_cast
      have hsq : 0 ≤ ((m : ℝ) + 1) * x ^ 2 := by positivity
      nlinarith
    calc
      (1 + ((m + 1 : ℕ) : ℝ) * x) * (1 - x) ^ (m + 1) =
          ((1 + ((m + 1 : ℕ) : ℝ) * x) * (1 - x)) * (1 - x) ^ m := by rw [pow_succ']; ring
      _ ≤ (1 + (m : ℝ) * x) * (1 - x) ^ m := mul_le_mul_of_nonneg_right hstep hpow_nn
      _ ≤ 1 := ih

private lemma one_sub_pow_le_inv_one_add_mul {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (m : ℕ) :
    (1 - x) ^ m ≤ 1 / (1 + (m : ℝ) * x) := by
  have hpos : 0 < 1 + (m : ℝ) * x := by positivity
  rw [le_div_iff₀ hpos, mul_comm]
  exact one_add_mul_mul_one_sub_pow_le_one hx0 hx1 m

private lemma one_sub_mul_le_pow_nonneg {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    ∀ m : ℕ, 1 - (m : ℝ) * x ≤ (1 - x) ^ m
  | 0 => by simp
  | m + 1 => by
    have ih := one_sub_mul_le_pow_nonneg hx0 hx1 m
    calc
      1 - ((m + 1 : ℕ) : ℝ) * x ≤ (1 - (m : ℝ) * x) * (1 - x) := by
        push_cast; nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) m) (sq_nonneg x)]
      _ ≤ (1 - x) ^ m * (1 - x) := mul_le_mul_of_nonneg_right ih (by linarith)
      _ = (1 - x) ^ (m + 1) := (pow_succ (1 - x) m).symm

/-- Deterministic polynomial-time promise reduction from `PromiseUSAT` to `PromiseThreeUSAT` via
the count-preserving clause-splitting reduction `toSharpThreeSAT`. -/
theorem polyTimeReducible_promiseUSAT_promiseThreeUSAT :
    PromiseProblem.PolyTimeReducible encCNF encCNF PromiseUSAT PromiseThreeUSAT := by
  refine ⟨toSharpThreeSAT, computableInPolyTime_toSharpThreeSAT, ?_, ?_⟩
  · intro φ hφ
    rw [yes_PromiseUSAT, SharpSAT.mem_USAT_iff] at hφ
    refine ⟨fun c hc ↦ length_le_three_of_mem_toSharpThreeSAT hc, ?_⟩
    rw [SharpSAT.mem_USAT_iff, SharpSAT, modelCount_toSharpThreeSAT]
    exact hφ
  · intro φ hφ
    rw [no_PromiseUSAT, mem_UNSAT, ← CNF.modelCount_pos_iff, not_lt, Nat.le_zero] at hφ
    refine ⟨fun c hc ↦ length_le_three_of_mem_toSharpThreeSAT hc, ?_⟩
    rw [mem_UNSAT, ← CNF.modelCount_pos_iff, not_lt, Nat.le_zero, modelCount_toSharpThreeSAT]
    exact hφ

/-- Pad a `CNF ℕ` formula `ψ` with `k` copies of the unit clause `[(v_fresh, true)]` on the fresh
variable `v_fresh = ψ.vars.foldl max 0 + 1`, preserving `USAT` and `UNSAT` for `1 ≤ k` while forcing
`(encCNF (padCNF k ψ)).length ≥ k`. -/
def padCNF (k : ℕ) (ψ : CNF ℕ) : CNF ℕ :=
  let v := ψ.vars.foldl max 0 + 1
  ψ ++ List.replicate k [(v, true)]

private lemma le_foldl_max : ∀ (l : List ℕ) (init : ℕ),
    init ≤ l.foldl max init ∧ ∀ x ∈ l, x ≤ l.foldl max init
  | [], init => ⟨le_rfl, fun _ h ↦ by cases h⟩
  | a :: as, init => by
    obtain ⟨hinit, hmem⟩ := le_foldl_max as (max init a)
    refine ⟨(le_max_left init a).trans hinit, fun x hx ↦ ?_⟩
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact (le_max_right init x).trans hinit
    · exact hmem x hx'

private lemma padCNF_mem_USAT_and_UNSAT {k : ℕ} (hk : 1 ≤ k) (ψ : CNF ℕ) :
    k ≤ (encCNF (padCNF k ψ)).length ∧
    (ψ ∈ USAT → padCNF k ψ ∈ USAT) ∧
    (ψ ∈ UNSAT → padCNF k ψ ∈ UNSAT) := by
  set v := ψ.vars.foldl max 0 + 1
  have hv_fresh : v ∉ ψ.vars := by
    intro hv
    have hle := (le_foldl_max ψ.vars 0).2 v hv
    omega
  have hlen : k ≤ (encCNF (padCNF k ψ)).length := by
    calc
      k ≤ ψ.length + k := Nat.le_add_left k ψ.length
      _ = (padCNF k ψ).length := by simp [padCNF]
      _ ≤ (encCNF (padCNF k ψ)).length :=
        length_le_length_encList (encList (encPair encNat encBool)) (padCNF k ψ)
  refine ⟨hlen, ?_, ?_⟩
  · rintro ⟨σ, hσ, huniq⟩
    let σ' : ℕ → Bool := fun u ↦ if u = v then true else σ u
    have hψ_σ' : ψ.eval σ' = true := by
      rw [← hσ]
      exact CNF.eval_congr fun u hu ↦ by
        have huv : u ≠ v := fun heq ↦ hv_fresh (heq ▸ hu)
        simp [σ', huv]
    have hrep_σ' : CNF.eval σ' (List.replicate k [(v, true)]) = true := by
      rw [CNF.eval_eq_true_iff]
      intro c hc
      rw [List.mem_replicate.mp hc |>.2]
      simp [Clause.eval, Literal.eval, σ']
    refine ⟨σ', by rw [padCNF, CNF.eval_append, hψ_σ', hrep_σ', Bool.and_self], fun τ hτ u hu ↦ ?_⟩
    rw [padCNF, CNF.eval_append, Bool.and_eq_true] at hτ
    rw [padCNF, CNF.vars_append, List.mem_append] at hu
    rcases hu with hu_ψ | hu_rep
    · have huv : u ≠ v := fun heq ↦ hv_fresh (heq ▸ hu_ψ)
      simp only [σ', huv, ↓reduceIte]
      exact huniq τ hτ.1 u hu_ψ
    · have hmem_c : [(v, true)] ∈ List.replicate k [(v, true)] :=
        List.mem_replicate.mpr ⟨by omega, rfl⟩
      have hv_true : τ v = true := by
        simpa [Clause.eval, Literal.eval] using CNF.eval_eq_true_iff τ _ |>.mp hτ.2 _ hmem_c
      have huv : u = v := by
        rw [CNF.mem_vars] at hu_rep
        obtain ⟨c, hc, b, hl⟩ := hu_rep
        rw [List.mem_replicate.mp hc |>.2] at hl
        exact congrArg Prod.fst (List.mem_singleton.mp hl)
      subst huv
      simp [σ', hv_true]
  · intro hunsat ⟨τ, hτ⟩
    rw [padCNF, CNF.eval_append, Bool.and_eq_true] at hτ
    exact hunsat ⟨τ, hτ.1⟩

private lemma computableInPolyTime_padCNF :
    ComputableInPolyTime (fun kp : ℕ × CNF ℕ ↦ padCNF kp.1 kp.2)
      (encPair encUnary encCNF) encCNF := by
  open ComputableInPolyTime in
  let encIn := encPair encUnary encCNF
  have hk := fst encUnary encCNF
  have hψ := snd encUnary encCNF
  have hvars := (CNF.computableInPolyTime_vars encNat).comp' hψ
  have hmax : ComputableInPolyTime (fun xs : List ℕ ↦ xs.foldl max 0) (encList encNat) encNat := by
    have hstep : ComputableInPolyTime (fun ab : ℕ × ℕ ↦ max ab.1 ab.2)
        (encPair encNat encNat) encNat :=
      ((binary_le' (fst encNat encNat) (snd encNat encNat)).ite'
        (snd encNat encNat) (fst encNat encNat)).of_enc_eq fun ab ↦
        congrArg encNat (by
          split_ifs with h
          · exact max_eq_right (of_decide_eq_true h)
          · exact max_eq_left (by simp at h; exact h.le))
    refine foldl' id' (const 0) hstep (B := fun xs ↦ (encList encNat xs).length + 2)
      (.add .self (.const 2)) ?_
    intro xs i _
    have htake : ∀ (j : ℕ) (ys : List ℕ),
        (encList encNat (ys.take j)).length ≤ (encList encNat ys).length := by
      intro j
      induction j with
      | zero => intro _; simp
      | succ j ih =>
        rintro (_ | ⟨y, ys⟩)
        · simp
        · have := ih ys
          rw [List.take_succ_cons, encList_cons, encList_cons, List.length_append,
            List.length_append]
          omega
    have hmem_len : ∀ (y : ℕ) (ys : List ℕ), y ∈ ys →
        (encNat y).length ≤ (encList encNat ys).length := by
      intro y ys
      induction ys with
      | nil => intro h; cases h
      | cons z zs ih =>
        intro h
        rcases List.mem_cons.mp h with rfl | hm
        · rw [encList_cons, List.length_append, length_frame]; omega
        · have := ih hm; rw [encList_cons, List.length_append, length_frame]; omega
    have hfold_mem : ∀ ys : List ℕ, ys.foldl max 0 = 0 ∨ ys.foldl max 0 ∈ ys := by
      intro ys
      induction ys using List.reverseRecOn with
      | nil => exact .inl rfl
      | append_singleton ys y ih =>
        simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
        rcases le_total (ys.foldl max 0) y with hle | hge
        · rw [max_eq_right hle]; exact .inr (by simp)
        · rw [max_eq_left hge]
          rcases ih with h0 | hm
          · exact .inl h0
          · exact .inr (by simp [hm])
    rcases hfold_mem (xs.take i) with h0 | hm
    · rw [h0]; simp
    · exact (hmem_len _ _ hm).trans ((htake i xs).trans (by omega))
  have hv := binary_add.comp' ((hmax.comp' hvars).prod (const 1))
  have hlit : ComputableInPolyTime (fun kp : ℕ × CNF ℕ ↦ ([(kp.2.vars.foldl max 0 + 1, true)] :
      Clause ℕ)) encIn (encList (encPair encNat encBool)) :=
    cons' (hv.prod (const true)) (const [])
  have hrep : ComputableInPolyTime
      (fun kp : ℕ × CNF ℕ ↦ List.replicate kp.1 [(kp.2.vars.foldl max 0 + 1, true)])
      encIn encCNF :=
    replicate hk hlit
  exact listAppend' hψ hrep

/-- If `PromiseUSAT ∈ PromiseBPP encCNF`, then `NP enc ⊆ BPP enc` for every instance encoding
`enc`. -/
theorem NP_subset_BPP_of_PromiseUSAT_mem_PromiseBPP
    (hUSAT : PromiseUSAT ∈ PromiseBPP encCNF) {α : Type} (enc : α ↪ List Bool) :
    NP enc ⊆ BPP enc := by
  classical
  intro L hL
  obtain ⟨g, hg, hgL⟩ := CookLevin.SAT_npHard enc L hL
  obtain ⟨c, d, hlen_g⟩ := hg.polyBounded_length.exists_le
  obtain ⟨pV, V, hV, hsolves⟩ :=
    mem_PromiseBPP_iff_forall_solvesWithErrorExponent.mp hUSAT (Polynomial.X + 10)
  let N (a : α) : ℕ := c * ((enc a).length + 1) ^ d + 1
  let W (a : α) : ℕ := (N a + 2) ^ 2
  have hN_poly : ComputableInPolyTime N enc encUnary := by
    open ComputableInPolyTime in
    let pol : Polynomial ℕ := Polynomial.C c * (Polynomial.X + 1) ^ d + 1
    exact ((unary_eval pol).comp' (encoding_length enc)).of_enc_eq fun a ↦
      congrArg encUnary (by simp [pol, N])
  have hW_poly : ComputableInPolyTime W enc encUnary := by
    open ComputableInPolyTime in
    have hN2 := unary_add.comp' (hN_poly.prod (const 2))
    exact (unary_mul.comp' (hN2.prod hN2)).of_enc_eq fun a ↦
      congrArg encUnary (sq (N a + 2))
  let solver (ψ : CNF ℕ) : ProbComp Bool :=
    (fun coins ↦ V (ψ, coins)) <$> BitString.sampleList (pV.eval (encCNF ψ).length)
  have hsolver_ppt : IsPPTOn encCNF encBool solver :=
    IsPPTOn.of_seeded (f := V)
      ((ComputableInPolyTime.unary_eval pV).comp' (ComputableInPolyTime.encoding_length encCNF)) hV
  let genPadded (a : α) : ProbComp (CNF ℕ) :=
    (fun seed ↦ padCNF (N a) (ValiantVazirani.reduce (g a, seed))) <$>
      BitString.sampleList (W a)
  have hgen_ppt : IsPPTOn enc encCNF genPadded := by
    refine IsPPTOn.of_seeded
      (f := fun aw : α × List Bool ↦ padCNF (N aw.1) (ValiantVazirani.reduce (g aw.1, aw.2)))
      hW_poly ?_
    open ComputableInPolyTime in
    have ha := fst enc encBits
    have hseed := snd enc encBits
    have hred := ValiantVazirani.computableInPolyTime_reduce.comp' ((hg.comp' ha).prod hseed)
    exact computableInPolyTime_padCNF.comp' ((hN_poly.comp' ha).prod hred)
  let oneTrial (a : α) : ProbComp Bool := genPadded a >>= solver
  have hone_ppt : IsPPTOn enc encBool oneTrial := hgen_ppt.bind hsolver_ppt
  let trials (a : α) : ℕ := 32 * (N a + 3)
  have htrials_poly : ComputableInPolyTime trials enc encUnary := by
    open ComputableInPolyTime in
    exact unary_mul.comp' ((const 32).prod (unary_add.comp' (hN_poly.prod (const 3))))
  let fullProg (a : α) : ProbComp Bool :=
    (fun votes : List Bool ↦ votes.any id) <$> OracleComp.replicate (trials a) (oneTrial a)
  have hfull_ppt : IsPPTOn enc encBool fullProg := by
    open ComputableInPolyTime in
    exact (hone_ppt.replicate_bool htrials_poly).map
      (anyWithEncoding (encA := encBool) (encL := encBits) (encP := encBits)
        (test := fun p ↦ p.2) (snd encBits encBool) id' id')
  rw [← ofSet_mem_PromiseBPP, mem_PromiseBPP_iff_exists_isPPTOn]
  refine ⟨fullProg, hfull_ppt, fun a ha ↦ ?_, fun a ha ↦ ?_⟩
  · have hsat : g a ∈ SAT := (hgL a).mp ha
    have hvars_le : (g a).vars.length ≤ N a := by
      have h1 : (g a).vars.length ≤ (encCNF (g a)).length := SAT.length_vars_le (g a)
      have h2 := hlen_g a
      dsimp only [N]
      omega
    have hrnd_le : ValiantVazirani.randomBits (g a) ≤ W a :=
      (ValiantVazirani.randomBits_le (g a)).trans (Nat.pow_le_pow_left (by omega) 2)
    have hvv := ValiantVazirani.three_mul_two_pow_le_card_reduce_mem_USAT hsat hrnd_le
    have hgen_yes : (3 : ℝ) / (32 * ((N a : ℝ) + 3)) ≤
        ((ProbComp.eval (genPadded a)).toOuterMeasure PromiseUSAT.yes).toReal := by
      simp only [genPadded, ProbComp.eval_map, BitString.eval_sampleList,
        BitString.toOuterMeasure_map_uniformList_toReal]
      have hsub : (Finset.univ.filter fun r : Fin (W a) → Bool ↦
          ValiantVazirani.reduce (g a, List.ofFn r) ∈ USAT) ⊆
          Finset.univ.filter fun r : Fin (W a) → Bool ↦
            padCNF (N a) (ValiantVazirani.reduce (g a, List.ofFn r)) ∈ PromiseUSAT.yes := by
        intro r hr
        rw [Finset.mem_filter] at hr ⊢
        rw [yes_PromiseUSAT]
        exact ⟨Finset.mem_univ _, (padCNF_mem_USAT_and_UNSAT (k :=
          N a) (Nat.succ_pos _) _).2.1 hr.2⟩
      have hcard_le := Finset.card_le_card hsub
      have hM_le : 32 * ((g a).vars.length + 3) ≤ 32 * (N a + 3) := by omega
      have hvv' : 3 * 2 ^ W a ≤ 32 * (N a + 3) *
          (Finset.univ.filter fun r : Fin (W a) → Bool ↦
            padCNF (N a) (ValiantVazirani.reduce (g a, List.ofFn r)) ∈ PromiseUSAT.yes).card :=
        hvv.trans ((Nat.mul_le_mul_right _ hM_le).trans (Nat.mul_le_mul_left _ hcard_le))
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have hcast : (3 : ℝ) * (2 : ℝ) ^ W a ≤
          (32 * ((N a : ℝ) + 3)) * ((Finset.univ.filter fun r : Fin (W a) → Bool ↦
            padCNF (N a) (ValiantVazirani.reduce (g a, List.ofFn r)) ∈
              PromiseUSAT.yes).card : ℝ) := by
        exact_mod_cast hvv'
      linarith
    have hsol_yes (ψ : CNF ℕ) (hψ : ψ ∈ PromiseUSAT.yes) : (3 / 4 : ℝ) ≤ Pr[solver ψ] := by
      have herr := (hsolves ψ).1 hψ
      have hcast : (2 : ℝ) ^ ((encCNF ψ).length + 10) *
          ((2 : ℝ) ^ pV.eval (encCNF ψ).length -
            acceptCount V ψ (pV.eval (encCNF ψ).length)) ≤
          2 ^ pV.eval (encCNF ψ).length := by
        have h1 := errorExponentAt_true_iff.mp herr
        simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_ofNat] at h1
        simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
          Nat.cast_sub acceptCount_le_two_pow] using Nat.cast_le (α := ℝ).mpr h1
      have hpow4 : (4 : ℝ) ≤ (2 : ℝ) ^ ((encCNF ψ).length + 10) := by
        calc (4 : ℝ) = (2 : ℝ) ^ 2 := by norm_num
          _ ≤ (2 : ℝ) ^ ((encCNF ψ).length + 10) :=
            pow_le_pow_right₀ (by norm_num) (by omega)
      dsimp only [solver]
      rw [probability_sampleList_verifier, div_le_div_iff₀ (by norm_num) (by positivity)]
      have hacc_le : (acceptCount V ψ (pV.eval (encCNF ψ).length) : ℝ) ≤
          (2 : ℝ) ^ pV.eval (encCNF ψ).length := by
        exact_mod_cast acceptCount_le_two_pow (V := V) (a := ψ) (n := pV.eval (encCNF ψ).length)
      nlinarith
    have hone_ge : (1 : ℝ) / (16 * ((N a : ℝ) + 3)) ≤ Pr[oneTrial a] := by
      have h := PMF.toOuterMeasure_bind_ge_mul (ProbComp.eval (genPadded a))
        (fun ψ ↦ ProbComp.eval (solver ψ)) PromiseUSAT.yes {true}
        (by norm_num : (0 : ℝ) ≤ 3 / 4) hgen_yes
        fun ψ _ hψ ↦ by simpa only [PMF.toOuterMeasure_apply_singleton] using hsol_yes ψ hψ
      rw [← ProbComp.eval_bind, PMF.toOuterMeasure_apply_singleton] at h
      have hfrac : (1 : ℝ) / (16 * ((N a : ℝ) + 3)) ≤
          (3 : ℝ) / (32 * ((N a : ℝ) + 3)) * (3 / 4) := by
        have hpos : (0 : ℝ) < (N a : ℝ) + 3 := by positivity
        rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
        linarith
      exact hfrac.trans h
    have hrej_eq : Pr[Bool.not <$> fullProg a] = (1 - Pr[oneTrial a]) ^ trials a := by
      have hev : Bool.not <$> fullProg a =
          (fun votes : List Bool ↦
            decide (votes ∈ {vs : List Bool | ∀ b ∈ vs, (!b) = true})) <$>
              OracleComp.replicate (trials a) (oneTrial a) := by
        simp only [fullProg, Functor.map_map, Set.mem_ofPred_eq]
        congr 1; funext votes
        cases h : votes.any id <;> simp_all [List.any_eq_true]
      rw [hev, ProbComp.probability_map_decide_mem, ProbComp.toOuterMeasure_replicate_forall,
        ENNReal.toReal_pow]
      congr 1
      have hnot : ((ProbComp.eval (oneTrial a)).toOuterMeasure {b | (!b) = true}).toReal =
          Pr[Bool.not <$> oneTrial a] := by
        rw [← ProbComp.probability_map_decide_mem (s := {b : Bool | (!b) = true})]
        congr 2
      rw [hnot, ProbComp.probability_not]
    have hp_le1 : Pr[oneTrial a] ≤ 1 := by
      have := PMF.toOuterMeasure_le_one (ProbComp.eval (oneTrial a)) {true}
      simpa [PMF.toOuterMeasure_apply_singleton] using ENNReal.toReal_mono ENNReal.one_ne_top this
    have hp_nn : 0 ≤ Pr[oneTrial a] := ENNReal.toReal_nonneg
    have hrej_le : Pr[Bool.not <$> fullProg a] ≤ 1 / 3 := by
      rw [hrej_eq]
      calc
        (1 - Pr[oneTrial a]) ^ trials a ≤
            (1 - (1 : ℝ) / (16 * ((N a : ℝ) + 3))) ^ trials a := by
          refine pow_le_pow_left₀ (by linarith) (by linarith) _
        _ ≤ 1 / (1 + (trials a : ℝ) * ((1 : ℝ) / (16 * ((N a : ℝ) + 3)))) := by
          refine one_sub_pow_le_inv_one_add_mul (by positivity) ?_ _
          rw [div_le_one (by positivity)]; linarith [show (0 : ℝ) ≤ N a by positivity]
        _ = 1 / 3 := by
          dsimp [trials]
          push_cast
          have hne : ((N a : ℝ) + 3) ≠ 0 := by positivity
          field_simp
          ring
    have hprob_not := ProbComp.probability_not (fullProg a)
    linarith
  · have hunsat : g a ∈ UNSAT := mt (hgL a).mpr ha
    have hone_le : Pr[oneTrial a] ≤ 1 / (2 : ℝ) ^ (N a + 10) := by
      have hsupp_no : ∀ ψ ∈ (ProbComp.eval (genPadded a)).support,
          ψ ∈ PromiseUSAT.no ∧ N a ≤ (encCNF ψ).length := by
        intro ψ hψ
        simp only [genPadded, ProbComp.eval_map, BitString.eval_sampleList,
          PMF.mem_support_map_iff] at hψ
        obtain ⟨seed, _, rfl⟩ := hψ
        have hpad := padCNF_mem_USAT_and_UNSAT (k := N a) (Nat.succ_pos _)
          (ValiantVazirani.reduce (g a, seed))
        exact ⟨hpad.2.2 (ValiantVazirani.reduce_mem_UNSAT hunsat seed), hpad.1⟩
      have hstep : ∀ ψ ∈ (ProbComp.eval (genPadded a)).support,
          ((ProbComp.eval (solver ψ)).toOuterMeasure {true}).toReal ≤
            1 / (2 : ℝ) ^ (N a + 10) := by
        intro ψ hψ
        obtain ⟨hno, hlen_ψ⟩ := hsupp_no ψ hψ
        have herr := errorExponentAt_false_iff.mp ((hsolves ψ).2 hno)
        simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_ofNat] at herr
        have hcast : (2 : ℝ) ^ ((encCNF ψ).length + 10) *
            (acceptCount V ψ (pV.eval (encCNF ψ).length) : ℝ) ≤
            (2 : ℝ) ^ pV.eval (encCNF ψ).length := by exact_mod_cast herr
        have hpow_ge : (2 : ℝ) ^ (N a + 10) ≤ (2 : ℝ) ^ ((encCNF ψ).length + 10) :=
          pow_le_pow_right₀ (by norm_num) (by omega)
        rw [PMF.toOuterMeasure_apply_singleton]
        dsimp only [solver]
        change Pr[(fun coins ↦ V (ψ, coins)) <$>
          BitString.sampleList (pV.eval (encCNF ψ).length)] ≤ _
        rw [probability_sampleList_verifier, div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [show (0 : ℝ) ≤ acceptCount V ψ (pV.eval (encCNF ψ).length) by positivity]
      have hfail := PMF.toOuterMeasure_bind_failure_toReal_le
        (ProbComp.eval (genPadded a)) (fun ψ ↦ ProbComp.eval (solver ψ)) Set.univ {true}
        (by positivity : 0 ≤ 1 / (2 : ℝ) ^ (N a + 10))
        fun ψ hψ _ ↦ hstep ψ hψ
      have hemp0 : (ProbComp.eval (genPadded a)).toOuterMeasure ∅ = 0 := by simp
      rw [Set.compl_univ, hemp0, ENNReal.toReal_zero, zero_add,
        ← ProbComp.eval_bind, PMF.toOuterMeasure_apply_singleton] at hfail
      exact hfail
    have hrej_eq : Pr[Bool.not <$> fullProg a] = (1 - Pr[oneTrial a]) ^ trials a := by
      have hev : Bool.not <$> fullProg a =
          (fun votes : List Bool ↦
            decide (votes ∈ {vs : List Bool | ∀ b ∈ vs, (!b) = true})) <$>
              OracleComp.replicate (trials a) (oneTrial a) := by
        simp only [fullProg, Functor.map_map, Set.mem_ofPred_eq]
        congr 1; funext votes
        cases h : votes.any id <;> simp_all [List.any_eq_true]
      rw [hev, ProbComp.probability_map_decide_mem, ProbComp.toOuterMeasure_replicate_forall,
        ENNReal.toReal_pow]
      congr 1
      have hnot : ((ProbComp.eval (oneTrial a)).toOuterMeasure {b | (!b) = true}).toReal =
          Pr[Bool.not <$> oneTrial a] := by
        rw [← ProbComp.probability_map_decide_mem (s := {b : Bool | (!b) = true})]
        congr 2
      rw [hnot, ProbComp.probability_not]
    rw [hrej_eq]
    have hp_nn : 0 ≤ Pr[oneTrial a] := ENNReal.toReal_nonneg
    have hbern : 1 - (trials a : ℝ) * (1 / (2 : ℝ) ^ (N a + 10)) ≤
        (1 - Pr[oneTrial a]) ^ trials a := by
      have h1 : 1 / (2 : ℝ) ^ (N a + 10) ≤ 1 := by
        rw [div_le_one (by positivity)]
        exact one_le_pow₀ (by norm_num)
      calc
        1 - (trials a : ℝ) * (1 / (2 : ℝ) ^ (N a + 10)) ≤
            (1 - 1 / (2 : ℝ) ^ (N a + 10)) ^ trials a :=
          one_sub_mul_le_pow_nonneg (by positivity) h1 (trials a)
        _ ≤ (1 - Pr[oneTrial a]) ^ trials a :=
          pow_le_pow_left₀ (by linarith) (by linarith) _
    have hpow_nat : 96 * (N a + 3) ≤ 2 ^ (N a + 10) := by
      have hlt : N a < 2 ^ N a := (N a).lt_two_pow_self
      have h1 : 1 ≤ 2 ^ N a := Nat.one_le_two_pow
      rw [pow_add]
      norm_num
      omega
    have hpow_real : (trials a : ℝ) * (1 / (2 : ℝ) ^ (N a + 10)) ≤ 1 / 3 := by
      dsimp [trials]
      push_cast
      rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      have hcast : (96 * ((N a : ℝ) + 3)) ≤ (2 : ℝ) ^ (N a + 10) := by exact_mod_cast hpow_nat
      linarith
    linarith

/-- If `PromiseThreeUSAT` lies in `PromiseBPP encCNF`, then `NP enc ⊆ BPP enc` for every instance
encoding `enc`. -/
theorem NP_subset_BPP_of_PromiseThreeUSAT_mem_PromiseBPP
    (h3USAT : PromiseThreeUSAT ∈ PromiseBPP encCNF) {α : Type} (enc : α ↪ List Bool) :
    NP enc ⊆ BPP enc :=
  NP_subset_BPP_of_PromiseUSAT_mem_PromiseBPP
    (polyTimeReducible_promiseUSAT_promiseThreeUSAT.mem_PromiseBPP h3USAT) enc

private def reduceDistinctWith (W : CNF ℕ) (k : ℕ) (seed : List Bool) : CNF ℕ :=
  toSharpThreeSAT
    ((W.relabel Sum.inl ++ ValiantVazirani.hashCNF W.distinctVars k seed).relabel splitVarToNat)

/-- Randomized 3SAT-to-`Unique-SAT` isolation reduction: on width-`≤ 3` inputs `W`, checks whether
the all-`true` assignment satisfies `W` (returning `[[(0, true)]]` if so); otherwise samples
`k ∈ {2, ..., n+1}` from `2n + 2` fair bits and `seed` of length `(n + 2)(n + 1)` and outputs
`reduceDistinctWith W k seed`. -/
noncomputable def valiantVazirani3SAT (W : CNF ℕ) : ProbComp (CNF ℕ) :=
  let n := CNF.numVars W
  if !(W.all fun c ↦ decide (c.length ≤ 3)) then
    pure [[]]
  else if CNF.eval (fun _ ↦ true) W then
    pure [[(0, true)]]
  else if decide (n = 0) then
    pure [[]]
  else
    let B := 2 * n + 2
    let S := (n + 2) * (n + 1)
    (fun coins ↦
      let k := 2 + min n (ofBits (coins.take B) % n)
      let seed := coins.drop B
      reduceDistinctWith W k seed) <$> BitString.sampleList (B + S)

private lemma eval_rowClauses_distinct (σ : ValiantVazirani.Var → Bool) (vars : List ℕ) (i : ℕ)
    (row : List Bool) (off : Bool) :
    (ValiantVazirani.rowClauses vars i row off).eval σ = true ↔
      σ (.inr (i, 0)) = off ∧ σ (.inr (i, vars.length)) = false ∧
        ∀ (j : ℕ) (hj : j < vars.length), σ (.inr (i, j + 1)) =
          (σ (.inr (i, j)) ^^ (row.getD j false && σ (.inl vars[j]))) := by
  simp only [ValiantVazirani.rowClauses, CNF.eval_cons, Clause.eval_cons, Clause.eval_nil,
    Bool.or_false, Bool.and_eq_true, Literal.eval_eq_true_iff, CNF.eval_flatMap_eq_true_iff,
    ValiantVazirani.eval_stepClauses, Prod.forall, List.mem_zipIdx_iff_getElem?,
    List.getElem?_eq_some_iff]
  exact and_congr_right' (and_congr_right' ⟨fun h j hj ↦ h _ j ⟨hj, rfl⟩,
    fun h _ j ⟨hj, hv⟩ ↦ hv ▸ h j hj⟩)

private lemma eval_hashCNF_distinct (σ : ValiantVazirani.Var → Bool) (vars : List ℕ) (k : ℕ)
    (w : List Bool) :
    (ValiantVazirani.hashCNF vars k w).eval σ = true ↔ ∀ i : Fin k,
      σ (.inr (i, 0)) = ValiantVazirani.offset k vars.length w i ∧
      σ (.inr (i, vars.length)) = false ∧
      ∀ (j : ℕ) (hj : j < vars.length), σ (.inr (i, j + 1)) =
        (σ (.inr (i, j)) ^^
          (ValiantVazirani.matrix k vars.length w i ⟨j, hj⟩ && σ (.inl vars[j]))) := by
  have hmem_zip {k width : ℕ} {w row : List Bool} {i : ℕ} :
      (row, i) ∈ (BitString.listRows k width w).zipIdx ↔
        ∃ hi : i < k,
          row = List.ofFn (BitString.block (BitString.ofList (k * width) w) ⟨i, hi⟩) := by
    rw [List.mem_zipIdx_iff_getElem?, BitString.listRows_eq_ofFn, List.getElem?_ofFn]
    split <;> simp [*, eq_comm]
  simp only [ValiantVazirani.hashCNF, CNF.eval_flatMap_eq_true_iff, Prod.forall, hmem_zip,
    forall_exists_index, eval_rowClauses_distinct]
  refine ⟨fun h i ↦ ?_, fun h _ i hi hr ↦ hr ▸ ?_⟩
  · obtain ⟨h0, hL, hs⟩ := h _ i i.2 rfl
    exact ⟨h0, hL, fun j hj ↦ (hs j hj).trans (by rw [List.getD_ofFn_of_lt _ hj]; rfl)⟩
  · obtain ⟨h0, hL, hs⟩ := h ⟨i, hi⟩
    exact ⟨h0, hL, fun j hj ↦ (hs j hj).trans (by rw [List.getD_ofFn_of_lt _ hj]; rfl)⟩

private lemma mem_vars_hashCNF_distinct {vars : List ℕ} {k : ℕ} {w : List Bool}
    {u : ValiantVazirani.Var} (h : u ∈ (ValiantVazirani.hashCNF vars k w).vars) :
    (∃ v ∈ vars, u = .inl v) ∨ ∃ i < k, ∃ j ≤ vars.length, u = .inr (i, j) := by
  have hstep {bit : Bool} {next prev x u : ValiantVazirani.Var}
      (hs : u ∈ (ValiantVazirani.stepClauses bit next prev x).vars) :
      u = next ∨ u = prev ∨ u = x := by
    cases bit <;> simp only [ValiantVazirani.stepClauses, CNF.vars, Bool.false_eq_true, ite_false,
      ite_true, List.flatten_cons, List.flatten_nil, List.map_append, List.map_cons, List.map_nil,
      List.append_nil, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hs <;> tauto
  simp only [ValiantVazirani.hashCNF, CNF.mem_vars, List.mem_flatMap] at h
  obtain ⟨cl, ⟨⟨row, i⟩, hp, hcl⟩, b, hb⟩ := h
  have hi_lt : i < k := by
    rw [List.mem_zipIdx_iff_getElem?, BitString.listRows_eq_ofFn, List.getElem?_ofFn] at hp
    split at hp
    · assumption
    · simp at hp
  have hrow : u ∈ (ValiantVazirani.rowClauses vars i row
      ((w.drop (k * vars.length)).getD i false)).vars := CNF.mem_vars.mpr ⟨cl, hcl, b, hb⟩
  simp only [ValiantVazirani.rowClauses, CNF.mem_vars, List.mem_cons, List.mem_flatMap] at hrow
  rcases hrow with ⟨cl', rfl | rfl | ⟨⟨v, j⟩, hpj, hcl'⟩, b', hb'⟩
  · simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hb'
    exact .inr ⟨i, hi_lt, 0, Nat.zero_le _, hb'.1⟩
  · simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hb'
    exact .inr ⟨i, hi_lt, _, le_rfl, hb'.1⟩
  · obtain ⟨hj, hvj⟩ := List.mem_zipIdx' hpj
    rcases hstep (CNF.mem_vars.mpr ⟨cl', hcl', b', hb'⟩) with rfl | rfl | rfl
    · exact .inr ⟨i, hi_lt, j + 1, hj, rfl⟩
    · exact .inr ⟨i, hi_lt, j, hj.le, rfl⟩
    · exact .inl ⟨_, hvj ▸ List.getElem_mem hj, rfl⟩

/-- `valiantVazirani3SAT` runs in probabilistic polynomial time, isolates a unique satisfying
assignment of any satisfiable 3SAT formula on `n ≥ 1` variables with probability at least
`1 / (8n)`, and outputs only unsatisfiable width-3 formulas on unsatisfiable 3SAT inputs. -/
theorem valiantVazirani_threeSAT :
    IsPPTOn encCNF encCNF valiantVazirani3SAT ∧
    (∀ W : CNF ℕ, (∀ c ∈ W, c.length ≤ 3) → 1 ≤ CNF.numVars W → W ∈ SAT →
      1 / (8 * (CNF.numVars W : ℝ)) ≤
        ((ProbComp.eval (valiantVazirani3SAT W)).toOuterMeasure PromiseThreeUSAT.yes).toReal) ∧
    (∀ W : CNF ℕ, (∀ c ∈ W, c.length ≤ 3) → W ∈ UNSAT →
      ∀ W' ∈ (ProbComp.eval (valiantVazirani3SAT W)).support, W' ∈ PromiseThreeUSAT.no) := by
  classical
  have hppt : IsPPTOn encCNF encCNF valiantVazirani3SAT := by
    open ComputableInPolyTime in
    have hw : ComputableInPolyTime (fun W : CNF ℕ ↦ !(W.all fun c ↦ decide (c.length ≤ 3)))
        encCNF encBool :=
      bool_not.comp' (allWithInput id' (unary_le'
        ((length_list (encPair encNat encBool)).comp' (snd _ _)) (const 3)))
    have hallTrue :
        ComputableInPolyTime (fun W : CNF ℕ ↦ CNF.eval (fun _ ↦ true) W) encCNF encBool := by
      have hcl : ComputableInPolyTime
          (fun p : CNF ℕ × Clause ℕ ↦ p.2.any fun l ↦ l.2)
          (encPair encCNF (encList (encPair encNat encBool))) encBool :=
        anyWithInput (test := fun _ l ↦ l.2) (snd encCNF (encList (encPair encNat encBool)))
          ((snd (encPair encCNF (encList (encPair encNat encBool))) (encPair encNat encBool)).snd')
      refine (allWithInput (test := fun _ c ↦ c.any fun l ↦ l.2) id' hcl).of_enc_eq fun W ↦
        congrArg encBool ?_
      dsimp only [CNF.eval]
      congr 1; funext c
      dsimp only [Clause.eval]
      congr 1; funext l
      rcases l with ⟨_, _ | _⟩ <;> rfl
    have hnv := CNF.computableInPolyTime_numVars encNat
    have hnv0 : ComputableInPolyTime (fun W : CNF ℕ ↦ decide (CNF.numVars W = 0)) encCNF encBool :=
      (unary_le' hnv (const 0)).of_enc_eq fun _ ↦
        congrArg encBool (by rw [Bool.eq_iff_iff]; simp)
    have hBS : ComputableInPolyTime
        (fun W : CNF ℕ ↦ (2 * CNF.numVars W + 2) + (CNF.numVars W + 2) * (CNF.numVars W + 1))
        encCNF encUnary := by
      have hB := unary_add.comp' ((unary_mul.comp' ((const 2).prod hnv)).prod (const 2))
      have hS := unary_mul.comp'
        ((unary_add.comp' (hnv.prod (const 2))).prod (unary_add.comp' (hnv.prod (const 1))))
      exact unary_add.comp' (hB.prod hS)
    have hmain : IsPPTOn encCNF encCNF
        (fun W : CNF ℕ ↦
          let n := CNF.numVars W
          let B := 2 * n + 2
          let S := (n + 2) * (n + 1)
          (fun coins ↦
            let k := 2 + min n (ofBits (coins.take B) % n)
            let seed := coins.drop B
            reduceDistinctWith W k seed) <$> BitString.sampleList (B + S)) := by
      refine IsPPTOn.of_seeded
        (f := fun p : CNF ℕ × List Bool ↦
          let n := CNF.numVars p.1
          reduceDistinctWith p.1 (2 + min n (ofBits (p.2.take (2 * n + 2)) % n))
            (p.2.drop (2 * n + 2)))
        hBS ?_
      let encIn := encPair encCNF encBits
      have hW := fst encCNF encBits
      have hcoins := snd encCNF encBits
      have hn_u := hnv.comp' hW
      have hB_u := unary_add.comp' ((unary_mul.comp' ((const 2).prod hn_u)).prod (const 2))
      have htake := bitsTakeWithInput hcoins hB_u
      have hdrop := bitsDropWithInput hcoins hB_u
      have hu_bin := bitsToNat.comp' htake
      have hmod_bin := binary_mod.comp' (hu_bin.prod (unary_to_binary.comp' hn_u))
      have hmod_u := binary_min_unary' hn_u hmod_bin
      have hk_u := unary_add.comp' ((const 2).prod hmod_u)
      have hdvars := (CNF.computableInPolyTime_distinctVars encNat).comp' hW
      have hhash := ValiantVazirani.computableInPolyTime_hashCNF.comp'
        (hdvars.prod (hk_u.prod hdrop))
      have hinl : ComputableInPolyTime
          (fun p : CNF ℕ × List Bool ↦ CNF.relabel (Sum.inl : ℕ → ValiantVazirani.Var) p.1)
          encIn (encCNFOver ValiantVazirani.encVar) :=
        (CNF.computableInPolyTime_relabel
          (sumInl encNat (encPair encUnary encUnary))).comp' hW
      have happ := listAppend' hinl hhash
      have hsplit : ComputableInPolyTime (CNF.relabel splitVarToNat)
          (encCNFOver ValiantVazirani.encVar) encCNF := by
        unfold ValiantVazirani.encVar encCNFOver encCNF
        exact CNF.computableInPolyTime_relabel computableInPolyTime_splitVarToNat
      exact computableInPolyTime_toSharpThreeSAT.comp' (hsplit.comp' happ)
    exact IsPPTOn.cond hw (const [[]]).isPPTOn
      (IsPPTOn.cond hallTrue (const [[(0, true)]]).isPPTOn
        (IsPPTOn.cond hnv0 (const [[]]).isPPTOn hmain))
  refine ⟨hppt, fun W hW_width hn1 hW_sat ↦ ?_, fun W hW_width hW_unsat W' hW' ↦ ?_⟩
  · have hw_true : (W.all fun c ↦ decide (c.length ≤ 3)) = true := by
      simpa [List.all_eq_true] using hW_width
    by_cases htrue : W.eval (fun _ ↦ true) = true
    · have hval_eq : valiantVazirani3SAT W = pure [[(0, true)]] := by
        simp [valiantVazirani3SAT, hw_true, htrue]
      have hyes0 : ([[(0, true)]] : CNF ℕ) ∈ PromiseThreeUSAT.yes := by
        refine ⟨by simp, ⟨fun _ ↦ true, by simp [CNF.eval, Clause.eval, Literal.eval], ?_⟩⟩
        intro τ hτ v hv
        simp only [CNF.vars, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
          List.append_nil, List.mem_singleton] at hv
        subst hv
        simpa [CNF.eval, Clause.eval, Literal.eval] using hτ
      rw [hval_eq, ProbComp.eval_pure, PMF.toOuterMeasure_pure_apply]
      simp only [hyes0, ↓reduceIte, ENNReal.toReal_one]
      rw [div_le_one (by positivity)]
      have : (1 : ℝ) ≤ W.numVars := by exact_mod_cast hn1
      linarith
    · set n := W.numVars
      have hdv_len : W.distinctVars.length = n := CNF.length_distinctVars W
      have hn0_false : decide (n = 0) = false := decide_eq_false (by omega)
      have hval_eq : valiantVazirani3SAT W =
          (fun coins ↦
            let k := 2 + ofBits (coins.take (2 * n + 2)) % n
            let seed := coins.drop (2 * n + 2)
            reduceDistinctWith W k seed) <$>
            BitString.sampleList ((2 * n + 2) + (n + 2) * (n + 1)) := by
        simp only [valiantVazirani3SAT, n, hw_true, htrue, hn0_false, Bool.not_true,
          Bool.false_eq_true, ↓reduceIte]
        congr 1; funext coins
        rw [Nat.min_eq_right (Nat.le_of_lt (Nat.mod_lt _ (by omega : 0 < n)))]
      let sols : Finset (BitString W.distinctVars.length) :=
        Finset.univ.filter fun x ↦
          ∃ σ : ℕ → Bool, W.eval σ = true ∧ ValiantVazirani.point W.distinctVars σ = x
      obtain ⟨σ₀, hσ₀⟩ := hW_sat
      have hsols_ne : sols.Nonempty :=
        ⟨ValiantVazirani.point W.distinctVars σ₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, σ₀,
          hσ₀, rfl⟩⟩
      have hall1_not : (fun _ : Fin W.distinctVars.length ↦ true) ∉ sols := by
        intro hmem
        obtain ⟨_, σ, hσ, hpt⟩ := Finset.mem_filter.mp hmem
        have heq_on : W.eval (fun _ ↦ true) = W.eval σ := by
          apply CNF.eval_congr
          intro v hv
          obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem (CNF.mem_distinctVars.mpr hv)
          exact (congrFun hpt ⟨j, hj⟩).symm
        exact htrue (heq_on.trans hσ)
      have hsols_lt : sols.card < 2 ^ n := by
        have hlt_univ : sols.card < (Finset.univ : Finset (BitString W.distinctVars.length)).card :=
          Finset.card_lt_card ⟨Finset.subset_univ _, fun hsub ↦
            hall1_not (hsub (Finset.mem_univ _))⟩
        simpa [hdv_len] using hlt_univ
      set kStar := Nat.log 2 sols.card + 2
      have hkStar_bounds : 2 ≤ kStar ∧ kStar ≤ n + 1 := by
        have hlog_lt : Nat.log 2 sols.card < n :=
          Nat.log_lt_of_lt_pow hsols_ne.card_pos.ne' hsols_lt
        exact ⟨by omega, by omega⟩
      have hiso_yes (seed : List Bool)
          (hiso : (sols.filter fun x ↦ BitString.LinearHash.affineHash
            (ValiantVazirani.matrix kStar W.distinctVars.length seed,
              ValiantVazirani.offset kStar W.distinctVars.length seed) x = 0).card = 1) :
          reduceDistinctWith W kStar seed ∈ PromiseThreeUSAT.yes := by
        refine ⟨fun c hc ↦ length_le_three_of_mem_toSharpThreeSAT hc, ?_⟩
        set ψ₀ := (W.relabel Sum.inl ++
          ValiantVazirani.hashCNF W.distinctVars kStar seed).relabel splitVarToNat
        have hψ₀_usat : ψ₀ ∈ USAT := by
          obtain ⟨x₀, hx₀⟩ := Finset.card_eq_one.mp hiso
          obtain ⟨hx₀_sol, hx₀_hash⟩ := Finset.mem_filter.mp (hx₀ ▸ Finset.mem_singleton_self x₀)
          obtain ⟨σ, hσ, rfl⟩ := (Finset.mem_filter.mp hx₀_sol).2
          let σ' : ValiantVazirani.Var → Bool := Sum.elim σ fun p ↦
            if hp : p.1 < kStar then
              ValiantVazirani.auxValue W.distinctVars kStar seed σ ⟨p.1, hp⟩ p.2
            else false
          have haux_len (τ₀ : ℕ → Bool) (i : Fin kStar) :
              ValiantVazirani.auxValue W.distinctVars kStar seed τ₀ i W.distinctVars.length =
                BitString.LinearHash.affineHash
                  (ValiantVazirani.matrix kStar W.distinctVars.length seed,
                    ValiantVazirani.offset kStar W.distinctVars.length seed)
                  (ValiantVazirani.point W.distinctVars τ₀) i := by
            rw [ValiantVazirani.auxValue, BitString.LinearHash.affineHash, Pi.add_apply, add_comm,
              ← Fin.sum_univ_eq_sum_range]
            simp only [Fin.is_lt, dite_true, Fin.eta]; rfl
          have hext_eval : (ValiantVazirani.hashCNF W.distinctVars kStar seed).eval σ' = true := by
            refine (eval_hashCNF_distinct σ' W.distinctVars kStar seed).mpr fun i ↦
              ⟨by simp [σ', ValiantVazirani.auxValue], ?_, fun j hj ↦ ?_⟩
            · simp only [σ', Sum.elim_inr, i.2, dite_true, Fin.eta, haux_len, hx₀_hash]; rfl
            · simp only [σ', Sum.elim_inr, Sum.elim_inl, i.2, dite_true, Fin.eta,
                ValiantVazirani.auxValue, Finset.sum_range_succ, hj, ← add_assoc]; rfl
          refine ⟨Function.extend splitVarToNat σ' fun _ ↦ false, ?_, fun τ hτ v hvψ ↦ ?_⟩
          · simp only [ψ₀, CNF.eval_relabel, Function.extend_comp splitVarToNat_injective,
              CNF.eval_append, Bool.and_eq_true, σ']
            exact ⟨hσ, hext_eval⟩
          · simp only [ψ₀, CNF.eval_relabel, CNF.eval_append, Bool.and_eq_true] at hτ
            have heq_aux {i : Fin kStar} {j : ℕ} (hj : j ≤ W.distinctVars.length) :
                (τ ∘ splitVarToNat) (.inr (i, j)) =
                  ValiantVazirani.auxValue W.distinctVars kStar seed
                    ((τ ∘ splitVarToNat) ∘ .inl) i j := by
              obtain ⟨h0, -, hs⟩ :=
                (eval_hashCNF_distinct (τ ∘ splitVarToNat) W.distinctVars kStar seed).mp hτ.2 i
              refine BitString.eq_add_sum_of_step
                (z := fun j ↦ (τ ∘ splitVarToNat) (.inr (i, j))) h0 (fun j' hj' ↦ ?_) j hj
              simp only [hs j' hj', hj', dite_true, Function.comp_apply]
            have hhash_τ : BitString.LinearHash.affineHash
                (ValiantVazirani.matrix kStar W.distinctVars.length seed,
                  ValiantVazirani.offset kStar W.distinctVars.length seed)
                (ValiantVazirani.point W.distinctVars ((τ ∘ splitVarToNat) ∘ .inl)) = 0 := by
              funext i
              rw [← haux_len, ← heq_aux le_rfl]
              exact ((eval_hashCNF_distinct (τ ∘ splitVarToNat) W.distinctVars kStar seed).mp
                hτ.2 i).2.1
            have hpt : ValiantVazirani.point W.distinctVars ((τ ∘ splitVarToNat) ∘ .inl) =
                ValiantVazirani.point W.distinctVars σ :=
              Finset.mem_singleton.mp (hx₀ ▸ Finset.mem_filter.mpr
                ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, _, hτ.1, rfl⟩, hhash_τ⟩)
            obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ((CNF.vars_relabel _ _) ▸ hvψ)
            rw [splitVarToNat_injective.extend_apply]
            rw [CNF.vars_append, List.mem_append, CNF.vars_relabel, List.mem_map] at hu
            rcases hu.elim (fun ⟨v₀, hv₀, h⟩ ↦ .inl ⟨v₀, CNF.mem_distinctVars.mpr hv₀, h.symm⟩)
              mem_vars_hashCNF_distinct with ⟨v₀, hv₀, rfl⟩ | ⟨i, hi, j, hj, rfl⟩
            · obtain ⟨idx, hidx, rfl⟩ := List.getElem_of_mem hv₀
              exact congrFun hpt ⟨idx, hidx⟩
            · change (τ ∘ splitVarToNat) (.inr (i, j)) = σ' (.inr (i, j))
              rw [heq_aux (i := ⟨i, hi⟩) hj, ValiantVazirani.auxValue_congr hpt]
              simp [σ', hi]
        rw [reduceDistinctWith, SharpSAT.mem_USAT_iff, SharpSAT, modelCount_toSharpThreeSAT]
        exact SharpSAT.mem_USAT_iff.mp hψ₀_usat
      set B := 2 * n + 2
      set S := (n + 2) * (n + 1)
      have heval_split : ProbComp.eval (valiantVazirani3SAT W) =
          (BitString.uniformList B).bind (fun u ↦
            (BitString.uniformList S).map (fun seed ↦
              reduceDistinctWith W (2 + ofBits u % n) seed)) := by
        rw [hval_eq, ProbComp.eval_map, BitString.eval_sampleList]
        exact BitString.uniformList_map_split B S
          (fun u seed ↦ reduceDistinctWith W (2 + ofBits u % n) seed)
      rw [heval_split]
      have hu_prob : (2 : ℝ) / (3 * (n : ℝ)) ≤
          ((BitString.uniformList B).toOuterMeasure
            {u : List Bool | 2 + ofBits u % n = kStar}).toReal := by
        rw [BitString.uniformList, PMF.toOuterMeasure_map_apply,
          PMF.toOuterMeasure_apply_toReal]
        simp only [PMF.uniformOfFintype_apply, Fintype.card_fun, Fintype.card_bool,
          Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat, ENNReal.toReal_inv,
          ENNReal.toReal_pow, ENNReal.toReal_ofNat, Set.mem_preimage, Set.mem_ofPred_eq,
          Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
        have h2B_ge_3n : 3 * n ≤ 2 ^ B := by
          have hn_pow : n < 2 ^ n := n.lt_two_pow_self
          have h4 : 2 ^ B = 4 * (2 ^ n * 2 ^ n) := by
            dsimp [B]; rw [pow_add, pow_mul']; ring
          have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
          nlinarith
        have hcard_ge : 2 ^ B / n ≤
            (Finset.univ.filter fun r : Fin B → Bool ↦
              2 + ofBits (List.ofFn r) % n = kStar).card := by
          let f (q : ℕ) : Fin B → Bool :=
            if h : q * n + (kStar - 2) < 2 ^ B then
              (Cslib.BitString.equivFin B).symm ⟨q * n + (kStar - 2), h⟩
            else fun _ ↦ false
          have hlt_q {q : ℕ} (hq : q ∈ Finset.range (2 ^ B / n)) :
              q * n + (kStar - 2) < 2 ^ B := by
            rw [Finset.mem_range] at hq
            have hmul : (q + 1) * n ≤ (2 ^ B / n) * n := Nat.mul_le_mul_right n hq
            rw [Nat.add_one_mul] at hmul
            have hdiv := Nat.div_mul_le_self (2 ^ B) n
            omega
          have hofBits_f {q : ℕ} (hq : q ∈ Finset.range (2 ^ B / n)) :
              ofBits (List.ofFn (f q)) = q * n + (kStar - 2) := by
            have hf_eq : f q = (Cslib.BitString.equivFin B).symm ⟨q * n + (kStar - 2), hlt_q hq⟩ :=
              dite_eq_left_of_eq_true (eq_true (hlt_q hq))
            rw [hf_eq, ofBits_ofFn, Equiv.apply_symm_apply]
          calc
            2 ^ B / n = (Finset.range (2 ^ B / n)).card := (Finset.card_range _).symm
            _ ≤ (Finset.univ.filter fun r : Fin B → Bool ↦
                  2 + ofBits (List.ofFn r) % n = kStar).card := by
              refine Finset.card_le_card_of_injOn f (fun q hq ↦ ?_) (fun q₁ hq₁ q₂ hq₂ heq ↦ ?_)
              · simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and,
                  hofBits_f hq]
                have hr_lt : kStar - 2 < n := by omega
                rw [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt hr_lt]
                omega
              · have h1 := hofBits_f hq₁
                rw [heq, hofBits_f hq₂] at h1
                nlinarith
        have hdiv_ge : 2 * 2 ^ B ≤ 3 * n * (2 ^ B / n) := by
          have hmod_lt : 2 ^ B % n < n := Nat.mod_lt _ (by omega)
          have hdiv_mod := Nat.div_add_mod (2 ^ B) n
          nlinarith
        have hnat_ineq : 2 * 2 ^ B ≤ 3 * n *
            (Finset.univ.filter fun r : Fin B → Bool ↦
              2 + ofBits (List.ofFn r) % n = kStar).card :=
          hdiv_ge.trans (Nat.mul_le_mul_left _ hcard_ge)
        rw [← div_eq_mul_inv, div_le_div_iff₀ (by positivity) (by positivity)]
        have hcast : (2 : ℝ) * (2 : ℝ) ^ B ≤
            (3 * (n : ℝ)) * ((Finset.univ.filter fun r : Fin B → Bool ↦
              2 + ofBits (List.ofFn r) % n = kStar).card : ℝ) := by exact_mod_cast hnat_ineq
        linarith
      have hseed_prob : (3 / 16 : ℝ) ≤
          (((BitString.uniformList S).map (fun seed ↦
            reduceDistinctWith W kStar seed)).toOuterMeasure PromiseThreeUSAT.yes).toReal := by
        rw [BitString.toOuterMeasure_map_uniformList_toReal]
        have hS_ge : kStar * W.distinctVars.length + kStar ≤ S := by
          rw [hdv_len]; dsimp [S]; nlinarith [hkStar_bounds.2]
        have hvv_core := ValiantVazirani.three_mul_two_pow_le_card_filter_card_filter_eq_one
          hsols_ne
        set L₀ := kStar * W.distinctVars.length + kStar
        have hrest := BitString.card_filter_take_drop hS_ge
          (fun w ↦ (sols.filter fun x ↦ BitString.LinearHash.affineHash
            (ValiantVazirani.matrix kStar W.distinctVars.length w,
              ValiantVazirani.offset kStar W.distinctVars.length w) x = 0).card = 1)
          (fun _ ↦ True)
        dsimp only [L₀] at hrest
        simp only [and_true, Finset.filter_true, Finset.card_univ, Fintype.card_fun,
          Fintype.card_bool, Fintype.card_fin, ValiantVazirani.matrix_take,
          ValiantVazirani.offset_take] at hrest
        rw [ValiantVazirani.card_filter_seed (fun p ↦
          (sols.filter fun x ↦ BitString.LinearHash.affineHash p x = 0).card = 1)] at hrest
        let goodSeed : Finset (Fin S → Bool) := Finset.univ.filter fun r : Fin S → Bool ↦
          (sols.filter fun x ↦ BitString.LinearHash.affineHash
            (ValiantVazirani.matrix kStar W.distinctVars.length (List.ofFn r),
              ValiantVazirani.offset kStar W.distinctVars.length (List.ofFn r)) x = 0).card = 1
        have hsub : goodSeed ⊆
            Finset.univ.filter fun r : Fin S → Bool ↦
              reduceDistinctWith W kStar (List.ofFn r) ∈ PromiseThreeUSAT.yes :=
          fun r hr ↦ Finset.mem_filter.mpr ⟨Finset.mem_univ _,
            hiso_yes (List.ofFn r) (Finset.mem_filter.mp hr).2⟩
        have hpow_split : 2 ^ S = 2 ^ L₀ * 2 ^ (S - L₀) := by
          rw [← pow_add, Nat.add_sub_of_le hS_ge]
        have hnat_bound : 3 * 2 ^ S ≤ 16 *
            (Finset.univ.filter fun r : Fin S → Bool ↦
              reduceDistinctWith W kStar (List.ofFn r) ∈ PromiseThreeUSAT.yes).card := by
          calc
            3 * 2 ^ S = 3 * 2 ^ L₀ * 2 ^ (S - L₀) := by rw [hpow_split]; ring
            _ ≤ 16 * (Finset.univ.filter fun p ↦ (sols.filter fun x ↦
                  BitString.LinearHash.affineHash p x = 0).card = 1).card * 2 ^ (S - L₀) :=
              Nat.mul_le_mul_right _ hvv_core
            _ = 16 * goodSeed.card := by
              dsimp only [goodSeed, L₀]; rw [hrest]; ring
            _ ≤ _ := Nat.mul_le_mul_left 16 (Finset.card_le_card hsub)
        rw [div_le_div_iff₀ (by norm_num) (by positivity)]
        have hcast : (3 : ℝ) * (2 : ℝ) ^ S ≤ 16 *
            ((Finset.univ.filter fun r : Fin S → Bool ↦
              reduceDistinctWith W kStar (List.ofFn r) ∈ PromiseThreeUSAT.yes).card : ℝ) := by
          exact_mod_cast hnat_bound
        linarith
      have hbind := PMF.toOuterMeasure_bind_ge_mul (BitString.uniformList B)
        (fun u ↦ (BitString.uniformList S).map (fun seed ↦
          reduceDistinctWith W (2 + ofBits u % n) seed))
        {u : List Bool | 2 + ofBits u % n = kStar} PromiseThreeUSAT.yes
        (by norm_num : (0 : ℝ) ≤ 3 / 16) hu_prob
        (fun u _ hu ↦ by dsimp at hu; rw [hu]; exact hseed_prob)
      have hprod_eq : (2 : ℝ) / (3 * (n : ℝ)) * (3 / 16) = 1 / (8 * (n : ℝ)) := by
        have hn_ne : (n : ℝ) ≠ 0 := by positivity
        field_simp; ring
      rwa [hprod_eq] at hbind
  · have hw_true : (W.all fun c ↦ decide (c.length ≤ 3)) = true := by
      simpa [List.all_eq_true] using hW_width
    have htrue_false : W.eval (fun _ ↦ true) = false :=
      Bool.eq_false_iff.mpr fun ht ↦ hW_unsat ⟨fun _ ↦ true, ht⟩
    have hempty_no : ([] :: [] : CNF ℕ) ∈ PromiseThreeUSAT.no :=
      ⟨by simp, fun ⟨σ, hσ⟩ ↦ by simp [CNF.eval, Clause.eval] at hσ⟩
    by_cases hn0 : W.numVars = 0
    · simp only [valiantVazirani3SAT, hw_true, htrue_false, hn0, decide_true,
        Bool.not_true, Bool.false_eq_true, ↓reduceIte, ProbComp.eval_pure,
        PMF.support_pure, Set.mem_singleton_iff] at hW'
      subst hW'; exact hempty_no
    · simp only [valiantVazirani3SAT, hw_true, htrue_false, decide_eq_false hn0,
        Bool.not_true, Bool.false_eq_true, ↓reduceIte, ProbComp.eval_map,
        BitString.eval_sampleList, PMF.mem_support_map_iff] at hW'
      obtain ⟨coins, _, rfl⟩ := hW'
      refine ⟨fun c hc ↦ length_le_three_of_mem_toSharpThreeSAT hc, ?_⟩
      rw [mem_UNSAT, ← CNF.modelCount_pos_iff, not_lt, Nat.le_zero, reduceDistinctWith,
        modelCount_toSharpThreeSAT, ← Nat.le_zero, ← not_lt, CNF.modelCount_pos_iff]
      rintro ⟨τ, hτ⟩
      simp only [CNF.eval_relabel, CNF.eval_append, Bool.and_eq_true] at hτ
      exact hW_unsat ⟨(τ ∘ splitVarToNat) ∘ Sum.inl, hτ.1⟩

end CslibFrontier.Complexity
