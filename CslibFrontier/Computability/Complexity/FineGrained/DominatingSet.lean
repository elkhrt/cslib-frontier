/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FormalPapers Contributors
-/
module

public import CslibFrontier.Computability.Complexity.FineGrained.Exponents
public import CslibFrontier.Computability.Complexity.Problems.DominatingSet
import CslibFrontier.Computability.Complexity.FineGrained.Bounds
import CslibFrontier.Computability.Complexity.Problems.SAT.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Degree
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Bounds
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Length
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Streaming
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.NatPower
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.OCountedIteration
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeBinaryDivision
import CslibFrontier.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial.Automation
import CslibFrontier.Tactic.EncLen
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Nat.Size

/-!
# Fine-Grained Reduction from CNF-SAT to `k`-Dominating Set under SETH

This module formalizes the clause-polynomial consequence of the Strong Exponential Time Hypothesis
(`SETH`) and the split-and-list reduction of Pătrașcu and Williams from unrestricted
CNF satisfiability (`SAT`) to the `k`-Dominating Set problem for every fixed $k \ge 3$:

1. **Clause-polynomial formulation of SETH**: any $O((2 - \varepsilon)^n (m + 1)^e)$ algorithm for
   `n`-variable `m`-clause CNF satisfiability ($0 < \varepsilon < 2$) yields an
   $O(2^{(1 - \delta) n} (|\varphi| + 1)^e)$ algorithm for `SAT` with $\delta > 0$, contradicting
   `SETH`.
2. **Pătrașcu–Williams reduction (`pwGraph`)**: partitioning the `n` distinct variables of a CNF
   formula `φ` into `k` blocks of at most $\lceil n / k \rceil$ variables produces a
   duplicate-free graph with at most $2k + m + k \cdot 2^{\lceil n / k \rceil}$ vertices
   (including two private guard vertices per block) that has a dominating set of size `k`
   (equivalently, at most `k`) if and only if `φ` is satisfiable, streamed within time
   $O(2^{2 \lceil n / k \rceil} (|\varphi| + 1)^e)$. Combining this reduction on sparse formulas
   ($m < 2^{\lceil n / k \rceil}$) with exhaustive search on dense formulas
   ($m \ge 2^{\lceil n / k \rceil}$) transfers any
   $O(|V|^{k - \varepsilon} + (|\mathrm{enc}(G)| + 1)^e)$ decider ($2e < k$) for `k`-Dominating
   Set to an $O(2^{(1 - \delta) n} \mathrm{poly}(|\varphi|))$ decider for `SAT`.

## Main definitions
* `CslibFrontier.FineGrainedDominatingSet.kDominatingSet`, `kDominatingSetLe`, `pwBlockSize`,
  `pwBlock`, `pwGraph`.

## Main results
* `CslibFrontier.FineGrainedDominatingSet.decidableInExpTime_SAT_of_two_sub`,
  `not_decidableInTimeO_SAT_two_sub`, `exists_computableInO_stream_counter`,
  `pwGraph_mem_kDominatingSet_iff`, `exists_computableInO_pwGraph`,
  `decidableInExpTime_SAT_of_kDominatingSet`, `not_decidableInTimeO_kDominatingSet`,
  `not_decidableInTimeO_kDominatingSet_card`, `not_decidableInTimeO_kDominatingSetLe`.
-/

public section

namespace CslibFrontier.FineGrainedDominatingSet

open Cslib.Complexity Cslib.Logic.PL Turing.MultiTapeTM
/-! ### Clause-polynomial formulation of SETH -/

private lemma exists_logb_saving {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 2) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ n : ℕ, (2 - ε) ^ n ≤ (2 : ℝ) ^ ((1 - δ) * n) := by
  let b : ℝ := max 1 (2 - ε)
  have hb_pos : 0 < b := lt_max_of_lt_left zero_lt_one
  have hb_lt : b < 2 := max_lt (by norm_num) (by linarith)
  have hlog_lt : Real.logb 2 b < 1 := by
    calc Real.logb 2 b < Real.logb 2 2 := Real.logb_lt_logb (by norm_num) hb_pos hb_lt
      _ = 1 := Real.logb_self_eq_one (by norm_num)
  have hlog_ge : 0 ≤ Real.logb 2 b := Real.logb_nonneg (by norm_num) (le_max_left _ _)
  refine ⟨1 - Real.logb 2 b, by linarith, by linarith, fun n => ?_⟩
  have hsub : 1 - (1 - Real.logb 2 b) = Real.logb 2 b := by ring
  rw [hsub]
  calc (2 - ε) ^ n ≤ b ^ n := pow_le_pow_left₀ (by linarith) (le_max_right _ _) _
    _ = ((2 : ℝ) ^ Real.logb 2 b) ^ n := by rw [Real.rpow_logb (by norm_num) (by norm_num) hb_pos]
    _ = (2 : ℝ) ^ (Real.logb 2 b * n) := by rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]

/-- Any algorithm deciding unrestricted CNF satisfiability in time
$O((2 - \varepsilon)^n (m + 1)^e)$ for $0 < \varepsilon < 2$ yields an exponential-time `SAT`
decider with exponent $1 - \delta < 1$. -/
theorem decidableInExpTime_SAT_of_two_sub {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 2) {e : ℕ}
    (h : DecidableInTimeO SAT encCNF fun φ => (2 - ε) ^ φ.numVars * ((φ.length : ℝ) + 1) ^ e) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ DecidableInExpTime SAT encCNF CNF.numVars (1 - δ) := by
  obtain ⟨δ, hδ, hδ1, hpow⟩ := exists_logb_saving hε hε2
  refine ⟨δ, hδ, hδ1, e, h.mono 1 (fun φ => ?_) (fun φ => by positivity)⟩
  have hlen : ((φ.length : ℝ) + 1) ^ e ≤ (((encCNF φ).length : ℝ) + 1) ^ e := by
    refine pow_le_pow_left₀ (by positivity) ?_ e
    have hle : (φ.length : ℝ) ≤ (encCNF φ).length := by
      exact_mod_cast length_le_length_encList (encList (encPair encNat encBool)) φ
    linarith
  have hmul := mul_le_mul (hpow φ.numVars) hlen (by positivity) (by positivity)
  simpa using le_trans hmul (le_add_of_nonneg_right zero_le_one)

/-- Every exponential-time `SAT` decider with exponent $1 - \delta$ ($0 < \delta \le 1$) refutes
`SETH`. -/
theorem not_seth_of_decidableInExpTime_SAT {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (h : DecidableInExpTime SAT encCNF CNF.numVars (1 - δ)) : ¬ SETH := by
  intro hSETH
  obtain ⟨k, hk⟩ := hSETH δ hδ
  apply hk
  rw [KSAT_eq_inter k (KSAT_subset_SAT k) le_rfl]
  exact h.inter (computableInPolyTime_all_length_le k) (by linarith)

/-- Under `SETH`, for every $0 < \varepsilon < 2$ and exponent `e`, unrestricted CNF satisfiability
cannot be decided in time $O((2 - \varepsilon)^n (m + 1)^e)$. -/
theorem not_decidableInTimeO_SAT_two_sub (h : SETH) {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 2) (e : ℕ) :
    ¬ DecidableInTimeO SAT encCNF fun φ => (2 - ε) ^ φ.numVars * ((φ.length : ℝ) + 1) ^ e := by
  intro hdec
  obtain ⟨δ, hδ, hδ1, hSAT⟩ := decidableInExpTime_SAT_of_two_sub hε hε2 hdec
  exact not_seth_of_decidableInExpTime_SAT hδ hδ1 hSAT h

/-- Under `SETH`, for every $0 < \varepsilon < 2$ and exponent `e`, unrestricted CNF satisfiability
cannot be decided in time $O((2 - \varepsilon)^n (|\mathrm{enc}(\varphi)| + 1)^e)$. -/
theorem not_decidableInTimeO_SAT_two_sub_enc (h : SETH) {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 2)
    (e : ℕ) :
    ¬ DecidableInTimeO SAT encCNF
        fun φ => (2 - ε) ^ φ.numVars * (((encCNF φ).length : ℝ) + 1) ^ e := by
  intro hdec
  obtain ⟨δ, hδ, hδ1, hpow⟩ := exists_logb_saving hε hε2
  have hSAT : DecidableInExpTime SAT encCNF CNF.numVars (1 - δ) := by
    refine ⟨e, hdec.mono 1 (fun φ => ?_) (fun φ => by positivity)⟩
    have hmul := mul_le_mul_of_nonneg_right (hpow φ.numVars)
      (by positivity : (0 : ℝ) ≤ (((encCNF φ).length : ℝ) + 1) ^ e)
    simpa using le_trans hmul (le_add_of_nonneg_right zero_le_one)
  exact not_seth_of_decidableInExpTime_SAT hδ hδ1 hSAT h

/-! ### Reusable framing and streaming helpers -/

private def escapeBits (w : List Bool) : List Bool :=
  (w.map fun b => [true, b]).flatten

private lemma frame_eq_escapeBits (w : List Bool) : frame w = escapeBits w ++ [false] := by
  simp only [frame, escapeBits]
  induction w with
  | nil => rfl
  | cons b w ih => simp [ih]

private lemma escapeBits_append (u v : List Bool) :
    escapeBits (u ++ v) = escapeBits u ++ escapeBits v := by
  simp [escapeBits, List.map_append]

private lemma escapeBits_flatten (L : List (List Bool)) :
    escapeBits L.flatten = (L.map escapeBits).flatten := by
  induction L with
  | nil => rfl
  | cons u L ih => simp [escapeBits_append, ih]

private lemma encList_eq_flatten {γ : Type*} (encγ : γ ↪ List Bool) (L : List γ) :
    encList encγ L = (L.map fun x => frame (encγ x)).flatten := by
  induction L with
  | nil => rfl
  | cons x L ih => rw [encList_cons, ih]; rfl

private lemma encList_append_eq {γ : Type*} (encγ : γ ↪ List Bool) (L₁ L₂ : List γ) :
    encList encγ (L₁ ++ L₂) = encList encγ L₁ ++ encList encγ L₂ := by
  simp [encList_eq_flatten, List.map_append]

private lemma encList_flatMap_eq {β γ : Type*} (encγ : γ ↪ List Bool) (xs : List β)
    (f : β → List γ) :
    encList encγ (xs.flatMap f) = (xs.map fun x => encList encγ (f x)).flatten := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih]

private lemma computableInPolyTime_escapeBits :
    ComputableInPolyTime escapeBits encBits encBits := by
  unfold escapeBits
  fun_prop

private lemma computableInPolyTime_takeUnary {γ : Type} (encγ : γ ↪ List Bool) :
    ComputableInPolyTime (fun p : List γ × ℕ => p.1.take p.2)
      (encPair (encList encγ) encUnary) (encList encγ) := by
  have hfst := ComputableInPolyTime.fst (encList encγ) encUnary
  have hrev := ComputableInPolyTime.listReverseWithInput hfst
  have hlen := (ComputableInPolyTime.length_list encγ).comp hfst
  have hk := ComputableInPolyTime.snd (encList encγ) encUnary
  have hsub : ComputableInPolyTime (fun p : List γ × ℕ => p.1.length - p.2)
      (encPair (encList encγ) encUnary) encUnary := by fun_prop
  refine (ComputableInPolyTime.listReverseWithInput
    ((ComputableInPolyTime.dropUnary (encA := encγ)).comp (hrev.prod hsub))).of_enc_eq fun p =>
    congrArg _ (by simp [← List.reverse_take])

private lemma computableInPolyTime_getD_list {γ : Type} (encγ : γ ↪ List Bool) (d : γ) :
    ComputableInPolyTime (fun p : List γ × ℕ => p.1.getD p.2 d)
      (encPair (encList encγ) encUnary) encγ := by
  have htake := (computableInPolyTime_takeUnary encγ).comp
    ((ComputableInPolyTime.dropUnary (encA := encγ)).prod (ComputableInPolyTime.const 1))
  have hpar := ComputableInPolyTime.fst (encList encγ) encUnary
  have hstep := ComputableInPolyTime.snd (encPair (encList encγ) encγ) encγ
  refine (ComputableInPolyTime.foldlWith_of_bounded_growth (encA := encγ) (encL := encList encγ)
    (encB := encγ) (par := fun p : List γ × ℕ => p.1)
    (list := fun p : List γ × ℕ => (p.1.drop p.2).take 1)
    (step := fun _ _ x => x) hpar htake (ComputableInPolyTime.const d) hstep
    (growth := fun p => (encList encγ p.1).length + (encγ d).length + 1)
    ((hpar.polyBounded_length.add (.const _)).add (.const 1))
    (fun p _ x hx => by
      have := length_le_encList_of_mem encγ (List.mem_of_mem_drop (List.mem_of_mem_take hx))
      omega)).of_enc_eq fun ⟨l, i⟩ => congrArg _ ?_
  rw [List.getD_eq_getElem?_getD, ← List.head?_drop]
  cases l.drop i <;> rfl

private lemma computableInPolyTime_unaryRange :
    ComputableInPolyTime List.range encUnary (encList encNat) :=
  (ComputableInPolyTime.mapWithInput (f := fun _ i => i)
    (ComputableInPolyTime.unary_range'
      (ComputableInPolyTime.id' : ComputableInPolyTime id encUnary encUnary))
    (ComputableInPolyTime.unary_to_binary.comp
      (ComputableInPolyTime.snd encUnary encUnary))).of_enc_eq fun _ =>
    congrArg _ (List.map_id _).symm

private lemma stream_time_bound {cF a S P b k C : ℕ} (hs : S ≤ b) (hP : b + 1 ≤ P)
    (ha : a + cF + 1 ≤ C) : cF * (S + 1) + k * (a * P) + b + 1 ≤ C * ((k + 1) * P + 1) := by
  have := Nat.mul_le_mul_right (k * P) (show a ≤ C by omega)
  nlinarith

private lemma stream_space_bound {cF a S P b k C : ℕ} (hs : S ≤ b) (hP : b + 1 ≤ P)
    (ha : a + cF + 1 ≤ C) : cF * (S + 1) + a * P + b + 1 ≤ C * ((k + 1) * P + 1) := by
  calc cF * (S + 1) + a * P + b + 1 ≤ C * (1 * P + 1) := by nlinarith
    _ ≤ C * ((k + 1) * P + 1) := Nat.mul_le_mul_left C (by nlinarith)

private lemma iterate_inc {α : Type} (s : α × ℕ) (i : ℕ) :
    (fun s : α × ℕ => (s.1, s.2 + 1))^[i] s = (s.1, s.2 + i) := by
  induction i with
  | zero => rfl
  | succ i ih => rw [Function.iterate_succ_apply', ih, Nat.add_assoc]

/-- Generic counted bit-stream lemma over a fixed context type `α` and a binary step counter. -/
theorem exists_computableInO_stream_counter {α : Type} (encα : α ↪ List Bool)
    {emit : α × ℕ → List Bool} (hemit : ComputableInPolyTime emit (encPair encα encNat) encBits)
    (fin : List Bool) :
    ∃ D : ℕ, 1 ≤ D ∧ ComputableInO
      (fun x : (α × ℕ) × ℕ => ((List.range x.2).map fun i => emit (x.1.1, x.1.2 +
        i)).flatten ++ fin)
      (encPair (encPair encα encNat) encUnary) encBits
      (fun x => (x.2 + 1) * (2 * (encα x.1.1).length + 1 + (encNat (x.1.2 + x.2)).length + 1) ^ D)
      (fun x => (x.2 + 1) *
        (2 * (encα x.1.1).length + 1 + (encNat (x.1.2 + x.2)).length + 1) ^ D) := by
  let encS : α × ℕ ↪ List Bool := encPair encα encNat
  obtain ⟨dN, _, hN_deg⟩ :=
    (show ComputableInPolyTime (fun s : α × ℕ => (s.1, s.2 + 1)) encS encS by
      unfold encS; fun_prop).exists_degree
  obtain ⟨tN, sN, ⟨cN, htN⟩, ⟨cN', hsN⟩, hN⟩ := hN_deg.1
  obtain ⟨dE, _, hE_deg⟩ := hemit.exists_degree
  obtain ⟨tE, sE, ⟨cE, htE⟩, ⟨cE', hsE⟩, hE⟩ := hE_deg.1
  obtain ⟨cF, hF, -⟩ :=
    (ComputableInDegree.const (encIn := encS) (encMid := encBits) fin).inO_one
  let D : ℕ := dN + dE + 1
  let B : (α × ℕ) × ℕ → ℕ := fun x =>
    2 * (encα x.1.1).length + 1 + (encNat (x.1.2 + x.2)).length
  have hstate : ∀ x : (α × ℕ) × ℕ, ∀ i ≤ x.2,
      (encS ((fun s : α × ℕ => (s.1, s.2 + 1))^[i] x.1)).length ≤ B x := by
    intro x i hi
    rw [iterate_inc]
    have hsz : (encNat (x.1.2 + i)).length ≤ (encNat (x.1.2 + x.2)).length := by
      simpa only [encNat_apply, Nat.size_eq_bits_len] using
        Nat.size_le_size (show x.1.2 + i ≤ x.1.2 + x.2 by omega)
    enc_len [encS, B] at hsz ⊢
  have hstep (x : (α × ℕ) × ℕ) {c' d i : ℕ} (hd : d ≤ D) (hi : i ≤ x.2)
      {f : α × ℕ → ℕ} (hf : ∀ s, f s ≤ c' * ((encS s).length + 1) ^ d) :
      f ((fun s : α × ℕ => (s.1, s.2 + 1))^[i] x.1) ≤ c' * (B x + 1) ^ D :=
    (hf _).trans <| Nat.mul_le_mul_left c' <|
      (Nat.pow_le_pow_left (Nat.add_le_add_right (hstate x i hi) 1) d).trans
        (Nat.pow_le_pow_right (Nat.succ_pos _) hd)
  have hB1 (x : (α × ℕ) × ℕ) : B x + 1 ≤ (B x + 1) ^ D := Nat.le_self_pow (by omega) _
  obtain ⟨c, h⟩ := ComputableInTimeAndSpace.iterate_unary_stream_sum hN hE hF
    (R := fun x _ => (cN + cE + 3) * (B x + 1) ^ D)
    (Q := fun x => (cN' + cE') * (B x + 1) ^ D) (B := B)
    (fun x i hi => by
      have h₀ := hstate x i hi.le
      have h₁ := hstate x (i + 1) hi
      have h₂ := hstep x (by omega) hi.le htN
      have h₃ := hstep x (by omega) hi.le htE
      have h₄ := hB1 x
      nlinarith)
    (fun x i hi => by
      have h₁ := hstep x (by omega) hi.le hsN
      have h₂ := hstep x (by omega) hi.le hsE
      nlinarith)
    hstate
  have hsum (x : (α × ℕ) × ℕ) :
      ∑ _i ∈ Finset.range x.2, (cN + cE + 3) * (B x + 1) ^ D =
        x.2 * ((cN + cE + 3) * (B x + 1) ^ D) := by simp
  refine ⟨D, by omega, (ComputableInO.of_bounds h (c * (cF + cN + cE + cN' + cE' + 6))
    (fun x => ?_) (fun x => ?_) (fun x => ?_)).of_enc_eq fun x => ?_⟩
  · rw [hsum, Nat.mul_assoc]
    exact Nat.mul_le_mul_left c (stream_time_bound (hstate x x.2 le_rfl) (hB1 x) (by omega))
  · rw [Nat.mul_assoc]
    exact Nat.mul_le_mul_left c (stream_space_bound (hstate x x.2 le_rfl) (hB1 x) (by omega))
  · refine (h.length_le x).trans ?_
    rw [hsum, Nat.mul_assoc]
    exact Nat.mul_le_mul_left c (stream_time_bound (hstate x x.2 le_rfl) (hB1 x) (by omega))
  · simp only [iterate_inc]

/-! ### Fixed-parameter `k`-Dominating Set and the Pătrașcu–Williams reduction -/

/-- The `k`-Dominating Set language: graphs with a dominating set of `k` declared vertices. -/
@[expose] def kDominatingSet (k : ℕ) : Set Graph :=
  {G | (⟨G, k⟩ : DominatingSetInstance) ∈ DominatingSet}

@[simp] theorem mem_kDominatingSet {k : ℕ} {G : Graph} :
    G ∈ kDominatingSet k ↔ (⟨G, k⟩ : DominatingSetInstance) ∈ DominatingSet := Iff.rfl

/-- The `≤ k`-Dominating Set language: graphs having a dominating set of at most `k` declared
vertices. -/
@[expose]
def kDominatingSetLe (k : ℕ) : Set Graph :=
  {G | ∃ S : Finset ℕ, (∀ v ∈ S, v ∈ G.vertices) ∧
    (∀ v ∈ G.vertices, v ∈ S ∨ ∃ s ∈ S, G.toSimpleGraph.Adj v s) ∧ S.card ≤ k}

/-- Ceiling block size $\lceil n / k \rceil = (n + k - 1) / k$ for splitting the `n` distinct
variables of a CNF formula `φ` into `k` blocks. -/
@[expose]
def pwBlockSize (k : ℕ) (φ : CNF ℕ) : ℕ :=
  (φ.numVars + k - 1) / k

/-- The `r`-th variable block of `φ` in the `k`-way Pătrașcu–Williams partition. -/
@[expose]
def pwBlock (k : ℕ) (φ : CNF ℕ) (r : ℕ) : List ℕ :=
  (φ.distinctVars.drop (r * pwBlockSize k φ)).take (pwBlockSize k φ)

private def pwGuardV (r b : ℕ) : ℕ := 4 * (2 * r + b)
private def pwClauseV (j : ℕ) : ℕ := 4 * j + 1
private def pwAssignV (k r a : ℕ) : ℕ := 4 * (a * k + r) + 2

private lemma pwAssignV_inj {k r₁ a₁ r₂ a₂ : ℕ} (hr₁ : r₁ < k) (hr₂ : r₂ < k)
    (h : pwAssignV k r₁ a₁ = pwAssignV k r₂ a₂) : r₁ = r₂ ∧ a₁ = a₂ := by
  have heq : a₁ * k + r₁ = a₂ * k + r₂ := by simp only [pwAssignV] at h; omega
  have hk : 0 < k := by omega
  have hr : r₁ = r₂ := by
    have := congrArg (· % k) heq
    simpa only [Nat.add_mul_mod_self_right, Nat.mul_add_mod_self_right,
      Nat.mod_eq_of_lt hr₁, Nat.mod_eq_of_lt hr₂] using this
  subst hr
  exact ⟨rfl, Nat.eq_of_mul_eq_mul_right hk (by omega)⟩

private def pwSatisfiesOn (vs : List ℕ) (a : ℕ) (c : Clause ℕ) : Bool :=
  c.any fun l => decide (l.1 ∈ vs) && (bitsAssignment vs a l.1 == l.2)

private lemma pwSatisfiesOn_iff {vs : List ℕ} {a : ℕ} {c : Clause ℕ} :
    pwSatisfiesOn vs a c = true ↔ ∃ l ∈ c, l.1 ∈ vs ∧ bitsAssignment vs a l.1 = l.2 := by
  simp [pwSatisfiesOn]

private def pwStaticVerts (k : ℕ) (φ : CNF ℕ) : List ℕ :=
  ((List.range k).flatMap fun r => [pwGuardV r 0, pwGuardV r 1]) ++
    (List.range φ.length).map pwClauseV

private def pwAssignVertsStep (k : ℕ) (φ : CNF ℕ) (a : ℕ) : List ℕ :=
  ((List.range k).filter fun r => decide (a < 2 ^ (pwBlock k φ r).length)).map
    fun r => pwAssignV k r a

private def pwGuardClauseEdgesStep (k : ℕ) (φ : CNF ℕ) (a : ℕ) : List (ℕ × ℕ) :=
  ((List.range k).filter fun r => decide (a < 2 ^ (pwBlock k φ r).length)).flatMap fun r =>
    [(pwAssignV k r a, pwGuardV r 0), (pwAssignV k r a, pwGuardV r 1)] ++
      ((List.range φ.length).filter fun j =>
        pwSatisfiesOn (pwBlock k φ r) a (φ.getD j [])).map
          fun j => (pwAssignV k r a, pwClauseV j)

private def pwCliqueEdgesStep (k : ℕ) (φ : CNF ℕ) (Q p : ℕ) : List (ℕ × ℕ) :=
  let a₁ := p / Q
  let a₂ := p % Q
  if a₁ < a₂ then
    ((List.range k).filter fun r => decide (a₂ < 2 ^ (pwBlock k φ r).length)).map
      fun r => (pwAssignV k r a₁, pwAssignV k r a₂)
  else []

/-- The Pătrașcu–Williams `k`-Dominating Set graph of a CNF formula `φ`: `k` cliques of block
partial assignments (of size at most $2^{\lceil n / k \rceil}$ each), two private guard vertices per
block forcing every dominating set of size at most `k` to pick one assignment per block, and one
vertex per clause of `φ` adjacent to all block assignments satisfying a literal in that clause. -/
def pwGraph (k : ℕ) (φ : CNF ℕ) : Graph where
  vertices :=
    pwStaticVerts k φ ++
      (List.range (2 ^ pwBlockSize k φ)).flatMap (pwAssignVertsStep k φ)
  edges :=
    (List.range (2 ^ pwBlockSize k φ)).flatMap (pwGuardClauseEdgesStep k φ) ++
      (List.range (2 ^ (2 * pwBlockSize k φ))).flatMap
        (pwCliqueEdgesStep k φ (2 ^ pwBlockSize k φ))

private lemma length_pwBlock_le (k : ℕ) (φ : CNF ℕ) (r : ℕ) :
    (pwBlock k φ r).length ≤ pwBlockSize k φ :=
  List.length_take_le _ _

private lemma mem_pwGraph_vertices {k : ℕ} {φ : CNF ℕ} {v : ℕ} :
    v ∈ (pwGraph k φ).vertices ↔
      (∃ r < k, v = pwGuardV r 0 ∨ v = pwGuardV r 1) ∨
      (∃ j < φ.length, v = pwClauseV j) ∨
      (∃ r < k, ∃ a < 2 ^ (pwBlock k φ r).length, v = pwAssignV k r a) := by
  have h1 : v ∈ pwStaticVerts k φ ↔
      (∃ r < k, v = pwGuardV r 0 ∨ v = pwGuardV r 1) ∨ (∃ j < φ.length, v = pwClauseV j) := by
    simp [pwStaticVerts, eq_comm]
  have h2 : v ∈ (List.range (2 ^ pwBlockSize k φ)).flatMap (pwAssignVertsStep k φ) ↔
      ∃ r < k, ∃ a < 2 ^ (pwBlock k φ r).length, v = pwAssignV k r a := by
    simp only [pwAssignVertsStep, List.mem_flatMap, List.mem_range, List.mem_map, List.mem_filter,
      decide_eq_true_eq]
    exact ⟨fun ⟨a, _, r, ⟨hr, ha⟩, hv⟩ => ⟨r, hr, a, ha, hv.symm⟩, fun ⟨r, hr, a, ha, hv⟩ =>
      ⟨a, lt_of_lt_of_le ha (Nat.pow_le_pow_right (by norm_num) (length_pwBlock_le k φ r)),
        r, ⟨hr, ha⟩, hv.symm⟩⟩
  simp only [pwGraph, List.mem_append, h1, h2, or_assoc]

private lemma mem_pwGraph_edges {k : ℕ} {φ : CNF ℕ} {u v : ℕ} :
    (u, v) ∈ (pwGraph k φ).edges ↔
      (∃ r < k, ∃ a < 2 ^ (pwBlock k φ r).length,
        u = pwAssignV k r a ∧
        (v = pwGuardV r 0 ∨ v = pwGuardV r 1 ∨
          ∃ j < φ.length, pwSatisfiesOn (pwBlock k φ r) a (φ.getD j []) = true ∧
            v = pwClauseV j)) ∨
      (∃ r < k, ∃ a₁ a₂, a₁ < a₂ ∧ a₂ < 2 ^ (pwBlock k φ r).length ∧
        u = pwAssignV k r a₁ ∧ v = pwAssignV k r a₂) := by
  set Q := 2 ^ pwBlockSize k φ with hQ
  have hQ2 : 2 ^ (2 * pwBlockSize k φ) = Q * Q := by
    rw [hQ, two_mul, Nat.pow_add]
  simp only [pwGraph, ← hQ, hQ2, List.mem_append, List.mem_flatMap, List.mem_range]
  refine or_congr ⟨?_, ?_⟩ ⟨?_, ?_⟩
  · rintro ⟨a, _, hm⟩
    simp only [pwGuardClauseEdgesStep, List.mem_flatMap, List.mem_filter, List.mem_range,
      decide_eq_true_eq, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
      List.mem_map, Prod.mk.injEq] at hm
    rcases hm with ⟨r, ⟨hr, ha⟩, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) | ⟨j, ⟨hj, hsat⟩, rfl, rfl⟩⟩
    · exact ⟨r, hr, a, ha, rfl, Or.inl rfl⟩
    · exact ⟨r, hr, a, ha, rfl, Or.inr (Or.inl rfl)⟩
    · exact ⟨r, hr, a, ha, rfl, Or.inr (Or.inr ⟨j, hj, hsat, rfl⟩)⟩
  · rintro ⟨r, hr, a, ha, rfl, rfl | rfl | ⟨j, hj, hsat, rfl⟩⟩
    all_goals
      have haQ : a < Q :=
        lt_of_lt_of_le ha (Nat.pow_le_pow_right (by norm_num) (length_pwBlock_le k φ r))
      refine ⟨a, haQ, ?_⟩
      simp only [pwGuardClauseEdgesStep, List.mem_flatMap, List.mem_filter, List.mem_range,
        decide_eq_true_eq, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
        List.mem_map, Prod.mk.injEq]
      refine ⟨r, ⟨hr, ha⟩, ?_⟩
    · exact Or.inl (Or.inl ⟨rfl, rfl⟩)
    · exact Or.inl (Or.inr ⟨rfl, rfl⟩)
    · exact Or.inr ⟨j, ⟨hj, hsat⟩, rfl, rfl⟩
  · rintro ⟨p, _, hm⟩
    simp only [pwCliqueEdgesStep] at hm
    split_ifs at hm with hlt
    · simp only [List.mem_map, List.mem_filter, List.mem_range, decide_eq_true_eq,
        Prod.mk.injEq] at hm
      obtain ⟨r, ⟨hr, ha₂⟩, rfl, rfl⟩ := hm
      exact ⟨r, hr, p / Q, p % Q, hlt, ha₂, rfl, rfl⟩
    · simp at hm
  · rintro ⟨r, hr, a₁, a₂, hlt, ha₂, rfl, rfl⟩
    have ha₂Q : a₂ < Q :=
      lt_of_lt_of_le ha₂ (Nat.pow_le_pow_right (by norm_num) (length_pwBlock_le k φ r))
    have ha₁Q : a₁ < Q := lt_trans hlt ha₂Q
    have hQpos : 0 < Q := Nat.pos_of_ne_zero (by positivity)
    refine ⟨a₁ * Q + a₂, by nlinarith, ?_⟩
    have hdiv : (a₁ * Q + a₂) / Q = a₁ := by
      rw [Nat.mul_comm, Nat.mul_add_div hQpos, Nat.div_eq_of_lt ha₂Q, Nat.add_zero]
    have hmod : (a₁ * Q + a₂) % Q = a₂ := by
      rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt ha₂Q]
    simp only [pwCliqueEdgesStep, hdiv, hmod, hlt, ↓reduceIte, List.mem_map, List.mem_filter,
      List.mem_range, decide_eq_true_eq, Prod.mk.injEq]
    exact ⟨r, ⟨hr, ha₂⟩, rfl, rfl⟩

/-- The declared vertex list of `pwGraph k φ` contains no duplicates. -/
theorem nodup_pwGraph_vertices (k : ℕ) (φ : CNF ℕ) : (pwGraph k φ).vertices.Nodup := by
  have hg : ((List.range k).flatMap fun r => [pwGuardV r 0, pwGuardV r 1]).Nodup := by
    rw [List.nodup_flatMap]
    refine ⟨fun r _ => by simp [pwGuardV], ?_⟩
    refine List.nodup_range.pairwise_of_forall_ne fun r₁ _ r₂ _ hne v hv₁ hv₂ => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false, pwGuardV] at hv₁ hv₂
    rcases hv₁ with rfl | rfl <;> rcases hv₂ with h | h <;> omega
  have hc : ((List.range φ.length).map pwClauseV).Nodup :=
    List.Nodup.map (fun i j h => by simp only [pwClauseV] at h; omega) List.nodup_range
  have hstatic : (pwStaticVerts k φ).Nodup := by
    refine List.nodup_append.mpr ⟨hg, hc, fun u hu v hv heq => ?_⟩
    simp only [List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil, or_false,
      List.mem_map, pwGuardV, pwClauseV] at hu hv
    obtain ⟨r, _, rfl | rfl⟩ := hu <;> obtain ⟨j, _, rfl⟩ := hv <;> omega
  have hassign :
      ((List.range (2 ^ pwBlockSize k φ)).flatMap (pwAssignVertsStep k φ)).Nodup := by
    rw [List.nodup_flatMap]
    refine ⟨fun a _ => ?_, ?_⟩
    · refine List.Nodup.map (fun r₁ r₂ h => ?_) (List.nodup_range.filter _)
      simp only [pwAssignV] at h; omega
    · refine List.nodup_range.pairwise_of_forall_ne fun a₁ _ a₂ _ hne v hv₁ hv₂ => ?_
      simp only [pwAssignVertsStep, List.mem_map, List.mem_filter, List.mem_range] at hv₁ hv₂
      obtain ⟨r₁, ⟨hr₁, _⟩, rfl⟩ := hv₁
      obtain ⟨r₂, ⟨hr₂, _⟩, heq⟩ := hv₂
      exact hne (pwAssignV_inj hr₁ hr₂ heq.symm).2
  refine List.nodup_append.mpr ⟨hstatic, hassign, fun u hu v hv heq => ?_⟩
  simp only [pwStaticVerts, List.mem_append, List.mem_flatMap, List.mem_range, List.mem_cons,
    List.not_mem_nil, or_false, List.mem_map, pwAssignVertsStep, List.mem_filter, pwGuardV,
    pwClauseV, pwAssignV] at hu hv
  obtain ⟨a, _, r, _, rfl⟩ := hv
  rcases hu with ⟨r', _, rfl | rfl⟩ | ⟨j, _, rfl⟩ <;> omega

/-- The vertex count of `pwGraph k φ` is at most $2k + m + k \cdot 2^{\lceil n / k \rceil}$. -/
theorem length_pwGraph_vertices_le (k : ℕ) (φ : CNF ℕ) :
    (pwGraph k φ).vertices.length ≤ 2 * k + φ.length + k * 2 ^ pwBlockSize k φ := by
  have hg : ((List.range k).flatMap fun r => [pwGuardV r 0, pwGuardV r 1]).length = 2 * k := by
    induction k with
    | zero => rfl
    | succ m ih => rw [List.range_succ, List.flatMap_append, List.length_append, ih]; simp; omega
  have ha : ∀ L : List ℕ, (L.flatMap (pwAssignVertsStep k φ)).length ≤ L.length * k := by
    intro L
    induction L with
    | nil => simp
    | cons a L ih =>
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      have hstep : (pwAssignVertsStep k φ a).length ≤ k := by
        simpa [pwAssignVertsStep] using List.length_filter_le _ (List.range k)
      nlinarith
  have h1 := ha (List.range (2 ^ pwBlockSize k φ))
  simp only [pwGraph, pwStaticVerts, List.length_append, hg, List.length_map,
    List.length_range] at h1 ⊢
  nlinarith

private lemma three_mul_le_pwGraph_vertices (k : ℕ) (φ : CNF ℕ) :
    3 * k ≤ (pwGraph k φ).vertices.length := by
  rw [← (pwGraph k φ).vertices.toFinset_card_of_nodup (nodup_pwGraph_vertices k φ)]
  let S : Finset ℕ := (Finset.range k).biUnion fun r =>
    {pwGuardV r 0, pwGuardV r 1, pwAssignV k r 0}
  have hsub : S ⊆ (pwGraph k φ).vertices.toFinset := by
    intro v hv
    simp only [S, Finset.mem_biUnion, Finset.mem_range, Finset.mem_insert,
      Finset.mem_singleton] at hv
    rw [List.mem_toFinset, mem_pwGraph_vertices]
    rcases hv with ⟨r, hr, rfl | rfl | rfl⟩
    · exact Or.inl ⟨r, hr, Or.inl rfl⟩
    · exact Or.inl ⟨r, hr, Or.inr rfl⟩
    · exact Or.inr (Or.inr ⟨r, hr, 0, Nat.two_pow_pos _, rfl⟩)
  have hcard : S.card = 3 * k := by
    rw [Finset.card_biUnion]
    · have h3 : ∀ r ∈ Finset.range k,
          ({pwGuardV r 0, pwGuardV r 1, pwAssignV k r 0} : Finset ℕ).card = 3 := by
        intro r _
        rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
        · simp [pwGuardV, pwAssignV]; omega
        · simp [pwGuardV, pwAssignV]; omega
      rw [Finset.sum_congr rfl h3, Finset.sum_const, Finset.card_range, smul_eq_mul, Nat.mul_comm]
    · intro r₁ hr₁ r₂ hr₂ hne
      refine Finset.disjoint_left.mpr fun v hv₁ hv₂ => ?_
      have hr₁' : r₁ < k := by simpa using hr₁
      have hr₂' : r₂ < k := by simpa using hr₂
      simp only [Finset.mem_insert, Finset.mem_singleton, pwGuardV, pwAssignV] at hv₁ hv₂
      rcases hv₁ with rfl | rfl | rfl <;> rcases hv₂ with h | h | h <;> omega
  exact hcard ▸ Finset.card_le_card hsub

private lemma mem_pwBlock_of_mem_vars {k : ℕ} (hk : 1 ≤ k) {φ : CNF ℕ} {x : ℕ} (hx : x ∈ φ.vars) :
    ∃ r < k, x ∈ pwBlock k φ r := by
  have hxd : x ∈ φ.distinctVars := CNF.mem_distinctVars.mpr hx
  obtain ⟨idx, hidx, rfl⟩ := List.mem_iff_getElem.mp hxd
  rw [CNF.length_distinctVars] at hidx
  set q := pwBlockSize k φ with hq
  have hcov : φ.numVars ≤ k * q := by
    have hd : k * q + (φ.numVars + k - 1) % k = φ.numVars + k - 1 :=
      Nat.div_add_mod (φ.numVars + k - 1) k
    have hm := Nat.mod_lt (φ.numVars + k - 1) (show 0 < k by omega)
    omega
  have hq_pos : 0 < q := Nat.pos_of_ne_zero fun h0 => by rw [h0, Nat.mul_zero] at hcov; omega
  have hlt_r : idx / q < k := Nat.div_lt_of_lt_mul (by linarith)
  have hlt_rem : idx % q < (pwBlock k φ (idx / q)).length := by
    simp only [pwBlock, ← hq, List.length_take, List.length_drop, CNF.length_distinctVars]
    have hd : idx / q * q + idx % q = idx := by rw [Nat.mul_comm]; exact Nat.div_add_mod idx q
    exact lt_min (Nat.mod_lt idx hq_pos) (by omega)
  refine ⟨idx / q, hlt_r, List.mem_iff_getElem.mpr ⟨idx % q, hlt_rem, ?_⟩⟩
  have heq : idx / q * q + idx % q = idx := by rw [Nat.mul_comm]; exact Nat.div_add_mod idx q
  simp only [pwBlock, ← hq, List.getElem_take, List.getElem_drop, heq]

private lemma pwBlock_disjoint {k : ℕ} {φ : CNF ℕ} {r₁ r₂ : ℕ} (hne : r₁ ≠ r₂) {x : ℕ}
    (h₁ : x ∈ pwBlock k φ r₁) (h₂ : x ∈ pwBlock k φ r₂) : False := by
  obtain ⟨i₁, hi₁, hx₁⟩ := List.mem_iff_getElem.mp h₁
  obtain ⟨i₂, hi₂, hx₂⟩ := List.mem_iff_getElem.mp h₂
  set q := pwBlockSize k φ
  have hq₁ : i₁ < q := lt_of_lt_of_le hi₁ (List.length_take_le _ _)
  have hq₂ : i₂ < q := lt_of_lt_of_le hi₂ (List.length_take_le _ _)
  simp only [pwBlock, List.getElem_take, List.getElem_drop] at hx₁ hx₂
  have hidx_eq : r₁ * q + i₁ = r₂ * q + i₂ :=
    (List.Nodup.getElem_inj_iff φ.nodup_distinctVars).mp (hx₁.trans hx₂.symm)
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have : (r₁ + 1) * q ≤ r₂ * q := Nat.mul_le_mul_right q hlt
    nlinarith
  · have : (r₂ + 1) * q ≤ r₁ * q := Nat.mul_le_mul_right q hgt
    nlinarith

private lemma pwGraph_adj_guard_iff {k : ℕ} {φ : CNF ℕ} {r b s : ℕ} (hb : b = 0 ∨ b = 1) :
    (pwGraph k φ).toSimpleGraph.Adj (pwGuardV r b) s ↔
      r < k ∧ ∃ a < 2 ^ (pwBlock k φ r).length, s = pwAssignV k r a := by
  rw [Graph.toSimpleGraph_adj]
  constructor
  · rintro ⟨_, h1 | h2⟩
    · rw [mem_pwGraph_edges] at h1
      rcases h1 with ⟨r', _, a, _, heq, _⟩ | ⟨r', _, a₁, a₂, _, _, heq, _⟩ <;>
        (simp only [pwGuardV, pwAssignV] at heq; omega)
    · rw [mem_pwGraph_edges] at h2
      rcases h2 with ⟨r', hr', a, ha, rfl, h0 | h1' | ⟨j, _, _, hc⟩⟩ |
          ⟨r', _, a₁, a₂, _, _, _, hc⟩
      · have : r' = r := by rcases hb with rfl | rfl <;> (simp only [pwGuardV] at h0; omega)
        subst this; exact ⟨hr', a, ha, rfl⟩
      · have : r' = r := by rcases hb with rfl | rfl <;> (simp only [pwGuardV] at h1'; omega)
        subst this; exact ⟨hr', a, ha, rfl⟩
      · simp only [pwGuardV, pwClauseV] at hc; omega
      · simp only [pwGuardV, pwAssignV] at hc; omega
  · rintro ⟨hr, a, ha, rfl⟩
    refine ⟨by simp [pwGuardV, pwAssignV]; omega, Or.inr (mem_pwGraph_edges.mpr (Or.inl ?_))⟩
    refine ⟨r, hr, a, ha, rfl, ?_⟩
    rcases hb with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)

private lemma pwGraph_adj_clause_assign {k : ℕ} {φ : CNF ℕ} {j r a : ℕ} (hj : j < φ.length)
    (hr : r < k) (ha : a < 2 ^ (pwBlock k φ r).length) :
    (pwGraph k φ).toSimpleGraph.Adj (pwClauseV j) (pwAssignV k r a) ↔
      pwSatisfiesOn (pwBlock k φ r) a (φ.getD j []) = true := by
  rw [Graph.toSimpleGraph_adj]
  constructor
  · rintro ⟨_, h1 | h2⟩
    · rw [mem_pwGraph_edges] at h1
      rcases h1 with ⟨_, _, _, _, hc, _⟩ | ⟨_, _, _, _, _, _, hc, _⟩ <;>
        (simp only [pwClauseV, pwAssignV] at hc; omega)
    · rw [mem_pwGraph_edges] at h2
      rcases h2 with ⟨r', hr', a', _, hassign, h0 | h1 | ⟨j', _, hsat, hcl⟩⟩ |
          ⟨_, _, _, _, _, _, _, hc⟩
      · simp only [pwClauseV, pwGuardV] at h0; omega
      · simp only [pwClauseV, pwGuardV] at h1; omega
      · obtain ⟨rfl, rfl⟩ := pwAssignV_inj hr hr' hassign
        have : j = j' := by simp only [pwClauseV] at hcl; omega
        subst this; exact hsat
      · simp only [pwClauseV, pwAssignV] at hc; omega
  · intro hsat
    refine ⟨by simp [pwClauseV, pwAssignV]; omega, Or.inr (mem_pwGraph_edges.mpr (Or.inl ?_))⟩
    exact ⟨r, hr, a, ha, rfl, Or.inr (Or.inr ⟨j, hj, hsat, rfl⟩)⟩

/-- Correctness of the Pătrașcu–Williams reduction for dominating sets of size at most `k`. -/
theorem pwGraph_mem_kDominatingSetLe_iff {k : ℕ} (hk : 1 ≤ k) (φ : CNF ℕ) :
    pwGraph k φ ∈ kDominatingSetLe k ↔ φ ∈ SAT := by
  rw [kDominatingSetLe, Set.mem_ofPred_eq, mem_SAT]
  constructor
  · rintro ⟨S, _, hdom, hcard⟩
    let blockPart (r : ℕ) : Finset ℕ :=
      S.filter fun v => v = pwGuardV r 0 ∨ v = pwGuardV r 1 ∨
        ∃ a < 2 ^ (pwBlock k φ r).length, v = pwAssignV k r a
    have hdisj : (SetLike.coe (Finset.range k)).PairwiseDisjoint blockPart := by
      intro r₁ hr₁ r₂ hr₂ hne
      refine Finset.disjoint_left.mpr fun v hv₁ hv₂ => ?_
      have hr₁' : r₁ < k := by simpa using hr₁
      have hr₂' : r₂ < k := by simpa using hr₂
      simp only [blockPart, Finset.mem_filter] at hv₁ hv₂
      rcases hv₁.2 with rfl | rfl | ⟨a₁, _, rfl⟩ <;>
        rcases hv₂.2 with h | h | ⟨a₂, _, h⟩
      all_goals try (simp only [pwGuardV, pwAssignV] at h; exact hne (by omega))
      exact hne (pwAssignV_inj hr₁' hr₂' h).1
    have hpos : ∀ r ∈ Finset.range k, 1 ≤ (blockPart r).card := by
      intro r hr
      have hr' : r < k := Finset.mem_range.mp hr
      have hg0 : pwGuardV r 0 ∈ (pwGraph k φ).vertices :=
        mem_pwGraph_vertices.mpr (Or.inl ⟨r, hr', Or.inl rfl⟩)
      refine Finset.one_le_card.mpr ?_
      rcases hdom _ hg0 with hs | ⟨s, hs, hadj⟩
      · exact ⟨pwGuardV r 0, Finset.mem_filter.mpr ⟨hs, Or.inl rfl⟩⟩
      · obtain ⟨_, a, ha, rfl⟩ := (pwGraph_adj_guard_iff (Or.inl rfl)).mp hadj
        exact ⟨pwAssignV k r a, Finset.mem_filter.mpr ⟨hs, Or.inr (Or.inr ⟨a, ha, rfl⟩)⟩⟩
    let U : Finset ℕ := (Finset.range k).biUnion blockPart
    have hUS : U ⊆ S := by
      intro v hv
      simp only [U, Finset.mem_biUnion] at hv
      obtain ⟨r, _, hvr⟩ := hv
      exact (Finset.mem_filter.mp hvr).1
    have hUcard : k ≤ U.card := by
      calc k = ∑ _r ∈ Finset.range k, 1 := by simp
        _ ≤ ∑ r ∈ Finset.range k, (blockPart r).card := Finset.sum_le_sum hpos
        _ = U.card := (Finset.card_biUnion hdisj).symm
    have hSU : S = U := (Finset.eq_of_subset_of_card_le hUS (hcard.trans hUcard)).symm
    have hcard_eq : ∀ r < k, (blockPart r).card = 1 := by
      intro r hr
      by_contra hne
      have hgt : 1 < (blockPart r).card :=
        lt_of_le_of_ne (hpos r (Finset.mem_range.mpr hr)) (Ne.symm hne)
      have hlt : k < U.card := by
        rw [Finset.card_biUnion hdisj]
        calc k = ∑ _i ∈ Finset.range k, 1 := by simp
          _ < ∑ i ∈ Finset.range k, (blockPart i).card :=
              Finset.sum_lt_sum hpos ⟨r, Finset.mem_range.mpr hr, hgt⟩
      exact absurd (hSU ▸ hcard) (not_le.mpr hlt)
    have hex_assign : ∀ r < k, ∃ a < 2 ^ (pwBlock k φ r).length,
        blockPart r = {pwAssignV k r a} := by
      intro r hr
      obtain ⟨w, hw⟩ := Finset.card_eq_one.mp (hcard_eq r hr)
      have hw_mem : w ∈ blockPart r := hw ▸ Finset.mem_singleton_self w
      rcases (Finset.mem_filter.mp hw_mem).2 with rfl | rfl | ⟨a, ha, rfl⟩
      · rcases hdom _ (mem_pwGraph_vertices.mpr (Or.inl ⟨r, hr, Or.inr rfl⟩)) with hs | ⟨s, hs, hj⟩
        · have hm : pwGuardV r 1 ∈ ({pwGuardV r 0} : Finset ℕ) :=
            by rw [← hw]; exact Finset.mem_filter.mpr ⟨hs, Or.inr (Or.inl rfl)⟩
          simp only [Finset.mem_singleton, pwGuardV] at hm; omega
        · obtain ⟨_, a', ha', rfl⟩ := (pwGraph_adj_guard_iff (Or.inr rfl)).mp hj
          have hm : pwAssignV k r a' ∈ ({pwGuardV r 0} : Finset ℕ) :=
            by rw [← hw]; exact Finset.mem_filter.mpr ⟨hs, Or.inr (Or.inr ⟨a', ha', rfl⟩)⟩
          simp only [Finset.mem_singleton, pwGuardV, pwAssignV] at hm; omega
      · rcases hdom _ (mem_pwGraph_vertices.mpr (Or.inl ⟨r, hr, Or.inl rfl⟩)) with hs | ⟨s, hs, hj⟩
        · have hm : pwGuardV r 0 ∈ ({pwGuardV r 1} : Finset ℕ) :=
            by rw [← hw]; exact Finset.mem_filter.mpr ⟨hs, Or.inl rfl⟩
          simp only [Finset.mem_singleton, pwGuardV] at hm; omega
        · obtain ⟨_, a', ha', rfl⟩ := (pwGraph_adj_guard_iff (Or.inl rfl)).mp hj
          have hm : pwAssignV k r a' ∈ ({pwGuardV r 1} : Finset ℕ) :=
            by rw [← hw]; exact Finset.mem_filter.mpr ⟨hs, Or.inr (Or.inr ⟨a', ha', rfl⟩)⟩
          simp only [Finset.mem_singleton, pwGuardV, pwAssignV] at hm; omega
      · exact ⟨a, ha, hw⟩
    let chosen (r : ℕ) : ℕ :=
      if hr : r < k then Classical.choose (hex_assign r hr) else 0
    have hchosen_lt (r : ℕ) (hr : r < k) : chosen r < 2 ^ (pwBlock k φ r).length := by
      simp only [chosen, hr, ↓reduceDIte]
      exact (Classical.choose_spec (hex_assign r hr)).1
    have hchosen_eq (r : ℕ) (hr : r < k) : blockPart r = {pwAssignV k r (chosen r)} := by
      simp only [chosen, hr, ↓reduceDIte]
      exact (Classical.choose_spec (hex_assign r hr)).2
    have hmem_S {s : ℕ} (hs : s ∈ S) : ∃ r < k, s = pwAssignV k r (chosen r) := by
      rw [hSU] at hs
      simp only [U, Finset.mem_biUnion, Finset.mem_range] at hs
      obtain ⟨r, hr, hsr⟩ := hs
      rw [hchosen_eq r hr, Finset.mem_singleton] at hsr
      exact ⟨r, hr, hsr⟩
    classical
    let σ (x : ℕ) : Bool :=
      if hx : ∃ r < k, x ∈ pwBlock k φ r then
        let r := Classical.choose hx
        bitsAssignment (pwBlock k φ r) (chosen r) x
      else false
    refine ⟨σ, (CNF.eval_eq_true_iff σ φ).mpr fun c hc => ?_⟩
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hc
    have hcj : pwClauseV j ∈ (pwGraph k φ).vertices :=
      mem_pwGraph_vertices.mpr (Or.inr (Or.inl ⟨j, hj, rfl⟩))
    rcases hdom _ hcj with hs | ⟨s, hs, hadj⟩
    · obtain ⟨r, _, hbad⟩ := hmem_S hs
      simp only [pwClauseV, pwAssignV] at hbad; omega
    · obtain ⟨r, hr, rfl⟩ := hmem_S hs
      have hsat := (pwGraph_adj_clause_assign hj hr (hchosen_lt r hr)).mp hadj
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some,
        pwSatisfiesOn_iff] at hsat
      obtain ⟨l, hl, hlv, heval⟩ := hsat
      refine (Clause.eval_eq_true_iff σ φ[j]).mpr ⟨l, hl, ?_⟩
      have hex : ∃ r' < k, l.1 ∈ pwBlock k φ r' := ⟨r, hr, hlv⟩
      simp only [σ, hex, ↓reduceDIte]
      have hspec := (Classical.choose_spec hex).2
      have hsame : Classical.choose hex = r := by
        by_contra hne
        exact pwBlock_disjoint hne hspec hlv
      rw [hsame, heval]
  · rintro ⟨σ, hσ⟩
    have hex_a : ∀ r < k, ∃ a < 2 ^ (pwBlock k φ r).length,
        ∀ x ∈ pwBlock k φ r, bitsAssignment (pwBlock k φ r) a x = σ x :=
      fun r _ => exists_lt_two_pow_bitsAssignment_eq σ
    let aOf (r : ℕ) : ℕ := if hr : r < k then Classical.choose (hex_a r hr) else 0
    have ha_lt (r : ℕ) (hr : r < k) : aOf r < 2 ^ (pwBlock k φ r).length := by
      simp only [aOf, hr, ↓reduceDIte]; exact (Classical.choose_spec (hex_a r hr)).1
    have ha_eq (r : ℕ) (hr : r < k) :
        ∀ x ∈ pwBlock k φ r, bitsAssignment (pwBlock k φ r) (aOf r) x = σ x := by
      simp only [aOf, hr, ↓reduceDIte]; exact (Classical.choose_spec (hex_a r hr)).2
    let S : Finset ℕ := (Finset.range k).image fun r => pwAssignV k r (aOf r)
    refine ⟨S, ?_, ?_, Finset.card_image_le.trans (by simp)⟩
    · intro v hv
      obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hv
      have hr' := Finset.mem_range.mp hr
      exact mem_pwGraph_vertices.mpr (Or.inr (Or.inr ⟨r, hr', aOf r, ha_lt r hr', rfl⟩))
    · intro v hv
      rcases mem_pwGraph_vertices.mp hv with
          ⟨r, hr, rfl | rfl⟩ | ⟨j, hj, rfl⟩ | ⟨r, hr, a, ha, rfl⟩
      · exact Or.inr ⟨pwAssignV k r (aOf r),
          Finset.mem_image_of_mem _ (Finset.mem_range.mpr hr),
          (pwGraph_adj_guard_iff (Or.inl rfl)).mpr ⟨hr, aOf r, ha_lt r hr, rfl⟩⟩
      · exact Or.inr ⟨pwAssignV k r (aOf r),
          Finset.mem_image_of_mem _ (Finset.mem_range.mpr hr),
          (pwGraph_adj_guard_iff (Or.inr rfl)).mpr ⟨hr, aOf r, ha_lt r hr, rfl⟩⟩
      · have hcj := (CNF.eval_eq_true_iff σ φ).mp hσ φ[j] (List.getElem_mem hj)
        obtain ⟨l, hl, hleval⟩ := (Clause.eval_eq_true_iff σ φ[j]).mp hcj
        have hlvars : l.1 ∈ φ.vars :=
          List.mem_map.mpr ⟨l, List.mem_flatten.mpr ⟨φ[j], List.getElem_mem hj, hl⟩, rfl⟩
        obtain ⟨r, hr, hlr⟩ := mem_pwBlock_of_mem_vars hk hlvars
        refine Or.inr ⟨pwAssignV k r (aOf r),
          Finset.mem_image_of_mem _ (Finset.mem_range.mpr hr),
          (pwGraph_adj_clause_assign hj hr (ha_lt r hr)).mpr ?_⟩
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some,
          pwSatisfiesOn_iff]
        exact ⟨l, hl, hlr, (ha_eq r hr l.1 hlr).trans hleval⟩
      · rcases lt_trichotomy a (aOf r) with hlt | rfl | hgt
        · exact Or.inr ⟨pwAssignV k r (aOf r),
            Finset.mem_image_of_mem _ (Finset.mem_range.mpr hr),
            Graph.toSimpleGraph_adj.mpr ⟨by simp [pwAssignV]; omega,
              Or.inl (mem_pwGraph_edges.mpr (Or.inr ⟨r, hr, a, aOf r, hlt, ha_lt r hr, rfl, rfl⟩))⟩⟩
        · exact Or.inl (Finset.mem_image_of_mem _ (Finset.mem_range.mpr hr))
        · exact Or.inr ⟨pwAssignV k r (aOf r),
            Finset.mem_image_of_mem _ (Finset.mem_range.mpr hr),
            Graph.toSimpleGraph_adj.mpr ⟨by simp [pwAssignV]; omega,
              Or.inr (mem_pwGraph_edges.mpr (Or.inr ⟨r, hr, aOf r, a, hgt, ha, rfl, rfl⟩))⟩⟩

/-- Correctness of the Pătrașcu–Williams reduction for exact `k`-Dominating Set. -/
theorem pwGraph_mem_kDominatingSet_iff {k : ℕ} (hk : 1 ≤ k) (φ : CNF ℕ) :
    pwGraph k φ ∈ kDominatingSet k ↔ φ ∈ SAT := by
  rw [kDominatingSet, Set.mem_ofPred_eq, mem_DominatingSet_iff_exists_card_le,
    ← pwGraph_mem_kDominatingSetLe_iff hk, kDominatingSetLe, Set.mem_ofPred_eq,
      and_iff_right_iff_imp]
  intro _
  rw [(pwGraph k φ).vertices.toFinset_card_of_nodup (nodup_pwGraph_vertices k φ)]
  have := three_mul_le_pwGraph_vertices k φ
  omega

/-! ### Streaming runtime of the Pătrașcu–Williams reduction -/

private lemma computableInPolyTime_pwBlockSize (k : ℕ) :
    ComputableInPolyTime (pwBlockSize k) encCNF encUnary := by
  have hdv := SAT.computableInPolyTime_distinctVars
  have hnum : ComputableInPolyTime CNF.numVars encCNF encUnary := by
    have heq : (CNF.numVars : CNF ℕ → ℕ) = fun φ => φ.distinctVars.length :=
      funext fun φ => φ.length_distinctVars.symm
    rw [heq]; fun_prop
  have hdiv := ComputableInPolyTime.unary_div_const k
  unfold pwBlockSize
  fun_prop

private lemma computableInPolyTime_pwBlock (k r : ℕ) :
    ComputableInPolyTime (fun φ => pwBlock k φ r) encCNF (encList encNat) := by
  have hdv := SAT.computableInPolyTime_distinctVars
  have hq := computableInPolyTime_pwBlockSize k
  have hmul : ComputableInPolyTime (fun φ => r * pwBlockSize k φ) encCNF encUnary := by fun_prop
  have hdrop := (ComputableInPolyTime.dropUnary (encA := encNat)).comp (hdv.prod hmul)
  exact (computableInPolyTime_takeUnary encNat).comp (hdrop.prod hq)

private lemma pwBlockSize_le_encCNF (k : ℕ) (φ : CNF ℕ) :
    pwBlockSize k φ ≤ (encCNF φ).length + 1 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [pwBlockSize]
  · have hq : (φ.numVars + k - 1) / k ≤ φ.numVars := by
      rcases Nat.eq_zero_or_pos φ.numVars with h0 | hn
      · rw [h0, Nat.zero_add]
        exact Nat.div_eq_of_lt (by omega) |>.le
      · refine Nat.div_le_of_le_mul ?_
        rcases k with _ | _ | k'
        · omega
        · simp
        · rcases hnv : φ.numVars with _ | n'
          · omega
          · have : n' + 1 + (k' + 2) - 1 = n' + k' + 2 := by omega
            rw [this]; nlinarith
    have hn : φ.numVars ≤ (encCNF φ).length :=
      φ.numVars_le_length_vars.trans (SAT.length_vars_le φ)
    simp only [pwBlockSize]
    omega

private lemma computableInPolyTime_pwSatisfiesOn {α : Type} (encα : α ↪ List Bool)
    {vs : α → List ℕ} {a : α → ℕ} {c : α → Clause ℕ}
    (hvs : ComputableInPolyTime vs encα (encList encNat))
    (ha : ComputableInPolyTime a encα encNat)
    (hc : ComputableInPolyTime c encα (encList (encPair encNat encBool))) :
    ComputableInPolyTime (fun x => pwSatisfiesOn (vs x) (a x) (c x)) encα encBool := by
  let encL := encPair encNat encBool
  have heq : (fun x => pwSatisfiesOn (vs x) (a x) (c x)) = fun x =>
      (c x).any fun l => decide ((vs x).idxOf l.1 < (vs x).length) &&
        ((a x).bits.getD ((vs x).idxOf l.1) false == l.2) := by
    funext x
    simp only [pwSatisfiesOn, bitsAssignment_eq_getD, List.idxOf_lt_length_iff]
  rw [heq]
  have hfst := ComputableInPolyTime.fst encα encL
  have hsnd := ComputableInPolyTime.snd encα encL
  have hvs' := hvs.comp hfst
  have hl1 : ComputableInPolyTime (fun p : α × Literal ℕ => p.2.1) (encPair encα encL) encNat := by
    unfold encL; fun_prop
  have hl2 : ComputableInPolyTime (fun p : α × Literal ℕ => p.2.2) (encPair encα encL) encBool := by
    unfold encL; fun_prop
  have hbits := ComputableInPolyTime.natBits.comp (ha.comp hfst)
  have hidx := ComputableInPolyTime.idxOfWithInput hvs' hl1
  have hget := ComputableInPolyTime.bitsGetDWithInput hbits hidx false
  have hlen := (ComputableInPolyTime.length_list encNat).comp hvs'
  have hlit := ComputableInPolyTime.bool_and'
    (ComputableInPolyTime.unary_lt' hidx hlen) (hget.beq hl2)
  exact ComputableInPolyTime.anyWithInput hc hlit

private lemma computableInPolyTime_listRangeFilterMap {α γ : Type}
    (encα : α ↪ List Bool) (encγ : γ ↪ List Bool) (k : ℕ)
    (cond : α → ℕ → Bool) (body : α → ℕ → List γ)
    (hcond : ∀ r < k, ComputableInPolyTime (fun x => cond x r) encα encBool)
    (hbody : ∀ r < k, ComputableInPolyTime (fun x => body x r) encα (encList encγ)) :
    ComputableInPolyTime
      (fun x => ((List.range k).filter (cond x)).flatMap (body x))
      encα (encList encγ) := by
  induction k with
  | zero => exact ComputableInPolyTime.const []
  | succ m ih =>
    have heq : (fun x => ((List.range (m + 1)).filter (cond x)).flatMap (body x)) =
        fun x => ((List.range m).filter (cond x)).flatMap (body x) ++
          if cond x m then body x m else [] := by
      funext x
      rw [List.range_succ, List.filter_append, List.flatMap_append]
      cases h : cond x m <;> simp [h]
    rw [heq]
    have hprev := ih (fun r hr => hcond r (by omega)) (fun r hr => hbody r (by omega))
    have hcm := hcond m (by omega)
    have hbm := hbody m (by omega)
    have hlast := hcm.ite hbm (ComputableInPolyTime.const [])
    fun_prop

private lemma exists_computableInO_cnf_stream (k : ℕ) (mult : ℕ) (hmult : 1 ≤ mult)
    {emit : CNF ℕ × ℕ → List Bool}
    (hemit : ComputableInPolyTime emit (encPair encCNF encNat) encBits) (fin : List Bool) :
    ∃ e : ℕ, ComputableInO
      (fun φ => ((List.range (2 ^ (mult * pwBlockSize k φ))).map fun i => emit (φ, i)).flatten ++
        fin)
      encCNF encBits
      (fun φ => 2 ^ (mult * pwBlockSize k φ) * ((encCNF φ).length + 1) ^ e)
      (fun φ => 2 ^ (mult * pwBlockSize k φ) * ((encCNF φ).length + 1) ^ e) := by
  obtain ⟨D, hD, hraw⟩ := exists_computableInO_stream_counter encCNF hemit fin
  obtain ⟨d₀, _, hp₀⟩ :=
    (show ComputableInPolyTime (fun φ : CNF ℕ => (φ, 0)) encCNF (encPair encCNF encNat) by
      fun_prop).exists_degree
  have hq := computableInPolyTime_pwBlockSize k
  obtain ⟨d₁, _, hp₁⟩ :=
    (show ComputableInPolyTime (fun φ => mult * pwBlockSize k φ) encCNF encUnary by
      fun_prop).exists_degree
  have hcomp := hraw.comp (hp₀.inO.prod (ComputableInO.unary_two_pow.comp hp₁.inO))
  let Bb (φ : CNF ℕ) : ℕ := (mult + 6) * ((encCNF φ).length + 1)
  have hBb (φ : CNF ℕ) :
      2 * (encCNF φ).length + 1 + (encNat (2 ^ (mult * pwBlockSize k φ))).length ≤ Bb φ := by
    rw [length_encNat_two_pow]
    have hle := pwBlockSize_le_encCNF k φ
    have := Nat.mul_le_mul_left mult hle
    dsimp only [Bb]
    nlinarith
  have hP : PolyBounded (fun φ : CNF ℕ => (encCNF φ).length)
      fun φ => 2 * ((Bb φ + 1) ^ D + (mult + 2) * ((encCNF φ).length + 1)) := by
    dsimp only [Bb]; growth_poly
  have hQ : PolyBounded (fun φ : CNF ℕ => (encCNF φ).length)
      fun φ => 2 * (((encCNF φ).length + 1) ^ d₀ + ((encCNF φ).length + 1) ^ d₁) := by
    growth_poly
  let μ (φ : CNF ℕ) : ℕ := mult * pwBlockSize k φ
  obtain ⟨c, e, hT⟩ := exists_le_mul_two_pow_of_polyBounded (size := fun φ => (encCNF φ).length)
    (μ := μ)
    (T := fun φ => 2 * (((encCNF φ).length + 1) ^ d₀ + ((encCNF φ).length + 1) ^ d₁ +
      (μ φ + 2) * 2 ^ μ φ +
      (2 ^ μ φ + 1) * (2 * (encCNF φ).length + 1 + (encNat (2 ^ μ φ)).length + 1) ^ D))
    hP hQ fun φ => by
      have h1 := Nat.mul_le_mul_left (2 ^ μ φ + 1)
        (Nat.pow_le_pow_left (Nat.add_le_add_right (hBb φ) 1) D)
      have h2 : μ φ ≤ mult * ((encCNF φ).length + 1) :=
        Nat.mul_le_mul_left mult (pwBlockSize_le_encCNF k φ)
      have h3 : (μ φ + 2) * 2 ^ μ φ ≤ (2 ^ μ φ + 1) * ((mult + 2) * ((encCNF φ).length + 1)) := by
        nlinarith [Nat.one_le_two_pow (n := μ φ)]
      nlinarith
  refine ⟨e, (hcomp.mono c (fun φ => ?_) (fun φ => ?_)).of_enc_eq fun φ => ?_⟩
  · have hTφ := hT φ
    have hce : c * (2 ^ μ φ * ((encCNF φ).length + 1) ^ e + 1) =
      c * 2 ^ μ φ * ((encCNF φ).length + 1) ^ e + c := by ring
    have hle : (μ φ + 1) * 2 ^ μ φ ≤ (μ φ + 2) * 2 ^ μ φ :=
      Nat.mul_le_mul_right _ (by omega)
    simp only [Function.comp_apply, Nat.zero_add, μ] at hTφ hce hle ⊢; omega
  · have hTφ := hT φ
    have hce : c * (2 ^ μ φ * ((encCNF φ).length + 1) ^ e + 1) =
      c * 2 ^ μ φ * ((encCNF φ).length + 1) ^ e + c := by ring
    have hle : 2 ^ μ φ ≤ (μ φ + 2) * 2 ^ μ φ := Nat.le_mul_of_pos_left _ (by omega)
    simp only [Function.comp_apply, Nat.zero_add, μ] at hTφ hce hle ⊢; omega
  · simp [Function.comp_apply]

/-- The Pătrașcu–Williams graph `pwGraph k φ` is computable within time and space
$O(2^{2 \lceil n / k \rceil} (|\mathrm{enc}(\varphi)| + 1)^e)$ for every fixed `k`. -/
theorem exists_computableInO_pwGraph (k : ℕ) :
    ∃ e : ℕ, ComputableInO (pwGraph k) encCNF encGraph
      (fun φ => 2 ^ (2 * pwBlockSize k φ) * ((encCNF φ).length + 1) ^ e)
      (fun φ => 2 ^ (2 * pwBlockSize k φ) * ((encCNF φ).length + 1) ^ e) := by
  let encE := encPair encNat encNat
  -- Part 1: static guard and clause vertices (polynomial time)
  have hstatic_pt : ComputableInPolyTime
      (fun φ : CNF ℕ => escapeBits (encList encNat (pwStaticVerts k φ))) encCNF encBits := by
    have hg : ComputableInPolyTime
        (fun _ : CNF ℕ => (List.range k).flatMap fun r => [pwGuardV r 0, pwGuardV r 1])
        encCNF (encList encNat) := ComputableInPolyTime.const _
    have hlen : ComputableInPolyTime (fun φ : CNF ℕ => φ.length) encCNF encUnary :=
      ComputableInPolyTime.length_list (encList (encPair encNat encBool))
    have hrange := computableInPolyTime_unaryRange.comp hlen
    have hcl : ComputableInPolyTime
        (fun φ : CNF ℕ => (List.range φ.length).map pwClauseV) encCNF (encList encNat) := by
      unfold pwClauseV
      have hfn : ComputableInPolyTime (fun p : CNF ℕ × ℕ => 4 * p.2 + 1)
          (encPair encCNF encNat) encNat := by fun_prop
      exact ComputableInPolyTime.mapWithInput hrange hfn
    have hv : ComputableInPolyTime (pwStaticVerts k) encCNF (encList encNat) := by
      unfold pwStaticVerts; fun_prop
    have hvBits : ComputableInPolyTime (fun φ => encList encNat (pwStaticVerts k φ))
        encCNF encBits := (ComputableInPolyTime.of_eq fun _ => rfl).comp hv
    exact computableInPolyTime_escapeBits.comp hvBits
  obtain ⟨e₀, _, hstatic_deg⟩ := hstatic_pt.exists_degree
  -- Part 2: streamed assignment vertices
  have hassign_pt : ComputableInPolyTime
      (fun s : CNF ℕ × ℕ => escapeBits (encList encNat (pwAssignVertsStep k s.1 s.2)))
      (encPair encCNF encNat) encBits := by
    have hstep : ComputableInPolyTime
        (fun s : CNF ℕ × ℕ => pwAssignVertsStep k s.1 s.2)
        (encPair encCNF encNat) (encList encNat) := by
      have heq : (fun s : CNF ℕ × ℕ => pwAssignVertsStep k s.1 s.2) = fun s =>
          ((List.range k).filter fun r => decide (s.2 < 2 ^ (pwBlock k s.1 r).length)).flatMap
            fun r => [pwAssignV k r s.2] := by
        funext s
        simp only [pwAssignVertsStep]
        generalize ((List.range k).filter fun r =>
          decide (s.2 < 2 ^ (pwBlock k s.1 r).length)) = L
        induction L <;> simp [*]
      rw [heq]
      refine computableInPolyTime_listRangeFilterMap (encPair encCNF encNat) encNat k _ _
        (fun r _ => ?_) (fun r _ => ?_)
      · have hbr := (computableInPolyTime_pwBlock k r).comp (ComputableInPolyTime.fst encCNF encNat)
        have hlen := (ComputableInPolyTime.length_list encNat).comp hbr
        have hpow := ComputableInPolyTime.binary_two_pow.comp hlen
        exact ComputableInPolyTime.binary_lt' (ComputableInPolyTime.snd encCNF encNat) hpow
      · unfold pwAssignV; fun_prop
    exact computableInPolyTime_escapeBits.comp
      ((ComputableInPolyTime.of_eq fun _ => rfl).comp hstep)
  obtain ⟨e₁, h₁⟩ := exists_computableInO_cnf_stream k 1 le_rfl hassign_pt [false]
  -- Part 3: streamed guard and clause edges
  have hgc_pt : ComputableInPolyTime
      (fun s : CNF ℕ × ℕ => encList encE (pwGuardClauseEdgesStep k s.1 s.2))
      (encPair encCNF encNat) encBits := by
    have hstep : ComputableInPolyTime
        (fun s : CNF ℕ × ℕ => pwGuardClauseEdgesStep k s.1 s.2)
        (encPair encCNF encNat) (encList encE) := by
      refine computableInPolyTime_listRangeFilterMap (encPair encCNF encNat) encE k _ _
        (fun r _ => ?_) (fun r _ => ?_)
      · have hbr := (computableInPolyTime_pwBlock k r).comp (ComputableInPolyTime.fst encCNF encNat)
        have hlen := (ComputableInPolyTime.length_list encNat).comp hbr
        have hpow := ComputableInPolyTime.binary_two_pow.comp hlen
        exact ComputableInPolyTime.binary_lt' (ComputableInPolyTime.snd encCNF encNat) hpow
      · have hguards : ComputableInPolyTime
            (fun s : CNF ℕ × ℕ => [(pwAssignV k r s.2, pwGuardV r 0),
              (pwAssignV k r s.2, pwGuardV r 1)])
            (encPair encCNF encNat) (encList encE) := by
          unfold pwAssignV pwGuardV encE; fun_prop
        have hlen : ComputableInPolyTime (fun s : CNF ℕ × ℕ => s.1.length)
            (encPair encCNF encNat) encUnary :=
          (ComputableInPolyTime.length_list _).comp (ComputableInPolyTime.fst _ _)
        have hrange := computableInPolyTime_unaryRange.comp hlen
        let encC := encList (encPair encNat encBool)
        have hpred : ComputableInPolyTime
            (fun p : (CNF ℕ × ℕ) × ℕ =>
              pwSatisfiesOn (pwBlock k p.1.1 r) p.1.2 (p.1.1.getD p.2 []))
            (encPair (encPair encCNF encNat) encNat) encBool := by
          have hφ : ComputableInPolyTime (fun p : (CNF ℕ × ℕ) × ℕ => p.1.1)
              (encPair (encPair encCNF encNat) encNat) encCNF := by fun_prop
          have hvs := (computableInPolyTime_pwBlock k r).comp hφ
          have ha : ComputableInPolyTime (fun p : (CNF ℕ × ℕ) × ℕ => p.1.2)
              (encPair (encPair encCNF encNat) encNat) encNat := by fun_prop
          have hj_cap : ComputableInPolyTime
              (fun p : (CNF ℕ × ℕ) × ℕ => min p.1.1.length p.2)
              (encPair (encPair encCNF encNat) encNat) encUnary :=
            ComputableInPolyTime.binary_min_unary'
              ((ComputableInPolyTime.length_list encC).comp hφ)
              (ComputableInPolyTime.snd _ _)
          have hget : ComputableInPolyTime
              (fun p : (CNF ℕ × ℕ) × ℕ => p.1.1.getD p.2 [])
              (encPair (encPair encCNF encNat) encNat) encC := by
            refine ((computableInPolyTime_getD_list encC []).comp (hφ.prod hj_cap)).of_enc_eq
              fun p => congrArg _ ?_
            dsimp only [Function.comp_apply]
            rcases lt_or_ge p.2 p.1.1.length with hlt | hge
            · rw [min_eq_right hlt.le]
            · rw [min_eq_left hge, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
                List.getElem?_eq_none le_rfl, List.getElem?_eq_none hge]
          exact computableInPolyTime_pwSatisfiesOn _ hvs ha hget
        have hfilt := ComputableInPolyTime.filterWithInput
          (encIn := encPair encCNF encNat) (encA := encNat)
          (list := fun s => List.range s.1.length)
          (test := fun s j => pwSatisfiesOn (pwBlock k s.1 r) s.2 (s.1.getD j [])) hrange hpred
        have hpair : ComputableInPolyTime
            (fun p : (CNF ℕ × ℕ) × ℕ => (pwAssignV k r p.1.2, pwClauseV p.2))
            (encPair (encPair encCNF encNat) encNat) encE := by
          unfold pwAssignV pwClauseV encE; fun_prop
        have hclEdges := ComputableInPolyTime.mapWithInput
          (f := fun s j => (pwAssignV k r s.2, pwClauseV j)) hfilt hpair
        exact (ComputableInPolyTime.listAppend encE).comp (hguards.prod hclEdges)
    exact (ComputableInPolyTime.of_eq fun _ => rfl).comp hstep
  obtain ⟨e₂, h₂⟩ := exists_computableInO_cnf_stream k 1 le_rfl hgc_pt []
  -- Part 4: streamed clique edges (2 ^ (2 * q) rounds)
  have hclq_pt : ComputableInPolyTime
      (fun s : CNF ℕ × ℕ =>
        encList encE (pwCliqueEdgesStep k s.1 (2 ^ pwBlockSize k s.1) s.2))
      (encPair encCNF encNat) encBits := by
    have hQ : ComputableInPolyTime (fun s : CNF ℕ × ℕ => 2 ^ pwBlockSize k s.1)
        (encPair encCNF encNat) encNat :=
      ComputableInPolyTime.binary_two_pow.comp
        ((computableInPolyTime_pwBlockSize k).comp (ComputableInPolyTime.fst _ _))
    have hdm := ComputableInPolyTime.binary_divMod.comp
      ((ComputableInPolyTime.snd _ _).prod hQ)
    have ha₁ := hdm.fst'
    have ha₂ := hdm.snd'
    have hlt := ComputableInPolyTime.binary_lt' ha₁ ha₂
    have hbody : ComputableInPolyTime
        (fun s : CNF ℕ × ℕ =>
          ((List.range k).filter fun r =>
            decide (s.2 % 2 ^ pwBlockSize k s.1 < 2 ^ (pwBlock k s.1 r).length)).flatMap
              fun r => [(pwAssignV k r (s.2 / 2 ^ pwBlockSize k s.1),
                pwAssignV k r (s.2 % 2 ^ pwBlockSize k s.1))])
        (encPair encCNF encNat) (encList encE) := by
      refine computableInPolyTime_listRangeFilterMap (encPair encCNF encNat) encE k _ _
        (fun r _ => ?_) (fun r _ => ?_)
      · have hbr := (computableInPolyTime_pwBlock k r).comp (ComputableInPolyTime.fst encCNF encNat)
        have hpow := ComputableInPolyTime.binary_two_pow.comp
          ((ComputableInPolyTime.length_list encNat).comp hbr)
        exact ComputableInPolyTime.binary_lt' ha₂ hpow
      · unfold pwAssignV encE
        have hp1 : ComputableInPolyTime
            (fun s : CNF ℕ × ℕ => 4 * ((s.2 / 2 ^ pwBlockSize k s.1) * k + r) + 2)
            (encPair encCNF encNat) encNat := by fun_prop
        have hp2 : ComputableInPolyTime
            (fun s : CNF ℕ × ℕ => 4 * ((s.2 % 2 ^ pwBlockSize k s.1) * k + r) + 2)
            (encPair encCNF encNat) encNat := by fun_prop
        fun_prop
    have hstep : ComputableInPolyTime
        (fun s : CNF ℕ × ℕ => pwCliqueEdgesStep k s.1 (2 ^ pwBlockSize k s.1) s.2)
        (encPair encCNF encNat) (encList encE) := by
      refine (hlt.ite hbody (ComputableInPolyTime.const [])).of_enc_eq fun s => congrArg _ ?_
      dsimp only [pwCliqueEdgesStep, Function.comp_apply]
      by_cases h : s.2 / 2 ^ pwBlockSize k s.1 < s.2 % 2 ^ pwBlockSize k s.1
      · simp only [h, decide_true, ↓reduceIte]
        generalize ((List.range k).filter fun r =>
          decide (s.2 % 2 ^ pwBlockSize k s.1 < 2 ^ (pwBlock k s.1 r).length)) = L
        induction L <;> simp [*]
      · simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte]
    exact (ComputableInPolyTime.of_eq fun _ => rfl).comp hstep
  obtain ⟨e₃, h₃⟩ := exists_computableInO_cnf_stream k 2 (by omega) hclq_pt []
  -- Concatenate all four parts into `encGraph (pwGraph k φ)`
  have h01 := hstatic_deg.inO.append h₁
    (g := fun φ => frame (encList encNat (pwGraph k φ).vertices)) (encOut := encBits) fun φ => by
      simp only [pwGraph, encList_append_eq, encList_flatMap_eq, frame_eq_escapeBits,
        escapeBits_append, escapeBits_flatten, List.map_map, Function.comp_def, encBits_apply,
        List.append_assoc, one_mul]
  have h23 := h₂.append h₃
    (g := fun φ => encList encE (pwGraph k φ).edges) (encOut := encBits) fun φ => by
      simp only [pwGraph, encList_append_eq, encList_flatMap_eq, encBits_apply, List.append_nil,
        one_mul]
  have hall := h01.append h23 (g := pwGraph k) (encOut := encGraph) fun φ => by
    simp only [encGraph_apply, encPair_apply, encBits_apply, encE]
  let E := e₀ + e₁ + e₂ + e₃
  refine ⟨E, hall.mono 4 (fun φ => ?_) (fun φ => ?_)⟩
  all_goals
    simp only [one_mul]
    have hpow : 2 ^ pwBlockSize k φ ≤ 2 ^ (2 * pwBlockSize k φ) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have h1pow : 1 ≤ 2 ^ (2 * pwBlockSize k φ) := Nat.one_le_two_pow
    have hLp (a : ℕ) (ha : a ≤ E) : ((encCNF φ).length + 1) ^ a ≤ ((encCNF φ).length + 1) ^ E :=
      Nat.pow_le_pow_right (Nat.succ_pos _) ha
    nlinarith [Nat.mul_le_mul h1pow (hLp e₀ (by omega)), Nat.mul_le_mul hpow (hLp e₁ (by omega)),
      Nat.mul_le_mul hpow (hLp e₂ (by omega)),
      Nat.mul_le_mul_left (2 ^ (2 * pwBlockSize k φ)) (hLp e₃ (by omega))]

/-! ### Pătrașcu–Williams transfer theorem and SETH lower bound for `k`-Dominating Set -/

private lemma pwDenseCheck_polyTime (k : ℕ) :
    ComputableInPolyTime (fun φ : CNF ℕ => decide (pwBlockSize k φ < φ.length.size))
      encCNF encBool := by
  have hq := computableInPolyTime_pwBlockSize k
  have hm_bin := ComputableInPolyTime.unary_to_binary.comp
    (ComputableInPolyTime.length_list (encList (encPair encNat encBool)))
  have hsz := ComputableInPolyTime.binary_size.comp hm_bin
  exact ComputableInPolyTime.unary_lt' hq hsz

private lemma pw_sparse_enc_and_total {k e cRed eRed cDom C_v C_tot dChk E_tot L q gl td : ℕ}
    {X vp : ℝ} (hL1 : (1 : ℝ) ≤ (L : ℝ) + 1) (hX1 : (1 : ℝ) ≤ X)
    (hchk : (((L + 1) ^ dChk : ℕ) : ℝ) ≤ X * ((L : ℝ) + 1) ^ E_tot)
    (hred : ((2 ^ (2 * q) * (L + 1) ^ eRed : ℕ) : ℝ) ≤
      ((2 ^ (2 * k) : ℕ) : ℝ) * (X * ((L : ℝ) + 1) ^ E_tot))
    (h2qe : ((2 ^ (2 * e * q) : ℕ) : ℝ) ≤ ((2 ^ (2 * k) : ℕ) : ℝ) * X)
    (heE : e * eRed ≤ E_tot) (hl : gl ≤ cRed * (2 ^ (2 * q) * (L + 1) ^ eRed + 1))
    (hvp : vp ≤ (C_v : ℝ) * X)
    (htd : (td : ℝ) ≤ cDom * (vp + ((gl : ℝ) + 1) ^ e) + cDom)
    (hC : 1 + 2 ^ (2 * k) + (cDom + 1) * (C_v + (2 * cRed + 2) ^ e * 2 ^ (2 * k) + 2) ≤ C_tot) :
    (((L + 1) ^ dChk + (2 ^ (2 * q) * (L + 1) ^ eRed + td) : ℕ) : ℝ) ≤
      (C_tot : ℝ) * (X * ((L : ℝ) + 1) ^ E_tot) := by
  let C_enc : ℕ := (2 * cRed + 2) ^ e * 2 ^ (2 * k)
  let Z : ℝ := X * ((L : ℝ) + 1) ^ E_tot
  have hLE1 : (1 : ℝ) ≤ ((L : ℝ) + 1) ^ E_tot := one_le_pow₀ hL1
  have hZ1 : (1 : ℝ) ≤ Z := one_le_mul_of_one_le_of_one_le hX1 hLE1
  have hlen : gl + 1 ≤ (2 * cRed + 2) * 2 ^ (2 * q) * (L + 1) ^ eRed := by
    have : 1 ≤ 2 ^ (2 * q) * (L + 1) ^ eRed :=
      Nat.mul_pos (Nat.two_pow_pos _) (Nat.pow_pos (Nat.succ_pos L))
    nlinarith [show (2 * cRed + 2) * 2 ^ (2 * q) * (L + 1) ^ eRed =
      (2 * cRed + 2) * (2 ^ (2 * q) * (L + 1) ^ eRed) by ring]
  have hpow : (gl + 1) ^ e ≤ (2 * cRed + 2) ^ e * 2 ^ (2 * e * q) * (L + 1) ^ (e * eRed) :=
    (Nat.pow_le_pow_left hlen e).trans <| le_of_eq <| by
      rw [Nat.mul_pow, Nat.mul_pow, ← Nat.pow_mul, ← Nat.pow_mul,
        show 2 * q * e = 2 * e * q by ring, Nat.mul_comm eRed e]
  have hpowr : ((gl : ℝ) + 1) ^ e ≤
      (((2 * cRed + 2) ^ e : ℕ) : ℝ) * ((2 ^ (2 * e * q) : ℕ) : ℝ) * ((L : ℝ) + 1) ^ (e * eRed) :=
    by exact_mod_cast hpow
  have henc : ((gl : ℝ) + 1) ^ e ≤ (C_enc : ℝ) * Z :=
    hpowr.trans <|
      (mul_le_mul (mul_le_mul_of_nonneg_left h2qe (by positivity))
        (pow_le_pow_right₀ hL1 heE) (by positivity) (by positivity)).trans <|
        le_of_eq (by simp only [C_enc, Z, Nat.cast_mul]; ring)
  have hvf : vp ≤ (C_v : ℝ) * Z := by
    calc vp ≤ (C_v : ℝ) * X * 1 := by linarith
      _ ≤ (C_v : ℝ) * X * ((L : ℝ) + 1) ^ E_tot :=
          mul_le_mul_of_nonneg_left hLE1 (by positivity)
      _ = (C_v : ℝ) * Z := by simp [Z, mul_assoc]
  have hc0 : (0 : ℝ) ≤ cDom := Nat.cast_nonneg _
  have hdom : (td : ℝ) ≤ ((cDom + 1) * (C_v + C_enc + 2) : ℝ) * Z := by
    nlinarith [mul_le_mul_of_nonneg_left (add_le_add hvf henc) hc0,
      mul_le_mul_of_nonneg_left hZ1 hc0]
  have hCr : (1 : ℝ) + ((2 ^ (2 * k) : ℕ) : ℝ) + (cDom + 1) * (C_v + C_enc + 2) ≤ C_tot := by
    exact_mod_cast hC
  have hZ0 : 0 ≤ Z := by linarith
  have hsum : (((L + 1) ^ dChk : ℕ) : ℝ) +
      (((2 ^ (2 * q) * (L + 1) ^ eRed : ℕ) : ℝ) + (td : ℝ)) ≤ (C_tot : ℝ) * Z := by
    linarith [hchk, hred, hdom, mul_le_mul_of_nonneg_right hCr hZ0]
  simpa only [Nat.cast_add] using hsum

private lemma decidableInExpTime_SAT_of_pwGraph_target {A : Set Graph} {k e : ℕ}
    (hk : 3 ≤ k) (he : 2 * e < k) {ε : ℝ} (hε : 0 < ε)
    (hA : ∀ φ : CNF ℕ, pwGraph k φ ∈ A ↔ φ ∈ SAT)
    (h : DecidableInTimeO A encGraph
      fun G => (G.vertices.length : ℝ) ^ (k - ε) + (((encGraph G).length : ℝ) + 1) ^ e) :
    DecidableInExpTime SAT encCNF CNF.numVars
      (1 - min (((k - 2 * max e 1 : ℕ) : ℝ) / k) (min ε 1 / k)) := by
  obtain ⟨gDom, tDom, cDom, hgDom, hDomIff, htDom⟩ := h.exists_computableInO
  obtain ⟨eRed, hRed⟩ := exists_computableInO_pwGraph k
  obtain ⟨cRed, hRedTS, hRedLen⟩ := hRed
  have hRed' : ComputableInO (pwGraph k) encCNF encGraph
      (fun φ => 2 ^ (2 * pwBlockSize k φ) * ((encCNF φ).length + 1) ^ eRed)
      (fun φ => 2 ^ (2 * pwBlockSize k φ) * ((encCNF φ).length + 1) ^ eRed) :=
    ⟨cRed, hRedTS, hRedLen⟩
  obtain ⟨eBF, hBF⟩ := SAT_decidableInExpTime_one
  obtain ⟨gBF, tBF, cBF, hgBF, hBFIff, htBF⟩ := hBF.exists_computableInO
  obtain ⟨dChk, _, hChk⟩ := (pwDenseCheck_polyTime k).exists_degree
  have hsparse := hgDom.comp hRed'
  have hall := hChk.inO.ite hgBF hsparse
  have hcorr (φ : CNF ℕ) :
      φ ∈ SAT ↔ (if decide (pwBlockSize k φ < φ.length.size) then gBF φ
        else gDom (pwGraph k φ)) = true := by
    split_ifs
    · exact hBFIff φ
    · rw [← hA φ]; exact hDomIff _
  let ε₀ : ℝ := min ε 1
  let m : ℕ := max e 1
  have hm_lt : 2 * m < k := by simp only [m]; omega
  let δ : ℝ := min (((k - 2 * m : ℕ) : ℝ) / k) (ε₀ / k)
  have hk_pos : (0 : ℝ) < k := by positivity
  have hε₀_pos : 0 < ε₀ := lt_min hε zero_lt_one
  have hε₀_le : ε₀ ≤ 1 := min_le_right ε 1
  have hδ_pos : 0 < δ := by
    refine lt_min (div_pos ?_ hk_pos) (div_pos hε₀_pos hk_pos)
    exact_mod_cast (show 0 < k - 2 * m by omega)
  have hδ_le1 : δ ≤ 1 := (min_le_right _ _).trans
    (div_le_one_of_le₀ (hε₀_le.trans (by exact_mod_cast (show 1 ≤ k by omega))) hk_pos.le)
  let C_v : ℕ := ((4 * k + 2) ^ k) * (2 ^ (2 * k))
  let C_enc : ℕ := (2 * cRed + 2) ^ e * (2 ^ (2 * k))
  let C_tot : ℕ := 4 + 2 * cBF + 2 ^ (2 * k) + (cDom + 1) * (C_v + C_enc + 2)
  have hCv_def : C_v = ((4 * k + 2) ^ k) * (2 ^ (2 * k)) := rfl
  have hCenc_def : C_enc = (2 * cRed + 2) ^ e * (2 ^ (2 * k)) := rfl
  have hCtot_def : C_tot = 4 + 2 * cBF + 2 ^ (2 * k) + (cDom + 1) * (C_v + C_enc + 2) := rfl
  clear_value C_tot C_v C_enc
  let E_tot : ℕ := dChk + k + eBF + (e + 1) * eRed + 1
  have hEtot_def : E_tot = dChk + k + eBF + (e + 1) * eRed + 1 := rfl
  clear_value E_tot
  refine DecidableInExpTime.of_computableInO hall hcorr C_tot E_tot fun φ => ?_
  set L : ℕ := (encCNF φ).length
  set q : ℕ := pwBlockSize k φ
  set n : ℕ := φ.numVars
  set X : ℝ := (2 : ℝ) ^ ((1 - δ) * n)
  have hL1 : (1 : ℝ) ≤ (L : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) L]
  have hX1 : (1 : ℝ) ≤ X := Real.one_le_rpow (by norm_num)
    (mul_nonneg (by linarith) (Nat.cast_nonneg n))
  have hpowL (a : ℕ) (ha : a ≤ E_tot) : ((L : ℝ) + 1) ^ a ≤ ((L : ℝ) + 1) ^ E_tot :=
    pow_le_pow_right₀ hL1 ha
  have hchk_le : (((L + 1) ^ dChk : ℕ) : ℝ) ≤ X * ((L : ℝ) + 1) ^ E_tot := by
    calc (((L + 1) ^ dChk : ℕ) : ℝ) = 1 * ((L : ℝ) + 1) ^ dChk := by push_cast; ring
      _ ≤ X * ((L : ℝ) + 1) ^ E_tot :=
          mul_le_mul hX1 (hpowL dChk (by rw [hEtot_def]; omega)) (by positivity) (by positivity)
  have hXY_pos : (0 : ℝ) ≤ X * ((L : ℝ) + 1) ^ E_tot := by positivity
  have hL_tot_1 : (1 : ℝ) ≤ ((L : ℝ) + 1) ^ E_tot := one_le_pow₀ hL1
  have hY : (1 : ℝ) ≤ X * ((L : ℝ) + 1) ^ E_tot := one_le_mul_of_one_le_of_one_le hX1 hL_tot_1
  split_ifs with hdense
  · have hlt_sz : q < φ.length.size := of_decide_eq_true hdense
    have h2q : 2 ^ q ≤ φ.length := by
      by_contra hnot
      exact absurd (Nat.size_le.mpr (lt_of_not_ge hnot)) (not_le.mpr hlt_sz)
    have hnk : n ≤ k * q := by
      have hd : k * q + (n + k - 1) % k = n + k - 1 := Nat.div_add_mod (n + k - 1) k
      have := Nat.mod_lt (n + k - 1) (show 0 < k by omega)
      omega
    have hmL : φ.length ≤ L := length_le_length_encList (encList (encPair encNat encBool)) φ
    have h2n : (2 : ℝ) ^ (1 * (n : ℝ)) ≤ ((L : ℝ) + 1) ^ k := by
      rw [one_mul, Real.rpow_natCast]
      exact_mod_cast calc 2 ^ n ≤ 2 ^ (k * q) := Nat.pow_le_pow_right (by norm_num) hnk
        _ = (2 ^ q) ^ k := by rw [Nat.mul_comm, Nat.pow_mul]
        _ ≤ (L + 1) ^ k := Nat.pow_le_pow_left (h2q.trans (hmL.trans (Nat.le_succ L))) k
    have hbf_le : (tBF φ : ℝ) ≤ (2 * cBF : ℝ) * (X * ((L : ℝ) + 1) ^ E_tot) := by
      have hmul : (2 : ℝ) ^ (1 * (n : ℝ)) * ((L : ℝ) + 1) ^ eBF ≤ X * ((L : ℝ) + 1) ^ E_tot :=
        calc (2 : ℝ) ^ (1 * (n : ℝ)) * ((L : ℝ) + 1) ^ eBF
            ≤ ((L : ℝ) + 1) ^ k * ((L : ℝ) + 1) ^ eBF :=
              mul_le_mul_of_nonneg_right h2n (by positivity)
          _ = 1 * ((L : ℝ) + 1) ^ (k + eBF) := by rw [← pow_add, one_mul]
          _ ≤ X * ((L : ℝ) + 1) ^ E_tot :=
              mul_le_mul hX1 (hpowL (k +
                eBF) (by rw [hEtot_def]; omega)) (by positivity) (by positivity)
      have hc0 : (0 : ℝ) ≤ cBF := Nat.cast_nonneg _
      nlinarith [htBF φ, mul_le_mul_of_nonneg_left hmul hc0, mul_le_mul_of_nonneg_left hY hc0]
    have hC : (1 : ℝ) + 2 * cBF ≤ C_tot := by
      rw [hCtot_def]; exact_mod_cast (show 1 + 2 * cBF ≤ 4 + 2 * cBF by omega).trans
        ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _))
    have hgoal : (((L + 1) ^ dChk : ℕ) : ℝ) + (tBF φ : ℝ) ≤
        (C_tot : ℝ) * (X * ((L : ℝ) + 1) ^ E_tot) := by
      nlinarith [mul_le_mul_of_nonneg_right hC hXY_pos]
    exact (Nat.cast_add ((L + 1) ^ dChk) (tBF φ)).trans_le hgoal
  · have hmlt : φ.length < 2 ^ q := Nat.size_le.mp (le_of_not_gt (by simpa using hdense))
    have hq_real : (q : ℝ) ≤ (n : ℝ) / k + 1 := by
      have hqk : (q : ℝ) * k ≤ n + k := by
        exact_mod_cast (Nat.div_mul_le_self (n + k - 1) k).trans (by omega)
      rw [div_add_one hk_pos.ne']
      exact (le_div_iff₀ hk_pos).mpr hqk
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have h2m_exp : (2 * m : ℝ) * q ≤ (1 - δ) * n + 2 * k := by
      have hδ1 : δ ≤ ((k : ℝ) - 2 * m) / k := by
        have hmin : δ ≤ ((k - 2 * m : ℕ) : ℝ) / k := min_le_left _ _
        have hsub : ((k - 2 * m : ℕ) : ℝ) = (k : ℝ) - 2 * m := by
          rw [Nat.cast_sub hm_lt.le]; push_cast; rfl
        rwa [hsub] at hmin
      have hcoef : (2 * m : ℝ) / k ≤ 1 - δ := by
        have : 1 - ((k : ℝ) - 2 * m) / k = (2 * m : ℝ) / k := by field_simp; ring
        linarith
      have hmk : (m : ℝ) ≤ k := by exact_mod_cast (show m ≤ k by omega)
      calc (2 * m : ℝ) * q ≤ (2 * m : ℝ) * ((n : ℝ) / k + 1) :=
            mul_le_mul_of_nonneg_left hq_real (by positivity)
        _ = ((2 * m : ℝ) / k) * n + 2 * m := by ring
        _ ≤ (1 - δ) * n + 2 * k := by linarith [mul_le_mul_of_nonneg_right hcoef hn0]
    have h2q_bound (r : ℕ) (hr : r ≤ m) :
        ((2 ^ (2 * r * q) : ℕ) : ℝ) ≤ ((2 ^ (2 * k) : ℕ) : ℝ) * X := by
      have hr' : (2 * r : ℝ) * q ≤ (2 * m : ℝ) * q := by
        have : (r : ℝ) ≤ m := by exact_mod_cast hr
        nlinarith [Nat.cast_nonneg (α := ℝ) q]
      calc ((2 ^ (2 * r * q) : ℕ) : ℝ) = (2 : ℝ) ^ ((2 * r : ℝ) * q) := by
            rw [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast]; congr 1; push_cast; ring
        _ ≤ (2 : ℝ) ^ ((1 - δ) * n + 2 * k) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (hr'.trans h2m_exp)
        _ = ((2 ^ (2 * k) : ℕ) : ℝ) * X := by
            rw [Real.rpow_add (by norm_num), mul_comm]; congr 1
            rw [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast, Nat.cast_mul, Nat.cast_ofNat]
    have hred_time : ((2 ^ (2 * q) * (L + 1) ^ eRed : ℕ) : ℝ) ≤
        ((2 ^ (2 * k) : ℕ) : ℝ) * (X * ((L : ℝ) + 1) ^ E_tot) := by
      have h1 := h2q_bound 1 (le_max_right e 1)
      rw [show 2 * 1 * q = 2 * q by ring, Nat.cast_pow, Nat.cast_ofNat] at h1
      have h2 := hpowL eRed (by rw [hEtot_def]; nlinarith)
      push_cast
      exact (mul_le_mul h1 h2 (by positivity) (by positivity)).trans
        (le_of_eq (by push_cast; ring))
    have hv_le : (pwGraph k φ).vertices.length ≤ (4 * k + 2) * 2 ^ q := by
      nlinarith [length_pwGraph_vertices_le k φ, Nat.one_le_two_pow (n := q)]
    have hv_pos : (1 : ℝ) ≤ (pwGraph k φ).vertices.length := by
      exact_mod_cast (show 1 ≤ (pwGraph k φ).vertices.length by
        have := three_mul_le_pwGraph_vertices k φ; omega)
    have hv_pow : ((pwGraph k φ).vertices.length : ℝ) ^ ((k : ℝ) - ε) ≤ (C_v : ℝ) * X := by
      have hke_pos : 0 ≤ (k : ℝ) - ε₀ := by
        have : (3 : ℝ) ≤ k := by exact_mod_cast hk
        linarith
      have hexp : ((k : ℝ) - ε₀) * q ≤ (1 - δ) * n + 2 * k := by
        have hcoef : ((k : ℝ) - ε₀) / k ≤ 1 - δ := by
          have : ((k : ℝ) - ε₀) / k = 1 - ε₀ / k := by field_simp
          linarith [min_le_right (((k - 2 * m : ℕ) : ℝ) / k) (ε₀ / k)]
        calc ((k : ℝ) - ε₀) * q ≤ ((k : ℝ) - ε₀) * ((n : ℝ) / k + 1) :=
              mul_le_mul_of_nonneg_left hq_real hke_pos
          _ = (((k : ℝ) - ε₀) / k) * n + ((k : ℝ) - ε₀) := by ring
          _ ≤ (1 - δ) * n + 2 * k := by linarith [mul_le_mul_of_nonneg_right hcoef hn0]
      calc ((pwGraph k φ).vertices.length : ℝ) ^ ((k : ℝ) - ε)
          ≤ ((pwGraph k φ).vertices.length : ℝ) ^ ((k : ℝ) - ε₀) :=
            Real.rpow_le_rpow_of_exponent_le hv_pos (by linarith [min_le_left ε 1])
        _ ≤ (((4 * k + 2) * 2 ^ q : ℕ) : ℝ) ^ ((k : ℝ) - ε₀) :=
            Real.rpow_le_rpow (by positivity) (by exact_mod_cast hv_le) hke_pos
        _ = ((4 * k + 2 : ℕ) : ℝ) ^ ((k : ℝ) - ε₀) * (2 : ℝ) ^ (((k : ℝ) - ε₀) * q) := by
            push_cast
            rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast,
              ← Real.rpow_mul (by norm_num), mul_comm (q : ℝ)]
        _ ≤ (((4 * k + 2) ^ k : ℕ) : ℝ) * (((2 ^ (2 * k) : ℕ) : ℝ) * X) := by
            refine mul_le_mul ?_ ?_ (by positivity) (by positivity)
            · rw [Nat.cast_pow, ← Real.rpow_natCast]
              exact Real.rpow_le_rpow_of_exponent_le
                (by exact_mod_cast (show 1 ≤ 4 * k + 2 by omega)) (by linarith)
            · calc (2 : ℝ) ^ (((k : ℝ) - ε₀) * q) ≤ (2 : ℝ) ^ ((1 - δ) * n + 2 * k) :=
                    Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
                _ = ((2 ^ (2 * k) : ℕ) : ℝ) * X := by
                    rw [Real.rpow_add (by norm_num), mul_comm]; congr 1
                    rw [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast, Nat.cast_mul,
                      Nat.cast_ofNat]
        _ = (C_v : ℝ) * X := by rw [hCv_def, Nat.cast_mul]; ring
    exact pw_sparse_enc_and_total hL1 hX1 hchk_le hred_time (h2q_bound e (le_max_left e 1))
      (by rw [hEtot_def]; nlinarith) (hRedLen φ) hv_pow (htDom (pwGraph k φ))
      (by rw [hCtot_def, hCenc_def]; omega)

/-- Quantitative Pătrașcu–Williams reduction allowing an additive polynomial term
$(|\mathrm{enc}(G)| + 1)^e$ with $2e < k$: any decider for `k`-Dominating Set ($k \ge 3$) running
in time $O(|V|^{k - \varepsilon} + (|\mathrm{enc}(G)| + 1)^e)$ yields a `SAT` decider running in
time $O(2^{(1 - \delta) n} \mathrm{poly}(|\varphi|))$ with
$\delta = \min((k - 2 \max(e, 1)) / k,\; \min(\varepsilon, 1) / k) > 0$. -/
theorem decidableInExpTime_SAT_of_kDominatingSet_add_enc {k e : ℕ} (hk : 3 ≤ k) (he : 2 * e < k)
    {ε : ℝ} (hε : 0 < ε)
    (h : DecidableInTimeO (kDominatingSet k) encGraph
      fun G => (G.vertices.length : ℝ) ^ (k - ε) + (((encGraph G).length : ℝ) + 1) ^ e) :
    DecidableInExpTime SAT encCNF CNF.numVars
      (1 - min (((k - 2 * max e 1 : ℕ) : ℝ) / k) (min ε 1 / k)) :=
  decidableInExpTime_SAT_of_pwGraph_target hk he hε
    (pwGraph_mem_kDominatingSet_iff (by omega)) h

/-- **Pătrașcu–Williams reduction**: for every $k \ge 3$ and $\varepsilon > 0$, any
algorithm deciding `k`-Dominating Set in time $O(|V|^{k - \varepsilon})$ yields an exponential-time
`SAT` algorithm with exponent $1 - \min(1 / 3,\; \min(\varepsilon, 1) / k) < 1$.
-/
theorem decidableInExpTime_SAT_of_kDominatingSet {k : ℕ} (hk : 3 ≤ k) {ε : ℝ} (hε : 0 < ε)
    (h : DecidableInTimeO (kDominatingSet k) encGraph
      fun G => (G.vertices.length : ℝ) ^ (k - ε)) :
    DecidableInExpTime SAT encCNF CNF.numVars (1 - min (1 / 3) (min ε 1 / k)) := by
  have h' : DecidableInTimeO (kDominatingSet k) encGraph
      fun G => (G.vertices.length : ℝ) ^ (k - ε) + (((encGraph G).length : ℝ) + 1) ^ 0 :=
    h.mono 1 (fun _ => by simp; linarith) (fun _ => by positivity)
  refine (decidableInExpTime_SAT_of_kDominatingSet_add_enc hk (by omega) hε h').mono ?_
  have hk_pos : (0 : ℝ) < k := by positivity
  have h13 : (1 : ℝ) / 3 ≤ ((k - 2 * max 0 1 : ℕ) : ℝ) / k := by
    simp only [max_eq_right zero_le_one, Nat.mul_one]
    rw [div_le_div_iff₀ (by norm_num) hk_pos, Nat.cast_sub (by omega : 2 ≤ k)]
    have : (3 : ℝ) ≤ k := by exact_mod_cast hk
    push_cast; linarith
  linarith [min_le_min_right (min ε 1 / k) h13]

private lemma card_rpow_le_length_rpow {k : ℕ} (hk : 3 ≤ k) {ε : ℝ} (G : Graph) :
    (G.vertices.toFinset.card : ℝ) ^ ((k : ℝ) - ε) ≤
      1 * (G.vertices.length : ℝ) ^ ((k : ℝ) - min ε 1) + 1 := by
  have hke : 0 ≤ (k : ℝ) - min ε 1 := by
    have : (3 : ℝ) ≤ k := by exact_mod_cast hk
    linarith [min_le_right ε 1]
  rcases Nat.eq_zero_or_pos G.vertices.toFinset.card with h0 | hpos
  · simp only [h0, Nat.cast_zero, one_mul]
    by_cases hz : (k : ℝ) - ε = 0
    · rw [hz, Real.rpow_zero]
      linarith [Real.rpow_nonneg (Nat.cast_nonneg G.vertices.length) ((k : ℝ) - min ε 1)]
    · rw [Real.zero_rpow hz]; positivity
  · calc (G.vertices.toFinset.card : ℝ) ^ ((k : ℝ) - ε)
        ≤ (G.vertices.toFinset.card : ℝ) ^ ((k : ℝ) - min ε 1) :=
          Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hpos)
            (by linarith [min_le_left ε 1])
      _ ≤ (G.vertices.length : ℝ) ^ ((k : ℝ) - min ε 1) :=
          Real.rpow_le_rpow (by positivity)
            (by exact_mod_cast List.toFinset_card_le G.vertices) hke
      _ ≤ 1 * (G.vertices.length : ℝ) ^ ((k : ℝ) - min ε 1) + 1 := by linarith

/-- $\varepsilon > 0$, `k`-Dominating Set cannot be decided in time $O(|V|^{k - \varepsilon})$. -/
theorem not_decidableInTimeO_kDominatingSet (h : SETH) {k : ℕ} (hk : 3 ≤ k) {ε : ℝ} (hε : 0 < ε) :
    ¬ DecidableInTimeO (kDominatingSet k) encGraph
        fun G => (G.vertices.length : ℝ) ^ (k - ε) := by
  intro hdec
  have hSAT := decidableInExpTime_SAT_of_kDominatingSet hk hε hdec
  have hδ : 0 < min (1 / 3 : ℝ) (min ε 1 / k) :=
    lt_min (by norm_num) (div_pos (lt_min hε zero_lt_one) (by positivity))
  have hδ1 : min (1 / 3 : ℝ) (min ε 1 / k) ≤ 1 := (min_le_left _ _).trans (by norm_num)
  exact not_seth_of_decidableInExpTime_SAT hδ hδ1 hSAT h

/-- Assuming `SETH`, for every $k \ge 3$ and $\varepsilon > 0$, `k`-Dominating Set cannot be decided
in time $O(|V_{\mathrm{distinct}}|^{k - \varepsilon})$. -/
theorem not_decidableInTimeO_kDominatingSet_card (h : SETH) {k : ℕ} (hk : 3 ≤ k) {ε : ℝ}
    (hε : 0 < ε) :
    ¬ DecidableInTimeO (kDominatingSet k) encGraph
        fun G => (G.vertices.toFinset.card : ℝ) ^ (k - ε) := fun hdec =>
  not_decidableInTimeO_kDominatingSet h hk (lt_min hε zero_lt_one)
    (hdec.mono 1 (fun G => by simpa using card_rpow_le_length_rpow hk G) fun _ => by positivity)

/-- Assuming `SETH`, for every $k \ge 3$ and $\varepsilon > 0$, `≤ k`-Dominating Set cannot be
decided in time $O(|V_{\mathrm{distinct}}|^{k - \varepsilon})$. -/
theorem not_decidableInTimeO_kDominatingSetLe (h : SETH) {k : ℕ} (hk : 3 ≤ k) {ε : ℝ}
    (hε : 0 < ε) :
    ¬ DecidableInTimeO (kDominatingSetLe k) encGraph
        fun G => (G.vertices.toFinset.card : ℝ) ^ (k - ε) := by
  intro hdec
  have hε₀ : 0 < min ε 1 := lt_min hε zero_lt_one
  have h' : DecidableInTimeO (kDominatingSetLe k) encGraph
      fun G => (G.vertices.length : ℝ) ^ (k - min ε 1) + (((encGraph G).length : ℝ) + 1) ^ 0 :=
    hdec.mono 1 (fun G => by
      have hG := card_rpow_le_length_rpow hk (ε := ε) G
      simp only [pow_zero, Nat.cast_one, one_mul] at hG ⊢; linarith) (fun _ => by positivity)
  have hSAT := decidableInExpTime_SAT_of_pwGraph_target hk (e := 0) (by omega) hε₀
    (pwGraph_mem_kDominatingSetLe_iff (by omega)) h'
  have hk_pos : (0 : ℝ) < k := by positivity
  have hδ : 0 < min (((k - 2 * max 0 1 : ℕ) : ℝ) / k) (min (min ε 1) 1 / k) :=
    lt_min (div_pos (by exact_mod_cast (show 0 < k - 2 * max 0 1 by omega)) hk_pos)
      (div_pos (lt_min hε₀ zero_lt_one) hk_pos)
  have hδ1 : min (((k - 2 * max 0 1 : ℕ) : ℝ) / k) (min (min ε 1) 1 / k) ≤ 1 :=
    (min_le_right _ _).trans (div_le_one_of_le₀
      ((min_le_right _ _).trans (by exact_mod_cast (show 1 ≤ k by omega))) hk_pos.le)
  exact not_seth_of_decidableInExpTime_SAT hδ hδ1 hSAT h

end CslibFrontier.FineGrainedDominatingSet
