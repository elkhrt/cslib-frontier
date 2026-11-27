/-
Copyright (c) 2026 CslibFrontier contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CslibFrontier contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.NP.Nondeterministic
public import CslibFrontier.Computability.Complexity.Classes.Promise.Reduction
public import CslibFrontier.Computability.Complexity.Parameterized.Hardness
public import CslibFrontier.Computability.Complexity.Parameterized.WHierarchy
import CslibFrontier.Computability.Circuit.Boolean.Unbounded.Kleene
import CslibFrontier.Computability.Complexity.Classes.NP.Closure
import CslibFrontier.Computability.Complexity.CookLevin.Completeness
import CslibFrontier.Computability.Complexity.Problems.ChromaticNumber
import CslibFrontier.Computability.Complexity.Problems.SAT.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Tactic.EncLen

/-!
# The Class `para-NP`, Slice Hardness, and Minimization Gap Inapproximability

This module develops the parameterized complexity class `para-NP`, `para-NP`-hardness and
completeness under fixed-parameter tractable (`fpt`) reductions, Flum–Grohe's slice hardness
criterion, the resulting `XP` and `FPT` collapse equivalences with `P = NP`, and integer-gap
multiplicative inapproximability for minimization problems under standard Lean axioms.

Building directly on `Cslib.Complexity` (`P`, `NP`, `FPT`, `XP`, `FPTReducible`, `FPTHard`, and
`PromiseProblem.gapMin`), `ParaNP enc κ` consists of the parameterized problems that fpt-reduce
to a trivially parameterized problem in `NP` (equivalently, to `SAT`). Every problem decided by a
nondeterministic multi-tape Turing machine within an fpt-computable unary time bound lies in
`ParaNP`, and for any bounded parameter `ParaNP` collapses to `NP`. By Flum–Grohe's slice theorem,
if a single parameter slice (or a bounded union of slices) of a parameterized problem is `NP`-hard,
then the problem is `para-NP`-hard, and cannot belong to `XP` or `FPT` unless `P = NP`.

For minimization objectives `opt : α → ℕ`, a polynomial-time reduction from an `NP`-hard problem
mapping yes-instances to `opt ≤ a` and no-instances to `a + 1 ≤ opt` (`0 < a`) establishes
unconditional `NP`-hardness of `PromiseProblem.gapMin` at `(a, a + 1)`, ruling out both
polynomial-time `c`-approximation for every `c < (a + 1) / a` and strict polynomial-time
`((a + 1) / a)`-approximation unless `P = NP`.

## Main definitions

- `CslibFrontier.Complexity.PEqNP`: global equality `P enc = NP enc` across all encodings.
- `CslibFrontier.Complexity.paramSlice`: the `k`-th slice `{a ∈ A | κ a = k}` of a parameterized
  problem.
- `CslibFrontier.Complexity.ParaNP`: the parameterized complexity class `para-NP`.
- `CslibFrontier.Complexity.ParaNPHard`, `CslibFrontier.Complexity.ParaNPComplete`: hardness and
  completeness for `para-NP` under fpt-reductions.
- `CslibFrontier.Complexity.IsPolyTimeMinApprox`,
`CslibFrontier.Complexity.IsStrictPolyTimeMinApprox`:
  non-strict and strict polynomial-time multiplicative approximation for `ℕ`-valued minimization
  objectives.

## Main results

- `CslibFrontier.Complexity.mem_ParaNP_iff_fptReducible_SAT`: characterization via fpt-reduction to
  `SAT`.
- `CslibFrontier.Complexity.mem_ParaNP_of_ntm_decidesInTime`: nondeterministic multi-tape machines
  halting within an fpt-computable unary clock belong to `ParaNP`.
- `CslibFrontier.Complexity.NP_subset_ParaNP`, `CslibFrontier.Complexity.FPT_subset_ParaNP`,
  `CslibFrontier.Complexity.W_subset_ParaNP`, `CslibFrontier.Complexity.ParaNP_eq_NP_of_le`,
  `CslibFrontier.Complexity.mem_ParaNP_of_fptReducible`: inclusions, bounded-parameter collapse, and
  closure under fpt-reductions.
- `CslibFrontier.Complexity.ParaNPHard.of_bounded_param_reduction`,
  `CslibFrontier.Complexity.ParaNPHard.of_const_param_reduction`,
  `CslibFrontier.Complexity.ParaNPHard.of_slice_npHard`: Flum–Grohe's slice hardness theorem.
- `CslibFrontier.Complexity.ParaNPHard.pEqNP_of_mem_XP`,
  `CslibFrontier.Complexity.ParaNPHard.notMem_XP`,
  `CslibFrontier.Complexity.ParaNPHard.notMem_FPT`,
  `CslibFrontier.Complexity.ParaNPComplete.mem_XP_iff_pEqNP`,
  `CslibFrontier.Complexity.ParaNPComplete.mem_FPT_iff_pEqNP`: `XP` and `FPT` intractability of
  `para-NP`-hard problems unless `P = NP`.
- `CslibFrontier.Complexity.gapMin_npHard_of_nat_gap_reduction`,
  `CslibFrontier.Complexity.pEqNP_of_isPolyTimeMinApprox_of_gap_reduction`,
  `CslibFrontier.Complexity.not_isPolyTimeMinApprox_of_gap_reduction`,
  `CslibFrontier.Complexity.pEqNP_of_isStrictPolyTimeMinApprox_of_gap_reduction`,
  `CslibFrontier.Complexity.not_isStrictPolyTimeMinApprox_of_gap_reduction`: gap promise
  `NP`-hardness and conditional inapproximability from integer-gap reductions.
-/

public section

namespace CslibFrontier.Complexity

open Cslib.Complexity Turing Turing.MultiTapeTM

/-! ### Global `P = NP` proposition -/

/-- Canonical statement of `P = NP`: deterministic and nondeterministic polynomial time coincide
for every binary instance encoding `enc : α ↪ List Bool`. -/
def PEqNP : Prop :=
  ∀ {α : Type} (enc : α ↪ List Bool), P enc = NP enc

/-- Characterization of `PEqNP` as equality of `P enc` and `NP enc` across all encodings. -/
theorem pEqNP_iff : PEqNP ↔ ∀ {α : Type} (enc : α ↪ List Bool), P enc = NP enc :=
  Iff.rfl

/-- `P = NP` holds globally if and only if `SAT` lies in `P encCNF`. -/
theorem pEqNP_iff_SAT_mem_P : PEqNP ↔ SAT ∈ P encCNF :=
  CookLevin.SAT_npComplete.mem_P_iff.symm

/-- `P = NP` holds globally if and only if `ThreeSAT` lies in `P encCNF`. -/
theorem pEqNP_iff_ThreeSAT_mem_P : PEqNP ↔ ThreeSAT ∈ P encCNF :=
  ThreeSAT_npComplete.mem_P_iff.symm

/-- Any `NP`-hard problem lying in `P` implies `PEqNP`. -/
theorem pEqNP_of_npHard_of_mem_P {β : Type} {encB : β ↪ List Bool} {B : Set β}
    (hHard : NPHard encB B) (hP : B ∈ P encB) : PEqNP :=
  pEqNP_iff_SAT_mem_P.mpr ((hHard encCNF SAT SAT.mem_NP).mem_P hP)

/-! ### Parameter slices and the class `para-NP` -/

/-- The `k`-th parameter slice `{a ∈ A | κ a = k}` of a parameterized problem `(A, κ)`. -/
@[expose] def paramSlice {α : Type*} (κ : α → ℕ) (A : Set α) (k : ℕ) : Set α :=
  {a ∈ A | κ a = k}

/-- Membership in `paramSlice κ A k`. -/
theorem mem_paramSlice_iff {α : Type*} {κ : α → ℕ} {A : Set α} {k : ℕ} {a : α} :
    a ∈ paramSlice κ A k ↔ a ∈ A ∧ κ a = k :=
  Iff.rfl

/-- The parameterized complexity class `para-NP`: the parameterized
problems `(A, κ)` over `enc` that fpt-reduce to some classical `NP` problem equipped with a
constant parameter.
-/
def ParaNP {α : Type} (enc : α ↪ List Bool) (κ : α → ℕ) : Set (Set α) :=
  {A | ∃ (β : Type) (encB : β ↪ List Bool) (B : Set β),
    B ∈ NP encB ∧ FPTReducible enc encB κ (fun _ ↦ 0) A B}

/-- `para-NP`-hardness under fpt-reductions: every problem in `ParaNP` fpt-reduces to `(B, κ)`. -/
abbrev ParaNPHard {β : Type} (enc : β ↪ List Bool) (κ : β → ℕ) (B : Set β) : Prop :=
  FPTHard @ParaNP enc κ B

/-- `para-NP`-completeness under fpt-reductions: membership in `ParaNP` together with
`ParaNPHard`. -/
@[expose] def ParaNPComplete {β : Type} (enc : β ↪ List Bool) (κ : β → ℕ) (B : Set β) : Prop :=
  B ∈ ParaNP enc κ ∧ ParaNPHard enc κ B

/-- Characterization of `ParaNPComplete`. -/
theorem paraNPComplete_iff {β : Type} {enc : β ↪ List Bool} {κ : β → ℕ} {B : Set β} :
    ParaNPComplete enc κ B ↔ B ∈ ParaNP enc κ ∧ ParaNPHard enc κ B :=
  Iff.rfl

section ParaNPAPI

variable {α β : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool} {κA : α → ℕ} {κB : β → ℕ}
  {A : Set α} {B : Set β}

/-- By the Cook–Levin theorem, a parameterized problem belongs to `ParaNP` if and only if it
fpt-reduces to `SAT` with a constant parameter. -/
theorem mem_ParaNP_iff_fptReducible_SAT :
    A ∈ ParaNP encA κA ↔ FPTReducible encA encCNF κA (fun _ ↦ 0) A SAT := by
  refine ⟨?_, fun h ↦ ⟨_, encCNF, SAT, SAT.mem_NP, h⟩⟩
  rintro ⟨γ, encC, C, hC, hAC⟩
  obtain ⟨g, hg, hgC⟩ := CookLevin.SAT_npHard encC C hC
  exact hAC.trans (FPTReducible.of_computableInPolyTime hg (h := fun _ ↦ 0) (fun _ ↦ le_rfl) hgC)

/-- `ParaNP` is closed under fpt-reductions. -/
theorem mem_ParaNP_of_fptReducible (hAB : FPTReducible encA encB κA κB A B)
    (hB : B ∈ ParaNP encB κB) : A ∈ ParaNP encA κA :=
  mem_ParaNP_iff_fptReducible_SAT.mpr (hAB.trans (mem_ParaNP_iff_fptReducible_SAT.mp hB))

/-- Every classical `NP` problem belongs to `ParaNP` under any parameterization. -/
theorem NP_subset_ParaNP : NP encA ⊆ ParaNP encA κA :=
  fun A hA ↦ ⟨α, encA, A, hA,
    FPTReducible.of_computableInPolyTime .id' (h := fun _ ↦ 0) (fun _ ↦ le_rfl) fun _ ↦ Iff.rfl⟩

/-- Every classical `P` problem belongs to `ParaNP` under any parameterization. -/
theorem P_subset_ParaNP : P encA ⊆ ParaNP encA κA :=
  P_subset_NP.trans NP_subset_ParaNP

/-- `FPT ⊆ ParaNP` for every encoding and parameter. -/
theorem FPT_subset_ParaNP : FPT encA κA ⊆ ParaNP encA κA := by
  intro A hA
  obtain ⟨g, hg, hgA⟩ := mem_FPT_iff_computableInFPTTime.mp hA
  refine mem_ParaNP_iff_fptReducible_SAT.mpr
    ⟨fun a ↦ if g a then [] else [[]],
      ⟨hg.ite ((ComputableInPolyTime.const []).computableInFPTTime κA)
        ((ComputableInPolyTime.const [[]]).computableInFPTTime κA),
        fun _ ↦ 0, fun _ ↦ le_rfl⟩,
      fun a ↦ ?_⟩
  cases hga : g a
  · rw [hgA a]
    simp only [hga, Bool.false_eq_true, ↓reduceIte, mem_SAT]
    exact iff_of_false not_false fun ⟨σ, hσ⟩ ↦ by
      simp [Cslib.Logic.PL.CNF.eval, Cslib.Logic.PL.Clause.eval] at hσ
  · rw [hgA a]
    simp only [hga, ↓reduceIte, mem_SAT]
    exact iff_of_true trivial ⟨fun _ ↦ false, rfl⟩

private theorem computableInPolyTime_of_computableInFPTTime_of_le {f : α → β} {K : ℕ}
    (hf : ComputableInFPTTime f encA encB κA) (hκ : ∀ a, κA a ≤ K) :
    ComputableInPolyTime f encA encB := by
  obtain ⟨F, c, hts⟩ := hf
  let M : ℕ := ∑ j ∈ Finset.range (K + 1), F j
  have hle (a : α) : F (κA a) * ((encA a).length + 1) ^ c ≤ M * ((encA a).length + 1) ^ c :=
    Nat.mul_le_mul_right _
      (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _)
        (Finset.mem_range.mpr (Nat.lt_succ_of_le (hκ a))))
  have hpb : Cslib.PolynomiallyBounded fun n ↦ M * (n + 1) ^ c :=
    Cslib.polynomiallyBounded_iff_le.mpr ⟨M, c, fun _ ↦ le_rfl⟩
  exact ⟨_, _, hpb, hpb, hts.mono hle hle⟩

/-- For any parameter bounded above by a constant `K`, `ParaNP` coincides with `NP`. -/
theorem ParaNP_eq_NP_of_le {K : ℕ} (hκ : ∀ a, κA a ≤ K) : ParaNP encA κA = NP encA := by
  refine Set.Subset.antisymm (fun A hA ↦ ?_) NP_subset_ParaNP
  obtain ⟨f, ⟨hf, -⟩, hfA⟩ := mem_ParaNP_iff_fptReducible_SAT.mp hA
  have hred : PolyTimeReducible encA encCNF A SAT :=
    ⟨f, computableInPolyTime_of_computableInFPTTime_of_le hf hκ, hfA⟩
  exact hred.mem_NP SAT.mem_NP

private theorem kleeneEval_map_some' {n : ℕ} {x : List Bool} (hx : x.length = n)
    {gates : List (Cslib.Circuits.Boolean.Unbounded.Op × List ℕ)}
    (h : Cslib.Circuits.Program.IsCodeFrom Cslib.Circuits.Boolean.Unbounded.signature n 0 gates) :
    Cslib.Circuits.Boolean.Unbounded.kleeneEval (x.map some) gates =
      (Cslib.Circuits.evalCode Cslib.Circuits.Boolean.Unbounded.interpretation
        false x gates).map some := by
  open Cslib.Circuits Cslib.Circuits.Boolean in
  induction gates using List.reverseRecOn with
  | nil => rfl
  | append_singleton gates g ih =>
    rw [Program.isCodeFrom_append, Program.isCodeFrom_cons, Nat.zero_add] at h
    obtain ⟨hgates, ⟨hg_len, hg_lt⟩, -⟩ := h
    rw [Unbounded.kleeneEval, List.foldl_append, List.foldl_cons, List.foldl_nil,
      ← Unbounded.kleeneEval, ih hgates, evalCode_append_singleton, List.map_append,
      List.map_singleton, Unbounded.kleeneStep]
    congr 2
    set vals := evalCode Unbounded.interpretation false x gates
    have hvals_len : vals.length = n + gates.length := by rw [length_evalCode, hx]
    have hargs : g.2.map ((vals.map some).getD · none) =
        (g.2.map (vals.getD · false)).map some := by
      rw [List.map_map]
      refine List.map_congr_left fun i hi ↦ ?_
      have hi_lt : i < vals.length := hvals_len ▸ hg_lt i hi
      simp only [Function.comp_apply, List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_eq_getElem hi_lt, Option.map_some, Option.getD_some]
    rw [hargs, ← ofFn_elim_eq_map (σ := Unbounded.signature) false vals g hg_len, List.map_ofFn]
    exact Unbounded.kleeneInterpretation_some g.1 _

private theorem kleeneEval_circuit_eq_some' {n : ℕ}
    (c : Cslib.Circuits.Circuit Cslib.Circuits.Boolean.Unbounded.signature n 1)
    {x : List Bool} (hx : x.length = n) :
    (Cslib.Circuits.Boolean.Unbounded.kleeneEval (x.map some) c.code.1).getD
        (c.code.2.getD 0 0) none =
      some (c.eval Cslib.Circuits.Boolean.Unbounded.interpretation
        (Cslib.BitString.ofList n x) 0) := by
  open Cslib.Circuits Cslib.Circuits.Boolean in
  have hc : (Circuit.ofCode n 1 c.code).isSome := by simp
  obtain ⟨hcode, houts_len, houts_lt⟩ := Circuit.isSome_ofCode_iff.1 hc
  have ho : c.code.2.getD 0 0 = (c.outputs 0).toNat := by simp [Circuit.code]
  have hout_lt :
      (c.outputs 0).toNat < (evalCode Unbounded.interpretation false x c.code.1).length := by
    rw [length_evalCode, hx]
    exact houts_lt _ (by rw [← ho]; exact List.getElem_mem (by omega : 0 < c.code.2.length))
  rw [ho, kleeneEval_map_some' hx hcode, Circuit.eval_eq_getD _ _ false,
    Cslib.BitString.ofFn_ofList hx, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_map, List.getElem?_eq_getElem hout_lt]
  rfl

/-- Every level `W[t]` of the `W`-hierarchy is contained in `ParaNP`. -/
theorem W_subset_ParaNP (t : ℕ) : W t encA κA ⊆ ParaNP encA κA := by
  open Cslib.Circuits Cslib.Circuits.Boolean in
  intro A ⟨d, hd⟩
  have hWCS_NP : WCS t d ∈ NP (encWCS t d) := by
    let pad (x : WCSInstance t d × List Bool) : List Bool :=
      (x.2 ++ List.replicate x.1.circuit.toCircuit.1 false).take x.1.circuit.toCircuit.1
    let check : WCSInstance t d × List Bool → Bool := fun x ↦
      let c := x.1.circuit.toCircuit
      decide ((pad x).count true = x.1.weight) &&
        ((Unbounded.kleeneEval ((pad x).map some) c.2.code.1).getD
          (c.2.code.2.getD 0 0) none == some true)
    have hpad_len (x : WCSInstance t d × List Bool) :
        (pad x).length = x.1.circuit.toCircuit.1 := by
      simp [pad]
    refine ⟨Polynomial.X, check, ?_, IsVerifier.of_padding (fun x w _ hw ↦ ?_) fun x hx ↦ ?_⟩
    · let encCode := encPair encUnary
        (encPair (encList (Circuit.encGate Unbounded.encOp)) (encList encNat))
      have hcode : ComputableInPolyTime
          (fun x : WCSInstance t d × List Bool ↦
            (x.1.circuit.toCircuit.1, x.1.circuit.toCircuit.2.code))
          (encPair (encWCS t d) encBits) encCode :=
        (ComputableInPolyTime.of_enc_eq (f := fun c : WeftCircuit t d ↦
            (c.toCircuit.1, c.toCircuit.2.code)) ComputableInPolyTime.id'
          fun _ ↦ rfl).comp
          ((encWCS_circuit_polyTime .id').comp (ComputableInPolyTime.fst _ _))
      have hn : ComputableInPolyTime
          (fun x : WCSInstance t d × List Bool ↦ x.1.circuit.toCircuit.1)
          (encPair (encWCS t d) encBits) encUnary := hcode.fst'
      have hgates : ComputableInPolyTime
          (fun x : WCSInstance t d × List Bool ↦ x.1.circuit.toCircuit.2.code.1)
          (encPair (encWCS t d) encBits) (encList (Circuit.encGate Unbounded.encOp)) :=
        hcode.snd'.fst'
      have ho : ComputableInPolyTime
          (fun x : WCSInstance t d × List Bool ↦ x.1.circuit.toCircuit.2.code.2.getD 0 0)
          (encPair (encWCS t d) encBits) encNat :=
        ComputableInPolyTime.listGetD_binary (encA := encNat) 0 hcode.snd'.snd' (.const 0)
      have hwt : ComputableInPolyTime
          (fun x : WCSInstance t d × List Bool ↦ x.1.weight)
          (encPair (encWCS t d) encBits) encNat :=
        (encWCS_weight_polyTime .id').comp (ComputableInPolyTime.fst _ _)
      have hpad_pt : ComputableInPolyTime pad (encPair (encWCS t d) encBits) encBits :=
        ComputableInPolyTime.bitsTakeWithInput
          ((ComputableInPolyTime.snd _ _).bitsAppend
            ((ComputableInPolyTime.bitsReplicate false).comp hn)) hn
      have hcntU := ComputableInPolyTime.bitsCountWithInput hpad_pt (.const true)
      have hcnt : ComputableInPolyTime
          (fun x : WCSInstance t d × List Bool ↦ decide ((pad x).count true = x.1.weight))
          (encPair (encWCS t d) encBits) encBool :=
        (ComputableInPolyTime.unary_to_binary.comp hcntU).decide_eq' hwt
      have hsome := (ComputableInPolyTime.map
        (ComputableInPolyTime.optionSome encBool)).comp
        (ComputableInPolyTime.bitsToList.comp hpad_pt)
      have hkl := Unbounded.computableInPolyTime_kleeneEval hsome hgates
      have hout := ComputableInPolyTime.listGetD_binary (encA := encOption encBool) none hkl ho
      have heval : ComputableInPolyTime _ (encPair (encWCS t d) encBits) encBool :=
        (ComputableInPolyTime.of_finite (fun v : Option Bool ↦ v == some true)).comp hout
      exact ComputableInPolyTime.bool_and' hcnt heval
    · simp only [check, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hw
      rw [kleeneEval_circuit_eq_some' x.circuit.toCircuit.2 (hpad_len (x, w)),
        Option.some.injEq] at hw
      refine ⟨Cslib.BitString.ofList x.circuit.toCircuit.1 (pad (x, w)), ?_, hw.2⟩
      rw [← Cslib.BitString.count_true_ofFn,
        Cslib.BitString.ofFn_ofList (hpad_len (x, w)), hw.1]
    · obtain ⟨bs, hwt, hev⟩ := hx
      let u : List Bool := List.ofFn bs
      have hulen : u.length ≤ Polynomial.X.eval (encWCS t d x).length := by
        simp only [u, List.length_ofFn, Polynomial.eval_X, encWCS_apply]
        have h1 : x.circuit.toCircuit.1 = (encUnary x.circuit.toCircuit.1).length := by simp
        have h2 : (encUnary x.circuit.toCircuit.1).length ≤
            (encWeftCircuit t d x.circuit).length := by
          rw [encWeftCircuit_apply]
          exact length_le_encPair_left encUnary
            (encPair (encList (Circuit.encGate Unbounded.encOp)) (encList encNat))
            (x.circuit.toCircuit.1, x.circuit.toCircuit.2.code)
        exact h1.trans_le (h2.trans (length_le_encPair_left _ _ (x.circuit, x.weight)))
      refine ⟨u, hulen, fun m ↦ ?_⟩
      have hpad_eq : pad (x, u ++ List.replicate m false) = u := by
        simp only [pad, List.append_assoc]
        rw [List.take_append_of_le_length (by simp [u]),
          show x.circuit.toCircuit.1 = u.length by simp [u], List.take_length]
      simp only [check, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
      rw [kleeneEval_circuit_eq_some' x.circuit.toCircuit.2
        (hpad_len (x, u ++ List.replicate m false)), Option.some.injEq, hpad_eq]
      have hof : Cslib.BitString.ofList x.circuit.toCircuit.1 u = bs :=
        funext fun i ↦ by simp [u]
      exact ⟨by simpa only [u, Cslib.BitString.count_true_ofFn] using hwt, hof ▸ hev⟩
  exact mem_ParaNP_of_fptReducible hd (NP_subset_ParaNP hWCS_NP)

/-- Every problem decided by a nondeterministic multi-tape machine within an fpt-computable unary
clock `t` belongs to `ParaNP`.
-/
theorem mem_ParaNP_of_ntm_decidesInTime {t : α → ℕ} (ht : ComputableInFPTTime t encA encUnary κA)
    {k : ℕ} {State : Type} [Finite State] (ntm : MultiTapeNTM k Bool State)
    (hdec : ntm.DecidesInTime encA A t) : A ∈ ParaNP encA κA := by
  let encPad : α × ℕ ↪ List Bool := encPair encA encUnary
  let PadA : Set (α × ℕ) :=
    {p | ∃ w : List Bool, w.length = p.2 ∧ ntm.checkChoices encA (p.1, w) = true}
  let V : (α × ℕ) × List Bool → Bool := fun x ↦
    decide (x.1.2 ≤ x.2.length) && ntm.checkChoices encA (x.1.1, x.2.take x.1.2)
  have hV_poly : ComputableInPolyTime V (encPair encPad encBits) encBool := by
    unfold V encPad
    fun_prop
  have hV_ver : IsVerifier encPad Polynomial.X V PadA := by
    refine IsVerifier.of_padding (fun p w _ hw ↦ ?_) fun p ⟨u, hulen, hu⟩ ↦ ?_
    · simp only [V, Bool.and_eq_true, decide_eq_true_eq] at hw
      exact ⟨w.take p.2, List.length_take_of_le hw.1, hw.2⟩
    · have hle : u.length ≤ Polynomial.X.eval (encPad p).length := by
        simp only [hulen, Polynomial.eval_X, encPad]
        calc p.2 = (encUnary p.2).length := by simp
          _ ≤ (encPair encA encUnary p).length := length_le_encPair_right _ _ p
      refine ⟨u, hle, fun m ↦ ?_⟩
      simp only [V, Bool.and_eq_true, decide_eq_true_eq, List.length_append,
        List.length_replicate, hulen]
      refine ⟨Nat.le_add_right _ _, ?_⟩
      rwa [List.take_append_of_le_length hulen.ge, ← hulen, List.take_length]
  have hPadNP : PadA ∈ NP encPad := ⟨Polynomial.X, V, hV_poly, hV_ver⟩
  let M : ℕ := Nat.card (Turing.Action k Bool State)
  have hmul : ComputableInPolyTime (fun n : ℕ ↦ M * n) encUnary encUnary := by fun_prop
  have hMt : ComputableInFPTTime (fun a ↦ M * t a) encA encUnary κA :=
    (hmul.computableInFPTTime (fun _ ↦ 0)).comp ht (h := fun _ ↦ 0) fun _ ↦ le_rfl
  have hpad : ComputableInFPTTime (fun a ↦ (a, M * t a)) encA encPad κA := by
    obtain ⟨F₁, c₁, hiT⟩ := ComputableInPolyTime.id'.computableInFPTTime κA (encA := encA)
    obtain ⟨F₂, c₂, htT⟩ := hMt
    have hiO : ComputableInO id encA encA
        (fun a ↦ F₁ (κA a) * ((encA a).length + 1) ^ c₁)
        (fun a ↦ F₁ (κA a) * ((encA a).length + 1) ^ c₁) :=
      .of_bounds hiT 1 (fun _ ↦ by omega) (fun _ ↦ by omega)
        fun a ↦ (hiT.length_le a).trans (by omega)
    have htO : ComputableInO (fun a ↦ M * t a) encA encUnary
        (fun a ↦ F₂ (κA a) * ((encA a).length + 1) ^ c₂)
        (fun a ↦ F₂ (κA a) * ((encA a).length + 1) ^ c₂) :=
      .of_bounds htT 1 (fun _ ↦ by omega) (fun _ ↦ by omega)
        fun a ↦ (htT.length_le a).trans (by omega)
    have hkey (a : α) :
        F₁ (κA a) * ((encA a).length + 1) ^ c₁ + F₂ (κA a) * ((encA a).length + 1) ^ c₂ ≤
          (F₁ (κA a) + F₂ (κA a)) * ((encA a).length + 1) ^ (c₁ + c₂) := by
      have h1 := Nat.mul_le_mul_left (F₁ (κA a))
        (Nat.pow_le_pow_right (Nat.succ_pos (encA a).length) (Nat.le_add_right c₁ c₂))
      have h2 := Nat.mul_le_mul_left (F₂ (κA a))
        (Nat.pow_le_pow_right (Nat.succ_pos (encA a).length) (Nat.le_add_left c₂ c₁))
      rw [Nat.add_mul]
      exact Nat.add_le_add h1 h2
    exact ComputableInO.computableInFPTTime (F := fun j ↦ F₁ j + F₂ j) (c := c₁ + c₂)
      ((hiO.prod htO).mono_le hkey hkey)
  exact ⟨α × ℕ, encPad, PadA, hPadNP, fun a ↦ (a, M * t a),
    ⟨hpad, fun _ ↦ 0, fun _ ↦ le_rfl⟩, fun a ↦ hdec.mem_iff_exists_checkChoices le_rfl⟩

/-! ### `para-NP`-hardness, Flum–Grohe slice theorem, and `XP` collapse -/

/-- A parameterized problem `(B, κB)` is `para-NP`-hard if and only if `SAT` (with a constant
parameter) fpt-reduces to `(B, κB)`. -/
theorem paraNPHard_iff_fptReducible_SAT :
    ParaNPHard encB κB B ↔ FPTReducible encCNF encB (fun _ ↦ 0) κB SAT B :=
  ⟨fun h ↦ h encCNF (fun _ ↦ 0) SAT (NP_subset_ParaNP SAT.mem_NP),
    fun h _ _ _ _ hA ↦ (mem_ParaNP_iff_fptReducible_SAT.mp hA).trans h⟩

/-- **Flum–Grohe Slice Hardness (bounded parameter)**: if an
`NP`-hard problem `A` polynomial-time many-one reduces to `B` via `f` with `κB (f a) ≤ K` for a
fixed constant `K`, then `(B, κB)` is `para-NP`-hard.
-/
theorem ParaNPHard.of_bounded_param_reduction (hHard : NPHard encA A) {f : α → β} {K : ℕ}
    (hf : ComputableInPolyTime f encA encB) (hκ : ∀ a, κB (f a) ≤ K)
    (hfAB : ∀ a, a ∈ A ↔ f a ∈ B) : ParaNPHard encB κB B := by
  obtain ⟨g, hg, hgA⟩ := hHard encCNF SAT SAT.mem_NP
  exact paraNPHard_iff_fptReducible_SAT.mpr
    (FPTReducible.of_computableInPolyTime (hf.comp hg) (h := fun _ ↦ K) (fun a ↦ hκ (g a))
      fun a ↦ (hgA a).trans (hfAB (g a)))

/-- **Flum–Grohe Slice Hardness (constant parameter)**: if
an `NP`-hard problem `A` polynomial-time many-one reduces to `B` via `f` into a single slice
`κB (f a) = k`, then `(B, κB)` is `para-NP`-hard.
-/
theorem ParaNPHard.of_const_param_reduction (hHard : NPHard encA A) {f : α → β} {k : ℕ}
    (hf : ComputableInPolyTime f encA encB) (hκ : ∀ a, κB (f a) = k)
    (hfAB : ∀ a, a ∈ A ↔ f a ∈ B) : ParaNPHard encB κB B :=
  ParaNPHard.of_bounded_param_reduction hHard hf (fun a ↦ (hκ a).le) hfAB

/-- **Flum–Grohe Slice Theorem**: if some single slice
`paramSlice κB B k` is `NP`-hard (allowing instances outside `B` to have any parameter when
complemented by a constant-parameter reduction), specifically if `NPHard encB (paramSlice κB B k)`
with a reduction landing in `{b | κB b = k}`, or whenever a fixed-slice language reducing to `B`
with parameter `k` is `NP`-hard, then `(B, κB)` is `para-NP`-hard.
-/
theorem ParaNPHard.of_slice_npHard {γ : Type} {encC : γ ↪ List Bool} {sliceSet : Set γ}
    (hHard : NPHard encC sliceSet) (embed : γ → β) {k : ℕ}
    (hembed : ComputableInPolyTime embed encC encB) (hκ : ∀ x, κB (embed x) = k)
    (hmem : ∀ x, x ∈ sliceSet ↔ embed x ∈ B) : ParaNPHard encB κB B :=
  ParaNPHard.of_const_param_reduction hHard hembed hκ hmem

/-- **Collapse from `XP`**: if a `para-NP`-hard problem
belongs to `XP`, then `P = NP` across all encodings.
-/
theorem ParaNPHard.pEqNP_of_mem_XP (hHard : ParaNPHard encB κB B) (hXP : B ∈ XP encB κB) :
    PEqNP := by
  have hSAT_XP : SAT ∈ XP encCNF (fun _ ↦ 0) :=
    (paraNPHard_iff_fptReducible_SAT.mp hHard).mem_XP hXP
  rw [XP_eq_P_of_le (K := 0) fun _ ↦ le_rfl] at hSAT_XP
  exact fun _ ↦ pEqNP_iff_SAT_mem_P.mpr hSAT_XP

/-- If a `para-NP`-hard problem belongs to `FPT`, then `P = NP` across all encodings. -/
theorem ParaNPHard.pEqNP_of_mem_FPT (hHard : ParaNPHard encB κB B) (hFPT : B ∈ FPT encB κB) :
    PEqNP :=
  hHard.pEqNP_of_mem_XP (FPT_subset_XP hFPT)

/-- Assuming `¬ PEqNP`, no `para-NP`-hard problem belongs to `XP`. -/
theorem ParaNPHard.notMem_XP (hHard : ParaNPHard encB κB B) (hne : ¬ PEqNP) :
    B ∉ XP encB κB :=
  fun hXP ↦ hne (hHard.pEqNP_of_mem_XP hXP)

/-- Assuming `¬ PEqNP`, no `para-NP`-hard problem belongs to `FPT`. -/
theorem ParaNPHard.notMem_FPT (hHard : ParaNPHard encB κB B) (hne : ¬ PEqNP) :
    B ∉ FPT encB κB :=
  fun hFPT ↦ hne (hHard.pEqNP_of_mem_FPT hFPT)

/-- A `para-NP`-complete problem belongs to `FPT` if and only if `P = NP`. -/
theorem ParaNPComplete.mem_FPT_iff_pEqNP (hB : ParaNPComplete encB κB B) :
    B ∈ FPT encB κB ↔ PEqNP := by
  refine ⟨hB.2.pEqNP_of_mem_FPT, fun hEq ↦ ?_⟩
  have hSAT : SAT ∈ FPT encCNF (fun _ ↦ 0) := P_subset_FPT (pEqNP_iff_SAT_mem_P.mp hEq)
  exact (mem_ParaNP_iff_fptReducible_SAT.mp hB.1).mem_FPT hSAT

/-- A `para-NP`-complete problem belongs to `XP` if and only if `P = NP`. -/
theorem ParaNPComplete.mem_XP_iff_pEqNP (hB : ParaNPComplete encB κB B) :
    B ∈ XP encB κB ↔ PEqNP :=
  ⟨hB.2.pEqNP_of_mem_XP, fun hEq ↦ FPT_subset_XP (hB.mem_FPT_iff_pEqNP.mpr hEq)⟩

end ParaNPAPI

/-! ### Minimization gap problems and multiplicative inapproximability -/

/-- A function `alg : α → ℕ` is a polynomial-time multiplicative `c`-approximation for a
minimization objective `opt : α → ℕ` relative to `enc` if `alg` is computable in polynomial time
(with binary output `encNat`) and satisfies `opt x ≤ alg x` and `(alg x : ℝ) ≤ c * opt x` on
every instance `x`. -/
def IsPolyTimeMinApprox {α : Type} (enc : α ↪ List Bool) (opt alg : α → ℕ) (c : ℝ) : Prop :=
  ComputableInPolyTime alg enc encNat ∧ ∀ x, opt x ≤ alg x ∧ (alg x : ℝ) ≤ c * (opt x : ℝ)

/-- Characterization of `IsPolyTimeMinApprox`. -/
theorem isPolyTimeMinApprox_iff {α : Type} {enc : α ↪ List Bool} {opt alg : α → ℕ} {c : ℝ} :
    IsPolyTimeMinApprox enc opt alg c ↔
      ComputableInPolyTime alg enc encNat ∧
        ∀ x, opt x ≤ alg x ∧ (alg x : ℝ) ≤ c * (opt x : ℝ) :=
  Iff.rfl

/-- A function `alg : α → ℕ` is a strict polynomial-time multiplicative `c`-approximation for a
minimization objective `opt : α → ℕ` if `alg` runs in polynomial time, satisfies
`opt x ≤ alg x ≤ c * opt x`, and achieves strict inequality `(alg x : ℝ) < c * opt x` whenever
`0 < opt x`. -/
def IsStrictPolyTimeMinApprox {α : Type} (enc : α ↪ List Bool) (opt alg : α → ℕ) (c : ℝ) : Prop :=
  ComputableInPolyTime alg enc encNat ∧
    ∀ x, opt x ≤ alg x ∧ (alg x : ℝ) ≤ c * (opt x : ℝ) ∧
      (0 < opt x → (alg x : ℝ) < c * (opt x : ℝ))

/-- Characterization of `IsStrictPolyTimeMinApprox`. -/
theorem isStrictPolyTimeMinApprox_iff {α : Type} {enc : α ↪ List Bool} {opt alg : α → ℕ}
    {c : ℝ} :
    IsStrictPolyTimeMinApprox enc opt alg c ↔
      ComputableInPolyTime alg enc encNat ∧
        ∀ x, opt x ≤ alg x ∧ (alg x : ℝ) ≤ c * (opt x : ℝ) ∧
          (0 < opt x → (alg x : ℝ) < c * (opt x : ℝ)) :=
  Iff.rfl

/-- Every strict polynomial-time `c`-approximation is a non-strict `c`-approximation. -/
theorem IsStrictPolyTimeMinApprox.isPolyTimeMinApprox {α : Type} {enc : α ↪ List Bool}
    {opt alg : α → ℕ} {c : ℝ} (h : IsStrictPolyTimeMinApprox enc opt alg c) :
    IsPolyTimeMinApprox enc opt alg c :=
  ⟨h.1, fun x ↦ ⟨(h.2 x).1, (h.2 x).2.1⟩⟩

/-- Monotonicity of `IsPolyTimeMinApprox` in the approximation factor `c`. -/
@[gcongr]
theorem IsPolyTimeMinApprox.mono {α : Type} {enc : α ↪ List Bool} {opt alg : α → ℕ} {c₁ c₂ : ℝ}
    (h : IsPolyTimeMinApprox enc opt alg c₁) (hc : c₁ ≤ c₂) :
    IsPolyTimeMinApprox enc opt alg c₂ :=
  ⟨h.1, fun x ↦ ⟨(h.2 x).1, (h.2 x).2.trans (mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg _))⟩⟩

/-- Monotonicity of `IsStrictPolyTimeMinApprox` in the approximation factor `c`. -/
@[gcongr]
theorem IsStrictPolyTimeMinApprox.mono {α : Type} {enc : α ↪ List Bool} {opt alg : α → ℕ}
    {c₁ c₂ : ℝ} (h : IsStrictPolyTimeMinApprox enc opt alg c₁) (hc : c₁ ≤ c₂) :
    IsStrictPolyTimeMinApprox enc opt alg c₂ :=
  ⟨h.1, fun x ↦ ⟨(h.2 x).1, (h.2 x).2.1.trans (mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg _)),
    fun hpos ↦ lt_of_lt_of_le ((h.2 x).2.2 hpos)
      (mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg _))⟩⟩

/-- **Gap Promise `NP`-Hardness**: if a polynomial-time function `f : α → β` reduces an `NP`-hard
problem `A` to the integer gap `[a, a + 1]` of `opt : β → ℕ` (yes-instances satisfy `opt ≤ a`,
no-instances satisfy `a + 1 ≤ opt`), then `PromiseProblem.gapMin` at `(a, a + 1)` is
unconditionally `NP`-hard. -/
theorem gapMin_npHard_of_nat_gap_reduction {α β : Type} {encA : α ↪ List Bool}
    {encB : β ↪ List Bool} {A : Set α} (hHard : NPHard encA A) {opt : β → ℕ} {a : ℕ}
    {f : α → β} (hf : ComputableInPolyTime f encA encB)
    (hyes : ∀ x ∈ A, opt (f x) ≤ a) (hno : ∀ x, x ∉ A → a + 1 ≤ opt (f x)) :
    PromiseProblem.NPHard encB
      (PromiseProblem.gapMin (fun b ↦ (opt b : ℝ)) (fun _ ↦ (a : ℝ))
        (fun _ ↦ ((a + 1 : ℕ) : ℝ))) := by
  have hred : PromiseProblem.PolyTimeReducible encA encB (PromiseProblem.ofSet A)
      (PromiseProblem.gapMin (fun b ↦ (opt b : ℝ)) (fun _ ↦ (a : ℝ))
        (fun _ ↦ ((a + 1 : ℕ) : ℝ))) :=
    ⟨f, hf, fun x hx ↦ PromiseProblem.mem_yes_gapMin.mpr (Nat.cast_le.mpr (hyes x hx)),
      fun x hx ↦ PromiseProblem.mem_no_gapMin.mpr
        ⟨Nat.cast_le.mpr (hno x hx), Nat.cast_lt.mpr (Nat.lt_succ_self a)⟩⟩
  exact (PromiseProblem.npHard_ofSet_iff.mpr hHard).trans hred

/-- Any polynomial-time `c`-approximation with `c < (a + 1) / a` (`0 < a`) solves the integer gap
problem `gapMin opt a (a + 1)` in `PromiseP`. -/
theorem gapMin_mem_PromiseP_of_isPolyTimeMinApprox {β : Type} {encB : β ↪ List Bool}
    {opt alg : β → ℕ} {a : ℕ} (ha : 0 < a) {c : ℝ} (hc : c < ((a + 1 : ℕ) : ℝ) / (a : ℝ))
    (happrox : IsPolyTimeMinApprox encB opt alg c) :
    PromiseProblem.gapMin (fun b ↦ (opt b : ℝ)) (fun _ ↦ (a : ℝ))
      (fun _ ↦ ((a + 1 : ℕ) : ℝ)) ∈ PromiseP encB := by
  have halg : ComputableInPolyTime alg encB encNat := happrox.1
  have hdec : ComputableInPolyTime (fun b ↦ decide (alg b ≤ a)) encB encBool := by fun_prop
  refine mem_PromiseP_iff.mpr ⟨fun b ↦ decide (alg b ≤ a), hdec, fun b hyes ↦ ?_, fun b hno ↦ ?_⟩
  · simp only [PromiseProblem.mem_yes_gapMin, Nat.cast_le] at hyes
    rw [decide_eq_true_eq]
    have hbd := (happrox.2 b).2
    by_cases hc0 : c ≤ 0
    · have h0 : (alg b : ℝ) ≤ 0 :=
      hbd.trans (mul_nonpos_of_nonpos_of_nonneg hc0 (Nat.cast_nonneg _))
      have heq : alg b = 0 := by exact_mod_cast le_antisymm h0 (Nat.cast_nonneg _)
      omega
    · have hcp : 0 < c := lt_of_not_ge hc0
      have har : (0 : ℝ) < (a : ℝ) := Nat.cast_pos.mpr ha
      have hlt : (alg b : ℝ) < ((a + 1 : ℕ) : ℝ) :=
        calc (alg b : ℝ) ≤ c * (opt b : ℝ) := hbd
          _ ≤ c * (a : ℝ) := mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hyes) hcp.le
          _ < (((a + 1 : ℕ) : ℝ) / (a : ℝ)) * (a : ℝ) := mul_lt_mul_of_pos_right hc har
          _ = ((a + 1 : ℕ) : ℝ) := div_mul_cancel₀ _ har.ne'
      exact Nat.lt_succ_iff.mp (by exact_mod_cast hlt)
  · simp only [PromiseProblem.mem_no_gapMin, Nat.cast_le] at hno
    rw [decide_eq_false_iff_not]
    have h1 := hno.1
    have h2 := (happrox.2 b).1
    omega

/-- Any strict polynomial-time `((a + 1) / a)`-approximation (`0 < a`) solves the integer gap
problem `gapMin opt a (a + 1)` in `PromiseP`. -/
theorem gapMin_mem_PromiseP_of_isStrictPolyTimeMinApprox {β : Type} {encB : β ↪ List Bool}
    {opt alg : β → ℕ} {a : ℕ} (ha : 0 < a)
    (happrox : IsStrictPolyTimeMinApprox encB opt alg (((a + 1 : ℕ) : ℝ) / (a : ℝ))) :
    PromiseProblem.gapMin (fun b ↦ (opt b : ℝ)) (fun _ ↦ (a : ℝ))
      (fun _ ↦ ((a + 1 : ℕ) : ℝ)) ∈ PromiseP encB := by
  have halg : ComputableInPolyTime alg encB encNat := happrox.1
  have hdec : ComputableInPolyTime (fun b ↦ decide (alg b ≤ a)) encB encBool := by fun_prop
  refine mem_PromiseP_iff.mpr ⟨fun b ↦ decide (alg b ≤ a), hdec, fun b hyes ↦ ?_, fun b hno ↦ ?_⟩
  · simp only [PromiseProblem.mem_yes_gapMin, Nat.cast_le] at hyes
    rw [decide_eq_true_eq]
    rcases Nat.eq_zero_or_pos (opt b) with h0 | hpos
    · have hle0 : (alg b : ℝ) ≤ 0 := by simpa [h0] using (happrox.2 b).2.1
      have heq : alg b = 0 := by exact_mod_cast le_antisymm hle0 (Nat.cast_nonneg _)
      omega
    · have har : (0 : ℝ) < (a : ℝ) := Nat.cast_pos.mpr ha
      have hlt : (alg b : ℝ) < ((a + 1 : ℕ) : ℝ) :=
        calc (alg b : ℝ) < (((a + 1 : ℕ) : ℝ) / (a : ℝ)) * (opt b : ℝ) := (happrox.2 b).2.2 hpos
          _ ≤ (((a + 1 : ℕ) : ℝ) / (a : ℝ)) * (a : ℝ) :=
              mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hyes) (by positivity)
          _ = ((a + 1 : ℕ) : ℝ) := div_mul_cancel₀ _ har.ne'
      exact Nat.lt_succ_iff.mp (by exact_mod_cast hlt)
  · simp only [PromiseProblem.mem_no_gapMin, Nat.cast_le] at hno
    rw [decide_eq_false_iff_not]
    have h1 := hno.1
    have h2 := (happrox.2 b).1
    omega

/-- If `PromiseProblem.gapMin opt a (a + 1)` (`0 < a`) is `NP`-hard, any polynomial-time
`c`-approximation with `c < (a + 1) / a` implies `P = NP`. -/
theorem pEqNP_of_isPolyTimeMinApprox_of_gap_reduction {β : Type} {encB : β ↪ List Bool}
    {opt alg : β → ℕ} {a : ℕ} (ha : 0 < a)
    (hGap : PromiseProblem.NPHard encB
      (PromiseProblem.gapMin (fun b ↦ (opt b : ℝ)) (fun _ ↦ (a : ℝ))
        (fun _ ↦ ((a + 1 : ℕ) : ℝ))))
    {c : ℝ} (hc : c < ((a + 1 : ℕ) : ℝ) / (a : ℝ))
    (happrox : IsPolyTimeMinApprox encB opt alg c) : PEqNP :=
  fun enc ↦ hGap.P_eq_NP_of_mem_PromiseP
    (gapMin_mem_PromiseP_of_isPolyTimeMinApprox ha hc happrox) enc

/-- Contrapositive inapproximability: if `gapMin opt a (a + 1)` (`0 < a`) is `NP`-hard and
`¬ PEqNP`, then no polynomial-time algorithm approximates `opt` within any factor
`c < (a + 1) / a`. -/
theorem not_isPolyTimeMinApprox_of_gap_reduction {β : Type} {encB : β ↪ List Bool}
    {opt alg : β → ℕ} {a : ℕ} (ha : 0 < a)
    (hGap : PromiseProblem.NPHard encB
      (PromiseProblem.gapMin (fun b ↦ (opt b : ℝ)) (fun _ ↦ (a : ℝ))
        (fun _ ↦ ((a + 1 : ℕ) : ℝ))))
    {c : ℝ} (hc : c < ((a + 1 : ℕ) : ℝ) / (a : ℝ)) (hne : ¬ PEqNP) :
    ¬ IsPolyTimeMinApprox encB opt alg c :=
  fun happrox ↦ hne (pEqNP_of_isPolyTimeMinApprox_of_gap_reduction ha hGap hc happrox)

/-- If `PromiseProblem.gapMin opt a (a + 1)` (`0 < a`) is `NP`-hard, any strict polynomial-time
`((a + 1) / a)`-approximation implies `P = NP`. -/
theorem pEqNP_of_isStrictPolyTimeMinApprox_of_gap_reduction {β : Type} {encB : β ↪ List Bool}
    {opt alg : β → ℕ} {a : ℕ} (ha : 0 < a)
    (hGap : PromiseProblem.NPHard encB
      (PromiseProblem.gapMin (fun b ↦ (opt b : ℝ)) (fun _ ↦ (a : ℝ))
        (fun _ ↦ ((a + 1 : ℕ) : ℝ))))
    (happrox : IsStrictPolyTimeMinApprox encB opt alg (((a + 1 : ℕ) : ℝ) / (a : ℝ))) : PEqNP :=
  fun enc ↦ hGap.P_eq_NP_of_mem_PromiseP
    (gapMin_mem_PromiseP_of_isStrictPolyTimeMinApprox ha happrox) enc

/-- Contrapositive strict inapproximability at the exact boundary `(a + 1) / a`. -/
theorem not_isStrictPolyTimeMinApprox_of_gap_reduction {β : Type} {encB : β ↪ List Bool}
    {opt alg : β → ℕ} {a : ℕ} (ha : 0 < a)
    (hGap : PromiseProblem.NPHard encB
      (PromiseProblem.gapMin (fun b ↦ (opt b : ℝ)) (fun _ ↦ (a : ℝ))
        (fun _ ↦ ((a + 1 : ℕ) : ℝ))))
    (hne : ¬ PEqNP) :
    ¬ IsStrictPolyTimeMinApprox encB opt alg (((a + 1 : ℕ) : ℝ) / (a : ℝ)) :=
  fun happrox ↦ hne (pEqNP_of_isStrictPolyTimeMinApprox_of_gap_reduction ha hGap happrox)

/-! ### Internal non-vacuity and sharpness checks -/

/-- Canonical benchmark: `ChromaticNumber` parameterized by
the number of colors `k` is `para-NP`-complete (its `k = 3` slice is `3`-Coloring).
-/
private theorem chromaticNumber_paraNPComplete :
    ParaNPComplete encChromaticNumber ChromaticNumberInstance.colors ChromaticNumber :=
  ⟨NP_subset_ParaNP ChromaticNumber.mem_NP,
    ParaNPHard.of_const_param_reduction ThreeColoring_npHard (f := fun G ↦ ⟨G, 3⟩) (k := 3)
      (by fun_prop) (fun _ ↦ rfl) fun _ ↦ Iff.rfl⟩

/-- Boundary sharpness: for every `a > 0`, a non-strict `((a + 1) / a)`-approximation need not
satisfy `IsStrictPolyTimeMinApprox` and need not separate `opt = a` from `opt = a + 1`. -/
private theorem nonStrict_boundary_sharpness {a : ℕ} (ha : 0 < a) :
    let opt : List Bool → ℕ := fun w ↦ if w.headD false then a else a + 1
    let alg : List Bool → ℕ := fun _ ↦ a + 1
    IsPolyTimeMinApprox encBits opt alg (((a + 1 : ℕ) : ℝ) / (a : ℝ)) ∧
      ¬ IsStrictPolyTimeMinApprox encBits opt alg (((a + 1 : ℕ) : ℝ) / (a : ℝ)) := by
  intro opt alg
  have har : (0 : ℝ) < (a : ℝ) := Nat.cast_pos.mpr ha
  refine ⟨⟨ComputableInPolyTime.const (a + 1), fun w ↦ ⟨?_, ?_⟩⟩, fun hs ↦ ?_⟩
  · dsimp only [opt, alg]; split_ifs <;> omega
  · dsimp only [opt, alg]
    split_ifs
    · rw [div_mul_cancel₀ _ har.ne']
    · have h1 : (1 : ℝ) ≤ ((a + 1 : ℕ) : ℝ) / (a : ℝ) :=
        (one_le_div har).mpr (by exact_mod_cast Nat.le_succ a)
      simpa using mul_le_mul_of_nonneg_right h1 (Nat.cast_nonneg (a + 1))
  · have hlt := (hs.2 [true]).2.2 (by simpa [opt] using ha)
    simp only [opt, alg, List.headD_cons, ↓reduceIte, div_mul_cancel₀ _ har.ne'] at hlt
    exact lt_irrefl _ hlt

end CslibFrontier.Complexity
