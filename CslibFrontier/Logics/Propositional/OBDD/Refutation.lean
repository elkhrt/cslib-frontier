module

public import CslibFrontier.Logics.Propositional.CNF
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import CslibFrontier.Computability.BranchingProgram.OBDD
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Basic

/-!
# OBDD Refutations and CNF Size Lower Bounds

Ordered binary decision diagram (OBDD) refutation systems for propositional formulas in conjunctive
normal form (CNF) built on `Cslib.Logic.PL.CNF` and `CslibFrontier.BranchingPrograms.OBDD`,
including a fooling-set internal-size lower bound for CNFs and completeness of OBDD refutations for
unsatisfiable nonempty CNFs over finite variable sets.

## Main definitions

* `CslibFrontier.Logic.PL.OBDD.OBDDRefutation`: OBDD refutation of a CNF formula using the axiom
  and join (conjunction) rules.
* `CslibFrontier.Logic.PL.OBDD.OBDDRefutation.size`: sum of internal sizes of all OBDDs in a
  refutation.
* `CslibFrontier.Logic.PL.OBDD.OBDDRefutation.ofUnsat`: construction of a valid OBDD refutation for
  any unsatisfiable nonempty CNF on a finite linearly ordered variable type.

## Main results

* `CslibFrontier.Logic.PL.OBDD.bddSize_lower_bound`: fooling-set internal-node lower bound
  `2 ^ A.card ≤ B.internalSize` for any OBDD representing a CNF formula whenever `2 ≤ A.card`.
-/

public section

namespace CslibFrontier.Logic.PL.OBDD

open CslibFrontier.BranchingPrograms

open Cslib.BranchingPrograms Cslib.Logic.PL

/-! ### Fooling-set OBDD size lower bound for CNFs -/

/-- **CNF OBDD size lower bound**:
Let `φ` be a CNF formula over variables `V` ordered by `ord`, `S_k` a downward-closed prefix of
`Var(φ)` (the `|S_k|` smallest variables of `Var(φ)` under `ord`), `A ⊆ S_k` with `2 ≤ |A|`, and
`z` a fixed assignment. If every pair of distinct assignments to `S_k` agreeing with `z` outside
`A` can be distinguished by some assignment outside `S_k`, then every reduced OBDD representing
`φ` under `ord` has at least `2 ^ |A|` internal nodes. -/
theorem bddSize_lower_bound {V : Type*} [DecidableEq V] (ord : LinearOrder V)
    (φ : CNF V) (B : OBDD ord) (hrep : ∀ σ, B.eval σ = φ.eval σ)
    {S_k A : Finset V}
    (hk_sub : S_k ⊆ φ.vars.toFinset)
    (hk_small : ∀ u ∈ S_k, ∀ w ∈ φ.vars.toFinset, ord.lt w u → w ∈ S_k)
    (hAS : A ⊆ S_k)
    (hA : 2 ≤ A.card)
    (z : V → Bool)
    (hfool : ∀ x₁ x₂ : V → Bool,
      (∀ v ∈ S_k, v ∉ A → x₁ v = z v) →
      (∀ v ∈ S_k, v ∉ A → x₂ v = z v) →
      (∃ v ∈ A, x₁ v ≠ x₂ v) →
      ∃ y : V → Bool,
        φ.eval (fun v => if v ∈ S_k then x₁ v else y v) ≠
          φ.eval (fun v => if v ∈ S_k then x₂ v else y v)) :
    2 ^ A.card ≤ B.internalSize := by
  classical
  let := ord
  let bpVars : Finset V :=
    Finset.univ.biUnion fun u : Fin B.toBranchingProgram.size =>
      match bpStepAt B.toBranchingProgram u with
      | .sink _ => ∅
      | .branch v _ => {v}
  let U : Finset V := φ.vars.toFinset ∪ bpVars
  let S : Finset V := U.filter fun v => ∃ u ∈ S_k, v ≤ u
  have hS_inter : ∀ v ∈ φ.vars.toFinset, v ∈ S ↔ v ∈ S_k := by
    intro v hv
    simp only [S, Finset.mem_filter, Finset.mem_union, U, hv, true_or, true_and]
    constructor
    · rintro ⟨u, hu, hvu⟩
      rcases lt_or_eq_of_le hvu with hlt | rfl
      · exact hk_small u hu v hv hlt
      · exact hu
    · intro hvS
      exact ⟨v, hvS, le_refl v⟩
  let ordU : LinearOrder U := LinearOrder.lift' Subtype.val Subtype.val_injective
  let stepFnU : (m : ℕ) → m < B.toBranchingProgram.size → BranchingProgram.Step U Bool (Fin m) :=
    fun m hm =>
      match h : bpStepAt B.toBranchingProgram ⟨m, hm⟩ with
      | .sink b => .sink b
      | .branch v next =>
        .branch ⟨v, Finset.mem_union_right _ (Finset.mem_biUnion.2
          ⟨⟨m, hm⟩, Finset.mem_univ _, by simp [h]⟩)⟩
          (fun b => ⟨(next b).val, bpStepAt_branch_lt B.toBranchingProgram ⟨m, hm⟩ h b⟩)
  let PU : BranchingProgram U Bool :=
    { nodes := BranchingProgram.Nodes.ofFn stepFnU
      start := B.toBranchingProgram.start }
  have hstepU : ∀ u : Fin B.toBranchingProgram.size,
      (∀ b, bpStepAt B.toBranchingProgram u = .sink b → bpStepAt PU u = .sink b) ∧
      (∀ v next (hv : v ∈ U), bpStepAt B.toBranchingProgram u = .branch v next →
        bpStepAt PU u = .branch ⟨v, hv⟩ next) := by
    intro u
    have hu_eq : bpStepAt PU u = stepMap (Fin.castLE u.isLt.le) (stepFnU u.val u.isLt) := by
      simpa [PU] using nodesStepAt_ofFn stepFnU u.val u.isLt
    constructor
    · intro b hb
      rw [hu_eq]
      unfold stepFnU
      split <;> rename_i hs
      · rw [hb] at hs; cases hs; exact stepMap_sink _ _
      · rw [hb] at hs; cases hs
    · intro v next hv hbr
      rw [hu_eq]
      unfold stepFnU
      split <;> rename_i hs
      · rw [hbr] at hs; cases hs
      · rw [hbr] at hs
        simp only [BranchingProgram.Step.branch.injEq] at hs
        obtain ⟨rfl, rfl⟩ := hs
        simp only [stepMap_branch, BranchingProgram.Step.branch.injEq, true_and]
        funext b; ext; rfl
  have hBU_eval : ∀ (τ : V → Bool),
      ∀ (m : ℕ) (u : Fin B.toBranchingProgram.size), u.val ≤ m →
        PU.nodes.eval (fun x => τ x.val) u = B.toBranchingProgram.nodes.eval τ u := by
    intro τ m
    induction m with
    | zero =>
      intro u hu
      cases hs : bpStepAt B.toBranchingProgram u with
      | sink b =>
        rw [eval_eq_of_bpStepAt_sink PU _ _ ((hstepU u).1 b hs),
          eval_eq_of_bpStepAt_sink B.toBranchingProgram _ _ hs]
      | branch v next =>
        have hlt := bpStepAt_branch_lt B.toBranchingProgram u hs false
        have : (next false).val < 0 := lt_of_lt_of_le hlt hu
        exact absurd this (Nat.not_lt_zero _)
    | succ m ih =>
      intro u hu
      cases hs : bpStepAt B.toBranchingProgram u with
      | sink b =>
        rw [eval_eq_of_bpStepAt_sink PU _ _ ((hstepU u).1 b hs),
          eval_eq_of_bpStepAt_sink B.toBranchingProgram _ _ hs]
      | branch v next =>
        have hvU : v ∈ U := Finset.mem_union_right _ (Finset.mem_biUnion.2
          ⟨u, Finset.mem_univ _, by simp [hs]⟩)
        rw [eval_eq_of_bpStepAt_branch PU _ _ ((hstepU u).2 v next hvU hs),
          eval_eq_of_bpStepAt_branch B.toBranchingProgram _ _ hs]
        exact ih (next (τ v)) (by
          have hlt := bpStepAt_branch_lt B.toBranchingProgram u hs (τ v)
          omega)
  let BU : OBDD ordU :=
    { toBranchingProgram := PU
      ordered := (isOrdered_iff ordU PU).2 fun u v next b v' next' h1 h2 => by
        cases hs1 : bpStepAt B.toBranchingProgram u with
        | sink _ => rw [(hstepU u).1 _ hs1] at h1; cases h1
        | branch v₁ n₁ =>
          have hv₁ : v₁ ∈ U := Finset.mem_union_right _ (Finset.mem_biUnion.2
            ⟨u, Finset.mem_univ _, by simp [hs1]⟩)
          rw [(hstepU u).2 v₁ n₁ hv₁ hs1] at h1
          simp only [BranchingProgram.Step.branch.injEq] at h1
          obtain ⟨rfl, rfl⟩ := h1
          cases hs2 : bpStepAt B.toBranchingProgram (n₁ b) with
          | sink _ => rw [(hstepU (n₁ b)).1 _ hs2] at h2; cases h2
          | branch v₂ n₂ =>
            have hv₂ : v₂ ∈ U := Finset.mem_union_right _ (Finset.mem_biUnion.2
              ⟨n₁ b, Finset.mem_univ _, by simp [hs2]⟩)
            rw [(hstepU (n₁ b)).2 v₂ n₂ hv₂ hs2] at h2
            simp only [BranchingProgram.Step.branch.injEq] at h2
            obtain ⟨rfl, _⟩ := h2
            exact (isOrdered_iff ord _).1 B.ordered u v₁ n₁ b v₂ n₂ hs1 hs2
      reduced := (isReduced_iff PU).2 ⟨by
        intro u₁ u₂ heq
        apply ((isReduced_iff _).1 B.reduced).1
        cases hs1 : bpStepAt B.toBranchingProgram u₁ with
        | sink b₁ =>
          cases hs2 : bpStepAt B.toBranchingProgram u₂ with
          | sink b₂ =>
            rw [(hstepU u₁).1 b₁ hs1, (hstepU u₂).1 b₂ hs2] at heq
            cases heq; rfl
          | branch v₂ n₂ =>
            have hv₂ : v₂ ∈ U := Finset.mem_union_right _ (Finset.mem_biUnion.2
              ⟨u₂, Finset.mem_univ _, by simp [hs2]⟩)
            rw [(hstepU u₁).1 b₁ hs1, (hstepU u₂).2 v₂ n₂ hv₂ hs2] at heq; cases heq
        | branch v₁ n₁ =>
          have hv₁ : v₁ ∈ U := Finset.mem_union_right _ (Finset.mem_biUnion.2
            ⟨u₁, Finset.mem_univ _, by simp [hs1]⟩)
          cases hs2 : bpStepAt B.toBranchingProgram u₂ with
          | sink b₂ =>
            rw [(hstepU u₁).2 v₁ n₁ hv₁ hs1, (hstepU u₂).1 b₂ hs2] at heq; cases heq
          | branch v₂ n₂ =>
            have hv₂ : v₂ ∈ U := Finset.mem_union_right _ (Finset.mem_biUnion.2
              ⟨u₂, Finset.mem_univ _, by simp [hs2]⟩)
            rw [(hstepU u₁).2 v₁ n₁ hv₁ hs1, (hstepU u₂).2 v₂ n₂ hv₂ hs2] at heq
            simp only [BranchingProgram.Step.branch.injEq, Subtype.mk.injEq] at heq
            obtain ⟨rfl, rfl⟩ := heq; rfl, by
        intro u v next h1
        cases hs1 : bpStepAt B.toBranchingProgram u with
        | sink _ => rw [(hstepU u).1 _ hs1] at h1; cases h1
        | branch v₁ n₁ =>
          have hv₁ : v₁ ∈ U := Finset.mem_union_right _ (Finset.mem_biUnion.2
            ⟨u, Finset.mem_univ _, by simp [hs1]⟩)
          rw [(hstepU u).2 v₁ n₁ hv₁ hs1] at h1
          simp only [BranchingProgram.Step.branch.injEq] at h1
          obtain ⟨rfl, rfl⟩ := h1
          exact ((isReduced_iff _).1 B.reduced).2 u v₁ n₁ hs1⟩ }
  have hint_eq : BU.internalSize = B.internalSize := by
    rw [OBDD.internalSize_eq, OBDD.internalSize_eq]
    change (Finset.univ.filter (fun u : Fin B.toBranchingProgram.size =>
        isInternalNode PU u)).card =
      (Finset.univ.filter (fun u : Fin B.toBranchingProgram.size =>
        isInternalNode B.toBranchingProgram u)).card
    apply congrArg Finset.card
    ext u
    rw [Finset.mem_filter, Finset.mem_filter]
    simp only [Finset.mem_univ, true_and, isInternalNode_iff]
    constructor
    · rintro ⟨v, next, hv⟩
      cases hs : bpStepAt B.toBranchingProgram u with
      | sink b => rw [(hstepU u).1 b hs] at hv; cases hv
      | branch v₁ n₁ => exact ⟨v₁, n₁, rfl⟩
    · rintro ⟨v, next, hv⟩
      have hvU : v ∈ U := Finset.mem_union_right _ (Finset.mem_biUnion.2
        ⟨u, Finset.mem_univ _, by simp [hv]⟩)
      exact ⟨⟨v, hvU⟩, next, (hstepU u).2 v next hvU hv⟩
  let SU : Finset U := Finset.univ.filter fun x => x.val ∈ S
  let AU : Finset U := Finset.univ.filter fun x => x.val ∈ A
  have hAU_card : AU.card = A.card := by
    have hbij : AU.image Subtype.val = A := by
      ext v
      simp only [AU, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Subtype.exists]
      exact ⟨fun ⟨_, _, hvA, heq⟩ => heq ▸ hvA,
        fun hvA => ⟨v, Finset.mem_union_left _ (hk_sub (hAS hvA)), hvA, rfl⟩⟩
    rw [← hbij, Finset.card_image_of_injective _ Subtype.val_injective]
  rw [← hint_eq, ← hAU_card]
  refine OBDD.two_pow_le_internalSize BU (S := SU) (A := AU) ?_ (by omega)
    (fun x => z x.val) ?_
  · intro u hu w hlt
    simp only [SU, Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
    obtain ⟨_, v₀, hv₀, huv₀⟩ := Finset.mem_filter.1 hu
    exact Finset.mem_filter.2 ⟨w.2, v₀, hv₀, le_trans (le_of_lt hlt) huv₀⟩
  · intro x₁ x₂ hx₁ hx₂ hdiff
    let liftX : (U → Bool) → (V → Bool) := fun f v => if hv : v ∈ U then f ⟨v, hv⟩ else z v
    have hx₁' : ∀ v ∈ S_k, v ∉ A → liftX x₁ v = z v := by
      intro v hvS hvA
      have hvU : v ∈ U := Finset.mem_union_left _ (hk_sub hvS)
      simp only [liftX, hvU, dite_true]
      exact hx₁ ⟨v, hvU⟩ (by simp [AU, hvA])
    have hx₂' : ∀ v ∈ S_k, v ∉ A → liftX x₂ v = z v := by
      intro v hvS hvA
      have hvU : v ∈ U := Finset.mem_union_left _ (hk_sub hvS)
      simp only [liftX, hvU, dite_true]
      exact hx₂ ⟨v, hvU⟩ (by simp [AU, hvA])
    have hdiff' : ∃ v ∈ A, liftX x₁ v ≠ liftX x₂ v := by
      obtain ⟨x, hxA, hne⟩ := hdiff
      have hvA : x.val ∈ A := by simpa [AU] using hxA
      exact ⟨x.val, hvA, by simpa [liftX, x.2] using hne⟩
    obtain ⟨y, hy⟩ := hfool (liftX x₁) (liftX x₂) hx₁' hx₂' hdiff'
    refine ⟨fun u => y u.val, ?_⟩
    have hev : ∀ (x : U → Bool),
        BU.eval (fun u => if u ∈ SU then x u else y u.val) =
          φ.eval (fun v => if v ∈ S_k then liftX x v else y v) := by
      intro x
      let σ : V → Bool := fun v => if v ∈ S then liftX x v else y v
      have h1 : (fun u : U => if u ∈ SU then x u else y u.val) = (fun u : U => σ u.val) := by
        funext u
        simp only [σ, SU, Finset.mem_filter, Finset.mem_univ, true_and, liftX, u.2, dite_true]
      rw [h1]
      have h2 : BU.eval (fun u : U => σ u.val) = B.eval σ := by
        rw [OBDD.eval_eq, OBDD.eval_eq]
        exact hBU_eval σ B.toBranchingProgram.size B.toBranchingProgram.start
          (Nat.le_of_lt B.toBranchingProgram.start.isLt)
      rw [h2, hrep σ]
      refine CNF.eval_congr fun v hv => ?_
      have hv' : v ∈ φ.vars.toFinset := List.mem_toFinset.2 hv
      simp only [σ, hS_inter v hv']
    rw [hev x₁, hev x₂]
    exact hy

/-! ### OBDD refutations -/

/-- An **OBDD refutation** of a CNF formula `φ` under variable order `ord`:
Given a total variable ordering `ord` on `V` and a CNF formula `φ`, an OBDD refutation of `φ` is a
nonempty sequence of reduced OBDDs `B₁(φ₁, ord), ..., B_l(φ_l, ord)` representing sub-CNFs
`φ₁, ..., φ_l` such that `B_l` represents constant `false` and each step `i` is either:
* **(Axiom)**: `φ_i = [c]` for some clause `c ∈ φ`; or
* **(Join)**: `φ_i` has clause set equal to the union of `φ_{i'}` and `φ_{i''}` for earlier
  steps `i', i'' < i`. -/
structure OBDDRefutation {V : Type*} (ord : LinearOrder V) (φ : CNF V) where
  /-- Number of steps `l` in the refutation. -/
  length : ℕ
  /-- The refutation has at least one step. -/
  length_pos : 0 < length
  /-- The CNF formula `φ_i` at each step. -/
  formula : Fin length → CNF V
  /-- The reduced OBDD `B_i(φ_i, ord)` at each step. -/
  diagram : Fin length → OBDD ord
  /-- Each OBDD represents its corresponding sub-CNF. -/
  represents : ∀ i σ, (diagram i).eval σ = (formula i).eval σ
  /-- Each step is either an axiom (a single clause of `φ`) or a join of two earlier steps. -/
  step : ∀ i : Fin length,
    (∃ c ∈ φ, formula i = [c]) ∨
      ∃ i' i'' : Fin length, i' < i ∧ i'' < i ∧
        ∀ c, c ∈ formula i ↔ c ∈ formula i' ∨ c ∈ formula i''
  /-- The final OBDD represents the constant `false`. -/
  refutes : ∀ σ, (diagram ⟨length - 1, Nat.sub_lt length_pos Nat.zero_lt_one⟩).eval σ = false

namespace OBDDRefutation

variable {V : Type*} {ord : LinearOrder V} {φ : CNF V}

/-- The clause set `Cls(B_i)` of the `i`-th OBDD in a refutation. -/
def clauses [DecidableEq V] (R : OBDDRefutation ord φ) (i : Fin R.length) : Finset (Clause V) :=
  (R.formula i).toFinset

/-- Membership in `R.clauses i` coincides with membership in `R.formula i`. -/
@[simp]
theorem mem_clauses_iff [DecidableEq V] (R : OBDDRefutation ord φ) (i : Fin R.length)
    (c : Clause V) : c ∈ R.clauses i ↔ c ∈ R.formula i := by
  simp [clauses]

/-- The size of an OBDD refutation, defined as the sum of internal sizes `∑ i, size(B_i)`. -/
def size (R : OBDDRefutation ord φ) : ℕ :=
  ∑ i : Fin R.length, (R.diagram i).internalSize

/-- Any single intermediate OBDD size is bounded above by the total refutation size. -/
theorem internalSize_le_size (R : OBDDRefutation ord φ) (i : Fin R.length) :
    (R.diagram i).internalSize ≤ R.size :=
  Finset.single_le_sum (f := fun j => (R.diagram j).internalSize)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)

/-- Every clause appearing in step `i` of an OBDD refutation of `φ` belongs to `φ`. -/
theorem mem_of_mem_formula (R : OBDDRefutation ord φ) :
    ∀ (i : Fin R.length) {c : Clause V}, c ∈ R.formula i → c ∈ φ := by
  have haux : ∀ (k : ℕ) (i : Fin R.length), i.val ≤ k → ∀ c, c ∈ R.formula i → c ∈ φ := by
    intro k
    induction k with
    | zero =>
      intro i hi c hc
      rcases R.step i with ⟨c', hc', hform⟩ | ⟨i', _, hi', _, _⟩
      · rw [hform] at hc
        simp only [List.mem_singleton] at hc
        exact hc ▸ hc'
      · have : i'.val < 0 := lt_of_lt_of_le hi' hi
        exact absurd this (Nat.not_lt_zero _)
    | succ k ih =>
      intro i hi c hc
      rcases R.step i with ⟨c', hc', hform⟩ | ⟨i', i'', hi', hi'', hunion⟩
      · rw [hform] at hc
        simp only [List.mem_singleton] at hc
        exact hc ▸ hc'
      · rcases (hunion c).1 hc with h1 | h2
        · exact ih i' (by omega) c h1
        · exact ih i'' (by omega) c h2
  intro i c hc
  exact haux R.length i (Nat.le_of_lt i.isLt) c hc

/-- The final formula in an OBDD refutation is unsatisfiable. -/
theorem not_satisfiable_last (R : OBDDRefutation ord φ) :
    ¬ (R.formula ⟨R.length - 1, Nat.sub_lt R.length_pos Nat.zero_lt_one⟩).Satisfiable := by
  rintro ⟨σ, hσ⟩
  have hfalse := R.refutes σ
  rw [R.represents] at hfalse
  rw [hσ] at hfalse
  cases hfalse

/-- Every unsatisfiable nonempty CNF over a finite linearly ordered variable type admits a valid
OBDD refutation (establishing non-vacuity for arbitrary variable orders). -/
noncomputable def ofUnsat [Fintype V] (ord : LinearOrder V) {φ : CNF V}
    (hne : φ ≠ []) (hunsat : ¬ φ.Satisfiable) : OBDDRefutation ord φ := by
  have hlen : 0 < φ.length := List.length_pos_iff.2 hne
  let L : ℕ := 2 * φ.length - 1
  have hL : 0 < L := by omega
  let form : Fin L → CNF V := fun i =>
    if h : i.val < φ.length then [φ[i.val]]
    else φ.take (i.val - φ.length + 2)
  refine
    { length := L
      length_pos := hL
      formula := form
      diagram := fun i => OBDD.ofFun ord (fun σ => (form i).eval σ)
      represents := fun i σ => OBDD.eval_ofFun ord _ σ
      step := ?_
      refutes := ?_ }
  · intro i
    by_cases hi : i.val < φ.length
    · left
      refine ⟨φ[i.val], List.getElem_mem hi, ?_⟩
      simp [form, hi]
    · right
      have hi_ge : φ.length ≤ i.val := Nat.le_of_not_lt hi
      by_cases hfirst : i.val = φ.length
      · have h0 : 0 < L := hL
        have h1 : 1 < φ.length := by omega
        have h1L : 1 < L := by omega
        refine ⟨⟨0, h0⟩, ⟨1, h1L⟩, by exact Fin.mk_lt_mk.2 (by omega),
          by exact Fin.mk_lt_mk.2 (by omega), ?_⟩
        intro c
        simp only [form, hfirst, lt_irrefl, dite_false, Nat.sub_self, Nat.zero_add, hlen, h1,
          dite_true]
        have htake1 : φ.take 1 = [φ[0]] := by
          simpa using List.take_succ_eq_append_getElem hlen
        have htake2 : φ.take 2 = [φ[0], φ[1]] := by
          have := List.take_succ_eq_append_getElem h1
          rw [htake1] at this
          simpa using this
        rw [htake2]
        simp
      · have hprev_lt : i.val - 1 < L := by omega
        have hprev_ge : φ.length ≤ i.val - 1 := by omega
        have hclause_lt : i.val - φ.length + 1 < φ.length := by omega
        have hclause_L : i.val - φ.length + 1 < L := by omega
        refine ⟨⟨i.val - 1, hprev_lt⟩, ⟨i.val - φ.length + 1, hclause_L⟩,
          by exact Fin.mk_lt_mk.2 (by omega), by exact Fin.mk_lt_mk.2 (by omega), ?_⟩
        intro c
        have hnot : ¬ (i.val - 1 < φ.length) := by omega
        simp only [form, hi, hnot, hclause_lt, dite_false, dite_true, List.mem_singleton]
        have hidx : i.val - φ.length + 2 = (i.val - 1 - φ.length + 2) + 1 := by omega
        have htake : φ.take (i.val - φ.length + 2) =
            φ.take (i.val - 1 - φ.length + 2) ++ [φ[i.val - φ.length + 1]] := by
          rw [hidx, List.take_succ_eq_append_getElem (by omega)]
          have heq_idx : i.val - 1 - φ.length + 2 = i.val - φ.length + 1 := by omega
          simp [heq_idx]
        rw [htake, List.mem_append, List.mem_singleton]
  · intro σ
    rw [OBDD.eval_ofFun]
    have hlast_eq : form ⟨L - 1, Nat.sub_lt hL Nat.zero_lt_one⟩ = φ := by
      by_cases h1 : φ.length = 1
      · have hL1 : L - 1 = 0 := by omega
        have hlt : L - 1 < φ.length := by omega
        simp only [form, hlt, dite_true]
        have htake1 : φ.take 1 = [φ[0]] := by
          simpa using List.take_succ_eq_append_getElem hlen
        have hfull : φ.take 1 = φ := by rw [← h1, List.take_length]
        simp [hL1, ← htake1, hfull]
      · have hnot : ¬ (L - 1 < φ.length) := by omega
        simp only [form, hnot, dite_false]
        have heq : L - 1 - φ.length + 2 = φ.length := by omega
        rw [heq, List.take_length]
    rw [hlast_eq]
    cases hev : φ.eval σ with
    | false => rfl
    | true => exact absurd ⟨σ, hev⟩ hunsat

end OBDDRefutation

end CslibFrontier.Logic.PL.OBDD
