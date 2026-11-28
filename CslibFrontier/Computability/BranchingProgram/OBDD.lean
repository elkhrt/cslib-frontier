module

public import CslibFrontier.Computability.BranchingProgram.Basic
public import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sort
import Mathlib.Order.Prod.Lex.Basic
import Mathlib.Tactic.Linarith

/-!
# Ordered Binary Decision Diagrams

Ordered and reduced binary decision diagrams (OBDDs) built on top of
`Cslib.BranchingPrograms.BranchingProgram` over arbitrary variable types equipped with a linear
order, together with a canonical reduced OBDD constructor for Boolean functions on finite variable
types and fooling-set lower bounds on internal and total node counts.

## Main definitions

* `CslibFrontier.BranchingPrograms.OBDD`: reduced ordered binary decision diagram over variables
  `V` with respect to a linear order `ord`.
* `CslibFrontier.BranchingPrograms.OBDD.internalSize`: number of internal (decision) nodes of an
  OBDD.
* `CslibFrontier.BranchingPrograms.OBDD.ofFun`: canonical reduced OBDD representing any Boolean
  function on a finite linearly ordered variable type.

## Main results

* `CslibFrontier.BranchingPrograms.OBDD.two_mul_two_pow_sub_three_le_internalSize`: sharp
  fooling-set lower bound `2 * 2 ^ A.card - 3 ≤ B.internalSize` whenever `1 ≤ A.card`.
* `CslibFrontier.BranchingPrograms.OBDD.two_pow_le_internalSize`: for `2 ≤ A.card`,
  `2 ^ A.card ≤ B.internalSize`.
* `CslibFrontier.BranchingPrograms.OBDD.two_pow_le_totalSize`: for all `A`,
  `2 ^ A.card ≤ B.totalSize`.
-/

public section

namespace CslibFrontier.BranchingPrograms

open Cslib.BranchingPrograms

/-! ### Inspecting nodes of a branching program -/

/-- Map the successor node indices of a branching program step along `f`. -/
def stepMap {ι α Node Node' : Type*} (f : Node → Node') :
    BranchingProgram.Step ι α Node → BranchingProgram.Step ι α Node'
  | .sink b => .sink b
  | .branch i next => .branch i (f ∘ next)

/-- `stepMap` preserves sinks. -/
@[simp] theorem stepMap_sink {ι α Node Node' : Type*} (f : Node → Node') (b : Bool) :
    stepMap (ι := ι) (α := α) f (.sink b) = .sink b := by rfl

/-- `stepMap` maps the successor function of a branch node. -/
@[simp] theorem stepMap_branch {ι α Node Node' : Type*} (f : Node → Node') (i : ι)
    (next : α → Node) :
    stepMap f (.branch i next) = .branch i (f ∘ next) := by rfl

/-- The action performed at node `u` in a topological node sequence, with successors embedded into
`Fin n`. -/
def nodesStepAt {ι α : Type*} :
    {n : ℕ} → BranchingProgram.Nodes ι α n → Fin n → BranchingProgram.Step ι α (Fin n)
  | _, .empty, v => v.elim0
  | _, .node P s, v =>
    Fin.lastCases (stepMap Fin.castSucc s) (fun u => stepMap Fin.castSucc (nodesStepAt P u)) v

/-- The action performed at node `u` of a branching program. -/
def bpStepAt {ι α : Type*} (P : BranchingProgram ι α) (u : Fin P.size) :
    BranchingProgram.Step ι α (Fin P.size) :=
  nodesStepAt P.nodes u

/-- Action at an earlier node in `Nodes.node P s`. -/
@[simp] theorem nodesStepAt_castSucc {ι α : Type*} {n : ℕ} (P : BranchingProgram.Nodes ι α n)
    (s : BranchingProgram.Step ι α (Fin n)) (u : Fin n) :
    nodesStepAt (.node P s) u.castSucc = stepMap Fin.castSucc (nodesStepAt P u) := by
  simp [nodesStepAt]

/-- Action at the last node in `Nodes.node P s`. -/
@[simp] theorem nodesStepAt_last {ι α : Type*} {n : ℕ} (P : BranchingProgram.Nodes ι α n)
    (s : BranchingProgram.Step ι α (Fin n)) :
    nodesStepAt (.node P s) (Fin.last n) = stepMap Fin.castSucc s := by
  simp [nodesStepAt]

/-- Action at a node of a branching program equals `nodesStepAt` of its node sequence. -/
@[simp] theorem bpStepAt_mk {ι α : Type*} {n : ℕ} (nodes : BranchingProgram.Nodes ι α n)
    (start u : Fin n) :
    bpStepAt ⟨nodes, start⟩ u = nodesStepAt nodes u := by rfl

/-- Action at the sole node of a constant branching program. -/
@[simp] theorem bpStepAt_const {ι α : Type*} (b : Bool)
    (u : Fin (BranchingProgram.const ι α b).size) :
    bpStepAt (BranchingProgram.const ι α b) u = .sink b := by
  have hu : u = ⟨0, by simp [BranchingProgram.const]⟩ := by
    ext
    have hlt := u.isLt
    simp only [BranchingProgram.size_const] at hlt
    dsimp only
    omega
  subst hu
  rfl

/-- Evaluating a sink node returns its Boolean constant. -/
theorem eval_eq_of_nodesStepAt_sink {ι α : Type*} :
    ∀ {n : ℕ} (P : BranchingProgram.Nodes ι α n) (x : ι → α) (u : Fin n) {b : Bool},
      nodesStepAt P u = .sink b → P.eval x u = b
  | _, .empty, _, u, _, _ => u.elim0
  | _, .node P s, x, u, b, hu => by
    induction u using Fin.lastCases with
    | last =>
      rw [nodesStepAt_last] at hu
      cases s with
      | sink b' =>
        simp only [stepMap, BranchingProgram.Step.sink.injEq] at hu
        simp [hu]
      | branch _ _ => simp [stepMap] at hu
    | cast v =>
      rw [nodesStepAt_castSucc] at hu
      cases hstep : nodesStepAt P v with
      | sink b' =>
        rw [hstep] at hu
        simp only [stepMap, BranchingProgram.Step.sink.injEq] at hu
        rw [BranchingProgram.Nodes.eval_node_castSucc]
        exact eval_eq_of_nodesStepAt_sink P x v (hu ▸ hstep)
      | branch _ _ =>
        rw [hstep] at hu
        simp [stepMap] at hu

/-- Evaluating a branch node steps to its child indexed by the queried variable. -/
theorem eval_eq_of_nodesStepAt_branch {ι α : Type*} :
    ∀ {n : ℕ} (P : BranchingProgram.Nodes ι α n) (x : ι → α) (u : Fin n) {i : ι}
      {next : α → Fin n}, nodesStepAt P u = .branch i next →
        P.eval x u = P.eval x (next (x i))
  | _, .empty, _, u, _, _, _ => u.elim0
  | _, .node P s, x, u, i, next, hu => by
    induction u using Fin.lastCases with
    | last =>
      rw [nodesStepAt_last] at hu
      cases s with
      | sink _ => simp [stepMap] at hu
      | branch i' next' =>
        simp only [stepMap, BranchingProgram.Step.branch.injEq] at hu
        obtain ⟨rfl, rfl⟩ := hu
        rw [BranchingProgram.Nodes.eval_node_last_branch, Function.comp_apply,
          BranchingProgram.Nodes.eval_node_castSucc]
    | cast v =>
      rw [nodesStepAt_castSucc] at hu
      cases hstep : nodesStepAt P v with
      | sink _ =>
        rw [hstep] at hu
        simp [stepMap] at hu
      | branch i' next' =>
        rw [hstep] at hu
        simp only [stepMap, BranchingProgram.Step.branch.injEq] at hu
        obtain ⟨rfl, rfl⟩ := hu
        rw [BranchingProgram.Nodes.eval_node_castSucc, Function.comp_apply,
          BranchingProgram.Nodes.eval_node_castSucc]
        exact eval_eq_of_nodesStepAt_branch P x v hstep

/-- Every successor of a branch node has strictly smaller topological index. -/
theorem nodesStepAt_branch_lt {ι α : Type*} :
    ∀ {n : ℕ} (P : BranchingProgram.Nodes ι α n) (u : Fin n) {i : ι} {next : α → Fin n},
      nodesStepAt P u = .branch i next → ∀ a, next a < u
  | _, .empty, u, _, _, _, _ => u.elim0
  | _, .node P s, u, i, next, hu, a => by
    induction u using Fin.lastCases with
    | last =>
      rw [nodesStepAt_last] at hu
      cases s with
      | sink _ => simp [stepMap] at hu
      | branch i' next' =>
        simp only [stepMap, BranchingProgram.Step.branch.injEq] at hu
        obtain ⟨rfl, rfl⟩ := hu
        exact Fin.castSucc_lt_last (next' a)
    | cast v =>
      rw [nodesStepAt_castSucc] at hu
      cases hstep : nodesStepAt P v with
      | sink _ =>
        rw [hstep] at hu
        simp [stepMap] at hu
      | branch i' next' =>
        rw [hstep] at hu
        simp only [stepMap, BranchingProgram.Step.branch.injEq] at hu
        obtain ⟨rfl, rfl⟩ := hu
        exact Fin.castSucc_lt_castSucc_iff.2 (nodesStepAt_branch_lt P v hstep a)

/-- Node action at index `k` of `BranchingProgram.Nodes.ofFn f`. -/
theorem nodesStepAt_ofFn {ι α : Type*} :
    ∀ {n : ℕ} (f : (k : ℕ) → k < n → BranchingProgram.Step ι α (Fin k)) (k : ℕ) (hk : k < n),
      nodesStepAt (BranchingProgram.Nodes.ofFn f) ⟨k, hk⟩ =
        stepMap (Fin.castLE hk.le) (f k hk)
  | 0, _, _, hk => absurd hk (Nat.not_lt_zero _)
  | n + 1, f, k, hk => by
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hlt | rfl
    · have hcast : (⟨k, hk⟩ : Fin (n + 1)) = (⟨k, hlt⟩ : Fin n).castSucc := rfl
      rw [BranchingProgram.Nodes.ofFn, hcast, nodesStepAt_castSucc,
        nodesStepAt_ofFn (fun j hj => f j (Nat.lt_succ_of_lt hj)) k hlt]
      cases f k hk <;> rfl
    · have hlast : (⟨k, hk⟩ : Fin (k + 1)) = Fin.last k := rfl
      rw [BranchingProgram.Nodes.ofFn, hlast, nodesStepAt_last]
      cases f k hk <;> rfl

/-- Every successor of a branch node in a branching program has strictly smaller index. -/
theorem bpStepAt_branch_lt {ι α : Type*} (P : BranchingProgram ι α) (u : Fin P.size) {i : ι}
    {next : α → Fin P.size} (h : bpStepAt P u = .branch i next) (a : α) : next a < u :=
  nodesStepAt_branch_lt P.nodes u h a

/-- Evaluating a sink node of a branching program returns its Boolean constant. -/
theorem eval_eq_of_bpStepAt_sink {ι α : Type*} (P : BranchingProgram ι α) (x : ι → α)
    (u : Fin P.size) {b : Bool} (h : bpStepAt P u = .sink b) : P.nodes.eval x u = b :=
  eval_eq_of_nodesStepAt_sink P.nodes x u h

/-- Evaluating a branch node of a branching program steps to its successor. -/
theorem eval_eq_of_bpStepAt_branch {ι α : Type*} (P : BranchingProgram ι α) (x : ι → α)
    (u : Fin P.size) {i : ι} {next : α → Fin P.size} (h : bpStepAt P u = .branch i next) :
    P.nodes.eval x u = P.nodes.eval x (next (x i)) :=
  eval_eq_of_nodesStepAt_branch P.nodes x u h

/-- Predicate asserting that a branching program node is an internal (decision) node. -/
@[expose] def isInternalNode {ι α : Type*} (P : BranchingProgram ι α) (u : Fin P.size) : Prop :=
  ∃ i next, bpStepAt P u = .branch i next

/-- Semantic characterization of `isInternalNode`. -/
theorem isInternalNode_iff {ι α : Type*} (P : BranchingProgram ι α) (u : Fin P.size) :
    isInternalNode P u ↔ ∃ i next, bpStepAt P u = .branch i next := by
  rfl

instance instDecidableIsInternalNode {ι α : Type*} (P : BranchingProgram ι α) (u : Fin P.size) :
    Decidable (isInternalNode P u) :=
  match h : bpStepAt P u with
  | .sink _ => isFalse (by rintro ⟨_, _, h'⟩; rw [h] at h'; cases h')
  | .branch i next => isTrue (show ∃ i next, bpStepAt P u = .branch i next from ⟨i, next, h⟩)

/-- The number of internal (decision) nodes of a branching program. -/
def bpInternalSize {ι α : Type*} (P : BranchingProgram ι α) : ℕ :=
  (Finset.univ.filter (fun u : Fin P.size => isInternalNode P u)).card

/-- Characterization of `bpInternalSize` as the cardinality of the filtered internal nodes. -/
theorem bpInternalSize_eq {ι α : Type*} (P : BranchingProgram ι α) :
    bpInternalSize P = (Finset.univ.filter (fun u : Fin P.size => isInternalNode P u)).card := by
  rfl

/-- A branching program over `V` is *ordered* with respect to `ord` if every edge between decision
nodes strictly increases the queried variable in `ord`. -/
def IsOrdered {V : Type*} (ord : LinearOrder V) (P : BranchingProgram V Bool) : Prop :=
  ∀ u v next b v' next',
    bpStepAt P u = .branch v next →
    bpStepAt P (next b) = .branch v' next' →
    ord.lt v v'

/-- Characterization of `IsOrdered`. -/
theorem isOrdered_iff {V : Type*} (ord : LinearOrder V) (P : BranchingProgram V Bool) :
    IsOrdered ord P ↔
      ∀ u v next b v' next',
        bpStepAt P u = .branch v next →
        bpStepAt P (next b) = .branch v' next' →
        ord.lt v v' :=
  Iff.rfl

/-- A branching program is *reduced* if no two distinct nodes have identical actions (merged
isomorphic subgraphs, in particular at most two terminal nodes `0` and `1`) and no decision node has
equal low and high children. -/
def IsReduced {V : Type*} (P : BranchingProgram V Bool) : Prop :=
  Function.Injective (bpStepAt P) ∧
    ∀ u v next, bpStepAt P u = .branch v next → next false ≠ next true

/-- Characterization of `IsReduced`. -/
theorem isReduced_iff {V : Type*} (P : BranchingProgram V Bool) :
    IsReduced P ↔
      Function.Injective (bpStepAt P) ∧
        ∀ u v next, bpStepAt P u = .branch v next → next false ≠ next true :=
  Iff.rfl

/-! ### Reduced Ordered Binary Decision Diagrams -/

/-- A reduced Ordered Binary Decision Diagram (OBDD) over variables `V` with variable ordering
`ord`, built on `Cslib.BranchingPrograms.BranchingProgram V Bool`. -/
structure OBDD {V : Type*} (ord : LinearOrder V) where
  /-- The underlying deterministic branching program. -/
  toBranchingProgram : BranchingProgram V Bool
  /-- Queries strictly increase along every path with respect to `ord`. -/
  ordered : IsOrdered ord toBranchingProgram
  /-- Isomorphic subgraphs are merged and redundant decision nodes are eliminated. -/
  reduced : IsReduced toBranchingProgram

namespace OBDD

section Basic

variable {V : Type*} {ord : LinearOrder V}

/-- The Boolean function evaluated by an OBDD. -/
def eval (B : OBDD ord) (σ : V → Bool) : Bool :=
  B.toBranchingProgram.eval σ

/-- Evaluating an OBDD coincides with evaluating its underlying branching program. -/
theorem eval_eq (B : OBDD ord) (σ : V → Bool) :
    B.eval σ = B.toBranchingProgram.eval σ := by rfl

/-- The size of an OBDD, defined as its number of internal (decision) nodes. -/
def internalSize (B : OBDD ord) : ℕ :=
  bpInternalSize B.toBranchingProgram

/-- Characterization of `OBDD.internalSize`. -/
theorem internalSize_eq (B : OBDD ord) :
    B.internalSize =
      (Finset.univ.filter (fun u : Fin B.toBranchingProgram.size =>
        isInternalNode B.toBranchingProgram u)).card := by
  rfl

/-- The total number of nodes (internal and terminal) of an OBDD. -/
def totalSize (B : OBDD ord) : ℕ :=
  B.toBranchingProgram.size

/-- Internal node count never exceeds total node count. -/
theorem internalSize_le_totalSize (B : OBDD ord) : B.internalSize ≤ B.totalSize := by
  simpa [internalSize, totalSize, bpInternalSize] using
    (Finset.card_filter_le (s := (Finset.univ : Finset (Fin B.toBranchingProgram.size)))
      (p := fun u => isInternalNode B.toBranchingProgram u))

end Basic

/-! ### Universal canonical construction of a reduced OBDD -/

section OfFun

variable {V : Type*}

private def DependsOn [DecidableEq V] (g : (V → Bool) → Bool) (v : V) : Prop :=
  ∃ σ : V → Bool, g (Function.update σ v false) ≠ g (Function.update σ v true)

private theorem eq_of_not_dependsOn [Finite V] [DecidableEq V] {g : (V → Bool) → Bool}
    (h : ∀ v, ¬ DependsOn g v) (σ τ : V → Bool) : g σ = g τ := by
  let := Fintype.ofFinite V
  have hstep : ∀ (s : Finset V) (σ τ : V → Bool), (∀ v, v ∉ s → σ v = τ v) → g σ = g τ := by
    intro s
    induction s using Finset.induction with
    | empty =>
      intro σ τ hst
      congr 1
      ext v
      exact hst v (by simp)
    | @insert a s ha ih =>
      intro σ τ hst
      have hupd : g (Function.update σ a (τ a)) = g τ := by
        refine ih (Function.update σ a (τ a)) τ (fun v hv => ?_)
        by_cases hva : v = a
        · subst hva; simp
        · simp [Function.update_of_ne hva, hst v (by simp [hv, hva])]
      have ha_eq : g σ = g (Function.update σ a (τ a)) := by
        have hnd : g (Function.update σ a false) = g (Function.update σ a true) := by
          by_contra hne
          exact h a ⟨σ, hne⟩
        cases hσ : σ a <;> cases hτ : τ a
        · rw [← hσ, Function.update_eq_self]
        · calc g σ = g (Function.update σ a false) := by rw [← hσ, Function.update_eq_self]
            _ = g (Function.update σ a true) := hnd
        · calc g σ = g (Function.update σ a true) := by rw [← hσ, Function.update_eq_self]
            _ = g (Function.update σ a false) := hnd.symm
        · rw [← hσ, Function.update_eq_self]
      exact ha_eq.trans hupd
  exact hstep Finset.univ σ τ (by simp)

private theorem not_dependsOn_cofactor_self [DecidableEq V] (g : (V → Bool) → Bool) (v : V)
    (b : Bool) : ¬ DependsOn (fun σ => g (Function.update σ v b)) v := by
  rintro ⟨σ, hne⟩
  simp at hne

private theorem not_dependsOn_cofactor_of_not_dependsOn [DecidableEq V] {g : (V → Bool) → Bool}
    {v w : V} (hvw : w ≠ v) (hw : ¬ DependsOn g w) (b : Bool) :
    ¬ DependsOn (fun σ => g (Function.update σ v b)) w := by
  rintro ⟨σ, hne⟩
  apply hw
  refine ⟨Function.update σ v b, ?_⟩
  simp only [Function.update_comm hvw] at hne
  exact hne

private noncomputable def canonStep [Fintype V] (ord : LinearOrder V) (g : (V → Bool) → Bool) :
    BranchingProgram.Step V Bool ((V → Bool) → Bool) := by
  classical
  exact if h : (Finset.univ.filter (fun v => @DependsOn V ord.toDecidableEq g v)).Nonempty then
    .branch (@Finset.min' V ord _ h)
      (fun b σ => g (@Function.update V _ ord.toDecidableEq σ (@Finset.min' V ord _ h) b))
  else
    .sink (g (fun _ => false))

private noncomputable def canonRank [Fintype V] (ord : LinearOrder V) (g : (V → Bool) → Bool) :
    ℕ := by
  classical
  exact if h : (Finset.univ.filter (fun v => @DependsOn V ord.toDecidableEq g v)).Nonempty then
    (Finset.univ.filter (fun w => ord.le (@Finset.min' V ord _ h) w)).card
  else 0

private theorem canonRank_lt [Fintype V] (ord : LinearOrder V) (g : (V → Bool) → Bool)
    (v : V) (next : Bool → (V → Bool) → Bool) (b : Bool)
    (h : canonStep ord g = .branch v next) :
    canonRank ord (next b) < canonRank ord g := by
  classical
  let := ord
  unfold canonStep at h
  split_ifs at h with hne
  · simp only [BranchingProgram.Step.branch.injEq] at h
    obtain ⟨hv, hnext⟩ := h
    subst hnext
    have hv_min : ∀ w, DependsOn g w → v ≤ w := fun w hw => by
      rw [← hv]
      exact Finset.min'_le _ w (by simp [hw])
    unfold canonRank
    rw [dite_eq_left hne]
    split_ifs with hne'
    · set v' := Finset.min'
        (Finset.univ.filter
          (fun w => DependsOn (fun σ => g (Function.update σ (Finset.min' _ hne) b)) w))
        hne'
      have hv'_dep0 : DependsOn (fun σ => g (Function.update σ (Finset.min' _ hne) b)) v' := by
        simpa [v'] using Finset.min'_mem _ hne'
      have hv'_dep : DependsOn (fun σ => g (Function.update σ v b)) v' := hv ▸ hv'_dep0
      have hv'_ne : v' ≠ v := fun heq => not_dependsOn_cofactor_self g v b (heq ▸ hv'_dep)
      have hv'_dep_g : DependsOn g v' := by
        by_contra hnd
        exact not_dependsOn_cofactor_of_not_dependsOn hv'_ne hnd b hv'_dep
      have hv_lt : v < v' := lt_of_le_of_ne (hv_min v' hv'_dep_g) hv'_ne.symm
      refine Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨fun w hw => ?_, ?_⟩)
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
        rw [hv]
        exact le_trans hv_lt.le hw
      · intro heq
        have hv_mem : v ∈ Finset.univ.filter (fun w => Finset.min' _ hne ≤ w) := by
          simp [hv]
        rw [← heq] at hv_mem
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv_mem
        exact not_lt_of_ge hv_mem hv_lt
    · exact Finset.card_pos.2 ⟨Finset.min' _ hne, by simp⟩

private theorem canonStep_ordered [Fintype V] (ord : LinearOrder V) (g : (V → Bool) → Bool)
    (v : V) (next : Bool → (V → Bool) → Bool) (b : Bool)
    (v' : V) (next' : Bool → (V → Bool) → Bool)
    (h1 : canonStep ord g = .branch v next) (h2 : canonStep ord (next b) = .branch v' next') :
    ord.lt v v' := by
  classical
  let := ord
  unfold canonStep at h1 h2
  split_ifs at h1 with hne1
  · simp only [BranchingProgram.Step.branch.injEq] at h1
    obtain ⟨hv, hnext⟩ := h1
    subst hnext
    split_ifs at h2 with hne2
    · simp only [BranchingProgram.Step.branch.injEq] at h2
      obtain ⟨hv', _⟩ := h2
      have hv'_dep0 : DependsOn (fun σ => g (Function.update σ (Finset.min' _ hne1) b)) v' := by
        have hmem := Finset.min'_mem _ hne2
        rw [hv'] at hmem
        simpa using hmem
      have hv'_dep : DependsOn (fun σ => g (Function.update σ v b)) v' := hv ▸ hv'_dep0
      have hv'_ne : v' ≠ v := fun heq => not_dependsOn_cofactor_self g v b (heq ▸ hv'_dep)
      have hv'_dep_g : DependsOn g v' := by
        by_contra hnd
        exact not_dependsOn_cofactor_of_not_dependsOn hv'_ne hnd b hv'_dep
      have hle : v ≤ v' := by
        rw [← hv]
        exact Finset.min'_le _ v' (by simp [hv'_dep_g])
      exact lt_of_le_of_ne hle hv'_ne.symm

private theorem canonStep_injective [Fintype V] (ord : LinearOrder V) :
    Function.Injective (canonStep ord) := by
  classical
  let := ord
  intro g₁ g₂ heq
  cases h1 : canonStep ord g₁ with
  | sink b =>
    have h2 : canonStep ord g₂ = .sink b := heq.symm.trans h1
    unfold canonStep at h1 h2
    split_ifs at h1 with hne1
    split_ifs at h2 with hne2
    simp only [BranchingProgram.Step.sink.injEq] at h1 h2
    ext σ
    calc g₁ σ = g₁ (fun _ => false) :=
          eq_of_not_dependsOn (fun v hv => hne1 ⟨v, by simp [hv]⟩) _ _
      _ = b := h1
      _ = g₂ (fun _ => false) := h2.symm
      _ = g₂ σ := eq_of_not_dependsOn (fun v hv => hne2 ⟨v, by simp [hv]⟩) _ _
  | branch v next =>
    have h2 : canonStep ord g₂ = .branch v next := heq.symm.trans h1
    unfold canonStep at h1 h2
    split_ifs at h1 with hne1
    simp only [BranchingProgram.Step.branch.injEq] at h1
    obtain ⟨hv1, hnext1⟩ := h1
    subst hnext1
    split_ifs at h2 with hne2
    simp only [BranchingProgram.Step.branch.injEq] at h2
    obtain ⟨hv2, hnext2⟩ := h2
    ext σ
    have hfun := congrArg (fun k => k (σ v) σ) hnext2
    dsimp only at hfun
    rw [hv1, hv2] at hfun
    simpa [Function.update_eq_self] using hfun.symm

private theorem canonStep_nonredundant [Fintype V] (ord : LinearOrder V) (g : (V → Bool) → Bool)
    (v : V) (next : Bool → (V → Bool) → Bool) (h : canonStep ord g = .branch v next) :
    next false ≠ next true := by
  classical
  let := ord
  unfold canonStep at h
  split_ifs at h with hne
  simp only [BranchingProgram.Step.branch.injEq] at h
  obtain ⟨hv, hnext⟩ := h
  subst hnext
  have hv_dep : DependsOn g v := by
    have hmem := Finset.min'_mem _ hne
    rw [hv] at hmem
    simpa using hmem
  obtain ⟨σ, hσ⟩ := hv_dep
  intro heq
  have := congrArg (fun k => k σ) heq
  dsimp only at this
  rw [hv] at this
  exact hσ this

private structure CanonNode (V : Type*) where
  fn : (V → Bool) → Bool

private def canonNodeEquiv (V : Type*) : CanonNode V ≃ ((V → Bool) → Bool) where
  toFun := CanonNode.fn
  invFun := CanonNode.mk
  left_inv _ := rfl
  right_inv _ := rfl

private noncomputable instance instFintypeCanonNode [Fintype V] : Fintype (CanonNode V) := by
  classical
  exact Fintype.ofEquiv ((V → Bool) → Bool) (canonNodeEquiv V).symm

@[instance_reducible]
private noncomputable def canonRankOrder [Fintype V] (ord : LinearOrder V) :
    LinearOrder (CanonNode V) := by
  classical
  exact LinearOrder.lift'
    (fun g => toLex (canonRank ord g.fn, Fintype.equivFin ((V → Bool) → Bool) g.fn))
    (fun a b h => by
      cases a; cases b
      congr 1
      exact (Fintype.equivFin _).injective (congrArg (fun p => (ofLex p).2) h))

private noncomputable def canonIndex [Fintype V] (ord : LinearOrder V) :
    ((V → Bool) → Bool) ≃ Fin (Fintype.card ((V → Bool) → Bool)) := by
  classical
  let := canonRankOrder ord
  have hcard : Fintype.card (CanonNode V) = Fintype.card ((V → Bool) → Bool) :=
    Fintype.card_congr (canonNodeEquiv V)
  exact (canonNodeEquiv V).symm.trans
    (Fintype.orderIsoFinOfCardEq (CanonNode V) hcard).symm.toEquiv

private theorem canonIndex_lt [Fintype V] (ord : LinearOrder V)
    {g₁ g₂ : (V → Bool) → Bool} (h : canonRank ord g₁ < canonRank ord g₂) :
    canonIndex ord g₁ < canonIndex ord g₂ := by
  classical
  let := canonRankOrder ord
  have hcard : Fintype.card (CanonNode V) = Fintype.card ((V → Bool) → Bool) :=
    Fintype.card_congr (canonNodeEquiv V)
  have hlt : (⟨g₁⟩ : CanonNode V) < ⟨g₂⟩ := Prod.Lex.toLex_lt_toLex.mpr (Or.inl h)
  exact (Fintype.orderIsoFinOfCardEq (CanonNode V) hcard).symm.strictMono hlt

private noncomputable def canonStepFn [Fintype V] (ord : LinearOrder V)
    (k : ℕ) (hk : k < Fintype.card ((V → Bool) → Bool)) :
    BranchingProgram.Step V Bool (Fin k) := by
  classical
  exact match h : canonStep ord ((canonIndex ord).symm ⟨k, hk⟩) with
  | .sink b => .sink b
  | .branch v next => .branch v fun b =>
    ⟨(canonIndex ord (next b)).val, by
      have hlt := canonIndex_lt ord (canonRank_lt ord _ v next b h)
      rw [Equiv.apply_symm_apply] at hlt
      exact hlt⟩

private noncomputable def canonBP [Fintype V] (ord : LinearOrder V)
    (f : (V → Bool) → Bool) : BranchingProgram V Bool where
  nodes := BranchingProgram.Nodes.ofFn (canonStepFn ord)
  start := canonIndex ord f

private theorem bpStepAt_canonBP [Fintype V] (ord : LinearOrder V) (f : (V → Bool) → Bool)
    (g : (V → Bool) → Bool) :
    bpStepAt (canonBP ord f) (canonIndex ord g) = stepMap (canonIndex ord) (canonStep ord g) := by
  unfold bpStepAt canonBP
  dsimp only
  have hidx : canonIndex ord g = ⟨(canonIndex ord g).val, (canonIndex ord g).isLt⟩ := rfl
  rw [hidx, nodesStepAt_ofFn]
  unfold canonStepFn
  have hsymm : (canonIndex ord).symm ⟨(canonIndex ord g).val, (canonIndex ord g).isLt⟩ = g := by
    simp
  split <;> rename_i hstep
  · rw [hsymm] at hstep
    rw [hstep]; rfl
  · rw [hsymm] at hstep
    rw [hstep]
    simp only [stepMap, BranchingProgram.Step.branch.injEq, true_and]
    funext b
    ext
    rfl

private theorem eval_canonBP_node [Fintype V] (ord : LinearOrder V) (f : (V → Bool) → Bool)
    (σ : V → Bool) (g : (V → Bool) → Bool) :
    (canonBP ord f).nodes.eval σ (canonIndex ord g) = g σ := by
  have haux : ∀ k g, canonRank ord g = k →
      (canonBP ord f).nodes.eval σ (canonIndex ord g) = g σ := by
    intro k
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro g hgk
      have hst := bpStepAt_canonBP ord f g
      cases hcs : canonStep ord g with
      | sink b =>
        rw [hcs] at hst
        rw [eval_eq_of_nodesStepAt_sink _ σ _ hst]
        classical
        let := ord
        unfold canonStep at hcs
        split_ifs at hcs with hne
        simp only [BranchingProgram.Step.sink.injEq] at hcs
        rw [← hcs]
        exact (eq_of_not_dependsOn (fun v hv => hne ⟨v, by simp [hv]⟩) σ (fun _ => false)).symm
      | branch v next =>
        rw [hcs] at hst
        rw [eval_eq_of_nodesStepAt_branch _ σ _ hst]
        simp only [Function.comp_apply]
        have hlt : canonRank ord (next (σ v)) < k :=
          hgk ▸ canonRank_lt ord g v next (σ v) hcs
        rw [ih _ hlt (next (σ v)) rfl]
        classical
        let := ord
        unfold canonStep at hcs
        split_ifs at hcs with hne
        simp only [BranchingProgram.Step.branch.injEq] at hcs
        obtain ⟨hv, hnext⟩ := hcs
        subst hnext
        dsimp only
        rw [hv, Function.update_eq_self]
  exact haux (canonRank ord g) g rfl

/-- Construct a reduced OBDD representing an arbitrary Boolean function `f : (V → Bool) → Bool`
under any variable ordering `ord` on a finite type `V`. -/
noncomputable def ofFun [Fintype V] (ord : LinearOrder V) (f : (V → Bool) → Bool) : OBDD ord where
  toBranchingProgram := canonBP ord f
  ordered := by
    intro u v next b v' next' h1 h2
    obtain ⟨g, rfl⟩ := (canonIndex ord).surjective u
    rw [bpStepAt_canonBP] at h1
    cases hcs : canonStep ord g with
    | sink _ => rw [hcs] at h1; simp [stepMap] at h1
    | branch v₁ n₁ =>
      rw [hcs] at h1
      simp only [stepMap] at h1
      cases h1
      simp only [Function.comp_apply] at h2
      rw [bpStepAt_canonBP] at h2
      cases hcs' : canonStep ord (n₁ b) with
      | sink _ => rw [hcs'] at h2; simp [stepMap] at h2
      | branch v₂ n₂ =>
        rw [hcs'] at h2
        simp only [stepMap] at h2
        cases h2
        exact canonStep_ordered ord g v n₁ b v' n₂ hcs hcs'
  reduced := by
    refine ⟨?_, ?_⟩
    · intro u₁ u₂ heq
      obtain ⟨g₁, rfl⟩ := (canonIndex ord).surjective u₁
      obtain ⟨g₂, rfl⟩ := (canonIndex ord).surjective u₂
      rw [bpStepAt_canonBP, bpStepAt_canonBP] at heq
      have hstep_eq : canonStep ord g₁ = canonStep ord g₂ := by
        cases h1 : canonStep ord g₁ with
        | sink b₁ =>
          cases h2 : canonStep ord g₂ with
          | sink b₂ =>
            rw [h1, h2] at heq
            simp only [stepMap] at heq
            cases heq
            rfl
          | branch _ _ => rw [h1, h2] at heq; simp [stepMap] at heq
        | branch v₁ n₁ =>
          cases h2 : canonStep ord g₂ with
          | sink _ => rw [h1, h2] at heq; simp [stepMap] at heq
          | branch v₂ n₂ =>
            rw [h1, h2] at heq
            simp only [stepMap] at heq
            injection heq with hv hcomp
            subst hv
            congr 1
            funext b
            exact (canonIndex ord).injective (congrFun hcomp b)
      exact congrArg (canonIndex ord) (canonStep_injective ord hstep_eq)
    · intro u v next hu
      obtain ⟨g, rfl⟩ := (canonIndex ord).surjective u
      rw [bpStepAt_canonBP] at hu
      cases hcs : canonStep ord g with
      | sink _ => rw [hcs] at hu; simp [stepMap] at hu
      | branch v₁ n₁ =>
        rw [hcs] at hu
        simp only [stepMap] at hu
        cases hu
        intro heq
        exact canonStep_nonredundant ord g v n₁ hcs ((canonIndex ord).injective heq)

/-- `OBDD.ofFun ord f` evaluates to `f`. -/
@[simp] theorem eval_ofFun [Fintype V] (ord : LinearOrder V) (f : (V → Bool) → Bool)
    (σ : V → Bool) : (ofFun ord f).eval σ = f σ :=
  eval_canonBP_node ord f σ f

end OfFun

/-! ### Fooling-set lower bounds on OBDD size -/

section FoolingSet

variable {V : Type*} {ord : LinearOrder V}

private def prefixTrace [DecidableEq V] (P : BranchingProgram V Bool) (S : Finset V)
    (x : V → Bool) : ℕ → Fin P.size → Fin P.size
  | 0, u => u
  | k + 1, u =>
    match bpStepAt P u with
    | .sink _ => u
    | .branch v next => if v ∈ S then prefixTrace P S x k (next (x v)) else u

private def prefixVisited [DecidableEq V] (P : BranchingProgram V Bool) (S : Finset V)
    (x : V → Bool) : ℕ → Fin P.size → Finset (Fin P.size)
  | 0, _ => ∅
  | k + 1, u =>
    match bpStepAt P u with
    | .sink _ => ∅
    | .branch v next =>
      if v ∈ S then insert u (prefixVisited P S x k (next (x v))) else ∅

private theorem prefixTrace_stops [DecidableEq V] (P : BranchingProgram V Bool) (S : Finset V)
    (x : V → Bool) :
    ∀ (k : ℕ) (u : Fin P.size), u.val ≤ k →
      ∀ v next, bpStepAt P (prefixTrace P S x k u) = .branch v next → v ∉ S
  | 0, u, hu, v, next, hst => by
    have hlt := nodesStepAt_branch_lt P.nodes u hst false
    have : (next false).val < 0 := lt_of_lt_of_le hlt hu
    exact absurd this (Nat.not_lt_zero _)
  | k + 1, u, hu, v, next, hst => by
    unfold prefixTrace at hst
    cases h : bpStepAt P u with
    | sink b =>
      rw [h] at hst
      simp [h] at hst
    | branch v₀ n₀ =>
      rw [h] at hst
      dsimp only at hst
      split_ifs at hst with hv₀
      · have hlt := nodesStepAt_branch_lt P.nodes u h (x v₀)
        exact prefixTrace_stops P S x k (n₀ (x v₀)) (by omega) v next hst
      · rw [h] at hst
        simp only [BranchingProgram.Step.branch.injEq] at hst
        obtain ⟨rfl, _⟩ := hst
        exact hv₀

private theorem eval_eq_eval_prefixTrace [DecidableEq V] (P : BranchingProgram V Bool)
    (S : Finset V) (x y : V → Bool) :
    ∀ (k : ℕ) (u : Fin P.size),
      P.nodes.eval (fun v => if v ∈ S then x v else y v) u =
        P.nodes.eval (fun v => if v ∈ S then x v else y v) (prefixTrace P S x k u)
  | 0, _ => rfl
  | k + 1, u => by
    unfold prefixTrace
    cases h : bpStepAt P u with
    | sink _ => rfl
    | branch v next =>
      dsimp only
      split_ifs with hv
      · have hev := eval_eq_of_nodesStepAt_branch P.nodes
          (fun w => if w ∈ S then x w else y w) u h
        simp only [hv, ite_true] at hev
        exact hev.trans (eval_eq_eval_prefixTrace P S x y k (next (x v)))
      · rfl

private theorem eval_congr_of_stopped {P : BranchingProgram V Bool}
    (hord : IsOrdered ord P) {S : Finset V}
    (hdown : ∀ u ∈ S, ∀ w, ord.lt w u → w ∈ S)
    {σ τ : V → Bool} (hagree : ∀ v, v ∉ S → σ v = τ v) :
    ∀ (k : ℕ) (w : Fin P.size), w.val ≤ k →
      (∀ v next, bpStepAt P w = .branch v next → v ∉ S) →
      P.nodes.eval σ w = P.nodes.eval τ w
  | 0, w, hw, _ => by
    cases h : bpStepAt P w with
    | sink b =>
      rw [eval_eq_of_nodesStepAt_sink _ _ _ h, eval_eq_of_nodesStepAt_sink _ _ _ h]
    | branch v next =>
      have hlt := nodesStepAt_branch_lt P.nodes w h false
      have : (next false).val < 0 := lt_of_lt_of_le hlt hw
      exact absurd this (Nat.not_lt_zero _)
  | k + 1, w, hw, hstop => by
    cases h : bpStepAt P w with
    | sink b =>
      rw [eval_eq_of_nodesStepAt_sink _ _ _ h, eval_eq_of_nodesStepAt_sink _ _ _ h]
    | branch v next =>
      have hv : v ∉ S := hstop v next h
      have hστ : σ v = τ v := hagree v hv
      rw [eval_eq_of_nodesStepAt_branch _ _ _ h, eval_eq_of_nodesStepAt_branch _ _ _ h, hστ]
      have hlt := nodesStepAt_branch_lt P.nodes w h (τ v)
      refine eval_congr_of_stopped hord hdown hagree k (next (τ v)) (by omega) ?_
      intro v' next' h' hv'
      exact hv (hdown v' hv' v (hord w v next (τ v) v' next' h h'))

private theorem mem_prefixVisited_branch [DecidableEq V] (P : BranchingProgram V Bool)
    (S : Finset V) (x : V → Bool) :
    ∀ (k : ℕ) (u w : Fin P.size), w ∈ prefixVisited P S x k u →
      ∃ v next, bpStepAt P w = .branch v next ∧ v ∈ S
  | 0, _, _, hw => by simp [prefixVisited] at hw
  | k + 1, u, w, hw => by
    unfold prefixVisited at hw
    cases h : bpStepAt P u with
    | sink _ => rw [h] at hw; simp at hw
    | branch v next =>
      rw [h] at hw
      dsimp only at hw
      split_ifs at hw with hv
      · rcases Finset.mem_insert.1 hw with rfl | hw'
        · exact ⟨v, next, h, hv⟩
        · exact mem_prefixVisited_branch P S x k (next (x v)) w hw'
      · simp at hw

private theorem mem_prefixVisited_or_trace_pred [DecidableEq V] (P : BranchingProgram V Bool)
    (S : Finset V) (x : V → Bool) :
    ∀ (k : ℕ) (u w : Fin P.size),
      w ∈ prefixVisited P S x k u ∨ w = prefixTrace P S x k u →
      w = u ∨ ∃ p ∈ prefixVisited P S x k u, ∃ v next b,
        bpStepAt P p = .branch v next ∧ next b = w
  | 0, u, w, hw => by
    rcases hw with hw | rfl
    · simp [prefixVisited] at hw
    · exact Or.inl rfl
  | k + 1, u, w, hw => by
    unfold prefixVisited at hw ⊢
    unfold prefixTrace at hw
    cases h : bpStepAt P u with
    | sink _ =>
      rw [h] at hw
      rcases hw with hw | rfl
      · simp at hw
      · exact Or.inl rfl
    | branch v next =>
      rw [h] at hw
      dsimp only at hw ⊢
      split_ifs at hw ⊢ with hv
      · rcases hw with hw | hw
        · rcases Finset.mem_insert.1 hw with rfl | hw'
          · exact Or.inl rfl
          · rcases mem_prefixVisited_or_trace_pred P S x k (next (x v)) w (Or.inl hw') with
              rfl | ⟨p, hp, v', n', b', hstep, hnb⟩
            · exact Or.inr ⟨u, Finset.mem_insert_self _ _, v, next, x v, h, rfl⟩
            · exact Or.inr ⟨p, Finset.mem_insert_of_mem hp, v', n', b', hstep, hnb⟩
        · rcases mem_prefixVisited_or_trace_pred P S x k (next (x v)) w (Or.inr hw) with
            rfl | ⟨p, hp, v', n', b', hstep, hnb⟩
          · exact Or.inr ⟨u, Finset.mem_insert_self _ _, v, next, x v, h, rfl⟩
          · exact Or.inr ⟨p, Finset.mem_insert_of_mem hp, v', n', b', hstep, hnb⟩
      · rcases hw with hw | rfl
        · simp at hw
        · exact Or.inl rfl

private theorem start_mem_prefixVisited_of_ne [DecidableEq V] (P : BranchingProgram V Bool)
    (S : Finset V) (x : V → Bool) (k : ℕ) (hk : 0 < k) (u : Fin P.size)
    (hne : prefixTrace P S x k u ≠ u) :
    u ∈ prefixVisited P S x k u := by
  cases k with
  | zero => omega
  | succ k' =>
    unfold prefixTrace at hne
    unfold prefixVisited
    cases h : bpStepAt P u with
    | sink _ => rw [h] at hne; exact absurd rfl hne
    | branch v next =>
      rw [h] at hne
      dsimp only at hne ⊢
      split_ifs at hne ⊢ with hv
      · exact Finset.mem_insert_self _ _
      · exact absurd rfl hne

/-- Sharp fooling-set lower bound on the number of **internal** nodes of a reduced OBDD:
if `S` is downward-closed in `ord`, `A` is nonempty, and every two distinct assignments to `A`
(extended by `z` outside `A`) can be distinguished by some suffix assignment outside `S`, then
`2 * 2 ^ A.card - 3 ≤ B.internalSize`. -/
theorem two_mul_two_pow_sub_three_le_internalSize [DecidableEq V] (B : OBDD ord)
    {S A : Finset V} (hdown : ∀ u ∈ S, ∀ w, ord.lt w u → w ∈ S)
    (hA : 1 ≤ A.card) (z : V → Bool)
    (hfool : ∀ x₁ x₂ : V → Bool,
      (∀ v, v ∉ A → x₁ v = z v) →
      (∀ v, v ∉ A → x₂ v = z v) →
      (∃ v ∈ A, x₁ v ≠ x₂ v) →
      ∃ y : V → Bool,
        B.eval (fun v => if v ∈ S then x₁ v else y v) ≠
          B.eval (fun v => if v ∈ S then x₂ v else y v)) :
    2 * 2 ^ A.card - 3 ≤ B.internalSize := by
  classical
  let P := B.toBranchingProgram
  let extA : (A → Bool) → (V → Bool) := fun a v => if hv : v ∈ A then a ⟨v, hv⟩ else z v
  let stop : (A → Bool) → Fin P.size := fun a =>
    prefixTrace P S (extA a) P.size P.start
  have hstop_inj : Function.Injective stop := by
    intro a₁ a₂ heq
    by_contra hne
    have hdiff : ∃ v ∈ A, extA a₁ v ≠ extA a₂ v := by
      have : ∃ x : A, a₁ x ≠ a₂ x := by
        by_contra hall
        push Not at hall
        exact hne (funext hall)
      obtain ⟨⟨v, hv⟩, hne'⟩ := this
      exact ⟨v, hv, by simpa [extA, hv] using hne'⟩
    obtain ⟨y, hy⟩ := hfool (extA a₁) (extA a₂)
      (fun v hv => by simp [extA, hv]) (fun v hv => by simp [extA, hv]) hdiff
    apply hy
    have h1 := eval_eq_eval_prefixTrace P S (extA a₁) y P.size P.start
    have h2 := eval_eq_eval_prefixTrace P S (extA a₂) y P.size P.start
    have hstops : ∀ v next, bpStepAt P (stop a₁) = .branch v next → v ∉ S :=
      prefixTrace_stops P S (extA a₁) P.size P.start (Nat.le_of_lt P.start.isLt)
    have hcongr := eval_congr_of_stopped B.ordered hdown
      (σ := fun v => if v ∈ S then extA a₁ v else y v)
      (τ := fun v => if v ∈ S then extA a₂ v else y v)
      (fun v hv => by simp [hv]) P.size (stop a₁) (Nat.le_of_lt (stop a₁).isLt) hstops
    change P.nodes.eval _ P.start = P.nodes.eval _ P.start
    rw [h1, h2]
    change P.nodes.eval _ (stop a₁) = P.nodes.eval _ (stop a₂)
    rw [← heq]
    exact hcongr
  let T : Finset (Fin P.size) := Finset.univ.image stop
  have hT_card : T.card = 2 ^ A.card := by
    rw [Finset.card_image_of_injective _ hstop_inj, Finset.card_univ, Fintype.card_fun]
    simp
  let Ix : Finset (Fin P.size) :=
    Finset.univ.biUnion (fun a : A → Bool => prefixVisited P S (extA a) P.size P.start)
  let Iy : Finset (Fin P.size) := T.filter (fun u => isInternalNode P u)
  let Sinks : Finset (Fin P.size) := T.filter (fun u => ¬ isInternalNode P u)
  have hSinks_le : Sinks.card ≤ 2 := by
    let sinkVal : Fin P.size → Bool := fun u =>
      match bpStepAt P u with
      | .sink b => b
      | .branch _ _ => false
    have hsub : Sinks.image sinkVal ⊆ Finset.univ := Finset.subset_univ _
    have hinj : Set.InjOn sinkVal Sinks := by
      intro u₁ hu₁ u₂ hu₂ heq
      have hns₁ : ¬ isInternalNode P u₁ := (Finset.mem_filter.1 hu₁).2
      have hns₂ : ¬ isInternalNode P u₂ := (Finset.mem_filter.1 hu₂).2
      cases hs₁ : bpStepAt P u₁ with
      | branch v n => exact absurd ⟨v, n, hs₁⟩ hns₁
      | sink b₁ =>
        cases hs₂ : bpStepAt P u₂ with
        | branch v n => exact absurd ⟨v, n, hs₂⟩ hns₂
        | sink b₂ =>
          have hb : b₁ = b₂ := by simpa [sinkVal, hs₁, hs₂] using heq
          exact B.reduced.1 (hs₁.trans (hb ▸ hs₂.symm))
    calc Sinks.card = (Sinks.image sinkVal).card := (Finset.card_image_of_injOn hinj).symm
      _ ≤ (Finset.univ : Finset Bool).card := Finset.card_le_card hsub
      _ = 2 := by decide
  have hIy_ge : 2 ^ A.card - 2 ≤ Iy.card := by
    have hsum : Iy.card + Sinks.card = T.card := by
      simpa [Iy, Sinks] using Finset.card_filter_add_card_filter_not
        (s := T) (p := fun u => isInternalNode P u)
    omega
  have hIx_branch : ∀ u ∈ Ix, ∃ v next, bpStepAt P u = .branch v next ∧ v ∈ S := by
    intro u hu
    obtain ⟨a, _, ha⟩ := Finset.mem_biUnion.1 hu
    exact mem_prefixVisited_branch P S (extA a) P.size P.start u ha
  have hT_stopped : ∀ w ∈ T, ∀ v next, bpStepAt P w = .branch v next → v ∉ S := by
    intro w hw v next hst
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.1 hw
    exact prefixTrace_stops P S (extA a) P.size P.start (Nat.le_of_lt P.start.isLt) v next hst
  have hDisj_Ix_T : Disjoint Ix T := by
    rw [Finset.disjoint_left]
    intro u huIx huT
    obtain ⟨v, next, hst, hvS⟩ := hIx_branch u huIx
    exact hT_stopped u huT v next hst hvS
  have hT_ge_two : 2 ≤ T.card := by
    rw [hT_card]
    have : 2 ^ 1 ≤ 2 ^ A.card := Nat.pow_le_pow_right (by norm_num) hA
    simpa using this
  have hstart_mem_Ix : P.start ∈ Ix := by
    have hex_ne : ∃ a : A → Bool, stop a ≠ P.start := by
      by_contra hall
      push Not at hall
      have hsub : T ⊆ {P.start} := by
        intro w hw
        obtain ⟨a, _, rfl⟩ := Finset.mem_image.1 hw
        exact Finset.mem_singleton.2 (hall a)
      have hle : T.card ≤ 1 := (Finset.card_le_card hsub).trans (by simp)
      omega
    obtain ⟨a, ha_ne⟩ := hex_ne
    have hpos : 0 < P.size := Nat.lt_of_le_of_lt (Nat.zero_le _) P.start.isLt
    exact Finset.mem_biUnion.2 ⟨a, Finset.mem_univ _,
      start_mem_prefixVisited_of_ne P S (extA a) P.size hpos P.start ha_ne⟩
  let childOf : Fin P.size × Bool → Fin P.size := fun p =>
    match bpStepAt P p.1 with
    | .sink _ => p.1
    | .branch _ next => next p.2
  have hcover : (Ix.erase P.start) ∪ T ⊆ (Ix ×ˢ (Finset.univ : Finset Bool)).image childOf := by
    intro w hw
    have hw_ne : w ≠ P.start := by
      rcases Finset.mem_union.1 hw with hw1 | hw2
      · exact (Finset.mem_erase.1 hw1).1
      · intro h; subst h; exact Finset.disjoint_left.1 hDisj_Ix_T hstart_mem_Ix hw2
    have hex_pred : ∃ p ∈ Ix, ∃ v next b, bpStepAt P p = .branch v next ∧ next b = w := by
      rcases Finset.mem_union.1 hw with hw1 | hw2
      · obtain ⟨a, _, ha⟩ := Finset.mem_biUnion.1 (Finset.mem_erase.1 hw1).2
        rcases mem_prefixVisited_or_trace_pred P S (extA a) P.size P.start w (Or.inl ha) with
          rfl | ⟨p, hp, v, next, b, hst, hnb⟩
        · exact absurd rfl hw_ne
        · exact ⟨p, Finset.mem_biUnion.2 ⟨a, Finset.mem_univ _, hp⟩, v, next, b, hst, hnb⟩
      · obtain ⟨a, _, rfl⟩ := Finset.mem_image.1 hw2
        rcases mem_prefixVisited_or_trace_pred P S (extA a) P.size P.start (stop a)
            (Or.inr rfl) with hst | ⟨p, hp, v, next, b, hstep, hnb⟩
        · exact absurd hst hw_ne
        · exact ⟨p, Finset.mem_biUnion.2 ⟨a, Finset.mem_univ _, hp⟩, v, next, b, hstep, hnb⟩
    obtain ⟨p, hp, v, next, b, hstep, hnb⟩ := hex_pred
    refine Finset.mem_image.2 ⟨(p, b), Finset.mem_product.2 ⟨hp, Finset.mem_univ _⟩, ?_⟩
    simpa [childOf, hstep] using hnb
  have hIx_ge : 2 ^ A.card - 1 ≤ Ix.card := by
    have hdisj' : Disjoint (Ix.erase P.start) T :=
      Finset.disjoint_of_subset_left (Finset.erase_subset _ _) hDisj_Ix_T
    have hcard_le : (Ix.erase P.start).card + T.card ≤ 2 * Ix.card := by
      calc (Ix.erase P.start).card + T.card
          = ((Ix.erase P.start) ∪ T).card := (Finset.card_union_of_disjoint hdisj').symm
        _ ≤ ((Ix ×ˢ (Finset.univ : Finset Bool)).image childOf).card :=
            Finset.card_le_card hcover
        _ ≤ (Ix ×ˢ (Finset.univ : Finset Bool)).card := Finset.card_image_le
        _ = Ix.card * 2 := by rw [Finset.card_product]; simp
        _ = 2 * Ix.card := Nat.mul_comm _ _
    have herase : (Ix.erase P.start).card = Ix.card - 1 :=
      Finset.card_erase_of_mem hstart_mem_Ix
    have hIx_pos : 1 ≤ Ix.card := Finset.card_pos.2 ⟨P.start, hstart_mem_Ix⟩
    omega
  have hDisj_Ix_Iy : Disjoint Ix Iy :=
    Finset.disjoint_of_subset_right (Finset.filter_subset _ _) hDisj_Ix_T
  have hsub_int : Ix ∪ Iy ⊆ Finset.univ.filter (fun u => isInternalNode P u) := by
    intro u hu
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
    rcases Finset.mem_union.1 hu with hu1 | hu2
    · obtain ⟨v, next, hst, _⟩ := hIx_branch u hu1
      exact ⟨v, next, hst⟩
    · exact (Finset.mem_filter.1 hu2).2
  have htotal : Ix.card + Iy.card ≤ B.internalSize := by
    calc Ix.card + Iy.card = (Ix ∪ Iy).card := (Finset.card_union_of_disjoint hDisj_Ix_Iy).symm
      _ ≤ (Finset.univ.filter (fun u => isInternalNode P u)).card := Finset.card_le_card hsub_int
      _ = B.internalSize := rfl
  omega

/-- For `2 ≤ A.card`, any reduced OBDD satisfying the fooling-set condition has at least `2 ^ |A|`
internal nodes. -/
theorem two_pow_le_internalSize [DecidableEq V] (B : OBDD ord)
    {S A : Finset V} (hdown : ∀ u ∈ S, ∀ w, ord.lt w u → w ∈ S)
    (hA : 2 ≤ A.card) (z : V → Bool)
    (hfool : ∀ x₁ x₂ : V → Bool,
      (∀ v, v ∉ A → x₁ v = z v) →
      (∀ v, v ∉ A → x₂ v = z v) →
      (∃ v ∈ A, x₁ v ≠ x₂ v) →
      ∃ y : V → Bool,
        B.eval (fun v => if v ∈ S then x₁ v else y v) ≠
          B.eval (fun v => if v ∈ S then x₂ v else y v)) :
    2 ^ A.card ≤ B.internalSize := by
  have hsharp := two_mul_two_pow_sub_three_le_internalSize B hdown (by omega) z hfool
  have hpow : 4 ≤ 2 ^ A.card := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ A.card := Nat.pow_le_pow_right (by norm_num) hA
  omega

/-- For any `A` (including `|A| = 0, 1`), the **total** node count (internal + terminal) of an OBDD
satisfying the fooling-set condition is at least `2 ^ |A|`. -/
theorem two_pow_le_totalSize [DecidableEq V] (B : OBDD ord)
    {S A : Finset V} (hdown : ∀ u ∈ S, ∀ w, ord.lt w u → w ∈ S)
    (z : V → Bool)
    (hfool : ∀ x₁ x₂ : V → Bool,
      (∀ v, v ∉ A → x₁ v = z v) →
      (∀ v, v ∉ A → x₂ v = z v) →
      (∃ v ∈ A, x₁ v ≠ x₂ v) →
      ∃ y : V → Bool,
        B.eval (fun v => if v ∈ S then x₁ v else y v) ≠
          B.eval (fun v => if v ∈ S then x₂ v else y v)) :
    2 ^ A.card ≤ B.totalSize := by
  by_cases hA : 2 ≤ A.card
  · exact (two_pow_le_internalSize B hdown hA z hfool).trans B.internalSize_le_totalSize
  · by_cases hA1 : 1 ≤ A.card
    · classical
      let P := B.toBranchingProgram
      have hcard1 : A.card = 1 := by omega
      obtain ⟨v₀, rfl⟩ := Finset.card_eq_one.1 hcard1
      let x₁ : V → Bool := fun v => if v = v₀ then false else z v
      let x₂ : V → Bool := fun v => if v = v₀ then true else z v
      obtain ⟨y, hy⟩ := hfool x₁ x₂
        (fun v hv => by simp [x₁, show v ≠ v₀ by simpa using hv])
        (fun v hv => by simp [x₂, show v ≠ v₀ by simpa using hv])
        ⟨v₀, Finset.mem_singleton_self _, by simp [x₁, x₂]⟩
      have hnot_le_one : ¬ P.size ≤ 1 := fun hle =>
        hy (BranchingProgram.eval_eq_of_size_le_one P hle _ _)
      change 2 ^ 1 ≤ P.size
      omega
    · have h0 : A.card = 0 := by omega
      rw [h0, pow_zero]
      exact Nat.one_le_of_lt B.toBranchingProgram.start.isLt

end FoolingSet

end OBDD

end CslibFrontier.BranchingPrograms
