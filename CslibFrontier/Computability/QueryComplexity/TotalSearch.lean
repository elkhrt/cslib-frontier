/-
Copyright (c) 2026 Google DeepMind. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Google DeepMind
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.DecisionTree.Composition
public import Mathlib.Data.Nat.Log

/-!
# Black-Box Total Search Complexity Classes $\mathsf{TFNP}^{\mathrm{dt}}$ and
$\mathsf{FP}^{\mathrm{dt}}$

Non-adaptive batch tuple-query decision trees (`queryVec`), closure of polylogarithmic
decision-tree depth bounds under continuation and query substitution, and the black-box total
search complexity classes $\mathsf{TFNP}^{\mathrm{dt}}$ and $\mathsf{FP}^{\mathrm{dt}}$ over
`Cslib.DecisionTree`, together with $\mathsf{FP}^{\mathrm{dt}} \subseteq
\mathsf{TFNP}^{\mathrm{dt}}$ and unconditional separation results on `ℕ`.

## Main definitions

* `Cslib.QueryComplexity.queryVec`: non-adaptive batch decision tree reading `m` specified
  coordinates from a Boolean oracle `ι → Bool` via `Cslib.DecisionTree.seqFin`.
* `Cslib.QueryComplexity.SearchProblem`: indexed black-box Boolean search problem family.
* `Cslib.QueryComplexity.SearchProblem.IsTotal`,
  `Cslib.QueryComplexity.SearchProblem.InTFNPdt`,
  `Cslib.QueryComplexity.SearchProblem.InFPdt`: totality and membership predicates for
  $\mathsf{TFNP}^{\mathrm{dt}}$ and $\mathsf{FP}^{\mathrm{dt}}$.
* `Cslib.QueryComplexity.TFNPdt`, `Cslib.QueryComplexity.FPdt`: the decision-tree total search
  complexity classes as sets of indexed search problems.

## Main results

* `Cslib.QueryComplexity.eval_queryVec`, `Cslib.QueryComplexity.cost_queryVec`,
  `Cslib.QueryComplexity.depth_queryVec`, `Cslib.QueryComplexity.depth_queryVec_le`: exact
  evaluation, path query cost, and depth laws for `queryVec`.
* `Cslib.QueryComplexity.le_mul_log_add_one_pow`,
  `Cslib.QueryComplexity.mul_log_add_one_pow_le_of_le`,
  `Cslib.QueryComplexity.polylog_add_le`, `Cslib.QueryComplexity.polylog_mul_le`,
  `Cslib.QueryComplexity.depth_bind_polylog_le`,
  `Cslib.QueryComplexity.depth_substitute_polylog_le`: closure and monotonicity of
  polylogarithmic bounds under decision-tree continuation and query substitution.
* `Cslib.QueryComplexity.fpdt_subset_tfnpdt`,
  `Cslib.QueryComplexity.SearchProblem.inFPdt_of_verifier_of_solver`: class inclusion
  $\mathsf{FP}^{\mathrm{dt}} \subseteq \mathsf{TFNP}^{\mathrm{dt}}$ and direct membership criterion.
* `Cslib.QueryComplexity.fpdt_nonempty`, `Cslib.QueryComplexity.tfnpdt_nonempty`,
  `Cslib.QueryComplexity.exists_not_isTotal`,
  `Cslib.QueryComplexity.exists_isTotal_not_inTFNPdt`: non-emptiness and unconditional separation
  results on `ℕ`.
-/

public section

namespace Cslib.QueryComplexity

section BatchQuery

variable {ι : Type*}

/-- Non-adaptive tuple batch query decision tree reading `idx 0, ..., idx (m - 1)` in sequence
from a Boolean oracle `x : ι → Bool` and returning `fun k ↦ x (idx k)`. -/
def queryVec (m : ℕ) (idx : Fin m → ι) : Cslib.DecisionTree ι (Fin m → Bool) :=
  Cslib.DecisionTree.seqFin fun k ↦ .node (idx k) (.leaf false) (.leaf true)

/-- Evaluating `queryVec m idx` on oracle `x` returns the tuple `fun k ↦ x (idx k)`. -/
@[simp]
theorem eval_queryVec (m : ℕ) (idx : Fin m → ι) (x : ι → Bool) :
    (queryVec m idx).eval x = fun k ↦ x (idx k) := by
  rw [queryVec, Cslib.DecisionTree.eval_seqFin]
  funext k
  cases hx : x (idx k) <;> simp [hx]

/-- The executed path query cost of `queryVec m idx` on every Boolean oracle `x` is `m`. -/
@[simp]
theorem cost_queryVec (m : ℕ) (idx : Fin m → ι) (x : ι → Bool) :
    (queryVec m idx).cost x = m := by
  rw [queryVec]
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [Cslib.DecisionTree.seqFin, Cslib.DecisionTree.cost,
      Cslib.DecisionTree.weightedCost_bind, Cslib.DecisionTree.weightedCost_leaf, Nat.add_zero]
    have hhead : (Cslib.DecisionTree.node (idx 0) (.leaf false) (.leaf true)).weightedCost
        (fun _ ↦ 1) x = 1 := by
      cases hx : x (idx 0) <;> simp [hx]
    have htail : (Cslib.DecisionTree.seqFin fun j : Fin m ↦
        Cslib.DecisionTree.node (idx j.succ) (.leaf false) (.leaf true)).weightedCost
          (fun _ ↦ 1) x = m :=
      ih (fun j ↦ idx j.succ)
    rw [hhead, htail, Nat.add_comm]

/-- The worst-case depth of `queryVec m idx` is at most `m`. -/
theorem depth_queryVec_le (m : ℕ) (idx : Fin m → ι) :
    (queryVec m idx).depth ≤ m := by
  simpa only [queryVec, Nat.mul_one] using
    Cslib.DecisionTree.depth_seqFin_le
      (fun k ↦ Cslib.DecisionTree.node (idx k) (.leaf false) (.leaf true))
      (d := 1) (fun _ ↦ le_rfl)

/-- The worst-case depth of `queryVec m idx` is exactly `m`. -/
@[simp]
theorem depth_queryVec (m : ℕ) (idx : Fin m → ι) :
    (queryVec m idx).depth = m :=
  le_antisymm (depth_queryVec_le m idx)
    (by simpa only [cost_queryVec] using (queryVec m idx).cost_le_depth (fun _ ↦ false))

end BatchQuery

section PolylogBounds

/-- Multiplying `C` by `(Nat.log 2 N + 1) ^ k ≥ 1` never decreases `C`. -/
theorem le_mul_log_add_one_pow (C N k : ℕ) :
    C ≤ C * (Nat.log 2 N + 1) ^ k :=
  Nat.le_mul_of_pos_right C (Nat.pow_pos (Nat.succ_pos _))

/-- Adding a constant overhead `c` to a polylogarithmic bound `C * (Nat.log 2 N + 1) ^ k` is
absorbed by shifting the leading constant to `c + C`. -/
theorem add_mul_log_add_one_pow_le (c C N k : ℕ) :
    c + C * (Nat.log 2 N + 1) ^ k ≤ (c + C) * (Nat.log 2 N + 1) ^ k := by
  rw [Nat.add_mul]
  exact Nat.add_le_add_right (le_mul_log_add_one_pow c N k) _

/-- The sum of two polylogarithmic bounds at length `N` is bounded by
`(C₁ + C₂) * (Nat.log 2 N + 1) ^ max k₁ k₂`. -/
theorem mul_log_add_one_pow_add_le (C₁ k₁ C₂ k₂ N : ℕ) :
    C₁ * (Nat.log 2 N + 1) ^ k₁ + C₂ * (Nat.log 2 N + 1) ^ k₂ ≤
      (C₁ + C₂) * (Nat.log 2 N + 1) ^ max k₁ k₂ := by
  rw [Nat.add_mul]
  have hpos : 0 < Nat.log 2 N + 1 := Nat.succ_pos _
  exact Nat.add_le_add
    (Nat.mul_le_mul_left C₁ (Nat.pow_le_pow_right hpos (le_max_left k₁ k₂)))
    (Nat.mul_le_mul_left C₂ (Nat.pow_le_pow_right hpos (le_max_right k₁ k₂)))

/-- The product of two polylogarithmic bounds at length `N` multiplies constants and adds
exponents. -/
theorem mul_log_add_one_pow_mul (C₁ k₁ C₂ k₂ N : ℕ) :
    (C₁ * (Nat.log 2 N + 1) ^ k₁) * (C₂ * (Nat.log 2 N + 1) ^ k₂) =
      (C₁ * C₂) * (Nat.log 2 N + 1) ^ (k₁ + k₂) := by
  rw [Nat.pow_add]
  ac_rfl

/-- Monotonicity of polylogarithmic bounds in the input bitstring length `N`. -/
theorem mul_log_add_one_pow_le_of_le (C k : ℕ) {N₁ N₂ : ℕ} (h : N₁ ≤ N₂) :
    C * (Nat.log 2 N₁ + 1) ^ k ≤ C * (Nat.log 2 N₂ + 1) ^ k :=
  Nat.mul_le_mul_left C
    (Nat.pow_le_pow_left (Nat.add_le_add_right (Nat.log_mono_right h) 1) k)

/-- Addition rule for polylogarithmically bounded quantities at length `N`. -/
theorem polylog_add_le {d₁ d₂ C₁ k₁ C₂ k₂ N : ℕ}
    (h₁ : d₁ ≤ C₁ * (Nat.log 2 N + 1) ^ k₁)
    (h₂ : d₂ ≤ C₂ * (Nat.log 2 N + 1) ^ k₂) :
    d₁ + d₂ ≤ (C₁ + C₂) * (Nat.log 2 N + 1) ^ max k₁ k₂ :=
  (Nat.add_le_add h₁ h₂).trans (mul_log_add_one_pow_add_le C₁ k₁ C₂ k₂ N)

/-- Multiplication rule for polylogarithmically bounded quantities at length `N`. -/
theorem polylog_mul_le {d₁ d₂ C₁ k₁ C₂ k₂ N : ℕ}
    (h₁ : d₁ ≤ C₁ * (Nat.log 2 N + 1) ^ k₁)
    (h₂ : d₂ ≤ C₂ * (Nat.log 2 N + 1) ^ k₂) :
    d₁ * d₂ ≤ (C₁ * C₂) * (Nat.log 2 N + 1) ^ (k₁ + k₂) :=
  (Nat.mul_le_mul h₁ h₂).trans_eq (mul_log_add_one_pow_mul C₁ k₁ C₂ k₂ N)

/-- Subadditivity of `Nat.log 2 · + 1` under multiplication. -/
theorem log_mul_add_one_le (a b : ℕ) :
    Nat.log 2 (a * b) + 1 ≤ (Nat.log 2 a + 1) + (Nat.log 2 b + 1) := by
  have ha : a < 2 ^ (Nat.log 2 a + 1) := Nat.lt_pow_succ_log_self (by decide) a
  have hb : b < 2 ^ (Nat.log 2 b + 1) := Nat.lt_pow_succ_log_self (by decide) b
  have hab : a * b < 2 ^ ((Nat.log 2 a + 1) + (Nat.log 2 b + 1)) := by
    rw [Nat.pow_add]
    exact Nat.mul_lt_mul'' ha hb
  exact Nat.log_lt_of_lt_pow' (by omega) hab

/-- Polylogarithmic depth bound for `Cslib.DecisionTree.bind`. -/
theorem depth_bind_polylog_le {ι β γ : Type*}
    (tree : Cslib.DecisionTree ι β) (f : β → Cslib.DecisionTree ι γ) {C₁ k₁ C₂ k₂ N : ℕ}
    (htree : tree.depth ≤ C₁ * (Nat.log 2 N + 1) ^ k₁)
    (hf : ∀ o, (f o).depth ≤ C₂ * (Nat.log 2 N + 1) ^ k₂) :
    (tree.bind f).depth ≤ (C₁ + C₂) * (Nat.log 2 N + 1) ^ max k₁ k₂ :=
  (tree.depth_bind_le f hf).trans (polylog_add_le htree le_rfl)

/-- Polylogarithmic depth bound for Boolean subroutine substitution
`Cslib.DecisionTree.substitute`. -/
theorem depth_substitute_polylog_le {ι κ β : Type*}
    (outer : Cslib.DecisionTree ι β) (sub : ι → Cslib.DecisionTree κ Bool)
    {C₁ k₁ C₂ k₂ N : ℕ}
    (houter : outer.depth ≤ C₁ * (Nat.log 2 N + 1) ^ k₁)
    (hsub : ∀ j, (sub j).depth ≤ C₂ * (Nat.log 2 N + 1) ^ k₂) :
    (outer.substitute sub).depth ≤ (C₁ * C₂) * (Nat.log 2 N + 1) ^ (k₁ + k₂) :=
  ((outer.depth_substitute_le sub).trans (outer.weightedDepth_le_depth_mul hsub)).trans
    (polylog_mul_le houter le_rfl)

end PolylogBounds

section TotalSearchClasses

/-- Indexed black-box Boolean search problem $\mathcal{P} = (N_i, \mathcal{O}_i, R_i)_{i \in \iota}$
assigning to each instance parameter `i : ι` an input bitstring length `inputLen i : ℕ`, a
candidate solution type `Output i`, and a solution set
`solutions i : Set ((Fin (inputLen i) → Bool) × Output i)`. -/
structure SearchProblem (ι : Type*) where
  /-- Input bitstring length $N_i \in \mathbb{N}$ for instance parameter `i : ι`. -/
  inputLen : ι → ℕ
  /-- Candidate solution type $\mathcal{O}_i$ for instance parameter `i : ι`. -/
  Output : ι → Type*
  /-- Solution set $\{(w, o) \mid R_i(w, o)\}$ of valid input-output pairs for parameter `i : ι`. -/
  solutions : (i : ι) → Set ((Fin (inputLen i) → Bool) × Output i)

variable {ι : Type*}

/-- Solution relation $R_i(w, o)$ between input bitstrings `w : Fin (P.inputLen i) → Bool` and
candidate outputs `o : P.Output i`. -/
@[expose] def SearchProblem.Rel (P : SearchProblem ι) (i : ι)
    (w : Fin (P.inputLen i) → Bool) (o : P.Output i) : Prop :=
  (w, o) ∈ P.solutions i

/-- Characterization of `SearchProblem.Rel`. -/
@[simp]
theorem SearchProblem.rel_iff {P : SearchProblem ι} {i : ι}
    {w : Fin (P.inputLen i) → Bool} {o : P.Output i} :
    P.Rel i w o ↔ (w, o) ∈ P.solutions i :=
  Iff.rfl

/-- A black-box search problem `P` is total if every instance `i : ι` and every input bitstring
`w : Fin (P.inputLen i) → Bool` admits at least one valid solution `o : P.Output i`. -/
def SearchProblem.IsTotal (P : SearchProblem ι) : Prop :=
  ∀ (i : ι) (w : Fin (P.inputLen i) → Bool), ∃ o : P.Output i, P.Rel i w o

/-- Characterization of `SearchProblem.IsTotal`. -/
theorem SearchProblem.isTotal_iff {P : SearchProblem ι} :
    P.IsTotal ↔ ∀ (i : ι) (w : Fin (P.inputLen i) → Bool), ∃ o : P.Output i, P.Rel i w o :=
  Iff.rfl

/-- Membership in $\mathsf{TFNP}^{\mathrm{dt}}$: `P` is total and there exist uniform constants
`C, k : ℕ` such that every candidate output `o : P.Output i` has a Boolean verifier decision tree
of depth at most `C * (Nat.log 2 (P.inputLen i) + 1) ^ k` deciding `P.Rel i w o`. -/
def SearchProblem.InTFNPdt (P : SearchProblem ι) : Prop :=
  P.IsTotal ∧
    ∃ C k : ℕ, ∀ (i : ι) (o : P.Output i),
      ∃ V : Cslib.DecisionTree (Fin (P.inputLen i)) Bool,
        V.depth ≤ C * (Nat.log 2 (P.inputLen i) + 1) ^ k ∧
        ∀ w : Fin (P.inputLen i) → Bool, V.eval w = true ↔ P.Rel i w o

/-- Characterization of `SearchProblem.InTFNPdt`. -/
theorem SearchProblem.inTFNPdt_iff {P : SearchProblem ι} :
    P.InTFNPdt ↔
      P.IsTotal ∧
        ∃ C k : ℕ, ∀ (i : ι) (o : P.Output i),
          ∃ V : Cslib.DecisionTree (Fin (P.inputLen i)) Bool,
            V.depth ≤ C * (Nat.log 2 (P.inputLen i) + 1) ^ k ∧
            ∀ w : Fin (P.inputLen i) → Bool, V.eval w = true ↔ P.Rel i w o :=
  Iff.rfl

/-- Every search problem in $\mathsf{TFNP}^{\mathrm{dt}}$ is total. -/
theorem SearchProblem.InTFNPdt.isTotal {P : SearchProblem ι} (h : P.InTFNPdt) : P.IsTotal :=
  h.1

/-- Membership in $\mathsf{FP}^{\mathrm{dt}}$: `P` belongs to $\mathsf{TFNP}^{\mathrm{dt}}$ and
there exist uniform constants `C, k : ℕ` such that every instance `i : ι` admits a deterministic
solver decision tree of depth at most `C * (Nat.log 2 (P.inputLen i) + 1) ^ k` finding a valid
solution `T.eval w`. -/
def SearchProblem.InFPdt (P : SearchProblem ι) : Prop :=
  P.InTFNPdt ∧
    ∃ C k : ℕ, ∀ i : ι,
      ∃ T : Cslib.DecisionTree (Fin (P.inputLen i)) (P.Output i),
        T.depth ≤ C * (Nat.log 2 (P.inputLen i) + 1) ^ k ∧
        ∀ w : Fin (P.inputLen i) → Bool, P.Rel i w (T.eval w)

/-- Characterization of `SearchProblem.InFPdt`. -/
theorem SearchProblem.inFPdt_iff {P : SearchProblem ι} :
    P.InFPdt ↔
      P.InTFNPdt ∧
        ∃ C k : ℕ, ∀ i : ι,
          ∃ T : Cslib.DecisionTree (Fin (P.inputLen i)) (P.Output i),
            T.depth ≤ C * (Nat.log 2 (P.inputLen i) + 1) ^ k ∧
            ∀ w : Fin (P.inputLen i) → Bool, P.Rel i w (T.eval w) :=
  Iff.rfl

/-- Every search problem in $\mathsf{FP}^{\mathrm{dt}}$ belongs to
$\mathsf{TFNP}^{\mathrm{dt}}$. -/
theorem SearchProblem.InFPdt.inTFNPdt {P : SearchProblem ι} (h : P.InFPdt) : P.InTFNPdt :=
  h.1

/-- Every search problem in $\mathsf{FP}^{\mathrm{dt}}$ is total. -/
theorem SearchProblem.InFPdt.isTotal {P : SearchProblem ι} (h : P.InFPdt) : P.IsTotal :=
  h.inTFNPdt.isTotal

/-- The black-box total search complexity class $\mathsf{TFNP}^{\mathrm{dt}}$ as a set of indexed
search problems over `ι`. -/
def TFNPdt (ι : Type*) : Set (SearchProblem ι) :=
  {P | P.InTFNPdt}

/-- Membership characterization for `TFNPdt`. -/
@[simp]
theorem mem_tfnpdt_iff {P : SearchProblem ι} : P ∈ TFNPdt ι ↔ P.InTFNPdt :=
  Iff.rfl

/-- The deterministic black-box total search complexity class $\mathsf{FP}^{\mathrm{dt}}$ as a set
of indexed search problems over `ι`. -/
def FPdt (ι : Type*) : Set (SearchProblem ι) :=
  {P | P.InFPdt}

/-- Membership characterization for `FPdt`. -/
@[simp]
theorem mem_fpdt_iff {P : SearchProblem ι} : P ∈ FPdt ι ↔ P.InFPdt :=
  Iff.rfl

/-- Class inclusion $\mathsf{FP}^{\mathrm{dt}} \subseteq \mathsf{TFNP}^{\mathrm{dt}}$ over any
instance index type `ι`. -/
theorem fpdt_subset_tfnpdt (ι : Type*) : FPdt ι ⊆ TFNPdt ι :=
  fun _ h ↦ h.inTFNPdt

/-- Direct $\mathsf{FP}^{\mathrm{dt}}$ membership criterion: polylogarithmic-depth verifiers
together with polylogarithmic-depth deterministic solvers automatically establish totality and
yield `P.InFPdt`. -/
theorem SearchProblem.inFPdt_of_verifier_of_solver {P : SearchProblem ι}
    (hV : ∃ C₁ k₁ : ℕ, ∀ (i : ι) (o : P.Output i),
      ∃ V : Cslib.DecisionTree (Fin (P.inputLen i)) Bool,
        V.depth ≤ C₁ * (Nat.log 2 (P.inputLen i) + 1) ^ k₁ ∧
        ∀ w : Fin (P.inputLen i) → Bool, V.eval w = true ↔ P.Rel i w o)
    (hT : ∃ C₂ k₂ : ℕ, ∀ i : ι,
      ∃ T : Cslib.DecisionTree (Fin (P.inputLen i)) (P.Output i),
        T.depth ≤ C₂ * (Nat.log 2 (P.inputLen i) + 1) ^ k₂ ∧
        ∀ w : Fin (P.inputLen i) → Bool, P.Rel i w (T.eval w)) :
    P.InFPdt := by
  obtain ⟨C₂, k₂, hT⟩ := hT
  have htot : P.IsTotal := fun i w ↦ by
    obtain ⟨T, _, hrel⟩ := hT i
    exact ⟨T.eval w, hrel w⟩
  exact ⟨⟨htot, hV⟩, C₂, k₂, hT⟩

end TotalSearchClasses

section Separations

universe v

private def firstBitSearch : SearchProblem.{0, v} ℕ where
  inputLen n := n + 1
  Output _ := ULift.{v} Bool
  solutions _ := {p | p.1 0 = p.2.down}

private lemma firstBitSearch_inFPdt : firstBitSearch.{v}.InFPdt := by
  refine SearchProblem.inFPdt_of_verifier_of_solver ?_ ?_
  · refine ⟨1, 0, fun n o ↦ ?_⟩
    dsimp only [firstBitSearch] at o ⊢
    refine ⟨.node 0 (.leaf (false == o.down)) (.leaf (true == o.down)), by simp, fun w ↦ ?_⟩
    cases hw : w 0 <;> simp [SearchProblem.Rel, hw]
  · refine ⟨1, 0, fun n ↦ ?_⟩
    dsimp only [firstBitSearch]
    refine ⟨.node 0 (.leaf (ULift.up false)) (.leaf (ULift.up true)), by simp, fun w ↦ ?_⟩
    cases hw : w 0 <;> simp [SearchProblem.Rel, hw]

/-- The complexity class $\mathsf{FP}^{\mathrm{dt}}$ over `ℕ` is nonempty. -/
theorem fpdt_nonempty : (FPdt.{0, v} ℕ).Nonempty :=
  ⟨firstBitSearch.{v}, firstBitSearch_inFPdt.{v}⟩

/-- The complexity class $\mathsf{TFNP}^{\mathrm{dt}}$ over `ℕ` is nonempty. -/
theorem tfnpdt_nonempty : (TFNPdt.{0, v} ℕ).Nonempty :=
  fpdt_nonempty.{v}.mono (fpdt_subset_tfnpdt ℕ)

private def emptyRelSearch : SearchProblem.{0, v} ℕ where
  inputLen n := n + 1
  Output _ := ULift.{v} Bool
  solutions _ := ∅

/-- Not every indexed search problem on `ℕ` is total. -/
theorem exists_not_isTotal : ∃ P : SearchProblem.{0, v} ℕ, ¬ P.IsTotal :=
  ⟨emptyRelSearch.{v}, fun h ↦ by
    obtain ⟨_, hrel⟩ := h 0 (fun _ ↦ false)
    exact hrel⟩

private def allOnesPredSearch : SearchProblem.{0, v} ℕ where
  inputLen n := n + 1
  Output _ := ULift.{v} Bool
  solutions n := {p | p.2.down = true ↔ ∀ j : Fin (n + 1), p.1 j = true}

private lemma allOnesPredSearch_isTotal : allOnesPredSearch.{v}.IsTotal := fun n w ↦ by
  classical
  dsimp only [allOnesPredSearch] at w ⊢
  exact ⟨ULift.up (decide (∀ j : Fin (n + 1), w j = true)), by simp [SearchProblem.Rel]⟩

private lemma linear_mul_succ_lt_two_pow_two_mul (a : ℕ) :
    a * (2 * (a + 1) + 1) + 2 < 2 ^ (2 * (a + 1)) := by
  induction a with
  | zero => decide
  | succ a ih =>
    have hpow : 2 ^ (2 * (a + 1 + 1)) = 4 * 2 ^ (2 * (a + 1)) := by
      rw [show 2 * (a + 1 + 1) = 2 * (a + 1) + 2 by omega, Nat.pow_add,
        show (2 ^ 2 : ℕ) = 4 by decide, Nat.mul_comm]
    have hstep : (a + 1) * (2 * (a + 1 + 1) + 1) + 2 = a * (2 * (a + 1) + 1) + 4 * a + 7 := by
      simp only [Nat.add_mul, Nat.mul_add]
      omega
    have hge : 3 * a ≤ a * (2 * (a + 1) + 1) :=
      (Nat.mul_comm 3 a).trans_le (Nat.mul_le_mul_left a (by omega))
    omega

private lemma exists_polylog_lt_two_pow (C k : ℕ) :
    ∃ m : ℕ, C * (2 ^ m + 1) ^ k < 2 ^ (2 ^ m) := by
  refine ⟨2 * (C + k + 1), ?_⟩
  set s := 2 * (C + k + 1)
  have hs : (C + k) * (s + 1) < 2 ^ s :=
    lt_of_le_of_lt (Nat.le_add_right _ 2) (linear_mul_succ_lt_two_pow_two_mul (C + k))
  have hC : C ≤ 2 ^ C := Nat.le_of_lt Nat.lt_two_pow_self
  have hstep : 2 ^ s + 1 ≤ 2 ^ (s + 1) := by
    rw [Nat.pow_succ']
    have : 1 ≤ 2 ^ s := Nat.one_le_two_pow
    omega
  have hpowk : (2 ^ s + 1) ^ k ≤ 2 ^ ((s + 1) * k) :=
    (Nat.pow_le_pow_left hstep k).trans_eq (Nat.pow_mul 2 (s + 1) k).symm
  have hexp : C + (s + 1) * k < 2 ^ s := by
    have hC_mul : C ≤ C * (s + 1) := Nat.le_mul_of_pos_right C (Nat.succ_pos s)
    have hmul : C + (s + 1) * k ≤ (C + k) * (s + 1) := by
      rw [Nat.mul_comm (s + 1) k, Nat.add_mul]
      omega
    exact lt_of_le_of_lt hmul hs
  calc C * (2 ^ s + 1) ^ k ≤ 2 ^ C * 2 ^ ((s + 1) * k) := Nat.mul_le_mul hC hpowk
    _ = 2 ^ (C + (s + 1) * k) := (Nat.pow_add 2 C ((s + 1) * k)).symm
    _ < 2 ^ (2 ^ s) := Nat.pow_lt_pow_right (by decide) hexp

private lemma not_allOnesPredSearch_inTFNPdt : ¬ allOnesPredSearch.{v}.InTFNPdt := by
  classical
  rintro ⟨_, C, k, hV⟩
  obtain ⟨m, hm⟩ := exists_polylog_lt_two_pow C k
  have hpos : 1 ≤ 2 ^ (2 ^ m) := Nat.one_le_two_pow
  set n := 2 ^ (2 ^ m) - 1
  have hn : n + 1 = 2 ^ (2 ^ m) := Nat.sub_add_cancel hpos
  obtain ⟨V, hdepth, hspec⟩ := hV n (ULift.up true)
  have hlog : Nat.log 2 (allOnesPredSearch.{v}.inputLen n) = 2 ^ m := by
    change Nat.log 2 (n + 1) = 2 ^ m
    rw [hn]
    exact Nat.log_pow (by decide) (2 ^ m)
  rw [hlog] at hdepth
  let allOnes : Fin (allOnesPredSearch.{v}.inputLen n) → Bool := fun _ ↦ true
  have hcard_lt : (V.queries allOnes).card < allOnesPredSearch.{v}.inputLen n :=
    (V.card_queries_le_depth allOnes).trans_lt
      (hdepth.trans_lt (by simpa [allOnesPredSearch, hn] using hm))
  have hex : ∃ j : Fin (allOnesPredSearch.{v}.inputLen n), j ∉ V.queries allOnes := by
    by_contra hnone
    push Not at hnone
    have hsub : Finset.univ ⊆ V.queries allOnes := fun j _ ↦ hnone j
    have hle := Finset.card_le_card hsub
    simp only [Finset.card_univ, Fintype.card_fin] at hle
    omega
  obtain ⟨j₀, hj₀⟩ := hex
  let flipJ : Fin (allOnesPredSearch.{v}.inputLen n) → Bool :=
    fun j ↦ if j = j₀ then false else true
  have heq : ∀ j ∈ V.queries allOnes, flipJ j = allOnes j := fun j hj ↦ by
    have hne : j ≠ j₀ := fun h ↦ hj₀ (h ▸ hj)
    simp [flipJ, allOnes, hne]
  have heval : V.eval flipJ = V.eval allOnes := V.eval_eq_of_forall_mem_queries heq
  have htrue : V.eval allOnes = true :=
    (hspec allOnes).mpr ⟨fun _ _ ↦ rfl, fun _ ↦ rfl⟩
  have hflip : allOnesPredSearch.{v}.Rel n flipJ (ULift.up true) :=
    (hspec flipJ).mp (heval.trans htrue)
  have hbad : flipJ j₀ = true := hflip.mp rfl j₀
  simp [flipJ] at hbad

/-- Totality strictly exceeds $\mathsf{TFNP}^{\mathrm{dt}}$: there exists a total search problem on
`ℕ` that does not belong to $\mathsf{TFNP}^{\mathrm{dt}}$. -/
theorem exists_isTotal_not_inTFNPdt :
    ∃ P : SearchProblem.{0, v} ℕ, P.IsTotal ∧ P ∉ TFNPdt.{0, v} ℕ :=
  ⟨allOnesPredSearch.{v}, allOnesPredSearch_isTotal.{v}, not_allOnesPredSearch_inTFNPdt.{v}⟩

end Separations

end Cslib.QueryComplexity
