module

public import Cslib.MachineLearning.PACLearning.Defs
public import CslibFrontier.MachineLearning.OnlineLearning.MistakeBound.Littlestone
public import CslibFrontier.MachineLearning.PACLearning.VCDimension
public import Mathlib.Analysis.SpecialFunctions.Log.Base
import Cslib.Probability.PMF
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Nat.Log
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Sequential Shattering, Sequential Covering Bounds, and Pseudo-Dimension

This module develops sequential tree-based complexity measures and covering bounds for
hypothesis classes alongside Pollard's pseudo-dimension and logarithmic growth-function
inversion, proved strictly under standard Lean axioms.

Given a domain `α`, a complete rooted binary `α`-labeled tree of depth `d` (`SeqTree α d`)
assigns an element of `α` to each binary prefix of length `< d`. Sequential shattering of
binary classes recovers the Littlestone dimension, while sequential fat-shattering at scale
`γ` (`seqFatDim`) extends this notion to real-valued function classes. For discrete
`{0, …, K}`-valued classes with finite `seqFatDim` at scale `1`, we prove the sequential
Sauer–Shelah covering bound of Rakhlin, Sridharan, and Tewari, bounding the size of
a covering family of labeled trees on any depth-`n` instance tree by
`∑_{i ≤ d} n.choose i * K ^ i ≤ (e * K * n / d) ^ d`.

We also formalize Pollard's pseudo-dimension (`pseudoDim`) for real-valued function classes
and identify it with the Vapnik–Chervonenkis dimension of the associated subgraph class, the
Anthony–Bartlett logarithmic growth-function inversion lemma, and a sharp finite-sample
No-Free-Lunch lower bound on shattered sets.

## Main definitions

* `CslibFrontier.MachineLearning.OnlineLearning.SeqTree`: complete rooted binary `α`-labeled trees
  of depth `d`.
* `CslibFrontier.MachineLearning.OnlineLearning.SeqShatters`: sequential shattering of an
  `α`-labeled tree by a
  Boolean concept class.
* `CslibFrontier.MachineLearning.OnlineLearning.SeqFatShatters`,
  `CslibFrontier.MachineLearning.OnlineLearning.seqFatDim`: sequential
  fat-shattering and sequential fat-shattering dimension at scale `γ`.
* `CslibFrontier.MachineLearning.OnlineLearning.seqCoverSum`: the combinatorial bound
  `∑_{i ≤ d} n.choose i * K ^ i` on sequential tree covers.
* `CslibFrontier.MachineLearning.OnlineLearning.PseudoShatters`,
  `CslibFrontier.MachineLearning.OnlineLearning.pseudoDim`: Pollard's
  pseudo-shattering predicate and pseudo-dimension for real-valued function classes.
* `CslibFrontier.MachineLearning.OnlineLearning.subgraphClass`: binary threshold-indicator class
  associated with a
  real-valued function class.

## Main results

* `CslibFrontier.MachineLearning.OnlineLearning.exists_seqShatters_iff_hasMistakeTree` and
    `CslibFrontier.MachineLearning.OnlineLearning.seqLittlestoneDim_eq_littlestoneDim`: equivalence
  between sequential
  tree shattering and the Littlestone mistake-tree dimension.
* `CslibFrontier.MachineLearning.OnlineLearning.seqFatDim_bool_one_eq_littlestoneDim`: at scale `1`,
  the sequential
  fat-shattering dimension of a `{0, 1}`-valued class equals its Littlestone dimension.
* `CslibFrontier.MachineLearning.OnlineLearning.exists_seqTree_cover_of_seqFatDim_le` and
    `CslibFrontier.MachineLearning.OnlineLearning.exists_bool_seqTree_cover_of_littlestoneDim_le`:
  the Rakhlin–Sridharan–
  Tewari sequential Sauer–Shelah tree-covering theorem and its exponential upper bounds.
* `CslibFrontier.MachineLearning.OnlineLearning.card_le_of_seqTree_cover`: distinct adaptively
  realized root-to-leaf
  paths occupy distinct trees in any sequential tree cover.
* `CslibFrontier.MachineLearning.OnlineLearning.pseudoDim_eq_evcDim_subgraphClass` and
    `CslibFrontier.MachineLearning.OnlineLearning.exists_pseudoShatters_iff_strict`: subgraph
  characterization and
  strict-versus-weak threshold invariance of pseudo-dimension.
* `CslibFrontier.MachineLearning.OnlineLearning.log_le_mul_sub_log_sub_one` and
    `CslibFrontier.MachineLearning.OnlineLearning.exists_nat_gt_mul_logb_exp_mul`: convex conjugate
  inequality for the
  natural logarithm and explicit integer solution of `N * log₂ (e * m * M) < m`.
* `CslibFrontier.MachineLearning.OnlineLearning.exists_concept_prob_error_ge_quarter_ge_half`:
  uniform-distribution
  No-Free-Lunch lower bound `ℙ(error ≥ 1/4) ≥ 1/2` when `2 * m < |W|`.

## Tags

Littlestone dimension, sequential fat-shattering, sequential covering number,
pseudo-dimension, Sauer-Shelah lemma, PAC learning
-/

public section

open Finset MeasureTheory
open scoped ENNReal NNReal
open Cslib.MachineLearning.PACLearning
open Cslib.MachineLearning.OnlineLearning.MistakeBound

namespace CslibFrontier.MachineLearning.OnlineLearning

/-! ### Complete binary labeled trees -/

/-- A complete rooted binary tree of depth `d` whose internal nodes are labeled by `α`. -/
inductive SeqTree.{u} (α : Type u) : ℕ → Type u where
  /-- The empty tree of depth `0`. -/
  | nil : SeqTree α 0
  /-- An internal node labeled by `root` with `left` (`false`) and `right` (`true`) subtrees
  of depth `d`. -/
  | branch {d : ℕ} (root : α) (left right : SeqTree α d) : SeqTree α (d + 1)
  deriving DecidableEq

namespace SeqTree

variable {α β : Type*}

/-- The constant depth-`d` tree assigning label `a` to every internal node. -/
def const (a : α) : (d : ℕ) → SeqTree α d
  | 0 => .nil
  | d + 1 => .branch a (const a d) (const a d)

instance instInhabited [Inhabited α] (d : ℕ) : Inhabited (SeqTree α d) :=
  ⟨const default d⟩

instance instNonemptyZero : Nonempty (SeqTree α 0) :=
  ⟨.nil⟩

/-- Evaluate the node label at depth `i` along the root-to-leaf path `ε : Fin d → Bool`,
following `left` on `false` and `right` on `true`. -/
def evalPath : {d : ℕ} → SeqTree α d → (Fin d → Bool) → Fin d → α
  | 0, .nil, _, i => i.elim0
  | _ + 1, .branch r l rt, ε, i =>
    Fin.cases r (fun j => (if ε 0 then rt else l).evalPath (ε ∘ Fin.succ) j) i

@[simp]
theorem evalPath_branch_zero {d : ℕ} (r : α) (l rt : SeqTree α d) (ε : Fin (d + 1) → Bool) :
    (SeqTree.branch r l rt).evalPath ε 0 = r := by
  simp [evalPath]

@[simp]
theorem evalPath_branch_succ {d : ℕ} (r : α) (l rt : SeqTree α d) (ε : Fin (d + 1) → Bool)
    (j : Fin d) :
    (SeqTree.branch r l rt).evalPath ε j.succ =
      (if ε 0 then rt else l).evalPath (ε ∘ Fin.succ) j := by
  simp [evalPath]

@[simp]
theorem evalPath_const (a : α) :
    ∀ {d : ℕ} (ε : Fin d → Bool) (i : Fin d), (const a d).evalPath ε i = a
  | 0, _, i => i.elim0
  | _ + 1, ε, i => by
    refine Fin.cases (by simp [const]) (fun j => ?_) i
    simp only [const, evalPath_branch_succ]
    split_ifs <;> exact evalPath_const a (ε ∘ Fin.succ) j

/-- The node reached at depth `i` depends only on the strict prefix `ε 0, …, ε (i - 1)`. -/
theorem evalPath_congr :
    ∀ {d : ℕ} (t : SeqTree α d) {ε₁ ε₂ : Fin d → Bool} {i : Fin d},
      (∀ j : Fin d, j < i → ε₁ j = ε₂ j) → t.evalPath ε₁ i = t.evalPath ε₂ i
  | 0, .nil, _, _, i, _ => i.elim0
  | _ + 1, .branch r l rt, ε₁, ε₂, i, h => by
    revert h
    refine Fin.cases (fun _ => by simp) (fun j h => ?_) i
    have h0 : ε₁ 0 = ε₂ 0 := h 0 (Fin.succ_pos j)
    simp only [evalPath_branch_succ, h0]
    exact evalPath_congr _ fun k hk => h k.succ (Fin.succ_lt_succ_iff.mpr hk)

/-- Map a function over every node label of a complete binary tree. -/
def map (g : α → β) : {d : ℕ} → SeqTree α d → SeqTree β d
  | 0, .nil => .nil
  | _ + 1, .branch r l rt => .branch (g r) (l.map g) (rt.map g)

@[simp]
theorem evalPath_map (g : α → β) :
    ∀ {d : ℕ} (t : SeqTree α d) (ε : Fin d → Bool) (i : Fin d),
      (t.map g).evalPath ε i = g (t.evalPath ε i)
  | 0, .nil, _, i => i.elim0
  | _ + 1, .branch r l rt, ε, i => by
    refine Fin.cases (by simp [map]) (fun j => ?_) i
    simp only [map, evalPath_branch_succ]
    split_ifs <;> exact evalPath_map g _ _ j

/-- Construct a `SeqTree α d` from a sequence of prefix-labeling functions
`f i : (Fin i.val → Bool) → α` for `i : Fin d`. -/
def ofPrefixFn : {d : ℕ} → ((i : Fin d) → (Fin i.val → Bool) → α) → SeqTree α d
  | 0, _ => .nil
  | _ + 1, f =>
    .branch (f 0 Fin.elim0)
      (ofPrefixFn fun j p => f j.succ (Fin.cons false p))
      (ofPrefixFn fun j p => f j.succ (Fin.cons true p))

@[simp]
theorem evalPath_ofPrefixFn :
    ∀ {d : ℕ} (f : (i : Fin d) → (Fin i.val → Bool) → α) (ε : Fin d → Bool) (i : Fin d),
      (ofPrefixFn f).evalPath ε i = f i (fun k => ε ⟨k.1, k.2.trans i.2⟩)
  | 0, _, _, i => i.elim0
  | _ + 1, f, ε, i => by
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [ofPrefixFn, evalPath_branch_zero]
      congr 1
      funext k
      exact k.elim0
    · simp only [ofPrefixFn, evalPath_branch_succ]
      cases h0 : ε 0
      · simp only [Bool.false_eq_true, ↓reduceIte, evalPath_ofPrefixFn]
        congr 1
        funext k
        refine Fin.cases ?_ (fun _ => rfl) k
        exact h0.symm
      · simp only [↓reduceIte, evalPath_ofPrefixFn]
        congr 1
        funext k
        refine Fin.cases ?_ (fun _ => rfl) k
        exact h0.symm

/-- Extract the prefix-labeling representation `(i : Fin d) → (Fin i.val → Bool) → α` from
a `SeqTree α d`. -/
def toPrefixFn {d : ℕ} (t : SeqTree α d) (i : Fin d) (p : Fin i.val → Bool) : α :=
  t.evalPath (fun j => if h : j.val < i.val then p ⟨j.val, h⟩ else false) i

@[simp]
theorem toPrefixFn_apply {d : ℕ} (t : SeqTree α d) (ε : Fin d → Bool) (i : Fin d) :
    t.toPrefixFn i (fun k => ε ⟨k.1, k.2.trans i.2⟩) = t.evalPath ε i := by
  refine evalPath_congr t fun j hj => ?_
  have hj' : j.val < i.val := hj
  simp only [hj', ↓reduceDIte]

end SeqTree

/-! ### Sequential shattering and Littlestone dimension -/

/-- A Boolean concept class `H` sequentially shatters an `α`-labeled tree `x` of depth `d`
if every root-to-leaf path `ε : Fin d → Bool` is realized along `x` by some `h ∈ H`. -/
def SeqShatters {α : Type*} (H : Set (α → Bool)) {d : ℕ} (x : SeqTree α d) : Prop :=
  ∀ ε : Fin d → Bool, ∃ h ∈ H, ∀ i : Fin d, h (x.evalPath ε i) = ε i

/-- Sequential shattering is monotone in the concept class. -/
theorem SeqShatters.mono {α : Type*} {H H' : Set (α → Bool)} {d : ℕ} {x : SeqTree α d}
    (hx : SeqShatters H x) (hsub : H ⊆ H') : SeqShatters H' x :=
  fun ε => let ⟨h, hh, hpath⟩ := hx ε; ⟨h, hsub hh, hpath⟩

/-- The depth-`0` tree is sequentially shattered iff the class is nonempty. -/
theorem seqShatters_nil_iff {α : Type*} {H : Set (α → Bool)} :
    SeqShatters H (.nil : SeqTree α 0) ↔ H.Nonempty := by
  constructor
  · intro h
    obtain ⟨f, hf, -⟩ := h Fin.elim0
    exact ⟨f, hf⟩
  · rintro ⟨f, hf⟩ _
    exact ⟨f, hf, fun i => i.elim0⟩

/-- Recursive characterization of sequential shattering at a branching node. -/
theorem seqShatters_branch_iff {α : Type*} {H : Set (α → Bool)} {d : ℕ}
    {r : α} {l rt : SeqTree α d} :
    SeqShatters H (.branch r l rt) ↔
      SeqShatters {h ∈ H | h r = false} l ∧ SeqShatters {h ∈ H | h r = true} rt := by
  constructor
  · intro h
    refine ⟨fun ε => ?_, fun ε => ?_⟩
    · obtain ⟨f, hf, hpath⟩ := h (Fin.cons false ε)
      refine ⟨f, ⟨hf, by simpa using hpath 0⟩, fun j => ?_⟩
      simpa using hpath j.succ
    · obtain ⟨f, hf, hpath⟩ := h (Fin.cons true ε)
      refine ⟨f, ⟨hf, by simpa using hpath 0⟩, fun j => ?_⟩
      simpa using hpath j.succ
  · rintro ⟨hl, hrt⟩ ε
    cases h0 : ε 0
    · obtain ⟨f, ⟨hf, hfr⟩, hpath⟩ := hl (ε ∘ Fin.succ)
      refine ⟨f, hf, fun i => Fin.cases ?_ (fun j => ?_) i⟩
      · exact hfr.trans h0.symm
      · simp [h0, hpath j]
    · obtain ⟨f, ⟨hf, hfr⟩, hpath⟩ := hrt (ε ∘ Fin.succ)
      refine ⟨f, hf, fun i => Fin.cases ?_ (fun j => ?_) i⟩
      · exact hfr.trans h0.symm
      · simp [h0, hpath j]

/-- Sequential shattering of some depth-`d` `SeqTree` coincides with `HasMistakeTree d H`. -/
theorem exists_seqShatters_iff_hasMistakeTree {α : Type*} :
    ∀ {d : ℕ} {H : Set (α → Bool)},
      (∃ x : SeqTree α d, SeqShatters H x) ↔ HasMistakeTree d H
  | 0, H => by
    rw [hasMistakeTree_zero]
    refine ⟨fun ⟨t, h⟩ => ?_, fun h => ⟨.nil, seqShatters_nil_iff.mpr h⟩⟩
    cases t
    exact seqShatters_nil_iff.mp h
  | d + 1, H => by
    rw [hasMistakeTree_succ_bool]
    have hvs : ∀ (r : α) (b : Bool),
        (versionSpace H [(r, b)] : Set (α → Bool)) = {h ∈ H | h r = b} := by
      intro r b
      ext h
      simp [versionSpace]
    constructor
    · rintro ⟨t, hx⟩
      cases t with
      | branch r l rt =>
        obtain ⟨hl, hrt⟩ := seqShatters_branch_iff.mp hx
        refine ⟨r, fun b => ?_⟩
        rw [hvs]
        cases b
        · exact exists_seqShatters_iff_hasMistakeTree.mp ⟨l, hl⟩
        · exact exists_seqShatters_iff_hasMistakeTree.mp ⟨rt, hrt⟩
    · rintro ⟨r, hr⟩
      have h0 := hr false; rw [hvs] at h0
      have h1 := hr true; rw [hvs] at h1
      obtain ⟨l, hl⟩ := exists_seqShatters_iff_hasMistakeTree.mpr h0
      obtain ⟨rt, hrt⟩ := exists_seqShatters_iff_hasMistakeTree.mpr h1
      exact ⟨.branch r l rt, seqShatters_branch_iff.mpr ⟨hl, hrt⟩⟩

/-- The supremum of sequentially shattered tree depths coincides with the canonical
`littlestoneDim` of `H`. -/
theorem seqLittlestoneDim_eq_littlestoneDim {α : Type*} (H : Set (α → Bool)) :
    (⨆ (d : ℕ) (_ : ∃ x : SeqTree α d, SeqShatters H x), (d : ℕ∞)) = littlestoneDim H := by
  apply le_antisymm
  · refine iSup₂_le fun d hd => ?_
    exact le_littlestoneDim_of_hasMistakeTree (exists_seqShatters_iff_hasMistakeTree.mp hd)
  · rw [littlestoneDim_le_iff]
    intro d hd
    exact le_iSup₂_of_le d (exists_seqShatters_iff_hasMistakeTree.mpr hd) le_rfl

/-- Every finite class sequentially shattering a depth-`d` tree has cardinality at least
`2 ^ d`. -/
theorem two_pow_le_card_of_hasMistakeTree {α : Type*} :
    ∀ {d : ℕ} {H : Finset (α → Bool)},
      HasMistakeTree d (H : Set (α → Bool)) → 2 ^ d ≤ H.card
  | 0, H, h => by
    obtain ⟨f, hf⟩ := hasMistakeTree_zero.mp h
    exact Finset.card_pos.mpr ⟨f, Finset.mem_coe.mp hf⟩
  | d + 1, H, h => by
    classical
    obtain ⟨t, hx⟩ := exists_seqShatters_iff_hasMistakeTree.mpr h
    cases t with
    | branch r l rt =>
    obtain ⟨hl, hrt⟩ := seqShatters_branch_iff.mp hx
    set H₀ := H.filter fun f => f r = false
    set H₁ := H.filter fun f => f r = true
    have hc₀ : (H₀ : Set (α → Bool)) = {f ∈ (H : Set (α → Bool)) | f r = false} := by
      ext f; simp [H₀]
    have hc₁ : (H₁ : Set (α → Bool)) = {f ∈ (H : Set (α → Bool)) | f r = true} := by
      ext f; simp [H₁]
    have h0 : 2 ^ d ≤ H₀.card := two_pow_le_card_of_hasMistakeTree
      (exists_seqShatters_iff_hasMistakeTree.mp ⟨l, hc₀.symm ▸ hl⟩)
    have h1 : 2 ^ d ≤ H₁.card := two_pow_le_card_of_hasMistakeTree
      (exists_seqShatters_iff_hasMistakeTree.mp ⟨rt, hc₁.symm ▸ hrt⟩)
    have hdisj : Disjoint H₀ H₁ := Finset.disjoint_filter.mpr fun f _ hf0 hf1 => by
      rw [hf0] at hf1; exact Bool.false_ne_true hf1
    have hsub : H₀ ∪ H₁ ⊆ H :=
      Finset.union_subset (Finset.filter_subset _ H) (Finset.filter_subset _ H)
    have hcard : H₀.card + H₁.card ≤ H.card := by
      rw [← Finset.card_union_of_disjoint hdisj]
      exact Finset.card_le_card hsub
    rw [pow_succ]
    omega

/-- The Littlestone dimension of a finite Boolean concept class is at most `⌊log₂ |H|⌋`. -/
theorem littlestoneDim_le_log_card {α : Type*} (H : Finset (α → Bool)) :
    littlestoneDim (H : Set (α → Bool)) ≤ (Nat.log 2 H.card : ℕ∞) := by
  rw [littlestoneDim_le_iff]
  intro d hd
  have hpow := two_pow_le_card_of_hasMistakeTree hd
  exact Nat.cast_le.mpr (Nat.le_log_of_pow_le (by norm_num) hpow)

/-- Every finite shattered set gives a constant-per-level shattered tree, so
`evcDim H ≤ littlestoneDim H`. -/
theorem evcDim_le_littlestoneDim {α : Type*} (H : Set (α → Bool)) :
    evcDim H ≤ littlestoneDim H := by
  classical
  rw [evcDim_le_iff]
  intro W hW
  let e : Fin W.card ≃ ↥W := (Fintype.equivFinOfCardEq (Fintype.card_coe W)).symm
  let t : SeqTree α W.card := SeqTree.ofPrefixFn fun i _ => (e i).val
  have hsh : SeqShatters H t := by
    intro ε
    let U : Set α := {a ∈ (W : Set α) | ∃ i : Fin W.card, (e i).val = a ∧ ε i = true}
    obtain ⟨h, hh, hhU⟩ := hW U (fun _ ha => ha.1)
    refine ⟨h, hh, fun i => ?_⟩
    have hmem : h (e i).val = true ↔ (e i).val ∈ U := by
      have := congrArg ((e i).val ∈ ·) hhU
      simpa [(e i).property] using this
    simp only [t, SeqTree.evalPath_ofPrefixFn]
    have hUiff : (e i).val ∈ U ↔ ε i = true := by
      refine ⟨fun ⟨_, j, hj, hεj⟩ => ?_, fun hεi => ⟨(e i).property, i, rfl, hεi⟩⟩
      have hij : j = i := e.injective (Subtype.ext hj)
      exact hij ▸ hεj
    cases hε : ε i
    · exact Bool.eq_false_iff.mpr fun htrue =>
        Bool.false_ne_true (hε.symm.trans (hUiff.mp (hmem.mp htrue)))
    · exact hmem.mpr (hUiff.mpr hε)
  exact le_littlestoneDim_of_hasMistakeTree (exists_seqShatters_iff_hasMistakeTree.mp ⟨t, hsh⟩)

/-! ### Sequential fat-shattering dimension -/

/-- A real-valued function class `F` sequentially shatters an `α`-labeled tree `x` of depth `d`
at scale `γ` if there is a real-valued witness tree `s` of depth `d` such that every sign path
`ε : Fin d → Bool` is realized with margin `γ / 2` by some `f ∈ F`. -/
def SeqFatShatters {α : Type*} (F : Set (α → ℝ)) (γ : ℝ) {d : ℕ} (x : SeqTree α d) : Prop :=
  ∃ s : SeqTree ℝ d, ∀ ε : Fin d → Bool, ∃ f ∈ F, ∀ i : Fin d,
    γ / 2 ≤ (if ε i then (1 : ℝ) else -1) * (f (x.evalPath ε i) - s.evalPath ε i)

/-- The sequential fat-shattering dimension of `F` at scale `γ`, valued in `ℕ∞`. -/
noncomputable def seqFatDim {α : Type*} (F : Set (α → ℝ)) (γ : ℝ) : ℕ∞ :=
  ⨆ (d : ℕ) (_ : ∃ x : SeqTree α d, SeqFatShatters F γ x), (d : ℕ∞)

/-- Sequential fat-shattering is monotone in the function class. -/
theorem SeqFatShatters.mono {α : Type*} {F F' : Set (α → ℝ)} {γ : ℝ} {d : ℕ}
    {x : SeqTree α d} (hx : SeqFatShatters F γ x) (hsub : F ⊆ F') :
    SeqFatShatters F' γ x := by
  obtain ⟨s, hs⟩ := hx
  exact ⟨s, fun ε => let ⟨f, hf, hpath⟩ := hs ε; ⟨f, hsub hf, hpath⟩⟩

/-- Sequential fat-shattering is antitone in the scale parameter `γ`. -/
theorem SeqFatShatters.anti_scale {α : Type*} {F : Set (α → ℝ)} {γ₁ γ₂ : ℝ} {d : ℕ}
    {x : SeqTree α d} (hx : SeqFatShatters F γ₂ x) (hγ : γ₁ ≤ γ₂) :
    SeqFatShatters F γ₁ x := by
  obtain ⟨s, hs⟩ := hx
  refine ⟨s, fun ε => ?_⟩
  obtain ⟨f, hf, hpath⟩ := hs ε
  exact ⟨f, hf, fun i => (by linarith : γ₁ / 2 ≤ γ₂ / 2).trans (hpath i)⟩

/-- The depth-`0` tree is sequentially fat-shattered at any scale iff `F` is nonempty. -/
theorem seqFatShatters_nil_iff {α : Type*} {F : Set (α → ℝ)} {γ : ℝ} :
    SeqFatShatters F γ (.nil : SeqTree α 0) ↔ F.Nonempty := by
  constructor
  · rintro ⟨_, hs⟩
    obtain ⟨f, hf, -⟩ := hs Fin.elim0
    exact ⟨f, hf⟩
  · rintro ⟨f, hf⟩
    exact ⟨.nil, fun _ => ⟨f, hf, fun i => i.elim0⟩⟩

/-- Recursive characterization of sequential fat-shattering at a branching node. -/
theorem seqFatShatters_branch_iff {α : Type*} {F : Set (α → ℝ)} {γ : ℝ} {d : ℕ}
    {r : α} {l rt : SeqTree α d} :
    SeqFatShatters F γ (.branch r l rt) ↔
      ∃ s₀ : ℝ,
        SeqFatShatters {f ∈ F | f r ≤ s₀ - γ / 2} γ l ∧
        SeqFatShatters {f ∈ F | s₀ + γ / 2 ≤ f r} γ rt := by
  constructor
  · rintro ⟨st, hs⟩
    cases st with
    | branch s₀ sl srt =>
    refine ⟨s₀, ⟨sl, fun ε => ?_⟩, ⟨srt, fun ε => ?_⟩⟩
    · obtain ⟨f, hf, hpath⟩ := hs (Fin.cons false ε)
      have h0 := hpath 0
      simp only [Fin.cons_zero, Bool.false_eq_true, ↓reduceIte,
        SeqTree.evalPath_branch_zero] at h0
      refine ⟨f, ⟨hf, by linarith⟩, fun j => ?_⟩
      simpa using hpath j.succ
    · obtain ⟨f, hf, hpath⟩ := hs (Fin.cons true ε)
      have h0 := hpath 0
      simp only [Fin.cons_zero, ↓reduceIte, SeqTree.evalPath_branch_zero] at h0
      refine ⟨f, ⟨hf, by linarith⟩, fun j => ?_⟩
      simpa using hpath j.succ
  · rintro ⟨s₀, ⟨sl, hl⟩, ⟨srt, hrt⟩⟩
    refine ⟨.branch s₀ sl srt, fun ε => ?_⟩
    cases h0 : ε 0
    · obtain ⟨f, ⟨hf, hfr⟩, hpath⟩ := hl (ε ∘ Fin.succ)
      refine ⟨f, hf, fun i => Fin.cases ?_ (fun j => ?_) i⟩
      · simp only [h0, Bool.false_eq_true, ↓reduceIte, SeqTree.evalPath_branch_zero]
        linarith
      · simpa [h0] using hpath j
    · obtain ⟨f, ⟨hf, hfr⟩, hpath⟩ := hrt (ε ∘ Fin.succ)
      refine ⟨f, hf, fun i => Fin.cases ?_ (fun j => ?_) i⟩
      · simp only [h0, ↓reduceIte, SeqTree.evalPath_branch_zero]
        linarith
      · simpa [h0] using hpath j

/-- Every sequentially fat-shattered tree bounds `seqFatDim` from below. -/
theorem SeqFatShatters.le_seqFatDim {α : Type*} {F : Set (α → ℝ)} {γ : ℝ} {d : ℕ}
    {x : SeqTree α d} (hx : SeqFatShatters F γ x) : (d : ℕ∞) ≤ seqFatDim F γ :=
  le_iSup₂_of_le d ⟨x, hx⟩ le_rfl

/-- Upper-bound characterization of `seqFatDim`. -/
theorem seqFatDim_le_iff {α : Type*} {F : Set (α → ℝ)} {γ : ℝ} {m : ℕ∞} :
    seqFatDim F γ ≤ m ↔ ∀ (d : ℕ) (x : SeqTree α d), SeqFatShatters F γ x → (d : ℕ∞) ≤ m := by
  simp only [seqFatDim, iSup₂_le_iff, forall_exists_index]

/-- `seqFatDim` is monotone in the function class. -/
theorem seqFatDim_mono {α : Type*} {F F' : Set (α → ℝ)} (hsub : F ⊆ F') (γ : ℝ) :
    seqFatDim F γ ≤ seqFatDim F' γ :=
  seqFatDim_le_iff.mpr fun _ _ hx => (hx.mono hsub).le_seqFatDim

/-- Embed a discrete `Fin n`-valued class into real-valued functions via `ℕ → ℝ`. -/
@[expose] def finClassToReal {α : Type*} {n : ℕ} (H : Set (α → Fin n)) : Set (α → ℝ) :=
  (fun h a => ((h a : ℕ) : ℝ)) '' H

/-- Embed a Boolean concept class into `{0, 1} ⊆ ℝ` via `Bool.toNat`. -/
def boolClassToReal {α : Type*} (H : Set (α → Bool)) : Set (α → ℝ) :=
  (fun h a => ((h a).toNat : ℝ)) '' H

/-- At scale `1`, sequential fat-shattering of a `{0, 1}`-embedded Boolean class coincides
with ordinary sequential shattering. -/
theorem seqFatShatters_boolClassToReal_one_iff {α : Type*} {H : Set (α → Bool)} {d : ℕ}
    {x : SeqTree α d} :
    SeqFatShatters (boolClassToReal H) 1 x ↔ SeqShatters H x := by
  constructor
  · rintro ⟨s, hs⟩ ε
    obtain ⟨_, ⟨h, hh, rfl⟩, hpath⟩ := hs ε
    refine ⟨h, hh, fun i => ?_⟩
    have hi := hpath i
    -- Also compare with the path flipping coordinate `i` to pin `s` inside `(0, 1)`.
    let ε' : Fin d → Bool := Function.update ε i (!ε i)
    obtain ⟨_, ⟨h', -, rfl⟩, hpath'⟩ := hs ε'
    have hi' := hpath' i
    have hcongr : s.evalPath ε' i = s.evalPath ε i :=
      SeqTree.evalPath_congr s fun j hj => Function.update_of_ne hj.ne (!ε i) ε
    have hsi : (0 : ℝ) < s.evalPath ε i ∧ s.evalPath ε i < 1 := by
      rw [hcongr] at hi'
      have hb1 : 0 ≤ ((h (x.evalPath ε i)).toNat : ℝ) ∧
          ((h (x.evalPath ε i)).toNat : ℝ) ≤ 1 := by
        cases h (x.evalPath ε i) <;> simp
      have hb2 : 0 ≤ ((h' (x.evalPath ε' i)).toNat : ℝ) ∧
          ((h' (x.evalPath ε' i)).toNat : ℝ) ≤ 1 := by
        cases h' (x.evalPath ε' i) <;> simp
      have hε'i : ε' i = !ε i := Function.update_self i (!ε i) ε
      rw [hε'i] at hi'
      cases hε : ε i <;>
        simp only [hε, Bool.false_eq_true, Bool.not_false, Bool.not_true, ↓reduceIte] at hi hi' <;>
        exact ⟨by linarith [hb1.1, hb1.2, hb2.1, hb2.2],
          by linarith [hb1.1, hb1.2, hb2.1, hb2.2]⟩
    cases hε : ε i <;> cases hhx : h (x.evalPath ε i) <;>
      simp only [hε, hhx, Bool.false_eq_true, ↓reduceIte, Bool.toNat_false, Bool.toNat_true,
        Nat.cast_zero, Nat.cast_one] at hi ⊢ <;> linarith [hsi.1, hsi.2]
  · intro hx
    refine ⟨SeqTree.const (1 / 2) d, fun ε => ?_⟩
    obtain ⟨h, hh, hpath⟩ := hx ε
    refine ⟨fun a => ((h a).toNat : ℝ), ⟨h, hh, rfl⟩, fun i => ?_⟩
    simp only [SeqTree.evalPath_const, hpath i]
    cases ε i <;> norm_num

/-- At scale `1`, the sequential fat-shattering dimension of a `{0, 1}`-valued class equals
its Littlestone dimension. -/
theorem seqFatDim_bool_one_eq_littlestoneDim {α : Type*} (H : Set (α → Bool)) :
    seqFatDim (boolClassToReal H) 1 = littlestoneDim H := by
  simp only [seqFatDim, seqFatShatters_boolClassToReal_one_iff,
    seqLittlestoneDim_eq_littlestoneDim]

/-! ### Rakhlin–Sridharan–Tewari sequential Sauer–Shelah tree-covering bound -/

/-- The sequential Sauer–Shelah covering bound `∑_{i ≤ d} n.choose i * K ^ i` for
`{0, …, K}`-valued classes of scale-`1` sequential fat-shattering dimension at most `d` on
depth-`n` trees (sequential Sauer–Shelah covering bound). -/
def seqCoverSum (K n d : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (d + 1), n.choose i * K ^ i

@[simp]
theorem seqCoverSum_zero_left (n d : ℕ) : seqCoverSum 0 n d = 1 := by
  simp [seqCoverSum, Finset.sum_range_succ']

@[simp]
theorem seqCoverSum_zero_mid (K d : ℕ) : seqCoverSum K 0 d = 1 := by
  simp [seqCoverSum, Finset.sum_range_succ']

@[simp]
theorem seqCoverSum_zero_right (K n : ℕ) : seqCoverSum K n 0 = 1 := by
  simp [seqCoverSum]

@[simp]
theorem seqCoverSum_one_left (n d : ℕ) :
    seqCoverSum 1 n d = ∑ i ∈ Finset.range (d + 1), n.choose i := by
  simp [seqCoverSum]

/-- Pascal recurrence for `seqCoverSum`. -/
theorem seqCoverSum_succ (K n d : ℕ) :
    seqCoverSum K (n + 1) (d + 1) = seqCoverSum K n (d + 1) + K * seqCoverSum K n d := by
  simp only [seqCoverSum]
  rw [Finset.sum_range_succ', Finset.sum_range_succ' (fun i => n.choose i * K ^ i),
    Finset.mul_sum]
  simp only [Nat.choose_succ_succ', Nat.choose_zero_right, pow_zero, add_mul,
    Finset.sum_add_distrib]
  have hmul : ∀ i ∈ Finset.range (d + 1), n.choose i * K ^ (i + 1) = K * (n.choose i * K ^ i) :=
    fun _ _ => by ring
  rw [Finset.sum_congr rfl hmul]
  ring

/-- `seqCoverSum K n d` is always positive. -/
theorem seqCoverSum_pos (K n d : ℕ) : 0 < seqCoverSum K n d := by
  rw [seqCoverSum, Finset.sum_range_succ']
  simp only [Nat.choose_zero_right, pow_zero, mul_one]
  omega

/-- Exponential upper bound `seqCoverSum K n d ≤ (e * K * n / d) ^ d` for `1 ≤ d ≤ n` and
`1 ≤ K`. -/
theorem seqCoverSum_le_exp_mul_div_pow {K n d : ℕ} (hK : 1 ≤ K) (hd : 1 ≤ d) (hdn : d ≤ n) :
    (seqCoverSum K n d : ℝ) ≤ (Real.exp 1 * K * n / d) ^ d := by
  have hd_pos : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (hd.trans hdn)
  have hK_pos : (0 : ℝ) < K := Nat.cast_pos.mpr hK
  have hKn_pos : (0 : ℝ) < (K : ℝ) * n := mul_pos hK_pos hn_pos
  have hdn_div : (d : ℝ) / n ≤ 1 := (div_le_one hn_pos).mpr (Nat.cast_le.mpr hdn)
  have hK1 : (1 : ℝ) ≤ K := Nat.one_le_cast.mpr hK
  have hscaled : ((d : ℝ) / (K * n)) ^ d * (seqCoverSum K n d : ℝ) ≤ Real.exp d := by
    rw [seqCoverSum, Nat.cast_sum, Finset.mul_sum]
    simp only [Nat.cast_mul, Nat.cast_pow]
    calc ∑ i ∈ Finset.range (d + 1),
          ((d : ℝ) / (K * n)) ^ d * ((n.choose i : ℝ) * (K : ℝ) ^ i)
        ≤ ∑ i ∈ Finset.range (d + 1), ((d : ℝ) / n) ^ i * 1 ^ (n - i) * (n.choose i : ℝ) := by
          refine Finset.sum_le_sum fun i hi => ?_
          have hid : i ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
          rw [one_pow, mul_one]
          have hpow_d : ((d : ℝ) / n) ^ d ≤ ((d : ℝ) / n) ^ i :=
            pow_le_pow_of_le_one (by positivity) hdn_div hid
          have hpow_K : (K : ℝ) ^ i ≤ (K : ℝ) ^ d := pow_le_pow_right₀ hK1 hid
          have hK_div : (K : ℝ) ^ i / (K : ℝ) ^ d ≤ 1 :=
            (div_le_one (by positivity)).mpr hpow_K
          calc ((d : ℝ) / (K * n)) ^ d * ((n.choose i : ℝ) * (K : ℝ) ^ i)
              = (n.choose i : ℝ) * (((d : ℝ) / n) ^ d * ((K : ℝ) ^ i / (K : ℝ) ^ d)) := by
                rw [div_pow, div_pow, mul_pow]
                field_simp
            _ ≤ (n.choose i : ℝ) * (((d : ℝ) / n) ^ i * 1) :=
                mul_le_mul_of_nonneg_left
                  (mul_le_mul hpow_d hK_div (by positivity) (by positivity))
                  (Nat.cast_nonneg _)
            _ = ((d : ℝ) / n) ^ i * (n.choose i : ℝ) := by ring
      _ ≤ ∑ i ∈ Finset.range (n + 1), ((d : ℝ) / n) ^ i * 1 ^ (n - i) * (n.choose i : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.range_mono (Nat.succ_le_succ hdn)) (fun _ _ _ => by positivity)
      _ = ((d : ℝ) / n + 1) ^ n := (add_pow ((d : ℝ) / n) 1 n).symm
      _ ≤ (Real.exp ((d : ℝ) / n)) ^ n :=
          pow_le_pow_left₀ (by positivity) (Real.add_one_le_exp _) n
      _ = Real.exp d := by
          rw [← Real.exp_nat_mul]
          congr 1
          field_simp
  have hscale_pos : (0 : ℝ) < ((d : ℝ) / (K * n)) ^ d := by positivity
  rw [← mul_le_mul_iff_right₀ hscale_pos]
  refine hscaled.trans_eq ?_
  have hexp : Real.exp d = (Real.exp 1) ^ d := by
    rw [← Real.exp_nat_mul, mul_one]
  rw [hexp, ← mul_pow]
  congr 1
  field_simp

/-- Pair left and right depth-`n` subtree covers for a fixed root label `b` into at most
`B` depth-`(n + 1)` trees whenever `VL.card ≤ B` and `VR.card ≤ B`. -/
private theorem pair_branch_covers {α β : Type*} [Inhabited β] {n B : ℕ} (r : α) (b : β)
    {xL xR : SeqTree α n} {H : Set (α → β)} (hroot : ∀ h ∈ H, h r = b)
    {VL VR : Finset (SeqTree β n)} (hL : VL.card ≤ B) (hR : VR.card ≤ B)
    (hcL : ∀ h ∈ H, ∀ ε : Fin n → Bool, ∃ u ∈ VL, ∀ j : Fin n,
      u.evalPath ε j = h (xL.evalPath ε j))
    (hcR : ∀ h ∈ H, ∀ ε : Fin n → Bool, ∃ w ∈ VR, ∀ j : Fin n,
      w.evalPath ε j = h (xR.evalPath ε j)) :
    ∃ V : Finset (SeqTree β (n + 1)),
      V.card ≤ B ∧
      ∀ h ∈ H, ∀ ε : Fin (n + 1) → Bool, ∃ v ∈ V, ∀ i : Fin (n + 1),
        v.evalPath ε i = h ((SeqTree.branch r xL xR).evalPath ε i) := by
  classical
  let eL : Fin VL.card ≃ ↥VL := (Fintype.equivFinOfCardEq (Fintype.card_coe VL)).symm
  let eR : Fin VR.card ≃ ↥VR := (Fintype.equivFinOfCardEq (Fintype.card_coe VR)).symm
  let fL (t : Fin B) : SeqTree β n :=
    if h : t.val < VL.card then (eL ⟨t.val, h⟩).val else default
  let fR (t : Fin B) : SeqTree β n :=
    if h : t.val < VR.card then (eR ⟨t.val, h⟩).val else default
  let V : Finset (SeqTree β (n + 1)) :=
    Finset.univ.image fun t : Fin B => SeqTree.branch b (fL t) (fR t)
  refine ⟨V, Finset.card_image_le.trans (by simp), fun h hh ε => ?_⟩
  cases h0 : ε 0
  · obtain ⟨u, hu, hup⟩ := hcL h hh (ε ∘ Fin.succ)
    let idx : Fin VL.card := eL.symm ⟨u, hu⟩
    let t : Fin B := ⟨idx.val, idx.isLt.trans_le hL⟩
    have hfL : fL t = u := by
      simp only [fL, t, idx.isLt, ↓reduceDIte, Fin.eta]
      exact congrArg Subtype.val (eL.apply_symm_apply ⟨u, hu⟩)
    exact ⟨SeqTree.branch b (fL t) (fR t), Finset.mem_image_of_mem _ (Finset.mem_univ t),
      fun i => Fin.cases (hroot h hh).symm (fun j => by simp [h0, hfL, hup j]) i⟩
  · obtain ⟨w, hw, hwp⟩ := hcR h hh (ε ∘ Fin.succ)
    let idx : Fin VR.card := eR.symm ⟨w, hw⟩
    let t : Fin B := ⟨idx.val, idx.isLt.trans_le hR⟩
    have hfR : fR t = w := by
      simp only [fR, t, idx.isLt, ↓reduceDIte, Fin.eta]
      exact congrArg Subtype.val (eR.apply_symm_apply ⟨w, hw⟩)
    exact ⟨SeqTree.branch b (fL t) (fR t), Finset.mem_image_of_mem _ (Finset.mem_univ t),
      fun i => Fin.cases (hroot h hh).symm (fun j => by simp [h0, hfR, hwp j]) i⟩

/-- **Sequential Sauer–Shelah tree-covering lemma.** For any `{0, …, K}`-valued hypothesis class
`H` whose scale-`1` sequential fat-shattering dimension is at most `d`, and any depth-`n` instance
tree `x : SeqTree α n`, there is a finite set `V` of at most `∑_{i ≤ d} n.choose i * K ^ i`
depth-`n` label trees such that every pair `(h, ε)` with `h ∈ H` and `ε : Fin n → Bool` agrees
with some `v ∈ V` along the entire path `ε`. -/
theorem exists_seqTree_cover_of_seqFatDim_le {α : Type*} (K : ℕ) :
    ∀ (n d : ℕ) {H : Set (α → Fin (K + 1))}
      (_hH : ∀ t : SeqTree α (d + 1), ¬ SeqFatShatters (finClassToReal H) 1 t)
      (x : SeqTree α n),
      ∃ V : Finset (SeqTree (Fin (K + 1)) n),
        V.card ≤ seqCoverSum K n d ∧
        ∀ h ∈ H, ∀ ε : Fin n → Bool, ∃ v ∈ V, ∀ i : Fin n,
          v.evalPath ε i = h (x.evalPath ε i)
  | 0, d, _, _, .nil =>
    ⟨{.nil}, by simp, fun _ _ _ => ⟨.nil, Finset.mem_singleton_self _, fun i => i.elim0⟩⟩
  | n + 1, 0, H, hH, .branch r xL xR => by
    classical
    rcases H.eq_empty_or_nonempty with rfl | ⟨h₀, hh₀⟩
    · exact ⟨∅, by simp, fun _ hf => hf.elim⟩
    -- With `d = 0`, all functions in `H` agree on the root label `r`.
    have hconst : ∀ h ∈ H, h r = h₀ r := by
      intro h hh
      by_contra hne
      have hne_val : (h r).val ≠ (h₀ r).val := fun heq => hne (Fin.ext heq)
      rcases lt_or_gt_of_ne hne_val with hlt | hgt
      · refine hH (.branch r .nil .nil) (seqFatShatters_branch_iff.mpr ?_)
        refine ⟨((h r : ℕ) + (h₀ r : ℕ) : ℝ) / 2,
          seqFatShatters_nil_iff.mpr ⟨_, ⟨h, hh, rfl⟩, ?_⟩,
          seqFatShatters_nil_iff.mpr ⟨_, ⟨h₀, hh₀, rfl⟩, ?_⟩⟩
        · have : ((h r : ℕ) : ℝ) + 1 ≤ (h₀ r : ℕ) := by exact_mod_cast hlt
          linarith
        · have : ((h r : ℕ) : ℝ) + 1 ≤ (h₀ r : ℕ) := by exact_mod_cast hlt
          linarith
      · refine hH (.branch r .nil .nil) (seqFatShatters_branch_iff.mpr ?_)
        refine ⟨((h₀ r : ℕ) + (h r : ℕ) : ℝ) / 2,
          seqFatShatters_nil_iff.mpr ⟨_, ⟨h₀, hh₀, rfl⟩, ?_⟩,
          seqFatShatters_nil_iff.mpr ⟨_, ⟨h, hh, rfl⟩, ?_⟩⟩
        · have : ((h₀ r : ℕ) : ℝ) + 1 ≤ (h r : ℕ) := by exact_mod_cast hgt
          linarith
        · have : ((h₀ r : ℕ) : ℝ) + 1 ≤ (h r : ℕ) := by exact_mod_cast hgt
          linarith
    obtain ⟨VL, hVL, hcovL⟩ := exists_seqTree_cover_of_seqFatDim_le K n 0 hH xL
    obtain ⟨VR, hVR, hcovR⟩ := exists_seqTree_cover_of_seqFatDim_le K n 0 hH xR
    rw [seqCoverSum_zero_right] at hVL hVR
    simpa only [seqCoverSum_zero_right] using
      pair_branch_covers r (h₀ r) hconst hVL hVR hcovL hcovR
  | n + 1, d + 1, H, hH, .branch r xL xR => by
    classical
    let Hj (b : Fin (K + 1)) : Set (α → Fin (K + 1)) := {h ∈ H | h r = b}
    let Big (b : Fin (K + 1)) : Prop :=
      ∃ t : SeqTree α (d + 1), SeqFatShatters (finClassToReal (Hj b)) 1 t
    -- At most one root label `b` can still fat-shatter a tree of depth `d + 1`.
    have huniq : ∀ b₁ b₂ : Fin (K + 1), Big b₁ → Big b₂ → b₁ = b₂ := by
      intro b₁ b₂ ⟨t₁, ht₁⟩ ⟨t₂, ht₂⟩
      by_contra hne
      have hne_val : b₁.val ≠ b₂.val := fun heq => hne (Fin.ext heq)
      rcases lt_or_gt_of_ne hne_val with hlt | hgt
      · refine hH (.branch r t₁ t₂) (seqFatShatters_branch_iff.mpr ?_)
        have hgap : ((b₁ : ℕ) : ℝ) + 1 ≤ (b₂ : ℕ) := by exact_mod_cast hlt
        refine ⟨((b₁ : ℕ) + (b₂ : ℕ) : ℝ) / 2, ht₁.mono ?_, ht₂.mono ?_⟩
        · rintro _ ⟨h, ⟨hh, hhr⟩, rfl⟩
          exact ⟨⟨h, hh, rfl⟩, by simp [hhr]; linarith⟩
        · rintro _ ⟨h, ⟨hh, hhr⟩, rfl⟩
          exact ⟨⟨h, hh, rfl⟩, by simp [hhr]; linarith⟩
      · refine hH (.branch r t₂ t₁) (seqFatShatters_branch_iff.mpr ?_)
        have hgap : ((b₂ : ℕ) : ℝ) + 1 ≤ (b₁ : ℕ) := by exact_mod_cast hgt
        refine ⟨((b₂ : ℕ) + (b₁ : ℕ) : ℝ) / 2, ht₂.mono ?_, ht₁.mono ?_⟩
        · rintro _ ⟨h, ⟨hh, hhr⟩, rfl⟩
          exact ⟨⟨h, hh, rfl⟩, by simp [hhr]; linarith⟩
        · rintro _ ⟨h, ⟨hh, hhr⟩, rfl⟩
          exact ⟨⟨h, hh, rfl⟩, by simp [hhr]; linarith⟩
    -- Pick the unique possible `Big` label `bStar` (defaulting to `0` if none exists).
    let bStar : Fin (K + 1) := if h : ∃ b, Big b then h.choose else 0
    have hsmall : ∀ b : Fin (K + 1), b ≠ bStar →
        ∀ t : SeqTree α (d + 1), ¬ SeqFatShatters (finClassToReal (Hj b)) 1 t := by
      intro b hb t ht
      have hex : ∃ b', Big b' := ⟨b, t, ht⟩
      have heq : b = bStar := by
        simp only [bStar, hex, ↓reduceDIte]
        exact huniq b hex.choose ⟨t, ht⟩ hex.choose_spec
      exact hb heq
    -- Build per-label covers `Vb b` of size `seqCoverSum K n (d + 1)` at `bStar`
    -- and `seqCoverSum K n d` at every `b ≠ bStar`.
    have hper : ∀ b : Fin (K + 1), ∃ Vb : Finset (SeqTree (Fin (K + 1)) (n + 1)),
        Vb.card ≤ (if b = bStar then seqCoverSum K n (d + 1) else seqCoverSum K n d) ∧
        ∀ h ∈ Hj b, ∀ ε : Fin (n + 1) → Bool, ∃ v ∈ Vb, ∀ i : Fin (n + 1),
          v.evalPath ε i = h ((SeqTree.branch r xL xR).evalPath ε i) := by
      intro b
      by_cases hb : b = bStar
      · have hHb : ∀ t : SeqTree α (d + 2), ¬ SeqFatShatters (finClassToReal (Hj b)) 1 t :=
          fun t ht => hH t (ht.mono (Set.image_mono fun _ hf => hf.1))
        obtain ⟨VL, hVL, hcL⟩ := exists_seqTree_cover_of_seqFatDim_le K n (d + 1) hHb xL
        obtain ⟨VR, hVR, hcR⟩ := exists_seqTree_cover_of_seqFatDim_le K n (d + 1) hHb xR
        simpa only [hb, ↓reduceIte] using
          pair_branch_covers r b (fun _ (hh : _ ∈ Hj b) => hh.2) hVL hVR hcL hcR
      · obtain ⟨VL, hVL, hcL⟩ :=
          exists_seqTree_cover_of_seqFatDim_le K n d (hsmall b hb) xL
        obtain ⟨VR, hVR, hcR⟩ :=
          exists_seqTree_cover_of_seqFatDim_le K n d (hsmall b hb) xR
        simpa only [hb, ↓reduceIte] using
          pair_branch_covers r b (fun _ (hh : _ ∈ Hj b) => hh.2) hVL hVR hcL hcR
    choose Vb hVb_card hVb_cov using hper
    refine ⟨Finset.univ.biUnion Vb, ?_, fun h hh ε => ?_⟩
    · calc (Finset.univ.biUnion Vb).card
          ≤ ∑ b : Fin (K + 1), (Vb b).card := Finset.card_biUnion_le
        _ ≤ ∑ b : Fin (K + 1),
              (if b = bStar then seqCoverSum K n (d + 1) else seqCoverSum K n d) :=
            Finset.sum_le_sum fun b _ => hVb_card b
        _ = seqCoverSum K n (d + 1) + K * seqCoverSum K n d := by
            rw [← Finset.add_sum_erase _ _ (Finset.mem_univ bStar)]
            simp only [↓reduceIte]
            congr 1
            have hcongr : ∑ x ∈ Finset.univ.erase bStar,
                (if x = bStar then seqCoverSum K n (d + 1) else seqCoverSum K n d) =
                ∑ _x ∈ Finset.univ.erase bStar, seqCoverSum K n d := by
              refine Finset.sum_congr rfl fun x hx => ?_
              simp [(Finset.mem_erase.mp hx).1]
            rw [hcongr, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ bStar),
              Finset.card_univ, Fintype.card_fin, Nat.add_sub_cancel, smul_eq_mul]
        _ = seqCoverSum K (n + 1) (d + 1) := (seqCoverSum_succ K n d).symm
    · obtain ⟨v, hv, hvp⟩ := hVb_cov (h r) h ⟨hh, rfl⟩ ε
      exact ⟨v, Finset.mem_biUnion.mpr ⟨h r, Finset.mem_univ _, hv⟩, hvp⟩

/-- Exponential form of the Rakhlin–Sridharan–Tewari sequential covering bound for
`{0, …, K}`-valued classes with `1 ≤ seqFatDim ≤ d ≤ n` and `1 ≤ K`:
`|V| ≤ (e * K * n / d) ^ d`. -/
theorem exists_seqTree_cover_le_exp_pow {α : Type*} {K n d : ℕ} (hK : 1 ≤ K) (hd : 1 ≤ d)
    (hdn : d ≤ n) {H : Set (α → Fin (K + 1))} (hdim : seqFatDim (finClassToReal H) 1 ≤ d)
    (x : SeqTree α n) :
    ∃ V : Finset (SeqTree (Fin (K + 1)) n),
      (V.card : ℝ) ≤ (Real.exp 1 * K * n / d) ^ d ∧
      ∀ h ∈ H, ∀ ε : Fin n → Bool, ∃ v ∈ V, ∀ i : Fin n,
        v.evalPath ε i = h (x.evalPath ε i) := by
  have hno : ∀ t : SeqTree α (d + 1), ¬ SeqFatShatters (finClassToReal H) 1 t := by
    intro t ht
    have hle : ((d + 1 : ℕ) : ℕ∞) ≤ (d : ℕ∞) := ht.le_seqFatDim.trans hdim
    exact (Nat.not_succ_le_self d) (Nat.cast_le.mp hle)
  obtain ⟨V, hVc, hcov⟩ := exists_seqTree_cover_of_seqFatDim_le K n d hno x
  exact ⟨V, (Nat.cast_le.mpr hVc).trans (seqCoverSum_le_exp_mul_div_pow hK hd hdn), hcov⟩

/-- **Binary sequential Sauer–Shelah tree-covering lemma.** For any Boolean concept class `H` with
`littlestoneDim H ≤ d` and any depth-`n` instance tree `x : SeqTree α n`, there is a finite set
`V` of at most `∑_{i ≤ d} n.choose i` depth-`n` Boolean trees covering all `(h, ε)`. -/
theorem exists_bool_seqTree_cover_of_littlestoneDim_le {α : Type*} {n d : ℕ}
    {H : Set (α → Bool)} (hdim : littlestoneDim H ≤ d) (x : SeqTree α n) :
    ∃ V : Finset (SeqTree Bool n),
      V.card ≤ ∑ i ∈ Finset.range (d + 1), n.choose i ∧
      ∀ h ∈ H, ∀ ε : Fin n → Bool, ∃ v ∈ V, ∀ i : Fin n,
        v.evalPath ε i = h (x.evalPath ε i) := by
  classical
  let toFin : Bool → Fin 2 := fun b => if b then 1 else 0
  let ofFin : Fin 2 → Bool := fun k => decide (k = 1)
  have hleft : ∀ b : Bool, ofFin (toFin b) = b := by intro b; cases b <;> rfl
  let H' : Set (α → Fin 2) := (fun h a => toFin (h a)) '' H
  have hreal : finClassToReal H' = boolClassToReal H := by
    ext f
    simp only [finClassToReal, H', boolClassToReal, Set.mem_image, exists_exists_and_eq_and]
    refine exists_congr fun h => and_congr_right fun _ => ?_
    have heq : (fun a => (((toFin (h a) : Fin 2) : ℕ) : ℝ)) =
        (fun a => ((h a).toNat : ℝ)) := by
      funext a; cases h a <;> simp [toFin]
    rw [heq]
  have hno : ∀ t : SeqTree α (d + 1), ¬ SeqFatShatters (finClassToReal H') 1 t := by
    intro t ht
    rw [hreal] at ht
    have hle : ((d + 1 : ℕ) : ℕ∞) ≤ (d : ℕ∞) :=
      ht.le_seqFatDim.trans ((seqFatDim_bool_one_eq_littlestoneDim H).trans_le hdim)
    exact (Nat.not_succ_le_self d) (Nat.cast_le.mp hle)
  obtain ⟨V', hVc, hcov⟩ := exists_seqTree_cover_of_seqFatDim_le 1 n d hno x
  refine ⟨V'.image (SeqTree.map ofFin), ?_, fun h hh ε => ?_⟩
  · exact Finset.card_image_le.trans (by simpa using hVc)
  · obtain ⟨v', hv', hvp⟩ := hcov (fun a => toFin (h a)) ⟨h, hh, rfl⟩ ε
    refine ⟨v'.map ofFin, Finset.mem_image_of_mem _ hv', fun i => ?_⟩
    rw [SeqTree.evalPath_map, hvp i, hleft]

/-- Exponential form of the binary sequential Sauer–Shelah covering bound: for
`1 ≤ d ≤ n` and `littlestoneDim H ≤ d`, `|V| ≤ (e * n / d) ^ d` (and hence also
`≤ (2 * e * n / d) ^ d`). -/
theorem exists_bool_seqTree_cover_le_exp_pow {α : Type*} {n d : ℕ} (hd : 1 ≤ d) (hdn : d ≤ n)
    {H : Set (α → Bool)} (hdim : littlestoneDim H ≤ d) (x : SeqTree α n) :
    ∃ V : Finset (SeqTree Bool n),
      (V.card : ℝ) ≤ (Real.exp 1 * n / d) ^ d ∧
      (V.card : ℝ) ≤ (2 * Real.exp 1 * n / d) ^ d ∧
      ∀ h ∈ H, ∀ ε : Fin n → Bool, ∃ v ∈ V, ∀ i : Fin n,
        v.evalPath ε i = h (x.evalPath ε i) := by
  obtain ⟨V, hVc, hcov⟩ := exists_bool_seqTree_cover_of_littlestoneDim_le hdim x
  have h1 : (V.card : ℝ) ≤ (Real.exp 1 * n / d) ^ d := by
    have := seqCoverSum_le_exp_mul_div_pow (K := 1) le_rfl hd hdn
    rw [seqCoverSum_one_left, Nat.cast_one, mul_one] at this
    exact (Nat.cast_le.mpr hVc).trans this
  have h2 : (Real.exp 1 * n / d) ^ d ≤ (2 * Real.exp 1 * n / d) ^ d := by
    have he : 0 ≤ Real.exp 1 := (Real.exp_pos 1).le
    gcongr
    linarith [mul_nonneg he (Nat.cast_nonneg n)]
  exact ⟨V, h1, h1.trans h2, hcov⟩

/-- **Distinct adaptively realized paths occupy distinct covering trees.** If each path
`ε ∈ P` is matched by some tree `v ∈ V` with labels `label ε i`, and whenever two paths
`ε₁, ε₂ ∈ P` first disagree at depth `i₀` they produce distinct labels `label ε₁ j ≠ label ε₂ j`
at some depth `j ≤ i₀`, then `P.card ≤ V.card`. -/
theorem card_le_of_seqTree_cover {β : Type*} {n : ℕ} {P : Finset (Fin n → Bool)}
    {V : Finset (SeqTree β n)} {label : (Fin n → Bool) → Fin n → β}
    (hcov : ∀ ε ∈ P, ∃ v ∈ V, ∀ i : Fin n, v.evalPath ε i = label ε i)
    (hsep : ∀ ε₁ ∈ P, ∀ ε₂ ∈ P, ∀ i₀ : Fin n,
      (∀ k : Fin n, k < i₀ → ε₁ k = ε₂ k) → ε₁ i₀ ≠ ε₂ i₀ →
      ∃ j : Fin n, j ≤ i₀ ∧ label ε₁ j ≠ label ε₂ j) :
    P.card ≤ V.card := by
  classical
  let pick : (p : P) → V := fun p =>
    ⟨(hcov p.1 p.2).choose, (hcov p.1 p.2).choose_spec.1⟩
  have hinj : Function.Injective pick := by
    intro p₁ p₂ heq
    by_contra hne
    have hfn : p₁.1 ≠ p₂.1 := fun h => hne (Subtype.ext h)
    have hex : ∃ i : Fin n, p₁.1 i ≠ p₂.1 i := Function.ne_iff.mp hfn
    let S : Finset (Fin n) := Finset.univ.filter fun i => p₁.1 i ≠ p₂.1 i
    have hSne : S.Nonempty := by
      obtain ⟨i, hi⟩ := hex
      exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
    let i₀ : Fin n := S.min' hSne
    have hi₀_ne : p₁.1 i₀ ≠ p₂.1 i₀ := (Finset.mem_filter.mp (Finset.min'_mem S hSne)).2
    have hi₀_prev : ∀ k : Fin n, k < i₀ → p₁.1 k = p₂.1 k := by
      intro k hk
      by_contra hkne
      exact not_le_of_gt hk (Finset.min'_le S k (Finset.mem_filter.mpr ⟨Finset.mem_univ k, hkne⟩))
    obtain ⟨j, hji₀, hj_ne⟩ := hsep p₁.1 p₁.2 p₂.1 p₂.2 i₀ hi₀_prev hi₀_ne
    have hv_eq : (pick p₁).1 = (pick p₂).1 := congrArg Subtype.val heq
    have hp₁ := (hcov p₁.1 p₁.2).choose_spec.2 j
    have hp₂ := (hcov p₂.1 p₂.2).choose_spec.2 j
    change (pick p₁).1.evalPath p₁.1 j = label p₁.1 j at hp₁
    change (pick p₂).1.evalPath p₂.1 j = label p₂.1 j at hp₂
    have hcongr : (pick p₁).1.evalPath p₁.1 j = (pick p₁).1.evalPath p₂.1 j :=
      SeqTree.evalPath_congr _ fun k hk => hi₀_prev k (hk.trans_le hji₀)
    exact hj_ne (hp₁.symm.trans (hcongr.trans (hv_eq ▸ hp₂)))
  simpa using Fintype.card_le_of_injective pick hinj

/-! ### Pollard's pseudo-dimension -/

/-- A real-valued function class `H` *pseudo-shatters* points `x : Fin d → α` with real
thresholds `θ : Fin d → ℝ` if every binary threshold pattern `b : Fin d → Bool` is realized
by `i ↦ decide (θ i ≤ h (x i))` for some `h ∈ H`.
-/
def PseudoShatters {α : Type*} (H : Set (α → ℝ)) {d : ℕ} (x : Fin d → α) (θ : Fin d → ℝ) :
    Prop :=
  ∀ b : Fin d → Bool, ∃ h ∈ H, ∀ i : Fin d, decide (θ i ≤ h (x i)) = b i

/-- Pollard's *pseudo-dimension* (also known as VC-subgraph dimension) of a real-valued
function class `H : Set (α → ℝ)`, valued in `ℕ∞`. -/
noncomputable def pseudoDim {α : Type*} (H : Set (α → ℝ)) : ℕ∞ :=
  ⨆ (d : ℕ) (_ : ∃ (x : Fin d → α) (θ : Fin d → ℝ), PseudoShatters H x θ), (d : ℕ∞)

/-- The binary subgraph (threshold-indicator) concept class
`{(a, t) ↦ decide (t ≤ h a) | h ∈ H}` on `α × ℝ`. -/
noncomputable def subgraphClass {α : Type*} (H : Set (α → ℝ)) : ConceptClass (α × ℝ) Bool :=
  (fun h (p : α × ℝ) => decide (p.2 ≤ h p.1)) '' H

/-- Every pseudo-shattered `d`-tuple gives a lower bound `d ≤ pseudoDim H`. -/
theorem PseudoShatters.le_pseudoDim {α : Type*} {H : Set (α → ℝ)} {d : ℕ}
    {x : Fin d → α} {θ : Fin d → ℝ} (h : PseudoShatters H x θ) :
    (d : ℕ∞) ≤ pseudoDim H :=
  le_iSup₂_of_le d ⟨x, θ, h⟩ le_rfl

/-- Upper-bound characterization of `pseudoDim`. -/
theorem pseudoDim_le_iff {α : Type*} {H : Set (α → ℝ)} {m : ℕ∞} :
    pseudoDim H ≤ m ↔
      ∀ (d : ℕ) (x : Fin d → α) (θ : Fin d → ℝ), PseudoShatters H x θ → (d : ℕ∞) ≤ m := by
  simp only [pseudoDim, iSup₂_le_iff, forall_exists_index]

/-- `pseudoDim` is monotone in the function class. -/
theorem pseudoDim_mono {α : Type*} {H H' : Set (α → ℝ)} (hsub : H ⊆ H') :
    pseudoDim H ≤ pseudoDim H' :=
  pseudoDim_le_iff.mpr fun _ _ _ hx =>
    PseudoShatters.le_pseudoDim fun b => let ⟨h, hh, hb⟩ := hx b; ⟨h, hsub hh, hb⟩

/-- A class has infinite pseudo-dimension iff it pseudo-shatters tuples of arbitrarily large
finite size. -/
theorem pseudoDim_eq_top_iff {α : Type*} {H : Set (α → ℝ)} :
    pseudoDim H = ⊤ ↔
      ∀ d : ℕ, ∃ (x : Fin d → α) (θ : Fin d → ℝ), PseudoShatters H x θ := by
  constructor
  · intro htop d
    rcases d with _ | d
    · have hlt : (0 : ℕ∞) < pseudoDim H := by simp [htop]
      simp only [pseudoDim, lt_iSup_iff] at hlt
      obtain ⟨k, ⟨x, θ, hk⟩, -⟩ := hlt
      obtain ⟨h, hh, -⟩ := hk (fun _ => false)
      exact ⟨Fin.elim0, Fin.elim0, fun _ => ⟨h, hh, fun i => i.elim0⟩⟩
    · have hlt : (d : ℕ∞) < pseudoDim H := by rw [htop]; exact ENat.natCast_lt_top d
      simp only [pseudoDim, lt_iSup_iff] at hlt
      obtain ⟨k, ⟨x, θ, hk⟩, hdk⟩ := hlt
      have hle : d + 1 ≤ k := Nat.succ_le_of_lt (Nat.cast_lt.mp hdk)
      let emb : Fin (d + 1) → Fin k := Fin.castLE hle
      refine ⟨x ∘ emb, θ ∘ emb, fun b => ?_⟩
      let b' : Fin k → Bool := fun j => if h : j.val < d + 1 then b ⟨j.val, h⟩ else false
      obtain ⟨f, hf, hfb⟩ := hk b'
      exact ⟨f, hf, fun i => by
        have := hfb (emb i)
        simp only [b', emb, Fin.val_castLE, i.isLt, ↓reduceDIte, Fin.eta] at this
        exact this⟩
  · intro h
    by_contra hne
    obtain ⟨d, hd⟩ := ENat.ne_top_iff_exists.mp hne
    obtain ⟨x, θ, hsh⟩ := h (d + 1)
    have hle : ((d + 1 : ℕ) : ℕ∞) ≤ (d : ℕ∞) := hd ▸ hsh.le_pseudoDim
    exact (Nat.not_succ_le_self d) (Nat.cast_le.mp hle)

/-- Pseudo-shattering with weak inequalities (`θ i ≤ h (x i)` vs `h (x i) < θ i`) and with
strict bilateral inequalities (`θ i < h (x i)` vs `h (x i) < θ i`) have witnesses on the
exact same tuples `x : Fin d → α`. -/
theorem exists_pseudoShatters_iff_strict {α : Type*} {H : Set (α → ℝ)} {d : ℕ}
    (x : Fin d → α) :
    (∃ θ : Fin d → ℝ, PseudoShatters H x θ) ↔
      ∃ θ : Fin d → ℝ, ∀ b : Fin d → Bool, ∃ h ∈ H, ∀ i : Fin d,
        (b i = true → θ i < h (x i)) ∧ (b i = false → h (x i) < θ i) := by
  classical
  constructor
  · rintro ⟨θ, hθ⟩
    choose f hf hfb using hθ
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · exact ⟨Fin.elim0, fun b => ⟨f b, hf b, fun i => i.elim0⟩⟩
    -- Shift each threshold `θ i` slightly downward into the open gap above all `false` values.
    let θ' (i : Fin d) : ℝ :=
      let falses : Finset (Fin d → Bool) := Finset.univ.filter fun b => b i = false
      have hne : falses.Nonempty :=
        ⟨fun _ => false, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩
      let m := falses.sup' hne fun b => f b (x i)
      (m + θ i) / 2
    refine ⟨θ', fun b => ⟨f b, hf b, fun i => ?_⟩⟩
    let falses : Finset (Fin d → Bool) := Finset.univ.filter fun b' => b' i = false
    have hne : falses.Nonempty :=
      ⟨fun _ => false, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩
    have hsup_lt : falses.sup' hne (fun b' => f b' (x i)) < θ i := by
      rw [Finset.sup'_lt_iff]
      intro b' hb'
      have hb'i : b' i = false := (Finset.mem_filter.mp hb').2
      have := hfb b' i
      rw [hb'i, decide_eq_false_iff_not, not_le] at this
      exact this
    have hθ' : θ' i = (falses.sup' hne (fun b' => f b' (x i)) + θ i) / 2 := rfl
    refine ⟨fun hbi => ?_, fun hbi => ?_⟩
    · have hge : θ i ≤ f b (x i) := by simpa [hbi] using hfb b i
      linarith
    · have hle : f b (x i) ≤ falses.sup' hne (fun b' => f b' (x i)) :=
        Finset.le_sup' (fun b' => f b' (x i)) (Finset.mem_filter.mpr ⟨Finset.mem_univ b, hbi⟩)
      linarith
  · rintro ⟨θ, hθ⟩
    refine ⟨θ, fun b => ?_⟩
    obtain ⟨h, hh, hhb⟩ := hθ b
    refine ⟨h, hh, fun i => ?_⟩
    cases hbi : b i
    · exact decide_eq_false (not_le_of_gt ((hhb i).2 hbi))
    · exact decide_eq_true (le_of_lt ((hhb i).1 hbi))

/-- Points in a pseudo-shattered tuple are pairwise distinct. -/
theorem PseudoShatters.injective {α : Type*} {H : Set (α → ℝ)} {d : ℕ}
    {x : Fin d → α} {θ : Fin d → ℝ} (h : PseudoShatters H x θ) :
    Function.Injective x := by
  classical
  intro i j hij
  by_contra hne
  rcases le_total (θ i) (θ j) with hle | hle
  · let b : Fin d → Bool := fun k => decide (k = j)
    obtain ⟨f, -, hfb⟩ := h b
    have hi : f (x i) < θ i := by
      have := hfb i; simp only [b, hne, decide_false, decide_eq_false_iff_not, not_le] at this
      exact this
    have hj : θ j ≤ f (x j) := by
      have := hfb j; simpa [b] using this
    rw [hij] at hi
    linarith
  · let b : Fin d → Bool := fun k => decide (k = i)
    obtain ⟨f, -, hfb⟩ := h b
    have hj : f (x j) < θ j := by
      have := hfb j
      simp only [b, Ne.symm hne, decide_false, decide_eq_false_iff_not, not_le] at this
      exact this
    have hi : θ i ≤ f (x i) := by
      have := hfb i; simpa [b] using this
    rw [hij] at hi
    linarith

/-- Pollard's pseudo-dimension coincides with the Vapnik–Chervonenkis dimension (`evcDim`)
of the subgraph concept class `subgraphClass H`. -/
theorem pseudoDim_eq_evcDim_subgraphClass {α : Type*} (H : Set (α → ℝ)) :
    pseudoDim H = evcDim (subgraphClass H) := by
  classical
  apply le_antisymm
  · rw [pseudoDim_le_iff]
    intro d x θ hsh
    have hinj : Function.Injective (fun i : Fin d => (x i, θ i)) :=
      fun i j h => hsh.injective (congrArg Prod.fst h)
    let W : Finset (α × ℝ) := Finset.univ.image fun i : Fin d => (x i, θ i)
    have hcard : W.card = d := by
      rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
    have hW : SetShatters (subgraphClass H) (W : Set (α × ℝ)) := by
      intro U hU
      obtain ⟨h, hh, hhb⟩ := hsh (fun i => decide ((x i, θ i) ∈ U))
      refine ⟨fun p => decide (p.2 ≤ h p.1), ⟨h, hh, rfl⟩, ?_⟩
      ext p
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, Finset.mem_coe,
        W, Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨hp, i, rfl⟩
        simpa [hhb i] using hp
      · intro hpU
        obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp (hU hpU))
        exact ⟨by simpa [hpU] using hhb i, i, rfl⟩
    rw [← hcard]
    exact hW.card_le_evcDim
  · rw [evcDim_le_iff]
    intro W hW
    let e : Fin W.card ≃ ↥W := (Fintype.equivFinOfCardEq (Fintype.card_coe W)).symm
    have hsh : PseudoShatters H (fun i => (e i).val.1) (fun i => (e i).val.2) := by
      intro b
      let U : Set (α × ℝ) := {p ∈ (W : Set (α × ℝ)) | ∃ i, (e i).val = p ∧ b i = true}
      obtain ⟨_, ⟨h, hh, rfl⟩, hhU⟩ := hW U (fun _ hp => hp.1)
      refine ⟨h, hh, fun i => ?_⟩
      have hmem : decide ((e i).val.2 ≤ h (e i).val.1) = true ↔ (e i).val ∈ U := by
        have := congrArg ((e i).val ∈ ·) hhU
        simpa [(e i).property] using this
      have hbi : (e i).val ∈ U ↔ b i = true :=
        ⟨fun ⟨_, j, hj, hbj⟩ => (e.injective (Subtype.ext hj)) ▸ hbj,
          fun hbi => ⟨(e i).property, i, rfl, hbi⟩⟩
      rw [hbi] at hmem
      cases hb : b i
      · exact Bool.eq_false_iff.mpr fun ht => Bool.false_ne_true (hb.symm.trans (hmem.mp ht))
      · exact hmem.mpr hb
    exact hsh.le_pseudoDim

/-! ### Logarithmic growth-function inversion -/

/-- For all `a, b > 0`, `log a ≤ a * b - log b - 1`
.
-/
theorem log_le_mul_sub_log_sub_one {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Real.log a ≤ a * b - Real.log b - 1 := by
  have hab : 0 < a * b := mul_pos ha hb
  have h := Real.log_le_sub_one_of_pos hab
  rw [Real.log_mul ha.ne' hb.ne'] at h
  linarith

/-- Equality holds in `log_le_mul_sub_log_sub_one` if and only if `a * b = 1`. -/
theorem log_eq_mul_sub_log_sub_one_iff {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Real.log a = a * b - Real.log b - 1 ↔ a * b = 1 := by
  have hab : 0 < a * b := mul_pos ha hb
  constructor
  · intro heq
    by_contra hne
    have hlt := Real.log_lt_sub_one_of_pos hab hne
    rw [Real.log_mul ha.ne' hb.ne'] at hlt
    linarith
  · intro h1
    have hlog : Real.log a + Real.log b = 0 := by
      rw [← Real.log_mul ha.ne' hb.ne', h1, Real.log_one]
    linarith

/-- **Logarithmic growth-function inversion.** For every `N ≥ 1` and `M > 0` with
`1 ≤ N * M`, there exists `m : ℕ` such that `N ≤ m`,
`m ≤ 3 * N * log₂ (2 * N * M / log 2)`, and `N * log₂ (e * m * M) < m`. -/
theorem exists_nat_gt_mul_logb_exp_mul {N : ℕ} (hN : 1 ≤ N) {M : ℝ} (hM : 0 < M)
    (hNM : 1 ≤ (N : ℝ) * M) :
    ∃ m : ℕ, N ≤ m ∧
      (m : ℝ) ≤ 3 * (N : ℝ) * Real.logb 2 (2 * (N : ℝ) * M / Real.log 2) ∧
      (N : ℝ) * Real.logb 2 (Real.exp 1 * (m : ℝ) * M) < (m : ℝ) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2_lt1 : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
  have hN_pos : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hN_ge1 : (1 : ℝ) ≤ N := Nat.one_le_cast.mpr hN
  set L : ℝ := Real.logb 2 (2 * (N : ℝ) * M / Real.log 2)
  have harg : 2 < 2 * (N : ℝ) * M / Real.log 2 := by
    rw [lt_div_iff₀ hlog2]
    nlinarith
  have hL_gt1 : 1 < L := by
    dsimp [L]
    rw [Real.lt_logb_iff_rpow_lt (by norm_num) (by linarith), Real.rpow_one]
    exact harg
  have hNL_gt1 : 1 < (N : ℝ) * L := by nlinarith
  let m : ℕ := ⌊2 * (N : ℝ) * L⌋₊ + 1
  have hm_pos : 0 < m := Nat.succ_pos _
  have hm_gt : 2 * (N : ℝ) * L < (m : ℝ) := by
    have hcast : (m : ℝ) = (⌊2 * (N : ℝ) * L⌋₊ : ℝ) + 1 := by simp [m]
    rw [hcast]
    exact Nat.lt_floor_add_one (2 * (N : ℝ) * L)
  have hm_le : (m : ℝ) ≤ 3 * (N : ℝ) * L := by
    have hfl : (⌊2 * (N : ℝ) * L⌋₊ : ℝ) ≤ 2 * (N : ℝ) * L := Nat.floor_le (by positivity)
    have hcast : (m : ℝ) = (⌊2 * (N : ℝ) * L⌋₊ : ℝ) + 1 := by simp [m]
    linarith
  have hNm : N ≤ m := by
    have : (N : ℝ) < (m : ℝ) := by nlinarith
    exact_mod_cast this.le
  refine ⟨m, hNm, hm_le, ?_⟩
  have ha : 0 < Real.exp 1 * (m : ℝ) * M := by positivity
  have hb : 0 < Real.log 2 / (2 * Real.exp 1 * (N : ℝ) * M) := by positivity
  have hineq := log_le_mul_sub_log_sub_one ha hb
  have hprod : (Real.exp 1 * (m : ℝ) * M) * (Real.log 2 / (2 * Real.exp 1 * (N : ℝ) * M)) =
      (m : ℝ) * Real.log 2 / (2 * (N : ℝ)) := by
    have he : Real.exp 1 ≠ 0 := (Real.exp_pos 1).ne'
    have hM' : M ≠ 0 := hM.ne'
    field_simp
  have hlogb : -Real.log (Real.log 2 / (2 * Real.exp 1 * (N : ℝ) * M)) - 1 =
      Real.log (2 * (N : ℝ) * M / Real.log 2) := by
    rw [← Real.log_inv, inv_div,
      show 2 * Real.exp 1 * (N : ℝ) * M / Real.log 2 =
        Real.exp 1 * (2 * (N : ℝ) * M / Real.log 2) by ring,
      Real.log_mul (Real.exp_pos 1).ne' (by positivity), Real.log_exp]
    ring
  have hstep : Real.log (Real.exp 1 * (m : ℝ) * M) ≤
      (m : ℝ) * Real.log 2 / (2 * (N : ℝ)) + Real.log (2 * (N : ℝ) * M / Real.log 2) := by
    linarith [hineq, hprod, hlogb]
  have hdiv : Real.logb 2 (Real.exp 1 * (m : ℝ) * M) ≤ (m : ℝ) / (2 * (N : ℝ)) + L := by
    simp only [Real.logb, L]
    rw [← div_le_div_iff_of_pos_right hlog2] at hstep
    refine hstep.trans_eq ?_
    field_simp
  have hmul : (N : ℝ) * Real.logb 2 (Real.exp 1 * (m : ℝ) * M) ≤ (m : ℝ) / 2 + (N : ℝ) * L := by
    have := mul_le_mul_of_nonneg_left hdiv hN_pos.le
    refine this.trans_eq ?_
    field_simp
  linarith

/-! ### Finite-sample No-Free-Lunch lower bound on shattered sets -/

/-- **Uniform-distribution No-Free-Lunch lower bound on a shattered set.** If a Boolean
concept class `C` shatters a finite set `W` and `2 * m < W.card`, then under the uniform
distribution `P` on `W`, for every deterministic learning rule
`A : LabeledSample α Bool m → α → Bool` there exists `c ∈ C` such that
`P {x | A S x ≠ c x} ≥ 1 / 4` holds with probability at least `1 / 2` over `m` i.i.d. draws
from `P`. -/
theorem exists_concept_prob_error_ge_quarter_ge_half {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] {C : ConceptClass α Bool} {W : Finset α}
    (hW : SetShatters C (W : Set α)) {m : ℕ} (hm : 2 * m < W.card)
    (A : LabeledSample α Bool m → α → Bool) :
    ∃ (P : Measure α), IsProbabilityMeasure P ∧ P (W : Set α)ᶜ = 0 ∧
      ∃ c ∈ C, (1 / 2 : ℝ≥0∞) ≤
        Measure.pi (fun _ : Fin m => P)
          {xs : Fin m → α |
            (1 / 4 : ℝ≥0∞) ≤ P {x : α | A (fun i => (xs i, c (xs i))) x ≠ c x}} := by
  classical
  have hW_pos : 0 < W.card := by omega
  have hW_ne : W.Nonempty := Finset.card_pos.mp hW_pos
  let μ : PMF α := Cslib.Probability.PMF.uniformOfFinset W hW_ne
  let P : Measure α := μ.toMeasure
  have hP_prob : IsProbabilityMeasure P := PMF.toMeasure.isProbabilityMeasure μ
  have hP_compl : P (W : Set α)ᶜ = 0 := by
    rw [PMF.toMeasure_apply μ W.finite_toSet.measurableSet.compl]
    refine tsum_eq_zero_iff.mpr fun a => ?_
    by_cases ha : a ∈ W
    · simp [Set.indicator_of_notMem, ha]
    · simp [μ, Cslib.Probability.PMF.uniformOfFinset_apply, ha]
  have hP_err : ∀ f g : α → Bool,
      P {x : α | f x ≠ g x} = ((W.filter fun x => f x ≠ g x).card : ℝ≥0∞) / W.card := by
    intro f g
    change μ.toMeasure {x : α | f x ≠ g x} = _
    rw [PMF.toMeasure_apply_eq_toOuterMeasure, PMF.toOuterMeasure_apply]
    have hsum : (∑' a : α, Set.indicator {x : α | f x ≠ g x} μ a) =
        ∑ a ∈ W.filter (fun x => f x ≠ g x), (W.card : ℝ≥0∞)⁻¹ := by
      rw [tsum_eq_sum (s := W.filter fun x => f x ≠ g x)]
      · refine Finset.sum_congr rfl fun a ha => ?_
        obtain ⟨haW, hfg⟩ := Finset.mem_filter.mp ha
        have hmem : a ∈ {x : α | f x ≠ g x} := hfg
        rw [Set.indicator_of_mem hmem]
        simp [μ, Cslib.Probability.PMF.uniformOfFinset_apply, haW]
      · intro a ha
        by_cases haW : a ∈ W
        · have hfg : a ∉ {x : α | f x ≠ g x} := fun h => ha (Finset.mem_filter.mpr ⟨haW, h⟩)
          exact Set.indicator_of_notMem hfg μ
        · simp [Set.indicator_apply, μ, Cslib.Probability.PMF.uniformOfFinset_apply, haW]
    rw [hsum, Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]
  -- Pick one shattering witness concept `c_b ∈ C` for each labeling `b : W → Bool`.
  have hex_c : ∀ b : ↥W → Bool, ∃ c ∈ C, ∀ w : ↥W, c w.1 = b w := by
    intro b
    obtain ⟨c, hc, hcb⟩ := hW {a ∈ (W : Set α) | ∃ w : ↥W, w.1 = a ∧ b w = true} (fun _ h => h.1)
    refine ⟨c, hc, fun w => ?_⟩
    have hmem : c w.1 = true ↔ b w = true := by
      have := congrArg (w.1 ∈ ·) hcb
      simpa [w.2, Subtype.ext_iff] using this
    cases hbw : b w
    · exact Bool.eq_false_iff.mpr fun ht => Bool.false_ne_true (hbw.symm.trans (hmem.mp ht))
    · exact hmem.mpr hbw
  choose cOf hcOf_mem hcOf_eq using hex_c
  -- Indicator of incurring error `≥ 1/4` on tuple `xs : Fin m → W` under labeling `b : W → Bool`.
  let isBad (xs : Fin m → W) (b : W → Bool) : Bool :=
    decide (W.card ≤ 4 * (W.filter fun x =>
      A (fun i => ((xs i).1, b (xs i))) x ≠ cOf b x).card)
  -- For every fixed sample `xs : Fin m → W`, at least half of all `b : W → Bool` are bad,
  -- by pairing each `b` with its negation off the seen points `Finset.univ.image xs`.
  have hpointwise : ∀ xs : Fin m → W,
      2 ^ W.card ≤ 2 * (Finset.univ.filter fun b : W → Bool => isBad xs b = true).card := by
    intro xs
    let seen : Finset W := Finset.univ.image xs
    let flip (b : W → Bool) : W → Bool := fun w => if w ∈ seen then b w else !b w
    have hflip_invol : Function.Involutive flip := by
      intro b; funext w; dsimp [flip]; split_ifs <;> simp
    have hpair : ∀ b : W → Bool, isBad xs b = true ∨ isBad xs (flip b) = true := by
      intro b
      by_contra hboth
      push Not at hboth
      have hb1 : 4 * (W.filter fun x =>
          A (fun i => ((xs i).1, b (xs i))) x ≠ cOf b x).card < W.card := by
        simpa [isBad] using hboth.1
      have hsame_sample : (fun i => ((xs i).1, flip b (xs i))) =
          (fun i => ((xs i).1, b (xs i))) := by
        funext i
        have hmem : xs i ∈ seen := Finset.mem_image_of_mem xs (Finset.mem_univ i)
        simp [flip, hmem]
      have hb2 : 4 * (W.filter fun x =>
          A (fun i => ((xs i).1, b (xs i))) x ≠ cOf (flip b) x).card < W.card := by
        have := hboth.2
        simp only [isBad, Bool.not_eq_true, decide_eq_false_iff_not, not_le,
          hsame_sample] at this
        exact this
      set h := A (fun i => ((xs i).1, b (xs i)))
      let U : Finset W := Finset.univ.filter fun w : W => w ∉ seen
      have hU_card : W.card - m ≤ U.card := by
        have hseen_le : seen.card ≤ m := Finset.card_image_le.trans (by simp)
        have hpart : U.card + seen.card = W.card := by
          have hUeq : U = Finset.univ \ seen := by ext w; simp [U]
          have hcard_coe : Fintype.card ↥W = W.card := Fintype.card_coe W
          rw [hUeq, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
            hcard_coe]
          exact Nat.sub_add_cancel (hcard_coe ▸ seen.card_le_univ)
        omega
      let E₁ : Finset W := U.filter fun w => h w.1 ≠ b w
      let E₂ : Finset W := U.filter fun w => h w.1 ≠ !b w
      have hE_cover : U.card ≤ E₁.card + E₂.card := by
        calc U.card = (E₁ ∪ E₂).card := by
              congr 1; ext w
              simp only [E₁, E₂, Finset.mem_union, Finset.mem_filter]
              refine ⟨fun hw => ?_, fun hw => hw.elim And.left And.left⟩
              cases h w.1 <;> cases b w <;> simp [hw]
          _ ≤ E₁.card + E₂.card := Finset.card_union_le E₁ E₂
      have hE₁_le : E₁.card ≤ (W.filter fun x => h x ≠ cOf b x).card := by
        have hmap : E₁.map ⟨Subtype.val, Subtype.val_injective⟩ ⊆
            W.filter fun x => h x ≠ cOf b x := by
          intro x hx
          simp only [Finset.mem_map, Function.Embedding.coeFn_mk, E₁, Finset.mem_filter] at hx
          obtain ⟨w, ⟨_, hwb⟩, rfl⟩ := hx
          exact Finset.mem_filter.mpr ⟨w.2, by rwa [hcOf_eq b w]⟩
        simpa using Finset.card_le_card hmap
      have hE₂_le : E₂.card ≤ (W.filter fun x => h x ≠ cOf (flip b) x).card := by
        have hmap : E₂.map ⟨Subtype.val, Subtype.val_injective⟩ ⊆
            W.filter fun x => h x ≠ cOf (flip b) x := by
          intro x hx
          simp only [Finset.mem_map, Function.Embedding.coeFn_mk, E₂, U, Finset.mem_filter] at hx
          obtain ⟨w, ⟨⟨_, hwn⟩, hwb⟩, rfl⟩ := hx
          exact Finset.mem_filter.mpr ⟨w.2, by rw [hcOf_eq (flip b) w]; simpa [flip, hwn] using hwb⟩
        simpa using Finset.card_le_card hmap
      omega
    let Bad : Finset (W → Bool) := Finset.univ.filter fun b => isBad xs b = true
    have hcov : (Finset.univ : Finset (W → Bool)) ⊆ Bad ∪ Bad.image flip := by
      intro b _
      rcases hpair b with hb | hfb
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ b, hb⟩)
      · refine Finset.mem_union_right _ (Finset.mem_image.mpr ⟨flip b, ?_, hflip_invol b⟩)
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hfb⟩
    have hcard_univ : (Finset.univ : Finset (W → Bool)).card = 2 ^ W.card := by
      simp
    calc 2 ^ W.card = (Finset.univ : Finset (W → Bool)).card := hcard_univ.symm
      _ ≤ (Bad ∪ Bad.image flip).card := Finset.card_le_card hcov
      _ ≤ Bad.card + (Bad.image flip).card := Finset.card_union_le _ _
      _ ≤ Bad.card + Bad.card := Nat.add_le_add_left Finset.card_image_le _
      _ = 2 * Bad.card := (two_mul _).symm
  -- Double-count over `(xs, b)` and choose `b` maximizing the bad-sample count.
  have hdouble : 2 ^ W.card * W.card ^ m ≤
      2 * ∑ b : W → Bool, (Finset.univ.filter fun xs : Fin m → W => isBad xs b = true).card := by
    have hswap : (∑ b : W → Bool,
        (Finset.univ.filter fun xs : Fin m → W => isBad xs b = true).card) =
        ∑ xs : Fin m → W, (Finset.univ.filter fun b : W → Bool => isBad xs b = true).card := by
      simp only [Finset.card_filter]
      exact Finset.sum_comm
    rw [hswap, Finset.mul_sum]
    calc 2 ^ W.card * W.card ^ m
        = ∑ _xs : Fin m → W, 2 ^ W.card := by simp [Fintype.card_coe, mul_comm]
      _ ≤ ∑ xs : Fin m → W,
            2 * (Finset.univ.filter fun b : W → Bool => isBad xs b = true).card :=
          Finset.sum_le_sum fun xs _ => hpointwise xs
  obtain ⟨bStar, -, hbStar⟩ : ∃ bStar ∈ (Finset.univ : Finset (W → Bool)),
      W.card ^ m ≤ 2 * (Finset.univ.filter fun xs : Fin m → W => isBad xs bStar = true).card := by
    by_contra hall
    push Not at hall
    have hlt : 2 * ∑ b : W → Bool,
        (Finset.univ.filter fun xs : Fin m → W => isBad xs b = true).card <
        2 ^ W.card * W.card ^ m := by
      rw [Finset.mul_sum]
      calc ∑ b : W → Bool,
            2 * (Finset.univ.filter fun xs : Fin m → W => isBad xs b = true).card
          < ∑ _b : W → Bool, W.card ^ m :=
            Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun b hb => hall b hb
        _ = 2 ^ W.card * W.card ^ m := by simp
    omega
  refine ⟨P, hP_prob, hP_compl, cOf bStar, hcOf_mem bStar, ?_⟩
  -- Relate the good `Fin m → W` tuples to the product measure `P^m`.
  let Good : Finset (Fin m → W) :=
    Finset.univ.filter fun xs : Fin m → W => isBad xs bStar = true
  let emb : (Fin m → W) → (Fin m → α) := fun xs i => (xs i).1
  have hemb_inj : Function.Injective emb :=
    fun xs₁ xs₂ h => funext fun i => Subtype.ext (congrFun h i)
  have hpi_single : ∀ xs : Fin m → W,
      Measure.pi (fun _ : Fin m => P) {emb xs} = ((W.card : ℝ≥0∞) ^ m)⁻¹ := by
    intro xs
    have hset : ({emb xs} : Set (Fin m → α)) = Set.univ.pi fun i => {(xs i).1} := by
      ext ys; simp [emb, funext_iff]
    rw [hset, Measure.pi_pi]
    have hfac : ∀ i : Fin m, P {(xs i).1} = (W.card : ℝ≥0∞)⁻¹ := fun i => by
      change μ.toMeasure {(xs i).1} = _
      rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
      simp [μ, Cslib.Probability.PMF.uniformOfFinset_apply, (xs i).2]
    simp [hfac, ENNReal.inv_pow]
  have hsub_ev : ((Good.image emb : Finset (Fin m → α)) : Set (Fin m → α)) ⊆
      {xs : Fin m → α |
        (1 / 4 : ℝ≥0∞) ≤
          P {x : α | A (fun i => (xs i, cOf bStar (xs i))) x ≠ cOf bStar x}} := by
    intro ys hys
    obtain ⟨xs, hxs, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hys)
    have hbad : W.card ≤ 4 * (W.filter fun x =>
        A (fun i => ((xs i).1, bStar (xs i))) x ≠ cOf bStar x).card := by
      simpa [Good, isBad] using hxs
    have hsample : (fun i => ((emb xs) i, cOf bStar ((emb xs) i))) =
        (fun i => ((xs i).1, bStar (xs i))) := by
      funext i; simp [emb, hcOf_eq bStar (xs i)]
    simp only [Set.mem_ofPred_eq, hsample, hP_err]
    have hW_ne0 : (W.card : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr hW_pos.ne'
    have hW_top : (W.card : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
    rw [ENNReal.le_div_iff_mul_le (Or.inl hW_ne0) (Or.inl hW_top), one_div,
      ENNReal.inv_mul_le_iff (by norm_num) (by norm_num)]
    exact_mod_cast hbad
  have hmeas_img :
      Measure.pi (fun _ : Fin m => P) (Good.image emb : Set (Fin m → α)) =
        (Good.card : ℝ≥0∞) * ((W.card : ℝ≥0∞) ^ m)⁻¹ := by
    have hunion : ((Good.image emb : Finset (Fin m → α)) : Set (Fin m → α)) =
        ⋃ xs ∈ Good, ({emb xs} : Set (Fin m → α)) := by
      ext ys; simp [eq_comm]
    rw [hunion, measure_biUnion_finset
      (fun a _ b _ hab => Set.disjoint_singleton.mpr (hemb_inj.ne hab))
      (fun _ _ => measurableSet_singleton _)]
    simp [hpi_single]
  have hhalf : (1 / 2 : ℝ≥0∞) ≤ (Good.card : ℝ≥0∞) * ((W.card : ℝ≥0∞) ^ m)⁻¹ := by
    have hpow0 : ((W.card : ℝ≥0∞) ^ m) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr hW_pos.ne')
    have hpowT : ((W.card : ℝ≥0∞) ^ m) ≠ ⊤ := ENNReal.pow_ne_top (ENNReal.natCast_ne_top _)
    rw [← div_eq_mul_inv, ENNReal.le_div_iff_mul_le (Or.inl hpow0) (Or.inl hpowT), one_div,
      ENNReal.inv_mul_le_iff (by norm_num) (by norm_num)]
    exact_mod_cast hbStar
  exact (hhalf.trans_eq hmeas_img.symm).trans (measure_mono hsub_ev)

end CslibFrontier.MachineLearning.OnlineLearning
