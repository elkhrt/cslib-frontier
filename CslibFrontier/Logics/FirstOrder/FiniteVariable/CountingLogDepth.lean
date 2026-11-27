module

public import CslibFrontier.Foundations.Combinatorics.SimpleGraph.WeisfeilerLeman
public import CslibFrontier.Foundations.ModelTheory.Graph
public import CslibFrontier.Logics.FirstOrder.FiniteVariable.Counting
public import CslibFrontier.Logics.FirstOrder.FiniteVariable.WeisfeilerLeman
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Nat.Log

import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Logarithmic Quantifier Depth, Tuple/Quotient Counting, and Weisfeiler–Leman

This module develops logarithmic quantifier-depth fragments $C_k^{O(\log n)}$ and
$C^{O(\log n)}$ directly on top of `CslibFrontier`'s finite-variable counting logic
`Cslib.Logic.FO.FiniteVariable.CountingFormula` and $k$-dimensional Weisfeiler–Leman
(`SimpleGraph.wlHistogram`), proved entirely under standard Lean axioms.

## Main definitions

* `Cslib.Logic.FO.FiniteVariable.relabel`, `Cslib.Logic.FO.FiniteVariable.castLE`,
  `Cslib.Logic.FO.FiniteVariable.atMost`, `Cslib.Logic.FO.FiniteVariable.iff`,
  `Cslib.Logic.FO.FiniteVariable.IsSentence`, `Cslib.Logic.FO.FiniteVariable.SentenceRealize`
* `Cslib.Logic.FO.FiniteVariable.updateTuple`, `Cslib.Logic.FO.FiniteVariable.exTuple`,
  `Cslib.Logic.FO.FiniteVariable.allTuple`, `Cslib.Logic.FO.FiniteVariable.countTupleEq`,
  `Cslib.Logic.FO.FiniteVariable.countQuotGe`, `Cslib.Logic.FO.FiniteVariable.countQuotEq`
* `Cslib.Logic.FO.FiniteVariable.IsLogarithmicDepth`,
  `Cslib.Logic.FO.FiniteVariable.ExpressesClassInCLogAt`,
  `Cslib.Logic.FO.FiniteVariable.ExpressesClassInCLog`,
  `Cslib.Logic.FO.FiniteVariable.CountingEquiv`,
  `Cslib.Logic.FO.FiniteVariable.IdentifiesInCLogAt`,
  `Cslib.Logic.FO.FiniteVariable.IdentifiesInCLog`
* `Cslib.Logic.FO.FiniteVariable.WLDistinguishes`,
  `Cslib.Logic.FO.FiniteVariable.WLIdentifiesInLogAt`,
  `Cslib.Logic.FO.FiniteVariable.WLIdentifiesInLog`

## Main results

* `Cslib.Logic.FO.FiniteVariable.realize_relabel`, `Cslib.Logic.FO.FiniteVariable.realize_castLE`,
  `Cslib.Logic.FO.FiniteVariable.Equiv.realize_countingFormula_iff`
* `Cslib.Logic.FO.FiniteVariable.realize_countTupleEq`,
  `Cslib.Logic.FO.FiniteVariable.quantifierRank_countTupleEq_le`,
  `Cslib.Logic.FO.FiniteVariable.realize_countQuotGe`,
  `Cslib.Logic.FO.FiniteVariable.quantifierRank_countQuotGe_le`
* `Cslib.Logic.FO.FiniteVariable.isLogarithmicDepth_of_le_mul_log_add`,
  `Cslib.Logic.FO.FiniteVariable.isLogarithmicDepth_of_le_mul_natLog_add`,
  `Cslib.Logic.FO.FiniteVariable.IdentifiesInCLogAt.of_sameCard`,
  `Cslib.Logic.FO.FiniteVariable.IdentifiesInCLog.distinguishes`
* `Cslib.Logic.FO.FiniteVariable.wlDistinguishes_of_countingFormula`,
  `Cslib.Logic.FO.FiniteVariable.exists_countingFormula_of_wlDistinguishes`,
  `Cslib.Logic.FO.FiniteVariable.wlIdentifiesInLogAt_of_identifiesInCLogAt`
-/

public section

namespace Cslib.Logic.FO.FiniteVariable

open FirstOrder Language Cslib.Logic.FO Cslib.Logic.FO.FiniteVariable SimpleGraph

universe u v w w'

/-! ### Variable reindexing, derived combinators, sentences, and isomorphism invariance -/

section FormulaAPI

variable {L : Language.{u, v}} {k k₁ k₂ : ℕ}

/-- Reindexes the variables of a `CountingFormula` along an injective map `f : Fin k₁ ↪ Fin k₂`. -/
def relabel (f : Fin k₁ ↪ Fin k₂) : CountingFormula L k₁ → CountingFormula L k₂
  | .falsum => .falsum
  | .equal i j => .equal (f i) (f j)
  | .rel R g => .rel R (f ∘ g)
  | .imp φ ψ => .imp (relabel f φ) (relabel f ψ)
  | .quant q i φ => .quant q (f i) (relabel f φ)

/-- Embeds a `C_{k₁}`-formula into `C_{k₂}` along `k₁ ≤ k₂`. -/
def castLE (h : k₁ ≤ k₂) (φ : CountingFormula L k₁) : CountingFormula L k₂ :=
  relabel (Fin.castLEEmb h) φ

/-- At-most counting quantifier `∃^{≤ m} xᵢ φ := ¬ ∃^{≥ m + 1} xᵢ φ`, valid for all `m : ℕ`
including `m = 0`. -/
def atMost (m : ℕ) (i : Fin k) (φ : CountingFormula L k) : CountingFormula L k :=
  (CountingFormula.atLeast (m + 1) i φ).not

/-- Biconditional `φ ↔ ψ := (φ → ψ) ∧ (ψ → φ)`. -/
def iff (φ ψ : CountingFormula L k) : CountingFormula L k :=
  φ.imp ψ ⊓ ψ.imp φ

/-- A `CountingFormula` is a sentence when it has no free variables. -/
@[expose] def IsSentence (φ : CountingFormula L k) : Prop :=
  φ.freeVars = ∅

theorem isSentence_of_freeVars_eq_empty {φ : CountingFormula L k} (h : φ.freeVars = ∅) :
    IsSentence φ := h

theorem IsSentence.freeVars_eq_empty {φ : CountingFormula L k} (h : IsSentence φ) :
    φ.freeVars = ∅ := h

theorem IsSentence.imp_left {φ ψ : CountingFormula L k} (h : IsSentence (φ.imp ψ)) :
    IsSentence φ := by
  unfold IsSentence at h ⊢
  rw [GenFormula.freeVars_imp, Finset.union_eq_empty] at h
  exact h.1

theorem IsSentence.imp_right {φ ψ : CountingFormula L k} (h : IsSentence (φ.imp ψ)) :
    IsSentence ψ := by
  unfold IsSentence at h ⊢
  rw [GenFormula.freeVars_imp, Finset.union_eq_empty] at h
  exact h.2

/-- Satisfaction of a `CountingFormula` across all variable assignments on `M`. -/
@[expose] def SentenceRealize (M : Type w) [L.Structure M] (φ : CountingFormula L k) : Prop :=
  ∀ a : Fin k → M, φ.Realize a

@[simp] theorem relabel_falsum (f : Fin k₁ ↪ Fin k₂) :
    relabel f (.falsum : CountingFormula L k₁) = .falsum := by rw [relabel]

@[simp] theorem relabel_equal (f : Fin k₁ ↪ Fin k₂) (i j : Fin k₁) :
    relabel f (.equal i j : CountingFormula L k₁) = .equal (f i) (f j) := by rw [relabel]

@[simp] theorem relabel_rel {l : ℕ} (f : Fin k₁ ↪ Fin k₂) (R : L.Relations l)
    (g : Fin l → Fin k₁) :
    relabel f (.rel R g : CountingFormula L k₁) = .rel R (f ∘ g) := by rw [relabel]

@[simp] theorem relabel_imp (f : Fin k₁ ↪ Fin k₂) (φ ψ : CountingFormula L k₁) :
    relabel f (.imp φ ψ) = .imp (relabel f φ) (relabel f ψ) := by rw [relabel]

@[simp] theorem relabel_quant (f : Fin k₁ ↪ Fin k₂) (q : CountingQuant) (i : Fin k₁)
    (φ : CountingFormula L k₁) :
    relabel f (.quant q i φ) = .quant q (f i) (relabel f φ) := by rw [relabel]

/-- Realization of a reindexed formula equals realization on the pulled-back assignment. -/
@[simp] theorem realize_relabel {M : Type w} [L.Structure M] (f : Fin k₁ ↪ Fin k₂)
    (φ : CountingFormula L k₁) (a : Fin k₂ → M) :
    (relabel f φ).Realize a ↔ φ.Realize (a ∘ f) := by
  induction φ generalizing a with
  | falsum => simp [relabel]
  | equal i j => simp [relabel]
  | rel R g =>
    simp only [relabel_rel, GenFormula.realize_rel]
    rfl
  | imp φ ψ ihφ ihψ =>
    simp only [relabel_imp, GenFormula.realize_imp, ihφ, ihψ]
  | quant q i φ ih =>
    simp only [relabel_quant, GenFormula.realize_quant]
    refine Quantifier.eval_congr q fun c ↦ ?_
    rw [ih]
    have hcomp : Function.update a (f i) c ∘ f = Function.update (a ∘ f) i c := by
      funext j
      by_cases hj : j = i
      · subst hj; simp
      · simp [hj, f.injective.ne hj]
    rw [hcomp]

/-- Reindexing preserves quantifier rank. -/
@[simp] theorem quantifierRank_relabel (f : Fin k₁ ↪ Fin k₂) (φ : CountingFormula L k₁) :
    (relabel f φ).quantifierRank = φ.quantifierRank := by
  induction φ with
  | falsum | equal _ _ | rel _ _ => simp [relabel]
  | imp _ _ ih₁ ih₂ => simp [relabel, ih₁, ih₂]
  | quant _ _ _ ih => simp [relabel, ih]

/-- Reindexing maps free variables by `Finset.image f`. -/
@[simp] theorem freeVars_relabel (f : Fin k₁ ↪ Fin k₂) (φ : CountingFormula L k₁) :
    (relabel f φ).freeVars = φ.freeVars.image f := by
  classical
  induction φ with
  | falsum => simp [relabel]
  | equal i j => simp [relabel, Finset.image_insert]
  | rel R g => simp [relabel, Finset.image_image, Function.comp_def]
  | imp _ _ ih₁ ih₂ => simp [relabel, ih₁, ih₂, Finset.image_union]
  | quant _ _ _ ih => simp [relabel, ih, Finset.image_erase f.injective]

@[simp] theorem realize_castLE {M : Type w} [L.Structure M] (h : k₁ ≤ k₂)
    (φ : CountingFormula L k₁) (a : Fin k₂ → M) :
    (castLE h φ).Realize a ↔ φ.Realize (a ∘ Fin.castLE h) :=
  realize_relabel (Fin.castLEEmb h) φ a

@[simp] theorem quantifierRank_castLE (h : k₁ ≤ k₂) (φ : CountingFormula L k₁) :
    (castLE h φ).quantifierRank = φ.quantifierRank :=
  quantifierRank_relabel (Fin.castLEEmb h) φ

@[simp] theorem freeVars_castLE (h : k₁ ≤ k₂) (φ : CountingFormula L k₁) :
    (castLE h φ).freeVars = φ.freeVars.image (Fin.castLE h) :=
  freeVars_relabel (Fin.castLEEmb h) φ

@[simp] theorem realize_atMost {M : Type w} [L.Structure M] (m : ℕ) (i : Fin k)
    (φ : CountingFormula L k) (a : Fin k → M) :
    (atMost m i φ).Realize a ↔
      {c : M | φ.Realize (Function.update a i c)}.encard ≤ m := by
  rw [atMost, GenFormula.realize_not, CountingFormula.realize_atLeast, Nat.cast_add_one,
    ENat.add_one_le_iff (ENat.natCast_ne_top m), not_lt]

/-- On a finite carrier, `atMost m i φ` holds iff at most `m` witnesses satisfy `φ`. -/
theorem realize_atMost_iff_ncard {M : Type w} [L.Structure M] [Finite M] (m : ℕ) (i : Fin k)
    (φ : CountingFormula L k) (a : Fin k → M) :
    (atMost m i φ).Realize a ↔ {c : M | φ.Realize (Function.update a i c)}.ncard ≤ m := by
  rw [realize_atMost, ← (Set.toFinite _).cast_ncard_eq, Nat.cast_le]

@[simp] theorem quantifierRank_atMost (m : ℕ) (i : Fin k) (φ : CountingFormula L k) :
    (atMost m i φ).quantifierRank = φ.quantifierRank + 1 := by
  simp [atMost]

@[simp] theorem freeVars_atMost (m : ℕ) (i : Fin k) (φ : CountingFormula L k) :
    (atMost m i φ).freeVars = φ.freeVars.erase i := by
  simp [atMost]

@[simp] theorem realize_iff {M : Type w} [L.Structure M] (φ ψ : CountingFormula L k)
    (a : Fin k → M) :
    (iff φ ψ).Realize a ↔ (φ.Realize a ↔ ψ.Realize a) := by
  simp only [iff, GenFormula.realize_inf, GenFormula.realize_imp, iff_iff_implies_and_implies]

@[simp] theorem quantifierRank_iff (φ ψ : CountingFormula L k) :
    (iff φ ψ).quantifierRank = max φ.quantifierRank ψ.quantifierRank := by
  simp [iff, max_comm ψ.quantifierRank φ.quantifierRank]

@[simp] theorem freeVars_iff (φ ψ : CountingFormula L k) :
    (iff φ ψ).freeVars = φ.freeVars ∪ ψ.freeVars := by
  simp [iff, Finset.union_comm ψ.freeVars]

theorem isSentence_castLE (h : k₁ ≤ k₂) (φ : CountingFormula L k₁) :
    IsSentence (castLE h φ) ↔ IsSentence φ := by
  simp [IsSentence]

theorem IsSentence.not {φ : CountingFormula L k} (hφ : IsSentence φ) : IsSentence φ.not := by
  simpa [IsSentence] using hφ

theorem IsSentence.inf {φ ψ : CountingFormula L k} (hφ : IsSentence φ) (hψ : IsSentence ψ) :
    IsSentence (φ ⊓ ψ) := by
  simp only [IsSentence, GenFormula.freeVars_inf, Finset.union_eq_empty] at hφ hψ ⊢
  exact ⟨hφ, hψ⟩

theorem IsSentence.sup {φ ψ : CountingFormula L k} (hφ : IsSentence φ) (hψ : IsSentence ψ) :
    IsSentence (φ ⊔ ψ) := by
  simp only [IsSentence, GenFormula.freeVars_sup, Finset.union_eq_empty] at hφ hψ ⊢
  exact ⟨hφ, hψ⟩

theorem IsSentence.imp {φ ψ : CountingFormula L k} (hφ : IsSentence φ) (hψ : IsSentence ψ) :
    IsSentence (φ.imp ψ) := by
  simp only [IsSentence, GenFormula.freeVars_imp, Finset.union_eq_empty] at hφ hψ ⊢
  exact ⟨hφ, hψ⟩

theorem IsSentence.iff {φ ψ : CountingFormula L k} (hφ : IsSentence φ) (hψ : IsSentence ψ) :
    IsSentence (Cslib.Logic.FO.FiniteVariable.iff φ ψ) := by
  simp only [IsSentence, freeVars_iff, Finset.union_eq_empty] at hφ hψ ⊢
  exact ⟨hφ, hψ⟩

theorem IsSentence.iInf {β : Type*} [Finite β] {f : β → CountingFormula L k}
    (h : ∀ b, IsSentence (f b)) : IsSentence (GenFormula.iInf f) := by
  rw [IsSentence, ← Finset.coe_eq_empty, ← Set.subset_empty_iff]
  exact GenFormula.freeVars_iInf_subset fun b ↦ by
    rw [Finset.coe_eq_empty.mpr (h b)]

theorem IsSentence.iSup {β : Type*} [Finite β] {f : β → CountingFormula L k}
    (h : ∀ b, IsSentence (f b)) : IsSentence (GenFormula.iSup f) := by
  rw [IsSentence, ← Finset.coe_eq_empty, ← Set.subset_empty_iff]
  exact GenFormula.freeVars_iSup_subset fun b ↦ by
    rw [Finset.coe_eq_empty.mpr (h b)]

/-- A sentence evaluates identically on all assignments. -/
theorem realize_eq_of_isSentence {M : Type w} [L.Structure M] {φ : CountingFormula L k}
    (hφ : IsSentence φ) (a b : Fin k → M) :
    φ.Realize a ↔ φ.Realize b :=
  GenFormula.realize_congr fun i hi ↦ by
    rw [hφ] at hi
    exact False.elim (Finset.notMem_empty i hi)

theorem IsSentence.sentenceRealize_iff_realize {M : Type w} [L.Structure M]
    {φ : CountingFormula L k} (hφ : IsSentence φ) (a : Fin k → M) :
    SentenceRealize M φ ↔ φ.Realize a :=
  ⟨fun h ↦ h a, fun h b ↦ (realize_eq_of_isSentence hφ b a).mpr h⟩

theorem IsSentence.sentenceRealize_not {M : Type w} [L.Structure M] [Nonempty M]
    {φ : CountingFormula L k} (hφ : IsSentence φ) :
    SentenceRealize M φ.not ↔ ¬ SentenceRealize M φ := by
  let a : Fin k → M := fun _ ↦ Classical.arbitrary M
  rw [hφ.not.sentenceRealize_iff_realize a, hφ.sentenceRealize_iff_realize a,
    GenFormula.realize_not]

theorem IsSentence.sentenceRealize_inf {M : Type w} [L.Structure M]
    {φ ψ : CountingFormula L k} (_hφ : IsSentence φ) (_hψ : IsSentence ψ) :
    SentenceRealize M (φ ⊓ ψ) ↔ SentenceRealize M φ ∧ SentenceRealize M ψ := by
  simp only [SentenceRealize, GenFormula.realize_inf, forall_and]

theorem IsSentence.sentenceRealize_sup {M : Type w} [L.Structure M] [Nonempty M]
    {φ ψ : CountingFormula L k} (hφ : IsSentence φ) (hψ : IsSentence ψ) :
    SentenceRealize M (φ ⊔ ψ) ↔ SentenceRealize M φ ∨ SentenceRealize M ψ := by
  let a : Fin k → M := fun _ ↦ Classical.arbitrary M
  rw [(hφ.sup hψ).sentenceRealize_iff_realize a, hφ.sentenceRealize_iff_realize a,
    hψ.sentenceRealize_iff_realize a, GenFormula.realize_sup]

theorem sentenceRealize_castLE {M : Type w} [L.Structure M] [Nonempty M] (h : k₁ ≤ k₂)
    (φ : CountingFormula L k₁) :
    SentenceRealize M (castLE h φ) ↔ SentenceRealize M φ := by
  classical
  constructor
  · intro hφ b
    let a : Fin k₂ → M := fun j ↦
      if hj : j.val < k₁ then b ⟨j.val, hj⟩ else Classical.arbitrary M
    have hcomp : a ∘ Fin.castLE h = b := by
      funext j
      simp [a, j.isLt]
    rw [← hcomp]
    exact (realize_castLE h φ a).mp (hφ a)
  · intro hφ a
    exact (realize_castLE h φ a).mpr (hφ (a ∘ Fin.castLE h))

/-- Every `L`-isomorphism preserves and reflects realization of `CountingFormula`. -/
theorem Equiv.realize_countingFormula_iff {M : Type w} {N : Type w'}
    [L.Structure M] [L.Structure N] (e : M ≃[L] N) (φ : CountingFormula L k) (a : Fin k → M) :
    φ.Realize (e ∘ a) ↔ φ.Realize a := by
  induction φ generalizing a with
  | falsum => simp
  | equal i j =>
    simp only [GenFormula.realize_equal, Function.comp_apply]
    exact e.injective.eq_iff
  | rel R g =>
    simp only [GenFormula.realize_rel]
    exact e.map_rel R (a ∘ g)
  | imp φ ψ ihφ ihψ =>
    simp only [GenFormula.realize_imp, ihφ, ihψ]
  | quant q i φ ih =>
    simp only [GenFormula.realize_quant]
    refine (CountingQuant.eval_iff_of_equiv q e.toEquiv fun c ↦ ?_).symm
    have hupd : Function.update (e ∘ a) i (e.toEquiv c) = e ∘ Function.update a i c := by
      funext j
      by_cases hj : j = i
      · subst hj; simp; rfl
      · simp [hj]
    rw [hupd, ih]

/-- Every `L`-isomorphism preserves and reflects sentence satisfaction. -/
theorem Equiv.sentenceRealize_countingFormula_iff {M : Type w} {N : Type w'}
    [L.Structure M] [L.Structure N] (e : M ≃[L] N) (φ : CountingFormula L k) :
    SentenceRealize N φ ↔ SentenceRealize M φ := by
  constructor
  · intro hN a
    exact (Equiv.realize_countingFormula_iff e φ a).mp (hN (e ∘ a))
  · intro hM b
    have hcomp : e ∘ (e.symm ∘ b) = b := by
      funext j
      exact e.apply_symm_apply (b j)
    rw [← hcomp]
    exact (Equiv.realize_countingFormula_iff e φ (e.symm ∘ b)).mpr (hM (e.symm ∘ b))

end FormulaAPI

/-! ### Tuple quantification, tuple counting, and quotient-class counting -/

section TupleAndQuotientCounting

variable {L : Language.{u, v}} {k : ℕ}

/-- Updates assignment `a : Fin k → M` simultaneously at indices `vars : Fin d → Fin k` with
values `t : Fin d → M`. -/
noncomputable def updateTuple {M : Type w} {d : ℕ} (a : Fin k → M) (vars : Fin d → Fin k)
    (t : Fin d → M) : Fin k → M := by
  classical
  exact fun j ↦ if h : ∃ i : Fin d, vars i = j then t (Classical.choose h) else a j

theorem updateTuple_apply {M : Type w} {d : ℕ} (a : Fin k → M) {vars : Fin d → Fin k}
    (hvars : Function.Injective vars) (t : Fin d → M) (i : Fin d) :
    updateTuple a vars t (vars i) = t i := by
  classical
  have hex : ∃ i' : Fin d, vars i' = vars i := ⟨i, rfl⟩
  simp only [updateTuple, hex, ↓reduceDIte]
  exact congrArg t (hvars (Classical.choose_spec hex))

theorem updateTuple_of_notMem_range {M : Type w} {d : ℕ} (a : Fin k → M)
    (vars : Fin d → Fin k) (t : Fin d → M) {j : Fin k} (hj : j ∉ Set.range vars) :
    updateTuple a vars t j = a j := by
  classical
  have hnot : ¬ ∃ i : Fin d, vars i = j := fun ⟨i, hi⟩ ↦ hj ⟨i, hi⟩
  simp [updateTuple, hnot]

theorem updateTuple_zero {M : Type w} (a : Fin k → M) (vars : Fin 0 → Fin k) (t : Fin 0 → M) :
    updateTuple a vars t = a := by
  funext j
  exact updateTuple_of_notMem_range a vars t (by simp)

theorem updateTuple_succ {M : Type w} {d : ℕ} (a : Fin k → M) {vars : Fin (d + 1) → Fin k}
    (hvars : Function.Injective vars) (c : M) (t : Fin d → M) :
    updateTuple (Function.update a (vars 0) c) (vars ∘ Fin.succ) t =
      updateTuple a vars (Fin.cons c t) := by
  funext j
  by_cases hj : j ∈ Set.range vars
  · obtain ⟨i, rfl⟩ := hj
    rw [updateTuple_apply a hvars]
    refine Fin.cases ?_ (fun i' ↦ ?_) i
    · have hnot : vars 0 ∉ Set.range (vars ∘ Fin.succ) := by
        rintro ⟨i', hi'⟩
        exact Fin.succ_ne_zero i' (hvars hi')
      rw [updateTuple_of_notMem_range _ _ _ hnot, Function.update_self, Fin.cons_zero]
    · have hinj : Function.Injective (vars ∘ Fin.succ) := hvars.comp (Fin.succ_injective d)
      change updateTuple (Function.update a (vars 0) c) (vars ∘ Fin.succ) t
        ((vars ∘ Fin.succ) i') = Fin.cons (α := fun _ ↦ M) c t i'.succ
      rw [updateTuple_apply _ hinj, Fin.cons_succ]
  · have hnot' : j ∉ Set.range (vars ∘ Fin.succ) := fun ⟨i', hi'⟩ ↦ hj ⟨i'.succ, hi'⟩
    have hne : j ≠ vars 0 := fun heq ↦ hj ⟨0, heq.symm⟩
    rw [updateTuple_of_notMem_range _ _ _ hnot', updateTuple_of_notMem_range _ _ _ hj,
      Function.update_of_ne hne]

/-- Existential quantification over a tuple of variables `vars : Fin d → Fin k`. -/
def exTuple : ∀ {d : ℕ}, (Fin d → Fin k) → CountingFormula L k → CountingFormula L k
  | 0, _, φ => φ
  | _ + 1, vars, φ => GenFormula.ex (vars 0) (exTuple (vars ∘ Fin.succ) φ)

/-- Universal quantification over a tuple of variables `vars : Fin d → Fin k`. -/
def allTuple : ∀ {d : ℕ}, (Fin d → Fin k) → CountingFormula L k → CountingFormula L k
  | 0, _, φ => φ
  | _ + 1, vars, φ => GenFormula.all (vars 0) (allTuple (vars ∘ Fin.succ) φ)

theorem realize_exTuple {M : Type w} [L.Structure M] {d : ℕ} {vars : Fin d → Fin k}
    (hvars : Function.Injective vars) (φ : CountingFormula L k) (a : Fin k → M) :
    (exTuple vars φ).Realize a ↔ ∃ t : Fin d → M, φ.Realize (updateTuple a vars t) := by
  induction d generalizing a with
  | zero =>
    simp only [exTuple]
    exact ⟨fun h ↦ ⟨Fin.elim0, by rwa [updateTuple_zero]⟩,
      fun ⟨t, ht⟩ ↦ by rwa [updateTuple_zero] at ht⟩
  | succ d ih =>
    simp only [exTuple, GenFormula.realize_ex]
    have hinj : Function.Injective (vars ∘ Fin.succ) := hvars.comp (Fin.succ_injective d)
    constructor
    · rintro ⟨c, hc⟩
      obtain ⟨t, ht⟩ := (ih hinj _).mp hc
      exact ⟨Fin.cons c t, by rwa [← updateTuple_succ a hvars c t]⟩
    · rintro ⟨t, ht⟩
      refine ⟨t 0, (ih hinj _).mpr ⟨Fin.tail t, ?_⟩⟩
      rw [updateTuple_succ a hvars]
      simpa only [Fin.cons_self_tail] using ht

theorem realize_allTuple {M : Type w} [L.Structure M] {d : ℕ} {vars : Fin d → Fin k}
    (hvars : Function.Injective vars) (φ : CountingFormula L k) (a : Fin k → M) :
    (allTuple vars φ).Realize a ↔ ∀ t : Fin d → M, φ.Realize (updateTuple a vars t) := by
  induction d generalizing a with
  | zero =>
    simp only [allTuple]
    exact ⟨fun h t ↦ by rwa [updateTuple_zero],
      fun h ↦ by simpa [updateTuple_zero] using h Fin.elim0⟩
  | succ d ih =>
    simp only [allTuple, GenFormula.realize_all]
    have hinj : Function.Injective (vars ∘ Fin.succ) := hvars.comp (Fin.succ_injective d)
    constructor
    · intro h t
      have ht := (ih hinj _).mp (h (t 0)) (Fin.tail t)
      rw [updateTuple_succ a hvars] at ht
      simpa only [Fin.cons_self_tail] using ht
    · intro h c
      refine (ih hinj _).mpr fun t ↦ ?_
      rw [updateTuple_succ a hvars]
      exact h (Fin.cons c t)

theorem quantifierRank_exTuple {d : ℕ} (vars : Fin d → Fin k) (φ : CountingFormula L k) :
    (exTuple vars φ).quantifierRank = φ.quantifierRank + d := by
  induction d with
  | zero => simp [exTuple]
  | succ d ih =>
    simp only [exTuple, GenFormula.quantifierRank_ex, ih (vars ∘ Fin.succ)]
    omega

theorem quantifierRank_allTuple {d : ℕ} (vars : Fin d → Fin k) (φ : CountingFormula L k) :
    (allTuple vars φ).quantifierRank = φ.quantifierRank + d := by
  induction d with
  | zero => simp [allTuple]
  | succ d ih =>
    simp only [allTuple, GenFormula.quantifierRank_all, ih (vars ∘ Fin.succ)]
    omega

theorem freeVars_exTuple_subset {d : ℕ} (vars : Fin d → Fin k) (φ : CountingFormula L k) :
    ((exTuple vars φ).freeVars : Set (Fin k)) ⊆ (φ.freeVars : Set (Fin k)) \ Set.range vars := by
  induction d with
  | zero =>
    simp only [exTuple, Set.range_eq_empty, Set.sdiff_empty, Set.Subset.rfl]
  | succ d ih =>
    intro x hx
    simp only [exTuple, GenFormula.freeVars_ex, Finset.coe_erase, Set.mem_sdiff,
      Set.mem_singleton_iff] at hx
    have hsub := ih (vars ∘ Fin.succ) hx.1
    refine ⟨hsub.1, ?_⟩
    rintro ⟨i, hi⟩
    cases i using Fin.cases with
    | zero => exact hx.2 hi.symm
    | succ i' => exact hsub.2 ⟨i', hi⟩

theorem freeVars_allTuple_subset {d : ℕ} (vars : Fin d → Fin k) (φ : CountingFormula L k) :
    ((allTuple vars φ).freeVars : Set (Fin k)) ⊆ (φ.freeVars : Set (Fin k)) \ Set.range vars := by
  induction d with
  | zero =>
    simp only [allTuple, Set.range_eq_empty, Set.sdiff_empty, Set.Subset.rfl]
  | succ d ih =>
    intro x hx
    simp only [allTuple, GenFormula.freeVars_all, Finset.coe_erase, Set.mem_sdiff,
      Set.mem_singleton_iff] at hx
    have hsub := ih (vars ∘ Fin.succ) hx.1
    refine ⟨hsub.1, ?_⟩
    rintro ⟨i, hi⟩
    cases i using Fin.cases with
    | zero => exact hx.2 hi.symm
    | succ i' => exact hsub.2 ⟨i', hi⟩

/-- Counts `d`-tuples `t : Fin d → M` satisfying `φ` at `vars` (on structures of size at most `n`),
adding exactly `d` to quantifier rank regardless of `n`. -/
noncomputable def countTupleEq :
    ∀ (d : ℕ), ℕ → (Fin d → Fin k) → CountingFormula L k → ℕ → CountingFormula L k
  | 0, _, _, φ, s =>
      if s = 0 then φ.not else if s = 1 then φ else ⊥
  | d + 1, n, vars, φ, s =>
      let B := n ^ d
      GenFormula.iSup fun h : {h : Fin (B + 1) → Fin (n + 1) //
          ∑ t : Fin (B + 1), t.val * (h t).val = s} ↦
        GenFormula.iInf fun t : Fin (B + 1) ↦
          if t.val = 0 then ⊤
          else
            CountingFormula.exactly (h.1 t).val (vars 0)
              (countTupleEq d n (vars ∘ Fin.succ) φ t.val)

/-- Quantifier rank of `countTupleEq d n vars φ s` is at most `φ.quantifierRank + d`. -/
theorem quantifierRank_countTupleEq_le :
    ∀ (d n : ℕ) (vars : Fin d → Fin k) (φ : CountingFormula L k) (s : ℕ),
      (countTupleEq d n vars φ s).quantifierRank ≤ φ.quantifierRank + d
  | 0, _, _, φ, s => by
    unfold countTupleEq
    split_ifs <;> simp
  | d + 1, n, vars, φ, s => by
    unfold countTupleEq
    refine GenFormula.quantifierRank_iSup_le fun _ ↦ GenFormula.quantifierRank_iInf_le fun t ↦ ?_
    split_ifs
    · simp
    · rw [CountingFormula.quantifierRank_exactly]
      have ih := quantifierRank_countTupleEq_le d n (vars ∘ Fin.succ) φ t.val
      omega

/-- Free variables of `countTupleEq d n vars φ s` lie in `φ.freeVars \ range vars`. -/
theorem freeVars_countTupleEq_subset :
    ∀ (d n : ℕ) (vars : Fin d → Fin k) (φ : CountingFormula L k) (s : ℕ),
      ((countTupleEq d n vars φ s).freeVars : Set (Fin k)) ⊆
        (φ.freeVars : Set (Fin k)) \ Set.range vars
  | 0, _, _, φ, s => by
    unfold countTupleEq
    split_ifs <;> simp
  | d + 1, n, vars, φ, s => by
    unfold countTupleEq
    refine GenFormula.freeVars_iSup_subset fun _ ↦ GenFormula.freeVars_iInf_subset fun t ↦ ?_
    split_ifs
    · simp
    · intro x hx
      rw [CountingFormula.freeVars_exactly, Finset.coe_erase] at hx
      have hsub := freeVars_countTupleEq_subset d n (vars ∘ Fin.succ) φ t.val hx.1
      refine ⟨hsub.1, ?_⟩
      rintro ⟨i, hi⟩
      cases i using Fin.cases with
      | zero => exact hx.2 hi.symm
      | succ i' => exact hsub.2 ⟨i', hi⟩

/-- On any finite structure of cardinality at most `n`, `countTupleEq d n vars φ s` holds iff
exactly `s` tuples `t : Fin d → M` satisfy `φ` at `vars`. -/
theorem realize_countTupleEq {M : Type w} [L.Structure M] [Fintype M] :
    ∀ (d n : ℕ) (_hn : Fintype.card M ≤ n) (vars : Fin d → Fin k)
      (_hvars : Function.Injective vars) (φ : CountingFormula L k) (s : ℕ) (a : Fin k → M),
      (countTupleEq d n vars φ s).Realize a ↔
        {t : Fin d → M | φ.Realize (updateTuple a vars t)}.ncard = s
  | 0, _, _, vars, _, φ, s, a => by
    classical
    unfold countTupleEq
    have hcard_iff : {t : Fin 0 → M | φ.Realize (updateTuple a vars t)}.ncard =
        if φ.Realize a then 1 else 0 := by
      by_cases hφ : φ.Realize a
      · have heq : {t : Fin 0 → M | φ.Realize (updateTuple a vars t)} = Set.univ := by
          ext t; simp [updateTuple_zero, hφ]
        rw [heq, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_unique]
        simp [hφ]
      · have heq : {t : Fin 0 → M | φ.Realize (updateTuple a vars t)} = ∅ := by
          ext t; simp [updateTuple_zero, hφ]
        rw [heq, Set.ncard_empty]
        simp [hφ]
    rw [hcard_iff]
    by_cases hs0 : s = 0
    · subst hs0; by_cases hφ : φ.Realize a <;> simp [hφ]
    · by_cases hs1 : s = 1
      · subst hs1; by_cases hφ : φ.Realize a <;> simp [hφ]
      · by_cases hφ : φ.Realize a <;> simp [hφ, hs0, hs1, Ne.symm hs0, Ne.symm hs1]
  | d + 1, n, hn, vars, hvars, φ, s, a => by
    classical
    let B := n ^ d
    have hinj : Function.Injective (vars ∘ Fin.succ) := hvars.comp (Fin.succ_injective d)
    have hcard_le : Fintype.card (Fin d → M) ≤ B := by
      simpa only [Fintype.card_fun, Fintype.card_fin] using Nat.pow_le_pow_left hn d
    let fiberCount (c : M) : ℕ :=
      {t' : Fin d → M | φ.Realize (updateTuple (Function.update a (vars 0) c)
        (vars ∘ Fin.succ) t')}.ncard
    have hfiber_le (c : M) : fiberCount c ≤ B := by
      refine le_trans ?_ hcard_le
      rw [← Nat.card_eq_fintype_card]
      exact Set.ncard_le_ncard (Set.subset_univ _) (Set.toFinite _) |>.trans_eq (Set.ncard_univ _)
    have htotal : {t : Fin (d + 1) → M | φ.Realize (updateTuple a vars t)}.ncard =
        ∑ t : Fin (B + 1), t.val * {c : M | fiberCount c = t.val}.ncard := by
      have hdecomp : {t : Fin (d + 1) → M | φ.Realize (updateTuple a vars t)}.ncard =
          ∑ c : M, fiberCount c := by
        have hbi : {t : Fin (d + 1) → M | φ.Realize (updateTuple a vars t)}.ncard =
            (Finset.univ.filter fun t : Fin (d + 1) → M ↦
              φ.Realize (updateTuple a vars t)).card := by
          rw [← Set.ncard_coe_finset]
          congr 1; ext t; simp
        rw [hbi]
        have hsum_eq : (Finset.univ.filter fun t : Fin (d + 1) → M ↦
            φ.Realize (updateTuple a vars t)).card =
            ∑ c : M, (Finset.univ.filter fun t' : Fin d → M ↦
              φ.Realize (updateTuple a vars (Fin.cons c t'))).card := by
          let e : (Fin (d + 1) → M) ≃ M × (Fin d → M) := Fin.consEquiv (fun _ ↦ M) |>.symm
          have hcard1 := Finset.card_bij
            (s := Finset.univ.filter fun t : Fin (d + 1) → M ↦ φ.Realize (updateTuple a vars t))
            (t := Finset.univ.sigma fun c : M ↦
              Finset.univ.filter fun t' : Fin d → M ↦
                φ.Realize (updateTuple a vars (Fin.cons c t')))
            (fun t _ ↦ ⟨t 0, Fin.tail t⟩)
            (fun t ht ↦ by
              simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sigma] at ht ⊢
              simpa only [Fin.cons_self_tail] using ht)
            (fun t₁ _ t₂ _ heq ↦ by
              have h0 : t₁ 0 = t₂ 0 := congrArg Sigma.fst heq
              have htl : Fin.tail t₁ = Fin.tail t₂ := by simpa using congrArg Sigma.snd heq
              rw [← Fin.cons_self_tail t₁, ← Fin.cons_self_tail t₂, h0, htl])
            (fun ⟨c, t'⟩ hct ↦ by
              simp only [Finset.mem_sigma, Finset.mem_univ, Finset.mem_filter, true_and] at hct ⊢
              exact ⟨Fin.cons c t', hct, by simp⟩)
          simpa [Finset.card_sigma] using hcard1
        rw [hsum_eq]
        refine Finset.sum_congr rfl fun c _ ↦ ?_
        rw [← Set.ncard_coe_finset]
        congr 1; ext t'
        simp [updateTuple_succ a hvars c t']
      rw [hdecomp]
      have hpart := Finset.sum_fiberwise_of_maps_to
        (s := Finset.univ) (t := Finset.univ)
        (g := fun c : M ↦ (⟨fiberCount c, Nat.lt_succ_of_le (hfiber_le c)⟩ : Fin (B + 1)))
        (fun c _ ↦ Finset.mem_univ _) (fun c ↦ fiberCount c)
      rw [← hpart]
      refine Finset.sum_congr rfl fun t _ ↦ ?_
      have hcongr : ∑ x ∈ Finset.univ.filter (fun c : M ↦
          (⟨fiberCount c, Nat.lt_succ_of_le (hfiber_le c)⟩ : Fin (B + 1)) = t), fiberCount x =
          ∑ _x ∈ Finset.univ.filter (fun c : M ↦ fiberCount c = t.val), t.val := by
        refine Finset.sum_congr ?_ fun x hx ↦ (Finset.mem_filter.mp hx).2
        ext c; simp [Fin.ext_iff]
      rw [hcongr, Finset.sum_const, smul_eq_mul, mul_comm, ← Set.ncard_coe_finset]
      congr 2
      ext c; simp
    unfold countTupleEq
    rw [GenFormula.realize_iSup]
    constructor
    · rintro ⟨⟨h, hsum⟩, hreal⟩
      rw [GenFormula.realize_iInf] at hreal
      rw [htotal, ← hsum]
      refine Finset.sum_congr rfl fun t _ ↦ ?_
      by_cases ht0 : t.val = 0
      · simp [ht0]
      · have hrt := hreal t
        simp only [ht0, ↓reduceIte, CountingFormula.realize_exactly_iff_ncard] at hrt
        have heq_set : {c : M | (countTupleEq d n (vars ∘ Fin.succ) φ t.val).Realize
            (Function.update a (vars 0) c)} = {c : M | fiberCount c = t.val} := by
          ext c
          exact realize_countTupleEq d n hn (vars ∘ Fin.succ) hinj φ t.val _
        rw [heq_set] at hrt
        rw [hrt]
    · intro hcard
      have hfib_le (t : Fin (B + 1)) : {c : M | fiberCount c = t.val}.ncard ≤ n := by
        refine le_trans ?_ hn
        rw [← Nat.card_eq_fintype_card]
        exact (Set.ncard_le_ncard (Set.subset_univ _) (Set.toFinite _)).trans_eq
          (Set.ncard_univ _)
      let h : Fin (B + 1) → Fin (n + 1) := fun t ↦
        ⟨{c : M | fiberCount c = t.val}.ncard, Nat.lt_succ_of_le (hfib_le t)⟩
      have hsum : ∑ t : Fin (B + 1), t.val * (h t).val = s := by
        simpa [h, htotal] using hcard
      refine ⟨⟨h, hsum⟩, ?_⟩
      rw [GenFormula.realize_iInf]
      intro t
      split_ifs with ht0
      · simp
      · rw [CountingFormula.realize_exactly_iff_ncard]
        have heq_set : {c : M | (countTupleEq d n (vars ∘ Fin.succ) φ t.val).Realize
            (Function.update a (vars 0) c)} = {c : M | fiberCount c = t.val} := by
          ext c
          exact realize_countTupleEq d n hn (vars ∘ Fin.succ) hinj φ t.val _
        rw [heq_set]

/-- Counts equivalence classes of `d`-tuples (for a definable equivalence relation `ψEq`)
satisfying a `ψEq`-invariant formula `φ`, on structures of size at most `n`. -/
noncomputable def countQuotGe (d n : ℕ) (vars₁ vars₂ : Fin d → Fin k)
    (ψEq φ : CountingFormula L k) (c : ℕ) : CountingFormula L k :=
  let B := n ^ d
  GenFormula.iSup fun q : {q : Fin (B + 1) → Fin (B + 1) //
      c ≤ ∑ s : Fin (B + 1), if s.val = 0 then 0 else (q s).val} ↦
    GenFormula.iInf fun s : Fin (B + 1) ↦
      if s.val = 0 then ⊤
      else
        countTupleEq d n vars₁ (φ ⊓ countTupleEq d n vars₂ ψEq s.val) (s.val * (q.1 s).val)

/-- Exact quotient-class count `|{[t]_~ | φ(t)}| = c`. -/
noncomputable def countQuotEq (d n : ℕ) (vars₁ vars₂ : Fin d → Fin k)
    (ψEq φ : CountingFormula L k) (c : ℕ) : CountingFormula L k :=
  countQuotGe d n vars₁ vars₂ ψEq φ c ⊓ (countQuotGe d n vars₁ vars₂ ψEq φ (c + 1)).not

/-- Quantifier rank of `countQuotGe` is linear in `d`: `≤ max φ.qd (ψEq.qd + d) + d`. -/
theorem quantifierRank_countQuotGe_le (d n : ℕ) (vars₁ vars₂ : Fin d → Fin k)
    (ψEq φ : CountingFormula L k) (c : ℕ) :
    (countQuotGe d n vars₁ vars₂ ψEq φ c).quantifierRank ≤
      max φ.quantifierRank (ψEq.quantifierRank + d) + d := by
  unfold countQuotGe
  refine GenFormula.quantifierRank_iSup_le fun _ ↦ GenFormula.quantifierRank_iInf_le fun s ↦ ?_
  split_ifs
  · simp
  · refine (quantifierRank_countTupleEq_le d n vars₁ _ _).trans ?_
    rw [GenFormula.quantifierRank_inf]
    have h2 := quantifierRank_countTupleEq_le d n vars₂ ψEq s.val
    omega

theorem quantifierRank_countQuotEq_le (d n : ℕ) (vars₁ vars₂ : Fin d → Fin k)
    (ψEq φ : CountingFormula L k) (c : ℕ) :
    (countQuotEq d n vars₁ vars₂ ψEq φ c).quantifierRank ≤
      max φ.quantifierRank (ψEq.quantifierRank + d) + d := by
  unfold countQuotEq
  rw [GenFormula.quantifierRank_inf, GenFormula.quantifierRank_not]
  exact max_le (quantifierRank_countQuotGe_le d n vars₁ vars₂ ψEq φ c)
    (quantifierRank_countQuotGe_le d n vars₁ vars₂ ψEq φ (c + 1))

theorem freeVars_countQuotGe_subset (d n : ℕ) (vars₁ vars₂ : Fin d → Fin k)
    (ψEq φ : CountingFormula L k) (c : ℕ) :
    ((countQuotGe d n vars₁ vars₂ ψEq φ c).freeVars : Set (Fin k)) ⊆
      ((φ.freeVars : Set (Fin k)) ∪ ((ψEq.freeVars : Set (Fin k)) \ Set.range vars₂)) \
        Set.range vars₁ := by
  unfold countQuotGe
  refine GenFormula.freeVars_iSup_subset fun _ ↦ GenFormula.freeVars_iInf_subset fun s ↦ ?_
  split_ifs
  · simp
  · intro x hx
    have h1 := freeVars_countTupleEq_subset d n vars₁ _ _ hx
    rw [GenFormula.freeVars_inf, Finset.coe_union] at h1
    refine ⟨?_, h1.2⟩
    rcases h1.1 with hφ | hψ
    · exact Or.inl hφ
    · exact Or.inr (freeVars_countTupleEq_subset d n vars₂ ψEq s.val hψ)

/-- On any finite structure of cardinality at most `n`, when `ψEq` defines an equivalence relation
`R` on `d`-tuples and `φ` is `R`-invariant (and `vars₂` is disjoint from `vars₁` and `φ.freeVars`,
while `ψEq` only depends on `vars₁`, `vars₂`, and fixed outer variables), `countQuotGe` holds iff
at least `c` equivalence classes satisfy `φ`. -/
theorem realize_countQuotGe {M : Type w} [L.Structure M] [Fintype M]
    {d n : ℕ} (hn : Fintype.card M ≤ n)
    {vars₁ vars₂ : Fin d → Fin k}
    (hvars₁ : Function.Injective vars₁) (hvars₂ : Function.Injective vars₂)
    {ψEq φ : CountingFormula L k}
    (a : Fin k → M)
    (R : Setoid (Fin d → M))
    (hR : ∀ t₁ t₂ : Fin d → M,
      ψEq.Realize (updateTuple (updateTuple a vars₁ t₁) vars₂ t₂) ↔ R.r t₁ t₂)
    (hφ_inv : ∀ t₁ t₂ : Fin d → M, R.r t₁ t₂ →
      (φ.Realize (updateTuple a vars₁ t₁) ↔ φ.Realize (updateTuple a vars₁ t₂)))
    (c : ℕ) :
    (countQuotGe d n vars₁ vars₂ ψEq φ c).Realize a ↔
      c ≤ {cl : Quotient R | Quotient.liftOn cl
        (fun t ↦ φ.Realize (updateTuple a vars₁ t))
        (fun t₁ t₂ h ↦ propext (hφ_inv t₁ t₂ h))}.ncard := by
  classical
  let B := n ^ d
  let P : (Fin d → M) → Prop := fun t ↦ φ.Realize (updateTuple a vars₁ t)
  let PQ : Quotient R → Prop := fun cl ↦
    Quotient.liftOn cl P (fun t₁ t₂ h ↦ propext (hφ_inv t₁ t₂ h))
  let classSize (t : Fin d → M) : ℕ := {t' : Fin d → M | R.r t t'}.ncard
  have hB : Fintype.card (Fin d → M) ≤ B := by
    simpa only [Fintype.card_fun, Fintype.card_fin] using Nat.pow_le_pow_left hn d
  have hclassSize_le (t : Fin d → M) : classSize t ≤ B := by
    refine le_trans ?_ hB
    rw [← Nat.card_eq_fintype_card]
    exact (Set.ncard_le_ncard (Set.subset_univ _) (Set.toFinite _)).trans_eq (Set.ncard_univ _)
  have hclassSize_pos (t : Fin d → M) : 0 < classSize t :=
    (Set.ncard_pos (Set.toFinite _)).mpr ⟨t, R.refl t⟩
  have hclassSize_inv : ∀ t₁ t₂, R.r t₁ t₂ → classSize t₁ = classSize t₂ := by
    intro t₁ t₂ h12
    dsimp only [classSize]
    congr 1; ext t'
    exact ⟨fun h ↦ R.trans (R.symm h12) h, fun h ↦ R.trans h12 h⟩
  let classSizeQ : Quotient R → ℕ := fun cl ↦ Quotient.liftOn cl classSize hclassSize_inv
  have hcount_inner (t₁ : Fin d → M) (s : ℕ) :
      (countTupleEq d n vars₂ ψEq s).Realize (updateTuple a vars₁ t₁) ↔ classSize t₁ = s := by
    rw [realize_countTupleEq d n hn vars₂ hvars₂ ψEq s]
    simp only [hR, classSize]
  have hfiber_card (s : ℕ) (_hs : s ≠ 0) :
      {t₁ : Fin d → M | P t₁ ∧ classSize t₁ = s}.ncard =
        s * {cl : Quotient R | PQ cl ∧ classSizeQ cl = s}.ncard := by
    have hbi : {t₁ : Fin d → M | P t₁ ∧ classSize t₁ = s}.ncard =
        (Finset.univ.filter fun t₁ : Fin d → M ↦ P t₁ ∧ classSize t₁ = s).card := by
      rw [← Set.ncard_coe_finset]; congr 1; ext t; simp
    have hbiQ : {cl : Quotient R | PQ cl ∧ classSizeQ cl = s}.ncard =
        (Finset.univ.filter fun cl : Quotient R ↦ PQ cl ∧ classSizeQ cl = s).card := by
      rw [← Set.ncard_coe_finset]; congr 1; ext cl; simp
    rw [hbi, hbiQ]
    have hpart := Finset.card_eq_sum_card_fiberwise
      (s := Finset.univ.filter fun t₁ : Fin d → M ↦ P t₁ ∧ classSize t₁ = s)
      (t := Finset.univ.filter fun cl : Quotient R ↦ PQ cl ∧ classSizeQ cl = s)
      (f := Quotient.mk R)
      (fun t₁ ht₁ ↦ by simpa [PQ, classSizeQ] using ht₁)
    rw [hpart, mul_comm, ← smul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_congr rfl fun cl hcl ↦ ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hcl
    obtain ⟨t₀, rfl⟩ := Quotient.exists_rep cl
    have heq : (Finset.univ.filter fun t₁ : Fin d → M ↦ P t₁ ∧ classSize t₁ = s).filter
        (fun t₁ ↦ Quotient.mk R t₁ = Quotient.mk R t₀) =
        Finset.univ.filter (fun t₁ : Fin d → M ↦ R.r t₀ t₁) := by
      ext t₁
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Quotient.eq]
      exact ⟨fun h ↦ R.symm h.2, fun h ↦
        ⟨⟨(hφ_inv t₀ t₁ h).mp hcl.1, (hclassSize_inv t₀ t₁ h).symm.trans hcl.2⟩, R.symm h⟩⟩
    rw [heq]
    have hcs : classSize t₀ = s := hcl.2
    rw [← hcs, ← Set.ncard_coe_finset]
    dsimp only [classSize]
    congr 1; ext t₁; simp
  have hsumQ : {cl : Quotient R | PQ cl}.ncard =
      ∑ s : Fin (B + 1), if s.val = 0 then 0 else
        {cl : Quotient R | PQ cl ∧ classSizeQ cl = s.val}.ncard := by
    have hbiQ : {cl : Quotient R | PQ cl}.ncard =
        (Finset.univ.filter fun cl : Quotient R ↦ PQ cl).card := by
      rw [← Set.ncard_coe_finset]; congr 1; ext cl; simp
    rw [hbiQ]
    have hmaps : ∀ cl ∈ Finset.univ.filter (fun cl : Quotient R ↦ PQ cl),
        (⟨classSizeQ cl, Nat.lt_succ_of_le (Quotient.inductionOn cl hclassSize_le)⟩ :
          Fin (B + 1)) ∈ Finset.univ := fun _ _ ↦ Finset.mem_univ _
    rw [Finset.card_eq_sum_card_fiberwise hmaps]
    refine Finset.sum_congr rfl fun s _ ↦ ?_
    by_cases hs0 : s.val = 0
    · simp only [hs0, ↓reduceIte, Finset.card_eq_zero]
      ext cl
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      rintro ⟨_, hcs⟩
      have hpos : 0 < classSizeQ cl := Quotient.inductionOn cl hclassSize_pos
      have : classSizeQ cl = 0 := by simpa [Fin.ext_iff, hs0] using hcs
      omega
    · simp only [hs0, ↓reduceIte]
      rw [← Set.ncard_coe_finset]
      congr 1; ext cl
      simp [Fin.ext_iff]
  unfold countQuotGe
  rw [GenFormula.realize_iSup]
  constructor
  · rintro ⟨⟨q, hqsum⟩, hreal⟩
    rw [GenFormula.realize_iInf] at hreal
    rw [show {cl : Quotient R | Quotient.liftOn cl (fun t ↦ φ.Realize (updateTuple a vars₁ t))
        (fun t₁ t₂ h ↦ propext (hφ_inv t₁ t₂ h))}.ncard = {cl : Quotient R | PQ cl}.ncard from rfl,
      hsumQ]
    refine hqsum.trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun s _ ↦ ?_
    by_cases hs0 : s.val = 0
    · simp [hs0]
    · simp only [hs0, ↓reduceIte]
      have hrs := hreal s
      simp only [hs0, ↓reduceIte] at hrs
      rw [realize_countTupleEq d n hn vars₁ hvars₁] at hrs
      have heq : {t₁ : Fin d → M | (φ ⊓ countTupleEq d n vars₂ ψEq s.val).Realize
          (updateTuple a vars₁ t₁)} = {t₁ : Fin d → M | P t₁ ∧ classSize t₁ = s.val} := by
        ext t₁
        simp only [GenFormula.realize_inf, Set.mem_ofPred_eq, hcount_inner, P]
      rw [heq, hfiber_card s.val hs0] at hrs
      exact Nat.mul_left_cancel (Nat.pos_of_ne_zero hs0) hrs.symm
  · intro hcle
    have hq_le (s : Fin (B + 1)) :
        {cl : Quotient R | PQ cl ∧ classSizeQ cl = s.val}.ncard ≤ B := by
      have hle_quot : {cl : Quotient R | PQ cl ∧ classSizeQ cl = s.val}.ncard ≤
          Fintype.card (Quotient R) := by
        rw [← Nat.card_eq_fintype_card]
        exact (Set.ncard_le_ncard (Set.subset_univ _) (Set.toFinite _)).trans_eq
          (Set.ncard_univ _)
      have hquot_le : Fintype.card (Quotient R) ≤ Fintype.card (Fin d → M) :=
        Fintype.card_le_of_surjective (Quotient.mk R) Quotient.exists_rep
      exact (hle_quot.trans hquot_le).trans hB
    let q : Fin (B + 1) → Fin (B + 1) := fun s ↦
      ⟨{cl : Quotient R | PQ cl ∧ classSizeQ cl = s.val}.ncard, Nat.lt_succ_of_le (hq_le s)⟩
    have hqsum : c ≤ ∑ s : Fin (B + 1), if s.val = 0 then 0 else (q s).val := by
      change c ≤ ∑ s : Fin (B + 1), if s.val = 0 then 0 else
        {cl : Quotient R | PQ cl ∧ classSizeQ cl = s.val}.ncard
      rw [← hsumQ]
      exact hcle
    refine ⟨⟨q, hqsum⟩, ?_⟩
    rw [GenFormula.realize_iInf]
    intro s
    split_ifs with hs0
    · simp
    · rw [realize_countTupleEq d n hn vars₁ hvars₁]
      have heq : {t₁ : Fin d → M | (φ ⊓ countTupleEq d n vars₂ ψEq s.val).Realize
          (updateTuple a vars₁ t₁)} = {t₁ : Fin d → M | P t₁ ∧ classSize t₁ = s.val} := by
        ext t₁
        simp only [GenFormula.realize_inf, Set.mem_ofPred_eq, hcount_inner, P]
      rw [heq, hfiber_card s.val hs0]

end TupleAndQuotientCounting

/-! ### Logarithmic quantifier depth and $C^{O(\log n)}$ -/

section LogarithmicDepth

/-- A depth bound `f : ℕ → ℕ` has logarithmic growth (`O(log n)`) if `(f n : ℝ)` is `IsBigO` of
`Real.log n` along `Filter.atTop`. -/
def IsLogarithmicDepth (f : ℕ → ℕ) : Prop :=
  Asymptotics.IsBigO Filter.atTop (fun n ↦ (f n : ℝ)) (fun n ↦ Real.log n)

/-- Constant depth bounds are logarithmic. -/
theorem isLogarithmicDepth_const (c : ℕ) : IsLogarithmicDepth (fun _ ↦ c) := by
  refine Asymptotics.IsBigO.of_bound ((c : ℝ) / Real.log 2) ?_
  refine Filter.eventually_atTop.mpr ⟨2, fun n hn ↦ ?_⟩
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h2n : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hlogn : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) h2n
  have hnonneg : 0 ≤ Real.log n := hlog2.le.trans hlogn
  rw [Real.norm_natCast, Real.norm_of_nonneg hnonneg, div_mul_eq_mul_div, le_div_iff₀' hlog2]
  dsimp only
  rw [mul_comm (Real.log 2)]
  exact mul_le_mul_of_nonneg_left hlogn (Nat.cast_nonneg c)

/-- Sum of two logarithmic depth functions is logarithmic. -/
theorem isLogarithmicDepth_add {f g : ℕ → ℕ} (hf : IsLogarithmicDepth f)
    (hg : IsLogarithmicDepth g) :
    IsLogarithmicDepth (fun n ↦ f n + g n) := by
  obtain ⟨c₁, hc₁⟩ := hf.bound
  obtain ⟨c₂, hc₂⟩ := hg.bound
  refine Asymptotics.IsBigO.of_bound (c₁ + c₂) ?_
  filter_upwards [hc₁, hc₂] with n h₁ h₂
  simp only [Real.norm_natCast] at h₁ h₂ ⊢
  push_cast
  linarith

/-- Pointwise maximum of two logarithmic depth functions is logarithmic. -/
theorem isLogarithmicDepth_max {f g : ℕ → ℕ} (hf : IsLogarithmicDepth f)
    (hg : IsLogarithmicDepth g) :
    IsLogarithmicDepth (fun n ↦ max (f n) (g n)) := by
  obtain ⟨c₁, hc₁⟩ := hf.bound
  obtain ⟨c₂, hc₂⟩ := hg.bound
  refine Asymptotics.IsBigO.of_bound (max c₁ c₂) ?_
  filter_upwards [hc₁, hc₂] with n h₁ h₂
  simp only [Real.norm_natCast] at h₁ h₂ ⊢
  rw [Nat.cast_max]
  exact max_le (h₁.trans (mul_le_mul_of_nonneg_right (le_max_left c₁ c₂) (norm_nonneg _)))
    (h₂.trans (mul_le_mul_of_nonneg_right (le_max_right c₁ c₂) (norm_nonneg _)))

/-- Downward monotonicity of logarithmic depth along `Filter.atTop`. -/
theorem isLogarithmicDepth_mono {f g : ℕ → ℕ} (hfg : ∀ᶠ n in Filter.atTop, f n ≤ g n)
    (hg : IsLogarithmicDepth g) :
    IsLogarithmicDepth f := by
  obtain ⟨c, hc⟩ := hg.bound
  refine Asymptotics.IsBigO.of_bound c ?_
  filter_upwards [hfg, hc] with n hle hbound
  simp only [Real.norm_natCast] at hbound ⊢
  exact (Nat.cast_le.mpr hle).trans hbound

/-- Pointwise domination by a logarithmic depth function yields logarithmic depth. -/
theorem isLogarithmicDepth_of_le {f g : ℕ → ℕ} (hfg : ∀ n, f n ≤ g n)
    (hg : IsLogarithmicDepth g) :
    IsLogarithmicDepth f :=
  isLogarithmicDepth_mono (Filter.Eventually.of_forall hfg) hg

/-- Any depth function bounded eventually by `C * Real.log (n + 1) + D` has logarithmic depth. -/
theorem isLogarithmicDepth_of_le_mul_log_add {f : ℕ → ℕ} (C D : ℝ)
    (h : ∀ᶠ n in Filter.atTop, (f n : ℝ) ≤ C * Real.log (n + 1) + D) :
    IsLogarithmicDepth f := by
  refine Asymptotics.IsBigO.of_bound (2 * max C 0 + |D| / Real.log 2) ?_
  filter_upwards [h, Filter.eventually_atTop.mpr ⟨2, fun _ hm ↦ hm⟩] with n hn h2
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h2n : (2 : ℝ) ≤ n := by exact_mod_cast h2
  have hlogn_ge : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) h2n
  have hlogn_nonneg : 0 ≤ Real.log n := hlog2.le.trans hlogn_ge
  have hpow : (n : ℝ) + 1 ≤ (n : ℝ) ^ 2 := by nlinarith
  have hlog_add : Real.log (n + 1) ≤ 2 * Real.log n := by
    have hle := Real.log_le_log (by linarith) hpow
    rwa [Real.log_pow, Nat.cast_ofNat] at hle
  have hlog_add_nonneg : 0 ≤ Real.log (n + 1) := Real.log_nonneg (by linarith)
  have hC : C * Real.log (n + 1) ≤ (2 * max C 0) * Real.log n := by
    calc C * Real.log (n + 1)
        ≤ max C 0 * Real.log (n + 1) :=
          mul_le_mul_of_nonneg_right (le_max_left C 0) hlog_add_nonneg
      _ ≤ max C 0 * (2 * Real.log n) :=
          mul_le_mul_of_nonneg_left hlog_add (le_max_right C 0)
      _ = (2 * max C 0) * Real.log n := by ring
  have hD : D ≤ (|D| / Real.log 2) * Real.log n := by
    have h1 : |D| ≤ (|D| / Real.log 2) * Real.log n := by
      rw [div_mul_eq_mul_div, le_div_iff₀' hlog2, mul_comm (Real.log 2)]
      exact mul_le_mul_of_nonneg_left hlogn_ge (abs_nonneg D)
    exact (le_abs_self D).trans h1
  rw [Real.norm_natCast, Real.norm_of_nonneg hlogn_nonneg]
  linarith

/-- Any depth function bounded eventually by `C * Nat.log b (n + 1) + D` (`1 < b`) has
logarithmic depth. -/
theorem isLogarithmicDepth_of_le_mul_natLog_add {f : ℕ → ℕ} {b : ℕ} (hb : 1 < b) (C D : ℝ)
    (h : ∀ᶠ n in Filter.atTop, (f n : ℝ) ≤ C * (Nat.log b (n + 1) : ℝ) + D) :
    IsLogarithmicDepth f := by
  refine isLogarithmicDepth_of_le_mul_log_add (max C 0 / Real.log b) D ?_
  have hb_real : (1 : ℝ) < b := by exact_mod_cast hb
  have hlogb : 0 < Real.log b := Real.log_pos hb_real
  filter_upwards [h] with n hn
  have hpow : b ^ Nat.log b (n + 1) ≤ n + 1 := Nat.pow_log_le_self b (Nat.succ_ne_zero n)
  have hpow_r : (b : ℝ) ^ Nat.log b (n + 1) ≤ (n : ℝ) + 1 := by exact_mod_cast hpow
  have hlog_le : (Nat.log b (n + 1) : ℝ) * Real.log b ≤ Real.log (n + 1) := by
    have hpos : (0 : ℝ) < (b : ℝ) ^ Nat.log b (n + 1) := by positivity
    simpa [Real.log_pow] using Real.log_le_log hpos hpow_r
  have hnatlog_le : (Nat.log b (n + 1) : ℝ) ≤ Real.log (n + 1) / Real.log b :=
    (le_div_iff₀ hlogb).mpr hlog_le
  have hC : C * (Nat.log b (n + 1) : ℝ) ≤ (max C 0 / Real.log b) * Real.log (n + 1) := by
    calc C * (Nat.log b (n + 1) : ℝ)
        ≤ max C 0 * (Nat.log b (n + 1) : ℝ) :=
          mul_le_mul_of_nonneg_right (le_max_left C 0) (Nat.cast_nonneg _)
      _ ≤ max C 0 * (Real.log (n + 1) / Real.log b) :=
          mul_le_mul_of_nonneg_left hnatlog_le (le_max_right C 0)
      _ = (max C 0 / Real.log b) * Real.log (n + 1) := by ring
  linarith

/-- Negative logarithmic-depth witness: the linear function `id` is not `O(log n)`. -/
theorem not_isLogarithmicDepth_id : ¬ IsLogarithmicDepth id := by
  intro h
  obtain ⟨C, hC⟩ := h.bound
  have hlog := Real.isLittleO_log_id_atTop.def (show (0 : ℝ) < (2 * max C 1)⁻¹ by positivity)
  have hnat : ∀ᶠ n : ℕ in Filter.atTop,
      ‖Real.log n‖ ≤ (2 * max C 1)⁻¹ * ‖(n : ℝ)‖ :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually hlog
  obtain ⟨N, hN⟩ := (hC.and (hnat.and (Filter.eventually_atTop.mpr ⟨2, fun _ hm ↦ hm⟩))).exists
  have h1 := hN.1
  have h2 := hN.2.1
  have h3 : (2 : ℝ) ≤ N := by exact_mod_cast hN.2.2
  simp only [id_eq, Real.norm_natCast] at h1 h2
  have hbound : (N : ℝ) ≤ (1 / 2 : ℝ) * N := by
    calc (N : ℝ) ≤ C * ‖Real.log N‖ := h1
      _ ≤ max C 1 * ‖Real.log N‖ := mul_le_mul_of_nonneg_right (le_max_left C 1) (norm_nonneg _)
      _ ≤ max C 1 * ((2 * max C 1)⁻¹ * (N : ℝ)) :=
          mul_le_mul_of_nonneg_left h2 (le_trans zero_le_one (le_max_right C 1))
      _ = (1 / 2 : ℝ) * N := by
          have hpos : max C 1 ≠ 0 := (lt_of_lt_of_le zero_lt_one (le_max_right C 1)).ne'
          field_simp [hpos]
  linarith

/-- A class of finite nonempty `L`-structures is expressed in `C_k^{O(log n)}` when a family of
`C_k`-sentences of logarithmic quantifier rank defines it at every cardinality `n`. -/
@[expose] def ExpressesClassInCLogAt (L : Language.{u, v}) (k : ℕ)
    (𝒞 : ∀ (M : Type w) [L.Structure M] [Fintype M] [Nonempty M], Prop) : Prop :=
  ∃ Φ : ℕ → CountingFormula L k,
    (∀ n, IsSentence (Φ n)) ∧
    IsLogarithmicDepth (fun n ↦ (Φ n).quantifierRank) ∧
    ∀ (M : Type w) [L.Structure M] [Fintype M] [Nonempty M],
      𝒞 M ↔ SentenceRealize M (Φ (Fintype.card M))

/-- A class of finite nonempty `L`-structures is expressed in `C^{O(log n)}`. -/
@[expose] def ExpressesClassInCLog (L : Language.{u, v})
    (𝒞 : ∀ (M : Type w) [L.Structure M] [Fintype M] [Nonempty M], Prop) : Prop :=
  ∃ k : ℕ, ExpressesClassInCLogAt L k 𝒞

theorem ExpressesClassInCLogAt.mono {L : Language.{u, v}} {k₁ k₂ : ℕ} (hk : k₁ ≤ k₂)
    {𝒞 : ∀ (M : Type w) [L.Structure M] [Fintype M] [Nonempty M], Prop}
    (h : ExpressesClassInCLogAt L k₁ 𝒞) :
    ExpressesClassInCLogAt L k₂ 𝒞 := by
  obtain ⟨Φ, hsent, hqd, hiff⟩ := h
  refine ⟨fun n ↦ castLE hk (Φ n), fun n ↦ (isSentence_castLE hk (Φ n)).mpr (hsent n),
    by simpa using hqd, fun M _ _ _ ↦ ?_⟩
  rw [hiff M, sentenceRealize_castLE]

theorem ExpressesClassInCLogAt.not {L : Language.{u, v}} {k : ℕ}
    {𝒞 : ∀ (M : Type w) [L.Structure M] [Fintype M] [Nonempty M], Prop}
    (h : ExpressesClassInCLogAt L k 𝒞) :
    ExpressesClassInCLogAt L k (fun M _ _ _ ↦ ¬ 𝒞 M) := by
  obtain ⟨Φ, hsent, hqd, hiff⟩ := h
  refine ⟨fun n ↦ (Φ n).not, fun n ↦ (hsent n).not, by simpa using hqd, fun M _ _ _ ↦ ?_⟩
  dsimp only
  rw [(hsent (Fintype.card M)).sentenceRealize_not, hiff M]

theorem ExpressesClassInCLogAt.and {L : Language.{u, v}} {k : ℕ}
    {𝒞₁ 𝒞₂ : ∀ (M : Type w) [L.Structure M] [Fintype M] [Nonempty M], Prop}
    (h₁ : ExpressesClassInCLogAt L k 𝒞₁) (h₂ : ExpressesClassInCLogAt L k 𝒞₂) :
    ExpressesClassInCLogAt L k (fun M _ _ _ ↦ 𝒞₁ M ∧ 𝒞₂ M) := by
  obtain ⟨Φ₁, hsent₁, hqd₁, hiff₁⟩ := h₁
  obtain ⟨Φ₂, hsent₂, hqd₂, hiff₂⟩ := h₂
  refine ⟨fun n ↦ Φ₁ n ⊓ Φ₂ n, fun n ↦ (hsent₁ n).inf (hsent₂ n),
    by simpa using isLogarithmicDepth_max hqd₁ hqd₂, fun M _ _ _ ↦ ?_⟩
  dsimp only
  rw [(hsent₁ _).sentenceRealize_inf (hsent₂ _), hiff₁ M, hiff₂ M]

theorem ExpressesClassInCLogAt.or {L : Language.{u, v}} {k : ℕ}
    {𝒞₁ 𝒞₂ : ∀ (M : Type w) [L.Structure M] [Fintype M] [Nonempty M], Prop}
    (h₁ : ExpressesClassInCLogAt L k 𝒞₁) (h₂ : ExpressesClassInCLogAt L k 𝒞₂) :
    ExpressesClassInCLogAt L k (fun M _ _ _ ↦ 𝒞₁ M ∨ 𝒞₂ M) := by
  obtain ⟨Φ₁, hsent₁, hqd₁, hiff₁⟩ := h₁
  obtain ⟨Φ₂, hsent₂, hqd₂, hiff₂⟩ := h₂
  refine ⟨fun n ↦ Φ₁ n ⊔ Φ₂ n, fun n ↦ (hsent₁ n).sup (hsent₂ n),
    by simpa using isLogarithmicDepth_max hqd₁ hqd₂, fun M _ _ _ ↦ ?_⟩
  dsimp only
  rw [(hsent₁ _).sentenceRealize_sup (hsent₂ _), hiff₁ M, hiff₂ M]

theorem ExpressesClassInCLog.isoClosed {L : Language.{u, v}}
    {𝒞 : ∀ (M : Type w) [L.Structure M] [Fintype M] [Nonempty M], Prop}
    (h : ExpressesClassInCLog L 𝒞)
    {M : Type w} [L.Structure M] [Fintype M] [Nonempty M]
    {N : Type w} [L.Structure N] [Fintype N] [Nonempty N]
    (e : M ≃[L] N) :
    𝒞 M ↔ 𝒞 N := by
  obtain ⟨k, Φ, _, _, hiff⟩ := h
  have hcard : Fintype.card M = Fintype.card N := Fintype.card_congr e.toEquiv
  rw [hiff M, hiff N, hcard]
  exact (Equiv.sentenceRealize_countingFormula_iff e (Φ (Fintype.card N))).symm

/-- Two `L`-structures `M` and `N` are `C_k^r`-equivalent when they agree on all `C_k`-sentences of
quantifier rank at most `r`. -/
@[expose] def CountingEquiv (L : Language.{u, v}) (k r : ℕ) (M : Type w) (N : Type w')
    [L.Structure M] [L.Structure N] : Prop :=
  ∀ φ : CountingFormula L k, IsSentence φ → φ.quantifierRank ≤ r →
    (SentenceRealize M φ ↔ SentenceRealize N φ)

/-- A class `K` of finite nonempty `L`-structures is identified in `C_k^{O(log n)}` when there is a
logarithmic depth bound `d` such that every `M` in `K` admits a `C_k`-sentence of depth `≤ d |M|`
characterizing `M` up to isomorphism among finite nonempty structures. -/
@[expose] def IdentifiesInCLogAt (L : Language.{u, v}) (k : ℕ)
    (K : ∀ (M : Type w) [L.Structure M] [Fintype M] [Nonempty M], Prop) : Prop :=
  ∃ d : ℕ → ℕ,
    IsLogarithmicDepth d ∧
    ∀ (M : Type w) [L.Structure M] [Fintype M] [Nonempty M], K M →
      ∃ φ : CountingFormula L k,
        IsSentence φ ∧
        φ.quantifierRank ≤ d (Fintype.card M) ∧
        SentenceRealize M φ ∧
        ∀ (N : Type w) [L.Structure N] [Fintype N] [Nonempty N],
          SentenceRealize N φ → Nonempty (M ≃[L] N)

/-- A class `K` of finite nonempty `L`-structures is identified in `C^{O(log n)}`. -/
@[expose] def IdentifiesInCLog (L : Language.{u, v})
    (K : ∀ (M : Type w) [L.Structure M] [Fintype M] [Nonempty M], Prop) : Prop :=
  ∃ k : ℕ, IdentifiesInCLogAt L k K

theorem IdentifiesInCLogAt.mono {L : Language.{u, v}} {k₁ k₂ : ℕ} (hk : k₁ ≤ k₂)
    {K : ∀ (M : Type w) [L.Structure M] [Fintype M] [Nonempty M], Prop}
    (h : IdentifiesInCLogAt L k₁ K) :
    IdentifiesInCLogAt L k₂ K := by
  obtain ⟨d, hd, hident⟩ := h
  refine ⟨d, hd, fun M _ _ _ hM ↦ ?_⟩
  obtain ⟨φ, hsent, hqd, hreal, huniq⟩ := hident M hM
  refine ⟨castLE hk φ, (isSentence_castLE hk φ).mpr hsent, by simpa using hqd,
    (sentenceRealize_castLE hk φ).mpr hreal, fun N _ _ _ hN ↦
      huniq N ((sentenceRealize_castLE hk φ).mp hN)⟩

/-- Same-cardinality reduction for `IdentifiesInCLogAt`: conjoining `∃^{= |M|} x₀ ⊤` extends
same-cardinality identification to all finite nonempty structures. -/
theorem IdentifiesInCLogAt.of_sameCard {L : Language.{u, v}} {k : ℕ} (hk : 0 < k)
    {K : ∀ (M : Type w) [L.Structure M] [Fintype M] [Nonempty M], Prop}
    (d : ℕ → ℕ) (hd : IsLogarithmicDepth d)
    (h : ∀ (M : Type w) [L.Structure M] [Fintype M] [Nonempty M], K M →
      ∃ φ : CountingFormula L k,
        IsSentence φ ∧ φ.quantifierRank ≤ d (Fintype.card M) ∧ SentenceRealize M φ ∧
        ∀ (N : Type w) [L.Structure N] [Fintype N] [Nonempty N],
          Fintype.card N = Fintype.card M → SentenceRealize N φ → Nonempty (M ≃[L] N)) :
    IdentifiesInCLogAt L k K := by
  classical
  refine ⟨fun n ↦ max (d n) 1, isLogarithmicDepth_max hd (isLogarithmicDepth_const 1), ?_⟩
  intro M _ _ _ hM
  obtain ⟨φ, hsent, hqd, hreal, huniq⟩ := h M hM
  let i₀ : Fin k := ⟨0, hk⟩
  let cardF : CountingFormula L k := CountingFormula.exactly (Fintype.card M) i₀ ⊤
  have hcardF_sent : IsSentence cardF := by simp [cardF, IsSentence]
  refine ⟨φ ⊓ cardF, hsent.inf hcardF_sent, ?_, ?_, ?_⟩
  · simp only [GenFormula.quantifierRank_inf, cardF, CountingFormula.quantifierRank_exactly,
      GenFormula.quantifierRank_top]
    exact max_le (hqd.trans (le_max_left _ _)) (le_max_right _ _)
  · rw [hsent.sentenceRealize_inf hcardF_sent]
    refine ⟨hreal, fun a ↦ ?_⟩
    rw [CountingFormula.realize_exactly_iff_ncard]
    simp [Nat.card_eq_fintype_card]
  · intro N _ _ _ hN
    rw [hsent.sentenceRealize_inf hcardF_sent] at hN
    have hcardN : Fintype.card N = Fintype.card M := by
      have ha := hN.2 (fun _ ↦ Classical.arbitrary N)
      rw [CountingFormula.realize_exactly_iff_ncard] at ha
      simpa [Nat.card_eq_fintype_card] using ha
    exact huniq N hcardN hN.1

/-- Identification in `C^{O(log n)}` implies uniform `C_k^{O(log n)}`-distinguishability from
every non-isomorphic finite nonempty structure across all universes. -/
theorem IdentifiesInCLog.distinguishes {L : Language.{u, v}}
    {K : ∀ (M : Type w) [L.Structure M] [Fintype M] [Nonempty M], Prop}
    (h : IdentifiesInCLog L K) :
    ∃ (k : ℕ) (d : ℕ → ℕ), IsLogarithmicDepth d ∧
      ∀ (M : Type w) [L.Structure M] [Fintype M] [Nonempty M], K M →
        ∀ (N : Type w') [L.Structure N] [Fintype N] [Nonempty N],
          IsEmpty (M ≃[L] N) → ¬ CountingEquiv L k (d (Fintype.card M)) M N := by
  obtain ⟨k, d, hd, hident⟩ := h
  refine ⟨k, d, hd, fun M _ _ _ hM N _ _ _ hne hEq ↦ ?_⟩
  obtain ⟨φ, hsent, hqd, hrealM, huniq⟩ := hident M hM
  have hrealN : SentenceRealize N φ := (hEq φ hsent hqd).mp hrealM
  let eFin : N ≃ Fin (Fintype.card N) := Fintype.equivFin N
  let e : N ≃ ULift.{w} (Fin (Fintype.card N)) := eFin.trans _root_.Equiv.ulift.symm
  let _ : L.Structure (ULift.{w} (Fin (Fintype.card N))) := e.inducedStructure
  have eIso : N ≃[L] ULift.{w} (Fin (Fintype.card N)) := e.inducedStructureEquiv
  let _ : Nonempty (ULift.{w} (Fin (Fintype.card N))) := ⟨e (Classical.arbitrary N)⟩
  have hrealN' : SentenceRealize (ULift.{w} (Fin (Fintype.card N))) φ :=
    (Equiv.sentenceRealize_countingFormula_iff eIso φ).mpr hrealN
  obtain ⟨eMN'⟩ := huniq (ULift.{w} (Fin (Fintype.card N))) hrealN'
  exact hne.false (eIso.symm.comp eMN')

end LogarithmicDepth

/-! ### Weisfeiler–Leman logarithmic-iteration bridge via `CslibFrontier` -/

section WeisfeilerLemanBridge

/-- `r` rounds of `k`-dimensional Weisfeiler–Leman distinguish finite simple graphs `G` and `H`
when their round-`r` tuple color histograms differ. -/
@[expose] def WLDistinguishes {V : Type w} {W : Type w'} [Fintype V] [Fintype W] (k r : ℕ)
    (G : SimpleGraph V) (H : SimpleGraph W) : Prop :=
  G.wlHistogram k r ≠ H.wlHistogram k r

/-- A class `K` of finite nonempty simple graphs is identified by `k`-WL in `O(log n)` iterations.
-/
@[expose] def WLIdentifiesInLogAt (k : ℕ)
    (K : ∀ (V : Type w) [Fintype V] [Nonempty V], SimpleGraph V → Prop) : Prop :=
  ∃ d : ℕ → ℕ, IsLogarithmicDepth d ∧
    ∀ (V : Type w) [Fintype V] [Nonempty V] (G : SimpleGraph V), K V G →
      ∀ (W : Type w) [Fintype W] [Nonempty W] (H : SimpleGraph W),
        IsEmpty (G ≃g H) → WLDistinguishes k (d (Fintype.card V)) G H

/-- A class `K` of finite nonempty simple graphs is identified by `WL_k^{O(log n)}` for some
constant dimension `k`. -/
@[expose] def WLIdentifiesInLog
    (K : ∀ (V : Type w) [Fintype V] [Nonempty V], SimpleGraph V → Prop) : Prop :=
  ∃ k : ℕ, WLIdentifiesInLogAt k K

/-- **Cai–Fürer–Immerman / Grohe–Verbitsky (forward direction)**: if a `C_{k+1}^r`-sentence
distinguishes `G` and `H`, then `WL_k^r` distinguishes `G` and `H`. -/
theorem wlDistinguishes_of_countingFormula {V : Type w} {W : Type w'} [Fintype V] [Fintype W]
    [Nonempty V] [Nonempty W] {k r : ℕ} {G : SimpleGraph V} {H : SimpleGraph W}
    (φ : CountingFormula Language.graph (k + 1)) (hsent : IsSentence φ)
    (hqd : φ.quantifierRank ≤ r)
    (hsep : (let _ := G.structure; SentenceRealize V φ) ↔
      ¬ (let _ := H.structure; SentenceRealize W φ)) :
    WLDistinguishes k r G H := by
  intro heq
  let a : Fin (k + 1) → V := fun _ ↦ Classical.arbitrary V
  let b : Fin (k + 1) → W := fun _ ↦ Classical.arbitrary W
  have hiff : (let _ := G.structure; φ.Realize a) ↔ (let _ := H.structure; φ.Realize b) :=
    realize_countingFormula_iff_of_wlHistogram_eq heq hqd hsent a b
  have hG : (let _ := G.structure; SentenceRealize V φ) ↔ (let _ := G.structure; φ.Realize a) :=
    let _ := G.structure; hsent.sentenceRealize_iff_realize a
  have hH : (let _ := H.structure; SentenceRealize W φ) ↔ (let _ := H.structure; φ.Realize b) :=
    let _ := H.structure; hsent.sentenceRealize_iff_realize b
  rw [hG, hH] at hsep
  exact (hsep.mp (hiff.mpr (by tauto))) (hiff.mp (by tauto))

/-- **Cai–Fürer–Immerman / Grohe–Verbitsky (sharp converse)**: if `WL_k^r` distinguishes nonempty
finite simple graphs `G` and `H`, then some `C_{k+1}^{r + k}`-sentence distinguishes `G` and `H`.
-/
theorem exists_countingFormula_of_wlDistinguishes {V : Type w} {W : Type w'} [Fintype V]
    [Fintype W] [Nonempty V] [Nonempty W] {k r : ℕ} {G : SimpleGraph V} {H : SimpleGraph W}
    (h : WLDistinguishes k r G H) :
    ∃ φ : CountingFormula Language.graph (k + 1),
      IsSentence φ ∧ φ.quantifierRank ≤ r + k ∧
        ((let _ := G.structure; SentenceRealize V φ) ↔
          ¬ (let _ := H.structure; SentenceRealize W φ)) := by
  by_contra! hall
  apply h
  refine wlHistogram_eq_of_forall_realize_countingFormula_empty_le fun φ hqd hsent a b ↦ ?_
  have hG : (let _ := G.structure; SentenceRealize V φ) ↔ (let _ := G.structure; φ.Realize a) :=
    let _ := G.structure; IsSentence.sentenceRealize_iff_realize hsent a
  have hH : (let _ := H.structure; SentenceRealize W φ) ↔ (let _ := H.structure; φ.Realize b) :=
    let _ := H.structure; IsSentence.sentenceRealize_iff_realize hsent b
  by_contra hne
  have hnot := hall φ hsent hqd
  rw [hG, hH] at hnot
  tauto

/-- Every class of finite nonempty simple graphs identified in `C_{k+1}^{O(log n)}` is identified
by `WL_k^{O(log n)}`. -/
theorem wlIdentifiesInLogAt_of_identifiesInCLogAt {k : ℕ}
    {K : ∀ (V : Type w) [Fintype V] [Nonempty V], SimpleGraph V → Prop}
    (h : IdentifiesInCLogAt Language.graph (k + 1)
      (fun (M : Type w) [Language.graph.Structure M] [Fintype M] [Nonempty M] ↦
        ∃ _ : M ⊨ Theory.simpleGraph, K M (simpleGraphOfStructure M))) :
    WLIdentifiesInLogAt k K := by
  obtain ⟨d, hd, hident⟩ := h
  refine ⟨d, hd, fun V _ _ G hG W _ _ H hne ↦ ?_⟩
  let _ := G.structure
  have hMG : ∃ _ : V ⊨ Theory.simpleGraph, K V (simpleGraphOfStructure V) := by
    refine ⟨Language.simpleGraph_model G, ?_⟩
    simpa only [SimpleGraph.simpleGraphOfStructure] using hG
  obtain ⟨φ, hsent, hqd, hrealG, huniq⟩ := hident V hMG
  refine wlDistinguishes_of_countingFormula φ hsent hqd ?_
  refine iff_of_true hrealG fun hrealH ↦ ?_
  let _ := H.structure
  obtain ⟨e⟩ := huniq W hrealH
  exact hne.false (SimpleGraph.Iso.ofLanguageEquiv e)

end WeisfeilerLemanBridge

/-! ### Private sanity witnesses -/

example : ¬ IsLogarithmicDepth id := not_isLogarithmicDepth_id

end Cslib.Logic.FO.FiniteVariable
