/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import CslibFrontier.Probability.StatisticalDistance
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Rank
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.Map
import CslibFrontier.Probability.PMF.ToReal
import CslibFrontier.Probability.Uniform
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Random Symmetric and Gram Matrices over $\mathbb{F}_2$

This module develops probabilistic linear algebra over $\mathbb{F}_2$ for symmetric matrices and
Gram matrices of random full-rank matrices:

1. **Gram-to-uniform total variation bound**: For $k + 1 \le n$, the Gram matrix $M M^\top$ of a
   uniformly random full-row-rank $k \times n$ matrix $M$ over $\mathbb{F}_2$ is within total
   variation distance $3 \cdot 2^{k - n}$ of a uniformly random symmetric $k \times k$ matrix over
   $\mathbb{F}_2$.
2. **Nonsingularity probability bound**: For every $k \ge 4$, a uniformly random symmetric
   $k \times k$ matrix over $\mathbb{F}_2$ is nonsingular with probability at most
   $1 / 2 - 2^{-7}$.

## Main definitions

* `CslibFrontier.Matrix.RandomSymmetric.SymMat`: symmetric $k \times k$ matrices over
  $\mathbb{F}_2$.
* `CslibFrontier.Matrix.RandomSymmetric.gramMat`: Gram matrix $M M^\top \in \mathrm{SymMat}\ k$.
* `CslibFrontier.Matrix.RandomSymmetric.uniformSymMat`: uniform distribution on
  $\mathrm{SymMat}\ k$.
* `CslibFrontier.Matrix.RandomSymmetric.gramPMF`: distribution of $M M^\top$ for uniformly random
  full-row-rank $M \in \mathbb{F}_2^{k \times n}$.
* `CslibFrontier.Matrix.RandomSymmetric.symMatSplitEquiv`,
  `CslibFrontier.Matrix.RandomSymmetric.symMatExtend`: border decomposition and extension of
  symmetric matrices.

## Main results

* `CslibFrontier.Matrix.RandomSymmetric.dist_gramPMF_uniformSymMat_le`: total variation distance
  $\le 3 \cdot 2^{k - n}$ between `gramPMF` and `uniformSymMat`.
* `CslibFrontier.Matrix.RandomSymmetric.card_extend_same_rank_ge`: rank-preserving symmetric
  extensions lower bound ($2^{\mathrm{rank}(B)}$ extensions preserve $\mathrm{rank}(B)$).
* `CslibFrontier.Matrix.RandomSymmetric.card_rank_le_sub_three_ge`: at least a $2^{-6}$ fraction
  of symmetric $(s + 3) \times (s + 3)$ matrices over $\mathbb{F}_2$ have rank at most $s + 1$.
* `CslibFrontier.Matrix.RandomSymmetric.prob_symmetric_fullRank_le`: for $k \ge 4$,
  $\Pr[\det A \ne 0] \le 1 / 2 - 2^{-7}$ for a uniformly random $A \in \mathrm{SymMat}\ k$.
-/

open scoped Matrix Cslib.Probability.PMF

namespace CslibFrontier.Matrix.RandomSymmetric

public section

private lemma zmod2_eq_zero_or_one (x : ZMod 2) : x = 0 ∨ x = 1 := by
  fin_cases x
  · exact Or.inl rfl
  · exact Or.inr rfl

private lemma zmod2_add_self (x : ZMod 2) : x + x = 0 := by
  rcases zmod2_eq_zero_or_one x with rfl | rfl <;> decide

private lemma zmod2_sq (x : ZMod 2) : x * x = x := by
  rcases zmod2_eq_zero_or_one x with rfl | rfl <;> decide

private lemma fin_cons_snoc {n k : ℕ} (v₀ : Fin n → ZMod 2) (a : Fin k → Fin n → ZMod 2)
    (v : Fin n → ZMod 2) :
    Fin.cons (α := fun _ ↦ Fin n → ZMod 2) v₀ (Fin.snoc (α := fun _ ↦ Fin n → ZMod 2) a v) =
      Fin.snoc (α := fun _ ↦ Fin n → ZMod 2) (Fin.cons (α := fun _ ↦ Fin n → ZMod 2) v₀ a) v := by
  ext i j
  refine Fin.cases ?_ (fun l ↦ ?_) i
  · change v₀ j = Fin.snoc (α := fun _ ↦ Fin n → ZMod 2)
      (Fin.cons (α := fun _ ↦ Fin n → ZMod 2) v₀ a) v (0 : Fin (k + 1)).castSucc j
    simp
  · refine Fin.lastCases ?_ (fun m ↦ ?_) l
    · rw [Fin.cons_succ, Fin.snoc_last,
        show (Fin.last k).succ = Fin.last (k + 1) from rfl, Fin.snoc_last]
    · rw [Fin.cons_succ, Fin.snoc_castSucc, Fin.succ_castSucc, Fin.snoc_castSucc, Fin.cons_succ]

/-! ### Symmetric matrices over $\mathbb{F}_2$ and border decomposition -/

/-- Symmetric $k \times k$ matrices over $\mathbb{F}_2$. -/
abbrev SymMat (k : ℕ) : Type := { A : Matrix (Fin k) (Fin k) (ZMod 2) // Aᵀ = A }

/-- Gram matrix $M M^\top \in \mathrm{SymMat}\ k$ of a $k$-tuple of vectors in $\mathbb{F}_2^n$. -/
def gramMat {k n : ℕ} (a : Fin k → Fin n → ZMod 2) : SymMat k :=
  ⟨(Matrix.of a) * (Matrix.of a)ᵀ, by simp [Matrix.transpose_mul]⟩

/-- Underlying matrix of `gramMat a`. -/
theorem gramMat_val {k n : ℕ} (a : Fin k → Fin n → ZMod 2) :
    (gramMat a).1 = (Matrix.of a) * (Matrix.of a)ᵀ := by
  rfl

/-- Uniform distribution on symmetric $k \times k$ matrices over $\mathbb{F}_2$. -/
noncomputable def uniformSymMat (k : ℕ) : PMF (SymMat k) :=
  have : Nonempty (SymMat k) := ⟨⟨0, Matrix.transpose_zero⟩⟩
  Cslib.Probability.PMF.uniformOfFintype (SymMat k)

/-- Point mass of `uniformSymMat k`. -/
theorem uniformSymMat_apply {k : ℕ} (A : SymMat k) :
    uniformSymMat k A = (Fintype.card (SymMat k) : ENNReal)⁻¹ := by
  have : Nonempty (SymMat k) := ⟨⟨0, Matrix.transpose_zero⟩⟩
  simp [uniformSymMat, Cslib.Probability.PMF.uniformOfFintype_apply]

/-- Splitting a symmetric $(k + 1) \times (k + 1)$ matrix into its top-left $k \times k$ principal
submatrix, the first $k$ entries of its last row, and its bottom-right diagonal entry. -/
def symMatSplitEquiv (k : ℕ) :
    SymMat (k + 1) ≃ SymMat k × ((Fin k → ZMod 2) × ZMod 2) where
  toFun A :=
    (⟨A.1.submatrix Fin.castSucc Fin.castSucc, by
        ext i j; exact congrFun (congrFun A.2 i.castSucc) j.castSucc⟩,
      (fun j ↦ A.1 (Fin.last k) j.castSucc, A.1 (Fin.last k) (Fin.last k)))
  invFun p :=
    ⟨Matrix.of fun i j ↦
        Fin.lastCases (Fin.lastCases p.2.2 (fun j' ↦ p.2.1 j') j)
          (fun i' ↦ Fin.lastCases (p.2.1 i') (fun j' ↦ p.1.1 i' j') j) i, by
      ext i j
      refine Fin.lastCases ?_ (fun i' ↦ ?_) i <;> refine Fin.lastCases ?_ (fun j' ↦ ?_) j
      · simp
      · simp
      · simp
      · simp [← congrFun (congrFun p.1.2 i') j']⟩
  left_inv A := by
    apply Subtype.ext
    ext i j
    refine Fin.lastCases ?_ (fun i' ↦ ?_) i <;> refine Fin.lastCases ?_ (fun j' ↦ ?_) j
    · simp
    · simp
    · simpa using congrFun (congrFun A.2 i'.castSucc) (Fin.last k)
    · simp
  right_inv p := by
    rcases p with ⟨⟨B, hB⟩, r, u⟩
    refine Prod.ext (Subtype.ext ?_) (Prod.ext ?_ ?_)
    · ext i j; simp
    · ext j; simp
    · simp

/-- Extending a symmetric $k \times k$ matrix $B$ by border row $r$ and diagonal entry $u$. -/
def symMatExtend {k : ℕ} (B : SymMat k) (r : Fin k → ZMod 2) (u : ZMod 2) : SymMat (k + 1) :=
  (symMatSplitEquiv k).symm (B, (r, u))

/-- Reconstructing a symmetric matrix from its split equals the original matrix. -/
theorem symMatExtend_symMatSplitEquiv {k : ℕ} (A : SymMat (k + 1)) :
    symMatExtend (symMatSplitEquiv k A).1 (symMatSplitEquiv k A).2.1
      (symMatSplitEquiv k A).2.2 = A := by
  exact (symMatSplitEquiv k).left_inv A

/-- Splitting an extended symmetric matrix recovers the base matrix and border. -/
theorem symMatSplitEquiv_symMatExtend {k : ℕ} (B : SymMat k) (r : Fin k → ZMod 2) (u : ZMod 2) :
    symMatSplitEquiv k (symMatExtend B r u) = (B, (r, u)) := by
  exact (symMatSplitEquiv k).right_inv (B, (r, u))

/-- Top-left block entry of `symMatExtend`. -/
theorem symMatExtend_apply_castSucc_castSucc {k : ℕ} (B : SymMat k)
    (r : Fin k → ZMod 2) (u : ZMod 2) (i j : Fin k) :
    (symMatExtend B r u).1 i.castSucc j.castSucc = B.1 i j := by
  simp [symMatExtend, symMatSplitEquiv]

/-- Bottom-left border entry of `symMatExtend`. -/
theorem symMatExtend_apply_last_castSucc {k : ℕ} (B : SymMat k)
    (r : Fin k → ZMod 2) (u : ZMod 2) (j : Fin k) :
    (symMatExtend B r u).1 (Fin.last k) j.castSucc = r j := by
  simp [symMatExtend, symMatSplitEquiv]

/-- Top-right border entry of `symMatExtend`. -/
theorem symMatExtend_apply_castSucc_last {k : ℕ} (B : SymMat k)
    (r : Fin k → ZMod 2) (u : ZMod 2) (i : Fin k) :
    (symMatExtend B r u).1 i.castSucc (Fin.last k) = r i := by
  simp [symMatExtend, symMatSplitEquiv]

/-- Bottom-right diagonal entry of `symMatExtend`. -/
theorem symMatExtend_apply_last_last {k : ℕ} (B : SymMat k)
    (r : Fin k → ZMod 2) (u : ZMod 2) :
    (symMatExtend B r u).1 (Fin.last k) (Fin.last k) = u := by
  simp [symMatExtend, symMatSplitEquiv]

/-- Cardinality recurrence for symmetric matrices over $\mathbb{F}_2$:
$|\mathrm{SymMat}\ (k + 1)| = |\mathrm{SymMat}\ k| \cdot 2^{k + 1}$. -/
theorem card_symMat_succ (k : ℕ) :
    Fintype.card (SymMat (k + 1)) = Fintype.card (SymMat k) * 2 ^ (k + 1) := by
  rw [Fintype.card_congr (symMatSplitEquiv k), Fintype.card_prod, Fintype.card_prod,
    Fintype.card_fun, ZMod.card, Fintype.card_fin, pow_succ]

/-! ### Counting linearly independent tuples and Gram matrix distribution -/

open Classical in
private lemma card_indepTuples (n : ℕ) : ∀ k : ℕ, k ≤ n →
    Fintype.card { a : Fin k → Fin n → ZMod 2 // LinearIndependent (ZMod 2) a } =
      ∏ i ∈ Finset.range k, (2 ^ n - 2 ^ i) := by
  intro k
  induction k with
  | zero =>
    intro _
    have h1 : ∀ a : Fin 0 → Fin n → ZMod 2, LinearIndependent (ZMod 2) a :=
      fun _ ↦ linearIndependent_empty_type
    rw [Finset.range_zero, Finset.prod_empty, Fintype.card_congr (Equiv.subtypeUnivEquiv h1)]
    simp
  | succ k ih =>
    intro hkn
    rw [Finset.prod_range_succ, ← ih (by omega)]
    have hbij :
        Fintype.card { a : Fin (k + 1) → Fin n → ZMod 2 // LinearIndependent (ZMod 2) a } =
          ∑ a' : { a' : Fin k → Fin n → ZMod 2 // LinearIndependent (ZMod 2) a' },
            (Finset.univ.filter fun v : Fin n → ZMod 2 ↦
              v ∉ Submodule.span (ZMod 2) (Set.range a'.1)).card := by
      rw [← Finset.card_sigma, ← Finset.card_univ]
      refine Finset.card_bij (fun a _ ↦
          ⟨⟨Fin.init a.1, a.2.comp Fin.castSucc (Fin.castSucc_injective k)⟩, a.1 (Fin.last k)⟩)
        (fun a _ ↦ ?_)
        (fun a₁ _ a₂ _ h ↦ ?_)
        (fun ⟨a', v⟩ hp ↦ ?_)
      · refine Finset.mem_sigma.mpr ⟨Finset.mem_univ _, Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, fun hmem ↦ ?_⟩⟩
        rw [Submodule.mem_span_range_iff_exists_fun] at hmem
        obtain ⟨c, hc⟩ := hmem
        have hsum : ∑ i : Fin (k + 1),
            Fin.snoc (α := fun _ ↦ ZMod 2) c (1 : ZMod 2) i • a.1 i = 0 := by
          rw [Fin.sum_univ_castSucc]
          simp only [Fin.snoc_castSucc, Fin.snoc_last, one_smul]
          have hfirst : ∑ i : Fin k, c i • a.1 i.castSucc = a.1 (Fin.last k) := hc
          rw [hfirst]; ext j; exact zmod2_add_self _
        have hlast := Fintype.linearIndependent_iff.mp a.2 _ hsum (Fin.last k)
        simp at hlast
      · have h1 : Fin.init a₁.1 = Fin.init a₂.1 := congrArg (fun x ↦ x.1.1) h
        have h2 : a₁.1 (Fin.last k) = a₂.1 (Fin.last k) := by
          have := (Sigma.mk.inj_iff.mp h).2; simpa using this
        apply Subtype.ext; ext i j
        refine Fin.lastCases (by rw [h2]) (fun l ↦ by
          have := congrFun (congrFun h1 l) j; simpa [Fin.init] using this) i
      · have hv_nmem : v ∉ Submodule.span (ZMod 2) (Set.range a'.1) :=
          (Finset.mem_filter.mp (Finset.mem_sigma.mp hp).2).2
        refine ⟨⟨Fin.snoc (α := fun _ ↦ Fin n → ZMod 2) a'.1 v, ?_⟩, Finset.mem_univ _, ?_⟩
        · rw [Fintype.linearIndependent_iff]
          intro g hg
          rw [Fin.sum_univ_castSucc] at hg
          simp only [Fin.snoc_castSucc, Fin.snoc_last] at hg
          have hglast : g (Fin.last k) = 0 := by
            rcases zmod2_eq_zero_or_one (g (Fin.last k)) with h0 | h1
            · exact h0
            · exfalso
              rw [h1, one_smul] at hg
              have hv_eq : v = ∑ i : Fin k, g i.castSucc • a'.1 i := by
                ext j
                have hj := congrFun hg j
                simp only [Pi.add_apply, Pi.zero_apply] at hj
                have := congrArg (· + v j) hj
                simpa [add_assoc, zmod2_add_self] using this.symm
              apply hv_nmem; rw [hv_eq]
              exact Submodule.sum_mem _ fun i _ ↦
                Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
          rw [hglast, zero_smul, add_zero] at hg
          intro i
          refine Fin.lastCases hglast
            (fun l ↦ Fintype.linearIndependent_iff.mp a'.2 (fun m ↦ g m.castSucc) hg l) i
        · refine Sigma.ext (Subtype.ext ?_) (heq_of_eq (by simp))
          ext l j; simp [Fin.init]
    rw [hbij]
    have hconst (a' : { a' : Fin k → Fin n → ZMod 2 // LinearIndependent (ZMod 2) a' }) :
        (Finset.univ.filter fun v : Fin n → ZMod 2 ↦
          v ∉ Submodule.span (ZMod 2) (Set.range a'.1)).card = 2 ^ n - 2 ^ k := by
      set S := Submodule.span (ZMod 2) (Set.range a'.1)
      have hrank : Module.finrank (ZMod 2) S = k := by
        rw [finrank_span_eq_card a'.2, Fintype.card_fin]
      have hScard : Fintype.card S = 2 ^ k := by
        rw [Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card, hrank]
      have hadd := Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset (Fin n → ZMod 2))) (p := fun v ↦ v ∈ S)
      have hin : (Finset.univ.filter fun v : Fin n → ZMod 2 ↦ v ∈ S).card = 2 ^ k := by
        rw [← hScard, ← Fintype.card_coe]
        exact Fintype.card_congr
          { toFun := fun x ↦ ⟨x.1, (Finset.mem_filter.mp x.2).2⟩
            invFun := fun x ↦ ⟨x.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, x.2⟩⟩
            left_inv := fun _ ↦ rfl
            right_inv := fun _ ↦ rfl }
      have htot : (Finset.univ : Finset (Fin n → ZMod 2)).card = 2 ^ n := by
        simp [ZMod.card]
      omega
    simp_rw [hconst, Finset.sum_const, Finset.card_univ, smul_eq_mul]

/-- Distribution of $M M^\top$ when $M \in \mathbb{F}_2^{k \times n}$ is uniformly random among
all matrices of full row rank $k$ (for $k \le n$). -/
noncomputable def gramPMF (n k : ℕ) (hkn : k ≤ n) : PMF (SymMat k) := by
  classical
  have : Nonempty { a : Fin k → Fin n → ZMod 2 // LinearIndependent (ZMod 2) a } := by
    refine Fintype.card_pos_iff.mp ?_
    rw [card_indepTuples n k hkn]
    refine Finset.prod_pos fun i hi ↦ ?_
    have hin : i < n := lt_of_lt_of_le (Finset.mem_range.mp hi) hkn
    exact Nat.sub_pos_of_lt (Nat.pow_lt_pow_right (by norm_num) hin)
  exact (Cslib.Probability.PMF.uniformOfFintype
    { a : Fin k → Fin n → ZMod 2 // LinearIndependent (ZMod 2) a }).map fun a ↦ gramMat a.1

private def IsGoodTuple {n k : ℕ} (a : Fin k → Fin n → ZMod 2) : Prop :=
  LinearIndependent (ZMod 2) (Fin.cons (α := fun _ ↦ Fin n → ZMod 2) (fun _ ↦ (1 : ZMod 2)) a)

private lemma isGoodTuple_imp_linearIndependent {n k : ℕ} {a : Fin k → Fin n → ZMod 2}
    (ha : IsGoodTuple a) : LinearIndependent (ZMod 2) a :=
  ha.comp Fin.succ (Fin.succ_injective k)

open Classical in
private lemma card_goodTuples (n : ℕ) : ∀ k : ℕ, k + 1 ≤ n →
    Fintype.card { a : Fin k → Fin n → ZMod 2 // IsGoodTuple a } =
      ∏ i ∈ Finset.range k, (2 ^ n - 2 ^ (i + 1)) := by
  intro k
  induction k with
  | zero =>
    intro hk
    have h1ne : (fun _ : Fin n ↦ (1 : ZMod 2)) ≠ 0 := by
      intro h
      have := congrFun h ⟨0, by omega⟩
      exact one_ne_zero this
    have hgood : ∀ a : Fin 0 → Fin n → ZMod 2, IsGoodTuple a := by
      intro a
      rw [IsGoodTuple, Fintype.linearIndependent_iff]
      intro g hg i
      have hi0 : i = 0 := Fin.eq_zero i
      subst hi0
      rw [Fin.sum_univ_one, Fin.cons_zero] at hg
      rcases zmod2_eq_zero_or_one (g 0) with h0 | h1
      · exact h0
      · rw [h1, one_smul] at hg; exact absurd hg h1ne
    rw [Finset.range_zero, Finset.prod_empty, Fintype.card_congr (Equiv.subtypeUnivEquiv hgood)]
    simp
  | succ k ih =>
    intro hk
    rw [Finset.prod_range_succ, ← ih (by omega)]
    have hbij :
        Fintype.card { a : Fin (k + 1) → Fin n → ZMod 2 // IsGoodTuple a } =
          ∑ a' : { a' : Fin k → Fin n → ZMod 2 // IsGoodTuple a' },
            (Finset.univ.filter fun v : Fin n → ZMod 2 ↦
              v ∉ Submodule.span (ZMod 2)
                (Set.range (Fin.cons (α := fun _ ↦ Fin n → ZMod 2)
                  (fun _ ↦ (1 : ZMod 2)) a'.1))).card := by
      rw [← Finset.card_sigma, ← Finset.card_univ]
      refine Finset.card_bij (fun a _ ↦
          ⟨⟨Fin.init a.1, by
              have hcomp := a.2.comp (Fin.castSucc : Fin (k + 1) → Fin (k + 2))
                (Fin.castSucc_injective _)
              have heq : (Fin.cons (α := fun _ ↦ Fin n → ZMod 2) (fun _ ↦ (1 : ZMod 2)) a.1 ∘
                  Fin.castSucc) =
                  Fin.cons (α := fun _ ↦ Fin n → ZMod 2) (fun _ ↦ (1 : ZMod 2)) (Fin.init a.1) := by
                ext i j
                refine Fin.cases (by simp) (fun l ↦ by simp [Fin.init]) i
              rwa [heq] at hcomp⟩, a.1 (Fin.last k)⟩)
        (fun a _ ↦ ?_)
        (fun a₁ _ a₂ _ h ↦ ?_)
        (fun ⟨a', v⟩ hp ↦ ?_)
      · refine Finset.mem_sigma.mpr ⟨Finset.mem_univ _, Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, fun hmem ↦ ?_⟩⟩
        rw [Submodule.mem_span_range_iff_exists_fun] at hmem
        obtain ⟨c, hc⟩ := hmem
        have hsum : ∑ i : Fin (k + 2),
            Fin.snoc (α := fun _ ↦ ZMod 2) c (1 : ZMod 2) i •
              Fin.cons (α := fun _ ↦ Fin n → ZMod 2) (fun _ ↦ (1 : ZMod 2)) a.1 i = 0 := by
          rw [Fin.sum_univ_castSucc]
          simp only [Fin.snoc_castSucc, Fin.snoc_last, one_smul]
          have hcons_last : Fin.cons (α := fun _ ↦ Fin n → ZMod 2) (fun _ ↦ (1 : ZMod 2)) a.1
              (Fin.last (k + 1)) = a.1 (Fin.last k) := by
            change Fin.cons (α := fun _ ↦ Fin n → ZMod 2) _ a.1 (Fin.succ (Fin.last k)) =
              a.1 (Fin.last k)
            simp
          rw [hcons_last]
          have hfirst : ∑ i : Fin (k + 1), c i •
              Fin.cons (α := fun _ ↦ Fin n → ZMod 2) (fun _ ↦ (1 : ZMod 2)) a.1 i.castSucc =
              a.1 (Fin.last k) := by
            convert hc using 1
            refine Finset.sum_congr rfl fun i _ ↦ ?_
            refine Fin.cases (by simp) (fun l ↦ by simp [Fin.init]) i
          rw [hfirst]; ext j; exact zmod2_add_self _
        have hlast := Fintype.linearIndependent_iff.mp a.2 _ hsum (Fin.last (k + 1))
        simp at hlast
      · have h1 : Fin.init a₁.1 = Fin.init a₂.1 := congrArg (fun x ↦ x.1.1) h
        have h2 : a₁.1 (Fin.last k) = a₂.1 (Fin.last k) := by
          have := (Sigma.mk.inj_iff.mp h).2; simpa using this
        apply Subtype.ext; ext i j
        refine Fin.lastCases (by rw [h2]) (fun l ↦ by
          have := congrFun (congrFun h1 l) j; simpa [Fin.init] using this) i
      · have hv_nmem : v ∉ Submodule.span (ZMod 2)
            (Set.range (Fin.cons (α := fun _ ↦ Fin n → ZMod 2) (fun _ ↦ (1 : ZMod 2)) a'.1)) :=
          (Finset.mem_filter.mp (Finset.mem_sigma.mp hp).2).2
        refine ⟨⟨Fin.snoc (α := fun _ ↦ Fin n → ZMod 2) a'.1 v, ?_⟩, Finset.mem_univ _, ?_⟩
        · rw [IsGoodTuple, Fintype.linearIndependent_iff]
          intro g hg
          rw [fin_cons_snoc, Fin.sum_univ_castSucc] at hg
          simp only [Fin.snoc_castSucc, Fin.snoc_last] at hg
          have hglast : g (Fin.last (k + 1)) = 0 := by
            rcases zmod2_eq_zero_or_one (g (Fin.last (k + 1))) with h0 | h1
            · exact h0
            · exfalso
              rw [h1, one_smul] at hg
              have hv_eq : v = ∑ i : Fin (k + 1), g i.castSucc •
                  Fin.cons (α := fun _ ↦ Fin n → ZMod 2) (fun _ ↦ (1 : ZMod 2)) a'.1 i := by
                ext j
                have hj := congrFun hg j
                simp only [Pi.add_apply, Pi.zero_apply] at hj
                have := congrArg (· + v j) hj
                simpa [add_assoc, zmod2_add_self] using this.symm
              apply hv_nmem; rw [hv_eq]
              exact Submodule.sum_mem _ fun i _ ↦
                Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
          rw [hglast, zero_smul, add_zero] at hg
          intro i
          refine Fin.lastCases hglast
            (fun l ↦ Fintype.linearIndependent_iff.mp a'.2 (fun m ↦ g m.castSucc) hg l) i
        · refine Sigma.ext (Subtype.ext ?_) (heq_of_eq (by simp))
          ext l j; simp [Fin.init]
    rw [hbij]
    have hconst (a' : { a' : Fin k → Fin n → ZMod 2 // IsGoodTuple a' }) :
        (Finset.univ.filter fun v : Fin n → ZMod 2 ↦
          v ∉ Submodule.span (ZMod 2)
            (Set.range (Fin.cons (α := fun _ ↦ Fin n → ZMod 2)
              (fun _ ↦ (1 : ZMod 2)) a'.1))).card = 2 ^ n - 2 ^ (k + 1) := by
      set S := Submodule.span (ZMod 2)
        (Set.range (Fin.cons (α := fun _ ↦ Fin n → ZMod 2) (fun _ ↦ (1 : ZMod 2)) a'.1))
      have hrank : Module.finrank (ZMod 2) S = k + 1 := by
        rw [finrank_span_eq_card a'.2, Fintype.card_fin]
      have hScard : Fintype.card S = 2 ^ (k + 1) := by
        rw [Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card, hrank]
      have hadd := Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset (Fin n → ZMod 2))) (p := fun v ↦ v ∈ S)
      have hin : (Finset.univ.filter fun v : Fin n → ZMod 2 ↦ v ∈ S).card = 2 ^ (k + 1) := by
        rw [← hScard, ← Fintype.card_coe]
        exact Fintype.card_congr
          { toFun := fun x ↦ ⟨x.1, (Finset.mem_filter.mp x.2).2⟩
            invFun := fun x ↦ ⟨x.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, x.2⟩⟩
            left_inv := fun _ ↦ rfl
            right_inv := fun _ ↦ rfl }
      have htot : (Finset.univ : Finset (Fin n → ZMod 2)).card = 2 ^ n := by
        simp [ZMod.card]
      omega
    simp_rw [hconst, Finset.sum_const, Finset.card_univ, smul_eq_mul]

open Classical in
private lemma card_goodTuples_pos (n k : ℕ) (hk : k + 1 ≤ n) :
    0 < Fintype.card { a : Fin k → Fin n → ZMod 2 // IsGoodTuple a } := by
  rw [card_goodTuples n k hk]
  refine Finset.prod_pos fun i hi ↦ ?_
  have hi1 : i + 1 < n := by have := Finset.mem_range.mp hi; omega
  exact Nat.sub_pos_of_lt (Nat.pow_lt_pow_right (by norm_num) hi1)

private noncomputable def uniformGoodTuples (n k : ℕ) (hk : k + 1 ≤ n) :
    PMF { a : Fin k → Fin n → ZMod 2 // IsGoodTuple a } := by
  classical
  have : Nonempty { a : Fin k → Fin n → ZMod 2 // IsGoodTuple a } :=
    Fintype.card_pos_iff.mp (card_goodTuples_pos n k hk)
  exact Cslib.Probability.PMF.uniformOfFintype _

private noncomputable def goodGramPMF (n k : ℕ) (hk : k + 1 ≤ n) : PMF (SymMat k) :=
  (uniformGoodTuples n k hk).map fun a ↦ gramMat a.1

/-! ### Total variation distance between `gramPMF` and `uniformSymMat` -/

private lemma dist_uniformSymMat_prod (k : ℕ) :
    (uniformSymMat (k + 1)).map (symMatSplitEquiv k) =
      (uniformSymMat k).bind fun B ↦
        (Cslib.Probability.PMF.uniformOfFintype ((Fin k → ZMod 2) × ZMod 2)).map (B, ·) := by
  have : Nonempty (SymMat (k + 1)) := ⟨⟨0, Matrix.transpose_zero⟩⟩
  have : Nonempty (SymMat k) := ⟨⟨0, Matrix.transpose_zero⟩⟩
  rw [uniformSymMat, Cslib.Probability.PMF.uniformOfFintype_map_equiv (symMatSplitEquiv k),
    uniformSymMat, Cslib.Probability.PMF.uniformOfFintype_prod]

private lemma dist_bind_prod_left {α β : Type*} [Fintype α] [Fintype β]
    (p₁ p₂ : PMF α) (q : PMF β) :
    dist (p₁.bind fun a ↦ q.map (a, ·)) (p₂.bind fun a ↦ q.map (a, ·)) = dist p₁ p₂ := by
  simp only [Cslib.Probability.PMF.dist_eq, Fintype.sum_prod_type]
  have happ (p : PMF α) (a : α) (b : β) :
      ((p.bind fun a' ↦ q.map (a', ·)) (a, b)).toReal = (p a).toReal * (q b).toReal := by
    rw [PMF.bind_apply, tsum_eq_single a]
    · rw [PMF.map_apply, tsum_eq_single b]
      · simp [ENNReal.toReal_mul]
      · intro b' hb'
        exact ite_eq_right fun h ↦ hb' (Prod.mk.inj h).2.symm
    · intro a' ha'
      have h0 : (q.map (a', ·)) (a, b) = 0 := by
        rw [PMF.map_apply, tsum_fintype]
        refine Finset.sum_eq_zero fun b' _ ↦ ?_
        have hne : (a, b) ≠ (a', b') := fun h ↦ ha' (Prod.mk.inj h).1.symm
        simp [hne]
      rw [h0, mul_zero]
  simp_rw [happ, ← sub_mul, abs_mul, abs_of_nonneg ENNReal.toReal_nonneg, ← Finset.mul_sum,
    Cslib.Probability.PMF.sum_toReal, mul_one]

private lemma map_surjective_linear_uniform {n k : ℕ} (a : Fin k → Fin n → ZMod 2)
    (ha : IsGoodTuple a) :
    let linOut : (Fin n → ZMod 2) →+ ((Fin k → ZMod 2) × ZMod 2) :=
      { toFun := fun v ↦ (fun j ↦ ∑ l : Fin n, v l * a j l, ∑ l : Fin n, v l)
        map_zero' := Prod.ext (funext fun _ ↦ by simp) (by simp)
        map_add' := fun v w ↦ Prod.ext
          (funext fun j ↦ by simp [add_mul, Finset.sum_add_distrib])
          (by simp [Finset.sum_add_distrib]) }
    (Cslib.Probability.PMF.uniformOfFintype (Fin n → ZMod 2)).map linOut =
      Cslib.Probability.PMF.uniformOfFintype ((Fin k → ZMod 2) × ZMod 2) := by
  intro linOut
  refine Cslib.Probability.PMF.uniformOfFintype_map_addHom linOut ?_
  let M : Matrix (Fin (k + 1)) (Fin n) (ZMod 2) :=
    Matrix.of (Fin.cons (α := fun _ ↦ Fin n → ZMod 2) (fun _ ↦ (1 : ZMod 2)) a)
  have hM_mulVec_surj : Function.Surjective M.mulVecLin := by
    have hinj : Function.Injective M.vecMulLinear := by
      rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
      intro w hw
      rw [LinearMap.mem_ker] at hw
      have hsum : ∑ i : Fin (k + 1),
          w i • Fin.cons (α := fun _ ↦ Fin n → ZMod 2) (fun _ ↦ (1 : ZMod 2)) a i = 0 := by
        ext j
        have hj := congrFun hw j
        simpa [Matrix.vecMulLinear_apply, Matrix.vecMul, dotProduct, M] using hj
      ext i
      exact Fintype.linearIndependent_iff.mp ha w hsum i
    have hrankT : Mᵀ.rank = k + 1 := by
      rw [Matrix.rank]
      have htr : Mᵀ.mulVecLin = M.vecMulLinear := by
        ext w j
        simp [Matrix.vecMul, dotProduct]
      rw [htr, LinearMap.finrank_range_of_inj hinj, Module.finrank_fin_fun]
    have hrank : M.rank = k + 1 := by rw [← Matrix.rank_transpose, hrankT]
    rw [← LinearMap.range_eq_top]
    apply Submodule.eq_top_of_finrank_eq
    rw [Module.finrank_fin_fun]
    exact hrank
  intro ⟨b, c⟩
  obtain ⟨v, hv⟩ := hM_mulVec_surj (Fin.cons (α := fun _ ↦ ZMod 2) c b)
  refine ⟨v, Prod.ext (funext fun j ↦ ?_) ?_⟩
  · have hj := congrFun hv j.succ
    simpa [M, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, mul_comm, linOut] using hj
  · have h0 := congrFun hv 0
    simpa [M, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, linOut] using h0

private lemma dist_goodGramPMF_uniformSymMat_le (n k : ℕ) (hk : k + 1 ≤ n) :
    dist (goodGramPMF n k hk) (uniformSymMat k) ≤
      ∑ i ∈ Finset.range k, (2 : ℝ) ^ ((i + 1 : ℤ) - n) := by
  induction k with
  | zero =>
    let A₀ : SymMat 0 := ⟨0, Matrix.transpose_zero⟩
    have hsub : ∀ A : SymMat 0, A = A₀ := fun A ↦
      Subtype.ext (Matrix.ext fun i _ ↦ Fin.elim0 i)
    have heq : goodGramPMF n 0 hk = uniformSymMat 0 :=
      PMF.ext fun A ↦ by
        have h1 := (goodGramPMF n 0 hk).tsum_coe
        have h2 := (uniformSymMat 0).tsum_coe
        rw [tsum_fintype, Finset.sum_eq_single A₀ (fun B _ hne ↦ absurd (hsub B) hne)
          (fun h ↦ absurd (Finset.mem_univ _) h)] at h1 h2
        rw [hsub A, h1, h2]
    rw [heq, dist_self]
    simp
  | succ k ih =>
    classical
    have hk' : k + 1 ≤ n := by omega
    have hisom : dist (goodGramPMF n (k + 1) hk) (uniformSymMat (k + 1)) =
        dist ((goodGramPMF n (k + 1) hk).map (symMatSplitEquiv k))
          ((uniformSymMat (k + 1)).map (symMatSplitEquiv k)) := by
      refine le_antisymm ?_ (Cslib.Probability.PMF.dist_map_le _ _ _)
      have hinv := Cslib.Probability.PMF.dist_map_le
        ((goodGramPMF n (k + 1) hk).map (symMatSplitEquiv k))
        ((uniformSymMat (k + 1)).map (symMatSplitEquiv k)) (symMatSplitEquiv k).symm
      have hcomp : (symMatSplitEquiv k).symm ∘ (symMatSplitEquiv k) = id :=
        funext (symMatSplitEquiv k).left_inv
      rw [PMF.map_comp, PMF.map_comp, hcomp, PMF.map_id, PMF.map_id] at hinv
      exact hinv
    rw [hisom, dist_uniformSymMat_prod]
    let unifBits : PMF ((Fin k → ZMod 2) × ZMod 2) :=
      Cslib.Probability.PMF.uniformOfFintype ((Fin k → ZMod 2) × ZMod 2)
    let linOut (a : { a : Fin k → Fin n → ZMod 2 // IsGoodTuple a }) :
        (Fin n → ZMod 2) → ((Fin k → ZMod 2) × ZMod 2) :=
      fun v ↦ (fun j ↦ ∑ l : Fin n, v l * a.1 j l, ∑ l : Fin n, v l)
    let S (a : { a : Fin k → Fin n → ZMod 2 // IsGoodTuple a }) : Set (Fin n → ZMod 2) :=
      { v | v ∉ Submodule.span (ZMod 2)
          (Set.range (Fin.cons (α := fun _ ↦ Fin n → ZMod 2) (fun _ ↦ (1 : ZMod 2)) a.1)) }
    have hS_card (a : { a : Fin k → Fin n → ZMod 2 // IsGoodTuple a }) :
        (Finset.univ.filter fun v : Fin n → ZMod 2 ↦ v ∈ S a).card = 2 ^ n - 2 ^ (k + 1) := by
      set W := Submodule.span (ZMod 2)
        (Set.range (Fin.cons (α := fun _ ↦ Fin n → ZMod 2) (fun _ ↦ (1 : ZMod 2)) a.1))
      have hrank : Module.finrank (ZMod 2) W = k + 1 := by
        rw [finrank_span_eq_card a.2, Fintype.card_fin]
      have hWcard : Fintype.card W = 2 ^ (k + 1) := by
        rw [Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card, hrank]
      have hadd := Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset (Fin n → ZMod 2))) (p := fun v ↦ v ∈ W)
      have hin : (Finset.univ.filter fun v : Fin n → ZMod 2 ↦ v ∈ W).card = 2 ^ (k + 1) := by
        rw [← hWcard, ← Fintype.card_coe]
        exact Fintype.card_congr
          { toFun := fun x ↦ ⟨x.1, (Finset.mem_filter.mp x.2).2⟩
            invFun := fun x ↦ ⟨x.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, x.2⟩⟩
            left_inv := fun _ ↦ rfl
            right_inv := fun _ ↦ rfl }
      have htot : (Finset.univ : Finset (Fin n → ZMod 2)).card = 2 ^ n := by
        simp [ZMod.card]
      change (Finset.univ.filter fun v : Fin n → ZMod 2 ↦ v ∉ W).card = _
      omega
    have hS_ex (a : { a : Fin k → Fin n → ZMod 2 // IsGoodTuple a }) :
        ∃ v ∈ S a, v ∈ (Cslib.Probability.PMF.uniformOfFintype (Fin n → ZMod 2)).support := by
      have hpos : 0 < 2 ^ n - 2 ^ (k + 1) :=
        Nat.sub_pos_of_lt (Nat.pow_lt_pow_right (by norm_num) (by omega))
      obtain ⟨v, hv⟩ := Finset.card_pos.mp ((hS_card a).symm ▸ hpos)
      exact ⟨v, (Finset.mem_filter.mp hv).2, by
        simp [PMF.mem_support_iff, Cslib.Probability.PMF.uniformOfFintype_apply]⟩
    have hdecomp :
        (goodGramPMF n (k + 1) hk).map (symMatSplitEquiv k) =
          (uniformGoodTuples n k hk').bind fun a ↦
            (((Cslib.Probability.PMF.uniformOfFintype (Fin n → ZMod 2)).filter
              (S a) (hS_ex a)).map (linOut a)).map (gramMat a.1, ·) := by
      have : Nonempty { b : Fin (k + 1) → Fin n → ZMod 2 // IsGoodTuple b } :=
        Fintype.card_pos_iff.mp (card_goodTuples_pos n (k + 1) hk)
      have hsnoc_good (a : { a : Fin k → Fin n → ZMod 2 // IsGoodTuple a })
          (v : Fin n → ZMod 2) (hv : v ∈ S a) :
          IsGoodTuple (Fin.snoc (α := fun _ ↦ Fin n → ZMod 2) a.1 v) := by
        rw [IsGoodTuple, Fintype.linearIndependent_iff]
        intro g hg
        rw [fin_cons_snoc, Fin.sum_univ_castSucc] at hg
        simp only [Fin.snoc_castSucc, Fin.snoc_last] at hg
        have hglast : g (Fin.last (k + 1)) = 0 := by
          rcases zmod2_eq_zero_or_one (g (Fin.last (k + 1))) with h0 | h1
          · exact h0
          · exfalso
            rw [h1, one_smul] at hg
            have hv_eq : v = ∑ i : Fin (k + 1), g i.castSucc •
                Fin.cons (α := fun _ ↦ Fin n → ZMod 2) (fun _ ↦ (1 : ZMod 2)) a.1 i := by
              ext j
              have hj := congrFun hg j
              simp only [Pi.add_apply, Pi.zero_apply] at hj
              have := congrArg (· + v j) hj
              simpa [add_assoc, zmod2_add_self] using this.symm
            apply hv; rw [hv_eq]
            exact Submodule.sum_mem _ fun i _ ↦
              Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
        rw [hglast, zero_smul, add_zero] at hg
        intro i
        refine Fin.lastCases hglast
          (fun l ↦ Fintype.linearIndependent_iff.mp a.2 (fun m ↦ g m.castSucc) hg l) i
      let arbGood : { b : Fin (k + 1) → Fin n → ZMod 2 // IsGoodTuple b } :=
        Classical.arbitrary _
      have hgood_bind :
          uniformGoodTuples n (k + 1) hk =
            (uniformGoodTuples n k hk').bind fun a ↦
              ((Cslib.Probability.PMF.uniformOfFintype (Fin n → ZMod 2)).filter
                (S a) (hS_ex a)).bind fun v ↦
                if hv : v ∈ S a then
                  PMF.pure ⟨Fin.snoc (α := fun _ ↦ Fin n → ZMod 2) a.1 v, hsnoc_good a v hv⟩
                else PMF.pure arbGood := by
        ext ⟨b, hb⟩
        have hb_init : IsGoodTuple (Fin.init b) := by
          have hcomp := hb.comp (Fin.castSucc : Fin (k + 1) → Fin (k + 2))
            (Fin.castSucc_injective _)
          have heq : (Fin.cons (α := fun _ ↦ Fin n → ZMod 2) (fun _ ↦ (1 : ZMod 2)) b ∘
              Fin.castSucc) =
              Fin.cons (α := fun _ ↦ Fin n → ZMod 2) (fun _ ↦ (1 : ZMod 2)) (Fin.init b) := by
            ext i j; refine Fin.cases (by simp) (fun l ↦ by simp [Fin.init]) i
          rwa [heq] at hcomp
        let a₀ : { a : Fin k → Fin n → ZMod 2 // IsGoodTuple a } := ⟨Fin.init b, hb_init⟩
        have hv₀ : b (Fin.last k) ∈ S a₀ := by
          intro hmem
          rw [Submodule.mem_span_range_iff_exists_fun] at hmem
          obtain ⟨c, hc⟩ := hmem
          have hsum : ∑ i : Fin (k + 2),
              Fin.snoc (α := fun _ ↦ ZMod 2) c (1 : ZMod 2) i •
                Fin.cons (α := fun _ ↦ Fin n → ZMod 2) (fun _ ↦ (1 : ZMod 2)) b i = 0 := by
            rw [Fin.sum_univ_castSucc]
            simp only [Fin.snoc_castSucc, Fin.snoc_last, one_smul]
            have hcons_last : Fin.cons (α := fun _ ↦ Fin n → ZMod 2) (fun _ ↦ (1 : ZMod 2)) b
                (Fin.last (k + 1)) = b (Fin.last k) := by
              change Fin.cons (α := fun _ ↦ Fin n → ZMod 2) _ b (Fin.succ (Fin.last k)) =
                b (Fin.last k); simp
            rw [hcons_last]
            have hfirst : ∑ i : Fin (k + 1), c i •
                Fin.cons (α := fun _ ↦ Fin n → ZMod 2) (fun _ ↦ (1 : ZMod 2)) b i.castSucc =
                b (Fin.last k) := by
              convert hc using 1
              refine Finset.sum_congr rfl fun i _ ↦ ?_
              refine Fin.cases (by simp) (fun l ↦ by simp [a₀, Fin.init]) i
            rw [hfirst]; ext j; exact zmod2_add_self _
          have hlast := Fintype.linearIndependent_iff.mp hb _ hsum (Fin.last (k + 1))
          simp at hlast
        have hsnoc_eq : Fin.snoc (α := fun _ ↦ Fin n → ZMod 2) a₀.1 (b (Fin.last k)) = b := by
          ext i j
          refine Fin.lastCases (by simp) (fun l ↦ by simp [a₀, Fin.init]) i
        rw [PMF.bind_apply, tsum_eq_single a₀]
        · rw [PMF.bind_apply, tsum_eq_single (b (Fin.last k))]
          · rw [dite_eq_left hv₀, PMF.pure_apply, ite_eq_left (Subtype.ext hsnoc_eq.symm), mul_one]
            simp only [uniformGoodTuples, Cslib.Probability.PMF.uniformOfFintype_apply]
            have hprod_pos : 0 < ∏ i ∈ Finset.range k, (2 ^ n - 2 ^ (i + 1)) := by
              rw [← card_goodTuples n k hk']; exact card_goodTuples_pos n k hk'
            have hprod_ne0 : ((∏ i ∈ Finset.range k, (2 ^ n - 2 ^ (i + 1)) : ℕ) : ENNReal) ≠ 0 :=
              Nat.cast_ne_zero.mpr hprod_pos.ne'
            rw [card_goodTuples n k hk', card_goodTuples n (k + 1) hk, Finset.prod_range_succ,
              Nat.cast_mul, ENNReal.mul_inv (Or.inl hprod_ne0) (Or.inl (ENNReal.natCast_ne_top _))]
            congr 1
            rw [PMF.filter_apply, Set.indicator_of_mem hv₀, ← PMF.toOuterMeasure_apply]
            have hmeas :
                (Cslib.Probability.PMF.uniformOfFintype (Fin n → ZMod 2)).toOuterMeasure (S a₀) =
                  ((2 ^ n - 2 ^ (k + 1) : ℕ) : ENNReal) / ((2 ^ n : ℕ) : ENNReal) := by
              rw [PMF.toOuterMeasure_apply, tsum_fintype]
              simp only [Set.indicator_apply, Cslib.Probability.PMF.uniformOfFintype_apply,
                Fintype.card_fun, ZMod.card, Fintype.card_fin, Finset.sum_ite,
                Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]
              congr 1
              exact_mod_cast hS_card a₀
            rw [hmeas, Cslib.Probability.PMF.uniformOfFintype_apply]
            have hcard_fn : Fintype.card (Fin n → ZMod 2) = 2 ^ n := by simp [ZMod.card]
            have hpos_sub : 0 < 2 ^ n - 2 ^ (k + 1) :=
              Nat.sub_pos_of_lt (Nat.pow_lt_pow_right (by norm_num) (by omega))
            have h2n_ne0 : ((2 ^ n : ℕ) : ENNReal) ≠ 0 := Nat.cast_ne_zero.mpr (by positivity)
            rw [hcard_fn, div_eq_mul_inv,
              ENNReal.mul_inv (Or.inl (by exact_mod_cast hpos_sub.ne')) (Or.inl (by simp)),
              inv_inv, mul_comm (((2 ^ n - 2 ^ (k + 1) : ℕ) : ENNReal)⁻¹), ← mul_assoc,
              ENNReal.inv_mul_cancel h2n_ne0 (ENNReal.natCast_ne_top _), one_mul]
          · intro v hv
            by_cases hvS : v ∈ S a₀
            · rw [dite_eq_left hvS, PMF.pure_apply, ite_eq_right, mul_zero]
              intro heq
              have := congrFun (congrArg Subtype.val heq) (Fin.last k)
              simp at this
              exact hv this.symm
            · rw [PMF.filter_apply, Set.indicator_of_notMem hvS, zero_mul, zero_mul]
        · intro a ha
          have h0 :
              (((Cslib.Probability.PMF.uniformOfFintype (Fin n → ZMod 2)).filter
                (S a) (hS_ex a)).bind fun v ↦
                  if hv : v ∈ S a then
                    PMF.pure ⟨Fin.snoc (α := fun _ ↦ Fin n → ZMod 2) a.1 v, hsnoc_good a v hv⟩
                  else PMF.pure arbGood) ⟨b, hb⟩ = 0 := by
            rw [PMF.bind_apply, tsum_fintype]
            refine Finset.sum_eq_zero fun v _ ↦ ?_
            by_cases hvS : v ∈ S a
            · rw [dite_eq_left hvS, PMF.pure_apply, ite_eq_right, mul_zero]
              intro heq
              apply ha
              apply Subtype.ext
              ext l j
              have := congrFun (congrFun (congrArg Subtype.val heq) l.castSucc) j
              simpa [a₀, Fin.init] using this.symm
            · rw [PMF.filter_apply, Set.indicator_of_notMem hvS, zero_mul, zero_mul]
          rw [h0, mul_zero]
      rw [goodGramPMF, PMF.map_comp, hgood_bind, PMF.map_bind]
      refine congrArg ((uniformGoodTuples n k hk').bind ·) (funext fun a ↦ ?_)
      rw [PMF.map_bind, PMF.map_comp, ← PMF.bind_pure_comp]
      refine PMF.ext fun y ↦ ?_
      rw [PMF.bind_apply, PMF.bind_apply]
      refine tsum_congr fun v ↦ ?_
      by_cases hvS : v ∈ S a
      · rw [dite_eq_left hvS, PMF.pure_map]
        have hpair : symMatSplitEquiv k
            (gramMat (Fin.snoc (α := fun _ ↦ Fin n → ZMod 2) a.1 v)) =
            (gramMat a.1, linOut a v) := by
          refine Prod.ext (Subtype.ext ?_) (Prod.ext ?_ ?_)
          · ext i j
            simp [symMatSplitEquiv, gramMat, Matrix.mul_apply, Function.swap]
          · ext j
            simp [symMatSplitEquiv, gramMat, linOut, Matrix.mul_apply, Function.swap]
          · simp only [symMatSplitEquiv, gramMat, linOut, Matrix.mul_apply, Matrix.transpose_apply,
              Matrix.of_apply, Fin.snoc_last, Equiv.coe_fn_mk]
            refine Finset.sum_congr rfl fun l _ ↦ zmod2_sq (v l)
        simp only [Function.comp_apply]
        rw [hpair]
      · rw [PMF.filter_apply, Set.indicator_of_notMem hvS, zero_mul, zero_mul, zero_mul]
    rw [hdecomp]
    let mid : PMF (SymMat k × ((Fin k → ZMod 2) × ZMod 2)) :=
      (uniformGoodTuples n k hk').bind fun a ↦ unifBits.map (gramMat a.1, ·)
    have hmid_eq : mid = (goodGramPMF n k hk').bind fun B ↦ unifBits.map (B, ·) := by
      dsimp only [mid, goodGramPMF]
      rw [PMF.bind_map]
      rfl
    have h1 :
        dist ((uniformGoodTuples n k hk').bind fun a ↦
            (((Cslib.Probability.PMF.uniformOfFintype (Fin n → ZMod 2)).filter
              (S a) (hS_ex a)).map (linOut a)).map (gramMat a.1, ·)) mid ≤
          (2 : ℝ) ^ ((k + 1 : ℤ) - n) := by
      let P₁ := (uniformGoodTuples n k hk').bind fun a ↦
        ((((Cslib.Probability.PMF.uniformOfFintype (Fin n → ZMod 2)).filter
          (S a) (hS_ex a)).map (linOut a)).map (gramMat a.1, ·)).map (a, ·)
      let P₂ := (uniformGoodTuples n k hk').bind fun a ↦
        (unifBits.map (gramMat a.1, ·)).map (a, ·)
      have hproj₁ : P₁.map Prod.snd =
          (uniformGoodTuples n k hk').bind fun a ↦
            (((Cslib.Probability.PMF.uniformOfFintype (Fin n → ZMod 2)).filter
              (S a) (hS_ex a)).map (linOut a)).map (gramMat a.1, ·) := by
        dsimp only [P₁]; rw [PMF.map_bind]
        refine congrArg _ (funext fun a ↦ (PMF.map_comp _ _ _).trans (PMF.map_id _))
      have hproj₂ : P₂.map Prod.snd = mid := by
        dsimp only [P₂, mid]; rw [PMF.map_bind]
        refine congrArg _ (funext fun a ↦ (PMF.map_comp _ _ _).trans (PMF.map_id _))
      calc dist _ mid = dist (P₁.map Prod.snd) (P₂.map Prod.snd) := by rw [hproj₁, hproj₂]
        _ ≤ dist P₁ P₂ := Cslib.Probability.PMF.dist_map_le P₁ P₂ Prod.snd
        _ = ∑ a, ((uniformGoodTuples n k hk') a).toReal *
              dist ((((Cslib.Probability.PMF.uniformOfFintype (Fin n → ZMod 2)).filter
                (S a) (hS_ex a)).map (linOut a)).map (gramMat a.1, ·))
                (unifBits.map (gramMat a.1, ·)) :=
            Cslib.Probability.PMF.dist_bind_pair _ _ _
        _ ≤ ∑ a, ((uniformGoodTuples n k hk') a).toReal * (2 : ℝ) ^ ((k + 1 : ℤ) - n) := by
            refine Finset.sum_le_sum fun a _ ↦ mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
            have hlin : (Cslib.Probability.PMF.uniformOfFintype (Fin n → ZMod 2)).map (linOut a) =
                unifBits := map_surjective_linear_uniform a.1 a.2
            calc dist _ (unifBits.map (gramMat a.1, ·))
                ≤ dist (((Cslib.Probability.PMF.uniformOfFintype (Fin n → ZMod 2)).filter
                    (S a) (hS_ex a)).map (linOut a)) unifBits :=
                  Cslib.Probability.PMF.dist_map_le _ _ _
              _ = dist (((Cslib.Probability.PMF.uniformOfFintype (Fin n → ZMod 2)).filter
                    (S a) (hS_ex a)).map (linOut a))
                    ((Cslib.Probability.PMF.uniformOfFintype (Fin n → ZMod 2)).map (linOut a)) := by
                  rw [hlin]
              _ ≤ dist ((Cslib.Probability.PMF.uniformOfFintype (Fin n → ZMod 2)).filter
                    (S a) (hS_ex a))
                    (Cslib.Probability.PMF.uniformOfFintype (Fin n → ZMod 2)) :=
                  Cslib.Probability.PMF.dist_map_le _ _ _
              _ = dist (Cslib.Probability.PMF.uniformOfFintype (Fin n → ZMod 2))
                    ((Cslib.Probability.PMF.uniformOfFintype (Fin n → ZMod 2)).filter
                      (S a) (hS_ex a)) := dist_comm _ _
              _ = ((Cslib.Probability.PMF.uniformOfFintype (Fin n → ZMod 2)).toOuterMeasure
                    (S a)ᶜ).toReal :=
                  Cslib.Probability.PMF.dist_filter _ _ _
              _ = (2 : ℝ) ^ ((k + 1 : ℤ) - n) := by
                  rw [Cslib.Probability.PMF.toOuterMeasure_apply_toReal]
                  set W := Submodule.span (ZMod 2)
                    (Set.range (Fin.cons (α := fun _ ↦ Fin n → ZMod 2)
                      (fun _ ↦ (1 : ZMod 2)) a.1))
                  have hcompl : (S a)ᶜ = (W : Set (Fin n → ZMod 2)) := by
                    ext v; simp [S, W]
                  rw [hcompl]
                  have hrank : Module.finrank (ZMod 2) W = k + 1 := by
                    rw [finrank_span_eq_card a.2, Fintype.card_fin]
                  have hWcard : Fintype.card W = 2 ^ (k + 1) := by
                    rw [Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card, hrank]
                  have hin : (Finset.univ.filter fun v : Fin n → ZMod 2 ↦ v ∈ (W : Set _)).card =
                      2 ^ (k + 1) := by
                    rw [← hWcard, ← Fintype.card_coe]
                    exact Fintype.card_congr
                      { toFun := fun x ↦ ⟨x.1, (Finset.mem_filter.mp x.2).2⟩
                        invFun := fun x ↦ ⟨x.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, x.2⟩⟩
                        left_inv := fun _ ↦ rfl
                        right_inv := fun _ ↦ rfl }
                  simp only [Cslib.Probability.PMF.uniformOfFintype_apply, Fintype.card_fun,
                    ZMod.card, Fintype.card_fin, ENNReal.toReal_inv, ENNReal.toReal_pow,
                    ENNReal.toReal_ofNat, Finset.sum_ite, Finset.sum_const_zero, add_zero,
                    Finset.sum_const, nsmul_eq_mul, hin, Nat.cast_pow, Nat.cast_ofNat]
                  rw [zpow_sub₀ (by norm_num),
                    show (k + 1 : ℤ) = ((k + 1 : ℕ) : ℤ) by push_cast; rfl,
                    zpow_natCast, zpow_natCast, div_eq_mul_inv]
        _ = (2 : ℝ) ^ ((k + 1 : ℤ) - n) := by
            rw [← Finset.sum_mul, Cslib.Probability.PMF.sum_toReal, one_mul]
    have h2 :
        dist mid ((uniformSymMat k).bind fun B ↦ unifBits.map (B, ·)) =
          dist (goodGramPMF n k hk') (uniformSymMat k) := by
      rw [hmid_eq]
      exact dist_bind_prod_left (goodGramPMF n k hk') (uniformSymMat k) unifBits
    rw [Finset.sum_range_succ]
    calc dist _ _ ≤ dist _ mid + dist mid _ := dist_triangle _ mid _
      _ ≤ (2 : ℝ) ^ ((k + 1 : ℤ) - n) + dist (goodGramPMF n k hk') (uniformSymMat k) := by
          linarith
      _ ≤ (∑ i ∈ Finset.range k, (2 : ℝ) ^ ((i + 1 : ℤ) - n)) + (2 : ℝ) ^ ((k + 1 : ℤ) - n) := by
          linarith [ih hk']

private lemma prod_sub_two_pow_tele (n : ℕ) : ∀ k : ℕ,
    (∏ i ∈ Finset.range k, (2 ^ n - 2 ^ (i + 1))) * (2 ^ n - 1) =
      (∏ i ∈ Finset.range k, (2 ^ n - 2 ^ i)) * (2 ^ n - 2 ^ k) := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.prod_range_succ, Finset.prod_range_succ]
    calc (∏ i ∈ Finset.range k, (2 ^ n - 2 ^ (i + 1))) * (2 ^ n - 2 ^ (k + 1)) * (2 ^ n - 1)
        = (∏ i ∈ Finset.range k, (2 ^ n - 2 ^ (i + 1))) * (2 ^ n - 1) *
            (2 ^ n - 2 ^ (k + 1)) := by ring
      _ = (∏ i ∈ Finset.range k, (2 ^ n - 2 ^ i)) * (2 ^ n - 2 ^ k) *
            (2 ^ n - 2 ^ (k + 1)) := by rw [ih]

/-- For $k + 1 \le n$, the total variation distance between the Gram matrix $M M^\top$ of a
uniformly random full-row-rank $M \in \mathbb{F}_2^{k \times n}$ and a uniformly random symmetric
matrix $A \in \mathrm{SymMat}\ k$ is at most $3 \cdot 2^{k - n}$. -/
theorem dist_gramPMF_uniformSymMat_le (n k : ℕ) (hk : k + 1 ≤ n) :
    dist (gramPMF n k (by omega)) (uniformSymMat k) ≤ 3 * (2 : ℝ) ^ ((k : ℤ) - n) := by
  classical
  have hkn : k ≤ n := by omega
  let Indep := { a : Fin k → Fin n → ZMod 2 // LinearIndependent (ZMod 2) a }
  have hGoodNE : Nonempty { a : Fin k → Fin n → ZMod 2 // IsGoodTuple a } :=
    Fintype.card_pos_iff.mp (card_goodTuples_pos n k hk)
  have hIndepNE : Nonempty Indep :=
    let ⟨a⟩ := hGoodNE
    ⟨⟨a.1, isGoodTuple_imp_linearIndependent a.2⟩⟩
  let E : Set Indep := { a | IsGoodTuple a.1 }
  have hE : ∃ a ∈ E, a ∈ (Cslib.Probability.PMF.uniformOfFintype Indep).support := by
    let ⟨a⟩ := hGoodNE
    exact ⟨⟨a.1, isGoodTuple_imp_linearIndependent a.2⟩, a.2, by
      simp [PMF.mem_support_iff, Cslib.Probability.PMF.uniformOfFintype_apply]⟩
  have hfilt_eq :
      ((Cslib.Probability.PMF.uniformOfFintype Indep).filter E hE).map (fun a ↦ gramMat a.1) =
        goodGramPMF n k hk := by
    let e : { a : Fin k → Fin n → ZMod 2 // IsGoodTuple a } → Indep :=
      fun a ↦ ⟨a.1, isGoodTuple_imp_linearIndependent a.2⟩
    have hmap : (uniformGoodTuples n k hk).map e =
        (Cslib.Probability.PMF.uniformOfFintype Indep).filter E hE := by
      ext a
      by_cases haE : a ∈ E
      · have hgood : IsGoodTuple a.1 := haE
        rw [PMF.map_apply, tsum_eq_single (⟨a.1, hgood⟩ : { b // IsGoodTuple b })]
        · rw [ite_eq_left rfl, PMF.filter_apply, Set.indicator_of_mem haE,
            ← PMF.toOuterMeasure_apply, uniformGoodTuples,
            Cslib.Probability.PMF.uniformOfFintype_apply,
            Cslib.Probability.PMF.uniformOfFintype_apply]
          have hmeas : (Cslib.Probability.PMF.uniformOfFintype Indep).toOuterMeasure E =
              (Fintype.card { b : Fin k → Fin n → ZMod 2 // IsGoodTuple b } : ENNReal) /
                (Fintype.card Indep : ENNReal) := by
            rw [PMF.toOuterMeasure_apply, tsum_fintype]
            simp only [Set.indicator_apply, Cslib.Probability.PMF.uniformOfFintype_apply,
              Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul,
              div_eq_mul_inv]
            congr 1
            have hcardE : (Finset.univ.filter fun x : Indep ↦ x ∈ E).card =
                Fintype.card { b : Fin k → Fin n → ZMod 2 // IsGoodTuple b } := by
              rw [← Finset.card_univ]
              refine Finset.card_bij
                (fun x hx ↦ (⟨x.1, (Finset.mem_filter.mp hx).2⟩ :
                  { b : Fin k → Fin n → ZMod 2 // IsGoodTuple b }))
                (fun _ _ ↦ Finset.mem_univ _)
                (fun _ _ _ _ h ↦ Subtype.ext (Subtype.mk.inj h))
                (fun y _ ↦ ⟨e y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, y.2⟩, rfl⟩)
            exact_mod_cast hcardE
          have hI_ne0 : (Fintype.card Indep : ENNReal) ≠ 0 :=
            Nat.cast_ne_zero.mpr (Fintype.card_pos_iff.mpr hIndepNE).ne'
          rw [hmeas, div_eq_mul_inv,
            ENNReal.mul_inv (Or.inl (by exact_mod_cast (card_goodTuples_pos n k hk).ne'))
              (Or.inl (by simp)),
            inv_inv, mul_comm (_ : ENNReal)⁻¹, mul_assoc,
            ENNReal.mul_inv_cancel hI_ne0 (ENNReal.natCast_ne_top _), mul_one]
        · intro b hb
          exact ite_eq_right fun (h : a = e b) ↦
            hb (Subtype.ext (congrArg (Subtype.val : Indep → _) h).symm)
      · rw [PMF.filter_apply, Set.indicator_of_notMem haE, zero_mul, PMF.map_apply, tsum_fintype]
        refine Finset.sum_eq_zero fun b _ ↦ ?_
        have hne : a ≠ e b := fun h ↦ haE (by rw [h]; exact b.2)
        simp [hne]
    rw [← hmap, PMF.map_comp, goodGramPMF]
    rfl
  have hdist1 : dist (gramPMF n k hkn) (goodGramPMF n k hk) ≤ (2 : ℝ) ^ ((k : ℤ) - n) := by
    rw [← hfilt_eq]
    have hgm : gramPMF n k hkn =
        (Cslib.Probability.PMF.uniformOfFintype Indep).map (fun a ↦ gramMat a.1) := rfl
    rw [hgm]
    calc dist ((Cslib.Probability.PMF.uniformOfFintype Indep).map (fun a ↦ gramMat a.1))
            (((Cslib.Probability.PMF.uniformOfFintype Indep).filter E hE).map
              (fun a ↦ gramMat a.1))
        ≤ dist (Cslib.Probability.PMF.uniformOfFintype Indep)
            ((Cslib.Probability.PMF.uniformOfFintype Indep).filter E hE) :=
          Cslib.Probability.PMF.dist_map_le _ _ _
      _ = ((Cslib.Probability.PMF.uniformOfFintype Indep).toOuterMeasure Eᶜ).toReal :=
          Cslib.Probability.PMF.dist_filter _ _ _
      _ ≤ (2 : ℝ) ^ ((k : ℤ) - n) := by
          rw [Cslib.Probability.PMF.toOuterMeasure_apply_toReal]
          have hcardI : Fintype.card Indep = ∏ i ∈ Finset.range k, (2 ^ n - 2 ^ i) :=
            card_indepTuples n k hkn
          have hcardE : (Finset.univ.filter fun x : Indep ↦ x ∈ E).card =
              ∏ i ∈ Finset.range k, (2 ^ n - 2 ^ (i + 1)) := by
            rw [← card_goodTuples n k hk, ← Finset.card_univ]
            refine Finset.card_bij
              (fun x hx ↦ (⟨x.1, (Finset.mem_filter.mp hx).2⟩ :
                { b : Fin k → Fin n → ZMod 2 // IsGoodTuple b }))
              (fun _ _ ↦ Finset.mem_univ _)
              (fun _ _ _ _ h ↦ Subtype.ext (Subtype.mk.inj h))
              (fun y _ ↦ ⟨⟨y.1, isGoodTuple_imp_linearIndependent y.2⟩,
                Finset.mem_filter.mpr ⟨Finset.mem_univ _, y.2⟩, rfl⟩)
          have hadd := Finset.card_filter_add_card_filter_not
            (s := (Finset.univ : Finset Indep)) (p := fun x ↦ x ∈ E)
          have hcardEc : (Finset.univ.filter fun x : Indep ↦ x ∈ Eᶜ).card =
              Fintype.card Indep - (Finset.univ.filter fun x : Indep ↦ x ∈ E).card := by
            change (Finset.univ.filter fun x : Indep ↦ x ∉ E).card = _
            have htot : (Finset.univ : Finset Indep).card = Fintype.card Indep := Finset.card_univ
            omega
          simp only [Cslib.Probability.PMF.uniformOfFintype_apply, ENNReal.toReal_inv,
            ENNReal.toReal_natCast, Finset.sum_ite, Finset.sum_const_zero, add_zero,
            Finset.sum_const, nsmul_eq_mul, hcardEc]
          have hEleI : (Finset.univ.filter fun x : Indep ↦ x ∈ E).card ≤ Fintype.card Indep :=
            (Finset.card_le_univ _).trans_eq Finset.card_univ
          rw [Nat.cast_sub hEleI, sub_mul, mul_inv_cancel₀
            (by exact_mod_cast (Fintype.card_pos_iff.mpr hIndepNE).ne')]
          have hteleR : ((Finset.univ.filter fun x : Indep ↦ x ∈ E).card : ℝ) *
              ((2 : ℝ) ^ n - 1) = (Fintype.card Indep : ℝ) * ((2 : ℝ) ^ n - (2 : ℝ) ^ k) := by
            have h1 : (1 : ℕ) ≤ 2 ^ n := Nat.one_le_two_pow
            have h2 : 2 ^ k ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hkn
            have hnat : ((Finset.univ.filter fun x : Indep ↦ x ∈ E).card * (2 ^ n - 1) : ℕ) =
                Fintype.card Indep * (2 ^ n - 2 ^ k) := by
              rw [hcardE, hcardI]; exact prod_sub_two_pow_tele n k
            have hr : (((Finset.univ.filter fun x : Indep ↦ x ∈ E).card * (2 ^ n - 1) : ℕ) : ℝ) =
                ((Fintype.card Indep * (2 ^ n - 2 ^ k) : ℕ) : ℝ) := by exact_mod_cast hnat
            push_cast [Nat.cast_sub h1, Nat.cast_sub h2] at hr
            exact hr
          have hI_pos : (0 : ℝ) < (Fintype.card Indep : ℝ) := by
            exact_mod_cast Fintype.card_pos_iff.mpr hIndepNE
          have h2n1_pos : (0 : ℝ) < (2 : ℝ) ^ n - 1 := by
            have : (2 : ℕ) ≤ 2 ^ n := by
              have : 1 ≤ n := by omega
              exact (Nat.pow_le_pow_right (by norm_num) this).trans_eq' (by norm_num)
            have : (2 : ℝ) ≤ (2 : ℝ) ^ n := by exact_mod_cast this
            linarith
          have hratio : ((Finset.univ.filter fun x : Indep ↦ x ∈ E).card : ℝ) *
              (Fintype.card Indep : ℝ)⁻¹ = ((2 : ℝ) ^ n - (2 : ℝ) ^ k) / ((2 : ℝ) ^ n - 1) := by
            rw [← div_eq_mul_inv, div_eq_div_iff hI_pos.ne' h2n1_pos.ne']
            exact hteleR.trans (mul_comm _ _)
          rw [hratio, zpow_sub₀ (by norm_num), zpow_natCast, zpow_natCast]
          have h2n_pos : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
          have h2k_le : (2 : ℝ) ^ k ≤ (2 : ℝ) ^ n := by
            exact_mod_cast Nat.pow_le_pow_right (by norm_num) hkn
          have hsub_eq : 1 - ((2 : ℝ) ^ n - (2 : ℝ) ^ k) / ((2 : ℝ) ^ n - 1) =
              ((2 : ℝ) ^ k - 1) / ((2 : ℝ) ^ n - 1) := by
            field_simp [h2n1_pos.ne']; ring
          rw [hsub_eq, div_le_div_iff₀ h2n1_pos h2n_pos]
          nlinarith
  have hgeom : ∑ i ∈ Finset.range k, (2 : ℝ) ^ ((i + 1 : ℤ) - n) ≤
      2 * (2 : ℝ) ^ ((k : ℤ) - n) := by
    have h2n_pos : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
    have hterm (i : ℕ) : (2 : ℝ) ^ ((i + 1 : ℤ) - n) = (2 : ℝ) ^ (i + 1) / (2 : ℝ) ^ n := by
      rw [zpow_sub₀ (by norm_num),
        show (i + 1 : ℤ) = ((i + 1 : ℕ) : ℤ) by push_cast; rfl, zpow_natCast, zpow_natCast]
    simp_rw [hterm, div_eq_mul_inv, ← Finset.sum_mul]
    rw [zpow_sub₀ (by norm_num), zpow_natCast, zpow_natCast, ← div_eq_mul_inv, ← mul_div_assoc,
      div_le_div_iff_of_pos_right h2n_pos]
    have hsum : ∑ i ∈ Finset.range k, (2 : ℝ) ^ (i + 1) = 2 * ((2 : ℝ) ^ k - 1) := by
      have : ∀ m : ℕ, ∑ i ∈ Finset.range m, (2 : ℝ) ^ (i + 1) = 2 * ((2 : ℝ) ^ m - 1) := by
        intro m
        induction m with
        | zero => simp
        | succ m ihm => rw [Finset.sum_range_succ, ihm, pow_succ]; ring
      exact this k
    rw [hsum]
    linarith
  calc dist (gramPMF n k hkn) (uniformSymMat k)
      ≤ dist (gramPMF n k hkn) (goodGramPMF n k hk) +
          dist (goodGramPMF n k hk) (uniformSymMat k) := dist_triangle _ _ _
    _ ≤ (2 : ℝ) ^ ((k : ℤ) - n) + 2 * (2 : ℝ) ^ ((k : ℤ) - n) := by
        linarith [hdist1, dist_goodGramPMF_uniformSymMat_le n k hk, hgeom]
    _ = 3 * (2 : ℝ) ^ ((k : ℤ) - n) := by ring

/-! ### Nonsingularity probability bound for random symmetric matrices over $\mathbb{F}_2$ -/

private lemma finrank_sup_le_rs {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [Module.Finite (ZMod 2) V] (S T : Submodule (ZMod 2) V) :
    Module.finrank (ZMod 2) ↥(S ⊔ T) ≤ Module.finrank (ZMod 2) S + Module.finrank (ZMod 2) T := by
  have := Submodule.finrank_sup_add_finrank_inf_eq S T
  omega

private lemma finrank_span_singleton_le_rs {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (x : V) : Module.finrank (ZMod 2) (Submodule.span (ZMod 2) ({x} : Set V)) ≤ 1 := by
  have := finrank_span_le_card (R := ZMod 2) ({x} : Set V)
  simpa using this

private lemma symMatExtend_mulVec {ℓ : ℕ} (B : SymMat ℓ) (r : Fin ℓ → ZMod 2) (u : ZMod 2)
    (v : Fin ℓ → ZMod 2) (c : ZMod 2) :
    (symMatExtend B r u).1.mulVec (Fin.snoc (α := fun _ ↦ ZMod 2) v c) =
      Fin.snoc (α := fun _ ↦ ZMod 2) (B.1.mulVec v + c • r) (dotProduct r v + u * c) := by
  ext i
  refine Fin.lastCases ?_ (fun i' ↦ ?_) i
  · simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, Fin.snoc_last,
      Fin.snoc_castSucc, symMatExtend_apply_last_castSucc, symMatExtend_apply_last_last]
  · simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, Fin.snoc_castSucc,
      Fin.snoc_last, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      symMatExtend_apply_castSucc_castSucc, symMatExtend_apply_castSucc_last, mul_comm c]

private lemma rank_le_rank_symMatExtend {ℓ : ℕ} (B : SymMat ℓ) (r : Fin ℓ → ZMod 2) (u : ZMod 2) :
    B.1.rank ≤ (symMatExtend B r u).1.rank := by
  let proj : (Fin (ℓ + 1) → ZMod 2) →ₗ[ZMod 2] (Fin ℓ → ZMod 2) :=
    { toFun := Fin.init
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  have hle : LinearMap.range B.1.mulVecLin ≤
      Submodule.map proj (LinearMap.range (symMatExtend B r u).1.mulVecLin) := by
    rintro _ ⟨v, rfl⟩
    refine ⟨(symMatExtend B r u).1.mulVec (Fin.snoc (α := fun _ ↦ ZMod 2) v 0),
      ⟨Fin.snoc (α := fun _ ↦ ZMod 2) v 0, rfl⟩, ?_⟩
    rw [symMatExtend_mulVec, zero_smul, add_zero]
    ext i
    change Fin.init (Fin.snoc (α := fun _ ↦ ZMod 2) (B.1.mulVec v) (dotProduct r v + u * 0)) i =
      B.1.mulVec v i
    simp [Fin.init]
  calc B.1.rank = Module.finrank (ZMod 2) (LinearMap.range B.1.mulVecLin) := rfl
    _ ≤ Module.finrank (ZMod 2)
          (Submodule.map proj (LinearMap.range (symMatExtend B r u).1.mulVecLin)) :=
        Submodule.finrank_mono hle
    _ ≤ Module.finrank (ZMod 2) (LinearMap.range (symMatExtend B r u).1.mulVecLin) :=
        Submodule.finrank_map_le proj _

private lemma rank_symMatExtend_le {ℓ : ℕ} (B : SymMat ℓ) (r : Fin ℓ → ZMod 2) (u : ZMod 2) :
    (symMatExtend B r u).1.rank ≤ B.1.rank + 2 := by
  let emb : (Fin ℓ → ZMod 2) →ₗ[ZMod 2] (Fin (ℓ + 1) → ZMod 2) :=
    { toFun := fun v ↦ Fin.snoc (α := fun _ ↦ ZMod 2) v 0
      map_add' := fun v w ↦ by
        ext i; refine Fin.lastCases (by simp) (fun l ↦ by simp) i
      map_smul' := fun c v ↦ by
        ext i; refine Fin.lastCases (by simp) (fun l ↦ by simp) i }
  let eLast : Fin (ℓ + 1) → ZMod 2 := Pi.single (Fin.last ℓ) 1
  let lastCol : Fin (ℓ + 1) → ZMod 2 := Fin.snoc (α := fun _ ↦ ZMod 2) r u
  let U₁ : Submodule (ZMod 2) (Fin (ℓ + 1) → ZMod 2) :=
    Submodule.map emb (LinearMap.range B.1.mulVecLin) ⊔ Submodule.span (ZMod 2) ({eLast} : Set _)
  let U : Submodule (ZMod 2) (Fin (ℓ + 1) → ZMod 2) :=
    U₁ ⊔ Submodule.span (ZMod 2) ({lastCol} : Set _)
  have hsub : LinearMap.range (symMatExtend B r u).1.mulVecLin ≤ U := by
    rintro _ ⟨w, rfl⟩
    have hw : w = Fin.snoc (α := fun _ ↦ ZMod 2) (Fin.init w) (w (Fin.last ℓ)) := by
      ext i; refine Fin.lastCases (by simp) (fun l ↦ by simp [Fin.init]) i
    simp only [Matrix.mulVecLin_apply]
    rw [hw, symMatExtend_mulVec]
    have hsplit : Fin.snoc (α := fun _ ↦ ZMod 2) (B.1.mulVec (Fin.init w) + w (Fin.last ℓ) • r)
          (dotProduct r (Fin.init w) + u * w (Fin.last ℓ)) =
        emb (B.1.mulVec (Fin.init w)) + dotProduct r (Fin.init w) • eLast +
          w (Fin.last ℓ) • lastCol := by
      ext i
      refine Fin.lastCases ?_ (fun l ↦ ?_) i
      · simp [emb, eLast, lastCol, mul_comm]
      · simp [emb, eLast, lastCol, Fin.castSucc_ne_last]
    rw [hsplit]
    refine Submodule.add_mem U ?_ (Submodule.mem_sup_right
      (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))))
    refine Submodule.mem_sup_left (Submodule.add_mem _ ?_ ?_)
    · exact Submodule.mem_sup_left ⟨B.1.mulVec (Fin.init w), ⟨Fin.init w, rfl⟩, rfl⟩
    · exact Submodule.mem_sup_right
        (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _)))
  calc (symMatExtend B r u).1.rank
      ≤ Module.finrank (ZMod 2) U := Submodule.finrank_mono hsub
    _ ≤ Module.finrank (ZMod 2) U₁ +
        Module.finrank (ZMod 2) (Submodule.span (ZMod 2) ({lastCol} : Set _)) :=
        finrank_sup_le_rs U₁ _
    _ ≤ (Module.finrank (ZMod 2) (Submodule.map emb (LinearMap.range B.1.mulVecLin)) +
          Module.finrank (ZMod 2) (Submodule.span (ZMod 2) ({eLast} : Set _))) + 1 := by
        gcongr
        · exact finrank_sup_le_rs _ _
        · exact finrank_span_singleton_le_rs lastCol
    _ ≤ (B.1.rank + 1) + 1 := by
        gcongr
        · exact Submodule.finrank_map_le emb _
        · exact finrank_span_singleton_le_rs eLast
    _ = B.1.rank + 2 := by ring

private lemma det_eq_zero_of_mulVec_eq_zero {k : ℕ} (A : Matrix (Fin k) (Fin k) (ZMod 2))
    {v : Fin k → ZMod 2} (hv : v ≠ 0) (hAv : A.mulVec v = 0) : A.det = 0 := by
  by_contra hdet
  have hunit : IsUnit A.det := isUnit_iff_ne_zero.mpr hdet
  have hinv := congrArg (A⁻¹.mulVec ·) hAv
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hunit, Matrix.one_mulVec,
    Matrix.mulVec_zero] at hinv
  exact hv hinv

private lemma det_ne_zero_imp_rank_eq {k : ℕ} (A : Matrix (Fin k) (Fin k) (ZMod 2))
    (hdet : A.det ≠ 0) : A.rank = k := by
  have hunit : IsUnit A.det := isUnit_iff_ne_zero.mpr hdet
  have hsurj : Function.Surjective A.mulVecLin := fun y ↦
    ⟨A⁻¹.mulVec y, by
      change A.mulVec (A⁻¹.mulVec y) = y
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hunit, Matrix.one_mulVec]⟩
  rw [Matrix.rank, LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_fin_fun]

/-- If a symmetric $\ell \times \ell$ matrix $B$ over $\mathbb{F}_2$ satisfies
$\mathrm{rank}(B) \le \ell - 2$, then every symmetric $(\ell + 1) \times (\ell + 1)$ extension of
$B$ is singular. -/
theorem symMatExtend_det_eq_zero_of_rank_add_two_le {ℓ : ℕ} (B : SymMat ℓ) (hB : B.1.rank + 2 ≤ ℓ)
    (r : Fin ℓ → ZMod 2) (u : ZMod 2) : (symMatExtend B r u).1.det = 0 := by
  by_contra hdet
  have h1 := det_ne_zero_imp_rank_eq _ hdet
  have h2 := rank_symMatExtend_le B r u
  omega

/-- For any symmetric $\ell \times \ell$ matrix $B$ over $\mathbb{F}_2$, at most half ($2^\ell$)
of its $2^{\ell + 1}$ symmetric extensions to $\mathrm{SymMat}\ (\ell + 1)$ are nonsingular. -/
theorem card_symMatExtend_det_ne_zero_le {ℓ : ℕ} (B : SymMat ℓ) :
    (Finset.univ.filter fun p : (Fin ℓ → ZMod 2) × ZMod 2 ↦
      (symMatExtend B p.1 p.2).1.det ≠ 0).card ≤ 2 ^ ℓ := by
  classical
  have hBr : B.1.rank ≤ ℓ := by
    have := Submodule.finrank_le (LinearMap.range B.1.mulVecLin)
    rwa [Module.finrank_fin_fun] at this
  rcases eq_or_lt_of_le hBr with hB | hB
  · have hsurj : Function.Surjective B.1.mulVecLin := by
      rw [← LinearMap.range_eq_top]
      apply Submodule.eq_top_of_finrank_eq
      rw [Module.finrank_fin_fun]
      exact hB
    have hbad : ∀ r : Fin ℓ → ZMod 2, ∃ u : ZMod 2, (symMatExtend B r u).1.det = 0 := by
      intro r
      obtain ⟨v, hv⟩ := hsurj r
      refine ⟨dotProduct r v, det_eq_zero_of_mulVec_eq_zero _
        (v := Fin.snoc (α := fun _ ↦ ZMod 2) v 1)
        (fun h ↦ by have := congrFun h (Fin.last ℓ); simp at this) ?_⟩
      rw [symMatExtend_mulVec, one_smul, mul_one]
      change Fin.snoc (α := fun _ ↦ ZMod 2) (B.1.mulVecLin v + r)
        (dotProduct r v + dotProduct r v) = 0
      rw [hv]
      ext i
      refine Fin.lastCases (by simp [zmod2_add_self]) (fun l ↦ by simp [zmod2_add_self]) i
    have hle : (Finset.univ.filter fun p : (Fin ℓ → ZMod 2) × ZMod 2 ↦
        (symMatExtend B p.1 p.2).1.det ≠ 0).card ≤
        (Finset.univ : Finset (Fin ℓ → ZMod 2)).card := by
      refine Finset.card_le_card_of_injOn Prod.fst (fun _ _ ↦ Finset.mem_univ _) ?_
      intro ⟨r₁, u₁⟩ h₁ ⟨r₂, u₂⟩ h₂ hr
      dsimp only at hr; subst hr
      obtain ⟨u₀, hu₀⟩ := hbad r₁
      have hne₁ : u₁ ≠ u₀ := fun h ↦ (Finset.mem_filter.mp h₁).2 (h ▸ hu₀)
      have hne₂ : u₂ ≠ u₀ := fun h ↦ (Finset.mem_filter.mp h₂).2 (h ▸ hu₀)
      have hu : u₁ = u₂ := by
        rcases zmod2_eq_zero_or_one u₀ with rfl | rfl <;>
        rcases zmod2_eq_zero_or_one u₁ with rfl | rfl <;>
        rcases zmod2_eq_zero_or_one u₂ with rfl | rfl <;> simp_all
      rw [hu]
    simpa [ZMod.card] using hle
  · have hker_pos : 0 < Module.finrank (ZMod 2) (LinearMap.ker B.1.mulVecLin) := by
      have hrt := LinearMap.finrank_range_add_finrank_ker B.1.mulVecLin
      rw [Module.finrank_fin_fun] at hrt
      have : Module.finrank (ZMod 2) (LinearMap.range B.1.mulVecLin) = B.1.rank := rfl
      omega
    have hker_nt : Nontrivial (LinearMap.ker B.1.mulVecLin) :=
      Module.nontrivial_of_finrank_pos hker_pos
    obtain ⟨⟨v, hv_ker⟩, hv_ne0⟩ := exists_ne (0 : LinearMap.ker B.1.mulVecLin)
    have hv_nz : v ≠ 0 := fun h ↦ hv_ne0 (Subtype.ext h)
    have hBv : B.1.mulVec v = 0 := LinearMap.mem_ker.mp hv_ker
    have hsub : (Finset.univ.filter fun p : (Fin ℓ → ZMod 2) × ZMod 2 ↦
        (symMatExtend B p.1 p.2).1.det ≠ 0) ⊆
        (Finset.univ.filter fun r : Fin ℓ → ZMod 2 ↦ dotProduct r v ≠ 0) ×ˢ
          (Finset.univ : Finset (ZMod 2)) := by
      intro ⟨r, u⟩ hp
      have hdet : (symMatExtend B r u).1.det ≠ 0 := (Finset.mem_filter.mp hp).2
      refine Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩,
        Finset.mem_univ _⟩
      intro hrv
      apply hdet
      refine det_eq_zero_of_mulVec_eq_zero _ (v := Fin.snoc (α := fun _ ↦ ZMod 2) v 0)
        (fun h ↦ hv_nz (funext fun l ↦ by have := congrFun h l.castSucc; simpa using this)) ?_
      rw [symMatExtend_mulVec, zero_smul, add_zero, hBv, hrv, mul_zero, add_zero]
      ext i; refine Fin.lastCases (by simp) (fun l ↦ by simp) i
    let φ : (Fin ℓ → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
      { toFun := fun r ↦ dotProduct r v
        map_add' := fun r₁ r₂ ↦ add_dotProduct r₁ r₂ v
        map_smul' := fun c r ↦ by simp [smul_dotProduct] }
    have hφ_surj : Function.Surjective φ := by
      obtain ⟨j₀, hj₀⟩ : ∃ j₀ : Fin ℓ, v j₀ ≠ 0 := by
        by_contra h; push Not at h; exact hv_nz (funext h)
      have hvj₀ : v j₀ = 1 := (zmod2_eq_zero_or_one (v j₀)).resolve_left hj₀
      intro c
      refine ⟨Pi.single j₀ c, ?_⟩
      simp [φ, dotProduct, Pi.single_apply, hvj₀]
    have hker_card : 2 * Fintype.card (LinearMap.ker φ) = 2 ^ ℓ := by
      have hq := Submodule.card_eq_card_quotient_mul_card (LinearMap.ker φ)
      rw [Nat.card_congr (LinearMap.quotKerEquivOfSurjective φ hφ_surj).toEquiv,
        Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
        ZMod.card, Fintype.card_fun, ZMod.card, Fintype.card_fin] at hq
      linarith
    have hzero_card : (Finset.univ.filter fun r : Fin ℓ → ZMod 2 ↦ dotProduct r v = 0).card =
        Fintype.card (LinearMap.ker φ) := by
      rw [← Fintype.card_coe]
      exact Fintype.card_congr
        { toFun := fun x ↦ ⟨x.1, (Finset.mem_filter.mp x.2).2⟩
          invFun := fun x ↦ ⟨x.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, x.2⟩⟩
          left_inv := fun _ ↦ rfl
          right_inv := fun _ ↦ rfl }
    have hnz_card : (Finset.univ.filter fun r : Fin ℓ → ZMod 2 ↦ dotProduct r v ≠ 0).card * 2 =
        2 ^ ℓ := by
      have hadd := Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset (Fin ℓ → ZMod 2))) (p := fun r ↦ dotProduct r v = 0)
      have htot : (Finset.univ : Finset (Fin ℓ → ZMod 2)).card = 2 ^ ℓ := by simp [ZMod.card]
      have hfeq : (Finset.univ.filter fun r : Fin ℓ → ZMod 2 ↦ dotProduct r v ≠ 0) =
          (Finset.univ.filter fun r : Fin ℓ → ZMod 2 ↦ ¬ dotProduct r v = 0) := rfl
      rw [hfeq]; omega
    calc (Finset.univ.filter fun p : (Fin ℓ → ZMod 2) × ZMod 2 ↦
            (symMatExtend B p.1 p.2).1.det ≠ 0).card
        ≤ ((Finset.univ.filter fun r : Fin ℓ → ZMod 2 ↦ dotProduct r v ≠ 0) ×ˢ
            (Finset.univ : Finset (ZMod 2))).card := Finset.card_le_card hsub
      _ = (Finset.univ.filter fun r : Fin ℓ → ZMod 2 ↦ dotProduct r v ≠ 0).card * 2 := by
          rw [Finset.card_product]; simp [ZMod.card]
      _ = 2 ^ ℓ := hnz_card

/-- Extending $B \in \mathrm{SymMat}\ \ell$ to $\mathrm{SymMat}\ (\ell + 1)$ preserves
$\mathrm{rank}(A) = \mathrm{rank}(B)$ for at least $2^{\mathrm{rank}(B)}$ choices of border
$(r, u) \in \mathbb{F}_2^\ell \times \mathbb{F}_2$. -/
theorem card_extend_same_rank_ge {ℓ : ℕ} (B : SymMat ℓ) :
    2 ^ B.1.rank ≤ (Finset.univ.filter fun p : (Fin ℓ → ZMod 2) × ZMod 2 ↦
      (symMatExtend B p.1 p.2).1.rank = B.1.rank).card := by
  classical
  set V := LinearMap.range B.1.mulVecLin
  have hVcard : Fintype.card V = 2 ^ B.1.rank := by
    rw [Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card]; rfl
  rw [← hVcard]
  have hchoose : ∀ r : V, ∃ c : Fin ℓ → ZMod 2, B.1.mulVec c = r.1 := fun r ↦ r.2
  choose c hc using hchoose
  have hmap_mem : ∀ r : V, (symMatExtend B r.1 (dotProduct (c r) r.1)).1.rank = B.1.rank := by
    intro r
    refine le_antisymm ?_ (rank_le_rank_symMatExtend B r.1 (dotProduct (c r) r.1))
    let φ : V →ₗ[ZMod 2] (Fin (ℓ + 1) → ZMod 2) :=
      { toFun := fun w ↦ Fin.snoc (α := fun _ ↦ ZMod 2) w.1 (dotProduct (c r) w.1)
        map_add' := fun w₁ w₂ ↦ by
          ext i; refine Fin.lastCases (by simp [dotProduct_add]) (fun l ↦ by simp) i
        map_smul' := fun a w ↦ by
          ext i; refine Fin.lastCases (by simp [dotProduct_smul]) (fun l ↦ by simp) i }
    have hsub : LinearMap.range (symMatExtend B r.1 (dotProduct (c r) r.1)).1.mulVecLin ≤
        LinearMap.range φ := by
      rintro _ ⟨w, rfl⟩
      have hw : w = Fin.snoc (α := fun _ ↦ ZMod 2) (Fin.init w) (w (Fin.last ℓ)) := by
        ext i; refine Fin.lastCases (by simp) (fun l ↦ by simp [Fin.init]) i
      simp only [Matrix.mulVecLin_apply]
      rw [hw, symMatExtend_mulVec]
      let y : V := ⟨B.1.mulVec (Fin.init w) + w (Fin.last ℓ) • r.1,
        Submodule.add_mem V ⟨Fin.init w, rfl⟩ (Submodule.smul_mem V _ r.2)⟩
      refine ⟨y, ?_⟩
      ext i
      refine Fin.lastCases ?_ (fun l ↦ by simp [φ, y]) i
      simp only [φ, y, LinearMap.coe_mk, AddHom.coe_mk, Fin.snoc_last, dotProduct_add,
        dotProduct_smul, smul_eq_mul]
      congr 1
      · calc dotProduct (c r) (B.1.mulVec (Fin.init w))
            = dotProduct (B.1.vecMul (c r)) (Fin.init w) :=
              Matrix.dotProduct_mulVec (c r) B.1 (Fin.init w)
          _ = dotProduct (B.1.mulVec (c r)) (Fin.init w) := by
              congr 1; ext j
              simp only [Matrix.vecMul, Matrix.mulVec, dotProduct]
              refine Finset.sum_congr rfl fun k _ ↦ ?_
              rw [mul_comm, ← congrFun (congrFun B.2 j) k]; rfl
          _ = dotProduct r.1 (Fin.init w) := by rw [hc r]
      · ring
    calc (symMatExtend B r.1 (dotProduct (c r) r.1)).1.rank
        ≤ Module.finrank (ZMod 2) (LinearMap.range φ) := Submodule.finrank_mono hsub
      _ ≤ Module.finrank (ZMod 2) V := LinearMap.finrank_range_le φ
      _ = B.1.rank := rfl
  have hle : (Finset.univ : Finset V).card ≤
      (Finset.univ.filter fun p : (Fin ℓ → ZMod 2) × ZMod 2 ↦
        (symMatExtend B p.1 p.2).1.rank = B.1.rank).card := by
    refine Finset.card_le_card_of_injOn (fun r : V ↦ (r.1, dotProduct (c r) r.1))
      (fun r _ ↦ Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmap_mem r⟩)
      (fun r₁ _ r₂ _ h ↦ Subtype.ext (Prod.mk.inj h).1)
  simpa using hle

private lemma card_extend_rank_le_ge {ℓ s : ℕ} (hsℓ : s ≤ ℓ) (B : SymMat ℓ)
    (hB : B.1.rank ≤ s + 1) :
    2 ^ s ≤ (Finset.univ.filter fun p : (Fin ℓ → ZMod 2) × ZMod 2 ↦
      (symMatExtend B p.1 p.2).1.rank ≤ s + 1).card := by
  classical
  by_cases hlt : B.1.rank + 1 ≤ s
  · have hall : (Finset.univ.filter fun p : (Fin ℓ → ZMod 2) × ZMod 2 ↦
        (symMatExtend B p.1 p.2).1.rank ≤ s + 1) = Finset.univ := by
      ext p; simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      have := rank_symMatExtend_le B p.1 p.2; omega
    rw [hall, Finset.card_univ, Fintype.card_prod, Fintype.card_fun, ZMod.card, Fintype.card_fin]
    exact (Nat.pow_le_pow_right (by norm_num) hsℓ).trans (Nat.le_mul_of_pos_right _ (by norm_num))
  · have hge : s ≤ B.1.rank := by omega
    have hsub : (Finset.univ.filter fun p : (Fin ℓ → ZMod 2) × ZMod 2 ↦
          (symMatExtend B p.1 p.2).1.rank = B.1.rank) ⊆
        (Finset.univ.filter fun p : (Fin ℓ → ZMod 2) × ZMod 2 ↦
          (symMatExtend B p.1 p.2).1.rank ≤ s + 1) := by
      intro p hp
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      rw [(Finset.mem_filter.mp hp).2]; exact hB
    exact (Nat.pow_le_pow_right (by norm_num) hge).trans
      ((card_extend_same_rank_ge B).trans (Finset.card_le_card hsub))

private lemma card_symMat_filter_split (ℓ : ℕ) (P : SymMat (ℓ + 1) → Prop) [DecidablePred P] :
    (Finset.univ.filter P).card =
      ∑ B : SymMat ℓ, (Finset.univ.filter fun p : (Fin ℓ → ZMod 2) × ZMod 2 ↦
        P (symMatExtend B p.1 p.2)).card := by
  rw [← Finset.card_sigma]
  refine Finset.card_bij (fun A _ ↦ ⟨(symMatSplitEquiv ℓ A).1, (symMatSplitEquiv ℓ A).2⟩)
    (fun A hA ↦ Finset.mem_sigma.mpr ⟨Finset.mem_univ _, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, by
        rw [symMatExtend_symMatSplitEquiv]; exact (Finset.mem_filter.mp hA).2⟩⟩)
    (fun A₁ _ A₂ _ h ↦ (symMatSplitEquiv ℓ).injective
      (Prod.ext (congrArg Sigma.fst h) (by simpa using (Sigma.mk.inj_iff.mp h).2)))
    (fun ⟨B, p⟩ hp ↦ ⟨symMatExtend B p.1 p.2, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (Finset.mem_filter.mp (Finset.mem_sigma.mp hp).2).2⟩, by
      simp [symMatSplitEquiv_symMatExtend]⟩)

/-- For every $s \in \mathbb{N}$, at least a $2^{-6} = 1 / 64$ fraction of symmetric
$(s + 3) \times (s + 3)$ matrices over $\mathbb{F}_2$ have rank at most $s + 1$. -/
theorem card_rank_le_sub_three_ge (s : ℕ) :
    Fintype.card (SymMat (s + 3)) ≤
      64 * (Finset.univ.filter fun A : SymMat (s + 3) ↦ A.1.rank ≤ s + 1).card := by
  classical
  have hstep : ∀ ℓ, s ≤ ℓ →
      (Finset.univ.filter fun A : SymMat ℓ ↦ A.1.rank ≤ s + 1).card * 2 ^ s ≤
        (Finset.univ.filter fun A : SymMat (ℓ + 1) ↦ A.1.rank ≤ s + 1).card := by
    intro ℓ hsℓ
    rw [card_symMat_filter_split ℓ (fun A ↦ A.1.rank ≤ s + 1)]
    calc (Finset.univ.filter fun A : SymMat ℓ ↦ A.1.rank ≤ s + 1).card * 2 ^ s
        = ∑ _A ∈ Finset.univ.filter (fun A : SymMat ℓ ↦ A.1.rank ≤ s + 1), 2 ^ s := by simp
      _ ≤ ∑ A ∈ Finset.univ.filter (fun A : SymMat ℓ ↦ A.1.rank ≤ s + 1),
            (Finset.univ.filter fun p : (Fin ℓ → ZMod 2) × ZMod 2 ↦
              (symMatExtend A p.1 p.2).1.rank ≤ s + 1).card :=
          Finset.sum_le_sum fun A hA ↦ card_extend_rank_le_ge hsℓ A (Finset.mem_filter.mp hA).2
      _ ≤ ∑ A : SymMat ℓ, (Finset.univ.filter fun p : (Fin ℓ → ZMod 2) × ZMod 2 ↦
            (symMatExtend A p.1 p.2).1.rank ≤ s + 1).card :=
          Finset.sum_le_univ_sum_of_nonneg fun _ ↦ Nat.zero_le _
  have hbase : (Finset.univ.filter fun A₀ : SymMat s ↦ A₀.1.rank ≤ s + 1).card =
      Fintype.card (SymMat s) := by
    rw [← Finset.card_univ]; congr 1
    exact Finset.filter_true_of_mem fun A₀ _ ↦ by
      have := Submodule.finrank_le (LinearMap.range A₀.1.mulVecLin)
      rw [Module.finrank_fin_fun] at this; exact this.trans (Nat.le_succ s)
  have hc1 := hbase ▸ hstep s le_rfl
  have hc2 := hstep (s + 1) (by omega)
  have hc3 := hstep (s + 2) (by omega)
  have hcard3 : Fintype.card (SymMat (s + 3)) =
      Fintype.card (SymMat s) * (64 * (2 ^ s * 2 ^ s * 2 ^ s)) := by
    rw [card_symMat_succ (s + 2), card_symMat_succ (s + 1), card_symMat_succ s]
    rw [pow_succ, pow_succ, pow_succ, pow_succ, pow_succ, pow_succ]
    ring
  rw [hcard3]
  have hchain : Fintype.card (SymMat s) * (2 ^ s * 2 ^ s * 2 ^ s) ≤
      (Finset.univ.filter fun A₃ : SymMat (s + 3) ↦ A₃.1.rank ≤ s + 1).card := by
    calc Fintype.card (SymMat s) * (2 ^ s * 2 ^ s * 2 ^ s)
        = (Fintype.card (SymMat s) * 2 ^ s) * 2 ^ s * 2 ^ s := by ring
      _ ≤ (Finset.univ.filter fun A₁ : SymMat (s + 1) ↦ A₁.1.rank ≤ s + 1).card * 2 ^ s * 2 ^ s :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hc1)
      _ ≤ (Finset.univ.filter fun A₂ : SymMat (s + 2) ↦ A₂.1.rank ≤ s + 1).card * 2 ^ s :=
          Nat.mul_le_mul_right _ hc2
      _ ≤ (Finset.univ.filter fun A₃ : SymMat (s + 3) ↦ A₃.1.rank ≤ s + 1).card := hc3
  nlinarith

/-- For every $k \ge 4$, the probability that a uniformly random symmetric $k \times k$ matrix
$A \in \mathrm{SymMat}\ k$ over $\mathbb{F}_2$ is nonsingular ($\det A \ne 0$) is at most
$1 / 2 - 2^{-7}$. -/
theorem prob_symmetric_fullRank_le {k : ℕ} (hk : 4 ≤ k) :
    (∑ A : SymMat k, ((uniformSymMat k) A).toReal * if A.1.det ≠ 0 then (1 : ℝ) else 0) ≤
      1 / 2 - (2 : ℝ) ^ (-7 : ℤ) := by
  classical
  obtain ⟨s, rfl⟩ : ∃ s, k = s + 4 := ⟨k - 4, by omega⟩
  have hsum_le :
      (Finset.univ.filter fun A : SymMat (s + 4) ↦ A.1.det ≠ 0).card ≤
        (Finset.univ.filter fun B : SymMat (s + 3) ↦ ¬ B.1.rank ≤ s + 1).card * 2 ^ (s + 3) := by
    rw [card_symMat_filter_split (s + 3) (fun A ↦ A.1.det ≠ 0),
      ← Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun B : SymMat (s + 3) ↦ B.1.rank ≤ s + 1)]
    have hlow0 :
        ∑ B ∈ Finset.univ.filter (fun B : SymMat (s + 3) ↦ B.1.rank ≤ s + 1),
          (Finset.univ.filter fun p : (Fin (s + 3) → ZMod 2) × ZMod 2 ↦
            (symMatExtend B p.1 p.2).1.det ≠ 0).card = 0 := by
      refine Finset.sum_eq_zero fun B hB ↦ Finset.card_eq_zero.mpr (Finset.filter_eq_empty_iff.mpr
        fun p _ ↦ not_not.mpr (symMatExtend_det_eq_zero_of_rank_add_two_le B
          (by have := (Finset.mem_filter.mp hB).2; omega) p.1 p.2))
    rw [hlow0, zero_add]
    exact (Finset.sum_le_sum fun B _ ↦ card_symMatExtend_det_ne_zero_le B).trans_eq (by simp)
  have hcompl : (Finset.univ.filter fun B : SymMat (s + 3) ↦ B.1.rank ≤ s + 1).card +
      (Finset.univ.filter fun B : SymMat (s + 3) ↦ ¬ B.1.rank ≤ s + 1).card =
        Fintype.card (SymMat (s + 3)) := by
    simpa using Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (SymMat (s + 3)))) (p := fun B ↦ B.1.rank ≤ s + 1)
  have hcl2 := card_rank_le_sub_three_ge s
  have hcard4 : Fintype.card (SymMat (s + 4)) =
      Fintype.card (SymMat (s + 3)) * (2 * 2 ^ (s + 3)) := by
    rw [card_symMat_succ (s + 3), pow_succ']
  have hnat_bound : 128 * (Finset.univ.filter fun A : SymMat (s + 4) ↦ A.1.det ≠ 0).card ≤
      63 * Fintype.card (SymMat (s + 4)) := by
    rw [hcard4]
    have h1 : 64 * (Finset.univ.filter fun B : SymMat (s + 3) ↦ ¬ B.1.rank ≤ s + 1).card ≤
        63 * Fintype.card (SymMat (s + 3)) := by omega
    calc 128 * (Finset.univ.filter fun A : SymMat (s + 4) ↦ A.1.det ≠ 0).card
        ≤ (64 * (Finset.univ.filter fun B : SymMat (s + 3) ↦ ¬ B.1.rank ≤ s + 1).card) *
            (2 * 2 ^ (s + 3)) := by linarith
      _ ≤ (63 * Fintype.card (SymMat (s + 3))) * (2 * 2 ^ (s + 3)) := Nat.mul_le_mul_right _ h1
      _ = 63 * (Fintype.card (SymMat (s + 3)) * (2 * 2 ^ (s + 3))) := by ring
  have hsum_eq : (∑ A : SymMat (s + 4), ((uniformSymMat (s + 4)) A).toReal *
        if A.1.det ≠ 0 then (1 : ℝ) else 0) =
      ((Finset.univ.filter fun A : SymMat (s + 4) ↦ A.1.det ≠ 0).card : ℝ) /
        (Fintype.card (SymMat (s + 4)) : ℝ) := by
    simp only [uniformSymMat_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast, mul_ite, mul_one,
      mul_zero, Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul,
      div_eq_mul_inv]
  rw [hsum_eq]
  have hne : Nonempty (SymMat (s + 4)) := ⟨⟨0, Matrix.transpose_zero⟩⟩
  have hpos : (0 : ℝ) < (Fintype.card (SymMat (s + 4)) : ℝ) :=
    Nat.cast_pos.mpr (Fintype.card_pos_iff.mpr hne)
  rw [div_le_iff₀ hpos, show (1 / 2 : ℝ) - (2 : ℝ) ^ (-7 : ℤ) = 63 / 128 by norm_num]
  have hreal : 128 * ((Finset.univ.filter fun A : SymMat (s + 4) ↦ A.1.det ≠ 0).card : ℝ) ≤
      63 * (Fintype.card (SymMat (s + 4)) : ℝ) := by exact_mod_cast hnat_bound
  linarith

end

end CslibFrontier.Matrix.RandomSymmetric
