module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Matrix.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.LinearAlgebra.Matrix.Rank

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.Tactic.Linarith
import CslibFrontier.Foundations.LinearAlgebra.Matrix.Rank

/-!
# Upper-Echelon Anti-Diagonal Sparsity for Low-Rank Matrices

This module develops leading-nonzero-entry (`IsLNE`) and partial `(< k)`-upper-echelon theory
along the anti-diagonals `i + j = k` of an `n × m` matrix over a field:

* **Row independence from distinct leading columns** (`rows_linearIndependent_of_lneCols_inj`):
  rows of a matrix whose leading nonzero entries occur in pairwise distinct columns are linearly
  independent.
* **Rank bound on leading nonzero entries** (`lneLt_card_le_rank_and_cols_inj`): in a
  `(< k)`-upper-echelon matrix of rank at most `r`, the leading nonzero entries lying on
  anti-diagonals `< k` have pairwise distinct columns and cardinality at most `rank M ≤ r`.
* **Anti-diagonal sparsity outside the advice set** (`diag_advice_sparse_of_ltUpperEchelon`):
  in a `(< k)`-upper-echelon matrix `M` of rank at most `r`, the `k`-th anti-diagonal `M^{(k)}`
  has at most `r - |LNE(M^{(< k)})|` nonzero entries outside the advice set induced by the rows
  and columns of `LNE(M^{(< k)})`.

## Main definitions

* `CslibFrontier.IsLNE`, `CslibFrontier.lneLt`, `CslibFrontier.lneRowsLt`,
  `CslibFrontier.lneColsLt`, `CslibFrontier.IsLtUpperEchelon`
* `CslibFrontier.diagLen`, `CslibFrontier.diagCol`, `CslibFrontier.diagRow`,
  `CslibFrontier.diagVec`, `CslibFrontier.diagAdviceSet`

## Main results

* `CslibFrontier.rows_linearIndependent_of_lneCols_inj`
* `CslibFrontier.lneLt_card_le_rank_and_cols_inj`
* `CslibFrontier.diag_advice_sparse_of_ltUpperEchelon`
-/

open scoped Matrix

namespace CslibFrontier

public section

/-- Entry `(i, j)` is the leading nonzero entry of row `i` in `M`. -/
@[expose] def IsLNE {R : Type*} [Zero R] {n m : ℕ} (M : Matrix (Fin n) (Fin m) R)
    (i : Fin n) (j : Fin m) : Prop :=
  M i j ≠ 0 ∧ ∀ j' : Fin m, j' < j → M i j' = 0

/-- Finset of leading nonzero entries of `M` lying on anti-diagonals `i + j < k`. -/
@[expose] def lneLt {R : Type*} [Zero R] [DecidableEq R] {n m : ℕ}
    (M : Matrix (Fin n) (Fin m) R) (k : ℕ) : Finset (Fin n × Fin m) :=
  Finset.univ.filter fun p =>
    p.1.1 + p.2.1 < k ∧ M p.1 p.2 ≠ 0 ∧ ∀ j' : Fin m, j' < p.2 → M p.1 j' = 0

/-- Row indices of leading nonzero entries in `lneLt M k`. -/
@[expose] def lneRowsLt {R : Type*} [Zero R] [DecidableEq R] {n m : ℕ}
    (M : Matrix (Fin n) (Fin m) R) (k : ℕ) : Finset (Fin n) :=
  (lneLt M k).image Prod.fst

/-- Column indices of leading nonzero entries in `lneLt M k`. -/
@[expose] def lneColsLt {R : Type*} [Zero R] [DecidableEq R] {n m : ℕ}
    (M : Matrix (Fin n) (Fin m) R) (k : ℕ) : Finset (Fin m) :=
  (lneLt M k).image Prod.snd

/-- A matrix `M` is in `(< k)`-upper-echelon form if for every leading nonzero entry `(i, j)`
with `i + j < k`, every entry below it in column `j` on anti-diagonals `< k` vanishes. -/
@[expose] def IsLtUpperEchelon {R : Type*} [Zero R] {n m : ℕ} (M : Matrix (Fin n) (Fin m) R)
    (k : ℕ) : Prop :=
  ∀ (i : Fin n) (j : Fin m), i.1 + j.1 < k → IsLNE M i j →
    ∀ i' : Fin n, i < i' → i'.1 + j.1 < k → M i' j = 0

/-- Length of the `k`-th anti-diagonal `{(i, j) : i + j = k}` of an `n × m` matrix (`n ≤ m`). -/
@[expose] def diagLen (n m k : ℕ) : ℕ := min (k + 1) (min n (n + m - (k + 1)))

/-- Column index of the `t`-th entry on anti-diagonal `k` of an `n × m` matrix (`n ≤ m`). -/
@[expose] def diagCol (n m k : ℕ) (hnm : n ≤ m) (_hk : k < n + m - 1)
    (t : Fin (diagLen n m k)) : Fin m :=
  ⟨(k + 1 - n) + t.1, by
    have ht := t.isLt
    unfold diagLen at ht
    omega⟩

/-- Row index of the `t`-th entry on anti-diagonal `k` of an `n × m` matrix (`n ≤ m`). -/
@[expose] def diagRow (n m k : ℕ) (_hnm : n ≤ m) (_hk : k < n + m - 1)
    (t : Fin (diagLen n m k)) : Fin n :=
  ⟨k - ((k + 1 - n) + t.1), by
    have ht := t.isLt
    unfold diagLen at ht
    omega⟩

/-- Sum identity `(diagRow t).1 + (diagCol t).1 = k`. -/
theorem diagRow_add_diagCol {n m k : ℕ} (hnm : n ≤ m) (hk : k < n + m - 1)
    (t : Fin (diagLen n m k)) :
    (diagRow n m k hnm hk t).1 + (diagCol n m k hnm hk t).1 = k := by
  have ht := t.isLt
  unfold diagLen at ht
  dsimp only [diagRow, diagCol]
  omega

/-- The `k`-th anti-diagonal of `M` viewed as a vector of length `diagLen n m k`. -/
@[expose] def diagVec {R : Type*} {n m : ℕ} (hnm : n ≤ m) (k : ℕ) (hk : k < n + m - 1)
    (M : Matrix (Fin n) (Fin m) R) : Fin (diagLen n m k) → R :=
  fun t => M (diagRow n m k hnm hk t) (diagCol n m k hnm hk t)

/-- Advice set on anti-diagonal `k` induced by known leading-entry rows `rowSet` and columns
`colSet`. -/
@[expose] def diagAdviceSet {n m : ℕ} (hnm : n ≤ m) (k : ℕ) (hk : k < n + m - 1)
    (rowSet : Finset (Fin n)) (colSet : Finset (Fin m)) : Finset (Fin (diagLen n m k)) :=
  Finset.univ.filter fun t =>
    diagRow n m k hnm hk t ∈ rowSet ∨ diagCol n m k hnm hk t ∈ colSet

/-- Row indices with pairwise distinct leading-nonzero columns are linearly independent. -/
theorem rows_linearIndependent_of_lneCols_inj {F : Type*} [Field F] {n m : ℕ}
    {M : Matrix (Fin n) (Fin m) F} {S : Finset (Fin n)} {col : Fin n → Fin m}
    (hlne : ∀ i ∈ S, IsLNE M i (col i))
    (hinj : ∀ i₁ ∈ S, ∀ i₂ ∈ S, col i₁ = col i₂ → i₁ = i₂) :
    LinearIndependent F (fun i : S => M.row i.1) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc
  by_contra hne
  push Not at hne
  let NZ : Finset S := Finset.univ.filter fun i => c i ≠ 0
  have hNZ : NZ.Nonempty := by
    rcases hne with ⟨i0, hi0⟩
    exact ⟨i0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi0⟩⟩
  obtain ⟨iMin, hiMin_mem, hiMin_le⟩ :=
    Finset.exists_min_image NZ (fun i : S => (col i.1).1) hNZ
  have hciMin : c iMin ≠ 0 := (Finset.mem_filter.mp hiMin_mem).2
  have hcol_zero := congrFun hc (col iMin.1)
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, Matrix.row_apply]
    at hcol_zero
  rw [Finset.sum_eq_single iMin] at hcol_zero
  · exact mul_ne_zero hciMin (hlne iMin.1 iMin.2).1 hcol_zero
  · intro i _ hine
    by_cases hci : c i = 0
    · simp [hci]
    · have hiNZ : i ∈ NZ := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hci⟩
      have hle : (col iMin.1).1 ≤ (col i.1).1 := hiMin_le i hiNZ
      have hne_col : col iMin.1 ≠ col i.1 := fun h =>
        hine (Subtype.ext (hinj iMin.1 iMin.2 i.1 i.2 h).symm)
      have hlt : col iMin.1 < col i.1 :=
        Fin.lt_def.mpr (lt_of_le_of_ne hle (fun h => hne_col (Fin.ext h)))
      rw [(hlne i.1 i.2).2 (col iMin.1) hlt, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- In a `(< k)`-upper-echelon matrix of rank at most `r`, the leading nonzero entries on
anti-diagonals `< k` have pairwise distinct columns and cardinality at most `rank M ≤ r`. -/
theorem lneLt_card_le_rank_and_cols_inj {F : Type*} [Field F] [DecidableEq F] {n m r k : ℕ}
    {M : Matrix (Fin n) (Fin m) F} (hMrank : M.rank ≤ r) (hue : IsLtUpperEchelon M k) :
    (∀ p₁ ∈ lneLt M k, ∀ p₂ ∈ lneLt M k, p₁.2 = p₂.2 → p₁ = p₂) ∧
    (lneRowsLt M k).card = (lneLt M k).card ∧
    (lneColsLt M k).card = (lneLt M k).card ∧
    (lneLt M k).card ≤ M.rank ∧
    (lneLt M k).card ≤ r := by
  have hrow_inj : ∀ p₁ ∈ lneLt M k, ∀ p₂ ∈ lneLt M k, p₁.1 = p₂.1 → p₁ = p₂ := by
    intro ⟨i₁, j₁⟩ h1 ⟨i₂, j₂⟩ h2 hrow
    dsimp only at hrow
    subst hrow
    have hp1 := (Finset.mem_filter.mp h1).2
    have hp2 := (Finset.mem_filter.mp h2).2
    congr 1
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact hp1.2.1 (hp2.2.2 j₁ hlt)
    · exact hp2.2.1 (hp1.2.2 j₂ hgt)
  have hcol_inj : ∀ p₁ ∈ lneLt M k, ∀ p₂ ∈ lneLt M k, p₁.2 = p₂.2 → p₁ = p₂ := by
    intro ⟨i₁, j₁⟩ h1 ⟨i₂, j₂⟩ h2 hcol
    dsimp only at hcol
    subst hcol
    have hp1 := (Finset.mem_filter.mp h1).2
    have hp2 := (Finset.mem_filter.mp h2).2
    congr 1
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact hp2.2.1 (hue i₁ j₁ hp1.1 ⟨hp1.2.1, hp1.2.2⟩ i₂ hlt hp2.1)
    · exact hp1.2.1 (hue i₂ j₁ hp2.1 ⟨hp2.2.1, hp2.2.2⟩ i₁ hgt hp1.1)
  have hcard_rows : (lneRowsLt M k).card = (lneLt M k).card :=
    Finset.card_image_of_injOn fun a ha b hb h => hrow_inj a ha b hb h
  have hcard_cols : (lneColsLt M k).card = (lneLt M k).card :=
    Finset.card_image_of_injOn fun a ha b hb h => hcol_inj a ha b hb h
  classical
  cases m with
  | zero =>
      simp [lneLt, lneRowsLt, lneColsLt]
  | succ m =>
      let colOf : Fin n → Fin (m + 1) := fun i =>
        if h : ∃ j : Fin (m + 1), (i, j) ∈ lneLt M k then h.choose else ⟨0, Nat.zero_lt_succ m⟩
      have hcolOf_mem : ∀ i ∈ lneRowsLt M k, (i, colOf i) ∈ lneLt M k := by
        intro i hi
        rcases Finset.mem_image.mp hi with ⟨⟨i', j'⟩, hmem, heq⟩
        dsimp only at heq
        subst heq
        have hex : ∃ j : Fin (m + 1), (i', j) ∈ lneLt M k := ⟨j', hmem⟩
        simpa only [colOf, hex, ↓reduceDIte] using hex.choose_spec
      have hli : LinearIndependent F (fun i : lneRowsLt M k => M.row i.1) := by
        refine rows_linearIndependent_of_lneCols_inj
          (fun i hi => let hp := (Finset.mem_filter.mp (hcolOf_mem i hi)).2; ⟨hp.2.1, hp.2.2⟩) ?_
        intro i₁ h1 i₂ h2 hceq
        exact congrArg Prod.fst (hcol_inj _ (hcolOf_mem i₁ h1) _ (hcolOf_mem i₂ h2) hceq)
      have hcard_le_rank : (lneRowsLt M k).card ≤ M.rank := by
        have hspan_le : Submodule.span F (Set.range fun i : lneRowsLt M k => M.row i.1) ≤
            LinearMap.range Mᵀ.mulVecLin := by
          rw [Submodule.span_le]
          rintro _ ⟨i, rfl⟩
          rw [Matrix.range_mulVecLin]
          exact Submodule.subset_span ⟨i.1, rfl⟩
        have hfr : Module.finrank F (Submodule.span F
            (Set.range fun i : lneRowsLt M k => M.row i.1)) = (lneRowsLt M k).card := by
          rw [finrank_span_eq_card hli, Fintype.card_coe]
        have hle := Submodule.finrank_mono hspan_le
        rw [hfr] at hle
        have htr : Module.finrank F (LinearMap.range Mᵀ.mulVecLin) = M.rank := by
          change Mᵀ.rank = M.rank
          exact Matrix.rank_transpose M
        omega
      refine ⟨hcol_inj, hcard_rows, hcard_cols, by omega, by omega⟩

/-- Anti-diagonal advice-sparsity bound: in a `(< k)`-upper-echelon matrix `M` of rank at most `r`,
the `k`-th anti-diagonal `M^{(k)}` has at most `r - |LNE(M^{(< k)})|` nonzero entries outside the
advice set `diagAdviceSet hnm k hk (lneRowsLt M k) (lneColsLt M k)`. -/
theorem diag_advice_sparse_of_ltUpperEchelon {F : Type*} [Field F] [DecidableEq F]
    {n m r k : ℕ} (hnm : n ≤ m) (hk : k < n + m - 1)
    {M : Matrix (Fin n) (Fin m) F} (hMrank : M.rank ≤ r) (hue : IsLtUpperEchelon M k) :
    let S := diagAdviceSet hnm k hk (lneRowsLt M k) (lneColsLt M k)
    let supp := Finset.univ.filter fun t : Fin (diagLen n m k) => diagVec hnm k hk M t ≠ 0
    S.card ≤ 2 * (lneLt M k).card ∧
    (supp \ S).card + (lneLt M k).card ≤ M.rank ∧
    2 * (supp \ S).card + S.card ≤ 2 * r := by
  have huer := lneLt_card_le_rank_and_cols_inj hMrank hue
  rcases huer with ⟨hcol_inj, hcard_rows, hcard_cols, hle_rank, hle_r⟩
  let S := diagAdviceSet hnm k hk (lneRowsLt M k) (lneColsLt M k)
  let supp := Finset.univ.filter fun t : Fin (diagLen n m k) => diagVec hnm k hk M t ≠ 0
  have hS_card : S.card ≤ 2 * (lneLt M k).card := by
    let SR := Finset.univ.filter fun t : Fin (diagLen n m k) =>
      diagRow n m k hnm hk t ∈ lneRowsLt M k
    let SC := Finset.univ.filter fun t : Fin (diagLen n m k) =>
      diagCol n m k hnm hk t ∈ lneColsLt M k
    have hSunion : S = SR ∪ SC := by
      ext t; simp [S, SR, SC, diagAdviceSet]
    have hSR_le : SR.card ≤ (lneRowsLt M k).card := by
      refine Finset.card_le_card_of_injOn (diagRow n m k hnm hk)
        (fun t ht => (Finset.mem_filter.mp ht).2) ?_
      intro a _ b _ h
      have h1 := diagRow_add_diagCol hnm hk a
      have h2 := diagRow_add_diagCol hnm hk b
      have hrow : (diagRow n m k hnm hk a).1 = (diagRow n m k hnm hk b).1 := congrArg Fin.val h
      dsimp only [diagCol] at h1 h2
      exact Fin.ext (by omega)
    have hSC_le : SC.card ≤ (lneColsLt M k).card := by
      refine Finset.card_le_card_of_injOn (diagCol n m k hnm hk)
        (fun t ht => (Finset.mem_filter.mp ht).2) ?_
      intro a _ b _ h
      have hv : (k + 1 - n) + a.1 = (k + 1 - n) + b.1 := congrArg Fin.val h
      exact Fin.ext (by omega)
    have hu := Finset.card_union_le SR SC
    rw [hSunion]; omega
  let T_out : Finset (Fin (diagLen n m k)) := supp \ S
  have hnew_lne : ∀ t ∈ T_out, IsLNE M (diagRow n m k hnm hk t) (diagCol n m k hnm hk t) := by
    intro t ht
    have ht_supp := (Finset.mem_sdiff.mp ht).1
    have ht_notS := (Finset.mem_sdiff.mp ht).2
    have hnz : M (diagRow n m k hnm hk t) (diagCol n m k hnm hk t) ≠ 0 :=
      (Finset.mem_filter.mp ht_supp).2
    have hnot_row : diagRow n m k hnm hk t ∉ lneRowsLt M k := fun h =>
      ht_notS (Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl h⟩)
    refine ⟨hnz, fun j' hj' => ?_⟩
    by_contra hnz'
    let NZ : Finset (Fin m) := Finset.univ.filter fun j'' =>
      j'' < diagCol n m k hnm hk t ∧ M (diagRow n m k hnm hk t) j'' ≠ 0
    have hNZ : NZ.Nonempty := ⟨j', Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj', hnz'⟩⟩
    obtain ⟨jmin, hjmin, hjmin_le⟩ :=
      Finset.exists_min_image NZ (fun j'' : Fin m => j''.1) hNZ
    have hjmin_prop := (Finset.mem_filter.mp hjmin).2
    have hlt_k : (diagRow n m k hnm hk t).1 + jmin.1 < k := by
      have hsum := diagRow_add_diagCol hnm hk t
      have : jmin.1 < (diagCol n m k hnm hk t).1 := hjmin_prop.1
      omega
    have hmem_lne : (diagRow n m k hnm hk t, jmin) ∈ lneLt M k := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt_k, hjmin_prop.2, fun j'' hj'' => ?_⟩
      by_contra hnz''
      have hle := hjmin_le j'' (Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, lt_trans hj'' hjmin_prop.1, hnz''⟩)
      have : j''.1 < jmin.1 := hj''
      omega
    exact hnot_row (Finset.mem_image.mpr ⟨_, hmem_lne, rfl⟩)
  let newRows : Finset (Fin n) := T_out.image (diagRow n m k hnm hk)
  have hdisj : Disjoint (lneRowsLt M k) newRows := by
    rw [Finset.disjoint_left]
    intro i hi hnew
    rcases Finset.mem_image.mp hnew with ⟨t, ht, rfl⟩
    exact (Finset.mem_sdiff.mp ht).2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl hi⟩)
  have hnewRows_card : newRows.card = T_out.card := by
    refine Finset.card_image_of_injOn fun a _ b _ h => ?_
    have h1 := diagRow_add_diagCol hnm hk a
    have h2 := diagRow_add_diagCol hnm hk b
    have hrow : (diagRow n m k hnm hk a).1 = (diagRow n m k hnm hk b).1 := congrArg Fin.val h
    dsimp only [diagCol] at h1 h2
    exact Fin.ext (by omega)
  let allRows : Finset (Fin n) := lneRowsLt M k ∪ newRows
  have hall_card : allRows.card = (lneLt M k).card + T_out.card := by
    rw [Finset.card_union_of_disjoint hdisj, hcard_rows, hnewRows_card]
  classical
  have hm_pos : 0 < m := by omega
  let colOf : Fin n → Fin m := fun i =>
    if h1 : ∃ j : Fin m, (i, j) ∈ lneLt M k then h1.choose
    else if h2 : ∃ t ∈ T_out, diagRow n m k hnm hk t = i then diagCol n m k hnm hk h2.choose
    else ⟨0, hm_pos⟩
  have hli : LinearIndependent F (fun i : allRows => M.row i.1) := by
    refine rows_linearIndependent_of_lneCols_inj (col := colOf) ?_ ?_
    · intro i hi
      rcases Finset.mem_union.mp hi with hi_old | hi_new
      · rcases Finset.mem_image.mp hi_old with ⟨⟨i', j'⟩, hmem, heq⟩
        dsimp only at heq; subst heq
        have h1 : ∃ j : Fin m, (i', j) ∈ lneLt M k := ⟨j', hmem⟩
        have hp := (Finset.mem_filter.mp h1.choose_spec).2
        simp only [colOf, h1, ↓reduceDIte]
        exact ⟨hp.2.1, hp.2.2⟩
      · have hnot1 : ¬ ∃ j : Fin m, (i, j) ∈ lneLt M k := fun ⟨j, hj⟩ =>
          Finset.disjoint_left.mp hdisj (Finset.mem_image.mpr ⟨(i, j), hj, rfl⟩) hi_new
        rcases Finset.mem_image.mp hi_new with ⟨t, ht, rfl⟩
        have h2 : ∃ t' ∈ T_out, diagRow n m k hnm hk t' = diagRow n m k hnm hk t := ⟨t, ht, rfl⟩
        simp only [colOf, hnot1, ↓reduceDIte, h2]
        have ht' := h2.choose_spec
        simpa only [ht'.2] using hnew_lne h2.choose ht'.1
    · intro i₁ h1 i₂ h2 hceq
      rcases Finset.mem_union.mp h1 with h1_old | h1_new <;>
        rcases Finset.mem_union.mp h2 with h2_old | h2_new
      · rcases Finset.mem_image.mp h1_old with ⟨⟨i1', j1⟩, hm1, rfl⟩
        rcases Finset.mem_image.mp h2_old with ⟨⟨i2', j2⟩, hm2, rfl⟩
        have ex1 : ∃ j, (i1', j) ∈ lneLt M k := ⟨j1, hm1⟩
        have ex2 : ∃ j, (i2', j) ∈ lneLt M k := ⟨j2, hm2⟩
        simp only [colOf, ex1, ex2, ↓reduceDIte] at hceq
        have hpair : (i1', ex1.choose) = (i2', ex2.choose) :=
          hcol_inj (i1', ex1.choose) ex1.choose_spec (i2', ex2.choose) ex2.choose_spec hceq
        exact (Prod.mk.inj hpair).1
      · exfalso
        rcases Finset.mem_image.mp h1_old with ⟨⟨i1', j1⟩, hm1, rfl⟩
        have ex1 : ∃ j, (i1', j) ∈ lneLt M k := ⟨j1, hm1⟩
        have hnot2 : ¬ ∃ j : Fin m, (i₂, j) ∈ lneLt M k := fun ⟨j, hj⟩ =>
          Finset.disjoint_left.mp hdisj (Finset.mem_image.mpr ⟨(i₂, j), hj, rfl⟩) h2_new
        rcases Finset.mem_image.mp h2_new with ⟨t2, ht2, rfl⟩
        have ex2 : ∃ t' ∈ T_out, diagRow n m k hnm hk t' = diagRow n m k hnm hk t2 :=
          ⟨t2, ht2, rfl⟩
        simp only [colOf, ex1, hnot2, ex2, ↓reduceDIte] at hceq
        have hcol_in : diagCol n m k hnm hk ex2.choose ∈ lneColsLt M k := by
          rw [← hceq]; exact Finset.mem_image.mpr ⟨_, ex1.choose_spec, rfl⟩
        exact (Finset.mem_sdiff.mp ex2.choose_spec.1).2
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr hcol_in⟩)
      · exfalso
        rcases Finset.mem_image.mp h2_old with ⟨⟨i2', j2⟩, hm2, rfl⟩
        have ex2 : ∃ j, (i2', j) ∈ lneLt M k := ⟨j2, hm2⟩
        have hnot1 : ¬ ∃ j : Fin m, (i₁, j) ∈ lneLt M k := fun ⟨j, hj⟩ =>
          Finset.disjoint_left.mp hdisj (Finset.mem_image.mpr ⟨(i₁, j), hj, rfl⟩) h1_new
        rcases Finset.mem_image.mp h1_new with ⟨t1, ht1, rfl⟩
        have ex1 : ∃ t' ∈ T_out, diagRow n m k hnm hk t' = diagRow n m k hnm hk t1 :=
          ⟨t1, ht1, rfl⟩
        simp only [colOf, ex2, hnot1, ex1, ↓reduceDIte] at hceq
        have hcol_in : diagCol n m k hnm hk ex1.choose ∈ lneColsLt M k := by
          rw [hceq]; exact Finset.mem_image.mpr ⟨_, ex2.choose_spec, rfl⟩
        exact (Finset.mem_sdiff.mp ex1.choose_spec.1).2
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr hcol_in⟩)
      · have hnot1 : ¬ ∃ j : Fin m, (i₁, j) ∈ lneLt M k := fun ⟨j, hj⟩ =>
          Finset.disjoint_left.mp hdisj (Finset.mem_image.mpr ⟨(i₁, j), hj, rfl⟩) h1_new
        have hnot2 : ¬ ∃ j : Fin m, (i₂, j) ∈ lneLt M k := fun ⟨j, hj⟩ =>
          Finset.disjoint_left.mp hdisj (Finset.mem_image.mpr ⟨(i₂, j), hj, rfl⟩) h2_new
        rcases Finset.mem_image.mp h1_new with ⟨t1, ht1, rfl⟩
        rcases Finset.mem_image.mp h2_new with ⟨t2, ht2, rfl⟩
        have ex1 : ∃ t' ∈ T_out, diagRow n m k hnm hk t' = diagRow n m k hnm hk t1 :=
          ⟨t1, ht1, rfl⟩
        have ex2 : ∃ t' ∈ T_out, diagRow n m k hnm hk t' = diagRow n m k hnm hk t2 :=
          ⟨t2, ht2, rfl⟩
        simp only [colOf, hnot1, hnot2, ex1, ex2, ↓reduceDIte] at hceq
        have hteq : ex1.choose = ex2.choose := by
          have hv : (k + 1 - n) + ex1.choose.1 = (k + 1 - n) + ex2.choose.1 :=
            congrArg Fin.val hceq
          exact Fin.ext (by omega)
        rw [← ex1.choose_spec.2, ← ex2.choose_spec.2, hteq]
  have hall_le_rank : allRows.card ≤ M.rank := by
    have hspan_le : Submodule.span F (Set.range fun i : allRows => M.row i.1) ≤
        LinearMap.range Mᵀ.mulVecLin := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      rw [Matrix.range_mulVecLin]
      exact Submodule.subset_span ⟨i.1, rfl⟩
    have hfr : Module.finrank F (Submodule.span F
        (Set.range fun i : allRows => M.row i.1)) = allRows.card := by
      rw [finrank_span_eq_card hli, Fintype.card_coe]
    have hle := Submodule.finrank_mono hspan_le
    rw [hfr] at hle
    have htr : Module.finrank F (LinearMap.range Mᵀ.mulVecLin) = M.rank := by
      change Mᵀ.rank = M.rank
      exact Matrix.rank_transpose M
    omega
  dsimp only [T_out, S, supp] at hall_card hS_card
  refine ⟨hS_card, by omega, by omega⟩

end

end CslibFrontier
