module

public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Data.Matrix.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Order.Hom.PowersetCard
public import CslibFrontier.Foundations.LinearAlgebra.Matrix.CauchyBinet

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import CslibFrontier.Foundations.LinearAlgebra.Matrix.Rank

/-!
# Rank-Preserving Vandermonde Matrices and Maximum-Weight Invertible Minors

This module establishes two general linear-algebraic results over arbitrary fields:

* **Unique maximum-weight invertible minor**: every `n × m` matrix of full row rank `n` has a
  unique `n`-element column subset `S ⊆ Fin m` maximizing the index sum `∑ i ∈ S, i` among all
  invertible `n × n` column submatrices (`exists_unique_max_weight_full_rank_submatrix`).
* **Rank-preserving Vandermonde matrices**: given a field extension `K / F`, an element `g ∈ K`
  whose first `n` powers `1, g, …, g^{n-1}` are distinct (`HasMultOrderGe g n`), and any `n × r`
  matrix `M` of rank `r ≤ n` over `F`, the matrix `(rankPreservingMat r n g α)_{i,j} = (g^i α)^j`
  satisfies `rank (rankPreservingMat r n g α * M) = r` for all `α ∈ K` outside a finite set of
  cardinality at most `n * r - (r + 1).choose 2 < n * r` (`rank_rankPreservingMat_mul_eq`),
  with a leading-rows extension to arbitrary rank `s ≤ r` matrices
  (`rank_rankPreservingMat_mul_leading_rows_eq`).

## Main definitions

* `CslibFrontier.HasMultOrderGe`
* `CslibFrontier.subsetWeight`
* `CslibFrontier.rankPreservingMat`

## Main results

* `CslibFrontier.exists_unique_max_weight_full_rank_submatrix`
* `CslibFrontier.rank_rankPreservingMat_mul_eq`
* `CslibFrontier.rank_rankPreservingMat_mul_leading_rows_eq`
-/

open scoped Matrix Polynomial

namespace CslibFrontier

public section

/-- An element `g` of a monoid has multiplicative order at least `n` if `g ≠ 0` and its powers
`g ^ 0, g ^ 1, …, g ^ (n - 1)` are pairwise distinct. -/
@[expose] def HasMultOrderGe {R : Type*} [MonoidWithZero R] (g : R) (n : ℕ) : Prop :=
  g ≠ 0 ∧ ∀ i j : ℕ, i < n → j < n → g ^ i = g ^ j → i = j

/-- Pairwise distinctness of powers below `n` for `HasMultOrderGe`. -/
theorem HasMultOrderGe.pow_injOn {R : Type*} [MonoidWithZero R] {g : R} {n : ℕ}
    (hg : HasMultOrderGe g n) {i j : ℕ} (hi : i < n) (hj : j < n) (heq : g ^ i = g ^ j) :
    i = j :=
  hg.2 i j hi hj heq

/-- Injectivity of `i ↦ g ^ i.1` on `Fin n` for `HasMultOrderGe g n`. -/
theorem HasMultOrderGe.pow_injective {R : Type*} [MonoidWithZero R] {g : R} {n : ℕ}
    (hg : HasMultOrderGe g n) : Function.Injective fun i : Fin n => g ^ i.1 :=
  fun _ _ heq => Fin.ext (hg.pow_injOn (Fin.isLt _) (Fin.isLt _) heq)

/-- Monotonicity of `HasMultOrderGe` in the order lower bound. -/
theorem HasMultOrderGe.mono {R : Type*} [MonoidWithZero R] {g : R} {m n : ℕ}
    (hg : HasMultOrderGe g n) (hmn : m ≤ n) : HasMultOrderGe g m :=
  ⟨hg.1, fun i j hi hj => hg.2 i j (lt_of_lt_of_le hi hmn) (lt_of_lt_of_le hj hmn)⟩

/-- Sum of indices of an `n`-element subset of `Fin m`. -/
@[expose] def subsetWeight {m n : ℕ} (S : Set.powersetCard (Fin m) n) : ℕ :=
  ∑ i : Fin n, (Set.powersetCard.ofFinEmbEquiv.symm S i).1

/-- Elementary binomial identity `2 * k.choose 2 = k * (k - 1)`. -/
private theorem two_mul_choose_two (k : ℕ) : 2 * k.choose 2 = k * (k - 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Nat.choose_succ_succ, Nat.choose_one_right, mul_add]
      cases k with
      | zero => simp
      | succ m =>
          simp only [Nat.add_sub_cancel] at ih ⊢
          nlinarith

/-- Sum of `1, …, r` equals `(r + 1).choose 2`. -/
private theorem sum_succ_eq_choose_two (r : ℕ) :
    ∑ i : Fin r, (i.1 + 1) = (r + 1).choose 2 := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      rw [ih, show (r + 1 + 1).choose 2 = (r + 1).choose 1 + (r + 1).choose 2 from
        Nat.choose_succ_succ (r + 1) 1, Nat.choose_one_right]
      omega

/-- Helper: `subsetWeight S` equals the sum of `.val` over the underlying `Finset` `S.val`. -/
private theorem subsetWeight_eq_sum_finset {m n : ℕ} (S : Set.powersetCard (Fin m) n) :
    subsetWeight S = ∑ x ∈ S.val, x.1 := by
  unfold subsetWeight
  let emb := Set.powersetCard.ofFinEmbEquiv.symm S
  have himg : Finset.univ.image (fun i : Fin n => emb i) = S.val := by
    ext x
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    change x ∈ Set.range emb ↔ x ∈ S.val
    rw [Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem]
    exact Set.powersetCard.mem_coe_iff.symm
  rw [← himg, Finset.sum_image]
  intro a _ b _ h
  exact emb.injective h

/-- Helper: a square `n × n` column submatrix is invertible iff its columns are linearly
independent. -/
private theorem det_submatrix_ne_zero_iff_linearIndependent {F : Type*} [Field F] {n m : ℕ}
    (M : Matrix (Fin n) (Fin m) F) (S : Set.powersetCard (Fin m) n) :
    (M.submatrix id (Set.powersetCard.ofFinEmbEquiv.symm S)).det ≠ 0 ↔
      LinearIndependent F (fun i : Fin n => M.col (Set.powersetCard.ofFinEmbEquiv.symm S i)) := by
  let B : Matrix (Fin n) (Fin n) F := M.submatrix id (Set.powersetCard.ofFinEmbEquiv.symm S)
  have hmul_iff : ∀ c : Fin n → F, B *ᵥ c = 0 ↔
      ∑ i : Fin n, c i • M.col (Set.powersetCard.ofFinEmbEquiv.symm S i) = 0 := by
    intro c
    constructor <;> intro h <;> ext row
    · have hrow := congrFun h row
      simpa [Matrix.mulVec, dotProduct, B, Matrix.col, mul_comm] using hrow
    · have hrow := congrFun h row
      simpa [Matrix.mulVec, dotProduct, B, Matrix.col, mul_comm] using hrow
  rw [← not_iff_not, not_not, ← Matrix.exists_mulVec_eq_zero_iff, Fintype.linearIndependent_iff]
  constructor
  · rintro ⟨c, hcne, hcmv⟩ hli
    apply hcne
    funext i
    exact hli c ((hmul_iff c).mp hcmv) i
  · intro hnot
    push Not at hnot
    rcases hnot with ⟨c, hcsum, i, hci⟩
    refine ⟨c, fun h0 => hci (congrFun h0 i), (hmul_iff c).mpr hcsum⟩

/-- Helper: linear independence of columns indexed by `Fin n` via `ofFinEmbEquiv.symm S` is
equivalent to linear independence indexed by `S.val`. -/
private theorem linearIndependent_cols_coe_iff {F : Type*} [Field F] {n m : ℕ}
    (M : Matrix (Fin n) (Fin m) F) (S : Set.powersetCard (Fin m) n) :
    LinearIndependent F (fun i : Fin n => M.col (Set.powersetCard.ofFinEmbEquiv.symm S i)) ↔
      LinearIndependent F (fun x : S.val => M.col x.1) := by
  let iso : Fin n ≃o S.val := Set.powersetCard.orderIsoOfFin S
  have hiso : ∀ i : Fin n, (iso i).1 = Set.powersetCard.ofFinEmbEquiv.symm S i := fun _ => rfl
  constructor
  · intro hli
    rw [Fintype.linearIndependent_iff] at hli ⊢
    intro c hc x
    have hsum : ∑ i : Fin n, c (iso i) • M.col (Set.powersetCard.ofFinEmbEquiv.symm S i) = 0 := by
      rw [← hc]
      exact Equiv.sum_comp iso.toEquiv fun y : S.val => c y • M.col y.1
    have h0 := hli (fun i => c (iso i)) hsum (iso.symm x)
    simpa using h0
  · intro hli
    rw [Fintype.linearIndependent_iff] at hli ⊢
    intro c hc i
    have hsum : ∑ x : S.val, c (iso.symm x) • M.col x.1 = 0 := by
      rw [← hc, ← Equiv.sum_comp iso.toEquiv fun y : S.val => c (iso.symm y) • M.col y.1]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp [hiso]
    have h0 := hli (fun x => c (iso.symm x)) hsum (iso i)
    simpa using h0

/-- Helper: any `n × m` matrix of rank `s` has `s` linearly independent columns. -/
private theorem exists_linearIndependent_cols {F : Type*} [Field F] {n m s : ℕ}
    (M : Matrix (Fin n) (Fin m) F) (hr : M.rank = s) :
    ∃ T : Finset (Fin m), T.card = s ∧ LinearIndependent F (fun x : T => M.col x.1) := by
  classical
  have hspan_eq : LinearMap.range M.mulVecLin = Submodule.span F (Set.range M.col) :=
    Matrix.range_mulVecLin M
  obtain ⟨I, hI_sub, hI_span, hI_li⟩ := exists_linearIndependent F (Set.range M.col)
  have hI_fin : I.Finite := (Set.finite_range M.col).subset hI_sub
  let _ : Fintype I := hI_fin.fintype
  have hcard_I : Fintype.card I = s := by
    have hfr : Module.finrank F (Submodule.span F I) = Fintype.card I := by
      have h1 := finrank_span_eq_card hI_li
      rwa [Subtype.range_coe_subtype, Set.ofPred_mem_eq] at h1
    have hsp : Submodule.span F I = LinearMap.range M.mulVecLin := hI_span.trans hspan_eq.symm
    change Module.finrank F (LinearMap.range M.mulVecLin) = s at hr
    rw [← hsp, hfr] at hr
    exact hr
  let pick : I → Fin m := fun v => (hI_sub v.2).choose
  have hpick_col : ∀ v : I, M.col (pick v) = v.1 := fun v => (hI_sub v.2).choose_spec
  have hpick_inj : Function.Injective pick := by
    intro a b hab
    apply Subtype.ext
    rw [← hpick_col a, ← hpick_col b, hab]
  let T : Finset (Fin m) := Finset.univ.image pick
  have hT_card : T.card = s := by
    rw [Finset.card_image_of_injective _ hpick_inj, Finset.card_univ, hcard_I]
  refine ⟨T, hT_card, ?_⟩
  have heq_I : ∀ y : T, ∃ v : I, pick v = y.1 := fun y => by
    rcases Finset.mem_image.mp y.2 with ⟨v, _, hv⟩
    exact ⟨v, hv⟩
  let e : T ≃ I :=
    { toFun := fun y => (heq_I y).choose
      invFun := fun v => ⟨pick v, Finset.mem_image.mpr ⟨v, Finset.mem_univ _, rfl⟩⟩
      left_inv := fun y => Subtype.ext (heq_I y).choose_spec
      right_inv := fun v => hpick_inj (heq_I ⟨pick v, _⟩).choose_spec }
  have hcomp := hI_li.comp e e.injective
  have hfun : (fun x : T => M.col x.1) = Subtype.val ∘ e := by
    funext y
    change M.col y.1 = (e y).1
    rw [← hpick_col (e y)]
    exact congrArg M.col (heq_I y).choose_spec.symm
  rwa [hfun]

/-- Helper: any `n × m` matrix of full row rank `n` has an invertible `n × n` column submatrix. -/
private theorem exists_full_rank_col_submatrix {F : Type*} [Field F] {n m : ℕ}
    (M : Matrix (Fin n) (Fin m) F) (hr : M.rank = n) :
    ∃ S : Set.powersetCard (Fin m) n,
      (M.submatrix id (Set.powersetCard.ofFinEmbEquiv.symm S)).det ≠ 0 := by
  obtain ⟨T, hT_card, hT_li⟩ := exists_linearIndependent_cols M hr
  let S : Set.powersetCard (Fin m) n := Set.powersetCard.ofCard hT_card
  refine ⟨S, ?_⟩
  rw [det_submatrix_ne_zero_iff_linearIndependent, linearIndependent_cols_coe_iff]
  have hval : S.val = T := Set.powersetCard.val_ofCard hT_card
  exact hT_li.comp (fun x : S.val => (⟨x.1, hval ▸ x.2⟩ : T))
    (fun a b h => Subtype.ext (congrArg Subtype.val h))

/-- Every `n × m` matrix `M` of full row rank `n` over a field has a unique `n`-element column
subset `S` maximizing `subsetWeight S` subject to `det(M_S) ≠ 0`. -/
theorem exists_unique_max_weight_full_rank_submatrix {F : Type*} [Field F] {n m : ℕ}
    (M : Matrix (Fin n) (Fin m) F) (hr : M.rank = n) :
    ∃ S : Set.powersetCard (Fin m) n,
      (M.submatrix id (Set.powersetCard.ofFinEmbEquiv.symm S)).det ≠ 0 ∧
      ∀ T : Set.powersetCard (Fin m) n,
        (M.submatrix id (Set.powersetCard.ofFinEmbEquiv.symm T)).det ≠ 0 →
        T ≠ S → subsetWeight T < subsetWeight S := by
  classical
  let good : Finset (Set.powersetCard (Fin m) n) :=
    Finset.univ.filter fun S => (M.submatrix id (Set.powersetCard.ofFinEmbEquiv.symm S)).det ≠ 0
  have hne : good.Nonempty := by
    obtain ⟨S0, hS0⟩ := exists_full_rank_col_submatrix M hr
    exact ⟨S0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hS0⟩⟩
  obtain ⟨S, hS_mem, hS_max⟩ := Finset.exists_max_image good subsetWeight hne
  have hS_det : (M.submatrix id (Set.powersetCard.ofFinEmbEquiv.symm S)).det ≠ 0 :=
    (Finset.mem_filter.mp hS_mem).2
  refine ⟨S, hS_det, fun T hT_det hTS => ?_⟩
  have hT_le : subsetWeight T ≤ subsetWeight S :=
    hS_max T (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hT_det⟩)
  refine lt_of_le_of_ne hT_le fun hEq => ?_
  have exchange_step : ∀ (A B : Set.powersetCard (Fin m) n),
      (M.submatrix id (Set.powersetCard.ofFinEmbEquiv.symm A)).det ≠ 0 →
      (M.submatrix id (Set.powersetCard.ofFinEmbEquiv.symm B)).det ≠ 0 →
      ∀ k ∈ B.val \ A.val, (∀ l ∈ A.val \ B.val, k < l) →
      ∃ C : Set.powersetCard (Fin m) n,
        (M.submatrix id (Set.powersetCard.ofFinEmbEquiv.symm C)).det ≠ 0 ∧
        subsetWeight B < subsetWeight C := by
    intro A B hAdet hBdet k hk hkl
    have hkB : k ∈ B.val := (Finset.mem_sdiff.mp hk).1
    have hkA : k ∉ A.val := (Finset.mem_sdiff.mp hk).2
    have hFB_card : B.val.card = n := Set.powersetCard.card_eq B
    have hFA_card : A.val.card = n := Set.powersetCard.card_eq A
    have hliA : LinearIndependent F (fun x : A.val => M.col x.1) :=
      (linearIndependent_cols_coe_iff M A).mp
        ((det_submatrix_ne_zero_iff_linearIndependent M A).mp hAdet)
    have hliB : LinearIndependent F (fun x : B.val => M.col x.1) :=
      (linearIndependent_cols_coe_iff M B).mp
        ((det_submatrix_ne_zero_iff_linearIndependent M B).mp hBdet)
    let W : Submodule F (Fin n → F) :=
      Submodule.span F (M.col '' ((B.val.erase k : Finset (Fin m)) : Set (Fin m)))
    have hW_lt : Module.finrank F W < n := by
      have hW_eq : W = Submodule.span F
          (((B.val.erase k).image M.col : Finset (Fin n → F)) : Set (Fin n → F)) := by
        simp [W, Finset.coe_image]
      calc
        Module.finrank F W ≤ ((B.val.erase k).image M.col).card := by
          rw [hW_eq]
          have hc := finrank_span_le_card (R := F)
            (((B.val.erase k).image M.col : Finset (Fin n → F)) : Set (Fin n → F))
          have htf : (((B.val.erase k).image M.col : Finset (Fin n → F)) :
              Set (Fin n → F)).toFinset = (B.val.erase k).image M.col := by
            ext x; rw [Set.mem_toFinset, Finset.mem_coe]
          rwa [htf] at hc
        _ ≤ (B.val.erase k).card := Finset.card_image_le
        _ = n - 1 := by rw [Finset.card_erase_of_mem hkB, hFB_card]
        _ < n := by
            have hpos : 0 < B.val.card := Finset.card_pos.mpr ⟨k, hkB⟩
            omega
    have hex_l : ∃ l ∈ A.val, M.col l ∉ W := by
      by_contra hall
      push Not at hall
      have hspanA : Submodule.span F (Set.range fun x : A.val => M.col x.1) ≤ W := by
        rw [Submodule.span_le]
        rintro _ ⟨⟨l, hl⟩, rfl⟩
        exact hall l hl
      have hfrA :
          Module.finrank F (Submodule.span F (Set.range fun x : A.val => M.col x.1)) = n := by
        rw [finrank_span_eq_card hliA, Fintype.card_coe, hFA_card]
      have hle := Submodule.finrank_mono hspanA
      omega
    obtain ⟨l, hlA, hlW⟩ := hex_l
    have hlB : l ∉ B.val := by
      intro hmem
      have hne_lk : l ≠ k := fun h => hkA (h ▸ hlA)
      exact hlW (Submodule.subset_span
        ⟨l, Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hne_lk, hmem⟩), rfl⟩)
    let FC : Finset (Fin m) := insert l (B.val.erase k)
    have hl_not_erase : l ∉ B.val.erase k := fun h => hlB (Finset.mem_of_mem_erase h)
    have hFC_card : FC.card = n := by
      rw [Finset.card_insert_of_notMem hl_not_erase, Finset.card_erase_of_mem hkB, hFB_card]
      have hpos : 0 < B.val.card := Finset.card_pos.mpr ⟨k, hkB⟩
      omega
    let C : Set.powersetCard (Fin m) n := Set.powersetCard.ofCard hFC_card
    have hC_val : C.val = FC := Set.powersetCard.val_ofCard hFC_card
    have hliC : LinearIndependent F (fun x : FC => M.col x.1) := by
      rw [Fintype.linearIndependent_iff]
      intro c hc x
      have hcl : c ⟨l, Finset.mem_insert_self l _⟩ = 0 := by
        by_contra hne0
        have hmemW : M.col l ∈ W := by
          have hsum := hc
          rw [← Finset.add_sum_erase _ _
            (Finset.mem_univ (⟨l, Finset.mem_insert_self l _⟩ : FC))] at hsum
          have hmul : c ⟨l, Finset.mem_insert_self l _⟩ • M.col l =
              -(∑ y ∈ Finset.univ.erase (⟨l, Finset.mem_insert_self l _⟩ : FC),
                c y • M.col y.1) :=
            eq_neg_of_add_eq_zero_left hsum
          have hcol_eq : M.col l =
              (c ⟨l, Finset.mem_insert_self l _⟩)⁻¹ •
                -(∑ y ∈ Finset.univ.erase (⟨l, Finset.mem_insert_self l _⟩ : FC),
                  c y • M.col y.1) := by
            rw [← hmul, inv_smul_smul₀ hne0]
          rw [hcol_eq]
          refine Submodule.smul_mem W _ (Submodule.neg_mem W (Submodule.sum_mem W fun y hy => ?_))
          have hy_ne : y.1 ≠ l := fun h => (Finset.mem_erase.mp hy).1 (Subtype.ext h)
          have hy_er : y.1 ∈ B.val.erase k := (Finset.mem_insert.mp y.2).resolve_left hy_ne
          exact Submodule.smul_mem W _
            (Submodule.subset_span ⟨y.1, Finset.mem_coe.mpr hy_er, rfl⟩)
        exact hlW hmemW
      by_cases hxl : x.1 = l
      · convert hcl
      · have hx_er : x.1 ∈ B.val.erase k := (Finset.mem_insert.mp x.2).resolve_left hxl
        have hxB : x.1 ∈ B.val := Finset.mem_of_mem_erase hx_er
        let cB : B.val → F := fun y =>
          if hy : y.1 ∈ FC then c ⟨y.1, hy⟩ else 0
        have hsumB : ∑ y : B.val, cB y • M.col y.1 = 0 := by
          have h1 : ∑ y : FC, c y • M.col y.1 =
              ∑ y ∈ (Finset.univ : Finset FC).erase ⟨l, Finset.mem_insert_self l _⟩,
                c y • M.col y.1 := by
            rw [← Finset.add_sum_erase _ _
              (Finset.mem_univ (⟨l, Finset.mem_insert_self l _⟩ : FC)),
              hcl, zero_smul, zero_add]
          rw [← hc, h1]
          symm
          refine Finset.sum_bij_ne_zero
            (fun y hy _ => ⟨y.1, Finset.mem_of_mem_erase ((Finset.mem_insert.mp y.2).resolve_left
              (fun h => (Finset.mem_erase.mp hy).1 (Subtype.ext h)))⟩) ?_ ?_ ?_ ?_
          · intro _ _ _; exact Finset.mem_univ _
          · intro _ _ _ _ _ _ h; exact Subtype.ext (by simpa using congrArg Subtype.val h)
          · intro y _ hnz
            have hyC : y.1 ∈ FC := by
              by_contra hnot
              simp [cB, hnot] at hnz
            have hyl : y.1 ≠ l := fun h => hlB (h ▸ y.2)
            refine ⟨⟨y.1, hyC⟩, Finset.mem_erase.mpr ⟨fun h => hyl (congrArg Subtype.val h),
              Finset.mem_univ _⟩, ?_, Subtype.ext rfl⟩
            simpa [cB, hyC] using hnz
          · intro y _ _; simp [cB, y.2]
        have hcB0 := Fintype.linearIndependent_iff.mp hliB cB hsumB ⟨x.1, hxB⟩
        simpa [cB, x.2] using hcB0
    have hC_det : (M.submatrix id (Set.powersetCard.ofFinEmbEquiv.symm C)).det ≠ 0 := by
      rw [det_submatrix_ne_zero_iff_linearIndependent, linearIndependent_cols_coe_iff]
      exact hliC
    refine ⟨C, hC_det, ?_⟩
    rw [subsetWeight_eq_sum_finset B, subsetWeight_eq_sum_finset C, hC_val]
    have hlt_kl : k.1 < l.1 := hkl l (Finset.mem_sdiff.mpr ⟨hlA, hlB⟩)
    have hsumB : ∑ x ∈ B.val, x.1 = k.1 + ∑ x ∈ B.val.erase k, x.1 :=
      (Finset.add_sum_erase B.val (fun x : Fin m => x.1) hkB).symm
    have hsumC : ∑ x ∈ FC, x.1 = l.1 + ∑ x ∈ B.val.erase k, x.1 :=
      Finset.sum_insert hl_not_erase
    omega
  let symDiff : Finset (Fin m) := (S.val \ T.val) ∪ (T.val \ S.val)
  have hsym_ne : symDiff.Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty] at hempty
    apply hTS
    apply Subtype.ext
    ext x
    constructor
    · intro hx
      by_contra hnot
      have : x ∈ symDiff := Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hx, hnot⟩)
      rw [hempty] at this; exact Finset.notMem_empty _ this
    · intro hx
      by_contra hnot
      have : x ∈ symDiff := Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hx, hnot⟩)
      rw [hempty] at this; exact Finset.notMem_empty _ this
  let k := symDiff.min' hsym_ne
  have hk_mem : k ∈ symDiff := Finset.min'_mem symDiff hsym_ne
  rcases Finset.mem_union.mp hk_mem with hkST | hkTS
  · obtain ⟨C, hCdet, hCgt⟩ := exchange_step T S hT_det hS_det k hkST (fun l hl => by
      have hle : k ≤ l := Finset.min'_le symDiff l (Finset.mem_union_right _ hl)
      have hne : k ≠ l := fun h => (Finset.mem_sdiff.mp hkST).2 (h ▸ (Finset.mem_sdiff.mp hl).1)
      exact lt_of_le_of_ne hle hne)
    have hCle := hS_max C (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hCdet⟩)
    omega
  · obtain ⟨C, hCdet, hCgt⟩ := exchange_step S T hS_det hT_det k hkTS (fun l hl => by
      have hle : k ≤ l := Finset.min'_le symDiff l (Finset.mem_union_left _ hl)
      have hne : k ≠ l := fun h => (Finset.mem_sdiff.mp hkTS).2 (h ▸ (Finset.mem_sdiff.mp hl).1)
      exact lt_of_le_of_ne hle hne)
    have hCle := hS_max C (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hCdet⟩)
    omega

/-- The Vandermonde-type rank-preserving matrix `A_α ∈ K^{r × n}` with entries `(g^i * α)^j`. -/
@[expose] def rankPreservingMat {K : Type*} [CommSemiring K] (r n : ℕ) (g α : K) :
    Matrix (Fin r) (Fin n) K :=
  Matrix.of fun i j => (g ^ i.1 * α) ^ j.1

/-- Weight upper bound: any `r`-element subset `S` of `Fin n` has
`subsetWeight S ≤ n * r - (r + 1).choose 2`. -/
theorem subsetWeight_le_mul_sub_choose {n r : ℕ} (_hrn : r ≤ n)
    (S : Set.powersetCard (Fin n) r) :
    subsetWeight S ≤ n * r - (r + 1).choose 2 := by
  let f := Set.powersetCard.ofFinEmbEquiv.symm S
  have hbound : ∀ i : Fin r, (f i).1 + (r - i.1) ≤ n := by
    intro i
    have hsub : ∀ (k : ℕ) (hk : i.1 + k < r), (f i).1 + k ≤ (f ⟨i.1 + k, hk⟩).1 := by
      intro k
      induction k with
      | zero => intro _; simp
      | succ k ih =>
          intro hk
          have hprev := ih (by omega)
          have hlt : f ⟨i.1 + k, by omega⟩ < f ⟨i.1 + (k + 1), hk⟩ :=
            f.strictMono (Fin.mk_lt_mk.mpr (by omega))
          have hlt' : (f ⟨i.1 + k, by omega⟩).1 < (f ⟨i.1 + (k + 1), hk⟩).1 := hlt
          omega
    have hlast := hsub (r - 1 - i.1) (by omega)
    have hlt_n : (f ⟨i.1 + (r - 1 - i.1), by omega⟩).1 < n := (f _).isLt
    omega
  have hsum_le : subsetWeight S + ∑ i : Fin r, (r - i.1) ≤ n * r := by
    calc
      subsetWeight S + ∑ i : Fin r, (r - i.1)
        = ∑ i : Fin r, ((f i).1 + (r - i.1)) := (Finset.sum_add_distrib).symm
      _ ≤ ∑ _i : Fin r, n := Finset.sum_le_sum fun i _ => hbound i
      _ = n * r := by simp [mul_comm]
  have hsum_tri : ∑ i : Fin r, (r - i.1) = (r + 1).choose 2 := by
    have hrev : ∑ i : Fin r, (r - i.1) = ∑ i : Fin r, (i.1 + 1) := by
      rw [← Equiv.sum_comp (Fin.revPerm (n := r))]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Fin.revPerm_apply, Fin.val_rev]
      omega
    rw [hrev, sum_succ_eq_choose_two]
  omega

/-- Monotonicity of `n * s - (s + 1).choose 2` for `s ≤ r ≤ n`. -/
theorem mul_sub_choose_le_of_le {n s r : ℕ} (hsr : s ≤ r) (hrn : r ≤ n) :
    n * s - (s + 1).choose 2 ≤ n * r - (r + 1).choose 2 := by
  have hstep : ∀ k, k < n → n * k - (k + 1).choose 2 ≤ n * (k + 1) - (k + 2).choose 2 := by
    intro k hk
    have htri : (k + 1).choose 2 ≤ n * k := by
      have h1 : 2 * (k + 1).choose 2 = (k + 1) * k := by
        simpa using two_mul_choose_two (k + 1)
      have h2 : (k + 1) * k ≤ 2 * (n * k) := by nlinarith
      omega
    have hchoose : (k + 2).choose 2 = (k + 1).choose 2 + (k + 1) := by
      rw [Nat.choose_succ_succ, Nat.choose_one_right, add_comm]
    have hmul : n * (k + 1) = n * k + n := by ring
    omega
  induction hsr with
  | refl => exact le_rfl
  | @step m hsm ih =>
      exact le_trans (ih (by omega)) (hstep m (by omega))

/-- Rank-preserving matrix theorem: if `1 ≤ r ≤ n`, `M ∈ F^{n × r}` has full rank `r`, and
`g ∈ K` has multiplicative order at least `n`, then outside a finite set `bad : Finset K` of
cardinality at most `n * r - (r + 1).choose 2 < n * r`, the product
`rankPreservingMat r n g α * M` has full rank `r`. -/
theorem rank_rankPreservingMat_mul_eq {F K : Type*} [Field F] [Field K] [Algebra F K]
    {n r : ℕ} (hr : 1 ≤ r) (hrn : r ≤ n)
    (M : Matrix (Fin n) (Fin r) F) (hMrank : M.rank = r)
    {g : K} (hg : HasMultOrderGe g n) :
    ∃ bad : Finset K,
      bad.card ≤ n * r - (r + 1).choose 2 ∧
      bad.card < n * r ∧
      ∀ α : K, α ∉ bad →
        (rankPreservingMat r n g α * M.map (algebraMap F K)).rank = r := by
  classical
  let A_X : Matrix (Fin r) (Fin n) K[X] :=
    Matrix.of fun i j => (Polynomial.C (g ^ i.1) * Polynomial.X) ^ j.1
  let M_K : Matrix (Fin n) (Fin r) K := M.map (algebraMap F K)
  let M_X : Matrix (Fin n) (Fin r) K[X] := M_K.map Polynomial.C
  let P : K[X] := (A_X * M_X).det
  have hM_K_rank : M_K.rank = r := by
    rw [Matrix.rank_map_of_field]; exact hMrank
  have hM_KT_rank : M_Kᵀ.rank = r := by
    rw [Matrix.rank_transpose]; exact hM_K_rank
  have hP_cb : P = ∑ S : Set.powersetCard (Fin n) r,
      Polynomial.C ((Matrix.vandermonde fun k : Fin r =>
          g ^ (Set.powersetCard.ofFinEmbEquiv.symm S k).1).det *
        (M_K.submatrix (Set.powersetCard.ofFinEmbEquiv.symm S) id).det) *
      Polynomial.X ^ (subsetWeight S) := by
    dsimp only [P]
    rw [Matrix.det_mul_eq_sum_powersetCard]
    refine Finset.sum_congr rfl fun S _ => ?_
    let f := Set.powersetCard.ofFinEmbEquiv.symm S
    have hA_fac : A_X.submatrix id f =
        (Matrix.vandermonde fun k : Fin r => Polynomial.C (g ^ (f k).1))ᵀ *
        Matrix.diagonal (fun k : Fin r => (Polynomial.X : K[X]) ^ (f k).1) := by
      ext i k
      simp only [Matrix.submatrix_apply, id_eq, A_X, Matrix.of_apply, Matrix.mul_diagonal,
        Matrix.transpose_apply, Matrix.vandermonde_apply, mul_pow, ← map_pow]
      rw [← pow_mul, ← pow_mul, mul_comm i.1 (f k).1]
    have hA_det : (A_X.submatrix id f).det =
        Polynomial.C (Matrix.vandermonde fun k : Fin r => g ^ (f k).1).det *
          Polynomial.X ^ (subsetWeight S) := by
      rw [hA_fac, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal]
      have hvand : (Matrix.vandermonde fun k : Fin r => Polynomial.C (g ^ (f k).1)).det =
          Polynomial.C (Matrix.vandermonde fun k : Fin r => g ^ (f k).1).det := by
        rw [Matrix.det_vandermonde, Matrix.det_vandermonde, map_prod]
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [map_prod]
        refine Finset.prod_congr rfl fun j _ => by simp
      rw [hvand, Finset.prod_pow_eq_pow_sum]
      rfl
    have hM_det : (M_X.submatrix f id).det = Polynomial.C (M_K.submatrix f id).det := by
      have : M_X.submatrix f id = (M_K.submatrix f id).map Polynomial.C := by ext i j; rfl
      rw [this, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    rw [hA_det, hM_det, map_mul]
    ring
  obtain ⟨Sstar, hSstar_detT, hSstar_uniq⟩ :=
    exists_unique_max_weight_full_rank_submatrix M_Kᵀ hM_KT_rank
  have hdet_trans : ∀ S : Set.powersetCard (Fin n) r,
      (M_Kᵀ.submatrix id (Set.powersetCard.ofFinEmbEquiv.symm S)).det =
        (M_K.submatrix (Set.powersetCard.ofFinEmbEquiv.symm S) id).det := fun S => by
    rw [← Matrix.det_transpose]; rfl
  have hSstar_det : (M_K.submatrix (Set.powersetCard.ofFinEmbEquiv.symm Sstar) id).det ≠ 0 := by
    rwa [← hdet_trans]
  have hP_ne : P ≠ 0 := by
    intro h0
    have hcoeff0 : P.coeff (subsetWeight Sstar) = 0 := by rw [h0, Polynomial.coeff_zero]
    rw [hP_cb] at hcoeff0
    change (Polynomial.lcoeff K (subsetWeight Sstar)) _ = 0 at hcoeff0
    rw [map_sum, Finset.sum_eq_single Sstar] at hcoeff0
    · rw [Polynomial.lcoeff_apply, Polynomial.coeff_C_mul_X_pow] at hcoeff0
      simp only [↓reduceIte] at hcoeff0
      have hv_ne : (Matrix.vandermonde fun k : Fin r =>
          g ^ (Set.powersetCard.ofFinEmbEquiv.symm Sstar k).1).det ≠ 0 := by
        rw [Matrix.det_vandermonde_ne_zero_iff]
        intro a b hab
        exact (Set.powersetCard.ofFinEmbEquiv.symm Sstar).injective (hg.pow_injective hab)
      exact mul_ne_zero hv_ne hSstar_det hcoeff0
    · intro S _ hSne
      rw [Polynomial.lcoeff_apply, Polynomial.coeff_C_mul_X_pow]
      by_cases hdetS : (M_K.submatrix (Set.powersetCard.ofFinEmbEquiv.symm S) id).det = 0
      · simp [hdetS]
      · have hdetST : (M_Kᵀ.submatrix id (Set.powersetCard.ofFinEmbEquiv.symm S)).det ≠ 0 := by
          rwa [hdet_trans]
        have hlt := hSstar_uniq S hdetST hSne
        have hne_w : subsetWeight Sstar ≠ subsetWeight S := ne_of_gt hlt
        simp [hne_w]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hP_deg : P.natDegree ≤ n * r - (r + 1).choose 2 := by
    rw [hP_cb]
    refine le_trans (Polynomial.natDegree_sum_le _ _) ?_
    rw [Finset.fold_max_le]
    refine ⟨Nat.zero_le _, fun S _ => ?_⟩
    calc
      (Polynomial.C _ * Polynomial.X ^ subsetWeight S).natDegree
        ≤ (Polynomial.C ((Matrix.vandermonde fun k : Fin r =>
              g ^ (Set.powersetCard.ofFinEmbEquiv.symm S k).1).det *
            (M_K.submatrix (Set.powersetCard.ofFinEmbEquiv.symm S) id).det)).natDegree +
            ((Polynomial.X : K[X]) ^ subsetWeight S).natDegree := Polynomial.natDegree_mul_le
      _ ≤ 0 + subsetWeight S := Nat.add_le_add (le_of_eq (Polynomial.natDegree_C _)) (by simp)
      _ = subsetWeight S := zero_add _
      _ ≤ n * r - (r + 1).choose 2 := subsetWeight_le_mul_sub_choose hrn S
  have hP_eval : ∀ α : K, P.eval α = (rankPreservingMat r n g α * M_K).det := by
    intro α
    change (Polynomial.evalRingHom α) (A_X * M_X).det = _
    rw [RingHom.map_det, RingHom.mapMatrix_apply, Matrix.map_mul]
    congr 1; congr 1
    · ext i j; simp [A_X, rankPreservingMat]
    · ext i j; simp [M_X]
  let bad : Finset K := P.roots.toFinset
  have hchoose_pos : 0 < (r + 1).choose 2 := by
    have h2 : 2 * (r + 1).choose 2 = (r + 1) * r := by simpa using two_mul_choose_two (r + 1)
    have hmul : 2 ≤ (r + 1) * r := by nlinarith
    omega
  have hnr_pos : (r + 1).choose 2 ≤ n * r := by
    have h2 : 2 * (r + 1).choose 2 = (r + 1) * r := by simpa using two_mul_choose_two (r + 1)
    have hmul : (r + 1) * r ≤ 2 * (n * r) := by nlinarith
    omega
  have hbad_le : bad.card ≤ n * r - (r + 1).choose 2 := by
    calc
      bad.card ≤ P.roots.card := Multiset.toFinset_card_le _
      _ ≤ P.natDegree := Polynomial.card_roots' P
      _ ≤ n * r - (r + 1).choose 2 := hP_deg
  refine ⟨bad, hbad_le, by omega, fun α hα => ?_⟩
  have hne0 : (rankPreservingMat r n g α * M_K).det ≠ 0 := by
    rw [← hP_eval α]
    intro h0
    apply hα
    exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hP_ne).mpr h0)
  apply le_antisymm (Matrix.rank_le_height _)
  have h1 : (1 : Matrix (Fin r) (Fin r) K).rank ≤ (rankPreservingMat r n g α * M_K).rank := by
    have hinv := Matrix.nonsing_inv_mul (rankPreservingMat r n g α * M_K)
      (isUnit_iff_ne_zero.mpr hne0)
    rw [← hinv]
    exact Matrix.rank_mul_le_right _ _
  simpa [Matrix.rank_one] using h1

/-- Leading-rows extension of `rank_rankPreservingMat_mul_eq`: for `1 ≤ s ≤ r ≤ n` and any
`M ∈ F^{n × r'}` of rank `s`, outside at most `n * r - (r + 1).choose 2 < n * r` values of `α ∈ K`,
both the first `s` rows of `rankPreservingMat r n g α * M` and the full product have rank `s`. -/
theorem rank_rankPreservingMat_mul_leading_rows_eq {F K : Type*} [Field F] [Field K] [Algebra F K]
    {n r r' s : ℕ} (hs : 1 ≤ s) (hsr : s ≤ r) (hrn : r ≤ n)
    (M : Matrix (Fin n) (Fin r') F) (hMrank : M.rank = s)
    {g : K} (hg : HasMultOrderGe g n) :
    ∃ bad : Finset K,
      bad.card ≤ n * r - (r + 1).choose 2 ∧
      bad.card < n * r ∧
      ∀ α : K, α ∉ bad →
        ((rankPreservingMat r n g α * M.map (algebraMap F K)).submatrix
          (fun i : Fin s => ⟨i.1, lt_of_lt_of_le i.2 hsr⟩) id).rank = s ∧
        (rankPreservingMat r n g α * M.map (algebraMap F K)).rank = s := by
  classical
  obtain ⟨T, hT_card, hT_li⟩ := exists_linearIndependent_cols M hMrank
  let eT : Fin s ≃ T := (Fintype.equivFinOfCardEq (by simpa using hT_card)).symm
  let colIdx : Fin s → Fin r' := fun k => (eT k).1
  let M' : Matrix (Fin n) (Fin s) F := M.submatrix id colIdx
  have hM'_rank : M'.rank = s := by
    have hli' : LinearIndependent F (fun j : Fin s => M'.col j) := by
      have hcomp := hT_li.comp eT eT.injective
      convert hcomp using 1
      funext j i; rfl
    have hspan_eq : LinearMap.range M'.mulVecLin = Submodule.span F (Set.range M'.col) :=
      Matrix.range_mulVecLin M'
    change Module.finrank F (LinearMap.range M'.mulVecLin) = s
    rw [hspan_eq, finrank_span_eq_card hli', Fintype.card_fin]
  obtain ⟨bad, hbad_s, _, hgood⟩ :=
    rank_rankPreservingMat_mul_eq (K := K) hs (le_trans hsr hrn) M' hM'_rank hg
  have hbad_r : bad.card ≤ n * r - (r + 1).choose 2 :=
    le_trans hbad_s (mul_sub_choose_le_of_le hsr hrn)
  have hchoose_pos : 0 < (r + 1).choose 2 := by
    have h2 : 2 * (r + 1).choose 2 = (r + 1) * r := by simpa using two_mul_choose_two (r + 1)
    have hmul : 2 ≤ (r + 1) * r := by nlinarith
    omega
  have hnr_pos : (r + 1).choose 2 ≤ n * r := by
    have h2 : 2 * (r + 1).choose 2 = (r + 1) * r := by simpa using two_mul_choose_two (r + 1)
    have hmul : (r + 1) * r ≤ 2 * (n * r) := by nlinarith
    omega
  refine ⟨bad, hbad_r, by omega, fun α hα => ?_⟩
  have hM'_good := hgood α hα
  have hsub_eq : ((rankPreservingMat r n g α * M.map (algebraMap F K)).submatrix
      (fun i : Fin s => ⟨i.1, lt_of_lt_of_le i.2 hsr⟩) id).submatrix id colIdx =
      rankPreservingMat s n g α * M'.map (algebraMap F K) := by
    ext i j
    simp [Matrix.mul_apply, rankPreservingMat, M']
  have hlead_ge : s ≤ ((rankPreservingMat r n g α * M.map (algebraMap F K)).submatrix
      (fun i : Fin s => ⟨i.1, lt_of_lt_of_le i.2 hsr⟩) id).rank := by
    calc
      s = (rankPreservingMat s n g α * M'.map (algebraMap F K)).rank := hM'_good.symm
      _ = (((rankPreservingMat r n g α * M.map (algebraMap F K)).submatrix
            (fun i : Fin s => ⟨i.1, lt_of_lt_of_le i.2 hsr⟩) id).submatrix id colIdx).rank := by
          rw [hsub_eq]
      _ ≤ ((rankPreservingMat r n g α * M.map (algebraMap F K)).submatrix
            (fun i : Fin s => ⟨i.1, lt_of_lt_of_le i.2 hsr⟩) id).rank :=
          Matrix.rank_submatrix_le _ _ _
  have hlead_le : ((rankPreservingMat r n g α * M.map (algebraMap F K)).submatrix
      (fun i : Fin s => ⟨i.1, lt_of_lt_of_le i.2 hsr⟩) id).rank ≤ s :=
    Matrix.rank_le_height _
  have hfull_le : (rankPreservingMat r n g α * M.map (algebraMap F K)).rank ≤ s := by
    calc
      (rankPreservingMat r n g α * M.map (algebraMap F K)).rank
        ≤ (M.map (algebraMap F K)).rank := Matrix.rank_mul_le_right _ _
      _ = M.rank := by rw [Matrix.rank_map_of_field]
      _ = s := hMrank
  have hfull_ge : s ≤ (rankPreservingMat r n g α * M.map (algebraMap F K)).rank := by
    calc
      s ≤ ((rankPreservingMat r n g α * M.map (algebraMap F K)).submatrix
            (fun i : Fin s => ⟨i.1, lt_of_lt_of_le i.2 hsr⟩) id).rank := hlead_ge
      _ ≤ (rankPreservingMat r n g α * M.map (algebraMap F K)).rank :=
          Matrix.rank_submatrix_le _ _ _
  exact ⟨le_antisymm hlead_le hlead_ge, le_antisymm hfull_le hfull_ge⟩

end

end CslibFrontier
