module

public import CslibFrontier.Crypto.Primitives.PRG.NisanWigderson
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Sign-Orthogonal Matrices and Designs from Finite Affine Planes

This module develops sign-orthogonal `{0, 1, -1}` matrices (`IsSignOrthogonalMatrix`), their
row-normalized unitaries (`normalizedRowMatrix`), and two explicit geometric constructions of
pairwise orthogonal `{0, 1, -1}`-vectors whose supports form combinatorial `(ℓ, p)`-designs:

1. **Paired-lines construction**: over any finite field `F` equipped with an equipartition
   `Equipartition F` (`|F| = q` even, in particular `GaloisField 2 n`), the `q ^ 2 / 2` vectors
   `pairedLinesVec` supported on parallel line pairs in `F × F` are pairwise orthogonal and their
   supports form a `(2q, 4)`-design (`pairedLinesDesign`).
2. **Punctured-plane all-rows construction**: over any finite field `F` of odd cardinality `q`
   with a half-set `Q ⊆ Fˣ` (`Q ∩ (-Q) = ∅`, `Q ∪ (-Q) = Fˣ`), the `q ^ 2 - 1` vectors
   `allRowsVec` on `(F × F) \ {(0, 0)}` are pairwise orthogonal, their supports form a
   `(q, 2)`-design (`allRowsDesign`), and their row-normalized matrix forms a full
   `(q ^ 2 - 1) × (q ^ 2 - 1)` unitary (`allRowsUnitary`).

## Main definitions

* `rowSupport`, `IsSignOrthogonalMatrix`, `normalizedRowMatrix`: row-support and unitary
  normalization of pairwise orthogonal `{0, 1, -1}`-matrices.
* `Equipartition`, `pairedLinesVec`, `pairedLinesSupport`, `pairedLinesDesign`: paired-lines
  orthogonal family and `(2q, 4)`-design.
* `OddFieldHalfSet`, `PuncturedPlane`, `AllRowsIndex`, `allRowsVec`, `allRowsDesign`,
  `allRowsMatrix`, `allRowsUnitary`: full-rank `(q ^ 2 - 1) × (q ^ 2 - 1)` sign-orthogonal matrix
  and `(q, 2)`-design over odd finite fields.

## Main results

* `pairedLinesVec_orthogonal`, `card_pairedLinesSupport`, `card_pairedLinesSupport_inter_le`,
  `exists_pairedLines_design_gf2`.
* `oddFieldHalfSetOfOdd`, `allRowsVec_orthogonal`, `card_allRowsSupport`,
  `allRowsVec_inter_and_orthogonal`, `allRowsMatrix_isSignOrthogonal`.
-/

public section

namespace CslibFrontier.Foundations.Combinatorics.Design

open Cslib.Crypto.PRG.NisanWigderson (Design)
open Finset Matrix
open scoped BigOperators

/-- Support `S(A, i) = {j | A_{i,j} ≠ 0}` of row `i` of a matrix `A`. -/
@[expose] def rowSupport {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℤ) (i : ι) : Finset ι :=
  Finset.univ.filter fun j => A i j ≠ 0

theorem mem_rowSupport {ι : Type*} [Fintype ι] (A : Matrix ι ι ℤ) (i j : ι) :
    j ∈ rowSupport A i ↔ A i j ≠ 0 := by
  simp [rowSupport]

/-- An `N × N` matrix `A` with entries in `{0, 1, -1}` whose rows are nonzero and pairwise
orthogonal. -/
structure IsSignOrthogonalMatrix {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℤ) : Prop where
  /-- Every entry lies in `{0, 1, -1}`. -/
  entries : ∀ i j, A i j = 0 ∨ A i j = 1 ∨ A i j = -1
  /-- Every row has nonempty support (needed to scale by `1 / √|S(A, i)|`). -/
  row_nonempty : ∀ i, (rowSupport A i).Nonempty
  /-- Distinct rows are pairwise orthogonal. -/
  rows_orthogonal : ∀ i j, i ≠ j → ∑ k, A i k * A j k = 0

/-- Row-normalized matrix `Ā` obtained by scaling row `i` of `A` by `1 / √|S(A, i)|`,
shown to be unitary. -/
noncomputable def normalizedRowMatrix {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℤ) (hA : IsSignOrthogonalMatrix A) : Matrix.unitaryGroup ι ℂ :=
  ⟨Matrix.of fun i j => ((A i j : ℝ) / Real.sqrt (#(rowSupport A i) : ℝ) : ℂ), by
    rw [Matrix.mem_unitaryGroup_iff]
    ext i j
    rw [Matrix.mul_apply, Matrix.one_apply]
    have hterm_star : ∀ k,
        (Matrix.of fun i j => ((A i j : ℝ) / Real.sqrt (#(rowSupport A i) : ℝ) : ℂ)) i k *
          star (Matrix.of fun i j => ((A i j : ℝ) / Real.sqrt (#(rowSupport A i) : ℝ) : ℂ)) k j =
        (((A i k : ℝ) * (A j k : ℝ) /
          (Real.sqrt (#(rowSupport A i) : ℝ) * Real.sqrt (#(rowSupport A j) : ℝ)) : ℝ) : ℂ) := by
      intro k
      rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply, Matrix.of_apply,
        Matrix.of_apply, RCLike.star_def, map_div₀, Complex.conj_ofReal, Complex.conj_ofReal]
      push_cast
      ring
    simp_rw [hterm_star]
    rw [← Complex.ofReal_sum, ← Finset.sum_div]
    by_cases hij : i = j
    · subst hij
      have hcard_pos : (0 : ℝ) < (#(rowSupport A i) : ℝ) := by
        exact_mod_cast (hA.row_nonempty i).card_pos
      have hsum_sq : ∑ k, (A i k : ℝ) * (A i k : ℝ) = (#(rowSupport A i) : ℝ) := by
        have hterm : ∀ k, (A i k : ℝ) * (A i k : ℝ) = if k ∈ rowSupport A i then 1 else 0 := by
          intro k
          rcases hA.entries i k with h0 | h1 | hm1
          · simp [mem_rowSupport, h0]
          · simp [mem_rowSupport, h1]
          · simp [mem_rowSupport, hm1]
        simp_rw [hterm]
        simp
      rw [ite_eq_left rfl, hsum_sq, Real.mul_self_sqrt hcard_pos.le,
        div_self hcard_pos.ne', Complex.ofReal_one]
    · have horth : ∑ k, (A i k : ℝ) * (A j k : ℝ) = 0 := by
        exact_mod_cast hA.rows_orthogonal i j hij
      rw [ite_eq_right hij, horth, zero_div, Complex.ofReal_zero]⟩

theorem normalizedRowMatrix_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℤ) (hA : IsSignOrthogonalMatrix A) (i j : ι) :
    (normalizedRowMatrix A hA : Matrix ι ι ℂ) i j =
      ((A i j : ℝ) / Real.sqrt (#(rowSupport A i) : ℝ) : ℂ) := by
  rfl


/-! ### The Paired-Lines Construction -/

section PairedLines

/-- An equipartition `(B₁, B₂)` of a finite type `F` together with a bijection `φ : B₁ ≃ B₂`. -/
structure Equipartition (F : Type*) [Fintype F] [DecidableEq F] where
  /-- First half of the partition. -/
  first : Finset F
  /-- Second half of the partition. -/
  second : Finset F
  /-- The two halves are disjoint. -/
  disjoint : Disjoint first second
  /-- The two halves cover all of `F`. -/
  union_eq_univ : first ∪ second = Finset.univ
  /-- Bijection pairing elements of `first` with elements of `second`. -/
  bij : first ≃ second

theorem Equipartition.card_first_eq_second {F : Type*} [Fintype F] [DecidableEq F]
    (P : Equipartition F) : #P.first = #P.second := by
  have h := Fintype.card_congr P.bij
  simpa using h

theorem Equipartition.two_mul_card_first {F : Type*} [Fintype F] [DecidableEq F]
    (P : Equipartition F) : 2 * #P.first = Fintype.card F := by
  have h := Finset.card_union_of_disjoint P.disjoint
  rw [P.union_eq_univ, Finset.card_univ, ← P.card_first_eq_second] at h
  omega

theorem Equipartition.ne_bij {F : Type*} [Fintype F] [DecidableEq F]
    (P : Equipartition F) (b : P.first) : (b : F) ≠ (P.bij b : F) := by
  intro h
  have hmem : (b : F) ∈ P.second := h ▸ (P.bij b).2
  exact Finset.disjoint_left.mp P.disjoint b.2 hmem

/-- Every finite type of even cardinality admits an equipartition. -/
noncomputable def equipartitionOfEven {α : Type*} [Fintype α] [DecidableEq α]
    (h : Even (Fintype.card α)) : Equipartition α := by
  let m : ℕ := Fintype.card α / 2
  have hm : Fintype.card α = m + m := by
    obtain ⟨k, hk⟩ := h
    omega
  let e : α ≃ Fin (m + m) := Fintype.equivFinOfCardEq hm
  let B₁ : Finset α := Finset.univ.filter fun x => (e x).val < m
  let B₂ : Finset α := Finset.univ.filter fun x => m ≤ (e x).val
  have hdisj : Disjoint B₁ B₂ := by
    rw [Finset.disjoint_filter]
    intro x _ hx1 hx2
    omega
  have hunion : B₁ ∪ B₂ = Finset.univ := by
    ext x
    simp only [B₁, B₂, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    exact iff_true_intro (lt_or_ge (e x).val m)
  have hcard1 : #B₁ = m := by
    have hbij :
        Finset.card B₁ = Finset.card (Finset.univ.filter fun i : Fin (m + m) => i.val < m) := by
      refine Finset.card_bij (fun x _ => e x) ?_ ?_ ?_
      · intro x hx
        simp only [B₁, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
        exact hx
      · intro x₁ _ x₂ _ h12
        exact e.injective h12
      · intro i hi
        refine ⟨e.symm i, ?_, by simp⟩
        simp only [B₁, Finset.mem_filter, Finset.mem_univ, true_and, Equiv.apply_symm_apply]
        exact (Finset.mem_filter.mp hi).2
    rw [hbij]
    have hfin : (Finset.univ.filter fun i : Fin (m + m) => i.val < m).card =
        (Finset.univ : Finset (Fin m)).card := by
      refine Finset.card_bij (fun i hi => (⟨i.val, (Finset.mem_filter.mp hi).2⟩ : Fin m))
        (fun _ _ => Finset.mem_univ _)
        (fun i₁ _ i₂ _ h12 => Fin.ext (by simpa [Fin.ext_iff] using h12))
        (fun j _ => ⟨⟨j.val, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, j.isLt⟩, rfl⟩)
    simpa using hfin
  have hcard2 : #B₂ = m := by
    have hu := Finset.card_union_of_disjoint hdisj
    rw [hunion, Finset.card_univ, hm, hcard1] at hu
    omega
  exact
    { first := B₁
      second := B₂
      disjoint := hdisj
      union_eq_univ := hunion
      bij := Fintype.equivOfCardEq (by simp [hcard1, hcard2]) }

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The paired-lines vector `v_{a, b}` on `𝔽_q × 𝔽_q`: `-1` on the line `y = ax + b`, `+1` on
the line `y = ax + φ(b)`, and `0` elsewhere. -/
@[expose] def pairedLinesVec (P : Equipartition F) (a : F) (b : P.first) (p : F × F) : ℤ :=
  if p.2 = a * p.1 + b.1 then -1
  else if p.2 = a * p.1 + (P.bij b).1 then 1
  else 0

theorem pairedLinesVec_entries (P : Equipartition F) (a : F) (b : P.first) (p : F × F) :
    pairedLinesVec P a b p = 0 ∨ pairedLinesVec P a b p = 1 ∨ pairedLinesVec P a b p = -1 := by
  unfold pairedLinesVec
  split_ifs <;> simp

/-- Support of `v_{a, b}` in `𝔽_q × 𝔽_q`. -/
def pairedLinesSupport (P : Equipartition F) (a : F) (b : P.first) : Finset (F × F) :=
  Finset.univ.filter fun p => pairedLinesVec P a b p ≠ 0

theorem mem_pairedLinesSupport (P : Equipartition F) (a : F) (b : P.first) (p : F × F) :
    p ∈ pairedLinesSupport P a b ↔ p.2 = a * p.1 + b.1 ∨ p.2 = a * p.1 + (P.bij b).1 := by
  unfold pairedLinesSupport pairedLinesVec
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  split_ifs with h1 h2
  · exact ⟨fun _ => Or.inl h1, fun _ => by decide⟩
  · exact ⟨fun _ => Or.inr h2, fun _ => by decide⟩
  · simp [h1, h2]

theorem card_pairedLinesSupport (P : Equipartition F) (a : F) (b : P.first) :
    #(pairedLinesSupport P a b) = 2 * Fintype.card F := by
  let L₁ : Finset (F × F) := Finset.univ.image fun x : F => (x, a * x + b.1)
  let L₂ : Finset (F × F) := Finset.univ.image fun x : F => (x, a * x + (P.bij b).1)
  have hEq : pairedLinesSupport P a b = L₁ ∪ L₂ := by
    ext ⟨x, y⟩
    rw [mem_pairedLinesSupport, Finset.mem_union]
    simp only [L₁, L₂, Finset.mem_image, Finset.mem_univ, true_and, Prod.mk.injEq]
    constructor
    · rintro (rfl | rfl)
      · exact Or.inl ⟨x, rfl, rfl⟩
      · exact Or.inr ⟨x, rfl, rfl⟩
    · rintro (⟨x', rfl, rfl⟩ | ⟨x', rfl, rfl⟩)
      · exact Or.inl rfl
      · exact Or.inr rfl
  have hdisj : Disjoint L₁ L₂ := by
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    simp only [L₁, L₂, Finset.mem_image, Finset.mem_univ, true_and] at hp1 hp2
    rcases hp1 with ⟨x₁, rfl⟩
    rcases hp2 with ⟨x₂, h2⟩
    have hx : x₂ = x₁ := congrArg Prod.fst h2
    have hy : a * x₂ + (P.bij b).1 = a * x₁ + b.1 := congrArg Prod.snd h2
    subst hx
    exact P.ne_bij b (add_left_cancel hy).symm
  have hcard1 : #L₁ = Fintype.card F := by
    rw [Finset.card_image_of_injective _ (fun x₁ x₂ h => congrArg Prod.fst h), Finset.card_univ]
  have hcard2 : #L₂ = Fintype.card F := by
    rw [Finset.card_image_of_injective _ (fun x₁ x₂ h => congrArg Prod.fst h), Finset.card_univ]
  rw [hEq, Finset.card_union_of_disjoint hdisj, hcard1, hcard2, two_mul]

/-- Unique intersection point of two non-parallel lines `y = ax + c` and `y = a'x + c'` over `F`. -/
private def lineInter (a a' c c' : F) : F × F :=
  ((c' - c) / (a - a'), a * ((c' - c) / (a - a')) + c)

omit [Fintype F] [DecidableEq F] in
private theorem lineInter_iff {a a' : F} (haa' : a ≠ a') (c c' : F) (p : F × F) :
    (p.2 = a * p.1 + c ∧ p.2 = a' * p.1 + c') ↔ p = lineInter a a' c c' := by
  have hne : a - a' ≠ 0 := sub_ne_zero.mpr haa'
  constructor
  · rintro ⟨h1, h2⟩
    have hx : (a - a') * p.1 = c' - c := by
      have : a * p.1 + c = a' * p.1 + c' := h1.symm.trans h2
      linear_combination this
    have hx' : p.1 = (c' - c) / (a - a') := (eq_div_iff_mul_eq hne).mpr (by rw [mul_comm]; exact hx)
    exact Prod.ext hx' (by simp [lineInter, h1, hx'])
  · rintro rfl
    refine ⟨rfl, ?_⟩
    simp only [lineInter]
    field_simp [hne]
    ring

/-- Paired-lines intersection bound:
distinct paired-lines vectors share either `0` (same slope) or `4` (distinct slopes) support
elements, and in particular at most `4`. -/
theorem card_pairedLinesSupport_inter_le (P : Equipartition F)
    {a a' : F} {b b' : P.first} (hne : (a, b) ≠ (a', b')) :
    #(pairedLinesSupport P a b ∩ pairedLinesSupport P a' b') ≤ 4 := by
  by_cases ha : a = a'
  · subst ha
    have hb : b ≠ b' := fun h => hne (by rw [h])
    have hempty : pairedLinesSupport P a b ∩ pairedLinesSupport P a b' = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro p hp
      rw [Finset.mem_inter, mem_pairedLinesSupport, mem_pairedLinesSupport] at hp
      rcases hp with ⟨h1 | h1, h2 | h2⟩
      · exact hb (Subtype.ext (add_left_cancel (h1.symm.trans h2)))
      · exact P.ne_bij b' (by
          have heq : (b : F) = (P.bij b' : F) := add_left_cancel (h1.symm.trans h2)
          have hmem : (b : F) ∈ P.second := heq ▸ (P.bij b').2
          exact (Finset.disjoint_left.mp P.disjoint b.2 hmem).elim)
      · exact (Finset.disjoint_left.mp P.disjoint b'.2
          ((add_left_cancel (h1.symm.trans h2)).symm ▸ (P.bij b).2)).elim
      · exact hb (P.bij.injective (Subtype.ext (add_left_cancel (h1.symm.trans h2))))
    rw [hempty]
    simp
  · let p1 := lineInter a a' b.1 b'.1
    let p2 := lineInter a a' (P.bij b).1 b'.1
    let p3 := lineInter a a' b.1 (P.bij b').1
    let p4 := lineInter a a' (P.bij b).1 (P.bij b').1
    have hsub : pairedLinesSupport P a b ∩ pairedLinesSupport P a' b' ⊆ {p1, p2, p3, p4} := by
      intro p hp
      rw [Finset.mem_inter, mem_pairedLinesSupport, mem_pairedLinesSupport] at hp
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rcases hp with ⟨h1 | h1, h2 | h2⟩
      · exact Or.inl ((lineInter_iff ha b.1 b'.1 p).mp ⟨h1, h2⟩)
      · exact Or.inr (Or.inr (Or.inl ((lineInter_iff ha b.1 (P.bij b').1 p).mp ⟨h1, h2⟩)))
      · exact Or.inr (Or.inl ((lineInter_iff ha (P.bij b).1 b'.1 p).mp ⟨h1, h2⟩))
      · exact Or.inr (Or.inr (Or.inr ((lineInter_iff ha (P.bij b).1 (P.bij b').1 p).mp ⟨h1, h2⟩)))
    exact (Finset.card_le_card hsub).trans (by
      calc #({p1, p2, p3, p4} : Finset (F × F))
          ≤ #({p2, p3, p4} : Finset (F × F)) + 1 := Finset.card_insert_le _ _
        _ ≤ #({p3, p4} : Finset (F × F)) + 1 + 1 := by gcongr; exact Finset.card_insert_le _ _
        _ ≤ #({p4} : Finset (F × F)) + 1 + 1 + 1 := by gcongr; exact Finset.card_insert_le _ _
        _ = 4 := by simp)

/-- Paired-lines orthogonality:
distinct paired-lines vectors are pairwise orthogonal over `ℤ`. -/
theorem pairedLinesVec_orthogonal (P : Equipartition F)
    {a a' : F} {b b' : P.first} (hne : (a, b) ≠ (a', b')) :
    ∑ p : F × F, pairedLinesVec P a b p * pairedLinesVec P a' b' p = 0 := by
  by_cases ha : a = a'
  · subst ha
    have hb : b ≠ b' := fun h => hne (by rw [h])
    refine Finset.sum_eq_zero fun p _ => ?_
    unfold pairedLinesVec
    by_cases h1 : p.2 = a * p.1 + b.1
    · rw [ite_eq_left h1]
      split_ifs with h2 h3
      · exact (hb (Subtype.ext (add_left_cancel (h1.symm.trans h2)))).elim
      · exact (Finset.disjoint_left.mp P.disjoint b.2
          ((add_left_cancel (h1.symm.trans h3)) ▸ (P.bij b').2)).elim
      · ring
    · rw [ite_eq_right h1]
      by_cases h4 : p.2 = a * p.1 + (P.bij b).1
      · rw [ite_eq_left h4]
        split_ifs with h5 h6
        · exact (Finset.disjoint_left.mp P.disjoint b'.2
            ((add_left_cancel (h4.symm.trans h5)).symm ▸ (P.bij b).2)).elim
        · exact (hb (P.bij.injective (Subtype.ext (add_left_cancel (h4.symm.trans h6))))).elim
        · ring
      · rw [ite_eq_right h4, zero_mul]
  · let p1 := lineInter a a' b.1 b'.1
    let p2 := lineInter a a' (P.bij b).1 b'.1
    let p3 := lineInter a a' b.1 (P.bij b').1
    let p4 := lineInter a a' (P.bij b).1 (P.bij b').1
    have hp1 : p1.2 = a * p1.1 + b.1 ∧ p1.2 = a' * p1.1 + b'.1 :=
      (lineInter_iff ha b.1 b'.1 p1).mpr rfl
    have hp2 : p2.2 = a * p2.1 + (P.bij b).1 ∧ p2.2 = a' * p2.1 + b'.1 :=
      (lineInter_iff ha (P.bij b).1 b'.1 p2).mpr rfl
    have hp3 : p3.2 = a * p3.1 + b.1 ∧ p3.2 = a' * p3.1 + (P.bij b').1 :=
      (lineInter_iff ha b.1 (P.bij b').1 p3).mpr rfl
    have hp4 : p4.2 = a * p4.1 + (P.bij b).1 ∧ p4.2 = a' * p4.1 + (P.bij b').1 :=
      (lineInter_iff ha (P.bij b).1 (P.bij b').1 p4).mpr rfl
    have h12 : p1 ≠ p2 := fun h =>
      P.ne_bij b (add_left_cancel (hp1.1.symm.trans (h ▸ hp2.1)))
    have h13 : p1 ≠ p3 := fun h =>
      P.ne_bij b' (add_left_cancel (hp1.2.symm.trans (h ▸ hp3.2)))
    have h14 : p1 ≠ p4 := fun h =>
      P.ne_bij b (add_left_cancel (hp1.1.symm.trans (h ▸ hp4.1)))
    have h23 : p2 ≠ p3 := fun h =>
      P.ne_bij b (add_left_cancel (hp2.1.symm.trans (h ▸ hp3.1))).symm
    have h24 : p2 ≠ p4 := fun h =>
      P.ne_bij b' (add_left_cancel (hp2.2.symm.trans (h ▸ hp4.2)))
    have h34 : p3 ≠ p4 := fun h =>
      P.ne_bij b (add_left_cancel (hp3.1.symm.trans (h ▸ hp4.1)))
    have hsupp :
        ∀ p ∈ (Finset.univ : Finset (F × F)),
          p ∉ ({p1, p2, p3, p4} : Finset (F × F)) →
          pairedLinesVec P a b p * pairedLinesVec P a' b' p = 0 := by
      intro p _ hp
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hp
      unfold pairedLinesVec
      by_cases c1 : p.2 = a * p.1 + b.1
      · rw [ite_eq_left c1]
        split_ifs with c2 c3
        · exact (hp.1 ((lineInter_iff ha b.1 b'.1 p).mp ⟨c1, c2⟩)).elim
        · exact (hp.2.2.1 ((lineInter_iff ha b.1 (P.bij b').1 p).mp ⟨c1, c3⟩)).elim
        · ring
      · rw [ite_eq_right c1]
        by_cases c4 : p.2 = a * p.1 + (P.bij b).1
        · rw [ite_eq_left c4]
          split_ifs with c5 c6
          · exact (hp.2.1 ((lineInter_iff ha (P.bij b).1 b'.1 p).mp ⟨c4, c5⟩)).elim
          · exact (hp.2.2.2 ((lineInter_iff ha (P.bij b).1 (P.bij b').1 p).mp ⟨c4, c6⟩)).elim
          · ring
        · rw [ite_eq_right c4, zero_mul]
    rw [← Finset.sum_subset (Finset.subset_univ ({p1, p2, p3, p4} : Finset (F × F))) hsupp]
    rw [Finset.sum_insert (by simp [h12, h13, h14]),
      Finset.sum_insert (by simp [h23, h24]),
      Finset.sum_insert (by simp [h34]),
      Finset.sum_singleton]
    have hv1 : pairedLinesVec P a b p1 * pairedLinesVec P a' b' p1 = 1 := by
      rw [pairedLinesVec, pairedLinesVec, ite_eq_left hp1.1, ite_eq_left hp1.2]
      norm_num
    have hv2 : pairedLinesVec P a b p2 * pairedLinesVec P a' b' p2 = -1 := by
      have hne1 : p2.2 ≠ a * p2.1 + b.1 := fun h =>
        P.ne_bij b (add_left_cancel (h.symm.trans hp2.1))
      rw [pairedLinesVec, pairedLinesVec, ite_eq_right hne1, ite_eq_left hp2.1, ite_eq_left hp2.2]
      norm_num
    have hv3 : pairedLinesVec P a b p3 * pairedLinesVec P a' b' p3 = -1 := by
      have hne2 : p3.2 ≠ a' * p3.1 + b'.1 := fun h =>
        P.ne_bij b' (add_left_cancel (h.symm.trans hp3.2))
      rw [pairedLinesVec, pairedLinesVec, ite_eq_left hp3.1, ite_eq_right hne2, ite_eq_left hp3.2]
      norm_num
    have hv4 : pairedLinesVec P a b p4 * pairedLinesVec P a' b' p4 = 1 := by
      have hne1 : p4.2 ≠ a * p4.1 + b.1 := fun h =>
        P.ne_bij b (add_left_cancel (h.symm.trans hp4.1))
      have hne2 : p4.2 ≠ a' * p4.1 + b'.1 := fun h =>
        P.ne_bij b' (add_left_cancel (h.symm.trans hp4.2))
      rw [pairedLinesVec, pairedLinesVec, ite_eq_right hne1, ite_eq_left hp4.1,
        ite_eq_right hne2, ite_eq_left hp4.2]
      norm_num
    rw [hv1, hv2, hv3, hv4]
    norm_num

/-- Paired-lines support family packaged as a
Nisan–Wigderson `(2q, 4)`-design with `q^2 / 2` blocks in a universe of size `q^2`. -/
noncomputable def pairedLinesDesign (P : Equipartition F) :
    Design (Fintype.card F ^ 2) (2 * Fintype.card F) 4 (Fintype.card F * #P.first) :=
  let eU : (F × F) ≃ Fin (Fintype.card F ^ 2) :=
    Fintype.equivFinOfCardEq (by simp [sq])
  let eI : (F × P.first) ≃ Fin (Fintype.card F * #P.first) :=
    Fintype.equivFinOfCardEq (by simp)
  { block := fun i =>
      (pairedLinesSupport P (eI.symm i).1 (eI.symm i).2).map eU.toEmbedding
    card_block := fun i => by
      rw [Finset.card_map, card_pairedLinesSupport]
    card_inter_le := fun {i j} hij => by
      have hne : eI.symm i ≠ eI.symm j := fun h => hij (eI.symm.injective h)
      rw [← Finset.map_inter, Finset.card_map]
      exact card_pairedLinesSupport_inter_le P (by
        intro heq
        apply hne
        exact Prod.ext (congrArg Prod.fst heq) (congrArg Prod.snd heq)) }

/-- Concrete instantiation for `𝔽_q = GaloisField 2 n` (`q = 2^n`, `n > 0`): there exists a
`(2q, 4)`-design with `q^2 / 2` blocks in a universe of size `q^2` arising from pairwise
orthogonal `{0, 1, -1}`-vectors. -/
theorem exists_pairedLines_design_gf2 (n : ℕ) (hn : 0 < n) :
    let q := 2 ^ n
    ∃ (_ : Fintype (GaloisField 2 n)) (_ : DecidableEq (GaloisField 2 n))
      (P : Equipartition (GaloisField 2 n)),
      Fintype.card (GaloisField 2 n) = q ∧
      Fintype.card (GaloisField 2 n) * #P.first = q ^ 2 / 2 ∧
      (∀ a a' b b', (a, b) ≠ (a', b') →
        ∑ p : GaloisField 2 n × GaloisField 2 n,
          pairedLinesVec P a b p * pairedLinesVec P a' b' p = 0) ∧
      Nonempty (Design (q ^ 2) (2 * q) 4 (q ^ 2 / 2)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnatCard : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n hn.ne'
  have hfin : Finite (GaloisField 2 n) :=
    Nat.finite_of_card_ne_zero (by rw [hnatCard]; positivity)
  let _ : Fintype (GaloisField 2 n) := Fintype.ofFinite (GaloisField 2 n)
  have hcard : Fintype.card (GaloisField 2 n) = 2 ^ n := by
    rw [← Nat.card_eq_fintype_card, hnatCard]
  have heven : Even (Fintype.card (GaloisField 2 n)) := by
    rw [hcard]
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
    exact ⟨2 ^ m, by rw [pow_succ]; ring⟩
  let P := equipartitionOfEven heven
  have h2 : 2 * #P.first = 2 ^ n := by
    rw [P.two_mul_card_first, hcard]
  have hprod' : 2 ^ n * #P.first = (2 ^ n) ^ 2 / 2 := by
    have hsq : 2 * (2 ^ n * #P.first) = (2 ^ n) ^ 2 := by nlinarith [h2]
    omega
  have hprod : Fintype.card (GaloisField 2 n) * #P.first = (2 ^ n) ^ 2 / 2 := by
    rw [hcard]
    exact hprod'
  refine ⟨inferInstance, inferInstance, P, hcard, hprod,
    fun a a' b b' hne => pairedLinesVec_orthogonal P hne, ?_⟩
  have hD := pairedLinesDesign P
  rw [hcard, hprod'] at hD
  exact ⟨hD⟩

end PairedLines

/-! ### A Unitary in Which All Rows Participate -/

section AllRows

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- A half-set `Q ⊆ 𝔽_q^*` satisfying `Q ∩ (-Q) = ∅` and `Q ∪ (-Q) = 𝔽_q^*`. -/
structure OddFieldHalfSet (F : Type*) [Field F] [Fintype F] [DecidableEq F] where
  /-- The subset `Q ⊆ 𝔽_q^*`. -/
  set : Finset F
  /-- `0 ∉ Q`. -/
  zero_notMem : (0 : F) ∉ set
  /-- `Q ∩ (-Q) = ∅`. -/
  disjoint_neg : ∀ x ∈ set, -x ∉ set
  /-- Every nonzero element lies in `Q` or `-Q`. -/
  mem_or_neg_mem : ∀ x : F, x ≠ 0 → x ∈ set ∨ -x ∈ set

theorem OddFieldHalfSet.ne_zero_of_mem (Q : OddFieldHalfSet F) {x : F} (hx : x ∈ Q.set) :
    x ≠ 0 := fun h => Q.zero_notMem (h ▸ hx)

theorem OddFieldHalfSet.two_mul_card (Q : OddFieldHalfSet F) :
    2 * #Q.set = Fintype.card F - 1 := by
  let negQ : Finset F := Q.set.image Neg.neg
  have hdisj : Disjoint Q.set negQ := by
    rw [Finset.disjoint_left]
    intro x hx hneg
    rcases Finset.mem_image.mp hneg with ⟨y, hy, rfl⟩
    exact Q.disjoint_neg y hy hx
  have hcard_neg : #negQ = #Q.set :=
    Finset.card_image_of_injective _ neg_injective
  have hunion : Q.set ∪ negQ = Finset.univ.erase (0 : F) := by
    ext x
    simp only [negQ, Finset.mem_union, Finset.mem_image, Finset.mem_erase, Finset.mem_univ,
      and_true]
    constructor
    · rintro (hx | ⟨y, hy, rfl⟩)
      · exact Q.ne_zero_of_mem hx
      · exact neg_ne_zero.mpr (Q.ne_zero_of_mem hy)
    · intro hx
      rcases Q.mem_or_neg_mem x hx with h | h
      · exact Or.inl h
      · exact Or.inr ⟨-x, h, neg_neg x⟩
  have hcard := Finset.card_union_of_disjoint hdisj
  rw [hunion, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, hcard_neg] at hcard
  omega

theorem OddFieldHalfSet.two_ne_zero (Q : OddFieldHalfSet F) (hnonempty : Q.set.Nonempty) :
    (2 : F) ≠ 0 := by
  obtain ⟨x, hx⟩ := hnonempty
  intro h2
  have hneg : -x = x := by
    have : x + x = 0 := by
      have : (2 : F) * x = 0 := by rw [h2, zero_mul]
      rwa [two_mul] at this
    exact neg_eq_iff_add_eq_zero.mpr this
  exact Q.disjoint_neg x hx (hneg.symm ▸ hx)

omit [DecidableEq F] in
theorem odd_card_two_ne_zero (hodd : Odd (Fintype.card F)) : (2 : F) ≠ 0 := by
  intro h2
  have hdvd : ringChar F ∣ 2 := (ringChar.spec F 2).mp (by simpa using h2)
  have hprime : (ringChar F).Prime := by
    rcases CharP.char_is_prime_or_zero F (ringChar F) with hp | h0
    · exact hp
    · rw [h0] at hdvd
      exact absurd hdvd (by decide)
  have hrc2 : ringChar F = 2 :=
    ((Nat.dvd_prime Nat.prime_two).mp hdvd).resolve_left hprime.ne_one
  have heven : Fintype.card F % 2 = 0 := FiniteField.even_card_iff_char_two.mp hrc2
  obtain ⟨k, hk⟩ := hodd
  omega

/-- Every finite field of odd cardinality admits a half-set `Q ⊆ 𝔽_q^*`. -/
noncomputable def oddFieldHalfSetOfOdd (hodd : Odd (Fintype.card F)) : OddFieldHalfSet F :=
  let e : F ≃ Fin (Fintype.card F) := Fintype.equivFin F
  have h2 : (2 : F) ≠ 0 := odd_card_two_ne_zero hodd
  have hne_neg : ∀ x : F, x ≠ 0 → x ≠ -x := by
    intro x hx heq
    have : (2 : F) * x = 0 := by
      rw [two_mul]
      exact eq_neg_iff_add_eq_zero.mp heq
    exact hx ((mul_eq_zero.mp this).resolve_left h2)
  { set := Finset.univ.filter fun x => x ≠ 0 ∧ (e x).val < (e (-x)).val
    zero_notMem := by simp
    disjoint_neg := fun x hx => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, neg_neg] at hx ⊢
      intro hneg
      omega
    mem_or_neg_mem := fun x hx => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, neg_neg]
      have hne : (e x).val ≠ (e (-x)).val := fun h => hne_neg x hx (e.injective (Fin.ext h))
      rcases lt_trichotomy (e x).val (e (-x)).val with hlt | heq | hgt
      · exact Or.inl ⟨hx, hlt⟩
      · exact (hne heq).elim
      · exact Or.inr ⟨neg_ne_zero.mpr hx, hgt⟩ }

/-- The punctured affine plane `P = (𝔽_q × 𝔽_q) \ {(0, 0)}`. -/
abbrev PuncturedPlane (F : Type*) [Zero F] := {p : F × F // p ≠ (0, 0)}

/-- Row index set for the `q^2 - 1` vectors of the punctured-plane construction:
`q(q-1)/2` Type-1 vectors, `q(q-1)/2` Type-2 vectors, and `q-1` Type-3 vectors. -/
inductive AllRowsIndex (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (Q : OddFieldHalfSet F) : Type _
  | type1 (a : F) (b : Q.set)
  | type2 (a : F) (b : Q.set)
  | type3 (c : {x : F // x ≠ 0})

/-- Equivalence expressing `AllRowsIndex F Q` as a disjoint sum of finite types. -/
def allRowsIndexEquivSum (Q : OddFieldHalfSet F) :
    AllRowsIndex F Q ≃ (F × Q.set) ⊕ (F × Q.set) ⊕ {x : F // x ≠ 0} where
  toFun
    | .type1 a b => Sum.inl (a, b)
    | .type2 a b => Sum.inr (Sum.inl (a, b))
    | .type3 c => Sum.inr (Sum.inr c)
  invFun
    | Sum.inl (a, b) => .type1 a b
    | Sum.inr (Sum.inl (a, b)) => .type2 a b
    | Sum.inr (Sum.inr c) => .type3 c
  left_inv x := by cases x <;> rfl
  right_inv x := by rcases x with ⟨a, b⟩ | ⟨a, b⟩ | c <;> rfl

/-- Decidable equality on `AllRowsIndex F Q`, transported along `allRowsIndexEquivSum`. -/
local instance instDecidableEqAllRowsIndex (Q : OddFieldHalfSet F) :
    DecidableEq (AllRowsIndex F Q) :=
  (allRowsIndexEquivSum Q).decidableEq

/-- `Fintype` instance on `AllRowsIndex F Q`, transported along `allRowsIndexEquivSum`. -/
noncomputable local instance instFintypeAllRowsIndex (Q : OddFieldHalfSet F) :
    Fintype (AllRowsIndex F Q) :=
  Fintype.ofEquiv _ (allRowsIndexEquivSum Q).symm

theorem card_puncturedPlane :
    Fintype.card (PuncturedPlane F) = Fintype.card F ^ 2 - 1 := by
  rw [Fintype.card_subtype_compl, Fintype.card_prod, Fintype.card_subtype_eq, sq]

theorem card_allRowsIndex (Q : OddFieldHalfSet F) :
    Fintype.card (AllRowsIndex F Q) = Fintype.card F ^ 2 - 1 := by
  rw [Fintype.card_congr (allRowsIndexEquivSum Q), Fintype.card_sum, Fintype.card_sum,
    Fintype.card_prod, Fintype.card_coe, Fintype.card_subtype_compl,
    Fintype.card_subtype_eq]
  have hQ := Q.two_mul_card
  have hpos : 1 ≤ Fintype.card F := Fintype.card_pos
  zify [hpos] at hQ ⊢
  have hsq : (1 : ℕ) ≤ Fintype.card F ^ 2 := by nlinarith
  zify [hsq]
  nlinarith

/-- The `q^2 - 1` vectors of the punctured-plane construction, indexed by `AllRowsIndex F Q` on
`PuncturedPlane F`. -/
def allRowsVec (Q : OddFieldHalfSet F) : AllRowsIndex F Q → PuncturedPlane F → ℤ
  | .type1 a b, p =>
      if p.1.1 = 0 ∧ p.1.2 = b.1 then 1
      else if p.1.1 ∈ Q.set ∧ p.1.2 = a * p.1.1 + b.1 then 1
      else if p.1.1 ∈ Q.set ∧ p.1.2 = a * p.1.1 - b.1 then -1
      else 0
  | .type2 a b, p =>
      if p.1.1 = 0 ∧ p.1.2 = -b.1 then 1
      else if -p.1.1 ∈ Q.set ∧ p.1.2 = a * p.1.1 - b.1 then 1
      else if -p.1.1 ∈ Q.set ∧ p.1.2 = a * p.1.1 + b.1 then -1
      else 0
  | .type3 c, p =>
      if p.1.1 = c.1 then 1 else 0

theorem allRowsVec_entries (Q : OddFieldHalfSet F) (i : AllRowsIndex F Q) (p : PuncturedPlane F) :
    allRowsVec Q i p = 0 ∨ allRowsVec Q i p = 1 ∨ allRowsVec Q i p = -1 := by
  cases i <;> dsimp only [allRowsVec] <;> split_ifs <;> simp

/-- Support of row `i` in `PuncturedPlane F`. -/
def allRowsSupport (Q : OddFieldHalfSet F) (i : AllRowsIndex F Q) :
    Finset (PuncturedPlane F) :=
  Finset.univ.filter fun p => allRowsVec Q i p ≠ 0

private theorem mem_allRowsSupport_type1 (Q : OddFieldHalfSet F) (a : F) (b : Q.set)
    (p : PuncturedPlane F) :
    p ∈ allRowsSupport Q (.type1 a b) ↔
      (p.1.1 = 0 ∧ p.1.2 = b.1) ∨
      (p.1.1 ∈ Q.set ∧ (p.1.2 = a * p.1.1 + b.1 ∨ p.1.2 = a * p.1.1 - b.1)) := by
  unfold allRowsSupport allRowsVec
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  split_ifs with h1 h2 h3
  · exact ⟨fun _ => Or.inl h1, fun _ => by decide⟩
  · exact ⟨fun _ => Or.inr ⟨h2.1, Or.inl h2.2⟩, fun _ => by decide⟩
  · exact ⟨fun _ => Or.inr ⟨h3.1, Or.inr h3.2⟩, fun _ => by decide⟩
  · constructor
    · intro h; exact (h rfl).elim
    · rintro (h | ⟨hx, hy | hy⟩)
      · exact (h1 h).elim
      · exact (h2 ⟨hx, hy⟩).elim
      · exact (h3 ⟨hx, hy⟩).elim

private theorem mem_allRowsSupport_type2 (Q : OddFieldHalfSet F) (a : F) (b : Q.set)
    (p : PuncturedPlane F) :
    p ∈ allRowsSupport Q (.type2 a b) ↔
      (p.1.1 = 0 ∧ p.1.2 = -b.1) ∨
      (-p.1.1 ∈ Q.set ∧ (p.1.2 = a * p.1.1 - b.1 ∨ p.1.2 = a * p.1.1 + b.1)) := by
  unfold allRowsSupport allRowsVec
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  split_ifs with h1 h2 h3
  · exact ⟨fun _ => Or.inl h1, fun _ => by decide⟩
  · exact ⟨fun _ => Or.inr ⟨h2.1, Or.inl h2.2⟩, fun _ => by decide⟩
  · exact ⟨fun _ => Or.inr ⟨h3.1, Or.inr h3.2⟩, fun _ => by decide⟩
  · constructor
    · intro h; exact (h rfl).elim
    · rintro (h | ⟨hx, hy | hy⟩)
      · exact (h1 h).elim
      · exact (h2 ⟨hx, hy⟩).elim
      · exact (h3 ⟨hx, hy⟩).elim

private theorem mem_allRowsSupport_type3 (Q : OddFieldHalfSet F) (c : {x : F // x ≠ 0})
    (p : PuncturedPlane F) :
    p ∈ allRowsSupport Q (.type3 c) ↔ p.1.1 = c.1 := by
  unfold allRowsSupport allRowsVec
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  split_ifs with h <;> simp [h]

private theorem add_ne_sub_of_mem_halfSet (Q : OddFieldHalfSet F) (hodd : Odd (Fintype.card F))
    {b : F} (hb : b ∈ Q.set) (t : F) : t + b ≠ t - b := by
  intro h
  have h2b : (2 : F) * b = 0 := by
    have : b = -b := by linear_combination h
    rw [two_mul]
    exact eq_neg_iff_add_eq_zero.mp this
  exact Q.ne_zero_of_mem hb ((mul_eq_zero.mp h2b).resolve_left (odd_card_two_ne_zero hodd))

/-- Every row in the punctured-plane construction has support cardinality `q = |𝔽_q|`. -/
theorem card_allRowsSupport (Q : OddFieldHalfSet F) (hodd : Odd (Fintype.card F))
    (i : AllRowsIndex F Q) :
    #(allRowsSupport Q i) = Fintype.card F := by
  have h2Q := Q.two_mul_card
  have hpos : 1 ≤ Fintype.card F := Fintype.card_pos
  cases i with
  | type1 a b =>
    let p0 : PuncturedPlane F := ⟨(0, b.1), fun h => Q.ne_zero_of_mem b.2 (congrArg Prod.snd h)⟩
    let S₁ : Finset (PuncturedPlane F) :=
      Q.set.attach.image fun x =>
        ⟨(x.1, a * x.1 + b.1), fun h => Q.ne_zero_of_mem x.2 (congrArg Prod.fst h)⟩
    let S₂ : Finset (PuncturedPlane F) :=
      Q.set.attach.image fun x =>
        ⟨(x.1, a * x.1 - b.1), fun h => Q.ne_zero_of_mem x.2 (congrArg Prod.fst h)⟩
    have hEq : allRowsSupport Q (.type1 a b) = insert p0 (S₁ ∪ S₂) := by
      ext p
      rw [mem_allRowsSupport_type1, Finset.mem_insert, Finset.mem_union]
      simp only [S₁, S₂, Finset.mem_image, Finset.mem_attach, true_and, Subtype.ext_iff,
        Prod.ext_iff, p0]
      constructor
      · rintro (⟨hx, hy⟩ | ⟨hx, hy | hy⟩)
        · exact Or.inl ⟨hx, hy⟩
        · exact Or.inr (Or.inl ⟨⟨p.1.1, hx⟩, rfl, hy.symm⟩)
        · exact Or.inr (Or.inr ⟨⟨p.1.1, hx⟩, rfl, hy.symm⟩)
      · rintro (⟨hx, hy⟩ | ⟨⟨x, hx⟩, rfl, hy⟩ | ⟨⟨x, hx⟩, rfl, hy⟩)
        · exact Or.inl ⟨hx, hy⟩
        · exact Or.inr ⟨hx, Or.inl hy.symm⟩
        · exact Or.inr ⟨hx, Or.inr hy.symm⟩
    have hp0 : p0 ∉ S₁ ∪ S₂ := by
      simp only [Finset.mem_union, S₁, S₂, Finset.mem_image, Finset.mem_attach, true_and,
        Subtype.ext_iff, Prod.ext_iff, p0]
      rintro (⟨⟨x, hx⟩, hx0, _⟩ | ⟨⟨x, hx⟩, hx0, _⟩) <;> exact Q.ne_zero_of_mem hx hx0
    have hdisj : Disjoint S₁ S₂ := by
      rw [Finset.disjoint_left]
      intro p hp1 hp2
      simp only [S₁, S₂, Finset.mem_image, Finset.mem_attach, true_and, Subtype.ext_iff,
        Prod.ext_iff] at hp1 hp2
      rcases hp1 with ⟨⟨x₁, _⟩, hx1, hy1⟩
      rcases hp2 with ⟨⟨x₂, _⟩, hx2, hy2⟩
      have hx : x₁ = x₂ := hx1.trans hx2.symm
      subst hx
      exact add_ne_sub_of_mem_halfSet Q hodd b.2 (a * x₁) (hy1.trans hy2.symm)
    have hcard1 : #S₁ = #Q.set := by
      rw [Finset.card_image_of_injective _ (fun x₁ x₂ h =>
        Subtype.ext (congrArg (fun p : PuncturedPlane F => p.1.1) h)), Finset.card_attach]
    have hcard2 : #S₂ = #Q.set := by
      rw [Finset.card_image_of_injective _ (fun x₁ x₂ h =>
        Subtype.ext (congrArg (fun p : PuncturedPlane F => p.1.1) h)), Finset.card_attach]
    rw [hEq, Finset.card_insert_of_notMem hp0, Finset.card_union_of_disjoint hdisj, hcard1, hcard2]
    omega
  | type2 a b =>
    let p0 : PuncturedPlane F :=
      ⟨(0, -b.1), fun h => neg_ne_zero.mpr (Q.ne_zero_of_mem b.2) (congrArg Prod.snd h)⟩
    let S₁ : Finset (PuncturedPlane F) :=
      Q.set.attach.image fun x =>
        ⟨(-x.1, a * (-x.1) - b.1), fun h =>
          neg_ne_zero.mpr (Q.ne_zero_of_mem x.2) (congrArg Prod.fst h)⟩
    let S₂ : Finset (PuncturedPlane F) :=
      Q.set.attach.image fun x =>
        ⟨(-x.1, a * (-x.1) + b.1), fun h =>
          neg_ne_zero.mpr (Q.ne_zero_of_mem x.2) (congrArg Prod.fst h)⟩
    have hEq : allRowsSupport Q (.type2 a b) = insert p0 (S₁ ∪ S₂) := by
      ext p
      rw [mem_allRowsSupport_type2, Finset.mem_insert, Finset.mem_union]
      simp only [S₁, S₂, Finset.mem_image, Finset.mem_attach, true_and, Subtype.ext_iff,
        Prod.ext_iff, p0]
      constructor
      · rintro (⟨hx, hy⟩ | ⟨hx, hy | hy⟩)
        · exact Or.inl ⟨hx, hy⟩
        · exact Or.inr (Or.inl ⟨⟨-p.1.1, hx⟩, neg_neg _, by rw [neg_neg, hy]⟩)
        · exact Or.inr (Or.inr ⟨⟨-p.1.1, hx⟩, neg_neg _, by rw [neg_neg, hy]⟩)
      · rintro (⟨hx, hy⟩ | ⟨⟨x, hx⟩, hx', hy⟩ | ⟨⟨x, hx⟩, hx', hy⟩)
        · exact Or.inl ⟨hx, hy⟩
        · exact Or.inr ⟨by rw [← hx', neg_neg]; exact hx, Or.inl (by rw [← hx', hy])⟩
        · exact Or.inr ⟨by rw [← hx', neg_neg]; exact hx, Or.inr (by rw [← hx', hy])⟩
    have hp0 : p0 ∉ S₁ ∪ S₂ := by
      simp only [Finset.mem_union, S₁, S₂, Finset.mem_image, Finset.mem_attach, true_and,
        Subtype.ext_iff, Prod.ext_iff, p0]
      rintro (⟨⟨x, hx⟩, hx0, _⟩ | ⟨⟨x, hx⟩, hx0, _⟩) <;>
        exact neg_ne_zero.mpr (Q.ne_zero_of_mem hx) hx0
    have hdisj : Disjoint S₁ S₂ := by
      rw [Finset.disjoint_left]
      intro p hp1 hp2
      simp only [S₁, S₂, Finset.mem_image, Finset.mem_attach, true_and, Subtype.ext_iff,
        Prod.ext_iff] at hp1 hp2
      rcases hp1 with ⟨⟨x₁, _⟩, hx1, hy1⟩
      rcases hp2 with ⟨⟨x₂, _⟩, hx2, hy2⟩
      have hx : x₁ = x₂ := neg_injective (hx1.trans hx2.symm)
      subst hx
      exact add_ne_sub_of_mem_halfSet Q hodd b.2 (a * (-x₁)) (hy2.trans hy1.symm)
    have hcard1 : #S₁ = #Q.set := by
      rw [Finset.card_image_of_injective _ (fun x₁ x₂ h =>
        Subtype.ext (neg_injective (congrArg (fun p : PuncturedPlane F => p.1.1) h))),
        Finset.card_attach]
    have hcard2 : #S₂ = #Q.set := by
      rw [Finset.card_image_of_injective _ (fun x₁ x₂ h =>
        Subtype.ext (neg_injective (congrArg (fun p : PuncturedPlane F => p.1.1) h))),
        Finset.card_attach]
    rw [hEq, Finset.card_insert_of_notMem hp0, Finset.card_union_of_disjoint hdisj, hcard1, hcard2]
    omega
  | type3 c =>
    let S : Finset (PuncturedPlane F) :=
      Finset.univ.image fun y : F => ⟨(c.1, y), fun h => c.2 (congrArg Prod.fst h)⟩
    have hEq : allRowsSupport Q (.type3 c) = S := by
      ext p
      rw [mem_allRowsSupport_type3]
      simp only [S, Finset.mem_image, Finset.mem_univ, true_and, Subtype.ext_iff, Prod.ext_iff]
      exact ⟨fun h => ⟨p.1.2, h.symm, rfl⟩, fun ⟨_, hx, _⟩ => hx.symm⟩
    rw [hEq, Finset.card_image_of_injective _ (fun y₁ y₂ h =>
      congrArg (fun p : PuncturedPlane F => p.1.2) h), Finset.card_univ]

/-- Helper: given `z ≠ 0` and a half-set `Q`, the pair `{z, -z}` meets `Q` in a unique element. -/
private theorem existsUnique_mem_halfSet_pm (Q : OddFieldHalfSet F) {z : F} (hz : z ≠ 0) :
    (z ∈ Q.set ∧ -z ∉ Q.set) ∨ (-z ∈ Q.set ∧ z ∉ Q.set) := by
  rcases Q.mem_or_neg_mem z hz with h | h
  · exact Or.inl ⟨h, Q.disjoint_neg z h⟩
  · exact Or.inr ⟨h, fun hz' => Q.disjoint_neg z hz' h⟩

/-- Helper for Type 1 vs Type 1 (same half-set `Q`), capturing both intersection bound `≤ 2`
and orthogonality simultaneously. -/
private theorem type1_type1_inter_and_orth (Q : OddFieldHalfSet F) (hodd : Odd (Fintype.card F))
    {a a' : F} {b b' : Q.set} (hne : (a, b) ≠ (a', b')) :
    #(allRowsSupport Q (.type1 a b) ∩ allRowsSupport Q (.type1 a' b')) ≤ 2 ∧
      ∑ p : PuncturedPlane F,
        allRowsVec Q (.type1 a b) p * allRowsVec Q (.type1 a' b') p = 0 := by
  have h2 : (2 : F) ≠ 0 := odd_card_two_ne_zero hodd
  have hdisj_sum : ∀ {x y : F}, x ∈ Q.set → y ∈ Q.set → x + y ≠ 0 := by
    intro x y hx hy hxy
    have : y = -x := eq_neg_of_add_eq_zero_right hxy
    exact Q.disjoint_neg x hx (this ▸ hy)
  by_cases ha : a = a'
  · subst ha
    have hb : b ≠ b' := fun h => hne (by rw [h])
    have hdisj : ∀ p : PuncturedPlane F,
        ¬(p ∈ allRowsSupport Q (.type1 a b) ∧ p ∈ allRowsSupport Q (.type1 a b')) := by
      intro p ⟨h1, h2'⟩
      rw [mem_allRowsSupport_type1] at h1 h2'
      rcases h1 with ⟨hx1, hy1⟩ | ⟨hx1, hy1 | hy1⟩ <;> rcases h2' with ⟨hx2, hy2⟩ | ⟨hx2, hy2 | hy2⟩
      · exact hb (Subtype.ext (hy1.symm.trans hy2))
      · exact Q.ne_zero_of_mem hx2 hx1
      · exact Q.ne_zero_of_mem hx2 hx1
      · exact Q.ne_zero_of_mem hx1 hx2
      · exact hb (Subtype.ext (add_left_cancel (hy1.symm.trans hy2)))
      · exact hdisj_sum b.2 b'.2 (by linear_combination hy1.symm.trans hy2)
      · exact Q.ne_zero_of_mem hx1 hx2
      · exact hdisj_sum b.2 b'.2 (by linear_combination -(hy1.symm.trans hy2))
      · exact hb (Subtype.ext (by linear_combination -(hy1.symm.trans hy2)))
    refine ⟨?_, ?_⟩
    · have hempty : allRowsSupport Q (.type1 a b) ∩ allRowsSupport Q (.type1 a b') = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro p hp
        exact hdisj p (Finset.mem_inter.mp hp)
      simp [hempty]
    · refine Finset.sum_eq_zero fun p _ => ?_
      by_cases hp1 : allRowsVec Q (.type1 a b) p = 0
      · simp [hp1]
      · by_cases hp2 : allRowsVec Q (.type1 a b') p = 0
        · simp [hp2]
        · exact (hdisj p ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp1⟩,
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp2⟩⟩).elim
  · have haa' : a - a' ≠ 0 := sub_ne_zero.mpr ha
    by_cases hb : b = b'
    · subst hb
      let p0 : PuncturedPlane F :=
        ⟨(0, b.1), fun h => Q.ne_zero_of_mem b.2 (congrArg Prod.snd h)⟩
      let xA : F := (-(2 * b.1)) / (a - a')
      have hxA_ne : xA ≠ 0 := div_ne_zero (neg_ne_zero.mpr (mul_ne_zero h2 (Q.ne_zero_of_mem b.2)))
        haa'
      have hxA_neg : -xA = (2 * b.1) / (a - a') := by simp [xA, neg_div]
      -- Exactly one of `xA` or `-xA` lies in `Q`.
      rcases existsUnique_mem_halfSet_pm Q hxA_ne with ⟨hxQ, hnxQ⟩ | ⟨hnxQ, hxQ⟩
      · let p1 : PuncturedPlane F :=
          ⟨(xA, a * xA + b.1), fun h => hxA_ne (congrArg Prod.fst h)⟩
        have hp1_eq : a * xA + b.1 = a' * xA - b.1 := by
          simp only [xA]
          field_simp [haa']
          ring
        have hp_ne : p0 ≠ p1 := fun h =>
          hxA_ne (congrArg (fun p : PuncturedPlane F => p.1.1) h).symm
        have hinter : ∀ p : PuncturedPlane F,
            p ∈ allRowsSupport Q (.type1 a b) ∧ p ∈ allRowsSupport Q (.type1 a' b) →
            p = p0 ∨ p = p1 := by
          intro p ⟨h1, h2'⟩
          rw [mem_allRowsSupport_type1] at h1 h2'
          rcases h1 with ⟨hx1, hy1⟩ | ⟨hx1, hy1 | hy1⟩ <;>
            rcases h2' with ⟨hx2, hy2⟩ | ⟨hx2, hy2 | hy2⟩
          · exact Or.inl (Subtype.ext (Prod.ext hx1 hy1))
          · exact (Q.ne_zero_of_mem hx2 hx1).elim
          · exact (Q.ne_zero_of_mem hx2 hx1).elim
          · exact (Q.ne_zero_of_mem hx1 hx2).elim
          · exfalso
            have : (a - a') * p.1.1 = 0 := by linear_combination hy1.symm.trans hy2
            exact Q.ne_zero_of_mem hx1 ((mul_eq_zero.mp this).resolve_left haa')
          · right
            have hx : p.1.1 = xA := by
              rw [eq_div_iff haa']
              linear_combination hy1.symm.trans hy2
            exact Subtype.ext (Prod.ext hx (by rw [hy1, hx]))
          · exact (Q.ne_zero_of_mem hx1 hx2).elim
          · exfalso
            have hx : p.1.1 = -xA := by
              rw [hxA_neg, eq_div_iff haa']
              linear_combination hy1.symm.trans hy2
            exact hnxQ (hx ▸ hx1)
          · exfalso
            have : (a - a') * p.1.1 = 0 := by linear_combination hy1.symm.trans hy2
            exact Q.ne_zero_of_mem hx1 ((mul_eq_zero.mp this).resolve_left haa')
        have hsub : allRowsSupport Q (.type1 a b) ∩ allRowsSupport Q (.type1 a' b) ⊆ {p0, p1} := by
          intro p hp
          simpa [Finset.mem_insert, Finset.mem_singleton] using hinter p (Finset.mem_inter.mp hp)
        refine ⟨(Finset.card_le_card hsub).trans (Finset.card_le_two), ?_⟩
        rw [← Finset.sum_subset (Finset.subset_univ ({p0, p1} : Finset (PuncturedPlane F)))
          (fun p _ hp => by
            by_cases h1 : allRowsVec Q (.type1 a b) p = 0
            · simp [h1]
            · by_cases h2' : allRowsVec Q (.type1 a' b) p = 0
              · simp [h2']
              · exfalso
                have := hinter p ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1⟩,
                  Finset.mem_filter.mpr ⟨Finset.mem_univ _, h2'⟩⟩
                simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hp
                rcases this with rfl | rfl <;> tauto)]
        rw [Finset.sum_pair hp_ne]
        have hv0 : allRowsVec Q (.type1 a b) p0 * allRowsVec Q (.type1 a' b) p0 = 1 := by
          simp [allRowsVec, p0]
        have hv1 : allRowsVec Q (.type1 a b) p1 * allRowsVec Q (.type1 a' b) p1 = -1 := by
          have hne_sub : a * xA + b.1 ≠ a' * xA + b.1 := by
            intro h
            have : (a - a') * xA = 0 := by linear_combination h
            exact hxA_ne ((mul_eq_zero.mp this).resolve_left haa')
          dsimp only [allRowsVec, p1]
          rw [ite_eq_right (fun h => hxA_ne h.1), ite_eq_left ⟨hxQ, rfl⟩,
            ite_eq_right (fun h => hxA_ne h.1), ite_eq_right (fun h => hne_sub h.2),
            ite_eq_left ⟨hxQ, hp1_eq⟩]
          norm_num
        rw [hv0, hv1]; norm_num
      · let p1 : PuncturedPlane F :=
          ⟨(-xA, a * (-xA) - b.1), fun h => neg_ne_zero.mpr hxA_ne (congrArg Prod.fst h)⟩
        have hp1_eq : a * (-xA) - b.1 = a' * (-xA) + b.1 := by
          rw [hxA_neg]
          field_simp [haa']
          ring
        have hp_ne : p0 ≠ p1 := fun h =>
          neg_ne_zero.mpr hxA_ne (congrArg (fun p : PuncturedPlane F => p.1.1) h).symm
        have hinter : ∀ p : PuncturedPlane F,
            p ∈ allRowsSupport Q (.type1 a b) ∧ p ∈ allRowsSupport Q (.type1 a' b) →
            p = p0 ∨ p = p1 := by
          intro p ⟨h1, h2'⟩
          rw [mem_allRowsSupport_type1] at h1 h2'
          rcases h1 with ⟨hx1, hy1⟩ | ⟨hx1, hy1 | hy1⟩ <;>
            rcases h2' with ⟨hx2, hy2⟩ | ⟨hx2, hy2 | hy2⟩
          · exact Or.inl (Subtype.ext (Prod.ext hx1 hy1))
          · exact (Q.ne_zero_of_mem hx2 hx1).elim
          · exact (Q.ne_zero_of_mem hx2 hx1).elim
          · exact (Q.ne_zero_of_mem hx1 hx2).elim
          · exfalso
            have : (a - a') * p.1.1 = 0 := by linear_combination hy1.symm.trans hy2
            exact Q.ne_zero_of_mem hx1 ((mul_eq_zero.mp this).resolve_left haa')
          · exfalso
            have hx : p.1.1 = xA := by
              rw [eq_div_iff haa']
              linear_combination hy1.symm.trans hy2
            exact hxQ (hx ▸ hx1)
          · exact (Q.ne_zero_of_mem hx1 hx2).elim
          · right
            have hx : p.1.1 = -xA := by
              rw [hxA_neg, eq_div_iff haa']
              linear_combination hy1.symm.trans hy2
            exact Subtype.ext (Prod.ext hx (by rw [hy1, hx]))
          · exfalso
            have : (a - a') * p.1.1 = 0 := by linear_combination hy1.symm.trans hy2
            exact Q.ne_zero_of_mem hx1 ((mul_eq_zero.mp this).resolve_left haa')
        have hsub : allRowsSupport Q (.type1 a b) ∩ allRowsSupport Q (.type1 a' b) ⊆ {p0, p1} := by
          intro p hp
          simpa [Finset.mem_insert, Finset.mem_singleton] using hinter p (Finset.mem_inter.mp hp)
        refine ⟨(Finset.card_le_card hsub).trans (Finset.card_le_two), ?_⟩
        rw [← Finset.sum_subset (Finset.subset_univ ({p0, p1} : Finset (PuncturedPlane F)))
          (fun p _ hp => by
            by_cases h1 : allRowsVec Q (.type1 a b) p = 0
            · simp [h1]
            · by_cases h2' : allRowsVec Q (.type1 a' b) p = 0
              · simp [h2']
              · exfalso
                have := hinter p ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1⟩,
                  Finset.mem_filter.mpr ⟨Finset.mem_univ _, h2'⟩⟩
                simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hp
                rcases this with rfl | rfl <;> tauto)]
        rw [Finset.sum_pair hp_ne]
        have hv0 : allRowsVec Q (.type1 a b) p0 * allRowsVec Q (.type1 a' b) p0 = 1 := by
          simp [allRowsVec, p0]
        have hv1 : allRowsVec Q (.type1 a b) p1 * allRowsVec Q (.type1 a' b) p1 = -1 := by
          have hne_add : a * (-xA) - b.1 ≠ a * (-xA) + b.1 :=
            (add_ne_sub_of_mem_halfSet Q hodd b.2 (a * (-xA))).symm
          have hnx0 : -xA ≠ 0 := neg_ne_zero.mpr hxA_ne
          dsimp only [allRowsVec, p1]
          rw [ite_eq_right (fun h => hnx0 h.1), ite_eq_right (fun h => hne_add h.2),
            ite_eq_left ⟨hnxQ, rfl⟩, ite_eq_right (fun h => hnx0 h.1),
            ite_eq_left ⟨hnxQ, hp1_eq⟩]
          norm_num
        rw [hv0, hv1]; norm_num
    · -- `a ≠ a'` and `b ≠ b'`: one same-sign intersection (`+1`) and one opposite-sign (`-1`).
      let x1 : F := (b'.1 - b.1) / (a - a')
      let x2 : F := (b'.1 + b.1) / (a - a')
      have hx1_ne : x1 ≠ 0 := div_ne_zero (sub_ne_zero.mpr fun h => hb (Subtype.ext h.symm)) haa'
      have hx2_ne : x2 ≠ 0 := div_ne_zero (hdisj_sum b'.2 b.2) haa'
      -- Choose the unique point `pPos` in `Q` from `{x1, -x1}` and `pNeg` in `Q` from `{x2, -x2}`.
      have hPos : ∃ pPos : PuncturedPlane F,
          allRowsVec Q (.type1 a b) pPos * allRowsVec Q (.type1 a' b') pPos = 1 ∧
          ∀ p : PuncturedPlane F,
            ((p.1.1 ∈ Q.set ∧ p.1.2 = a * p.1.1 + b.1 ∧ p.1.2 = a' * p.1.1 + b'.1) ∨
             (p.1.1 ∈ Q.set ∧ p.1.2 = a * p.1.1 - b.1 ∧ p.1.2 = a' * p.1.1 - b'.1)) →
            p = pPos := by
        rcases existsUnique_mem_halfSet_pm Q hx1_ne with ⟨hxQ, hnxQ⟩ | ⟨hnxQ, hxQ⟩
        · refine ⟨⟨(x1, a * x1 + b.1), fun h => hx1_ne (congrArg Prod.fst h)⟩, ?_, ?_⟩
          · have heq : a * x1 + b.1 = a' * x1 + b'.1 := by
              simp only [x1]; field_simp [haa']; ring
            simp [allRowsVec, hx1_ne, hxQ, heq]
          · rintro p (⟨_, hy1, hy2⟩ | ⟨hx, hy1, hy2⟩)
            · have hx' : p.1.1 = x1 := by
                rw [eq_div_iff haa']; linear_combination hy1.symm.trans hy2
              exact Subtype.ext (Prod.ext hx' (by rw [hy1, hx']))
            · exfalso
              have hx' : p.1.1 = -x1 := by
                dsimp only [x1]
                rw [← neg_div, eq_div_iff haa']
                linear_combination hy1.symm.trans hy2
              exact hnxQ (hx' ▸ hx)
        · refine ⟨⟨(-x1, a * (-x1) - b.1), fun h =>
              neg_ne_zero.mpr hx1_ne (congrArg Prod.fst h)⟩, ?_, ?_⟩
          · have heq : a * (-x1) - b.1 = a' * (-x1) - b'.1 := by
              simp only [x1]; field_simp [haa']; ring
            have hne1 : a * (-x1) - b.1 ≠ a * (-x1) + b.1 :=
              (add_ne_sub_of_mem_halfSet Q hodd b.2 _).symm
            have hne2 : a * (-x1) - b.1 ≠ a' * (-x1) + b'.1 := by
              rw [heq]; exact (add_ne_sub_of_mem_halfSet Q hodd b'.2 _).symm
            have hnx0 : -x1 ≠ 0 := neg_ne_zero.mpr hx1_ne
            dsimp only [allRowsVec]
            rw [ite_eq_right (fun h => hnx0 h.1), ite_eq_right (fun h => hne1 h.2),
              ite_eq_left ⟨hnxQ, rfl⟩, ite_eq_right (fun h => hnx0 h.1),
              ite_eq_right (fun h => hne2 h.2), ite_eq_left ⟨hnxQ, heq⟩]
            norm_num
          · rintro p (⟨hx, hy1, hy2⟩ | ⟨_, hy1, hy2⟩)
            · exfalso
              have hx' : p.1.1 = x1 := by
                rw [eq_div_iff haa']; linear_combination hy1.symm.trans hy2
              exact hxQ (hx' ▸ hx)
            · have hx' : p.1.1 = -x1 := by
                dsimp only [x1]
                rw [← neg_div, eq_div_iff haa']
                linear_combination hy1.symm.trans hy2
              exact Subtype.ext (Prod.ext hx' (by rw [hy1, hx']))
      have hNeg : ∃ pNeg : PuncturedPlane F,
          allRowsVec Q (.type1 a b) pNeg * allRowsVec Q (.type1 a' b') pNeg = -1 ∧
          ∀ p : PuncturedPlane F,
            ((p.1.1 ∈ Q.set ∧ p.1.2 = a * p.1.1 - b.1 ∧ p.1.2 = a' * p.1.1 + b'.1) ∨
             (p.1.1 ∈ Q.set ∧ p.1.2 = a * p.1.1 + b.1 ∧ p.1.2 = a' * p.1.1 - b'.1)) →
            p = pNeg := by
        rcases existsUnique_mem_halfSet_pm Q hx2_ne with ⟨hxQ, hnxQ⟩ | ⟨hnxQ, hxQ⟩
        · refine ⟨⟨(x2, a * x2 - b.1), fun h => hx2_ne (congrArg Prod.fst h)⟩, ?_, ?_⟩
          · have heq : a * x2 - b.1 = a' * x2 + b'.1 := by
              simp only [x2]; field_simp [haa']; ring
            have hne1 : a * x2 - b.1 ≠ a * x2 + b.1 :=
              (add_ne_sub_of_mem_halfSet Q hodd b.2 _).symm
            dsimp only [allRowsVec]
            rw [ite_eq_right (fun h => hx2_ne h.1), ite_eq_right (fun h => hne1 h.2),
              ite_eq_left ⟨hxQ, rfl⟩, ite_eq_right (fun h => hx2_ne h.1),
              ite_eq_left ⟨hxQ, heq⟩]
            norm_num
          · rintro p (⟨_, hy1, hy2⟩ | ⟨hx, hy1, hy2⟩)
            · have hx' : p.1.1 = x2 := by
                rw [eq_div_iff haa']; linear_combination hy1.symm.trans hy2
              exact Subtype.ext (Prod.ext hx' (by rw [hy1, hx']))
            · exfalso
              have hx' : p.1.1 = -x2 := by
                dsimp only [x2]
                rw [← neg_div, eq_div_iff haa']
                linear_combination hy1.symm.trans hy2
              exact hnxQ (hx' ▸ hx)
        · refine ⟨⟨(-x2, a * (-x2) + b.1), fun h =>
              neg_ne_zero.mpr hx2_ne (congrArg Prod.fst h)⟩, ?_, ?_⟩
          · have heq : a * (-x2) + b.1 = a' * (-x2) - b'.1 := by
              simp only [x2]; field_simp [haa']; ring
            have hne2 : a * (-x2) + b.1 ≠ a' * (-x2) + b'.1 := by
              rw [heq]; exact (add_ne_sub_of_mem_halfSet Q hodd b'.2 _).symm
            have hnx0 : -x2 ≠ 0 := neg_ne_zero.mpr hx2_ne
            dsimp only [allRowsVec]
            rw [ite_eq_right (fun h => hnx0 h.1), ite_eq_left ⟨hnxQ, rfl⟩,
              ite_eq_right (fun h => hnx0 h.1), ite_eq_right (fun h => hne2 h.2),
              ite_eq_left ⟨hnxQ, heq⟩]
            norm_num
          · rintro p (⟨hx, hy1, hy2⟩ | ⟨_, hy1, hy2⟩)
            · exfalso
              have hx' : p.1.1 = x2 := by
                rw [eq_div_iff haa']; linear_combination hy1.symm.trans hy2
              exact hxQ (hx' ▸ hx)
            · have hx' : p.1.1 = -x2 := by
                dsimp only [x2]
                rw [← neg_div, eq_div_iff haa']
                linear_combination hy1.symm.trans hy2
              exact Subtype.ext (Prod.ext hx' (by rw [hy1, hx']))
      obtain ⟨pPos, hvPos, hpPos⟩ := hPos
      obtain ⟨pNeg, hvNeg, hpNeg⟩ := hNeg
      have hp_ne : pPos ≠ pNeg := fun h => by
        rw [h, hvNeg] at hvPos
        exact absurd hvPos (by decide)
      have hinter : ∀ p : PuncturedPlane F,
          p ∈ allRowsSupport Q (.type1 a b) ∧ p ∈ allRowsSupport Q (.type1 a' b') →
          p = pPos ∨ p = pNeg := by
        intro p ⟨h1, h2'⟩
        rw [mem_allRowsSupport_type1] at h1 h2'
        rcases h1 with ⟨hx1, hy1⟩ | ⟨hx1, hy1 | hy1⟩ <;>
          rcases h2' with ⟨hx2, hy2⟩ | ⟨hx2, hy2 | hy2⟩
        · exact (hb (Subtype.ext (hy1.symm.trans hy2))).elim
        · exact (Q.ne_zero_of_mem hx2 hx1).elim
        · exact (Q.ne_zero_of_mem hx2 hx1).elim
        · exact (Q.ne_zero_of_mem hx1 hx2).elim
        · exact Or.inl (hpPos p (Or.inl ⟨hx1, hy1, hy2⟩))
        · exact Or.inr (hpNeg p (Or.inr ⟨hx1, hy1, hy2⟩))
        · exact (Q.ne_zero_of_mem hx1 hx2).elim
        · exact Or.inr (hpNeg p (Or.inl ⟨hx1, hy1, hy2⟩))
        · exact Or.inl (hpPos p (Or.inr ⟨hx1, hy1, hy2⟩))
      have hsub : allRowsSupport Q (.type1 a b) ∩ allRowsSupport Q (.type1 a' b') ⊆
          {pPos, pNeg} := by
        intro p hp
        simpa [Finset.mem_insert, Finset.mem_singleton] using hinter p (Finset.mem_inter.mp hp)
      refine ⟨(Finset.card_le_card hsub).trans Finset.card_le_two, ?_⟩
      rw [← Finset.sum_subset (Finset.subset_univ ({pPos, pNeg} : Finset (PuncturedPlane F)))
        (fun p _ hp => by
          by_cases h1 : allRowsVec Q (.type1 a b) p = 0
          · simp [h1]
          · by_cases h2' : allRowsVec Q (.type1 a' b') p = 0
            · simp [h2']
            · exfalso
              have := hinter p ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1⟩,
                Finset.mem_filter.mpr ⟨Finset.mem_univ _, h2'⟩⟩
              simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hp
              rcases this with rfl | rfl <;> tauto)]
      rw [Finset.sum_pair hp_ne, hvPos, hvNeg]
      norm_num

/-- Negation symmetry on `PuncturedPlane F`: `(x, y) ↦ (-x, -y)` swaps Type-1 and Type-2 rows
with the same slope `a` and parameter `b`. -/
private def negPlaneEquiv : PuncturedPlane F ≃ PuncturedPlane F where
  toFun p := ⟨(-p.1.1, -p.1.2), fun h => p.2 (Prod.ext (neg_eq_zero.mp (congrArg Prod.fst h))
    (neg_eq_zero.mp (congrArg Prod.snd h)))⟩
  invFun p := ⟨(-p.1.1, -p.1.2), fun h => p.2 (Prod.ext (neg_eq_zero.mp (congrArg Prod.fst h))
    (neg_eq_zero.mp (congrArg Prod.snd h)))⟩
  left_inv _ := Subtype.ext (Prod.ext (neg_neg _) (neg_neg _))
  right_inv _ := Subtype.ext (Prod.ext (neg_neg _) (neg_neg _))

private theorem allRowsVec_type2_eq_type1_neg (Q : OddFieldHalfSet F) (a : F) (b : Q.set)
    (p : PuncturedPlane F) :
    allRowsVec Q (.type2 a b) p = allRowsVec Q (.type1 a b) (negPlaneEquiv p) := by
  unfold allRowsVec negPlaneEquiv
  simp only [Equiv.coe_fn_mk, neg_eq_zero, mul_neg]
  have h1 : p.1.2 = -b.1 ↔ -p.1.2 = b.1 := by
    constructor <;> intro h <;> linear_combination -h
  have h2 : p.1.2 = a * p.1.1 - b.1 ↔ -p.1.2 = -(a * p.1.1) + b.1 := by
    constructor <;> intro h <;> linear_combination -h
  have h3 : p.1.2 = a * p.1.1 + b.1 ↔ -p.1.2 = -(a * p.1.1) - b.1 := by
    constructor <;> intro h <;> linear_combination -h
  simp only [h1, h2, h3]

/-- Helper for Type 1 vs Type 3, capturing both intersection bound `≤ 2` and orthogonality. -/
private theorem type1_type3_inter_and_orth (Q : OddFieldHalfSet F) (hodd : Odd (Fintype.card F))
    (a : F) (b : Q.set) (c : {x : F // x ≠ 0}) :
    #(allRowsSupport Q (.type1 a b) ∩ allRowsSupport Q (.type3 c)) ≤ 2 ∧
      ∑ p : PuncturedPlane F,
        allRowsVec Q (.type1 a b) p * allRowsVec Q (.type3 c) p = 0 := by
  by_cases hc : c.1 ∈ Q.set
  · let p1 : PuncturedPlane F := ⟨(c.1, a * c.1 + b.1), fun h => c.2 (congrArg Prod.fst h)⟩
    let p2 : PuncturedPlane F := ⟨(c.1, a * c.1 - b.1), fun h => c.2 (congrArg Prod.fst h)⟩
    have hp_ne : p1 ≠ p2 := fun h =>
      add_ne_sub_of_mem_halfSet Q hodd b.2 (a * c.1)
        (congrArg (fun p : PuncturedPlane F => p.1.2) h)
    have hinter : ∀ p : PuncturedPlane F,
        p ∈ allRowsSupport Q (.type1 a b) ∧ p ∈ allRowsSupport Q (.type3 c) →
        p = p1 ∨ p = p2 := by
      intro p ⟨h1, h3⟩
      rw [mem_allRowsSupport_type1] at h1
      rw [mem_allRowsSupport_type3] at h3
      rcases h1 with ⟨hx0, _⟩ | ⟨_, hy | hy⟩
      · exact (c.2 (h3.symm.trans hx0)).elim
      · exact Or.inl (Subtype.ext (Prod.ext h3 (by rw [hy, h3])))
      · exact Or.inr (Subtype.ext (Prod.ext h3 (by rw [hy, h3])))
    have hsub : allRowsSupport Q (.type1 a b) ∩ allRowsSupport Q (.type3 c) ⊆ {p1, p2} := by
      intro p hp
      simpa [Finset.mem_insert, Finset.mem_singleton] using hinter p (Finset.mem_inter.mp hp)
    refine ⟨(Finset.card_le_card hsub).trans Finset.card_le_two, ?_⟩
    rw [← Finset.sum_subset (Finset.subset_univ ({p1, p2} : Finset (PuncturedPlane F)))
      (fun p _ hp => by
        by_cases h1 : allRowsVec Q (.type1 a b) p = 0
        · simp [h1]
        · by_cases h3 : allRowsVec Q (.type3 c) p = 0
          · simp [h3]
          · exfalso
            have := hinter p ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1⟩,
              Finset.mem_filter.mpr ⟨Finset.mem_univ _, h3⟩⟩
            simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hp
            rcases this with rfl | rfl <;> tauto)]
    rw [Finset.sum_pair hp_ne]
    have hv1 : allRowsVec Q (.type1 a b) p1 * allRowsVec Q (.type3 c) p1 = 1 := by
      simp [allRowsVec, p1, c.2, hc]
    have hv2 : allRowsVec Q (.type1 a b) p2 * allRowsVec Q (.type3 c) p2 = -1 := by
      have hne_add : a * c.1 - b.1 ≠ a * c.1 + b.1 :=
        (add_ne_sub_of_mem_halfSet Q hodd b.2 (a * c.1)).symm
      simp [allRowsVec, p2, c.2, hc, hne_add]
    rw [hv1, hv2]; norm_num
  · have hdisj : ∀ p : PuncturedPlane F,
        ¬(p ∈ allRowsSupport Q (.type1 a b) ∧ p ∈ allRowsSupport Q (.type3 c)) := by
      intro p ⟨h1, h3⟩
      rw [mem_allRowsSupport_type1] at h1
      rw [mem_allRowsSupport_type3] at h3
      rcases h1 with ⟨hx0, _⟩ | ⟨hxQ, _⟩
      · exact c.2 (h3.symm.trans hx0)
      · exact hc (h3 ▸ hxQ)
    refine ⟨?_, ?_⟩
    · have hempty : allRowsSupport Q (.type1 a b) ∩ allRowsSupport Q (.type3 c) = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro p hp
        exact hdisj p (Finset.mem_inter.mp hp)
      simp [hempty]
    · refine Finset.sum_eq_zero fun p _ => ?_
      by_cases h1 : allRowsVec Q (.type1 a b) p = 0
      · simp [h1]
      · by_cases h3 : allRowsVec Q (.type3 c) p = 0
        · simp [h3]
        · exact (hdisj p ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1⟩,
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, h3⟩⟩).elim

/-- the `q^2 - 1` vectors on the punctured plane
(2), (3), and (4) are pairwise orthogonal and their supports have pairwise intersections of
cardinality at most `2`. -/
theorem allRowsVec_inter_and_orthogonal (Q : OddFieldHalfSet F) (hodd : Odd (Fintype.card F))
    {i j : AllRowsIndex F Q} (hij : i ≠ j) :
    #(allRowsSupport Q i ∩ allRowsSupport Q j) ≤ 2 ∧
      ∑ p : PuncturedPlane F, allRowsVec Q i p * allRowsVec Q j p = 0 := by
  have hsymm : ∀ {i j : AllRowsIndex F Q},
      (#(allRowsSupport Q i ∩ allRowsSupport Q j) ≤ 2 ∧
        ∑ p : PuncturedPlane F, allRowsVec Q i p * allRowsVec Q j p = 0) →
      (#(allRowsSupport Q j ∩ allRowsSupport Q i) ≤ 2 ∧
        ∑ p : PuncturedPlane F, allRowsVec Q j p * allRowsVec Q i p = 0) := by
    intro i j ⟨h1, h2⟩
    refine ⟨by rwa [Finset.inter_comm], ?_⟩
    simpa only [mul_comm] using h2
  have htype12 : ∀ (a a' : F) (b b' : Q.set),
      #(allRowsSupport Q (.type1 a b) ∩ allRowsSupport Q (.type2 a' b')) ≤ 2 ∧
        ∑ p : PuncturedPlane F,
          allRowsVec Q (.type1 a b) p * allRowsVec Q (.type2 a' b') p = 0 := by
    intro a a' b b'
    have hdisj : ∀ p : PuncturedPlane F,
        ¬(p ∈ allRowsSupport Q (.type1 a b) ∧ p ∈ allRowsSupport Q (.type2 a' b')) := by
      intro p ⟨h1, h2⟩
      rw [mem_allRowsSupport_type1] at h1
      rw [mem_allRowsSupport_type2] at h2
      rcases h1 with ⟨hx1, hy1⟩ | ⟨hx1, _⟩ <;> rcases h2 with ⟨hx2, hy2⟩ | ⟨hx2, _⟩
      · exact Q.disjoint_neg b'.1 b'.2 ((hy1.symm.trans hy2) ▸ b.2)
      · exact Q.ne_zero_of_mem hx2 (by simp [hx1])
      · exact Q.ne_zero_of_mem hx1 hx2
      · exact Q.disjoint_neg p.1.1 hx1 hx2
    refine ⟨?_, ?_⟩
    · have hempty : allRowsSupport Q (.type1 a b) ∩ allRowsSupport Q (.type2 a' b') = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro p hp
        exact hdisj p (Finset.mem_inter.mp hp)
      simp [hempty]
    · refine Finset.sum_eq_zero fun p _ => ?_
      by_cases h1 : allRowsVec Q (.type1 a b) p = 0
      · simp [h1]
      · by_cases h2 : allRowsVec Q (.type2 a' b') p = 0
        · simp [h2]
        · exact (hdisj p ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1⟩,
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, h2⟩⟩).elim
  cases i with
  | type1 a b =>
    cases j with
    | type1 a' b' =>
      exact type1_type1_inter_and_orth Q hodd fun h =>
        hij (by cases h; rfl)
    | type2 a' b' =>
      exact htype12 a a' b b'
    | type3 c =>
      exact type1_type3_inter_and_orth Q hodd a b c
  | type2 a b =>
    cases j with
    | type1 a' b' =>
      exact hsymm (htype12 a' a b' b)
    | type2 a' b' =>
      have h11 := type1_type1_inter_and_orth Q hodd (a := a) (a' := a') (b := b) (b' := b')
        fun h => hij (by cases h; rfl)
      have hcard :
          #(allRowsSupport Q (.type2 a b) ∩ allRowsSupport Q (.type2 a' b')) =
            #(allRowsSupport Q (.type1 a b) ∩ allRowsSupport Q (.type1 a' b')) := by
        refine Finset.card_bij (fun p _ => negPlaneEquiv p) ?_ ?_ ?_
        · intro p hp
          simp only [Finset.mem_inter, allRowsSupport, Finset.mem_filter, Finset.mem_univ,
            true_and, allRowsVec_type2_eq_type1_neg] at hp ⊢
          exact hp
        · intro p₁ _ p₂ _ h
          exact negPlaneEquiv.injective h
        · intro p hp
          refine ⟨negPlaneEquiv.symm p, ?_, negPlaneEquiv.apply_symm_apply p⟩
          simp only [Finset.mem_inter, allRowsSupport, Finset.mem_filter, Finset.mem_univ,
            true_and, allRowsVec_type2_eq_type1_neg, Equiv.apply_symm_apply] at hp ⊢
          exact hp
      refine ⟨hcard ▸ h11.1, ?_⟩
      simp_rw [allRowsVec_type2_eq_type1_neg]
      rw [Equiv.sum_comp negPlaneEquiv (fun p =>
        allRowsVec Q (.type1 a b) p * allRowsVec Q (.type1 a' b') p)]
      exact h11.2
    | type3 c =>
      let nc : {x : F // x ≠ 0} := ⟨-c.1, neg_ne_zero.mpr c.2⟩
      have h13 := type1_type3_inter_and_orth Q hodd a b nc
      have htype3_neg : ∀ p : PuncturedPlane F,
          allRowsVec Q (.type3 c) p = allRowsVec Q (.type3 nc) (negPlaneEquiv p) := by
        intro p
        dsimp only [allRowsVec, negPlaneEquiv, Equiv.coe_fn_mk, nc]
        have : p.1.1 = c.1 ↔ -p.1.1 = -c.1 := neg_inj.symm
        exact if_congr this rfl rfl
      have hcard :
          #(allRowsSupport Q (.type2 a b) ∩ allRowsSupport Q (.type3 c)) =
            #(allRowsSupport Q (.type1 a b) ∩ allRowsSupport Q (.type3 nc)) := by
        refine Finset.card_bij (fun p _ => negPlaneEquiv p) ?_ ?_ ?_
        · intro p hp
          simp only [Finset.mem_inter, allRowsSupport, Finset.mem_filter, Finset.mem_univ,
            true_and, allRowsVec_type2_eq_type1_neg, htype3_neg] at hp ⊢
          exact hp
        · intro p₁ _ p₂ _ h
          exact negPlaneEquiv.injective h
        · intro p hp
          refine ⟨negPlaneEquiv.symm p, ?_, negPlaneEquiv.apply_symm_apply p⟩
          simp only [Finset.mem_inter, allRowsSupport, Finset.mem_filter, Finset.mem_univ,
            true_and, allRowsVec_type2_eq_type1_neg, htype3_neg,
            Equiv.apply_symm_apply] at hp ⊢
          exact hp
      refine ⟨hcard ▸ h13.1, ?_⟩
      simp_rw [allRowsVec_type2_eq_type1_neg, htype3_neg]
      rw [Equiv.sum_comp negPlaneEquiv (fun p =>
        allRowsVec Q (.type1 a b) p * allRowsVec Q (.type3 nc) p)]
      exact h13.2
  | type3 c =>
    cases j with
    | type1 a' b' =>
      exact hsymm (type1_type3_inter_and_orth Q hodd a' b' c)
    | type2 a' b' =>
      let nc : {x : F // x ≠ 0} := ⟨-c.1, neg_ne_zero.mpr c.2⟩
      have h13 := type1_type3_inter_and_orth Q hodd a' b' nc
      have htype3_neg : ∀ p : PuncturedPlane F,
          allRowsVec Q (.type3 c) p = allRowsVec Q (.type3 nc) (negPlaneEquiv p) := by
        intro p
        dsimp only [allRowsVec, negPlaneEquiv, Equiv.coe_fn_mk, nc]
        have : p.1.1 = c.1 ↔ -p.1.1 = -c.1 := neg_inj.symm
        exact if_congr this rfl rfl
      have h23 :
          #(allRowsSupport Q (.type2 a' b') ∩ allRowsSupport Q (.type3 c)) ≤ 2 ∧
            ∑ p : PuncturedPlane F,
              allRowsVec Q (.type2 a' b') p * allRowsVec Q (.type3 c) p = 0 := by
        have hcard :
            #(allRowsSupport Q (.type2 a' b') ∩ allRowsSupport Q (.type3 c)) =
              #(allRowsSupport Q (.type1 a' b') ∩ allRowsSupport Q (.type3 nc)) := by
          refine Finset.card_bij (fun p _ => negPlaneEquiv p) ?_ ?_ ?_
          · intro p hp
            simp only [Finset.mem_inter, allRowsSupport, Finset.mem_filter, Finset.mem_univ,
              true_and, allRowsVec_type2_eq_type1_neg, htype3_neg] at hp ⊢
            exact hp
          · intro p₁ _ p₂ _ h
            exact negPlaneEquiv.injective h
          · intro p hp
            refine ⟨negPlaneEquiv.symm p, ?_, negPlaneEquiv.apply_symm_apply p⟩
            simp only [Finset.mem_inter, allRowsSupport, Finset.mem_filter, Finset.mem_univ,
              true_and, allRowsVec_type2_eq_type1_neg, htype3_neg,
              Equiv.apply_symm_apply] at hp ⊢
            exact hp
        refine ⟨hcard ▸ h13.1, ?_⟩
        simp_rw [allRowsVec_type2_eq_type1_neg, htype3_neg]
        rw [Equiv.sum_comp negPlaneEquiv (fun p =>
          allRowsVec Q (.type1 a' b') p * allRowsVec Q (.type3 nc) p)]
        exact h13.2
      exact hsymm h23
    | type3 c' =>
      have hcc' : c.1 ≠ c'.1 := fun h => hij (by rw [Subtype.ext h])
      have hempty : allRowsSupport Q (.type3 c) ∩ allRowsSupport Q (.type3 c') = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro p hp
        rw [Finset.mem_inter, mem_allRowsSupport_type3, mem_allRowsSupport_type3] at hp
        exact hcc' (hp.1.symm.trans hp.2)
      refine ⟨by simp [hempty], Finset.sum_eq_zero fun p _ => ?_⟩
      dsimp only [allRowsVec]
      split_ifs with h1 h2
      · exact (hcc' (h1.symm.trans h2)).elim
      · ring
      · ring
      · ring

/-- orthogonality corollary. -/
theorem allRowsVec_orthogonal (Q : OddFieldHalfSet F) (hodd : Odd (Fintype.card F))
    {i j : AllRowsIndex F Q} (hij : i ≠ j) :
    ∑ p : PuncturedPlane F, allRowsVec Q i p * allRowsVec Q j p = 0 :=
  (allRowsVec_inter_and_orthogonal Q hodd hij).2

/-- the supports of all `q^2 - 1`
vectors form a `(q, 2)`-design in a universe of size `q^2 - 1`. -/
noncomputable def allRowsDesign (Q : OddFieldHalfSet F) (hodd : Odd (Fintype.card F)) :
    Design (Fintype.card F ^ 2 - 1) (Fintype.card F) 2 (Fintype.card F ^ 2 - 1) :=
  letI := instFintypeAllRowsIndex Q
  let eU : PuncturedPlane F ≃ Fin (Fintype.card F ^ 2 - 1) :=
    Fintype.equivFinOfCardEq card_puncturedPlane
  let eI : AllRowsIndex F Q ≃ Fin (Fintype.card F ^ 2 - 1) :=
    Fintype.equivFinOfCardEq (card_allRowsIndex Q)
  { block := fun i => (allRowsSupport Q (eI.symm i)).map eU.toEmbedding
    card_block := fun i => by
      rw [Finset.card_map, card_allRowsSupport Q hodd]
    card_inter_le := fun {i j} hij => by
      rw [← Finset.map_inter, Finset.card_map]
      exact (allRowsVec_inter_and_orthogonal Q hodd
        (fun h => hij (eI.symm.injective h))).1 }

/-- The square `(q^2 - 1) × (q^2 - 1)` sign-orthogonal matrix from the punctured-plane
construction in which all rows
participate. -/
noncomputable def allRowsMatrix (Q : OddFieldHalfSet F) :
    Matrix (Fin (Fintype.card F ^ 2 - 1)) (Fin (Fintype.card F ^ 2 - 1)) ℤ :=
  letI := instFintypeAllRowsIndex Q
  let eU : PuncturedPlane F ≃ Fin (Fintype.card F ^ 2 - 1) :=
    Fintype.equivFinOfCardEq card_puncturedPlane
  let eI : AllRowsIndex F Q ≃ Fin (Fintype.card F ^ 2 - 1) :=
    Fintype.equivFinOfCardEq (card_allRowsIndex Q)
  Matrix.of fun i j => allRowsVec Q (eI.symm i) (eU.symm j)

/-- `allRowsMatrix Q` is a sign-orthogonal matrix (and hence `normalizedRowMatrix` gives a
`(q^2 - 1) × (q^2 - 1)` unitary matrix whose every row has support size `q` and pairwise
intersection at most `2`). -/
theorem allRowsMatrix_isSignOrthogonal (Q : OddFieldHalfSet F) (hodd : Odd (Fintype.card F)) :
    IsSignOrthogonalMatrix (allRowsMatrix Q) := by
  let eU : PuncturedPlane F ≃ Fin (Fintype.card F ^ 2 - 1) :=
    Fintype.equivFinOfCardEq card_puncturedPlane
  let eI : AllRowsIndex F Q ≃ Fin (Fintype.card F ^ 2 - 1) :=
    Fintype.equivFinOfCardEq (card_allRowsIndex Q)
  refine ⟨fun i j => allRowsVec_entries Q _ _, fun i => ?_, fun i j hij => ?_⟩
  · have hpos : 0 < #(allRowsSupport Q (eI.symm i)) := by
      rw [card_allRowsSupport Q hodd]
      exact Fintype.card_pos
    obtain ⟨p, hp⟩ := Finset.card_pos.mp hpos
    refine ⟨eU p, ?_⟩
    rw [mem_rowSupport]
    simpa [allRowsMatrix, eU, eI, allRowsSupport] using hp
  · have hsum :
        ∑ k : Fin (Fintype.card F ^ 2 - 1),
          allRowsMatrix Q i k * allRowsMatrix Q j k =
        ∑ p : PuncturedPlane F,
          allRowsVec Q (eI.symm i) p * allRowsVec Q (eI.symm j) p := by
      simpa [allRowsMatrix, eU, eI] using
        (Equiv.sum_comp eU.symm (fun p => allRowsVec Q (eI.symm i) p * allRowsVec Q (eI.symm j) p))
    rw [hsum]
    exact allRowsVec_orthogonal Q hodd fun h => hij (eI.symm.injective h)

/-- The `(q^2 - 1) × (q^2 - 1)` unitary matrix of the punctured-plane construction in which
all rows participate. -/
noncomputable def allRowsUnitary (Q : OddFieldHalfSet F) (hodd : Odd (Fintype.card F)) :
    Matrix.unitaryGroup (Fin (Fintype.card F ^ 2 - 1)) ℂ :=
  normalizedRowMatrix (allRowsMatrix Q) (allRowsMatrix_isSignOrthogonal Q hodd)

end AllRows

end CslibFrontier.Foundations.Combinatorics.Design
