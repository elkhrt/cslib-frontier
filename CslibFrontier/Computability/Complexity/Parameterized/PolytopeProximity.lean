module

public import CslibFrontier.Computability.Complexity.Parameterized
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.IntBinary
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Unary
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Rat.Defs

import Mathlib.Data.Finset.Max
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Bounded Polytope Vertices and CGST Proximity

Defines bounded-coefficient integer linear programming (ILP) instances and proves two
foundational polyhedral geometry theorems over `ℚ`: vertex existence for nonempty bounded
polytopes, and the Cook–Gerards–Schrijver–Tardos (CGST) proximity bound for arbitrary
feasible rational points.

## Main definitions

- `CslibFrontier.Complexity.BoundedCoeffILPInstance`: integer linear system `A x ≤ b` with box
  bounds `lower ≤ x ≤ upper`.
- `CslibFrontier.Complexity.BoundedCoeffILPInstance.enc`: multi-tape binary encoding via
  `enc_structure` (with unary `numVars`).
- `CslibFrontier.Complexity.maxAbsCoeff`, `CslibFrontier.Complexity.ilpParam`: maximum absolute
  constraint coefficient and parameter `numVars + maxAbsCoeff`.
- `CslibFrontier.Complexity.BoundedCoeffILP`: set of integer-feasible instances.

## Main results

- `CslibFrontier.Complexity.exists_vertex_of_bounded_polytope`: every nonempty bounded rational
  polytope has a vertex defined by `p` linearly independent active rows.
- `CslibFrontier.Complexity.boundedCoeffILP_proximity`: Cook–Gerards–Schrijver–Tardos proximity
  bound `|x* j - y* j| ≤ p! * (max 1 W) ^ p` for any feasible rational point `y*`.
-/

public section

namespace CslibFrontier.Complexity

open Cslib Cslib.Complexity Turing.MultiTapeTM ComputableInPolyTime Matrix

/-! ### 1. Instance, Encoding, Semantics, and Parameter -/

/-- An integer linear programming feasibility instance `A x ≤ b` with box bounds
`lower ≤ x ≤ upper` on `numVars` variables. -/
@[ext]
structure BoundedCoeffILPInstance where
  /-- Number of integer decision variables `d`. -/
  numVars : ℕ
  /-- Constraint matrix rows `A_i` of length `numVars`. -/
  rows : List (List ℤ)
  /-- Right-hand side vector `b` of linear upper bounds `A_i · x ≤ b_i`. -/
  rhs : List ℤ
  /-- Coordinatewise integer lower-bound vector `l` (`l_j ≤ x_j`). -/
  lower : List ℤ
  /-- Coordinatewise integer upper-bound vector `u` (`x_j ≤ u_j`). -/
  upper : List ℤ

namespace BoundedCoeffILPInstance

/-- Structured multi-tape binary encoding with unary variable count and signed-binary entries. -/
enc_structure enc : BoundedCoeffILPInstance where
  numVars : encUnary,
  rows : (encList (encList encIntBin)),
  rhs : (encList encIntBin),
  lower : (encList encIntBin),
  upper : (encList encIntBin)

/-- Rational feasibility of `y : Fin inst.numVars → ℚ`. -/
@[expose] def IsFeasibleRat (inst : BoundedCoeffILPInstance) (y : Fin inst.numVars → ℚ) : Prop :=
  (∀ j : Fin inst.numVars,
    (inst.lower.getD j.1 0 : ℚ) ≤ y j ∧ y j ≤ (inst.upper.getD j.1 0 : ℚ)) ∧
  ∀ i : Fin inst.rows.length,
    ∑ j : Fin inst.numVars, ((inst.rows.getD i.1 []).getD j.1 0 : ℚ) * y j ≤
      (inst.rhs.getD i.1 0 : ℚ)

/-- Integer feasibility of `x : Fin inst.numVars → ℤ`. -/
@[expose] def IsFeasibleInt (inst : BoundedCoeffILPInstance) (x : Fin inst.numVars → ℤ) : Prop :=
  (∀ j : Fin inst.numVars,
    inst.lower.getD j.1 0 ≤ x j ∧ x j ≤ inst.upper.getD j.1 0) ∧
  ∀ i : Fin inst.rows.length,
    ∑ j : Fin inst.numVars, (inst.rows.getD i.1 []).getD j.1 0 * x j ≤ inst.rhs.getD i.1 0

theorem IsFeasibleInt.isFeasibleRat {inst : BoundedCoeffILPInstance} {x : Fin inst.numVars → ℤ}
    (hx : inst.IsFeasibleInt x) : inst.IsFeasibleRat (fun j ↦ (x j : ℚ)) := by
  refine ⟨fun j ↦ ⟨Int.cast_le.mpr (hx.1 j).1, Int.cast_le.mpr (hx.1 j).2⟩, fun i ↦ ?_⟩
  have hi := hx.2 i
  have hcast : (∑ j : Fin inst.numVars, ((inst.rows.getD i.1 []).getD j.1 0 : ℚ) * (x j : ℚ)) =
      ((∑ j : Fin inst.numVars, (inst.rows.getD i.1 []).getD j.1 0 * x j : ℤ) : ℚ) := by
    push_cast; rfl
  rw [hcast]
  exact_mod_cast hi

end BoundedCoeffILPInstance

/-- Alias for the encoding of `BoundedCoeffILPInstance`. -/
abbrev encBoundedCoeffILP : BoundedCoeffILPInstance ↪ List Bool := BoundedCoeffILPInstance.enc

/-- Maximum absolute value of a coefficient in the first `numVars` columns of `rows`. -/
@[expose] def maxAbsCoeff (inst : BoundedCoeffILPInstance) : ℕ :=
  inst.rows.foldl (fun acc row ↦
    max acc (((List.range inst.numVars).map fun j ↦ (row.getD j 0).natAbs).foldl max 0)) 0

/-- Parameter for bounded-coefficient ILP: variable count plus maximum coefficient magnitude. -/
@[expose] def ilpParam (inst : BoundedCoeffILPInstance) : ℕ :=
  inst.numVars + maxAbsCoeff inst

/-- The decision problem of bounded-coefficient ILP feasibility. -/
@[expose] def BoundedCoeffILP : Set BoundedCoeffILPInstance :=
  { inst | ∃ x, inst.IsFeasibleInt x }

private theorem le_foldl_max_init (l : List ℕ) (acc : ℕ) : acc ≤ l.foldl max acc := by
  induction l generalizing acc with
  | nil => exact le_rfl
  | cons a t ih => exact (le_max_left acc a).trans (ih (max acc a))

private theorem mem_le_foldl_max {l : List ℕ} {x : ℕ} (hx : x ∈ l) (acc : ℕ) :
    x ≤ l.foldl max acc := by
  induction l generalizing acc with
  | nil => simp at hx
  | cons a t ih =>
    rcases List.mem_cons.mp hx with rfl | ht
    · exact (le_max_right acc x).trans (le_foldl_max_init t (max acc x))
    · exact ih ht (max acc a)

/-- Every entry in the first `numVars` columns of `rows` has absolute value at most
`maxAbsCoeff inst`. -/
theorem le_maxAbsCoeff (inst : BoundedCoeffILPInstance) (i : Fin inst.rows.length)
    (j : Fin inst.numVars) :
    ((inst.rows.getD i.1 []).getD j.1 0).natAbs ≤ maxAbsCoeff inst := by
  unfold maxAbsCoeff
  have hrow_mem : inst.rows.getD i.1 [] ∈ inst.rows := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem i.isLt, Option.getD_some]
    exact List.getElem_mem i.isLt
  have hj_mem : ((inst.rows.getD i.1 []).getD j.1 0).natAbs ∈
      (List.range inst.numVars).map (fun k ↦ ((inst.rows.getD i.1 []).getD k 0).natAbs) :=
    List.mem_map.mpr ⟨j.1, List.mem_range.mpr j.isLt, rfl⟩
  have hrow_le : ((inst.rows.getD i.1 []).getD j.1 0).natAbs ≤
      (((List.range inst.numVars).map fun k ↦
        ((inst.rows.getD i.1 []).getD k 0).natAbs).foldl max 0) :=
    mem_le_foldl_max hj_mem 0
  let f : List ℤ → ℕ := fun row ↦
    ((List.range inst.numVars).map fun k ↦ (row.getD k 0).natAbs).foldl max 0
  have hfold : ∀ (rows : List (List ℤ)) (r : List ℤ) (acc : ℕ), r ∈ rows →
      f r ≤ rows.foldl (fun a row ↦ max a (f row)) acc := by
    intro rows r acc hr
    induction rows generalizing acc with
    | nil => simp at hr
    | cons hd tl ih =>
      rcases List.mem_cons.mp hr with rfl | htl
      · exact (le_max_right acc (f r)).trans (by
          have hmono : ∀ (l : List (List ℤ)) (a : ℕ),
              a ≤ l.foldl (fun a row ↦ max a (f row)) a := by
            intro l
            induction l with
            | nil => intro _; exact le_rfl
            | cons x xs ihx => intro a; exact (le_max_left a (f x)).trans (ihx (max a (f x)))
          exact hmono tl (max acc (f r)))
      · exact ih (max acc (f hd)) htl
  exact hrow_le.trans (hfold inst.rows _ 0 hrow_mem)

/-! ### 2. Linear Algebra Helpers for Active Row Rank -/

private lemma range_transpose_mulVecLin_eq_span {q p : ℕ} (M : Matrix (Fin q) (Fin p) ℚ)
    (E : Finset (Fin q)) :
    LinearMap.range (M.submatrix (Subtype.val : E → Fin q) id)ᵀ.mulVecLin =
      Submodule.span ℚ ((fun i ↦ M i) '' (E : Set (Fin q))) := by
  rw [Matrix.range_mulVecLin]
  congr 1
  ext v
  simp only [Set.mem_range, Set.mem_image, Finset.mem_coe]
  constructor
  · rintro ⟨⟨i, hi⟩, rfl⟩; exact ⟨i, hi, rfl⟩
  · rintro ⟨i, hi, rfl⟩; exact ⟨⟨i, hi⟩, rfl⟩

private lemma exists_nonzero_ker_of_finrank_lt {q p : ℕ} (M : Matrix (Fin q) (Fin p) ℚ)
    (E : Finset (Fin q))
    (h : Module.finrank ℚ (Submodule.span ℚ ((fun i ↦ M i) '' (E : Set (Fin q)))) < p) :
    ∃ u : Fin p → ℚ, u ≠ 0 ∧ ∀ i ∈ E, M i ⬝ᵥ u = 0 := by
  let ME : Matrix E (Fin p) ℚ := M.submatrix Subtype.val id
  have hrank_eq : ME.rank =
      Module.finrank ℚ (Submodule.span ℚ ((fun i ↦ M i) '' (E : Set (Fin q)))) := by
    rw [← Matrix.rank_transpose, Matrix.rank, range_transpose_mulVecLin_eq_span]
  have hadd := LinearMap.finrank_range_add_finrank_ker ME.mulVecLin
  rw [Module.finrank_fin_fun ℚ] at hadd
  change ME.rank + Module.finrank ℚ (LinearMap.ker ME.mulVecLin) = p at hadd
  have hker_pos : 0 < Module.finrank ℚ (LinearMap.ker ME.mulVecLin) := by omega
  have hker_ne : LinearMap.ker ME.mulVecLin ≠ ⊥ := by
    intro hbot; rw [hbot, finrank_bot] at hker_pos; omega
  obtain ⟨u, hu_mem, hu_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker_ne
  refine ⟨u, hu_ne, fun i hi ↦ ?_⟩
  have hzero : (ME *ᵥ u) ⟨i, hi⟩ = 0 := congrFun (LinearMap.mem_ker.mp hu_mem) ⟨i, hi⟩
  simpa [ME, Matrix.mulVec] using hzero

private lemma exists_ker_not_mem_span_of_finrank_le {q p : ℕ} (M : Matrix (Fin q) (Fin p) ℚ)
    (E : Finset (Fin q)) (z : Fin p → ℚ)
    (h : Module.finrank ℚ (Submodule.span ℚ ((fun i ↦ M i) '' (E : Set (Fin q)))) + 2 ≤ p) :
    ∃ u : Fin p → ℚ, (∀ i ∈ E, M i ⬝ᵥ u = 0) ∧ u ∉ Submodule.span ℚ ({z} : Set (Fin p → ℚ)) := by
  let ME : Matrix E (Fin p) ℚ := M.submatrix Subtype.val id
  have hrank_eq : ME.rank =
      Module.finrank ℚ (Submodule.span ℚ ((fun i ↦ M i) '' (E : Set (Fin q)))) := by
    rw [← Matrix.rank_transpose, Matrix.rank, range_transpose_mulVecLin_eq_span]
  have hadd := LinearMap.finrank_range_add_finrank_ker ME.mulVecLin
  rw [Module.finrank_fin_fun ℚ] at hadd
  change ME.rank + Module.finrank ℚ (LinearMap.ker ME.mulVecLin) = p at hadd
  have hker_ge2 : 2 ≤ Module.finrank ℚ (LinearMap.ker ME.mulVecLin) := by omega
  have hspan_le1 : Module.finrank ℚ (Submodule.span ℚ ({z} : Set (Fin p → ℚ))) ≤ 1 :=
    (finrank_span_le_card ({z} : Set (Fin p → ℚ))).trans (by simp)
  have hnot_le : ¬ LinearMap.ker ME.mulVecLin ≤ Submodule.span ℚ ({z} : Set (Fin p → ℚ)) := by
    intro hle
    have := Submodule.finrank_mono hle
    omega
  obtain ⟨u, hu_ker, hu_not⟩ :
      ∃ u ∈ LinearMap.ker ME.mulVecLin, u ∉ Submodule.span ℚ ({z} : Set (Fin p → ℚ)) := by
    by_contra h; push Not at h; exact hnot_le h
  refine ⟨u, fun i hi ↦ ?_, hu_not⟩
  have hzero : (ME *ᵥ u) ⟨i, hi⟩ = 0 := congrFun (LinearMap.mem_ker.mp hu_ker) ⟨i, hi⟩
  simpa [ME, Matrix.mulVec] using hzero

private lemma finrank_span_lt_of_not_mem {q p : ℕ} (M : Matrix (Fin q) (Fin p) ℚ)
    {E E' : Finset (Fin q)} (hsub : E ⊆ E') {i₀ : Fin q} (hi₀ : i₀ ∈ E')
    {u : Fin p → ℚ} (huE : ∀ i ∈ E, M i ⬝ᵥ u = 0) (hui₀ : M i₀ ⬝ᵥ u ≠ 0) :
    Module.finrank ℚ (Submodule.span ℚ ((fun i ↦ M i) '' (E : Set (Fin q)))) <
      Module.finrank ℚ (Submodule.span ℚ ((fun i ↦ M i) '' (E' : Set (Fin q)))) := by
  set S := Submodule.span ℚ ((fun i ↦ M i) '' (E : Set (Fin q)))
  set S' := Submodule.span ℚ ((fun i ↦ M i) '' (E' : Set (Fin q)))
  have hle : S ≤ S' := Submodule.span_mono (Set.image_mono (Finset.coe_subset.mpr hsub))
  have hnot : M i₀ ∉ S := by
    intro hmem
    have h0 : M i₀ ⬝ᵥ u = 0 := by
      refine Submodule.span_induction ?_ (by simp) (fun x y _ _ hx hy ↦ by
        rw [add_dotProduct, hx, hy, add_zero]) (fun c x _ hx ↦ by
        rw [smul_dotProduct, hx, smul_zero]) hmem
      rintro _ ⟨i, hi, rfl⟩
      exact huE i hi
    exact hui₀ h0
  have hmem' : M i₀ ∈ S' := Submodule.subset_span ⟨i₀, hi₀, rfl⟩
  exact Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne hle (fun heq ↦ hnot (heq ▸ hmem')))

private lemma exists_basis_indices_of_finrank_eq {q p r : ℕ} (M : Matrix (Fin q) (Fin p) ℚ)
    (E : Finset (Fin q))
    (hr : Module.finrank ℚ (Submodule.span ℚ ((fun i ↦ M i) '' (E : Set (Fin q)))) = r) :
    ∃ I : Fin r → Fin q, (∀ k, I k ∈ E) ∧ LinearIndependent ℚ (fun k ↦ M (I k)) ∧
      Submodule.span ℚ (Set.range (fun k ↦ M (I k))) =
        Submodule.span ℚ ((fun i ↦ M i) '' (E : Set (Fin q))) := by
  classical
  set S := Submodule.span ℚ ((fun i ↦ M i) '' (E : Set (Fin q)))
  obtain ⟨B, hB_sub, hB_span, hB_li⟩ :=
    exists_linearIndependent ℚ ((fun i ↦ M i) '' (E : Set (Fin q)))
  have hB_fin : B.Finite := ((E.finite_toSet.image (fun i ↦ M i)).subset hB_sub)
  let _ : Fintype B := hB_fin.fintype
  let bS : Module.Basis B ℚ S :=
    Module.Basis.mk
      (v := fun x : B ↦ (⟨x.1, Submodule.subset_span (hB_sub x.2)⟩ : S))
      (hB_li.of_comp S.subtype)
      (by
        intro ⟨v, hv⟩ _
        have hvB : v ∈ Submodule.span ℚ B := hB_span.symm ▸ hv
        have hgoal : ∀ w ∈ Submodule.span ℚ B, ∀ hw : w ∈ S,
            (⟨w, hw⟩ : S) ∈ Submodule.span ℚ
              (Set.range fun x : B ↦ (⟨x.1, Submodule.subset_span (hB_sub x.2)⟩ : S)) := by
          intro w hwB
          refine Submodule.span_induction ?_ (fun _ ↦ Submodule.zero_mem _)
            (fun x y hxB hyB hx hy hxy ↦ ?_) (fun c x hxB hx hcx ↦ ?_) hwB
          · intro x hxB _
            exact Submodule.subset_span ⟨⟨x, hxB⟩, rfl⟩
          · have hxS : x ∈ S := by dsimp only [S]; rwa [← hB_span]
            have hyS : y ∈ S := by dsimp only [S]; rwa [← hB_span]
            exact Submodule.add_mem _ (hx hxS) (hy hyS)
          · have hxS : x ∈ S := by dsimp only [S]; rwa [← hB_span]
            exact Submodule.smul_mem _ c (hx hxS)
        exact hgoal v hvB hv)
  have hcard : Fintype.card B = r := by
    have := Module.finrank_eq_card_basis bS
    omega
  let e : Fin r ≃ B := (Fintype.equivFinOfCardEq hcard).symm
  have hmem_img : ∀ k : Fin r, ∃ i ∈ E, M i = (e k).1 := fun k ↦ hB_sub (e k).2
  choose I hIE hIM using hmem_img
  refine ⟨I, hIE, ?_, ?_⟩
  · have hli : LinearIndependent ℚ (fun k : Fin r ↦ (e k).1) :=
      hB_li.comp e e.injective
    simpa only [hIM] using hli
  · have hrange : Set.range (fun k ↦ M (I k)) = B := by
      ext v
      simp only [Set.mem_range, hIM]
      constructor
      · rintro ⟨k, rfl⟩; exact (e k).2
      · intro hv; exact ⟨e.symm ⟨v, hv⟩, by simp⟩
    rw [hrange, hB_span]

/-! ### 3. Bounded Polytope Vertex Existence -/

/-- Every nonempty bounded rational polytope `{y | M *ᵥ y ≤ h}` has a vertex where `p` linearly
independent rows are active (`(M *ᵥ y*) (I k) = h (I k)`). -/
theorem exists_vertex_of_bounded_polytope {q p : ℕ}
    (M : Matrix (Fin q) (Fin p) ℚ) (h : Fin q → ℚ) (L U : Fin p → ℚ)
    (hne : ∃ y : Fin p → ℚ, ∀ i, (M *ᵥ y) i ≤ h i)
    (hbdd : ∀ y : Fin p → ℚ, (∀ i, (M *ᵥ y) i ≤ h i) → ∀ j, L j ≤ y j ∧ y j ≤ U j) :
    ∃ (y : Fin p → ℚ) (I : Fin p → Fin q),
      (∀ i, (M *ᵥ y) i ≤ h i) ∧
      LinearIndependent ℚ (fun k ↦ M (I k)) ∧
      ∀ k, (M *ᵥ y) (I k) = h (I k) := by
  classical
  let Eof : (Fin p → ℚ) → Finset (Fin q) := fun y ↦
    Finset.univ.filter fun i ↦ (M *ᵥ y) i = h i
  let rOf : (Fin p → ℚ) → ℕ := fun y ↦
    Module.finrank ℚ (Submodule.span ℚ ((fun i ↦ M i) '' (Eof y : Set (Fin q))))
  have hr_le : ∀ y, rOf y ≤ p := fun y ↦ by
    simpa [Module.finrank_fin_fun] using
      Submodule.finrank_le (Submodule.span ℚ ((fun i ↦ M i) '' (Eof y : Set (Fin q))))
  let Rset : Finset ℕ := (Finset.range (p + 1)).filter fun r ↦
    ∃ y : Fin p → ℚ, (∀ i, (M *ᵥ y) i ≤ h i) ∧ rOf y = r
  obtain ⟨y₀, hy₀⟩ := hne
  have hRne : Rset.Nonempty :=
    ⟨rOf y₀, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (hr_le y₀)),
      ⟨y₀, hy₀, rfl⟩⟩⟩
  obtain ⟨rmax, hrmax_mem, hrmax_ge⟩ := Finset.exists_max_image Rset id hRne
  obtain ⟨_, ⟨y, hy, hry⟩⟩ := Finset.mem_filter.mp hrmax_mem
  have hr_eq_p : rOf y = p := by
    by_contra hne_p
    have hlt_p : rOf y < p := lt_of_le_of_ne (hr_le y) hne_p
    obtain ⟨u, hu_ne, huE⟩ := exists_nonzero_ker_of_finrank_lt M (Eof y) hlt_p
    have hj0 : ∃ j : Fin p, u j ≠ 0 := by
      by_contra hall; push Not at hall; exact hu_ne (funext hall)
    obtain ⟨j₀, hj₀⟩ := hj0
    let v : Fin p → ℚ := if 0 < u j₀ then u else -u
    have hv_pos : 0 < v j₀ := by
      dsimp only [v]; split_ifs with h1
      · exact h1
      · have : u j₀ < 0 := lt_of_le_of_ne (not_lt.mp h1) hj₀
        simp only [Pi.neg_apply]; linarith
    have hvE : ∀ i ∈ Eof y, M i ⬝ᵥ v = 0 := fun i hi ↦ by
      dsimp only [v]; split_ifs
      · exact huE i hi
      · rw [dotProduct_neg, huE i hi, neg_zero]
    have hex_pos : ∃ i : Fin q, 0 < M i ⬝ᵥ v := by
      by_contra hno; push Not at hno
      have hfeas : ∀ t : ℚ, 0 ≤ t → ∀ i, (M *ᵥ (y + t • v)) i ≤ h i := by
        intro t ht i
        have hmul : (M *ᵥ (y + t • v)) i = (M *ᵥ y) i + t * (M i ⬝ᵥ v) := by
          simp [Matrix.mulVec, dotProduct_add, dotProduct_smul]
        rw [hmul]; nlinarith [hy i, hno i]
      let t : ℚ := (U j₀ - y j₀ + 1) / v j₀
      have hUy := (hbdd y hy j₀).2
      have ht_pos : 0 ≤ t := div_nonneg (by linarith) hv_pos.le
      have hU' := (hbdd (y + t • v) (hfeas t ht_pos) j₀).2
      have hval : (y + t • v) j₀ = U j₀ + 1 := by
        simp [Pi.add_apply, Pi.smul_apply, t]; field_simp [hv_pos.ne']; ring
      linarith
    let Ppos : Finset (Fin q) := Finset.univ.filter fun i ↦ 0 < M i ⬝ᵥ v
    have hPne : Ppos.Nonempty := by
      obtain ⟨i, hi⟩ := hex_pos
      exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
    let ratio : Fin q → ℚ := fun i ↦ (h i - (M *ᵥ y) i) / (M i ⬝ᵥ v)
    obtain ⟨i₀, hi₀_mem, hi₀_min⟩ := Finset.exists_min_image Ppos ratio hPne
    have hi₀_pos : 0 < M i₀ ⬝ᵥ v := (Finset.mem_filter.mp hi₀_mem).2
    let t₀ : ℚ := ratio i₀
    have ht₀_nonneg : 0 ≤ t₀ := div_nonneg (sub_nonneg.mpr (hy i₀)) hi₀_pos.le
    let y' : Fin p → ℚ := y + t₀ • v
    have hy' : ∀ i, (M *ᵥ y') i ≤ h i := by
      intro i
      have hmul : (M *ᵥ y') i = (M *ᵥ y) i + t₀ * (M i ⬝ᵥ v) := by
        simp [y', Matrix.mulVec, dotProduct_add, dotProduct_smul]
      rw [hmul]
      by_cases hpos : 0 < M i ⬝ᵥ v
      · have hle := hi₀_min i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpos⟩)
        have h1 : t₀ * (M i ⬝ᵥ v) ≤ h i - (M *ᵥ y) i := (le_div_iff₀ hpos).mp hle
        linarith
      · nlinarith [hy i, not_lt.mp hpos]
    have hsub : Eof y ⊆ Eof y' := by
      intro i hi
      rw [Finset.mem_filter] at hi ⊢
      refine ⟨Finset.mem_univ _, ?_⟩
      have hmul : (M *ᵥ y') i = (M *ᵥ y) i + t₀ * (M i ⬝ᵥ v) := by
        simp [y', Matrix.mulVec, dotProduct_add, dotProduct_smul]
      rw [hmul, hvE i (Finset.mem_filter.mpr hi), mul_zero, add_zero, hi.2]
    have hi₀_act : i₀ ∈ Eof y' := by
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      have hmul : (M *ᵥ y') i₀ = (M *ᵥ y) i₀ + t₀ * (M i₀ ⬝ᵥ v) := by
        simp [y', Matrix.mulVec, dotProduct_add, dotProduct_smul]
      rw [hmul]
      dsimp only [t₀, ratio]
      rw [div_mul_cancel₀ _ hi₀_pos.ne']
      ring
    have hlt_r : rOf y < rOf y' :=
      finrank_span_lt_of_not_mem M hsub hi₀_act hvE hi₀_pos.ne'
    have hmem_y' : rOf y' ∈ Rset :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (hr_le y')), ⟨y', hy', rfl⟩⟩
    have hge := hrmax_ge (rOf y') hmem_y'
    dsimp only [id] at hge
    omega
  obtain ⟨I, hIE, hIli, _⟩ := exists_basis_indices_of_finrank_eq M (Eof y) hr_eq_p
  exact ⟨y, I, hy, hIli, fun k ↦ (Finset.mem_filter.mp (hIE k)).2⟩

/-! ### 4. Integer Ray Bound, Pointed Cone Decomposition, Carathéodory, and CGST Proximity -/

private lemma exists_int_ray_of_finrank_eq_pred {q n : ℕ}
    (M : Matrix (Fin q) (Fin (n + 1)) ℤ) (E : Finset (Fin q)) (W : ℕ)
    (hW : ∀ i j, (M i j).natAbs ≤ W)
    (hE : Module.finrank ℚ (Submodule.span ℚ
      ((fun i ↦ (fun j ↦ (M i j : ℚ))) '' (E : Set (Fin q)))) = n)
    (z : Fin (n + 1) → ℚ) (hz : z ≠ 0)
    (hzE : ∀ i ∈ E, (fun j ↦ (M i j : ℚ)) ⬝ᵥ z = 0) :
    ∃ (g : Fin (n + 1) → ℤ) (c : ℚ), 0 < c ∧ g ≠ 0 ∧
      (∀ j, (g j).natAbs ≤ n.factorial * W ^ n) ∧
      z = c • (fun j ↦ (g j : ℚ)) := by
  classical
  let Mq : Matrix (Fin q) (Fin (n + 1)) ℚ := fun i j ↦ (M i j : ℚ)
  obtain ⟨I, hIE, hIli, hIspan⟩ := exists_basis_indices_of_finrank_eq Mq E hE
  let R : Matrix (Fin n) (Fin (n + 1)) ℤ := fun k j ↦ M (I k) j
  let Rq : Matrix (Fin n) (Fin (n + 1)) ℚ := fun k j ↦ (R k j : ℚ)
  let g0 : Fin (n + 1) → ℤ := fun j ↦ (-1 : ℤ) ^ (j : ℕ) * (R.submatrix id j.succAbove).det
  let g0q : Fin (n + 1) → ℚ := fun j ↦ (g0 j : ℚ)
  have hRg0 : ∀ r : Fin n, R r ⬝ᵥ g0 = 0 := by
    intro r
    let A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ := Matrix.of (Fin.cons (R r) R)
    have hdet0 : A.det = 0 :=
      Matrix.det_zero_of_row_eq (i := 0) (j := r.succ) (Fin.succ_ne_zero r).symm
        (by ext j; rfl)
    have hexp : A.det = ∑ j : Fin (n + 1), (-1 : ℤ) ^ (j : ℕ) * R r j *
        (R.submatrix id j.succAbove).det := by
      rw [Matrix.det_succ_row_zero]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      have hsub : A.submatrix Fin.succ j.succAbove = R.submatrix id j.succAbove := by
        ext a b; rfl
      rw [hsub]; rfl
    have hdot : R r ⬝ᵥ g0 = ∑ j : Fin (n + 1), (-1 : ℤ) ^ (j : ℕ) * R r j *
        (R.submatrix id j.succAbove).det := by
      simp only [dotProduct, g0]
      refine Finset.sum_congr rfl fun j _ ↦ by ring
    rw [hdot, ← hexp, hdet0]
  have hRqg0 : ∀ r : Fin n, Rq r ⬝ᵥ g0q = 0 := fun r ↦ by
    have h1 := hRg0 r
    have hcast : Rq r ⬝ᵥ g0q = ((R r ⬝ᵥ g0 : ℤ) : ℚ) := by
      simp [dotProduct, Rq, g0q]
    rw [hcast, h1, Int.cast_zero]
  have hg0_bound : ∀ j : Fin (n + 1), (g0 j).natAbs ≤ n.factorial * W ^ n := by
    intro j
    have habs : |(g0 j)| ≤ (n.factorial * W ^ n : ℤ) := by
      dsimp only [g0]
      rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, Matrix.det_apply]
      calc |∑ σ : Equiv.Perm (Fin n),
              Equiv.Perm.sign σ • ∏ i : Fin n, R.submatrix id j.succAbove (σ i) i|
          ≤ ∑ σ : Equiv.Perm (Fin n),
              |Equiv.Perm.sign σ • ∏ i : Fin n, R.submatrix id j.succAbove (σ i) i| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _σ : Equiv.Perm (Fin n), (W : ℤ) ^ n := by
            refine Finset.sum_le_sum fun σ _ ↦ ?_
            have hsign : |Equiv.Perm.sign σ • ∏ i : Fin n, R (σ i) (j.succAbove i)| =
                ∏ i : Fin n, |R (σ i) (j.succAbove i)| := by
              rw [← Finset.abs_prod]
              rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;> simp [hs]
            have hprod : ∏ i : Fin n, |R (σ i) (j.succAbove i)| ≤ (W : ℤ) ^ n := by
              have hgen : ∀ s : Finset (Fin n),
                  ∏ i ∈ s, |R (σ i) (j.succAbove i)| ≤ ∏ _i ∈ s, (W : ℤ) := by
                intro s
                induction s using Finset.induction_on with
                | empty => simp
                | insert a s ha ih =>
                  rw [Finset.prod_insert ha, Finset.prod_insert ha]
                  have ha_le : |R (σ a) (j.succAbove a)| ≤ (W : ℤ) := by
                    rw [← Int.natCast_natAbs]; exact_mod_cast hW (I (σ a)) (j.succAbove a)
                  exact mul_le_mul ha_le ih (Finset.prod_nonneg fun _ _ ↦ abs_nonneg _)
                    (Nat.cast_nonneg _)
              simpa using hgen Finset.univ
            simpa only [Matrix.submatrix_apply, id, hsign] using hprod
        _ = (n.factorial * W ^ n : ℤ) := by
            simp [Finset.sum_const, Fintype.card_perm, Fintype.card_fin]
    rw [← Int.natCast_natAbs] at habs
    exact_mod_cast habs
  have hg0_ne : g0 ≠ 0 := by
    have hRq_rank : Rq.rank = n := by
      rw [← Matrix.rank_transpose, Matrix.rank, Matrix.range_mulVecLin]
      change Module.finrank ℚ (Submodule.span ℚ (Set.range fun k ↦ Rq k)) = n
      rw [hIspan, hE]
    have hcol_span' : Submodule.span ℚ (Set.range fun j : Fin (n + 1) ↦ fun k : Fin n ↦ Rq k j) =
      ⊤ := by
      have h1 : LinearMap.range Rq.mulVecLin = ⊤ := by
        apply Submodule.eq_top_of_finrank_eq
        rw [← Matrix.rank, hRq_rank, Module.finrank_fin_fun]
      rw [Matrix.range_mulVecLin] at h1
      exact h1
    obtain ⟨B, hB_sub, hB_span, hB_li⟩ :=
      exists_linearIndependent ℚ (Set.range fun j : Fin (n + 1) ↦ fun k : Fin n ↦ Rq k j)
    have hB_fin : B.Finite := (Set.finite_range _).subset hB_sub
    let _ : Fintype B := hB_fin.fintype
    have hB_card : Fintype.card B = n := by
      let b : Module.Basis B ℚ (Fin n → ℚ) :=
        Module.Basis.mk hB_li (le_of_eq (by
          rw [Subtype.range_coe_subtype, Set.ofPred_mem_eq, hB_span, hcol_span']))
      simpa [Module.finrank_fin_fun] using (Module.finrank_eq_card_basis b).symm
    let e : Fin n ≃ B := (Fintype.equivFinOfCardEq hB_card).symm
    have hJex : ∀ k : Fin n, ∃ j : Fin (n + 1), (fun r ↦ Rq r j) = (e k).1 := fun k ↦ hB_sub (e k).2
    choose J hJeq using hJex
    have hJli : LinearIndependent ℚ (fun k : Fin n ↦ fun r : Fin n ↦ Rq r (J k)) := by
      have hfeq : (fun k : Fin n ↦ fun r : Fin n ↦ Rq r (J k)) = (Subtype.val ∘ e) :=
        funext hJeq
      rw [hfeq]
      exact hB_li.comp e e.injective
    have hJinj : Function.Injective J := by
      intro k1 k2 hk
      exact hJli.injective (by simp [hk])
    have hcard_miss : (Finset.univ \ Finset.univ.image J).card = 1 := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),
        Finset.card_image_of_injective _ hJinj,
        Finset.card_univ, Finset.card_univ, Fintype.card_fin, Fintype.card_fin]
      omega
    obtain ⟨j₀, hj₀⟩ := Finset.card_eq_one.mp hcard_miss
    have hj₀_not : j₀ ∉ Finset.univ.image J := by
      have : j₀ ∈ Finset.univ \ Finset.univ.image J := by rw [hj₀]; simp
      exact (Finset.mem_sdiff.mp this).2
    have hrange_eq : Set.range J = Set.range j₀.succAbove := by
      ext j
      simp only [Set.mem_range]
      constructor
      · rintro ⟨k, rfl⟩
        have hne : J k ≠ j₀ := fun h ↦ hj₀_not (Finset.mem_image.mpr ⟨k, Finset.mem_univ _, h⟩)
        exact Fin.exists_succAbove_eq hne
      · rintro ⟨k, rfl⟩
        by_contra hnot
        have hmem : j₀.succAbove k ∈ Finset.univ \ Finset.univ.image J :=
          Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun h ↦ by
            obtain ⟨m, _, hm⟩ := Finset.mem_image.mp h
            exact hnot ⟨m, hm⟩⟩
        rw [hj₀, Finset.mem_singleton] at hmem
        exact Fin.succAbove_ne j₀ k hmem
    have hsub_det : (Rq.submatrix id j₀.succAbove).det ≠ 0 := by
      intro hdet
      have hdep := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
      obtain ⟨v, hv_ne, hv_eq⟩ := hdep
      -- Wait: `hJli` says columns `J` are linearly independent, and `j₀.succAbove` has the same
      -- set of columns, so `LinearIndependent ℚ (fun k ↦ fun r ↦ Rq r (j₀.succAbove k))`!
      have hperm_ex : ∀ k : Fin n, ∃ m : Fin n, J m = j₀.succAbove k := fun k ↦ by
        have : j₀.succAbove k ∈ Set.range J := by rw [hrange_eq]; exact ⟨k, rfl⟩
        exact this
      choose σ hσ using hperm_ex
      have hσ_inj : Function.Injective σ := fun a b hab ↦
        j₀.succAbove_right_injective (by rw [← hσ a, ← hσ b, hab])
      have hli' : LinearIndependent ℚ (fun k : Fin n ↦ fun r : Fin n ↦ Rq r (j₀.succAbove k)) := by
        have := hJli.comp σ hσ_inj
        simpa only [Function.comp_def, hσ] using this
      have hsum : ∑ k : Fin n, v k • (fun r : Fin n ↦ Rq r (j₀.succAbove k)) = 0 := by
        ext r
        have hr := congrFun hv_eq r
        simpa [Matrix.mulVec, dotProduct, mul_comm] using hr
      have hv0 := Fintype.linearIndependent_iff.mp hli' v hsum
      exact hv_ne (funext hv0)
    have hg0_j0 : g0 j₀ ≠ 0 := by
      intro h0
      have hq : (g0 j₀ : ℚ) = 0 := by exact_mod_cast h0
      dsimp only [g0] at hq
      push_cast at hq
      rw [show (R.submatrix id j₀.succAbove).map (fun x ↦ (x : ℚ)) =
          Rq.submatrix id j₀.succAbove from rfl] at hq
      have hsign : ((-1 : ℚ) ^ (j₀ : ℕ)) ≠ 0 := pow_ne_zero _ (by norm_num)
      exact hsub_det (mul_eq_zero.mp hq |>.resolve_left hsign)
    intro hzero
    exact hg0_j0 (congrFun hzero j₀)
  -- Both `z` and `g0q` lie in the 1-dimensional kernel of `ME_ℚ`:
  let ME : Matrix E (Fin (n + 1)) ℚ := Mq.submatrix Subtype.val id
  have hker_dim : Module.finrank ℚ (LinearMap.ker ME.mulVecLin) = 1 := by
    have hrank_eq : ME.rank = n := by
      rw [← Matrix.rank_transpose, Matrix.rank, range_transpose_mulVecLin_eq_span]; exact hE
    have hadd := LinearMap.finrank_range_add_finrank_ker ME.mulVecLin
    rw [Module.finrank_fin_fun ℚ] at hadd
    change ME.rank + Module.finrank ℚ (LinearMap.ker ME.mulVecLin) = n + 1 at hadd
    omega
  have hg0q_ker : g0q ∈ LinearMap.ker ME.mulVecLin := by
    rw [LinearMap.mem_ker]
    ext ⟨i, hi⟩
    have hmem : Mq i ∈ Submodule.span ℚ (Set.range fun k ↦ Rq k) := by
      rw [hIspan]; exact Submodule.subset_span ⟨i, hi, rfl⟩
    change Mq i ⬝ᵥ g0q = 0
    refine Submodule.span_induction ?_ (by simp) (fun x y _ _ hx hy ↦ by
      rw [add_dotProduct, hx, hy, add_zero]) (fun c x _ hx ↦ by
      rw [smul_dotProduct, hx, smul_zero]) hmem
    rintro _ ⟨r, rfl⟩
    exact hRqg0 r
  have hz_ker : z ∈ LinearMap.ker ME.mulVecLin := by
    rw [LinearMap.mem_ker]; ext ⟨i, hi⟩; exact hzE i hi
  have hg0q_ne : g0q ≠ 0 := by
    intro h0; exact hg0_ne (funext fun j ↦ Int.cast_eq_zero.mp (congrFun h0 j))
  have hspan_eq : Submodule.span ℚ ({(⟨g0q, hg0q_ker⟩ : LinearMap.ker ME.mulVecLin)} :
      Set (LinearMap.ker ME.mulVecLin)) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [hker_dim, finrank_span_singleton]
    intro h0; exact hg0q_ne (congrArg Subtype.val h0)
  have hz_mem : (⟨z, hz_ker⟩ : LinearMap.ker ME.mulVecLin) ∈
      Submodule.span ℚ ({(⟨g0q, hg0q_ker⟩ : LinearMap.ker ME.mulVecLin)} :
        Set (LinearMap.ker ME.mulVecLin)) := by
    rw [hspan_eq]; trivial
  rw [Submodule.mem_span_singleton] at hz_mem
  obtain ⟨c, hc⟩ := hz_mem
  have hzc : z = c • g0q := (congrArg Subtype.val hc).symm
  have hc_ne : c ≠ 0 := by
    intro h0; rw [h0, zero_smul] at hzc; exact hz hzc
  rcases lt_or_gt_of_ne hc_ne with hlt | hgt
  · refine ⟨-g0, -c, by linarith, by simpa using hg0_ne, fun j ↦ by
      simpa [Pi.neg_apply] using hg0_bound j, ?_⟩
    rw [hzc]; ext j; simp [g0q]
  · exact ⟨g0, c, hgt, hg0_ne, hg0_bound, hzc⟩

/-- Pointed cone decomposition into bounded integer rays of active rank `p - 1`. -/
private lemma cone_decomp_int_rays {q n : ℕ} (M : Matrix (Fin q) (Fin (n + 1)) ℤ) (W : ℕ)
    (hW : ∀ i j, (M i j).natAbs ≤ W)
    (hpointed : ∀ z : Fin (n + 1) → ℚ,
      (∀ i, 0 ≤ (fun j ↦ (M i j : ℚ)) ⬝ᵥ z) →
      (∀ i, 0 ≤ (fun j ↦ (M i j : ℚ)) ⬝ᵥ (-z)) → z = 0)
    (z : Fin (n + 1) → ℚ) (hz : ∀ i, 0 ≤ (fun j ↦ (M i j : ℚ)) ⬝ᵥ z) :
    ∃ (m : ℕ) (lam : Fin m → ℚ) (G : Fin m → Fin (n + 1) → ℤ),
      (∀ r, 0 < lam r) ∧ (∀ r, G r ≠ 0) ∧
      (∀ r i, 0 ≤ (fun j ↦ (M i j : ℚ)) ⬝ᵥ (fun j ↦ (G r j : ℚ))) ∧
      (∀ r j, (G r j).natAbs ≤ n.factorial * W ^ n) ∧
      z = ∑ r : Fin m, lam r • (fun j ↦ (G r j : ℚ)) := by
  classical
  let Mq : Matrix (Fin q) (Fin (n + 1)) ℚ := fun i j ↦ (M i j : ℚ)
  let Eof : (Fin (n + 1) → ℚ) → Finset (Fin q) := fun v ↦
    Finset.univ.filter fun i ↦ Mq i ⬝ᵥ v = 0
  let rOf : (Fin (n + 1) → ℚ) → ℕ := fun v ↦
    Module.finrank ℚ (Submodule.span ℚ ((fun i ↦ Mq i) '' (Eof v : Set (Fin q))))
  have hr_le : ∀ v, rOf v ≤ n + 1 := fun v ↦ by
    simpa [Module.finrank_fin_fun] using
      Submodule.finrank_le (Submodule.span ℚ ((fun i ↦ Mq i) '' (Eof v : Set (Fin q))))
  have hcombine : ∀ {v₁ v₂ : Fin (n + 1) → ℚ} {c₁ c₂ : ℚ}, 0 < c₁ → 0 < c₂ →
      (∃ (m₁ : ℕ) (lam₁ : Fin m₁ → ℚ) (G₁ : Fin m₁ → Fin (n + 1) → ℤ),
        (∀ r, 0 < lam₁ r) ∧ (∀ r, G₁ r ≠ 0) ∧
        (∀ r i, 0 ≤ Mq i ⬝ᵥ (fun j ↦ (G₁ r j : ℚ))) ∧
        (∀ r j, (G₁ r j).natAbs ≤ n.factorial * W ^ n) ∧
        v₁ = ∑ r, lam₁ r • (fun j ↦ (G₁ r j : ℚ))) →
      (∃ (m₂ : ℕ) (lam₂ : Fin m₂ → ℚ) (G₂ : Fin m₂ → Fin (n + 1) → ℤ),
        (∀ r, 0 < lam₂ r) ∧ (∀ r, G₂ r ≠ 0) ∧
        (∀ r i, 0 ≤ Mq i ⬝ᵥ (fun j ↦ (G₂ r j : ℚ))) ∧
        (∀ r j, (G₂ r j).natAbs ≤ n.factorial * W ^ n) ∧
        v₂ = ∑ r, lam₂ r • (fun j ↦ (G₂ r j : ℚ))) →
      ∃ (m : ℕ) (lam : Fin m → ℚ) (G : Fin m → Fin (n + 1) → ℤ),
        (∀ r, 0 < lam r) ∧ (∀ r, G r ≠ 0) ∧
        (∀ r i, 0 ≤ Mq i ⬝ᵥ (fun j ↦ (G r j : ℚ))) ∧
        (∀ r j, (G r j).natAbs ≤ n.factorial * W ^ n) ∧
        c₁ • v₁ + c₂ • v₂ = ∑ r, lam r • (fun j ↦ (G r j : ℚ)) := by
    intro v₁ v₂ c₁ c₂ hc₁ hc₂ ⟨m₁, lam₁, G₁, h1, h2, h3, h4, h5⟩
      ⟨m₂, lam₂, G₂, k1, k2, k3, k4, k5⟩
    refine ⟨m₁ + m₂, Fin.addCases (fun r ↦ c₁ * lam₁ r) (fun r ↦ c₂ * lam₂ r),
      Fin.addCases G₁ G₂, ?_, ?_, ?_, ?_, ?_⟩
    · intro r
      refine Fin.addCases
        (motive := fun r ↦ (0 : ℚ) <
          Fin.addCases (motive := fun _ ↦ ℚ) (fun r ↦ c₁ * lam₁ r) (fun r ↦ c₂ * lam₂ r) r)
        (fun r ↦ by rw [Fin.addCases_left]; exact mul_pos hc₁ (h1 r))
        (fun r ↦ by rw [Fin.addCases_right]; exact mul_pos hc₂ (k1 r)) r
    · intro r
      refine Fin.addCases (motive := fun r ↦ Fin.addCases (motive :=
        fun _ ↦ Fin (n + 1) → ℤ) G₁ G₂ r ≠ 0)
        (fun r ↦ by rw [Fin.addCases_left]; exact h2 r)
        (fun r ↦ by rw [Fin.addCases_right]; exact k2 r) r
    · intro r i
      refine Fin.addCases
        (motive := fun r ↦ 0 ≤ Mq i ⬝ᵥ (fun j ↦ (Fin.addCases (motive :=
          fun _ ↦ Fin (n + 1) → ℤ) G₁ G₂ r j : ℚ)))
        (fun r ↦ by rw [Fin.addCases_left]; exact h3 r i)
        (fun r ↦ by rw [Fin.addCases_right]; exact k3 r i) r
    · intro r j
      refine Fin.addCases
        (motive := fun r ↦ (Fin.addCases (motive :=
          fun _ ↦ Fin (n + 1) → ℤ) G₁ G₂ r j).natAbs ≤ n.factorial * W ^ n)
        (fun r ↦ by rw [Fin.addCases_left]; exact h4 r j)
        (fun r ↦ by rw [Fin.addCases_right]; exact k4 r j) r
    · rw [Fin.sum_univ_add, h5, k5, Finset.smul_sum, Finset.smul_sum]
      simp [Fin.addCases_left, Fin.addCases_right, smul_smul]
  have hmain : ∀ k : ℕ, ∀ v : Fin (n + 1) → ℚ,
      (∀ i, 0 ≤ Mq i ⬝ᵥ v) → n + 1 - rOf v ≤ k →
      ∃ (m : ℕ) (lam : Fin m → ℚ) (G : Fin m → Fin (n + 1) → ℤ),
        (∀ r, 0 < lam r) ∧ (∀ r, G r ≠ 0) ∧
        (∀ r i, 0 ≤ Mq i ⬝ᵥ (fun j ↦ (G r j : ℚ))) ∧
        (∀ r j, (G r j).natAbs ≤ n.factorial * W ^ n) ∧
        v = ∑ r, lam r • (fun j ↦ (G r j : ℚ)) := by
    intro k
    induction k with
    | zero =>
      intro v hv hrank
      have hr : Module.finrank ℚ (Submodule.span ℚ ((fun i ↦ Mq i) '' (Eof v : Set (Fin q)))) =
          n + 1 := by
        have := hr_le v; dsimp only [rOf] at this hrank ⊢; omega
      have hspan : Submodule.span ℚ ((fun i ↦ Mq i) '' (Eof v : Set (Fin q))) = ⊤ :=
        Submodule.eq_top_of_finrank_eq (by rw [hr, Module.finrank_fin_fun])
      have hv0 : v = 0 := by
        by_contra hne
        obtain ⟨j₀, hj₀⟩ : ∃ j, v j ≠ 0 := by
          by_contra hall; push Not at hall; exact hne (funext hall)
        have hmem : Pi.single j₀ (1 : ℚ) ∈
            Submodule.span ℚ ((fun i ↦ Mq i) '' (Eof v : Set (Fin q))) := by
          rw [hspan]; trivial
        have hdot0 : (Pi.single j₀ (1 : ℚ) : Fin (n + 1) → ℚ) ⬝ᵥ v = 0 := by
          refine Submodule.span_induction ?_ (by simp) (fun x y _ _ hx hy ↦ by
            rw [add_dotProduct, hx, hy, add_zero]) (fun c x _ hx ↦ by
            rw [smul_dotProduct, hx, smul_zero]) hmem
          rintro _ ⟨i, hi, rfl⟩
          exact (Finset.mem_filter.mp hi).2
        have hvj : v j₀ = 0 := by simpa [dotProduct, Pi.single_apply] using hdot0
        exact hj₀ hvj
      exact ⟨0, Fin.elim0, Fin.elim0, fun r ↦ r.elim0, fun r ↦ r.elim0,
        fun r ↦ r.elim0, fun r ↦ r.elim0, by simp [hv0]⟩
    | succ k ih =>
      intro v hv hrank
      by_cases hv0 : v = 0
      · exact ⟨0, Fin.elim0, Fin.elim0, fun r ↦ r.elim0, fun r ↦ r.elim0,
          fun r ↦ r.elim0, fun r ↦ r.elim0, by simp [hv0]⟩
      by_cases hlt : n + 1 - rOf v ≤ k
      · exact ih v hv hlt
      have hr_eq : n + 1 - rOf v = k + 1 := by omega
      by_cases hk0 : k = 0
      · have hr_n : rOf v = n := by omega
        obtain ⟨g, c, hc, hg_ne, hg_bd, hvg⟩ :=
          exists_int_ray_of_finrank_eq_pred M (Eof v) W hW hr_n v hv0
            (fun i hi ↦ (Finset.mem_filter.mp hi).2)
        have hg_cone : ∀ i, 0 ≤ Mq i ⬝ᵥ (fun j ↦ (g j : ℚ)) := fun i ↦ by
          have hvi := hv i
          rw [hvg, dotProduct_smul] at hvi
          exact nonneg_of_mul_nonneg_right hvi hc
        refine ⟨1, fun _ ↦ c, fun _ ↦ g, fun _ ↦ hc, fun _ ↦ hg_ne, fun _ ↦ hg_cone,
          fun _ ↦ hg_bd, ?_⟩
        simp [hvg]
      · have hr_le2 : rOf v + 2 ≤ n + 1 := by omega
        obtain ⟨u, huE, hu_not⟩ := exists_ker_not_mem_span_of_finrank_le Mq (Eof v) v hr_le2
        have hu_ne : u ≠ 0 := fun h0 ↦ hu_not (h0 ▸ Submodule.zero_mem _)
        by_cases hboth : (∃ i, 0 < Mq i ⬝ᵥ u) ∧ (∃ i, Mq i ⬝ᵥ u < 0)
        · -- Both positive and negative signs on `u`: split `v` along `±u`.
          let Ppos := Finset.univ.filter fun i : Fin q ↦ 0 < Mq i ⬝ᵥ u
          let Pneg := Finset.univ.filter fun i : Fin q ↦ Mq i ⬝ᵥ u < 0
          have hPpos : Ppos.Nonempty := by
            obtain ⟨i, hi⟩ := hboth.1; exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
          have hPneg : Pneg.Nonempty := by
            obtain ⟨i, hi⟩ := hboth.2; exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
          obtain ⟨i₁, hi₁_mem, hi₁_min⟩ :=
            Finset.exists_min_image Pneg (fun i ↦ (Mq i ⬝ᵥ v) / (-(Mq i ⬝ᵥ u))) hPneg
          obtain ⟨i₂, hi₂_mem, hi₂_min⟩ :=
            Finset.exists_min_image Ppos (fun i ↦ (Mq i ⬝ᵥ v) / (Mq i ⬝ᵥ u)) hPpos
          have hi₁_neg : Mq i₁ ⬝ᵥ u < 0 := (Finset.mem_filter.mp hi₁_mem).2
          have hi₂_pos : 0 < Mq i₂ ⬝ᵥ u := (Finset.mem_filter.mp hi₂_mem).2
          have hi₁_vpos : 0 < Mq i₁ ⬝ᵥ v :=
            lt_of_le_of_ne (hv i₁)
              (fun h0 ↦ absurd (huE i₁ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,
                h0.symm⟩)) hi₁_neg.ne)
          have hi₂_vpos : 0 < Mq i₂ ⬝ᵥ v :=
            lt_of_le_of_ne (hv i₂)
              (fun h0 ↦ absurd (huE i₂ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,
                h0.symm⟩)) hi₂_pos.ne')
          let α : ℚ := (Mq i₁ ⬝ᵥ v) / (-(Mq i₁ ⬝ᵥ u))
          let β : ℚ := (Mq i₂ ⬝ᵥ v) / (Mq i₂ ⬝ᵥ u)
          have hα : 0 < α := div_pos hi₁_vpos (by linarith)
          have hβ : 0 < β := div_pos hi₂_vpos hi₂_pos
          let v₁ : Fin (n + 1) → ℚ := v + α • u
          let v₂ : Fin (n + 1) → ℚ := v - β • u
          have hv₁ : ∀ i, 0 ≤ Mq i ⬝ᵥ v₁ := fun i ↦ by
            rw [show Mq i ⬝ᵥ v₁ = Mq i ⬝ᵥ v + α * (Mq i ⬝ᵥ u) by
              simp [v₁, dotProduct_add, dotProduct_smul]]
            by_cases hneg : Mq i ⬝ᵥ u < 0
            · have hle := hi₁_min i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hneg⟩)
              have h1 : α * (-(Mq i ⬝ᵥ u)) ≤ Mq i ⬝ᵥ v := (le_div_iff₀ (by linarith)).mp hle
              linarith
            · nlinarith [hv i, not_lt.mp hneg]
          have hv₂ : ∀ i, 0 ≤ Mq i ⬝ᵥ v₂ := fun i ↦ by
            rw [show Mq i ⬝ᵥ v₂ = Mq i ⬝ᵥ v - β * (Mq i ⬝ᵥ u) by
              simp [v₂, dotProduct_sub, dotProduct_smul]]
            by_cases hpos : 0 < Mq i ⬝ᵥ u
            · have hle := hi₂_min i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpos⟩)
              have h1 : β * (Mq i ⬝ᵥ u) ≤ Mq i ⬝ᵥ v := (le_div_iff₀ hpos).mp hle
              linarith
            · nlinarith [hv i, not_lt.mp hpos]
          have hsub₁ : Eof v ⊆ Eof v₁ := fun i hi ↦ by
            rw [Finset.mem_filter] at hi ⊢
            refine ⟨Finset.mem_univ _, ?_⟩
            simp [v₁, dotProduct_add, dotProduct_smul, hi.2, huE i (Finset.mem_filter.mpr hi)]
          have hsub₂ : Eof v ⊆ Eof v₂ := fun i hi ↦ by
            rw [Finset.mem_filter] at hi ⊢
            refine ⟨Finset.mem_univ _, ?_⟩
            simp [v₂, dotProduct_sub, dotProduct_smul, hi.2, huE i (Finset.mem_filter.mpr hi)]
          have hi₁_act : i₁ ∈ Eof v₁ := by
            rw [Finset.mem_filter]; refine ⟨Finset.mem_univ _, ?_⟩
            simp only [v₁, dotProduct_add, dotProduct_smul, smul_eq_mul, α]
            rw [div_eq_mul_inv, inv_neg, mul_neg, neg_mul, mul_assoc,
              inv_mul_cancel₀ hi₁_neg.ne, mul_one, add_neg_cancel]
          have hi₂_act : i₂ ∈ Eof v₂ := by
            rw [Finset.mem_filter]; refine ⟨Finset.mem_univ _, ?_⟩
            simp only [v₂, dotProduct_sub, dotProduct_smul, smul_eq_mul, β]
            rw [div_mul_cancel₀ _ hi₂_pos.ne']; ring
          have hr₁ : rOf v < rOf v₁ := finrank_span_lt_of_not_mem Mq hsub₁ hi₁_act huE hi₁_neg.ne
          have hr₂ : rOf v < rOf v₂ := finrank_span_lt_of_not_mem Mq hsub₂ hi₂_act huE hi₂_pos.ne'
          have hdec₁ := ih v₁ hv₁ (by omega)
          have hdec₂ := ih v₂ hv₂ (by omega)
          have hv_eq : v = (β / (α + β)) • v₁ + (α / (α + β)) • v₂ := by
            ext j; dsimp only [v₁, v₂]; simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
              smul_eq_mul]
            field_simp [(show α + β ≠ 0 by linarith)]; ring
          rw [hv_eq]
          exact hcombine (div_pos hβ (by linarith)) (div_pos hα (by linarith)) hdec₁ hdec₂
        · -- All `Mq i ⬝ᵥ u` have the same sign: choose `w = ±u ∈ K \ span{v}`!
          have hsign : (∀ i, 0 ≤ Mq i ⬝ᵥ u) ∨ (∀ i, Mq i ⬝ᵥ u ≤ 0) := by
            by_contra hnot
            push Not at hnot
            exact hboth ⟨hnot.2, hnot.1⟩
          let w : Fin (n + 1) → ℚ := if ∀ i, 0 ≤ Mq i ⬝ᵥ u then u else -u
          have hw_cone : ∀ i, 0 ≤ Mq i ⬝ᵥ w := fun i ↦ by
            dsimp only [w]; split_ifs with h1
            · exact h1 i
            · rw [dotProduct_neg]; linarith [(hsign.resolve_left h1) i]
          have hwE : ∀ i ∈ Eof v, Mq i ⬝ᵥ w = 0 := fun i hi ↦ by
            dsimp only [w]; split_ifs
            · exact huE i hi
            · rw [dotProduct_neg, huE i hi, neg_zero]
          have hw_not : w ∉ Submodule.span ℚ ({v} : Set (Fin (n + 1) → ℚ)) := by
            dsimp only [w]; split_ifs
            · exact hu_not
            · intro hmem; exact hu_not (by simpa using Submodule.neg_mem _ hmem)
          have hw_ne : w ≠ 0 := fun h0 ↦ hw_not (h0 ▸ Submodule.zero_mem _)
          have hex_wpos : ∃ i, 0 < Mq i ⬝ᵥ w := by
            by_contra hno; push Not at hno
            exact hw_ne (hpointed w hw_cone fun i ↦ by rw [dotProduct_neg]; linarith [hno i])
          have hex_vpos : ∃ i, 0 < Mq i ⬝ᵥ v := by
            by_contra hno; push Not at hno
            exact hv0 (hpointed v hv fun i ↦ by rw [dotProduct_neg]; linarith [hno i])
          let Pw := Finset.univ.filter fun i : Fin q ↦ 0 < Mq i ⬝ᵥ w
          let Pv := Finset.univ.filter fun i : Fin q ↦ 0 < Mq i ⬝ᵥ v
          have hPw : Pw.Nonempty := by
            obtain ⟨i, hi⟩ := hex_wpos; exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
          have hPv : Pv.Nonempty := by
            obtain ⟨i, hi⟩ := hex_vpos; exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
          obtain ⟨i₁, hi₁_mem, hi₁_min⟩ :=
            Finset.exists_min_image Pw (fun i ↦ (Mq i ⬝ᵥ v) / (Mq i ⬝ᵥ w)) hPw
          obtain ⟨i₂, hi₂_mem, hi₂_min⟩ :=
            Finset.exists_min_image Pv (fun i ↦ (Mq i ⬝ᵥ w) / (Mq i ⬝ᵥ v)) hPv
          have hi₁_wpos : 0 < Mq i₁ ⬝ᵥ w := (Finset.mem_filter.mp hi₁_mem).2
          have hi₂_vpos : 0 < Mq i₂ ⬝ᵥ v := (Finset.mem_filter.mp hi₂_mem).2
          have hi₁_vpos : 0 < Mq i₁ ⬝ᵥ v :=
            lt_of_le_of_ne (hv i₁)
              (fun h0 ↦ absurd (hwE i₁ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,
                h0.symm⟩)) hi₁_wpos.ne')
          let α₀ : ℚ := (Mq i₁ ⬝ᵥ v) / (Mq i₁ ⬝ᵥ w)
          let β₀ : ℚ := (Mq i₂ ⬝ᵥ w) / (Mq i₂ ⬝ᵥ v)
          have hα₀ : 0 < α₀ := div_pos hi₁_vpos hi₁_wpos
          have hβ₀ : 0 ≤ β₀ := div_nonneg (hw_cone i₂) hi₂_vpos.le
          let v₁ : Fin (n + 1) → ℚ := v - α₀ • w
          have hv₁ : ∀ i, 0 ≤ Mq i ⬝ᵥ v₁ := fun i ↦ by
            rw [show Mq i ⬝ᵥ v₁ = Mq i ⬝ᵥ v - α₀ * (Mq i ⬝ᵥ w) by
              simp [v₁, dotProduct_sub, dotProduct_smul]]
            by_cases hpos : 0 < Mq i ⬝ᵥ w
            · have hle := hi₁_min i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpos⟩)
              have h1 : α₀ * (Mq i ⬝ᵥ w) ≤ Mq i ⬝ᵥ v := (le_div_iff₀ hpos).mp hle
              linarith
            · have h0 : Mq i ⬝ᵥ w = 0 := le_antisymm (not_lt.mp hpos) (hw_cone i)
              rw [h0, mul_zero, sub_zero]; exact hv i
          have hsub₁ : Eof v ⊆ Eof v₁ := fun i hi ↦ by
            rw [Finset.mem_filter] at hi ⊢
            refine ⟨Finset.mem_univ _, ?_⟩
            simp [v₁, dotProduct_sub, dotProduct_smul, hi.2, hwE i (Finset.mem_filter.mpr hi)]
          have hi₁_act : i₁ ∈ Eof v₁ := by
            rw [Finset.mem_filter]; refine ⟨Finset.mem_univ _, ?_⟩
            simp only [v₁, dotProduct_sub, dotProduct_smul, smul_eq_mul, α₀]
            rw [div_mul_cancel₀ _ hi₁_wpos.ne']; ring
          have hr₁ : rOf v < rOf v₁ := finrank_span_lt_of_not_mem Mq hsub₁ hi₁_act hwE hi₁_wpos.ne'
          have hdec₁ := ih v₁ hv₁ (by omega)
          rcases eq_or_lt_of_le hβ₀ with hβ0_eq | hβ0_pos
          · -- `β₀ = 0` means `Mq i₂ ⬝ᵥ w = 0` while `Mq i₂ ⬝ᵥ v > 0`, so `w` has higher rank!
            have hi₂_w0 : Mq i₂ ⬝ᵥ w = 0 := by
              have h := hβ0_eq.symm
              dsimp only [β₀] at h
              exact (div_eq_zero_iff.mp h).resolve_right hi₂_vpos.ne'
            have hsub_w : Eof v ⊆ Eof w := fun i hi ↦
              Finset.mem_filter.mpr ⟨Finset.mem_univ _, hwE i hi⟩
            have hi₂_wact : i₂ ∈ Eof w := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi₂_w0⟩
            have hr_w : rOf v < rOf w := by
              -- `Mq i₂` is nonzero on `v`, so `Mq i₂ ∉ span(Eof v)`!
              set S := Submodule.span ℚ ((fun i ↦ Mq i) '' (Eof v : Set (Fin q)))
              set Sw := Submodule.span ℚ ((fun i ↦ Mq i) '' (Eof w : Set (Fin q)))
              have hle : S ≤ Sw :=
                Submodule.span_mono (Set.image_mono (Finset.coe_subset.mpr hsub_w))
              have hnot : Mq i₂ ∉ S := fun hmem ↦ by
                have h0 : Mq i₂ ⬝ᵥ v = 0 := by
                  refine Submodule.span_induction ?_ (by simp) (fun x y _ _ hx hy ↦ by
                    rw [add_dotProduct, hx, hy, add_zero]) (fun c x _ hx ↦ by
                    rw [smul_dotProduct, hx, smul_zero]) hmem
                  rintro _ ⟨i, hi, rfl⟩
                  exact (Finset.mem_filter.mp hi).2
                exact hi₂_vpos.ne' h0
              exact Submodule.finrank_lt_finrank_of_lt
                (lt_of_le_of_ne hle fun heq ↦ by
                  have hmem : Mq i₂ ∈ Sw := Submodule.subset_span ⟨i₂, hi₂_wact, rfl⟩
                  dsimp only [Sw] at hmem; rw [← heq] at hmem; exact hnot hmem)
            have hdec_w := ih w hw_cone (by omega)
            have hv_eq : v = (1 : ℚ) • v₁ + α₀ • w := by
              ext j; dsimp only [v₁]; simp
            rw [hv_eq]
            exact hcombine one_pos hα₀ hdec₁ hdec_w
          · -- `β₀ > 0`: then `α₀ * β₀ < 1`, and `v₂ = w - β₀ • v` also has higher rank!
            let v₂ : Fin (n + 1) → ℚ := w - β₀ • v
            have hv₂ : ∀ i, 0 ≤ Mq i ⬝ᵥ v₂ := fun i ↦ by
              rw [show Mq i ⬝ᵥ v₂ = Mq i ⬝ᵥ w - β₀ * (Mq i ⬝ᵥ v) by
                simp [v₂, dotProduct_sub, dotProduct_smul]]
              by_cases hpos : 0 < Mq i ⬝ᵥ v
              · have hle := hi₂_min i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpos⟩)
                have h1 : β₀ * (Mq i ⬝ᵥ v) ≤ Mq i ⬝ᵥ w := (le_div_iff₀ hpos).mp hle
                linarith
              · have h0 : Mq i ⬝ᵥ v = 0 := le_antisymm (not_lt.mp hpos) (hv i)
                rw [h0, mul_zero, sub_zero]; exact hw_cone i
            have hprod_lt : α₀ * β₀ < 1 := by
              by_contra hge1
              push Not at hge1
              have hv₁_neg : ∀ i, 0 ≤ Mq i ⬝ᵥ (-v₁) := fun i ↦ by
                rw [dotProduct_neg, show Mq i ⬝ᵥ v₁ = Mq i ⬝ᵥ v - α₀ * (Mq i ⬝ᵥ w) by
                  simp [v₁, dotProduct_sub, dotProduct_smul]]
                have h1 := hv₂ i
                rw [show Mq i ⬝ᵥ v₂ = Mq i ⬝ᵥ w - β₀ * (Mq i ⬝ᵥ v) by
                  simp [v₂, dotProduct_sub, dotProduct_smul]] at h1
                have h2 : α₀ * (Mq i ⬝ᵥ w) ≥ α₀ * (β₀ * (Mq i ⬝ᵥ v)) :=
                  mul_le_mul_of_nonneg_left (by linarith) hα₀.le
                have h3 : (α₀ * β₀) * (Mq i ⬝ᵥ v) ≥ 1 * (Mq i ⬝ᵥ v) :=
                  mul_le_mul_of_nonneg_right hge1 (hv i)
                linarith
              have hv₁0 : v₁ = 0 := hpointed v₁ hv₁ hv₁_neg
              have hw_mem : w ∈ Submodule.span ℚ ({v} : Set (Fin (n + 1) → ℚ)) := by
                rw [Submodule.mem_span_singleton]
                refine ⟨α₀⁻¹, ?_⟩
                have hveq : v = α₀ • w := sub_eq_zero.mp hv₁0
                rw [hveq, smul_smul, inv_mul_cancel₀ hα₀.ne', one_smul]
              exact hw_not hw_mem
            have hsub₂ : Eof v ⊆ Eof v₂ := fun i hi ↦ by
              rw [Finset.mem_filter] at hi ⊢
              refine ⟨Finset.mem_univ _, ?_⟩
              simp [v₂, dotProduct_sub, dotProduct_smul, hi.2, hwE i (Finset.mem_filter.mpr hi)]
            have hi₂_act : i₂ ∈ Eof v₂ := by
              rw [Finset.mem_filter]; refine ⟨Finset.mem_univ _, ?_⟩
              simp only [v₂, dotProduct_sub, dotProduct_smul, smul_eq_mul, β₀]
              rw [div_mul_cancel₀ _ hi₂_vpos.ne']; ring
            have hr₂ : rOf v < rOf v₂ := by
              set S := Submodule.span ℚ ((fun i ↦ Mq i) '' (Eof v : Set (Fin q)))
              set S₂ := Submodule.span ℚ ((fun i ↦ Mq i) '' (Eof v₂ : Set (Fin q)))
              have hle : S ≤ S₂ :=
                Submodule.span_mono (Set.image_mono (Finset.coe_subset.mpr hsub₂))
              have hnot : Mq i₂ ∉ S := fun hmem ↦ by
                have h0 : Mq i₂ ⬝ᵥ v = 0 := by
                  refine Submodule.span_induction ?_ (by simp) (fun x y _ _ hx hy ↦ by
                    rw [add_dotProduct, hx, hy, add_zero]) (fun c x _ hx ↦ by
                    rw [smul_dotProduct, hx, smul_zero]) hmem
                  rintro _ ⟨i, hi, rfl⟩
                  exact (Finset.mem_filter.mp hi).2
                exact hi₂_vpos.ne' h0
              exact Submodule.finrank_lt_finrank_of_lt
                (lt_of_le_of_ne hle fun heq ↦ by
                  have hmem : Mq i₂ ∈ S₂ := Submodule.subset_span ⟨i₂, hi₂_act, rfl⟩
                  dsimp only [S₂] at hmem; rw [← heq] at hmem; exact hnot hmem)
            have hdec₂ := ih v₂ hv₂ (by omega)
            have hden_pos : 0 < 1 - α₀ * β₀ := by linarith
            have hv_eq : v = (1 / (1 - α₀ * β₀)) • v₁ + (α₀ / (1 - α₀ * β₀)) • v₂ := by
              ext j; dsimp only [v₁, v₂]; simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
                smul_eq_mul]
              field_simp [hden_pos.ne']; ring
            rw [hv_eq]
            exact hcombine (div_pos one_pos hden_pos) (div_pos hα₀ hden_pos) hdec₁ hdec₂
  exact hmain (n + 1) z hz (Nat.sub_le _ _)

/-- Carathéodory reduction: any positive combination in `ℚ^p` reduces to at most `p` terms. -/
private lemma caratheodory_pos {p m : ℕ} {z : Fin p → ℚ} {lam : Fin m → ℚ}
    {V : Fin m → Fin p → ℚ} (hlam : ∀ r, 0 < lam r) (hz : z = ∑ r, lam r • V r) :
    ∃ (k : ℕ) (mu : Fin k → ℚ) (U : Fin k → Fin p → ℚ),
      k ≤ p ∧ (∀ r, 0 < mu r) ∧ (∀ r, ∃ s, U r = V s) ∧ z = ∑ r, mu r • U r := by
  classical
  have hstrong : ∀ m : ℕ, ∀ (lam : Fin m → ℚ) (V : Fin m → Fin p → ℚ),
      (∀ r, 0 < lam r) → z = ∑ r, lam r • V r →
      ∃ (k : ℕ) (mu : Fin k → ℚ) (U : Fin k → Fin p → ℚ),
        k ≤ p ∧ (∀ r, 0 < mu r) ∧ (∀ r, ∃ s, U r = V s) ∧ z = ∑ r, mu r • U r := by
    intro m
    induction m using Nat.strong_induction_on with
    | ind m ih =>
      intro lam V hlam hz
      by_cases hle : m ≤ p
      · exact ⟨m, lam, V, hle, hlam, fun r ↦ ⟨r, rfl⟩, hz⟩
      have hgt : p < m := by omega
      have hdep : ¬ LinearIndependent ℚ V := fun hli ↦ by
        have := hli.fintype_card_le_finrank
        rw [Fintype.card_fin, Module.finrank_fin_fun] at this
        omega
      rw [Fintype.not_linearIndependent_iff] at hdep
      obtain ⟨c, hc_sum, r₀, hr₀⟩ := hdep
      let c' : Fin m → ℚ := if 0 < c r₀ then c else -c
      have hc'_pos_ex : ∃ r, 0 < c' r := by
        refine ⟨r₀, ?_⟩
        dsimp only [c']; split_ifs with h
        · exact h
        · have : c r₀ < 0 := lt_of_le_of_ne (not_lt.mp h) hr₀
          simp only [Pi.neg_apply]; linarith
      have hc'_sum : ∑ r, c' r • V r = 0 := by
        dsimp only [c']; split_ifs
        · exact hc_sum
        · simp [neg_smul, Finset.sum_neg_distrib, hc_sum]
      let Ppos := Finset.univ.filter fun r : Fin m ↦ 0 < c' r
      have hPne : Ppos.Nonempty := by
        obtain ⟨r, hr⟩ := hc'_pos_ex; exact ⟨r, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr⟩⟩
      obtain ⟨r₁, hr₁_mem, hr₁_min⟩ := Finset.exists_min_image Ppos (fun r ↦ lam r / c' r) hPne
      have hr₁_cpos : 0 < c' r₁ := (Finset.mem_filter.mp hr₁_mem).2
      let t : ℚ := lam r₁ / c' r₁
      let lam' : Fin m → ℚ := fun r ↦ lam r - t * c' r
      have hlam'_r1 : lam' r₁ = 0 := by
        dsimp only [lam', t]; rw [div_mul_cancel₀ _ hr₁_cpos.ne']; ring
      have hlam'_nonneg : ∀ r, 0 ≤ lam' r := fun r ↦ by
        dsimp only [lam']
        by_cases hpos : 0 < c' r
        · have hle := hr₁_min r (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpos⟩)
          have h1 : t * c' r ≤ lam r := (le_div_iff₀ hpos).mp hle
          linarith
        · have ht_pos : 0 < t := div_pos (hlam r₁) hr₁_cpos
          nlinarith [hlam r, not_lt.mp hpos]
      have hz' : z = ∑ r : Fin m, lam' r • V r := by
        rw [hz]
        have hsub : ∑ r, lam' r • V r = (∑ r, lam r • V r) - t • (∑ r, c' r • V r) := by
          simp only [lam', sub_smul, Finset.sum_sub_distrib, Finset.smul_sum, smul_smul]
        rw [hsub, hc'_sum, smul_zero, sub_zero]
      let Spos : Finset (Fin m) := Finset.univ.filter fun r ↦ 0 < lam' r
      have hr₁_not : r₁ ∉ Spos := by simp [Spos, hlam'_r1]
      have hSsub : Spos ⊆ Finset.univ.erase r₁ :=
        fun r hr ↦ Finset.mem_erase.mpr ⟨fun h ↦ hr₁_not (h ▸ hr), Finset.mem_univ _⟩
      have hScard : Spos.card < m := by
        have h1 := Finset.card_le_card hSsub
        rw [Finset.card_erase_of_mem (Finset.mem_univ r₁), Finset.card_univ, Fintype.card_fin] at h1
        have hm_pos : 0 < m := by omega
        omega
      have hz_S : z = ∑ r ∈ Spos, lam' r • V r := by
        rw [hz', ← Finset.sum_subset (Finset.subset_univ Spos)]
        intro r _ hrnot
        have h0 : lam' r = 0 :=
          le_antisymm (not_lt.mp (by simpa [Spos] using hrnot)) (hlam'_nonneg r)
        simp [h0]
      let eS : Fin Spos.card ≃ Spos := (Fintype.equivFinOfCardEq (Fintype.card_coe Spos)).symm
      have hsum_eq : z = ∑ i : Fin Spos.card, lam' (eS i).1 • V (eS i).1 := by
        rw [hz_S, ← Finset.sum_coe_sort Spos]
        exact (Equiv.sum_comp eS (fun x : Spos ↦ lam' x.1 • V x.1)).symm
      obtain ⟨k, mu, U, hk, hmu, hU, hzk⟩ := ih Spos.card hScard
        (fun i ↦ lam' (eS i).1) (fun i ↦ V (eS i).1)
        (fun i ↦ (Finset.mem_filter.mp (eS i).2).2) hsum_eq
      exact ⟨k, mu, U, hk, hmu, fun r ↦ let ⟨i, hi⟩ := hU r; ⟨(eS i).1, hi⟩, hzk⟩
  exact hstrong m lam V hlam hz

/-- **Cook–Gerards–Schrijver–Tardos Proximity Theorem** for any feasible rational point `y*` of a
bounded-coefficient ILP instance: if an integer solution exists, there is one within `L^∞` distance
`p! * (max 1 W) ^ p` of `y*`. -/
theorem boundedCoeffILP_proximity (inst : BoundedCoeffILPInstance) (hp : 1 ≤ inst.numVars)
    (y : Fin inst.numVars → ℚ) (hy : inst.IsFeasibleRat y)
    (hx_ex : ∃ x : Fin inst.numVars → ℤ, inst.IsFeasibleInt x) :
    ∃ x : Fin inst.numVars → ℤ, inst.IsFeasibleInt x ∧
      ∀ j : Fin inst.numVars,
        |(x j : ℚ) - y j| ≤
          ((inst.numVars.factorial * (max 1 (maxAbsCoeff inst)) ^ inst.numVars : ℕ) : ℚ) := by
  classical
  obtain ⟨n, hnv⟩ : ∃ n, inst.numVars = n + 1 := ⟨inst.numVars - 1, by omega⟩
  -- Build finite set of integer-feasible points inside the box `∏ j, [L j, U j]`:
  let box : Finset (Fin inst.numVars → ℤ) :=
    Fintype.piFinset fun j : Fin inst.numVars ↦
      Finset.Icc (inst.lower.getD j.1 0) (inst.upper.getD j.1 0)
  let feasSet : Finset (Fin inst.numVars → ℤ) := box.filter fun x ↦ inst.IsFeasibleInt x
  have hfeas_ne : feasSet.Nonempty := by
    obtain ⟨x₀, hx₀⟩ := hx_ex
    refine ⟨x₀, Finset.mem_filter.mpr ⟨?_, hx₀⟩⟩
    exact Fintype.mem_piFinset.mpr fun j ↦ Finset.mem_Icc.mpr (hx₀.1 j)
  let dist1 : (Fin inst.numVars → ℤ) → ℚ := fun x ↦ ∑ j : Fin inst.numVars, |(x j : ℚ) - y j|
  obtain ⟨xstar, hxstar_mem, hxstar_min⟩ := Finset.exists_min_image feasSet dist1 hfeas_ne
  have hxstar : inst.IsFeasibleInt xstar := (Finset.mem_filter.mp hxstar_mem).2
  let d : Fin inst.numVars → ℚ := fun j ↦ (xstar j : ℚ) - y j
  let p := inst.numVars
  let m := inst.rows.length
  let W1 := max 1 (maxAbsCoeff inst)
  -- Sign-consistent matrix `M : Matrix (Fin (p + m)) (Fin p) ℤ`
  let M : Matrix (Fin (p + m)) (Fin p) ℤ := fun i j ↦
    if hlt : i.1 < p then
      let j0 : Fin p := ⟨i.1, hlt⟩
      if j = j0 then (if 0 ≤ d j0 then 1 else -1) else 0
    else
      let i0 : Fin m := ⟨i.1 - p, by omega⟩
      let rowSum : ℚ := ∑ k : Fin p, ((inst.rows.getD i0.1 []).getD k.1 0 : ℚ) * d k
      let s : ℤ := if 0 ≤ rowSum then 1 else -1
      s * (inst.rows.getD i0.1 []).getD j.1 0
  have hM_bound : ∀ i j, (M i j).natAbs ≤ W1 := by
    intro i j
    dsimp only [M]
    split_ifs with h1 h2 h3
    · simp [W1]
    · simp [W1]
    · simp
    · have hle := le_maxAbsCoeff inst ⟨i.1 - p, by omega⟩ j
      have hW1 : maxAbsCoeff inst ≤ W1 := le_max_right 1 _
      calc (1 * (inst.rows.getD (i.1 - p) []).getD j.1 0).natAbs
          = ((inst.rows.getD (i.1 - p) []).getD j.1 0).natAbs := by simp
        _ ≤ W1 := hle.trans hW1
    · have hle := le_maxAbsCoeff inst ⟨i.1 - p, by omega⟩ j
      have hW1 : maxAbsCoeff inst ≤ W1 := le_max_right 1 _
      calc (-1 * (inst.rows.getD (i.1 - p) []).getD j.1 0).natAbs
          = ((inst.rows.getD (i.1 - p) []).getD j.1 0).natAbs := by simp
        _ ≤ W1 := hle.trans hW1
  have hM_coord : ∀ j0 : Fin p,
      (fun j ↦ (M ⟨j0.1, by omega⟩ j : ℚ)) ⬝ᵥ (fun j ↦ d j) = |d j0| := by
    intro j0
    simp only [dotProduct, M, j0.isLt, ↓reduceDIte]
    rw [Finset.sum_eq_single j0]
    · simp only [↓reduceIte]
      split_ifs with h0
      · simp [abs_of_nonneg h0]
      · simp [abs_of_neg (lt_of_not_ge h0)]
    · intro j _ hj; simp [hj]
    · intro h; exact absurd (Finset.mem_univ j0) h
  have hM_coord_vec : ∀ (j0 : Fin p) (v : Fin p → ℚ),
      (fun j ↦ (M ⟨j0.1, by omega⟩ j : ℚ)) ⬝ᵥ v =
        (if 0 ≤ d j0 then 1 else -1) * v j0 := by
    intro j0 v
    simp only [dotProduct, M, j0.isLt, ↓reduceDIte]
    rw [Finset.sum_eq_single j0]
    · simp only [↓reduceIte]; split_ifs <;> simp
    · intro j _ hj; simp [hj]
    · intro h; exact absurd (Finset.mem_univ j0) h
  have hM_row_vec : ∀ (i0 : Fin m) (v : Fin p → ℚ),
      (fun j ↦ (M ⟨p + i0.1, by omega⟩ j : ℚ)) ⬝ᵥ v =
        (if 0 ≤ ∑ k : Fin p, ((inst.rows.getD i0.1 []).getD k.1 0 : ℚ) * d k then 1 else -1) *
          ∑ k : Fin p, ((inst.rows.getD i0.1 []).getD k.1 0 : ℚ) * v k := by
    intro i0 v
    simp only [dotProduct, M, show ¬ (p + i0.1 < p) by omega, ↓reduceDIte,
      show p + i0.1 - p = i0.1 by omega, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    split_ifs <;> simp
  have hd_cone : ∀ i : Fin (p + m), 0 ≤ (fun j ↦ (M i j : ℚ)) ⬝ᵥ d := by
    intro i
    by_cases hlt : i.1 < p
    · have heq : i = ⟨(⟨i.1, hlt⟩ : Fin p).1, by omega⟩ := rfl
      rw [heq, hM_coord]; exact abs_nonneg _
    · have heq : i = ⟨p + (⟨i.1 - p, by omega⟩ : Fin m).1, by omega⟩ := by
        ext; dsimp only; omega
      rw [heq, hM_row_vec]
      split_ifs with h0
      · simpa using h0
      · linarith [not_le.mp h0]
  have hM_pointed : ∀ z : Fin p → ℚ,
      (∀ i, 0 ≤ (fun j ↦ (M i j : ℚ)) ⬝ᵥ z) →
      (∀ i, 0 ≤ (fun j ↦ (M i j : ℚ)) ⬝ᵥ (-z)) → z = 0 := by
    intro z hz1 hz2
    ext j0
    have h1 := hz1 ⟨j0.1, by omega⟩
    have h2 := hz2 ⟨j0.1, by omega⟩
    rw [hM_coord_vec] at h1
    rw [dotProduct_neg, hM_coord_vec] at h2
    simp only [Pi.zero_apply]
    split_ifs at h1 h2 <;> linarith
  -- Cast `M` to `Fin (n + 1)` using `hnv` and apply `cone_decomp_int_rays` + `caratheodory_pos`:
  let M' : Matrix (Fin (p + m)) (Fin (n + 1)) ℤ := M.submatrix id (finCongr hnv.symm)
  let d' : Fin (n + 1) → ℚ := d ∘ finCongr hnv.symm
  have hM'_bound : ∀ i j, (M' i j).natAbs ≤ W1 := fun i j ↦ hM_bound i _
  have hM'_pointed : ∀ z : Fin (n + 1) → ℚ,
      (∀ i, 0 ≤ (fun j ↦ (M' i j : ℚ)) ⬝ᵥ z) →
      (∀ i, 0 ≤ (fun j ↦ (M' i j : ℚ)) ⬝ᵥ (-z)) → z = 0 := by
    intro z hz1 hz2
    have hdot : ∀ (i : Fin (p + m)) (v : Fin (n + 1) → ℚ),
        (fun j ↦ (M' i j : ℚ)) ⬝ᵥ v = (fun j ↦ (M i j : ℚ)) ⬝ᵥ (v ∘ finCongr hnv) := by
      intro i v
      simp only [dotProduct, M', Matrix.submatrix_apply, id, Function.comp_apply]
      rw [← Equiv.sum_comp (finCongr hnv.symm)]
      refine Finset.sum_congr rfl fun k _ ↦ by simp
    have hz0 : z ∘ finCongr hnv = 0 :=
      hM_pointed _ (fun i ↦ by rw [← hdot]; exact hz1 i) (fun i ↦ by
        have := hz2 i; rw [dotProduct_neg] at this ⊢; rw [← hdot]; exact this)
    ext j; have := congrFun hz0 (finCongr hnv.symm j); simpa using this
  have hd'_cone : ∀ i, 0 ≤ (fun j ↦ (M' i j : ℚ)) ⬝ᵥ d' := fun i ↦ by
    have hdot : (fun j ↦ (M' i j : ℚ)) ⬝ᵥ d' = (fun j ↦ (M i j : ℚ)) ⬝ᵥ d := by
      simp only [dotProduct, M', d', Matrix.submatrix_apply, id, Function.comp_apply]
      rw [← Equiv.sum_comp (finCongr hnv.symm)]
    rw [hdot]; exact hd_cone i
  obtain ⟨k0, lam0, G0, hlam0, hG0_ne, hG0_cone, hG0_bd, hd'_eq⟩ :=
    cone_decomp_int_rays M' W1 hM'_bound hM'_pointed d' hd'_cone
  obtain ⟨k, lam, U, hk_le, hlam, hU_mem, hd'_cara⟩ :=
    caratheodory_pos hlam0 hd'_eq
  -- Every `lam r < 1`, otherwise `xstar - g` contradicts minimality of `xstar`!
  have hlam_lt_one : ∀ r : Fin k, lam r < 1 := by
    intro r₀
    by_contra hge1; push Not at hge1
    obtain ⟨s₀, hs₀⟩ := hU_mem r₀
    let g' : Fin (n + 1) → ℤ := G0 s₀
    let g : Fin p → ℤ := g' ∘ finCongr hnv
    have hg_cone : ∀ i, 0 ≤ (fun j ↦ (M i j : ℚ)) ⬝ᵥ (fun j ↦ (g j : ℚ)) := fun i ↦ by
      have hdot : (fun j ↦ (M' i j : ℚ)) ⬝ᵥ (fun j ↦ (g' j : ℚ)) =
          (fun j ↦ (M i j : ℚ)) ⬝ᵥ (fun j ↦ (g j : ℚ)) := by
        simp only [dotProduct, M', g, Matrix.submatrix_apply, id, Function.comp_apply]
        rw [← Equiv.sum_comp (finCongr hnv.symm)]
        refine Finset.sum_congr rfl fun k _ ↦ by simp
      rw [← hdot]; exact hG0_cone s₀ i
    have hdg_cone : ∀ i, 0 ≤ (fun j ↦ (M i j : ℚ)) ⬝ᵥ (d - fun j ↦ (g j : ℚ)) := fun i ↦ by
      have hrem : d' - (fun j ↦ (g' j : ℚ)) =
          (lam r₀ - 1) • (fun j ↦ (g' j : ℚ)) +
            ∑ r ∈ Finset.univ.erase r₀, lam r • U r := by
        rw [hd'_cara, ← Finset.add_sum_erase _ _ (Finset.mem_univ r₀), hs₀]
        ext j; simp [sub_smul]; ring
      have hdot_eq : (fun j ↦ (M i j : ℚ)) ⬝ᵥ (d - fun j ↦ (g j : ℚ)) =
          (fun j ↦ (M' i j : ℚ)) ⬝ᵥ (d' - (fun j ↦ (g' j : ℚ))) := by
        simp only [dotProduct, M', d', g, Pi.sub_apply, Matrix.submatrix_apply, id,
          Function.comp_apply]
        rw [← Equiv.sum_comp (finCongr hnv.symm)]
        refine Finset.sum_congr rfl fun k _ ↦ by simp
      rw [hdot_eq, hrem, dotProduct_add, dotProduct_smul, dotProduct_sum]
      refine add_nonneg (mul_nonneg (by linarith) (hG0_cone s₀ i)) (Finset.sum_nonneg fun r _ ↦ ?_)
      obtain ⟨s, hs⟩ := hU_mem r
      rw [hs, dotProduct_smul]
      exact mul_nonneg (hlam r).le (hG0_cone s i)
    -- Check `x' := xstar - g` is integer-feasible and has strictly smaller `dist1`:
    let x' : Fin p → ℤ := fun j ↦ xstar j - g j
    have hx'_feas : inst.IsFeasibleInt x' := by
      refine ⟨fun j ↦ ?_, fun i ↦ ?_⟩
      · have hc1 := hg_cone ⟨j.1, by omega⟩
        have hc2 := hdg_cone ⟨j.1, by omega⟩
        rw [hM_coord_vec] at hc1 hc2
        have hL : (inst.lower.getD j.1 0 : ℚ) ≤ y j := (hy.1 j).1
        have hU : y j ≤ (inst.upper.getD j.1 0 : ℚ) := (hy.1 j).2
        have hLx : (inst.lower.getD j.1 0 : ℚ) ≤ (xstar j : ℚ) := by
          exact_mod_cast (hxstar.1 j).1
        have hUx : (xstar j : ℚ) ≤ (inst.upper.getD j.1 0 : ℚ) := by
          exact_mod_cast (hxstar.1 j).2
        split_ifs at hc1 hc2 with hd0
        · simp only [one_mul, Pi.sub_apply, d] at hc1 hc2
          have h1 : (inst.lower.getD j.1 0 : ℚ) ≤ (x' j : ℚ) := by
            dsimp only [x']; push_cast; linarith
          have h2 : (x' j : ℚ) ≤ (inst.upper.getD j.1 0 : ℚ) := by
            dsimp only [x']; push_cast; linarith
          exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
        · simp only [neg_one_mul, Pi.sub_apply, d] at hc1 hc2
          have h1 : (inst.lower.getD j.1 0 : ℚ) ≤ (x' j : ℚ) := by
            dsimp only [x']; push_cast; linarith
          have h2 : (x' j : ℚ) ≤ (inst.upper.getD j.1 0 : ℚ) := by
            dsimp only [x']; push_cast; linarith
          exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
      · have hc1 := hg_cone ⟨p + i.1, by omega⟩
        have hc2 := hdg_cone ⟨p + i.1, by omega⟩
        rw [hM_row_vec] at hc1 hc2
        have hsum_eq : ∑ j : Fin p, ((inst.rows.getD i.1 []).getD j.1 0 : ℚ) * (x' j : ℚ) =
            (∑ j : Fin p, ((inst.rows.getD i.1 []).getD j.1 0 : ℚ) * (xstar j : ℚ)) -
            (∑ j : Fin p, ((inst.rows.getD i.1 []).getD j.1 0 : ℚ) * (g j : ℚ)) := by
          simp only [x', Int.cast_sub, mul_sub, Finset.sum_sub_distrib]
        have hsum_eq2 : ∑ j : Fin p, ((inst.rows.getD i.1 []).getD j.1 0 : ℚ) * (x' j : ℚ) =
            (∑ j : Fin p, ((inst.rows.getD i.1 []).getD j.1 0 : ℚ) * y j) +
            (∑ j : Fin p, ((inst.rows.getD i.1 []).getD j.1 0 : ℚ) * (d j - (g j : ℚ))) := by
          simp only [x', d, Int.cast_sub, mul_sub, Finset.sum_sub_distrib]; ring
        have hxstar_i : ∑ j : Fin p, ((inst.rows.getD i.1 []).getD j.1 0 : ℚ) * (xstar j : ℚ) ≤
            (inst.rhs.getD i.1 0 : ℚ) := by
          have := hxstar.isFeasibleRat.2 i; exact this
        have hy_i := hy.2 i
        have hq : ∑ j : Fin p, ((inst.rows.getD i.1 []).getD j.1 0 : ℚ) * (x' j : ℚ) ≤
            (inst.rhs.getD i.1 0 : ℚ) := by
          split_ifs at hc1 hc2 with h0
          · rw [hsum_eq]; linarith
          · rw [hsum_eq2]; simp only [Pi.sub_apply] at hc2; linarith
        have hcast : (∑ j : Fin p, ((inst.rows.getD i.1 []).getD j.1 0 : ℚ) * (x' j : ℚ)) =
            ((∑ j : Fin p, (inst.rows.getD i.1 []).getD j.1 0 * x' j : ℤ) : ℚ) := by
          push_cast; rfl
        rw [hcast] at hq
        exact_mod_cast hq
    have hx'_mem : x' ∈ feasSet := Finset.mem_filter.mpr
      ⟨Fintype.mem_piFinset.mpr fun j ↦ Finset.mem_Icc.mpr (hx'_feas.1 j), hx'_feas⟩
    have hmin := hxstar_min x' hx'_mem
    have hlt_dist : dist1 x' < dist1 xstar := by
      have hterm_le : ∀ j : Fin p, |(x' j : ℚ) - y j| = |d j| - |(g j : ℚ)| := fun j ↦ by
        have hc1 := hg_cone ⟨j.1, by omega⟩
        have hc2 := hdg_cone ⟨j.1, by omega⟩
        rw [hM_coord_vec] at hc1 hc2
        have hxeq : (x' j : ℚ) - y j = d j - (g j : ℚ) := by simp [x', d]; ring
        rw [hxeq]
        split_ifs at hc1 hc2 with hd0
        · simp only [one_mul, Pi.sub_apply] at hc1 hc2
          rw [abs_of_nonneg hc2, abs_of_nonneg hd0, abs_of_nonneg hc1]
        · simp only [neg_one_mul, Pi.sub_apply] at hc1 hc2
          rw [abs_of_nonpos (by linarith), abs_of_neg (lt_of_not_ge hd0),
            abs_of_nonpos (by linarith)]; ring
      have hg_pos : 0 < ∑ j : Fin p, |(g j : ℚ)| := by
        have hj_ne : ∃ j : Fin p, g j ≠ 0 := by
          by_contra hall; push Not at hall
          exact hG0_ne s₀ (funext fun j ↦ by
            have := hall (finCongr hnv.symm j); simpa [g, g'] using this)
        obtain ⟨j₀, hj₀⟩ := hj_ne
        refine Finset.sum_pos' (fun j _ ↦ abs_nonneg _) ⟨j₀, Finset.mem_univ _, ?_⟩
        exact abs_pos.mpr (by exact_mod_cast hj₀)
      dsimp only [dist1]
      simp_rw [hterm_le, Finset.sum_sub_distrib]
      linarith
    linarith
  -- Now bound `|d j| ≤ (n + 1) * n! * W1 ^ n = (n + 1)! * W1 ^ n ≤ (n + 1)! * W1 ^ (n + 1)`:
  refine ⟨xstar, hxstar, fun j ↦ ?_⟩
  let j' : Fin (n + 1) := finCongr hnv j
  have hd_j : d j = d' j' := by simp [d', j']
  rw [show (xstar j : ℚ) - y j = d j from rfl, hd_j, hd'_cara, Finset.sum_apply]
  calc |∑ r : Fin k, (lam r • U r) j'|
      ≤ ∑ r : Fin k, |(lam r • U r) j'| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _r : Fin k, ((n.factorial * W1 ^ n : ℕ) : ℚ) := by
        refine Finset.sum_le_sum fun r _ ↦ ?_
        obtain ⟨s, hs⟩ := hU_mem r
        rw [hs, Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_pos (hlam r)]
        have hU_bd : |(G0 s j' : ℚ)| ≤ ((n.factorial * W1 ^ n : ℕ) : ℚ) := by
          have hnat_bd := hG0_bd s j'
          have h1 : ((G0 s j').natAbs : ℚ) ≤ ((n.factorial * W1 ^ n : ℕ) : ℚ) := by
            exact_mod_cast hnat_bd
          have h2 : |(G0 s j' : ℚ)| = ((G0 s j').natAbs : ℚ) := by
            rw [← Int.cast_abs, ← Int.natCast_natAbs, Int.cast_natCast]
          rw [h2]; exact h1
        have h1 : lam r * |(G0 s j' : ℚ)| ≤ 1 * ((n.factorial * W1 ^ n : ℕ) : ℚ) :=
          mul_le_mul (hlam_lt_one r).le hU_bd (abs_nonneg _) zero_le_one
        linarith
    _ = (k : ℚ) * ((n.factorial * W1 ^ n : ℕ) : ℚ) := by
        simp [Finset.sum_const]
    _ ≤ ((n + 1 : ℕ) : ℚ) * ((n.factorial * W1 ^ n : ℕ) : ℚ) := by
        refine mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _)
        exact_mod_cast hk_le
    _ ≤ (((n + 1).factorial * W1 ^ (n + 1) : ℕ) : ℚ) := by
        have hnat : (n + 1) * (n.factorial * W1 ^ n) ≤ (n + 1).factorial * W1 ^ (n + 1) := by
          rw [Nat.factorial_succ, Nat.pow_succ]
          have hW1 : 1 ≤ W1 := le_max_left 1 _
          calc (n + 1) * (n.factorial * W1 ^ n)
              = ((n + 1) * n.factorial) * W1 ^ n := by ring
            _ ≤ ((n + 1) * n.factorial) * (W1 ^ n * W1) :=
                Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_right _ hW1)
        have hcast : (((n + 1) * (n.factorial * W1 ^ n) : ℕ) : ℚ) ≤
            (((n + 1).factorial * W1 ^ (n + 1) : ℕ) : ℚ) := by exact_mod_cast hnat
        simpa only [Nat.cast_mul] using hcast
    _ = ((inst.numVars.factorial * W1 ^ inst.numVars : ℕ) : ℚ) := by rw [hnv]

end CslibFrontier.Complexity
