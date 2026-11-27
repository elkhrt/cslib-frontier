module

public import CslibFrontier.Foundations.BooleanAnalysis.Degree
public import CslibFrontier.Foundations.BooleanAnalysis.Fourier
public import CslibFrontier.Foundations.BooleanAnalysis.Noise
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Affine Pullbacks and Mod-q Fourier Mass on Boolean Functions

This module develops affine pullbacks of functions on the Boolean cube over `ZMod 2`, cumulative
low-degree Fourier mass (both mod-2 and mod-`q`), and noise stability preservation on top of
`Cslib.BitString`.

## Main definitions

* `CslibFrontier.Foundations.BooleanAnalysis.affineMap`: the $\mathbb{F}_2$-affine map
  `T(x) = A x ⊕ r` on Boolean cubes.
* `CslibFrontier.Foundations.BooleanAnalysis.rowSupport`,
  `CslibFrontier.Foundations.BooleanAnalysis.outputFanIn`, and
  `CslibFrontier.Foundations.BooleanAnalysis.pullbackSupport`: row supports, maximum fan-in
  $\Delta$, and character pullback support `J(S)`.
* `CslibFrontier.Foundations.BooleanAnalysis.lowDegreeMass`: cumulative mod-2 Fourier mass up to
  degree `k`, `∑_{|S| ≤ k} f̂(S)²`.
* `CslibFrontier.Foundations.BooleanAnalysis.supNorm`: supremum norm on finite Boolean cubes.
* `CslibFrontier.Foundations.BooleanAnalysis.modQChar`,
  `CslibFrontier.Foundations.BooleanAnalysis.modQFourierCoeff`, and
  `CslibFrontier.Foundations.BooleanAnalysis.modQLowDegreeMass`: cumulative mod-`q` Fourier mass
  over `(ι → ZMod q)`.

## Main results

* `CslibFrontier.Foundations.BooleanAnalysis.totalDegree_comp_affineMap_le` and
  `CslibFrontier.Foundations.BooleanAnalysis.totalDegree_comp_affineMap_perm_eq`: degree expansion
  `deg(p ∘ T) ≤ Δ * deg(p)` and exact preservation under coordinate permutations.
* `CslibFrontier.Foundations.BooleanAnalysis.supNorm_comp_le` and
  `CslibFrontier.Foundations.BooleanAnalysis.supNorm_comp_bijective_eq`: supremum norm contraction
  and bijective preservation.
* `CslibFrontier.Foundations.BooleanAnalysis.lowDegreeMass_comp_perm_eq`,
  `CslibFrontier.Foundations.BooleanAnalysis.lowDegreeMass_comp_disjoint_le`,
  `CslibFrontier.Foundations.BooleanAnalysis.lowDegreeMass_comp_le_mul_collision`, and
  `CslibFrontier.Foundations.BooleanAnalysis.noiseStability_comp_perm_eq`: low-degree Fourier mass
  and noise stability under affine pullbacks (permutation, disjoint row-supports, and
  collision-aware bounded fan-in).
* `CslibFrontier.Foundations.BooleanAnalysis.modQLowDegreeMass_comp_perm_shift_eq`: exact invariance
  of cumulative mod-`q` Fourier mass under signed coordinate permutations and shifts.
-/

public section

namespace CslibFrontier.Foundations.BooleanAnalysis

open Cslib.BitString Finset
open scoped BigOperators

/-! ### Affine maps over `ZMod 2` and character pullbacks -/

/-- Convert `Bool` to `ZMod 2` (`false ↦ 0`, `true ↦ 1`). -/
def boolToZMod2 (b : Bool) : ZMod 2 :=
  if b then 1 else 0

/-- Convert `ZMod 2` to `Bool` (`0 ↦ false`, `1 ↦ true`). -/
def zmod2ToBool (z : ZMod 2) : Bool :=
  decide (z = 1)

@[simp]
private theorem zmod2ToBool_boolToZMod2 (b : Bool) : zmod2ToBool (boolToZMod2 b) = b := by
  cases b <;> decide

private theorem zmod2_eq_zero_or_one (z : ZMod 2) : z = 0 ∨ z = 1 := by
  fin_cases z
  · left; rfl
  · right; rfl

private theorem neg_one_pow_zmod2ToBool_add (a b : ZMod 2) :
    ((-1 : ℝ) ^ (zmod2ToBool (a + b)).toNat) =
      (-1 : ℝ) ^ (zmod2ToBool a).toNat * (-1 : ℝ) ^ (zmod2ToBool b).toNat := by
  have h0 : zmod2ToBool 0 = false := rfl
  have h1 : zmod2ToBool 1 = true := rfl
  have h11 : (1 + 1 : ZMod 2) = 0 := rfl
  rcases zmod2_eq_zero_or_one a with rfl | rfl <;>
    rcases zmod2_eq_zero_or_one b with rfl | rfl <;>
    simp [h0, h1, h11]

private theorem neg_one_pow_zmod2ToBool_sum {α : Type*} (s : Finset α) (f : α → ZMod 2) :
    ((-1 : ℝ) ^ (zmod2ToBool (∑ i ∈ s, f i)).toNat) =
      ∏ i ∈ s, (-1 : ℝ) ^ (zmod2ToBool (f i)).toNat := by
  have h0 : zmod2ToBool 0 = false := rfl
  classical
  induction s using Finset.induction_on with
  | empty => simp [h0]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha, neg_one_pow_zmod2ToBool_add, ih]

/-- The $\mathbb{F}_2$-affine map `T(x) = A x ⊕ r` on Boolean cubes. -/
def affineMap {ι κ : Type*} [Fintype ι] (A : Matrix κ ι (ZMod 2)) (r : κ → Bool)
    (x : ι → Bool) : κ → Bool :=
  fun i => zmod2ToBool ((∑ j : ι, A i j * boolToZMod2 (x j)) + boolToZMod2 (r i))

/-- Support of row `i` of a `ZMod 2`-matrix `A`. -/
def rowSupport {ι κ : Type*} [Fintype ι] (A : Matrix κ ι (ZMod 2)) (i : κ) : Finset ι :=
  Finset.univ.filter fun j => A i j ≠ 0

/-- Output fan-in $\Delta = \max_i \|\mathrm{row}_i(A)\|_0$ of a `ZMod 2`-matrix `A`. -/
def outputFanIn {ι κ : Type*} [Fintype ι] [Fintype κ] (A : Matrix κ ι (ZMod 2)) : ℕ :=
  Finset.univ.sup fun i => (rowSupport A i).card

/-- Character pullback support `J(S) = {j | ∑ i ∈ S, A i j ≠ 0}` (the symmetric difference of
the row-supports over `i ∈ S`). -/
def pullbackSupport {ι κ : Type*} [Fintype ι] (A : Matrix κ ι (ZMod 2)) (S : Finset κ) :
    Finset ι :=
  Finset.univ.filter fun j => (∑ i ∈ S, A i j) ≠ 0

/-- Character pullback cardinality bound `|J(S)| ≤ Δ * |S|`. -/
theorem card_pullbackSupport_le {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix κ ι (ZMod 2)) (S : Finset κ) :
    (pullbackSupport A S).card ≤ outputFanIn A * S.card := by
  classical
  have hsub : pullbackSupport A S ⊆ S.biUnion (rowSupport A) := by
    intro j hj
    have hne : (∑ i ∈ S, A i j) ≠ 0 := (Finset.mem_filter.mp hj).2
    obtain ⟨i, hi, hA⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    exact Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hA⟩⟩
  calc
    (pullbackSupport A S).card ≤ (S.biUnion (rowSupport A)).card := Finset.card_le_card hsub
    _ ≤ ∑ i ∈ S, (rowSupport A i).card := Finset.card_biUnion_le
    _ ≤ ∑ _i ∈ S, outputFanIn A :=
        Finset.sum_le_sum fun i _ => Finset.le_sup (f := fun i => (rowSupport A i).card)
          (Finset.mem_univ i)
    _ = outputFanIn A * S.card := by
        simp [Finset.sum_const, mul_comm]

/-- Character pullback identity `χ_S(A x ⊕ r) = χ_S(r) * χ_{J(S)}(x)`. -/
theorem chi_affineMap {ι κ : Type*} [Fintype ι]
    (A : Matrix κ ι (ZMod 2)) (r : κ → Bool) (S : Finset κ) (x : ι → Bool) :
    chi ℝ S (affineMap A r x) = chi ℝ S r * chi ℝ (pullbackSupport A S) x := by
  classical
  have h0_bool : zmod2ToBool 0 = false := rfl
  have h1 : chi ℝ S (affineMap A r x) =
      chi ℝ S r *
        ∏ i ∈ S, ∏ j : ι, (-1 : ℝ) ^ (zmod2ToBool (A i j * boolToZMod2 (x j))).toNat := by
    simp only [chi, affineMap]
    have hrow : ∀ i ∈ S,
        ((-1 : ℝ) ^ (zmod2ToBool ((∑ j : ι, A i j * boolToZMod2 (x j)) +
          boolToZMod2 (r i))).toNat) =
        (-1 : ℝ) ^ (r i).toNat *
          ∏ j : ι, (-1 : ℝ) ^ (zmod2ToBool (A i j * boolToZMod2 (x j))).toNat := by
      intro i _
      rw [neg_one_pow_zmod2ToBool_add, zmod2ToBool_boolToZMod2, neg_one_pow_zmod2ToBool_sum,
        mul_comm]
    rw [Finset.prod_congr rfl hrow, Finset.prod_mul_distrib]
  rw [h1]
  congr 1
  rw [Finset.prod_comm]
  have hcol : ∀ j : ι,
      ∏ i ∈ S, (-1 : ℝ) ^ (zmod2ToBool (A i j * boolToZMod2 (x j))).toNat =
        if j ∈ pullbackSupport A S then (-1 : ℝ) ^ (x j).toNat else 1 := by
    intro j
    rw [← neg_one_pow_zmod2ToBool_sum, ← Finset.sum_mul]
    rcases zmod2_eq_zero_or_one (∑ i ∈ S, A i j) with h0 | h1'
    · have hnot : j ∉ pullbackSupport A S := by simp [pullbackSupport, h0]
      simp [h0, hnot, h0_bool]
    · have hmem : j ∈ pullbackSupport A S := by simp [pullbackSupport, h1']
      simp [h1', hmem, zmod2ToBool_boolToZMod2]
  simp_rw [hcol]
  rw [← Finset.prod_filter]
  have hfilt : Finset.univ.filter (fun j => j ∈ pullbackSupport A S) = pullbackSupport A S := by
    ext j; simp
  rw [hfilt, chi]

/-- Fourier coefficient formula for an affine pullback:
`widehat{p ∘ T}(U) = ∑_{J(S) = U} χ_S(r) * p̂(S)`. -/
theorem fourierCoeff_comp_affineMap {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (A : Matrix κ ι (ZMod 2)) (r : κ → Bool)
    (p : (κ → Bool) → ℝ) (U : Finset ι) :
    fourierCoeff (fun x => p (affineMap A r x)) U =
      ∑ S ∈ Finset.univ.filter (fun S => pullbackSupport A S = U),
        chi ℝ S r * fourierCoeff p S := by
  have hexp : (fun x => p (affineMap A r x)) =
      fun x => ∑ S : Finset κ,
        (chi ℝ S r * fourierCoeff p S) * chi ℝ (pullbackSupport A S) x := by
    funext x
    rw [← sum_fourierCoeff_mul_chi p (affineMap A r x)]
    refine Finset.sum_congr rfl fun S _ => ?_
    rw [chi_affineMap]
    ring
  rw [hexp, fourierCoeff_sum_mul]
  have hchi : ∀ S : Finset κ,
      fourierCoeff (chi ℝ (pullbackSupport A S)) U =
        if pullbackSupport A S = U then 1 else 0 := fun S => by
    rw [fourierCoeff_chi]
  simp_rw [hchi]
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun S _ => by split_ifs <;> simp

/-- **Affine pullback degree bound**: if `totalDegree p ≤ k`, then
`totalDegree (p ∘ T) ≤ Δ * k`. -/
theorem totalDegree_comp_affineMap_le {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix κ ι (ZMod 2)) (r : κ → Bool)
    (p : (κ → Bool) → ℝ) {k : ℕ} (hp : totalDegree p ≤ k) :
    totalDegree (fun x => p (affineMap A r x)) ≤ outputFanIn A * k := by
  classical
  rw [totalDegree_le_iff_fourierCoeff_eq_zero]
  intro U hU
  rw [fourierCoeff_comp_affineMap]
  refine Finset.sum_eq_zero fun S hS => ?_
  have hJU : pullbackSupport A S = U := (Finset.mem_filter.mp hS).2
  have hcard : U.card ≤ outputFanIn A * S.card := by
    rw [← hJU]
    exact card_pullbackSupport_le A S
  have hkS : k < S.card := by
    by_contra hle
    have hSk : S.card ≤ k := Nat.le_of_not_lt hle
    have h1 : outputFanIn A * S.card ≤ outputFanIn A * k := Nat.mul_le_mul_left _ hSk
    omega
  have hp0 : fourierCoeff p S = 0 := (totalDegree_le_iff_fourierCoeff_eq_zero.mp hp) S hkS
  simp [hp0]

/-- Permutation matrix over `ZMod 2` associated with an equivalence `e : κ ≃ ι`. -/
def permMatrix {ι κ : Type*} [DecidableEq ι] (e : κ ≃ ι) : Matrix κ ι (ZMod 2) :=
  Matrix.of fun i j => if e i = j then 1 else 0

private theorem rowSupport_permMatrix {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (e : κ ≃ ι) (i : κ) :
    rowSupport (permMatrix e) i = {e i} := by
  ext j
  simp [rowSupport, permMatrix, eq_comm]

private theorem pullbackSupport_permMatrix {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (e : κ ≃ ι) (S : Finset κ) :
    pullbackSupport (permMatrix e) S = S.map e.toEmbedding := by
  classical
  ext j
  simp only [pullbackSupport, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
    Equiv.coe_toEmbedding]
  simp only [permMatrix, Matrix.of_apply]
  have hsum : (∑ i ∈ S, if e i = j then (1 : ZMod 2) else 0) =
      if e.symm j ∈ S then 1 else 0 := by
    by_cases hmem : e.symm j ∈ S
    · have h1 : (∑ i ∈ S, if e i = j then (1 : ZMod 2) else 0) = 1 := by
        rw [Finset.sum_eq_single (e.symm j)]
        · simp
        · intro i _ hne
          have : e i ≠ j := fun heq => hne (e.injective (heq.trans (e.apply_symm_apply j).symm))
          simp [this]
        · intro h; exact False.elim (h hmem)
      simp [hmem, h1]
    · have h0 : (∑ i ∈ S, if e i = j then (1 : ZMod 2) else 0) = 0 := by
        refine Finset.sum_eq_zero fun i hi => ?_
        have : e i ≠ j := fun heq => hmem (by simpa [← heq] using hi)
        simp [this]
      simp [hmem, h0]
  rw [hsum]
  constructor
  · intro h
    have hmem : e.symm j ∈ S := by by_contra hc; simp [hc] at h
    exact ⟨e.symm j, hmem, e.apply_symm_apply j⟩
  · rintro ⟨i, hi, rfl⟩
    simp [hi]

private theorem outputFanIn_permMatrix {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [Nonempty κ] (e : κ ≃ ι) :
    outputFanIn (permMatrix e) = 1 := by
  simp only [outputFanIn, rowSupport_permMatrix, Finset.card_singleton]
  exact Finset.sup_const Finset.univ_nonempty 1

private theorem fourierCoeff_comp_permMatrix {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (e : κ ≃ ι) (r : κ → Bool)
    (p : (κ → Bool) → ℝ) (U : Finset ι) :
    fourierCoeff (fun x => p (affineMap (permMatrix e) r x)) U =
      chi ℝ (U.map e.symm.toEmbedding) r * fourierCoeff p (U.map e.symm.toEmbedding) := by
  rw [fourierCoeff_comp_affineMap]
  have huniq :
      Finset.univ.filter (fun S => pullbackSupport (permMatrix e) S = U) =
        {U.map e.symm.toEmbedding} := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
      pullbackSupport_permMatrix]
    constructor
    · intro h
      rw [← h, Finset.map_map]
      ext i; simp
    · rintro rfl
      rw [Finset.map_map]
      ext j; simp
  rw [huniq, Finset.sum_singleton]

/-- Under a coordinate permutation `permMatrix e` with $\mathbb{F}_2$-shift `r`, multilinear
degree is preserved exactly: `totalDegree (p ∘ T) = totalDegree p`. -/
theorem totalDegree_comp_affineMap_perm_eq {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (e : κ ≃ ι) (r : κ → Bool) (p : (κ → Bool) → ℝ) :
    totalDegree (fun x => p (affineMap (permMatrix e) r x)) = totalDegree p := by
  let _ : Fintype κ := Fintype.ofEquiv ι e.symm
  classical
  apply le_antisymm
  · by_cases hne : Nonempty κ
    · have h := totalDegree_comp_affineMap_le (permMatrix e) r p (k := totalDegree p) le_rfl
      rwa [outputFanIn_permMatrix e, one_mul] at h
    · have _hκ : IsEmpty κ := not_nonempty_iff.mp hne
      have _hι : IsEmpty ι := e.symm.isEmpty
      rw [totalDegree_le_iff_fourierCoeff_eq_zero]
      intro U hU
      have hU0 : U.card = 0 := by simp [Finset.eq_empty_of_isEmpty U]
      omega
  · rw [totalDegree_le_iff_fourierCoeff_eq_zero]
    intro S hS
    have h0 := (totalDegree_le_iff_fourierCoeff_eq_zero.mp
      (le_refl (totalDegree (fun x => p (affineMap (permMatrix e) r x)))))
      (S.map e.toEmbedding) (by simpa [Finset.card_map] using hS)
    rw [fourierCoeff_comp_permMatrix] at h0
    have hmap : (S.map e.toEmbedding).map e.symm.toEmbedding = S := by
      rw [Finset.map_map]; ext i; simp
    rw [hmap] at h0
    have hchi_ne : chi ℝ S r ≠ 0 := by
      have habs : |chi ℝ S r| = 1 := abs_chi S r
      intro hc; rw [hc, abs_zero] at habs; norm_num at habs
    exact (mul_eq_zero.mp h0).resolve_left hchi_ne

/-! ### Supremum norm, low-degree Fourier mass, and noise stability -/

/-- Supremum norm `‖f‖_∞ = sup_x |f(x)|` on a finite Boolean cube. -/
noncomputable def supNorm {ι : Type*} (f : (ι → Bool) → ℝ) : ℝ :=
  ⨆ x : ι → Bool, |f x|

/-- Pullback contracts the supremum norm: `‖p ∘ T‖_∞ ≤ ‖p‖_∞`. -/
theorem supNorm_comp_le {ι κ : Type*} [Finite κ]
    (T : (ι → Bool) → (κ → Bool)) (p : (κ → Bool) → ℝ) :
    supNorm (fun x => p (T x)) ≤ supNorm p := by
  unfold supNorm
  exact ciSup_le fun x => le_ciSup (f := fun y : κ → Bool => |p y|)
    (Set.finite_range _).bddAbove (T x)

/-- Bijective maps preserve the supremum norm exactly: `‖p ∘ T‖_∞ = ‖p‖_∞`. -/
theorem supNorm_comp_bijective_eq {ι κ : Type*} [Finite ι] [Finite κ]
    {T : (ι → Bool) → (κ → Bool)} (hT : Function.Bijective T)
    (p : (κ → Bool) → ℝ) :
    supNorm (fun x => p (T x)) = supNorm p := by
  apply le_antisymm (supNorm_comp_le T p)
  unfold supNorm
  refine ciSup_le fun y => ?_
  obtain ⟨x, rfl⟩ := hT.2 y
  exact le_ciSup (f := fun z : ι → Bool => |p (T z)|) (Set.finite_range _).bddAbove x

section LowDegree

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- Cumulative mod-2 Fourier mass up to degree `k`: `mass_{≤ k}(f) = ∑_{|S| ≤ k} f̂(S)²`. -/
noncomputable def lowDegreeMass (k : ℕ) (f : (ι → Bool) → ℝ) : ℝ :=
  ∑ S ∈ Finset.univ.filter (fun S : Finset ι => S.card ≤ k), fourierCoeff f S ^ 2

/-- Cumulative low-degree Fourier mass is nonnegative. -/
theorem lowDegreeMass_nonneg (k : ℕ) (f : (ι → Bool) → ℝ) : 0 ≤ lowDegreeMass k f :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- Any single squared Fourier coefficient of degree `|S| ≤ k` is bounded by `lowDegreeMass k f`. -/
theorem fourierCoeff_sq_le_lowDegreeMass {k : ℕ} {S : Finset ι} (hS : S.card ≤ k)
    (f : (ι → Bool) → ℝ) : fourierCoeff f S ^ 2 ≤ lowDegreeMass k f :=
  Finset.single_le_sum (fun _ _ => sq_nonneg _) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hS⟩)

/-- Scalar multiplication distributes into `lowDegreeMass k f`. -/
theorem mul_lowDegreeMass (c : ℝ) (k : ℕ) (f : (ι → Bool) → ℝ) :
    c * lowDegreeMass k f =
      ∑ S ∈ Finset.univ.filter (fun S : Finset ι => S.card ≤ k), c * fourierCoeff f S ^ 2 :=
  Finset.mul_sum _ _ _

/-- **Permutation case of low-degree Fourier mass**: for a permutation matrix with shift `r`,
`mass_{≤ k}(p ∘ T) = mass_{≤ k}(p)`. -/
theorem lowDegreeMass_comp_perm_eq (e : κ ≃ ι) (r : κ → Bool) (k : ℕ) (p : (κ → Bool) → ℝ) :
    lowDegreeMass k (fun x => p (affineMap (permMatrix e) r x)) = lowDegreeMass k p := by
  simp only [lowDegreeMass]
  refine Finset.sum_bij (fun U _ => U.map e.symm.toEmbedding)
    (fun U hU => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.card_map] at hU ⊢
      exact hU)
    (fun U₁ _ U₂ _ h => by
      have := congrArg (fun V => V.map e.toEmbedding) h
      simpa [Finset.map_map] using this)
    (fun S hS => ⟨S.map e.toEmbedding, by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.card_map] at hS ⊢
      exact hS, by rw [Finset.map_map]; ext i; simp⟩)
    (fun U _ => by
      rw [fourierCoeff_comp_permMatrix, mul_pow]
      have hsq : chi ℝ (U.map e.symm.toEmbedding) r ^ 2 = 1 := by
        rw [sq, chi_mul_self]
      rw [hsq, one_mul])

/-- **Disjoint row-supports case**: if distinct rows of `A` have pairwise disjoint nonempty
supports, then `mass_{≤ k}(p ∘ T) = ∑_{|J(S)| ≤ k} p̂(S)² ≤ mass_{≤ k}(p)`. -/
theorem lowDegreeMass_comp_disjoint_le (A : Matrix κ ι (ZMod 2)) (r : κ → Bool)
    (hne : ∀ i : κ, (rowSupport A i).Nonempty)
    (hdisj : ∀ i₁ i₂ : κ, i₁ ≠ i₂ → Disjoint (rowSupport A i₁) (rowSupport A i₂))
    (k : ℕ) (p : (κ → Bool) → ℝ) :
    lowDegreeMass k (fun x => p (affineMap A r x)) =
      (∑ S ∈ Finset.univ.filter (fun S => (pullbackSupport A S).card ≤ k),
        fourierCoeff p S ^ 2) ∧
    lowDegreeMass k (fun x => p (affineMap A r x)) ≤ lowDegreeMass k p := by
  have hJ_eq : ∀ S : Finset κ, pullbackSupport A S = S.biUnion (rowSupport A) := by
    intro S
    ext j
    simp only [pullbackSupport, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
      rowSupport]
    constructor
    · intro hsum
      obtain ⟨i, hi, hA⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum
      exact ⟨i, hi, hA⟩
    · rintro ⟨i, hi, hA⟩
      rw [Finset.sum_eq_single i]
      · exact hA
      · intro i' hi' hne'
        by_contra hA'
        have hmem1 : j ∈ rowSupport A i := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hA⟩
        have hmem2 : j ∈ rowSupport A i' := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hA'⟩
        exact Finset.disjoint_left.mp (hdisj i i' hne'.symm) hmem1 hmem2
      · intro h; exact False.elim (h hi)
  have hJ_card : ∀ S : Finset κ, S.card ≤ (pullbackSupport A S).card := by
    intro S
    rw [hJ_eq S, Finset.card_biUnion (fun i₁ _ i₂ _ hne' => hdisj i₁ i₂ hne')]
    calc
      S.card = ∑ _i ∈ S, 1 := by simp
      _ ≤ ∑ i ∈ S, (rowSupport A i).card :=
          Finset.sum_le_sum fun i _ => Finset.card_pos.mpr (hne i)
  have hJ_inj : Function.Injective (pullbackSupport A) := by
    intro S₁ S₂ heq
    ext i
    obtain ⟨j, hj⟩ := hne i
    have hmem : ∀ S : Finset κ, j ∈ pullbackSupport A S ↔ i ∈ S := fun S => by
      rw [hJ_eq S, Finset.mem_biUnion]
      constructor
      · rintro ⟨i', hi', hj'⟩
        by_contra hne'
        exact Finset.disjoint_left.mp (hdisj i i' (fun h => hne' (h ▸ hi'))) hj hj'
      · intro hi; exact ⟨i, hi, hj⟩
    rw [← hmem S₁, heq, hmem S₂]
  have hcoeff_sq : ∀ S : Finset κ,
      fourierCoeff (fun x => p (affineMap A r x)) (pullbackSupport A S) ^ 2 =
        fourierCoeff p S ^ 2 := by
    intro S
    rw [fourierCoeff_comp_affineMap]
    have hfilt :
        Finset.univ.filter (fun S' => pullbackSupport A S' = pullbackSupport A S) = {S} := by
      ext S'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      exact ⟨fun h => hJ_inj h, fun h => h ▸ rfl⟩
    rw [hfilt, Finset.sum_singleton, mul_pow, show chi ℝ S r ^ 2 = 1 by rw [sq, chi_mul_self],
      one_mul]
  have hzero_off : ∀ U : Finset ι, (∀ S : Finset κ, pullbackSupport A S ≠ U) →
      fourierCoeff (fun x => p (affineMap A r x)) U = 0 := by
    intro U hU
    rw [fourierCoeff_comp_affineMap]
    refine Finset.sum_eq_zero fun S hS => ?_
    exact False.elim (hU S (Finset.mem_filter.mp hS).2)
  have heq : lowDegreeMass k (fun x => p (affineMap A r x)) =
      ∑ S ∈ Finset.univ.filter (fun S => (pullbackSupport A S).card ≤ k),
        fourierCoeff p S ^ 2 := by
    simp only [lowDegreeMass]
    have hsplit :
        ∑ U ∈ Finset.univ.filter (fun U : Finset ι => U.card ≤ k),
          fourierCoeff (fun x => p (affineMap A r x)) U ^ 2 =
        ∑ U ∈ (Finset.univ.filter (fun S : Finset κ => (pullbackSupport A S).card ≤ k)).image
            (pullbackSupport A),
          fourierCoeff (fun x => p (affineMap A r x)) U ^ 2 := by
      symm
      refine Finset.sum_subset ?_ ?_
      · intro U hU
        obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hU
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hS).2⟩
      · intro U hU hnot
        have hnone : ∀ S : Finset κ, pullbackSupport A S ≠ U := by
          intro S hS
          apply hnot
          refine Finset.mem_image.mpr ⟨S, ?_, hS⟩
          exact Finset.mem_filter.mpr
            ⟨Finset.mem_univ _, by rw [hS]; exact (Finset.mem_filter.mp hU).2⟩
        rw [hzero_off U hnone, zero_pow two_ne_zero]
    rw [hsplit, Finset.sum_image (fun S₁ _ S₂ _ h => hJ_inj h)]
    refine Finset.sum_congr rfl fun S _ => hcoeff_sq S
  refine ⟨heq, ?_⟩
  rw [heq, lowDegreeMass]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => sq_nonneg _)
  intro S hS
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hJ_card S).trans (Finset.mem_filter.mp hS).2⟩

omit [DecidableEq κ] in
/-- Collision multiplicity `m_U = |{S : J(S) = U}|`. -/
def collisionMult (A : Matrix κ ι (ZMod 2)) (U : Finset ι) : ℕ :=
  (Finset.univ.filter (fun S : Finset κ => pullbackSupport A S = U)).card

omit [DecidableEq κ] in
/-- Maximum collision multiplicity up to degree `k`: `M_k = max_{|U| ≤ k} m_U`. -/
def maxCollisionMult (A : Matrix κ ι (ZMod 2)) (k : ℕ) : ℕ :=
  (Finset.univ.filter (fun U : Finset ι => U.card ≤ k)).sup (collisionMult A)

/-- **General bounded fan-in collision-aware bound**:
`mass_{≤ k}(p ∘ T) ≤ M_k * ∑_{S : |J(S)| ≤ k} p̂(S)²`. -/
theorem lowDegreeMass_comp_le_mul_collision (A : Matrix κ ι (ZMod 2)) (r : κ → Bool)
    (k : ℕ) (p : (κ → Bool) → ℝ) :
    lowDegreeMass k (fun x => p (affineMap A r x)) ≤
      (maxCollisionMult A k : ℝ) *
        ∑ S ∈ Finset.univ.filter (fun S => (pullbackSupport A S).card ≤ k),
          fourierCoeff p S ^ 2 := by
  simp only [lowDegreeMass]
  have hpoint : ∀ U ∈ Finset.univ.filter (fun U : Finset ι => U.card ≤ k),
      fourierCoeff (fun x => p (affineMap A r x)) U ^ 2 ≤
        (maxCollisionMult A k : ℝ) *
          ∑ S ∈ Finset.univ.filter (fun S => pullbackSupport A S = U),
            fourierCoeff p S ^ 2 := by
    intro U hU
    rw [fourierCoeff_comp_affineMap]
    have hcs :
        (∑ S ∈ Finset.univ.filter (fun S => pullbackSupport A S = U),
            chi ℝ S r * fourierCoeff p S) ^ 2 ≤
          (collisionMult A U : ℝ) *
            ∑ S ∈ Finset.univ.filter (fun S => pullbackSupport A S = U),
              (chi ℝ S r * fourierCoeff p S) ^ 2 := by
      have hraw := Finset.sum_mul_sq_le_sq_mul_sq
        (Finset.univ.filter (fun S : Finset κ => pullbackSupport A S = U))
        (fun _ => (1 : ℝ)) (fun S => chi ℝ S r * fourierCoeff p S)
      simpa only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one,
        collisionMult] using hraw
    have hsq : ∀ S : Finset κ, (chi ℝ S r * fourierCoeff p S) ^ 2 = fourierCoeff p S ^ 2 := by
      intro S
      rw [mul_pow, show chi ℝ S r ^ 2 = 1 by rw [sq, chi_mul_self], one_mul]
    simp_rw [hsq] at hcs
    have hmult : (collisionMult A U : ℝ) ≤ (maxCollisionMult A k : ℝ) := by
      exact_mod_cast Finset.le_sup (f := collisionMult A) hU
    calc
      (∑ S ∈ Finset.univ.filter (fun S => pullbackSupport A S = U),
          chi ℝ S r * fourierCoeff p S) ^ 2
          ≤ (collisionMult A U : ℝ) *
              ∑ S ∈ Finset.univ.filter (fun S => pullbackSupport A S = U),
                fourierCoeff p S ^ 2 := hcs
      _ ≤ (maxCollisionMult A k : ℝ) *
            ∑ S ∈ Finset.univ.filter (fun S => pullbackSupport A S = U),
              fourierCoeff p S ^ 2 :=
          mul_le_mul_of_nonneg_right hmult (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  calc
    ∑ U ∈ Finset.univ.filter (fun U : Finset ι => U.card ≤ k),
        fourierCoeff (fun x => p (affineMap A r x)) U ^ 2
        ≤ ∑ U ∈ Finset.univ.filter (fun U : Finset ι => U.card ≤ k),
            (maxCollisionMult A k : ℝ) *
              ∑ S ∈ Finset.univ.filter (fun S => pullbackSupport A S = U),
                fourierCoeff p S ^ 2 := Finset.sum_le_sum hpoint
    _ = (maxCollisionMult A k : ℝ) *
          ∑ U ∈ Finset.univ.filter (fun U : Finset ι => U.card ≤ k),
            ∑ S ∈ Finset.univ.filter (fun S => pullbackSupport A S = U),
              fourierCoeff p S ^ 2 := by rw [Finset.mul_sum]
    _ = (maxCollisionMult A k : ℝ) *
          ∑ S ∈ Finset.univ.filter (fun S => (pullbackSupport A S).card ≤ k),
            fourierCoeff p S ^ 2 := by
          congr 1
          rw [← Finset.sum_biUnion]
          · congr 1
            ext S
            simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨fun ⟨U, hU, hSU⟩ => hSU ▸ hU, fun hS => ⟨pullbackSupport A S, hS, rfl⟩⟩
          · intro U₁ _ U₂ _ hne
            change Disjoint _ _
            rw [Finset.disjoint_left]
            intro S h1 h2
            exact hne ((Finset.mem_filter.mp h1).2.symm.trans (Finset.mem_filter.mp h2).2)

/-- **Noise stability preservation (permutation case)**: for a permutation matrix with shift `r`,
`noiseStability ρ (p ∘ T) = noiseStability ρ p` for all `ρ : ℝ`. -/
theorem noiseStability_comp_perm_eq (e : κ ≃ ι) (r : κ → Bool) (ρ : ℝ) (p : (κ → Bool) → ℝ) :
    noiseStability ρ (fun x => p (affineMap (permMatrix e) r x)) = noiseStability ρ p := by
  rw [noiseStability_eq_sum, noiseStability_eq_sum]
  refine Finset.sum_bij (fun U _ => U.map e.symm.toEmbedding)
    (fun _ _ => Finset.mem_univ _)
    (fun U₁ _ U₂ _ h => by
      have := congrArg (fun V => V.map e.toEmbedding) h
      simpa [Finset.map_map] using this)
    (fun S _ => ⟨S.map e.toEmbedding, Finset.mem_univ _, by rw [Finset.map_map]; ext i; simp⟩)
    (fun U _ => ?_)
  rw [Finset.card_map, fourierCoeff_comp_permMatrix, mul_pow,
    show chi ℝ (U.map e.symm.toEmbedding) r ^ 2 = 1 by rw [sq, chi_mul_self], one_mul]

end LowDegree

/-! ### Mod-`q` Fourier mass invariance under signed permutations and shifts -/

section ModQ

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- Additive character `χ_a(x) = exp(2πi (∑_j a_j x_j) / q)` on `(ι → ZMod q)`. -/
noncomputable def modQChar (q : ℕ) (a x : ι → ZMod q) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (((∑ j : ι, (a j * x j).val : ℕ) : ℂ) / (q : ℂ)))

/-- Mod-`q` Fourier coefficient `f̂(a) = q^{-|ι|} ∑_x f(x) conj(χ_a(x))`. -/
noncomputable def modQFourierCoeff (q : ℕ) [NeZero q] (f : (ι → ZMod q) → ℂ)
    (a : ι → ZMod q) : ℂ :=
  ((q : ℂ)⁻¹ ^ Fintype.card ι) * ∑ x : ι → ZMod q, f x * star (modQChar q a x)

/-- Cumulative mod-`q` Fourier mass up to Hamming degree `k`. -/
noncomputable def modQLowDegreeMass (q : ℕ) [NeZero q] (k : ℕ)
    (f : (ι → ZMod q) → ℂ) : ℝ :=
  ∑ a ∈ Finset.univ.filter
      (fun a : ι → ZMod q => (Finset.univ.filter (fun i => a i ≠ 0)).card ≤ k),
    ‖modQFourierCoeff q f a‖ ^ 2

private theorem modQChar_val_eq (q : ℕ) [NeZero q] (z : ZMod q) (m : ℕ)
    (h : (m : ZMod q) = z) :
    Complex.exp (2 * Real.pi * Complex.I * ((m : ℂ) / (q : ℂ))) =
      Complex.exp (2 * Real.pi * Complex.I * ((z.val : ℂ) / (q : ℂ))) := by
  have hq_ne : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  have hmod : m % q = z.val := by
    rw [← h, ZMod.val_natCast]
  have hdiv : (m : ℕ) = q * (m / q) + m % q := (Nat.div_add_mod m q).symm
  have hcast : ((m : ℂ) / (q : ℂ)) = ((m / q : ℕ) : ℂ) + ((z.val : ℂ) / (q : ℂ)) := by
    rw [← hmod]
    have hm : (m : ℂ) = (q : ℂ) * ((m / q : ℕ) : ℂ) + ((m % q : ℕ) : ℂ) := by
      exact_mod_cast hdiv
    rw [hm]
    field_simp [hq_ne]
  rw [hcast, mul_add, Complex.exp_add]
  have hper : Complex.exp (2 * Real.pi * Complex.I * ((m / q : ℕ) : ℂ)) = 1 := by
    rw [show 2 * Real.pi * Complex.I * ((m / q : ℕ) : ℂ) =
        ((m / q : ℕ) : ℂ) * (2 * Real.pi * Complex.I) by ring]
    exact Complex.exp_nat_mul_two_pi_mul_I (m / q)
  rw [hper, one_mul]

omit [DecidableEq ι] in
private theorem modQChar_add (q : ℕ) [NeZero q] (a x y : ι → ZMod q) :
    modQChar q a (x + y) = modQChar q a x * modQChar q a y := by
  simp only [modQChar, ← Complex.exp_add, ← mul_add, ← add_div]
  have hsum :
      ((∑ j : ι, (a j * (x j + y j)).val : ℕ) : ZMod q) =
        ∑ j : ι, a j * (x j + y j) := by
    simp
  have hsum2 :
      (((∑ j : ι, (a j * x j).val) + (∑ j : ι, (a j * y j).val) : ℕ) : ZMod q) =
        ∑ j : ι, a j * (x j + y j) := by
    simp [mul_add, Finset.sum_add_distrib]
  have h1 := modQChar_val_eq q (∑ j : ι, a j * (x j + y j))
    (∑ j : ι, (a j * (x j + y j)).val) hsum
  have h2 := modQChar_val_eq q (∑ j : ι, a j * (x j + y j))
    ((∑ j : ι, (a j * x j).val) + (∑ j : ι, (a j * y j).val)) hsum2
  rw [← h1] at h2
  have hcast : (((∑ j : ι, (a j * x j).val) + (∑ j : ι, (a j * y j).val) : ℕ) : ℂ) =
      ((∑ j : ι, (a j * x j).val : ℕ) : ℂ) + ((∑ j : ι, (a j * y j).val : ℕ) : ℂ) := by
    push_cast; rfl
  rw [hcast] at h2
  exact h2.symm

omit [DecidableEq ι] in
private theorem norm_modQChar (q : ℕ) (a x : ι → ZMod q) :
    ‖modQChar q a x‖ = 1 := by
  simp only [modQChar]
  have hrew :
      2 * Real.pi * Complex.I * (((∑ j : ι, (a j * x j).val : ℕ) : ℂ) / (q : ℂ)) =
        ((2 * Real.pi * ((∑ j : ι, (a j * x j).val : ℕ) : ℝ) / (q : ℝ) : ℝ) : ℂ) *
          Complex.I := by
    push_cast; ring
  rw [hrew, Complex.norm_exp_ofReal_mul_I]

/-- **Exact invariance of mod-`q` low-degree Fourier mass** under coordinate permutations,
unit-scalar coordinate rescalings (including bit flips `x_i ↦ 1 - x_i = (-1) x_i + 1`), and
shifts over `ZMod q`. -/
theorem modQLowDegreeMass_comp_perm_shift_eq {κ : Type*} [Fintype κ] [DecidableEq κ]
    (q : ℕ) [NeZero q] (e : κ ≃ ι) (ε : κ → (ZMod q)ˣ) (r : κ → ZMod q)
    (k : ℕ) (f : (κ → ZMod q) → ℂ) :
    let T : (ι → ZMod q) → (κ → ZMod q) := fun x i => (ε i : ZMod q) * x (e i) + r i
    modQLowDegreeMass q k (fun x => f (T x)) = modQLowDegreeMass q k f := by
  intro T
  have hT_bij : Function.Bijective T := by
    refine ⟨fun x₁ x₂ h => ?_, fun y => ?_⟩
    · funext j
      have hi := congrFun h (e.symm j)
      simp only [T, Equiv.apply_symm_apply, add_right_cancel_iff] at hi
      have := congrArg (fun z => ((ε (e.symm j))⁻¹ : ZMod q) * z) hi
      simpa [← mul_assoc] using this
    · refine ⟨fun j => ((ε (e.symm j))⁻¹ : ZMod q) * (y (e.symm j) - r (e.symm j)), ?_⟩
      funext i
      simp [T, ← mul_assoc]
  set Tinv : (κ → ZMod q) → (ι → ZMod q) :=
    fun y j => ((ε (e.symm j))⁻¹ : ZMod q) * (y (e.symm j) - r (e.symm j))
  have hTinvT : ∀ x, Tinv (T x) = x := fun x => by
    funext j; simp [T, Tinv, ← mul_assoc]
  -- Associated frequency bijection on `(ι → ZMod q) ≃ (κ → ZMod q)`.
  set freq : (ι → ZMod q) ≃ (κ → ZMod q) :=
    { toFun := fun a i => ((ε i)⁻¹ : ZMod q) * a (e i)
      invFun := fun b j => (ε (e.symm j) : ZMod q) * b (e.symm j)
      left_inv := fun a => by funext j; simp [← mul_assoc]
      right_inv := fun b => by funext i; simp [← mul_assoc] }
  have hdot : ∀ (a : ι → ZMod q) (y : κ → ZMod q),
      (∑ j : ι, a j * Tinv y j) =
        (∑ i : κ, freq a i * y i) + (∑ i : κ, freq a i * (-r i)) := by
    intro a y
    have h1 : (∑ j : ι, a j * Tinv y j) =
        ∑ i : κ, a (e i) * (((ε i)⁻¹ : ZMod q) * (y i - r i)) := by
      refine Fintype.sum_equiv e.symm _ _ fun j => ?_
      simp [Tinv]
    rw [h1, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [freq, Equiv.coe_fn_mk]
    ring
  have hchar : ∀ (a : ι → ZMod q) (y : κ → ZMod q),
      modQChar q a (Tinv y) =
        modQChar q (freq a) y * modQChar q (freq a) (-r) := by
    intro a y
    rw [← modQChar_add]
    simp only [modQChar]
    have h1 := modQChar_val_eq q (∑ j : ι, a j * Tinv y j)
      (∑ j : ι, (a j * Tinv y j).val) (by simp)
    have h2 := modQChar_val_eq q (∑ i : κ, freq a i * (y + -r) i)
      (∑ i : κ, (freq a i * (y + -r) i).val) (by simp)
    rw [h1, h2]
    congr 1
    have heq : (∑ j : ι, a j * Tinv y j) = ∑ i : κ, freq a i * (y + -r) i := by
      rw [hdot, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => by simp [Pi.add_apply, mul_add]
    rw [heq]
  have hnorm_coeff : ∀ a : ι → ZMod q,
      ‖modQFourierCoeff q (fun x => f (T x)) a‖ = ‖modQFourierCoeff q f (freq a)‖ := by
    intro a
    simp only [modQFourierCoeff]
    have hsum :
        ∑ x : ι → ZMod q, f (T x) * star (modQChar q a x) =
          star (modQChar q (freq a) (-r)) *
            ∑ y : κ → ZMod q, f y * star (modQChar q (freq a) y) := by
      rw [Finset.mul_sum]
      refine Fintype.sum_equiv (Equiv.ofBijective T hT_bij) _ _ fun x => ?_
      simp only [Equiv.ofBijective_apply]
      have hcx : modQChar q a x = modQChar q (freq a) (T x) * modQChar q (freq a) (-r) := by
        simpa only [hTinvT x] using hchar a (T x)
      rw [hcx, star_mul']
      ring
    rw [hsum, ← mul_assoc, mul_comm (((q : ℂ)⁻¹ ^ Fintype.card ι)) (star _), mul_assoc,
      norm_mul, norm_star, norm_modQChar, one_mul, Fintype.card_congr e]
  have hwt : ∀ a : ι → ZMod q,
      (Finset.univ.filter (fun i : κ => freq a i ≠ 0)).card =
        (Finset.univ.filter (fun j : ι => a j ≠ 0)).card := by
    intro a
    refine Finset.card_bij (fun i _ => e i)
      (fun i hi => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, freq, Equiv.coe_fn_mk] at hi ⊢
        exact right_ne_zero_of_mul hi)
      (fun i₁ _ i₂ _ h => e.injective h)
      (fun j hj => ⟨e.symm j, by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, freq, Equiv.coe_fn_mk] at hj ⊢
        rw [Equiv.apply_symm_apply]
        intro h0
        apply hj
        have := congrArg (fun z => (ε (e.symm j) : ZMod q) * z) h0
        simpa [← mul_assoc] using this, e.apply_symm_apply j⟩)
  simp only [modQLowDegreeMass]
  refine Finset.sum_bij (fun a _ => freq a)
    (fun a ha => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
      rwa [hwt a])
    (fun a₁ _ a₂ _ h => freq.injective h)
    (fun b hb => ⟨freq.symm b, by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
      rwa [← hwt (freq.symm b), Equiv.apply_symm_apply], Equiv.apply_symm_apply freq b⟩)
    (fun a _ => by rw [hnorm_coeff a])

end ModQ

private theorem affinePullback_sanity :
    totalDegree (fun x : Fin 2 → Bool =>
      chi ℝ ({0} : Finset (Fin 2)) (affineMap (permMatrix (Equiv.swap (0 : Fin 2) 1))
        (fun _ => true) x)) = 1 := by
  have h := totalDegree_comp_affineMap_perm_eq (Equiv.swap (0 : Fin 2) 1) (fun _ => true)
    (chi ℝ ({0} : Finset (Fin 2)))
  rw [h]
  apply le_antisymm
  · rw [totalDegree_le_iff_fourierCoeff_eq_zero]
    intro S hS
    rw [fourierCoeff_chi]
    have hne : ({0} : Finset (Fin 2)) ≠ S := by
      intro heq; subst heq; simp at hS
    simp [hne]
  · have h1 := card_le_totalDegree_of_fourierCoeff_ne_zero (f := chi ℝ ({0} : Finset (Fin 2)))
      (S := {0}) (by rw [fourierCoeff_chi]; simp)
    simpa using h1

end CslibFrontier.Foundations.BooleanAnalysis
