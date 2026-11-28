module

public import CslibFrontier.Computability.Complexity.Polyhedra.QuasiPolynomial
public import Mathlib.Data.Set.Card
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Data.Int.Interval
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Vector Partition Functions and Parametric Rational Polytope Lattice Point Counts

This module proves piecewise quasi-polynomiality of vector partition functions and bounded
parametric rational convex polytope lattice-point counts on `ℤ^d`:

* `vectorPartitionCount_isPiecewiseQuasiPolynomial`: for any integer linear map
  `A : (Fin s → ℤ) →+ (Fin k → ℤ)` admitting a strictly positive separating linear functional,
  `b ↦ #{x ∈ ℕ^s : A x = b}` is a piecewise quasi-polynomial on `ℤ^k`.
* `exists_pos_linearFunctional_of_pointed`: Gordan's separation lemma yielding an integer linear
  functional strictly positive on the columns of `A` whenever `ker(A_ℝ) ∩ ℝ≥0^s = {0}`.
* `parametricPolytopeCount_isPiecewiseQuasiPolynomial`: for any integer linear maps
  `A₁ : ℤ^s →+ ℤ^u`, `A₂ : ℤ^{s'} →+ ℤ^u`, and `B : ℤ^d →+ ℤ^u` with
  `ker(A_ℝ) ∩ (ℝ≥0^s × ℝ^{s'}) = {0}`, the lattice-point count
  `n(y) = #{(x, z) ∈ ℕ^s × ℤ^{s'} : A₁ x + A₂ z = B y}` is piecewise quasi-polynomial in `y`.
-/

public section

namespace CslibFrontier.Complexity.Polyhedra

open scoped BigOperators

/-! ### 1. Summing a Piecewise Quasi-Polynomial Along an Integer Ray -/

section RaySum

/-- Integer ceiling of `n / d` for `d > 0`: `⌈n / d⌉ = -((-n) / d)` using Euclidean division. -/
private def intCeilDiv (n d : ℤ) : ℤ := -((-n) / d)

private theorem intCeilDiv_le_iff {n d m : ℤ} (hd : 0 < d) :
    intCeilDiv n d ≤ m ↔ n ≤ d * m := by
  unfold intCeilDiv
  rw [neg_le, Int.le_ediv_iff_mul_le hd]
  constructor <;> intro h <;> nlinarith

private theorem le_intFloorDiv_iff {n d m : ℤ} (hd : 0 < d) :
    m ≤ n / d ↔ d * m ≤ n := by
  rw [Int.le_ediv_iff_mul_le hd, mul_comm]

private theorem int_ediv_cast_rat (n : ℤ) {D : ℕ} (hD : 0 < D) :
    ((n / (D : ℤ) : ℤ) : ℚ) = ((n : ℚ) - ((n % (D : ℤ) : ℤ) : ℚ)) / (D : ℚ) := by
  have hD' : (D : ℚ) ≠ 0 := by positivity
  have h := Int.mul_ediv_add_emod n (D : ℤ)
  have hq : (D : ℚ) * ((n / (D : ℤ) : ℤ) : ℚ) + ((n % (D : ℤ) : ℤ) : ℚ) = (n : ℚ) := by
    exact_mod_cast h
  field_simp [hD']
  linarith

private theorem intCeilDiv_cast_rat (n : ℤ) {D : ℕ} (hD : 0 < D) :
    ((intCeilDiv n (D : ℤ) : ℤ) : ℚ) =
      ((n : ℚ) + ((((-n) % (D : ℤ) : ℤ) : ℚ))) / (D : ℚ) := by
  unfold intCeilDiv
  rw [Int.cast_neg, int_ediv_cast_rat (-n) hD]
  push_cast
  ring

private theorem sum_ray_interval_quasiPoly {k : ℕ} (q : QuasiPolynomial k) (v : Fin k → ℤ)
    (a₁ a₂ : Fin k → ℤ) (c₁ c₂ : ℤ) {D₁ D₂ : ℕ} (hD₁ : 0 < D₁) (hD₂ : 0 < D₂) :
    PiecewiseQuasiPolynomial.IsPiecewiseQuasiPolynomial (fun b : Fin k → ℤ ↦
      ∑ m ∈ Finset.Icc (intCeilDiv ((∑ i, a₁ i * b i) + c₁) D₁)
          (((∑ i, a₂ i * b i) + c₂) / D₂), q.eval (b - m • v)) := by
  obtain ⟨M, hM, hML⟩ := q.exists_pos_period
  let P : ℕ := M * D₁ * D₂
  have hP : 0 < P := by positivity
  have hMP : M ∣ P := ⟨D₁ * D₂, by ring⟩
  suffices hpart : ∀ r : Fin M, PiecewiseQuasiPolynomial.IsPiecewiseQuasiPolynomial
      (fun b : Fin k → ℤ ↦
        ∑ m ∈ (Finset.Icc (intCeilDiv ((∑ i, a₁ i * b i) + c₁) D₁)
            (((∑ i, a₂ i * b i) + c₂) / D₂)).filter (fun m ↦ m % (M : ℤ) = (r.1 : ℤ)),
          q.eval (b - m • v)) by
    have htot := PiecewiseQuasiPolynomial.isPiecewiseQuasiPolynomial_sum
      (Finset.univ : Finset (Fin M)) _ (fun r _ ↦ hpart r)
    rcases htot with ⟨f, hf⟩
    refine ⟨f, fun b ↦ ?_⟩
    rw [hf b]
    dsimp only
    have hfib := Finset.sum_fiberwise_of_maps_to
      (s := Finset.Icc (intCeilDiv ((∑ i, a₁ i * b i) + c₁) D₁)
        (((∑ i, a₂ i * b i) + c₂) / D₂))
      (t := (Finset.univ : Finset (Fin M)))
      (g := fun m : ℤ ↦ (⟨(m % (M : ℤ)).toNat, by
        have := Int.emod_lt_of_pos m (by positivity : (0 : ℤ) < M)
        have := Int.emod_nonneg m (by positivity : (M : ℤ) ≠ 0)
        omega⟩ : Fin M))
      (fun _ _ ↦ Finset.mem_univ _)
      (f := fun m ↦ q.eval (b - m • v))
    rw [← hfib]
    refine Finset.sum_congr rfl fun r _ ↦ ?_
    congr 1
    ext m
    simp only [Finset.mem_filter, Fin.ext_iff]
    have h0 := Int.emod_nonneg m (by positivity : (M : ℤ) ≠ 0)
    constructor <;> rintro ⟨hm, hrm⟩ <;> exact ⟨hm, by omega⟩
  intro r
  let L₁ : ℕ := M * D₁
  let L₂ : ℕ := M * D₂
  have hL₁ : 0 < L₁ := by positivity
  have hL₂ : 0 < L₂ := by positivity
  let num₁ (b : Fin k → ℤ) : ℤ := (∑ i, a₁ i * b i) + (c₁ - (D₁ : ℤ) * (r.1 : ℤ))
  let num₂ (b : Fin k → ℤ) : ℤ := (∑ i, a₂ i * b i) + (c₂ - (D₂ : ℤ) * (r.1 : ℤ))
  have hrew : ∀ b : Fin k → ℤ,
      (∑ m ∈ (Finset.Icc (intCeilDiv ((∑ i, a₁ i * b i) + c₁) D₁)
          (((∑ i, a₂ i * b i) + c₂) / D₂)).filter (fun m ↦ m % (M : ℤ) = (r.1 : ℤ)),
        q.eval (b - m • v)) =
      ∑ t ∈ Finset.Icc (intCeilDiv (num₁ b) L₁) (num₂ b / L₂),
        q.eval (b - ((M : ℤ) * t + (r.1 : ℤ)) • v) := by
    intro b
    refine Finset.sum_bij (fun m _ ↦ m / (M : ℤ)) ?_ ?_ ?_ ?_
    · intro m hm
      simp only [Finset.mem_filter, Finset.mem_Icc] at hm
      rcases hm with ⟨⟨hlo, hhi⟩, hmod⟩
      have hm_eq : m = (M : ℤ) * (m / (M : ℤ)) + (r.1 : ℤ) := by
        have := Int.mul_ediv_add_emod m (M : ℤ); omega
      rw [intCeilDiv_le_iff (by positivity : (0 : ℤ) < D₁)] at hlo
      rw [le_intFloorDiv_iff (by positivity : (0 : ℤ) < D₂)] at hhi
      simp only [Finset.mem_Icc]
      rw [intCeilDiv_le_iff (by positivity : (0 : ℤ) < L₁),
        le_intFloorDiv_iff (by positivity : (0 : ℤ) < L₂)]
      simp only [num₁, num₂, L₁, L₂, Nat.cast_mul]
      constructor <;> nlinarith
    · intro m₁ hm₁ m₂ hm₂ heq
      simp only [Finset.mem_filter] at hm₁ hm₂
      have h1 := Int.mul_ediv_add_emod m₁ (M : ℤ)
      have h2 := Int.mul_ediv_add_emod m₂ (M : ℤ)
      rw [hm₁.2] at h1
      rw [hm₂.2] at h2
      rw [heq] at h1
      linarith
    · intro t ht
      simp only [Finset.mem_Icc] at ht
      rcases ht with ⟨hlo, hhi⟩
      rw [intCeilDiv_le_iff (by positivity : (0 : ℤ) < L₁)] at hlo
      rw [le_intFloorDiv_iff (by positivity : (0 : ℤ) < L₂)] at hhi
      refine ⟨(M : ℤ) * t + (r.1 : ℤ), ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_Icc]
        rw [intCeilDiv_le_iff (by positivity : (0 : ℤ) < D₁),
          le_intFloorDiv_iff (by positivity : (0 : ℤ) < D₂)]
        simp only [num₁, num₂, L₁, L₂, Nat.cast_mul] at hlo hhi
        refine ⟨⟨by nlinarith, by nlinarith⟩, ?_⟩
        rw [Int.mul_add_emod_self_left, Int.emod_eq_of_lt (by omega) (by omega)]
      · rw [Int.mul_add_ediv_left _ _ (by positivity : (M : ℤ) ≠ 0),
          Int.ediv_eq_zero_of_lt (by omega) (by omega), add_zero]
    · intro m hm
      simp only [Finset.mem_filter] at hm
      have h1 := Int.mul_ediv_add_emod m (M : ℤ)
      have : (M : ℤ) * (m / (M : ℤ)) + (r.1 : ℤ) = m := by omega
      rw [this]
  let coeffDiff : Fin k → ℤ := fun i ↦ (D₂ : ℤ) * a₁ i - (D₁ : ℤ) * a₂ i
  let baseConst : ℤ := (L₁ : ℤ) * (c₂ - (D₂ : ℤ) * (r.1 : ℤ)) -
    (L₂ : ℤ) * (c₁ - (D₁ : ℤ) * (r.1 : ℤ))
  let R : ℕ := 2 * L₁ * L₂ + 2
  let threshIneqs : List ((Fin k → ℤ) × ℤ) :=
    (List.range (2 * R + 1)).map fun (j : ℕ) ↦
      ((M : ℤ) • coeffDiff, baseConst - (R : ℤ) + (j : ℤ))
  let chambers := PiecewiseQuasiPolynomial.splitPartitionList [PolyhedralChamber.univ k] threshIneqs
  have hcov := PiecewiseQuasiPolynomial.splitPartitionList_cover
    (chambers := [PolyhedralChamber.univ k])
    (fun y ↦ ⟨PolyhedralChamber.univ k, by simp, by simp⟩) threshIneqs
  have hdisj := PiecewiseQuasiPolynomial.splitPartitionList_disjoint
    (chambers := [PolyhedralChamber.univ k]) (by simp) threshIneqs
  have hdec := PiecewiseQuasiPolynomial.splitPartitionList_decides
    [PolyhedralChamber.univ k] threshIneqs
  have : NeZero P := ⟨hP.ne'⟩
  let zRep (z : Fin k → ZMod P) : Fin k → ℤ := fun i ↦ (ZMod.val (z i) : ℤ)
  have hzRep_mod : ∀ (b : Fin k → ℤ) (i : Fin k),
      (P : ℤ) ∣ (b i - zRep (fun i ↦ (b i : ZMod P)) i) := by
    intro b i
    have h0 : ((b i - zRep (fun i ↦ (b i : ZMod P)) i : ℤ) : ZMod P) = 0 := by
      simp [zRep]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ P).1 h0
  have hnum₁_mod : ∀ (b : Fin k → ℤ),
      ((-num₁ b) % (L₁ : ℤ)) = ((-num₁ (zRep (fun i ↦ (b i : ZMod P)))) % (L₁ : ℤ)) := by
    intro b
    have hdiv : (L₁ : ℤ) ∣ (-num₁ b) - (-num₁ (zRep (fun i ↦ (b i : ZMod P)))) := by
      have hPdiv : (L₁ : ℤ) ∣ (P : ℤ) := ⟨D₂, by simp [P, L₁]⟩
      have hdiff : (-num₁ b) - (-num₁ (zRep (fun i ↦ (b i : ZMod P)))) =
          -(∑ i, a₁ i * (b i - zRep (fun i ↦ (b i : ZMod P)) i)) := by
        have hsub : (∑ i, a₁ i * b i) - (∑ i, a₁ i * zRep (fun i ↦ (b i : ZMod P)) i) =
            ∑ i, a₁ i * (b i - zRep (fun i ↦ (b i : ZMod P)) i) := by
          rw [← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun i _ ↦ (mul_sub _ _ _).symm
        simp only [num₁]; linarith
      rw [hdiff]
      exact dvd_neg.2 (Finset.dvd_sum fun i _ ↦ dvd_mul_of_dvd_right
        (dvd_trans hPdiv (hzRep_mod b i)) _)
    exact (Int.modEq_iff_dvd.2 (by simpa using hdiv)).symm
  have hnum₂_mod : ∀ (b : Fin k → ℤ),
      (num₂ b % (L₂ : ℤ)) = (num₂ (zRep (fun i ↦ (b i : ZMod P))) % (L₂ : ℤ)) := by
    intro b
    have hdiv : (L₂ : ℤ) ∣ num₂ b - num₂ (zRep (fun i ↦ (b i : ZMod P))) := by
      have hPdiv : (L₂ : ℤ) ∣ (P : ℤ) := ⟨D₁, by simp [P, L₂]; ring⟩
      have hdiff : num₂ b - num₂ (zRep (fun i ↦ (b i : ZMod P))) =
          ∑ i, a₂ i * (b i - zRep (fun i ↦ (b i : ZMod P)) i) := by
        have hsub : (∑ i, a₂ i * b i) - (∑ i, a₂ i * zRep (fun i ↦ (b i : ZMod P)) i) =
            ∑ i, a₂ i * (b i - zRep (fun i ↦ (b i : ZMod P)) i) := by
          rw [← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun i _ ↦ (mul_sub _ _ _).symm
        simp only [num₂]; linarith
      rw [hdiff]
      exact Finset.dvd_sum fun i _ ↦ dvd_mul_of_dvd_right (dvd_trans hPdiv (hzRep_mod b i)) _
    exact (Int.modEq_iff_dvd.2 (by simpa using hdiv)).symm
  classical
  let mkPoly (C : PolyhedralChamber k) (z : Fin k → ZMod P) : MvPolynomial (Fin k) ℚ :=
    let rem₁ : ℤ := (-num₁ (zRep z)) % (L₁ : ℤ)
    let rem₂ : ℤ := num₂ (zRep z) % (L₂ : ℤ)
    let thresh : ℤ := baseConst - (L₂ : ℤ) * rem₁ - (L₁ : ℤ) * rem₂
    if ∃ b ∈ C.carrier, (∑ i, ((M : ℤ) • coeffDiff) i * b i) ≤ thresh then
      let qPoly := q.poly (QuotientAddGroup.mk (zRep z - (r.1 : ℤ) • v))
      let Q := (exists_mvPoly_sum_Icc_ray qPoly ((M : ℤ) • v)).choose
      let loPoly : MvPolynomial (Fin k) ℚ :=
        MvPolynomial.C ((L₁ : ℚ)⁻¹) *
          ((∑ i, MvPolynomial.C (a₁ i : ℚ) * MvPolynomial.X i) +
            MvPolynomial.C ((c₁ - (D₁ : ℤ) * (r.1 : ℤ) + rem₁ : ℤ) : ℚ))
      let hiPoly : MvPolynomial (Fin k) ℚ :=
        MvPolynomial.C ((L₂ : ℚ)⁻¹) *
          ((∑ i, MvPolynomial.C (a₂ i : ℚ) * MvPolynomial.X i) +
            MvPolynomial.C ((c₂ - (D₂ : ℤ) * (r.1 : ℤ) - rem₂ : ℤ) : ℚ))
      let subMap : Fin (k + 2) → MvPolynomial (Fin k) ℚ := fun j ↦
        if h : j.1 < k then
          MvPolynomial.X ⟨j.1, h⟩ - MvPolynomial.C (((r.1 : ℤ) * v ⟨j.1, h⟩ : ℤ) : ℚ)
        else if j.1 = k then loPoly else hiPoly
      MvPolynomial.aeval subMap Q
    else 0
  let f : PiecewiseQuasiPolynomial k :=
    { pieces := chambers.map fun C ↦ (C, QuasiPolynomial.ofPeriod hP (mkPoly C))
      cover := fun b ↦ by
        obtain ⟨C, hC, hb⟩ := hcov b
        exact ⟨(C, QuasiPolynomial.ofPeriod hP (mkPoly C)), List.mem_map_of_mem hC, hb⟩
      disjoint := List.pairwise_map.2 (hdisj.imp fun h ↦ h) }
  refine ⟨f, fun b ↦ ?_⟩
  dsimp only
  rw [hrew b]
  obtain ⟨C, hC, hb⟩ := hcov b
  rw [PiecewiseQuasiPolynomial.eval_eq_of_mem f
      (p := (C, QuasiPolynomial.ofPeriod hP (mkPoly C))) (List.mem_map_of_mem hC) hb,
    QuasiPolynomial.eval_ofPeriod]
  let z : Fin k → ZMod P := fun i ↦ (b i : ZMod P)
  let rem₁ : ℤ := (-num₁ (zRep z)) % (L₁ : ℤ)
  let rem₂ : ℤ := num₂ (zRep z) % (L₂ : ℤ)
  let thresh : ℤ := baseConst - (L₂ : ℤ) * rem₁ - (L₁ : ℤ) * rem₂
  have hrem₁ : (-num₁ b) % (L₁ : ℤ) = rem₁ := hnum₁_mod b
  have hrem₂ : num₂ b % (L₂ : ℤ) = rem₂ := hnum₂_mod b
  have hrem₁_bd : 0 ≤ rem₁ ∧ rem₁ < (L₁ : ℤ) :=
    ⟨Int.emod_nonneg _ (by positivity), Int.emod_lt_of_pos _ (by positivity)⟩
  have hrem₂_bd : 0 ≤ rem₂ ∧ rem₂ < (L₂ : ℤ) :=
    ⟨Int.emod_nonneg _ (by positivity), Int.emod_lt_of_pos _ (by positivity)⟩
  have hthresh_mem : ((M : ℤ) • coeffDiff, thresh) ∈ threshIneqs := by
    simp only [threshIneqs, List.mem_map]
    have hR_eq : (R : ℤ) = 2 * (L₁ : ℤ) * (L₂ : ℤ) + 2 := by
      simp only [R, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    have hbd1 : (L₂ : ℤ) * rem₁ + (L₁ : ℤ) * rem₂ ≤ 2 * (L₁ : ℤ) * (L₂ : ℤ) := by nlinarith
    have hbd2 : 0 ≤ (L₂ : ℤ) * rem₁ + (L₁ : ℤ) * rem₂ := by nlinarith
    refine ⟨((R : ℤ) - (L₂ : ℤ) * rem₁ - (L₁ : ℤ) * rem₂).toNat, ?_, ?_⟩
    · rw [List.mem_range]; omega
    · congr 1
      have hcast : (((R : ℤ) - (L₂ : ℤ) * rem₁ - (L₁ : ℤ) * rem₂).toNat : ℤ) =
          (R : ℤ) - (L₂ : ℤ) * rem₁ - (L₁ : ℤ) * rem₂ := by omega
      rw [hcast]; linarith
  have hlo_hi_iff : intCeilDiv (num₁ b) L₁ ≤ num₂ b / L₂ ↔
      (∑ i, ((M : ℤ) • coeffDiff) i * b i) ≤ thresh := by
    have h1 := Int.mul_ediv_add_emod (-num₁ b) (L₁ : ℤ)
    have h2 := Int.mul_ediv_add_emod (num₂ b) (L₂ : ℤ)
    have hsum_eq : (∑ i, ((M : ℤ) • coeffDiff) i * b i) =
        (L₂ : ℤ) * (∑ i, a₁ i * b i) - (L₁ : ℤ) * (∑ i, a₂ i * b i) := by
      have hterm : ∀ i : Fin k, ((M : ℤ) • coeffDiff) i * b i =
          (L₂ : ℤ) * (a₁ i * b i) - (L₁ : ℤ) * (a₂ i * b i) := by
        intro i
        rw [Pi.smul_apply, zsmul_eq_mul, Int.cast_id]
        simp only [coeffDiff, L₁, L₂, Nat.cast_mul]; ring
      simp_rw [hterm]
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    unfold intCeilDiv
    have hmul : -((-num₁ b) / (L₁ : ℤ)) ≤ num₂ b / (L₂ : ℤ) ↔
        (L₁ : ℤ) * (L₂ : ℤ) * (-((-num₁ b) / (L₁ : ℤ))) ≤
          (L₁ : ℤ) * (L₂ : ℤ) * (num₂ b / (L₂ : ℤ)) :=
      ⟨fun h ↦ mul_le_mul_of_nonneg_left h (by positivity),
        fun h ↦ le_of_mul_le_mul_left h (by positivity)⟩
    rw [hmul]
    have hlhs : (L₁ : ℤ) * (L₂ : ℤ) * (-((-num₁ b) / (L₁ : ℤ))) =
        (L₂ : ℤ) * (num₁ b + rem₁) := by rw [← hrem₁]; nlinarith
    have hrhs : (L₁ : ℤ) * (L₂ : ℤ) * (num₂ b / (L₂ : ℤ)) =
        (L₁ : ℤ) * (num₂ b - rem₂) := by rw [← hrem₂]; nlinarith
    rw [hlhs, hrhs, hsum_eq]
    simp only [num₁, num₂, thresh, baseConst]
    constructor <;> intro h <;> linarith
  have hdec_b : (∃ b' ∈ C.carrier, (∑ i, ((M : ℤ) • coeffDiff) i * b' i) ≤ thresh) ↔
      (∑ i, ((M : ℤ) • coeffDiff) i * b i) ≤ thresh := by
    rcases hdec C hC ((M : ℤ) • coeffDiff, thresh) hthresh_mem with hall | hnone
    · exact ⟨fun _ ↦ hall b hb, fun _ ↦ ⟨b, hb, hall b hb⟩⟩
    · exact ⟨fun ⟨b', hb', hle⟩ ↦ (hnone b' hb' hle).elim, fun hle ↦ (hnone b hb hle).elim⟩
  change MvPolynomial.eval (fun i ↦ (b i : ℚ)) (mkPoly C z) = _
  simp only [mkPoly]
  split_ifs with hex
  · have hle_z : intCeilDiv (num₁ b) L₁ ≤ num₂ b / L₂ := hlo_hi_iff.2 (hdec_b.1 hex)
    let Q := (exists_mvPoly_sum_Icc_ray
      (q.poly (QuotientAddGroup.mk (zRep z - (r.1 : ℤ) • v))) ((M : ℤ) • v)).choose
    have hQspec := (exists_mvPoly_sum_Icc_ray
      (q.poly (QuotientAddGroup.mk (zRep z - (r.1 : ℤ) • v))) ((M : ℤ) • v)).choose_spec
    have heval_aeval : MvPolynomial.eval (fun i ↦ (b i : ℚ))
        (MvPolynomial.aeval (fun j : Fin (k + 2) ↦
          if h : j.1 < k then
            MvPolynomial.X ⟨j.1, h⟩ - MvPolynomial.C (((r.1 : ℤ) * v ⟨j.1, h⟩ : ℤ) : ℚ)
          else if j.1 = k then
            MvPolynomial.C ((L₁ : ℚ)⁻¹) *
              ((∑ i, MvPolynomial.C (a₁ i : ℚ) * MvPolynomial.X i) +
                MvPolynomial.C ((c₁ - (D₁ : ℤ) * (r.1 : ℤ) + rem₁ : ℤ) : ℚ))
          else
            MvPolynomial.C ((L₂ : ℚ)⁻¹) *
              ((∑ i, MvPolynomial.C (a₂ i : ℚ) * MvPolynomial.X i) +
                MvPolynomial.C ((c₂ - (D₂ : ℤ) * (r.1 : ℤ) - rem₂ : ℤ) : ℚ))) Q) =
        MvPolynomial.eval
          (fun j : Fin (k + 2) ↦
            if h : j.1 < k then (((b - (r.1 : ℤ) • v) ⟨j.1, h⟩ : ℤ) : ℚ)
            else if j.1 = k then (intCeilDiv (num₁ b) L₁ : ℚ)
            else ((num₂ b / L₂ : ℤ) : ℚ)) Q := by
      change (MvPolynomial.aeval (fun i ↦ (b i : ℚ))).comp (MvPolynomial.aeval _) Q =
        MvPolynomial.aeval _ Q
      congr 1
      apply MvPolynomial.algHom_ext
      intro j
      simp only [AlgHom.comp_apply, MvPolynomial.aeval_X]
      split_ifs with hj hjk
      · simp
      · simp only [map_mul, map_add, map_sum, MvPolynomial.aeval_C, MvPolynomial.aeval_X,
          Algebra.algebraMap_self, RingHom.id_apply]
        rw [intCeilDiv_cast_rat (num₁ b) hL₁, hrem₁]
        simp only [num₁, Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_sum]
        ring
      · simp only [map_mul, map_add, map_sum, MvPolynomial.aeval_C, MvPolynomial.aeval_X,
          Algebra.algebraMap_self, RingHom.id_apply]
        rw [int_ediv_cast_rat (num₂ b) hL₂, hrem₂]
        simp only [num₂, Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_sum]
        ring
    rw [heval_aeval, ← hQspec (b - (r.1 : ℤ) • v) (intCeilDiv (num₁ b) L₁) (num₂ b / L₂)
      (by omega)]
    refine Finset.sum_congr rfl fun t _ ↦ ?_
    have hcoset : QuotientAddGroup.mk (s := q.sublattice)
        (b - ((M : ℤ) * t + (r.1 : ℤ)) • v) =
        QuotientAddGroup.mk (s := q.sublattice) (zRep z - (r.1 : ℤ) • v) := by
      rw [QuotientAddGroup.eq]
      apply hML
      rw [QuasiPolynomial.mem_mulSublattice_iff]
      intro i
      have hbi : (M : ℤ) ∣ b i - zRep z i :=
        dvd_trans (Int.natCast_dvd_natCast.2 hMP) (hzRep_mod b i)
      have hgoal : -(b - ((M : ℤ) * t + (r.1 : ℤ)) • v) i + (zRep z - (r.1 : ℤ) • v) i =
          -(b i - zRep z i) + (M : ℤ) * (t * v i) := by
        rw [Pi.sub_apply, Pi.sub_apply, Pi.smul_apply, Pi.smul_apply, zsmul_eq_mul, zsmul_eq_mul,
          Int.cast_id, Int.cast_id]; ring
      change (M : ℤ) ∣ -(b - ((M : ℤ) * t + (r.1 : ℤ)) • v) i + (zRep z - (r.1 : ℤ) • v) i
      rw [hgoal]
      exact dvd_add (dvd_neg.2 hbi) (dvd_mul_right _ _)
    simp only [QuasiPolynomial.eval, hcoset]
    refine congrArg (fun env ↦ MvPolynomial.eval env _) (funext fun i ↦ ?_)
    rw [Pi.sub_apply, Pi.sub_apply, Pi.smul_apply, Pi.smul_apply, Pi.smul_apply,
      zsmul_eq_mul, zsmul_eq_mul, zsmul_eq_mul, Int.cast_id, Int.cast_id, Int.cast_id]
    push_cast
    ring
  · have hgt : num₂ b / L₂ < intCeilDiv (num₁ b) L₁ := by
      have := mt hdec_b.2 hex
      have := mt hlo_hi_iff.1 this
      omega
    rw [Finset.Icc_eq_empty (not_le.2 hgt), Finset.sum_empty, map_zero]

private theorem sum_ray_chamber_quasiPoly {k : ℕ} (C : PolyhedralChamber k)
    (q : QuasiPolynomial k) (v : Fin k → ℤ)
    (ℓ : (Fin k → ℤ) →+ ℤ) (hℓv : 0 < ℓ v) :
    PiecewiseQuasiPolynomial.IsPiecewiseQuasiPolynomial (fun b : Fin k → ℤ ↦
      ∑ m ∈ (Finset.Icc (0 : ℤ) (ℓ b / ℓ v)).filter (fun m ↦ b - m • v ∈ C.carrier),
        q.eval (b - m • v)) := by
  let lowerBounds : List ((Fin k → ℤ) × ℤ × ℕ) :=
    ((0, 0, 1) :: C.ineqs.filterMap fun p ↦
      let av := ∑ i, p.1 i * v i
      if 0 < av then some (p.1, -p.2, av.toNat) else none)
  let ℓvec : Fin k → ℤ := fun i ↦ ℓ (Pi.single i 1)
  have hℓ_eq : ∀ y : Fin k → ℤ, ℓ y = ∑ i, ℓvec i * y i := by
    intro y
    have hy : y = ∑ i : Fin k, y i • Pi.single i (1 : ℤ) := by
      ext m; simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [hy]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ by rw [map_zsmul, zsmul_eq_mul, Int.cast_id, mul_comm]
  let upperBounds : List ((Fin k → ℤ) × ℤ × ℕ) :=
    ((ℓvec, 0, (ℓ v).toNat) :: C.ineqs.filterMap fun p ↦
      let av := ∑ i, p.1 i * v i
      if av < 0 then some (-p.1, p.2, (-av).toNat) else none)
  let zeroBounds : List ((Fin k → ℤ) × ℤ) :=
    C.ineqs.filterMap fun p ↦ if (∑ i, p.1 i * v i) = 0 then some p else none
  have hLpos : ∀ lb ∈ lowerBounds, 0 < lb.2.2 := by
    intro lb hlb
    simp only [lowerBounds, List.mem_cons, List.mem_filterMap] at hlb
    rcases hlb with rfl | ⟨p, _, hp⟩
    · simp
    · split_ifs at hp with h
      · injection hp with hp'; subst hp'; dsimp only; omega
  have hUpos : ∀ ub ∈ upperBounds, 0 < ub.2.2 := by
    intro ub hub
    simp only [upperBounds, List.mem_cons, List.mem_filterMap] at hub
    rcases hub with rfl | ⟨p, _, hp⟩
    · dsimp only; omega
    · split_ifs at hp with h
      · injection hp with hp'; subst hp'; dsimp only; omega
  have hmem_iff : ∀ (b : Fin k → ℤ) (m : ℤ),
      (m ∈ (Finset.Icc (0 : ℤ) (ℓ b / ℓ v)).filter (fun m ↦ b - m • v ∈ C.carrier)) ↔
      (∀ zb ∈ zeroBounds, (∑ i, zb.1 i * b i) ≤ zb.2) ∧
      (∀ lb ∈ lowerBounds, intCeilDiv ((∑ i, lb.1 i * b i) + lb.2.1) lb.2.2 ≤ m) ∧
      (∀ ub ∈ upperBounds, m ≤ ((∑ i, ub.1 i * b i) + ub.2.1) / ub.2.2) := by
    intro b m
    simp only [Finset.mem_filter, Finset.mem_Icc, PolyhedralChamber.mem_carrier_iff]
    have hstep : ∀ p : (Fin k → ℤ) × ℤ,
        (∑ i, p.1 i * (b - m • v) i) = (∑ i, p.1 i * b i) - m * (∑ i, p.1 i * v i) := by
      intro p
      have hterm : ∀ i : Fin k, p.1 i * (b - m • v) i = p.1 i * b i - m * (p.1 i * v i) := by
        intro i
        rw [Pi.sub_apply, Pi.smul_apply, zsmul_eq_mul, Int.cast_id]
        ring
      simp_rw [hterm]
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    constructor
    · rintro ⟨⟨hm0, hmhi⟩, hC⟩
      refine ⟨?_, ?_, ?_⟩
      · intro zb hzb
        simp only [zeroBounds, List.mem_filterMap] at hzb
        obtain ⟨p, hp, hpeq⟩ := hzb
        split_ifs at hpeq with h0
        · injection hpeq with hp'; subst hp'
          have := hC p hp; rw [hstep, h0, mul_zero, sub_zero] at this; exact this
      · intro lb hlb
        simp only [lowerBounds, List.mem_cons, List.mem_filterMap] at hlb
        rcases hlb with rfl | ⟨p, hp, hpeq⟩
        · dsimp only
          rw [Nat.cast_one, intCeilDiv_le_iff (by omega)]; simpa using hm0
        · split_ifs at hpeq with hpos
          · injection hpeq with hp'; subst hp'; dsimp only
            rw [intCeilDiv_le_iff (by omega)]
            have := hC p hp; rw [hstep] at this
            have hcast : ((∑ i, p.1 i * v i).toNat : ℤ) = ∑ i, p.1 i * v i := by omega
            rw [hcast]; linarith
      · intro ub hub
        simp only [upperBounds, List.mem_cons, List.mem_filterMap] at hub
        rcases hub with rfl | ⟨p, hp, hpeq⟩
        · dsimp only
          rw [le_intFloorDiv_iff (by omega)]
          have hcast : ((ℓ v).toNat : ℤ) = ℓ v := by omega
          rw [hcast, add_zero, ← hℓ_eq b]
          exact (le_intFloorDiv_iff hℓv).1 hmhi
        · split_ifs at hpeq with hneg
          · injection hpeq with hp'; subst hp'; dsimp only
            rw [le_intFloorDiv_iff (by omega)]
            have := hC p hp; rw [hstep] at this
            have hcast : ((-(∑ i, p.1 i * v i)).toNat : ℤ) = -(∑ i, p.1 i * v i) := by omega
            have hns : (∑ i, (-p.1) i * b i) = -(∑ i, p.1 i * b i) := by
              simp [Finset.sum_neg_distrib]
            rw [hcast, hns]; linarith
    · rintro ⟨hzb, hlb, hub⟩
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · have h0 := hlb (0, 0, 1) (by simp [lowerBounds])
        dsimp only at h0
        rw [Nat.cast_one, intCeilDiv_le_iff (by omega)] at h0; simpa using h0
      · have hhi := hub (ℓvec, 0, (ℓ v).toNat) (by simp [upperBounds])
        dsimp only at hhi
        rw [le_intFloorDiv_iff (by omega)] at hhi
        rw [le_intFloorDiv_iff hℓv, hℓ_eq b]
        have hcast : ((ℓ v).toNat : ℤ) = ℓ v := by omega
        rw [hcast, add_zero] at hhi; exact hhi
      · intro p hp
        rw [hstep]
        rcases lt_trichotomy (∑ i, p.1 i * v i) 0 with hneg | h0 | hpos
        · have hubp := hub (-p.1, p.2, (-(∑ i, p.1 i * v i)).toNat)
            (List.mem_cons_of_mem _ (List.mem_filterMap.2 ⟨p, hp, by simp [hneg]⟩))
          dsimp only at hubp
          rw [le_intFloorDiv_iff (by omega)] at hubp
          have hcast : ((-(∑ i, p.1 i * v i)).toNat : ℤ) = -(∑ i, p.1 i * v i) := by omega
          have hns : (∑ i, (-p.1) i * b i) = -(∑ i, p.1 i * b i) := by
            simp [Finset.sum_neg_distrib]
          rw [hcast, hns] at hubp; linarith
        · have hzbp := hzb p (List.mem_filterMap.2 ⟨p, hp, by simp [h0]⟩)
          rw [h0, mul_zero, sub_zero]; exact hzbp
        · have hlbp := hlb (p.1, -p.2, (∑ i, p.1 i * v i).toNat)
            (List.mem_cons_of_mem _ (List.mem_filterMap.2 ⟨p, hp, by simp [hpos]⟩))
          dsimp only at hlbp
          rw [intCeilDiv_le_iff (by omega)] at hlbp
          have hcast : ((∑ i, p.1 i * v i).toNat : ℤ) = ∑ i, p.1 i * v i := by omega
          rw [hcast] at hlbp; linarith
  let M_all : ℕ := (lowerBounds.map fun lb ↦ lb.2.2).prod * (upperBounds.map fun ub ↦ ub.2.2).prod
  have hM_all : 0 < M_all := by
    refine Nat.mul_pos ?_ ?_
    · exact List.prod_pos (fun d hd ↦ by
        obtain ⟨lb, hlb, rfl⟩ := List.mem_map.1 hd; exact hLpos lb hlb)
    · exact List.prod_pos (fun d hd ↦ by
        obtain ⟨ub, hub, rfl⟩ := List.mem_map.1 hd; exact hUpos ub hub)
  let pairIneqs (l : List ((Fin k → ℤ) × ℤ × ℕ)) : List ((Fin k → ℤ) × ℤ) :=
    l.flatMap fun p₁ ↦ l.flatMap fun p₂ ↦
      let D₁ : ℕ := p₁.2.2
      let D₂ : ℕ := p₂.2.2
      let R : ℕ := 2 * D₁ * D₂ + 2
      let base : ℤ := (D₁ : ℤ) * p₂.2.1 - (D₂ : ℤ) * p₁.2.1
      let a : Fin k → ℤ := fun i ↦ (D₂ : ℤ) * p₁.1 i - (D₁ : ℤ) * p₂.1 i
      (List.range (2 * R + 1)).map fun (j : ℕ) ↦ (a, base - (R : ℤ) + (j : ℤ))
  let allIneqs := zeroBounds ++ pairIneqs lowerBounds ++ pairIneqs upperBounds
  let chambers := PiecewiseQuasiPolynomial.splitPartitionList [PolyhedralChamber.univ k] allIneqs
  have hcov := PiecewiseQuasiPolynomial.splitPartitionList_cover
    (chambers := [PolyhedralChamber.univ k])
    (fun y ↦ ⟨PolyhedralChamber.univ k, by simp, by simp⟩) allIneqs
  have hdisj := PiecewiseQuasiPolynomial.splitPartitionList_disjoint
    (chambers := [PolyhedralChamber.univ k]) (by simp) allIneqs
  have hdec := PiecewiseQuasiPolynomial.splitPartitionList_decides
    [PolyhedralChamber.univ k] allIneqs
  have hpair_pq : ∀ lb ∈ lowerBounds, ∀ ub ∈ upperBounds,
      PiecewiseQuasiPolynomial.IsPiecewiseQuasiPolynomial (fun b : Fin k → ℤ ↦
        ∑ m ∈ Finset.Icc (intCeilDiv ((∑ i, lb.1 i * b i) + lb.2.1) lb.2.2)
          (((∑ i, ub.1 i * b i) + ub.2.1) / ub.2.2), q.eval (b - m • v)) :=
    fun lb hlb ub hub ↦ sum_ray_interval_quasiPoly q v lb.1 ub.1 lb.2.1 ub.2.1
      (hLpos lb hlb) (hUpos ub hub)
  have hdvd_L : ∀ lb ∈ lowerBounds, (lb.2.2 : ℤ) ∣ (M_all : ℤ) := fun lb hlb ↦
    Int.natCast_dvd_natCast.2 (dvd_mul_of_dvd_left (List.dvd_prod (List.mem_map_of_mem hlb)) _)
  have hdvd_U : ∀ ub ∈ upperBounds, (ub.2.2 : ℤ) ∣ (M_all : ℤ) := fun ub hub ↦
    Int.natCast_dvd_natCast.2 (dvd_mul_of_dvd_right (List.dvd_prod (List.mem_map_of_mem hub)) _)
  have hlb_order_const : ∀ D ∈ chambers, ∀ b₁ ∈ D.carrier, ∀ b₂ ∈ D.carrier,
      (fun i ↦ (b₁ i : ZMod M_all)) = (fun i ↦ (b₂ i : ZMod M_all)) →
      ∀ lb₁ ∈ lowerBounds, ∀ lb₂ ∈ lowerBounds,
        (intCeilDiv ((∑ i, lb₁.1 i * b₁ i) + lb₁.2.1) lb₁.2.2 ≤
          intCeilDiv ((∑ i, lb₂.1 i * b₁ i) + lb₂.2.1) lb₂.2.2) ↔
        (intCeilDiv ((∑ i, lb₁.1 i * b₂ i) + lb₁.2.1) lb₁.2.2 ≤
          intCeilDiv ((∑ i, lb₂.1 i * b₂ i) + lb₂.2.1) lb₂.2.2) := by
    intro D hD b₁ hb₁ b₂ hb₂ hz lb₁ hlb₁ lb₂ hlb₂
    have hD₁ : 0 < lb₁.2.2 := hLpos lb₁ hlb₁
    have hD₂ : 0 < lb₂.2.2 := hLpos lb₂ hlb₂
    let n₁ (b : Fin k → ℤ) := (∑ i, lb₁.1 i * b i) + lb₁.2.1
    let n₂ (b : Fin k → ℤ) := (∑ i, lb₂.1 i * b i) + lb₂.2.1
    have hrem₁ : (-n₁ b₁) % (lb₁.2.2 : ℤ) = (-n₁ b₂) % (lb₁.2.2 : ℤ) := by
      have hdiv : (lb₁.2.2 : ℤ) ∣ (-n₁ b₁) - (-n₁ b₂) := by
        have hdiff : (-n₁ b₁) - (-n₁ b₂) = -(∑ i, lb₁.1 i * (b₁ i - b₂ i)) := by
          simp only [n₁, mul_sub, Finset.sum_sub_distrib]; linarith
        rw [hdiff]
        refine dvd_neg.2 (Finset.dvd_sum fun i _ ↦ dvd_mul_of_dvd_right
          (dvd_trans (hdvd_L lb₁ hlb₁) ((ZMod.intCast_zmod_eq_zero_iff_dvd _ M_all).1
            (by push_cast; exact sub_eq_zero.2 (congrFun hz i)))) _)
      exact (Int.modEq_iff_dvd.2 (by simpa using hdiv)).symm
    have hrem₂ : (-n₂ b₁) % (lb₂.2.2 : ℤ) = (-n₂ b₂) % (lb₂.2.2 : ℤ) := by
      have hdiv : (lb₂.2.2 : ℤ) ∣ (-n₂ b₁) - (-n₂ b₂) := by
        have hdiff : (-n₂ b₁) - (-n₂ b₂) = -(∑ i, lb₂.1 i * (b₁ i - b₂ i)) := by
          simp only [n₂, mul_sub, Finset.sum_sub_distrib]; linarith
        rw [hdiff]
        refine dvd_neg.2 (Finset.dvd_sum fun i _ ↦ dvd_mul_of_dvd_right
          (dvd_trans (hdvd_L lb₂ hlb₂) ((ZMod.intCast_zmod_eq_zero_iff_dvd _ M_all).1
            (by push_cast; exact sub_eq_zero.2 (congrFun hz i)))) _)
      exact (Int.modEq_iff_dvd.2 (by simpa using hdiv)).symm
    let r₁ := (-n₁ b₁) % (lb₁.2.2 : ℤ)
    let r₂ := (-n₂ b₁) % (lb₂.2.2 : ℤ)
    let a : Fin k → ℤ := fun i ↦ (lb₂.2.2 : ℤ) * lb₁.1 i - (lb₁.2.2 : ℤ) * lb₂.1 i
    let thresh : ℤ := (lb₁.2.2 : ℤ) * lb₂.2.1 - (lb₂.2.2 : ℤ) * lb₁.2.1 +
      (lb₁.2.2 : ℤ) * r₂ - (lb₂.2.2 : ℤ) * r₁
    have hchar : ∀ b, (-n₁ b) % (lb₁.2.2 : ℤ) = r₁ → (-n₂ b) % (lb₂.2.2 : ℤ) = r₂ →
        (intCeilDiv (n₁ b) lb₁.2.2 ≤ intCeilDiv (n₂ b) lb₂.2.2 ↔
          (∑ i, a i * b i) ≤ thresh) := by
      intro b hr₁ hr₂
      unfold intCeilDiv
      have hmul : -((-n₁ b) / (lb₁.2.2 : ℤ)) ≤ -((-n₂ b) / (lb₂.2.2 : ℤ)) ↔
          (lb₁.2.2 : ℤ) * (lb₂.2.2 : ℤ) * (-((-n₁ b) / (lb₁.2.2 : ℤ))) ≤
            (lb₁.2.2 : ℤ) * (lb₂.2.2 : ℤ) * (-((-n₂ b) / (lb₂.2.2 : ℤ))) :=
        ⟨fun h ↦ mul_le_mul_of_nonneg_left h (by positivity),
          fun h ↦ le_of_mul_le_mul_left h (by positivity)⟩
      rw [hmul]
      have h1 := Int.mul_ediv_add_emod (-n₁ b) (lb₁.2.2 : ℤ)
      have h2 := Int.mul_ediv_add_emod (-n₂ b) (lb₂.2.2 : ℤ)
      have hsum : (∑ i, a i * b i) =
          (lb₂.2.2 : ℤ) * (∑ i, lb₁.1 i * b i) - (lb₁.2.2 : ℤ) * (∑ i, lb₂.1 i * b i) := by
        simp only [a, sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum]
      rw [hsum]
      simp only [n₁, n₂, thresh] at hr₁ hr₂ h1 h2 ⊢
      constructor <;> intro h <;> nlinarith
    rw [hchar b₁ rfl rfl, hchar b₂ hrem₁.symm hrem₂.symm]
    have hmem_ineq : (a, thresh) ∈ allIneqs := by
      refine List.mem_append_left _ (List.mem_append_right _ ?_)
      refine List.mem_flatMap.2 ⟨lb₁, hlb₁, List.mem_flatMap.2 ⟨lb₂, hlb₂, ?_⟩⟩
      simp only [List.mem_map]
      let R := 2 * lb₁.2.2 * lb₂.2.2 + 2
      have hr₁_bd : 0 ≤ r₁ ∧ r₁ < (lb₁.2.2 : ℤ) :=
        ⟨Int.emod_nonneg _ (by positivity), Int.emod_lt_of_pos _ (by positivity)⟩
      have hr₂_bd : 0 ≤ r₂ ∧ r₂ < (lb₂.2.2 : ℤ) :=
        ⟨Int.emod_nonneg _ (by positivity), Int.emod_lt_of_pos _ (by positivity)⟩
      have hR_eq : (R : ℤ) = 2 * (lb₁.2.2 : ℤ) * (lb₂.2.2 : ℤ) + 2 := by
        simp only [R, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
      have hbd1 : -(2 * (lb₁.2.2 : ℤ) * (lb₂.2.2 : ℤ)) ≤
          (lb₁.2.2 : ℤ) * r₂ - (lb₂.2.2 : ℤ) * r₁ := by nlinarith
      have hbd2 : (lb₁.2.2 : ℤ) * r₂ - (lb₂.2.2 : ℤ) * r₁ ≤
          2 * (lb₁.2.2 : ℤ) * (lb₂.2.2 : ℤ) := by nlinarith
      refine ⟨((R : ℤ) + (lb₁.2.2 : ℤ) * r₂ - (lb₂.2.2 : ℤ) * r₁).toNat, ?_, ?_⟩
      · rw [List.mem_range]
        omega
      · congr 1
        have hcast : (((R : ℤ) + (lb₁.2.2 : ℤ) * r₂ - (lb₂.2.2 : ℤ) * r₁).toNat : ℤ) =
            (R : ℤ) + (lb₁.2.2 : ℤ) * r₂ - (lb₂.2.2 : ℤ) * r₁ := by omega
        rw [hcast]
        linarith
    rcases hdec D hD (a, thresh) hmem_ineq with hall | hnone
    · exact ⟨fun _ ↦ hall b₂ hb₂, fun _ ↦ hall b₁ hb₁⟩
    · exact ⟨fun h ↦ (hnone b₁ hb₁ h).elim, fun h ↦ (hnone b₂ hb₂ h).elim⟩
  have hub_order_const : ∀ D ∈ chambers, ∀ b₁ ∈ D.carrier, ∀ b₂ ∈ D.carrier,
      (fun i ↦ (b₁ i : ZMod M_all)) = (fun i ↦ (b₂ i : ZMod M_all)) →
      ∀ ub₁ ∈ upperBounds, ∀ ub₂ ∈ upperBounds,
        (((∑ i, ub₁.1 i * b₁ i) + ub₁.2.1) / ub₁.2.2 ≤
          ((∑ i, ub₂.1 i * b₁ i) + ub₂.2.1) / ub₂.2.2) ↔
        (((∑ i, ub₁.1 i * b₂ i) + ub₁.2.1) / ub₁.2.2 ≤
          ((∑ i, ub₂.1 i * b₂ i) + ub₂.2.1) / ub₂.2.2) := by
    intro D hD b₁ hb₁ b₂ hb₂ hz ub₁ hub₁ ub₂ hub₂
    have hD₁ : 0 < ub₁.2.2 := hUpos ub₁ hub₁
    have hD₂ : 0 < ub₂.2.2 := hUpos ub₂ hub₂
    let n₁ (b : Fin k → ℤ) := (∑ i, ub₁.1 i * b i) + ub₁.2.1
    let n₂ (b : Fin k → ℤ) := (∑ i, ub₂.1 i * b i) + ub₂.2.1
    have hrem₁ : n₁ b₁ % (ub₁.2.2 : ℤ) = n₁ b₂ % (ub₁.2.2 : ℤ) := by
      have hdiv : (ub₁.2.2 : ℤ) ∣ n₁ b₁ - n₁ b₂ := by
        have hdiff : n₁ b₁ - n₁ b₂ = ∑ i, ub₁.1 i * (b₁ i - b₂ i) := by
          simp only [n₁, mul_sub, Finset.sum_sub_distrib]; linarith
        rw [hdiff]
        refine Finset.dvd_sum fun i _ ↦ dvd_mul_of_dvd_right
          (dvd_trans (hdvd_U ub₁ hub₁) ((ZMod.intCast_zmod_eq_zero_iff_dvd _ M_all).1
            (by push_cast; exact sub_eq_zero.2 (congrFun hz i)))) _
      exact (Int.modEq_iff_dvd.2 (by simpa using hdiv)).symm
    have hrem₂ : n₂ b₁ % (ub₂.2.2 : ℤ) = n₂ b₂ % (ub₂.2.2 : ℤ) := by
      have hdiv : (ub₂.2.2 : ℤ) ∣ n₂ b₁ - n₂ b₂ := by
        have hdiff : n₂ b₁ - n₂ b₂ = ∑ i, ub₂.1 i * (b₁ i - b₂ i) := by
          simp only [n₂, mul_sub, Finset.sum_sub_distrib]; linarith
        rw [hdiff]
        refine Finset.dvd_sum fun i _ ↦ dvd_mul_of_dvd_right
          (dvd_trans (hdvd_U ub₂ hub₂) ((ZMod.intCast_zmod_eq_zero_iff_dvd _ M_all).1
            (by push_cast; exact sub_eq_zero.2 (congrFun hz i)))) _
      exact (Int.modEq_iff_dvd.2 (by simpa using hdiv)).symm
    let r₁ := n₁ b₁ % (ub₁.2.2 : ℤ)
    let r₂ := n₂ b₁ % (ub₂.2.2 : ℤ)
    let a : Fin k → ℤ := fun i ↦ (ub₂.2.2 : ℤ) * ub₁.1 i - (ub₁.2.2 : ℤ) * ub₂.1 i
    let thresh : ℤ := (ub₁.2.2 : ℤ) * ub₂.2.1 - (ub₂.2.2 : ℤ) * ub₁.2.1 +
      (ub₂.2.2 : ℤ) * r₁ - (ub₁.2.2 : ℤ) * r₂
    have hchar : ∀ b, n₁ b % (ub₁.2.2 : ℤ) = r₁ → n₂ b % (ub₂.2.2 : ℤ) = r₂ →
        (n₁ b / (ub₁.2.2 : ℤ) ≤ n₂ b / (ub₂.2.2 : ℤ) ↔ (∑ i, a i * b i) ≤ thresh) := by
      intro b hr₁ hr₂
      have hmul : n₁ b / (ub₁.2.2 : ℤ) ≤ n₂ b / (ub₂.2.2 : ℤ) ↔
          (ub₁.2.2 : ℤ) * (ub₂.2.2 : ℤ) * (n₁ b / (ub₁.2.2 : ℤ)) ≤
            (ub₁.2.2 : ℤ) * (ub₂.2.2 : ℤ) * (n₂ b / (ub₂.2.2 : ℤ)) :=
        ⟨fun h ↦ mul_le_mul_of_nonneg_left h (by positivity),
          fun h ↦ le_of_mul_le_mul_left h (by positivity)⟩
      rw [hmul]
      have h1 := Int.mul_ediv_add_emod (n₁ b) (ub₁.2.2 : ℤ)
      have h2 := Int.mul_ediv_add_emod (n₂ b) (ub₂.2.2 : ℤ)
      have hsum : (∑ i, a i * b i) =
          (ub₂.2.2 : ℤ) * (∑ i, ub₁.1 i * b i) - (ub₁.2.2 : ℤ) * (∑ i, ub₂.1 i * b i) := by
        simp only [a, sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum]
      rw [hsum]
      simp only [n₁, n₂, thresh] at hr₁ hr₂ h1 h2 ⊢
      constructor <;> intro h <;> nlinarith
    rw [hchar b₁ rfl rfl, hchar b₂ hrem₁.symm hrem₂.symm]
    have hmem_ineq : (a, thresh) ∈ allIneqs := by
      refine List.mem_append_right _ ?_
      refine List.mem_flatMap.2 ⟨ub₁, hub₁, List.mem_flatMap.2 ⟨ub₂, hub₂, ?_⟩⟩
      simp only [List.mem_map]
      let R := 2 * ub₁.2.2 * ub₂.2.2 + 2
      have hr₁_bd : 0 ≤ r₁ ∧ r₁ < (ub₁.2.2 : ℤ) :=
        ⟨Int.emod_nonneg _ (by positivity), Int.emod_lt_of_pos _ (by positivity)⟩
      have hr₂_bd : 0 ≤ r₂ ∧ r₂ < (ub₂.2.2 : ℤ) :=
        ⟨Int.emod_nonneg _ (by positivity), Int.emod_lt_of_pos _ (by positivity)⟩
      have hR_eq : (R : ℤ) = 2 * (ub₁.2.2 : ℤ) * (ub₂.2.2 : ℤ) + 2 := by
        simp only [R, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
      have hbd1 : -(2 * (ub₁.2.2 : ℤ) * (ub₂.2.2 : ℤ)) ≤
          (ub₂.2.2 : ℤ) * r₁ - (ub₁.2.2 : ℤ) * r₂ := by nlinarith
      have hbd2 : (ub₂.2.2 : ℤ) * r₁ - (ub₁.2.2 : ℤ) * r₂ ≤
          2 * (ub₁.2.2 : ℤ) * (ub₂.2.2 : ℤ) := by nlinarith
      refine ⟨((R : ℤ) + (ub₂.2.2 : ℤ) * r₁ - (ub₁.2.2 : ℤ) * r₂).toNat, ?_, ?_⟩
      · rw [List.mem_range]
        omega
      · congr 1
        have hcast : (((R : ℤ) + (ub₂.2.2 : ℤ) * r₁ - (ub₁.2.2 : ℤ) * r₂).toNat : ℤ) =
            (R : ℤ) + (ub₂.2.2 : ℤ) * r₁ - (ub₁.2.2 : ℤ) * r₂ := by omega
        rw [hcast]
        linarith
    rcases hdec D hD (a, thresh) hmem_ineq with hall | hnone
    · exact ⟨fun _ ↦ hall b₂ hb₂, fun _ ↦ hall b₁ hb₁⟩
    · exact ⟨fun h ↦ (hnone b₁ hb₁ h).elim, fun h ↦ (hnone b₂ hb₂ h).elim⟩
  have hpiece : ∀ D ∈ chambers, ∃ fD : PiecewiseQuasiPolynomial k,
      ∀ b ∈ D.carrier, fD.eval b =
        ∑ m ∈ (Finset.Icc (0 : ℤ) (ℓ b / ℓ v)).filter (fun m ↦ b - m • v ∈ C.carrier),
          q.eval (b - m • v) := by
    intro D hD
    classical
    by_cases hzb_ok : ∀ zb ∈ zeroBounds, ∀ b ∈ D.carrier, (∑ i, zb.1 i * b i) ≤ zb.2
    · have hres : ∀ z : Fin k → ZMod M_all, ∃ fz : PiecewiseQuasiPolynomial k,
          ∀ b ∈ D.carrier, (fun i ↦ (b i : ZMod M_all)) = z →
            fz.eval b =
              ∑ m ∈ (Finset.Icc (0 : ℤ) (ℓ b / ℓ v)).filter (fun m ↦ b - m • v ∈ C.carrier),
                q.eval (b - m • v) := by
        intro z
        by_cases hex : ∃ b₀ ∈ D.carrier, (fun i ↦ (b₀ i : ZMod M_all)) = z
        · obtain ⟨b₀, hb₀D, hb₀z⟩ := hex
          have hLne : lowerBounds.toFinset.Nonempty :=
            ⟨(0, 0, 1), List.mem_toFinset.2 (by simp [lowerBounds])⟩
          have hUne : upperBounds.toFinset.Nonempty :=
            ⟨(ℓvec, 0, (ℓ v).toNat), List.mem_toFinset.2 (by simp [upperBounds])⟩
          obtain ⟨lbStar, hlbStar_mem, hlbStar_max⟩ := Finset.exists_max_image
            lowerBounds.toFinset
            (fun lb ↦ intCeilDiv ((∑ i, lb.1 i * b₀ i) + lb.2.1) lb.2.2) hLne
          obtain ⟨ubStar, hubStar_mem, hubStar_min⟩ := Finset.exists_min_image
            upperBounds.toFinset
            (fun ub ↦ ((∑ i, ub.1 i * b₀ i) + ub.2.1) / ub.2.2) hUne
          rw [List.mem_toFinset] at hlbStar_mem hubStar_mem
          obtain ⟨fp, hfp⟩ := hpair_pq lbStar hlbStar_mem ubStar hubStar_mem
          refine ⟨fp, fun b hbD hbz ↦ ?_⟩
          rw [hfp b]
          dsimp only
          congr 1
          ext m
          rw [hmem_iff b m, Finset.mem_Icc]
          have hbz0 : (fun i ↦ (b i : ZMod M_all)) = (fun i ↦ (b₀ i : ZMod M_all)) :=
            hbz.trans hb₀z.symm
          constructor
          · rintro ⟨hlo, hhi⟩
            refine ⟨fun zb hzb ↦ hzb_ok zb hzb b hbD, fun lb hlb ↦ ?_, fun ub hub ↦ ?_⟩
            · exact ((hlb_order_const D hD b hbD b₀ hb₀D hbz0 lb hlb lbStar hlbStar_mem).2
                (hlbStar_max lb (List.mem_toFinset.2 hlb))).trans hlo
            · exact hhi.trans ((hub_order_const D hD b hbD b₀ hb₀D hbz0 ubStar hubStar_mem ub hub).2
                (hubStar_min ub (List.mem_toFinset.2 hub)))
          · rintro ⟨_, hlbs, hubs⟩
            exact ⟨hlbs lbStar hlbStar_mem, hubs ubStar hubStar_mem⟩
        · refine ⟨PiecewiseQuasiPolynomial.zero k, fun b hbD hbz ↦ ?_⟩
          exact (hex ⟨b, hbD, hbz⟩).elim
      choose fz hfz using hres
      have : NeZero M_all := ⟨hM_all.ne'⟩
      let hsum := PiecewiseQuasiPolynomial.isPiecewiseQuasiPolynomial_sum
        (Finset.univ : Finset (Fin k → ZMod M_all))
        (fun z b ↦ if (fun i ↦ (b i : ZMod M_all)) = z then (fz z).eval b else 0)
        (fun z _ ↦ PiecewiseQuasiPolynomial.isPiecewiseQuasiPolynomial_mulPeriodicIndicator
          hM_all (fun w ↦ w = z) ⟨fz z, fun _ ↦ rfl⟩)
      obtain ⟨fD, hfD⟩ := hsum
      refine ⟨fD, fun b hbD ↦ ?_⟩
      rw [hfD b]
      dsimp only
      rw [Finset.sum_eq_single (fun i ↦ (b i : ZMod M_all))]
      · simp [hfz _ b hbD rfl]
      · intro z _ hne; simp [hne.symm]
      · intro h; exact (h (Finset.mem_univ _)).elim
    · push Not at hzb_ok
      obtain ⟨zb, hzb, b₀, hb₀D, hgt⟩ := hzb_ok
      have hzb_all : zb ∈ allIneqs := List.mem_append_left _ (List.mem_append_left _ hzb)
      have hnone : ∀ b ∈ D.carrier, ¬ (∑ i, zb.1 i * b i) ≤ zb.2 := by
        rcases hdec D hD zb hzb_all with hall | hnone
        · exact (not_le.2 hgt (hall b₀ hb₀D)).elim
        · exact hnone
      refine ⟨PiecewiseQuasiPolynomial.zero k, fun b hbD ↦ ?_⟩
      rw [PiecewiseQuasiPolynomial.eval_zero]
      symm
      refine Finset.sum_eq_zero fun m hm ↦ ?_
      have hcontr := (hmem_iff b m).1 hm
      exact (hnone b hbD (hcontr.1 zb hzb)).elim
  classical
  let fOf (D : PolyhedralChamber k) : PiecewiseQuasiPolynomial k :=
    if hD : D ∈ chambers then (hpiece D hD).choose else PiecewiseQuasiPolynomial.zero k
  let f : PiecewiseQuasiPolynomial k :=
    { pieces := chambers.flatMap fun D ↦ (fOf D).pieces.map fun p ↦ (D.inter p.1, p.2)
      cover := fun b ↦ by
        obtain ⟨D, hD, hbD⟩ := hcov b
        obtain ⟨p, hp, hbp⟩ := (fOf D).cover b
        exact ⟨(D.inter p.1, p.2),
          List.mem_flatMap.2 ⟨D, hD, List.mem_map_of_mem hp⟩, by simp [hbD, hbp]⟩
      disjoint := by
        refine List.pairwise_flatMap.2 ⟨?_, ?_⟩
        · intro D _
          refine List.pairwise_map.2 ((fOf D).disjoint.imp fun h ↦ ?_)
          simp only [PolyhedralChamber.carrier_inter]
          exact h.mono Set.inter_subset_right Set.inter_subset_right
        · refine hdisj.imp fun {D₁ D₂} h a ha b hb ↦ ?_
          obtain ⟨p₁, _, rfl⟩ := List.mem_map.1 ha
          obtain ⟨p₂, _, rfl⟩ := List.mem_map.1 hb
          simp only [PolyhedralChamber.carrier_inter]
          exact h.mono Set.inter_subset_left Set.inter_subset_left }
  refine ⟨f, fun b ↦ ?_⟩
  obtain ⟨D, hD, hbD⟩ := hcov b
  obtain ⟨p, hp, hbp⟩ := (fOf D).cover b
  have hmem : (D.inter p.1, p.2) ∈ f.pieces :=
    List.mem_flatMap.2 ⟨D, hD, List.mem_map_of_mem hp⟩
  rw [PiecewiseQuasiPolynomial.eval_eq_of_mem f hmem (by simp [hbD, hbp]),
    ← PiecewiseQuasiPolynomial.eval_eq_of_mem (fOf D) hp hbp]
  change (if h : D ∈ chambers then (hpiece D h).choose
    else PiecewiseQuasiPolynomial.zero k).eval b = _
  rw [dite_eq_left_of_eq_true (eq_true hD)]
  exact (hpiece D hD).choose_spec b hbD

private theorem sum_ray_piecewiseQuasiPoly {k : ℕ} {g : (Fin k → ℤ) → ℚ}
    (hg : PiecewiseQuasiPolynomial.IsPiecewiseQuasiPolynomial g) (v : Fin k → ℤ)
    (ℓ : (Fin k → ℤ) →+ ℤ) (hℓv : 0 < ℓ v) :
    PiecewiseQuasiPolynomial.IsPiecewiseQuasiPolynomial (fun b : Fin k → ℤ ↦
      ∑ m ∈ Finset.Icc (0 : ℤ) (ℓ b / ℓ v), g (b - m • v)) := by
  obtain ⟨f, hf⟩ := hg
  let pieceList := f.pieces
  have hsum_eq : ∀ b : Fin k → ℤ,
      (∑ m ∈ Finset.Icc (0 : ℤ) (ℓ b / ℓ v), g (b - m • v)) =
      ∑ idx : Fin pieceList.length,
        ∑ m ∈ (Finset.Icc (0 : ℤ) (ℓ b / ℓ v)).filter
            (fun m ↦ b - m • v ∈ (pieceList.get idx).1.carrier),
          (pieceList.get idx).2.eval (b - m • v) := by
    intro b
    have hinner : ∀ idx : Fin pieceList.length,
        (∑ m ∈ (Finset.Icc (0 : ℤ) (ℓ b / ℓ v)).filter
            (fun m ↦ b - m • v ∈ (pieceList.get idx).1.carrier),
          (pieceList.get idx).2.eval (b - m • v)) =
        ∑ m ∈ Finset.Icc (0 : ℤ) (ℓ b / ℓ v),
          if b - m • v ∈ (pieceList.get idx).1.carrier then g (b - m • v) else 0 := by
      intro idx
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun m _ ↦ ?_
      split_ifs with hm
      · rw [← hf (b - m • v)]
        exact (PiecewiseQuasiPolynomial.eval_eq_of_mem f (List.get_mem _ idx) hm).symm
      · rfl
    simp_rw [hinner]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ ↦ ?_
    obtain ⟨p, hp, hmp⟩ := f.cover (b - m • v)
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hp
    rw [Finset.sum_eq_single (⟨i, hi⟩ : Fin pieceList.length)]
    · simp only [pieceList, List.get_eq_getElem, hmp, ↓reduceIte]
    · intro j _ hne
      have hdisj : Disjoint (pieceList.get j).1.carrier (pieceList.get ⟨i, hi⟩).1.carrier := by
        have hpw := List.pairwise_iff_getElem.1 f.disjoint
        rcases lt_trichotomy j.1 i with hlt | heq | hgt
        · exact hpw j.1 i j.2 hi hlt
        · exact (hne (Fin.ext heq)).elim
        · exact (hpw i j.1 hi j.2 hgt).symm
      have hnot : b - m • v ∉ (pieceList.get j).1.carrier :=
        fun h ↦ Set.disjoint_left.1 hdisj h hmp
      simp only [hnot, ↓reduceIte]
    · intro h; exact (h (Finset.mem_univ _)).elim
  have htot := PiecewiseQuasiPolynomial.isPiecewiseQuasiPolynomial_sum
    (Finset.univ : Finset (Fin pieceList.length))
    (fun idx b ↦ ∑ m ∈ (Finset.Icc (0 : ℤ) (ℓ b / ℓ v)).filter
        (fun m ↦ b - m • v ∈ (pieceList.get idx).1.carrier),
      (pieceList.get idx).2.eval (b - m • v))
    (fun idx _ ↦ sum_ray_chamber_quasiPoly (pieceList.get idx).1 (pieceList.get idx).2 v ℓ hℓv)
  rcases htot with ⟨F, hF⟩
  exact ⟨F, fun b ↦ by rw [hF b]; dsimp only; rw [hsum_eq b]⟩

end RaySum

/-! ### 2. Vector Partition Functions and Parametric Rational Polytopes -/

section VectorPartition

/-- The vector partition function `φ_A(b) = #{x ∈ ℕ^s : A x = b}` associated to an integer linear
map `A : (Fin s → ℤ) →+ (Fin k → ℤ)`. -/
@[expose]
noncomputable def vectorPartitionCount {s k : ℕ} (A : (Fin s → ℤ) →+ (Fin k → ℤ))
    (b : Fin k → ℤ) : ℕ :=
  Nat.card {x : Fin s → ℕ // A (fun i ↦ (x i : ℤ)) = b}

/-- If `ℓ : ℤ^k →+ ℤ` is strictly positive on every column of `A`, then every fiber
`{x ∈ ℕ^s : A x = b}` is finite. -/
theorem finite_vectorPartitionFiber {s k : ℕ} (A : (Fin s → ℤ) →+ (Fin k → ℤ))
    (ℓ : (Fin k → ℤ) →+ ℤ) (hℓ : ∀ i : Fin s, 0 < ℓ (A (Pi.single i 1))) (b : Fin k → ℤ) :
    Finite {x : Fin s → ℕ // A (fun i ↦ (x i : ℤ)) = b} := by
  have hbound : ∀ (x : Fin s → ℕ), A (fun i ↦ (x i : ℤ)) = b →
      ∀ i : Fin s, x i ≤ (ℓ b).toNat := by
    intro x hx i
    have hsum : ℓ (A (fun j ↦ (x j : ℤ))) = ∑ j : Fin s, (x j : ℤ) * ℓ (A (Pi.single j 1)) := by
      have hvec : (fun j ↦ (x j : ℤ)) = ∑ j : Fin s, (x j : ℤ) • Pi.single j (1 : ℤ) := by
        ext m; simp [Finset.sum_apply, Pi.single_apply]
      conv_lhs => rw [hvec]
      rw [map_sum, map_sum]
      refine Finset.sum_congr rfl fun j _ ↦ by rw [map_zsmul, map_zsmul, zsmul_eq_mul, Int.cast_id]
    rw [hx] at hsum
    have hle : (x i : ℤ) * ℓ (A (Pi.single i 1)) ≤ ℓ b := by
      rw [hsum]
      exact Finset.single_le_sum (fun j _ ↦ mul_nonneg (Int.natCast_nonneg _) (le_of_lt (hℓ j)))
        (Finset.mem_univ i)
    have h1 : (x i : ℤ) ≤ (x i : ℤ) * ℓ (A (Pi.single i 1)) := by
      have := hℓ i; nlinarith
    omega
  let B := (ℓ b).toNat + 1
  let f : {x : Fin s → ℕ // A (fun i ↦ (x i : ℤ)) = b} → (Fin s → Fin B) :=
    fun x i ↦ ⟨x.1 i, Nat.lt_succ_of_le (hbound x.1 x.2 i)⟩
  have hinj : Function.Injective f := by
    intro x y hxy; apply Subtype.ext; ext i; exact congrArg Fin.val (congrFun hxy i)
  exact Finite.of_injective f hinj

/-- **Vector Partition Function Piecewise Quasi-Polynomiality**: for any integer linear map
`A : ℤ^s →+ ℤ^k` admitting a strictly positive separating linear functional `ℓ`, the vector
partition function `b ↦ (vectorPartitionCount A b : ℚ)` is piecewise quasi-polynomial on `ℤ^k`. -/
theorem vectorPartitionCount_isPiecewiseQuasiPolynomial {s k : ℕ}
    (A : (Fin s → ℤ) →+ (Fin k → ℤ))
    (ℓ : (Fin k → ℤ) →+ ℤ) (hℓ : ∀ i : Fin s, 0 < ℓ (A (Pi.single i 1))) :
    PiecewiseQuasiPolynomial.IsPiecewiseQuasiPolynomial
      (fun b : Fin k → ℤ ↦ (vectorPartitionCount A b : ℚ)) := by
  induction s with
  | zero =>
    have heq : ∀ b : Fin k → ℤ, (vectorPartitionCount A b : ℚ) = if b = 0 then 1 else 0 := by
      intro b
      unfold vectorPartitionCount
      by_cases hb : b = 0
      · subst hb
        have : Unique {x : Fin 0 → ℕ // A (fun i ↦ (x i : ℤ)) = 0} :=
          { default := ⟨Fin.elim0, by
              have : (fun i : Fin 0 ↦ ((Fin.elim0 i : ℕ) : ℤ)) = 0 := funext fun i ↦ i.elim0
              rw [this, map_zero]⟩
            uniq := fun ⟨x, _⟩ ↦ Subtype.ext (funext fun i ↦ i.elim0) }
        rw [Nat.card_unique]; simp
      · have : IsEmpty {x : Fin 0 → ℕ // A (fun i ↦ (x i : ℤ)) = b} :=
          ⟨fun ⟨x, hx⟩ ↦ by
            have : (fun i : Fin 0 ↦ (x i : ℤ)) = 0 := funext fun i ↦ i.elim0
            rw [this, map_zero] at hx; exact hb hx.symm⟩
        have : Fintype {x : Fin 0 → ℕ // A (fun i ↦ (x i : ℤ)) = b} := Fintype.ofIsEmpty
        rw [Nat.card_eq_fintype_card, Fintype.card_eq_zero]; simp [hb]
    let zeroIneqs : List ((Fin k → ℤ) × ℤ) :=
      (List.finRange k).flatMap fun i ↦ [(Pi.single i (1 : ℤ), 0), (Pi.single i (-1 : ℤ), 0)]
    let chambers := PiecewiseQuasiPolynomial.splitPartitionList
      [PolyhedralChamber.univ k] zeroIneqs
    have hcov := PiecewiseQuasiPolynomial.splitPartitionList_cover
      (chambers := [PolyhedralChamber.univ k])
      (fun y ↦ ⟨PolyhedralChamber.univ k, by simp, by simp⟩) zeroIneqs
    have hdisj := PiecewiseQuasiPolynomial.splitPartitionList_disjoint
      (chambers := [PolyhedralChamber.univ k]) (by simp) zeroIneqs
    have hdec := PiecewiseQuasiPolynomial.splitPartitionList_decides
      [PolyhedralChamber.univ k] zeroIneqs
    classical
    let f : PiecewiseQuasiPolynomial k :=
      { pieces := chambers.map fun C ↦
          (C, if (0 : Fin k → ℤ) ∈ C.carrier then QuasiPolynomial.const k 1
              else QuasiPolynomial.zero k)
        cover := fun b ↦ by
          obtain ⟨C, hC, hbC⟩ := hcov b
          exact ⟨_, List.mem_map_of_mem hC, hbC⟩
        disjoint := List.pairwise_map.2 (hdisj.imp fun h ↦ h) }
    refine ⟨f, fun b ↦ ?_⟩
    dsimp only
    rw [heq b]
    obtain ⟨C, hC, hbC⟩ := hcov b
    rw [PiecewiseQuasiPolynomial.eval_eq_of_mem f (List.mem_map_of_mem hC) hbC]
    have hzero_iff : (0 : Fin k → ℤ) ∈ C.carrier ↔ b = 0 := by
      constructor
      · intro h0C
        ext i
        have hi1 : (Pi.single i (1 : ℤ), (0 : ℤ)) ∈ zeroIneqs :=
          List.mem_flatMap.2 ⟨i, List.mem_finRange i, by simp⟩
        have hi2 : (Pi.single i (-1 : ℤ), (0 : ℤ)) ∈ zeroIneqs :=
          List.mem_flatMap.2 ⟨i, List.mem_finRange i, by simp⟩
        have hle1 : b i ≤ 0 := by
          rcases hdec C hC _ hi1 with hall | hnone
          · simpa [Pi.single_apply] using hall b hbC
          · exact (hnone 0 h0C (by simp)).elim
        have hle2 : -b i ≤ 0 := by
          rcases hdec C hC _ hi2 with hall | hnone
          · simpa [Pi.single_apply] using hall b hbC
          · exact (hnone 0 h0C (by simp)).elim
        rw [Pi.zero_apply]; omega
      · rintro rfl; exact hbC
    by_cases hb : b = 0
    · have h0 : (0 : Fin k → ℤ) ∈ C.carrier := hzero_iff.2 hb
      simp [hb, h0]
    · have h0 : (0 : Fin k → ℤ) ∉ C.carrier := fun h ↦ hb (hzero_iff.1 h)
      simp [hb, h0]
  | succ s ih =>
    let A' : (Fin s → ℤ) →+ (Fin k → ℤ) :=
      A.comp
        { toFun := fun x ↦ Fin.snoc x 0
          map_zero' := by ext i; refine Fin.lastCases ?_ ?_ i <;> simp
          map_add' := fun x y ↦ by ext i; refine Fin.lastCases ?_ ?_ i <;> simp }
    have hA'_single : ∀ i : Fin s, A' (Pi.single i 1) = A (Pi.single i.castSucc 1) := by
      intro i
      change A (Fin.snoc (Pi.single i 1) 0) = A (Pi.single i.castSucc 1)
      congr 1; ext j
      refine Fin.lastCases ?_ (fun j' ↦ ?_) j
      · simp
      · simp [Pi.single_apply, Fin.castSucc_inj]
    have hℓ' : ∀ i : Fin s, 0 < ℓ (A' (Pi.single i 1)) := fun i ↦ by
      rw [hA'_single i]; exact hℓ i.castSucc
    let v : Fin k → ℤ := A (Pi.single (Fin.last s) 1)
    have hℓv : 0 < ℓ v := hℓ (Fin.last s)
    have hrec : ∀ b : Fin k → ℤ,
        (vectorPartitionCount A b : ℚ) =
        ∑ m ∈ Finset.Icc (0 : ℤ) (ℓ b / ℓ v), (vectorPartitionCount A' (b - m • v) : ℚ) := by
      intro b
      norm_cast
      have hdecomp : ∀ x : Fin (s + 1) → ℕ,
          A (fun i ↦ (x i : ℤ)) =
            A' (fun i : Fin s ↦ (x i.castSucc : ℤ)) + (x (Fin.last s) : ℤ) • v := by
        intro x
        have hx_eq : (fun i : Fin (s + 1) ↦ (x i : ℤ)) =
            Fin.snoc (fun i : Fin s ↦ (x i.castSucc : ℤ)) 0 +
              (x (Fin.last s) : ℤ) • Pi.single (Fin.last s) 1 := by
          ext i
          refine Fin.lastCases ?_ (fun j ↦ ?_) i
          · simp
          · simp [Fin.ne_of_lt (Fin.castSucc_lt_last j)]
        conv_lhs => rw [hx_eq]
        rw [map_add, map_zsmul]
        rfl
      have hℓ_nonneg : ∀ y : Fin s → ℕ, 0 ≤ ℓ (A' (fun i ↦ (y i : ℤ))) := by
        intro y
        have hy : (fun i : Fin s ↦ (y i : ℤ)) = ∑ i : Fin s, (y i : ℤ) • Pi.single i (1 : ℤ) := by
          ext m; simp [Finset.sum_apply, Pi.single_apply]
        rw [hy, map_sum, map_sum]
        refine Finset.sum_nonneg fun i _ ↦ ?_
        rw [map_zsmul, map_zsmul, zsmul_eq_mul, Int.cast_id]
        exact mul_nonneg (Int.natCast_nonneg _) (le_of_lt (hℓ' i))
      let e : {x : Fin (s + 1) → ℕ // A (fun i ↦ (x i : ℤ)) = b} ≃
          Σ m : Finset.Icc (0 : ℤ) (ℓ b / ℓ v),
            {y : Fin s → ℕ // A' (fun i ↦ (y i : ℤ)) = b - (m : ℤ) • v} :=
        { toFun := fun ⟨x, hx⟩ ↦
            ⟨⟨(x (Fin.last s) : ℤ), Finset.mem_Icc.2 ⟨Int.natCast_nonneg _, by
              rw [le_intFloorDiv_iff hℓv]
              have h1 := congrArg ℓ (hdecomp x)
              rw [hx, map_add, map_zsmul, zsmul_eq_mul, Int.cast_id] at h1
              have h2 := hℓ_nonneg (fun i ↦ x i.castSucc)
              linarith⟩⟩,
              ⟨fun i ↦ x i.castSucc, by
                have := hdecomp x; rw [hx] at this; exact eq_sub_of_add_eq this.symm⟩⟩
          invFun := fun ⟨⟨m, hm⟩, ⟨y, hy⟩⟩ ↦
            ⟨Fin.snoc (α := fun _ ↦ ℕ) y m.toNat, by
              rw [hdecomp]
              have hm0 : 0 ≤ m := (Finset.mem_Icc.1 hm).1
              have hsnoc_cast :
                  (fun i : Fin s ↦ ((Fin.snoc (α := fun _ ↦ ℕ) y m.toNat i.castSucc : ℕ) : ℤ)) =
                  (fun i : Fin s ↦ (y i : ℤ)) := by ext i; simp
              rw [hsnoc_cast, Fin.snoc_last, Int.toNat_of_nonneg hm0, hy, sub_add_cancel]⟩
          left_inv := fun ⟨x, _⟩ ↦ by
            apply Subtype.ext; ext i; refine Fin.lastCases ?_ (fun j ↦ ?_) i <;> simp
          right_inv := fun ⟨⟨m, hm⟩, ⟨y, _⟩⟩ ↦ by
            have hm0 : 0 ≤ m := (Finset.mem_Icc.1 hm).1
            ext
            · simp [Int.toNat_of_nonneg hm0]
            · simp }
      have : ∀ m : Finset.Icc (0 : ℤ) (ℓ b / ℓ v),
          Finite {y : Fin s → ℕ // A' (fun i ↦ (y i : ℤ)) = b - (m : ℤ) • v} :=
        fun m ↦ finite_vectorPartitionFiber A' ℓ hℓ' (b - (m : ℤ) • v)
      unfold vectorPartitionCount
      rw [Nat.card_congr e, Nat.card_sigma, ← Finset.sum_attach (Finset.Icc (0 : ℤ) (ℓ b / ℓ v))]
      rfl
    have hstep := sum_ray_piecewiseQuasiPoly (ih A' hℓ') v ℓ hℓv
    rcases hstep with ⟨F, hF⟩
    exact ⟨F, fun b ↦ by rw [hF b]; dsimp only; rw [← hrec b]⟩

/-- **Gordan's Separation Lemma**: if the real extension of `A : ℤ^s →+ ℤ^u` satisfies
`ker(A_ℝ) ∩ ℝ≥0^s = {0}`, then there exists an integer linear functional `ℓ : ℤ^u →+ ℤ` that is
strictly positive on every column `A (Pi.single i 1)` of `A`. -/
theorem exists_pos_linearFunctional_of_pointed {s u : ℕ}
    (A : (Fin s → ℤ) →+ (Fin u → ℤ))
    (hpointed : ∀ x : Fin s → ℝ, (∀ i, 0 ≤ x i) →
      (∀ j, ∑ i, (A (Pi.single i 1) j : ℝ) * x i = 0) → x = 0) :
    ∃ ℓ : (Fin u → ℤ) →+ ℤ, ∀ i : Fin s, 0 < ℓ (A (Pi.single i 1)) := by
  by_cases hs : s = 0
  · subst hs; exact ⟨0, fun i ↦ i.elim0⟩
  let col : Fin s → (Fin u → ℝ) := fun i j ↦ (A (Pi.single i 1) j : ℝ)
  let S : Set (Fin u → ℝ) := Set.range col
  let K : Set (Fin u → ℝ) := convexHull ℝ S
  have hSfin : S.Finite := Set.finite_range col
  have hKcomp : IsCompact K := hSfin.isCompact_convexHull (𝕜 := ℝ)
  have hKclosed : IsClosed K := hKcomp.isClosed
  have hKconv : Convex ℝ K := convex_convexHull ℝ S
  have h0not : (0 : Fin u → ℝ) ∉ K := by
    intro h0
    change (0 : Fin u → ℝ) ∈ convexHull ℝ S at h0
    rw [convexHull_eq] at h0
    obtain ⟨ι, t, w, z, hw0, hw1, hzS, hsum⟩ := h0
    choose idx hidx using fun (a : t) ↦ hzS a.1 a.2
    let x : Fin s → ℝ := fun i ↦ ∑ a ∈ t.attach, if idx a = i then w a.1 else 0
    have hx0 : ∀ i, 0 ≤ x i := fun i ↦
      Finset.sum_nonneg fun a _ ↦ by
        split_ifs
        · exact hw0 a.1 a.2
        · exact le_rfl
    have hAx : ∀ j, ∑ i, (A (Pi.single i 1) j : ℝ) * x i = 0 := by
      intro j
      have h1 : (∑ i, (A (Pi.single i 1) j : ℝ) * x i) =
          ∑ a ∈ t.attach, w a.1 * col (idx a) j := by
        simp only [x, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun a _ ↦ ?_
        simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, col]
        ring
      rw [h1]
      have h2 := congrFun hsum j
      simp only [Finset.centerMass, hw1, inv_one, Finset.sum_apply, Pi.smul_apply,
        smul_eq_mul, Pi.zero_apply, one_mul] at h2
      rw [← h2, ← Finset.sum_attach t]
      refine Finset.sum_congr rfl fun a _ ↦ by rw [hidx a]
    have hxzero := hpointed x hx0 hAx
    have hsum_x : ∑ i : Fin s, x i = 1 := by
      simp only [x]
      rw [Finset.sum_comm]
      calc
        (∑ a ∈ t.attach, ∑ i : Fin s, if idx a = i then w a.1 else 0)
            = ∑ a ∈ t.attach, w a.1 := Finset.sum_congr rfl fun a _ ↦ by simp
        _ = ∑ a ∈ t, w a := Finset.sum_attach t w
        _ = 1 := hw1
    simp [hxzero] at hsum_x
  obtain ⟨f, r, hfr0, hfrK⟩ := geometric_hahn_banach_point_closed hKconv hKclosed h0not
  have hfi : ∀ i : Fin s, 0 < f (col i) := fun i ↦ by
    have hmem : col i ∈ K := subset_convexHull ℝ S ⟨i, rfl⟩
    have := hfrK (col i) hmem
    rw [map_zero] at hfr0
    linarith
  let hne_img : (Finset.univ.image fun i : Fin s ↦ f (col i)).Nonempty :=
    Finset.image_nonempty.2 ⟨⟨0, Nat.pos_of_ne_zero hs⟩, Finset.mem_univ _⟩
  let δ : ℝ := (Finset.univ.image fun i : Fin s ↦ f (col i)).min' hne_img
  have hδ : 0 < δ := by
    have hmem := Finset.min'_mem (Finset.univ.image fun i : Fin s ↦ f (col i)) hne_img
    obtain ⟨i, _, hi⟩ := Finset.mem_image.1 hmem
    change 0 < (Finset.univ.image fun i : Fin s ↦ f (col i)).min' hne_img
    rw [← hi]; exact hfi i
  let M : ℝ := 1 + ∑ j : Fin u, ∑ i : Fin s, |col i j|
  have hM : 0 < M := by
    have hnn : 0 ≤ ∑ j : Fin u, ∑ i : Fin s, |col i j| :=
      Finset.sum_nonneg fun j _ ↦ Finset.sum_nonneg fun i _ ↦ abs_nonneg _
    linarith
  have hq_exists : ∀ j : Fin u, ∃ q : ℚ, |((q : ℝ) - f (Pi.single j 1))| < δ / (2 * M) := by
    intro j
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show f (Pi.single j 1) - δ / (2 * M) <
      f (Pi.single j 1) + δ / (2 * M) by linarith [div_pos hδ (by positivity : (0 : ℝ) < 2 * M)])
    refine ⟨q, abs_lt.2 ⟨by linarith, by linarith⟩⟩
  choose q hq using hq_exists
  let D : ℕ := ∏ j : Fin u, (q j).den
  have hD : 0 < D := Finset.prod_pos fun j _ ↦ (q j).pos
  let c : Fin u → ℤ := fun j ↦ (q j).num * ((D / (q j).den : ℕ) : ℤ)
  have hc_eq : ∀ j : Fin u, (c j : ℝ) = (D : ℝ) * (q j : ℝ) := by
    intro j
    have hdvd : (q j).den ∣ D := Finset.dvd_prod_of_mem _ (Finset.mem_univ j)
    have hmul : (q j).den * (D / (q j).den) = D := Nat.mul_div_cancel' hdvd
    have hden_ne : ((q j).den : ℝ) ≠ 0 := by positivity
    have hmulR : ((q j).den : ℝ) * ((D / (q j).den : ℕ) : ℝ) = (D : ℝ) := by exact_mod_cast hmul
    rw [Rat.cast_def]
    simp only [c, Int.cast_mul, Int.cast_natCast]
    calc
      ((q j).num : ℝ) * ((D / (q j).den : ℕ) : ℝ)
          = ((q j).num : ℝ) / ((q j).den : ℝ) *
              (((q j).den : ℝ) * ((D / (q j).den : ℕ) : ℝ)) := by field_simp [hden_ne]
      _ = (D : ℝ) * (((q j).num : ℝ) / ((q j).den : ℝ)) := by rw [hmulR, mul_comm]
  let ℓ : (Fin u → ℤ) →+ ℤ :=
    { toFun := fun y ↦ ∑ j : Fin u, c j * y j
      map_zero' := by simp
      map_add' := fun x y ↦ by simp [mul_add, Finset.sum_add_distrib] }
  refine ⟨ℓ, fun i ↦ ?_⟩
  have hreal : (0 : ℝ) < (ℓ (A (Pi.single i 1)) : ℝ) := by
    have hcast : (ℓ (A (Pi.single i 1)) : ℝ) = (D : ℝ) * ∑ j : Fin u, (q j : ℝ) * col i j := by
      simp only [ℓ, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Int.cast_sum, Int.cast_mul, hc_eq,
        Finset.mul_sum, col, mul_assoc]
    rw [hcast]
    refine mul_pos (by positivity) ?_
    have hf_expand : f (col i) = ∑ j : Fin u, f (Pi.single j 1) * col i j := by
      have hvec : col i = ∑ j : Fin u, col i j • Pi.single j (1 : ℝ) := by
        ext m; simp [Finset.sum_apply, Pi.single_apply]
      conv_lhs => rw [hvec]
      rw [map_sum]
      refine Finset.sum_congr rfl fun j _ ↦ by rw [map_smul, smul_eq_mul, mul_comm]
    have hdiff : |(∑ j : Fin u, (q j : ℝ) * col i j) - f (col i)| ≤ δ / 2 := by
      rw [hf_expand, ← Finset.sum_sub_distrib]
      calc
        |∑ j : Fin u, ((q j : ℝ) * col i j - f (Pi.single j 1) * col i j)|
            ≤ ∑ j : Fin u, |(q j : ℝ) - f (Pi.single j 1)| * |col i j| := by
              refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
              refine Finset.sum_le_sum fun j _ ↦ by rw [← sub_mul, abs_mul]
        _ ≤ ∑ j : Fin u, (δ / (2 * M)) * |col i j| :=
              Finset.sum_le_sum fun j _ ↦
                mul_le_mul_of_nonneg_right (le_of_lt (hq j)) (abs_nonneg _)
        _ = (δ / (2 * M)) * ∑ j : Fin u, |col i j| := by rw [← Finset.mul_sum]
        _ ≤ (δ / (2 * M)) * M := by
              refine mul_le_mul_of_nonneg_left ?_ (by positivity)
              have hle : ∑ j : Fin u, |col i j| ≤ ∑ j : Fin u, ∑ i' : Fin s, |col i' j| :=
                Finset.sum_le_sum fun j _ ↦
                  Finset.single_le_sum (f := fun i' : Fin s ↦ |col i' j|)
                    (fun i' _ ↦ abs_nonneg _) (Finset.mem_univ i)
              linarith
        _ = δ / 2 := by field_simp [hM.ne']
    have hδi : δ ≤ f (col i) :=
      Finset.min'_le _ _ (Finset.mem_image.2 ⟨i, Finset.mem_univ i, rfl⟩)
    have := (abs_le.1 hdiff).1
    linarith
  exact_mod_cast hreal

/-- Lattice-point count of a bounded parametric rational polytope
`Δ_{A,B}(y) = {(x, z) ∈ ℝ≥0^s × ℝ^{s'} : A₁ x + A₂ z = B y}`. -/
@[expose]
noncomputable def parametricPolytopeCount {s s' u d : ℕ}
    (A₁ : (Fin s → ℤ) →+ (Fin u → ℤ)) (A₂ : (Fin s' → ℤ) →+ (Fin u → ℤ))
    (B : (Fin d → ℤ) →+ (Fin u → ℤ)) (y : Fin d → ℤ) : ℕ :=
  Nat.card {p : (Fin s → ℕ) × (Fin s' → ℤ) //
    A₁ (fun i ↦ (p.1 i : ℤ)) + A₂ p.2 = B y}

/-- **Parametric Rational Polytope Piecewise Quasi-Polynomiality**:
for any integer linear maps `A₁ : ℤ^s →+ ℤ^u`, `A₂ : ℤ^{s'} →+ ℤ^u`, and `B : ℤ^d →+ ℤ^u` whose
real kernel intersects `ℝ≥0^s × ℝ^{s'}` trivially, the lattice-point count
`y ↦ (parametricPolytopeCount A₁ A₂ B y : ℚ)` is a piecewise quasi-polynomial function on `ℤ^d`. -/
theorem parametricPolytopeCount_isPiecewiseQuasiPolynomial {s s' u d : ℕ}
    (A₁ : (Fin s → ℤ) →+ (Fin u → ℤ)) (A₂ : (Fin s' → ℤ) →+ (Fin u → ℤ))
    (B : (Fin d → ℤ) →+ (Fin u → ℤ))
    (hpointed : ∀ (x : Fin s → ℝ) (z : Fin s' → ℝ), (∀ i, 0 ≤ x i) →
      (∀ j, (∑ i, (A₁ (Pi.single i 1) j : ℝ) * x i) +
            (∑ l, (A₂ (Pi.single l 1) j : ℝ) * z l) = 0) →
      x = 0 ∧ z = 0) :
    PiecewiseQuasiPolynomial.IsPiecewiseQuasiPolynomial
      (fun y : Fin d → ℤ ↦ (parametricPolytopeCount A₁ A₂ B y : ℚ)) := by
  let A₂Q : (Fin s' → ℚ) →ₗ[ℚ] (Fin u → ℚ) :=
    { toFun := fun z j ↦ ∑ l : Fin s', (A₂ (Pi.single l 1) j : ℚ) * z l
      map_add' := fun z₁ z₂ ↦ by ext j; simp [mul_add, Finset.sum_add_distrib]
      map_smul' := fun r z ↦ by
        ext j; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        refine Finset.sum_congr rfl fun l _ ↦ by ring }
  have hA₂Q_inj : Function.Injective A₂Q := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    have hzR := (hpointed 0 (fun l ↦ (z l : ℝ)) (fun _ ↦ le_rfl) (fun j ↦ by
      have hj := congrFun hz j
      simp only [A₂Q, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply] at hj
      have hjR : ∑ l : Fin s', (A₂ (Pi.single l 1) j : ℝ) * (z l : ℝ) = 0 := by
        exact_mod_cast hj
      simpa using hjR)).2
    ext l
    have hl : (z l : ℝ) = 0 := by simpa using congrFun hzR l
    exact_mod_cast hl
  obtain ⟨LQ, hLQ⟩ := A₂Q.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 hA₂Q_inj)
  let D : ℕ := ∏ j : Fin u, ∏ l : Fin s', (LQ (Pi.single j 1) l).den
  have hD : 0 < D := Finset.prod_pos fun j _ ↦ Finset.prod_pos fun l _ ↦ (LQ (Pi.single j 1) l).pos
  let Lmat (j : Fin u) (l : Fin s') : ℤ :=
    (LQ (Pi.single j 1) l).num * ((D / (LQ (Pi.single j 1) l).den : ℕ) : ℤ)
  have hLmat_cast : ∀ j l, (Lmat j l : ℚ) = (D : ℚ) * LQ (Pi.single j 1) l := by
    intro j l
    have hdvd : (LQ (Pi.single j 1) l).den ∣ D :=
      dvd_trans (Finset.dvd_prod_of_mem (fun l' ↦ (LQ (Pi.single j 1) l').den) (Finset.mem_univ l))
        (Finset.dvd_prod_of_mem (fun j' ↦ ∏ l' : Fin s', (LQ (Pi.single j' 1) l').den)
          (Finset.mem_univ j))
    have hmul : (LQ (Pi.single j 1) l).den * (D / (LQ (Pi.single j 1) l).den) = D :=
      Nat.mul_div_cancel' hdvd
    have hden_ne : ((LQ (Pi.single j 1) l).den : ℚ) ≠ 0 := by positivity
    simp only [Lmat, Int.cast_mul, Int.cast_natCast]
    have hq := (Rat.num_div_den (LQ (Pi.single j 1) l)).symm
    calc
      ((LQ (Pi.single j 1) l).num : ℚ) * ((D / (LQ (Pi.single j 1) l).den : ℕ) : ℚ)
          = ((LQ (Pi.single j 1) l).num : ℚ) / ((LQ (Pi.single j 1) l).den : ℚ) *
              (((LQ (Pi.single j 1) l).den : ℚ) * ((D / (LQ (Pi.single j 1) l).den : ℕ) : ℚ)) := by
            field_simp [hden_ne]
      _ = (D : ℚ) * LQ (Pi.single j 1) l := by
            have hmulQ : ((LQ (Pi.single j 1) l).den : ℚ) *
                ((D / (LQ (Pi.single j 1) l).den : ℕ) : ℚ) = (D : ℚ) := by exact_mod_cast hmul
            rw [hmulQ, ← hq, mul_comm]
  let L : (Fin u → ℤ) →+ (Fin s' → ℤ) :=
    { toFun := fun v l ↦ ∑ j : Fin u, Lmat j l * v j
      map_zero' := by ext l; simp
      map_add' := fun v₁ v₂ ↦ by ext l; simp [mul_add, Finset.sum_add_distrib] }
  have hLA₂ : ∀ z : Fin s' → ℤ, L (A₂ z) = (D : ℤ) • z := by
    intro z; ext l
    suffices hq : ((L (A₂ z) l : ℤ) : ℚ) = (((D : ℤ) • z) l : ℚ) by exact_mod_cast hq
    have h1 : (A₂Q (fun m ↦ (z m : ℚ))) = fun j ↦ (A₂ z j : ℚ) := by
      ext j
      simp only [A₂Q, LinearMap.coe_mk, AddHom.coe_mk]
      rw [QuasiPolynomial.addMonoidHom_fin_apply A₂ z j, Int.cast_sum]
      refine Finset.sum_congr rfl fun m _ ↦ by push_cast; rfl
    have h2 : LQ (fun j ↦ (A₂ z j : ℚ)) l = (z l : ℚ) := by
      rw [← h1]
      exact congrFun (congrArg (fun f : (Fin s' → ℚ) →ₗ[ℚ] (Fin s' → ℚ) ↦ f (fun m ↦ (z m : ℚ)))
        hLQ) l
    have h3 : LQ (fun j ↦ (A₂ z j : ℚ)) l = ∑ j : Fin u, LQ (Pi.single j 1) l * (A₂ z j : ℚ) := by
      have hvec : (fun j ↦ (A₂ z j : ℚ)) = ∑ j : Fin u, (A₂ z j : ℚ) • Pi.single j (1 : ℚ) := by
        ext m; simp [Finset.sum_apply, Pi.single_apply]
      conv_lhs => rw [hvec]
      rw [map_sum, Finset.sum_apply]
      refine Finset.sum_congr rfl fun j _ ↦ by rw [map_smul, Pi.smul_apply, smul_eq_mul, mul_comm]
    simp only [L, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Int.cast_sum, Int.cast_mul, hLmat_cast,
      Pi.smul_apply, zsmul_eq_mul, Int.cast_natCast, mul_assoc]
    rw [← Finset.mul_sum, ← h3, h2]
  let P : (Fin u → ℤ) →+ (Fin u → ℤ) :=
    { toFun := fun v ↦ (D : ℤ) • v - A₂ (L v)
      map_zero' := by simp
      map_add' := fun v₁ v₂ ↦ by simp [smul_add, map_add]; abel }
  have hmem_range_A₂ : ∀ v : Fin u → ℤ,
      (∃ z : Fin s' → ℤ, A₂ z = v) ↔ P v = 0 ∧ ∀ l : Fin s', (D : ℤ) ∣ L v l := by
    intro v
    constructor
    · rintro ⟨z, rfl⟩
      refine ⟨?_, fun l ↦ ?_⟩
      · simp only [P, AddMonoidHom.coe_mk, ZeroHom.coe_mk, hLA₂, map_zsmul, sub_self]
      · simp only [hLA₂, Pi.smul_apply, zsmul_eq_mul]; exact dvd_mul_right _ _
    · rintro ⟨hPv, hdvd⟩
      choose z hz using hdvd
      refine ⟨z, ?_⟩
      have hLz : L v = (D : ℤ) • z := by ext l; simp [hz l]
      have hDv : (D : ℤ) • v = (D : ℤ) • A₂ z := by
        have h0 : (D : ℤ) • v - A₂ (L v) = 0 := hPv
        rw [hLz, map_zsmul] at h0
        exact sub_eq_zero.1 h0
      ext j
      have hj := congrFun hDv j
      simp only [Pi.smul_apply, zsmul_eq_mul] at hj
      exact (mul_left_cancel₀ (by positivity : (D : ℤ) ≠ 0) hj).symm
  have hA₂_inj : Function.Injective A₂ := by
    intro z₁ z₂ h
    have := congrArg L h; rw [hLA₂, hLA₂] at this
    ext l
    have hl := congrFun this l
    simp only [Pi.smul_apply, zsmul_eq_mul] at hl
    exact mul_left_cancel₀ (by positivity : (D : ℤ) ≠ 0) hl
  let PA₁ : (Fin s → ℤ) →+ (Fin u → ℤ) := P.comp A₁
  have hPA₁_pointed : ∀ x : Fin s → ℝ, (∀ i, 0 ≤ x i) →
      (∀ j, ∑ i, (PA₁ (Pi.single i 1) j : ℝ) * x i = 0) → x = 0 := by
    intro x hx0 hsum
    let z : Fin s' → ℝ := fun l ↦ -∑ i : Fin s, (L (A₁ (Pi.single i 1)) l : ℝ) * x i
    have hcomb : ∀ j, (∑ i, (A₁ (Pi.single i 1) j : ℝ) * ((D : ℝ) * x i)) +
        (∑ l, (A₂ (Pi.single l 1) j : ℝ) * z l) = 0 := by
      intro j
      have hcol : ∀ i : Fin s, (PA₁ (Pi.single i 1) j : ℝ) =
          (D : ℝ) * (A₁ (Pi.single i 1) j : ℝ) -
            ∑ l : Fin s', (A₂ (Pi.single l 1) j : ℝ) * (L (A₁ (Pi.single i 1)) l : ℝ) := by
        intro i
        change ((((D : ℤ) • A₁ (Pi.single i 1) - A₂ (L (A₁ (Pi.single i 1)))) j : ℤ) : ℝ) = _
        rw [Pi.sub_apply, Pi.smul_apply, zsmul_eq_mul, Int.cast_id, Int.cast_sub, Int.cast_mul,
          Int.cast_natCast]
        congr 1
        rw [QuasiPolynomial.addMonoidHom_fin_apply A₂ (L (A₁ (Pi.single i 1))) j, Int.cast_sum]
        refine Finset.sum_congr rfl fun l _ ↦ by push_cast; rfl
      have h0 := hsum j
      simp_rw [hcol, sub_mul, Finset.sum_sub_distrib, Finset.sum_mul] at h0
      rw [Finset.sum_comm] at h0
      have hleft : (∑ i, (A₁ (Pi.single i 1) j : ℝ) * ((D : ℝ) * x i)) =
          ∑ i, (D : ℝ) * (A₁ (Pi.single i 1) j : ℝ) * x i :=
        Finset.sum_congr rfl fun i _ ↦ by ring
      have hright : (∑ l, (A₂ (Pi.single l 1) j : ℝ) * z l) =
          -(∑ l, ∑ i, (A₂ (Pi.single l 1) j : ℝ) * (L (A₁ (Pi.single i 1)) l : ℝ) * x i) := by
        simp only [z, mul_neg, Finset.sum_neg_distrib, Finset.mul_sum, mul_assoc]
      rw [hleft, hright]; linarith
    have hxD := (hpointed (fun i ↦ (D : ℝ) * x i) z
      (fun i ↦ mul_nonneg (by positivity) (hx0 i)) hcomb).1
    ext i
    exact (mul_eq_zero.1 (congrFun hxD i)).resolve_left (by positivity : (D : ℝ) ≠ 0)
  obtain ⟨ℓ, hℓ⟩ := exists_pos_linearFunctional_of_pointed PA₁ hPA₁_pointed
  let DPA₁ : (Fin s → ℤ) →+ (Fin u → ℤ) :=
    { toFun := fun x ↦ (D : ℤ) • PA₁ x
      map_zero' := by simp
      map_add' := fun x y ↦ by simp [map_add, smul_add] }
  have hℓD : ∀ i : Fin s, 0 < ℓ (DPA₁ (Pi.single i 1)) := fun i ↦ by
    change 0 < ℓ ((D : ℤ) • PA₁ (Pi.single i 1))
    rw [map_zsmul, zsmul_eq_mul, Int.cast_id]
    exact mul_pos (by positivity) (hℓ i)
  have hDPA₁_pq := vectorPartitionCount_isPiecewiseQuasiPolynomial DPA₁ ℓ hℓD
  let rVec (r : Fin s → Fin D) : Fin s → ℤ := fun i ↦ (r i : ℤ)
  have hcount_eq : ∀ y : Fin d → ℤ,
      (parametricPolytopeCount A₁ A₂ B y : ℚ) =
      ∑ r : Fin s → Fin D,
        if ∀ l : Fin s', (D : ℤ) ∣ L (B y - A₁ (rVec r)) l then
          (vectorPartitionCount DPA₁ (P (B y - A₁ (rVec r))) : ℚ)
        else 0 := by
    intro y
    classical
    norm_cast
    let e₁ : {p : (Fin s → ℕ) × (Fin s' → ℤ) // A₁ (fun i ↦ (p.1 i : ℤ)) + A₂ p.2 = B y} ≃
        {x : Fin s → ℕ // P (B y - A₁ (fun i ↦ (x i : ℤ))) = 0 ∧
          ∀ l : Fin s', (D : ℤ) ∣ L (B y - A₁ (fun i ↦ (x i : ℤ))) l} :=
      { toFun := fun ⟨⟨x, z⟩, hxz⟩ ↦ ⟨x, (hmem_range_A₂ _).1 ⟨z, eq_sub_of_add_eq' hxz⟩⟩
        invFun := fun ⟨x, hx⟩ ↦
          ⟨⟨x, ((hmem_range_A₂ _).2 hx).choose⟩,
            add_eq_of_eq_sub' ((hmem_range_A₂ _).2 hx).choose_spec⟩
        left_inv := fun ⟨⟨x, z⟩, hxz⟩ ↦ by
          apply Subtype.ext; refine Prod.ext rfl ?_; apply hA₂_inj
          have hs := ((hmem_range_A₂ _).2 ((hmem_range_A₂ _).1
            ⟨z, eq_sub_of_add_eq' hxz⟩)).choose_spec
          exact hs.trans (eq_sub_of_add_eq' hxz).symm
        right_inv := fun ⟨x, _⟩ ↦ Subtype.ext rfl }
    let goodR := {r : Fin s → Fin D // ∀ l : Fin s', (D : ℤ) ∣ L (B y - A₁ (rVec r)) l}
    let e₂ : {x : Fin s → ℕ // P (B y - A₁ (fun i ↦ (x i : ℤ))) = 0 ∧
          ∀ l : Fin s', (D : ℤ) ∣ L (B y - A₁ (fun i ↦ (x i : ℤ))) l} ≃
        Σ r : goodR,
          {x' : Fin s → ℕ // DPA₁ (fun i ↦ (x' i : ℤ)) = P (B y - A₁ (rVec r.1))} :=
      { toFun := fun ⟨x, hP, hL⟩ ↦
          let r : Fin s → Fin D := fun i ↦ ⟨x i % D, Nat.mod_lt _ hD⟩
          let x' : Fin s → ℕ := fun i ↦ x i / D
          have hx_split : (fun i ↦ (x i : ℤ)) = (D : ℤ) • (fun i ↦ (x' i : ℤ)) + rVec r := by
            ext i
            rw [Pi.add_apply, Pi.smul_apply, zsmul_eq_mul, Int.cast_id]
            simp only [rVec, x', r]
            exact_mod_cast (Nat.div_add_mod (x i) D).symm
          have hLr : ∀ l : Fin s', (D : ℤ) ∣ L (B y - A₁ (rVec r)) l := by
            intro l
            have h1 : B y - A₁ (fun i ↦ (x i : ℤ)) + (D : ℤ) • A₁ (fun i ↦ (x' i : ℤ)) =
                B y - A₁ (rVec r) := by rw [hx_split, map_add, map_zsmul]; abel
            rw [← h1, map_add, map_zsmul, Pi.add_apply, Pi.smul_apply, zsmul_eq_mul, Int.cast_id]
            exact dvd_add (hL l) (dvd_mul_right _ _)
          ⟨⟨r, hLr⟩, ⟨x', by
            have hP0 : P (B y) - P (A₁ (fun i ↦ (x i : ℤ))) = 0 := by rw [← map_sub]; exact hP
            rw [hx_split, map_add, map_zsmul, map_add, map_zsmul] at hP0
            change (D : ℤ) • P (A₁ (fun i ↦ (x' i : ℤ))) = P (B y - A₁ (rVec r))
            rw [map_sub]
            ext j
            have hj := congrFun hP0 j
            simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, Pi.zero_apply] at hj ⊢
            linarith⟩⟩
        invFun := fun ⟨⟨r, hLr⟩, ⟨x', hx'⟩⟩ ↦
          ⟨fun i ↦ D * x' i + (r i).1,
            by
              have hx_split : (fun i ↦ ((D * x' i + (r i).1 : ℕ) : ℤ)) =
                  (D : ℤ) • (fun i ↦ (x' i : ℤ)) + rVec r := by
                ext i; rw [Pi.add_apply, Pi.smul_apply, zsmul_eq_mul, Int.cast_id]; simp [rVec]
              rw [hx_split, map_sub, map_add, map_zsmul, map_add, map_zsmul]
              change (D : ℤ) • P (A₁ (fun i ↦ (x' i : ℤ))) = P (B y - A₁ (rVec r)) at hx'
              rw [map_sub] at hx'
              rw [hx']; abel,
            by
              intro l
              have hx_split : (fun i ↦ ((D * x' i + (r i).1 : ℕ) : ℤ)) =
                  (D : ℤ) • (fun i ↦ (x' i : ℤ)) + rVec r := by
                ext i; rw [Pi.add_apply, Pi.smul_apply, zsmul_eq_mul, Int.cast_id]; simp [rVec]
              have hsub : L (B y - A₁ (fun i ↦ ((D * x' i + (r i).1 : ℕ) : ℤ))) l =
                  L (B y - A₁ (rVec r)) l - (D : ℤ) * L (A₁ (fun i ↦ (x' i : ℤ))) l := by
                rw [hx_split, map_add, map_zsmul, map_sub, map_add, map_zsmul, map_sub,
                  Pi.sub_apply, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, zsmul_eq_mul,
                  Int.cast_id]
                ring
              rw [hsub]; exact dvd_sub (hLr l) (dvd_mul_right _ _)⟩
        left_inv := fun ⟨x, _, _⟩ ↦ by
          apply Subtype.ext; ext i; exact Nat.div_add_mod (x i) D
        right_inv := fun ⟨⟨r, hLr⟩, ⟨x', hx'⟩⟩ ↦ by
          have hr_eq : (fun i ↦ ⟨(D * x' i + (r i).1) % D, Nat.mod_lt _ hD⟩ : Fin s → Fin D) =
              r := by ext i; simp [Nat.mod_eq_of_lt (r i).2]
          have hx'_eq : (fun i ↦ (D * x' i + (r i).1) / D) = x' := by
            ext i; rw [Nat.mul_add_div hD, Nat.div_eq_of_lt (r i).2, add_zero]
          refine Sigma.ext (Subtype.ext hr_eq) ?_
          exact (Subtype.heq_iff_coe_eq fun _ ↦ by dsimp only; rw [hr_eq]).2 hx'_eq }
    have : ∀ r : goodR,
        Finite {x' : Fin s → ℕ // DPA₁ (fun i ↦ (x' i : ℤ)) = P (B y - A₁ (rVec r.1))} :=
      fun r ↦ finite_vectorPartitionFiber DPA₁ ℓ hℓD _
    unfold parametricPolytopeCount
    rw [Nat.card_congr (e₁.trans e₂), Nat.card_sigma]
    rw [← Finset.sum_filter]
    refine Finset.sum_bij (fun (r : goodR) _ ↦ r.1) ?_ ?_ ?_ ?_
    · intro r _; exact Finset.mem_filter.2 ⟨Finset.mem_univ _, r.2⟩
    · intro r₁ _ r₂ _ h; exact Subtype.ext h
    · intro r hr; exact ⟨⟨r, (Finset.mem_filter.1 hr).2⟩, Finset.mem_univ _, rfl⟩
    · intro r _; rfl
  have hterm : ∀ r : Fin s → Fin D,
      PiecewiseQuasiPolynomial.IsPiecewiseQuasiPolynomial (fun y : Fin d → ℤ ↦
        if ∀ l : Fin s', (D : ℤ) ∣ L (B y - A₁ (rVec r)) l then
          (vectorPartitionCount DPA₁ (P (B y - A₁ (rVec r))) : ℚ)
        else 0) := by
    intro r
    have hcomp := PiecewiseQuasiPolynomial.isPiecewiseQuasiPolynomial_compAffine
      hDPA₁_pq (P.comp B) (-P (A₁ (rVec r)))
    let pred : (Fin d → ZMod D) → Prop := fun z ↦
      ∀ l : Fin s',
        (∑ i : Fin d, ((L (B (Pi.single i 1)) l : ℤ) : ZMod D) * z i) -
          ((L (A₁ (rVec r)) l : ℤ) : ZMod D) = 0
    classical
    have hind := PiecewiseQuasiPolynomial.isPiecewiseQuasiPolynomial_mulPeriodicIndicator
      hD pred hcomp
    rcases hind with ⟨F, hF⟩
    refine ⟨F, fun y ↦ ?_⟩
    rw [hF y]
    have hpred_iff : pred (fun i ↦ (y i : ZMod D)) ↔
        ∀ l : Fin s', (D : ℤ) ∣ L (B y - A₁ (rVec r)) l := by
      refine forall_congr' fun l ↦ ?_
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      have hLB : L (B y - A₁ (rVec r)) l =
          (∑ i : Fin d, L (B (Pi.single i 1)) l * y i) - L (A₁ (rVec r)) l := by
        rw [map_sub, Pi.sub_apply]
        congr 1
        exact QuasiPolynomial.addMonoidHom_fin_apply (L.comp B) y l
      rw [hLB]; push_cast; rfl
    have hPsub : P (B y) + -P (A₁ (rVec r)) = P (B y - A₁ (rVec r)) := by
      rw [map_sub, sub_eq_add_neg]
    simp only [AddMonoidHom.comp_apply, hPsub, hpred_iff]
  have htot := PiecewiseQuasiPolynomial.isPiecewiseQuasiPolynomial_sum
    (Finset.univ : Finset (Fin s → Fin D)) _ (fun r _ ↦ hterm r)
  rcases htot with ⟨F, hF⟩
  exact ⟨F, fun y ↦ by rw [hF y]; dsimp only; rw [← hcount_eq y]⟩

end VectorPartition

end CslibFrontier.Complexity.Polyhedra
