/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FormalPapers Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Complexity.RealAlgebraic.RootIsolation
public import CslibFrontier.Computability.PolyTime.LinearAlgebra.RationalElimination
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Rat
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.ListProd
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
import CslibFrontier.Foundations.Data.Rat.Basic
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Data.List.GetD
import Mathlib.RingTheory.Localization.Rat
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Polynomial-Time Rational Root Finding for Univariate Rational Polynomials

Implements and certifies `findRationalRoots : List ℚ → List ℚ`, computing the duplicate-free list
of all rational roots of `p = Polynomial.ofCoeffList cs ∈ ℚ[X]` in polynomial time on multi-tape
Turing machines (`Turing.MultiTapeTM.ComputableInPolyTime`) under `encRatPoly`:
(1) squarefree part `sqfreePartList` via Sturm GCD + Bareiss `ratSolve`, (2) Rational Root Theorem
denominator bound `denomBoundNat`, (3) Sturm bisection `bisectInterval` on `isolateRootsTotal`,
and (4) Euclidean rational reconstruction `ratReconstruct`.
-/

public section

namespace Cslib.Complexity.RealAlgebraic

open Matrix Polynomial Cslib.RealRoot Cslib.LinearAlgebra
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime

/-! ### Part 1: Squarefree part via Sturm sequence GCD and Bareiss `ratSolve` -/

/-- The trimmed last polynomial in the rational Sturm sequence (associated to `gcd p p'`),
computed via `reverse.headD` and `CoeffList.trim`. -/
def sturmLastList (cs : List ℚ) : List ℚ :=
  CoeffList.trim ((sturmSeqList cs).reverse.headD [])

/-- The Toeplitz linear system `g * q = t` for dividing trimmed `t` by trimmed `g`. -/
def toeplitzSystem (g t : List ℚ) : LinearSystemInput :=
  let numCols := t.length - g.length + 1
  let rows := (List.range t.length).map fun i =>
    (List.range numCols).map fun j => if j ≤ i then g.getD (i - j) 0 else 0
  { matrix := { numRows := t.length, numCols := numCols, rows := rows }, rhs := t }

/-- Computable squarefree part `p / gcd(p, p')` of a rational coefficient list `cs`. -/
def sqfreePartList (cs : List ℚ) : List ℚ :=
  let t := CoeffList.trim cs
  if t.isEmpty then []
  else
    let g := sturmLastList cs
    let sol := ((ratSolve (toeplitzSystem g t)).solution).getD []
    CoeffList.trim sol

private theorem sturmSeq_last_dvd_iff {K : Type*} [Field K] [DecidableEq K] :
    ∀ (m : ℕ) (p q : K[X]), (if q = 0 then 0 else q.natDegree + 1) ≤ m → p ≠ 0 →
      ∀ (g : K[X]), (sturmSeq p q).getLast? = some g →
        ∀ d : K[X], (d ∣ p ∧ d ∣ q) ↔ d ∣ g
  | m, p, q, hm, hp, g, hlast, d => by
    by_cases hq : q = 0
    · subst hq
      rw [sturmSeq_zero_right] at hlast
      simp only [hp, ↓reduceIte] at hlast
      simp only [List.getLast?_singleton, Option.some.injEq] at hlast
      subst hlast
      simp
    · obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := by
        simp only [hq, ↓reduceIte] at hm
        exact Nat.exists_eq_succ_of_ne_zero (by omega)
      rw [sturmSeq_cons hp] at hlast
      have hne : sturmSeq q (-p % q) ≠ [] := by
        rw [ne_eq, sturmSeq_eq_nil_iff]; exact hq
      rw [List.getLast?_cons_of_ne_nil hne] at hlast
      have hmeas : (if -p % q = 0 then 0 else (-p % q).natDegree + 1) ≤ k := by
        simp only [hq, ↓reduceIte] at hm
        split_ifs with hr
        · exact Nat.zero_le k
        · have hlt := Polynomial.degree_mod_lt (-p) hq
          have hnat := (Polynomial.natDegree_lt_iff_degree_lt hr).mpr
            (by rwa [← Polynomial.degree_eq_natDegree hq])
          omega
      have ih := sturmSeq_last_dvd_iff k q (-p % q) hmeas hq g hlast d
      rw [← ih]
      constructor
      · rintro ⟨hdp, hdq⟩
        refine ⟨hdq, ?_⟩
        have hdiv : -p = q * (-p / q) + -p % q := (EuclideanDomain.div_add_mod (-p) q).symm
        have hmod : -p % q = -p - q * (-p / q) := by
          apply eq_sub_of_add_eq'
          exact hdiv.symm
        rw [hmod]
        exact dvd_sub (dvd_neg.mpr hdp) (dvd_mul_of_dvd_left hdq _)
      · rintro ⟨hdq, hdr⟩
        refine ⟨?_, hdq⟩
        have hdiv : -p = q * (-p / q) + -p % q := (EuclideanDomain.div_add_mod (-p) q).symm
        have hneg : d ∣ -p := hdiv ▸ dvd_add (dvd_mul_of_dvd_left hdq _) hdr
        exact dvd_neg.mp hneg

private theorem sturmLastList_spec {cs : List ℚ} (hcs : ofCoeffList cs ≠ 0) :
    let g := ofCoeffList (sturmLastList cs)
    g ≠ 0 ∧ ∀ d : ℚ[X], (d ∣ ofCoeffList cs ∧ d ∣ derivative (ofCoeffList cs)) ↔ d ∣ g := by
  have hmap := sturmSeqList_map_ofCoeffList cs
  have hne : sturmSeq (ofCoeffList cs) (derivative (ofCoeffList cs)) ≠ [] := by
    rw [ne_eq, sturmSeq_eq_nil_iff]; exact hcs
  have hseq_ne : sturmSeqList cs ≠ [] := fun h => hne (by rw [← hmap, h, List.map_nil])
  have hlast_mem : (sturmSeqList cs).reverse.headD [] ∈ sturmSeqList cs := by
    rw [List.headD_eq_head?_getD, ← List.getLast?_eq_head?_reverse,
      List.getLast?_eq_some_getLast hseq_ne, Option.getD_some]
    exact List.getLast_mem hseq_ne
  have hlast_some : (sturmSeq (ofCoeffList cs) (derivative (ofCoeffList cs))).getLast? =
      some (ofCoeffList (sturmLastList cs)) := by
    rw [← hmap, List.getLast?_map, List.getLast?_eq_some_getLast hseq_ne, Option.map_some]
    congr 1
    rw [sturmLastList, CoeffList.ofCoeffList_trim, List.headD_eq_head?_getD,
      ← List.getLast?_eq_head?_reverse, List.getLast?_eq_some_getLast hseq_ne, Option.getD_some]
  have hlast_eq :
      ofCoeffList (sturmLastList cs) = ofCoeffList ((sturmSeqList cs).reverse.headD []) :=
    CoeffList.ofCoeffList_trim _
  refine ⟨hlast_eq ▸ ne_zero_of_mem_sturmSeq (hmap ▸ List.mem_map_of_mem hlast_mem), ?_⟩
  exact sturmSeq_last_dvd_iff _ _ _ le_rfl hcs _ hlast_some

private theorem exists_pow_factor {v : ℚ[X]} (hv : Irreducible v) :
    ∀ (f : ℚ[X]), f ≠ 0 → ∃ (m : ℕ) (h : ℚ[X]), f = v ^ m * h ∧ ¬ v ∣ h := by
  intro f
  suffices ∀ (d : ℕ) (f : ℚ[X]), f.natDegree ≤ d → f ≠ 0 →
      ∃ (m : ℕ) (h : ℚ[X]), f = v ^ m * h ∧ ¬ v ∣ h from fun hf => this f.natDegree f le_rfl hf
  intro d
  induction d with
  | zero =>
    intro f hdeg hf
    refine ⟨0, f, by simp, fun hdvd => ?_⟩
    have hv_deg : 0 < v.natDegree := by
      by_contra h0
      have hc := Polynomial.eq_C_of_natDegree_eq_zero (show v.natDegree = 0 by omega)
      have hv0 : v.coeff 0 ≠ 0 := fun h => hv.ne_zero (by rw [hc, h, C_0])
      exact hv.not_isUnit (by rw [hc]; exact Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hv0))
    have hle := Polynomial.natDegree_le_of_dvd hdvd hf
    omega
  | succ d ih =>
    intro f hdeg hf
    by_cases hvd : v ∣ f
    · obtain ⟨f', rfl⟩ := hvd
      have hf'0 : f' ≠ 0 := right_ne_zero_of_mul hf
      have hv_deg : 0 < v.natDegree := by
        by_contra h0
        have hc := Polynomial.eq_C_of_natDegree_eq_zero (show v.natDegree = 0 by omega)
        have hv0 : v.coeff 0 ≠ 0 := fun h => hv.ne_zero (by rw [hc, h, C_0])
        exact hv.not_isUnit (by rw [hc]; exact Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hv0))
      have hdeg' : f'.natDegree ≤ d := by
        have hm := Polynomial.natDegree_mul hv.ne_zero hf'0
        omega
      obtain ⟨m, h, heq, hnot⟩ := ih f' hdeg' hf'0
      refine ⟨m + 1, h, ?_, hnot⟩
      rw [heq, pow_succ']; ring
    · exact ⟨0, f, by simp, hvd⟩

private theorem toeplitz_mulVec_eq_coeff (g t sol : List ℚ)
    (hsol : sol.length = (toeplitzSystem g t).matrix.numCols) :
    ((toeplitzSystem g t).matrix.toMatrix *ᵥ fun j : Fin (toeplitzSystem g t).matrix.numCols =>
        sol.getD j.val 0) =
      (fun i : Fin (toeplitzSystem g t).matrix.numRows => t.getD i.val 0) ↔
    (∀ i < t.length, (ofCoeffList g * ofCoeffList sol).coeff i = t.getD i 0) := by
  let sys := toeplitzSystem g t
  have h1 : ∀ (i : ℕ) (hi : i < t.length) (j : Fin sys.matrix.numCols),
      sys.matrix.toMatrix ⟨i, hi⟩ j * sol.getD j.val 0 =
        if j.val ≤ i then (ofCoeffList g).coeff (i - j.val) * (ofCoeffList sol).coeff j.val
        else 0 := fun i hi j => by
    rw [Cslib.RowTable.toMatrix_apply, Cslib.RowTable.entry]
    have hj' : j.val < t.length - g.length + 1 := j.isLt
    simp only [sys, toeplitzSystem, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range hi, List.getElem?_range hj', Option.map_some, Option.getD_some]
    split_ifs with hji
    · rw [Polynomial.coeff_ofCoeffList, Polynomial.coeff_ofCoeffList]
      simp only [List.getD_eq_getElem?_getD]
    · simp
  have hrow_eq : ∀ (i : ℕ) (hi : i < t.length),
      (sys.matrix.toMatrix *ᵥ fun j : Fin sys.matrix.numCols => sol.getD j.val 0) ⟨i, hi⟩ =
        (ofCoeffList g * ofCoeffList sol).coeff i := fun i hi => by
    rw [Matrix.mulVec, dotProduct]
    simp_rw [h1 i hi]
    rw [Fin.sum_univ_eq_sum_range (fun j => if j ≤ i then
      (ofCoeffList g).coeff (i - j) * (ofCoeffList sol).coeff j else 0), ← Finset.sum_filter]
    have hfilt : (Finset.range sys.matrix.numCols).filter (· ≤ i) =
        (Finset.range (i + 1)).filter (· < sys.matrix.numCols) := by
      ext x; simp only [Finset.mem_filter, Finset.mem_range]; omega
    rw [hfilt, Finset.sum_filter, Polynomial.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun u v => (ofCoeffList g).coeff u * (ofCoeffList sol).coeff v) i]
    have hrev : ∑ x ∈ Finset.range (i + 1),
        (ofCoeffList g).coeff x * (ofCoeffList sol).coeff (i - x) =
        ∑ x ∈ Finset.range (i + 1),
          (ofCoeffList g).coeff (i - x) * (ofCoeffList sol).coeff x := by
      rw [← Finset.sum_range_reflect
        (fun x => (ofCoeffList g).coeff (i - x) * (ofCoeffList sol).coeff x) (i + 1)]
      refine Finset.sum_congr rfl fun x hx => ?_
      have hx' := Finset.mem_range.mp hx
      simp [show i - (i - x) = x by omega]
    rw [hrev]
    refine Finset.sum_congr rfl fun x _ => ?_
    split_ifs with hlt
    · rfl
    · have hsol_len : sol.length = sys.matrix.numCols := hsol
      have hzero : (ofCoeffList sol).coeff x = 0 := by
        rw [Polynomial.coeff_ofCoeffList, List.getD_eq_getElem?_getD,
          List.getElem?_eq_none (by omega), Option.getD_none]
      rw [hzero, mul_zero]
  constructor
  · intro h i hi
    rw [← hrow_eq i hi, h]
  · intro h
    ext ⟨i, hi⟩
    rw [hrow_eq i hi, h i hi]

/-- Specification of `sqfreePartList`: for any nonzero polynomial `p = ofCoeffList cs`,
`sq = ofCoeffList (sqfreePartList cs)` is squarefree, divides `p` via `g`, and has the exact
same rational roots as `p`. -/
theorem sqfreePartList_spec {cs : List ℚ} (hcs : ofCoeffList cs ≠ 0) :
    let sq := ofCoeffList (sqfreePartList cs)
    let g := ofCoeffList (sturmLastList cs)
    g * sq = ofCoeffList cs ∧ Squarefree sq ∧
      ∀ r : ℚ, sq.eval r = 0 ↔ (ofCoeffList cs).eval r = 0 := by
  intro sq g
  set t := CoeffList.trim cs
  have ht_ne : t ≠ [] := mt (CoeffList.trim_eq_nil_iff cs).mp hcs
  have ht_empty : t.isEmpty = false := List.isEmpty_eq_false_iff.mpr ht_ne
  obtain ⟨hg_ne, hg_dvd⟩ := sturmLastList_spec hcs
  have hg_dvd_p : g ∣ ofCoeffList cs := (hg_dvd g).mpr dvd_rfl |>.1
  obtain ⟨q0, hq0⟩ := hg_dvd_p
  have hq0_ne : q0 ≠ 0 := fun h0 => hcs (by rw [hq0, h0, mul_zero])
  have hg_mem : (sturmSeqList cs).reverse.headD [] ∈ sturmSeqList cs := by
    have hmap := sturmSeqList_map_ofCoeffList cs
    have hne : sturmSeq (ofCoeffList cs) (derivative (ofCoeffList cs)) ≠ [] := by
      rw [ne_eq, sturmSeq_eq_nil_iff]; exact hcs
    have hseq_ne : sturmSeqList cs ≠ [] := fun h => hne (by rw [← hmap, h, List.map_nil])
    rw [List.headD_eq_head?_getD, ← List.getLast?_eq_head?_reverse,
      List.getLast?_eq_some_getLast hseq_ne, Option.getD_some]
    exact List.getLast_mem hseq_ne
  have hg_len : (sturmLastList cs).length ≤ t.length :=
    (CoeffList.length_trim_le _).trans (sturmSeqList_entry_length_le cs hg_mem)
  have hg_trim : CoeffList.IsTrimmed (sturmLastList cs) := CoeffList.isTrimmed_trim _
  have hq0_deg : q0.natDegree ≤ t.length - (sturmLastList cs).length := by
    have ht_len : t.length = (ofCoeffList cs).natDegree + 1 :=
      CoeffList.length_trim_eq_natDegree_add_one hcs
    have hg_deg : (sturmLastList cs).length = g.natDegree + 1 := by
      have := CoeffList.length_trim_eq_natDegree_add_one hg_ne
      rwa [hg_trim.trim_eq] at this
    have hmul_deg : (g * q0).natDegree = g.natDegree + q0.natDegree :=
      Polynomial.natDegree_mul hg_ne hq0_ne
    rw [← hq0] at hmul_deg
    omega
  have hsys_ex : ∃ x : Fin (toeplitzSystem (sturmLastList cs) t).matrix.numCols → ℚ,
      (toeplitzSystem (sturmLastList cs) t).matrix.toMatrix *ᵥ x =
        fun i => t.getD i.val 0 := by
    let sol0 : List ℚ := (List.range (t.length - (sturmLastList cs).length + 1)).map q0.coeff
    have hsol0_len : sol0.length = (toeplitzSystem (sturmLastList cs) t).matrix.numCols := by
      simp [sol0, toeplitzSystem]
    refine ⟨fun j => sol0.getD j.val 0, ?_⟩
    rw [toeplitz_mulVec_eq_coeff _ _ _ hsol0_len]
    intro i hi
    have hq0_eq : ofCoeffList sol0 = q0 := by
      ext r
      rw [Polynomial.coeff_ofCoeffList]
      by_cases hr : r < t.length - (sturmLastList cs).length + 1
      · simp only [sol0, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hr,
          Option.map_some, Option.getD_some]
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp [sol0]; omega),
          Option.getD_none]
        symm
        exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    rw [hq0_eq, ← hq0, ← CoeffList.ofCoeffList_trim cs, Polynomial.coeff_ofCoeffList]
  have hsol_some : ∃ sol : List ℚ,
      (ratSolve (toeplitzSystem (sturmLastList cs) t)).solution = some sol := by
    cases h : (ratSolve (toeplitzSystem (sturmLastList cs) t)).solution with
    | none => exact absurd hsys_ex ((ratSolve_spec _).2.mp h)
    | some sol => exact ⟨sol, rfl⟩
  obtain ⟨sol, hsol_eq⟩ := hsol_some
  obtain ⟨hsol_len, hsol_mv⟩ := (ratSolve_spec _).1 sol hsol_eq
  have hsq_def : sqfreePartList cs = CoeffList.trim sol := by
    simp [sqfreePartList, t, ht_empty, hsol_eq]
  have hmul : g * sq = ofCoeffList cs := by
    have hcoeff_all : ∀ i < t.length, (g * ofCoeffList sol).coeff i = t.getD i 0 :=
      (toeplitz_mulVec_eq_coeff _ _ _ hsol_len).mp hsol_mv
    have hdeg_gs : (g * ofCoeffList sol).natDegree < t.length := by
      have hg_deg : g.natDegree ≤ (sturmLastList cs).length - 1 := natDegree_ofCoeffList_le _
      have hs_deg : (ofCoeffList sol).natDegree ≤ sol.length - 1 := natDegree_ofCoeffList_le _
      have hsol_len' : sol.length = t.length - (sturmLastList cs).length + 1 := hsol_len
      have hlen_pos : 1 ≤ (sturmLastList cs).length :=
        List.length_pos_of_ne_nil (fun h => hg_ne (by simp [h]))
      have h1 : (g * ofCoeffList sol).natDegree ≤ g.natDegree + (ofCoeffList sol).natDegree :=
        Polynomial.natDegree_mul_le
      omega
    ext i
    rw [show sq = ofCoeffList sol from by dsimp only [sq]; rw [hsq_def, CoeffList.ofCoeffList_trim]]
    by_cases hi : i < t.length
    · rw [hcoeff_all i hi, ← Polynomial.coeff_ofCoeffList, CoeffList.ofCoeffList_trim]
    · have hi' : (CoeffList.trim cs).length ≤ i := by dsimp only [t] at hi; omega
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega),
        ← CoeffList.ofCoeffList_trim cs, Polynomial.coeff_ofCoeffList,
        List.getD_eq_getElem?_getD, List.getElem?_eq_none hi', Option.getD_none]
  have hsq_ne : sq ≠ 0 := fun h0 => hcs (by rw [← hmul, h0, mul_zero])
  have hsq_free : Squarefree sq := by
    intro v hv_sq
    by_contra hnu
    have hv0 : v ≠ 0 :=
      fun h0 => hsq_ne (zero_dvd_iff.mp (by rw [h0, mul_zero] at hv_sq; exact hv_sq))
    obtain ⟨u, hu_irr, huv⟩ := WfDvdMonoid.exists_irreducible_factor hnu hv0
    have hv_sq2 : v ^ 2 ∣ sq := by rwa [_root_.sq]
    have hu_sq2 : u ^ 2 ∣ sq := dvd_trans (pow_dvd_pow_of_dvd huv 2) hv_sq2
    obtain ⟨m, h, hg_eq, hu_not_h⟩ := exists_pow_factor hu_irr g hg_ne
    have ⟨w, hsq_eq⟩ := hu_sq2
    have hp_eq : ofCoeffList cs = u ^ (m + 2) * (h * w) := by
      rw [← hmul, hg_eq, hsq_eq, pow_add]; ring
    have hpow_dp : u ^ (m + 1) ∣ derivative (ofCoeffList cs) := by
      rw [hp_eq, derivative_mul, derivative_pow]
      refine dvd_add ?_ ?_
      · rw [show m + 2 - 1 = m + 1 by omega]
        exact ⟨C ((m + 2 : ℕ) : ℚ) * derivative u * (h * w), by ring⟩
      · exact ⟨u * derivative (h * w), by rw [pow_succ]; ring⟩
    have hh_dp : h ∣ derivative (ofCoeffList cs) :=
      dvd_trans ⟨u ^ m, by rw [hg_eq, mul_comm]⟩ ((hg_dvd g).mpr dvd_rfl).2
    have hcop_uh : IsCoprime (u ^ (m + 1)) h :=
      (hu_irr.coprime_iff_not_dvd.mpr hu_not_h).pow_left
    have hgv_dp : g * u ∣ derivative (ofCoeffList cs) := by
      have hprod : u ^ (m + 1) * h ∣ derivative (ofCoeffList cs) :=
        hcop_uh.mul_dvd hpow_dp hh_dp
      have heq : u ^ (m + 1) * h = g * u := by rw [hg_eq, pow_succ]; ring
      rwa [heq] at hprod
    have hgv_p : g * u ∣ ofCoeffList cs := by
      rw [← hmul]
      exact mul_dvd_mul_left g (dvd_trans (dvd_pow_self u two_ne_zero) hu_sq2)
    have hgv_g : g * u ∣ g := (hg_dvd (g * u)).mp ⟨hgv_p, hgv_dp⟩
    obtain ⟨c, hc⟩ := hgv_g
    have huc : u * c = 1 := mul_left_cancel₀ hg_ne (by rw [← mul_assoc, ← hc, mul_one])
    exact hu_irr.not_isUnit (isUnit_iff_exists_inv.mpr ⟨c, huc⟩)
  refine ⟨hmul, hsq_free, fun r => ?_⟩
  constructor
  · intro hr
    rw [← hmul, Polynomial.eval_mul, hr, mul_zero]
  · intro hr
    by_contra hne
    have hirr : Irreducible (X - C r) := Polynomial.irreducible_X_sub_C r
    obtain ⟨m, w, hp_eq, hnot_w⟩ := exists_pow_factor hirr (ofCoeffList cs) hcs
    have hm_pos : 1 ≤ m := by
      by_contra h0
      have hm0 : m = 0 := by omega
      rw [hm0, pow_zero, one_mul] at hp_eq
      exact hnot_w (Polynomial.dvd_iff_isRoot.mpr (hp_eq ▸ hr))
    have hpow_g : (X - C r) ^ m ∣ g := by
      have hpow_p : (X - C r) ^ m ∣ g * sq := ⟨w, by rw [hmul, hp_eq]⟩
      have hcop_r : IsCoprime ((X - C r) ^ m) sq :=
        (hirr.coprime_iff_not_dvd.mpr (Polynomial.dvd_iff_isRoot.not.mpr hne)).pow_left
      exact hcop_r.dvd_of_dvd_mul_right hpow_p
    have hpow_dp : (X - C r) ^ m ∣ derivative (ofCoeffList cs) :=
      dvd_trans hpow_g ((hg_dvd g).mpr dvd_rfl).2
    have hdp_eq : derivative (ofCoeffList cs) =
        C (m : ℚ) * (X - C r) ^ (m - 1) * w + (X - C r) ^ m * derivative w := by
      rw [hp_eq, derivative_mul, derivative_pow, derivative_sub, derivative_X, derivative_C,
        sub_zero, mul_one]
    have hdvd_first : (X - C r) ^ m ∣ C (m : ℚ) * (X - C r) ^ (m - 1) * w := by
      have : C (m : ℚ) * (X - C r) ^ (m - 1) * w =
          derivative (ofCoeffList cs) - (X - C r) ^ m * derivative w := by
        rw [hdp_eq]; ring
      rw [this]
      exact dvd_sub hpow_dp (dvd_mul_right _ _)
    obtain ⟨c, hc⟩ := hdvd_first
    have hsplit : (X - C r) ^ m = (X - C r) ^ (m - 1) * (X - C r) := by
      conv_lhs => rw [show m = (m - 1) + 1 by omega, pow_succ]
    have hpow_ne : ((X - C r) ^ (m - 1) : ℚ[X]) ≠ 0 := pow_ne_zero _ (Polynomial.X_sub_C_ne_zero r)
    have hcmw : (X - C r) ∣ C (m : ℚ) * w := by
      refine ⟨c, ?_⟩
      apply mul_left_cancel₀ hpow_ne
      calc (X - C r) ^ (m - 1) * (C (m : ℚ) * w)
          = C (m : ℚ) * (X - C r) ^ (m - 1) * w := by ring
        _ = (X - C r) ^ m * c := hc
        _ = (X - C r) ^ (m - 1) * ((X - C r) * c) := by rw [hsplit]; ring
    have hm_ne : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hdw : (X - C r) ∣ w := by
      obtain ⟨d, hd⟩ := hcmw
      refine ⟨C ((m : ℚ)⁻¹) * d, ?_⟩
      have hmul' := congrArg (C ((m : ℚ)⁻¹) * ·) hd
      have hmul'' : w = C ((m : ℚ)⁻¹) * ((X - C r) * d) := by
        simpa only [← mul_assoc, ← C_mul, inv_mul_cancel₀ hm_ne, C_1, one_mul] using hmul'
      rw [hmul'']; ring
    exact hnot_w hdw

/-! ### Part 2: Rational Root Theorem denominator bound -/

/-- Denominator upper bound `H` for any rational root of `ofCoeffList sq`:
`max 1 (|(sq.getLastD 0).num| * ∏ c ∈ sq, c.den)`. -/
def denomBoundNat (sq : List ℚ) : ℕ :=
  max 1 ((sq.reverse.headD 0).num.natAbs * (sq.map (·.den)).prod)

theorem one_le_denomBoundNat (sq : List ℚ) : 1 ≤ denomBoundNat sq :=
  le_max_left 1 _

theorem den_le_denomBoundNat_of_isRoot {sq : List ℚ} (hsq : ofCoeffList sq ≠ 0)
    (htrim : CoeffList.IsTrimmed sq) {r : ℚ} (hr : (ofCoeffList sq).eval r = 0) :
    r.den ≤ denomBoundNat sq := by
  let D : ℕ := (sq.map (·.den)).prod
  have hD_pos : 0 < D := List.prod_pos fun d hd => by
    obtain ⟨q, _, rfl⟩ := List.mem_map.mp hd
    exact q.den_pos
  have hdvd_D : ∀ q ∈ sq, q.den ∣ D := fun q hq =>
    List.dvd_prod (List.mem_map.mpr ⟨q, hq, rfl⟩)
  let ns : List ℤ := sq.map fun q => q.num * ((D / q.den : ℕ) : ℤ)
  have hmap_aux : ∀ l : List ℚ, (∀ q ∈ l, q.den ∣ D) →
      (ofCoeffList (l.map fun q => q.num * ((D / q.den : ℕ) : ℤ))).map (algebraMap ℤ ℚ) =
        C (D : ℚ) * ofCoeffList l := fun l => by
    induction l with
    | nil => intro _; simp
    | cons q qs ih =>
      intro hd
      simp only [List.map_cons, ofCoeffList_cons, Polynomial.map_add, Polynomial.map_C,
        Polynomial.map_mul, Polynomial.map_X]
      have hcast_div : ((D / q.den : ℕ) : ℚ) = (D : ℚ) / (q.den : ℚ) := by
        rw [eq_div_iff (by exact_mod_cast q.den_nz)]
        exact_mod_cast Nat.div_mul_cancel (hd q List.mem_cons_self)
      have hterm : ((q.num * ((D / q.den : ℕ) : ℤ) : ℤ) : ℚ) = (D : ℚ) * q := by
        rw [Int.cast_mul, Int.cast_natCast, hcast_div, mul_div_assoc',
          mul_comm (q.num : ℚ) (D : ℚ), mul_div_assoc, Rat.num_div_den]
      change C ((q.num * ((D / q.den : ℕ) : ℤ) : ℤ) : ℚ) +
          X * (ofCoeffList (qs.map _)).map (algebraMap ℤ ℚ) =
        C (D : ℚ) * (C q + X * ofCoeffList qs)
      rw [hterm, ih (fun a ha => hd a (List.mem_cons_of_mem q ha)), C_mul]
      ring
  have hmap : (ofCoeffList ns).map (algebraMap ℤ ℚ) = C (D : ℚ) * ofCoeffList sq :=
    hmap_aux sq hdvd_D
  have haeval : Polynomial.aeval r (ofCoeffList ns) = 0 := by
    rw [Polynomial.aeval_def, ← Polynomial.eval_map, hmap, Polynomial.eval_mul, hr, mul_zero]
  have hden_dvd' : ((IsFractionRing.den ℤ r : ℤ)) ∣ (ofCoeffList ns).leadingCoeff :=
    den_dvd_of_is_root haeval
  have hlc_ne : (ofCoeffList ns).leadingCoeff ≠ 0 := by
    rw [Polynomial.leadingCoeff_ne_zero]
    intro h0
    have hD0 : (D : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hD_pos.ne'
    rw [h0, Polynomial.map_zero] at hmap
    exact mul_ne_zero (C_ne_zero.mpr hD0) hsq hmap.symm
  have hlc_eq : ((ofCoeffList ns).leadingCoeff : ℚ) = (D : ℚ) * (ofCoeffList sq).leadingCoeff := by
    have h1 := congrArg Polynomial.leadingCoeff hmap
    rw [Polynomial.leadingCoeff_map_of_injective
        (show Function.Injective (algebraMap ℤ ℚ) from Int.cast_injective),
      Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C] at h1
    exact h1
  have hsq_lc : (ofCoeffList sq).leadingCoeff = sq.reverse.headD 0 := by
    rw [htrim.leadingCoeff_ofCoeffList, List.getLastD_eq_getLast?, List.headD_eq_head?_getD,
      List.getLast?_eq_head?_reverse]
  have hlc_nat : (ofCoeffList ns).leadingCoeff.natAbs ≤
      (sq.reverse.headD 0).num.natAbs * D := by
    have hrat_eq : ((ofCoeffList ns).leadingCoeff : ℚ) =
        ((sq.reverse.headD 0).num : ℚ) * ((D / (sq.reverse.headD 0).den : ℕ) : ℚ) := by
      rw [hlc_eq, hsq_lc]
      have hsq_ne : sq ≠ [] := fun h => hsq (by simp [h])
      have hmem : sq.reverse.headD 0 ∈ sq := by
        rw [List.headD_eq_head?_getD, ← List.getLast?_eq_head?_reverse,
          List.getLast?_eq_some_getLast hsq_ne, Option.getD_some]
        exact List.getLast_mem hsq_ne
      have hcast_div : ((D / (sq.reverse.headD 0).den : ℕ) : ℚ) =
          (D : ℚ) / ((sq.reverse.headD 0).den : ℚ) := by
        rw [eq_div_iff (by exact_mod_cast (sq.reverse.headD 0).den_nz)]
        exact_mod_cast Nat.div_mul_cancel (hdvd_D _ hmem)
      rw [hcast_div, mul_div_assoc', mul_comm ((sq.reverse.headD 0).num : ℚ) (D : ℚ),
        mul_div_assoc, Rat.num_div_den]
    have hint_eq : (ofCoeffList ns).leadingCoeff =
        (sq.reverse.headD 0).num * ((D / (sq.reverse.headD 0).den : ℕ) : ℤ) := by
      rw [show ((D / (sq.reverse.headD 0).den : ℕ) : ℚ) =
          (((D / (sq.reverse.headD 0).den : ℕ) : ℤ) : ℚ) from (Int.cast_natCast _).symm,
        ← Int.cast_mul] at hrat_eq
      exact Int.cast_injective hrat_eq
    rw [hint_eq, Int.natAbs_mul, Int.natAbs_natCast]
    exact Nat.mul_le_mul_left _ (Nat.div_le_self D _)
  have hdvd_nat : r.den ∣ (ofCoeffList ns).leadingCoeff.natAbs := by
    rw [← Rat.isFractionRingDen r]
    exact Int.natAbs_dvd_natAbs.mpr hden_dvd'
  exact ((Nat.le_of_dvd (Int.natAbs_pos.mpr hlc_ne) hdvd_nat).trans hlc_nat).trans
    (le_max_right 1 _)

/-! ### Part 3: Sturm bisection to width `< 1 / (4 * H^2)` -/

/-- One Sturm bisection step on `(a, b]`: keep the half containing the unique root. -/
def bisectStep (seq : List (List ℚ)) (ab : ℚ × ℚ) : ℚ × ℚ :=
  let m := (ab.1 + ab.2) / 2
  if sturmVariationsList seq ab.1 = sturmVariationsList seq m then (m, ab.2)
  else (ab.1, m)

/-- Refine isolating interval `J` by `steps` Sturm bisection steps. -/
def bisectInterval (seq : List (List ℚ)) (steps : ℕ) (J : RootInterval) : ℚ × ℚ :=
  (bisectStep seq)^[steps] (J.lower, J.upper)

/-- Number of bisection steps needed to shrink the isolating-interval width below
`1 / (4 * H^2)`. -/
def refineStepsNat (sq : List ℚ) : ℕ :=
  let H := denomBoundNat sq
  (8 * cauchyBoundNat sq * H ^ 2).size + 3 * mignotteBisectionDepth sq + 3

/-! ### Part 4: Euclidean rational reconstruction -/

/-- State of the bounded Euclidean rational-reconstruction loop. -/
structure EuclidReconState where
  /-- Current Euclidean remainder `a₀`. -/
  a0 : ℕ
  /-- Next Euclidean remainder `a₁`. -/
  a1 : ℕ
  /-- Convergent numerator `p₀`. -/
  p0 : ℕ
  /-- Convergent denominator `q₀`. -/
  q0 : ℕ
  /-- Convergent numerator `p₁`. -/
  p1 : ℕ
  /-- Convergent denominator `q₁`. -/
  q1 : ℕ

/-- One step of the bounded Euclidean rational-reconstruction loop with denominator ceiling `H2`. -/
def euclidReconStep (H2 : ℕ) (st : EuclidReconState) : EuclidReconState :=
  if st.a1 = 0 then st
  else
    let m := st.a0 / st.a1
    let q2 := m * st.q1 + st.q0
    if H2 < q2 then st
    else { a0 := st.a1, a1 := st.a0 % st.a1, p0 := st.p1, q0 := st.q1,
           p1 := m * st.p1 + st.p0, q1 := q2 }

/-- Recover a nonnegative rational with denominator `≤ H` within `< 1 / (4 * H^2)` of `A / B`. -/
def ratReconstructNonneg (H A B : ℕ) : ℚ :=
  let st := (euclidReconStep (2 * H))^[2 * (A.size + B.size + 2)]
    { a0 := A, a1 := B, p0 := 0, q0 := 1, p1 := 1, q1 := 0 }
  (st.p1 : ℚ) / (st.q1 : ℚ)

/-- Recover a rational with denominator `≤ H` within `< 1 / (4 * H^2)` of `x : ℚ`. -/
def ratReconstruct (H : ℕ) (x : ℚ) : ℚ :=
  let r := ratReconstructNonneg H x.num.natAbs x.den
  if 0 ≤ x then r else -r

private def EuclidInv (A B H2 : ℕ) (st : EuclidReconState) : Prop :=
  st.p1 * st.a0 + st.p0 * st.a1 = A ∧ st.q1 * st.a0 + st.q0 * st.a1 = B ∧
  ((st.q1 : ℤ) * (st.p0 : ℤ) - (st.p1 : ℤ) * (st.q0 : ℤ)) ^ 2 = 1 ∧ st.q1 ≤ H2 ∧
  st.a0 ≤ A + B ∧ st.a1 ≤ A + B ∧ st.p0 ≤ A + 1 ∧ st.p1 ≤ A + 1 ∧
  st.q0 ≤ B + 1 ∧ st.q1 ≤ B + 1

private theorem euclidInv_init {A B H : ℕ} (hH : 1 ≤ H) :
    EuclidInv A B (2 * H) { a0 := A, a1 := B, p0 := 0, q0 := 1, p1 := 1, q1 := 0 } := by
  dsimp only [EuclidInv]
  refine ⟨by ring, by ring, by norm_num, by omega, by omega, by omega, by omega, by omega,
    by omega, by omega⟩

private theorem euclidReconStep_inv {A B H2 : ℕ} {st : EuclidReconState}
    (hinv : EuclidInv A B H2 st) :
    EuclidInv A B H2 (euclidReconStep H2 st) := by
  obtain ⟨hp, hq, hdet, hq1_le, ha0, ha1, hp0, hp1, hq0, hq1B⟩ := hinv
  unfold euclidReconStep
  by_cases h0 : st.a1 = 0
  · simp only [h0, ↓reduceIte]
    exact ⟨hp, hq, hdet, hq1_le, ha0, ha1, hp0, hp1, hq0, hq1B⟩
  · simp only [h0, ↓reduceIte]
    set m := st.a0 / st.a1
    set a2 := st.a0 % st.a1
    set p2 := m * st.p1 + st.p0
    set q2 := m * st.q1 + st.q0
    by_cases hlt : H2 < q2
    · simp only [hlt, ↓reduceIte]
      exact ⟨hp, hq, hdet, hq1_le, ha0, ha1, hp0, hp1, hq0, hq1B⟩
    · simp only [hlt, ↓reduceIte]
      have hdiv : m * st.a1 + a2 = st.a0 := Nat.div_add_mod' st.a0 st.a1
      have hp' : p2 * st.a1 + st.p1 * a2 = A := by
        calc p2 * st.a1 + st.p1 * a2 = st.p1 * (m * st.a1 + a2) + st.p0 * st.a1 := by
                dsimp only [p2]; ring
          _ = st.p1 * st.a0 + st.p0 * st.a1 := by rw [hdiv]
          _ = A := hp
      have hq' : q2 * st.a1 + st.q1 * a2 = B := by
        calc q2 * st.a1 + st.q1 * a2 = st.q1 * (m * st.a1 + a2) + st.q0 * st.a1 := by
                dsimp only [q2]; ring
          _ = st.q1 * st.a0 + st.q0 * st.a1 := by rw [hdiv]
          _ = B := hq
      have hdet' : ((q2 : ℤ) * (st.p1 : ℤ) - (p2 : ℤ) * (st.q1 : ℤ)) ^ 2 = 1 := by
        have hEq : (q2 : ℤ) * (st.p1 : ℤ) - (p2 : ℤ) * (st.q1 : ℤ) =
            -((st.q1 : ℤ) * (st.p0 : ℤ) - (st.p1 : ℤ) * (st.q0 : ℤ)) := by
          dsimp only [p2, q2]; push_cast; ring
        rw [hEq, neg_sq, hdet]
      have ha1_pos : 1 ≤ st.a1 := Nat.pos_of_ne_zero h0
      have hp2_le : p2 ≤ A + 1 := by nlinarith
      have hq2_le : q2 ≤ B + 1 := by nlinarith
      have ha2_lt : a2 < st.a1 := Nat.mod_lt st.a0 (Nat.pos_of_ne_zero h0)
      dsimp only [EuclidInv]
      exact ⟨hp', hq', hdet', by omega, ha1, by omega, hp1, hp2_le, hq1B, hq2_le⟩

private theorem euclidRecon_abs_diff {A B H2 : ℕ} {st : EuclidReconState}
    (hinv : EuclidInv A B H2 st) :
    |((st.q1 : ℤ) * (A : ℤ) - (st.p1 : ℤ) * (B : ℤ))| = (st.a1 : ℤ) := by
  obtain ⟨hp, hq, hdet, _, _, _, _, _, _, _⟩ := hinv
  have hEq : (st.q1 : ℤ) * (A : ℤ) - (st.p1 : ℤ) * (B : ℤ) =
      ((st.q1 : ℤ) * (st.p0 : ℤ) - (st.p1 : ℤ) * (st.q0 : ℤ)) * (st.a1 : ℤ) := by
    rw [← hp, ← hq]; push_cast; ring
  rw [hEq, abs_mul, show |(st.a1 : ℤ)| = (st.a1 : ℤ) from abs_of_nonneg (Nat.cast_nonneg _)]
  have h1 : |((st.q1 : ℤ) * (st.p0 : ℤ) - (st.p1 : ℤ) * (st.q0 : ℤ))| = 1 := by
    rcases sq_eq_one_iff.mp hdet with h | h <;> simp [h]
  rw [h1, one_mul]

private theorem euclidRecon_terminates {A B H2 : ℕ} (hB : 1 ≤ B) (hH2 : 1 ≤ H2) :
    let init : EuclidReconState := { a0 := A, a1 := B, p0 := 0, q0 := 1, p1 := 1, q1 := 0 }
    let steps := 2 * (A.size + B.size + 2)
    let st := (euclidReconStep H2)^[steps] init
    1 ≤ st.q1 ∧ (st.a1 = 0 ∨ H2 < (st.a0 / st.a1) * st.q1 + st.q0) := by
  intro init steps st
  let s₁ : EuclidReconState := { a0 := B, a1 := A % B, p0 := 1, q0 := 0, p1 := A / B, q1 := 1 }
  have hstep1 : (euclidReconStep H2) init = s₁ := by
    simp only [euclidReconStep, init, s₁]
    have hB0 : B ≠ 0 := by omega
    simp only [hB0, ↓reduceIte, mul_zero, add_zero, mul_one, zero_add]
    have hle : ¬ H2 < 1 := by omega
    simp [hle]
  have hP_step : ∀ s : EuclidReconState,
      (1 ≤ s.q1 ∧ (s.a1 ≠ 0 → s.a1 ≤ s.a0)) →
      let s' := euclidReconStep H2 s
      1 ≤ s'.q1 ∧ (s'.a1 ≠ 0 → s'.a1 ≤ s'.a0) := by
    intro s ⟨hq1, ha⟩
    unfold euclidReconStep
    by_cases h0 : s.a1 = 0
    · simp only [h0, ↓reduceIte]; exact ⟨hq1, fun h => absurd rfl h⟩
    · simp only [h0, ↓reduceIte]
      by_cases hlt : H2 < (s.a0 / s.a1) * s.q1 + s.q0
      · simp only [hlt, ↓reduceIte]; exact ⟨hq1, ha⟩
      · simp only [hlt, ↓reduceIte]
        have hdiv_ge : 1 ≤ s.a0 / s.a1 := Nat.div_pos (ha h0) (Nat.pos_of_ne_zero h0)
        refine ⟨by nlinarith, fun _ => (Nat.mod_lt s.a0 (Nat.pos_of_ne_zero h0)).le⟩
  have hP_iter : ∀ j : ℕ,
      let s' := (euclidReconStep H2)^[j] s₁
      1 ≤ s'.q1 ∧ (s'.a1 ≠ 0 → s'.a1 ≤ s'.a0) := fun j => by
    induction j with
    | zero =>
      simp only [Function.iterate_zero, id_eq, s₁]
      exact ⟨le_rfl, fun _ => (Nat.mod_lt A (by omega)).le⟩
    | succ j ih =>
      rw [Function.iterate_succ_apply']
      exact hP_step _ ih
  have hq1_pos : 1 ≤ st.q1 := by
    have hsteps_pos : steps = (steps - 1) + 1 := by omega
    dsimp only [st]
    rw [hsteps_pos, Function.iterate_succ_apply, hstep1]
    exact (hP_iter (steps - 1)).1
  refine ⟨hq1_pos, ?_⟩
  by_contra hnot
  push Not at hnot
  obtain ⟨ha1_ne, hq2_le⟩ := hnot
  have hfixed : ∀ s : EuclidReconState,
      (s.a1 = 0 ∨ H2 < (s.a0 / s.a1) * s.q1 + s.q0) → euclidReconStep H2 s = s := by
    intro s hs; unfold euclidReconStep
    by_cases h0 : s.a1 = 0
    · simp only [h0, ↓reduceIte]
    · simp only [h0, ↓reduceIte]
      have hlt : H2 < (s.a0 / s.a1) * s.q1 + s.q0 := hs.resolve_left h0
      simp only [hlt, ↓reduceIte]
  have hactive : ∀ j < steps,
      let sj := (euclidReconStep H2)^[j] init
      sj.a1 ≠ 0 ∧ (sj.a0 / sj.a1) * sj.q1 + sj.q0 ≤ H2 := by
    intro j hj
    by_contra hbad
    have hstop : let sj := (euclidReconStep H2)^[j] init
        sj.a1 = 0 ∨ H2 < (sj.a0 / sj.a1) * sj.q1 + sj.q0 := by dsimp only; omega
    have hstay : ∀ m, (euclidReconStep H2)^[m] ((euclidReconStep H2)^[j] init) =
        (euclidReconStep H2)^[j] init := fun m => Function.iterate_fixed (hfixed _ hstop) m
    have hst_eq : st = (euclidReconStep H2)^[j] init := by
      dsimp only [st]
      rw [show steps = (steps - j) + j by omega, Function.iterate_add_apply, hstay]
    rw [← hst_eq] at hstop
    rcases hstop with h | h
    · exact ha1_ne h
    · omega
  have htwo_step : ∀ j, j + 2 ≤ steps →
      2 * ((euclidReconStep H2)^[j + 2] init).a1 ≤ ((euclidReconStep H2)^[j] init).a1 := by
    intro j hj
    obtain ⟨h1, h1'⟩ := hactive j (by omega)
    obtain ⟨h2, h2'⟩ := hactive (j + 1) (by omega)
    set s0 := (euclidReconStep H2)^[j] init
    have hs1 : (euclidReconStep H2)^[j + 1] init =
        { a0 := s0.a1, a1 := s0.a0 % s0.a1, p0 := s0.p1, q0 := s0.q1,
          p1 := (s0.a0 / s0.a1) * s0.p1 + s0.p0, q1 := (s0.a0 / s0.a1) * s0.q1 + s0.q0 } := by
      rw [Function.iterate_succ_apply']
      change euclidReconStep H2 s0 = _
      unfold euclidReconStep
      simp only [h1, ↓reduceIte, not_lt.mpr h1']
    set s1 := (euclidReconStep H2)^[j + 1] init
    have hs2 : ((euclidReconStep H2)^[j + 2] init).a1 = s1.a0 % s1.a1 := by
      rw [Function.iterate_succ_apply']
      change (euclidReconStep H2 s1).a1 = _
      unfold euclidReconStep
      simp only [h2, ↓reduceIte, not_lt.mpr h2']
    rw [hs2, show s1.a0 = s0.a1 by rw [hs1]]
    have hlt : s1.a1 < s0.a1 := by
      rw [show s1.a1 = s0.a0 % s0.a1 by rw [hs1]]
      exact Nat.mod_lt s0.a0 (Nat.pos_of_ne_zero h1)
    have hdiv_pos : 1 ≤ s0.a1 / s1.a1 := Nat.div_pos hlt.le (Nat.pos_of_ne_zero h2)
    have hmod_lt : s0.a1 % s1.a1 < s1.a1 := Nat.mod_lt s0.a1 (Nat.pos_of_ne_zero h2)
    have hdm := Nat.div_add_mod' s0.a1 s1.a1
    nlinarith
  have hpow : ∀ m, 2 * m ≤ steps →
      2 ^ m * ((euclidReconStep H2)^[2 * m] init).a1 ≤ B := fun m => by
    induction m with
    | zero => intro _; simp [init]
    | succ m ih =>
      intro hm
      have h1 := ih (by omega)
      have h2 := htwo_step (2 * m) (by omega)
      rw [show 2 * (m + 1) = 2 * m + 2 by omega, pow_succ]
      calc 2 ^ m * 2 * ((euclidReconStep H2)^[2 * m + 2] init).a1
          = 2 ^ m * (2 * ((euclidReconStep H2)^[2 * m + 2] init).a1) := by ring
        _ ≤ 2 ^ m * ((euclidReconStep H2)^[2 * m] init).a1 := Nat.mul_le_mul_left _ h2
        _ ≤ B := h1
  have hbig := hpow (A.size + B.size + 2) le_rfl
  have hst_a1_pos : 1 ≤ st.a1 := Nat.pos_of_ne_zero ha1_ne
  have hB_lt : B < 2 ^ (A.size + B.size + 2) :=
    (Nat.lt_size_self B).trans_le (Nat.pow_le_pow_right (by omega) (by omega))
  have hcontra : 2 ^ (A.size + B.size + 2) ≤ B :=
    (Nat.le_mul_of_pos_right _ hst_a1_pos).trans hbig
  omega

/-- Exactness of `ratReconstructNonneg`: any rational `p / q` with `1 ≤ q ≤ H` and
`|(A / B) - (p / q)| < 1 / (4 * H^2)` is recovered identically. -/
theorem ratReconstructNonneg_spec {H A B p q : ℕ} (hB : 1 ≤ B) (hq : 1 ≤ q) (hqH : q ≤ H)
    (happrox : |(A : ℚ) / (B : ℚ) - (p : ℚ) / (q : ℚ)| < 1 / (4 * (H : ℚ) ^ 2)) :
    ratReconstructNonneg H A B = (p : ℚ) / (q : ℚ) := by
  have hH1 : 1 ≤ H := hq.trans hqH
  set steps := 2 * (A.size + B.size + 2)
  set init : EuclidReconState := { a0 := A, a1 := B, p0 := 0, q0 := 1, p1 := 1, q1 := 0 }
  set st := (euclidReconStep (2 * H))^[steps] init
  have hinv : EuclidInv A B (2 * H) st := by
    have : ∀ j, EuclidInv A B (2 * H) ((euclidReconStep (2 * H))^[j] init) := fun j => by
      induction j with
      | zero => exact euclidInv_init hH1
      | succ j ih => rw [Function.iterate_succ_apply']; exact euclidReconStep_inv ih
    exact this steps
  obtain ⟨hq1_pos, hterm⟩ := euclidRecon_terminates (A := A) hB (by omega : 1 ≤ 2 * H)
  change 1 ≤ st.q1 at hq1_pos
  change st.a1 = 0 ∨ 2 * H < (st.a0 / st.a1) * st.q1 + st.q0 at hterm
  have hq1_le : st.q1 ≤ 2 * H := hinv.2.2.2.1
  have habs := euclidRecon_abs_diff hinv
  have hB_pos : (0 : ℚ) < (B : ℚ) := by exact_mod_cast hB
  have hq_pos : (0 : ℚ) < (q : ℚ) := by exact_mod_cast hq
  have hq1_posQ : (0 : ℚ) < (st.q1 : ℚ) := by exact_mod_cast hq1_pos
  have hH_posQ : (0 : ℚ) < (H : ℚ) := by exact_mod_cast hH1
  have hstep_err : |(st.q1 : ℚ) * ((A : ℚ) / (B : ℚ)) - (st.p1 : ℚ)| < 1 / (2 * (H : ℚ)) := by
    have heq : |(st.q1 : ℚ) * ((A : ℚ) / (B : ℚ)) - (st.p1 : ℚ)| = (st.a1 : ℚ) / (B : ℚ) := by
      have h1 : (st.q1 : ℚ) * ((A : ℚ) / (B : ℚ)) - (st.p1 : ℚ) =
          (((st.q1 : ℤ) * (A : ℤ) - (st.p1 : ℤ) * (B : ℤ) : ℤ) : ℚ) / (B : ℚ) := by
        push_cast; field_simp [hB_pos.ne']
      rw [h1, abs_div, abs_of_pos hB_pos, ← Int.cast_abs, habs]
      simp
    rw [heq]
    by_cases ha1_0 : st.a1 = 0
    · rw [ha1_0, Nat.cast_zero, zero_div]; positivity
    · have hq2_gt : 2 * H < (st.a0 / st.a1) * st.q1 + st.q0 := hterm.resolve_left ha1_0
      have hB_ge : 2 * H * st.a1 < B := by
        have hBq := hinv.2.1
        have ha1_pos : 1 ≤ st.a1 := Nat.pos_of_ne_zero ha1_0
        have hdiv := Nat.div_add_mod' st.a0 st.a1
        have hEq : ((st.a0 / st.a1) * st.q1 + st.q0) * st.a1 + st.q1 * (st.a0 % st.a1) = B := by
          calc ((st.a0 / st.a1) * st.q1 + st.q0) * st.a1 + st.q1 * (st.a0 % st.a1)
              = st.q1 * ((st.a0 / st.a1) * st.a1 + st.a0 % st.a1) + st.q0 * st.a1 := by ring
            _ = st.q1 * st.a0 + st.q0 * st.a1 := by rw [hdiv]
            _ = B := hBq
        have hmul_lt : 2 * H * st.a1 < ((st.a0 / st.a1) * st.q1 + st.q0) * st.a1 :=
          Nat.mul_lt_mul_of_pos_right hq2_gt ha1_pos
        omega
      rw [div_lt_div_iff₀ hB_pos (by positivity : (0 : ℚ) < 2 * (H : ℚ)), one_mul]
      exact_mod_cast (show st.a1 * (2 * H) < B by linarith)
  have hcross : |((st.p1 : ℤ) * (q : ℤ) - (p : ℤ) * (st.q1 : ℤ) : ℤ)| < 1 := by
    have hcast : (((st.p1 : ℤ) * (q : ℤ) - (p : ℤ) * (st.q1 : ℤ) : ℤ) : ℚ) =
        (st.q1 : ℚ) * ((q : ℚ) * ((A : ℚ) / (B : ℚ)) - (p : ℚ)) -
          (q : ℚ) * ((st.q1 : ℚ) * ((A : ℚ) / (B : ℚ)) - (st.p1 : ℚ)) := by
      push_cast; ring
    have htri : |(((st.p1 : ℤ) * (q : ℤ) - (p : ℤ) * (st.q1 : ℤ) : ℤ) : ℚ)| < 1 := by
      rw [hcast]
      have h1 : |(st.q1 : ℚ) * ((q : ℚ) * ((A : ℚ) / (B : ℚ)) - (p : ℚ))| < 1 / 2 := by
        have heq_q : (q : ℚ) * ((A : ℚ) / (B : ℚ)) - (p : ℚ) =
            (q : ℚ) * ((A : ℚ) / (B : ℚ) - (p : ℚ) / (q : ℚ)) := by field_simp [hq_pos.ne']
        rw [heq_q, abs_mul, abs_mul, abs_of_pos hq1_posQ, abs_of_pos hq_pos]
        have hq1q : (st.q1 : ℚ) * (q : ℚ) ≤ 2 * (H : ℚ) ^ 2 := by
          have h1 : (st.q1 : ℚ) ≤ 2 * (H : ℚ) := by exact_mod_cast hq1_le
          have h2 : (q : ℚ) ≤ (H : ℚ) := by exact_mod_cast hqH
          nlinarith
        calc (st.q1 : ℚ) * ((q : ℚ) * |(A : ℚ) / (B : ℚ) - (p : ℚ) / (q : ℚ)|)
            = ((st.q1 : ℚ) * (q : ℚ)) * |(A : ℚ) / (B : ℚ) - (p : ℚ) / (q : ℚ)| := by ring
          _ ≤ (2 * (H : ℚ) ^ 2) * |(A : ℚ) / (B : ℚ) - (p : ℚ) / (q : ℚ)| :=
              mul_le_mul_of_nonneg_right hq1q (abs_nonneg _)
          _ < (2 * (H : ℚ) ^ 2) * (1 / (4 * (H : ℚ) ^ 2)) :=
              mul_lt_mul_of_pos_left happrox (by positivity)
          _ = 1 / 2 := by field_simp [hH_posQ.ne']; ring
      have h2 : |(q : ℚ) * ((st.q1 : ℚ) * ((A : ℚ) / (B : ℚ)) - (st.p1 : ℚ))| < 1 / 2 := by
        rw [abs_mul, abs_of_pos hq_pos]
        have hqH' : (q : ℚ) ≤ (H : ℚ) := by exact_mod_cast hqH
        calc (q : ℚ) * |(st.q1 : ℚ) * ((A : ℚ) / (B : ℚ)) - (st.p1 : ℚ)|
            ≤ (H : ℚ) * |(st.q1 : ℚ) * ((A : ℚ) / (B : ℚ)) - (st.p1 : ℚ)| :=
              mul_le_mul_of_nonneg_right hqH' (abs_nonneg _)
          _ < (H : ℚ) * (1 / (2 * (H : ℚ))) := mul_lt_mul_of_pos_left hstep_err hH_posQ
          _ = 1 / 2 := by field_simp [hH_posQ.ne']
      calc |(st.q1 : ℚ) * ((q : ℚ) * ((A : ℚ) / (B : ℚ)) - (p : ℚ)) -
              (q : ℚ) * ((st.q1 : ℚ) * ((A : ℚ) / (B : ℚ)) - (st.p1 : ℚ))|
          ≤ |(st.q1 : ℚ) * ((q : ℚ) * ((A : ℚ) / (B : ℚ)) - (p : ℚ))| +
              |(q : ℚ) * ((st.q1 : ℚ) * ((A : ℚ) / (B : ℚ)) - (st.p1 : ℚ))| := abs_sub _ _
        _ < 1 / 2 + 1 / 2 := add_lt_add h1 h2
        _ = 1 := by norm_num
    exact_mod_cast htri
  have hzero : (st.p1 : ℤ) * (q : ℤ) - (p : ℤ) * (st.q1 : ℤ) = 0 := by
    rw [abs_lt] at hcross; omega
  have heq_mul : (st.p1 : ℚ) * (q : ℚ) = (p : ℚ) * (st.q1 : ℚ) := by
    have : ((st.p1 : ℤ) * (q : ℤ) : ℚ) = ((p : ℤ) * (st.q1 : ℤ) : ℚ) := by
      exact_mod_cast sub_eq_zero.mp hzero
    push_cast at this; exact this
  change (st.p1 : ℚ) / (st.q1 : ℚ) = (p : ℚ) / (q : ℚ)
  rw [div_eq_div_iff hq1_posQ.ne' hq_pos.ne']
  exact heq_mul

/-- Exactness of `ratReconstruct`: any rational `r` with `r.den ≤ H` and
`|x - r| < 1 / (4 * H^2)` is recovered identically. -/
theorem ratReconstruct_spec {H : ℕ} {x r : ℚ} (hrH : r.den ≤ H)
    (happrox : |x - r| < 1 / (4 * (H : ℚ) ^ 2)) :
    ratReconstruct H x = r := by
  have hH1 : 1 ≤ H := r.den_pos.trans_le hrH
  have hH1Q : (1 : ℚ) ≤ (H : ℚ) := by exact_mod_cast hH1
  have hH_pos : (0 : ℚ) < (H : ℚ) := by exact_mod_cast hH1
  have h4H2 : (1 : ℚ) / (4 * (H : ℚ) ^ 2) ≤ 1 / (H : ℚ) := by
    rw [div_le_div_iff₀ (by positivity) hH_pos]; nlinarith
  by_cases hx : 0 ≤ x
  · simp only [ratReconstruct, hx, ↓reduceIte]
    have hx_eq : x = (x.num.natAbs : ℚ) / (x.den : ℚ) := by
      have hnum : (x.num.natAbs : ℚ) = (x.num : ℚ) := by
        rw [← Int.cast_natCast, Int.natAbs_of_nonneg (Rat.num_nonneg.mpr hx)]
      rw [hnum, Rat.num_div_den]
    by_cases hr0 : 0 ≤ r
    · have hr_eq : r = (r.num.natAbs : ℚ) / (r.den : ℚ) := by
        have hnum : (r.num.natAbs : ℚ) = (r.num : ℚ) := by
          rw [← Int.cast_natCast, Int.natAbs_of_nonneg (Rat.num_nonneg.mpr hr0)]
        rw [hnum, Rat.num_div_den]
      rw [hx_eq, hr_eq] at happrox
      rw [ratReconstructNonneg_spec x.den_pos r.den_pos hrH happrox, ← hr_eq]
    · push Not at hr0
      exfalso
      have hr_le : r ≤ -(1 / (r.den : ℚ)) := by
        have hnum : r.num ≤ -1 := by have := Rat.num_neg.mpr hr0; omega
        conv_lhs => rw [← Rat.num_div_den r]
        rw [neg_div', div_le_div_iff_of_pos_right (by exact_mod_cast r.den_pos)]
        exact_mod_cast hnum
      have h1r : (1 : ℚ) / (H : ℚ) ≤ 1 / (r.den : ℚ) :=
        one_div_le_one_div_of_le (by exact_mod_cast r.den_pos) (by exact_mod_cast hrH)
      have habs_ge : 1 / (H : ℚ) ≤ |x - r| := by rw [abs_of_nonneg (by linarith)]; linarith
      linarith
  · push Not at hx
    simp only [ratReconstruct, not_le.mpr hx, ↓reduceIte]
    have hx_eq : -x = (x.num.natAbs : ℚ) / (x.den : ℚ) := by
      have hnum : (x.num.natAbs : ℚ) = -(x.num : ℚ) := by
        rw [← Int.cast_natCast, Int.ofNat_natAbs_of_nonpos (Rat.num_neg.mpr hx).le, Int.cast_neg]
      rw [hnum, neg_div, Rat.num_div_den]
    by_cases hr0 : r ≤ 0
    · have hr_eq : -r = (r.num.natAbs : ℚ) / (r.den : ℚ) := by
        have hnum : (r.num.natAbs : ℚ) = -(r.num : ℚ) := by
          rw [← Int.cast_natCast, Int.ofNat_natAbs_of_nonpos (Rat.num_nonpos.mpr hr0), Int.cast_neg]
        rw [hnum, neg_div, Rat.num_div_den]
      have happrox' : |(-x) - (-r)| < 1 / (4 * (H : ℚ) ^ 2) := by
        rw [show (-x) - (-r) = -(x - r) by ring, abs_neg]; exact happrox
      rw [hx_eq, hr_eq] at happrox'
      rw [ratReconstructNonneg_spec x.den_pos r.den_pos hrH happrox', ← hr_eq, neg_neg]
    · push Not at hr0
      exfalso
      have hr_ge : 1 / (r.den : ℚ) ≤ r := by
        have hnum : 1 ≤ r.num := by have := Rat.num_pos.mpr hr0; omega
        conv_rhs => rw [← Rat.num_div_den r]
        rw [div_le_div_iff_of_pos_right (by exact_mod_cast r.den_pos)]
        exact_mod_cast hnum
      have h1r : (1 : ℚ) / (H : ℚ) ≤ 1 / (r.den : ℚ) :=
        one_div_le_one_div_of_le (by exact_mod_cast r.den_pos) (by exact_mod_cast hrH)
      have habs_ge : 1 / (H : ℚ) ≤ |x - r| := by rw [abs_of_neg (by linarith)]; linarith
      linarith

/-! ### Part 5: `findRationalRoots` and its exactness specification -/

/-- Extract the unique rational root inside isolating interval `J` of `sq` (if any), checking
both interval membership and exact evaluation in `cs`. -/
def rootsFromInterval (cs sq : List ℚ) (seq : List (List ℚ)) (steps H : ℕ)
    (J : RootInterval) : List ℚ :=
  let r :=
    if evalCoeffList J.lower sq = 0 then J.lower
    else ratReconstruct H (bisectInterval seq steps J).2
  if J.lower ≤ r ∧ r ≤ J.upper ∧ evalCoeffList r cs = 0 then [r] else []

/-- Compute the duplicate-free list of all rational roots of `Polynomial.ofCoeffList cs` in
polynomial time. Returns `[]` when `ofCoeffList cs = 0`. -/
def findRationalRoots (cs : List ℚ) : List ℚ :=
  let t := CoeffList.trim cs
  if t.isEmpty then []
  else
    let sq := sqfreePartList cs
    let seq := sturmSeqList sq
    let H := denomBoundNat sq
    let steps := refineStepsNat sq
    (isolateRootsTotal sq).flatMap (rootsFromInterval cs sq seq steps H)

private theorem bisectInterval_spec {sq : List ℚ} (hsep : (ofCoeffList sq).Separable)
    {J : RootInterval} (hiso : J.IsIsolatingFor ((ofCoeffList sq).map (algebraMap ℚ ℝ)))
    (hnotl : evalCoeffList J.lower sq ≠ 0) (steps : ℕ) :
    let ab := bisectInterval (sturmSeqList sq) steps J
    J.lower ≤ ab.1 ∧ ab.1 ≤ ab.2 ∧ ab.2 ≤ J.upper ∧
      ((ab.2 : ℝ) - (ab.1 : ℝ)) * (2 : ℝ) ^ steps = (J.upper : ℝ) - (J.lower : ℝ) ∧
      ∃ r₀ : ℝ, ((ofCoeffList sq).map (algebraMap ℚ ℝ)).IsRoot r₀ ∧
        (ab.1 : ℝ) < r₀ ∧ r₀ ≤ (ab.2 : ℝ) := by
  have hev_trim (x : ℚ) : evalCoeffList x sq = evalCoeffList x (CoeffList.trim sq) := by
    rw [← Polynomial.eval_ofCoeffList, ← CoeffList.ofCoeffList_trim, Polynomial.eval_ofCoeffList]
  have hnotlR : ¬ ((ofCoeffList sq).map (algebraMap ℚ ℝ)).IsRoot (J.lower : ℝ) :=
    fun h => hnotl ((hev_trim J.lower).trans ((eval_rat_eq_zero_iff sq J.lower).mpr h.eq_zero))
  obtain ⟨r₀, ⟨hr₀l, hr₀u, hr₀r⟩, huniq⟩ := hiso.2
  have hr₀_gt : (J.lower : ℝ) < r₀ := lt_of_le_of_ne hr₀l (fun h => hnotlR (h ▸ hr₀r))
  suffices ∀ k : ℕ,
      let ab := (bisectStep (sturmSeqList sq))^[k] (J.lower, J.upper)
      J.lower ≤ ab.1 ∧ ab.1 ≤ ab.2 ∧ ab.2 ≤ J.upper ∧
        ((ab.2 : ℝ) - (ab.1 : ℝ)) * (2 : ℝ) ^ k = (J.upper : ℝ) - (J.lower : ℝ) ∧
        (ab.1 : ℝ) < r₀ ∧ r₀ ≤ (ab.2 : ℝ) ∧
        sturmVariationsList (sturmSeqList sq) ab.1 -
          sturmVariationsList (sturmSeqList sq) ab.2 = 1 by
    obtain ⟨h0, h1, h2, h3, h4, h5, _⟩ := this steps
    exact ⟨h0, h1, h2, h3, r₀, hr₀r, h4, h5⟩
  intro k
  induction k with
  | zero =>
    simp only [Function.iterate_zero, id_eq, pow_zero, mul_one]
    refine ⟨le_rfl, hiso.1, le_rfl, trivial, hr₀_gt, hr₀u, ?_⟩
    rw [card_roots_Ioc_eq hsep hiso.1]
    have hpR0 : (ofCoeffList sq).map (algebraMap ℚ ℝ) ≠ 0 :=
      (Polynomial.map_ne_zero_iff (algebraMap ℚ ℝ).injective).mpr hsep.ne_zero
    have hset : ((ofCoeffList sq).map (algebraMap ℚ ℝ)).roots.toFinset.filter
        (fun r : ℝ => (J.lower : ℝ) < r ∧ r ≤ (J.upper : ℝ)) = {r₀} := by
      ext x; simp only [Finset.mem_filter, Multiset.mem_toFinset, Polynomial.mem_roots hpR0,
        Finset.mem_singleton]
      exact ⟨fun ⟨hx, hxl, hxu⟩ => huniq x ⟨hxl.le, hxu, hx⟩, fun h => h ▸ ⟨hr₀r, hr₀_gt, hr₀u⟩⟩
    rw [hset, Finset.card_singleton]
  | succ k ih =>
    obtain ⟨hl_le, hle, hu_le, hwid, hlt_r, hr_le, hvar⟩ := ih
    set ab := (bisectStep (sturmSeqList sq))^[k] (J.lower, J.upper)
    set m := (ab.1 + ab.2) / 2
    rw [Function.iterate_succ_apply']
    change let ab' := bisectStep (sturmSeqList sq) ab; _
    have hm1 : ab.1 ≤ m := by dsimp only [m]; linarith
    have hm2 : m ≤ ab.2 := by dsimp only [m]; linarith
    have hanti1 := sturmVariationsList_antitone hsep hm1
    have hanti2 := sturmVariationsList_antitone hsep hm2
    dsimp only [bisectStep]
    change let ab' := if sturmVariationsList (sturmSeqList sq) ab.1 =
        sturmVariationsList (sturmSeqList sq) m then (m, ab.2) else (ab.1, m); _
    split_ifs with heq
    · refine ⟨hl_le.trans hm1, hm2, hu_le, ?_, ?_, hr_le, ?_⟩
      · have hhalf : (ab.2 : ℝ) - (m : ℝ) = ((ab.2 : ℝ) - (ab.1 : ℝ)) / 2 := by
          dsimp only [m]; push_cast; ring
        rw [hhalf, pow_succ]
        calc ((ab.2 : ℝ) - (ab.1 : ℝ)) / 2 * ((2 : ℝ) ^ k * 2)
            = ((ab.2 : ℝ) - (ab.1 : ℝ)) * (2 : ℝ) ^ k := by ring
          _ = (J.upper : ℝ) - (J.lower : ℝ) := hwid
      · by_contra hle_m; push Not at hle_m
        exact no_root_Ioc_of_card_eq_zero hsep hm1 (by omega) hlt_r hle_m hr₀r
      · change sturmVariationsList (sturmSeqList sq) m -
            sturmVariationsList (sturmSeqList sq) ab.2 = 1
        omega
    · refine ⟨hl_le, hm1, hm2.trans hu_le, ?_, hlt_r, ?_, ?_⟩
      · have hhalf : (m : ℝ) - (ab.1 : ℝ) = ((ab.2 : ℝ) - (ab.1 : ℝ)) / 2 := by
          dsimp only [m]; push_cast; ring
        rw [hhalf, pow_succ]
        calc ((ab.2 : ℝ) - (ab.1 : ℝ)) / 2 * ((2 : ℝ) ^ k * 2)
            = ((ab.2 : ℝ) - (ab.1 : ℝ)) * (2 : ℝ) ^ k := by ring
          _ = (J.upper : ℝ) - (J.lower : ℝ) := hwid
      · by_contra hgt_m; push Not at hgt_m
        exact no_root_Ioc_of_card_eq_zero hsep hm2 (by omega) hgt_m hr_le hr₀r
      · change sturmVariationsList (sturmSeqList sq) ab.1 -
            sturmVariationsList (sturmSeqList sq) m = 1
        omega

private theorem isolateRootsTotal_width_le {sq : List ℚ}
    {J : RootInterval} (hJ : J ∈ isolateRootsTotal sq) :
    (J.upper : ℝ) - (J.lower : ℝ) ≤
      2 * (cauchyBoundNat sq : ℝ) * (2 : ℝ) ^ (3 * mignotteBisectionDepth sq) := by
  have hbd := isolateRootsTotal_endpoint_bounds sq J hJ
  have hle_abs : ∀ q : ℚ,
      q.num.natAbs ≤ cauchyBoundNat sq * 2 ^ (3 * mignotteBisectionDepth sq) →
      |(q : ℝ)| ≤ (cauchyBoundNat sq : ℝ) * (2 : ℝ) ^ (3 * mignotteBisectionDepth sq) := by
    intro q hq
    have hq_rat : |q| ≤ (cauchyBoundNat sq : ℚ) * (2 : ℚ) ^ (3 * mignotteBisectionDepth sq) := by
      have hden1 : (1 : ℚ) ≤ (q.den : ℚ) := by exact_mod_cast q.den_pos
      have habs_q : |q| = (q.num.natAbs : ℚ) / (q.den : ℚ) := by
        conv_lhs => rw [← Rat.num_div_den q]
        rw [abs_div, show |(q.den : ℚ)| = (q.den : ℚ) from
          abs_of_pos (by exact_mod_cast q.den_pos), ← Int.cast_abs, Int.abs_eq_natAbs]
        simp
      rw [habs_q, div_le_iff₀ (by exact_mod_cast q.den_pos)]
      have hnum : (q.num.natAbs : ℚ) ≤
          (cauchyBoundNat sq : ℚ) * (2 : ℚ) ^ (3 * mignotteBisectionDepth sq) := by
        exact_mod_cast hq
      nlinarith
    exact_mod_cast hq_rat
  have h1 := abs_le.mp (hle_abs J.lower hbd.2.2.2.2.1)
  have h2 := abs_le.mp (hle_abs J.upper hbd.2.2.2.2.2)
  linarith

private theorem two_pow_refineSteps_gt (B H e : ℕ) :
    8 * B * H ^ 2 * 2 ^ e < 2 ^ ((8 * B * H ^ 2).size + e + 3) := by
  have h1 : 8 * B * H ^ 2 < 2 ^ ((8 * B * H ^ 2).size + 3) :=
    (Nat.lt_size_self _).trans_le (Nat.pow_le_pow_right zero_lt_two (Nat.le_add_right _ 3))
  have h2 : 8 * B * H ^ 2 * 2 ^ e < 2 ^ ((8 * B * H ^ 2).size + 3) * 2 ^ e :=
    Nat.mul_lt_mul_of_pos_right h1 (Nat.pow_pos (a := 2) zero_lt_two)
  rw [← pow_add] at h2
  rwa [Nat.add_right_comm] at h2

/-- **Exactness and deduplication of `findRationalRoots`**: for any `cs : List ℚ` with
`ofCoeffList cs ≠ 0`, `findRationalRoots cs` is duplicate-free and contains `r : ℚ` iff
`(ofCoeffList cs).eval r = 0`. -/
theorem findRationalRoots_spec {cs : List ℚ} (hcs : ofCoeffList cs ≠ 0) :
    (findRationalRoots cs).Nodup ∧
      ∀ r : ℚ, r ∈ findRationalRoots cs ↔ (ofCoeffList cs).eval r = 0 := by
  set t := CoeffList.trim cs
  have ht_ne : t ≠ [] := mt (CoeffList.trim_eq_nil_iff cs).mp hcs
  have ht_empty : t.isEmpty = false := List.isEmpty_eq_false_iff.mpr ht_ne
  obtain ⟨hg_mul, hsq_free, hsq_roots⟩ := sqfreePartList_spec hcs
  set sq := sqfreePartList cs
  have hsq_ne : ofCoeffList sq ≠ 0 := fun h0 => hcs (by rw [← hg_mul, h0, mul_zero])
  have hsep : (ofCoeffList sq).Separable := PerfectField.separable_iff_squarefree.mpr hsq_free
  have hsq_trim : CoeffList.IsTrimmed sq := by
    dsimp only [sq, sqfreePartList]
    simp only [t, ht_empty, Bool.false_eq_true, ↓reduceIte]
    exact CoeffList.isTrimmed_trim _
  have hdef : findRationalRoots cs =
      (isolateRootsTotal sq).flatMap
        (rootsFromInterval cs sq (sturmSeqList sq) (refineStepsNat sq) (denomBoundNat sq)) := by
    simp [findRationalRoots, t, ht_empty, sq]
  have hroots_mem : ∀ (J : RootInterval) (r : ℚ),
      r ∈ rootsFromInterval cs sq (sturmSeqList sq) (refineStepsNat sq) (denomBoundNat sq) J →
      J.lower ≤ r ∧ r ≤ J.upper ∧ evalCoeffList r cs = 0 := by
    intro J r hr
    unfold rootsFromInterval at hr
    set r₀ := if evalCoeffList J.lower sq = 0 then J.lower
      else ratReconstruct (denomBoundNat sq)
        (bisectInterval (sturmSeqList sq) (refineStepsNat sq) J).2
    change r ∈ (if J.lower ≤ r₀ ∧ r₀ ≤ J.upper ∧ evalCoeffList r₀ cs = 0 then [r₀] else []) at hr
    split_ifs at hr with h
    · rw [List.mem_singleton.mp hr]; exact h
    · exact absurd hr List.not_mem_nil
  constructor
  · rw [hdef, List.nodup_flatMap]
    refine ⟨fun J _ => ?_, ?_⟩
    · dsimp only [rootsFromInterval]
      split_ifs <;> simp
    · refine (isolateRootsTotal_pairwise_lt hsep).imp_of_mem ?_
      intro J₁ J₂ _ _ hlt r hr₁ hr₂
      obtain ⟨_, h1u, _⟩ := hroots_mem J₁ r hr₁
      obtain ⟨h2l, _, _⟩ := hroots_mem J₂ r hr₂
      linarith
  · intro r
    rw [hdef, List.mem_flatMap]
    constructor
    · rintro ⟨J, _, hrJ⟩
      rw [Polynomial.eval_ofCoeffList]
      exact (hroots_mem J r hrJ).2.2
    · intro hr
      have hroot_sq : (ofCoeffList sq).eval r = 0 := (hsq_roots r).mpr hr
      have hroot_R : Polynomial.aeval (r : ℝ) (ofCoeffList sq) = 0 := by
        rw [show (r : ℝ) = algebraMap ℚ ℝ r from rfl, Polynomial.aeval_algebraMap_apply]
        change (algebraMap ℚ ℝ) ((ofCoeffList sq).eval r) = 0
        rw [hroot_sq, map_zero]
      obtain ⟨i, hi⟩ := (isolateRootsTotal_bijective hsep).2 ⟨(r : ℝ), hroot_R⟩
      set J := (isolateRootsTotal sq)[i]
      refine ⟨J, List.getElem_mem i.2, ?_⟩
      have hmem_J : (r : ℝ) ∈ Set.Icc (J.lower : ℝ) (J.upper : ℝ) := by
        have := totalIsolatedRoot_mem hsep i; rwa [hi] at this
      have hiso := isolateRootsTotal_isIsolatingFor hsep J (List.getElem_mem i.2)
      have hcand_eq : (if evalCoeffList J.lower sq = 0 then J.lower
          else ratReconstruct (denomBoundNat sq)
            (bisectInterval (sturmSeqList sq) (refineStepsNat sq) J).2) = r := by
        split_ifs with hl
        · have hl_trim : evalCoeffList J.lower (CoeffList.trim sq) = 0 := by
            rwa [← Polynomial.eval_ofCoeffList, CoeffList.ofCoeffList_trim,
              Polynomial.eval_ofCoeffList]
          have hl_root : ((ofCoeffList sq).map (algebraMap ℚ ℝ)).IsRoot (J.lower : ℝ) :=
            IsRoot.def.mpr ((eval_rat_eq_zero_iff sq J.lower).mp hl_trim)
          obtain ⟨r₀, _, huniq⟩ := hiso.2
          exact Rat.cast_injective <| by
            rw [huniq _ ⟨le_rfl, Rat.cast_le.mpr hiso.1, hl_root⟩,
              ← huniq _ ⟨hmem_J.1, hmem_J.2, by rwa [IsRoot.def, Polynomial.eval_map_algebraMap]⟩]
        · obtain ⟨hl_le, hab_le, hu_le, hwid, r₀, hr₀r, hlt_r₀, hr₀_le⟩ :=
            bisectInterval_spec hsep hiso hl (refineStepsNat sq)
          have hr₀_eq : r₀ = (r : ℝ) := by
            obtain ⟨_, _, huniq⟩ := hiso.2
            rw [huniq _ ⟨(Rat.cast_le.mpr hl_le).trans hlt_r₀.le,
              hr₀_le.trans (Rat.cast_le.mpr hu_le), hr₀r⟩,
              ← huniq _ ⟨hmem_J.1, hmem_J.2, by rwa [IsRoot.def, Polynomial.eval_map_algebraMap]⟩]
          subst hr₀_eq
          have hden_le : r.den ≤ denomBoundNat sq :=
            den_le_denomBoundNat_of_isRoot hsq_ne hsq_trim hroot_sq
          apply ratReconstruct_spec hden_le
          set ab := bisectInterval (sturmSeqList sq) (refineStepsNat sq) J
          have hB_pos : (0 : ℝ) < (cauchyBoundNat sq : ℝ) := by
            exact_mod_cast one_le_cauchyBoundNat sq
          have hH_pos : (0 : ℝ) < (denomBoundNat sq : ℝ) := by
            exact_mod_cast one_le_denomBoundNat sq
          have hpow_gt : (8 * (cauchyBoundNat sq : ℝ) * (denomBoundNat sq : ℝ) ^ 2 *
              (2 : ℝ) ^ (3 * mignotteBisectionDepth sq)) <
              (2 : ℝ) ^ (refineStepsNat sq) := by
            exact_mod_cast two_pow_refineSteps_gt (cauchyBoundNat sq) (denomBoundNat sq)
              (3 * mignotteBisectionDepth sq)
          have hJ_wid := isolateRootsTotal_width_le (List.getElem_mem i.2)
          have hab_wid : (ab.2 : ℝ) - (ab.1 : ℝ) < 1 / (4 * (denomBoundNat sq : ℝ) ^ 2) := by
            have h1 : ((ab.2 : ℝ) - (ab.1 : ℝ)) * (2 : ℝ) ^ (refineStepsNat sq) ≤
                2 * (cauchyBoundNat sq : ℝ) * (2 : ℝ) ^ (3 * mignotteBisectionDepth sq) :=
              hwid.le.trans hJ_wid
            have h2 : (ab.2 : ℝ) - (ab.1 : ℝ) ≤
                (2 * (cauchyBoundNat sq : ℝ) * (2 : ℝ) ^ (3 * mignotteBisectionDepth sq)) /
                  (2 : ℝ) ^ (refineStepsNat sq) :=
              (le_div_iff₀ (by positivity)).mpr h1
            have h3 : (2 * (cauchyBoundNat sq : ℝ) * (2 : ℝ) ^ (3 * mignotteBisectionDepth sq)) /
                  (2 : ℝ) ^ (refineStepsNat sq) <
                1 / (4 * (denomBoundNat sq : ℝ) ^ 2) := by
              rw [div_lt_div_iff₀ (by positivity) (by positivity)]
              linarith
            exact h2.trans_lt h3
          have hdiff_R : |(ab.2 : ℝ) - (r : ℝ)| < 1 / (4 * (denomBoundNat sq : ℝ) ^ 2) := by
            rw [abs_of_nonneg (sub_nonneg.mpr hr₀_le)]
            linarith [hlt_r₀, hab_wid]
          have hq_lt : ((|ab.2 - r| : ℚ) : ℝ) <
              ((1 / (4 * (denomBoundNat sq : ℚ) ^ 2) : ℚ) : ℝ) := by
            push_cast; exact hdiff_R
          exact Rat.cast_lt.mp hq_lt
      have hJl_le : J.lower ≤ r := Rat.cast_le.mp hmem_J.1
      have hr_le_Ju : r ≤ J.upper := Rat.cast_le.mp hmem_J.2
      have hev_cs : evalCoeffList r cs = 0 := by rw [← Polynomial.eval_ofCoeffList]; exact hr
      simp [rootsFromInterval, hcand_eq, hJl_le, hr_le_Ju, hev_cs]

/-! ### Part 6: Polynomial-time computability of `findRationalRoots` -/

private enc_structure encEuclidReconState : EuclidReconState where
  a0 : encNat,
  a1 : encNat,
  p0 : encNat,
  q0 : encNat,
  p1 : encNat,
  q1 : encNat

private theorem length_encRat_le_of_pow_bound {q : ℚ} {K : ℕ}
    (hn : q.num.natAbs ≤ 2 ^ K) (hd : q.den ≤ 2 ^ K) :
    (encRat q).length ≤ 3 * K + 6 := by
  have h := length_encRat_le q hn hd
  have hs : (2 ^ K).size ≤ K + 1 := Nat.size_le.mpr (Nat.pow_lt_pow_right (by omega) (by omega))
  omega

private theorem sturmLastList_polyTime :
    ComputableInPolyTime sturmLastList encRatPoly encRatPoly := by
  unfold sturmLastList
  exact trim_computableInPolyTime.comp
    (((headD (encA := encRatPoly) []).comp (listReverse encRatPoly)).comp
      sturmSeqList_computableInPolyTime)

private theorem toeplitzSystem_polyTime :
    ComputableInPolyTime (fun p : List ℚ × List ℚ => toeplitzSystem p.1 p.2)
      (encPair encRatPoly encRatPoly) LinearSystemInput.enc := by
  unfold toeplitzSystem
  have hg := fst encRatPoly encRatPoly
  have ht := snd encRatPoly encRatPoly
  have htlen := (length_list encRat).comp ht
  have hglen := (length_list encRat).comp hg
  have hcols := unary_add' (unary_sub' htlen hglen) (const 1)
  have hrow : ComputableInPolyTime
      (fun q : (List ℚ × List ℚ) × ℕ =>
        (List.range (q.1.2.length - q.1.1.length + 1)).map fun j =>
          if j ≤ q.2 then q.1.1.getD (q.2 - j) 0 else 0)
      (encPair (encPair encRatPoly encRatPoly) encUnary) (encList encRat) := by
    have hcols' := hcols.comp (fst (encPair encRatPoly encRatPoly) encUnary)
    refine mapWithInput (range.comp hcols') ?_
    have hj := snd (encPair (encPair encRatPoly encRatPoly) encUnary) encUnary
    have hi := (snd (encPair encRatPoly encRatPoly) encUnary).comp
      (fst (encPair (encPair encRatPoly encRatPoly) encUnary) encUnary)
    have hg' := (fst encRatPoly encRatPoly).comp
      ((fst (encPair encRatPoly encRatPoly) encUnary).comp
        (fst (encPair (encPair encRatPoly encRatPoly) encUnary) encUnary))
    exact (unary_le' hj hi).ite_decide (listGetDWithInput hg' (unary_sub' hi hj) 0) (const (0 : ℚ))
  have hrows : ComputableInPolyTime
      (fun p : List ℚ × List ℚ =>
        (List.range p.2.length).map fun i =>
          (List.range (p.2.length - p.1.length + 1)).map fun j =>
            if j ≤ i then p.1.getD (i - j) 0 else 0)
      (encPair encRatPoly encRatPoly) (encList (encList encRat)) :=
    mapWithInput (range.comp htlen) hrow
  have hmat := RatTable.enc_mk_polyTime htlen hcols hrows
  exact LinearSystemInput.enc_mk_polyTime hmat ht

private theorem sqfreePartList_polyTime :
    ComputableInPolyTime sqfreePartList encRatPoly encRatPoly := by
  unfold sqfreePartList
  have ht := trim_computableInPolyTime
  have hg := sturmLastList_polyTime
  have hres := ratSolve_computableInPolyTime.comp (toeplitzSystem_polyTime.comp (hg.prod ht))
  have hsol := (optionGetD (encList encRat)).comp
    ((LinearSolveResult.enc_solution_polyTime hres).prod (const ([] : List ℚ)))
  exact ((listIsEmpty' encRat).comp ht).ite (const []) (trim_computableInPolyTime.comp hsol)

private theorem denomBoundNat_polyTime :
    ComputableInPolyTime denomBoundNat encRatPoly encNat := by
  have hlast : ComputableInPolyTime (fun sq : List ℚ => sq.reverse.headD 0) encRatPoly encRat :=
    (headD (encA := encRat) (0 : ℚ)).comp (listReverse encRat)
  have hnum : ComputableInPolyTime (fun sq : List ℚ => (sq.reverse.headD 0).num.natAbs)
      encRatPoly encNat := intBin_natAbs.comp (rat_num.comp hlast)
  have hden_prod : ComputableInPolyTime (fun sq : List ℚ => (sq.map (·.den)).prod)
      encRatPoly encNat := binary_prod.comp (map rat_den)
  have hmul := binary_mul' hnum hden_prod
  refine ((binary_lt' (const 1) hmul).ite_decide hmul (const 1)).of_enc_eq fun sq =>
    congrArg encNat ?_
  unfold denomBoundNat
  split_ifs <;> omega

private theorem refineStepsNat_polyTime :
    ComputableInPolyTime refineStepsNat encRatPoly encUnary := by
  unfold refineStepsNat
  have hH := denomBoundNat_polyTime
  have hH2 := binary_mul' hH hH
  have hB := cauchyBoundNat_computableInPolyTime
  have hprod : ComputableInPolyTime
      (fun sq : List ℚ => 8 * cauchyBoundNat sq * (denomBoundNat sq) ^ 2) encRatPoly encNat :=
    (binary_mul' (binary_mul' (const 8) hB) hH2).of_enc_eq fun sq => by simp [pow_two]
  exact unary_add'
    (unary_add' (binary_size.comp hprod)
      (unary_mul' (const 3) mignotteBisectionDepth_computableInPolyTime))
    (const 3)

private def ScaledDyadic (D M e : ℕ) (q : ℚ) : Prop :=
  ∃ z : ℤ, q = (z : ℚ) / ((D : ℚ) * (2 : ℚ) ^ e) ∧ z.natAbs ≤ M * 2 ^ e

private theorem ScaledDyadic.zero {D M : ℕ} {q : ℚ} {d' : ℕ} (hd' : 0 < d')
    (hD : q.den * d' = D) (hM : q.num.natAbs * d' ≤ M) :
    ScaledDyadic D M 0 q := by
  refine ⟨q.num * (d' : ℤ), ?_, ?_⟩
  · rw [pow_zero, mul_one, ← hD, Int.cast_mul, Int.cast_natCast, Nat.cast_mul,
      mul_div_mul_right _ _ (Nat.cast_ne_zero.mpr hd'.ne'), Rat.num_div_den]
  · simpa [Int.natAbs_mul, Int.natAbs_natCast] using hM

private theorem ScaledDyadic.lift {D M e : ℕ} {q : ℚ} (hD : 1 ≤ D) (hq : ScaledDyadic D M e q) :
    ScaledDyadic D M (e + 1) q := by
  obtain ⟨z, hz, hle⟩ := hq
  refine ⟨2 * z, ?_, ?_⟩
  · have hD0 : (D : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    rw [hz, pow_succ, Int.cast_mul, Int.cast_ofNat]; field_simp [hD0]
  · rw [Int.natAbs_mul, show (2 : ℤ).natAbs = 2 from rfl, pow_succ]; nlinarith

private theorem ScaledDyadic.mid {D M e : ℕ} {a b : ℚ} (hD : 1 ≤ D)
    (ha : ScaledDyadic D M e a) (hb : ScaledDyadic D M e b) :
    ScaledDyadic D M (e + 1) ((a + b) / 2) := by
  obtain ⟨za, hza, hla⟩ := ha; obtain ⟨zb, hzb, hlb⟩ := hb
  refine ⟨za + zb, ?_, ?_⟩
  · have hD0 : (D : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    rw [hza, hzb, pow_succ, Int.cast_add]; field_simp [hD0]
  · calc (za + zb).natAbs ≤ za.natAbs + zb.natAbs := Int.natAbs_add_le _ _
      _ ≤ M * 2 ^ e + M * 2 ^ e := Nat.add_le_add hla hlb
      _ = M * 2 ^ (e + 1) := by rw [pow_succ]; ring

private theorem ScaledDyadic.length_encRat_le {D M e K : ℕ} {q : ℚ} (hD : 1 ≤ D)
    (hq : ScaledDyadic D M e q) (hD_le : D * 2 ^ e ≤ 2 ^ K) (hM_le : M * 2 ^ e ≤ 2 ^ K) :
    (encRat q).length ≤ 3 * K + 6 := by
  obtain ⟨z, hz, hle⟩ := hq
  have hden_ne : ((D * 2 ^ e : ℕ) : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr (by positivity)
  have hq_div : q = Rat.divInt z ((D * 2 ^ e : ℕ) : ℤ) := by
    rw [Rat.divInt_eq_div, hz]; push_cast; rfl
  have hn : q.num.natAbs ≤ 2 ^ K := by
    rw [hq_div]; exact (Rat.natAbs_num_divInt_le _ _ hden_ne).trans (hle.trans hM_le)
  have hd : q.den ≤ 2 ^ K := by
    rw [hq_div]; refine (Rat.den_divInt_le _ _ hden_ne).trans ?_
    rw [Int.natAbs_natCast]; exact hD_le
  exact length_encRat_le_of_pow_bound hn hd

private theorem bisectInterval_polyTime :
    ComputableInPolyTime
      (fun p : (List (List ℚ) × ℕ) × RootInterval => bisectInterval p.1.1 p.1.2 p.2)
      (encPair (encPair encSturmSeq encUnary) encRootInterval) (encPair encRat encRat) := by
  unfold bisectInterval
  have hstep : ComputableInPolyTime
      (fun p : List (List ℚ) × (ℚ × ℚ) => bisectStep p.1 p.2)
      (encPair encSturmSeq (encPair encRat encRat)) (encPair encRat encRat) := by
    unfold bisectStep
    have hseq := fst encSturmSeq (encPair encRat encRat)
    have ha := (fst encRat encRat).comp (snd encSturmSeq (encPair encRat encRat))
    have hb := (snd encRat encRat).comp (snd encSturmSeq (encPair encRat encRat))
    have hm := rat_div' (rat_add' ha hb) (const (2 : ℚ))
    have hva := sturmVariationsList_computableInPolyTime.comp (hseq.prod ha)
    have hvm := sturmVariationsList_computableInPolyTime.comp (hseq.prod hm)
    exact (unary_beq hva hvm).ite_decide (hm.prod hb) (ha.prod hm)
  refine iterateWith
    (par := fun p : (List (List ℚ) × ℕ) × RootInterval => p.1.1)
    (count := fun p => p.1.2)
    (init := fun p => (p.2.lower, p.2.upper))
    (step := bisectStep)
    ((fst encSturmSeq encUnary).comp (fst (encPair encSturmSeq encUnary) encRootInterval))
    ((snd encSturmSeq encUnary).comp (fst (encPair encSturmSeq encUnary) encRootInterval))
    ((encRootInterval_lower_polyTime (snd (encPair encSturmSeq encUnary) encRootInterval)).prod
      (encRootInterval_upper_polyTime (snd (encPair encSturmSeq encUnary) encRootInterval)))
    hstep
    (bound := fun p => 30 * ((encPair (encPair encSturmSeq encUnary) encRootInterval p).length + 1))
    (PolyBounded.of_forall_le 30 1 fun _ => by simp only [pow_one, le_refl])
    fun p i hi => ?_
  set L := (encPair (encPair encSturmSeq encUnary) encRootInterval p).length
  have hsteps_le : p.1.2 ≤ L := by
    have h1 := (length_le_encPair_right encSturmSeq encUnary p.1).trans
      (length_le_encPair_left _ encRootInterval p)
    simpa only [encUnary_apply, List.length_replicate] using h1
  have hJ_len : (encRootInterval p.2).length ≤ L := length_le_encPair_right _ _ p
  have hl_len : (encRat p.2.lower).length ≤ L :=
    (length_le_encPair_left encRat encRat (p.2.lower, p.2.upper)).trans
      (by simpa [encRootInterval_apply, encRootIntervalFields] using hJ_len)
  have hu_len : (encRat p.2.upper).length ≤ L :=
    (length_le_encPair_right encRat encRat (p.2.lower, p.2.upper)).trans
      (by simpa [encRootInterval_apply, encRootIntervalFields] using hJ_len)
  have hln := (natAbs_num_lt_two_pow_length_encRat p.2.lower).le.trans
    (Nat.pow_le_pow_right zero_lt_two hl_len)
  have hld := (den_lt_two_pow_length_encRat p.2.lower).le.trans
    (Nat.pow_le_pow_right zero_lt_two hl_len)
  have hun := (natAbs_num_lt_two_pow_length_encRat p.2.upper).le.trans
    (Nat.pow_le_pow_right zero_lt_two hu_len)
  have hud := (den_lt_two_pow_length_encRat p.2.upper).le.trans
    (Nat.pow_le_pow_right zero_lt_two hu_len)
  -- `ScaledDyadic` invariant for `bisectStep`
  let D := p.2.lower.den * p.2.upper.den
  let M := max (p.2.lower.num.natAbs * p.2.upper.den) (p.2.upper.num.natAbs * p.2.lower.den)
  have hD1 : 1 ≤ D := Nat.mul_pos p.2.lower.den_pos p.2.upper.den_pos
  have htrace : ∀ j : ℕ,
      let ab := (bisectStep p.1.1)^[j] (p.2.lower, p.2.upper)
      ScaledDyadic D M j ab.1 ∧ ScaledDyadic D M j ab.2 := fun j => by
    induction j with
    | zero =>
      exact ⟨.zero p.2.upper.den_pos rfl (le_max_left _ _),
        .zero p.2.lower.den_pos (mul_comm _ _) (le_max_right _ _)⟩
    | succ j ih =>
      rw [Function.iterate_succ_apply']
      dsimp only [bisectStep]
      have hm := ih.1.mid hD1 ih.2
      split_ifs
      · exact ⟨hm, ih.2.lift hD1⟩
      · exact ⟨ih.1.lift hD1, hm⟩
  obtain ⟨ha, hb⟩ := htrace i
  have hpow : 2 ^ L * 2 ^ L * 2 ^ i ≤ 2 ^ (3 * L) := by
    rw [← pow_add, ← pow_add]; exact Nat.pow_le_pow_right zero_lt_two (by omega)
  have hD : D * 2 ^ i ≤ 2 ^ (3 * L) :=
    (Nat.mul_le_mul_right _ (Nat.mul_le_mul hld hud)).trans hpow
  have hM : M * 2 ^ i ≤ 2 ^ (3 * L) :=
    (Nat.mul_le_mul_right _ (max_le (Nat.mul_le_mul hln hud) (Nat.mul_le_mul hun hld))).trans hpow
  have ha_enc := ha.length_encRat_le hD1 hD hM
  have hb_enc := hb.length_encRat_le hD1 hD hM
  rw [length_encPair]
  omega

private theorem ratReconstructNonneg_polyTime :
    ComputableInPolyTime (fun p : ℕ × (ℕ × ℕ) => ratReconstructNonneg p.1 p.2.1 p.2.2)
      (encPair encNat (encPair encNat encNat)) encRat := by
  unfold ratReconstructNonneg
  have hstep : ComputableInPolyTime
      (fun p : ℕ × EuclidReconState => euclidReconStep p.1 p.2)
      (encPair encNat encEuclidReconState) encEuclidReconState := by
    unfold euclidReconStep
    have hH2 := fst encNat encEuclidReconState
    have hst := snd encNat encEuclidReconState
    have ha0 := encEuclidReconState_a0_polyTime hst; have ha1 := encEuclidReconState_a1_polyTime hst
    have hp0 := encEuclidReconState_p0_polyTime hst; have hq0 := encEuclidReconState_q0_polyTime hst
    have hp1 := encEuclidReconState_p1_polyTime hst; have hq1 := encEuclidReconState_q1_polyTime hst
    have hm := binary_div' ha0 ha1; have hq2 := binary_add' (binary_mul' hm hq1) hq0
    have hnext := encEuclidReconState_mk_polyTime ha1 (binary_mod' ha0 ha1) hp1 hq1
      (binary_add' (binary_mul' hm hp1) hp0) hq2
    exact (beq ha1 (const 0)).ite_decide hst ((binary_lt' hH2 hq2).ite_decide hst hnext)
  have hH := fst encNat (encPair encNat encNat)
  have hA := (fst encNat encNat).comp (snd encNat (encPair encNat encNat))
  have hB := (snd encNat encNat).comp (snd encNat (encPair encNat encNat))
  have hsteps := unary_mul' (const 2)
    (unary_add' (unary_add' (binary_size.comp hA) (binary_size.comp hB)) (const 2))
  have hinit := encEuclidReconState_mk_polyTime hA hB (const 0) (const 1) (const 1) (const 0)
  have hiter := iterateWith (step := euclidReconStep) (binary_mul' (const 2) hH) hsteps hinit hstep
    (bound := fun p => 120 * ((encPair encNat (encPair encNat encNat) p).length + 1))
    (PolyBounded.of_forall_le 120 1 fun _ => by simp only [pow_one, le_refl])
    fun p i _ => by
      set L := (encPair encNat (encPair encNat encNat) p).length
      have hA_len : p.2.1.size ≤ L := by
        have h1 : (encNat p.2.1).length ≤ L :=
          (length_le_encPair_left encNat encNat p.2).trans
            (length_le_encPair_right encNat (encPair encNat encNat) p)
        simpa only [encNat_apply, List.length_map, ← Nat.size_eq_bits_len] using h1
      have hB_len : p.2.2.size ≤ L := by
        have h1 : (encNat p.2.2).length ≤ L :=
          (length_le_encPair_right encNat encNat p.2).trans
            (length_le_encPair_right encNat (encPair encNat encNat) p)
        simpa only [encNat_apply, List.length_map, ← Nat.size_eq_bits_len] using h1
      have hA_lt : p.2.1 < 2 ^ L :=
        (Nat.lt_size_self p.2.1).trans_le (Nat.pow_le_pow_right (by omega) hA_len)
      have hB_lt : p.2.2 < 2 ^ L :=
        (Nat.lt_size_self p.2.2).trans_le (Nat.pow_le_pow_right (by omega) hB_len)
      have hAB : (p.2.1 + p.2.2).size ≤ L + 1 := Nat.size_le.mpr (by rw [pow_succ]; omega)
      have hA1 : (p.2.1 + 1).size ≤ L + 1 :=
        Nat.size_le.mpr (by rw [pow_succ]; have := Nat.one_le_two_pow (n := L); omega)
      have hB1 : (p.2.2 + 1).size ≤ L + 1 :=
        Nat.size_le.mpr (by rw [pow_succ]; have := Nat.one_le_two_pow (n := L); omega)
      let init0 : EuclidReconState :=
        { a0 := p.2.1, a1 := p.2.2, p0 := 0, q0 := 1, p1 := 1, q1 := 0 }
      set st := (euclidReconStep (2 * p.1))^[i] init0
      have hbounds : st.a0 ≤ p.2.1 + p.2.2 ∧ st.a1 ≤ p.2.1 + p.2.2 ∧
          st.p0 ≤ p.2.1 + 1 ∧ st.p1 ≤ p.2.1 + 1 ∧ st.q0 ≤ p.2.2 + 1 ∧ st.q1 ≤ p.2.2 + 1 := by
        by_cases hH0 : p.1 = 0
        · have hfix : euclidReconStep 0 init0 = init0 := by
            unfold euclidReconStep
            by_cases h0 : p.2.2 = 0 <;> simp [init0, h0]
          have hst_init : st = init0 := by
            dsimp only [st]; rw [hH0, mul_zero]; exact Function.iterate_fixed hfix i
          rw [hst_init]; dsimp only [init0]; omega
        · have hinv : EuclidInv p.2.1 p.2.2 (2 * p.1) st := by
            have : ∀ j, EuclidInv p.2.1 p.2.2 (2 * p.1)
                ((euclidReconStep (2 * p.1))^[j] init0) := fun j => by
              induction j with
              | zero => exact euclidInv_init (Nat.pos_of_ne_zero hH0)
              | succ j ih => rw [Function.iterate_succ_apply']; exact euclidReconStep_inv ih
            exact this i
          exact hinv.2.2.2.2
      have hs (x n : ℕ) (h : x ≤ n) (hn : n.size ≤ L + 1) : (encNat x).length ≤ L + 1 := by
        simpa [encNat_apply, Nat.size_eq_bits_len] using (Nat.size_le_size h).trans hn
      have ha0s := hs st.a0 _ hbounds.1 hAB; have ha1s := hs st.a1 _ hbounds.2.1 hAB
      have hp0s := hs st.p0 _ hbounds.2.2.1 hA1; have hq0s := hs st.q0 _ hbounds.2.2.2.2.1 hB1
      have hp1s := hs st.p1 _ hbounds.2.2.2.1 hA1; have hq1s := hs st.q1 _ hbounds.2.2.2.2.2 hB1
      rw [encEuclidReconState_apply]; dsimp only [encEuclidReconStateFields]
      rw [length_encPair, length_encPair, length_encPair, length_encPair, length_encPair]
      change 2 * (encNat st.a0).length + 1 + (2 * (encNat st.a1).length + 1 +
          (2 * (encNat st.p0).length + 1 + (2 * (encNat st.q0).length + 1 +
            (2 * (encNat st.p1).length + 1 + (encNat st.q1).length)))) ≤ 120 * (L + 1)
      omega
  exact rat_div' (rat_natCast.comp (encEuclidReconState_p1_polyTime hiter))
    (rat_natCast.comp (encEuclidReconState_q1_polyTime hiter))

private theorem ratReconstruct_polyTime :
    ComputableInPolyTime (fun p : ℕ × ℚ => ratReconstruct p.1 p.2)
      (encPair encNat encRat) encRat := by
  unfold ratReconstruct
  have hH := fst encNat encRat; have hx := snd encNat encRat
  have hr := ratReconstructNonneg_polyTime.comp
    (hH.prod ((intBin_natAbs.comp (rat_num.comp hx)).prod (rat_den.comp hx)))
  exact (rat_le' (const (0 : ℚ)) hx).ite_decide hr (rat_neg' hr)

/-- **Polynomial-time computability of `findRationalRoots`**: finding all rational roots of a
univariate rational polynomial is computable in polynomial time on multi-tape Turing machines. -/
@[fun_prop]
theorem findRationalRoots_computableInPolyTime :
    ComputableInPolyTime findRationalRoots encRatPoly (encList encRat) := by
  unfold findRationalRoots
  have ht := trim_computableInPolyTime; have hsq := sqfreePartList_polyTime
  have hseq := sturmSeqList_computableInPolyTime.comp hsq
  have hH := denomBoundNat_polyTime.comp hsq
  have hsteps := refineStepsNat_polyTime.comp hsq
  have hints := isolateRootsTotal_computableInPolyTime.comp hsq
  have hpar := id'.prod (hsq.prod (hseq.prod (hsteps.prod hH)))
  have hstep : ComputableInPolyTime
      (fun q : (List ℚ × (List ℚ × (List (List ℚ) × (ℕ × ℕ)))) × RootInterval =>
        rootsFromInterval q.1.1 q.1.2.1 q.1.2.2.1 q.1.2.2.2.1 q.1.2.2.2.2 q.2)
      (encPair (encPair encRatPoly (encPair encRatPoly
        (encPair encSturmSeq (encPair encUnary encNat)))) encRootInterval)
      (encList encRat) := by
    unfold rootsFromInterval
    let encP := encPair encRatPoly (encPair encRatPoly
      (encPair encSturmSeq (encPair encUnary encNat)))
    have hp := fst encP encRootInterval
    have hJ := snd encP encRootInterval
    have hcs := hp.fst'; have hsq' := hp.snd'.fst'; have hseq' := hp.snd'.snd'.fst'
    have hsteps' := hp.snd'.snd'.snd'.fst'; have hH' := hp.snd'.snd'.snd'.snd'
    have hlow := encRootInterval_lower_polyTime hJ; have hup := encRootInterval_upper_polyTime hJ
    have hbis := bisectInterval_polyTime.comp ((hseq'.prod hsteps').prod hJ)
    have hr := (rat_isZero' (evalCoeffList_computableInPolyTime.comp
      (hlow.prod hsq'))).ite_decide hlow (ratReconstruct_polyTime.comp (hH'.prod hbis.snd'))
    have hcond := bool_and' (rat_le' hlow hr)
      (bool_and' (rat_le' hr hup)
        (rat_isZero' (evalCoeffList_computableInPolyTime.comp (hr.prod hcs))))
    exact (hcond.ite ((cons encRat).comp (hr.prod (const []))) (const [])).of_enc_eq fun q =>
      congrArg (encList encRat) (by dsimp only [Function.comp_apply]; split_ifs <;> simp_all)
  have hflat := flatMapWith hstep hpar hints
  exact ((listIsEmpty' encRat).comp ht).ite (const []) hflat

end Cslib.Complexity.RealAlgebraic
