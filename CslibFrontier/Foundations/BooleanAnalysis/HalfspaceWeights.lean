module

public import Cslib.Foundations.Data.BitString
public import CslibFrontier.Foundations.BooleanAnalysis.PolynomialThreshold
public import CslibFrontier.Foundations.Data.BitString.Sign
import CslibFrontier.Foundations.BooleanAnalysis.Degree
import CslibFrontier.Foundations.BooleanAnalysis.Fourier
import CslibFrontier.Foundations.BooleanAnalysis.LowDegree
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Matrix.AbsoluteValue
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Integer-Weight Bounds for Linear Threshold Functions and Threshold Density

This module provides foundational results on polynomial threshold representations of Boolean
functions on `{0, 1}^n`:

1. **Integer-weight representation of linear threshold functions (Muroga's theorem):** every
   degree-1 polynomial threshold function (`Cslib.BitString.IsPTF 1 f`) admits an integer-weight
   representation with weights and threshold bounded in absolute value by `(n + 1)!` and unit
   separation margin on every input in `{0, 1}^n`.
2. **Threshold degree and threshold density:** definitions of the minimum sign-representing degree
   (`thresholdDegree`) and minimum parity sparsity (`thresholdDensity`), together with the
   multiplexer transform `kpTransform` and the exponential degree-to-density inequality
   `2 ^ thresholdDegree f ≤ thresholdDensity (kpTransform f)` (Krause and Pudlák).

## Main definitions

* `CslibFrontier.Foundations.BooleanAnalysis.thresholdDegree`: minimum polynomial threshold degree
  of a Boolean function.
* `CslibFrontier.Foundations.BooleanAnalysis.thresholdDensity`: minimum number of parity characters
  needed to sign-represent a Boolean function.
* `CslibFrontier.Foundations.BooleanAnalysis.kpTransform`: the `3n`-bit multiplexer transform
  sending `(x, y, z)` to `f(i ↦ (¬z_i ∧ x_i) ∨ (z_i ∧ y_i))`.

## Main results

* `CslibFrontier.Foundations.BooleanAnalysis.exists_int_weights_of_isPTF_one`: integer-weight
  bound `|w_i|, |θ| ≤ (n + 1)!` with unit margin for every linear threshold function.
* `CslibFrontier.Foundations.BooleanAnalysis.two_pow_thresholdDegree_le_thresholdDensity_kp`:
  exponential degree-to-density lower bound
  `2 ^ thresholdDegree f ≤ thresholdDensity (kpTransform f)`.
-/

public section

namespace CslibFrontier.Foundations.BooleanAnalysis

open Finset
open scoped Matrix BigOperators
open Cslib (BooleanFunction BitString)
open Cslib.BitString (bitVal signVal chi fourierCoeff IsPTF IsPTFOn)

/-- Minimum polynomial threshold degree of a Boolean function `f : BooleanFunction n`. -/
@[expose] noncomputable def thresholdDegree {n : ℕ} (f : BooleanFunction n) : ℕ :=
  sInf {d : ℕ | IsPTF d f}

/-- Every Boolean function on `n` bits has threshold degree at most `n`. -/
theorem thresholdDegree_le_card {n : ℕ} (f : BooleanFunction n) :
    thresholdDegree f ≤ n :=
  Nat.sInf_le (Set.mem_ofPred.2 (by simpa using Cslib.BitString.isPTF_card f))

/-- Characterization `thresholdDegree f ≤ d ↔ IsPTF d f`. -/
theorem thresholdDegree_le_iff {n : ℕ} {f : BooleanFunction n} {d : ℕ} :
    thresholdDegree f ≤ d ↔ IsPTF d f := by
  constructor
  · intro h
    have hmem : IsPTF (thresholdDegree f) f :=
      Nat.sInf_mem (s := {k : ℕ | IsPTF k f})
        ⟨n, Set.mem_ofPred.2 (by simpa using Cslib.BitString.isPTF_card f)⟩
    exact hmem.mono h
  · intro h
    exact Nat.sInf_le (Set.mem_ofPred.2 h)

/-- Minimum parity sparsity (threshold density) of a Boolean function `f : BooleanFunction n`. -/
@[expose] noncomputable def thresholdDensity {n : ℕ} (f : BooleanFunction n) : ℕ :=
  sInf {k : ℕ | ∃ S : Finset (Finset (Fin n)), S.card = k ∧ IsPTFOn S f}

/-- Every Boolean function on `n` bits has threshold density at most `2 ^ n`. -/
theorem thresholdDensity_le_two_pow {n : ℕ} (f : BooleanFunction n) :
    thresholdDensity f ≤ 2 ^ n := by
  refine Nat.sInf_le ⟨Finset.univ, ?_, ?_⟩
  · simp [Fintype.card_finset]
  · exact Cslib.BitString.isPTFOn_of_fourierCoeff_eq_zero fun S hS =>
      absurd (Finset.mem_univ S) hS

/-- Every Boolean function has threshold density at least `1`. -/
theorem one_le_thresholdDensity {n : ℕ} (f : BooleanFunction n) :
    1 ≤ thresholdDensity f := by
  have hne : ({k : ℕ | ∃ S : Finset (Finset (Fin n)), S.card = k ∧ IsPTFOn S f}).Nonempty :=
    ⟨2 ^ n, Finset.univ, by simp [Fintype.card_finset],
      Cslib.BitString.isPTFOn_of_fourierCoeff_eq_zero fun S hS =>
        absurd (Finset.mem_univ S) hS⟩
  obtain ⟨S, hScard, hS⟩ := Nat.sInf_mem hne
  by_contra hlt
  dsimp only [thresholdDensity] at hlt
  have h0 : S.card = 0 := by omega
  rw [Finset.card_eq_zero] at h0
  subst h0
  obtain ⟨p, hp0, hpsign⟩ := hS
  have hpzero : p = 0 := by
    funext x
    rw [← Cslib.BitString.sum_fourierCoeff_mul_chi p x]
    simp [hp0]
  have hpos := hpsign (fun _ => false)
  simp [hpzero] at hpos

/-- The `3n`-bit multiplexer transform sending `(x, y, z) ∈ ({0, 1}^n)^3` to
`f(i ↦ (¬z_i ∧ x_i) ∨ (z_i ∧ y_i))`. -/
@[expose] def kpTransform {n : ℕ} (f : BooleanFunction n) : BooleanFunction (3 * n) :=
  fun v =>
    f fun i =>
      let x := v ⟨i.1, by omega⟩
      let y := v ⟨n + i.1, by omega⟩
      let z := v ⟨2 * n + i.1, by omega⟩
      (!z && x) || (z && y)

/-- Muroga's integer-weight bound: every linear threshold function (`IsPTF 1 f`) on `{0, 1}^n`
admits integer weights `w : Fin n → ℤ` and threshold `θ : ℤ` bounded in magnitude by `(n + 1)!`,
with unit margin `1 ≤ signVal (f x) * (∑ i, w_i x_i - θ)` for every `x ∈ {0, 1}^n`. -/
theorem exists_int_weights_of_isPTF_one {n : ℕ} {f : BooleanFunction n} (hf : IsPTF 1 f) :
    ∃ (w : Fin n → ℤ) (θ : ℤ),
      (∀ i : Fin n, |(w i : ℝ)| ≤ ((n + 1).factorial : ℝ)) ∧
      |(θ : ℝ)| ≤ ((n + 1).factorial : ℝ) ∧
      ∀ x : BitString n,
        1 ≤ signVal (f x) * (∑ i : Fin n, (w i : ℝ) * bitVal ℝ (x i) - (θ : ℝ)) := by
  -- Extract real linear weights `(w0, θ0)` from the degree-1 Fourier representation.
  obtain ⟨p, hpdeg, hpsign⟩ := Cslib.BitString.isPTF_iff.1 hf
  let w0 : Fin n → ℝ := fun i => -2 * fourierCoeff p {i}
  let θ0 : ℝ := -(fourierCoeff p ∅ + ∑ i : Fin n, fourierCoeff p {i})
  have hp_lin : ∀ x : BitString n, p x = ∑ i : Fin n, w0 i * bitVal ℝ (x i) - θ0 := by
    intro x
    rw [← Cslib.BitString.sum_fourierCoeff_mul_chi p x]
    have hsub : (Finset.univ.filter fun S : Finset (Fin n) => S.card ≤ 1) =
        insert ∅ (Finset.univ.image fun i : Fin n => ({i} : Finset (Fin n))) := by
      ext S
      simp only [mem_filter, mem_univ, true_and, mem_insert, mem_image]
      constructor
      · intro hcard
        rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hcard with h0 | h1
        · exact Or.inl (Finset.card_eq_zero.1 h0)
        · obtain ⟨i, rfl⟩ := Finset.card_eq_one.1 h1
          exact Or.inr ⟨i, rfl⟩
      · rintro (rfl | ⟨i, rfl⟩) <;> simp
    have htrim : ∑ S : Finset (Fin n), fourierCoeff p S * chi ℝ S x =
        ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin n) => S.card ≤ 1),
          fourierCoeff p S * chi ℝ S x :=
      (Finset.sum_subset (subset_univ _) fun S _ hS => by
        have hgt : 1 < S.card := by
          simp only [mem_filter, mem_univ, true_and, not_le] at hS; exact hS
        rw [hpdeg S hgt, zero_mul]).symm
    rw [htrim, hsub, Finset.sum_insert (by simp)]
    have hchi0 : chi ℝ (∅ : Finset (Fin n)) x = 1 := by simp [Cslib.BitString.chi]
    rw [hchi0, mul_one]
    rw [Finset.sum_image (fun a _ b _ hab => Finset.singleton_injective hab)]
    have hchi1 : ∀ i : Fin n, chi ℝ ({i} : Finset (Fin n)) x = 1 - 2 * bitVal ℝ (x i) := by
      intro i
      cases hxi : x i
      · simp [Cslib.BitString.chi, Cslib.BitString.bitVal, hxi]
      · simp [Cslib.BitString.chi, Cslib.BitString.bitVal, hxi]; norm_num
    simp_rw [hchi1]
    dsimp only [w0, θ0]
    have hsplit : ∑ i : Fin n, fourierCoeff p {i} * (1 - 2 * bitVal ℝ (x i)) =
        (∑ i : Fin n, fourierCoeff p {i}) +
          ∑ i : Fin n, (-2 * fourierCoeff p {i}) * bitVal ℝ (x i) := by
      rw [← Finset.sum_add_distrib]
      exact sum_congr rfl fun i _ => by ring
    rw [hsplit]; ring
  -- Define integer row vectors `rowInt x : Fin (n + 1) → ℤ` and real lifts `row x`.
  let rowInt (x : BitString n) : Fin (n + 1) → ℤ :=
    Fin.snoc (fun i : Fin n => if f x then -(bitVal ℤ (x i)) else bitVal ℤ (x i))
      (if f x then 1 else -1)
  let row (x : BitString n) : Fin (n + 1) → ℝ := fun j => (rowInt x j : ℝ)
  have hrow_abs : ∀ x j, |rowInt x j| ≤ 1 := by
    intro x j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simp only [rowInt, Fin.snoc_last]; cases f x <;> norm_num
    · simp only [rowInt, Fin.snoc_castSucc]; cases f x <;> cases x i <;>
        simp [Cslib.BitString.bitVal]
  have hrow_dot : ∀ (x : BitString n) (v : Fin (n + 1) → ℝ),
      row x ⬝ᵥ v = signVal (f x) *
        (∑ i : Fin n, v i.castSucc * bitVal ℝ (x i) - v (Fin.last n)) := by
    intro x v
    rw [dotProduct, Fin.sum_univ_castSucc]
    simp only [row, rowInt, Fin.snoc_castSucc, Fin.snoc_last]
    cases f x
    · simp only [Bool.false_eq_true, ↓reduceIte, Int.cast_neg, Int.cast_one,
        Cslib.BitString.signVal_false, one_mul, neg_one_mul]
      rw [sub_eq_add_neg]
      congr 1
      refine sum_congr rfl fun i _ => ?_
      cases x i <;> simp [Cslib.BitString.bitVal]
    · simp only [↓reduceIte, Int.cast_neg, Int.cast_one, Cslib.BitString.signVal_true,
        neg_one_mul, one_mul]
      rw [neg_sub, sub_eq_neg_add]
      congr 1
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      cases x i <;> simp [Cslib.BitString.bitVal]
  classical
  let vraw : Fin (n + 1) → ℝ := Fin.snoc w0 θ0
  have hpos_raw : ∀ x : BitString n, 0 < row x ⬝ᵥ vraw := by
    intro x
    rw [hrow_dot]
    simp only [vraw, Fin.snoc_castSucc, Fin.snoc_last, ← hp_lin x]
    exact hpsign x
  set m0 : ℝ := Finset.univ.inf' Finset.univ_nonempty fun x => row x ⬝ᵥ vraw
  have hm0_pos : 0 < m0 := (Finset.lt_inf'_iff _).2 fun x _ => hpos_raw x
  let K : Set (Fin (n + 1) → ℝ) := {v | ∀ x : BitString n, 1 ≤ row x ⬝ᵥ v}
  have hv0_mem : m0⁻¹ • vraw ∈ K := by
    intro x
    rw [dotProduct_smul, smul_eq_mul, inv_mul_eq_div, one_le_div hm0_pos]
    exact Finset.inf'_le _ (mem_univ x)
  let active (v : Fin (n + 1) → ℝ) : Finset (BitString n) :=
    Finset.univ.filter fun x => row x ⬝ᵥ v = 1
  let activeSpan (v : Fin (n + 1) → ℝ) : Submodule ℝ (Fin (n + 1) → ℝ) :=
    Submodule.span ℝ ((active v : Set (BitString n)).image row)
  let activeRank (v : Fin (n + 1) → ℝ) : ℕ := Module.finrank ℝ (activeSpan v)
  let Rset : Finset ℕ := (range (n + 2)).filter fun r => ∃ v ∈ K, activeRank v = r
  have hRne : Rset.Nonempty := by
    refine ⟨activeRank (m0⁻¹ • vraw), mem_filter.2 ⟨mem_range.2 ?_, m0⁻¹ • vraw, hv0_mem, rfl⟩⟩
    have hle : activeRank (m0⁻¹ • vraw) ≤ n + 1 := by
      calc activeRank (m0⁻¹ • vraw)
          ≤ Module.finrank ℝ (Fin (n + 1) → ℝ) := Submodule.finrank_le _
        _ = n + 1 := by simp
    omega
  set rMax := Rset.max' hRne
  obtain ⟨v, hvK, hvr⟩ := (mem_filter.1 (Finset.max'_mem Rset hRne)).2
  have hfull : activeRank v = n + 1 := by
    by_contra hne_full
    have hle_tot : activeRank v ≤ n + 1 := by
      calc activeRank v ≤ Module.finrank ℝ (Fin (n + 1) → ℝ) := Submodule.finrank_le _
        _ = n + 1 := by simp
    have hlt_full : activeRank v < n + 1 := lt_of_le_of_ne hle_tot hne_full
    let Aact : Matrix {x // x ∈ active v} (Fin (n + 1)) ℝ :=
      Matrix.of fun x j => row x.1 j
    have hker_pos : 0 < Module.finrank ℝ (LinearMap.ker Aact.mulVecLin) := by
      have hrn := LinearMap.finrank_range_add_finrank_ker Aact.mulVecLin
      have hdom : Module.finrank ℝ (Fin (n + 1) → ℝ) = n + 1 := by simp
      have hrange_le : Module.finrank ℝ (LinearMap.range Aact.mulVecLin) ≤ activeRank v := by
        have hr1 : Module.finrank ℝ (LinearMap.range Aact.mulVecLin) = Aact.rank := rfl
        have hr2 : Aact.rank = Aactᵀ.rank := (Matrix.rank_transpose Aact).symm
        rw [hr1, hr2, Matrix.rank]
        have hsub : LinearMap.range Aactᵀ.mulVecLin ≤ activeSpan v := by
          rintro y ⟨c, rfl⟩
          have heq : Aactᵀ.mulVecLin c = ∑ x : {x // x ∈ active v}, c x • row x.1 := by
            funext j
            simp [Matrix.mulVec, dotProduct, Aact, Finset.sum_apply, mul_comm]
          rw [heq]
          exact Submodule.sum_mem _ fun x _ =>
            Submodule.smul_mem _ _ (Submodule.subset_span ⟨x.1, x.2, rfl⟩)
        exact Submodule.finrank_mono hsub
      omega
    obtain ⟨u0, hu0_mem, hu0_ne⟩ : ∃ u0 ∈ LinearMap.ker Aact.mulVecLin, u0 ≠ 0 := by
      by_contra h
      push Not at h
      have hbot : LinearMap.ker Aact.mulVecLin = ⊥ :=
        (Submodule.eq_bot_iff _).2 h
      rw [hbot, finrank_bot] at hker_pos
      exact lt_irrefl 0 hker_pos
    have hu0_orth : ∀ x ∈ active v, row x ⬝ᵥ u0 = 0 := fun x hx => by
      have := congr_fun (LinearMap.mem_ker.1 hu0_mem) ⟨x, hx⟩
      simpa [Matrix.mulVecLin_apply, Matrix.mulVec, Aact] using this
    have hex_nz : ∃ x : BitString n, row x ⬝ᵥ u0 ≠ 0 := by
      by_contra hall
      push Not at hall
      have hlast : u0 (Fin.last n) = 0 := by
        have h0 := hall (fun _ => false)
        rw [hrow_dot] at h0
        simp only [Cslib.BitString.bitVal_false, mul_zero, sum_const_zero, zero_sub, mul_neg] at h0
        have hs : signVal (f fun _ => false) ≠ 0 := by
          cases f (fun _ => false) <;> simp
        exact mul_eq_zero.1 (neg_eq_zero.1 h0) |>.resolve_left hs
      have hcast : ∀ i : Fin n, u0 i.castSucc = 0 := by
        intro i
        have hi := hall (fun j => decide (j = i))
        rw [hrow_dot, hlast, sub_zero] at hi
        have hsum : ∑ j : Fin n, u0 j.castSucc * bitVal ℝ (decide (j = i)) = u0 i.castSucc := by
          rw [Finset.sum_eq_single i]
          · simp [Cslib.BitString.bitVal_true]
          · intro j _ hji; simp [hji, Cslib.BitString.bitVal_false]
          · intro hni; exact absurd (mem_univ i) hni
        rw [hsum] at hi
        have hs : signVal (f fun j => decide (j = i)) ≠ 0 := by
          cases f (fun j => decide (j = i)) <;> simp
        exact (mul_eq_zero.1 hi).resolve_left hs
      apply hu0_ne
      funext j
      exact Fin.lastCases hlast hcast j
    obtain ⟨x_nz, hx_nz⟩ := hex_nz
    let u : Fin (n + 1) → ℝ := if row x_nz ⬝ᵥ u0 < 0 then u0 else -u0
    have hu_orth : ∀ x ∈ active v, row x ⬝ᵥ u = 0 := fun x hx => by
      dsimp only [u]; split_ifs
      · exact hu0_orth x hx
      · rw [dotProduct_neg, hu0_orth x hx, neg_zero]
    have hex_neg : ∃ x : BitString n, row x ⬝ᵥ u < 0 := by
      refine ⟨x_nz, ?_⟩
      dsimp only [u]; split_ifs with hlt
      · exact hlt
      · rw [dotProduct_neg]
        have hpos : 0 < row x_nz ⬝ᵥ u0 := lt_of_le_of_ne (not_lt.1 hlt) (Ne.symm hx_nz)
        linarith
    set negSet : Finset (BitString n) := Finset.univ.filter fun x => row x ⬝ᵥ u < 0
    have hneg_ne : negSet.Nonempty :=
      let ⟨x, hx⟩ := hex_neg; ⟨x, mem_filter.2 ⟨mem_univ x, hx⟩⟩
    obtain ⟨xstar, hxstar_mem, hxstar_min⟩ :=
      Finset.exists_min_image negSet (fun x => (row x ⬝ᵥ v - 1) / -(row x ⬝ᵥ u)) hneg_ne
    set t : ℝ := (row xstar ⬝ᵥ v - 1) / -(row xstar ⬝ᵥ u)
    have hxstar_neg : row xstar ⬝ᵥ u < 0 := (mem_filter.1 hxstar_mem).2
    have hxstar_not_act : xstar ∉ active v := fun hact =>
      ne_of_lt hxstar_neg (hu_orth xstar hact)
    have ht_pos : 0 < t := by
      have hgt : 1 < row xstar ⬝ᵥ v :=
        lt_of_le_of_ne (hvK xstar) (Ne.symm fun heq => hxstar_not_act (mem_filter.2 ⟨mem_univ _,
          heq⟩))
      exact div_pos (by linarith) (by linarith)
    let v' : Fin (n + 1) → ℝ := v + t • u
    have hv'K : v' ∈ K := by
      intro x
      dsimp only [v']
      rw [dotProduct_add, dotProduct_smul, smul_eq_mul]
      by_cases hxneg : row x ⬝ᵥ u < 0
      · have hle := hxstar_min x (mem_filter.2 ⟨mem_univ x, hxneg⟩)
        have hpos_den : 0 < -(row x ⬝ᵥ u) := by linarith
        have hmul := (le_div_iff₀ hpos_den).1 hle
        linarith
      · push Not at hxneg
        nlinarith [hvK x]
    have hact_sub : active v ⊆ active v' := by
      intro x hx
      refine mem_filter.2 ⟨mem_univ x, ?_⟩
      dsimp only [v']
      rw [dotProduct_add, dotProduct_smul, smul_eq_mul, hu_orth x hx, mul_zero, add_zero]
      exact (mem_filter.1 hx).2
    have hxstar_act' : xstar ∈ active v' := by
      refine mem_filter.2 ⟨mem_univ xstar, ?_⟩
      dsimp only [v', t]
      rw [dotProduct_add, dotProduct_smul, smul_eq_mul]
      have hne : row xstar ⬝ᵥ u ≠ 0 := hxstar_neg.ne
      field_simp [hne]
      ring
    have hnot_mem_span : row xstar ∉ activeSpan v := by
      intro hmem
      have horth_span : ∀ y ∈ activeSpan v, y ⬝ᵥ u = 0 := by
        intro y hy
        induction hy using Submodule.span_induction with
        | mem z hz =>
          obtain ⟨x, hx, rfl⟩ := hz
          exact hu_orth x hx
        | zero => simp
        | add a b _ _ ha hb => rw [add_dotProduct, ha, hb, add_zero]
        | smul c a _ ha => rw [smul_dotProduct, smul_eq_mul, ha, mul_zero]
      exact (ne_of_lt hxstar_neg) (horth_span _ hmem)
    have hspan_lt : activeSpan v < activeSpan v' := by
      refine lt_of_le_of_ne (Submodule.span_mono (Set.image_mono (Finset.coe_subset.2 hact_sub))) ?_
      intro heq
      exact hnot_mem_span (heq ▸ Submodule.subset_span ⟨xstar, hxstar_act', rfl⟩)
    have hrank_lt : activeRank v < activeRank v' :=
      Submodule.finrank_lt_finrank_of_lt hspan_lt
    have hmem_R : activeRank v' ∈ Rset := by
      refine mem_filter.2 ⟨mem_range.2 ?_, v', hv'K, rfl⟩
      have hle : activeRank v' ≤ n + 1 :=
        (Submodule.finrank_le _).trans (by simp)
      omega
    have hle_max := Finset.le_max' Rset _ hmem_R
    omega
  have hspan_top : activeSpan v = ⊤ :=
    Submodule.eq_top_of_finrank_eq
      (by rw [show Module.finrank ℝ (activeSpan v) = activeRank v from rfl, hfull]; simp)
  have hgen : ⊤ ≤ Submodule.span ℝ (Set.range fun x : {x // x ∈ active v} => row x.1) := by
    rw [← hspan_top]
    refine Submodule.span_mono ?_
    rintro y ⟨x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  obtain ⟨s, hs_sub, hs_span, hs_indep⟩ :=
    exists_linearIndependent ℝ (Set.range fun x : {x // x ∈ active v} => row x.1)
  have hs_top : Submodule.span ℝ s = ⊤ := eq_top_iff.2 (hgen.trans hs_span.ge)
  let bS : Module.Basis s ℝ (Fin (n + 1) → ℝ) :=
    Module.Basis.mk hs_indep (by rw [Subtype.range_coe]; exact hs_top.ge)
  have hfin_s : s.Finite := (Set.finite_range _).subset hs_sub
  let _ : Fintype s := hfin_s.fintype
  have hcard_s : Fintype.card s = n + 1 := by
    have h := Module.finrank_eq_card_basis bS
    simp only [Module.finrank_fin_fun] at h
    exact h.symm
  let e : Fin (n + 1) ≃ s := (Fintype.equivFinOfCardEq hcard_s).symm
  have hpick : ∀ i : Fin (n + 1), ∃ x ∈ active v, row x = (e i).1 := fun i =>
    let ⟨x, hx⟩ := hs_sub (e i).2
    ⟨x.1, x.2, hx⟩
  choose xs hxs_act hxs_eq using hpick
  let B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ := Matrix.of fun i j => rowInt (xs i) j
  let BR : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ := B.map (Int.castRingHom ℝ)
  have hBR_eq : ∀ i j, BR i j = row (xs i) j := fun i j => rfl
  have hBR_mul : BR *ᵥ v = fun _ => (1 : ℝ) := by
    funext i
    have hi : row (xs i) ⬝ᵥ v = 1 := (mem_filter.1 (hxs_act i)).2
    simpa [Matrix.mulVec, dotProduct, hBR_eq] using hi
  have hBR_det_ne : BR.det ≠ 0 := by
    have hind : LinearIndependent ℝ (fun i : Fin (n + 1) => BR i) := by
      have heq : (fun i : Fin (n + 1) => BR i) = fun i => bS (e i) := by
        funext i j
        have := congr_fun (hxs_eq i) j
        simpa [bS, hBR_eq] using this
      rw [heq]
      exact bS.linearIndependent.comp e e.injective
    have hinj : Function.Injective BRᵀ.mulVecLin := by
      rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
      intro c hc
      have hsum : ∑ i : Fin (n + 1), c i • BR i = 0 := by
        funext j
        have hj := congr_fun (LinearMap.mem_ker.1 hc) j
        simpa [Matrix.vecMul, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm] using hj
      funext i
      exact Fintype.linearIndependent_iff.1 hind c hsum i
    have hsurj : Function.Surjective BRᵀ.mulVecLin :=
      LinearMap.injective_iff_surjective.1 hinj
    obtain ⟨U, hU⟩ : ∃ U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ, BRᵀ * U = 1 := by
      choose u hu using fun j : Fin (n + 1) => hsurj (Pi.single j 1)
      refine ⟨Matrix.of fun i j => u j i, ?_⟩
      ext i j
      have hj := congr_fun (hu j) i
      simpa [Matrix.mul_apply, Matrix.vecMul, Matrix.mulVec, dotProduct, Matrix.one_apply,
        Pi.single_apply, eq_comm, mul_comm] using hj
    intro h0
    have h1 := congrArg Matrix.det hU
    rw [Matrix.det_mul, Matrix.det_transpose, h0, zero_mul, Matrix.det_one] at h1
    exact zero_ne_one h1
  have hBdet_ne : B.det ≠ 0 := by
    intro h0
    apply hBR_det_ne
    have : BR.det = (B.det : ℝ) := ((Int.castRingHom ℝ).map_det B).symm
    rw [this, h0, Int.cast_zero]
  let sgnD : ℤ := if 0 < B.det then 1 else -1
  let D : ℤ := sgnD * B.det
  have hDpos : (0 : ℤ) < D := by
    dsimp only [D, sgnD]
    split_ifs with hpos
    · linarith
    · have hneg : B.det < 0 := lt_of_le_of_ne (not_lt.1 hpos) hBdet_ne
      linarith
  let wInt : Fin (n + 1) → ℤ := fun j => sgnD * (B.adjugate *ᵥ fun _ => (1 : ℤ)) j
  have hwInt_eq : ∀ j : Fin (n + 1), (wInt j : ℝ) = (D : ℝ) * v j := by
    intro j
    have hadj : BR.adjugate *ᵥ (BR *ᵥ v) = BR.det • v := by
      rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
    rw [hBR_mul] at hadj
    have hmap_adj : BR.adjugate = B.adjugate.map (Int.castRingHom ℝ) :=
      ((Int.castRingHom ℝ).map_adjugate B).symm
    have hmap_det : BR.det = (B.det : ℝ) := ((Int.castRingHom ℝ).map_det B).symm
    have hj := congr_fun hadj j
    rw [hmap_adj, hmap_det] at hj
    have hcast_mv : (B.adjugate.map (Int.castRingHom ℝ) *ᵥ fun _ => (1 : ℝ)) j =
        ((B.adjugate *ᵥ fun _ => (1 : ℤ)) j : ℝ) := by
      simp [Matrix.mulVec, dotProduct]
    rw [hcast_mv, Pi.smul_apply, smul_eq_mul] at hj
    dsimp only [wInt, D]
    rw [Int.cast_mul, Int.cast_mul, hj]
    ring
  have hwInt_bound : ∀ j : Fin (n + 1), |(wInt j : ℝ)| ≤ ((n + 1).factorial : ℝ) := by
    intro j
    have hsgn_abs : |(sgnD : ℝ)| = 1 := by dsimp only [sgnD]; split_ifs <;> norm_num
    have hadj_entry : ∀ i : Fin (n + 1), |(B.adjugate j i : ℝ)| ≤ (n.factorial : ℝ) := by
      intro i
      have hsub_det : |B.adjugate j i| =
          |(B.submatrix (Fin.succAbove i) (Fin.succAbove j)).det| := by
        rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
        simp [abs_mul, abs_pow]
      have hcast_abs : |(B.adjugate j i : ℝ)| = ((|B.adjugate j i| : ℤ) : ℝ) :=
        Int.cast_abs.symm
      rw [hcast_abs, hsub_det]
      have hdet := Matrix.det_le (A := B.submatrix (Fin.succAbove i) (Fin.succAbove j))
        (abv := (AbsoluteValue.abs : AbsoluteValue ℤ ℤ)) (x := (1 : ℤ))
        fun r c => hrow_abs (xs _) _
      simp only [AbsoluteValue.abs_apply, Fintype.card_fin, one_pow, nsmul_eq_mul, mul_one] at hdet
      exact_mod_cast hdet
    dsimp only [wInt]
    rw [Int.cast_mul, abs_mul, hsgn_abs, one_mul]
    simp only [Matrix.mulVec, dotProduct, mul_one, Int.cast_sum]
    calc |∑ i : Fin (n + 1), (B.adjugate j i : ℝ)|
        ≤ ∑ i : Fin (n + 1), |(B.adjugate j i : ℝ)| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin (n + 1), (n.factorial : ℝ) := sum_le_sum fun i _ => hadj_entry i
      _ = ((n + 1 : ℕ) : ℝ) * (n.factorial : ℝ) := by
          rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ = ((n + 1).factorial : ℝ) := by rw [Nat.factorial_succ]; push_cast; ring
  refine ⟨fun i => wInt i.castSucc, wInt (Fin.last n),
    fun i => hwInt_bound i.castSucc, hwInt_bound (Fin.last n), fun x => ?_⟩
  have h1 := hvK x
  rw [hrow_dot] at h1
  have hDge1 : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hDpos
  have hrew : signVal (f x) *
      (∑ i : Fin n, (wInt i.castSucc : ℝ) * bitVal ℝ (x i) - (wInt (Fin.last n) : ℝ)) =
      (D : ℝ) * (signVal (f x) * (∑ i : Fin n, v i.castSucc * bitVal ℝ (x i) -
        v (Fin.last n))) := by
    simp_rw [hwInt_eq, mul_assoc]
    rw [← Finset.mul_sum]
    ring
  rw [hrew]
  nlinarith

private def kpMerge {n : ℕ} (w u z : BitString n) : BitString (3 * n) :=
  fun idx =>
    if h1 : idx.1 < n then
      if z ⟨idx.1, h1⟩ then u ⟨idx.1, h1⟩ else w ⟨idx.1, h1⟩
    else if h2 : idx.1 < 2 * n then
      if z ⟨idx.1 - n, by omega⟩ then w ⟨idx.1 - n, by omega⟩ else u ⟨idx.1 - n, by omega⟩
    else
      z ⟨idx.1 - 2 * n, by omega⟩

private theorem kpTransform_kpMerge {n : ℕ} (f : BooleanFunction n) (w u z : BitString n) :
    kpTransform f (kpMerge w u z) = f w := by
  simp only [kpTransform]
  congr 1
  funext i
  have h1 : i.1 < n := i.2
  have h2 : ¬(n + i.1 < n) := by omega
  have h3 : n + i.1 < 2 * n := by omega
  have h4 : ¬(2 * n + i.1 < n) := by omega
  have h5 : ¬(2 * n + i.1 < 2 * n) := by omega
  have heq1 : (⟨n + i.1 - n, by omega⟩ : Fin n) = i := Fin.ext (by dsimp; omega)
  have heq2 : (⟨2 * n + i.1 - 2 * n, by omega⟩ : Fin n) = i := Fin.ext (by dsimp; omega)
  simp only [kpMerge, h1, h2, h3, h4, h5, ↓reduceDIte, heq1, heq2]
  cases z i <;> simp

private def kpSliceA {n : ℕ} (T : Finset (Fin (3 * n))) : Finset (Fin n) :=
  Finset.univ.filter fun i => ⟨i.1, by omega⟩ ∈ T

private def kpSliceB {n : ℕ} (T : Finset (Fin (3 * n))) : Finset (Fin n) :=
  Finset.univ.filter fun i => ⟨n + i.1, by omega⟩ ∈ T

private def kpSliceC {n : ℕ} (T : Finset (Fin (3 * n))) : Finset (Fin n) :=
  Finset.univ.filter fun i => ⟨2 * n + i.1, by omega⟩ ∈ T

private theorem chi_kpMerge {n : ℕ} (T : Finset (Fin (3 * n))) (w u z : BitString n) :
    chi ℝ T (kpMerge w u z) =
      chi ℝ (kpSliceC T) z *
      chi ℝ ((kpSliceA T).filter (fun i => z i = false) ∪
        (kpSliceB T).filter (fun i => z i = true)) w *
      chi ℝ ((kpSliceA T).filter (fun i => z i = true) ∪
        (kpSliceB T).filter (fun i => z i = false)) u := by
  have hprod_split : ∀ (S : Finset (Fin (3 * n))) (v : BitString (3 * n)),
      chi ℝ S v = ∏ idx ∈ S, signVal (v idx) := fun S v => by
    simp [Cslib.BitString.chi, Cslib.BitString.signVal_eq_neg_one_pow]
  have hprod_fin : ∀ (S : Finset (Fin n)) (v : BitString n),
      chi ℝ S v = ∏ i ∈ S, signVal (v i) := fun S v => by
    simp [Cslib.BitString.chi, Cslib.BitString.signVal_eq_neg_one_pow]
  let T1 := T.filter fun idx => idx.1 < n
  let T2 := T.filter fun idx => n ≤ idx.1 ∧ idx.1 < 2 * n
  let T3 := T.filter fun idx => 2 * n ≤ idx.1
  have hTpart : T = T1 ∪ T2 ∪ T3 := by
    ext idx
    simp only [T1, T2, T3, mem_union, mem_filter]
    constructor
    · intro h
      by_cases h1 : idx.1 < n
      · exact Or.inl (Or.inl ⟨h, h1⟩)
      · by_cases h2 : idx.1 < 2 * n
        · exact Or.inl (Or.inr ⟨h, by omega, h2⟩)
        · exact Or.inr ⟨h, by omega⟩
    · rintro ((⟨h, _⟩ | ⟨h, _⟩) | ⟨h, _⟩) <;> exact h
  have hd12 : Disjoint T1 T2 := Finset.disjoint_left.2 fun idx h1 h2 => by
    have := (mem_filter.1 h1).2; have := (mem_filter.1 h2).2; omega
  have hd123 : Disjoint (T1 ∪ T2) T3 := Finset.disjoint_left.2 fun idx h12 h3 => by
    have := (mem_filter.1 h3).2
    rcases mem_union.1 h12 with h1 | h2
    · have := (mem_filter.1 h1).2; omega
    · have := (mem_filter.1 h2).2; omega
  rw [hprod_split, hTpart, Finset.prod_union hd123, Finset.prod_union hd12]
  have hP1 : ∏ idx ∈ T1, signVal (kpMerge w u z idx) =
      (∏ i ∈ (kpSliceA T).filter (fun i => z i = false), signVal (w i)) *
      (∏ i ∈ (kpSliceA T).filter (fun i => z i = true), signVal (u i)) := by
    have hbij : ∏ idx ∈ T1, signVal (kpMerge w u z idx) =
        ∏ i ∈ kpSliceA T, signVal (if z i then u i else w i) := by
      refine Finset.prod_bij (fun idx hidx => ⟨idx.1, (mem_filter.1 hidx).2⟩)
        (fun idx hidx => mem_filter.2 ⟨mem_univ _, (mem_filter.1 hidx).1⟩)
        (fun a _ b _ h => Fin.ext (by simpa using congrArg Fin.val h))
        (fun i hi => ⟨⟨i.1, by omega⟩, mem_filter.2 ⟨(mem_filter.1 hi).2, i.2⟩, Fin.ext rfl⟩)
        (fun idx hidx => ?_)
      simp [kpMerge, (mem_filter.1 hidx).2]
    rw [hbij, ← Finset.prod_filter_mul_prod_filter_not (kpSliceA T) (fun i => z i = false)]
    congr 1
    · exact Finset.prod_congr rfl fun i hi => by simp [(mem_filter.1 hi).2]
    · refine Finset.prod_congr ?_ fun i hi => by
        have hz : z i = true := by
          have := (mem_filter.1 hi).2; cases h : z i <;> simp_all
        simp [hz]
      ext i; simp only [mem_filter, Bool.not_eq_false]
  have hP2 : ∏ idx ∈ T2, signVal (kpMerge w u z idx) =
      (∏ i ∈ (kpSliceB T).filter (fun i => z i = true), signVal (w i)) *
      (∏ i ∈ (kpSliceB T).filter (fun i => z i = false), signVal (u i)) := by
    have hbij : ∏ idx ∈ T2, signVal (kpMerge w u z idx) =
        ∏ i ∈ kpSliceB T, signVal (if z i then w i else u i) := by
      refine Finset.prod_bij (fun idx hidx => ⟨idx.1 - n, by have := (mem_filter.1 hidx).2; omega⟩)
        (fun idx hidx => by
          refine mem_filter.2 ⟨mem_univ _, ?_⟩
          have h := (mem_filter.1 hidx).2
          convert (mem_filter.1 hidx).1 using 1
          exact Fin.ext (by dsimp; omega))
        (fun a ha b hb h => by
          have ha' := (mem_filter.1 ha).2; have hb' := (mem_filter.1 hb).2
          have := congrArg Fin.val h; dsimp at this; exact Fin.ext (by omega))
        (fun i hi => ⟨⟨n + i.1, by omega⟩,
          mem_filter.2 ⟨(mem_filter.1 hi).2, by dsimp; omega, by dsimp; omega⟩,
          Fin.ext (by dsimp; omega)⟩)
        (fun idx hidx => ?_)
      have h := (mem_filter.1 hidx).2
      have hnot1 : ¬(idx.1 < n) := by omega
      simp [kpMerge, hnot1, h.2]
    rw [hbij, ← Finset.prod_filter_mul_prod_filter_not (kpSliceB T) (fun i => z i = true)]
    congr 1
    · exact Finset.prod_congr rfl fun i hi => by simp [(mem_filter.1 hi).2]
    · refine Finset.prod_congr ?_ fun i hi => by
        have hz : z i = false := by
          have := (mem_filter.1 hi).2; cases h : z i <;> simp_all
        simp [hz]
      ext i; simp only [mem_filter, Bool.not_eq_true]
  have hP3 : ∏ idx ∈ T3, signVal (kpMerge w u z idx) = chi ℝ (kpSliceC T) z := by
    rw [hprod_fin]
    refine Finset.prod_bij
      (fun idx hidx => ⟨idx.1 - 2 * n, by have := (mem_filter.1 hidx).2; omega⟩)
      (fun idx hidx => by
        refine mem_filter.2 ⟨mem_univ _, ?_⟩
        have h := (mem_filter.1 hidx).2
        convert (mem_filter.1 hidx).1 using 1
        exact Fin.ext (by dsimp; omega))
      (fun a ha b hb h => by
        have ha' := (mem_filter.1 ha).2; have hb' := (mem_filter.1 hb).2
        have := congrArg Fin.val h; dsimp at this; exact Fin.ext (by omega))
      (fun i hi => ⟨⟨2 * n + i.1, by omega⟩,
        mem_filter.2 ⟨(mem_filter.1 hi).2, by dsimp; omega⟩,
        Fin.ext (by dsimp; omega)⟩)
      (fun idx hidx => ?_)
    have h := (mem_filter.1 hidx).2
    have hnot1 : ¬(idx.1 < n) := by omega
    have hnot2 : ¬(idx.1 < 2 * n) := by omega
    simp [kpMerge, hnot1, hnot2]
  rw [hP1, hP2, hP3]
  have hdisj_w : Disjoint ((kpSliceA T).filter (fun i => z i = false))
      ((kpSliceB T).filter (fun i => z i = true)) :=
    Finset.disjoint_left.2 fun i h1 h2 => by
      have := (mem_filter.1 h1).2; have := (mem_filter.1 h2).2; simp_all
  have hdisj_u : Disjoint ((kpSliceA T).filter (fun i => z i = true))
      ((kpSliceB T).filter (fun i => z i = false)) :=
    Finset.disjoint_left.2 fun i h1 h2 => by
      have := (mem_filter.1 h1).2; have := (mem_filter.1 h2).2; simp_all
  simp_rw [hprod_fin, ← hTpart]
  rw [Finset.prod_union hdisj_w, Finset.prod_union hdisj_u]
  ring

/-- Krause–Pudlák degree-to-density theorem: every Boolean function `f : BooleanFunction n`
satisfies `2 ^ thresholdDegree f ≤ thresholdDensity (kpTransform f)`. -/
theorem two_pow_thresholdDegree_le_thresholdDensity_kp {n : ℕ} (f : BooleanFunction n) :
    2 ^ thresholdDegree f ≤ thresholdDensity (kpTransform f) := by
  set d := thresholdDegree f
  rcases Nat.eq_zero_or_pos d with hd0 | hdpos
  · rw [hd0, pow_zero]; exact one_le_thresholdDensity _
  have hne : ({k : ℕ | ∃ S : Finset (Finset (Fin (3 * n))),
      S.card = k ∧ IsPTFOn S (kpTransform f)}).Nonempty :=
    ⟨2 ^ (3 * n), Finset.univ, by simp [Fintype.card_finset],
      Cslib.BitString.isPTFOn_of_fourierCoeff_eq_zero fun S hS =>
        absurd (mem_univ S) hS⟩
  obtain ⟨𝒮, h𝒮card, P, hPsupp, hPsign⟩ := Nat.sInf_mem hne
  dsimp only [thresholdDensity]
  rw [← h𝒮card]
  let survives (T : Finset (Fin (3 * n))) (z : BitString n) : Prop :=
    (∀ i ∈ kpSliceA T, z i = false) ∧ (∀ i ∈ kpSliceB T, z i = true)
  have hcover : ∀ z : BitString n,
      ∃ T ∈ 𝒮, d ≤ (kpSliceA T ∪ kpSliceB T).card ∧ survives T z := by
    intro z
    by_contra hno
    push Not at hno
    let Pz : BitString n → ℝ := fun w => 𝔼 u : BitString n, P (kpMerge w u z)
    have hPz_sign : ∀ w : BitString n, 0 < signVal (f w) * Pz w := by
      intro w
      dsimp only [Pz]
      rw [Finset.mul_expect, Finset.expect_eq_sum_div_card]
      refine div_pos (Finset.sum_pos (fun u _ => ?_) Finset.univ_nonempty) (by simp)
      rw [← kpTransform_kpMerge f w u z]
      exact hPsign (kpMerge w u z)
    have hPz_eq : ∀ w : BitString n, Pz w =
        ∑ T ∈ 𝒮, if survives T z then
          fourierCoeff P T * chi ℝ (kpSliceC T) z * chi ℝ (kpSliceA T ∪ kpSliceB T) w
        else 0 := by
      intro w
      have hP_exp : ∀ v : BitString (3 * n),
          P v = ∑ T ∈ 𝒮, fourierCoeff P T * chi ℝ T v := fun v => by
        rw [← Cslib.BitString.sum_fourierCoeff_mul_chi P v]
        exact (Finset.sum_subset (subset_univ 𝒮) fun T _ hT => by rw [hPsupp T hT, zero_mul]).symm
      dsimp only [Pz]
      simp_rw [hP_exp, Finset.expect_sum_comm]
      refine sum_congr rfl fun T _ => ?_
      simp_rw [chi_kpMerge, ← mul_assoc, ← Finset.mul_expect]
      set U := (kpSliceA T).filter (fun i => z i = true) ∪
        (kpSliceB T).filter (fun i => z i = false)
      have hU_empty : U = ∅ ↔ survives T z := by
        simp only [U, survives, Finset.union_eq_empty, Finset.filter_eq_empty_iff,
          Bool.not_eq_true, Bool.not_eq_false]
      have hexp_U : 𝔼 u : BitString n, chi ℝ U u = if U = ∅ then 1 else 0 := by
        have := Cslib.BitString.fourierCoeff_chi (ι := Fin n) U ∅
        rw [Cslib.BitString.fourierCoeff_empty] at this
        exact this
      rw [hexp_U]
      by_cases hs : survives T z
      · have hU0 : U = ∅ := hU_empty.2 hs
        simp only [hU0, hs, ↓reduceIte, mul_one]
        have hAf : (kpSliceA T).filter (fun i => z i = false) = kpSliceA T :=
          Finset.filter_true_of_mem hs.1
        have hBt : (kpSliceB T).filter (fun i => z i = true) = kpSliceB T :=
          Finset.filter_true_of_mem hs.2
        rw [hAf, hBt]
      · have hU0 : U ≠ ∅ := fun h => hs (hU_empty.1 h)
        simp [hU0, hs]
    have hPz_low : Pz ∈ Cslib.BitString.lowDegree ℝ (Fin n) (d - 1) := by
      have hfn : Pz = ∑ T ∈ 𝒮, fun w => if survives T z then
          (fourierCoeff P T * chi ℝ (kpSliceC T) z) • chi ℝ (kpSliceA T ∪ kpSliceB T) w
        else 0 := by
        funext w; rw [hPz_eq w, Finset.sum_apply]; rfl
      rw [hfn]
      refine Cslib.BitString.sum_mem_lowDegree _ fun T hT => ?_
      by_cases hs : survives T z
      · simp only [hs, ↓reduceIte]
        have hlt : (kpSliceA T ∪ kpSliceB T).card < d := by
          by_contra hge
          exact hno T hT (not_lt.1 hge) hs
        exact Submodule.smul_mem _ _ (Cslib.BitString.lowDegree_mono (by omega)
          (Cslib.BitString.chi_mem_lowDegree (kpSliceA T ∪ kpSliceB T)))
      · simp only [hs, ↓reduceIte]; exact Submodule.zero_mem _
    have hptf' : IsPTF (d - 1) f :=
      Cslib.BitString.isPTF_iff.2 ⟨Pz,
        fun S hS => Cslib.BitString.fourierCoeff_eq_zero_of_mem_lowDegree hPz_low hS, hPz_sign⟩
    have hle : d ≤ d - 1 := thresholdDegree_le_iff.2 hptf'
    omega
  have hsurv_card : ∀ T : Finset (Fin (3 * n)), d ≤ (kpSliceA T ∪ kpSliceB T).card →
      (Finset.univ.filter fun z : BitString n => survives T z).card ≤ 2 ^ (n - d) := by
    intro T hTdeg
    set U := kpSliceA T ∪ kpSliceB T
    have hcard_map : (Finset.univ.filter fun z : BitString n => survives T z).card ≤
        (Finset.univ : Finset ({i : Fin n // i ∉ U} → Bool)).card := by
      refine Finset.card_le_card_of_injOn (fun z i => z i.1) (fun _ _ => mem_univ _) ?_
      intro z₁ hz₁ z₂ hz₂ hEq
      have hs1 := (mem_filter.1 hz₁).2
      have hs2 := (mem_filter.1 hz₂).2
      funext i
      by_cases hi : i ∈ U
      · rcases mem_union.1 hi with hA | hB
        · rw [hs1.1 i hA, hs2.1 i hA]
        · rw [hs1.2 i hB, hs2.2 i hB]
      · exact congr_fun hEq ⟨i, hi⟩
    have hcompl_card : Fintype.card {i : Fin n // i ∉ U} = n - U.card := by
      rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_coe]
    have hcard_rhs : (Finset.univ : Finset ({i : Fin n // i ∉ U} → Bool)).card =
        2 ^ (n - U.card) := by
      rw [card_univ, Fintype.card_fun, Fintype.card_bool, hcompl_card]
    rw [hcard_rhs] at hcard_map
    exact hcard_map.trans (Nat.pow_le_pow_right (by norm_num) (Nat.sub_le_sub_left hTdeg n))
  set 𝒮high := 𝒮.filter fun T => d ≤ (kpSliceA T ∪ kpSliceB T).card
  have huniv_sub : (Finset.univ : Finset (BitString n)) ⊆
      𝒮high.biUnion fun T => Finset.univ.filter fun z => survives T z := by
    intro z _
    obtain ⟨T, hT, hTdeg, hsurv⟩ := hcover z
    exact mem_biUnion.2 ⟨T, mem_filter.2 ⟨hT, hTdeg⟩, mem_filter.2 ⟨mem_univ z, hsurv⟩⟩
  have h2n_le : 2 ^ n ≤ 𝒮.card * 2 ^ (n - d) := by
    calc 2 ^ n
        = (Finset.univ : Finset (BitString n)).card := by simp
      _ ≤ (𝒮high.biUnion fun T => Finset.univ.filter fun z => survives T z).card :=
          card_le_card huniv_sub
      _ ≤ ∑ T ∈ 𝒮high, (Finset.univ.filter fun z => survives T z).card := card_biUnion_le
      _ ≤ ∑ _T ∈ 𝒮high, 2 ^ (n - d) :=
          sum_le_sum fun T hT => hsurv_card T (mem_filter.1 hT).2
      _ = 𝒮high.card * 2 ^ (n - d) := by rw [sum_const, smul_eq_mul]
      _ ≤ 𝒮.card * 2 ^ (n - d) :=
          Nat.mul_le_mul_right _ (card_le_card (filter_subset _ _))
  have hd_le_n : d ≤ n := thresholdDegree_le_card f
  have hpow : 2 ^ n = 2 ^ d * 2 ^ (n - d) := by
    rw [← pow_add, Nat.add_sub_of_le hd_le_n]
  rw [hpow] at h2n_le
  exact Nat.le_of_mul_le_mul_right h2n_le (by positivity)

end CslibFrontier.Foundations.BooleanAnalysis
