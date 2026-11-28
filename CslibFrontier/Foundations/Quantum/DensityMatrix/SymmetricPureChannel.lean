/-
Copyright (c) 2026 The Cslib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Cslib contributors
-/
module
-- upstream: candidate

public import Cslib.Probability.PMF
public import CslibFrontier.Foundations.Quantum.DensityMatrix.Holevo
public import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle

import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Holevo Capacity of the Symmetric $q$-ary Pure-State Channel

This module studies the symmetric $q$-ary pure-state classical-quantum channel mapping each input
symbol $i \in \{0, \dots, q - 1\}$ ($q \ge 2$) at error parameter $p \in [0, 1]$ to the unit vector
$$|i_p\rangle = \sqrt{1 - p}\,|i\rangle + \sqrt{\frac{p}{q - 1}} \sum_{j \neq i} |j\rangle \in
\mathbb{C}^q$$
and its pure density matrix $\rho_i(p) = |i_p\rangle\langle i_p|$, under standard Lean axioms.

## Main definitions

* `CslibFrontier.Quantum.symmetricPureVec`: the state vector
  $|i_p\rangle \in \mathbb{C}^q$.
* `CslibFrontier.Quantum.symmetricPureDensity`: the pure density operator
  $|i_p\rangle\langle i_p|$.
* `CslibFrontier.Quantum.symmetricPureAvgDensity`: the uniform ensemble average
  $\bar{\rho}_q(p) = \frac{1}{q} \sum_i |i_p\rangle\langle i_p|$.
* `CslibFrontier.Quantum.symmetricPureHolevo`: the Holevo information $\chi_q(p)$ of
  the symmetric pure-state channel under the uniform input distribution (in bits).
* `CslibFrontier.Quantum.symmetricPureCorr`: the off-diagonal correlation parameter
  $\gamma_q(p) = 2\sqrt{p(1-p)/(q-1)} + \frac{q-2}{q-1} p$.
* `CslibFrontier.Quantum.symmetricPureEigenvalue`: the spectrum of $\bar{\rho}_q(p)$,
  consisting of $\frac{1 + (q - 1)\gamma_q(p)}{q}$ with multiplicity $1$ and
  $\frac{1 - \gamma_q(p)}{q}$ with multiplicity $q - 1$.

## Main results

* `CslibFrontier.Quantum.norm_symmetricPureVec`: unit-norm identity
  $\||i_p\rangle\| = 1$ for $q \ge 2$ and $p \in [0, 1]$.
* `CslibFrontier.Quantum.isDensityMatrix_symmetricPureDensity` and
  `CslibFrontier.Quantum.vonNeumannEntropy_symmetricPureDensity`: purity and zero
  von Neumann entropy of each output state.
* `CslibFrontier.Quantum.symmetricPureHolevo_eq_vonNeumannEntropy_avg`: identity
  $\chi_q(p) = S(\bar{\rho}_q(p))$.
* `CslibFrontier.Quantum.holevoInformation_symmetricPureDensity_le`: optimality of the
  uniform input distribution over all input PMFs on `Fin q`.
* `CslibFrontier.Quantum.symmetricPureHolevo_eq_eigenvalue_sum`: closed-form diagonal
  entropy formula via discrete Fourier diagonalization of $\bar{\rho}_q(p)$.
* `CslibFrontier.Quantum.symmetricPureHolevo_two`: exact binary identity
  $\chi_2(p) = H_2(\frac{1}{2} - \sqrt{p(1 - p)})$.
* `CslibFrontier.Quantum.symmetricPureHolevo_expansion` and
  `CslibFrontier.Quantum.symmetricPureHolevo_le_logb_sub_linear`: asymptotic expansion
  $\chi_q(p) = \log_2 q - \frac{2 p}{\ln 2} + O_q(p^{3/2})$ with $q$-independent leading linear
  coefficient, plus global linear capacity-loss bound.

## Tags

quantum information, Holevo capacity, von Neumann entropy, symmetric pure-state channel
-/

public section

namespace CslibFrontier.Quantum

open Complex Matrix Finset Cslib.Quantum Cslib.Probability
open scoped BigOperators Matrix ComplexOrder

private theorem star_ofReal_eq (r : ℝ) : star (r : ℂ) = (r : ℂ) := by
  rw [Complex.star_def, Complex.conj_ofReal]

/-- The state vector
$|i_p\rangle = \sqrt{1 - p}\,|i\rangle + \sqrt{p/(q - 1)} \sum_{j \neq i} |j\rangle$
of the $q$-ary symmetric pure-state channel at symbol $i \in \mathrm{Fin}\,
  q$ and error rate $p$. -/
noncomputable def symmetricPureVec (q : ℕ) (p : ℝ) (i : Fin q) : EuclideanSpace ℂ (Fin q) :=
  WithLp.toLp 2 fun j : Fin q ↦
    if j = i then ((Real.sqrt (1 - p) : ℝ) : ℂ)
    else ((Real.sqrt (p / ((q : ℝ) - 1)) : ℝ) : ℂ)

@[simp]
theorem symmetricPureVec_ofLp (q : ℕ) (p : ℝ) (i j : Fin q) :
    (symmetricPureVec q p i).ofLp j =
      if j = i then ((Real.sqrt (1 - p) : ℝ) : ℂ)
      else ((Real.sqrt (p / ((q : ℝ) - 1)) : ℝ) : ℂ) := by
  unfold symmetricPureVec
  rfl

/-- Pure density matrix $\rho_i(p) = |i_p\rangle\langle i_p|$ of symbol $i$ under the $q$-ary
symmetric pure-state channel. -/
noncomputable def symmetricPureDensity (q : ℕ) (p : ℝ) (i : Fin q) : Matrix (Fin q) (Fin q) ℂ :=
  pureState (symmetricPureVec q p i)

/-- Ensemble average state $\bar{\rho}_q(p) = \frac{1}{q} \sum_{i} \rho_i(p)$ of the $q$-ary
symmetric pure-state channel under uniform input weights. -/
noncomputable def symmetricPureAvgDensity (q : ℕ) (p : ℝ) : Matrix (Fin q) (Fin q) ℂ :=
  ((q : ℝ)⁻¹ : ℝ) • ∑ i : Fin q, symmetricPureDensity q p i

/-- Holevo information $\chi_q(p)$ (in bits) of the $q$-ary symmetric pure-state channel under the
uniform input distribution on `Fin q`. -/
noncomputable def symmetricPureHolevo (q : ℕ) [NeZero q] (p : ℝ) : ℝ :=
  holevoInformation (PMF.uniformOfFintype (Fin q)) (symmetricPureDensity q p)

/-- Off-diagonal correlation parameter
$\gamma_q(p) = 2\sqrt{p(1 - p)/(q - 1)} + \frac{q - 2}{q - 1} p$
of the ensemble average $\bar{\rho}_q(p)$. -/
noncomputable def symmetricPureCorr (q : ℕ) (p : ℝ) : ℝ :=
  2 * Real.sqrt (p * (1 - p) / ((q : ℝ) - 1)) + ((q : ℝ) - 2) * p / ((q : ℝ) - 1)

/-- Eigenvalue profile of $\bar{\rho}_q(p)$: index $0$ carries $\frac{1 + (q - 1)\gamma_q(p)}{q}$
and each nonzero index carries $\frac{1 - \gamma_q(p)}{q}$. -/
noncomputable def symmetricPureEigenvalue (q : ℕ) (p : ℝ) (k : Fin q) : ℝ :=
  if k.val = 0 then (1 + ((q : ℝ) - 1) * symmetricPureCorr q p) / (q : ℝ)
  else (1 - symmetricPureCorr q p) / (q : ℝ)

/-! ### Unit norm, purity, and average-state representation -/

/-- Every output vector $|i_p\rangle$ has Euclidean norm $1$ for $q \ge 2$ and $p \in [0, 1]$. -/
theorem norm_symmetricPureVec {q : ℕ} (hq : 2 ≤ q) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (i : Fin q) : ‖symmetricPureVec q p i‖ = 1 := by
  have hq1 : (0 : ℝ) < (q : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    linarith
  have h1p : 0 ≤ 1 - p := sub_nonneg.mpr hp1
  have hpq : 0 ≤ p / ((q : ℝ) - 1) := div_nonneg hp0 hq1.le
  have hsq : ‖symmetricPureVec q p i‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq]
    have hterm (j : Fin q) :
        ‖(symmetricPureVec q p i).ofLp j‖ ^ 2 =
          if j = i then 1 - p else p / ((q : ℝ) - 1) := by
      rw [symmetricPureVec_ofLp]
      split_ifs
      · rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt h1p]
      · rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt hpq]
    simp_rw [hterm]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), ite_eq_left rfl]
    have herase : ∀ j ∈ Finset.univ.erase i,
        (if j = i then 1 - p else p / ((q : ℝ) - 1)) = p / ((q : ℝ) - 1) :=
      fun j hj ↦ ite_eq_right (Finset.ne_of_mem_erase hj)
    rw [Finset.sum_congr rfl herase, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i),
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hcard : ((q - 1 : ℕ) : ℝ) = (q : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ q), Nat.cast_one]
    rw [hcard, mul_div_cancel₀ p hq1.ne']
    ring
  nlinarith [norm_nonneg (symmetricPureVec q p i)]

/-- Each output $\rho_i(p)$ of the symmetric pure-state channel is a valid density matrix. -/
theorem isDensityMatrix_symmetricPureDensity {q : ℕ} (hq : 2 ≤ q) {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (i : Fin q) :
    IsDensityMatrix (symmetricPureDensity q p i) :=
  isDensityMatrix_pureState (norm_symmetricPureVec hq hp0 hp1 i)

/-- Each pure output state $\rho_i(p)$ has zero von Neumann entropy. -/
theorem vonNeumannEntropy_symmetricPureDensity {q : ℕ} (hq : 2 ≤ q) {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (i : Fin q) :
    vonNeumannEntropy (symmetricPureDensity q p i) = 0 :=
  vonNeumannEntropy_pureState (norm_symmetricPureVec hq hp0 hp1 i)

/-- Because all output states are pure, the Holevo information $\chi_q(p)$ equals the von Neumann
entropy of the average state $\bar{\rho}_q(p)$. -/
theorem symmetricPureHolevo_eq_vonNeumannEntropy_avg {q : ℕ} (hq : 2 ≤ q) [NeZero q] {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    symmetricPureHolevo q p = vonNeumannEntropy (symmetricPureAvgDensity q p) := by
  rw [symmetricPureHolevo, holevoInformation]
  have hzero : ∑ x : Fin q,
      (PMF.uniformOfFintype (Fin q) x).toReal * vonNeumannEntropy (symmetricPureDensity q p x) =
        0 := by
    refine Finset.sum_eq_zero fun i _ ↦ ?_
    rw [vonNeumannEntropy_symmetricPureDensity hq hp0 hp1 i, mul_zero]
  have havg : ∑ x : Fin q,
      (PMF.uniformOfFintype (Fin q) x).toReal • symmetricPureDensity q p x =
        symmetricPureAvgDensity q p := by
    rw [symmetricPureAvgDensity, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp [PMF.uniformOfFintype_apply]
  rw [hzero, sub_zero, havg]

/-! ### Optimality of uniform input weights over all input distributions -/

private noncomputable def shiftPerm (q : ℕ) [NeZero q] (c : Fin q) : Equiv.Perm (Fin q) :=
  (finCongr (ZMod.card q)).symm.trans <|
    (Equiv.addRight ((finCongr (ZMod.card q)).symm c)).trans (finCongr (ZMod.card q))

private noncomputable def permUnitary {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun j k ↦ if j = σ k then 1 else 0

private theorem permUnitary_conjTranspose {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    (permUnitary σ)ᴴ = permUnitary σ.symm := by
  ext j k
  simp only [permUnitary, conjTranspose_apply, of_apply, Equiv.eq_symm_apply, eq_comm]
  split_ifs <;> simp

private theorem permUnitary_conjTranspose_mul {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    (permUnitary σ)ᴴ * permUnitary σ = 1 := by
  ext j k
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [permUnitary, conjTranspose_apply, of_apply, apply_ite star, star_one, star_zero]
  by_cases hjk : j = k
  · subst hjk
    rw [ite_eq_left rfl, Finset.sum_eq_single (σ j)]
    · simp
    · intro m _ hm; simp [hm]
    · simp
  · rw [ite_eq_right hjk]
    refine Finset.sum_eq_zero fun m _ ↦ ?_
    by_cases hm : m = σ j
    · subst hm
      have hne : σ j ≠ σ k := σ.injective.ne hjk
      simp [hne]
    · simp [hm]

private theorem permUnitary_mul_conjTranspose {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    permUnitary σ * (permUnitary σ)ᴴ = 1 := by
  have h := permUnitary_conjTranspose_mul σ.symm
  rwa [permUnitary_conjTranspose, Equiv.symm_symm, ← permUnitary_conjTranspose] at h

private theorem permUnitary_conj_symmetricPureDensity {q : ℕ} (σ : Equiv.Perm (Fin q))
    (p : ℝ) (i : Fin q) :
    permUnitary σ * symmetricPureDensity q p i * (permUnitary σ)ᴴ =
      symmetricPureDensity q p (σ i) := by
  ext j k
  simp only [symmetricPureDensity, pureState_apply, Matrix.mul_apply, permUnitary,
    conjTranspose_apply, of_apply, apply_ite star, star_one, star_zero]
  have h1 : ∀ m : Fin q,
      (∑ l : Fin q, (if j = σ l then (1 : ℂ) else 0) *
        ((symmetricPureVec q p i).ofLp l * star ((symmetricPureVec q p i).ofLp m))) =
      (symmetricPureVec q p i).ofLp (σ.symm j) * star ((symmetricPureVec q p i).ofLp m) := by
    intro m
    rw [Finset.sum_eq_single (σ.symm j)]
    · simp
    · intro l _ hl
      have : j ≠ σ l := fun h ↦ hl ((σ.symm_apply_eq.mpr h).symm)
      simp [this]
    · simp
  simp_rw [h1]
  rw [Finset.sum_eq_single (σ.symm k)]
  · simp only [Equiv.apply_symm_apply, ↓reduceIte, mul_one, symmetricPureVec_ofLp]
    have hj : (σ.symm j = i) ↔ (j = σ i) := Equiv.symm_apply_eq σ
    have hk : (σ.symm k = i) ↔ (k = σ i) := Equiv.symm_apply_eq σ
    simp only [hj, hk]
  · intro m _ hm
    have : k ≠ σ m := fun h ↦ hm ((σ.symm_apply_eq.mpr h).symm)
    simp [this]
  · simp

/-- The uniform input distribution maximizes the Holevo information of the $q$-ary symmetric
pure-state channel across all input distributions `π : PMF (Fin q)`. -/
theorem holevoInformation_symmetricPureDensity_le {q : ℕ} (hq : 2 ≤ q) [NeZero q] {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (π : PMF (Fin q)) :
    holevoInformation π (symmetricPureDensity q p) ≤ symmetricPureHolevo q p := by
  have hzero : ∑ x : Fin q, (π x).toReal * vonNeumannEntropy (symmetricPureDensity q p x) = 0 := by
    refine Finset.sum_eq_zero fun i _ ↦ ?_
    rw [vonNeumannEntropy_symmetricPureDensity hq hp0 hp1 i, mul_zero]
  let ρπ : Matrix (Fin q) (Fin q) ℂ := ∑ x : Fin q, (π x).toReal • symmetricPureDensity q p x
  have hρπ : IsDensityMatrix ρπ := by
    dsimp only [ρπ]
    rw [← partialTraceRight_classicalQuantumState π (symmetricPureDensity q p)]
    exact (isDensityMatrix_classicalQuantumState π
      (isDensityMatrix_symmetricPureDensity hq hp0 hp1)).partialTraceRight
  let ens (c : Fin q) : Matrix (Fin q) (Fin q) ℂ :=
    permUnitary (shiftPerm q c) * ρπ * (permUnitary (shiftPerm q c))ᴴ
  have hens_dm (c : Fin q) : IsDensityMatrix (ens c) := by
    have hU : permUnitary (shiftPerm q c) ∈ unitaryGroup (Fin q) ℂ := by
      rw [Matrix.mem_unitaryGroup_iff']
      exact permUnitary_conjTranspose_mul (shiftPerm q c)
    exact hρπ.conj_unitary hU
  have hens_ent (c : Fin q) : vonNeumannEntropy (ens c) = vonNeumannEntropy ρπ := by
    have hinv : permUnitary (shiftPerm q c) * (permUnitary (shiftPerm q c))ᴴ = 1 :=
      permUnitary_mul_conjTranspose (shiftPerm q c)
    have hrew : ρπ = (permUnitary (shiftPerm q c))ᴴ * ens c * permUnitary (shiftPerm q c) := by
      dsimp only [ens]
      simp only [← Matrix.mul_assoc, permUnitary_conjTranspose_mul, Matrix.one_mul]
      rw [Matrix.mul_assoc, permUnitary_conjTranspose_mul, Matrix.mul_one]
    have hV : ((permUnitary (shiftPerm q c))ᴴ)ᴴ * (permUnitary (shiftPerm q c))ᴴ = 1 := by
      rw [conjTranspose_conjTranspose]
      exact hinv
    have hiso := (vonNeumannEntropy_conj_isometry hV (hens_dm c).posSemidef.isHermitian).symm
    rwa [conjTranspose_conjTranspose, ← hrew] at hiso
  have havg_eq : ∑ c : Fin q, (PMF.uniformOfFintype (Fin q) c).toReal • ens c =
      symmetricPureAvgDensity q p := by
    have hstep (c : Fin q) : ens c =
        ∑ x : Fin q, (π x).toReal • symmetricPureDensity q p (shiftPerm q c x) := by
      dsimp only [ens, ρπ]
      rw [Matrix.mul_sum, Matrix.sum_mul]
      refine Finset.sum_congr rfl fun x _ ↦ ?_
      rw [Matrix.mul_smul, Matrix.smul_mul, permUnitary_conj_symmetricPureDensity]
    simp_rw [hstep, PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast,
      Fintype.card_fin, Finset.smul_sum]
    rw [Finset.sum_comm]
    have hinner (x : Fin q) :
        ∑ c : Fin q, (q : ℝ)⁻¹ • (π x).toReal • symmetricPureDensity q p (shiftPerm q c x) =
          (π x).toReal • symmetricPureAvgDensity q p := by
      let bij : Equiv.Perm (Fin q) :=
        { toFun := fun c ↦ shiftPerm q c x
          invFun := fun y ↦ finCongr (ZMod.card q)
            ((finCongr (ZMod.card q)).symm y - (finCongr (ZMod.card q)).symm x)
          left_inv := fun c ↦ by simp [shiftPerm]
          right_inv := fun y ↦ by simp [shiftPerm] }
      have hsum_bij : ∑ c : Fin q, symmetricPureDensity q p (shiftPerm q c x) =
          ∑ y : Fin q, symmetricPureDensity q p y :=
        Equiv.sum_comp bij (symmetricPureDensity q p)
      rw [symmetricPureAvgDensity, smul_comm, ← Finset.smul_sum, ← Finset.smul_sum, hsum_bij]
    simp_rw [hinner]
    rw [← Finset.sum_smul, PMF.sum_toReal, one_smul]
  have hconc := holevoInformation_nonneg (PMF.uniformOfFintype (Fin q)) hens_dm
  rw [holevoInformation, havg_eq] at hconc
  simp_rw [hens_ent] at hconc
  rw [← Finset.sum_mul, PMF.sum_toReal, one_mul] at hconc
  rw [holevoInformation, hzero, sub_zero, symmetricPureHolevo_eq_vonNeumannEntropy_avg hq hp0 hp1]
  exact sub_nonneg.mp hconc

/-! ### Exact entries and discrete Fourier diagonalization of $\bar{\rho}_q(p)$ -/

/-- Exact matrix entries of the ensemble average $\bar{\rho}_q(p)$: diagonal entries equal $1 / q$
and off-diagonal entries equal $\gamma_q(p) / q$. -/
theorem symmetricPureAvgDensity_apply {q : ℕ} (hq : 2 ≤ q) {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (j k : Fin q) :
    symmetricPureAvgDensity q p j k =
      if j = k then (((q : ℝ)⁻¹ : ℝ) : ℂ)
      else ((symmetricPureCorr q p / (q : ℝ) : ℝ) : ℂ) := by
  have hq1 : (0 : ℝ) < (q : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    linarith
  have h1p : 0 ≤ 1 - p := sub_nonneg.mpr hp1
  have hpq : 0 ≤ p / ((q : ℝ) - 1) := div_nonneg hp0 hq1.le
  rw [symmetricPureAvgDensity, Matrix.smul_apply, Matrix.sum_apply]
  by_cases hjk : j = k
  · subst hjk
    rw [ite_eq_left rfl]
    have hterm (i : Fin q) : symmetricPureDensity q p i j j =
        if j = i then ((1 - p : ℝ) : ℂ) else ((p / ((q : ℝ) - 1) : ℝ) : ℂ) := by
      simp only [symmetricPureDensity, pureState_apply, symmetricPureVec_ofLp]
      split_ifs
      · rw [star_ofReal_eq, ← Complex.ofReal_mul, Real.mul_self_sqrt h1p]
      · rw [star_ofReal_eq, ← Complex.ofReal_mul, Real.mul_self_sqrt hpq]
    simp_rw [hterm]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j), ite_eq_left rfl]
    have herase : ∀ i ∈ Finset.univ.erase j,
        (if j = i then ((1 - p : ℝ) : ℂ) else ((p / ((q : ℝ) - 1) : ℝ) : ℂ)) =
          ((p / ((q : ℝ) - 1) : ℝ) : ℂ) :=
      fun i hi ↦ ite_eq_right (Finset.ne_of_mem_erase hi).symm
    rw [Finset.sum_congr rfl herase, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ j),
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hcard : ((q - 1 : ℕ) : ℝ) = (q : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ q), Nat.cast_one]
    have hreal : (1 - p) + ((q - 1 : ℕ) : ℝ) * (p / ((q : ℝ) - 1)) = 1 := by
      rw [hcard, mul_div_cancel₀ p hq1.ne']; ring
    have hcast : ((1 - p : ℝ) : ℂ) + (q - 1 : ℕ) * ((p / ((q : ℝ) - 1) : ℝ) : ℂ) = 1 := by
      exact_mod_cast hreal
    rw [hcast, Complex.real_smul, mul_one]
  · rw [ite_eq_right hjk]
    have hterm (i : Fin q) : symmetricPureDensity q p i j k =
        if i = j ∨ i = k then ((Real.sqrt (1 - p) * Real.sqrt (p / ((q : ℝ) - 1)) : ℝ) : ℂ)
        else ((p / ((q : ℝ) - 1) : ℝ) : ℂ) := by
      simp only [symmetricPureDensity, pureState_apply, symmetricPureVec_ofLp]
      by_cases hij : j = i
      · subst hij
        have hki : k ≠ j := Ne.symm hjk
        simp only [true_or, ↓reduceIte, hki, star_ofReal_eq, Complex.ofReal_mul]
      · by_cases hik : k = i
        · subst hik
          simp only [Ne.symm hij, or_true, ↓reduceIte, hij, star_ofReal_eq, ← Complex.ofReal_mul]
          congr 1; ring
        · have h1 : ¬ (i = j ∨ i = k) := by
            rintro (rfl | rfl)
            · exact hij rfl
            · exact hik rfl
          simp only [hij, hik, h1, ↓reduceIte, star_ofReal_eq, ← Complex.ofReal_mul,
            Real.mul_self_sqrt hpq]
    simp_rw [hterm]
    let pair : Finset (Fin q) := {j, k}
    have hpair_card : pair.card = 2 := Finset.card_pair hjk
    rw [← Finset.sum_sdiff (Finset.subset_univ pair)]
    have hcomp : ∀ i ∈ Finset.univ \ pair,
        (if i = j ∨ i = k then ((Real.sqrt (1 - p) * Real.sqrt (p / ((q : ℝ) - 1)) : ℝ) : ℂ)
         else ((p / ((q : ℝ) - 1) : ℝ) : ℂ)) = ((p / ((q : ℝ) - 1) : ℝ) : ℂ) := by
      intro i hi
      rw [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton] at hi
      exact ite_eq_right hi.2
    have hin : ∀ i ∈ pair,
        (if i = j ∨ i = k then ((Real.sqrt (1 - p) * Real.sqrt (p / ((q : ℝ) - 1)) : ℝ) : ℂ)
         else ((p / ((q : ℝ) - 1) : ℝ) : ℂ)) =
          ((Real.sqrt (1 - p) * Real.sqrt (p / ((q : ℝ) - 1)) : ℝ) : ℂ) := by
      intro i hi
      rw [Finset.mem_insert, Finset.mem_singleton] at hi
      exact ite_eq_left hi
    rw [Finset.sum_congr rfl hcomp, Finset.sum_congr rfl hin, Finset.sum_const, Finset.sum_const,
      Finset.card_sdiff_of_subset (Finset.subset_univ pair), Finset.card_univ, Fintype.card_fin,
        hpair_card,
      nsmul_eq_mul, nsmul_eq_mul]
    have hcard2 : ((q - 2 : ℕ) : ℝ) = (q : ℝ) - 2 := Nat.cast_sub hq
    have hsqrt_prod : Real.sqrt (1 - p) * Real.sqrt (p / ((q : ℝ) - 1)) =
        Real.sqrt (p * (1 - p) / ((q : ℝ) - 1)) := by
      rw [← Real.sqrt_mul h1p]
      congr 1; ring
    have hcorr_eq : ((q - 2 : ℕ) : ℝ) * (p / ((q : ℝ) - 1)) +
        2 * (Real.sqrt (1 - p) * Real.sqrt (p / ((q : ℝ) - 1))) = symmetricPureCorr q p := by
      rw [hcard2, hsqrt_prod, symmetricPureCorr]; ring
    rw [Complex.real_smul]
    exact_mod_cast (by rw [hcorr_eq]; ring :
      (q : ℝ)⁻¹ * (((q - 2 : ℕ) : ℝ) * (p / ((q : ℝ) - 1)) +
        2 * (Real.sqrt (1 - p) * Real.sqrt (p / ((q : ℝ) - 1)))) =
      symmetricPureCorr q p / (q : ℝ))

private noncomputable def dftMatrix (q : ℕ) : Matrix (Fin q) (Fin q) ℂ :=
  Matrix.of fun j k ↦
    ((Real.sqrt q : ℝ)⁻¹ : ℂ) *
      Complex.exp (2 * Real.pi * Complex.I * ((j.val * k.val : ℕ) : ℂ) / (q : ℂ))

private theorem exp_two_pi_I_int_eq_one (z : ℤ) :
    Complex.exp (2 * Real.pi * Complex.I * (z : ℂ)) = 1 := by
  have h : 2 * Real.pi * Complex.I * (z : ℂ) = (z : ℂ) * (2 * Real.pi * Complex.I) := by ring
  rw [h]
  exact Complex.exp_int_mul_two_pi_mul_I z

private theorem sum_exp_roots_of_unity {q : ℕ} (hq : 1 ≤ q) (d : ℤ) :
    (∑ m ∈ Finset.range q,
      Complex.exp (2 * Real.pi * Complex.I * (d : ℂ) / (q : ℂ)) ^ m) =
      if (q : ℤ) ∣ d then (q : ℂ) else 0 := by
  have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I * (d : ℂ) / (q : ℂ))
  by_cases hdvd : (q : ℤ) ∣ d
  · rw [ite_eq_left hdvd]
    obtain ⟨t, rfl⟩ := hdvd
    have hζ1 : ζ = 1 := by
      dsimp only [ζ]
      push_cast
      have hdiv : 2 * ↑Real.pi * Complex.I * (↑q * ↑t) / ↑q =
          2 * ↑Real.pi * Complex.I * ↑t := by field_simp [hq0]
      rw [hdiv]
      exact exp_two_pi_I_int_eq_one t
    simp [hζ1]
  · rw [ite_eq_right hdvd]
    have hζ_ne_one : ζ ≠ 1 := by
      intro h1
      rw [Complex.exp_eq_one_iff] at h1
      obtain ⟨t, ht⟩ := h1
      have hd : (d : ℂ) = (t : ℂ) * (q : ℂ) := by
        have hpi : (2 * Real.pi : ℂ) * Complex.I ≠ 0 :=
          mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
            Complex.I_ne_zero
        have hmul := congrArg (· * (q : ℂ)) ht
        rw [div_mul_cancel₀ _ hq0] at hmul
        exact mul_left_cancel₀ hpi (by linear_combination hmul)
      have hd_int : d = q * t := by
        exact_mod_cast (by push_cast; linear_combination hd : (d : ℂ) = ((q * t : ℤ) : ℂ))
      exact hdvd ⟨t, hd_int⟩
    have hζq : ζ ^ q = 1 := by
      dsimp only [ζ]
      rw [← Complex.exp_nat_mul]
      have hmul : (q : ℂ) * (2 * ↑Real.pi * Complex.I * ↑d / ↑q) =
          2 * ↑Real.pi * Complex.I * ↑d := by field_simp [hq0]
      rw [hmul]
      exact exp_two_pi_I_int_eq_one d
    rw [geom_sum_eq hζ_ne_one, hζq, sub_self, zero_div]

private theorem dftMatrix_conjTranspose_mul {q : ℕ} (hq : 1 ≤ q) :
    (dftMatrix q)ᴴ * dftMatrix q = 1 := by
  have hq_pos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hq_c : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  ext j k
  rw [Matrix.mul_apply, Matrix.one_apply]
  obtain ⟨d, hd⟩ : ∃ d : ℤ, d = (k.val : ℤ) - (j.val : ℤ) := ⟨_, rfl⟩
  have hterm (m : Fin q) :
      (dftMatrix q)ᴴ j m * dftMatrix q m k =
        ((q : ℂ))⁻¹ *
          Complex.exp (2 * Real.pi * Complex.I * (d : ℂ) / (q : ℂ)) ^ m.val := by
    simp only [dftMatrix, conjTranspose_apply, of_apply,
      star_mul', star_inv₀, star_ofReal_eq]
    have hconj : star (Complex.exp (2 * ↑Real.pi * Complex.I * ↑(m.val * j.val) / ↑q)) =
        Complex.exp (-(2 * ↑Real.pi * Complex.I * ↑(m.val * j.val) / ↑q)) := by
      rw [Complex.star_def, ← Complex.exp_conj]
      congr 1
      simp only [map_div₀, map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I, map_natCast]
      ring
    rw [hconj]
    have hinv_sq : ((Real.sqrt q : ℂ))⁻¹ * ((Real.sqrt q : ℂ))⁻¹ = ((q : ℂ))⁻¹ := by
      rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt hq_pos.le, Complex.ofReal_natCast]
    have hexp_prod :
        Complex.exp (-(2 * ↑Real.pi * Complex.I * ↑(m.val * j.val) / ↑q)) *
          Complex.exp (2 * ↑Real.pi * Complex.I * ↑(m.val * k.val) / ↑q) =
        Complex.exp (2 * ↑Real.pi * Complex.I * (d : ℂ) / ↑q) ^ m.val := by
      rw [← Complex.exp_add, ← Complex.exp_nat_mul]
      congr 1
      rw [hd]
      push_cast
      ring
    calc
      ((Real.sqrt q : ℂ))⁻¹ *
          Complex.exp (-(2 * ↑Real.pi * Complex.I * ↑(m.val * j.val) / ↑q)) *
        (((Real.sqrt q : ℂ))⁻¹ *
          Complex.exp (2 * ↑Real.pi * Complex.I * ↑(m.val * k.val) / ↑q)) =
        (((Real.sqrt q : ℂ))⁻¹ * ((Real.sqrt q : ℂ))⁻¹) *
          (Complex.exp (-(2 * ↑Real.pi * Complex.I * ↑(m.val * j.val) / ↑q)) *
            Complex.exp (2 * ↑Real.pi * Complex.I * ↑(m.val * k.val) / ↑q)) := by ring
      _ = ((q : ℂ))⁻¹ *
          Complex.exp (2 * ↑Real.pi * Complex.I * (d : ℂ) / ↑q) ^ m.val := by
        rw [hinv_sq, hexp_prod]
  simp_rw [hterm]
  rw [← Finset.mul_sum, Fin.sum_univ_eq_sum_range
    (fun m : ℕ ↦ Complex.exp (2 * Real.pi * Complex.I * (d : ℂ) / (q : ℂ)) ^ m) q,
    sum_exp_roots_of_unity hq d]
  by_cases hjk : j = k
  · subst hjk
    have hd0 : d = 0 := by omega
    rw [hd0, ite_eq_left rfl, ite_eq_left (dvd_zero _), inv_mul_cancel₀ hq_c]
  · rw [ite_eq_right hjk]
    have hndvd : ¬ ((q : ℤ) ∣ d) := by
      rintro ⟨t, ht⟩
      have hlt1 : d < (q : ℤ) := by omega
      have hlt2 : -(q : ℤ) < d := by omega
      have ht0 : t = 0 := by nlinarith
      subst ht0
      apply hjk
      ext
      omega
    rw [ite_eq_right hndvd, mul_zero]

private theorem dftMatrix_mul_conjTranspose {q : ℕ} (hq : 1 ≤ q) :
    dftMatrix q * (dftMatrix q)ᴴ = 1 := by
  have h1 := congrArg (fun M : Matrix (Fin q) (Fin q) ℂ ↦ M.map (starRingEnd ℂ))
    (dftMatrix_conjTranspose_mul hq)
  have hmap_one : (1 : Matrix (Fin q) (Fin q) ℂ).map (starRingEnd ℂ) = 1 :=
    Matrix.map_one (starRingEnd ℂ) (map_zero _) (map_one _)
  rw [Matrix.map_mul, hmap_one] at h1
  have hF1 : (dftMatrix q)ᴴ.map (starRingEnd ℂ) = dftMatrix q := by
    ext j k
    simp only [map_apply, conjTranspose_apply, RCLike.star_def,
      RingHomCompTriple.comp_apply, RingHom.id_apply, dftMatrix, of_apply]
    rw [Nat.mul_comm]
  have hF2 : (dftMatrix q).map (starRingEnd ℂ) = (dftMatrix q)ᴴ := by
    ext j k
    simp only [map_apply, conjTranspose_apply, RCLike.star_def, dftMatrix, of_apply]
    rw [Nat.mul_comm]
  rwa [hF1, hF2] at h1

private theorem dftMatrix_row_sum {q : ℕ} (hq : 1 ≤ q) (k : Fin q) :
    (∑ j : Fin q, dftMatrix q j k) =
      if k.val = 0 then ((Real.sqrt q : ℝ) : ℂ) else 0 := by
  have hq_pos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hterm (j : Fin q) :
      dftMatrix q j k =
        ((Real.sqrt q : ℝ)⁻¹ : ℂ) *
          Complex.exp (2 * Real.pi * Complex.I * ((k.val : ℤ) : ℂ) / (q : ℂ)) ^ j.val := by
    simp only [dftMatrix, of_apply, ← Complex.exp_nat_mul]
    congr 2
    push_cast
    ring
  simp_rw [hterm, ← Finset.mul_sum, Fin.sum_univ_eq_sum_range
    (fun m : ℕ ↦ Complex.exp (2 * ↑Real.pi * Complex.I * ((k.val : ℤ) : ℂ) / ↑q) ^ m) q,
    sum_exp_roots_of_unity hq]
  by_cases hk0 : k.val = 0
  · rw [ite_eq_left hk0, hk0, Int.ofNat_zero, ite_eq_left (dvd_zero _)]
    have hreal : (Real.sqrt q)⁻¹ * (q : ℝ) = Real.sqrt q := by
      rw [inv_mul_eq_div, div_eq_iff (Real.sqrt_pos.mpr hq_pos).ne', Real.mul_self_sqrt hq_pos.le]
    exact_mod_cast hreal
  · rw [ite_eq_right hk0]
    have hndvd : ¬ ((q : ℤ) ∣ (k.val : ℤ)) := by
      rintro ⟨t, ht⟩
      have hk_lt : (k.val : ℤ) < (q : ℤ) := by exact_mod_cast k.isLt
      have hk_pos : (0 : ℤ) < (k.val : ℤ) := by omega
      rcases le_or_gt t 0 with ht0 | ht0
      · have : (k.val : ℤ) ≤ 0 := by nlinarith
        omega
      · have : (q : ℤ) ≤ (k.val : ℤ) := by nlinarith
        omega
    rw [ite_eq_right hndvd, mul_zero]

/-- Closed-form eigenvalue formula for the Holevo capacity $\chi_q(p)$ of the $q$-ary symmetric
pure-state channel ($q \ge 2$, $p \in [0, 1]$). -/
theorem symmetricPureHolevo_eq_eigenvalue_sum {q : ℕ} (hq : 2 ≤ q) [NeZero q] {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    symmetricPureHolevo q p =
      (Real.negMulLog ((1 + ((q : ℝ) - 1) * symmetricPureCorr q p) / (q : ℝ)) +
         ((q : ℝ) - 1) * Real.negMulLog ((1 - symmetricPureCorr q p) / (q : ℝ))) /
        Real.log 2 := by
  have hq1 : 1 ≤ q := by omega
  have hq_pos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq1
  rw [symmetricPureHolevo_eq_vonNeumannEntropy_avg hq hp0 hp1]
  have hFF : (dftMatrix q)ᴴ * dftMatrix q = 1 := dftMatrix_conjTranspose_mul hq1
  have hFF' : dftMatrix q * (dftMatrix q)ᴴ = 1 := dftMatrix_mul_conjTranspose hq1
  let D : Matrix (Fin q) (Fin q) ℂ :=
    diagonal fun k : Fin q ↦ ((symmetricPureEigenvalue q p k : ℝ) : ℂ)
  have hconj : (dftMatrix q)ᴴ * symmetricPureAvgDensity q p * dftMatrix q = D := by
    let α : ℂ := (((1 - symmetricPureCorr q p) / (q : ℝ) : ℝ) : ℂ)
    let β : ℂ := ((symmetricPureCorr q p / (q : ℝ) : ℝ) : ℂ)
    have hdecomp : symmetricPureAvgDensity q p =
        α • (1 : Matrix (Fin q) (Fin q) ℂ) + β • Matrix.of (fun _ _ : Fin q ↦ (1 : ℂ)) := by
      ext j k
      rw [symmetricPureAvgDensity_apply hq hp0 hp1 j k]
      by_cases hjk : j = k
      · subst hjk
        simp only [↓reduceIte, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_eq,
          of_apply, smul_eq_mul, mul_one, α, β]
        exact_mod_cast (by field_simp [hq_pos.ne']; ring :
          (q : ℝ)⁻¹ = (1 - symmetricPureCorr q p) / (q : ℝ) + symmetricPureCorr q p / (q : ℝ))
      · simp [hjk, α, β]
    rw [hdecomp, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      hFF, Matrix.mul_smul, Matrix.smul_mul]
    ext k l
    simp only [D, diagonal_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
      smul_eq_mul]
    have hall : ((dftMatrix q)ᴴ * Matrix.of (fun _ _ : Fin q ↦ (1 : ℂ)) * dftMatrix q) k l =
        if k.val = 0 ∧ l.val = 0 then (q : ℂ) else 0 := by
      rw [Matrix.mul_apply]
      have hinner (i : Fin q) :
          ((dftMatrix q)ᴴ * Matrix.of (fun _ _ : Fin q ↦ (1 : ℂ))) k i =
            star (∑ j : Fin q, dftMatrix q j k) := by
        rw [Matrix.mul_apply, star_sum]
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        rw [conjTranspose_apply, of_apply, mul_one]
      simp_rw [hinner]
      rw [← Finset.mul_sum, dftMatrix_row_sum hq1 k, dftMatrix_row_sum hq1 l]
      by_cases hk0 : k.val = 0 <;> by_cases hl0 : l.val = 0
      · simp only [hk0, hl0, and_self, ↓reduceIte, star_ofReal_eq,
          ← Complex.ofReal_mul, Real.mul_self_sqrt hq_pos.le, Complex.ofReal_natCast]
      · simp [hk0, hl0]
      · simp [hk0, hl0]
      · simp [hk0, hl0]
    rw [hall]
    by_cases hkl : k = l
    · subst hkl
      by_cases hk0 : k.val = 0
      · simp only [↓reduceIte, hk0, and_self, mul_one, symmetricPureEigenvalue, α, β]
        exact_mod_cast (by field_simp [hq_pos.ne']; ring :
          (1 - symmetricPureCorr q p) / (q : ℝ) + symmetricPureCorr q p / (q : ℝ) * (q : ℝ) =
            (1 + ((q : ℝ) - 1) * symmetricPureCorr q p) / (q : ℝ))
      · simp only [↓reduceIte, hk0, and_self, mul_one, mul_zero, add_zero,
          symmetricPureEigenvalue, α]
    · have hnot : ¬ (k.val = 0 ∧ l.val = 0) := by
        rintro ⟨hk0, hl0⟩
        apply hkl; ext; omega
      rw [ite_eq_right hkl, ite_eq_right hnot, ite_eq_right hkl, mul_zero, mul_zero, add_zero]
  have hrev : symmetricPureAvgDensity q p = dftMatrix q * D * (dftMatrix q)ᴴ := by
    calc
      symmetricPureAvgDensity q p =
          (dftMatrix q * (dftMatrix q)ᴴ) * symmetricPureAvgDensity q p *
            (dftMatrix q * (dftMatrix q)ᴴ) := by
        rw [hFF', Matrix.one_mul, Matrix.mul_one]
      _ = dftMatrix q * ((dftMatrix q)ᴴ * symmetricPureAvgDensity q p * dftMatrix q) *
            (dftMatrix q)ᴴ := by
        simp only [Matrix.mul_assoc]
      _ = dftMatrix q * D * (dftMatrix q)ᴴ := by rw [hconj]
  have hD_herm : D.IsHermitian := by
    refine Matrix.isHermitian_diagonal_of_self_adjoint _ ?_
    ext k; simp
  rw [hrev, vonNeumannEntropy_conj_isometry hFF hD_herm, vonNeumannEntropy_diagonal]
  congr 1
  let zeroFin : Fin q := ⟨0, by omega⟩
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ zeroFin)]
  have h0 : symmetricPureEigenvalue q p zeroFin =
      (1 + ((q : ℝ) - 1) * symmetricPureCorr q p) / (q : ℝ) := by
    simp [symmetricPureEigenvalue, zeroFin]
  have herase : ∀ k ∈ Finset.univ.erase zeroFin,
      Real.negMulLog (symmetricPureEigenvalue q p k) =
        Real.negMulLog ((1 - symmetricPureCorr q p) / (q : ℝ)) := by
    intro k hk
    have hne : k.val ≠ 0 := fun hv ↦ (Finset.ne_of_mem_erase hk) (Fin.ext hv)
    simp [symmetricPureEigenvalue, hne]
  rw [h0, Finset.sum_congr rfl herase, Finset.sum_const,
    Finset.card_erase_of_mem (Finset.mem_univ zeroFin), Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_sub hq1, Nat.cast_one]

/-! ### Exact binary identity (`q = 2`) -/

/-- For the binary symmetric pure-state channel ($q = 2$) and $p \in [0, 1]$, the Holevo capacity
satisfies the exact identity $\chi_2(p) = H_2(\frac{1}{2} - \sqrt{p(1 - p)})$ (in bits). -/
theorem symmetricPureHolevo_two {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    symmetricPureHolevo 2 p =
      Real.binEntropy (1 / 2 - Real.sqrt (p * (1 - p))) / Real.log 2 := by
  rw [symmetricPureHolevo_eq_eigenvalue_sum (by norm_num : 2 ≤ 2) hp0 hp1]
  have hcorr : symmetricPureCorr 2 p = 2 * Real.sqrt (p * (1 - p)) := by
    rw [symmetricPureCorr]; norm_num
  rw [hcorr, Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  congr 1
  push_cast
  have h1 : (2 : ℝ) - 1 = 1 := by norm_num
  have ha : (1 + (2 - 1) * (2 * Real.sqrt (p * (1 - p)))) / 2 =
      1 - (1 / 2 - Real.sqrt (p * (1 - p))) := by ring
  have hb : (1 - 2 * Real.sqrt (p * (1 - p))) / 2 =
      1 / 2 - Real.sqrt (p * (1 - p)) := by ring
  rw [ha, hb, h1, one_mul, add_comm]

/-! ### Quadratic/cubic Taylor estimates and asymptotic expansion of $\chi_q(p)$ -/

private theorem mul_log_one_add_sub_ge_nonpos {t : ℝ} (ht : -1 < t) (ht0 : t ≤ 0) :
    t ^ 2 / 2 ≤ (1 + t) * Real.log (1 + t) - t := by
  let g : ℝ → ℝ := fun x ↦ (1 + x) * Real.log (1 + x) - x - x ^ 2 / 2
  have hanti : AntitoneOn g (Set.Icc t 0) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc t 0) ?_ ?_ fun x hx ↦ ?_
    · refine ContinuousOn.sub (ContinuousOn.sub ?_ continuousOn_id) (by fun_prop)
      exact (continuousOn_const.add continuousOn_id).mul
        (Real.continuousOn_log.comp (continuousOn_const.add continuousOn_id) fun y hy ↦
          ne_of_gt (by linarith [hy.1]))
    · intro x hx
      rw [interior_Icc] at hx
      have hxpos : 0 < 1 + x := by linarith [hx.1]
      exact (((differentiableAt_id.const_add 1).mul
        ((differentiableAt_id.const_add 1).log hxpos.ne')).sub differentiableAt_id).sub
          (by fun_prop) |>.differentiableWithinAt
    · rw [interior_Icc] at hx
      have hxpos : 0 < 1 + x := by linarith [hx.1]
      have hd : HasDerivAt g (Real.log (1 + x) - x) x := by
        have h1 : HasDerivAt (fun y ↦ 1 + y) 1 x := by
          simpa using (hasDerivAt_id x).const_add 1
        have h2 : HasDerivAt (fun y ↦ Real.log (1 + y)) (1 / (1 + x)) x := by
          simpa using h1.log hxpos.ne'
        have h3 : HasDerivAt (fun y ↦ (1 + y) * Real.log (1 + y))
            (1 * Real.log (1 + x) + (1 + x) * (1 / (1 + x))) x := h1.mul h2
        have h4 : HasDerivAt (fun y ↦ y ^ 2 / 2) x x := by
          simpa using ((hasDerivAt_pow 2 x).div_const 2)
        exact ((h3.sub (hasDerivAt_id x)).sub h4).congr_deriv (by field_simp [hxpos.ne']; ring)
      rw [hd.deriv]
      linarith [Real.log_le_sub_one_of_pos hxpos]
  have hg0 : g 0 = 0 := by simp [g]
  have hgt : 0 ≤ g t := hg0 ▸ hanti ⟨le_rfl, ht0⟩ ⟨ht0, le_rfl⟩ ht0
  dsimp only [g] at hgt
  linarith

/-- Lower Taylor bound $(1 + t)\ln(1 + t) - t \ge \frac{t^2}{2} - \frac{|t|^3}{3}$ for all
$t > -1$ (in fact $\ge t^2 / 2$ on $(-1, 0]$ and $\ge t^2 / 2 - t^3 / 6$ on $[0, \infty)$). -/
private theorem mul_log_one_add_sub_ge {t : ℝ} (ht : -1 < t) :
    t ^ 2 / 2 - |t| ^ 3 / 3 ≤ (1 + t) * Real.log (1 + t) - t := by
  rcases le_or_gt t 0 with ht0 | ht0
  · have hgt := mul_log_one_add_sub_ge_nonpos ht ht0
    have habs : 0 ≤ |t| ^ 3 / 3 := by positivity
    linarith
  · -- On `[0, ∞)`, `(1 + t) log(1 + t) - t ≥ t^2 / 2 - t^3 / 6`.
    let h : ℝ → ℝ := fun x ↦ (1 + x) * Real.log (1 + x) - x - x ^ 2 / 2 + x ^ 3 / 6
    let h' : ℝ → ℝ := fun x ↦ Real.log (1 + x) - x + x ^ 2 / 2
    have h'_mono : MonotoneOn h' (Set.Icc 0 t) := by
      refine monotoneOn_of_deriv_nonneg (convex_Icc 0 t) ?_ ?_ fun x hx ↦ ?_
      · refine ContinuousOn.add (ContinuousOn.sub ?_ continuousOn_id) (by fun_prop)
        exact Real.continuousOn_log.comp (continuousOn_const.add continuousOn_id) fun y hy ↦
          ne_of_gt (by linarith [hy.1])
      · intro x hx
        rw [interior_Icc] at hx
        have hxpos : 0 < 1 + x := by linarith [hx.1]
        exact (((differentiableAt_id.const_add 1).log hxpos.ne').sub differentiableAt_id).add
          (by fun_prop) |>.differentiableWithinAt
      · rw [interior_Icc] at hx
        have hxpos : 0 < 1 + x := by linarith [hx.1]
        have hd : HasDerivAt h' (x ^ 2 / (1 + x)) x := by
          have h1 : HasDerivAt (fun y ↦ 1 + y) 1 x := by
            simpa using (hasDerivAt_id x).const_add 1
          have h2 : HasDerivAt (fun y ↦ Real.log (1 + y)) (1 / (1 + x)) x := by
            simpa using h1.log hxpos.ne'
          have h3 : HasDerivAt (fun y ↦ y ^ 2 / 2) x x := by
            simpa using ((hasDerivAt_pow 2 x).div_const 2)
          exact ((h2.sub (hasDerivAt_id x)).add h3).congr_deriv (by field_simp [hxpos.ne']; ring)
        rw [hd.deriv]
        positivity
    have h_mono : MonotoneOn h (Set.Icc 0 t) := by
      refine monotoneOn_of_deriv_nonneg (convex_Icc 0 t) ?_ ?_ fun x hx ↦ ?_
      · refine ContinuousOn.add (ContinuousOn.sub (ContinuousOn.sub ?_ continuousOn_id)
          (by fun_prop)) (by fun_prop)
        exact (continuousOn_const.add continuousOn_id).mul
          (Real.continuousOn_log.comp (continuousOn_const.add continuousOn_id) fun y hy ↦
            ne_of_gt (by linarith [hy.1]))
      · intro x hx
        rw [interior_Icc] at hx
        have hxpos : 0 < 1 + x := by linarith [hx.1]
        exact ((((differentiableAt_id.const_add 1).mul
          ((differentiableAt_id.const_add 1).log hxpos.ne')).sub differentiableAt_id).sub
            (by fun_prop)).add (by fun_prop) |>.differentiableWithinAt
      · rw [interior_Icc] at hx
        have hxpos : 0 < 1 + x := by linarith [hx.1]
        have hd : HasDerivAt h (h' x) x := by
          have h1 : HasDerivAt (fun y ↦ 1 + y) 1 x := by
            simpa using (hasDerivAt_id x).const_add 1
          have h2 : HasDerivAt (fun y ↦ Real.log (1 + y)) (1 / (1 + x)) x := by
            simpa using h1.log hxpos.ne'
          have h3 : HasDerivAt (fun y ↦ (1 + y) * Real.log (1 + y))
              (1 * Real.log (1 + x) + (1 + x) * (1 / (1 + x))) x := h1.mul h2
          have h4 : HasDerivAt (fun y ↦ y ^ 2 / 2) x x := by
            simpa using ((hasDerivAt_pow 2 x).div_const 2)
          have h5 : HasDerivAt (fun y ↦ y ^ 3 / 6) (x ^ 2 / 2) x :=
            ((hasDerivAt_pow 3 x).div_const 6).congr_deriv (by norm_num; ring)
          exact (((h3.sub (hasDerivAt_id x)).sub h4).add h5).congr_deriv
            (by dsimp only [h']; field_simp [hxpos.ne']; ring)
        rw [hd.deriv]
        have h'0 : h' 0 = 0 := by simp [h']
        exact h'0 ▸ h'_mono ⟨le_rfl, ht0.le⟩ ⟨le_of_lt hx.1, le_of_lt hx.2⟩ (le_of_lt hx.1)
    have hh0 : h 0 = 0 := by simp [h]
    have hht : 0 ≤ h t := hh0 ▸ h_mono ⟨le_rfl, ht0.le⟩ ⟨ht0.le, le_rfl⟩ ht0.le
    rw [abs_of_pos ht0]
    have hpow : t ^ 3 / 6 ≤ t ^ 3 / 3 := by
      have : 0 ≤ t ^ 3 := by positivity
      linarith
    dsimp only [h] at hht
    linarith

/-- Upper Taylor bound $(1 + t)\ln(1 + t) - t \le \frac{t^2}{2} + \frac{|t|^3}{3}$ for all
$t \ge -1 / 2$. -/
private theorem mul_log_one_add_sub_le {t : ℝ} (ht : -1 / 2 ≤ t) :
    (1 + t) * Real.log (1 + t) - t ≤ t ^ 2 / 2 + |t| ^ 3 / 3 := by
  rcases le_or_gt t 0 with ht0 | ht0
  · -- On `[-1/2, 0]`, `(1 + t) log(1 + t) - t ≤ t^2 / 2 - t^3 / 3`.
    let k : ℝ → ℝ := fun x ↦ x ^ 2 / 2 - x ^ 3 / 3 - ((1 + x) * Real.log (1 + x) - x)
    let k' : ℝ → ℝ := fun x ↦ x - x ^ 2 - Real.log (1 + x)
    have hk'_mono : MonotoneOn k' (Set.Icc t 0) := by
      refine monotoneOn_of_deriv_nonneg (convex_Icc t 0) ?_ ?_ fun x hx ↦ ?_
      · refine ContinuousOn.sub (by fun_prop) ?_
        exact Real.continuousOn_log.comp (continuousOn_const.add continuousOn_id) fun y hy ↦
          ne_of_gt (by linarith [hy.1])
      · intro x hx
        rw [interior_Icc] at hx
        have hxpos : 0 < 1 + x := by linarith [hx.1]
        exact ((by fun_prop : DifferentiableAt ℝ (fun y ↦ y - y ^ 2) x).sub
          ((differentiableAt_id.const_add 1).log hxpos.ne')).differentiableWithinAt
      · rw [interior_Icc] at hx
        have hxpos : 0 < 1 + x := by linarith [hx.1]
        have hd : HasDerivAt k' (-x * (1 + 2 * x) / (1 + x)) x := by
          have h1 : HasDerivAt (fun y ↦ 1 + y) 1 x := by
            simpa using (hasDerivAt_id x).const_add 1
          have h2 : HasDerivAt (fun y ↦ Real.log (1 + y)) (1 / (1 + x)) x := by
            simpa using h1.log hxpos.ne'
          have h3 : HasDerivAt (fun y ↦ y - y ^ 2) (1 - 2 * x) x :=
            ((hasDerivAt_id x).sub (hasDerivAt_pow 2 x)).congr_deriv (by norm_num)
          exact (h3.sub h2).congr_deriv (by field_simp [hxpos.ne']; ring)
        rw [hd.deriv]
        have hnx : 0 ≤ -x := by linarith [hx.2]
        have h12x : 0 ≤ 1 + 2 * x := by linarith [hx.1]
        positivity
    have hk_anti : AntitoneOn k (Set.Icc t 0) := by
      refine antitoneOn_of_deriv_nonpos (convex_Icc t 0) ?_ ?_ fun x hx ↦ ?_
      · refine ContinuousOn.sub (by fun_prop)
          (ContinuousOn.sub ?_ continuousOn_id)
        exact (continuousOn_const.add continuousOn_id).mul
          (Real.continuousOn_log.comp (continuousOn_const.add continuousOn_id) fun y hy ↦
            ne_of_gt (by linarith [hy.1]))
      · intro x hx
        rw [interior_Icc] at hx
        have hxpos : 0 < 1 + x := by linarith [hx.1]
        exact ((by fun_prop : DifferentiableAt ℝ (fun y ↦ y ^ 2 / 2 - y ^ 3 / 3) x).sub
          (((differentiableAt_id.const_add 1).mul
            ((differentiableAt_id.const_add 1).log hxpos.ne')).sub
              differentiableAt_id)).differentiableWithinAt
      · rw [interior_Icc] at hx
        have hxpos : 0 < 1 + x := by linarith [hx.1]
        have hd : HasDerivAt k (k' x) x := by
          have h1 : HasDerivAt (fun y ↦ 1 + y) 1 x := by
            simpa using (hasDerivAt_id x).const_add 1
          have h2 : HasDerivAt (fun y ↦ Real.log (1 + y)) (1 / (1 + x)) x := by
            simpa using h1.log hxpos.ne'
          have h3 : HasDerivAt (fun y ↦ (1 + y) * Real.log (1 + y))
              (1 * Real.log (1 + x) + (1 + x) * (1 / (1 + x))) x := h1.mul h2
          have h4 : HasDerivAt (fun y ↦ y ^ 2 / 2) x x := by
            simpa using (hasDerivAt_pow 2 x).div_const 2
          have h5 : HasDerivAt (fun y ↦ y ^ 3 / 3) (x ^ 2) x :=
            ((hasDerivAt_pow 3 x).div_const 3).congr_deriv (by norm_num)
          exact ((h4.sub h5).sub (h3.sub (hasDerivAt_id x))).congr_deriv
            (by dsimp only [k']; field_simp [hxpos.ne']; ring)
        rw [hd.deriv]
        have hk'0 : k' 0 = 0 := by simp [k']
        exact hk'0 ▸ hk'_mono ⟨le_of_lt hx.1, le_of_lt hx.2⟩ ⟨ht0, le_rfl⟩ (le_of_lt hx.2)
    have hk0 : k 0 = 0 := by simp [k]
    have hkt : 0 ≤ k t := hk0 ▸ hk_anti ⟨le_rfl, ht0⟩ ⟨ht0, le_rfl⟩ ht0
    rw [abs_of_nonpos ht0]
    dsimp only [k] at hkt
    have hcube : (-t) ^ 3 = -t ^ 3 := by ring
    rw [hcube]
    linarith
  · -- On `(0, ∞)`, `(1 + t) log(1 + t) - t ≤ t^2 / 2`.
    let m : ℝ → ℝ := fun x ↦ x ^ 2 / 2 - ((1 + x) * Real.log (1 + x) - x)
    have hm_mono : MonotoneOn m (Set.Icc 0 t) := by
      refine monotoneOn_of_deriv_nonneg (convex_Icc 0 t) ?_ ?_ fun x hx ↦ ?_
      · refine ContinuousOn.sub (by fun_prop) (ContinuousOn.sub ?_ continuousOn_id)
        exact (continuousOn_const.add continuousOn_id).mul
          (Real.continuousOn_log.comp (continuousOn_const.add continuousOn_id) fun y hy ↦
            ne_of_gt (by linarith [hy.1]))
      · intro x hx
        rw [interior_Icc] at hx
        have hxpos : 0 < 1 + x := by linarith [hx.1]
        exact ((by fun_prop : DifferentiableAt ℝ (fun y ↦ y ^ 2 / 2) x).sub
          (((differentiableAt_id.const_add 1).mul
            ((differentiableAt_id.const_add 1).log hxpos.ne')).sub
              differentiableAt_id)).differentiableWithinAt
      · rw [interior_Icc] at hx
        have hxpos : 0 < 1 + x := by linarith [hx.1]
        have hd : HasDerivAt m (x - Real.log (1 + x)) x := by
          have h1 : HasDerivAt (fun y ↦ 1 + y) 1 x := by
            simpa using (hasDerivAt_id x).const_add 1
          have h2 : HasDerivAt (fun y ↦ Real.log (1 + y)) (1 / (1 + x)) x := by
            simpa using h1.log hxpos.ne'
          have h3 : HasDerivAt (fun y ↦ (1 + y) * Real.log (1 + y))
              (1 * Real.log (1 + x) + (1 + x) * (1 / (1 + x))) x := h1.mul h2
          have h4 : HasDerivAt (fun y ↦ y ^ 2 / 2) x x := by
            simpa using (hasDerivAt_pow 2 x).div_const 2
          exact (h4.sub (h3.sub (hasDerivAt_id x))).congr_deriv
            (by field_simp [hxpos.ne']; ring)
        rw [hd.deriv]
        linarith [Real.log_le_sub_one_of_pos hxpos]
    have hm0 : m 0 = 0 := by simp [m]
    have hmt : 0 ≤ m t := hm0 ▸ hm_mono ⟨le_rfl, ht0.le⟩ ⟨ht0.le, le_rfl⟩ ht0.le
    have habs : 0 ≤ |t| ^ 3 / 3 := by positivity
    dsimp only [m] at hmt
    linarith

/-- Exact algebraic completion-of-square identity
$1 - \gamma_q(p) = (\sqrt{1 - p} - \sqrt{p / (q - 1)})^2$ for $q \ge 2$ and $p \in [0, 1]$,
implying $\gamma_q(p) \in [0, 1]$. -/
theorem one_sub_symmetricPureCorr_eq_sq {q : ℕ} (hq : 2 ≤ q) {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    1 - symmetricPureCorr q p =
      (Real.sqrt (1 - p) - Real.sqrt (p / ((q : ℝ) - 1))) ^ 2 := by
  have hq1 : (0 : ℝ) < (q : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    linarith
  have h1p : 0 ≤ 1 - p := sub_nonneg.mpr hp1
  have hpq : 0 ≤ p / ((q : ℝ) - 1) := div_nonneg hp0 hq1.le
  rw [sub_sq, Real.sq_sqrt h1p, Real.sq_sqrt hpq, symmetricPureCorr]
  have hsqrt : Real.sqrt (1 - p) * Real.sqrt (p / ((q : ℝ) - 1)) =
      Real.sqrt (p * (1 - p) / ((q : ℝ) - 1)) := by
    rw [← Real.sqrt_mul h1p]; congr 1; ring
  rw [mul_assoc 2, hsqrt]
  field_simp [hq1.ne']
  ring

theorem symmetricPureCorr_nonneg {q : ℕ} (hq : 2 ≤ q) {p : ℝ} (hp0 : 0 ≤ p) :
    0 ≤ symmetricPureCorr q p := by
  have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  rw [symmetricPureCorr]
  have h1 : 0 ≤ ((q : ℝ) - 2) * p / ((q : ℝ) - 1) :=
    div_nonneg (mul_nonneg (by linarith) hp0) (by linarith)
  positivity

theorem symmetricPureCorr_le_one {q : ℕ} (hq : 2 ≤ q) {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    symmetricPureCorr q p ≤ 1 := by
  have h := one_sub_symmetricPureCorr_eq_sq hq hp0 hp1
  nlinarith [sq_nonneg (Real.sqrt (1 - p) - Real.sqrt (p / ((q : ℝ) - 1)))]

/-- Global linear upper bound on the Holevo capacity of the $q$-ary symmetric pure-state channel:
for all $q \ge 2$ and $p \in [0, 1 / 2]$,
$$\chi_q(p) \le \log_2 q - \frac{p}{q \ln 2}.$$ -/
theorem symmetricPureHolevo_le_logb_sub_linear {q : ℕ} (hq : 2 ≤ q) [NeZero q] {p : ℝ}
    (hp0 : 0 ≤ p) (hp_half : p ≤ 1 / 2) :
    symmetricPureHolevo q p ≤ Real.logb 2 (q : ℝ) - p / ((q : ℝ) * Real.log 2) := by
  have hp1 : p ≤ 1 := by linarith
  have hq_ge2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hq_pos : (0 : ℝ) < (q : ℝ) := by linarith
  have hq1_pos : (0 : ℝ) < (q : ℝ) - 1 := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [symmetricPureHolevo_eq_eigenvalue_sum hq hp0 hp1]
  set γ := symmetricPureCorr q p
  have hγ0 : 0 ≤ γ := symmetricPureCorr_nonneg hq hp0
  have hγ1 : γ ≤ 1 := symmetricPureCorr_le_one hq hp0 hp1
  -- Nonnegativity of `(1 + t₀) log(1 + t₀) - t₀` for `t₀ = (q - 1) γ ≥ 0`.
  set t₀ : ℝ := ((q : ℝ) - 1) * γ
  have ht₀_nonneg : 0 ≤ t₀ := mul_nonneg hq1_pos.le hγ0
  have ht₀_pos : 0 < 1 + t₀ := by linarith
  have hterm₀ : 0 ≤ (1 + t₀) * Real.log (1 + t₀) - t₀ := by
    have hinv := Real.log_le_sub_one_of_pos (inv_pos.mpr ht₀_pos)
    rw [Real.log_inv] at hinv
    have h1 : 1 - (1 + t₀)⁻¹ ≤ Real.log (1 + t₀) := by linarith
    have hm := mul_le_mul_of_nonneg_left h1 ht₀_pos.le
    rw [mul_sub, mul_one, mul_inv_cancel₀ ht₀_pos.ne'] at hm
    linarith
  -- Quadratic lower bound `(1 - γ) log(1 - γ) + γ ≥ γ² / 2` (including the endpoint `γ = 1`).
  have hterm₁ : γ ^ 2 / 2 ≤ (1 - γ) * Real.log (1 - γ) + γ := by
    rcases eq_or_lt_of_le hγ1 with hγ_eq | hγ_lt
    · rw [hγ_eq]; norm_num
    · have hgt := mul_log_one_add_sub_ge_nonpos (t := -γ) (by linarith) (by linarith)
      have h1 : 1 + -γ = 1 - γ := by ring
      have h2 : (-γ) ^ 2 = γ ^ 2 := by ring
      rw [h1, h2] at hgt
      linarith
  -- Lower bound `(q - 1) γ² ≥ 2 p` for `p ≤ 1/2`.
  have hγ_sq : 2 * p ≤ ((q : ℝ) - 1) * γ ^ 2 := by
    have hγ_ge : 2 * Real.sqrt (p * (1 - p) / ((q : ℝ) - 1)) ≤ γ := by
      dsimp only [γ, symmetricPureCorr]
      have h2 : 0 ≤ ((q : ℝ) - 2) * p / ((q : ℝ) - 1) :=
        div_nonneg (mul_nonneg (by linarith) hp0) hq1_pos.le
      linarith
    have hsq : (2 * Real.sqrt (p * (1 - p) / ((q : ℝ) - 1))) ^ 2 ≤ γ ^ 2 :=
      pow_le_pow_left₀ (by positivity) hγ_ge 2
    have hval : (2 * Real.sqrt (p * (1 - p) / ((q : ℝ) - 1))) ^ 2 =
        4 * p * (1 - p) / ((q : ℝ) - 1) := by
      rw [mul_pow, Real.sq_sqrt (div_nonneg (mul_nonneg hp0 (by linarith)) hq1_pos.le)]
      ring
    rw [hval] at hsq
    have hm := mul_le_mul_of_nonneg_left hsq hq1_pos.le
    rw [mul_div_cancel₀ _ hq1_pos.ne'] at hm
    nlinarith
  -- Express `negMulLog((1 + t)/q)` in terms of `log q` and `(1 + t) log(1 + t)`.
  have hnml0 : Real.negMulLog ((1 + t₀) / (q : ℝ)) =
      (1 + t₀) / (q : ℝ) * Real.log (q : ℝ) - (1 + t₀) * Real.log (1 + t₀) / (q : ℝ) := by
    rw [Real.negMulLog, Real.log_div ht₀_pos.ne' hq_pos.ne']
    ring
  have hnml1 : Real.negMulLog ((1 - γ) / (q : ℝ)) =
      (1 - γ) / (q : ℝ) * Real.log (q : ℝ) - (1 - γ) * Real.log (1 - γ) / (q : ℝ) := by
    rcases eq_or_lt_of_le hγ1 with hγ_eq | hlt
    · rw [hγ_eq]; simp [Real.negMulLog]
    · have h1γ : 0 < 1 - γ := sub_pos.mpr hlt
      rw [Real.negMulLog, Real.log_div h1γ.ne' hq_pos.ne']
      ring
  rw [hnml0, hnml1, Real.logb]
  have hsum_id :
      ((1 + t₀) / (q : ℝ) * Real.log (q : ℝ) - (1 + t₀) * Real.log (1 + t₀) / (q : ℝ)) +
        ((q : ℝ) - 1) *
          ((1 - γ) / (q : ℝ) * Real.log (q : ℝ) - (1 - γ) * Real.log (1 - γ) / (q : ℝ)) =
      Real.log (q : ℝ) -
        (((1 + t₀) * Real.log (1 + t₀) - t₀) +
          ((q : ℝ) - 1) * ((1 - γ) * Real.log (1 - γ) + γ)) / (q : ℝ) := by
    dsimp only [t₀]
    field_simp [hq_pos.ne']
    ring
  rw [hsum_id, sub_div, ← div_mul_eq_div_div]
  refine sub_le_sub_left ?_ _
  rw [div_le_div_iff₀ (mul_pos hq_pos hlog2) (mul_pos hq_pos hlog2)]
  have hcomb : p ≤ ((1 + t₀) * Real.log (1 + t₀) - t₀) +
      ((q : ℝ) - 1) * ((1 - γ) * Real.log (1 - γ) + γ) := by
    have hmul1 := mul_le_mul_of_nonneg_left hterm₁ hq1_pos.le
    linarith
  exact mul_le_mul_of_nonneg_right hcomb (mul_pos hq_pos hlog2).le

private theorem symmetricPureCorr_quad_rem {q : ℕ} (hq : 2 ≤ q) {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    |((q : ℝ) - 1) * (symmetricPureCorr q p) ^ 2 / 2 - 2 * p| ≤
      12 * (q : ℝ) * (Real.sqrt p) ^ 3 := by
  have hq_ge2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hq_pos : (0 : ℝ) < (q : ℝ) := by linarith
  have hq1_pos : (0 : ℝ) < (q : ℝ) - 1 := by linarith
  have hexpand : ((q : ℝ) - 1) * (symmetricPureCorr q p) ^ 2 / 2 - 2 * p =
      -2 * p ^ 2 + 2 * ((q : ℝ) - 2) * p * Real.sqrt (p * (1 - p) / ((q : ℝ) - 1)) +
        ((q : ℝ) - 2) ^ 2 / (2 * ((q : ℝ) - 1)) * p ^ 2 := by
    rw [symmetricPureCorr]
    have hsq : (2 * Real.sqrt (p * (1 - p) / ((q : ℝ) - 1)) +
        ((q : ℝ) - 2) * p / ((q : ℝ) - 1)) ^ 2 =
        4 * (p * (1 - p) / ((q : ℝ) - 1)) +
          4 * (((q : ℝ) - 2) * p / ((q : ℝ) - 1)) *
            Real.sqrt (p * (1 - p) / ((q : ℝ) - 1)) +
          (((q : ℝ) - 2) * p / ((q : ℝ) - 1)) ^ 2 := by
      rw [add_sq, mul_pow,
        Real.sq_sqrt (div_nonneg (mul_nonneg hp0 (by linarith)) hq1_pos.le)]
      ring
    rw [hsq]
    field_simp [hq1_pos.ne']
    ring
  rw [hexpand]
  have hsp_sq : (Real.sqrt p) ^ 2 = p := Real.sq_sqrt hp0
  have hp_sp3 : p * Real.sqrt p = (Real.sqrt p) ^ 3 := by
    calc
      p * Real.sqrt p = (Real.sqrt p) ^ 2 * Real.sqrt p := by rw [hsp_sq]
      _ = (Real.sqrt p) ^ 3 := by ring
  have hsp_le1 : Real.sqrt p ≤ 1 := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt hp1
  have hp_le_sp : p ≤ Real.sqrt p := by
    calc
      p = Real.sqrt p * Real.sqrt p := (Real.mul_self_sqrt hp0).symm
      _ ≤ 1 * Real.sqrt p := mul_le_mul_of_nonneg_right hsp_le1 (Real.sqrt_nonneg p)
      _ = Real.sqrt p := one_mul _
  have hp2_le : p ^ 2 ≤ (Real.sqrt p) ^ 3 := by
    calc
      p ^ 2 = p * p := sq p
      _ ≤ p * Real.sqrt p := mul_le_mul_of_nonneg_left hp_le_sp hp0
      _ = (Real.sqrt p) ^ 3 := hp_sp3
  have hrad_le : Real.sqrt (p * (1 - p) / ((q : ℝ) - 1)) ≤ Real.sqrt p := by
    refine Real.sqrt_le_sqrt ?_
    rw [div_le_iff₀ hq1_pos]; nlinarith
  have hmid_le : 2 * ((q : ℝ) - 2) * p * Real.sqrt (p * (1 - p) / ((q : ℝ) - 1)) ≤
      2 * (q : ℝ) * (Real.sqrt p) ^ 3 := by
    calc
      2 * ((q : ℝ) - 2) * p * Real.sqrt (p * (1 - p) / ((q : ℝ) - 1))
        ≤ 2 * ((q : ℝ) - 2) * p * Real.sqrt p :=
          mul_le_mul_of_nonneg_left hrad_le (mul_nonneg (by linarith) hp0)
      _ = 2 * ((q : ℝ) - 2) * (Real.sqrt p) ^ 3 := by rw [mul_assoc, hp_sp3]
      _ ≤ 2 * (q : ℝ) * (Real.sqrt p) ^ 3 :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have hlast_le : ((q : ℝ) - 2) ^ 2 / (2 * ((q : ℝ) - 1)) * p ^ 2 ≤
      (q : ℝ) * (Real.sqrt p) ^ 3 := by
    have hdiv_le : ((q : ℝ) - 2) ^ 2 / (2 * ((q : ℝ) - 1)) ≤ (q : ℝ) := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    calc
      ((q : ℝ) - 2) ^ 2 / (2 * ((q : ℝ) - 1)) * p ^ 2
        ≤ (q : ℝ) * p ^ 2 := mul_le_mul_of_nonneg_right hdiv_le (sq_nonneg p)
      _ ≤ (q : ℝ) * (Real.sqrt p) ^ 3 := mul_le_mul_of_nonneg_left hp2_le hq_pos.le
  have hp2_nn : 0 ≤ p ^ 2 := sq_nonneg p
  have hnonneg_mid : 0 ≤ 2 * ((q : ℝ) - 2) * p * Real.sqrt (p * (1 - p) / ((q : ℝ) - 1)) :=
    mul_nonneg (mul_nonneg (by linarith) hp0) (Real.sqrt_nonneg _)
  have hnonneg_last : 0 ≤ ((q : ℝ) - 2) ^ 2 / (2 * ((q : ℝ) - 1)) * p ^ 2 := by positivity
  have hnonneg_sp3 : 0 ≤ (Real.sqrt p) ^ 3 := by positivity
  have h2p2_le : 2 * p ^ 2 ≤ 2 * (q : ℝ) * (Real.sqrt p) ^ 3 := by
    calc
      2 * p ^ 2 ≤ 2 * (Real.sqrt p) ^ 3 := mul_le_mul_of_nonneg_left hp2_le (by norm_num)
      _ = 2 * 1 * (Real.sqrt p) ^ 3 := by ring
      _ ≤ 2 * (q : ℝ) * (Real.sqrt p) ^ 3 :=
          mul_le_mul_of_nonneg_right (by linarith) hnonneg_sp3
  have hpos_qsp3 : 0 ≤ (q : ℝ) * (Real.sqrt p) ^ 3 := by positivity
  exact abs_le.mpr ⟨by linarith, by linarith⟩

private theorem holevo_expansion_algebraic {qr log2 γ E₀ E₁ p sp : ℝ}
    (hq_ge2 : 2 ≤ qr) (hq_pos : 0 < qr) (hlog2 : 0 < log2) (_hsp0 : 0 ≤ sp)
    (hγ0 : 0 ≤ γ) (hγ_le : γ ≤ 3 * sp)
    (habs₀ : |E₀ - ((qr - 1) * γ) ^ 2 / 2| ≤ |(qr - 1) * γ| ^ 3 / 3)
    (habs₁ : |E₁ - (-γ) ^ 2 / 2| ≤ |-γ| ^ 3 / 3)
    (hquad : |(qr - 1) * γ ^ 2 / 2 - 2 * p| ≤ 12 * qr * sp ^ 3) :
    (((1 + (qr - 1) * γ) / qr * Real.log qr - ((qr - 1) * γ + E₀) / qr) +
        (qr - 1) * ((1 - γ) / qr * Real.log qr - (-γ + E₁) / qr)) / log2 -
      (Real.log qr / log2 - 2 * p / log2) ∈
      Set.Icc (-((18 * qr ^ 2 + 12 * qr) / log2 * sp ^ 3))
        ((18 * qr ^ 2 + 12 * qr) / log2 * sp ^ 3) := by
  rw [Set.mem_Icc, ← abs_le]
  have hq1_pos : 0 < qr - 1 := by linarith
  have hdiff_id :
      (((1 + (qr - 1) * γ) / qr * Real.log qr - ((qr - 1) * γ + E₀) / qr) +
          (qr - 1) * ((1 - γ) / qr * Real.log qr - (-γ + E₁) / qr)) / log2 -
        (Real.log qr / log2 - 2 * p / log2) =
      -((E₀ - ((qr - 1) * γ) ^ 2 / 2) + (qr - 1) * (E₁ - (-γ) ^ 2 / 2)) / (qr * log2) -
        ((qr - 1) * γ ^ 2 / 2 - 2 * p) / log2 := by
    field_simp [hq_pos.ne', hlog2.ne']
    ring
  rw [hdiff_id]
  have ht₀_abs : |(qr - 1) * γ| ≤ 3 * qr * sp := by
    rw [abs_of_nonneg (mul_nonneg hq1_pos.le hγ0)]
    calc
      (qr - 1) * γ ≤ qr * γ := by nlinarith
      _ ≤ qr * (3 * sp) := mul_le_mul_of_nonneg_left hγ_le hq_pos.le
      _ = 3 * qr * sp := by ring
  have ht₁_abs : |-γ| ≤ 3 * sp := by
    rw [abs_neg, abs_of_nonneg hγ0]
    exact hγ_le
  have hq_le_q3 : qr - 1 ≤ qr ^ 3 := by
    have hsq : qr ≤ qr ^ 2 := by nlinarith
    nlinarith
  have hrem_taylor :
      |(E₀ - ((qr - 1) * γ) ^ 2 / 2) + (qr - 1) * (E₁ - (-γ) ^ 2 / 2)| / qr ≤
        18 * qr ^ 2 * sp ^ 3 := by
    have htri : |(E₀ - ((qr - 1) * γ) ^ 2 / 2) + (qr - 1) * (E₁ - (-γ) ^ 2 / 2)| ≤
        |(qr - 1) * γ| ^ 3 / 3 + (qr - 1) * (|-γ| ^ 3 / 3) := by
      calc
        |(E₀ - ((qr - 1) * γ) ^ 2 / 2) + (qr - 1) * (E₁ - (-γ) ^ 2 / 2)|
          ≤ |E₀ - ((qr - 1) * γ) ^ 2 / 2| + |(qr - 1) * (E₁ - (-γ) ^ 2 / 2)| := abs_add_le _ _
        _ = |E₀ - ((qr - 1) * γ) ^ 2 / 2| + (qr - 1) * |E₁ - (-γ) ^ 2 / 2| := by
          rw [abs_mul, abs_of_pos hq1_pos]
        _ ≤ |(qr - 1) * γ| ^ 3 / 3 + (qr - 1) * (|-γ| ^ 3 / 3) := by gcongr
    have hc₀ : |(qr - 1) * γ| ^ 3 / 3 ≤ 9 * qr ^ 3 * sp ^ 3 := by
      have hp3 := pow_le_pow_left₀ (abs_nonneg _) ht₀_abs 3
      linarith [show (3 * qr * sp) ^ 3 = 27 * qr ^ 3 * sp ^ 3 by ring]
    have hc₁ : |-γ| ^ 3 / 3 ≤ 9 * sp ^ 3 := by
      have hp3 := pow_le_pow_left₀ (abs_nonneg _) ht₁_abs 3
      linarith [show (3 * sp) ^ 3 = 27 * sp ^ 3 by ring]
    have hmul₁ : (qr - 1) * (|-γ| ^ 3 / 3) ≤ 9 * qr ^ 3 * sp ^ 3 := by
      calc
        (qr - 1) * (|-γ| ^ 3 / 3)
          ≤ qr ^ 3 * (9 * sp ^ 3) := mul_le_mul hq_le_q3 hc₁ (by positivity) (by positivity)
        _ = 9 * qr ^ 3 * sp ^ 3 := by ring
    rw [div_le_iff₀ hq_pos]
    linarith [show (18 * qr ^ 2 * sp ^ 3) * qr = 18 * qr ^ 3 * sp ^ 3 by ring]
  calc
    |-((E₀ - ((qr - 1) * γ) ^ 2 / 2) + (qr - 1) * (E₁ - (-γ) ^ 2 / 2)) / (qr * log2) -
        ((qr - 1) * γ ^ 2 / 2 - 2 * p) / log2|
      ≤ |-((E₀ - ((qr - 1) * γ) ^ 2 / 2) + (qr - 1) * (E₁ - (-γ) ^ 2 / 2)) / (qr * log2)| +
          |((qr - 1) * γ ^ 2 / 2 - 2 * p) / log2| := abs_sub _ _
    _ = (|(E₀ - ((qr - 1) * γ) ^ 2 / 2) + (qr - 1) * (E₁ - (-γ) ^ 2 / 2)| / qr) / log2 +
          |(qr - 1) * γ ^ 2 / 2 - 2 * p| / log2 := by
        rw [neg_div, abs_neg, abs_div, abs_of_pos (mul_pos hq_pos hlog2), div_mul_eq_div_div,
          abs_div, abs_of_pos hlog2]
    _ ≤ (18 * qr ^ 2 * sp ^ 3) / log2 + (12 * qr * sp ^ 3) / log2 := by gcongr
    _ = (18 * qr ^ 2 + 12 * qr) / log2 * sp ^ 3 := by ring

/-- **Asymptotic expansion of the $q$-ary symmetric pure-state Holevo capacity**:
for every $q \ge 2$, there exists a constant $C_q > 0$ such that for all
$p \in [0, \frac{1}{36}]$,
$$\left|\chi_q(p) - \left(\log_2 q - \frac{2 p}{\ln 2}\right)\right| \le C_q \, p^{3/2},$$
with leading linear coefficient $-2 / \ln 2$ independent of $q$. -/
theorem symmetricPureHolevo_expansion (q : ℕ) (hq : 2 ≤ q) [NeZero q] :
    ∃ C : ℝ, 0 < C ∧ ∀ ⦃p : ℝ⦄, 0 ≤ p → p ≤ 1 / 36 →
      |symmetricPureHolevo q p - (Real.logb 2 (q : ℝ) - 2 * p / Real.log 2)| ≤
        C * p ^ ((3 : ℝ) / 2) := by
  have hq_ge2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hq_pos : (0 : ℝ) < (q : ℝ) := by linarith
  have hq1_pos : (0 : ℝ) < (q : ℝ) - 1 := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨(18 * (q : ℝ) ^ 2 + 12 * (q : ℝ)) / Real.log 2, by positivity, fun p hp0 hp36 ↦ ?_⟩
  have hp1 : p ≤ 1 := by linarith
  have hsqrt_le : Real.sqrt p ≤ 1 / 6 := by
    have h36 : Real.sqrt (1 / 36 : ℝ) = 1 / 6 := by
      rw [show (1 / 36 : ℝ) = (1 / 6 : ℝ) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    exact h36 ▸ Real.sqrt_le_sqrt hp36
  have hγ0 : 0 ≤ symmetricPureCorr q p := symmetricPureCorr_nonneg hq hp0
  have hγ_le_3sqrt : symmetricPureCorr q p ≤ 3 * Real.sqrt p := by
    rw [symmetricPureCorr]
    have h1 : Real.sqrt (p * (1 - p) / ((q : ℝ) - 1)) ≤ Real.sqrt p := by
      refine Real.sqrt_le_sqrt ?_
      rw [div_le_iff₀ hq1_pos]
      nlinarith
    have h2 : ((q : ℝ) - 2) * p / ((q : ℝ) - 1) ≤ p := by
      rw [div_le_iff₀ hq1_pos]; nlinarith
    have h3 : p ≤ Real.sqrt p := by
      have hsq : p = Real.sqrt p * Real.sqrt p := (Real.mul_self_sqrt hp0).symm
      nlinarith [Real.sqrt_nonneg p]
    linarith
  have hγ_half : symmetricPureCorr q p ≤ 1 / 2 := by linarith
  have ht₀_ge : -1 / 2 ≤ ((q : ℝ) - 1) * symmetricPureCorr q p := by nlinarith
  have ht₁_ge : -1 / 2 ≤ -symmetricPureCorr q p := by linarith
  have ht₀_gt : -1 < ((q : ℝ) - 1) * symmetricPureCorr q p := by linarith
  have ht₁_gt : -1 < -symmetricPureCorr q p := by linarith
  have habs₀ : |((1 + ((q : ℝ) - 1) * symmetricPureCorr q p) *
        Real.log (1 + ((q : ℝ) - 1) * symmetricPureCorr q p) -
        ((q : ℝ) - 1) * symmetricPureCorr q p) -
      (((q : ℝ) - 1) * symmetricPureCorr q p) ^ 2 / 2| ≤
      |((q : ℝ) - 1) * symmetricPureCorr q p| ^ 3 / 3 :=
    abs_sub_le_iff.mpr ⟨by linarith [mul_log_one_add_sub_le ht₀_ge],
      by linarith [mul_log_one_add_sub_ge ht₀_gt]⟩
  have habs₁ : |((1 + -symmetricPureCorr q p) * Real.log (1 + -symmetricPureCorr q p) -
        -symmetricPureCorr q p) - (-symmetricPureCorr q p) ^ 2 / 2| ≤
      |-symmetricPureCorr q p| ^ 3 / 3 :=
    abs_sub_le_iff.mpr ⟨by linarith [mul_log_one_add_sub_le ht₁_ge],
      by linarith [mul_log_one_add_sub_ge ht₁_gt]⟩
  rw [symmetricPureHolevo_eq_eigenvalue_sum hq hp0 hp1, Real.logb]
  have ht₀_pos : 0 < 1 + ((q : ℝ) - 1) * symmetricPureCorr q p := by linarith
  have ht₁_pos : 0 < 1 - symmetricPureCorr q p := by linarith
  have hnml0 : Real.negMulLog ((1 + ((q : ℝ) - 1) * symmetricPureCorr q p) / (q : ℝ)) =
      (1 + ((q : ℝ) - 1) * symmetricPureCorr q p) / (q : ℝ) * Real.log (q : ℝ) -
        (((q : ℝ) - 1) * symmetricPureCorr q p +
          ((1 + ((q : ℝ) - 1) * symmetricPureCorr q p) *
            Real.log (1 + ((q : ℝ) - 1) * symmetricPureCorr q p) -
            ((q : ℝ) - 1) * symmetricPureCorr q p)) / (q : ℝ) := by
    rw [Real.negMulLog, Real.log_div ht₀_pos.ne' hq_pos.ne']; ring
  have hnml1 : Real.negMulLog ((1 - symmetricPureCorr q p) / (q : ℝ)) =
      (1 - symmetricPureCorr q p) / (q : ℝ) * Real.log (q : ℝ) -
        (-symmetricPureCorr q p +
          ((1 + -symmetricPureCorr q p) * Real.log (1 + -symmetricPureCorr q p) -
            -symmetricPureCorr q p)) / (q : ℝ) := by
    have h1 : 1 + -symmetricPureCorr q p = 1 - symmetricPureCorr q p := by ring
    rw [h1, Real.negMulLog, Real.log_div ht₁_pos.ne' hq_pos.ne']; ring
  rw [hnml0, hnml1]
  have hp_rpow : p ^ ((3 : ℝ) / 2) = (Real.sqrt p) ^ 3 := by
    have h1 : (Real.sqrt p) ^ 3 = (p ^ ((1 : ℝ) / 2)) ^ (3 : ℕ) := by rw [Real.sqrt_eq_rpow]
    rw [h1, ← Real.rpow_natCast, ← Real.rpow_mul hp0]
    norm_num
  rw [hp_rpow, abs_le]
  exact Set.mem_Icc.mp (holevo_expansion_algebraic hq_ge2 hq_pos hlog2 (Real.sqrt_nonneg p)
    hγ0 hγ_le_3sqrt habs₀ habs₁ (symmetricPureCorr_quad_rem hq hp0 hp1))

end CslibFrontier.Quantum

