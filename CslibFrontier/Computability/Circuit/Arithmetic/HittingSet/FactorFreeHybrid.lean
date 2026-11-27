/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FormalPapers Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.HittingSet.LowerBound
public import CslibFrontier.Computability.Circuit.Arithmetic.HittingSet.NWGenerator
public import CslibFrontier.Foundations.Data.Polynomial.InterpolationCoeff

import Mathlib.Algebra.Polynomial.Div
import Mathlib.Data.Fintype.EquivFin

/-!
# Factor-Free Nisan–Wigderson Hybrid Extraction and Bounded-Support Interpolation

This module develops two reusable algebraic-complexity building blocks for hardness-to-randomness
and hitting-set bootstrapping without polynomial factorization closure (Kaltofen's theorem):

1. **Bounded-support Heintz–Schnorr interpolation**
   (`exists_ne_zero_card_support_le_succ_forall_eval_eq_zero` and
   `IsHittingSet.exists_notMem_card_support_le_succ`): refines
   `Cslib.Circuits.Arithmetic.exists_ne_zero_forall_eval_eq_zero` by restricting `T` to a subset of
   cardinality `#H + 1`, guaranteeing `#f.support ≤ #H + 1` while preserving `f.support ⊆ T`.
2. **Lowest-nonzero-coefficient root-to-multiple extraction**
   (`exists_coeff_dvd_of_isRoot`) and **factor-free Nisan–Wigderson hybrid multiple extraction**
   (`exists_multiple_eq_sum_smul_aeval_of_nwGenerator_vanishing`): over any infinite field `K`
   (including positive characteristic), if a nonzero polynomial `P` of total degree at most `D`
   vanishes on `nwGenerator Q S` for `Q ≠ 0`, then `Q` divides a nonzero `(D + 1)`-term Lagrange
   linear combination of hybrid evaluations of `P` in which earlier blocks are specialized outside
   a single target block `S t` and later variables are specialized to field constants.

## Main results

* `Cslib.Circuits.Arithmetic.exists_ne_zero_card_support_le_succ_forall_eval_eq_zero`: bounded
  monomial support `#f.support ≤ #H + 1` for vanishing interpolants.
* `Cslib.Circuits.Arithmetic.IsHittingSet.exists_notMem_card_support_le_succ`: hard polynomial
  outside `𝒞` with support size at most `#H + 1`.
* `Cslib.Circuits.Arithmetic.exists_coeff_dvd_of_isRoot`: if `q ≠ 0` over an integral domain `R`
  has root `Q ≠ 0`, some nonzero coefficient `q.coeff a` (`a ≤ q.natDegree`) is divisible by `Q`.
* `Cslib.Circuits.Arithmetic.exists_multiple_eq_sum_smul_aeval_of_nwGenerator_vanishing`:
  factor-free Kabanets–Impagliazzo / Kumar–Saptharishi–Tengse hybrid multiple theorem over any
  infinite field.
-/

public section

namespace Cslib.Circuits.Arithmetic

open Finset MvPolynomial

section BoundedSupportInterpolation

variable {F σ : Type*} [Field F]

/-- **Bounded-support vanishing interpolant**: if `#H < #T`, there exists a nonzero polynomial `f`
supported in `T` with at most `#H + 1` nonzero monomials vanishing at every point of `H`. -/
theorem exists_ne_zero_card_support_le_succ_forall_eval_eq_zero
    (H : Finset (σ → F)) (T : Finset (σ →₀ ℕ)) (h : #H < #T) :
    ∃ f : MvPolynomial σ F,
      f ≠ 0 ∧ f.support ⊆ T ∧ #f.support ≤ #H + 1 ∧ ∀ a ∈ H, eval a f = 0 := by
  obtain ⟨T', hT'T, hT'card⟩ := Finset.exists_subset_card_eq (Nat.succ_le_of_lt h)
  obtain ⟨f, hf0, hfsupp, hfvan⟩ :=
    exists_ne_zero_forall_eval_eq_zero H T' (by omega)
  exact ⟨f, hf0, hfsupp.trans hT'T, (Finset.card_le_card hfsupp).trans_eq hT'card, hfvan⟩

/-- **Bounded-support hard polynomial from a hitting set**: if `H` hits `𝒞` and `#H < #T`, some
nonzero polynomial outside `𝒞` is supported in `T` and has at most `#H + 1` monomials. -/
theorem IsHittingSet.exists_notMem_card_support_le_succ
    {H : Finset (σ → F)} {𝒞 : Set (MvPolynomial σ F)} (hH : IsHittingSet H 𝒞)
    (T : Finset (σ →₀ ℕ)) (h : #H < #T) :
    ∃ f : MvPolynomial σ F,
      f ≠ 0 ∧ f.support ⊆ T ∧ #f.support ≤ #H + 1 ∧ (∀ a ∈ H, eval a f = 0) ∧ f ∉ 𝒞 := by
  obtain ⟨f, hf0, hfsupp, hfcard, hfvan⟩ :=
    exists_ne_zero_card_support_le_succ_forall_eval_eq_zero H T h
  refine ⟨f, hf0, hfsupp, hfcard, hfvan, fun hf𝒞 => ?_⟩
  obtain ⟨a, haH, hne⟩ := hH f hf𝒞 hf0
  exact hne (hfvan a haH)

end BoundedSupportInterpolation

section RootToMultiple

/-- Over any commutative integral domain `R`, if `q : Polynomial R` is nonzero and `Q ≠ 0` is a
root of `q`, then some nonzero coefficient `q.coeff a` (`a ≤ q.natDegree`) is divisible by `Q`. -/
theorem exists_coeff_dvd_of_isRoot {R : Type*} [CommRing R] [IsDomain R]
    {Q : R} (hQ0 : Q ≠ 0) {q : Polynomial R} (hq0 : q ≠ 0) (hroot : Polynomial.IsRoot q Q) :
    ∃ a ≤ q.natDegree, q.coeff a ≠ 0 ∧ Q ∣ q.coeff a := by
  classical
  obtain ⟨R_poly, hq_eq⟩ := Polynomial.dvd_iff_isRoot.mpr hroot
  have hR0 : R_poly ≠ 0 := fun h0 => hq0 (by simp [hq_eq, h0])
  have hex : ∃ n : ℕ, R_poly.coeff n ≠ 0 := by
    by_contra! hall
    exact hR0 (by ext n; simp [hall n])
  let a := Nat.find hex
  have ha_ne : R_poly.coeff a ≠ 0 := Nat.find_spec hex
  have ha_eq : q.coeff a = -(Q * R_poly.coeff a) := by
    rw [hq_eq, sub_mul, Polynomial.coeff_sub, Polynomial.coeff_C_mul]
    cases h_a : a with
    | zero => simp
    | succ b =>
      have hb_lt : b < a := by omega
      have hb0 : R_poly.coeff b = 0 := Decidable.byContradiction fun h => Nat.find_min hex hb_lt h
      have hX : (Polynomial.X * R_poly).coeff (b + 1) = R_poly.coeff b := by
        rw [mul_comm, Polynomial.coeff_mul_X]
      rw [hX, hb0, zero_sub]
  have hqa_ne : q.coeff a ≠ 0 := by
    rw [ha_eq, neg_ne_zero]
    exact mul_ne_zero hQ0 ha_ne
  refine ⟨a, Polynomial.le_natDegree_of_ne_zero hqa_ne, hqa_ne, ⟨-R_poly.coeff a, ?_⟩⟩
  rw [ha_eq]; ring

end RootToMultiple

section FactorFreeHybrid

variable {K L : Type*} {m n : ℕ}

private noncomputable def hybridGenInput [CommSemiring K] (Q : MvPolynomial (Fin m) K)
    (S : Fin n → (Fin m ↪ L)) (k : ℕ) (j : Fin n) : MvPolynomial (L ⊕ Fin n) K :=
  if (j : ℕ) < k then rename Sum.inl (nwGenerator Q S j) else X (Sum.inr j)

private noncomputable def hybridPivotVar (S : Fin n → (Fin m ↪ L)) (i : Fin n) :
    L ⊕ Fin n → (L ⊕ Fin n) ⊕ Fin (m + 1)
  | .inl l => Function.extend (S i) (fun k => .inr k.succ) (fun l => .inl (.inl l)) l
  | .inr j => if j = i then .inr 0 else .inl (.inr j)

private theorem injective_hybridPivotVar (S : Fin n → (Fin m ↪ L)) (i : Fin n) :
    Function.Injective (hybridPivotVar S i) := by
  refine Function.LeftInverse.injective
    (g := Sum.elim id (Fin.cases (.inr i) fun k => .inl (S i k))) ?_
  rintro (l | j)
  · rcases Classical.em (∃ k, S i k = l) with ⟨k, rfl⟩ | hl
    · simp [hybridPivotVar, (S i).injective.extend_apply]
    · simp [hybridPivotVar, Function.extend_apply' _ _ _ hl]
  · by_cases hj : j = i <;> simp [hybridPivotVar, hj]

/-- **Factor-free Nisan–Wigderson hybrid multiple theorem**:
over any infinite field `K`, if `Q ≠ 0`, `P ≠ 0` has total degree at most `D`, and `P` vanishes on
`nwGenerator Q S`, then there exist a block index `t : Fin n`, off-block specialization
`ψ_seed : L → MvPolynomial (Fin m) K` (mapping `S t k ↦ X k` and every `l ∉ range (S t)` to a
constant), post-`t` constants `cPost : Fin n → K`, evaluation points `α : Fin (D + 1) → K`, and
Lagrange weights `w : Fin (D + 1) → K` such that the `(D + 1)`-term linear combination of hybrid
evaluations of `P` is nonzero and divisible by `Q`.
-/
theorem exists_multiple_eq_sum_smul_aeval_of_nwGenerator_vanishing [Field K] [Infinite K]
    {Q : MvPolynomial (Fin m) K} (hQ0 : Q ≠ 0) (S : Fin n → (Fin m ↪ L))
    {P : MvPolynomial (Fin n) K} (hP0 : P ≠ 0) {D : ℕ} (hPD : P.totalDegree ≤ D)
    (hvan : aeval (nwGenerator Q S) P = 0) :
    ∃ (t : Fin n) (cSeed : L → K) (cPost : Fin n → K)
      (α : Fin (D + 1) → K) (w : Fin (D + 1) → K),
      let ψ_seed : L → MvPolynomial (Fin m) K :=
        Function.extend (S t) (X : Fin m → MvPolynomial (Fin m) K) (fun l => C (cSeed l))
      let g : Fin (D + 1) → Fin n → MvPolynomial (Fin m) K := fun u j =>
        if (j : ℕ) < (t : ℕ) then aeval ψ_seed (nwGenerator Q S j)
        else if j = t then C (α u)
        else C (cPost j)
      let P_tilde : MvPolynomial (Fin m) K :=
        ∑ u : Fin (D + 1), w u • aeval (g u) P
      P_tilde ≠ 0 ∧ Q ∣ P_tilde := by
  classical
  let H : ℕ → MvPolynomial (L ⊕ Fin n) K := fun k => aeval (hybridGenInput Q S k) P
  have H0 : H 0 ≠ 0 := by
    have h0 : hybridGenInput Q S 0 = X ∘ Sum.inr := funext fun j => by simp [hybridGenInput]
    simpa only [H, h0, ← rename_eq_aeval] using
      (map_ne_zero_iff _ (rename_injective _ Sum.inr_injective)).2 hP0
  have Hn : H n = 0 := by
    have hn : hybridGenInput Q S n = fun j => rename Sum.inl (nwGenerator Q S j) :=
      funext fun j => by simp [hybridGenInput]
    simp only [H, hn, ← comp_aeval_apply, hvan, map_zero]
  obtain ⟨t₀, ht₀, hHt0, hHt1⟩ : ∃ i < n, H i ≠ 0 ∧ H (i + 1) = 0 := by
    by_contra! hall
    exact Nat.rec (motive := fun k => k ≤ n → H k ≠ 0) (fun _ => H0)
      (fun k ih hk => hall k (by omega) (ih (by omega))) n le_rfl Hn
  let t : Fin n := ⟨t₀, ht₀⟩
  obtain ⟨v, hv⟩ := exists_aeval_sumElim_ne_zero
    ((map_ne_zero_iff _ (rename_injective _ (injective_hybridPivotVar S t))).2 hHt0)
  rw [aeval_rename] at hv
  let ψ : L ⊕ Fin n → MvPolynomial (Fin (m + 1)) K :=
    Sum.elim (fun a => C (v a)) (X : Fin (m + 1) → MvPolynomial (Fin (m + 1)) K) ∘
      hybridPivotVar S t
  let P' : MvPolynomial (Fin (m + 1)) K := aeval ψ (H t₀)
  have hP'0 : P' ≠ 0 := hv
  let cSeed : L → K := fun l => v (.inl l)
  let cPost : Fin n → K := fun j => v (.inr j)
  let ψ_seed : L → MvPolynomial (Fin m) K :=
    Function.extend (S t) (X : Fin m → MvPolynomial (Fin m) K) (fun l => C (cSeed l))
  have hψ_inl : ∀ l : L, ψ (.inl l) = rename Fin.succ (ψ_seed l) := by
    intro l
    rcases Classical.em (∃ k, S t k = l) with ⟨k, rfl⟩ | hl
    · simp [ψ, ψ_seed, hybridPivotVar, (S t).injective.extend_apply]
    · simp [ψ, ψ_seed, cSeed, hybridPivotVar, Function.extend_apply' _ _ _ hl]
  have hψ_nw : ∀ j : Fin n,
      aeval ψ (rename Sum.inl (nwGenerator Q S j)) =
        rename Fin.succ (aeval ψ_seed (nwGenerator Q S j)) := by
    intro j
    rw [aeval_rename]
    have hcomp : aeval (ψ ∘ Sum.inl) = (rename Fin.succ).comp (aeval ψ_seed) := by
      apply MvPolynomial.algHom_ext
      intro l
      simp only [aeval_X, AlgHom.comp_apply, Function.comp_apply]
      exact hψ_inl l
    exact DFunLike.congr_fun hcomp (nwGenerator Q S j)
  have hP'_eq : P' = aeval (fun j : Fin n =>
      if (j : ℕ) < (t : ℕ) then rename Fin.succ (aeval ψ_seed (nwGenerator Q S j))
      else if j = t then X 0
      else C (cPost j)) P := by
    dsimp only [P', H]
    rw [comp_aeval_apply]
    congr 2; funext j
    dsimp only [hybridGenInput]
    split_ifs with hlt hjt
    · exact hψ_nw j
    · subst hjt; simp [ψ, hybridPivotVar]
    · simp [ψ, hybridPivotVar, hjt, cPost]
  let q : Polynomial (MvPolynomial (Fin m) K) := finSuccEquiv K m P'
  have hq0 : q ≠ 0 := (map_ne_zero_iff _ (finSuccEquiv K m).injective).2 hP'0
  have hq_deg : q.natDegree ≤ D := by
    let φ0 : MvPolynomial (Fin n) K →ₐ[K] Polynomial (MvPolynomial (Fin m) K) :=
      (finSuccEquiv K m).toAlgHom.comp
        (aeval fun j : Fin n =>
          if (j : ℕ) < (t : ℕ) then rename Fin.succ (aeval ψ_seed (nwGenerator Q S j))
          else if j = t then X 0
          else C (cPost j))
    have hq_φ0 : q = φ0 P := by simp [q, φ0, hP'_eq]
    rw [hq_φ0]
    conv_lhs => rw [P.as_sum, map_sum]
    refine (Polynomial.natDegree_sum_le _ _).trans (Finset.sup_le fun d_exp hd_exp => ?_)
    dsimp only [Function.comp_apply]
    rw [monomial_eq, map_mul]
    have hC0 : φ0 (C (P.coeff d_exp)) = Polynomial.C (C (P.coeff d_exp)) := by
      simp [φ0]
    rw [hC0]
    refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
    rw [Finsupp.prod, map_prod]
    refine (Polynomial.natDegree_prod_le _ _).trans ?_
    have hvar_deg : ∀ j : Fin n, (φ0 (X j)).natDegree ≤ 1 := by
      intro j
      dsimp only [φ0, AlgHom.comp_apply]
      rw [aeval_X, AlgEquiv.coe_toAlgHom]
      split_ifs with hlt hjt
      · rw [natDegree_finSuccEquiv]
        have hnot : (0 : Fin (m + 1)) ∉
            (rename Fin.succ (aeval ψ_seed (nwGenerator Q S j))).vars := by
          intro hmem
          have hsub := vars_rename Fin.succ (aeval ψ_seed (nwGenerator Q S j)) hmem
          rcases Finset.mem_image.mp hsub with ⟨z, _, hz⟩
          exact Fin.succ_ne_zero z hz
        have hzero : (rename Fin.succ (aeval ψ_seed (nwGenerator Q S j))).degreeOf 0 = 0 := by
          by_contra hne
          exact hnot ((mem_vars_iff_degreeOf_ne_zero).mpr hne)
        omega
      · simp [finSuccEquiv_X_zero]
      · rw [natDegree_finSuccEquiv, degreeOf_C]
        omega
    calc
      ∑ j ∈ d_exp.support, (φ0 (X j ^ d_exp j)).natDegree
        ≤ ∑ j ∈ d_exp.support, d_exp j * 1 := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [map_pow]
          exact Polynomial.natDegree_pow_le.trans (Nat.mul_le_mul_left _ (hvar_deg j))
      _ = d_exp.sum (fun _ e => e) := by simp [Finsupp.sum]
      _ ≤ P.totalDegree := le_totalDegree hd_exp
      _ ≤ D := hPD
  have hq_eval : ∀ R₀ : MvPolynomial (Fin m) K,
      Polynomial.eval R₀ q =
        aeval (Fin.cases R₀ (X : Fin m → MvPolynomial (Fin m) K)) P' := by
    intro R₀
    let evHom : Polynomial (MvPolynomial (Fin m) K) →ₐ[K] MvPolynomial (Fin m) K :=
      { toRingHom := Polynomial.evalRingHom R₀
        commutes' r := by simp [Polynomial.algebraMap_apply, algebraMap_eq] }
    have hcomp : evHom.comp (finSuccEquiv K m).toAlgHom =
        aeval (Fin.cases R₀ (X : Fin m → MvPolynomial (Fin m) K)) := by
      apply MvPolynomial.algHom_ext; intro i
      refine Fin.cases ?_ (fun k => ?_) i
      · change Polynomial.eval R₀ ((finSuccEquiv K m) (X 0)) = _
        simp [finSuccEquiv_X_zero]
      · change Polynomial.eval R₀ ((finSuccEquiv K m) (X k.succ)) = _
        simp [finSuccEquiv_X_succ]
    exact DFunLike.congr_fun hcomp P'
  have hq_root : Polynomial.IsRoot q Q := by
    rw [Polynomial.IsRoot.def, hq_eval Q]
    dsimp only [P']
    rw [comp_aeval_apply]
    have hsub_t1 :
        aeval (aeval (Fin.cases Q X) ∘ ψ) (H t₀) =
          aeval (aeval (Fin.cases Q X) ∘ ψ) (H (t₀ + 1)) := by
      dsimp only [H]
      rw [comp_aeval_apply, comp_aeval_apply]
      congr 2; funext j
      by_cases hjt : j = t
      · subst hjt
        have hlt_f : ¬ (t : ℕ) < t₀ := lt_irrefl _
        have hlt_t : (t : ℕ) < t₀ + 1 := Nat.lt_succ_self _
        simp only [hybridGenInput, hlt_f, hlt_t, ↓reduceIte]
        have hleft : aeval (aeval (Fin.cases Q X) ∘ ψ) (X (R := K) (.inr t)) = Q := by
          simp [ψ, hybridPivotVar]
        have hright : aeval (aeval (Fin.cases Q X) ∘ ψ) (rename Sum.inl (nwGenerator Q S t)) =
          Q := by
          dsimp only [Function.comp_def]
          rw [← comp_aeval_apply, hψ_nw t, aeval_rename]
          have hid : Fin.cases Q X ∘ Fin.succ = X := funext fun _ => rfl
          rw [hid, aeval_X_left_apply, nwGenerator_apply, aeval_rename]
          have hself : ψ_seed ∘ S t = X :=
            funext fun k => by simp [ψ_seed, (S t).injective.extend_apply]
          rw [hself, aeval_X_left_apply]
        rw [hleft, hright]
      · have hne : (j : ℕ) ≠ t₀ := fun h => hjt (Fin.ext h)
        simp only [hybridGenInput, show (j : ℕ) < t₀ ↔ (j : ℕ) < t₀ + 1 by omega]
    change aeval (aeval (Fin.cases Q X) ∘ ψ) (H t₀) = 0
    rw [hsub_t1, hHt1, map_zero]
  obtain ⟨a, _, hqa_ne, hQ_dvd⟩ := exists_coeff_dvd_of_isRoot hQ0 hq0 hq_root
  obtain ⟨S_pts, hS_pts⟩ := Infinite.exists_subset_card_eq K (D + 1)
  let α : Fin (D + 1) → K := fun u => ((S_pts.equivFinOfCardEq hS_pts).symm u).1
  have hα_inj : Set.InjOn α (Finset.univ : Finset (Fin (D + 1))) :=
    fun u₁ _ u₂ _ heq => (S_pts.equivFinOfCardEq hS_pts).symm.injective (Subtype.ext heq)
  let w : Fin (D + 1) → K := fun u => (Lagrange.basis Finset.univ α u).coeff a
  have hlagrange := Lagrange.coeff_eq_sum_coeff_basis_smul_eval (R := MvPolynomial (Fin m) K)
    hα_inj (hq := by simpa using Nat.lt_succ_of_le hq_deg) a
  let g : Fin (D + 1) → Fin n → MvPolynomial (Fin m) K := fun u j =>
    if (j : ℕ) < (t : ℕ) then aeval ψ_seed (nwGenerator Q S j)
    else if j = t then C (α u)
    else C (cPost j)
  have heval_u : ∀ u : Fin (D + 1),
      q.eval (algebraMap K (MvPolynomial (Fin m) K) (α u)) = aeval (g u) P := by
    intro u
    rw [algebraMap_eq, hq_eval (C (α u)), hP'_eq, comp_aeval_apply]
    congr 2; funext j
    dsimp only [g]
    split_ifs with hlt hjt
    · rw [aeval_rename]
      have hid : Fin.cases (C (α u)) (X : Fin m → MvPolynomial (Fin m) K) ∘ Fin.succ = X :=
        funext fun _ => rfl
      rw [hid, aeval_X_left_apply]
    · simp
    · simp
  have hP_tilde_eq : (∑ u : Fin (D + 1), w u • aeval (g u) P) = q.coeff a := by
    rw [hlagrange]
    exact Finset.sum_congr rfl fun u _ => by rw [heval_u u]
  refine ⟨t, cSeed, cPost, α, w, ?_, ?_⟩
  · dsimp only; rwa [hP_tilde_eq]
  · dsimp only; rwa [hP_tilde_eq]

end FactorFreeHybrid

end Cslib.Circuits.Arithmetic
