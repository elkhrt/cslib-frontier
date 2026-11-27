module

public import CslibFrontier.Foundations.BooleanAnalysis.SheraliAdams

import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Nat.Choose.Basic

/-!
# Matching Lower Bound for Sherali–Adams Approximate Cauchy–Schwarz

This module constructs symmetric $R$-local Sherali–Adams pseudo-distributions on
$(\mathrm{Fin}\,n \to \mathrm{Bool}) \simeq \{-1, 1\}^n$ establishing that exact Cauchy–Schwarz
and any finite multiplicative approximate Cauchy–Schwarz inequality fail for Sherali–Adams
pseudo-distributions, and that the additive error term in the approximate Cauchy–Schwarz
inequality is asymptotically tight down to the leading constant $1 / \sqrt{R - 1}$ as
$R \to \infty$ and $n / R \to \infty$, under standard Lean axioms.

## Main declarations

- `exists_local_pseudoDist_linearSumPoly_lower_bound_explicit`: for all integers $2 \le R < n$,
  there exists an $R$-local Sherali–Adams pseudo-distribution $D$ on $\mathrm{Fin}\,n \to
  \mathrm{Bool}$ such that $\tilde{\mathbb{E}}_D[p^2] = 0$ and
  $\tilde{\mathbb{E}}_D[p] \ge (1 - 3(1/R + R/n))\,n / \sqrt{R - 1}$ for
  $p(x) = \sum_i \sigma(x_i)$.
- `sa_matching_lower_bound`: asymptotic $1 - O(1/R + R/n)$ matching lower bound for
  $p(x) = \sum_i \sigma(x_i)$ under $R$-local Sherali–Adams pseudo-distributions.
- `sa_approx_cs_tight_sandwich`: simultaneous matching lower and upper bounds
  $(1 - 3(1/R + R/n))\,n / \sqrt{R - 1} \le \tilde{\mathbb{E}}_D[p] \le n / \sqrt{R - 1}$
  with $\tilde{\mathbb{E}}_D[p^2] = 0$.
- `sa_cannot_satisfy_cauchy_schwarz_exactly`: for every $\varepsilon > 0$, for all sufficiently
  large $R$ and $n \gg R$, there exists an $R$-local pseudo-distribution $D$ with
  $\tilde{\mathbb{E}}_D[p^2] = 0$ and
  $\tilde{\mathbb{E}}_D[p] \ge (1 - \varepsilon)\,n / \sqrt{R - 1}$.
- `no_multiplicative_approx_cauchy_schwarz`: no finite multiplicative factor $M$ can bound
  $\tilde{\mathbb{E}}_D[p \cdot 1]$ by
  $M \sqrt{\tilde{\mathbb{E}}_D[p^2]} \sqrt{\tilde{\mathbb{E}}_D[1^2]}$ across $R$-local
  Sherali–Adams pseudo-distributions.
-/

public section
noncomputable section

namespace CslibFrontier.Foundations.BooleanAnalysis

open scoped BigOperators
open Cslib.BitString (signVal signVal_false signVal_true signVal_mul_self)

/-! ### Two-Level Permutation-Invariant Local Distribution on $\mathrm{Fin}\,R \to \mathrm{Bool}$ -/

/-- Number of `false` (`+1` in the $\pm 1$ basis) coordinates of $z : \mathrm{Fin}\,R \to
\mathrm{Bool}$. -/
private def falseCount {R : ℕ} (z : Fin R → Bool) : ℕ :=
  (Finset.univ.filter fun i : Fin R ↦ z i = false).card

private lemma linearSumPoly_eq_two_mul_falseCount_sub {R : ℕ} (z : Fin R → Bool) :
    linearSumPoly R z = 2 * (falseCount z : ℝ) - (R : ℝ) := by
  have hpart := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Fin R))
    (fun i : Fin R ↦ z i = false) (fun i ↦ signVal (z i))
  have hcardR : (falseCount z : ℝ) +
      ((Finset.univ.filter fun i : Fin R ↦ ¬z i = false).card : ℝ) = (R : ℝ) := by
    have h1 := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Fin R))
      (fun i : Fin R ↦ z i = false) (fun _ ↦ (1 : ℝ))
    simpa [falseCount] using h1
  have ht : (∑ i ∈ Finset.univ.filter (fun i : Fin R ↦ z i = false), signVal (z i)) =
      (falseCount z : ℝ) := by
    calc (∑ i ∈ Finset.univ.filter (fun i : Fin R ↦ z i = false), signVal (z i))
      _ = ∑ _ ∈ Finset.univ.filter (fun i : Fin R ↦ z i = false), (1 : ℝ) :=
          Finset.sum_congr rfl fun i hi ↦ by
            rw [(Finset.mem_filter.mp hi).2, signVal_false]
      _ = (falseCount z : ℝ) := by simp [falseCount]
  have hf : (∑ i ∈ Finset.univ.filter (fun i : Fin R ↦ ¬z i = false), signVal (z i)) =
      -((Finset.univ.filter fun i : Fin R ↦ ¬z i = false).card : ℝ) := by
    calc (∑ i ∈ Finset.univ.filter (fun i : Fin R ↦ ¬z i = false), signVal (z i))
      _ = ∑ _ ∈ Finset.univ.filter (fun i : Fin R ↦ ¬z i = false), (-1 : ℝ) :=
          Finset.sum_congr rfl fun i hi ↦ by
            have hzi : z i = true := by
              cases h : z i
              · exact absurd h (Finset.mem_filter.mp hi).2
              · rfl
            rw [hzi, signVal_true]
      _ = -((Finset.univ.filter fun i : Fin R ↦ ¬z i = false).card : ℝ) := by simp
  rw [linearSumPoly_def, ← hpart, ht, hf]
  linarith

private lemma card_filter_falseCount_eq (R u : ℕ) :
    (Finset.univ.filter fun z : Fin R → Bool ↦ falseCount z = u).card = R.choose u := by
  let e : (Fin R → Bool) ≃ Finset (Fin R) :=
    { toFun := fun z ↦ Finset.univ.filter fun i : Fin R ↦ z i = false
      invFun := fun S i ↦ if i ∈ S then false else true
      left_inv := fun z ↦ funext fun i ↦ by cases h : z i <;> simp [h]
      right_inv := fun S ↦ by ext i; by_cases hi : i ∈ S <;> simp [hi] }
  have hbij : (Finset.univ.filter fun z : Fin R → Bool ↦ falseCount z = u).card =
      (Finset.univ.filter fun S : Finset (Fin R) ↦ S.card = u).card :=
    Finset.card_bij (fun z _ ↦ e z)
      (fun z hz ↦ Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hz).2⟩)
      (fun z₁ _ z₂ _ h ↦ e.injective h)
      (fun S hS ↦ ⟨e.symm S, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
        change (e (e.symm S)).card = u
        rw [e.apply_symm_apply]
        exact (Finset.mem_filter.mp hS).2⟩, e.apply_symm_apply S⟩)
  rw [hbij, Finset.univ_filter_card_eq, Finset.card_powersetCard, Finset.card_univ,
    Fintype.card_fin]

private lemma falseCount_comp_equiv {R : ℕ} (e : Fin R ≃ Fin R) (z : Fin R → Bool) :
    falseCount (z ∘ e) = falseCount z :=
  Finset.card_bij (fun i _ ↦ e i)
    (fun i hi ↦ Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2⟩)
    (fun _ _ _ _ h ↦ e.injective h)
    (fun j hj ↦ ⟨e.symm j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
      simp [(Finset.mem_filter.mp hj).2]⟩, e.apply_symm_apply j⟩)

/-- Symmetric probability distribution on $\mathrm{Fin}\,R \to \mathrm{Bool}$ placing total mass
$1 - \theta$ uniformly on Slice $u_1$ and total mass $\theta$ uniformly on Slice $u_2$. -/
private def twoLevelSymDist (R u₁ u₂ : ℕ) (θ : ℝ) (z : Fin R → Bool) : ℝ :=
  (if falseCount z = u₁ then (1 - θ) / (R.choose u₁ : ℝ) else 0) +
    (if falseCount z = u₂ then θ / (R.choose u₂ : ℝ) else 0)

private lemma twoLevelSymDist_nonneg {R u₁ u₂ : ℕ} {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (z : Fin R → Bool) : 0 ≤ twoLevelSymDist R u₁ u₂ θ z := by
  unfold twoLevelSymDist
  refine add_nonneg ?_ ?_
  · split_ifs
    · exact div_nonneg (by linarith) (Nat.cast_nonneg _)
    · exact le_rfl
  · split_ifs
    · exact div_nonneg hθ0 (Nat.cast_nonneg _)
    · exact le_rfl

private lemma twoLevelSymDist_comp_equiv {R u₁ u₂ : ℕ} (θ : ℝ) (e : Fin R ≃ Fin R)
    (z : Fin R → Bool) :
    twoLevelSymDist R u₁ u₂ θ (z ∘ e) = twoLevelSymDist R u₁ u₂ θ z := by
  simp only [twoLevelSymDist, falseCount_comp_equiv]

private lemma sum_slice_weight {R u : ℕ} (hu : u ≤ R) (w : ℝ) (Φ : ℕ → ℝ) :
    (∑ z : Fin R → Bool, (if falseCount z = u then w / (R.choose u : ℝ) else 0) *
      Φ (falseCount z)) = w * Φ u := by
  have hchoose : (R.choose u : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.choose_pos hu).ne'
  have hrew : (∑ z : Fin R → Bool, (if falseCount z = u then w / (R.choose u : ℝ) else 0) *
      Φ (falseCount z)) =
      ∑ z : Fin R → Bool, if falseCount z = u then (w / (R.choose u : ℝ)) * Φ u else 0 :=
    Finset.sum_congr rfl fun z _ ↦ by split_ifs with hz <;> simp [hz]
  rw [hrew, Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
    card_filter_falseCount_eq, nsmul_eq_mul, ← mul_assoc, mul_div_cancel₀ _ hchoose]

private lemma pseudoExpect_twoLevelSymDist_of_falseCount {R u₁ u₂ : ℕ}
    (hu₁ : u₁ ≤ R) (hu₂ : u₂ ≤ R) (θ : ℝ) (Φ : ℕ → ℝ) :
    pseudoExpect (twoLevelSymDist R u₁ u₂ θ) (fun z ↦ Φ (falseCount z)) =
      (1 - θ) * Φ u₁ + θ * Φ u₂ := by
  rw [pseudoExpect_fin_eq R]
  simp only [twoLevelSymDist, add_mul, Finset.sum_add_distrib]
  rw [sum_slice_weight hu₁ (1 - θ) Φ, sum_slice_weight hu₂ θ Φ]

private lemma pseudoExpect_twoLevelSymDist_one {R u₁ u₂ : ℕ}
    (hu₁ : u₁ ≤ R) (hu₂ : u₂ ≤ R) (θ : ℝ) :
    pseudoExpect (twoLevelSymDist R u₁ u₂ θ) (fun _ ↦ 1) = 1 := by
  have h := pseudoExpect_twoLevelSymDist_of_falseCount hu₁ hu₂ θ (fun _ ↦ 1)
  linarith

/-! ### Permutation-Invariant Walsh Moments and Gluing to $\mathrm{Fin}\,n \to \mathrm{Bool}$ -/

private def finsetSumComplEquiv {α : Type*} [Fintype α] [DecidableEq α] (S : Finset α) :
    S ⊕ (Sᶜ : Finset α) ≃ α where
  toFun := Sum.elim Subtype.val Subtype.val
  invFun x := if hx : x ∈ S then Sum.inl ⟨x, hx⟩ else Sum.inr ⟨x, Finset.mem_compl.mpr hx⟩
  left_inv := by
    rintro (⟨x, hx⟩ | ⟨x, hx⟩)
    · simp [hx]
    · simp [Finset.mem_compl.mp hx]
  right_inv x := by by_cases hx : x ∈ S <;> simp [hx]

private lemma exists_perm_map_finset_eq {R : ℕ} {S₁ S₂ : Finset (Fin R)}
    (hcard : S₁.card = S₂.card) :
    ∃ e : Fin R ≃ Fin R, S₁.map e.toEmbedding = S₂ := by
  have hc₁ : Fintype.card S₁ = Fintype.card S₂ := by simp [hcard]
  have hc₂ : Fintype.card (S₁ᶜ : Finset (Fin R)) = Fintype.card (S₂ᶜ : Finset (Fin R)) := by
    simp [hcard]
  let e₁ : S₁ ≃ S₂ := Fintype.equivOfCardEq hc₁
  let e₂ : (S₁ᶜ : Finset (Fin R)) ≃ (S₂ᶜ : Finset (Fin R)) := Fintype.equivOfCardEq hc₂
  let e : Fin R ≃ Fin R :=
    (finsetSumComplEquiv S₁).symm.trans ((Equiv.sumCongr e₁ e₂).trans (finsetSumComplEquiv S₂))
  refine ⟨e, ?_⟩
  ext y
  simp only [Finset.mem_map, Equiv.coe_toEmbedding]
  constructor
  · rintro ⟨x, hx, rfl⟩
    change (finsetSumComplEquiv S₂ (Equiv.sumCongr e₁ e₂
      ((finsetSumComplEquiv S₁).symm x))) ∈ S₂
    have hsymm : (finsetSumComplEquiv S₁).symm x = Sum.inl ⟨x, hx⟩ := by
      simp [finsetSumComplEquiv, hx]
    rw [hsymm]
    exact (e₁ ⟨x, hx⟩).2
  · intro hy
    let x := e₁.symm ⟨y, hy⟩
    refine ⟨x.1, x.2, ?_⟩
    change finsetSumComplEquiv S₂ (Equiv.sumCongr e₁ e₂
      ((finsetSumComplEquiv S₁).symm x.1)) = y
    have hsymm : (finsetSumComplEquiv S₁).symm x.1 = Sum.inl x := by
      simp [finsetSumComplEquiv, x.2]
    rw [hsymm, Equiv.sumCongr_apply, Sum.map_inl, e₁.apply_symm_apply]
    rfl

private lemma pseudoExpect_walshChar_map_perm {R : ℕ} {ν : (Fin R → Bool) → ℝ}
    (hνsym : ∀ (e : Fin R ≃ Fin R) (z : Fin R → Bool), ν (z ∘ e) = ν z)
    (e : Fin R ≃ Fin R) (S : Finset (Fin R)) :
    pseudoExpect ν (Cslib.BitString.chi ℝ (S.map e.toEmbedding)) =
      pseudoExpect ν (Cslib.BitString.chi ℝ S) := by
  let φ : (Fin R → Bool) ≃ (Fin R → Bool) :=
    { toFun := fun z i ↦ z (e i)
      invFun := fun z i ↦ z (e.symm i)
      left_inv := fun z ↦ funext fun i ↦ by simp
      right_inv := fun z ↦ funext fun i ↦ by simp }
  calc pseudoExpect ν (Cslib.BitString.chi ℝ (S.map e.toEmbedding))
    _ = ∑ z : Fin R → Bool, ν (φ z) * Cslib.BitString.chi ℝ S (φ z) := by
        rw [pseudoExpect_fin_eq R]
        refine Finset.sum_congr rfl fun z _ ↦ ?_
        have hφ : φ z = z ∘ e := rfl
        rw [hφ, hνsym e z, Cslib.BitString.chi_eq_prod_signVal, Cslib.BitString.chi_eq_prod_signVal,
          Finset.prod_map]
        rfl
    _ = ∑ w : Fin R → Bool, ν w * Cslib.BitString.chi ℝ S w :=
        φ.sum_comp (fun w ↦ ν w * Cslib.BitString.chi ℝ S w)
    _ = pseudoExpect ν (Cslib.BitString.chi ℝ S) := (pseudoExpect_fin_eq R _ _).symm

private def prefixFinset (R k : ℕ) : Finset (Fin R) :=
  Finset.univ.filter fun i : Fin R ↦ i.1 < k

private lemma card_prefixFinset {R k : ℕ} (hk : k ≤ R) : (prefixFinset R k).card = k := by
  have hbij : (Finset.univ : Finset (Fin k)).card = (prefixFinset R k).card :=
    Finset.card_bij (fun (j : Fin k) _ ↦ (⟨j.1, j.2.trans_le hk⟩ : Fin R))
      (fun j _ ↦ by simp [prefixFinset, j.2])
      (fun j₁ _ j₂ _ h ↦ Fin.ext (Fin.mk.inj h))
      (fun i hi ↦ by
        simp only [prefixFinset, Finset.mem_filter, Finset.mem_univ, true_and] at hi
        exact ⟨⟨i.1, hi⟩, Finset.mem_univ _, rfl⟩)
  simpa using hbij.symm

private lemma prefixFinset_zero (R : ℕ) : prefixFinset R 0 = ∅ := by
  ext i; simp [prefixFinset]

/-- Canonical degree-$k$ Walsh moment of a symmetric distribution $\nu$ on
$\mathrm{Fin}\,R \to \mathrm{Bool}$. -/
private def symMoment {R : ℕ} (ν : (Fin R → Bool) → ℝ) (k : ℕ) : ℝ :=
  if k ≤ R then pseudoExpect ν (Cslib.BitString.chi ℝ (prefixFinset R k)) else 0

private lemma symMoment_zero {R : ℕ} {ν : (Fin R → Bool) → ℝ}
    (hν1 : pseudoExpect ν (fun _ ↦ 1) = 1) : symMoment ν 0 = 1 := by
  simp only [symMoment, Nat.zero_le, ↓reduceIte, prefixFinset_zero]
  rwa [show Cslib.BitString.chi ℝ (∅ : Finset (Fin R)) = fun _ ↦ 1 from
    funext Cslib.BitString.chi_empty]

private lemma pseudoExpect_walshChar_eq_symMoment {R : ℕ} {ν : (Fin R → Bool) → ℝ}
    (hνsym : ∀ (e : Fin R ≃ Fin R) (z : Fin R → Bool), ν (z ∘ e) = ν z)
    (S : Finset (Fin R)) :
    pseudoExpect ν (Cslib.BitString.chi ℝ S) = symMoment ν S.card := by
  have hSR : S.card ≤ R := by simpa using S.card_le_univ
  obtain ⟨e, he⟩ := exists_perm_map_finset_eq (card_prefixFinset hSR).symm
  simp only [symMoment, hSR, ↓reduceIte]
  rw [← he, pseudoExpect_walshChar_map_perm hνsym]

private lemma isLocalPseudoDist_glued_symMoment {n R : ℕ} (hRn : R ≤ n)
    {ν : (Fin R → Bool) → ℝ} (hν0 : ∀ z, 0 ≤ ν z) (hν1 : pseudoExpect ν (fun _ ↦ 1) = 1)
    (hνsym : ∀ (e : Fin R ≃ Fin R) (z : Fin R → Bool), ν (z ∘ e) = ν z) :
    IsLocalPseudoDist R (pseudoDistOfMoments (fun S : Finset (Fin n) ↦ symMoment ν S.card)) := by
  refine isLocalPseudoDist_pseudoDistOfMoments_of_local_marginals R _ ?_ ?_
  · simpa using symMoment_zero hν1
  · intro J hJ
    obtain ⟨T, hJT, hTR⟩ := Finset.exists_superset_card_eq hJ (by simpa using hRn)
    let eT : T ≃ Fin R := Fintype.equivFinOfCardEq (by simpa using hTR)
    let ιJT : J ↪ Fin R :=
      ⟨fun j ↦ eT ⟨j.1, hJT j.2⟩, fun j₁ j₂ h ↦ Subtype.ext (Subtype.mk.inj (eT.injective h))⟩
    let g : (Fin R → Bool) → (J → Bool) := fun z j ↦ z (ιJT j)
    let μ : (J → Bool) → ℝ := pushforwardPseudoDist g ν
    refine ⟨μ, ?_, ?_, ?_⟩
    · intro y
      dsimp only [μ]
      rw [pushforwardPseudoDist_def]
      exact Finset.sum_nonneg fun z _ ↦ by
        classical
        split_ifs
        · exact hν0 z
        · exact le_rfl
    · have h1 : pseudoExpect μ (fun _ ↦ 1) = 1 := by
        rw [pseudoExpect_pushforwardPseudoDist]
        exact hν1
      rwa [pseudoExpect_const, mul_one] at h1
    · intro S
      rw [pseudoExpect_pushforwardPseudoDist]
      have hchar : (fun z : Fin R → Bool ↦ Cslib.BitString.chi ℝ S (g z)) =
          Cslib.BitString.chi ℝ (S.map ιJT) := funext fun z ↦ by
        simp [Cslib.BitString.chi_eq_prod_signVal, g]
      rw [hchar, pseudoExpect_walshChar_eq_symMoment hνsym, Finset.card_map, Finset.card_map]

/-! ### First and Second Moments of `linearSumPoly` under Uniformly Degree-Symmetric Weights -/

private lemma pseudoExpect_linearSumPoly_of_uniform_deg_one {m : ℕ} {μ : (Fin m → Bool) → ℝ}
    {c₁ : ℝ} (h1 : ∀ i : Fin m, pseudoExpect μ (Cslib.BitString.chi ℝ {i}) = c₁) :
    pseudoExpect μ (linearSumPoly m) = (m : ℝ) * c₁ := by
  have hlin : linearSumPoly m = fun x ↦ ∑ i : Fin m, Cslib.BitString.chi ℝ {i} x :=
    funext fun x ↦ by
      rw [linearSumPoly_def]
      exact Finset.sum_congr rfl fun i _ ↦ (Cslib.BitString.chi_singleton i x).symm
  rw [hlin, pseudoExpect_sum]
  simp_rw [h1]
  simp

private lemma pseudoExpect_linearSumPoly_sq_of_uniform_deg_two {m : ℕ} {μ : (Fin m → Bool) → ℝ}
    {c₂ : ℝ} (h0 : pseudoExpect μ (fun _ ↦ 1) = 1)
    (h2 : ∀ i j : Fin m, i ≠ j → pseudoExpect μ (Cslib.BitString.chi ℝ {i, j}) = c₂) :
    pseudoExpect μ (fun x ↦ linearSumPoly m x ^ 2) = (m : ℝ) + (m : ℝ) * ((m : ℝ) - 1) * c₂ := by
  have hsq : (fun x : Fin m → Bool ↦ linearSumPoly m x ^ 2) = fun x ↦
      ∑ i : Fin m, ((1 : ℝ) +
        ∑ j ∈ Finset.univ.erase i, Cslib.BitString.chi ℝ {i, j} x) := by
    funext x
    rw [linearSumPoly_def, sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), signVal_mul_self]
    congr 1
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    have hij : i ≠ j := (Finset.ne_of_mem_erase hj).symm
    exact ((Cslib.BitString.chi_eq_prod_signVal {i, j} x).trans (Finset.prod_pair hij)).symm
  rw [hsq, pseudoExpect_sum]
  have hterm : ∀ i : Fin m,
      pseudoExpect μ (fun x ↦ (1 : ℝ) +
        ∑ j ∈ Finset.univ.erase i, Cslib.BitString.chi ℝ {i, j} x) =
      1 + ((m : ℝ) - 1) * c₂ := fun i ↦ by
    have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr fun h0m ↦ Fin.elim0 (h0m ▸ i)
    rw [pseudoExpect_add, h0, pseudoExpect_sum]
    have hinner : (∑ j ∈ Finset.univ.erase i,
        pseudoExpect μ (Cslib.BitString.chi ℝ {i, j})) = ((m : ℝ) - 1) * c₂ := by
      calc (∑ j ∈ Finset.univ.erase i, pseudoExpect μ (Cslib.BitString.chi ℝ {i, j}))
        _ = ∑ _ ∈ Finset.univ.erase i, c₂ :=
            Finset.sum_congr rfl fun j hj ↦ h2 i j (Finset.ne_of_mem_erase hj).symm
        _ = ((Finset.univ.erase i).card : ℝ) * c₂ := by simp
        _ = ((m : ℝ) - 1) * c₂ := by
            rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin,
              Nat.cast_sub hm1, Nat.cast_one]
    rw [hinner]
  simp_rw [hterm]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-! ### Parity Grid Selection and Quantitative Algebraic Bounds -/

private lemma targetSecondMoment_bounds {n R : ℕ} (hR : 2 ≤ R) (hRn : R < n) :
    1 ≤ (R : ℝ) * ((n : ℝ) - (R : ℝ)) / ((n : ℝ) - 1) ∧
      (R : ℝ) * ((n : ℝ) - (R : ℝ)) / ((n : ℝ) - 1) < (R : ℝ) := by
  have hR1 : (2 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
  have hRn1 : (R : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hRn
  have hn_pos : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  constructor
  · rw [le_div_iff₀ hn_pos]
    nlinarith
  · rw [div_lt_iff₀ hn_pos]
    nlinarith

private lemma exists_parity_grid_bracket {R : ℕ} {A : ℝ} (hR : 2 ≤ R)
    (hA1 : 1 ≤ A) (hAR : A < (R : ℝ)) :
    ∃ a u₁ : ℕ, a + 2 ≤ R ∧ 2 * u₁ = R + a ∧
      (a : ℝ) ≤ Real.sqrt A ∧ Real.sqrt A < (a : ℝ) + 2 := by
  have hR_one : (1 : ℝ) ≤ (R : ℝ) := by
    have : (2 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
    linarith
  have hsqrt_ge_one : 1 ≤ Real.sqrt A := by
    simpa using Real.sqrt_le_sqrt hA1
  have hsqrt_lt_R : Real.sqrt A < (R : ℝ) := by
    have hsqR : (R : ℝ) ≤ (R : ℝ) ^ 2 := by nlinarith
    have hlt_sq : A < (R : ℝ) ^ 2 := hAR.trans_le hsqR
    exact (Real.sqrt_lt_sqrt (by linarith) hlt_sq).trans_eq (Real.sqrt_sq (by linarith))
  rcases Nat.even_or_odd R with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · have hdiv_nonneg : 0 ≤ Real.sqrt A / 2 := by positivity
    have hdiv_lt : Real.sqrt A / 2 < (m : ℝ) := by
      have hmR : ((m + m : ℕ) : ℝ) = 2 * (m : ℝ) := by push_cast; ring
      linarith
    let k := ⌊Real.sqrt A / 2⌋₊
    have hk_lt : k < m := (Nat.floor_lt hdiv_nonneg).mpr hdiv_lt
    have hk_le : (k : ℝ) ≤ Real.sqrt A / 2 := Nat.floor_le hdiv_nonneg
    have hlt_k1 : Real.sqrt A / 2 < (k : ℝ) + 1 := Nat.lt_floor_add_one (Real.sqrt A / 2)
    refine ⟨2 * k, m + k, by omega, by omega, ?_, ?_⟩
    · push_cast; linarith
    · push_cast; linarith
  · have hdiv_nonneg : 0 ≤ (Real.sqrt A - 1) / 2 := by linarith
    have hdiv_lt : (Real.sqrt A - 1) / 2 < (m : ℝ) := by
      have hmR : ((2 * m + 1 : ℕ) : ℝ) = 2 * (m : ℝ) + 1 := by push_cast; ring
      linarith
    let k := ⌊(Real.sqrt A - 1) / 2⌋₊
    have hk_lt : k < m := (Nat.floor_lt hdiv_nonneg).mpr hdiv_lt
    have hk_le : (k : ℝ) ≤ (Real.sqrt A - 1) / 2 := Nat.floor_le hdiv_nonneg
    have hlt_k1 : (Real.sqrt A - 1) / 2 < (k : ℝ) + 1 :=
      Nat.lt_floor_add_one ((Real.sqrt A - 1) / 2)
    refine ⟨2 * k + 1, m + k + 1, by omega, by omega, ?_, ?_⟩
    · push_cast; linarith
    · push_cast; linarith

private lemma first_moment_quantitative_lower_bound {n R a : ℕ} {A θ : ℝ}
    (hR : 2 ≤ R) (hRn : R < n)
    (hAdef : A = (R : ℝ) * ((n : ℝ) - (R : ℝ)) / ((n : ℝ) - 1))
    (ha_le : (a : ℝ) ≤ Real.sqrt A) (hsqrt_lt : Real.sqrt A < (a : ℝ) + 2)
    (hθdef : θ = (A - (a : ℝ) ^ 2) / (4 * ((a : ℝ) + 1))) :
    (1 - 3 * (1 / (R : ℝ) + (R : ℝ) / (n : ℝ))) * ((n : ℝ) / Real.sqrt ((R : ℝ) - 1)) ≤
      (n : ℝ) * ((a : ℝ) + 2 * θ) / (R : ℝ) := by
  have hR2 : (2 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
  have hRn1 : (R : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hRn
  have hR_pos : (0 : ℝ) < (R : ℝ) := by linarith
  have hn_pos : (0 : ℝ) < (n : ℝ) := by linarith
  have hn1_pos : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hR1_pos : (0 : ℝ) < (R : ℝ) - 1 := by linarith
  have hsqrtR1_pos : 0 < Real.sqrt ((R : ℝ) - 1) := Real.sqrt_pos.mpr hR1_pos
  have ha0 : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg a
  have hA_ge_sq : (a : ℝ) ^ 2 ≤ A := by
    have hA_nonneg : 0 ≤ A := by
      rw [hAdef]
      exact div_nonneg (mul_nonneg hR_pos.le (by linarith)) hn1_pos.le
    calc (a : ℝ) ^ 2 ≤ Real.sqrt A ^ 2 := sq_le_sq' (by linarith [Real.sqrt_nonneg A]) ha_le
      _ = A := Real.sq_sqrt hA_nonneg
  have hθ_nonneg : 0 ≤ θ := by
    rw [hθdef]
    exact div_nonneg (by linarith) (by linarith)
  by_cases hn2R : n ≤ 2 * R
  · have hn2R' : (n : ℝ) ≤ 2 * (R : ℝ) := by exact_mod_cast hn2R
    have hRn_half : (1 : ℝ) / 2 ≤ (R : ℝ) / (n : ℝ) := by
      rw [div_le_div_iff₀ (by norm_num) hn_pos]
      linarith
    have h1R_pos : 0 < 1 / (R : ℝ) := by positivity
    have hfactor_neg : 1 - 3 * (1 / (R : ℝ) + (R : ℝ) / (n : ℝ)) ≤ 0 := by linarith
    have hlhs_nonpos :
        (1 - 3 * (1 / (R : ℝ) + (R : ℝ) / (n : ℝ))) *
          ((n : ℝ) / Real.sqrt ((R : ℝ) - 1)) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hfactor_neg (div_nonneg hn_pos.le hsqrtR1_pos.le)
    have hrhs_nonneg : 0 ≤ (n : ℝ) * ((a : ℝ) + 2 * θ) / (R : ℝ) :=
      div_nonneg (mul_nonneg hn_pos.le (by linarith)) hR_pos.le
    exact hlhs_nonpos.trans hrhs_nonneg
  · push Not at hn2R
    have hn2R' : 2 * (R : ℝ) < (n : ℝ) := by exact_mod_cast hn2R
    have hA_gt_halfR : (R : ℝ) / 2 < A := by
      rw [hAdef, div_lt_div_iff₀ (by norm_num) hn1_pos]
      nlinarith
    have hA_pos : 0 < A := by linarith
    have hsqrtA_pos : 0 < Real.sqrt A := Real.sqrt_pos.mpr hA_pos
    have hsqA : Real.sqrt A ^ 2 = A := Real.sq_sqrt hA_pos.le
    -- Step 1: `√A * (1 - 2 / R) ≤ a + 2 * θ` via AM-GM on `(√A - a)` and `(a + 2 - √A)`.
    have ha2θ_ge : Real.sqrt A * (1 - 2 / (R : ℝ)) ≤ (a : ℝ) + 2 * θ := by
      have ha1_ne : (2 : ℝ) * ((a : ℝ) + 1) ≠ 0 := by linarith
      have hθ_sq : θ = (Real.sqrt A ^ 2 - (a : ℝ) ^ 2) / (4 * ((a : ℝ) + 1)) := by
        rw [hsqA]; exact hθdef
      have hdiff_id : Real.sqrt A - ((a : ℝ) + 2 * θ) =
          (Real.sqrt A - (a : ℝ)) * ((a : ℝ) + 2 - Real.sqrt A) / (2 * ((a : ℝ) + 1)) := by
        rw [hθ_sq]
        field_simp [ha1_ne]
        ring
      have hprod_le_one : (Real.sqrt A - (a : ℝ)) * ((a : ℝ) + 2 - Real.sqrt A) ≤ 1 := by
        nlinarith [sq_nonneg (Real.sqrt A - (a : ℝ) - 1)]
      have hprod_nonneg : 0 ≤ (Real.sqrt A - (a : ℝ)) * ((a : ℝ) + 2 - Real.sqrt A) :=
        mul_nonneg (by linarith) (by linarith)
      have hdiff_le : Real.sqrt A - ((a : ℝ) + 2 * θ) ≤ 1 / Real.sqrt A := by
        rw [hdiff_id, div_le_div_iff₀ (by linarith) hsqrtA_pos]
        have h2a_ge : Real.sqrt A ≤ 2 * ((a : ℝ) + 1) := by linarith
        nlinarith
      have h1_div_sqrt : 1 / Real.sqrt A = Real.sqrt A * (1 / A) := by
        have hA_ne : A ≠ 0 := hA_pos.ne'
        have hsqrtA_ne : Real.sqrt A ≠ 0 := hsqrtA_pos.ne'
        field_simp [hA_ne, hsqrtA_ne]
        exact hsqA.symm
      have h1A_le_2R : 1 / A ≤ 2 / (R : ℝ) := by
        rw [div_le_div_iff₀ hA_pos hR_pos]
        linarith
      have hstep : Real.sqrt A * (1 - 1 / A) ≤ (a : ℝ) + 2 * θ := by
        linarith [hdiff_le, h1_div_sqrt]
      have hmono : Real.sqrt A * (1 - 2 / (R : ℝ)) ≤ Real.sqrt A * (1 - 1 / A) :=
        mul_le_mul_of_nonneg_left (by linarith) hsqrtA_pos.le
      exact hmono.trans hstep
    -- Step 2: `R / √(R - 1) * (1 - 1 / R) * (1 - R / n) ≤ √A`.
    have hsqrtA_lower :
        (R : ℝ) / Real.sqrt ((R : ℝ) - 1) * (1 - 1 / (R : ℝ)) * (1 - (R : ℝ) / (n : ℝ)) ≤
          Real.sqrt A := by
      refine Real.le_sqrt_of_sq_le ?_
      have hu0 : 0 ≤ 1 - 1 / (R : ℝ) := by
        rw [sub_nonneg, div_le_one hR_pos]; linarith
      have hu1 : 1 - 1 / (R : ℝ) ≤ 1 := by
        have : 0 ≤ 1 / (R : ℝ) := by positivity
        linarith
      have hv0 : 0 ≤ 1 - (R : ℝ) / (n : ℝ) := by
        rw [sub_nonneg, div_le_one hn_pos]; linarith
      have hv1 : 1 - (R : ℝ) / (n : ℝ) ≤ 1 := by
        have : 0 ≤ (R : ℝ) / (n : ℝ) := by positivity
        linarith
      have hu_sq : (1 - 1 / (R : ℝ)) ^ 2 ≤ ((R : ℝ) - 1) / (R : ℝ) := by
        have h1 : (1 - 1 / (R : ℝ)) ^ 2 ≤ 1 - 1 / (R : ℝ) := by nlinarith
        have h2 : 1 - 1 / (R : ℝ) = ((R : ℝ) - 1) / (R : ℝ) := by
          field_simp [hR_pos.ne']
        linarith
      have hv_sq : (1 - (R : ℝ) / (n : ℝ)) ^ 2 ≤ ((n : ℝ) - (R : ℝ)) / ((n : ℝ) - 1) := by
        have h1 : (1 - (R : ℝ) / (n : ℝ)) ^ 2 ≤ 1 - (R : ℝ) / (n : ℝ) := by nlinarith
        have h2 : 1 - (R : ℝ) / (n : ℝ) = ((n : ℝ) - (R : ℝ)) / (n : ℝ) := by
          field_simp [hn_pos.ne']
        have h3 : ((n : ℝ) - (R : ℝ)) / (n : ℝ) ≤ ((n : ℝ) - (R : ℝ)) / ((n : ℝ) - 1) := by
          rw [div_le_div_iff₀ hn_pos hn1_pos]
          nlinarith
        linarith
      have hprod_sq : (1 - 1 / (R : ℝ)) ^ 2 * (1 - (R : ℝ) / (n : ℝ)) ^ 2 ≤
          (((R : ℝ) - 1) / (R : ℝ)) * (((n : ℝ) - (R : ℝ)) / ((n : ℝ) - 1)) :=
        mul_le_mul hu_sq hv_sq (sq_nonneg _) (div_nonneg hR1_pos.le hR_pos.le)
      have hlhs_sq :
          ((R : ℝ) / Real.sqrt ((R : ℝ) - 1) * (1 - 1 / (R : ℝ)) *
            (1 - (R : ℝ) / (n : ℝ))) ^ 2 =
          ((R : ℝ) ^ 2 / ((R : ℝ) - 1)) *
            ((1 - 1 / (R : ℝ)) ^ 2 * (1 - (R : ℝ) / (n : ℝ)) ^ 2) := by
        rw [mul_pow, mul_pow, div_pow, Real.sq_sqrt hR1_pos.le]
        ring
      have hrhs_eq :
          ((R : ℝ) ^ 2 / ((R : ℝ) - 1)) *
            ((((R : ℝ) - 1) / (R : ℝ)) * (((n : ℝ) - (R : ℝ)) / ((n : ℝ) - 1))) = A := by
        rw [hAdef]
        field_simp [hR_pos.ne', hR1_pos.ne', hn1_pos.ne']
      rw [hlhs_sq, ← hrhs_eq]
      exact mul_le_mul_of_nonneg_left hprod_sq (div_nonneg (sq_nonneg _) hR1_pos.le)
    -- Step 3: Combine the three multiplicative factors `(1 - u)(1 - v)(1 - w) ≥ 1 - u - v - w`.
    have hw0 : 0 ≤ 1 - 2 / (R : ℝ) := by
      rw [sub_nonneg, div_le_one hR_pos]; linarith
    have hthree :
        1 - 3 * (1 / (R : ℝ) + (R : ℝ) / (n : ℝ)) ≤
          (1 - 1 / (R : ℝ)) * (1 - (R : ℝ) / (n : ℝ)) * (1 - 2 / (R : ℝ)) := by
      let u : ℝ := 1 / (R : ℝ)
      let v : ℝ := (R : ℝ) / (n : ℝ)
      let w : ℝ := 2 / (R : ℝ)
      have hu_pos : 0 ≤ u := by positivity
      have hv_pos : 0 ≤ v := by positivity
      have hw_pos : 0 ≤ w := by positivity
      have hw_le1 : 0 ≤ 1 - w := hw0
      have hid : (1 - u) * (1 - v) * (1 - w) - (1 - u - v - w) =
          u * v * (1 - w) + (u + v) * w := by ring
      have hge0 : 0 ≤ u * v * (1 - w) + (u + v) * w :=
        add_nonneg (mul_nonneg (mul_nonneg hu_pos hv_pos) hw_le1)
          (mul_nonneg (add_nonneg hu_pos hv_pos) hw_pos)
      have huw : u + w = 3 * u := by simp [u, w]; ring
      linarith
    have ha2θ_final :
        (R : ℝ) / Real.sqrt ((R : ℝ) - 1) *
          (1 - 3 * (1 / (R : ℝ) + (R : ℝ) / (n : ℝ))) ≤ (a : ℝ) + 2 * θ := by
      calc (R : ℝ) / Real.sqrt ((R : ℝ) - 1) *
            (1 - 3 * (1 / (R : ℝ) + (R : ℝ) / (n : ℝ)))
        _ ≤ (R : ℝ) / Real.sqrt ((R : ℝ) - 1) *
              ((1 - 1 / (R : ℝ)) * (1 - (R : ℝ) / (n : ℝ)) * (1 - 2 / (R : ℝ))) :=
            mul_le_mul_of_nonneg_left hthree (div_nonneg hR_pos.le hsqrtR1_pos.le)
        _ = ((R : ℝ) / Real.sqrt ((R : ℝ) - 1) * (1 - 1 / (R : ℝ)) *
              (1 - (R : ℝ) / (n : ℝ))) * (1 - 2 / (R : ℝ)) := by ring
        _ ≤ Real.sqrt A * (1 - 2 / (R : ℝ)) :=
            mul_le_mul_of_nonneg_right hsqrtA_lower hw0
        _ ≤ (a : ℝ) + 2 * θ := ha2θ_ge
    have hmul := mul_le_mul_of_nonneg_left ha2θ_final (div_nonneg hn_pos.le hR_pos.le)
    have hlhs_simp :
        ((n : ℝ) / (R : ℝ)) *
          ((R : ℝ) / Real.sqrt ((R : ℝ) - 1) *
            (1 - 3 * (1 / (R : ℝ) + (R : ℝ) / (n : ℝ)))) =
        (1 - 3 * (1 / (R : ℝ) + (R : ℝ) / (n : ℝ))) *
          ((n : ℝ) / Real.sqrt ((R : ℝ) - 1)) := by
      field_simp [hR_pos.ne', hsqrtR1_pos.ne']
    have hrhs_simp :
        ((n : ℝ) / (R : ℝ)) * ((a : ℝ) + 2 * θ) =
          (n : ℝ) * ((a : ℝ) + 2 * θ) / (R : ℝ) := by ring
    linarith

/-! ### Main Lower Bound Theorems -/

/-- Explicit quantitative matching lower bound for Sherali–Adams pseudo-distributions: for all
integers $2 \le R < n$, there exists an $R$-local Sherali–Adams pseudo-distribution $D$ on
$\mathrm{Fin}\,n \to \mathrm{Bool}$ such that $\tilde{\mathbb{E}}_D[p^2] = 0$ and
$\tilde{\mathbb{E}}_D[p] \ge (1 - 3(1/R + R/n))\,n / \sqrt{R - 1}$ for
$p(x) = \sum_{i=0}^{n-1} \sigma(x_i)$. -/
theorem exists_local_pseudoDist_linearSumPoly_lower_bound_explicit {n R : ℕ}
    (hR : 2 ≤ R) (hRn : R < n) :
    ∃ D : (Fin n → Bool) → ℝ, IsLocalPseudoDist R D ∧
      pseudoExpect D (fun x ↦ linearSumPoly n x ^ 2) = 0 ∧
      (1 - 3 * (1 / (R : ℝ) + (R : ℝ) / (n : ℝ))) *
        ((n : ℝ) / Real.sqrt ((R : ℝ) - 1)) ≤ pseudoExpect D (linearSumPoly n) := by
  let A : ℝ := (R : ℝ) * ((n : ℝ) - (R : ℝ)) / ((n : ℝ) - 1)
  obtain ⟨hA1, hAR⟩ := targetSecondMoment_bounds hR hRn
  obtain ⟨a, u₁, haR, hu₁_eq, ha_le, hsqrt_lt⟩ := exists_parity_grid_bracket hR hA1 hAR
  let u₂ : ℕ := u₁ + 1
  have hu₁R : u₁ ≤ R := by omega
  have hu₂R : u₂ ≤ R := by omega
  let θ : ℝ := (A - (a : ℝ) ^ 2) / (4 * ((a : ℝ) + 1))
  have ha0 : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg a
  have hA_ge_sq : (a : ℝ) ^ 2 ≤ A := by
    calc (a : ℝ) ^ 2 ≤ Real.sqrt A ^ 2 := sq_le_sq' (by linarith [Real.sqrt_nonneg A]) ha_le
      _ = A := Real.sq_sqrt (by linarith)
  have hA_lt_sq2 : A < ((a : ℝ) + 2) ^ 2 := by
    calc A = Real.sqrt A ^ 2 := (Real.sq_sqrt (by linarith)).symm
      _ < ((a : ℝ) + 2) ^ 2 := sq_lt_sq' (by linarith [Real.sqrt_nonneg A]) hsqrt_lt
  have hθ0 : 0 ≤ θ := div_nonneg (by linarith) (by linarith)
  have hθ1 : θ ≤ 1 := by
    rw [div_le_one (by linarith : (0 : ℝ) < 4 * ((a : ℝ) + 1))]
    linarith [show ((a : ℝ) + 2) ^ 2 = (a : ℝ) ^ 2 + 4 * ((a : ℝ) + 1) by ring]
  let ν : (Fin R → Bool) → ℝ := twoLevelSymDist R u₁ u₂ θ
  have hν0 : ∀ z, 0 ≤ ν z := twoLevelSymDist_nonneg hθ0 hθ1
  have hν1 : pseudoExpect ν (fun _ ↦ 1) = 1 := pseudoExpect_twoLevelSymDist_one hu₁R hu₂R θ
  have hνsym : ∀ (e : Fin R ≃ Fin R) (z : Fin R → Bool), ν (z ∘ e) = ν z :=
    twoLevelSymDist_comp_equiv θ
  let D : (Fin n → Bool) → ℝ := pseudoDistOfMoments (fun S : Finset (Fin n) ↦ symMoment ν S.card)
  have hDloc : IsLocalPseudoDist R D :=
    isLocalPseudoDist_glued_symMoment hRn.le hν0 hν1 hνsym
  have hu₁_val : 2 * (u₁ : ℝ) - (R : ℝ) = (a : ℝ) := by
    have hcast : 2 * (u₁ : ℝ) = (R : ℝ) + (a : ℝ) := by exact_mod_cast hu₁_eq
    linarith
  have hu₂_val : 2 * (u₂ : ℝ) - (R : ℝ) = (a : ℝ) + 2 := by
    have hcast : (u₂ : ℝ) = (u₁ : ℝ) + 1 := by exact_mod_cast rfl
    linarith
  have hν_lin : pseudoExpect ν (linearSumPoly R) = (a : ℝ) + 2 * θ := by
    rw [show linearSumPoly R = fun z ↦ 2 * (falseCount z : ℝ) - (R : ℝ) from
      funext linearSumPoly_eq_two_mul_falseCount_sub]
    rw [pseudoExpect_twoLevelSymDist_of_falseCount hu₁R hu₂R θ
      (fun u ↦ 2 * (u : ℝ) - (R : ℝ)), hu₁_val, hu₂_val]
    ring
  have hν_sq : pseudoExpect ν (fun z ↦ linearSumPoly R z ^ 2) = A := by
    have hfun : (fun z : Fin R → Bool ↦ linearSumPoly R z ^ 2) =
        fun z ↦ (2 * (falseCount z : ℝ) - (R : ℝ)) ^ 2 :=
      funext fun z ↦ by rw [linearSumPoly_eq_two_mul_falseCount_sub]
    rw [hfun, pseudoExpect_twoLevelSymDist_of_falseCount hu₁R hu₂R θ
      (fun u ↦ (2 * (u : ℝ) - (R : ℝ)) ^ 2), hu₁_val, hu₂_val]
    have ha1_ne : (4 : ℝ) * ((a : ℝ) + 1) ≠ 0 := by linarith
    dsimp only [θ]
    field_simp [ha1_ne]
    ring
  have hR_pos : (0 : ℝ) < (R : ℝ) := by
    have : (2 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
    linarith
  have hR1_pos : (0 : ℝ) < (R : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
    linarith
  have hn1_pos : (0 : ℝ) < (n : ℝ) - 1 := by
    have : (R : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hRn
    linarith
  have hsym1 : symMoment ν 1 = ((a : ℝ) + 2 * θ) / (R : ℝ) := by
    have h1 := pseudoExpect_linearSumPoly_of_uniform_deg_one (μ := ν) (c₁ := symMoment ν 1)
      fun i ↦ by simpa using pseudoExpect_walshChar_eq_symMoment hνsym {i}
    rw [hν_lin] at h1
    rw [eq_div_iff hR_pos.ne']
    linarith
  have hsym2 : symMoment ν 2 = -1 / ((n : ℝ) - 1) := by
    have h2 := pseudoExpect_linearSumPoly_sq_of_uniform_deg_two (μ := ν) (c₂ := symMoment ν 2)
      hν1 fun i j hij ↦ by
        simpa [Finset.card_pair hij] using pseudoExpect_walshChar_eq_symMoment hνsym {i, j}
    rw [hν_sq] at h2
    have hprod_ne : (R : ℝ) * ((R : ℝ) - 1) ≠ 0 := mul_ne_zero hR_pos.ne' hR1_pos.ne'
    have hsol : symMoment ν 2 = (A - (R : ℝ)) / ((R : ℝ) * ((R : ℝ) - 1)) := by
      rw [eq_div_iff hprod_ne]
      linarith
    rw [hsol]
    dsimp only [A]
    field_simp [hR_pos.ne', hR1_pos.ne', hn1_pos.ne']
    ring
  have hD_lin : pseudoExpect D (linearSumPoly n) = (n : ℝ) * ((a : ℝ) + 2 * θ) / (R : ℝ) := by
    have h1 := pseudoExpect_linearSumPoly_of_uniform_deg_one (μ := D) (c₁ := symMoment ν 1)
      fun i ↦ by simp [D]
    rw [h1, hsym1, mul_div_assoc]
  have hD_sq : pseudoExpect D (fun x ↦ linearSumPoly n x ^ 2) = 0 := by
    have h2 := pseudoExpect_linearSumPoly_sq_of_uniform_deg_two (μ := D) (c₂ := symMoment ν 2)
      hDloc.pseudoExpect_one fun i j hij ↦ by simp [D, Finset.card_pair hij]
    rw [h2, hsym2]
    field_simp [hn1_pos.ne']
    ring
  refine ⟨D, hDloc, hD_sq, ?_⟩
  rw [hD_lin]
  exact first_moment_quantitative_lower_bound hR hRn rfl ha_le hsqrt_lt rfl

/-- Asymptotic $1 - O(1/R + R/n)$ matching lower bound for Sherali–Adams pseudo-distributions:
there exists an absolute constant $C > 0$ such that for all integers $2 \le R < n$, some
$R$-local Sherali–Adams pseudo-distribution $D$ on $\mathrm{Fin}\,n \to \mathrm{Bool}$ satisfies
$\tilde{\mathbb{E}}_D[p^2] = 0$ and
$\tilde{\mathbb{E}}_D[p] \ge (1 - C(1/R + R/n))\,n / \sqrt{R - 1}$. -/
theorem sa_matching_lower_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ ⦃n R : ℕ⦄, 2 ≤ R → R < n →
      ∃ D : (Fin n → Bool) → ℝ, IsLocalPseudoDist R D ∧
        pseudoExpect D (fun x ↦ linearSumPoly n x ^ 2) = 0 ∧
        (1 - C * (1 / (R : ℝ) + (R : ℝ) / (n : ℝ))) *
          ((n : ℝ) / Real.sqrt ((R : ℝ) - 1)) ≤ pseudoExpect D (linearSumPoly n) :=
  ⟨3, by norm_num, fun _ _ hR hRn ↦
    exists_local_pseudoDist_linearSumPoly_lower_bound_explicit hR hRn⟩

/-- Tightness sandwich combining the approximate Cauchy–Schwarz upper bound with the matching
Sherali–Adams lower bound for $p(x) = \sum_{i=0}^{n-1} \sigma(x_i)$. -/
theorem sa_approx_cs_tight_sandwich {n R : ℕ} (hR : 2 ≤ R) (hRn : R < n) :
    ∃ D : (Fin n → Bool) → ℝ, IsLocalPseudoDist R D ∧
      pseudoExpect D (fun x ↦ linearSumPoly n x ^ 2) = 0 ∧
      (1 - 3 * (1 / (R : ℝ) + (R : ℝ) / (n : ℝ))) *
        ((n : ℝ) / Real.sqrt ((R : ℝ) - 1)) ≤ pseudoExpect D (linearSumPoly n) ∧
      pseudoExpect D (linearSumPoly n) ≤ (n : ℝ) / Real.sqrt ((R : ℝ) - 1) := by
  obtain ⟨D, hD, hsq, hlow⟩ := exists_local_pseudoDist_linearSumPoly_lower_bound_explicit hR hRn
  exact ⟨D, hD, hsq, hlow, (le_abs_self _).trans (abs_pseudoExpect_linearSumPoly_le hR hD hsq)⟩

/-- Sherali–Adams pseudo-distributions cannot satisfy Cauchy–Schwarz even approximately without the
additive $\ell_1$ term: for every $\varepsilon > 0$, there exists $R_0 \ge 2$ such that for every
$R \ge R_0$, there exists $N_0 > R$ such that for every $n \ge N_0$, some $R$-local
pseudo-distribution $D$ on $\mathrm{Fin}\,n \to \mathrm{Bool}$ satisfies
$\tilde{\mathbb{E}}_D[p^2] = 0$ and
$\tilde{\mathbb{E}}_D[p] \ge (1 - \varepsilon)\,n / \sqrt{R - 1}$. -/
theorem sa_cannot_satisfy_cauchy_schwarz_exactly {ε : ℝ} (hε : 0 < ε) :
    ∃ R₀ : ℕ, 2 ≤ R₀ ∧ ∀ ⦃R : ℕ⦄, R₀ ≤ R →
      ∃ N₀ : ℕ, R < N₀ ∧ ∀ ⦃n : ℕ⦄, N₀ ≤ n →
        ∃ D : (Fin n → Bool) → ℝ, IsLocalPseudoDist R D ∧
          pseudoExpect D (fun x ↦ linearSumPoly n x ^ 2) = 0 ∧
          (1 - ε) * ((n : ℝ) / Real.sqrt ((R : ℝ) - 1)) ≤
            pseudoExpect D (linearSumPoly n) := by
  let R₀ : ℕ := max 2 (⌊6 / ε⌋₊ + 1)
  refine ⟨R₀, le_max_left _ _, fun R hR₀ ↦ ?_⟩
  have hR2 : 2 ≤ R := (le_max_left 2 _).trans hR₀
  have hR_gt : 6 / ε < (R : ℝ) := by
    have hfl : ⌊6 / ε⌋₊ + 1 ≤ R := (le_max_right 2 _).trans hR₀
    have hflR : ((⌊6 / ε⌋₊ : ℝ) + 1) ≤ (R : ℝ) := by exact_mod_cast hfl
    linarith [Nat.lt_floor_add_one (6 / ε)]
  have hR_pos : (0 : ℝ) < (R : ℝ) := by
    have : (2 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR2
    linarith
  have h1R : 3 * (1 / (R : ℝ)) ≤ ε / 2 := by
    have hmul := (div_lt_iff₀ hε).mp hR_gt
    rw [mul_one_div, div_le_div_iff₀ hR_pos (by norm_num)]
    linarith
  let N₀ : ℕ := max (R + 1) (⌊6 * (R : ℝ) / ε⌋₊ + 1)
  refine ⟨N₀, Nat.lt_of_lt_of_le (Nat.lt_succ_self R) (le_max_left _ _), fun n hn₀ ↦ ?_⟩
  have hRn : R < n := Nat.lt_of_lt_of_le (Nat.lt_succ_self R) ((le_max_left _ _).trans hn₀)
  have hn_gt : 6 * (R : ℝ) / ε < (n : ℝ) := by
    have hfl : ⌊6 * (R : ℝ) / ε⌋₊ + 1 ≤ n := (le_max_right (R + 1) _).trans hn₀
    have hfln : ((⌊6 * (R : ℝ) / ε⌋₊ : ℝ) + 1) ≤ (n : ℝ) := by exact_mod_cast hfl
    linarith [Nat.lt_floor_add_one (6 * (R : ℝ) / ε)]
  have hn_pos : (0 : ℝ) < (n : ℝ) := by
    have : (R : ℝ) < (n : ℝ) := by exact_mod_cast hRn
    linarith
  have hRn_err : 3 * ((R : ℝ) / (n : ℝ)) ≤ ε / 2 := by
    have hmul := (div_lt_iff₀ hε).mp hn_gt
    rw [mul_div_assoc', div_le_div_iff₀ hn_pos (by norm_num)]
    linarith
  obtain ⟨D, hD, hsq, hlow⟩ := exists_local_pseudoDist_linearSumPoly_lower_bound_explicit hR2 hRn
  refine ⟨D, hD, hsq, ?_⟩
  have herr : 1 - ε ≤ 1 - 3 * (1 / (R : ℝ) + (R : ℝ) / (n : ℝ)) := by linarith
  have hscale_nonneg : 0 ≤ (n : ℝ) / Real.sqrt ((R : ℝ) - 1) :=
    div_nonneg hn_pos.le (Real.sqrt_nonneg _)
  exact (mul_le_mul_of_nonneg_right herr hscale_nonneg).trans hlow

/-- No finite multiplicative factor $M$ can satisfy an inequality of the form
$\tilde{\mathbb{E}}_D[p \cdot 1] \le M \sqrt{\tilde{\mathbb{E}}_D[p^2]}
\sqrt{\tilde{\mathbb{E}}_D[1^2]}$ across $R$-local Sherali–Adams pseudo-distributions. -/
theorem no_multiplicative_approx_cauchy_schwarz (M : ℝ) :
    ∃ n R : ℕ, 2 ≤ R ∧ R < n ∧ ∃ D : (Fin n → Bool) → ℝ, IsLocalPseudoDist R D ∧
      pseudoExpect D (fun x ↦ linearSumPoly n x ^ 2) = 0 ∧
      pseudoExpect D (fun _ ↦ (1 : ℝ) ^ 2) = 1 ∧
      M * Real.sqrt (pseudoExpect D (fun x ↦ linearSumPoly n x ^ 2)) *
          Real.sqrt (pseudoExpect D (fun _ ↦ (1 : ℝ) ^ 2)) <
        pseudoExpect D (linearSumPoly n) := by
  obtain ⟨R₀, hR₀, hmain⟩ := sa_cannot_satisfy_cauchy_schwarz_exactly (ε := 1 / 2) (by norm_num)
  obtain ⟨N₀, hRN₀, hN₀⟩ := hmain le_rfl
  obtain ⟨D, hD, hsq, hlow⟩ := hN₀ le_rfl
  have h1 : pseudoExpect D (fun _ ↦ (1 : ℝ) ^ 2) = 1 := by
    simpa using hD.pseudoExpect_one
  have hR₀_real : (2 : ℝ) ≤ (R₀ : ℝ) := by exact_mod_cast hR₀
  have hN₀_pos : (0 : ℝ) < (N₀ : ℝ) := by
    have : (R₀ : ℝ) < (N₀ : ℝ) := by exact_mod_cast hRN₀
    linarith
  have hsqrt_pos : 0 < Real.sqrt ((R₀ : ℝ) - 1) := Real.sqrt_pos.mpr (by linarith)
  have hpos : 0 < (1 - (1 / 2 : ℝ)) * ((N₀ : ℝ) / Real.sqrt ((R₀ : ℝ) - 1)) :=
    mul_pos (by norm_num) (div_pos hN₀_pos hsqrt_pos)
  refine ⟨N₀, R₀, hR₀, hRN₀, D, hD, hsq, h1, ?_⟩
  rw [hsq, h1, Real.sqrt_zero, mul_zero, zero_mul]
  exact hpos.trans_le hlow

end CslibFrontier.Foundations.BooleanAnalysis
