/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import CslibFrontier.Foundations.Data.Code.ReedMuller
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.InformationTheory.Hamming
public import Mathlib.LinearAlgebra.AffineSpace.AffineEquiv

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Data.Fintype.Powerset
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Binary Reed–Muller Codes: Multilinear Expansion, Minimum Distance, and Duality

This module develops the foundational algebraic and coding-theoretic properties of binary
Reed–Muller codes `Cslib.Code.reedMuller (ZMod 2) n d` over $\mathbb{F}_2$:

## Main definitions

* `CslibFrontier.Code.BinaryReedMuller.indVec`, `CslibFrontier.Code.BinaryReedMuller.vecSupp`,
  `CslibFrontier.Code.BinaryReedMuller.indVecEquiv`: bijection between subsets of `Fin n` and
  vectors in $\mathbb{F}_2^n$.
* `CslibFrontier.Code.BinaryReedMuller.mlMonomial`, `CslibFrontier.Code.BinaryReedMuller.mlCoeff`:
  multilinear monomials $\prod_{i \in S} x_i$ and Möbius transform coefficients over $\mathbb{F}_2$.

## Main results

* `CslibFrontier.Code.BinaryReedMuller.mlExpansion`,
  `CslibFrontier.Code.BinaryReedMuller.mlCoeff_unique`,
  `CslibFrontier.Code.BinaryReedMuller.mem_reedMuller_iff_mlCoeff`: unique multilinear expansion
  and degree characterization of binary Reed–Muller codewords.
* `CslibFrontier.Code.BinaryReedMuller.card_reedMuller`: exact cardinality
  $2^{\sum_{i = 0}^{d} \binom{n}{i}}$ of `Cslib.Code.reedMuller (ZMod 2) n d`.
* `CslibFrontier.Code.BinaryReedMuller.comp_affineMap_mem_reedMuller`,
  `CslibFrontier.Code.BinaryReedMuller.comp_affineEquiv_mem_reedMuller_iff`: affine invariance
  of binary Reed–Muller codes.
* `CslibFrontier.Code.BinaryReedMuller.two_pow_sub_le_hammingNorm_of_mem_reedMuller`: binary
  Reed–Muller minimum weight $2^{n - d}$ for $d \le n$, proved via the Plotkin split.
* `CslibFrontier.Code.BinaryReedMuller.eval_surjective`: evaluation of binary Reed–Muller codes
  of degree $d$ on any set of fewer than $2^{d + 1}$ points is surjective (establishing
  $(2^{d + 1} - 1)$-wise independence of a uniformly random codeword).
-/

namespace CslibFrontier.Code.BinaryReedMuller

open Finset MvPolynomial

public section

/-- The indicator vector in $\mathbb{F}_2^n$ of a coordinate subset
$S \subseteq \mathrm{Fin}\, n$. -/
@[expose]
def indVec {n : ℕ} (S : Finset (Fin n)) : Fin n → ZMod 2 :=
  fun i ↦ if i ∈ S then 1 else 0

/-- The support of a binary vector $x \in \mathbb{F}_2^n$ as a `Finset (Fin n)`. -/
def vecSupp {n : ℕ} (x : Fin n → ZMod 2) : Finset (Fin n) :=
  Finset.univ.filter fun i ↦ x i = 1

private lemma zmod2_eq_zero_or_one (a : ZMod 2) : a = 0 ∨ a = 1 := by
  revert a; decide

private lemma zmod2_pow_eq_self {a : ZMod 2} {k : ℕ} (hk : 0 < k) : a ^ k = a := by
  rcases zmod2_eq_zero_or_one a with rfl | rfl
  · exact zero_pow hk.ne'
  · exact one_pow k

private lemma zmod2_eq_one_iff_ne_zero (a : ZMod 2) : a = 1 ↔ a ≠ 0 := by
  revert a; decide

/-- Reconstructing a vector from its support recovers the vector. -/
@[simp]
theorem indVec_vecSupp {n : ℕ} (x : Fin n → ZMod 2) : indVec (vecSupp x) = x := by
  ext i
  rcases zmod2_eq_zero_or_one (x i) with h | h <;> simp [indVec, vecSupp, h]

/-- The support of an indicator vector is the original subset. -/
@[simp]
theorem vecSupp_indVec {n : ℕ} (S : Finset (Fin n)) : vecSupp (indVec S) = S := by
  ext i
  by_cases hi : i ∈ S <;> simp [indVec, vecSupp, hi]

/-- The equivalence `Finset (Fin n) ≃ (Fin n → ZMod 2)` given by indicator vectors. -/
def indVecEquiv (n : ℕ) : Finset (Fin n) ≃ (Fin n → ZMod 2) where
  toFun := indVec
  invFun := vecSupp
  left_inv := vecSupp_indVec
  right_inv := indVec_vecSupp

/-- The multilinear monomial $\prod_{i \in S} x_i$ on $\mathbb{F}_2^n$. -/
@[expose]
def mlMonomial {n : ℕ} (S : Finset (Fin n)) (x : Fin n → ZMod 2) : ZMod 2 :=
  ∏ i ∈ S, x i

/-- Evaluation of `mlMonomial S` at `indVec T` is $1$ iff $S \subseteq T$. -/
theorem mlMonomial_indVec {n : ℕ} (S T : Finset (Fin n)) :
    mlMonomial S (indVec T) = if S ⊆ T then 1 else 0 := by
  unfold mlMonomial indVec
  by_cases h : S ⊆ T
  · rw [ite_eq_left h]
    exact Finset.prod_eq_one fun i hi ↦ ite_eq_left (h hi)
  · rw [ite_eq_right h]
    obtain ⟨i, hiS, hiT⟩ := Finset.not_subset.mp h
    exact Finset.prod_eq_zero hiS (ite_eq_right hiT)

/-- The multilinear monomial of a subset of size at most $d$ lies in
`Cslib.Code.reedMuller (ZMod 2) n d`. -/
theorem mlMonomial_mem_reedMuller {d n : ℕ} {S : Finset (Fin n)} (hS : S.card ≤ d) :
    mlMonomial S ∈ Cslib.Code.reedMuller (ZMod 2) n d := by
  refine Cslib.Code.mem_reedMuller.mpr ⟨∏ i ∈ S, MvPolynomial.X i, ?_, ?_⟩
  · refine (MvPolynomial.totalDegree_finsetProd _ _).trans ?_
    calc ∑ i ∈ S, (MvPolynomial.X i : MvPolynomial (Fin n) (ZMod 2)).totalDegree
        ≤ ∑ _i ∈ S, 1 := Finset.sum_le_sum fun i _ ↦ (MvPolynomial.totalDegree_X i).le
      _ = S.card := by simp
      _ ≤ d := hS
  · ext x
    simp [mlMonomial, map_prod]

/-- The multilinear Möbius coefficient of $f : \mathbb{F}_2^n \to \mathbb{F}_2$ on monomial $S$,
given by $\sum_{T \subseteq S} f(\mathbf{1}_T)$. -/
def mlCoeff {n : ℕ} (f : (Fin n → ZMod 2) → ZMod 2) (S : Finset (Fin n)) : ZMod 2 :=
  ∑ T ∈ S.powerset, f (indVec T)

/-- `mlCoeff` is additive in the function. -/
theorem mlCoeff_add {n : ℕ} (f g : (Fin n → ZMod 2) → ZMod 2) (S : Finset (Fin n)) :
    mlCoeff (f + g) S = mlCoeff f S + mlCoeff g S := by
  simp [mlCoeff, Finset.sum_add_distrib]

/-- `mlCoeff` of the zero function is $0$. -/
@[simp]
theorem mlCoeff_zero {n : ℕ} (S : Finset (Fin n)) :
    mlCoeff (0 : (Fin n → ZMod 2) → ZMod 2) S = 0 := by
  simp [mlCoeff]

/-- `mlCoeff` respects scalar multiplication. -/
theorem mlCoeff_smul {n : ℕ} (c : ZMod 2) (f : (Fin n → ZMod 2) → ZMod 2) (S : Finset (Fin n)) :
    mlCoeff (c • f) S = c * mlCoeff f S := by
  simp [mlCoeff, Finset.mul_sum]

/-- `mlCoeff` distributes over finite sums of functions. -/
theorem mlCoeff_sum {n : ℕ} {ι : Type*} (s : Finset ι)
    (g : ι → (Fin n → ZMod 2) → ZMod 2) (S : Finset (Fin n)) :
    mlCoeff (∑ i ∈ s, g i) S = ∑ i ∈ s, mlCoeff (g i) S := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, mlCoeff_add, ih, Finset.sum_insert ha]

private theorem card_interval_powerset_zmod2 {n : ℕ} {A B : Finset (Fin n)} (hAB : A ⊆ B) :
    (((B.powerset.filter fun T ↦ A ⊆ T).card : ℕ) : ZMod 2) = if A = B then 1 else 0 := by
  have hbij : (B.powerset.filter fun T ↦ A ⊆ T).card = (B \ A).powerset.card := by
    refine Finset.card_bij (fun T _ ↦ T \ A) ?_ ?_ ?_
    · intro T hT
      simp only [Finset.mem_filter, Finset.mem_powerset] at hT ⊢
      exact Finset.sdiff_subset_sdiff hT.1 Subset.rfl
    · intro T₁ hT₁ T₂ hT₂ heq
      simp only [Finset.mem_filter, Finset.mem_powerset] at hT₁ hT₂
      calc T₁ = (T₁ \ A) ∪ A := (Finset.sdiff_union_of_subset hT₁.2).symm
        _ = (T₂ \ A) ∪ A := by rw [heq]
        _ = T₂ := Finset.sdiff_union_of_subset hT₂.2
    · intro U hU
      simp only [Finset.mem_powerset] at hU
      refine ⟨U ∪ A, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_powerset]
        exact ⟨Finset.union_subset (hU.trans Finset.sdiff_subset) hAB, Finset.subset_union_right⟩
      · exact Finset.union_sdiff_cancel_right
          (Finset.disjoint_of_subset_left hU disjoint_sdiff_self_left)
  rw [hbij, Finset.card_powerset]
  by_cases h : A = B
  · subst h; simp
  · rw [ite_eq_right h]
    have hpos : 0 < (B \ A).card := by
      rw [Finset.card_pos, Finset.sdiff_nonempty]
      intro hBA
      exact h (Finset.Subset.antisymm hAB hBA)
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
    rw [hk, pow_succ, Nat.cast_mul]
    have h2 : ((2 : ℕ) : ZMod 2) = 0 := by decide
    rw [h2, mul_zero]

/-- The Möbius coefficient of `mlMonomial A` at $B$ is $1$ iff $A = B$. -/
theorem mlCoeff_mlMonomial {n : ℕ} (A B : Finset (Fin n)) :
    mlCoeff (mlMonomial A) B = if A = B then 1 else 0 := by
  unfold mlCoeff
  simp_rw [mlMonomial_indVec]
  rw [Finset.sum_boole]
  by_cases hAB : A ⊆ B
  · exact card_interval_powerset_zmod2 hAB
  · have hne : A ≠ B := fun h ↦ hAB (h ▸ Subset.rfl)
    rw [ite_eq_right hne]
    have hempty : B.powerset.filter (fun T ↦ A ⊆ T) = ∅ := by
      ext T
      simp only [Finset.mem_filter, Finset.mem_powerset, Finset.notMem_empty, iff_false, not_and]
      intro hTB hAT
      exact hAB (hAT.trans hTB)
    simp [hempty]

/-- Every function $f : \mathbb{F}_2^n \to \mathbb{F}_2$ equals its multilinear Möbius expansion. -/
theorem mlExpansion {n : ℕ} (f : (Fin n → ZMod 2) → ZMod 2) (x : Fin n → ZMod 2) :
    f x = ∑ S : Finset (Fin n), mlCoeff f S * mlMonomial S x := by
  set U := vecSupp x
  have hx : x = indVec U := (indVec_vecSupp x).symm
  rw [hx]
  simp_rw [mlMonomial_indVec, mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  have hfilt : (Finset.univ.filter fun S : Finset (Fin n) ↦ S ⊆ U) = U.powerset := by
    ext S; simp
  rw [hfilt]
  simp_rw [mlCoeff]
  have hswap : ∑ S ∈ U.powerset, ∑ T ∈ S.powerset, f (indVec T) =
      ∑ T ∈ U.powerset, ∑ S ∈ U.powerset.filter (fun S ↦ T ⊆ S), f (indVec T) := by
    trans ∑ S ∈ U.powerset, ∑ T ∈ U.powerset, if T ⊆ S then f (indVec T) else 0
    · refine Finset.sum_congr rfl fun S hS ↦ ?_
      rw [← Finset.sum_filter]
      congr 1
      ext T
      simp only [Finset.mem_powerset, Finset.mem_filter] at hS ⊢
      exact ⟨fun hTS ↦ ⟨hTS.trans hS, hTS⟩, fun h ↦ h.2⟩
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun T _ ↦ ?_
      rw [Finset.sum_filter]
  rw [hswap]
  have hterm : ∀ T ∈ U.powerset,
      (∑ _S ∈ U.powerset.filter (fun S ↦ T ⊆ S), f (indVec T)) =
        if T = U then f (indVec U) else 0 := by
    intro T hT
    rw [Finset.sum_const, nsmul_eq_mul, card_interval_powerset_zmod2 (Finset.mem_powerset.mp hT)]
    split_ifs with h
    · subst h; simp
    · simp
  rw [Finset.sum_congr rfl hterm]
  simp

/-- Uniqueness of multilinear coefficients over $\mathbb{F}_2$. -/
theorem mlCoeff_unique {n : ℕ} {f : (Fin n → ZMod 2) → ZMod 2} {c : Finset (Fin n) → ZMod 2}
    (h : ∀ x, f x = ∑ S : Finset (Fin n), c S * mlMonomial S x) :
    c = mlCoeff f := by
  ext B
  have hfun : f = ∑ S : Finset (Fin n), c S • mlMonomial S := by
    ext x
    rw [h x, Finset.sum_apply]
    simp [smul_eq_mul]
  rw [hfun, mlCoeff_sum]
  simp_rw [mlCoeff_smul, mlCoeff_mlMonomial]
  simp

private theorem eval_monomial_eq_mlMonomial {n : ℕ} (s : Fin n →₀ ℕ) (a : ZMod 2) :
    (fun x : Fin n → ZMod 2 ↦ MvPolynomial.eval x (MvPolynomial.monomial s a)) =
      a • mlMonomial s.support := by
  ext x
  rw [MvPolynomial.eval_monomial, Pi.smul_apply, smul_eq_mul, mlMonomial]
  congr 1
  rw [Finsupp.prod]
  refine Finset.prod_congr rfl fun i hi ↦ ?_
  exact zmod2_pow_eq_self (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hi))

/-- A function $f : \mathbb{F}_2^n \to \mathbb{F}_2$ lies in
`Cslib.Code.reedMuller (ZMod 2) n d` if and only if every multilinear coefficient of degree
greater than $d$ vanishes. -/
theorem mem_reedMuller_iff_mlCoeff {d n : ℕ} {f : (Fin n → ZMod 2) → ZMod 2} :
    f ∈ Cslib.Code.reedMuller (ZMod 2) n d ↔
      ∀ S : Finset (Fin n), d < S.card → mlCoeff f S = 0 := by
  constructor
  · intro hf
    obtain ⟨P, hP, rfl⟩ := Cslib.Code.mem_reedMuller.mp hf
    have hPeq : (fun x : Fin n → ZMod 2 ↦ MvPolynomial.eval x P) =
        ∑ s ∈ P.support, P.coeff s • mlMonomial s.support := by
      ext x
      conv_lhs => rw [P.as_sum]
      rw [map_sum, Finset.sum_apply]
      refine Finset.sum_congr rfl fun s _ ↦ ?_
      exact congrFun (eval_monomial_eq_mlMonomial s (P.coeff s)) x
    intro S hS
    rw [hPeq, mlCoeff_sum]
    refine Finset.sum_eq_zero fun s hs ↦ ?_
    rw [mlCoeff_smul, mlCoeff_mlMonomial]
    have hcard : s.support.card ≤ d := by
      calc s.support.card
          = ∑ _i ∈ s.support, 1 := by simp
        _ ≤ ∑ i ∈ s.support, s i := Finset.sum_le_sum fun i hi ↦
            Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi)
        _ ≤ P.totalDegree := MvPolynomial.le_totalDegree hs
        _ ≤ d := hP
    have hne : s.support ≠ S := fun heq ↦ by rw [heq] at hcard; omega
    simp [hne]
  · intro h
    have hexp : f = ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin n) ↦ S.card ≤ d),
        mlCoeff f S • mlMonomial S := by
      ext x
      rw [mlExpansion f x, Finset.sum_apply]
      symm
      refine Finset.sum_subset (Finset.filter_subset _ _) fun S _ hS ↦ ?_
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hS
      simp [h S hS]
    rw [hexp]
    refine Submodule.sum_mem _ fun S hS ↦ ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS
    exact Submodule.smul_mem _ _ (mlMonomial_mem_reedMuller hS)

/-- Every function on $\mathbb{F}_2^n$ lies in `Cslib.Code.reedMuller (ZMod 2) n d` when
$n \le d$. -/
theorem mem_reedMuller_of_le {d n : ℕ} (h : n ≤ d) (f : (Fin n → ZMod 2) → ZMod 2) :
    f ∈ Cslib.Code.reedMuller (ZMod 2) n d := by
  rw [mem_reedMuller_iff_mlCoeff]
  intro S hS
  have : S.card ≤ n := (Finset.card_le_univ S).trans (by simp)
  omega

/-- A function $f : \mathbb{F}_2^{d+1} \to \mathbb{F}_2$ lies in
`Cslib.Code.reedMuller (ZMod 2) (d + 1) d` iff the sum of all its evaluations is $0$. -/
theorem sum_eq_zero_iff_mem_reedMuller_pred {d : ℕ} (f : (Fin (d + 1) → ZMod 2) → ZMod 2) :
    (∑ x : Fin (d + 1) → ZMod 2, f x) = 0 ↔ f ∈ Cslib.Code.reedMuller (ZMod 2) (d + 1) d := by
  have hsum : (∑ x : Fin (d + 1) → ZMod 2, f x) = mlCoeff f Finset.univ := by
    unfold mlCoeff
    rw [Finset.powerset_univ]
    exact (Equiv.sum_comp (indVecEquiv (d + 1)) f).symm
  rw [hsum, mem_reedMuller_iff_mlCoeff]
  constructor
  · intro h S hS
    have hcard : S.card = d + 1 :=
      le_antisymm ((Finset.card_le_univ S).trans (by simp)) hS
    have hSu : S = Finset.univ := Finset.eq_univ_of_card S (by simpa using hcard)
    exact hSu ▸ h
  · intro h
    exact h Finset.univ (by simp)

/-- The cardinality of `Cslib.Code.reedMuller (ZMod 2) n d` is
$2^{\sum_{i = 0}^{d} \binom{n}{i}}$. -/
theorem card_reedMuller (d n : ℕ) :
    Nat.card (Cslib.Code.reedMuller (ZMod 2) n d) =
      2 ^ (∑ i ∈ Finset.range (d + 1), n.choose i) := by
  classical
  let idx := { S : Finset (Fin n) // S.card ≤ d }
  let e : Cslib.Code.reedMuller (ZMod 2) n d ≃ (idx → ZMod 2) :=
    { toFun := fun f S ↦ mlCoeff f.1 S.1
      invFun := fun c ↦
        ⟨∑ S : Finset (Fin n), (if h : S.card ≤ d then c ⟨S, h⟩ else 0) • mlMonomial S, by
          refine Submodule.sum_mem _ fun S _ ↦ ?_
          by_cases h : S.card ≤ d
          · rw [dite_eq_left h]; exact Submodule.smul_mem _ _ (mlMonomial_mem_reedMuller h)
          · rw [dite_eq_right h, zero_smul]; exact Submodule.zero_mem _⟩
      left_inv := fun f ↦ by
        apply Subtype.ext
        ext x
        change (∑ S : Finset (Fin n),
          (if h : S.card ≤ d then mlCoeff f.1 S else 0) • mlMonomial S) x = f.1 x
        rw [Finset.sum_apply, mlExpansion f.1 x]
        refine Finset.sum_congr rfl fun S _ ↦ ?_
        by_cases h : S.card ≤ d
        · simp [h]
        · have hzero := (mem_reedMuller_iff_mlCoeff.mp f.2) S (Nat.lt_of_not_ge h)
          simp [h, hzero]
      right_inv := fun c ↦ by
        ext ⟨S, hS⟩
        dsimp only
        rw [mlCoeff_sum]
        simp_rw [mlCoeff_smul, mlCoeff_mlMonomial]
        simp [hS] }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card]
  congr 1
  have hcard : Fintype.card idx = (Finset.univ.filter fun S : Finset (Fin n) ↦ S.card ≤ d).card :=
    Fintype.card_subtype _
  rw [hcard]
  have hbi : (Finset.univ.filter fun S : Finset (Fin n) ↦ S.card ≤ d) =
      (Finset.range (d + 1)).biUnion fun i ↦
        Finset.powersetCard i (Finset.univ : Finset (Fin n)) := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
      Finset.mem_range, Finset.mem_powersetCard, Finset.subset_univ, Nat.lt_succ_iff]
    exact ⟨fun h ↦ ⟨S.card, h, rfl⟩, fun ⟨_, hi, hS⟩ ↦ hS ▸ hi⟩
  rw [hbi, Finset.card_biUnion]
  · refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  · intro i _ j _ hij
    change Disjoint _ _
    rw [Finset.disjoint_left]
    intro S hSi hSj
    rw [Finset.mem_powersetCard] at hSi hSj
    exact hij (hSi.2.symm.trans hSj.2)

/-! ### Affine invariance -/

private theorem totalDegree_aeval_linear_le {m n : ℕ}
    (L : Fin n → MvPolynomial (Fin m) (ZMod 2)) (hL : ∀ i, (L i).totalDegree ≤ 1)
    (P : MvPolynomial (Fin n) (ZMod 2)) :
    (MvPolynomial.aeval L P).totalDegree ≤ P.totalDegree := by
  conv_lhs => rw [P.as_sum]
  rw [map_sum]
  refine MvPolynomial.totalDegree_finsetSum_le fun s hs ↦ ?_
  rw [MvPolynomial.aeval_monomial, MvPolynomial.algebraMap_eq]
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  rw [MvPolynomial.totalDegree_C, zero_add, Finsupp.prod]
  refine (MvPolynomial.totalDegree_finsetProd _ _).trans ?_
  calc ∑ i ∈ s.support, (L i ^ s i).totalDegree
      ≤ ∑ i ∈ s.support, s i * (L i).totalDegree :=
        Finset.sum_le_sum fun i _ ↦ MvPolynomial.totalDegree_pow _ _
    _ ≤ ∑ i ∈ s.support, s i * 1 :=
        Finset.sum_le_sum fun i _ ↦ Nat.mul_le_mul_left _ (hL i)
    _ = ∑ i ∈ s.support, s i := by simp
    _ ≤ P.totalDegree := MvPolynomial.le_totalDegree hs

private theorem eval_aeval_eq {m n : ℕ} (L : Fin n → MvPolynomial (Fin m) (ZMod 2))
    (x : Fin m → ZMod 2) (P : MvPolynomial (Fin n) (ZMod 2)) :
    MvPolynomial.eval x (MvPolynomial.aeval L P) =
      MvPolynomial.eval (fun i ↦ MvPolynomial.eval x (L i)) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]
  | mul_X p i hp => rw [map_mul, map_mul, map_mul, MvPolynomial.aeval_X, MvPolynomial.eval_X, hp]

/-- Precomposition with an affine map $\mathbb{F}_2^m \to \mathbb{F}_2^n$ preserves binary
Reed–Muller codes. -/
theorem comp_affineMap_mem_reedMuller {d m n : ℕ}
    (T : (Fin m → ZMod 2) →ᵃ[ZMod 2] (Fin n → ZMod 2))
    {f : (Fin n → ZMod 2) → ZMod 2} (hf : f ∈ Cslib.Code.reedMuller (ZMod 2) n d) :
    (f ∘ T) ∈ Cslib.Code.reedMuller (ZMod 2) m d := by
  obtain ⟨P, hP, rfl⟩ := Cslib.Code.mem_reedMuller.mp hf
  let b : Fin n → ZMod 2 := T 0
  let L : Fin n → MvPolynomial (Fin m) (ZMod 2) := fun i ↦
    MvPolynomial.C (b i) +
      ∑ j : Fin m, MvPolynomial.C (T.linear (Pi.single j 1) i) * MvPolynomial.X j
  have hLdeg : ∀ i, (L i).totalDegree ≤ 1 := fun i ↦ by
    refine (MvPolynomial.totalDegree_add _ _).trans (max_le ?_ ?_)
    · simp
    · refine MvPolynomial.totalDegree_finsetSum_le fun j _ ↦ ?_
      refine (MvPolynomial.totalDegree_mul _ _).trans ?_
      simp
  have hLeval : ∀ (x : Fin m → ZMod 2) (i : Fin n), MvPolynomial.eval x (L i) = T x i := by
    intro x i
    simp only [L, map_add, MvPolynomial.eval_C, map_sum, map_mul, MvPolynomial.eval_X]
    have hx : x = ∑ j : Fin m, x j • Pi.single j (1 : ZMod 2) := by
      ext k; simp [Finset.sum_apply, Pi.single_apply]
    have hTx : T x = T.linear x + T 0 := by
      have := T.map_vadd 0 x
      simpa [vadd_eq_add] using this
    rw [hTx, Pi.add_apply, add_comm]
    congr 1
    conv_rhs => rw [hx, map_sum]
    simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm]
  refine Cslib.Code.mem_reedMuller.mpr ⟨MvPolynomial.aeval L P,
    (totalDegree_aeval_linear_le L hLdeg P).trans hP, ?_⟩
  ext x
  rw [Function.comp_apply, eval_aeval_eq,
    show (fun i ↦ MvPolynomial.eval x (L i)) = T x from funext (hLeval x)]

/-- Precomposition with an affine equivalence preserves membership in binary Reed–Muller codes
in both directions. -/
theorem comp_affineEquiv_mem_reedMuller_iff {d m n : ℕ}
    (e : (Fin m → ZMod 2) ≃ᵃ[ZMod 2] (Fin n → ZMod 2))
    (f : (Fin n → ZMod 2) → ZMod 2) :
    (f ∘ e) ∈ Cslib.Code.reedMuller (ZMod 2) m d ↔ f ∈ Cslib.Code.reedMuller (ZMod 2) n d := by
  constructor
  · intro h
    have h' := comp_affineMap_mem_reedMuller e.symm.toAffineMap h
    have heq : (f ∘ e) ∘ e.symm = f := by ext x; simp
    simpa [heq] using h'
  · exact comp_affineMap_mem_reedMuller e.toAffineMap

/-! ### Minimum weight via the Plotkin split -/

private def slice0 {n : ℕ} (f : (Fin (n + 1) → ZMod 2) → ZMod 2) : (Fin n → ZMod 2) → ZMod 2 :=
  fun x ↦ f (Fin.cons 0 x)

private def slice1 {n : ℕ} (f : (Fin (n + 1) → ZMod 2) → ZMod 2) : (Fin n → ZMod 2) → ZMod 2 :=
  fun x ↦ f (Fin.cons 1 x)

private theorem mlCoeff_slice0 {n : ℕ} (f : (Fin (n + 1) → ZMod 2) → ZMod 2) (S : Finset (Fin n)) :
    mlCoeff (slice0 f) S = mlCoeff f (S.map ⟨Fin.succ, Fin.succ_injective n⟩) := by
  unfold mlCoeff slice0
  refine Finset.sum_bij (fun T _ ↦ T.map ⟨Fin.succ, Fin.succ_injective n⟩) ?_ ?_ ?_ ?_
  · intro T hT
    exact Finset.mem_powerset.mpr (Finset.map_subset_map.mpr (Finset.mem_powerset.mp hT))
  · intro T₁ _ T₂ _ h; exact Finset.map_injective _ h
  · intro U hU
    rw [Finset.mem_powerset] at hU
    refine ⟨U.preimage Fin.succ (Fin.succ_injective n).injOn, ?_, ?_⟩
    · rw [Finset.mem_powerset]
      intro i hi
      have hsucc : i.succ ∈ S.map ⟨Fin.succ, Fin.succ_injective n⟩ := hU (Finset.mem_preimage.mp hi)
      simpa using hsucc
    · ext j
      simp only [Finset.mem_map, Finset.mem_preimage, Function.Embedding.coeFn_mk]
      constructor
      · rintro ⟨i, hi, rfl⟩; exact hi
      · intro hj
        obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp (hU hj)
        exact ⟨i, hj, rfl⟩
  · intro T _
    congr 1
    ext j
    refine Fin.cases (by simp [indVec]) (fun i ↦ by simp [indVec]) j

private theorem mlCoeff_slice0_add_slice1 {n : ℕ} (f : (Fin (n + 1) → ZMod 2) → ZMod 2)
    (S : Finset (Fin n)) :
    mlCoeff (slice0 f + slice1 f) S =
      mlCoeff f (insert 0 (S.map ⟨Fin.succ, Fin.succ_injective n⟩)) := by
  have hnotmem : (0 : Fin (n + 1)) ∉ S.map ⟨Fin.succ, Fin.succ_injective n⟩ := by simp
  rw [mlCoeff_add, mlCoeff_slice0]
  unfold mlCoeff
  rw [Finset.powerset_insert, Finset.sum_union]
  · rw [Finset.sum_image]
    · congr 1
      refine Finset.sum_bij (fun T _ ↦ T.map ⟨Fin.succ, Fin.succ_injective n⟩) ?_ ?_ ?_ ?_
      · intro T hT
        exact Finset.mem_powerset.mpr (Finset.map_subset_map.mpr (Finset.mem_powerset.mp hT))
      · intro T₁ _ T₂ _ h; exact Finset.map_injective _ h
      · intro U hU
        rw [Finset.mem_powerset] at hU
        refine ⟨U.preimage Fin.succ (Fin.succ_injective n).injOn, ?_, ?_⟩
        · rw [Finset.mem_powerset]
          intro i hi
          have hsucc : i.succ ∈ S.map ⟨Fin.succ, Fin.succ_injective n⟩ :=
            hU (Finset.mem_preimage.mp hi)
          simpa using hsucc
        · ext j
          simp only [Finset.mem_map, Finset.mem_preimage, Function.Embedding.coeFn_mk]
          constructor
          · rintro ⟨i, hi, rfl⟩; exact hi
          · intro hj
            obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp (hU hj)
            exact ⟨i, hj, rfl⟩
      · intro T _
        dsimp [slice1]
        congr 1
        ext j
        refine Fin.cases (by simp [indVec]) (fun i ↦ by simp [indVec]) j
    · intro U₁ hU₁ U₂ hU₂ heq
      have h0₁ : (0 : Fin (n + 1)) ∉ U₁ := fun h ↦ hnotmem (Finset.mem_powerset.mp hU₁ h)
      have h0₂ : (0 : Fin (n + 1)) ∉ U₂ := fun h ↦ hnotmem (Finset.mem_powerset.mp hU₂ h)
      have := congrArg (fun A ↦ A.erase 0) heq
      simpa [Finset.erase_insert h0₁, Finset.erase_insert h0₂] using this
  · rw [Finset.disjoint_left]
    intro U hU₁ hU₂
    obtain ⟨V, _, rfl⟩ := Finset.mem_image.mp hU₂
    exact hnotmem (Finset.mem_powerset.mp hU₁ (Finset.mem_insert_self 0 V))

private theorem slice0_mem_reedMuller {d n : ℕ} {f : (Fin (n + 1) → ZMod 2) → ZMod 2}
    (hf : f ∈ Cslib.Code.reedMuller (ZMod 2) (n + 1) d) :
    slice0 f ∈ Cslib.Code.reedMuller (ZMod 2) n d := by
  rw [mem_reedMuller_iff_mlCoeff] at hf ⊢
  intro S hS
  rw [mlCoeff_slice0]
  exact hf _ (by simpa using hS)

private theorem slice0_add_slice1_mem_reedMuller {d n : ℕ} {f : (Fin (n + 1) → ZMod 2) → ZMod 2}
    (hf : f ∈ Cslib.Code.reedMuller (ZMod 2) (n + 1) (d + 1)) :
    slice0 f + slice1 f ∈ Cslib.Code.reedMuller (ZMod 2) n d := by
  rw [mem_reedMuller_iff_mlCoeff] at hf ⊢
  intro S hS
  rw [mlCoeff_slice0_add_slice1]
  have hnotmem : (0 : Fin (n + 1)) ∉ S.map ⟨Fin.succ, Fin.succ_injective n⟩ := by simp
  refine hf _ ?_
  rw [Finset.card_insert_of_notMem hnotmem, Finset.card_map]
  omega

private theorem hammingNorm_eq_add_slices {n : ℕ} (f : (Fin (n + 1) → ZMod 2) → ZMod 2) :
    hammingNorm f = hammingNorm (slice0 f) + hammingNorm (slice1 f) := by
  unfold hammingNorm slice0 slice1
  have hsplit : (Finset.univ.filter fun x : Fin (n + 1) → ZMod 2 ↦ f x ≠ 0) =
      (Finset.univ.filter fun x : Fin (n + 1) → ZMod 2 ↦ x 0 = 0 ∧ f x ≠ 0) ∪
      (Finset.univ.filter fun x : Fin (n + 1) → ZMod 2 ↦ x 0 = 1 ∧ f x ≠ 0) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    rcases zmod2_eq_zero_or_one (x 0) with h | h <;> simp [h]
  rw [hsplit, Finset.card_union_of_disjoint]
  · congr 1
    · refine Finset.card_bij (fun x _ ↦ fun i ↦ x i.succ) ?_ ?_ ?_
      · intro x hx
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
        have hcons : Fin.cons (0 : ZMod 2) (fun i ↦ x i.succ) = x := by
          ext j; refine Fin.cases (by simpa using hx.1.symm) (fun i ↦ by simp) j
        rw [hcons]; exact hx.2
      · intro x₁ hx₁ x₂ hx₂ heq
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx₁ hx₂
        ext j; refine Fin.cases (hx₁.1.trans hx₂.1.symm) (fun i ↦ congrFun heq i) j
      · intro y hy
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
        exact ⟨Fin.cons 0 y, by simp [hy], by ext i; simp⟩
    · refine Finset.card_bij (fun x _ ↦ fun i ↦ x i.succ) ?_ ?_ ?_
      · intro x hx
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
        have hcons : Fin.cons (1 : ZMod 2) (fun i ↦ x i.succ) = x := by
          ext j; refine Fin.cases (by simpa using hx.1.symm) (fun i ↦ by simp) j
        rw [hcons]; exact hx.2
      · intro x₁ hx₁ x₂ hx₂ heq
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx₁ hx₂
        ext j; refine Fin.cases (hx₁.1.trans hx₂.1.symm) (fun i ↦ congrFun heq i) j
      · intro y hy
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
        exact ⟨Fin.cons 1 y, by simp [hy], by ext i; simp⟩
  · rw [Finset.disjoint_left]
    intro x hx₁ hx₂
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx₁ hx₂
    exact absurd (hx₁.1.symm.trans hx₂.1) (by decide)

/-- **Minimum distance of binary Reed–Muller codes**: every nonzero codeword
$f \in \mathrm{RM}(d, n)$ with $d \le n$ has Hamming weight at least $2^{n - d}$. -/
theorem two_pow_sub_le_hammingNorm_of_mem_reedMuller {d n : ℕ} {f : (Fin n → ZMod 2) → ZMod 2}
    (hdn : d ≤ n) (hf : f ∈ Cslib.Code.reedMuller (ZMod 2) n d) (hf0 : f ≠ 0) :
    2 ^ (n - d) ≤ hammingNorm f := by
  induction n generalizing d with
  | zero =>
    have hd0 : d = 0 := Nat.eq_zero_of_le_zero hdn
    subst hd0
    rw [Nat.sub_self, pow_zero]
    exact Nat.one_le_iff_ne_zero.mpr (hammingNorm_pos_iff.mpr hf0).ne'
  | succ n ih =>
    rcases eq_or_lt_of_le hdn with rfl | hlt
    · rw [Nat.sub_self, pow_zero]
      exact Nat.one_le_iff_ne_zero.mpr (hammingNorm_pos_iff.mpr hf0).ne'
    · cases d with
      | zero =>
        have hconst : ∀ x, f x = 1 := by
          have hexp : ∀ x, f x = mlCoeff f ∅ := fun x ↦ by
            rw [mlExpansion f x]
            have : ∀ S : Finset (Fin (n + 1)), S ≠ ∅ → mlCoeff f S * mlMonomial S x = 0 := by
              intro S hS
              have hpos : 0 < S.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hS)
              rw [(mem_reedMuller_iff_mlCoeff.mp hf) S hpos, zero_mul]
            rw [Finset.sum_eq_single ∅ (fun S _ hS ↦ this S hS) (by simp)]
            simp [mlMonomial]
          have hne0 : mlCoeff f ∅ ≠ 0 := fun hc ↦ hf0 (by ext x; rw [hexp x, hc]; rfl)
          intro x
          rw [hexp x]
          exact (zmod2_eq_one_iff_ne_zero _).mpr hne0
        have hnorm : hammingNorm f = 2 ^ (n + 1) := by
          unfold hammingNorm
          have : (Finset.univ.filter fun x : Fin (n + 1) → ZMod 2 ↦ f x ≠ 0) = Finset.univ := by
            ext x; simp [hconst x]
          rw [this, Finset.card_univ, Fintype.card_fun, ZMod.card, Fintype.card_fin]
        rw [Nat.sub_zero, hnorm]
      | succ d =>
        have hdn' : d + 1 ≤ n := Nat.lt_succ_iff.mp hlt
        have hdle : d ≤ n := Nat.le_of_succ_le hdn'
        rw [hammingNorm_eq_add_slices f]
        by_cases hsum : slice0 f + slice1 f = 0
        · have heq : slice0 f = slice1 f := by
            ext x
            have hx := congrFun hsum x
            simp only [Pi.add_apply, Pi.zero_apply] at hx
            rcases zmod2_eq_zero_or_one (slice0 f x) with h0 | h0 <;>
              rcases zmod2_eq_zero_or_one (slice1 f x) with h1 | h1 <;>
              simp_all
          have h0ne : slice0 f ≠ 0 := by
            intro h0
            apply hf0
            ext x
            have hx : x = Fin.cons (x 0) (fun i ↦ x i.succ) := by
              ext j; refine Fin.cases (by simp) (fun i ↦ by simp) j
            rw [hx]
            rcases zmod2_eq_zero_or_one (x 0) with h | h
            · rw [h]; exact congrFun h0 _
            · rw [h]; exact congrFun (heq.symm.trans h0) _
          have hih := ih hdn' (slice0_mem_reedMuller hf) h0ne
          rw [← heq]
          have hexp : n + 1 - (d + 1) = (n - (d + 1)) + 1 := by omega
          rw [hexp, pow_succ]
          omega
        · have hih := ih hdle (slice0_add_slice1_mem_reedMuller hf) hsum
          have htri : hammingNorm (slice0 f + slice1 f) ≤
              hammingNorm (slice0 f) + hammingNorm (slice1 f) := by
            unfold hammingNorm
            calc (Finset.univ.filter fun x ↦ (slice0 f + slice1 f) x ≠ 0).card
                ≤ ((Finset.univ.filter fun x ↦ slice0 f x ≠ 0) ∪
                    (Finset.univ.filter fun x ↦ slice1 f x ≠ 0)).card := by
                  refine Finset.card_le_card fun x hx ↦ ?_
                  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Pi.add_apply,
                    Finset.mem_union] at hx ⊢
                  by_contra hboth
                  push Not at hboth
                  exact hx (by rw [hboth.1, hboth.2, add_zero])
              _ ≤ _ := Finset.card_union_le _ _
          have hexp : n + 1 - (d + 1) = n - d := by omega
          rw [hexp]
          exact hih.trans htri

/-! ### Duality and $(2^{d+1} - 1)$-wise evaluation surjectivity -/

private theorem sum_mul_compl_indicator_eq_mlCoeff {n : ℕ}
    (w : (Fin n → ZMod 2) → ZMod 2) (T : Finset (Fin n)) :
    (∑ x : Fin n → ZMod 2, w x * ∏ i ∈ Tᶜ, (1 + x i)) = mlCoeff w T := by
  have hprod : ∀ x : Fin n → ZMod 2,
      (∏ i ∈ Tᶜ, (1 + x i)) = if vecSupp x ⊆ T then 1 else 0 := by
    intro x
    by_cases h : vecSupp x ⊆ T
    · rw [ite_eq_left h]
      refine Finset.prod_eq_one fun i hi ↦ ?_
      have hiT : i ∉ T := Finset.mem_compl.mp hi
      have hx0 : x i = 0 := by
        rcases zmod2_eq_zero_or_one (x i) with h0 | h1
        · exact h0
        · exfalso; exact hiT (h (by simp [vecSupp, h1]))
      simp [hx0]
    · rw [ite_eq_right h]
      obtain ⟨i, hiSupp, hiT⟩ := Finset.not_subset.mp h
      have hx1 : x i = 1 := (Finset.mem_filter.mp hiSupp).2
      refine Finset.prod_eq_zero (Finset.mem_compl.mpr hiT) ?_
      rw [hx1]; decide
  simp_rw [hprod, mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  unfold mlCoeff
  refine Finset.sum_bij (fun x _ ↦ vecSupp x) ?_ ?_ ?_ ?_
  · intro x hx
    exact Finset.mem_powerset.mpr (Finset.mem_filter.mp hx).2
  · intro x₁ _ x₂ _ heq
    rw [← indVec_vecSupp x₁, ← indVec_vecSupp x₂, heq]
  · intro U hU
    refine ⟨indVec U, ?_, vecSupp_indVec U⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, vecSupp_indVec]
    exact Finset.mem_powerset.mp hU
  · intro x _
    rw [indVec_vecSupp]

/-- Evaluation of `Cslib.Code.reedMuller (ZMod 2) n d` on any set $S \subseteq \mathbb{F}_2^n$ of
cardinality strictly less than $2^{d + 1}$ is surjective onto $\mathbb{F}_2^S$. -/
theorem eval_surjective {d n : ℕ} (S : Finset (Fin n → ZMod 2)) (hS : S.card < 2 ^ (d + 1)) :
    Function.Surjective (fun (P : Cslib.Code.reedMuller (ZMod 2) n d) (x : S) ↦ P.1 x.1) := by
  by_cases hnd : n ≤ d
  · intro y
    refine ⟨⟨fun x ↦ if hx : x ∈ S then y ⟨x, hx⟩ else 0, mem_reedMuller_of_le hnd _⟩, ?_⟩
    ext ⟨x, hx⟩
    simp [hx]
  · have hdn : d < n := Nat.lt_of_not_ge hnd
    let ev : Cslib.Code.reedMuller (ZMod 2) n d →ₗ[ZMod 2] (S → ZMod 2) :=
      { toFun := fun P x ↦ P.1 x.1
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun _ _ ↦ rfl }
    change Function.Surjective ev
    rw [← LinearMap.range_eq_top]
    by_contra hne
    have hlt : LinearMap.range ev < ⊤ := lt_top_iff_ne_top.mpr hne
    obtain ⟨φ, hφ0, hφker⟩ := Submodule.exists_le_ker_of_lt_top (LinearMap.range ev) hlt
    let v : S → ZMod 2 := fun x ↦ φ (Pi.single x 1)
    have hφ_eq : ∀ y : S → ZMod 2, φ y = ∑ x : S, v x * y x := fun y ↦ by
      have hy : y = ∑ x : S, y x • Pi.single x (1 : ZMod 2) := by
        ext z; simp [Finset.sum_apply, Pi.single_apply]
      conv_lhs => rw [hy, map_sum]
      refine Finset.sum_congr rfl fun x _ ↦ ?_
      rw [map_smul, smul_eq_mul, mul_comm]
    let w : (Fin n → ZMod 2) → ZMod 2 := fun x ↦ if hx : x ∈ S then v ⟨x, hx⟩ else 0
    have hw_orth : ∀ P ∈ Cslib.Code.reedMuller (ZMod 2) n d,
        (∑ x : Fin n → ZMod 2, w x * P x) = 0 := by
      intro P hP
      have h1 : (∑ x : Fin n → ZMod 2, w x * P x) = ∑ x : S, v x * P x.1 := by
        symm
        calc ∑ x : S, v x * P x.1
            = ∑ x : S, w x.1 * P x.1 := Finset.sum_congr rfl fun x _ ↦ by simp [w, x.2]
          _ = ∑ x ∈ S, w x * P x := Finset.sum_coe_sort S (fun x ↦ w x * P x)
          _ = ∑ x : Fin n → ZMod 2, w x * P x := by
              refine Finset.sum_subset (Finset.subset_univ S) fun x _ hx ↦ ?_
              simp [w, hx]
      rw [h1]
      have h2 : (∑ x : S, v x * P x.1) = φ (ev ⟨P, hP⟩) := (hφ_eq (ev ⟨P, hP⟩)).symm
      rw [h2]
      exact hφker (LinearMap.mem_range_self ev ⟨P, hP⟩)
    have hw_rm : w ∈ Cslib.Code.reedMuller (ZMod 2) n (n - d - 1) := by
      rw [mem_reedMuller_iff_mlCoeff]
      intro T hT
      rw [← sum_mul_compl_indicator_eq_mlCoeff w T]
      have hPmem : (fun x : Fin n → ZMod 2 ↦ ∏ i ∈ Tᶜ, (1 + x i)) ∈
          Cslib.Code.reedMuller (ZMod 2) n d := by
        refine Cslib.Code.mem_reedMuller.mpr ⟨∏ i ∈ Tᶜ, (1 + MvPolynomial.X i), ?_, ?_⟩
        · refine (MvPolynomial.totalDegree_finsetProd _ _).trans ?_
          calc ∑ i ∈ Tᶜ, (1 + MvPolynomial.X i : MvPolynomial (Fin n) (ZMod 2)).totalDegree
              ≤ ∑ _i ∈ Tᶜ, 1 := Finset.sum_le_sum fun i _ ↦ by
                refine (MvPolynomial.totalDegree_add _ _).trans (max_le ?_ ?_)
                · simp
                · exact (MvPolynomial.totalDegree_X i).le
            _ = Tᶜ.card := by simp
            _ = n - T.card := by rw [Finset.card_compl, Fintype.card_fin]
            _ ≤ d := by omega
        · ext x; simp [map_prod]
      exact hw_orth _ hPmem
    have hw0 : w = 0 := by
      by_contra hwne
      have hwt := two_pow_sub_le_hammingNorm_of_mem_reedMuller (by omega : n - d - 1 ≤ n)
        hw_rm hwne
      have hsub : n - (n - d - 1) = d + 1 := by omega
      rw [hsub] at hwt
      have hleS : hammingNorm w ≤ S.card := by
        unfold hammingNorm
        refine Finset.card_le_card fun x hx ↦ ?_
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
        by_contra hxS
        exact hx (by simp [w, hxS])
      omega
    apply hφ0
    refine LinearMap.ext fun y ↦ ?_
    rw [hφ_eq y, LinearMap.zero_apply]
    refine Finset.sum_eq_zero fun x _ ↦ ?_
    have hvx : v x = 0 := by
      have := congrFun hw0 x.1
      simpa [w, x.2] using this
    simp [hvx]

end

end CslibFrontier.Code.BinaryReedMuller
