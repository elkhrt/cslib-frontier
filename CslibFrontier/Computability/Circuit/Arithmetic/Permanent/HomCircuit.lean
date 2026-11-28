module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.Determinant
public import CslibFrontier.Computability.Circuit.Arithmetic.VNP
public import CslibFrontier.Computability.Circuit.Arithmetic.ClauseSum
public import CslibFrontier.Computability.Circuit.Arithmetic.ComputedWithin
public import CslibFrontier.Computability.Circuit.Arithmetic.SubstMatrix
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
import CslibFrontier.Computability.Circuit.Arithmetic.Permanent.Projection
import CslibFrontier.Foundations.Data.Matrix.Permanent.Blocks
import CslibFrontier.Foundations.Data.Matrix.Permanent.Grid
import CslibFrontier.Foundations.Data.Matrix.Permanent.Relay
import Mathlib.Algebra.BigOperators.Fin

/-!
# Permanent Relay Elimination, Clause Sums, and Homogeneous Circuit Decomposition

Algebraic infrastructure for reducing arithmetic circuits to projections of the generic permanent:

1. **Affine-entry elimination (`exists_substMatrix_of_affine`)**: Repeated relay elimination
   reduces any `S × S` affine-entry matrix (`S ≥ 1`) to an `(S + S * S) × (S + S * S)`
   specialization matrix (`IsSubstMatrix`) with the same permanent.
2. **Universe-polymorphic clause-sum permanents (`isProjection_clauseSum_permanent`)**: Over any
   field `K` with `(2 : K) ≠ 0`, any non-degenerate clause sum over variables and constants is a
   projection of `(genericMatrix K (S + S * S)).permanent` for `S ≥ 3 * ∑ κ, (lits κ).length + 1`.
3. **Homogeneous circuit decomposition (`linCoeff`, `PTree`, `sum_pTree_eval`)**: Every wire of an
   arithmetic straight-line program admits a degree-independent linear-propagation table giving a
   binary multiplication-gate recurrence and binary parse-tree sum for homogeneous components.
-/

public section

namespace CslibFrontier.Computability.Circuit.Arithmetic.Permanent

open Cslib Cslib.Circuits Cslib.Circuits.Arithmetic MvPolynomial Finset

universe u

/-! ### Stage 1: Eliminating affine entries via relay vertices -/

section AffineToSubst

variable {K : Type u} [CommSemiring K] {n : ℕ}

/-- Adding one relay vertex replaces an affine entry `C a * X v + C b` at `(s, t)` by `C b` while
preserving the permanent. -/
private theorem exists_relay_step {m : ℕ} (hm : 1 ≤ m)
    (A : Matrix (Fin m) (Fin m) (MvPolynomial (Fin n) K))
    (s t : Fin m) (v : Fin n) (a b : K) (hst : A s t = C a * X v + C b) :
    ∃ A' : Matrix (Fin (m + 1)) (Fin (m + 1)) (MvPolynomial (Fin n) K),
      A'.permanent = A.permanent ∧
      (∀ i j : Fin m, A' i.castSucc j.castSucc = if i = s ∧ j = t then C b else A i j) ∧
      (∀ j : Fin m, IsSubstEntry (A' (Fin.last m) j.castSucc)) ∧
      (∀ i : Fin m, IsSubstEntry (A' i.castSucc (Fin.last m))) ∧
      IsSubstEntry (A' (Fin.last m) (Fin.last m)) := by
  obtain ⟨m', rfl⟩ := Nat.exists_eq_add_of_le' hm
  let A' : Matrix (Fin (m' + 2)) (Fin (m' + 2)) (MvPolynomial (Fin n) K) :=
    Matrix.of fun i j =>
      Fin.lastCases
        (Fin.lastCases (1 : MvPolynomial (Fin n) K)
          (fun j' => if j' = t then X v else 0) j)
        (fun i' =>
          Fin.lastCases (if i' = s then C a else 0)
            (fun j' => if i' = s ∧ j' = t then C b else A i' j') j)
        i
  have hll : A' (Fin.last (m' + 1)) (Fin.last (m' + 1)) = 1 := by simp [A']
  have hrow : ∀ j : Fin (m' + 1),
      A' (Fin.last (m' + 1)) j.castSucc = if j = t then X v else 0 := fun j => by
    simp [A']
  have hcol : ∀ i : Fin (m' + 1),
      A' i.castSucc (Fin.last (m' + 1)) = if i = s then C a else 0 := fun i => by
    simp [A']
  have hperm : A'.permanent = A.permanent := by
    rw [Matrix.permanent_eq_of_relay A' s t (C a) (X v) hll hrow hcol]
    congr 1
    ext i j
    simp only [Matrix.add_apply, Matrix.submatrix_apply, Matrix.of_apply, A',
      Fin.lastCases_castSucc]
    by_cases hij : i = s ∧ j = t
    · obtain ⟨rfl, rfl⟩ := hij
      simp [hst, add_comm]
    · simp [hij]
  refine ⟨A', hperm, fun i j => by simp [A'], fun j => ?_, fun i => ?_, ?_⟩
  · rw [hrow j]; split_ifs <;> simp
  · rw [hcol i]; split_ifs <;> simp
  · rw [hll]; exact .one

/-- Padding a matrix by a `1 × 1` identity corner preserves the permanent and adds only `0`/`1`
entries. -/
private theorem exists_pad_one_step {m : ℕ}
    (A : Matrix (Fin m) (Fin m) (MvPolynomial (Fin n) K)) :
    ∃ A' : Matrix (Fin (m + 1)) (Fin (m + 1)) (MvPolynomial (Fin n) K),
      A'.permanent = A.permanent ∧
      (∀ i j : Fin m, A' i.castSucc j.castSucc = A i j) ∧
      (∀ j : Fin m, IsSubstEntry (A' (Fin.last m) j.castSucc)) ∧
      (∀ i : Fin m, IsSubstEntry (A' i.castSucc (Fin.last m))) ∧
      IsSubstEntry (A' (Fin.last m) (Fin.last m)) := by
  let A' : Matrix (Fin (m + 1)) (Fin (m + 1)) (MvPolynomial (Fin n) K) :=
    Matrix.of fun i j =>
      Fin.lastCases (Fin.lastCases 1 (fun _ => 0) j)
        (fun i' => Fin.lastCases 0 (fun j' => A i' j') j) i
  have hcs : ∀ i' : Fin m, finSumFinEquiv.symm (i'.castSucc : Fin (m + 1)) = Sum.inl i' := by
    intro i'
    have : (i'.castSucc : Fin (m + 1)) = finSumFinEquiv (Sum.inl i') := by
      ext; simp [finSumFinEquiv_apply_left]
    rw [this, Equiv.symm_apply_apply]
  have hlast : finSumFinEquiv.symm (Fin.last m) = Sum.inr (0 : Fin 1) := by
    have : Fin.last m = finSumFinEquiv (Sum.inr (0 : Fin 1)) := by
      ext; simp [finSumFinEquiv_apply_right]
    rw [this, Equiv.symm_apply_apply]
  have hblk : A' = (Matrix.fromBlocks A 0 0 (1 : Matrix (Fin 1) (Fin 1) _)).submatrix
      finSumFinEquiv.symm finSumFinEquiv.symm := by
    ext i j
    refine Fin.lastCases ?_ ?_ i <;> refine Fin.lastCases ?_ ?_ j
    · simp [A', hlast]
    · intro j'; simp [A', hlast, hcs]
    · intro i'; simp [A', hlast, hcs]
    · intro i' j'; simp [A', hcs]
  have hperm : A'.permanent = A.permanent := by
    rw [hblk, Matrix.permanent_submatrix_equiv, Matrix.permanent_fromBlocks_zero,
      Matrix.permanent_one, mul_one]
  refine ⟨A', hperm, fun i j => by simp [A'], fun j => by simp [A'],
    fun i => by simp [A'], by simp [A']⟩

/-- Any `S × S` matrix (`S ≥ 1`) with affine entries (`IsAffine`) has the same permanent as an
`(S + S * S) × (S + S * S)` specialization matrix (`IsSubstMatrix`). -/
public theorem exists_substMatrix_of_affine {S : ℕ} (hS : 1 ≤ S)
    (M : Matrix (Fin S) (Fin S) (MvPolynomial (Fin n) K))
    (hM : ∀ i j, IsAffine (M i j)) :
    ∃ M' : Matrix (Fin (S + S * S)) (Fin (S + S * S)) (MvPolynomial (Fin n) K),
      IsSubstMatrix M' ∧ M'.permanent = M.permanent := by
  have hind : ∀ k ≤ S * S,
      ∃ A : Matrix (Fin (S + k)) (Fin (S + k)) (MvPolynomial (Fin n) K),
        A.permanent = M.permanent ∧
        (∀ i j : Fin (S + k),
          (∃ (hi : i.1 < S) (hj : j.1 < S),
            k ≤ (finProdFinEquiv (⟨i.1, hi⟩, ⟨j.1, hj⟩)).1) → IsAffine (A i j)) ∧
        (∀ i j : Fin (S + k),
          (∀ (hi : i.1 < S) (hj : j.1 < S),
            (finProdFinEquiv (⟨i.1, hi⟩, ⟨j.1, hj⟩)).1 < k) → IsSubstEntry (A i j)) := by
    intro k
    induction k with
    | zero =>
        intro _
        refine ⟨M, rfl, fun i j _ => hM i j, fun i j h => ?_⟩
        exact absurd (h i.2 j.2) (Nat.not_lt_zero _)
    | succ k ih =>
        intro hk
        obtain ⟨A, hAperm, hAaff, hAsub⟩ := ih (Nat.le_of_succ_le hk)
        let rc := finProdFinEquiv.symm ⟨k, hk⟩
        let s : Fin (S + k) := rc.1.castLE (Nat.le_add_right S k)
        let t : Fin (S + k) := rc.2.castLE (Nat.le_add_right S k)
        have hst_aff : IsAffine (A s t) := by
          refine hAaff s t ⟨rc.1.2, rc.2.2, ?_⟩
          have hfin : finProdFinEquiv (⟨s.1, rc.1.2⟩, ⟨t.1, rc.2.2⟩) = ⟨k, hk⟩ := by
            have : (⟨s.1, rc.1.2⟩, ⟨t.1, rc.2.2⟩) = rc := by ext <;> rfl
            rw [this, Equiv.apply_symm_apply]
          simp [hfin]
        have hstep : ∃ A' : Matrix (Fin (S + k + 1)) (Fin (S + k + 1)) (MvPolynomial (Fin n) K),
            A'.permanent = A.permanent ∧
            (∀ i j : Fin (S + k), (i ≠ s ∨ j ≠ t) → A' i.castSucc j.castSucc = A i j) ∧
            IsSubstEntry (A' s.castSucc t.castSucc) ∧
            (∀ j : Fin (S + k), IsSubstEntry (A' (Fin.last (S + k)) j.castSucc)) ∧
            (∀ i : Fin (S + k), IsSubstEntry (A' i.castSucc (Fin.last (S + k)))) ∧
            IsSubstEntry (A' (Fin.last (S + k)) (Fin.last (S + k))) := by
          rcases hst_aff with ⟨b, hb⟩ | ⟨v, a, b, hab⟩
          · obtain ⟨A', hp, htl, hr, hc, hll⟩ := exists_pad_one_step A
            refine ⟨A', hp, fun i j _ => htl i j, ?_, hr, hc, hll⟩
            rw [htl s t, hb]
            exact .C b
          · obtain ⟨A', hp, htl, hr, hc, hll⟩ :=
              exists_relay_step (by omega : 1 ≤ S + k) A s t v a b hab
            refine ⟨A', hp, fun i j hne => ?_, ?_, hr, hc, hll⟩
            · rw [htl i j]
              have : ¬ (i = s ∧ j = t) := by rintro ⟨rfl, rfl⟩; exact hne.elim (· rfl) (· rfl)
              simp [this]
            · rw [htl s t]
              simp
        obtain ⟨A', hA'p, hA'eq, hA'st, hA'r, hA'c, hA'll⟩ := hstep
        refine ⟨A', hA'p.trans hAperm, fun i j hge => ?_, fun i j hlt => ?_⟩
        · obtain ⟨hi, hj, hidx⟩ := hge
          have hi' : i.1 < S + k := by omega
          have hj' : j.1 < S + k := by omega
          let i₀ : Fin (S + k) := ⟨i.1, hi'⟩
          let j₀ : Fin (S + k) := ⟨j.1, hj'⟩
          have hieq : i = i₀.castSucc := Fin.ext rfl
          have hjeq : j = j₀.castSucc := Fin.ext rfl
          have hne : i₀ ≠ s ∨ j₀ ≠ t := by
            by_contra hall
            push Not at hall
            obtain ⟨hi₀, hj₀⟩ := hall
            have hfin : finProdFinEquiv (⟨i.1, hi⟩, ⟨j.1, hj⟩) = ⟨k, hk⟩ := by
              have h1 : i.1 = rc.1.1 := congrArg (fun x : Fin (S + k) => x.1) hi₀
              have h2 : j.1 = rc.2.1 := congrArg (fun x : Fin (S + k) => x.1) hj₀
              have : (⟨i.1, hi⟩, ⟨j.1, hj⟩) = rc := Prod.ext (Fin.ext h1) (Fin.ext h2)
              rw [this, Equiv.apply_symm_apply]
            simp only [hfin] at hidx
            omega
          rw [hieq, hjeq, hA'eq i₀ j₀ hne]
          exact hAaff i₀ j₀ ⟨hi, hj, Nat.le_of_succ_le hidx⟩
        · revert hlt
          refine Fin.lastCases ?_ ?_ i
          · refine Fin.lastCases (fun _ => hA'll) (fun j₀ _ => hA'r j₀) j
          · intro i₀
            refine Fin.lastCases (fun _ => hA'c i₀) (fun j₀ hlt => ?_) j
            by_cases hst_eq : i₀ = s ∧ j₀ = t
            · obtain ⟨rfl, rfl⟩ := hst_eq
              exact hA'st
            · have hne : i₀ ≠ s ∨ j₀ ≠ t := by tauto
              rw [hA'eq i₀ j₀ hne]
              refine hAsub i₀ j₀ fun hi hj => ?_
              have hlt' := hlt hi hj
              simp only [Fin.val_castSucc] at hlt'
              have hne_k : (finProdFinEquiv (⟨i₀.1, hi⟩, ⟨j₀.1, hj⟩)).1 ≠ k := by
                intro heq
                have heqv : finProdFinEquiv (⟨i₀.1, hi⟩, ⟨j₀.1, hj⟩) = ⟨k, hk⟩ := Fin.ext heq
                have hrc : (⟨i₀.1, hi⟩, ⟨j₀.1, hj⟩) = rc := by
                  simpa [rc] using congrArg finProdFinEquiv.symm heqv
                apply hst_eq
                constructor <;> ext
                · exact congrArg (fun p => p.1.1) hrc
                · exact congrArg (fun p => p.2.1) hrc
              omega
  obtain ⟨A, hAp, -, hAs⟩ := hind (S * S) le_rfl
  refine ⟨A, fun i j => hAs i j fun hi hj => (finProdFinEquiv (⟨i.1, hi⟩, ⟨j.1, hj⟩)).2, hAp⟩

end AffineToSubst

/-! ### Stage 2: Universe-polymorphic clause sums as permanent projections -/

section ClauseSumPermanent

variable {K : Type u} [Field K] {n : ℕ}

private theorem isAffine_of_mem_span_opt (o : Option (Fin n)) {P : MvPolynomial (Fin n) K}
    (h : P ∈ match o with
      | none => Submodule.span K {(1 : MvPolynomial (Fin n) K)}
      | some i => Submodule.span K {(X i : MvPolynomial (Fin n) K), 1}) :
    IsAffine P := by
  cases o with
  | none =>
      obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.1 h
      exact Or.inl ⟨b, by rw [smul_eq_C_mul, mul_one]⟩
  | some i =>
      obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.1 h
      exact Or.inr ⟨i, a, b, by rw [smul_eq_C_mul, smul_eq_C_mul, mul_one]⟩

/-- Universe-polymorphic clause-sum permanent theorem: over any field `K` with `2 ≠ 0`, any
non-degenerate clause sum over variables and constants is a projection of the generic permanent of
dimension `S + S * S`, where `S ≥ 3 * ∑ κ, (lits κ).length + 1`. -/
public theorem isProjection_clauseSum_permanent (h2 : (2 : K) ≠ 0)
    {V Θ : Type} [Fintype V] [DecidableEq V] [Fintype Θ]
    (lits : Θ → List (V × Bool)) (hne : ∀ κ, lits κ ≠ [])
    (hocc : ∀ b, ∃ κ, ∃ l ∈ lits κ, l.1 = b) (wt : Θ → MvPolynomial (Fin n) K)
    (hwt : ∀ κ, (∃ i, wt κ = X i) ∨ ∃ a, wt κ = C a)
    {S : ℕ} (hS : 3 * ∑ κ, (lits κ).length + 1 ≤ S) :
    IsProjection (clauseSum lits wt) (genericMatrix K (S + S * S)).permanent := by
  classical
  let N := Σ κ, Fin (lits κ).length
  let v : N → V := fun p => ((lits p.1).get p.2).1
  let W : N → Bool → Bool → MvPolynomial (Fin n) K := fun p x r =>
    if r then
      (if x = ((lits p.1).get p.2).2 then (if p.2.1 = 0 then wt p.1 - 1 else 1) else 0)
    else 1
  let affSp : Option (Fin n) → Submodule K (MvPolynomial (Fin n) K)
    | none => Submodule.span K {1}
    | some i => Submodule.span K {X i, 1}
  have hone : ∀ o, (1 : MvPolynomial (Fin n) K) ∈ affSp o := fun o => by
    cases o <;> exact Submodule.subset_span (by simp)
  let o : Θ → Option (Fin n) := fun κ => if h : ∃ i, wt κ = X i then some h.choose else none
  have hwt' : ∀ κ, wt κ ∈ affSp (o κ) := fun κ => by
    by_cases h : ∃ i, wt κ = X i
    · simp only [o, h, ↓reduceDIte, affSp]
      exact Submodule.subset_span (Set.mem_insert_iff.2 (.inl h.choose_spec))
    · obtain ⟨a, ha⟩ := (hwt κ).resolve_left h
      rw [ha]
      simpa [smul_eq_C_mul] using (affSp (o κ)).smul_mem a (hone (o κ))
  have hv : Function.Surjective v := fun b => by
    obtain ⟨κ, l, hl, rfl⟩ := hocc b
    obtain ⟨i, rfl⟩ := List.mem_iff_get.1 hl
    exact ⟨⟨κ, i⟩, rfl⟩
  have hw : Function.Surjective (fun p : N => p.1) := fun κ =>
    ⟨⟨κ, ⟨0, List.length_pos_iff.2 (hne κ)⟩⟩, rfl⟩
  have hW : ∀ p x r, W p x r ∈ affSp (o p.1) := fun p x r => by
    simp only [W]
    split_ifs
    · exact Submodule.sub_mem _ (hwt' _) (hone _)
    · exact hone _
    · exact Submodule.zero_mem _
    · exact hone _
  have hC2 : (C (2⁻¹ : K) : MvPolynomial (Fin n) K) * 2 = 1 := by
    rw [← map_ofNat C 2, ← map_mul, inv_mul_cancel₀ h2, map_one]
  have hcard : 3 * Fintype.card N ≤ S := by
    have : Fintype.card N = ∑ κ, (lits κ).length := by simp [N]
    omega
  obtain ⟨M, hM, hMp⟩ := Matrix.exists_permanent_eq_gridSum (C (2⁻¹ : K)) hC2 v
    (fun p : N => p.1) hv hw W hcard
  have hMaff : ∀ i j, IsAffine (M i j) := fun i j => by
    rcases hM i j with h | ⟨κ, h⟩
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
      rcases h with h | h | h | h | h
      · exact Or.inl ⟨0, h.trans C_0.symm⟩
      · exact Or.inl ⟨1, h.trans C_1.symm⟩
      · exact Or.inl ⟨-1, h.trans (by rw [map_neg, C_1])⟩
      · exact Or.inl ⟨2⁻¹, h⟩
      · exact Or.inl ⟨-2⁻¹, h.trans (map_neg C _).symm⟩
    · refine isAffine_of_mem_span_opt (o κ)
        ((AddSubmonoid.closure_le (S := (affSp (o κ)).toAddSubmonoid)).2 ?_ h)
      rintro _ ⟨p, x, r, rfl, rfl⟩
      exact hW p x r
  have hgrid : (∑ x : V → Bool, ∑ r : Θ → Bool, ∏ p : N, W p (x (v p)) (r p.1)) =
      clauseSum lits wt := by
    refine Finset.sum_congr rfl fun x _ => ?_
    have hprod (r : Θ → Bool) :
        ∏ p : N, W p (x (v p)) (r p.1) =
          ∏ κ, ∏ i : Fin (lits κ).length, W ⟨κ, i⟩ (x (v ⟨κ, i⟩)) (r κ) :=
      Fintype.prod_sigma _
    simp only [hprod]
    rw [← Fintype.prod_sum fun κ b =>
      ∏ i : Fin (lits κ).length, W ⟨κ, i⟩ (x (v ⟨κ, i⟩)) b]
    refine Finset.prod_congr rfl fun κ _ => ?_
    rw [Fintype.sum_bool]
    simp only [W, Bool.false_eq_true, ↓reduceIte, Finset.prod_const_one]
    by_cases hall : ∀ l ∈ lits κ, x l.1 = l.2
    · rw [ite_eq_left hall]
      simp only [v, fun i => hall _ (List.get_mem (lits κ) i), ↓reduceIte]
      rw [Finset.prod_eq_single (⟨0, List.length_pos_iff.2 (hne κ)⟩ : Fin (lits κ).length)]
      · simp
      · intro i _ hi
        exact ite_eq_right fun h => hi (Fin.ext h)
      · simp
    · rw [ite_eq_right hall]
      push Not at hall
      obtain ⟨l, hl, hne'⟩ := hall
      obtain ⟨i, rfl⟩ := List.mem_iff_get.1 hl
      rw [Finset.prod_eq_zero (mem_univ i) (ite_eq_right hne'), zero_add]
  obtain ⟨M', hM'sub, hM'p⟩ := exists_substMatrix_of_affine (by omega : 1 ≤ S) M hMaff
  have hproj := hM'sub.isProjection_permanent
  rw [Fintype.card_fin, hM'p, hMp, hgrid] at hproj
  exact hproj

end ClauseSumPermanent

/-! ### Stage 3: Homogeneous circuit decomposition and binary parse trees -/

section HomCircuit

variable {K : Type u} [CommSemiring K]

/-- Homogeneous component of a product as a convolution of homogeneous components. -/
private theorem homogeneousComponent_mul_conv {σ : Type*} (k : ℕ) (P Q : MvPolynomial σ K) :
    homogeneousComponent k (P * Q) =
      ∑ a ∈ Finset.range (k + 1), homogeneousComponent a P * homogeneousComponent (k - a) Q := by
  classical
  ext e
  rw [coeff_homogeneousComponent, coeff_sum]
  simp_rw [coeff_mul]
  by_cases he : e.degree = k
  · rw [ite_eq_left he]
    calc ∑ x ∈ Finset.antidiagonal e, P.coeff x.1 * Q.coeff x.2
        = ∑ x ∈ Finset.antidiagonal e,
            ∑ a ∈ Finset.range (k + 1),
              (homogeneousComponent a P).coeff x.1 *
                (homogeneousComponent (k - a) Q).coeff x.2 := by
          refine Finset.sum_congr rfl fun x hx => ?_
          have hdeg : x.1.degree + x.2.degree = k := by
            rw [← he, ← Finset.mem_antidiagonal.1 hx, map_add]
          rw [Finset.sum_eq_single x.1.degree]
          · simp [coeff_homogeneousComponent, show k - x.1.degree = x.2.degree by omega]
          · intro a _ ha
            simp [coeff_homogeneousComponent, Ne.symm ha]
          · intro hmem
            exact absurd (Finset.mem_range.2 (by omega)) hmem
      _ = ∑ a ∈ Finset.range (k + 1), ∑ x ∈ Finset.antidiagonal e,
            (homogeneousComponent a P).coeff x.1 *
              (homogeneousComponent (k - a) Q).coeff x.2 :=
          Finset.sum_comm
  · rw [ite_eq_right he]
    symm
    refine Finset.sum_eq_zero fun a ha => Finset.sum_eq_zero fun x hx => ?_
    simp only [coeff_homogeneousComponent]
    split_ifs with h1 h2
    · exfalso
      have hdeg : e.degree = x.1.degree + x.2.degree := by
        rw [← Finset.mem_antidiagonal.1 hx, map_add]
      have ha' := Finset.mem_range.1 ha
      omega
    · simp
    · simp
    · simp

/-- The pair of input wires of a line if it is a `.mul` gate, and `none` otherwise. -/
@[expose] public def mulWires {N s : ℕ} : Line (arithSignature K) N s →
    Option (Wire N s × Wire N s)
  | ⟨.mul, ws⟩ => some (ws 0, ws 1)
  | ⟨.add, _⟩ => none
  | ⟨.const _, _⟩ => none

omit [CommSemiring K] in
private theorem mulWires_mapWires {N s s' : ℕ} (L : Line (arithSignature K) N s)
    (f : Wire N s → Wire N s') :
    mulWires (L.mapWires f) = (mulWires L).map (Prod.map f f) := by
  obtain ⟨op, ws⟩ := L
  cases op <;> rfl

/-- The formal polynomial carried by wire `w` of an arithmetic program `p`. -/
@[expose] public noncomputable def wirePoly {N s : ℕ} (p : Program (arithSignature K) N s)
    (w : Wire N s) : MvPolynomial (Fin N) K :=
  p.trace (arithInterpretationWith K C) X w

/-- The constant term (evaluation at `0`) of wire `w` of an arithmetic program `p`. -/
@[expose] public def wireConst {N s : ℕ} (p : Program (arithSignature K) N s) (w : Wire N s) : K :=
  p.trace (arithInterpretation K) 0 w

/-- Degree-0 homogeneous component of `wirePoly p w` is `C (wireConst p w)`. -/
public theorem homogeneousComponent_zero_wirePoly {N s : ℕ} (p : Program (arithSignature K) N s)
    (w : Wire N s) :
    homogeneousComponent 0 (wirePoly p w) = C (wireConst p w) := by
  rw [homogeneousComponent_zero, wirePoly, wireConst]
  congr 1
  have hev : (p.trace (arithInterpretationWith K C) X w).coeff 0 =
      MvPolynomial.eval 0 (p.trace (arithInterpretationWith K C) X w) := by
    rw [MvPolynomial.eval_zero, MvPolynomial.constantCoeff_eq]
  rw [hev]
  let h : Homomorphism (arithInterpretationWith K (C : K → MvPolynomial (Fin N) K))
      (arithInterpretation K) :=
    ⟨MvPolynomial.eval 0, fun op args => by
      cases op <;> simp [arithInterpretationWith, arithInterpretation]⟩
  have hcomp : (MvPolynomial.eval (0 : Fin N → K) ∘ (X : Fin N → MvPolynomial (Fin N) K)) = 0 := by
    funext i; simp
  have htr := congrFun (p.map_trace h X) w
  dsimp only [h, Function.comp_apply] at htr
  rwa [hcomp] at htr

/-- Scalar linear-propagation table `linCoeff p w z` giving the weight with which source wire `z`
contributes to homogeneous components of degree `≥ 1` at wire `w`. -/
@[expose] public def linCoeff {N : ℕ} :
    ∀ {s : ℕ}, Program (arithSignature K) N s → Wire N s → Wire N s → K
  | _, .empty, .input i, .input j => if i = j then 1 else 0
  | _, .empty, .gate g, _ => Fin.elim0 g
  | _, .empty, _, .gate g => Fin.elim0 g
  | _ + 1, .gate q ⟨op, ws⟩, w, z =>
      Wire.lastCases
        (Wire.lastCases
          (match op with | .mul => 1 | _ => 0)
          (fun z' =>
            match op, ws with
            | .const _, _ => 0
            | .add, ws => linCoeff q (ws 0) z' + linCoeff q (ws 1) z'
            | .mul, ws =>
                wireConst q (ws 0) * linCoeff q (ws 1) z' +
                  wireConst q (ws 1) * linCoeff q (ws 0) z')
          z)
        (fun w' => Wire.lastCases 0 (fun z' => linCoeff q w' z') z)
        w

/-- Degree-`d` bilinear multiplication-gate source term. -/
private noncomputable def mulSplit {N s : ℕ} (p : Program (arithSignature K) N s)
    (g : Fin s) (d : ℕ) : MvPolynomial (Fin N) K :=
  match mulWires (p.lines g) with
  | some (u, v) =>
      ∑ a ∈ Finset.Ioo 0 d,
        homogeneousComponent a (wirePoly p u) * homogeneousComponent (d - a) (wirePoly p v)
  | none => 0

private theorem mulSplit_gate_castSucc {N s : ℕ} (q : Program (arithSignature K) N s)
    (line : Line (arithSignature K) N s) (g : Fin s) (d : ℕ) :
    mulSplit (q.gate line) g.castSucc d = mulSplit q g d := by
  unfold mulSplit
  rw [Program.lines_gate_castSucc, mulWires_mapWires]
  cases mulWires (q.lines g) with
  | none => rfl
  | some uv =>
      obtain ⟨u, v⟩ := uv
      simp only [Option.map_some, Prod.map_apply, Wire.Renaming.castSucc_apply, wirePoly,
        Program.trace_gate_castSucc]

private theorem mulSplit_gate_last {N s : ℕ} (q : Program (arithSignature K) N s)
    (line : Line (arithSignature K) N s) (d : ℕ) :
    mulSplit (q.gate line) (Fin.last s) d =
      match mulWires line with
      | some (u, v) =>
          ∑ a ∈ Finset.Ioo 0 d,
            homogeneousComponent a (wirePoly q u) * homogeneousComponent (d - a) (wirePoly q v)
      | none => 0 := by
  unfold mulSplit
  rw [Program.lines_gate_last, mulWires_mapWires]
  cases mulWires line with
  | none => rfl
  | some uv =>
      obtain ⟨u, v⟩ := uv
      simp only [Option.map_some, Prod.map_apply, Wire.Renaming.castSucc_apply, wirePoly,
        Program.trace_gate_castSucc]

private theorem sum_range_succ_succ {M : Type*} [AddCommMonoid M] (k : ℕ) (f : ℕ → M) :
    ∑ a ∈ Finset.range (k + 2), f a = f 0 + f (k + 1) + ∑ a ∈ Finset.Ioo 0 (k + 1), f a := by
  have h1 : Finset.range (k + 2) = insert (k + 1) (Finset.range (k + 1)) := by
    rw [Finset.range_add_one]
  rw [h1, Finset.sum_insert (Finset.notMem_range_self),
    Finset.sum_range_succ', add_comm (f (k + 1))]
  have h2 : ∑ a ∈ Finset.range k, f (a + 1) = ∑ a ∈ Finset.Ioo 0 (k + 1), f a := by
    refine Finset.sum_bij (fun a _ => a + 1) ?_ ?_ ?_ ?_
    · intro a ha; simp only [Finset.mem_range] at ha; simp only [Finset.mem_Ioo]; omega
    · intro a₁ _ a₂ _ h; omega
    · intro b hb
      simp only [Finset.mem_Ioo] at hb
      exact ⟨b - 1, Finset.mem_range.2 (by omega), by omega⟩
    · intro _ _; rfl
  rw [h2]
  abel

/-- **Homogeneous circuit decomposition**: for every degree `k + 1 ≥ 1` and every wire `w`, the
homogeneous component of degree `k + 1` of `wirePoly p w` obeys a pure binary multiplication-gate
recurrence with scalar coefficients `linCoeff p w z` independent of `k`. -/
private theorem homogeneousComponent_wirePoly_succ {N s : ℕ}
    (p : Program (arithSignature K) N s) (k : ℕ) (w : Wire N s) :
    homogeneousComponent (k + 1) (wirePoly p w) =
      (if k = 0 then ∑ i : Fin N, C (linCoeff p w (.input i)) * X i else 0) +
      ∑ g : Fin s, C (linCoeff p w (.gate g)) * mulSplit p g (k + 1) := by
  induction p with
  | empty =>
      cases w with
      | input i =>
          simp only [wirePoly, Program.trace_input, Finset.univ_eq_empty, Finset.sum_empty,
            add_zero]
          by_cases hk : k = 0
          · subst hk
            have h1 : homogeneousComponent 1 (X i : MvPolynomial (Fin N) K) = X i :=
              homogeneousComponent_eq_self (isHomogeneous_X K i)
            rw [h1, ite_eq_left rfl]
            rw [Finset.sum_eq_single i]
            · simp [linCoeff]
            · intro j _ hj; simp [linCoeff, Ne.symm hj]
            · intro h; exact absurd (Finset.mem_univ i) h
          · rw [ite_eq_right hk, homogeneousComponent_of_mem (isHomogeneous_X K i)]
            exact ite_eq_right (by omega)
      | gate g => exact Fin.elim0 g
  | @gate t q line ih =>
      refine Wire.lastCases ?_ ?_ w
      · have hval : wirePoly (q.gate line) (.gate (Fin.last t)) =
            line.eval (arithInterpretationWith K C) X
              (q.eval (arithInterpretationWith K C) X) := by
          simp [wirePoly, Program.eval_gate_last]
        rw [hval, Line.eval, Fin.sum_univ_castSucc]
        simp_rw [mulSplit_gate_castSucc]
        rw [mulSplit_gate_last]
        obtain ⟨op, ws⟩ := line
        cases op with
        | const a =>
            simp only [arithInterpretationWith_const, linCoeff, Wire.lastCases, Fin.lastCases_last,
              Fin.lastCases_castSucc, mulWires, map_zero, zero_mul, Finset.sum_const_zero,
              add_zero, ite_self]
            rw [homogeneousComponent_of_mem (isHomogeneous_C (Fin N) a)]
            exact ite_eq_right (Nat.succ_ne_zero k)
        | add =>
            have hadd : arithInterpretationWith K C .add (Wire.elim X _ ∘ ws) =
                wirePoly q (ws 0) + wirePoly q (ws 1) := rfl
            rw [hadd, map_add, ih (ws 0), ih (ws 1)]
            simp only [linCoeff, Wire.lastCases, Fin.lastCases_last, Fin.lastCases_castSucc,
              mulWires, map_add, add_mul, map_zero, zero_mul, add_zero, Finset.sum_add_distrib]
            by_cases hk : k = 0
            · simp only [hk, ↓reduceIte]; abel
            · simp only [hk, ↓reduceIte, zero_add]
        | mul =>
            have hmul : arithInterpretationWith K C .mul (Wire.elim X _ ∘ ws) =
                wirePoly q (ws 0) * wirePoly q (ws 1) := rfl
            rw [hmul, homogeneousComponent_mul_conv, sum_range_succ_succ]
            simp only [Nat.sub_zero, Nat.sub_self]
            rw [homogeneousComponent_zero_wirePoly, homogeneousComponent_zero_wirePoly,
              ih (ws 0), ih (ws 1)]
            simp only [linCoeff, Wire.lastCases, Fin.lastCases_last, Fin.lastCases_castSucc,
              mulWires, map_add, map_mul, map_one, one_mul, add_mul, mul_add, Finset.mul_sum,
              Finset.sum_add_distrib]
            have hcomm :
                C (wireConst q (ws 0)) * (∑ i : Fin N, C (linCoeff q (ws 1) (.input i)) * X i) +
                (∑ i : Fin N, C (linCoeff q (ws 0) (.input i)) * X i) * C (wireConst q (ws 1)) =
                (∑ i : Fin N, C (wireConst q (ws 0)) * C (linCoeff q (ws 1) (.input i)) * X i) +
                (∑ i : Fin N, C (wireConst q (ws 1)) * C (linCoeff q (ws 0) (.input i)) * X i) := by
              rw [Finset.mul_sum, Finset.sum_mul]
              congr 1
              · refine Finset.sum_congr rfl fun i _ => by ring
              · refine Finset.sum_congr rfl fun i _ => by ring
            have hcommg :
                (∑ g : Fin t, C (wireConst q (ws 0)) *
                  (C (linCoeff q (ws 1) (.gate g)) * mulSplit q g (k + 1))) +
                (∑ g : Fin t, C (linCoeff q (ws 0) (.gate g)) * mulSplit q g (k + 1)) *
                  C (wireConst q (ws 1)) =
                (∑ g : Fin t, C (wireConst q (ws 0)) * C (linCoeff q (ws 1) (.gate g)) *
                  mulSplit q g (k + 1)) +
                (∑ g : Fin t, C (wireConst q (ws 1)) * C (linCoeff q (ws 0) (.gate g)) *
                  mulSplit q g (k + 1)) := by
              rw [Finset.sum_mul]
              congr 1
              · refine Finset.sum_congr rfl fun g _ => by ring
              · refine Finset.sum_congr rfl fun g _ => by ring
            by_cases hk : k = 0
            · subst hk
              simp only [↓reduceIte]
              calc
                C (wireConst q (ws 0)) * ∑ i : Fin N, C (linCoeff q (ws 1) (.input i)) * X i +
                    ∑ g : Fin t, C (wireConst q (ws 0)) *
                      (C (linCoeff q (ws 1) (.gate g)) * mulSplit q g 1) +
                  ((∑ i : Fin N, C (linCoeff q (ws 0) (.input i)) * X i) *
                      C (wireConst q (ws 1)) +
                    (∑ g : Fin t, C (linCoeff q (ws 0) (.gate g)) * mulSplit q g 1) *
                      C (wireConst q (ws 1))) +
                  ∑ a ∈ Finset.Ioo 0 1,
                    homogeneousComponent a (wirePoly q (ws 0)) *
                      homogeneousComponent (1 - a) (wirePoly q (ws 1))
                _ = (C (wireConst q (ws 0)) * ∑ i : Fin N, C (linCoeff q (ws 1) (.input i)) * X i +
                      (∑ i : Fin N, C (linCoeff q (ws 0) (.input i)) * X i) *
                        C (wireConst q (ws 1))) +
                    ((∑ g : Fin t, C (wireConst q (ws 0)) *
                        (C (linCoeff q (ws 1) (.gate g)) * mulSplit q g 1)) +
                      (∑ g : Fin t, C (linCoeff q (ws 0) (.gate g)) * mulSplit q g 1) *
                        C (wireConst q (ws 1))) +
                    ∑ a ∈ Finset.Ioo 0 1,
                      homogeneousComponent a (wirePoly q (ws 0)) *
                        homogeneousComponent (1 - a) (wirePoly q (ws 1)) := by abel
                _ = _ := by rw [hcomm, hcommg]; abel
            · simp only [hk, ↓reduceIte, mul_zero, zero_mul, zero_add]
              rw [hcommg]
      · intro w'
        have htr : wirePoly (q.gate line) w'.castSucc = wirePoly q w' := by
          simp [wirePoly, Program.trace_gate_castSucc]
        rw [htr, ih w', Fin.sum_univ_castSucc]
        simp_rw [mulSplit_gate_castSucc]
        obtain ⟨op, ws⟩ := line
        have hlc_in : ∀ i : Fin N, linCoeff (q.gate ⟨op, ws⟩) w'.castSucc (.input i) =
            linCoeff q w' (.input i) := fun i => by
          cases w' <;> simp [linCoeff, Wire.lastCases]
        have hlc_g : ∀ g : Fin t, linCoeff (q.gate ⟨op, ws⟩) w'.castSucc (.gate g.castSucc) =
            linCoeff q w' (.gate g) := fun g => by
          cases w' <;> simp [linCoeff, Wire.lastCases]
        have hlc_last : linCoeff (q.gate ⟨op, ws⟩) w'.castSucc (.gate (Fin.last t)) = 0 := by
          cases w' <;> simp [linCoeff, Wire.lastCases]
        simp only [hlc_in, hlc_g, hlc_last, map_zero, zero_mul, add_zero]

/-- Binary parse trees of degree `k + 1` over `N` variables and `s` gates. -/
public inductive PTree (N s : ℕ) : ℕ → Type
  /-- Degree-1 leaf selecting input variable `j`. -/
  | leaf (j : Fin N) : PTree N s 0
  /-- Internal multiplication node splitting degree `k + 2` into `a + 1` and `k - a + 1`. -/
  | node (g : Fin s) {k : ℕ} (a : Fin (k + 1))
      (L : PTree N s a.1) (R : PTree N s (k - a.1)) : PTree N s (k + 1)
  deriving DecidableEq

private def pTreeZeroEquiv (N s : ℕ) : PTree N s 0 ≃ Fin N where
  toFun | .leaf j => j
  invFun j := .leaf j
  left_inv t := by cases t; rfl
  right_inv _ := rfl

private def pTreeSuccEquiv (N s k : ℕ) :
    PTree N s (k + 1) ≃ Fin s × Σ a : Fin (k + 1), PTree N s a.1 × PTree N s (k - a.1) where
  toFun | .node g a L R => (g, ⟨a, L, R⟩)
  invFun p := .node p.1 p.2.1 p.2.2.1 p.2.2.2
  left_inv t := by cases t; rfl
  right_inv _ := rfl

/-- Recursive `Fintype` construction for `PTree N s k`. -/
public def pTreeFintype (N s : ℕ) : ∀ k : ℕ, Fintype (PTree N s k)
  | 0 => Fintype.ofEquiv _ (pTreeZeroEquiv N s).symm
  | k + 1 =>
      let _ : ∀ a : Fin (k + 1), Fintype (PTree N s a.1) := fun a => pTreeFintype N s a.1
      let _ : ∀ a : Fin (k + 1), Fintype (PTree N s (k - a.1)) :=
        fun a => pTreeFintype N s (k - a.1)
      Fintype.ofEquiv _ (pTreeSuccEquiv N s k).symm

/-- `Fintype` instance for `PTree N s k`. -/
public instance instFintypePTree (N s k : ℕ) : Fintype (PTree N s k) := pTreeFintype N s k

/-- Whether gate `g` of `p` is a multiplication gate. -/
@[expose] public def isMulGate {N s : ℕ} (p : Program (arithSignature K) N s) (g : Fin s) : Bool :=
  (mulWires (p.lines g)).isSome

/-- Left input wire of a multiplication gate `g`, or `none`. -/
@[expose] public def mulLeftWire {N s : ℕ} (p : Program (arithSignature K) N s) (g : Fin s) :
    Option (Wire N s) :=
  (mulWires (p.lines g)).map Prod.fst

/-- Right input wire of a multiplication gate `g`, or `none`. -/
@[expose] public def mulRightWire {N s : ℕ} (p : Program (arithSignature K) N s) (g : Fin s) :
    Option (Wire N s) :=
  (mulWires (p.lines g)).map Prod.snd

omit [CommSemiring K] in
/-- Characterization of `isMulGate` via `mulWires`. -/
public theorem isMulGate_eq_isSome {N s : ℕ} (p : Program (arithSignature K) N s) (g : Fin s) :
    isMulGate p g = (mulWires (p.lines g)).isSome := rfl

omit [CommSemiring K] in
/-- Characterization of `mulLeftWire` via `mulWires`. -/
public theorem mulLeftWire_eq_map {N s : ℕ} (p : Program (arithSignature K) N s) (g : Fin s) :
    mulLeftWire p g = (mulWires (p.lines g)).map Prod.fst := rfl

omit [CommSemiring K] in
/-- Characterization of `mulRightWire` via `mulWires`. -/
public theorem mulRightWire_eq_map {N s : ℕ} (p : Program (arithSignature K) N s) (g : Fin s) :
    mulRightWire p g = (mulWires (p.lines g)).map Prod.snd := rfl

/-- Value of variable `j : Fin (n + m)` under `booleanAssignment e`. -/
@[expose] public noncomputable def varVal {n m : ℕ} (e : Fin m → Bool) (j : Fin (n + m)) :
    MvPolynomial (Fin n) K :=
  Sum.elim X (fun a => C a) (booleanAssignment e j)

/-- `varVal` on a primary input variable `Fin.castAdd m i` is `X i`. -/
@[simp] public theorem varVal_castAdd {n m : ℕ} (e : Fin m → Bool) (i : Fin n) :
    varVal (K := K) e (Fin.castAdd m i) = X i := by
  simp [varVal, booleanAssignment]

/-- `varVal` on a Boolean summation variable `Fin.natAdd n b` is `1` when `e b = true` and `0`
otherwise. -/
@[simp] public theorem varVal_natAdd {n m : ℕ} (e : Fin m → Bool) (b : Fin m) :
    varVal (K := K) e (Fin.natAdd n b) = if e b then 1 else 0 := by
  cases hb : e b <;> simp [varVal, booleanAssignment, hb]

/-- Whether a `PTree` uses only multiplication gates and active Boolean variables under `e`. -/
@[expose] public def PTree.IsLegal {n m s : ℕ} (p : Program (arithSignature K) (n + m) s)
    (e : Fin m → Bool) : ∀ {k : ℕ}, PTree (n + m) s k → Prop
  | 0, .leaf j => ∀ b : Fin m, j = Fin.natAdd n b → e b = true
  | _ + 1, .node g _ L R => isMulGate p g = true ∧ L.IsLegal p e ∧ R.IsLegal p e

/-- Evaluate a `PTree` rooted at wire `w` under Boolean assignment `e`. -/
@[expose] public noncomputable def PTree.eval {n m s : ℕ}
    (p : Program (arithSignature K) (n + m) s) (e : Fin m → Bool) :
    ∀ {k : ℕ}, Wire (n + m) s → PTree (n + m) s k → MvPolynomial (Fin n) K
  | 0, w, .leaf j => C (linCoeff p w (.input j)) * varVal e j
  | _ + 1, w, .node g _ L R =>
      match mulWires (p.lines g) with
      | some (u, v) => C (linCoeff p w (.gate g)) * L.eval p e u * R.eval p e v
      | none => 0

/-- Evaluation of a leaf parse tree. -/
@[simp] public theorem PTree.eval_leaf {n m s : ℕ}
    (p : Program (arithSignature K) (n + m) s) (e : Fin m → Bool) (w : Wire (n + m) s)
    (j : Fin (n + m)) :
    (PTree.leaf (s := s) j).eval p e w = C (linCoeff p w (.input j)) * varVal e j := rfl

/-- Evaluation of an internal node parse tree. -/
@[simp] public theorem PTree.eval_node {n m s k : ℕ}
    (p : Program (arithSignature K) (n + m) s) (e : Fin m → Bool) (w : Wire (n + m) s)
    (g : Fin s) (a : Fin (k + 1)) (L : PTree (n + m) s a.1) (R : PTree (n + m) s (k - a.1)) :
    (PTree.node g a L R).eval p e w =
      match mulWires (p.lines g) with
      | some (u, v) => C (linCoeff p w (.gate g)) * L.eval p e u * R.eval p e v
      | none => 0 := rfl

/-- Illegal parse trees evaluate to `0`. -/
public theorem PTree.eval_eq_zero_of_not_isLegal {n m s : ℕ}
    (p : Program (arithSignature K) (n + m) s) (e : Fin m → Bool) {k : ℕ}
    (w : Wire (n + m) s) (T : PTree (n + m) s k) (h : ¬ T.IsLegal p e) :
    T.eval p e w = 0 := by
  induction T generalizing w with
  | leaf j =>
      simp only [PTree.IsLegal, not_forall] at h
      obtain ⟨b, rfl, hb⟩ := h
      have hbf : e b = false := Bool.eq_false_iff.2 hb
      simp [PTree.eval, varVal, booleanAssignment, hbf]
  | node g a L R ihL ihR =>
      simp only [PTree.IsLegal, not_and_or] at h
      cases hmw : mulWires (p.lines g) with
      | none => simp [hmw]
      | some uv =>
          have hmul : isMulGate p g = true := by simp [isMulGate, hmw]
          simp only [PTree.eval, hmw]
          rcases h with h1 | h2 | h3
          · exact absurd hmul h1
          · rw [ihL _ h2, mul_zero, zero_mul]
          · rw [ihR _ h3, mul_zero]

/-- Sum of `PTree.eval` over all degree-`(k + 1)` parse trees equals the projected homogeneous
component of degree `k + 1`. -/
public theorem sum_pTree_eval {n m s : ℕ} (p : Program (arithSignature K) (n + m) s)
    (e : Fin m → Bool) :
    ∀ k : ℕ, ∀ w : Wire (n + m) s,
      ∑ T : PTree (n + m) s k, T.eval p e w =
        projection (booleanAssignment e) (homogeneousComponent (k + 1) (wirePoly p w)) := by
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
      intro w
      rw [homogeneousComponent_wirePoly_succ]
      cases k with
      | zero =>
          have hIoo : Finset.Ioo 0 1 = ∅ := by decide
          have hms : ∀ g : Fin s, mulSplit p g 1 = 0 := fun g => by
            unfold mulSplit
            cases mulWires (p.lines g) <;> simp [hIoo]
          simp only [↓reduceIte, hms, mul_zero, Finset.sum_const_zero, add_zero, map_sum, map_mul,
            projection_C, projection_X]
          rw [← (pTreeZeroEquiv (n + m) s).symm.sum_comp]
          rfl
      | succ k =>
          simp only [Nat.succ_ne_zero, ↓reduceIte, zero_add, map_sum, map_mul, projection_C]
          rw [← (pTreeSuccEquiv (n + m) s k).symm.sum_comp, Fintype.sum_prod_type]
          refine Finset.sum_congr rfl fun g _ => ?_
          unfold mulSplit
          cases hmw : mulWires (p.lines g) with
          | none =>
              simp only [map_zero, mul_zero]
              refine Finset.sum_eq_zero fun x _ => ?_
              rcases x with ⟨a, L, R⟩
              change (PTree.node g a L R).eval p e w = 0
              simp [hmw]
          | some uv =>
              obtain ⟨u, v⟩ := uv
              rw [Fintype.sum_sigma]
              have hterm :
                  ∀ (a : Fin (k + 1)) (LR : PTree (n + m) s a.1 × PTree (n + m) s (k - a.1)),
                  ((pTreeSuccEquiv (n + m) s k).symm (g, ⟨a, LR⟩)).eval p e w =
                    C (linCoeff p w (.gate g)) * (LR.1.eval p e u * LR.2.eval p e v) := by
                rintro a ⟨L, R⟩
                change (match mulWires (p.lines g) with
                  | some (u', v') => C (linCoeff p w (.gate g)) * L.eval p e u' * R.eval p e v'
                  | none => 0) = _
                rw [hmw]
                exact mul_assoc _ _ _
              simp_rw [hterm, ← Finset.mul_sum, Fintype.sum_prod_type, ← Finset.mul_sum,
                ← Finset.sum_mul]
              congr 1
              rw [map_sum]
              refine Finset.sum_bij (fun a _ => a.1 + 1) ?_ ?_ ?_ ?_
              · intro a _; simp only [Finset.mem_Ioo]; omega
              · intro a₁ _ a₂ _ h; exact Fin.ext (by omega)
              · intro b hb
                simp only [Finset.mem_Ioo] at hb
                exact ⟨⟨b - 1, by omega⟩, Finset.mem_univ _, by dsimp; omega⟩
              · intro a _
                have hsub : k + 2 - (a.1 + 1) = (k - a.1) + 1 := by omega
                rw [hsub, map_mul, ih a.1 (by omega), ih (k - a.1) (by omega)]

end HomCircuit

end CslibFrontier.Computability.Circuit.Arithmetic.Permanent
