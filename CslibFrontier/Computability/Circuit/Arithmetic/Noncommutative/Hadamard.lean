/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.Noncommutative.ABP
public import CslibFrontier.Computability.Circuit.Arithmetic.Noncommutative.Circuit
public import CslibFrontier.Computability.Circuit.Arithmetic.Synthesis
public import CslibFrontier.Foundations.LinearAlgebra.FreeAlgebra

import Mathlib.Data.Fintype.BigOperators

/-!
# Hadamard Product of Non-Commutative Polynomials and Circuit–ABP Product

Defines the Hadamard (coefficient-wise) product `hadamardProd` on `FreeAlgebra K X` and proves the
theorem of Arvind–Joglekar–Srinivasan and Arvind–Srinivasan: the Hadamard product of
a non-commutative arithmetic circuit of size `s` with a homogeneous non-commutative ABP of size `B`
is computed by a non-commutative arithmetic circuit of size
`≤ 2 * m * B^2 + s * (2 * B^3 + B^2) + 1`.

## Main definitions

* `Cslib.Circuits.Arithmetic.hadamardProd`: coefficient-wise product on `FreeAlgebra K X`.
* `Cslib.Circuits.Arithmetic.abpBetween`: layer-to-layer path polynomial of a `NoncommABP`.

## Main results

* `Cslib.Circuits.Arithmetic.coeff_hadamardProd`: coefficient characterization.
* `Cslib.Circuits.Arithmetic.exists_circuit_hadamard_abp`: polynomial-size circuit for `f ⊙ g`
  when `f` is given by a circuit and `g` by a `NoncommABP`.
-/

public section

namespace Cslib.Circuits.Arithmetic

open FreeAlgebra Cslib.Circuits

/-- Coefficient-wise (Hadamard) product of two non-commutative polynomials in
`FreeAlgebra K X`. -/
noncomputable def hadamardProd {K : Type*} [CommSemiring K] {X : Type*}
    (f g : FreeAlgebra K X) : FreeAlgebra K X :=
  equivMonoidAlgebraFreeMonoid.symm
    (MonoidAlgebra.coeffAddEquiv.symm
      (Finsupp.zipWith (fun a b => a * b) (zero_mul 0)
        (equivMonoidAlgebraFreeMonoid f).coeff
        (equivMonoidAlgebraFreeMonoid g).coeff))

@[simp]
theorem coeff_hadamardProd {K : Type*} [CommSemiring K] {X : Type*}
    (f g : FreeAlgebra K X) (w : FreeMonoid X) :
    coeff w (hadamardProd f g) = coeff w f * coeff w g := by
  simp [hadamardProd, FreeAlgebra.coeff_def]

theorem hadamardProd_comm {K : Type*} [CommSemiring K] {X : Type*}
    (f g : FreeAlgebra K X) : hadamardProd f g = hadamardProd g f := by
  apply FreeAlgebra.ext_coeff; intro w; simp [coeff_hadamardProd, mul_comm]

theorem hadamardProd_add_left {K : Type*} [CommSemiring K] {X : Type*}
    (f₁ f₂ g : FreeAlgebra K X) :
    hadamardProd (f₁ + f₂) g = hadamardProd f₁ g + hadamardProd f₂ g := by
  apply FreeAlgebra.ext_coeff; intro w; simp [coeff_hadamardProd, add_mul]

theorem hadamardProd_smul_left {K : Type*} [CommSemiring K] {X : Type*}
    (c : K) (f g : FreeAlgebra K X) :
    hadamardProd (c • f) g = c • hadamardProd f g := by
  apply FreeAlgebra.ext_coeff; intro w; simp [coeff_hadamardProd, mul_assoc]

theorem hadamardProd_sum_left {K : Type*} [CommSemiring K] {X ι : Type*}
    (s : Finset ι) (f : ι → FreeAlgebra K X) (g : FreeAlgebra K X) :
    hadamardProd (∑ i ∈ s, f i) g = ∑ i ∈ s, hadamardProd (f i) g := by
  apply FreeAlgebra.ext_coeff; intro w
  simp [coeff_hadamardProd, map_sum, Finset.sum_mul]

theorem isHomogeneous_hadamardProd_right {K : Type*} [CommSemiring K] {X : Type*} {d : ℕ}
    {f g : FreeAlgebra K X} (hg : g.IsHomogeneous d) :
    (hadamardProd f g).IsHomogeneous d := fun w hw => by
  by_contra hlen
  exact hw (by rw [coeff_hadamardProd, hg.coeff_eq_zero hlen, mul_zero])

/-- Path polynomial of `A : NoncommABP K X d` from vertex `i` of layer `p` to vertex `j` of
layer `p + k`. -/
noncomputable def abpBetween {K : Type*} [CommSemiring K] {X : Type*} [Fintype X] {d : ℕ}
    (A : NoncommABP K X d) (p : ℕ) :
    (k : ℕ) → Fin (A.width p) → Fin (A.width (p + k)) → FreeAlgebra K X
  | 0, i, j => if i = j then 1 else 0
  | k + 1, i, j => ∑ l : Fin (A.width (p + k)), abpBetween A p k i l * A.edge (p + k) l j

theorem isHomogeneous_abpBetween {K : Type*} [CommSemiring K] {X : Type*} [Fintype X] {d : ℕ}
    (A : NoncommABP K X d) (p : ℕ) :
    ∀ (k : ℕ) (i : Fin (A.width p)) (j : Fin (A.width (p + k))),
      (abpBetween A p k i j).IsHomogeneous k
  | 0, i, j => by
    dsimp [abpBetween]
    split_ifs
    · exact isHomogeneous_one
    · exact IsHomogeneous.zero
  | k + 1, i, j => by
    dsimp [abpBetween]
    refine IsHomogeneous.sum _ _ fun l _ => ?_
    exact (isHomogeneous_abpBetween A p k i l).mul (A.isHomogeneous_edge (p + k) l j)

theorem abpBetween_add {K : Type*} [CommSemiring K] {X : Type*} [Fintype X] {d : ℕ}
    (A : NoncommABP K X d) (p k₁ k₂ : ℕ) (i : Fin (A.width p))
    (j : Fin (A.width (p + (k₁ + k₂)))) :
    abpBetween A p (k₁ + k₂) i j =
      ∑ l : Fin (A.width (p + k₁)),
        abpBetween A p k₁ i l *
          abpBetween A (p + k₁) k₂ l (j.cast (by rw [Nat.add_assoc])) := by
  induction k₂ with
  | zero =>
    dsimp only [abpBetween]
    rw [Finset.sum_eq_single (j.cast (by rw [Nat.add_zero]))]
    · simp only [↓reduceIte, mul_one]; rfl
    · intro l _ hne
      split_ifs with heq
      · exfalso; exact hne (by ext; simpa using congrArg Fin.val heq)
      · rw [mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  | succ k₂ ih =>
    change ∑ m : Fin (A.width (p + (k₁ + k₂))),
        abpBetween A p (k₁ + k₂) i m * A.edge (p + (k₁ + k₂)) m j = _
    simp_rw [ih]
    simp only [abpBetween, Finset.sum_mul, Finset.mul_sum, mul_assoc]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    refine Fintype.sum_equiv (finCongr (congrArg A.width (Nat.add_assoc p k₁ k₂).symm))
      _ _ fun m => ?_
    refine congrArg (abpBetween A p k₁ i l * ·) ?_
    refine congrArg (abpBetween A (p + k₁) k₂ l (m.cast _) * ·) ?_
    have hcast : ∀ (a b : ℕ) (h : a = b) (m₁ : Fin (A.width a)) (j₁ : Fin (A.width (a + 1))),
        A.edge a m₁ j₁ =
          A.edge b (m₁.cast (congrArg A.width h))
            (j₁.cast (congrArg A.width (congrArg (· + 1) h))) := by
      intro a b h; subst h; intro _ _; rfl
    exact hcast _ _ (Nat.add_assoc p k₁ k₂).symm m j

theorem abpBetween_zero_deg {K : Type*} [CommSemiring K] {X : Type*} [Fintype X] {d : ℕ}
    (A : NoncommABP K X d) (j : Fin (A.width (0 + d))) :
    abpBetween A 0 d ⟨0, by rw [A.width_zero]; omega⟩ j =
      A.pre d (j.cast (by rw [Nat.zero_add])) := by
  suffices h : ∀ (k : ℕ) (j : Fin (A.width (0 + k))),
      abpBetween A 0 k ⟨0, by rw [A.width_zero]; omega⟩ j =
        A.pre k (j.cast (by rw [Nat.zero_add])) from h d j
  intro k
  induction k with
  | zero =>
    intro j
    have hj : j = ⟨0, by rw [A.width_zero]; omega⟩ := by
      ext
      have hlt : j.val < A.width (0 + 0) := j.isLt
      have hw : A.width (0 + 0) = 1 := by rw [Nat.zero_add, A.width_zero]
      omega
    subst hj
    simp [abpBetween, NoncommABP.pre_zero]
  | succ k ih =>
    intro j
    simp only [abpBetween, NoncommABP.pre_succ]
    refine Fintype.sum_equiv (finCongr (congrArg A.width (Nat.zero_add k))) _ _ fun l => ?_
    rw [ih l]
    refine congrArg (A.pre k (l.cast _) * ·) ?_
    have hcast : ∀ (a b : ℕ) (h : a = b) (l₁ : Fin (A.width a)) (j₁ : Fin (A.width (a + 1))),
        A.edge a l₁ j₁ =
          A.edge b (l₁.cast (congrArg A.width h))
            (j₁.cast (congrArg A.width (congrArg (· + 1) h))) := by
      intro a b h; subst h; intro _ _; rfl
    exact hcast _ _ (Nat.zero_add k) l j

theorem hadamardProd_mul_abpBetween {K : Type*} [CommSemiring K] {X : Type*} [Fintype X] {d : ℕ}
    (A : NoncommABP K X d) (f₁ f₂ : FreeAlgebra K X) (p k : ℕ)
    (i : Fin (A.width p)) (j : Fin (A.width (p + k))) :
    hadamardProd (f₁ * f₂) (abpBetween A p k i j) =
      ∑ r : Fin (k + 1), ∑ l : Fin (A.width (p + r.val)),
        hadamardProd f₁ (abpBetween A p r.val i l) *
          hadamardProd f₂ (abpBetween A (p + r.val) (k - r.val) l
            (j.cast (by rw [Nat.add_assoc, Nat.add_sub_cancel' (Nat.le_of_lt_succ r.isLt)]))) := by
  apply FreeAlgebra.ext_coeff
  intro w
  rw [coeff_hadamardProd, map_sum]
  simp_rw [map_sum]
  by_cases hlen : w.toList.length = k
  · have hcoeff_mul : coeff w (f₁ * f₂) =
        ∑ r : Fin (k + 1),
          coeff (FreeMonoid.ofList (w.toList.take r.val)) f₁ *
            coeff (FreeMonoid.ofList (w.toList.drop r.val)) f₂ := by
      rw [FreeAlgebra.coeff_mul, hlen, ← Fin.sum_univ_eq_sum_range]
    have hRHS : ∀ r : Fin (k + 1),
        ∑ l : Fin (A.width (p + r.val)),
          coeff w (hadamardProd f₁ (abpBetween A p r.val i l) *
            hadamardProd f₂ (abpBetween A (p + r.val) (k - r.val) l
              (j.cast (by rw [Nat.add_assoc, Nat.add_sub_cancel' (Nat.le_of_lt_succ r.isLt)])))) =
        coeff (FreeMonoid.ofList (w.toList.take r.val)) f₁ *
          coeff (FreeMonoid.ofList (w.toList.drop r.val)) f₂ *
          coeff w (abpBetween A p k i j) := by
      intro r
      have hw_split : w = FreeMonoid.ofList (w.toList.take r.val) *
          FreeMonoid.ofList (w.toList.drop r.val) := by
        rw [← FreeMonoid.ofList_append, List.take_append_drop]
      have hlen1 : (FreeMonoid.ofList (w.toList.take r.val)).toList.length = r.val := by
        simp [List.length_take, hlen]; omega
      have hhom1 : ∀ l, (hadamardProd f₁ (abpBetween A p r.val i l)).IsHomogeneous r.val :=
        fun l => isHomogeneous_hadamardProd_right (isHomogeneous_abpBetween A p r.val i l)
      have habp_split : abpBetween A p k i j =
          ∑ l : Fin (A.width (p + r.val)),
            abpBetween A p r.val i l *
              abpBetween A (p + r.val) (k - r.val) l
                (j.cast (by rw [Nat.add_assoc,
                  Nat.add_sub_cancel' (Nat.le_of_lt_succ r.isLt)])) := by
        have hgen : ∀ (k' : ℕ) (hk' : r.val + (k - r.val) = k') (j' : Fin (A.width (p + k'))),
            abpBetween A p k' i j' =
              ∑ l : Fin (A.width (p + r.val)),
                abpBetween A p r.val i l *
                  abpBetween A (p + r.val) (k - r.val) l
                    (j'.cast (by rw [← hk', Nat.add_assoc])) := by
          intro k' hk' j'; subst hk'; exact abpBetween_add A p r.val (k - r.val) i j'
        exact hgen k (Nat.add_sub_cancel' (Nat.le_of_lt_succ r.isLt)) j
      rw [habp_split, map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      have hc1 := FreeAlgebra.coeff_mul_mul_of_isHomogeneous
        (hadamardProd f₂ (abpBetween A (p + r.val) (k - r.val) l
          (j.cast (by rw [Nat.add_assoc, Nat.add_sub_cancel' (Nat.le_of_lt_succ r.isLt)]))))
        (FreeMonoid.ofList (w.toList.take r.val)) (FreeMonoid.ofList (w.toList.drop r.val))
        (by rw [hlen1]; exact hhom1 l)
      have hc2 := FreeAlgebra.coeff_mul_mul_of_isHomogeneous
        (abpBetween A (p + r.val) (k - r.val) l
          (j.cast (by rw [Nat.add_assoc, Nat.add_sub_cancel' (Nat.le_of_lt_succ r.isLt)])))
        (FreeMonoid.ofList (w.toList.take r.val)) (FreeMonoid.ofList (w.toList.drop r.val))
        (by rw [hlen1]; exact isHomogeneous_abpBetween A p r.val i l)
      rw [← hw_split] at hc1 hc2
      rw [hc1, hc2, coeff_hadamardProd, coeff_hadamardProd]
      ring
    simp_rw [hRHS, ← Finset.sum_mul, ← hcoeff_mul]
  · have h0 : coeff w (abpBetween A p k i j) = 0 :=
      (isHomogeneous_abpBetween A p k i j).coeff_eq_zero hlen
    rw [h0, mul_zero]
    symm
    refine Finset.sum_eq_zero fun r _ => Finset.sum_eq_zero fun l _ => ?_
    have hk : r.val + (k - r.val) = k := Nat.add_sub_cancel' (Nat.le_of_lt_succ r.isLt)
    have hmul := (isHomogeneous_hadamardProd_right (f := f₁)
      (isHomogeneous_abpBetween A p r.val i l)).mul
      (isHomogeneous_hadamardProd_right (f := f₂)
        (isHomogeneous_abpBetween A (p + r.val) (k - r.val) l
          (j.cast (by rw [Nat.add_assoc, hk]))))
    exact hmul.coeff_eq_zero (by omega)

private theorem hadamardProd_const_abpBetween {K : Type*} [CommSemiring K] {X : Type*} [Fintype X]
    {d : ℕ} (A : NoncommABP K X d) (c : K) (p k : ℕ)
    (i : Fin (A.width p)) (j : Fin (A.width (p + k))) :
    hadamardProd (algebraMap K (FreeAlgebra K X) c) (abpBetween A p k i j) =
      if k = 0 ∧ i.val = j.val then algebraMap K (FreeAlgebra K X) c else 0 := by
  apply FreeAlgebra.ext_coeff
  intro w
  rw [coeff_hadamardProd]
  by_cases hw : w = 1
  · subst hw
    rw [FreeAlgebra.coeff_algebraMap, Finsupp.single_eq_same]
    by_cases hk : k = 0
    · subst hk
      dsimp [abpBetween]
      by_cases h1 : i = j
      · simp [h1, FreeAlgebra.coeff_one, FreeAlgebra.coeff_algebraMap]
      · have h1' : i.val ≠ j.val := fun h => h1 (Fin.ext h)
        simp [h1, h1']
    · have h0 : coeff (1 : FreeMonoid X) (abpBetween A p k i j) = 0 :=
        (isHomogeneous_abpBetween A p k i j).coeff_eq_zero (by simp [Ne.symm hk])
      simp [hk, h0]
  · have h0 : coeff w (algebraMap K (FreeAlgebra K X) c) = 0 := by
      rw [FreeAlgebra.coeff_algebraMap]; exact Finsupp.single_eq_of_ne' (Ne.symm hw)
    rw [h0, zero_mul]
    split_ifs
    · exact h0.symm
    · simp

private theorem hadamardProd_ι_abpBetween {K : Type*} [CommSemiring K] {X : Type*} [Fintype X]
    {d : ℕ} (A : NoncommABP K X d) (x : X) (p k : ℕ)
    (i : Fin (A.width p)) (j : Fin (A.width (p + k))) :
    hadamardProd (ι K x) (abpBetween A p k i j) =
      if hk : k = 1 then
        A.weight p x i (j.cast (by rw [hk])) • ι K x
      else 0 := by
  apply FreeAlgebra.ext_coeff
  intro w
  rw [coeff_hadamardProd]
  by_cases hw : w = FreeMonoid.of x
  · subst hw
    rw [FreeAlgebra.coeff_ι, Finsupp.single_eq_same]
    by_cases hk : k = 1
    · subst hk
      simp only [↓reduceDIte, map_smul, FreeAlgebra.coeff_ι, Finsupp.single_eq_same, smul_eq_mul,
        mul_one, one_mul, abpBetween]
      have hsum : (∑ l : Fin (A.width p),
          (if i = l then (1 : FreeAlgebra K X) else 0) * A.edge (p + 0) l j) =
          A.edge (p + 0) i j := by
        rw [Finset.sum_eq_single i]
        · simp
        · intro l _ hne; simp [hne.symm]
        · intro h; exact absurd (Finset.mem_univ _) h
      exact (congrArg (coeff (FreeMonoid.of x)) hsum).trans (NoncommABP.coeff_of_edge A p i j x)
    · simp only [hk, ↓reduceDIte, map_zero, one_mul]
      exact (isHomogeneous_abpBetween A p k i j).coeff_eq_zero (by simp [Ne.symm hk])
  · have h0 : coeff w (ι K x) = 0 := by
      rw [FreeAlgebra.coeff_ι]; exact Finsupp.single_eq_of_ne' (Ne.symm hw)
    rw [h0, zero_mul]
    split_ifs
    · rw [map_smul, h0, smul_zero]
    · simp

private abbrev ABPQuad {K : Type*} [CommSemiring K] {X : Type*} {d : ℕ} (A : NoncommABP K X d) :=
  Σ (p : Fin (d + 1)) (k : Fin (d + 1 - p.val)), Fin (A.width p.val) × Fin (A.width (p.val + k.val))

private theorem card_abpQuad_le {K : Type*} [CommSemiring K] {X : Type*} {d : ℕ}
    (A : NoncommABP K X d) : Fintype.card (ABPQuad A) ≤ A.size ^ 2 := by
  simp only [Fintype.card_sigma, Fintype.card_prod, Fintype.card_fin]
  have h1 : ∀ p : Fin (d + 1),
      ∑ k : Fin (d + 1 - p.val), A.width p.val * A.width (p.val + k.val) ≤
        A.width p.val * A.size := by
    intro p
    rw [← Finset.mul_sum]
    refine Nat.mul_le_mul_left _ ?_
    calc ∑ k : Fin (d + 1 - p.val), A.width (p.val + k.val)
        = ∑ m ∈ Finset.Ico p.val (d + 1), A.width m := by
          refine Finset.sum_bij (fun k _ => p.val + k.val) ?_ ?_ ?_ ?_
          · intro k _; rw [Finset.mem_Ico]; omega
          · intro k₁ _ k₂ _ h; ext; omega
          · intro m hm
            rw [Finset.mem_Ico] at hm
            have hp := p.isLt
            exact ⟨⟨m - p.val, by omega⟩, Finset.mem_univ _, by dsimp; omega⟩
          · intro _ _; rfl
      _ ≤ ∑ m ∈ Finset.range (d + 1), A.width m :=
          Finset.sum_le_sum_of_subset (fun m hm => Finset.mem_range.mpr (Finset.mem_Ico.mp hm).2)
      _ = A.size := rfl
  calc ∑ p : Fin (d + 1), ∑ k : Fin (d + 1 - p.val), A.width p.val * A.width (p.val + k.val)
      ≤ ∑ p : Fin (d + 1), A.width p.val * A.size := Finset.sum_le_sum fun p _ => h1 p
    _ = (∑ p : Fin (d + 1), A.width p.val) * A.size := by rw [← Finset.sum_mul]
    _ = A.size ^ 2 := by
      rw [sq, Fin.sum_univ_eq_sum_range A.width (d + 1)]; rfl

/-- **Arvind–Joglekar–Srinivasan / Arvind–Srinivasan**: The Hadamard product of a
non-commutative arithmetic circuit `C` and a homogeneous `NoncommABP` `A` is computed by a
non-commutative arithmetic circuit of size
`≤ 2 * m * A.size^2 + C.size * (2 * A.size^3 + A.size^2) + 1`.
-/
theorem exists_circuit_hadamard_abp {K : Type*} [CommSemiring K] {m d : ℕ}
    (C : Circuit (arithSignature K) m 1) (A : NoncommABP K (Fin m) d) :
    ∃ D : Circuit (arithSignature K) m 1,
      D.noncommPolynomial 0 = hadamardProd (C.noncommPolynomial 0) A.polynomial ∧
      D.size ≤ 2 * m * A.size ^ 2 + C.size * (2 * A.size ^ 3 + A.size ^ 2) + 1 := by
  let I := arithInterpretationWith K (algebraMap K (FreeAlgebra K (Fin m)))
  let targetOf (f : FreeAlgebra K (Fin m)) (q : ABPQuad A) :
      (Fin m → FreeAlgebra K (Fin m)) → FreeAlgebra K (Fin m) :=
    fun x => FreeAlgebra.lift K x (hadamardProd f (abpBetween A q.1.val q.2.1.val q.2.2.1 q.2.2.2))
  let progFamily {g : ℕ} (p : Program (arithSignature K) m g) :
      Set ((Fin m → FreeAlgebra K (Fin m)) → FreeAlgebra K (Fin m)) :=
    {fun _ => (0 : FreeAlgebra K (Fin m))} ∪
      Set.range (fun (wq : Wire m g × ABPQuad A) => targetOf (p.trace I (ι K) wq.1) wq.2)
  have hprog : ∀ {g : ℕ} (p : Program (arithSignature K) m g),
      Synthesis I (inputs m) (progFamily p)
        (2 * m * A.size ^ 2 + g * (2 * A.size ^ 3 + A.size ^ 2) + 1) := by
    intro g p
    induction p with
    | empty =>
      have hzero : Synthesis I (inputs m) {fun _ => (0 : FreeAlgebra K (Fin m))} 1 := by
        simpa [I, arithInterpretationWith, map_zero] using
          Synthesis.arith_const (K := K) (R := FreeAlgebra K (Fin m))
            (constant := algebraMap K _) (s := inputs m) (0 : K)
      have hbase : Synthesis I (inputs m ∪ {fun _ => (0 : FreeAlgebra K (Fin m))})
          (Set.range fun wq : Wire m 0 × ABPQuad A =>
            targetOf ((Program.empty : Program _ m 0).trace I (ι K) wq.1) wq.2)
          (2 * m * A.size ^ 2) := by
        have hcost : ∑ _wq : Wire m 0 × ABPQuad A, 2 ≤ 2 * m * A.size ^ 2 := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, smul_eq_mul]
          have hcardW : Fintype.card (Wire m 0) = m := by simp
          rw [hcardW]
          have hQ := card_abpQuad_le A
          calc m * Fintype.card (ABPQuad A) * 2
              ≤ m * A.size ^ 2 * 2 := by gcongr
            _ = 2 * m * A.size ^ 2 := by ring
        refine (Synthesis.family _ (fun _ => 2) fun ⟨w, q⟩ => ?_).mono Set.Subset.rfl
          Set.Subset.rfl hcost
        cases w with
        | gate j => exact Fin.elim0 j
        | input k =>
          dsimp only [targetOf, Program.trace_input]
          rw [hadamardProd_ι_abpBetween]
          split_ifs with hk
          · let c0 : K := A.weight q.1.val k q.2.2.1 (q.2.2.2.cast (by rw [hk]))
            have hfun : (fun x : Fin m → FreeAlgebra K (Fin m) =>
                FreeAlgebra.lift K x (c0 • ι K k)) =
                fun x => algebraMap K _ c0 * x k := by
              funext x
              rw [map_smul, FreeAlgebra.lift_ι_apply, Algebra.smul_def]
            rw [hfun]
            have hc_synth : Synthesis I (inputs m ∪ {fun _ => (0 : FreeAlgebra K (Fin m))})
                {fun _ => algebraMap K (FreeAlgebra K (Fin m)) c0} 1 :=
              Synthesis.arith_const (constant := algebraMap K _) c0
            have hm_synth : Synthesis I
                ((inputs m ∪ {fun _ => (0 : FreeAlgebra K (Fin m))}) ∪
                  {fun _ => algebraMap K (FreeAlgebra K (Fin m)) c0})
                {fun x => algebraMap K (FreeAlgebra K (Fin m)) c0 * x k} 1 :=
              Synthesis.arith_mul (Set.mem_union_right _ rfl)
                (Set.mem_union_left _ (Set.mem_union_left _ ⟨k, rfl⟩))
            exact hc_synth.trans hm_synth
          · have h0 : (fun x : Fin m → FreeAlgebra K (Fin m) => FreeAlgebra.lift K x 0) =
                fun _ => 0 := by funext x; exact map_zero _
            rw [h0]
            exact (Synthesis.of_mem (Set.mem_union_right _ rfl)).mono Set.Subset.rfl
              Set.Subset.rfl (by omega)
      refine (hzero.comp hbase).mono Set.Subset.rfl ?_ (by omega)
      rintro f (hf | hf)
      · exact Or.inl hf
      · exact Or.inr hf
    | @gate g p line ih =>
      let newF (q : ABPQuad A) := targetOf ((p.gate line).trace I (ι K) (.gate (Fin.last g))) q
      have hstep : Synthesis I (inputs m ∪ progFamily p) (Set.range newF)
          (2 * A.size ^ 3 + A.size ^ 2) := by
        have hgate_avail : ∀ (w : Wire m g) (q : ABPQuad A),
            targetOf (p.trace I (ι K) w) q ∈ inputs m ∪ progFamily p :=
          fun w q => Set.mem_union_right _ (Set.mem_union_right _ ⟨(w, q), rfl⟩)
        have hzero_avail : (fun _ : Fin m → FreeAlgebra K (Fin m) => (0 : FreeAlgebra K (Fin m))) ∈
            inputs m ∪ progFamily p :=
          Set.mem_union_right _ (Set.mem_union_left _ rfl)
        have heach : ∀ q : ABPQuad A,
            Synthesis I (inputs m ∪ progFamily p) {newF q} (2 * A.size + 1) := by
          intro q
          have hval : (p.gate line).trace I (ι K) (.gate (Fin.last g)) =
              I line.op (fun a => p.trace I (ι K) (line.wires a)) :=
            Program.eval_gate_last p line I (ι K)
          dsimp only [newF, targetOf]
          rw [hval]
          rcases line with ⟨op, wires⟩
          cases op with
          | const c =>
            dsimp only [I, arithInterpretationWith]
            rw [hadamardProd_const_abpBetween]
            split_ifs with h0
            · have hf : (fun x : Fin m → FreeAlgebra K (Fin m) =>
                  FreeAlgebra.lift K x (algebraMap K _ c)) = fun _ => algebraMap K _ c := by
                funext x; exact AlgHom.commutes _ c
              rw [hf]
              exact (Synthesis.arith_const (constant := algebraMap K _) c).mono
                Set.Subset.rfl Set.Subset.rfl (by omega)
            · have hf : (fun x : Fin m → FreeAlgebra K (Fin m) => FreeAlgebra.lift K x 0) =
                  fun _ => 0 := by funext x; exact map_zero _
              rw [hf]
              exact (Synthesis.of_mem hzero_avail).mono Set.Subset.rfl Set.Subset.rfl (by omega)
          | add =>
            dsimp only [I, arithInterpretationWith]
            rw [hadamardProd_add_left]
            have hf : (fun x : Fin m → FreeAlgebra K (Fin m) =>
                FreeAlgebra.lift K x
                  (hadamardProd (p.trace I (ι K) (wires 0))
                      (abpBetween A q.1.val q.2.1.val q.2.2.1 q.2.2.2) +
                    hadamardProd (p.trace I (ι K) (wires 1))
                      (abpBetween A q.1.val q.2.1.val q.2.2.1 q.2.2.2))) =
                fun x => targetOf (p.trace I (ι K) (wires 0)) q x +
                  targetOf (p.trace I (ι K) (wires 1)) q x := by
              funext x; exact map_add _ _ _
            rw [hf]
            exact (Synthesis.arith_add (hgate_avail (wires 0) q)
              (hgate_avail (wires 1) q)).mono Set.Subset.rfl Set.Subset.rfl (by omega)
          | mul =>
            dsimp only [I, arithInterpretationWith]
            rw [hadamardProd_mul_abpBetween]
            let idxType := Σ r : Fin (q.2.1.val + 1), Fin (A.width (q.1.val + r.val))
            let summand (rl : idxType) :
                (Fin m → FreeAlgebra K (Fin m)) → FreeAlgebra K (Fin m) :=
              fun x =>
                targetOf (p.trace I (ι K) (wires 0))
                  ⟨q.1, ⟨rl.1.val, by omega⟩, q.2.2.1, rl.2⟩ x *
                targetOf (p.trace I (ι K) (wires 1))
                  ⟨⟨q.1.val + rl.1.val, by omega⟩, ⟨q.2.1.val - rl.1.val, by dsimp; omega⟩,
                    rl.2, q.2.2.2.cast (by
                      rw [Nat.add_assoc, Nat.add_sub_cancel' (Nat.le_of_lt_succ rl.1.isLt)])⟩ x
            have hf : (fun x : Fin m → FreeAlgebra K (Fin m) =>
                FreeAlgebra.lift K x (∑ r : Fin (q.2.1.val + 1),
                  ∑ l : Fin (A.width (q.1.val + r.val)),
                    hadamardProd (p.trace I (ι K) (wires 0))
                      (abpBetween A q.1.val r.val q.2.2.1 l) *
                    hadamardProd (p.trace I (ι K) (wires 1))
                      (abpBetween A (q.1.val + r.val) (q.2.1.val - r.val) l
                        (q.2.2.2.cast (by
                          rw [Nat.add_assoc, Nat.add_sub_cancel' (Nat.le_of_lt_succ r.isLt)]))))) =
                fun x => ∑ rl : idxType, summand rl x := by
              funext x
              rw [map_sum, Fintype.sum_sigma]
              refine Finset.sum_congr rfl fun r _ => ?_
              rw [map_sum]
              refine Finset.sum_congr rfl fun l _ => ?_
              exact map_mul _ _ _
            rw [hf]
            have hsum := Synthesis.arith_sum (K := K) (constant := algebraMap K _)
              Finset.univ summand (fun _ => 1) hzero_avail
              (fun rl _ => Synthesis.arith_mul (K := K) (constant := algebraMap K _)
                (hgate_avail _ _) (hgate_avail _ _))
            have hcard_idx : Fintype.card idxType ≤ A.size := by
              simp only [idxType, Fintype.card_sigma, Fintype.card_fin]
              calc ∑ r : Fin (q.2.1.val + 1), A.width (q.1.val + r.val)
                  = ∑ t ∈ Finset.Ico q.1.val (q.1.val + q.2.1.val + 1), A.width t := by
                    refine Finset.sum_bij (fun r _ => q.1.val + r.val) ?_ ?_ ?_ ?_
                    · intro r _; rw [Finset.mem_Ico]; omega
                    · intro r₁ _ r₂ _ h; ext; omega
                    · intro t ht; rw [Finset.mem_Ico] at ht
                      exact ⟨⟨t - q.1.val, by omega⟩, Finset.mem_univ _, by dsimp only; omega⟩
                    · intro _ _; rfl
                _ ≤ ∑ t ∈ Finset.range (d + 1), A.width t :=
                    Finset.sum_le_sum_of_subset (fun t ht => by
                      rw [Finset.mem_range]; have := Finset.mem_Ico.mp ht; omega)
                _ = A.size := rfl
            refine hsum.mono Set.Subset.rfl Set.Subset.rfl ?_
            simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul]
            omega
        have hcost : ∑ _q : ABPQuad A, (2 * A.size + 1) ≤ 2 * A.size ^ 3 + A.size ^ 2 := by
          simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul]
          have hQ := card_abpQuad_le A
          calc Fintype.card (ABPQuad A) * (2 * A.size + 1)
              ≤ A.size ^ 2 * (2 * A.size + 1) := by gcongr
            _ = 2 * A.size ^ 3 + A.size ^ 2 := by ring
        exact (Synthesis.family newF (fun _ => 2 * A.size + 1) heach).mono
          Set.Subset.rfl Set.Subset.rfl hcost
      refine (ih.comp hstep).mono Set.Subset.rfl ?_ (by ring_nf; omega)
      rintro f (hf0 | ⟨⟨w, q⟩, rfl⟩)
      · exact Or.inl (Or.inl hf0)
      · cases w with
        | input k =>
          exact Or.inl (Or.inr ⟨(.input k, q), rfl⟩)
        | gate idx =>
          refine Fin.lastCases ?_ (fun j => ?_) idx
          · exact Or.inr ⟨q, rfl⟩
          · refine Or.inl (Or.inr ⟨(.gate j, q), ?_⟩)
            simp [targetOf]
  let qOut : ABPQuad A :=
    ⟨⟨0, Nat.zero_lt_succ d⟩, ⟨d, by dsimp; omega⟩,
      ⟨0, by rw [A.width_zero]; omega⟩, ⟨0, by rw [Nat.zero_add, A.width_deg]; omega⟩⟩
  have hmem : targetOf (C.program.trace I (ι K) (C.outputs 0)) qOut ∈ progFamily C.program :=
    Set.mem_union_right _ ⟨(C.outputs 0, qOut), rfl⟩
  have hsynth := (hprog C.program).mono Set.Subset.rfl (Set.singleton_subset_iff.mpr hmem) le_rfl
  obtain ⟨D, hD, hDsize⟩ := hsynth.exists_circuit
  refine ⟨D, ?_, hDsize⟩
  have hDeval := congrFun (hD (ι K)) 0
  rw [Circuit.noncommPolynomial_eq_eval, Circuit.noncommPolynomial_eq_eval]
  change D.eval I (ι K) 0 = targetOf (C.program.trace I (ι K) (C.outputs 0)) qOut (ι K) at hDeval
  rw [hDeval]
  dsimp only [targetOf, qOut]
  have hid : FreeAlgebra.lift K (ι K) = AlgHom.id K (FreeAlgebra K (Fin m)) :=
    FreeAlgebra.hom_ext (funext fun i => FreeAlgebra.lift_ι_apply _ i)
  rw [AlgHom.ext_iff.mp hid]
  rw [abpBetween_zero_deg, NoncommABP.polynomial,
    Finset.sum_eq_single ⟨0, by rw [A.width_deg]; omega⟩]
  · rfl
  · intro j _ hne
    exfalso; apply hne; ext
    have hj : j.val < A.width d := j.isLt
    have hw : A.width d = 1 := A.width_deg
    dsimp only; omega
  · intro h; exact absurd (Finset.mem_univ _) h

end Cslib.Circuits.Arithmetic
