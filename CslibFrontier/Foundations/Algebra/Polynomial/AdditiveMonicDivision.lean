module

public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.Tactic.Ring

/-!
# Additive Direct-Sum Monic Polynomial Division over Finite Commutative Rings

Componentwise Euclidean division modulo a monic integer polynomial under the additive direct-sum
decomposition of a finite commutative ring into cyclic abelian groups.

## Main definitions

* `CslibFrontier.Algebra.liftZModPoly`: canonical lift of a polynomial over `ZMod m` to
  `Polynomial ℤ` using representatives in `0, …, m - 1`.

## Main results

* `CslibFrontier.Algebra.additive_component_divByMonic_eq`: if `e ∈ R` has additive order
  dividing `m > 1` and `q ∈ ℤ[X]` is monic, then dividing `(liftZModPoly g) · e` by `q` in `R[X]`
  produces the lifted quotient and remainder from `(ZMod m)[X]` scaled by `e`.
* `CslibFrontier.Algebra.additive_decomp_divByMonic`: every finite nontrivial commutative ring
  `R` decomposes additively as `⨁ i, ZMod (n i) · e i` with `n i > 1` such that monic division
  in `R[X]` by any monic `q ∈ ℤ[X]` operates componentwise across `(ZMod (n i))[X]`.
-/

public section

namespace CslibFrontier.Algebra

private theorem poly_finset_sum_coeff {R ι : Type*} [Semiring R] (s : Finset ι)
    (f : ι → Polynomial R) (k : ℕ) :
    (∑ i ∈ s, f i).coeff k = ∑ i ∈ s, (f i).coeff k := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Polynomial.coeff_add, ih]

/-- Lift a polynomial over `ZMod m` to `Polynomial ℤ` using canonical representatives in
`0, …, m - 1`. -/
noncomputable def liftZModPoly {m : ℕ} (p : Polynomial (ZMod m)) : Polynomial ℤ :=
  ∑ i ∈ p.support, Polynomial.monomial i ((p.coeff i).val : ℤ)

/-- Reducing `liftZModPoly p` modulo `m` recovers `p` (for `0 < m`). -/
theorem liftZModPoly_map_zmod {m : ℕ} [NeZero m] (p : Polynomial (ZMod m)) :
    (liftZModPoly p).map (Int.castRingHom (ZMod m)) = p := by
  unfold liftZModPoly
  ext i
  rw [Polynomial.coeff_map, poly_finset_sum_coeff]
  simp only [Polynomial.coeff_monomial, Finsupp.single_apply]
  rw [Finset.sum_ite_eq']
  by_cases hi : i ∈ p.support
  · simp only [hi, ↓reduceIte, eq_intCast, Int.cast_natCast, ZMod.natCast_zmod_val]
  · simp only [hi, ↓reduceIte, map_zero]
    exact (not_not.mp (Polynomial.mem_support_iff.not.mp hi)).symm

/-- `natDegree` of `liftZModPoly p` is at most `p.natDegree`. -/
theorem liftZModPoly_natDegree_le {m : ℕ} (p : Polynomial (ZMod m)) :
    (liftZModPoly p).natDegree ≤ p.natDegree := by
  unfold liftZModPoly
  refine (Polynomial.natDegree_sum_le p.support _).trans ?_
  rw [Finset.fold_max_le]
  refine ⟨Nat.zero_le _, fun i hi ↦ ?_⟩
  exact (Polynomial.natDegree_monomial_le _).trans (Polynomial.le_natDegree_of_mem_supp i hi)

/-- `degree` of `liftZModPoly p` is at most `p.degree`. -/
theorem liftZModPoly_degree_le {m : ℕ} (p : Polynomial (ZMod m)) :
    (liftZModPoly p).degree ≤ p.degree := by
  by_cases hp0 : p = 0
  · subst hp0; simp [liftZModPoly]
  · by_cases hl0 : liftZModPoly p = 0
    · rw [hl0, Polynomial.degree_zero]; exact bot_le
    · rw [Polynomial.degree_eq_natDegree hl0, Polynomial.degree_eq_natDegree hp0]
      exact WithBot.coe_le_coe.mpr (liftZModPoly_natDegree_le p)

/-- Scaling an integer polynomial by an element $e \in R$ of additive order dividing $m$ depends
only on the coefficients modulo $m$. -/
theorem intPoly_map_mul_C_eq_of_map_zmod_eq {R : Type*} [CommRing R] {m : ℕ}
    {e : R} (he : (m : R) * e = 0) {a b : Polynomial ℤ}
    (hab : a.map (Int.castRingHom (ZMod m)) = b.map (Int.castRingHom (ZMod m))) :
    a.map (Int.castRingHom R) * Polynomial.C e = b.map (Int.castRingHom R) * Polynomial.C e := by
  ext i
  rw [Polynomial.coeff_mul_C, Polynomial.coeff_mul_C, Polynomial.coeff_map, Polynomial.coeff_map]
  have hi := congrArg (fun p : Polynomial (ZMod m) ↦ p.coeff i) hab
  rw [Polynomial.coeff_map, Polynomial.coeff_map] at hi
  have hdvd : (m : ℤ) ∣ a.coeff i - b.coeff i := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sub, sub_eq_zero]
    exact hi
  obtain ⟨t, ht⟩ := hdvd
  have hsub : a.coeff i = b.coeff i + (m : ℤ) * t := by omega
  rw [hsub]
  simp only [eq_intCast, Int.cast_add, Int.cast_mul, Int.cast_natCast, add_mul]
  have h0 : (m : R) * (t : R) * e = 0 := by
    calc (m : R) * (t : R) * e = (t : R) * ((m : R) * e) := by ring
      _ = 0 := by rw [he, mul_zero]
  rw [h0, add_zero]

/-- If $e \in R$ satisfies $m e = 0$ ($m > 1$), $q \in \mathbb{Z}[x]$ is monic, and
$g = q \cdot q' + r'$ is Euclidean division in $\mathbb{Z}_m[x]$, then dividing $g e$ by $q$ in
$R[x]$ produces quotient $q' e$ and remainder $r' e$. -/
theorem additive_component_divByMonic_eq {R : Type*} [CommRing R] [Nontrivial R]
    {m : ℕ} (hm : 1 < m) {e : R} (he : (m : R) * e = 0)
    (gZ : Polynomial (ZMod m)) {qZ : Polynomial ℤ} (hqZ : qZ.Monic) :
    have _ : NeZero m := ⟨by omega⟩
    let qm : Polynomial (ZMod m) := qZ.map (Int.castRingHom (ZMod m))
    let qR : Polynomial R := qZ.map (Int.castRingHom R)
    let q' := gZ /ₘ qm
    let r' := gZ %ₘ qm
    let gR : Polynomial R := (liftZModPoly gZ).map (Int.castRingHom R) * Polynomial.C e
    gR /ₘ qR = (liftZModPoly q').map (Int.castRingHom R) * Polynomial.C e ∧
    gR %ₘ qR = (liftZModPoly r').map (Int.castRingHom R) * Polynomial.C e := by
  have : NeZero m := ⟨by omega⟩
  have : Nontrivial (ZMod m) := ZMod.nontrivial_iff.mpr (by omega)
  intro _ qm qR q' r' gR
  have hqm : qm.Monic := hqZ.map _
  have hqR : qR.Monic := hqZ.map _
  have hdiv_zm : r' + qm * q' = gZ := Polynomial.modByMonic_add_div gZ qm
  have hcong : (liftZModPoly r' + qZ * liftZModPoly q').map (Int.castRingHom (ZMod m)) =
      (liftZModPoly gZ).map (Int.castRingHom (ZMod m)) := by
    rw [Polynomial.map_add, Polynomial.map_mul, liftZModPoly_map_zmod, liftZModPoly_map_zmod,
      liftZModPoly_map_zmod]
    exact hdiv_zm
  have heq_R :
      (liftZModPoly r').map (Int.castRingHom R) * Polynomial.C e +
        qR * ((liftZModPoly q').map (Int.castRingHom R) * Polynomial.C e) = gR := by
    have h1 := intPoly_map_mul_C_eq_of_map_zmod_eq he hcong
    rw [Polynomial.map_add, Polynomial.map_mul, add_mul, mul_assoc] at h1
    exact h1
  have hdeg_r :
      ((liftZModPoly r').map (Int.castRingHom R) * Polynomial.C e).degree < qR.degree := by
    have hr_lt : r'.degree < qm.degree := Polynomial.degree_modByMonic_lt gZ hqm
    have hqm_deg : qm.degree = qZ.degree := by
      rw [Polynomial.degree_eq_natDegree hqm.ne_zero, Polynomial.degree_eq_natDegree hqZ.ne_zero,
        hqZ.natDegree_map]
    have hqR_deg : qR.degree = qZ.degree := by
      rw [Polynomial.degree_eq_natDegree hqR.ne_zero, Polynomial.degree_eq_natDegree hqZ.ne_zero,
        hqZ.natDegree_map]
    calc
      ((liftZModPoly r').map (Int.castRingHom R) * Polynomial.C e).degree
        ≤ ((liftZModPoly r').map (Int.castRingHom R)).degree + (Polynomial.C e).degree :=
          Polynomial.degree_mul_le _ _
      _ ≤ (liftZModPoly r').degree + 0 :=
          add_le_add Polynomial.degree_map_le Polynomial.degree_C_le
      _ = (liftZModPoly r').degree := add_zero _
      _ ≤ r'.degree := liftZModPoly_degree_le r'
      _ < qm.degree := hr_lt
      _ = qR.degree := hqm_deg.trans hqR_deg.symm
  exact Polynomial.div_modByMonic_unique _ _ hqR ⟨heq_R, hdeg_r⟩

/-- Every finite nontrivial commutative ring $R$ admits an additive decomposition
$R \cong \bigoplus_i \mathbb{Z}_{n_i} e_i$ ($n_i > 1$) under which monic division of any
$g \in R[x]$ by any monic $q \in \mathbb{Z}[x]$ decomposes componentwise: $g \bmod q = 0$ in
$R[x]$ iff $g_i \bmod q = 0$ in $\mathbb{Z}_{n_i}[x]$ for every component $i$. -/
theorem additive_decomp_divByMonic (R : Type*) [CommRing R] [Finite R] [Nontrivial R] :
    ∃ (ι : Type) (_ : Fintype ι) (n : ι → ℕ) (_ : ∀ i, 1 < n i) (e : ι → R),
      (∀ i, ((n i : ℕ) : R) * e i = 0) ∧
      ∀ (g : Polynomial R),
        ∃ gComp : (i : ι) → Polynomial (ZMod (n i)),
          g = ∑ i : ι, (liftZModPoly (gComp i)).map (Int.castRingHom R) * Polynomial.C (e i) ∧
          (g ≠ 0 → ∃ j : ι, gComp j ≠ 0) ∧
          ∀ (qZ : Polynomial ℤ), qZ.Monic →
            let qR := qZ.map (Int.castRingHom R)
            g %ₘ qR =
              ∑ i : ι,
                (liftZModPoly (gComp i %ₘ qZ.map (Int.castRingHom (ZMod (n i))))).map
                  (Int.castRingHom R) * Polynomial.C (e i) ∧
            (g %ₘ qR = 0 ↔
              ∀ i : ι, gComp i %ₘ qZ.map (Int.castRingHom (ZMod (n i))) = 0) := by
  classical
  obtain ⟨ι, hFin, n, hn, ⟨ψ⟩⟩ := AddCommGroup.equiv_directSum_zmod_of_finite' R
  let e : ι → R := fun i ↦ ψ.symm (DirectSum.of (fun j ↦ ZMod (n j)) i 1)
  have he_ord : ∀ i : ι, ((n i : ℕ) : R) * e i = 0 := by
    intro i
    have hns : n i • e i = 0 := by
      dsimp [e]
      rw [← map_nsmul, ← map_nsmul]
      have h1 : n i • (1 : ZMod (n i)) = 0 := by simp
      rw [h1, map_zero, map_zero]
    simpa [nsmul_eq_mul] using hns
  refine ⟨ι, hFin, n, hn, e, he_ord, fun g ↦ ?_⟩
  let gComp : (i : ι) → Polynomial (ZMod (n i)) := fun i ↦
    ∑ k ∈ g.support, Polynomial.monomial k (ψ (g.coeff k) i)
  have hsum_coeff : ∀ (r : R),
      r = ∑ i : ι, (((ψ r i).val : ℤ) : R) * e i := by
    intro r
    have hds : ψ r = ∑ i : ι, DirectSum.of (fun j ↦ ZMod (n j)) i (ψ r i) :=
      (DirectSum.sum_support_of (ψ r)).symm.trans
        (Finset.sum_subset (Finset.subset_univ _) fun i _ hi ↦ by
          have h0 : ψ r i = 0 := DFinsupp.notMem_support_iff.mp hi
          rw [h0, map_zero])
    have hr : r = ψ.symm (ψ r) := (ψ.symm_apply_apply r).symm
    conv_lhs => rw [hr, hds, map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    have : NeZero (n i) := ⟨by have := hn i; omega⟩
    have hval : ψ r i = (ψ r i).val • (1 : ZMod (n i)) := by simp
    conv_lhs => rw [hval, map_nsmul, map_nsmul]
    simp [e, nsmul_eq_mul]
  have hg_eq :
      g = ∑ i : ι, (liftZModPoly (gComp i)).map (Int.castRingHom R) * Polynomial.C (e i) := by
    ext k
    rw [poly_finset_sum_coeff]
    have hterm : ∀ i : ι,
        ((liftZModPoly (gComp i)).map (Int.castRingHom R) * Polynomial.C (e i)).coeff k =
          (((ψ (g.coeff k) i).val : ℤ) : R) * e i := by
      intro i
      rw [Polynomial.coeff_mul_C, Polynomial.coeff_map]
      have hgi_k : (gComp i).coeff k = ψ (g.coeff k) i := by
        rw [poly_finset_sum_coeff]
        simp only [Polynomial.coeff_monomial, Finsupp.single_apply]
        rw [Finset.sum_ite_eq']
        by_cases hk : k ∈ g.support
        · simp [hk]
        · have h0 : g.coeff k = 0 := not_not.mp (Polynomial.mem_support_iff.not.mp hk)
          simp [hk, h0]
      have hlift_k : (liftZModPoly (gComp i)).coeff k = ((gComp i).coeff k).val := by
        unfold liftZModPoly
        rw [poly_finset_sum_coeff]
        simp only [Polynomial.coeff_monomial, Finsupp.single_apply]
        rw [Finset.sum_ite_eq']
        by_cases hk : k ∈ (gComp i).support
        · simp [hk]
        · have h0 : (gComp i).coeff k = 0 := not_not.mp (Polynomial.mem_support_iff.not.mp hk)
          simp [hk, h0]
      rw [hlift_k, hgi_k]
      simp
    simp_rw [hterm]
    exact hsum_coeff (g.coeff k)
  refine ⟨gComp, hg_eq, fun hg_ne ↦ ?_, fun qZ hqZ ↦ ?_⟩
  · by_contra hall
    push Not at hall
    apply hg_ne
    rw [hg_eq]
    refine Finset.sum_eq_zero fun i _ ↦ ?_
    rw [hall i]
    simp [liftZModPoly]
  · intro qR
    have hqR : qR.Monic := hqZ.map _
    have hmod_sum : g %ₘ qR =
        ∑ i : ι,
          (liftZModPoly (gComp i %ₘ qZ.map (Int.castRingHom (ZMod (n i))))).map
            (Int.castRingHom R) * Polynomial.C (e i) := by
      have hcomp := fun i : ι ↦
        additive_component_divByMonic_eq (hn i) (he_ord i) (gComp i) hqZ
      have hdiv_sum :
          (∑ i : ι, (liftZModPoly (gComp i %ₘ qZ.map (Int.castRingHom (ZMod (n i))))).map
            (Int.castRingHom R) * Polynomial.C (e i)) +
          qR * (∑ i : ι, (liftZModPoly (gComp i /ₘ qZ.map (Int.castRingHom (ZMod (n i))))).map
            (Int.castRingHom R) * Polynomial.C (e i)) = g := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib, hg_eq]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        have hi := hcomp i
        rw [← hi.1, ← hi.2]
        exact Polynomial.modByMonic_add_div _ qR
      have hdeg_sum :
          (∑ i : ι, (liftZModPoly (gComp i %ₘ qZ.map (Int.castRingHom (ZMod (n i))))).map
            (Int.castRingHom R) * Polynomial.C (e i)).degree < qR.degree := by
        refine (Polynomial.degree_sum_le _ _).trans_lt ?_
        rw [Finset.sup_lt_iff (by
          rw [Polynomial.degree_eq_natDegree hqR.ne_zero]; exact WithBot.bot_lt_coe _)]
        intro i _
        rw [← (hcomp i).2]
        exact Polynomial.degree_modByMonic_lt _ hqR
      exact (Polynomial.div_modByMonic_unique _ _ hqR ⟨hdiv_sum, hdeg_sum⟩).2
    refine ⟨hmod_sum, ?_⟩
    rw [hmod_sum]
    constructor
    · intro hsum0 i
      ext k
      have hk := congrArg (fun p : Polynomial R ↦ p.coeff k) hsum0
      rw [poly_finset_sum_coeff, Polynomial.coeff_zero] at hk
      have hψ := congrArg (fun r : R ↦ ψ r i) hk
      rw [map_zero, map_sum] at hψ
      have hterm : ∀ j : ι,
          ψ (((liftZModPoly (gComp j %ₘ qZ.map (Int.castRingHom (ZMod (n j))))).map
            (Int.castRingHom R) * Polynomial.C (e j)).coeff k) i =
          if j = i then (gComp i %ₘ qZ.map (Int.castRingHom (ZMod (n i)))).coeff k else 0 := by
        intro j
        have : NeZero (n j) := ⟨by have := hn j; omega⟩
        rw [Polynomial.coeff_mul_C, Polynomial.coeff_map]
        let rj := gComp j %ₘ qZ.map (Int.castRingHom (ZMod (n j)))
        have hlift_k : (liftZModPoly rj).coeff k = (rj.coeff k).val := by
          unfold liftZModPoly
          rw [poly_finset_sum_coeff]
          simp only [Polynomial.coeff_monomial, Finsupp.single_apply]
          rw [Finset.sum_ite_eq']
          by_cases hks : k ∈ rj.support
          · simp [hks]
          · have h0 : rj.coeff k = 0 := not_not.mp (Polynomial.mem_support_iff.not.mp hks)
            simp [hks, h0]
        change ψ (((liftZModPoly rj).coeff k : R) * e j) i = _
        rw [hlift_k]
        simp only [Int.cast_natCast, ← nsmul_eq_mul, map_nsmul, e, ψ.apply_symm_apply]
        by_cases hji : j = i
        · subst hji
          simp [DirectSum.smul_apply, rj]
        · simp [hji, DirectSum.smul_apply, DirectSum.of_apply]
      have hval : (∑ j : ι,
          ψ (((liftZModPoly (gComp j %ₘ qZ.map (Int.castRingHom (ZMod (n j))))).map
            (Int.castRingHom R) * Polynomial.C (e j)).coeff k)) i =
          (gComp i %ₘ qZ.map (Int.castRingHom (ZMod (n i)))).coeff k := by
        rw [DirectSum.sum_apply]
        simp_rw [hterm]
        simp
      rw [hval] at hψ
      simpa using hψ
    · intro hall
      refine Finset.sum_eq_zero fun i _ ↦ ?_
      rw [hall i]
      simp [liftZModPoly]

end CslibFrontier.Algebra
