module

public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.ModelTheory.Algebra.Ring.Basic
public import Mathlib.ModelTheory.Complexity
public import Mathlib.RingTheory.AlgebraicIndependent.Defs
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Data.Finsupp.Weight
import Mathlib.RingTheory.AlgebraicIndependent.Basic

/-!
# Fast-Growing Integer Specialization of Quantifier-Free Ring Formulas

Over any characteristic-zero field admitting `r` elements algebraically independent over `ℚ`, a
quantifier-free first-order formula in the language of rings whose polynomial equations have total
degree `< D` and integer coefficients strictly bounded by `C` in absolute value holds on every
sufficiently fast-growing integer sequence (`β₀ ≥ C`, `β_{j+1} ≥ C · D^{j+1} · β_j^D`) whenever it
holds on all `ℚ`-algebraically independent `r`-tuples.

## Main definitions

* `CslibFrontier.Foundations.ModelTheory.ringTermToPoly`: translates a term in
  `FirstOrder.Language.ring` into an integer multivariate polynomial.
* `CslibFrontier.Foundations.ModelTheory.BoundedFormulaPolyBounds` and
  `CslibFrontier.Foundations.ModelTheory.FormulaPolyBounds`: degree and coefficient bounds on every
  polynomial equation appearing in a quantifier-free `FirstOrder.Language.ring` formula.

## Main results

* `CslibFrontier.Foundations.ModelTheory.realize_ringTerm_eq_aeval`: realizing a ring term in any
  compatible commutative ring equals evaluating `ringTermToPoly`.
* `CslibFrontier.Foundations.ModelTheory.realize_of_algebraicIndependent_of_fastGrowth`:
  specialization from `ℚ`-algebraically independent tuples to fast-growing integer sequences.
-/

public section

namespace CslibFrontier.Foundations.ModelTheory

open MvPolynomial FirstOrder FirstOrder.Language

/-- The integer polynomial computed by a term in `FirstOrder.Language.ring`. -/
noncomputable def ringTermToPoly {α : Type*} : Language.ring.Term α → MvPolynomial α ℤ
  | .var a => X a
  | .func .add ts => ringTermToPoly (ts 0) + ringTermToPoly (ts 1)
  | .func .mul ts => ringTermToPoly (ts 0) * ringTermToPoly (ts 1)
  | .func .neg ts => -ringTermToPoly (ts 0)
  | .func .zero _ => 0
  | .func .one _ => 1

/-- Realizing a `Language.ring` term in any compatible commutative ring evaluates its integer
polynomial. -/
theorem realize_ringTerm_eq_aeval (R : Type*) [CommRing R] [FirstOrder.Ring.CompatibleRing R]
    {α : Type*} (t : Language.ring.Term α) (v : α → R) :
    t.realize v = aeval v (ringTermToPoly t) := by
  induction t with
  | var a => simp [ringTermToPoly]
  | func f ts ih =>
    cases f with
    | add => simp [ringTermToPoly, Term.realize, FirstOrder.Ring.CompatibleRing.funMap_add, ih]
    | mul => simp [ringTermToPoly, Term.realize, FirstOrder.Ring.CompatibleRing.funMap_mul, ih]
    | neg => simp [ringTermToPoly, Term.realize, FirstOrder.Ring.CompatibleRing.funMap_neg, ih]
    | zero => simp [ringTermToPoly, Term.realize, FirstOrder.Ring.CompatibleRing.funMap_zero]
    | one => simp [ringTermToPoly, Term.realize, FirstOrder.Ring.CompatibleRing.funMap_one]

/-- Degree `< D` and integer-coefficient bound `< C` on every polynomial equation `t₁ - t₂ = 0`
occurring in a quantifier-free `Language.ring` bounded formula. -/
def BoundedFormulaPolyBounds {r : ℕ} :
    {k : ℕ} → Language.ring.BoundedFormula (Fin r) k → ℕ → ℕ → Prop
  | _, .falsum, _, _ => True
  | _, .equal t₁ t₂, D, C =>
    let p : MvPolynomial (Fin r ⊕ Fin _) ℤ := ringTermToPoly t₁ - ringTermToPoly t₂
    p ≠ 0 → p.totalDegree < D ∧ ∀ m : Fin r ⊕ Fin _ →₀ ℕ, (p.coeff m).natAbs < C
  | _, .rel _ _, _, _ => True
  | _, .imp φ₁ φ₂, D, C => BoundedFormulaPolyBounds φ₁ D C ∧ BoundedFormulaPolyBounds φ₂ D C
  | _, .all _, _, _ => False

/-- Degree `< D` and integer-coefficient bound `< C` on every polynomial equation `t₁ - t₂ = 0`
occurring in a quantifier-free `Language.ring` formula. -/
abbrev FormulaPolyBounds {r : ℕ} (φ : Language.ring.Formula (Fin r)) (D C : ℕ) : Prop :=
  BoundedFormulaPolyBounds φ D C

private lemma eval_ne_zero_of_fast_growth :
    ∀ {r D C : ℕ} (p : MvPolynomial (Fin r) ℤ),
      p ≠ 0 →
      p.totalDegree < D →
      (∀ m : Fin r →₀ ℕ, (p.coeff m).natAbs < C) →
      ∀ β : Fin r → ℤ,
        (∀ h : 0 < r, (C : ℤ) ≤ β ⟨0, h⟩) →
        (∀ j : ℕ, (hj : j + 1 < r) →
          (C : ℤ) * (D : ℤ) ^ (j + 1) * (β ⟨j, by omega⟩) ^ D ≤ β ⟨j + 1, hj⟩) →
        eval β p ≠ 0 := by
  intro r
  induction r with
  | zero =>
    intro D C p hp _ _ β _ _
    have hp_eq : p = MvPolynomial.C (p.coeff 0) := by
      ext m
      have hm : m = 0 := Finsupp.ext fun i => Fin.elim0 i
      subst hm
      rw [MvPolynomial.coeff_C]
      simp
    have hcoeff_ne : p.coeff 0 ≠ 0 := by
      intro h0
      rw [h0, map_zero] at hp_eq
      exact hp hp_eq
    rw [hp_eq, eval_C]
    exact hcoeff_ne
  | succ k ih =>
    intro D C p hp hdeg hcoeff β hβ0 hβstep
    have hD_pos : 1 ≤ D := Nat.pos_of_ne_zero fun hD0 => by rw [hD0] at hdeg; omega
    have hC_pos : 1 ≤ C := by
      have hne_supp : p.support.Nonempty := by
        by_contra hempty
        rw [Finset.not_nonempty_iff_eq_empty] at hempty
        apply hp
        ext m
        have hm : m ∉ p.support := by simp [hempty]
        simpa using MvPolynomial.notMem_support_iff.mp hm
      obtain ⟨m, hm⟩ := hne_supp
      have hcm : (p.coeff m).natAbs < C := hcoeff m
      have hne : (p.coeff m).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (mem_support_iff.mp hm)
      omega
    have hβ_mono : ∀ i j : Fin (k + 1), i ≤ j → 1 ≤ β i ∧ β i ≤ β j := by
      have hstep1 : ∀ t : ℕ, (ht : t < k + 1) → 1 ≤ β ⟨t, ht⟩ := by
        intro t
        induction t with
        | zero =>
          intro ht
          have := hβ0 (Nat.zero_lt_succ k)
          omega
        | succ t iht =>
          intro ht
          have h1 := iht (by omega)
          have h2 := hβstep t ht
          have hpow : (1 : ℤ) ≤ (β ⟨t, by omega⟩) ^ D := one_le_pow₀ h1
          have hD1 : (1 : ℤ) ≤ (D : ℤ) ^ (t + 1) := one_le_pow₀ (by exact_mod_cast hD_pos)
          have hC1 : (1 : ℤ) ≤ (C : ℤ) := by exact_mod_cast hC_pos
          have hCD : (1 : ℤ) ≤ (C : ℤ) * (D : ℤ) ^ (t + 1) := by nlinarith
          nlinarith
      have hstep_le : ∀ t : ℕ, (ht : t + 1 < k + 1) → β ⟨t, by omega⟩ ≤ β ⟨t + 1, ht⟩ := by
        intro t ht
        have h1 := hstep1 t (by omega)
        have h2 := hβstep t ht
        have hpow : β ⟨t, by omega⟩ ≤ (β ⟨t, by omega⟩) ^ D :=
          le_self_pow₀ h1 (by omega)
        have hCD : (1 : ℤ) ≤ (C : ℤ) * (D : ℤ) ^ (t + 1) := by
          have hD1 : (1 : ℤ) ≤ (D : ℤ) ^ (t + 1) := one_le_pow₀ (by exact_mod_cast hD_pos)
          have hC1 : (1 : ℤ) ≤ (C : ℤ) := by exact_mod_cast hC_pos
          nlinarith
        nlinarith
      intro i j hij
      refine ⟨hstep1 i.val i.isLt, ?_⟩
      obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (Fin.le_iff_val_le_val.mp hij)
      have haux : ∀ d : ℕ, (h : i.val + d < k + 1) → β i ≤ β ⟨i.val + d, h⟩ := by
        intro d
        induction d with
        | zero => intro _; exact le_rfl
        | succ d ihd =>
          intro h
          exact (ihd (by omega)).trans (hstep_le (i.val + d) h)
      have hj_eq : j = ⟨i.val + d, by omega⟩ := Fin.ext hd
      rw [hj_eq]
      exact haux d (by omega)
    let eRot : Fin (k + 1) ≃ Fin (k + 1) :=
      { toFun := fun i => if h : i.val < k then (⟨i.val, h⟩ : Fin k).succ else 0
        invFun := fun i => Fin.cases (Fin.last k) Fin.castSucc i
        left_inv := fun i => by
          by_cases h : i.val < k
          · simp [h]
          · have : i = Fin.last k := Fin.ext (by simp only [Fin.val_last]; omega)
            simp [this]
        right_inv := fun i => by
          refine Fin.cases ?_ ?_ i
          · simp
          · intro j
            simp [j.isLt] }
    let pRot : MvPolynomial (Fin (k + 1)) ℤ := rename eRot p
    let q : Polynomial (MvPolynomial (Fin k) ℤ) := finSuccEquiv ℤ k pRot
    let β' : Fin k → ℤ := fun i => β i.castSucc
    have hq_eval : eval β p = Polynomial.eval (β (Fin.last k)) (q.map (eval β')) := by
      have h1 : eval β p = eval (Fin.cons (β (Fin.last k)) β') pRot := by
        rw [eval_rename]
        refine congrArg (fun v => eval v p) (funext fun i => ?_)
        by_cases h : i.val < k
        · simp only [eRot, Equiv.coe_fn_mk, h, ↓reduceDIte, Function.comp_apply, Fin.cons_succ, β']
          rfl
        · have : i = Fin.last k := Fin.ext (by simp only [Fin.val_last]; omega)
          simp [eRot, this]
      rw [h1]
      exact MvPolynomial.eval_eq_eval_mv_eval' β' (β (Fin.last k)) pRot
    have hpRot_ne : pRot ≠ 0 := fun h0 =>
      hp (rename_injective eRot eRot.injective (by simpa using h0))
    have hpRot_deg : pRot.totalDegree < D :=
      lt_of_le_of_lt (MvPolynomial.totalDegree_rename_le eRot p) hdeg
    have hpRot_coeff : ∀ m : Fin (k + 1) →₀ ℕ, (pRot.coeff m).natAbs < C := by
      intro m
      have hm : pRot.coeff m = p.coeff (m.equivMapDomain eRot.symm) := by
        have h := coeff_rename_mapDomain eRot eRot.injective p (m.equivMapDomain eRot.symm)
        have heq : (m.equivMapDomain eRot.symm).mapDomain eRot = m := by
          ext i
          rw [Finsupp.mapDomain_equiv_apply]
          simp [Finsupp.equivMapDomain_apply]
        simpa [pRot, heq] using h
      rw [hm]
      exact hcoeff _
    have hq_ne : q ≠ 0 := by
      intro h0
      exact hpRot_ne ((finSuccEquiv ℤ k).injective (by simpa [q] using h0))
    have hq_coeff_deg : ∀ e : ℕ, (q.coeff e).totalDegree < D := by
      intro e
      dsimp only [q]
      by_cases he : ((finSuccEquiv ℤ k) pRot).coeff e = 0
      · rw [he, totalDegree_zero]
        omega
      · have hle := MvPolynomial.totalDegree_coeff_finSuccEquiv_add_le pRot e he
        omega
    have hq_coeff_bound : ∀ (e : ℕ) (m : Fin k →₀ ℕ), ((q.coeff e).coeff m).natAbs < C := by
      intro e m
      rw [MvPolynomial.finSuccEquiv_coeff_coeff]
      exact hpRot_coeff (m.cons e)
    let d : ℕ := q.natDegree
    have hd_lt : d < D := by
      have hle : d ≤ pRot.totalDegree := by
        rw [show d = degreeOf 0 pRot from MvPolynomial.natDegree_finSuccEquiv pRot]
        exact degreeOf_le_totalDegree pRot 0
      omega
    have hlead_ne : q.coeff d ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hq_ne
    have hlead_eval_ne : eval β' (q.coeff d) ≠ 0 := by
      refine ih (q.coeff d) hlead_ne (hq_coeff_deg d) (hq_coeff_bound d) β' ?_ ?_
      · intro hkpos
        exact hβ0 (by omega)
      · intro j hj
        exact hβstep j (by omega)
    have hlead_abs_ge : (1 : ℤ) ≤ |eval β' (q.coeff d)| := by
      have : (0 : ℤ) < |eval β' (q.coeff d)| := abs_pos.mpr hlead_eval_ne
      omega
    rw [hq_eval, Polynomial.eval_eq_sum_range' (n := d + 1)]
    · rw [Finset.sum_range_succ, Polynomial.coeff_map]
      by_cases hd0 : d = 0
      · rw [hd0]
        simpa [hd0] using hlead_eval_ne
      · let B : ℤ := β (Fin.last k)
        have hB_ge : (1 : ℤ) ≤ B := (hβ_mono (Fin.last k) (Fin.last k) le_rfl).1
        have hterm_le : ∀ e : ℕ, |eval β' (q.coeff e)| ≤ B - 1 := by
          intro e
          have hsum_abs : |eval β' (q.coeff e)| ≤
              ∑ m ∈ (q.coeff e).support,
                |(q.coeff e).coeff m| * ∏ i : Fin k, |β' i| ^ (m i) := by
            rw [eval_eq']
            refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun m _ => ?_)
            simp only [abs_mul, Finset.abs_prod, abs_pow, le_refl]
          have hcard : ((q.coeff e).support).card ≤ D ^ k := by
            let toTuple : (Fin k →₀ ℕ) → (Fin k → Fin D) :=
              fun m i => ⟨min (m i) (D - 1), by omega⟩
            have hinj : Set.InjOn toTuple ((q.coeff e).support : Set (Fin k →₀ ℕ)) := by
              intro m₁ hm₁ m₂ hm₂ heq
              have hdeg1 : m₁.degree < D := by
                have hle : m₁.degree ≤ (q.coeff e).totalDegree :=
                  Finset.le_sup (f := fun s : Fin k →₀ ℕ => s.sum fun _ n => n) hm₁
                exact lt_of_le_of_lt hle (hq_coeff_deg e)
              have hdeg2 : m₂.degree < D := by
                have hle : m₂.degree ≤ (q.coeff e).totalDegree :=
                  Finset.le_sup (f := fun s : Fin k →₀ ℕ => s.sum fun _ n => n) hm₂
                exact lt_of_le_of_lt hle (hq_coeff_deg e)
              have hdeg_eq : ∀ m : Fin k →₀ ℕ, m.degree = ∑ j : Fin k, m j := fun m => by
                change ∑ j ∈ m.support, m j = ∑ j : Fin k, m j
                exact Finset.sum_subset (Finset.subset_univ _) fun j _ hj =>
                  Finsupp.notMem_support_iff.mp hj
              ext i
              have hi1 : m₁ i < D := by
                have hle : m₁ i ≤ ∑ j : Fin k, m₁ j :=
                  Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
                rw [hdeg_eq] at hdeg1
                omega
              have hi2 : m₂ i < D := by
                have hle : m₂ i ≤ ∑ j : Fin k, m₂ j :=
                  Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
                rw [hdeg_eq] at hdeg2
                omega
              have hval := congrArg (fun f : Fin k → Fin D => (f i).val) heq
              simp only [toTuple] at hval
              omega
            have hle := Finset.card_le_card_of_injOn toTuple (fun _ _ => Finset.mem_univ _) hinj
            simpa [Fintype.card_fun, Fintype.card_fin] using hle
          cases k with
          | zero =>
            have hB0 : (C : ℤ) ≤ B := hβ0 (Nat.zero_lt_succ 0)
            have hle1 : ∑ m ∈ (q.coeff e).support,
                |(q.coeff e).coeff m| * ∏ i : Fin 0, |β' i| ^ (m i) ≤ (C : ℤ) - 1 := by
              have hsub : (q.coeff e).support ⊆ {0} := by
                intro m _
                rw [Finset.mem_singleton]
                exact Finsupp.ext fun i => Fin.elim0 i
              calc
                ∑ m ∈ (q.coeff e).support, |(q.coeff e).coeff m| * ∏ i : Fin 0, |β' i| ^ (m i)
                  ≤ ∑ m ∈ ({0} : Finset (Fin 0 →₀ ℕ)), |(q.coeff e).coeff m| * 1 := by
                    refine Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => ?_
                    positivity
                _ = |(q.coeff e).coeff 0| := by simp
                _ ≤ (C : ℤ) - 1 := by
                    have h := hq_coeff_bound e 0
                    have habs : |(q.coeff e).coeff 0| = (((q.coeff e).coeff 0).natAbs : ℤ) :=
                      Int.abs_eq_natAbs _
                    omega
            exact hsum_abs.trans (hle1.trans (by omega))
          | succ j =>
            let βPrev : ℤ := β ⟨j, by omega⟩
            have hβPrev_ge : (1 : ℤ) ≤ βPrev := (hβ_mono ⟨j, by omega⟩ ⟨j, by omega⟩ le_rfl).1
            have hterm_mon : ∀ m ∈ (q.coeff e).support,
                |(q.coeff e).coeff m| * ∏ i : Fin (j + 1), |β' i| ^ (m i) ≤
                  ((C : ℤ) - 1) * βPrev ^ D := by
              intro m hm
              have hcm : |(q.coeff e).coeff m| ≤ (C : ℤ) - 1 := by
                have h := hq_coeff_bound e m
                have habs : |(q.coeff e).coeff m| = (((q.coeff e).coeff m).natAbs : ℤ) :=
                  Int.abs_eq_natAbs _
                omega
              have hm_deg : (∑ i : Fin (j + 1), m i) ≤ D := by
                have hle : m.degree ≤ (q.coeff e).totalDegree :=
                  Finset.le_sup (f := fun s : Fin (j + 1) →₀ ℕ => s.sum fun _ n => n) hm
                have hsum_eq : m.degree = ∑ i : Fin (j + 1), m i := by
                  change ∑ i ∈ m.support, m i = ∑ i : Fin (j + 1), m i
                  exact Finset.sum_subset (Finset.subset_univ _) fun i _ hi =>
                    Finsupp.notMem_support_iff.mp hi
                have hlt_e := hq_coeff_deg e
                omega
              have hprod_le : ∏ i : Fin (j + 1), |β' i| ^ (m i) ≤ βPrev ^ D := by
                have hstep : ∀ s : Finset (Fin (j + 1)),
                    ∏ i ∈ s, |β' i| ^ (m i) ≤ ∏ i ∈ s, βPrev ^ (m i) := by
                  intro s
                  induction s using Finset.induction_on with
                  | empty => simp
                  | insert a s ha ihs =>
                    rw [Finset.prod_insert ha, Finset.prod_insert ha]
                    have hba := hβ_mono a.castSucc ⟨j, by omega⟩
                      (Fin.le_iff_val_le_val.mpr (by
                        simp only [Fin.val_castSucc]
                        exact Nat.le_of_lt_succ a.isLt))
                    have habs : |β' a| = β' a := abs_of_nonneg (by dsimp only [β']; omega)
                    have hpow : |β' a| ^ (m a) ≤ βPrev ^ (m a) := by
                      rw [habs]
                      exact pow_le_pow_left₀ (le_trans zero_le_one hba.1) hba.2 (m a)
                    exact mul_le_mul hpow ihs
                      (Finset.prod_nonneg fun _ _ => by positivity) (by positivity)
                have h2 : ∏ i : Fin (j + 1), βPrev ^ (m i) =
                    βPrev ^ (∑ i : Fin (j + 1), m i) := by
                  rw [Finset.prod_pow_eq_pow_sum]
                exact (hstep Finset.univ).trans (h2.le.trans (pow_le_pow_right₀ hβPrev_ge hm_deg))
              exact mul_le_mul hcm hprod_le (by positivity) (by omega)
            have hsum_le :
                ∑ m ∈ (q.coeff e).support,
                  |(q.coeff e).coeff m| * ∏ i : Fin (j + 1), |β' i| ^ (m i) ≤
                ((q.coeff e).support).card * (((C : ℤ) - 1) * βPrev ^ D) := by
              simpa [Finset.sum_const, nsmul_eq_mul] using Finset.sum_le_sum hterm_mon
            have hcard_z : (((q.coeff e).support).card : ℤ) ≤ (D : ℤ) ^ (j + 1) := by
              exact_mod_cast hcard
            have hstep_b : (C : ℤ) * (D : ℤ) ^ (j + 1) * βPrev ^ D ≤ B :=
              hβstep j (Nat.lt_succ_self (j + 1))
            have hDpow_ge : (1 : ℤ) ≤ (D : ℤ) ^ (j + 1) :=
              one_le_pow₀ (by exact_mod_cast hD_pos)
            have hβpow_ge : (1 : ℤ) ≤ βPrev ^ D := one_le_pow₀ hβPrev_ge
            have h1 : (((q.coeff e).support).card : ℤ) * (((C : ℤ) - 1) * βPrev ^ D) ≤
                (D : ℤ) ^ (j + 1) * (((C : ℤ) - 1) * βPrev ^ D) :=
              mul_le_mul_of_nonneg_right hcard_z (by nlinarith)
            have h2 : (D : ℤ) ^ (j + 1) * (((C : ℤ) - 1) * βPrev ^ D) ≤
                (C : ℤ) * (D : ℤ) ^ (j + 1) * βPrev ^ D - 1 := by
              have hprod1 : (1 : ℤ) ≤ (D : ℤ) ^ (j + 1) * βPrev ^ D := by nlinarith
              nlinarith
            exact hsum_abs.trans (hsum_le.trans (h1.trans (h2.trans (by omega))))
        have htail_lt :
            |∑ e ∈ Finset.range d, (q.map (eval β')).coeff e * B ^ e| < B ^ d := by
          have hsum1 :
              |∑ e ∈ Finset.range d, (q.map (eval β')).coeff e * B ^ e| ≤
              ∑ e ∈ Finset.range d, (B - 1) * B ^ e := by
            refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun e _ => ?_)
            rw [abs_mul, Polynomial.coeff_map, abs_pow, abs_of_nonneg (by omega : (0 : ℤ) ≤ B)]
            exact mul_le_mul_of_nonneg_right (hterm_le e) (by positivity)
          have hgeom : ∑ e ∈ Finset.range d, (B - 1) * B ^ e = B ^ d - 1 := by
            induction d with
            | zero => simp
            | succ t iht =>
              rw [Finset.sum_range_succ, iht]
              ring
          rw [hgeom] at hsum1
          omega
        intro hzero
        have heq : eval β' (q.coeff d) * B ^ d =
            -(∑ e ∈ Finset.range d, (q.map (eval β')).coeff e * B ^ e) := by
          linarith
        have habs := congrArg abs heq
        rw [abs_mul, abs_neg, abs_pow, abs_of_nonneg (by omega : (0 : ℤ) ≤ B)] at habs
        have hge : B ^ d ≤ |eval β' (q.coeff d)| * B ^ d := by
          have : (0 : ℤ) ≤ B ^ d := by positivity
          nlinarith
        linarith
    · exact Nat.lt_succ_of_le Polynomial.natDegree_map_le

/-- Over any characteristic-zero field `E` admitting an `r`-tuple algebraically independent over
`ℚ`, any quantifier-free `Language.ring` formula whose polynomial equations have degree `< D` and
integer coefficients strictly bounded by `C` in absolute value, and which holds on all
`ℚ`-algebraically independent tuples in `E^r`, also holds on every integer sequence `β₀ ≥ C`,
`β_{j+1} ≥ C · D^{j+1} · β_j^D`. -/
theorem realize_of_algebraicIndependent_of_fastGrowth (E : Type*) [Field E] [CharZero E]
    [FirstOrder.Ring.CompatibleRing E] {r D C : ℕ} (φ : Language.ring.Formula (Fin r))
    (hQF : φ.IsQF)
    (hbounds : FormulaPolyBounds φ D C)
    (hex : ∃ α : Fin r → E, AlgebraicIndependent ℚ α)
    (hindep : ∀ α : Fin r → E, AlgebraicIndependent ℚ α → φ.Realize α)
    (β : Fin r → ℤ)
    (hβ₀ : ∀ h : 0 < r, (C : ℤ) ≤ β ⟨0, h⟩)
    (hβ_step : ∀ j : ℕ, (hj : j + 1 < r) →
      (C : ℤ) * (D : ℤ) ^ (j + 1) * (β ⟨j, by omega⟩) ^ D ≤ β ⟨j + 1, hj⟩) :
    φ.Realize (fun i => (β i : E)) := by
  obtain ⟨α, hα⟩ := hex
  have hα_real : φ.Realize α := hindep α hα
  let eSum : Fin r ⊕ Fin 0 ≃ Fin r :=
    { toFun := Sum.elim id Fin.elim0
      invFun := Sum.inl
      left_inv := fun x => by cases x with | inl _ => rfl | inr j => exact Fin.elim0 j
      right_inv := fun _ => rfl }
  have hterm_eq : ∀ (v : Fin r → E) (t : Language.ring.Term (Fin r ⊕ Fin 0)),
      t.realize (Sum.elim v Fin.elim0) = aeval v (rename eSum (ringTermToPoly t)) := by
    intro v t
    rw [realize_ringTerm_eq_aeval E, aeval_rename]
    refine congrArg (fun f => aeval f (ringTermToPoly t)) (funext fun x => ?_)
    cases x with
    | inl _ => rfl
    | inr j => exact Fin.elim0 j
  have hiff : ∀ ψ : Language.ring.Formula (Fin r),
      ψ.IsQF → BoundedFormulaPolyBounds ψ D C → (ψ.Realize α ↔ ψ.Realize (fun i => (β i : E))) := by
    intro ψ hψQF hψB
    induction hψQF with
    | falsum => exact Iff.rfl
    | of_isAtomic hat =>
      cases hat with
      | equal t₁ t₂ =>
        change (t₁.realize (Sum.elim α Fin.elim0) = t₂.realize (Sum.elim α Fin.elim0)) ↔
          (t₁.realize (Sum.elim (fun i => (β i : E)) Fin.elim0) =
            t₂.realize (Sum.elim (fun i => (β i : E)) Fin.elim0))
        rw [hterm_eq α t₁, hterm_eq α t₂, hterm_eq (fun i => (β i : E)) t₁,
          hterm_eq (fun i => (β i : E)) t₂]
        let p₀ : MvPolynomial (Fin r ⊕ Fin 0) ℤ := ringTermToPoly t₁ - ringTermToPoly t₂
        let p₁ : MvPolynomial (Fin r) ℤ := rename eSum (ringTermToPoly t₁)
        let p₂ : MvPolynomial (Fin r) ℤ := rename eSum (ringTermToPoly t₂)
        let p : MvPolynomial (Fin r) ℤ := p₁ - p₂
        have hp_eq : p = rename eSum p₀ := (map_sub _ _ _).symm
        have hα_zero : aeval α p₁ = aeval α p₂ ↔ p = 0 := by
          constructor
          · intro heq
            have hp0 : aeval α p = 0 := by simp [p, heq]
            have hhom : (algebraMap ℚ E).comp (Int.castRingHom ℚ) = Int.castRingHom E :=
              RingHom.ext_int _ _
            have hq0 : aeval α (p.map (Int.castRingHom ℚ)) = 0 := by
              rw [aeval_def, eval₂_map, hhom]
              simpa [aeval_def] using hp0
            have hmap0 : p.map (Int.castRingHom ℚ) = 0 :=
              hα.eq_zero_of_aeval_eq_zero _ hq0
            exact MvPolynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
              (by simpa using hmap0)
          · intro hp0
            have : p₁ = p₂ := sub_eq_zero.mp hp0
            rw [this]
        have hβ_zero :
            aeval (fun i => (β i : E)) p₁ = aeval (fun i => (β i : E)) p₂ ↔ p = 0 := by
          constructor
          · intro heq
            by_contra hpne
            have hpE : aeval (fun i => (β i : E)) p = 0 := by simp [p, heq]
            have hpZ : ((eval β p : ℤ) : E) = 0 := by
              have hcast : (Int.castRingHom E) (eval β p) = aeval (fun i => (β i : E)) p := by
                induction p using MvPolynomial.induction_on with
                | C c => simp
                | add p₁ p₂ ih₁ ih₂ => simp [map_add, ih₁, ih₂]
                | mul_X p₁ i ih => simp [map_mul, ih]
              exact hcast.trans hpE
            have hpZ0 : eval β p = 0 := Int.cast_eq_zero.mp hpZ
            have hp0_ne : p₀ ≠ 0 := fun h0 => hpne (by rw [hp_eq, h0, map_zero])
            obtain ⟨hdeg₀, hcoeff₀⟩ := hψB hp0_ne
            have hdeg : p.totalDegree < D := by
              rw [hp_eq]
              exact lt_of_le_of_lt (MvPolynomial.totalDegree_rename_le eSum p₀) hdeg₀
            have hcoeff : ∀ m : Fin r →₀ ℕ, (p.coeff m).natAbs < C := by
              intro m
              rw [hp_eq]
              have hm : (rename eSum p₀).coeff m = p₀.coeff (m.equivMapDomain eSum.symm) := by
                have h := coeff_rename_mapDomain eSum eSum.injective p₀
                  (m.equivMapDomain eSum.symm)
                have heq' : (m.equivMapDomain eSum.symm).mapDomain eSum = m := by
                  ext i
                  rw [Finsupp.mapDomain_equiv_apply]
                  simp [Finsupp.equivMapDomain_apply]
                simpa [heq'] using h
              rw [hm]
              exact hcoeff₀ _
            exact eval_ne_zero_of_fast_growth p hpne hdeg hcoeff β hβ₀ hβ_step hpZ0
          · intro hp0
            have : p₁ = p₂ := sub_eq_zero.mp hp0
            rw [this]
        exact hα_zero.trans hβ_zero.symm
      | rel r _ => cases r
    | imp h₁ h₂ ih₁ ih₂ =>
      simp only [Formula.Realize, BoundedFormula.realize_imp]
      exact imp_congr (ih₁ hψB.1) (ih₂ hψB.2)
  exact (hiff φ hQF hbounds).mp hα_real

end CslibFrontier.Foundations.ModelTheory
