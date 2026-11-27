/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.Noncommutative.QuadraticSpanningSet
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Main Quadratic Lower Bound for Noncommutative Circuits

This module formalizes the unconditional quadratic size lower bound for noncommutative circuits:
* the master inequality: $n^n \le (s + n + 1)\sum_{r=0}^n s^r / r!$;
* the explicit lower bound $s > n^2 / (2e)$ for every $n \ge 1$ (and $s \ge n^2 / (2e)$ for all
  $n \in \mathbb{N}$);
* the unconditional $\Omega(n^2)$ lower bound (`thm_main` and `thm_intro_main`) for fan-in 2
  noncommutative arithmetic circuits computing $\mathrm{Pal}_{n,n}(X, Y)$;
* the low-syntactic-degree $\Omega(n^{1+c})$ corollary (`thm_low_syn_deg`);
* the corollary for unweighted `Cslib.Circuits.Circuit (arithSignature F) (n + n) 1`;
* the matching $O(n^2)$ homogeneous circuit construction `palCircuitWeighted` witnessing tightness
  and joint non-vacuity of the main theorem.

## Main definitions

* `CslibFrontier.Circuits.Arithmetic.Noncommutative.palCircuitWeighted`: explicit homogeneous fan-in
  2 noncommutative
  circuit of size $1 + 2n + 3nd$ computing $\mathrm{Pal}_{n,d}(X, Y)$.

## Main results

* `CslibFrontier.Circuits.Arithmetic.Noncommutative.master_inequality`.
* `CslibFrontier.Circuits.Arithmetic.Noncommutative.size_gt_sq_div_two_mul_exp`: explicit bound $s >
  n^2 / (2e)$ for
  all $n \ge 1$.
* `CslibFrontier.Circuits.Arithmetic.Noncommutative.thm_main` and `thm_intro_main`.
* `CslibFrontier.Circuits.Arithmetic.Noncommutative.thm_low_syn_deg`.
* `CslibFrontier.Circuits.Arithmetic.Noncommutative.cslib_circuit_quadratic_lower_bound`.
* `CslibFrontier.Circuits.Arithmetic.Noncommutative.nonvacuity_circuit_computes_palPoly`.
-/

public section

namespace CslibFrontier.Circuits.Arithmetic.Noncommutative

open _root_.FreeAlgebra

section MasterInequality

variable {F : Type*} [Field F]

/-- Master inequality: any fan-in 2 noncommutative arithmetic circuit of size
`s` computing `palPoly F n n` satisfies $n^n \le (s + n + 1)\sum_{r=0}^n \frac{s^r}{r!}$. -/
theorem master_inequality {n : ℕ} (Ψ : NoncommCircuit F (Fin n ⊕ Fin n))
    (hΨ : Ψ.eval = palPoly F n n) :
    (n : ℝ) ^ n ≤
      ((Ψ.size + n + 1 : ℕ) : ℝ) *
        ∑ r ∈ Finset.range (n + 1), (Ψ.size : ℝ) ^ r / (r.factorial : ℝ) := by
  classical
  let Ψ' := Ψ.normalize
  have hnorm : Ψ'.IsNormalized := Ψ.isNormalized_normalize
  have heval' : Ψ'.eval = palPoly F n n := Ψ.normalize_eval.trans hΨ
  have hsize' : Ψ'.size = Ψ.size := Ψ.normalize_size
  let last : Fin (numSynDegs Ψ') :=
    ⟨numSynDegs Ψ' - 1, Nat.sub_lt (numSynDegs_pos Ψ') Nat.zero_lt_one⟩
  let surv := survivingGenerators Ψ'
  have hspan_sub :
      Submodule.span F (coeffXSet (palPoly F n n)) ≤
        Submodule.span F (CslibFrontier.FreeAlgebra.homogeneousComponent n ''
          (surv : Set (FreeAlgebra F (Fin n)))) := by
    rw [Submodule.span_le]
    intro c hc
    have hmem_span : c ∈ Submodule.span F (spanningSet Ψ' last : Set (FreeAlgebra F (Fin n))) :=
      coeffXSet_palPoly_subset_span Ψ' hnorm heval' hc
    have hhom : CslibFrontier.FreeAlgebra.homogeneousComponent n c = c :=
      CslibFrontier.FreeAlgebra.homogeneousComponent_eq_self_of_isHomogeneous
        (isHomogeneous_of_mem_coeffXSet_palPoly F n hc)
    rw [← hhom]
    have hmap := Submodule.apply_mem_span_image_of_mem_span
      (CslibFrontier.FreeAlgebra.homogeneousComponent n) hmem_span
    have hsub_img :
        CslibFrontier.FreeAlgebra.homogeneousComponent n ''
            (spanningSet Ψ' last : Set (FreeAlgebra F (Fin n))) ⊆
          insert 0 (CslibFrontier.FreeAlgebra.homogeneousComponent n ''
            (surv : Set (FreeAlgebra F (Fin n)))) := by
      rintro _ ⟨v, hv, rfl⟩
      by_cases h0 : CslibFrontier.FreeAlgebra.homogeneousComponent n v = 0
      · rw [h0]; exact Set.mem_insert _ _
      · exact Set.mem_insert_of_mem _
          ⟨v, Finset.mem_coe.mpr ((mem_survivingGenerators Ψ').mpr ⟨hv, h0⟩), rfl⟩
    have hspan_insert :
        Submodule.span F
            (insert (0 : FreeAlgebra F (Fin n))
              (CslibFrontier.FreeAlgebra.homogeneousComponent n ''
                (surv : Set (FreeAlgebra F (Fin n))))) =
          Submodule.span F (CslibFrontier.FreeAlgebra.homogeneousComponent n ''
            (surv : Set (FreeAlgebra F (Fin n)))) := by
      rw [Submodule.span_insert_zero]
    exact hspan_insert ▸ Submodule.span_mono hsub_img hmap
  have hfin_le : n ^ n ≤ surv.card := by
    have hfin_mod : Module.Finite F
        (Submodule.span F (CslibFrontier.FreeAlgebra.homogeneousComponent n ''
          (surv : Set (FreeAlgebra F (Fin n))))) :=
      Module.Finite.span_of_finite F
        ((Finset.finite_toSet surv).image (CslibFrontier.FreeAlgebra.homogeneousComponent n))
    have h1 : Module.finrank F (Submodule.span F (coeffXSet (palPoly F n n))) ≤
        Module.finrank F
          (Submodule.span F (CslibFrontier.FreeAlgebra.homogeneousComponent n ''
            (surv : Set (FreeAlgebra F (Fin n))))) :=
      Submodule.finrank_mono hspan_sub
    rw [finrank_span_coeffXSet_palPoly] at h1
    have h2 : Module.finrank F
        (Submodule.span F (CslibFrontier.FreeAlgebra.homogeneousComponent n ''
          (surv : Set (FreeAlgebra F (Fin n))))) ≤
        (surv.image (CslibFrontier.FreeAlgebra.homogeneousComponent n)).card := by
      have hcoe :
          (CslibFrontier.FreeAlgebra.homogeneousComponent n '' (surv : Set (FreeAlgebra F (Fin
            n)))) =
            ((surv.image (CslibFrontier.FreeAlgebra.homogeneousComponent n) :
              Finset (FreeAlgebra F (Fin n))) : Set (FreeAlgebra F (Fin n))) := by
        simp [Finset.coe_image]
      rw [hcoe]
      simpa using finrank_span_le_card (R := F)
        ((surv.image (CslibFrontier.FreeAlgebra.homogeneousComponent n) :
          Finset (FreeAlgebra F (Fin n))) : Set (FreeAlgebra F (Fin n)))
    exact h1.trans (h2.trans Finset.card_image_le)
  have hsurv := thm_surviving_generators Ψ'
  rw [hsize'] at hsurv
  have hnat : ((n ^ n : ℕ) : ℝ) ≤ (surv.card : ℝ) := by exact_mod_cast hfin_le
  simpa using hnat.trans hsurv

end MasterInequality

section MainLowerBound

variable {F : Type*} [Field F]

/-- For `n ≥ 1`, any circuit computing `palPoly F n n` has at least `2 * n` vertices (at least one
leaf for each variable `x_i` and `y_i`). -/
theorem two_mul_le_size_of_eval_eq_palPoly {n : ℕ} (hn : 1 ≤ n)
    (Ψ : NoncommCircuit F (Fin n ⊕ Fin n)) (hΨ : Ψ.eval = palPoly F n n) :
    2 * n ≤ Ψ.size := by
  classical
  have hvar : ∀ x : Fin n ⊕ Fin n, ∃ i : Fin Ψ.size, Ψ.gates i = .var x := by
    intro x
    apply NoncommCircuit.exists_var_gate_of_lift_ne Ψ x
    rw [hΨ]
    intro hfix
    let u0 : Fin n → Fin n := match x with
      | .inl i => fun _ ↦ i
      | .inr i => fun _ ↦ i
    let w0 : FreeMonoid (Fin n ⊕ Fin n) :=
      FreeMonoid.ofFn (Sum.inl ∘ u0) * FreeMonoid.ofFn (Sum.inr ∘ (u0 ∘ Fin.rev))
    have hcoeff1 : FreeAlgebra.coeff w0 (palPoly F n n) = 1 := by
      rw [coeff_palPoly_ofFn]
      simp
    have hzero : FreeAlgebra.lift F (fun y ↦ if y = x then 0 else ι F y)
        (palPoly F n n) =
        ∑ u : Fin n → Fin n,
          FreeAlgebra.lift F (fun y ↦ if y = x then 0 else ι F y)
            (FreeMonoid.lift (ι F)
              (FreeMonoid.ofFn (Sum.inl ∘ u) * FreeMonoid.ofFn (Sum.inr ∘ (u ∘ Fin.rev)))) := by
      rw [palPoly, map_sum]
    have hterm_eq : ∀ u : Fin n → Fin n,
        FreeAlgebra.coeff w0
          (FreeAlgebra.lift F (fun y ↦ if y = x then 0 else ι F y)
            (FreeMonoid.lift (ι F)
              (FreeMonoid.ofFn (Sum.inl ∘ u) * FreeMonoid.ofFn (Sum.inr ∘ (u ∘ Fin.rev))))) =
        0 := by
      intro u
      by_cases hx_in : ∃ j : Fin n,
          (Sum.inl (u j) : Fin n ⊕ Fin n) = x ∨ Sum.inr (u (Fin.rev j)) = x
      · have hmul_zero :
            FreeAlgebra.lift F (fun y ↦ if y = x then 0 else ι F y)
              (FreeMonoid.lift (ι F)
                (FreeMonoid.ofFn (Sum.inl ∘ u) * FreeMonoid.ofFn (Sum.inr ∘ (u ∘ Fin.rev)))) =
              0 := by
          obtain ⟨j, hj⟩ := hx_in
          have hfactor : ∀ (k : ℕ) (v : Fin k → Fin n ⊕ Fin n),
              (∃ t, v t = x) →
                FreeAlgebra.lift F (fun y ↦ if y = x then 0 else ι F y)
                  (FreeMonoid.lift (ι F) (FreeMonoid.ofFn v)) = 0 := by
            intro k
            induction k with
            | zero => rintro v ⟨t, -⟩; exact Fin.elim0 t
            | succ k ih =>
              intro v ⟨t, ht⟩
              have hv : v = Fin.cons (v 0) (fun r ↦ v r.succ) := by
                ext r; refine Fin.cases rfl (fun _ ↦ rfl) r
              rw [hv, FreeMonoid.ofFn_cons, map_mul, map_mul, FreeMonoid.lift_eval_of,
                FreeAlgebra.lift_ι_apply]
              revert ht
              refine Fin.cases ?_ (fun r ↦ ?_) t
              · intro ht0
                simp [ht0]
              · intro htr
                rw [ih (fun r ↦ v r.succ) ⟨r, htr⟩, mul_zero]
          rw [map_mul, map_mul]
          rcases hj with hjl | hjr
          · rw [hfactor n (Sum.inl ∘ u) ⟨j, hjl⟩, zero_mul]
          · rw [hfactor n (Sum.inr ∘ (u ∘ Fin.rev)) ⟨j, hjr⟩, mul_zero]
        rw [hmul_zero, map_zero]
      · push Not at hx_in
        have hlift_id :
            FreeAlgebra.lift F (fun y ↦ if y = x then 0 else ι F y)
              (FreeMonoid.lift (ι F)
                (FreeMonoid.ofFn (Sum.inl ∘ u) * FreeMonoid.ofFn (Sum.inr ∘ (u ∘ Fin.rev)))) =
              FreeMonoid.lift (ι F)
                (FreeMonoid.ofFn (Sum.inl ∘ u) * FreeMonoid.ofFn (Sum.inr ∘ (u ∘ Fin.rev))) := by
          have hfactor : ∀ (k : ℕ) (v : Fin k → Fin n ⊕ Fin n),
              (∀ t, v t ≠ x) →
                FreeAlgebra.lift F (fun y ↦ if y = x then 0 else ι F y)
                  (FreeMonoid.lift (ι F) (FreeMonoid.ofFn v)) =
                  FreeMonoid.lift (ι F) (FreeMonoid.ofFn v) := by
            intro k
            induction k with
            | zero => intro v _; simp
            | succ k ih =>
              intro v hne
              have hv : v = Fin.cons (v 0) (fun r ↦ v r.succ) := by
                ext r; refine Fin.cases rfl (fun _ ↦ rfl) r
              rw [hv, FreeMonoid.ofFn_cons, map_mul, map_mul, FreeMonoid.lift_eval_of,
                FreeAlgebra.lift_ι_apply, ih (fun r ↦ v r.succ) (fun r ↦ hne r.succ)]
              simp [hne 0]
          rw [map_mul, map_mul]
          exact congrArg₂ (· * ·)
            (hfactor n (Sum.inl ∘ u) (fun j ↦ (hx_in j).1))
            (hfactor n (Sum.inr ∘ (u ∘ Fin.rev)) (fun j ↦ (hx_in j).2))
        rw [hlift_id, coeff_lift_ι]
        refine Finsupp.single_eq_of_ne' fun heq ↦ ?_
        have hu_eq := (FreeMonoid.ofFn_mul_ofFn_injective heq).1
        have hval := congrFun hu_eq ⟨0, hn⟩
        cases x with
        | inl i =>
          have : (Sum.inl (u ⟨0, hn⟩) : Fin n ⊕ Fin n) = Sum.inl i := by simpa [u0] using hval
          exact (hx_in ⟨0, hn⟩).1 this
        | inr i =>
          have : u ⟨0, hn⟩ = i :=
            Sum.inl.inj (β := Fin n) (by simpa [u0] using hval)
          have hrev0 : u (Fin.rev (Fin.rev ⟨0, hn⟩)) = i := by simpa using this
          exact (hx_in (Fin.rev ⟨0, hn⟩)).2 (congrArg Sum.inr hrev0)
    have hcoeff0 : FreeAlgebra.coeff w0
        (FreeAlgebra.lift F (fun y ↦ if y = x then 0 else ι F y) (palPoly F n n)) = 0 := by
      rw [hzero, map_sum]
      exact Finset.sum_eq_zero fun u _ ↦ hterm_eq u
    rw [hfix, hcoeff1] at hcoeff0
    exact one_ne_zero hcoeff0
  choose f hf using hvar
  have hfinj : Function.Injective f := by
    intro x₁ x₂ h
    have h1 := hf x₁
    rw [h, hf x₂] at h1
    exact GateKind.var.inj h1.symm
  have hcard := Fintype.card_le_of_injective f hfinj
  simp only [Fintype.card_sum, Fintype.card_fin] at hcard
  omega

/-- Elementary exponential domination: $(n + 2)^2 (n + 1) < 4 \cdot 2^n$ for all $n \ge 10$. -/
private theorem poly_lt_four_mul_two_pow :
    ∀ n : ℕ, 10 ≤ n → (n + 2) ^ 2 * (n + 1) < 4 * 2 ^ n := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have hstep : (k + 3) ^ 2 * (k + 2) ≤ 2 * ((k + 2) ^ 2 * (k + 1)) := by nlinarith
    calc
      (k + 3) ^ 2 * (k + 2) ≤ 2 * ((k + 2) ^ 2 * (k + 1)) := hstep
      _ < 2 * (4 * 2 ^ k) := Nat.mul_lt_mul_of_pos_left ih (by norm_num)
      _ = 4 * 2 ^ (k + 1) := by ring

/-- Elementary bound `2.7 < Real.exp 1` proved directly from the partial sum `∑_{k<5} 1/k!`. -/
private theorem exp_one_gt_two_point_seven : (2.7 : ℝ) < Real.exp 1 := by
  have hsum := Real.sum_le_exp_of_nonneg (x := (1 : ℝ)) (by norm_num) 5
  have hval : (∑ i ∈ Finset.range 5, (1 : ℝ) ^ i / (i.factorial : ℝ)) = 65 / 24 := by
    norm_num [Finset.sum_range_succ, Nat.factorial]
  linarith

/-- Elementary bound `Real.exp 1 ≤ 4` proved directly from `Real.add_one_le_exp (-1 / 2)`. -/
private theorem exp_one_le_four : Real.exp 1 ≤ 4 := by
  have h := Real.add_one_le_exp (-(1 / 2 : ℝ))
  rw [Real.exp_neg] at h
  have hpos : (0 : ℝ) < Real.exp (1 / 2) := Real.exp_pos _
  have hle2 : Real.exp (1 / 2) ≤ 2 := by
    have h1 : (1 / 2 : ℝ) ≤ (Real.exp (1 / 2))⁻¹ := by linarith
    have h2 : (1 / 2 : ℝ) * Real.exp (1 / 2) ≤ 1 := by
      simpa [inv_mul_cancel₀ hpos.ne'] using mul_le_mul_of_nonneg_right h1 hpos.le
    linarith
  have hsq : Real.exp 1 = Real.exp (1 / 2) * Real.exp (1 / 2) := by
    rw [← Real.exp_add]
    norm_num
  rw [hsq]
  nlinarith

/-- Explicit quadratic lower bound: for every $n \ge 1$, every fan-in 2 noncommutative arithmetic
circuit computing $\mathrm{Pal}_{n,n}(X, Y)$ has size $s > \frac{n^2}{2e}$. -/
theorem size_gt_sq_div_two_mul_exp {n : ℕ} (hn : 1 ≤ n)
    (Ψ : NoncommCircuit F (Fin n ⊕ Fin n)) (hΨ : Ψ.eval = palPoly F n n) :
    (n : ℝ) ^ 2 / (2 * Real.exp 1) < (Ψ.size : ℝ) := by
  have hs_ge : 2 * n ≤ Ψ.size := two_mul_le_size_of_eval_eq_palPoly hn Ψ hΨ
  have he_gt : (2.7 : ℝ) < Real.exp 1 := exp_one_gt_two_point_seven
  have he_pos : (0 : ℝ) < 2 * Real.exp 1 := by positivity
  by_cases hsmall : n ≤ 10
  · rw [div_lt_iff₀ he_pos]
    have hn_r : (n : ℝ) ≤ 10 := by exact_mod_cast hsmall
    have hs_r : (2 * n : ℝ) ≤ (Ψ.size : ℝ) := by exact_mod_cast hs_ge
    have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    nlinarith
  · have hn11 : 11 ≤ n := by omega
    by_contra hle
    push Not at hle
    have hs_gt_n : (n : ℝ) < (Ψ.size : ℝ) := by
      have : (n : ℝ) < (2 * n : ℝ) := by
        have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
        linarith
      exact this.trans_le (by exact_mod_cast hs_ge)
    -- Step 1: monotonicity of `t_r = s^r / r!` for `0 ≤ r ≤ n`.
    have hstep_r : ∀ m : ℕ, m < n →
        (Ψ.size : ℝ) ^ m / (m.factorial : ℝ) ≤
          (Ψ.size : ℝ) ^ (m + 1) / ((m + 1).factorial : ℝ) := by
      intro m hmn
      have hm1 : (m + 1 : ℝ) ≤ (Ψ.size : ℝ) :=
        (show (m + 1 : ℝ) ≤ (n : ℝ) by exact_mod_cast hmn).trans hs_gt_n.le
      have hfac_pos : (0 : ℝ) < (m.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos m)
      have hm1_pos : (0 : ℝ) < (m + 1 : ℝ) := by positivity
      rw [Nat.factorial_succ, Nat.cast_mul, pow_succ]
      rw [div_le_div_iff₀ hfac_pos (by positivity)]
      have : (Ψ.size : ℝ) ^ m * ((m + 1 : ℝ) * (m.factorial : ℝ)) ≤
          (Ψ.size : ℝ) ^ m * (Ψ.size : ℝ) * (m.factorial : ℝ) := by
        have hpow_nn : (0 : ℝ) ≤ (Ψ.size : ℝ) ^ m := by positivity
        have h1 : (m + 1 : ℝ) * (m.factorial : ℝ) ≤ (Ψ.size : ℝ) * (m.factorial : ℝ) :=
          mul_le_mul_of_nonneg_right hm1 hfac_pos.le
        have h2 := mul_le_mul_of_nonneg_left h1 hpow_nn
        linarith
      simpa [Nat.cast_add, Nat.cast_one, mul_comm, mul_left_comm, mul_assoc] using this
    have hmono_r : ∀ a b : ℕ, a ≤ b → b ≤ n →
        (Ψ.size : ℝ) ^ a / (a.factorial : ℝ) ≤ (Ψ.size : ℝ) ^ b / (b.factorial : ℝ) := by
      intro a b hab hbn
      induction b, hab using Nat.le_induction with
      | base => exact le_rfl
      | succ m hm ih => exact (ih (by omega)).trans (hstep_r m (by omega))
    have hterm_le : ∀ r ∈ Finset.range (n + 1),
        (Ψ.size : ℝ) ^ r / (r.factorial : ℝ) ≤ (Ψ.size : ℝ) ^ n / (n.factorial : ℝ) :=
      fun r hr ↦ hmono_r r n (Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)) le_rfl
    have hsum_le : ∑ r ∈ Finset.range (n + 1), (Ψ.size : ℝ) ^ r / (r.factorial : ℝ) ≤
        ((n + 1 : ℕ) : ℝ) * ((Ψ.size : ℝ) ^ n / (n.factorial : ℝ)) := by
      calc
        ∑ r ∈ Finset.range (n + 1), (Ψ.size : ℝ) ^ r / (r.factorial : ℝ) ≤
            ∑ _r ∈ Finset.range (n + 1), (Ψ.size : ℝ) ^ n / (n.factorial : ℝ) :=
          Finset.sum_le_sum hterm_le
        _ = ((n + 1 : ℕ) : ℝ) * ((Ψ.size : ℝ) ^ n / (n.factorial : ℝ)) := by
          simp [Finset.sum_const, nsmul_eq_mul]
    -- Step 2: `n^n / n! ≤ exp(n) = (exp 1)^n`.
    have hfac_bound : (n : ℝ) ^ n / (n.factorial : ℝ) ≤ (Real.exp 1) ^ n := by
      have h := Real.pow_div_factorial_le_exp (n : ℝ) (Nat.cast_nonneg n) n
      have hexp : Real.exp (n : ℝ) = (Real.exp 1) ^ n := by
        rw [← Real.exp_nat_mul, mul_one]
      exact hexp ▸ h
    have hmaster := master_inequality Ψ hΨ
    have h1 : (n : ℝ) ^ n ≤
        ((Ψ.size + n + 1 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ) *
          ((Ψ.size : ℝ) ^ n / (n.factorial : ℝ)) := by
      have hnn : (0 : ℝ) ≤ ((Ψ.size + n + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
      have := hmaster.trans (mul_le_mul_of_nonneg_left hsum_le hnn)
      simpa [mul_assoc] using this
    have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hpow_pos : (0 : ℝ) < (n : ℝ) ^ n := pow_pos hn_pos n
    have hdiv_fac : (Ψ.size : ℝ) ^ n / (n.factorial : ℝ) ≤
        (Real.exp 1 * (Ψ.size : ℝ) / (n : ℝ)) ^ n := by
      rw [mul_div_assoc, mul_pow, div_pow]
      have hmul := mul_le_mul_of_nonneg_left hfac_bound
        (div_nonneg (pow_nonneg (Nat.cast_nonneg Ψ.size) n) hpow_pos.le)
      have hcancel : (Ψ.size : ℝ) ^ n / (n : ℝ) ^ n * ((n : ℝ) ^ n / (n.factorial : ℝ)) =
          (Ψ.size : ℝ) ^ n / (n.factorial : ℝ) := by
        field_simp
      rw [hcancel] at hmul
      refine hmul.trans_eq ?_
      ring
    have hes_le : Real.exp 1 * (Ψ.size : ℝ) / (n : ℝ) ≤ (n : ℝ) / 2 := by
      rw [div_le_iff₀ hn_pos]
      have hle' : (Ψ.size : ℝ) * (2 * Real.exp 1) ≤ (n : ℝ) ^ 2 :=
        (le_div_iff₀ he_pos).mp hle
      linarith
    have hpow_half : (Real.exp 1 * (Ψ.size : ℝ) / (n : ℝ)) ^ n ≤ ((n : ℝ) / 2) ^ n :=
      pow_le_pow_left₀ (by positivity) hes_le n
    have h2 : (n : ℝ) ^ n ≤
        ((Ψ.size + n + 1 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ) * ((n : ℝ) / 2) ^ n := by
      have hnn : (0 : ℝ) ≤ ((Ψ.size + n + 1 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ) := by positivity
      exact h1.trans (mul_le_mul_of_nonneg_left (hdiv_fac.trans hpow_half) hnn)
    rw [div_pow] at h2
    have h2pow_pos : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
    have h3 : (2 : ℝ) ^ n ≤ ((Ψ.size + n + 1 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ) := by
      have hmul := mul_le_mul_of_nonneg_right h2 (div_nonneg h2pow_pos.le hpow_pos.le)
      have hlhs : (n : ℝ) ^ n * ((2 : ℝ) ^ n / (n : ℝ) ^ n) = (2 : ℝ) ^ n := by field_simp
      have hrhs :
          ((Ψ.size + n + 1 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ) * ((n : ℝ) ^ n / (2 : ℝ) ^ n) *
            ((2 : ℝ) ^ n / (n : ℝ) ^ n) =
          ((Ψ.size + n + 1 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ) := by field_simp
      rw [hlhs, hrhs] at hmul
      exact hmul
    have hs_le_quarter : (Ψ.size : ℝ) ≤ (n : ℝ) ^ 2 / 4 := by
      refine hle.trans ?_
      exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
    have h4 : 4 * (2 : ℝ) ^ n ≤ ((n : ℝ) + 2) ^ 2 * ((n : ℝ) + 1) := by
      have hsn : ((Ψ.size + n + 1 : ℕ) : ℝ) ≤ (n : ℝ) ^ 2 / 4 + (n : ℝ) + 1 := by
        push_cast; linarith
      have hn1_nn : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
      have h5 := h3.trans (mul_le_mul_of_nonneg_right hsn hn1_nn)
      push_cast at h5
      nlinarith
    have h5 : (4 * 2 ^ n : ℕ) ≤ (n + 2) ^ 2 * (n + 1) := by
      exact_mod_cast h4
    exact absurd (poly_lt_four_mul_two_pow n (by omega)) (not_lt.mpr h5)

/-- Explicit bound for all `n : ℕ`: `(n : ℝ)^2 / (2 * Real.exp 1) ≤ (Ψ.size : ℝ)`. -/
theorem size_ge_sq_div_two_mul_exp (n : ℕ) (Ψ : NoncommCircuit F (Fin n ⊕ Fin n))
    (hΨ : Ψ.eval = palPoly F n n) :
    (n : ℝ) ^ 2 / (2 * Real.exp 1) ≤ (Ψ.size : ℝ) := by
  by_cases hn : 1 ≤ n
  · exact (size_gt_sq_div_two_mul_exp hn Ψ hΨ).le
  · have h0 : n = 0 := by omega
    subst h0
    simp

/-- Quadratic lower bound: Every fan-in 2 noncommutative arithmetic circuit computing
$\mathrm{Pal}_{n,n}(X, Y)$ has size $\Omega(n^2)$. -/
theorem thm_main :
    ∃ c : ℝ, 0 < c ∧
      ∀ (n : ℕ) (Ψ : NoncommCircuit F (Fin n ⊕ Fin n)),
        Ψ.eval = palPoly F n n → c * (n : ℝ) ^ 2 ≤ (Ψ.size : ℝ) := by
  refine ⟨1 / (2 * Real.exp 1), by positivity, fun n Ψ hΨ ↦ ?_⟩
  have h := size_ge_sq_div_two_mul_exp n Ψ hΨ
  rw [one_div_mul_eq_div]
  exact h

/-- Asymptotic `IsBigO` lower bound: for any family of
fan-in 2 noncommutative arithmetic circuits $\Psi_n$ computing $\mathrm{Pal}_{n,n}(X, Y)$,
$n^2 = O(\mathrm{size}(\Psi_n))$, i.e., $\mathrm{size}(\Psi_n) = \Omega(n^2)$. -/
theorem thm_intro_main (Ψ : ∀ n : ℕ, NoncommCircuit F (Fin n ⊕ Fin n))
    (hΨ : ∀ n : ℕ, (Ψ n).eval = palPoly F n n) :
    (fun n : ℕ ↦ (n : ℝ) ^ 2) =O[Filter.atTop] (fun n : ℕ ↦ ((Ψ n).size : ℝ)) := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨2 * Real.exp 1, Filter.Eventually.of_forall fun n ↦ ?_⟩
  have h := size_ge_sq_div_two_mul_exp n (Ψ n) (hΨ n)
  have he_pos : (0 : ℝ) < 2 * Real.exp 1 := by positivity
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (Nat.cast_nonneg _)]
  exact (div_le_iff₀ he_pos).mp h |> fun h' ↦ by linarith

/-- Low-syntactic-degree corollary: every fan-in 2 noncommutative arithmetic circuit computing
$\mathrm{Pal}_{n,n}(X, Y)$ with syntactic degree $O(n)$ has size $\Omega(n^{1+c})$ for some
constant $c > 0$ (immediate corollary of `thm_main` with $c = 1$). -/
theorem thm_low_syn_deg :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (D : ℕ) (n : ℕ) (Ψ : NoncommCircuit F (Fin n ⊕ Fin n)),
        Ψ.circuitSynDeg ≤ D * n → Ψ.eval = palPoly F n n →
          C * (n : ℝ) ^ (1 + c) ≤ (Ψ.size : ℝ) := by
  obtain ⟨C, hC, hbound⟩ := thm_main (F := F)
  refine ⟨1, by norm_num, C, hC, fun _ n Ψ _ hΨ ↦ ?_⟩
  have h := hbound n Ψ hΨ
  simpa [show (1 : ℝ) + 1 = 2 by norm_num, Real.rpow_two] using h

end MainLowerBound

section CslibCircuitCorollary

variable {F : Type*} [Field F]

/-- The palindrome polynomial $\mathrm{Pal}_{n,n}(X, Y)$ transferred to `FreeAlgebra F (Fin (n+n))`
via `finSumFinEquiv`. -/
noncomputable def palPolyFin (F : Type*) [CommSemiring F] (n : ℕ) :
    FreeAlgebra F (Fin (n + n)) :=
  FreeAlgebra.lift F (fun s ↦ ι F (finSumFinEquiv s)) (palPoly F n n)

/-- Corollary for unweighted `Cslib.Circuits.Circuit (arithSignature F) (n + n) 1`:
any such circuit computing `palPolyFin F n` has gate count $c.\mathrm{size} > n^2/(2e) - 2n$ for
all $n \ge 1$. -/
theorem cslib_circuit_size_gt {n : ℕ} (hn : 1 ≤ n)
    (c : Cslib.Circuits.Circuit (Cslib.Circuits.arithSignature F) (n + n) 1)
    (hc : c.noncommPolynomial 0 = palPolyFin F n) :
    (n : ℝ) ^ 2 / (2 * Real.exp 1) - 2 * (n : ℝ) < (c.size : ℝ) := by
  let Ψ0 : NoncommCircuit F (Fin (n + n)) := NoncommCircuit.ofCslibCircuit c
  let Ψ : NoncommCircuit F (Fin n ⊕ Fin n) := {
    size := Ψ0.size
    output := Ψ0.output
    gates := fun i ↦
      match Ψ0.gates i with
      | .const a => .const a
      | .var x => .var (finSumFinEquiv.symm x)
      | .add a b wa wb => .add a b wa wb
      | .mul a b wa wb => .mul a b wa wb
  }
  have hmap : ∀ i : Fin Ψ.size,
      FreeAlgebra.lift F (fun s ↦ ι F (finSumFinEquiv s)) (Ψ.evalGate i) = Ψ0.evalGate i := by
    intro i
    induction h : i.val using Nat.strong_induction_on generalizing i with
    | ind k ih =>
      subst h
      cases hg : Ψ0.gates i with
      | const a =>
        have hg' : Ψ.gates i = .const a := by simp [Ψ, hg]
        rw [Ψ.evalGate_const hg', Ψ0.evalGate_const hg, AlgHom.commutes]
      | var x =>
        have hg' : Ψ.gates i = .var (finSumFinEquiv.symm x) := by simp [Ψ, hg]
        rw [Ψ.evalGate_var hg', Ψ0.evalGate_var hg, FreeAlgebra.lift_ι_apply,
          Equiv.apply_symm_apply]
      | add a b wa wb =>
        have hg' : Ψ.gates i = .add a b wa wb := by simp [Ψ, hg]
        rw [Ψ.evalGate_add hg', Ψ0.evalGate_add hg, map_add, map_smul, map_smul,
          ih a.val a.isLt _ rfl, ih b.val b.isLt _ rfl]
      | mul a b wa wb =>
        have hg' : Ψ.gates i = .mul a b wa wb := by simp [Ψ, hg]
        rw [Ψ.evalGate_mul hg', Ψ0.evalGate_mul hg, map_mul, map_smul, map_smul,
          ih a.val a.isLt _ rfl, ih b.val b.isLt _ rfl]
  have hΨ_eval : Ψ.eval = palPoly F n n := by
    have hinj : Function.Injective
        (FreeAlgebra.lift F (fun s : Fin n ⊕ Fin n ↦ ι F (finSumFinEquiv s))) := by
      have hleft :
          (FreeAlgebra.lift F (fun x : Fin (n + n) ↦ ι F (finSumFinEquiv.symm x))).comp
            (FreeAlgebra.lift F (fun s : Fin n ⊕ Fin n ↦ ι F (finSumFinEquiv s))) =
            AlgHom.id F _ := by
        apply FreeAlgebra.hom_ext
        ext s
        simp
      exact Function.LeftInverse.injective (DFunLike.congr_fun hleft)
    apply hinj
    rw [Ψ.eval_eq_evalGate_output, hmap, ← Ψ0.eval_eq_evalGate_output,
      NoncommCircuit.ofCslibCircuit_eval, hc, palPolyFin]
  have hbound := size_gt_sq_div_two_mul_exp hn Ψ hΨ_eval
  have hsize : (Ψ.size : ℝ) = (2 * (n : ℝ)) + (c.size : ℝ) := by
    have hs : Ψ.size = n + n + c.size := NoncommCircuit.ofCslibCircuit_size c
    rw [hs]
    push_cast
    ring
  linarith

/-- Asymptotic quadratic lower bound for `Cslib.Circuits.Circuit (arithSignature F) (n + n) 1`
computing `palPolyFin F n`. -/
theorem cslib_circuit_quadratic_lower_bound
    (c : ∀ n : ℕ, Cslib.Circuits.Circuit (Cslib.Circuits.arithSignature F) (n + n) 1)
    (hc : ∀ n : ℕ, (c n).noncommPolynomial 0 = palPolyFin F n) :
    (fun n : ℕ ↦ (n : ℝ) ^ 2) =O[Filter.atTop] (fun n : ℕ ↦ ((c n).size : ℝ)) := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨4 * Real.exp 1, Filter.eventually_atTop.mpr ⟨32, fun n hn ↦ ?_⟩⟩
  have h := cslib_circuit_size_gt (by omega) (c n) (hc n)
  have he_lt : Real.exp 1 ≤ 4 := exp_one_le_four
  have he_pos : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have hn_r : (32 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (Nat.cast_nonneg _)]
  have h1 : (n : ℝ) ^ 2 / (4 * Real.exp 1) < ((c n).size : ℝ) := by
    have h2 : 2 * (n : ℝ) ≤ (n : ℝ) ^ 2 / (4 * Real.exp 1) := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith
    have h3 : (n : ℝ) ^ 2 / (2 * Real.exp 1) - (n : ℝ) ^ 2 / (4 * Real.exp 1) =
        (n : ℝ) ^ 2 / (4 * Real.exp 1) := by ring
    linarith
  have hmul := (div_le_iff₀ (by positivity)).mp h1.le
  linarith

end CslibCircuitCorollary

section UpperBoundAndNonVacuity

variable (F : Type*) [CommSemiring F]

/-- Step helper for the $O(n^2)$ circuit computing $\mathrm{Pal}_{n,d}(X,Y)$:
given a circuit computing $P$ of size `s` with the `2n` variable leaves at indices `0..2n-1`,
appending `3*n + 2` gates computes $\sum_{i < n} x_i P y_i$. -/
private def appendPalStep {n : ℕ} (Ψ : NoncommCircuit F (Fin n ⊕ Fin n))
    (hvars : 2 * n ≤ Ψ.size) : NoncommCircuit F (Fin n ⊕ Fin n) :=
  { size := Ψ.size + (3 * n + 2)
    output := ⟨Ψ.size + 3 * n + 1, by omega⟩
    gates := fun i ↦
      if hi : i.val < Ψ.size then
        match Ψ.gates ⟨i.val, hi⟩ with
        | .const c => .const c
        | .var x => .var x
        | .add a b wa wb => .add a b wa wb
        | .mul a b wa wb => .mul a b wa wb
      else if h0 : i.val = Ψ.size then
        .const 0
      else
        let off := i.val - (Ψ.size + 1)
        have hdm : 3 * (off / 3) + off % 3 = off := by
          simpa [mul_comm] using Nat.div_add_mod off 3
        if hj : off / 3 < n then
          if hrem0 : off % 3 = 0 then
            .mul ⟨off / 3, by omega⟩ ⟨Ψ.output.val, by omega⟩ 1 1
          else if hrem1 : off % 3 = 1 then
            .mul ⟨Ψ.size + 1 + 3 * (off / 3), by omega⟩ ⟨n + off / 3, by omega⟩ 1 1
          else if hprev : off / 3 = 0 then
            .add ⟨Ψ.size, by omega⟩ ⟨Ψ.size + 1 + 3 * (off / 3) + 1, by omega⟩ 1 1
          else
            .add ⟨Ψ.size + 1 + 3 * (off / 3 - 1) + 2, by omega⟩
              ⟨Ψ.size + 1 + 3 * (off / 3) + 1, by omega⟩ 1 1
        else
          if hn0 : n = 0 then
            .const 0
          else
            .add ⟨Ψ.size + 1 + 3 * (n - 1) + 2, by omega⟩ ⟨Ψ.size, by omega⟩ 1 0
  }

/-- Auxiliary pair bundling `palCircuitWeighted F n d` with the invariant `2 * n ≤ size`. -/
private def palCircuitWeightedAux (n : ℕ) :
    ℕ → { Ψ : NoncommCircuit F (Fin n ⊕ Fin n) // 2 * n ≤ Ψ.size }
  | 0 => ⟨{
      size := 2 * n + 1
      output := ⟨2 * n, by omega⟩
      gates := fun i ↦
        if h1 : i.val < n then .var (Sum.inl ⟨i.val, h1⟩)
        else if h2 : i.val < 2 * n then .var (Sum.inr ⟨i.val - n, by omega⟩)
        else .const 1
    }, by dsimp only; omega⟩
  | d + 1 =>
      let prev := palCircuitWeightedAux n d
      ⟨appendPalStep F prev.1 prev.2, by
        change 2 * n ≤ prev.1.size + (3 * n + 2)
        have := prev.2
        omega⟩

/-- Explicit homogeneous fan-in 2 noncommutative arithmetic circuit computing
$\mathrm{Pal}_{n,d}(X, Y)$ of size $O(n \cdot d + n)$. -/
def palCircuitWeighted (n d : ℕ) : NoncommCircuit F (Fin n ⊕ Fin n) :=
  (palCircuitWeightedAux F n d).1

/-- The size of `palCircuitWeighted F n d` is `2 * n + 1 + d * (3 * n + 2)`. -/
theorem palCircuitWeighted_size (n d : ℕ) :
    (palCircuitWeighted F n d).size = 2 * n + 1 + d * (3 * n + 2) := by
  induction d with
  | zero => simp [palCircuitWeighted, palCircuitWeightedAux]
  | succ k ih =>
    change (palCircuitWeighted F n k).size + (3 * n + 2) = _
    rw [ih]
    ring

private theorem appendPalStep_gates_old {n : ℕ} (Ψ : NoncommCircuit F (Fin n ⊕ Fin n))
    (hvars : 2 * n ≤ Ψ.size) {i : ℕ} (hi : i < Ψ.size)
    (hi' : i < (appendPalStep F Ψ hvars).size) :
    (appendPalStep F Ψ hvars).gates ⟨i, hi'⟩ = Ψ.gates ⟨i, hi⟩ := by
  dsimp only [appendPalStep]
  rw [dite_eq_left hi]
  cases Ψ.gates ⟨i, hi⟩ <;> rfl

private theorem palCircuitWeighted_var_inl (n d : ℕ) (j : Fin n) :
    (palCircuitWeighted F n d).gates ⟨j.val, by rw [palCircuitWeighted_size]; omega⟩ =
      .var (Sum.inl j) := by
  induction d with
  | zero =>
    simp [palCircuitWeighted, palCircuitWeightedAux, j.isLt]
  | succ k ih =>
    have hlt : j.val < (palCircuitWeighted F n k).size := by
      rw [palCircuitWeighted_size]; omega
    exact (appendPalStep_gates_old F _ (palCircuitWeightedAux F n k).2 hlt _).trans ih

private theorem palCircuitWeighted_var_inr (n d : ℕ) (j : Fin n) :
    (palCircuitWeighted F n d).gates ⟨n + j.val, by rw [palCircuitWeighted_size]; omega⟩ =
      .var (Sum.inr j) := by
  induction d with
  | zero =>
    have h1 : ¬ (n + j.val < n) := by omega
    have h2 : n + j.val < 2 * n := by omega
    simp [palCircuitWeighted, palCircuitWeightedAux, h1, h2]
  | succ k ih =>
    have hlt : n + j.val < (palCircuitWeighted F n k).size := by
      rw [palCircuitWeighted_size]; omega
    exact (appendPalStep_gates_old F _ (palCircuitWeightedAux F n k).2 hlt _).trans ih

private theorem appendPalStep_evalGate_old {n : ℕ} (Ψ : NoncommCircuit F (Fin n ⊕ Fin n))
    (hvars : 2 * n ≤ Ψ.size) (i : ℕ) (hi : i < Ψ.size)
    (hi' : i < (appendPalStep F Ψ hvars).size) :
    (appendPalStep F Ψ hvars).evalGate ⟨i, hi'⟩ = Ψ.evalGate ⟨i, hi⟩ := by
  induction i using Nat.strong_induction_on with
  | _ k ih =>
    cases hg : Ψ.gates ⟨k, hi⟩ with
    | const c =>
      have hg' : (appendPalStep F Ψ hvars).gates ⟨k, hi'⟩ = .const c :=
        (appendPalStep_gates_old F Ψ hvars hi hi').trans hg
      rw [NoncommCircuit.evalGate_const _ hg', NoncommCircuit.evalGate_const _ hg]
    | var x =>
      have hg' : (appendPalStep F Ψ hvars).gates ⟨k, hi'⟩ = .var x :=
        (appendPalStep_gates_old F Ψ hvars hi hi').trans hg
      rw [NoncommCircuit.evalGate_var _ hg', NoncommCircuit.evalGate_var _ hg]
    | add a b wa wb =>
      have hg' : (appendPalStep F Ψ hvars).gates ⟨k, hi'⟩ = .add a b wa wb :=
        (appendPalStep_gates_old F Ψ hvars hi hi').trans hg
      rw [NoncommCircuit.evalGate_add _ hg', NoncommCircuit.evalGate_add _ hg,
        ih a.val a.isLt (lt_trans a.isLt hi) (lt_trans a.isLt hi'),
        ih b.val b.isLt (lt_trans b.isLt hi) (lt_trans b.isLt hi')]
    | mul a b wa wb =>
      have hg' : (appendPalStep F Ψ hvars).gates ⟨k, hi'⟩ = .mul a b wa wb :=
        (appendPalStep_gates_old F Ψ hvars hi hi').trans hg
      rw [NoncommCircuit.evalGate_mul _ hg', NoncommCircuit.evalGate_mul _ hg,
        ih a.val a.isLt (lt_trans a.isLt hi) (lt_trans a.isLt hi'),
        ih b.val b.isLt (lt_trans b.isLt hi) (lt_trans b.isLt hi')]

/-- `palCircuitWeighted F n d` computes `palPoly F n d`. -/
theorem palCircuitWeighted_eval (n d : ℕ) :
    (palCircuitWeighted F n d).eval = palPoly F n d := by
  induction d with
  | zero =>
    rw [palPoly_zero, NoncommCircuit.eval_eq_evalGate_output]
    have hg : (palCircuitWeighted F n 0).gates (palCircuitWeighted F n 0).output = .const 1 := by
      have h1 : ¬ (2 * n < n) := by omega
      simp [palCircuitWeighted, palCircuitWeightedAux, h1]
    rw [NoncommCircuit.evalGate_const _ hg, map_one]
  | succ k ih =>
    rw [palPoly_succ, ← ih]
    set Ψ := palCircuitWeighted F n k
    have hvars : 2 * n ≤ Ψ.size := (palCircuitWeightedAux F n k).2
    have hzero_gate :
        (appendPalStep F Ψ hvars).gates ⟨Ψ.size, by dsimp [appendPalStep]; omega⟩ = .const 0 := by
      have h1 : ¬ (Ψ.size < Ψ.size) := by omega
      dsimp only [appendPalStep]
      rw [dite_eq_right h1, dite_eq_left rfl]
    have hzero_val :
        (appendPalStep F Ψ hvars).evalGate ⟨Ψ.size, by dsimp [appendPalStep]; omega⟩ = 0 := by
      rw [NoncommCircuit.evalGate_const _ hzero_gate, map_zero]
    have hmul1 : ∀ j : Fin n,
        (appendPalStep F Ψ hvars).evalGate
          ⟨Ψ.size + 1 + 3 * j.val, by dsimp [appendPalStep]; omega⟩ =
        ι F (Sum.inl j) * Ψ.eval := by
      intro j
      have hgate :
          (appendPalStep F Ψ hvars).gates
            ⟨Ψ.size + 1 + 3 * j.val, by dsimp [appendPalStep]; omega⟩ =
          .mul ⟨j.val, by dsimp; omega⟩ ⟨Ψ.output.val, by dsimp; omega⟩ 1 1 := by
        have h1 : ¬ (Ψ.size + 1 + 3 * j.val < Ψ.size) := by omega
        have h2 : ¬ (Ψ.size + 1 + 3 * j.val = Ψ.size) := by omega
        have h3 : (Ψ.size + 1 + 3 * j.val - (Ψ.size + 1)) / 3 < n := by omega
        have h4 : (Ψ.size + 1 + 3 * j.val - (Ψ.size + 1)) % 3 = 0 := by omega
        dsimp only [appendPalStep]
        rw [dite_eq_right h1, dite_eq_right h2, dite_eq_left h3, dite_eq_left h4]
        congr 1; exact Fin.ext (by dsimp; omega)
      rw [NoncommCircuit.evalGate_mul _ hgate, one_smul, one_smul]
      have hvar_inl :
          (appendPalStep F Ψ hvars).evalGate ⟨j.val, by dsimp [appendPalStep]; omega⟩ =
            ι F (Sum.inl j) := by
        rw [appendPalStep_evalGate_old F Ψ hvars j.val (by omega),
          NoncommCircuit.evalGate_var _ (palCircuitWeighted_var_inl F n k j)]
      rw [hvar_inl, appendPalStep_evalGate_old F Ψ hvars Ψ.output.val Ψ.output.isLt,
        ← Ψ.eval_eq_evalGate_output]
    have hmul2 : ∀ j : Fin n,
        (appendPalStep F Ψ hvars).evalGate
          ⟨Ψ.size + 1 + 3 * j.val + 1, by dsimp [appendPalStep]; omega⟩ =
        ι F (Sum.inl j) * Ψ.eval * ι F (Sum.inr j) := by
      intro j
      have hgate :
          (appendPalStep F Ψ hvars).gates
            ⟨Ψ.size + 1 + 3 * j.val + 1, by dsimp [appendPalStep]; omega⟩ =
          .mul ⟨Ψ.size + 1 + 3 * j.val, by dsimp; omega⟩ ⟨n + j.val, by dsimp; omega⟩ 1 1 := by
        have h1 : ¬ (Ψ.size + 1 + 3 * j.val + 1 < Ψ.size) := by omega
        have h2 : ¬ (Ψ.size + 1 + 3 * j.val + 1 = Ψ.size) := by omega
        have h3 : (Ψ.size + 1 + 3 * j.val + 1 - (Ψ.size + 1)) / 3 < n := by omega
        have h4 : ¬ ((Ψ.size + 1 + 3 * j.val + 1 - (Ψ.size + 1)) % 3 = 0) := by omega
        have h5 : (Ψ.size + 1 + 3 * j.val + 1 - (Ψ.size + 1)) % 3 = 1 := by omega
        dsimp only [appendPalStep]
        rw [dite_eq_right h1, dite_eq_right h2, dite_eq_left h3, dite_eq_right h4, dite_eq_left h5]
        congr 1 <;> exact Fin.ext (by dsimp; omega)
      rw [NoncommCircuit.evalGate_mul _ hgate, one_smul, one_smul, hmul1 j]
      have hvar_inr :
          (appendPalStep F Ψ hvars).evalGate ⟨n + j.val, by dsimp [appendPalStep]; omega⟩ =
            ι F (Sum.inr j) := by
        rw [appendPalStep_evalGate_old F Ψ hvars (n + j.val) (by omega),
          NoncommCircuit.evalGate_var _ (palCircuitWeighted_var_inr F n k j)]
      rw [hvar_inr]
    have hsum : ∀ (m : ℕ) (hm : m < n),
        (appendPalStep F Ψ hvars).evalGate
          ⟨Ψ.size + 1 + 3 * m + 2, by dsimp [appendPalStep]; omega⟩ =
        ∑ j ∈ (Finset.univ : Finset (Fin n)).filter (fun j ↦ j.val ≤ m),
          ι F (Sum.inl j) * Ψ.eval * ι F (Sum.inr j) := by
      intro m
      induction m with
      | zero =>
        intro hm
        have hgate :
            (appendPalStep F Ψ hvars).gates
              ⟨Ψ.size + 1 + 3 * 0 + 2, by dsimp [appendPalStep]; omega⟩ =
            .add ⟨Ψ.size, by dsimp; omega⟩ ⟨Ψ.size + 1 + 3 * 0 + 1, by dsimp; omega⟩ 1 1 := by
          have h1 : ¬ (Ψ.size + 1 + 3 * 0 + 2 < Ψ.size) := by omega
          have h2 : ¬ (Ψ.size + 1 + 3 * 0 + 2 = Ψ.size) := by omega
          have h3 : (Ψ.size + 1 + 3 * 0 + 2 - (Ψ.size + 1)) / 3 < n := by omega
          have h4 : ¬ ((Ψ.size + 1 + 3 * 0 + 2 - (Ψ.size + 1)) % 3 = 0) := by omega
          have h5 : ¬ ((Ψ.size + 1 + 3 * 0 + 2 - (Ψ.size + 1)) % 3 = 1) := by omega
          have h6 : (Ψ.size + 1 + 3 * 0 + 2 - (Ψ.size + 1)) / 3 = 0 := by omega
          dsimp only [appendPalStep]
          rw [dite_eq_right h1, dite_eq_right h2, dite_eq_left h3, dite_eq_right h4,
            dite_eq_right h5, dite_eq_left h6]
          congr 1; exact Fin.ext (by dsimp; omega)
        rw [NoncommCircuit.evalGate_add _ hgate, one_smul, one_smul, hzero_val, zero_add]
        have hfilt : (Finset.univ : Finset (Fin n)).filter (fun j ↦ j.val ≤ 0) = {⟨0, hm⟩} := by
          ext j
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
            Fin.ext_iff]
          omega
        rw [hfilt, Finset.sum_singleton]
        exact hmul2 ⟨0, hm⟩
      | succ m ihm =>
        intro hm
        have hgate :
            (appendPalStep F Ψ hvars).gates
              ⟨Ψ.size + 1 + 3 * (m + 1) + 2, by dsimp [appendPalStep]; omega⟩ =
            .add ⟨Ψ.size + 1 + 3 * m + 2, by dsimp; omega⟩
              ⟨Ψ.size + 1 + 3 * (m + 1) + 1, by dsimp; omega⟩ 1 1 := by
          have h1 : ¬ (Ψ.size + 1 + 3 * (m + 1) + 2 < Ψ.size) := by omega
          have h2 : ¬ (Ψ.size + 1 + 3 * (m + 1) + 2 = Ψ.size) := by omega
          have h3 : (Ψ.size + 1 + 3 * (m + 1) + 2 - (Ψ.size + 1)) / 3 < n := by omega
          have h4 : ¬ ((Ψ.size + 1 + 3 * (m + 1) + 2 - (Ψ.size + 1)) % 3 = 0) := by omega
          have h5 : ¬ ((Ψ.size + 1 + 3 * (m + 1) + 2 - (Ψ.size + 1)) % 3 = 1) := by omega
          have h6 : ¬ ((Ψ.size + 1 + 3 * (m + 1) + 2 - (Ψ.size + 1)) / 3 = 0) := by omega
          dsimp only [appendPalStep]
          rw [dite_eq_right h1, dite_eq_right h2, dite_eq_left h3, dite_eq_right h4,
            dite_eq_right h5, dite_eq_right h6]
          congr 1 <;> exact Fin.ext (by dsimp; omega)
        rw [NoncommCircuit.evalGate_add _ hgate, one_smul, one_smul, ihm (by omega),
          hmul2 ⟨m + 1, hm⟩]
        have hfilt :
            (Finset.univ : Finset (Fin n)).filter (fun j ↦ j.val ≤ m + 1) =
              insert ⟨m + 1, hm⟩ ((Finset.univ : Finset (Fin n)).filter (fun j ↦ j.val ≤ m)) := by
          ext j
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
          omega
        rw [hfilt, Finset.sum_insert]
        · rw [add_comm]
        · simp
    change (appendPalStep F Ψ hvars).eval = _
    rw [NoncommCircuit.eval_eq_evalGate_output]
    by_cases hn0 : n = 0
    · subst hn0
      have hgate :
          (appendPalStep F Ψ hvars).gates (appendPalStep F Ψ hvars).output = .const 0 := by
        have h1 : ¬ (Ψ.size + 3 * 0 + 1 < Ψ.size) := by omega
        have h2 : ¬ (Ψ.size + 3 * 0 + 1 = Ψ.size) := by omega
        dsimp only [appendPalStep]
        rw [dite_eq_right h1, dite_eq_right h2]
        have hdiv : ¬ ((Ψ.size + 3 * 0 + 1 - (Ψ.size + 1)) / 3 < 0) := by omega
        rw [dite_eq_right hdiv, dite_eq_left rfl]
      rw [NoncommCircuit.evalGate_const _ hgate, map_zero]
      simp
    · have hgate :
          (appendPalStep F Ψ hvars).gates (appendPalStep F Ψ hvars).output =
            .add ⟨Ψ.size + 1 + 3 * (n - 1) + 2, by dsimp [appendPalStep]; omega⟩
              ⟨Ψ.size, by dsimp [appendPalStep]; omega⟩ 1 0 := by
        have h1 : ¬ (Ψ.size + 3 * n + 1 < Ψ.size) := by omega
        have h2 : ¬ (Ψ.size + 3 * n + 1 = Ψ.size) := by omega
        have hdiv : ¬ ((Ψ.size + 3 * n + 1 - (Ψ.size + 1)) / 3 < n) := by omega
        dsimp only [appendPalStep]
        rw [dite_eq_right h1, dite_eq_right h2, dite_eq_right hdiv, dite_eq_right hn0]
      rw [NoncommCircuit.evalGate_add _ hgate, one_smul, zero_smul, add_zero,
        hsum (n - 1) (by omega)]
      have hfilt : (Finset.univ : Finset (Fin n)).filter (fun j ↦ j.val ≤ n - 1) = Finset.univ := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
        have := j.isLt
        omega
      rw [hfilt]

/-- Joint non-vacuity and tightness witness: for every `n`, there exists a genuine fan-in 2
noncommutative arithmetic circuit computing `palPoly F n n` of size `3 * n^2 + 4 * n + 1`,
matching the `Ω(n^2)` lower bound up to a constant factor. -/
theorem nonvacuity_circuit_computes_palPoly (n : ℕ) :
    ∃ Ψ : NoncommCircuit F (Fin n ⊕ Fin n),
      Ψ.eval = palPoly F n n ∧ Ψ.size = 3 * n ^ 2 + 4 * n + 1 := by
  refine ⟨palCircuitWeighted F n n, palCircuitWeighted_eval F n n, ?_⟩
  rw [palCircuitWeighted_size]
  ring

end UpperBoundAndNonVacuity

end CslibFrontier.Circuits.Arithmetic.Noncommutative
