/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.FormulaOps
public import CslibFrontier.Computability.Circuit.Arithmetic.SPCircuit
public import CslibFrontier.Foundations.BooleanAnalysis.BooleanQuotient
public import CslibFrontier.Logics.Propositional.Algebraic.Boolean
import Mathlib.Algebra.MvPolynomial.Variables

/-!
# The Ideal Proof System (`IPS`) and Linear Variants

Algebraic propositional proof systems, Shpilka, Tzameret, and Wigderson:

* `CslibFrontier.Logic.PL.Algebraic.IPSVar`: variables `(x_1, …, x_n, y_1, …, y_m, z_1, …, z_n)`
  for refuting `m` polynomial equations in `n` Boolean variables.
* `CslibFrontier.Logic.PL.Algebraic.IsIPSCertificate`, `IsIPSLINCertificate`,
  `IsIPSLINpCertificate`: semantic certificates for `IPS`, `IPS_LIN`, and `IPS_{LIN'}`.
* Soundness (`IsIPSCertificate.hasNoBoolSolution`) and simulation of Nullstellensatz certificates
  by constant-depth `IPS_LIN` formulas (`nullstellensatz_certificate_implies_ipsLIN_formula`).
-/

public section

namespace CslibFrontier.Logic.PL.Algebraic

open Finset MvPolynomial
open Cslib.BitString Cslib.Circuits Cslib.Circuits.Arithmetic Cslib.Logic.PL.Algebraic

/-- Variables `(x_1, …, x_n, y_1, …, y_m, z_1, …, z_n)` of an `IPS` refutation of `m` polynomial
equations in `n` Boolean variables. -/
inductive IPSVar (n m : ℕ) : Type
  | x : Fin n → IPSVar n m
  | y : Fin m → IPSVar n m
  | z : Fin n → IPSVar n m
  deriving DecidableEq

/-- Canonical equivalence between `IPSVar n m` and `Fin (n + m + n)` for circuit/formula inputs. -/
def ipsVarEquiv (n m : ℕ) : IPSVar n m ≃ Fin (n + m + n) where
  toFun
    | .x i => ⟨i.1, by omega⟩
    | .y j => ⟨n + j.1, by omega⟩
    | .z k => ⟨n + m + k.1, by omega⟩
  invFun idx :=
    if hx : idx.1 < n then .x ⟨idx.1, hx⟩
    else if hy : idx.1 < n + m then .y ⟨idx.1 - n, by omega⟩
    else .z ⟨idx.1 - (n + m), by omega⟩
  left_inv v := by
    cases v with
    | x i => simp [i.isLt]
    | y j =>
      have h1 : ¬ n + j.1 < n := by omega
      have h2 : n + j.1 < n + m := by omega
      simp [h1, h2]
    | z k =>
      have h1 : ¬ n + m + k.1 < n := by omega
      have h2 : ¬ n + m + k.1 < n + m := by omega
      simp [h1, h2]
  right_inv idx := by
    ext
    by_cases hx : idx.1 < n
    · simp [hx]
    · by_cases hy : idx.1 < n + m <;> simp [hx, hy] <;> omega

instance instFintypeIPSVar (n m : ℕ) : Fintype (IPSVar n m) :=
  Fintype.ofEquiv (Fin (n + m + n)) (ipsVarEquiv n m).symm

/-- A polynomial system `f : Fin m → MvPolynomial (Fin n) R` has no Boolean solution on
`{0, 1}^n`. -/
def HasNoBoolSolution {n m : ℕ} {R : Type*} [CommRing R]
    (f : Fin m → MvPolynomial (Fin n) R) : Prop :=
  ∀ a : Fin n → Bool, ∃ j : Fin m, eval (bitPoint a) (f j) ≠ 0

/-- Evaluation homomorphism `C(x, 0, 0) : R[x, y, z] → R[x]`. -/
noncomputable def ipsEvalZero {n m : ℕ} {R : Type*} [CommSemiring R] :
    MvPolynomial (IPSVar n m) R →ₐ[R] MvPolynomial (Fin n) R :=
  aeval fun
    | .x i => X i
    | .y _ => 0
    | .z _ => 0

/-- Evaluation homomorphism `C(x, f(x), x^2 - x) : R[x, y, z] → R[x]`. -/
noncomputable def ipsEvalAxioms {n m : ℕ} {R : Type*} [CommRing R]
    (f : Fin m → MvPolynomial (Fin n) R) :
    MvPolynomial (IPSVar n m) R →ₐ[R] MvPolynomial (Fin n) R :=
  aeval fun
    | .x i => X i
    | .y j => f j
    | .z i => X i ^ 2 - X i

/-- Partial evaluation `C(x, y, 0) : R[x, y, z] → R[x ⊕ y]`. -/
noncomputable def ipsEvalZZero {n m : ℕ} {R : Type*} [CommSemiring R] :
    MvPolynomial (IPSVar n m) R →ₐ[R] MvPolynomial (Fin n ⊕ Fin m) R :=
  aeval fun
    | .x i => X (.inl i)
    | .y j => X (.inr j)
    | .z _ => 0

/-- An Ideal Proof System (`IPS`) certificate for `f_1, …, f_m`. -/
def IsIPSCertificate {n m : ℕ} {R : Type*} [CommRing R]
    (f : Fin m → MvPolynomial (Fin n) R) (C : MvPolynomial (IPSVar n m) R) : Prop :=
  ipsEvalZero C = 0 ∧ ipsEvalAxioms f C = 1

/-- An `IPS_LIN` certificate: linear in both `y` and `z` variables. -/
def IsIPSLINCertificate {n m : ℕ} {R : Type*} [CommRing R]
    (f : Fin m → MvPolynomial (Fin n) R) (C : MvPolynomial (IPSVar n m) R) : Prop :=
  IsIPSCertificate f C ∧ (∀ j, C.degreeOf (.y j) ≤ 1) ∧ (∀ i, C.degreeOf (.z i) ≤ 1)

/-- An `IPS_{LIN'}` certificate: linear in `y` variables (`z`-degree unrestricted). -/
def IsIPSLINpCertificate {n m : ℕ} {R : Type*} [CommRing R]
    (f : Fin m → MvPolynomial (Fin n) R) (C : MvPolynomial (IPSVar n m) R) : Prop :=
  IsIPSCertificate f C ∧ ∀ j, C.degreeOf (.y j) ≤ 1

private theorem eval_aeval_eq_eval {σ τ R : Type*} [CommSemiring R]
    (a : τ → R) (g : σ → MvPolynomial τ R) (p : MvPolynomial σ R) :
    eval a (aeval g p) = eval (fun s => eval a (g s)) p := by
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p s hp => simp [hp]

/-- Soundness of `IPS` over any nontrivial commutative ring `R`. -/
theorem IsIPSCertificate.hasNoBoolSolution {n m : ℕ} {R : Type*} [CommRing R] [Nontrivial R]
    {f : Fin m → MvPolynomial (Fin n) R} {C : MvPolynomial (IPSVar n m) R}
    (hC : IsIPSCertificate f C) : HasNoBoolSolution f := by
  intro a
  by_contra hsol
  push Not at hsol
  have h1 := congrArg (eval (bitPoint a)) hC.2
  have h0 := congrArg (eval (bitPoint a)) hC.1
  rw [map_one, ipsEvalAxioms, eval_aeval_eq_eval] at h1
  rw [map_zero, ipsEvalZero, eval_aeval_eq_eval] at h0
  have heq : (fun v : IPSVar n m => eval (bitPoint a) (match v with
      | .x i => X i
      | .y j => f j
      | .z i => X i ^ 2 - X i)) =
      (fun v : IPSVar n m => eval (bitPoint a) (match v with
      | .x i => (X i : MvPolynomial (Fin n) R)
      | .y _ => 0
      | .z _ => 0)) := by
    funext v
    cases v with
    | x i => rfl
    | y j => simp [hsol j]
    | z i => simp [bitPoint, bitVal_pow _ two_ne_zero]
  rw [heq, h0] at h1
  exact zero_ne_one h1

/-- Polynomial in `MvPolynomial (IPSVar n m) K` computed by `F : SPFormula K (n + m + n)`. -/
noncomputable def ipsFormulaPoly {n m : ℕ} {K : Type*} [CommSemiring K]
    (F : SPFormula K (n + m + n)) : MvPolynomial (IPSVar n m) K :=
  rename (ipsVarEquiv n m).symm F.polynomial

/-- Simulation of Nullstellensatz certificates by constant-depth `IPS_LIN` formulas. -/
theorem nullstellensatz_certificate_implies_ipsLIN_formula {n m s Δ : ℕ} {F : Type*} [Field F]
    (P : Fin m → MvPolynomial (Fin n) F)
    (A : Fin m → SPFormula F n) (B : Fin n → SPFormula F n)
    (hcert : (∑ i : Fin m, (A i).polynomial * P i) +
      (∑ j : Fin n, (B j).polynomial * (X j ^ 2 - X j)) = 1)
    (hAs : ∀ i, (A i).nodeCount ≤ s) (hBs : ∀ j, (B j).nodeCount ≤ s)
    (hAΔ : ∀ i, (A i).depth ≤ Δ) (hBΔ : ∀ j, (B j).depth ≤ Δ) :
    ∃ C : SPFormula F (n + m + n),
      IsIPSLINCertificate P (ipsFormulaPoly C) ∧
      C.depth ≤ Δ + 2 ∧
      C.nodeCount ≤ (m + n) * (s + 2) + 1 := by
  let liftX : SPFormula F n → SPFormula F (n + m + n) :=
    SPFormula.substFormula fun i => .input (ipsVarEquiv n m (.x i))
  have hlift_poly : ∀ G : SPFormula F n,
      ipsFormulaPoly (n := n) (m := m) (liftX G) = rename IPSVar.x G.polynomial := by
    intro G
    simp only [ipsFormulaPoly, liftX, SPFormula.polynomial_substFormula, SPFormula.polynomial_input]
    rw [rename_eq_aeval, ← AlgHom.comp_apply]
    congr 1; ext i; simp
  have hlift_nodes : ∀ G : SPFormula F n, (liftX G).nodeCount ≤ G.nodeCount := by
    intro G
    simpa using SPFormula.nodeCount_substFormula_le (S := 1) (fun _ => by simp) le_rfl G
  have hlift_depth : ∀ G : SPFormula F n, (liftX G).depth ≤ G.depth := by
    intro G
    induction G with
    | input i => simp [liftX, SPFormula.substFormula]
    | gate op args ih =>
      simp only [liftX, SPFormula.substFormula, Formula.gate_bind, Formula.depth_gate] at ih ⊢
      exact Nat.succ_le_succ (Finset.sup_le fun k _ => (ih k).trans
        (Finset.le_sup (f := fun k => (args k).depth) (mem_univ k)))
  let terms : Fin (m + n) → SPFormula F (n + m + n) :=
    Fin.addCases
      (fun i => SPFormula.mul ![liftX (A i), .input (ipsVarEquiv n m (.y i))])
      (fun j => SPFormula.mul ![liftX (B j), .input (ipsVarEquiv n m (.z j))])
  let C : SPFormula F (n + m + n) := SPFormula.add (fun _ => 1) terms
  refine ⟨C, ?_, ?_, ?_⟩
  · have hCpoly : ipsFormulaPoly C =
        (∑ i : Fin m, rename IPSVar.x (A i).polynomial * X (.y i)) +
        (∑ j : Fin n, rename IPSVar.x (B j).polynomial * X (.z j)) := by
      unfold ipsFormulaPoly
      simp only [C, SPFormula.polynomial_add, map_one, one_mul, Fin.sum_univ_add,
        map_add, map_sum]
      congr 1
      · refine sum_congr rfl fun i _ => ?_
        simp only [terms, Fin.addCases_left, SPFormula.polynomial_mul, Fin.prod_univ_two,
          Matrix.cons_val_zero, Matrix.cons_val_one, SPFormula.polynomial_input, map_mul]
        rw [← ipsFormulaPoly, hlift_poly]
        simp
      · refine sum_congr rfl fun j _ => ?_
        simp only [terms, Fin.addCases_right, SPFormula.polynomial_mul, Fin.prod_univ_two,
          Matrix.cons_val_zero, Matrix.cons_val_one, SPFormula.polynomial_input, map_mul]
        rw [← ipsFormulaPoly, hlift_poly]
        simp
    have hzero : ipsEvalZero (ipsFormulaPoly C) = 0 := by
      rw [hCpoly, ipsEvalZero, map_add, map_sum, map_sum]; simp
    have hax : ipsEvalAxioms P (ipsFormulaPoly C) = 1 := by
      rw [hCpoly, ipsEvalAxioms, map_add, map_sum, map_sum]
      have hren : ∀ q : MvPolynomial (Fin n) F,
          aeval (fun
            | IPSVar.x i => (X i : MvPolynomial (Fin n) F)
            | IPSVar.y j => P j
            | IPSVar.z i => X i ^ 2 - X i) (rename IPSVar.x q) = q := by
        intro q; rw [aeval_rename]; exact aeval_X_left_apply q
      simp only [map_mul, hren, aeval_X, hcert]
    have hdeg_term_x : ∀ (q : MvPolynomial (Fin n) F) (v : IPSVar n m),
        (∀ i, v ≠ .x i) → (rename IPSVar.x q).degreeOf v = 0 := by
      intro q v hv
      rw [← Nat.le_zero, degreeOf_le_iff]
      intro u hu
      have hnot : v ∉ (rename IPSVar.x q).vars := by
        intro hmem
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp (vars_rename IPSVar.x q hmem)
        exact hv i rfl
      by_contra hpos
      exact hnot ((MvPolynomial.mem_vars_iff_mem_support v).mpr
        ⟨u, hu, Finsupp.mem_support_iff.mpr (by omega)⟩)
    refine ⟨⟨hzero, hax⟩, ?_, ?_⟩
    · intro k
      rw [hCpoly]
      refine (degreeOf_add_le _ _ _).trans (max_le ?_ ?_)
      · refine (degreeOf_sum_le _ _ _).trans (Finset.sup_le fun i _ => ?_)
        refine (degreeOf_mul_le _ _ _).trans ?_
        rw [hdeg_term_x _ _ (fun _ h => by cases h), zero_add, degreeOf_X]
        split_ifs <;> omega
      · refine (degreeOf_sum_le _ _ _).trans (Finset.sup_le fun j _ => ?_)
        refine (degreeOf_mul_le _ _ _).trans ?_
        rw [hdeg_term_x _ _ (fun _ h => by cases h), zero_add, degreeOf_X]; simp
    · intro k
      rw [hCpoly]
      refine (degreeOf_add_le _ _ _).trans (max_le ?_ ?_)
      · refine (degreeOf_sum_le _ _ _).trans (Finset.sup_le fun i _ => ?_)
        refine (degreeOf_mul_le _ _ _).trans ?_
        rw [hdeg_term_x _ _ (fun _ h => by cases h), zero_add, degreeOf_X]; simp
      · refine (degreeOf_sum_le _ _ _).trans (Finset.sup_le fun j _ => ?_)
        refine (degreeOf_mul_le _ _ _).trans ?_
        rw [hdeg_term_x _ _ (fun _ h => by cases h), zero_add, degreeOf_X]
        split_ifs <;> omega
  · simp only [C, Formula.depth_gate]
    refine Nat.succ_le_succ (Finset.sup_le fun t _ => ?_)
    induction t using Fin.addCases with
    | left i =>
      simp only [terms, Fin.addCases_left, Formula.depth_gate]
      refine Nat.succ_le_succ (Finset.sup_le fun b _ => ?_)
      fin_cases b
      · exact (hlift_depth (A i)).trans (hAΔ i)
      · simp
    | right j =>
      simp only [terms, Fin.addCases_right, Formula.depth_gate]
      refine Nat.succ_le_succ (Finset.sup_le fun b _ => ?_)
      fin_cases b
      · exact (hlift_depth (B j)).trans (hBΔ j)
      · simp
  · simp only [C, Formula.nodeCount_gate, Fin.sum_univ_add]
    have hsumA : ∑ i : Fin m, (terms (Fin.castAdd n i)).nodeCount ≤ ∑ _i : Fin m, (s + 2) := by
      refine sum_le_sum fun i _ => ?_
      simp only [terms, Fin.addCases_left, Formula.nodeCount_gate, Fin.sum_univ_two,
        Matrix.cons_val_zero, Matrix.cons_val_one, Formula.nodeCount_input]
      have := (hlift_nodes (A i)).trans (hAs i); omega
    have hsumB : ∑ j : Fin n, (terms (Fin.natAdd m j)).nodeCount ≤ ∑ _j : Fin n, (s + 2) := by
      refine sum_le_sum fun j _ => ?_
      simp only [terms, Fin.addCases_right, Formula.nodeCount_gate, Fin.sum_univ_two,
        Matrix.cons_val_zero, Matrix.cons_val_one, Formula.nodeCount_input]
      have := (hlift_nodes (B j)).trans (hBs j); omega
    calc
      (∑ i : Fin m, (terms (Fin.castAdd n i)).nodeCount +
          ∑ j : Fin n, (terms (Fin.natAdd m j)).nodeCount) + 1
        ≤ (m * (s + 2) + n * (s + 2)) + 1 := by
            simp only [sum_const, card_fin, smul_eq_mul] at hsumA hsumB; omega
      _ = (m + n) * (s + 2) + 1 := by ring

end CslibFrontier.Logic.PL.Algebraic
