module

public import CslibFrontier.Foundations.BooleanAnalysis.Degree
public import CslibFrontier.Foundations.BooleanAnalysis.Fourier
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Logic.Function.DependsOn

import Mathlib.Analysis.MeanInequalities

/-!
# Sherali–Adams Pseudo-Distributions and the Approximate Cauchy–Schwarz Inequality

This module formalizes $R$-local Sherali–Adams pseudo-distributions, local marginal probability
characterizations, Walsh–Fourier moment gluing, local-junta pushforwards, the Fourier / monomial
$\ell_1$ norm, and the approximate Cauchy–Schwarz inequality on the Boolean hypercube
$(\iota \to \mathrm{Bool}) \simeq \{-1, 1\}^\iota$ under standard Lean axioms, building on the
canonical Boolean Fourier analysis carriers of `CslibFrontier.Foundations.BooleanAnalysis`.

## Main declarations

- `boolSignVec`, `boolCubeEquivPmOneCube`, `finCubeEquivBoolCube`: coordinatewise $\pm 1$ sign
  vectors and equivalences between $\iota \to \mathrm{Bool}$ and $\{-1, 1\}^\iota$.
- `pseudoExpect`, `IsLocalJunta`, `IsLocalPseudoDist`: the pseudo-expectation functional
  $\tilde{\mathbb{E}}_D[f] = \sum_x D(x)\,f(x)$, $R$-local juntas, and $R$-local Sherali–Adams
  pseudo-distributions.
- `marginalDist`, `pseudoExpect_eq_sum_marginalDist`,
  `isLocalPseudoDist_iff_marginalDist_nonneg`: local marginal distributions on coordinate subsets
  $J$ with $|J| \le R$ and characterization of $R$-local pseudo-distributions via non-negative
  local marginals.
- `pseudoDistOfMoments`, `isLocalPseudoDist_pseudoDistOfMoments_iff`,
  `isLocalPseudoDist_pseudoDistOfMoments_of_local_marginals`: Walsh–Fourier moment constructor
  and local-distribution gluing criterion.
- `pushforwardPseudoDist`, `IsLocalPseudoDist.pushforward`, `finsetParityMap`, `listParityMap`,
  `tupleParityMap`: pushforward of $(kR)$-local pseudo-distributions to $R$-local
  pseudo-distributions along $k$-local coordinate maps and monomial substitutions.
- `local_cauchy_schwarz`, `fourierL1Norm`, `abs_pseudoExpect_le_fourierL1Norm`: exact local
  Cauchy–Schwarz inequality for $s$-local and $t$-local juntas when $s + t \le R$, and the
  Fourier $\ell_1$ norm $\|f\|_1 = \sum_S |\widehat{f}(S)|$.
- `approx_cs_radicand_nonneg`, `approx_cauchy_schwarz_asymmetric`, `approx_cauchy_schwarz`,
  `approx_cauchy_schwarz_fin`, `abs_pseudoExpect_le_sqrt_approx_cs`: the approximate
  Cauchy–Schwarz inequality for bounded-degree polynomials under $R$-local Sherali–Adams
  pseudo-distributions.
- `linearSumPoly`, `abs_pseudoExpect_linearSumPoly_le`,
  `exists_two_local_counterexample_fin_three`: the linear polynomial
  $p(x) = \sum_{i=1}^n x_i$, the $n / \sqrt{R - 1}$ upper bound when
  $\tilde{\mathbb{E}}_D[p^2] = 0$, and an explicit signed $2$-local Sherali–Adams witness on
  $\mathrm{Fin}\,3 \to \mathrm{Bool}$ violating exact Cauchy–Schwarz.
-/

public section
noncomputable section

namespace CslibFrontier.Foundations.BooleanAnalysis

open scoped BigOperators
open Cslib.BitString

/-! ### Coordinate Sign Vectors and Equivalences with $\{-1, 1\}^\iota$ -/
section SignCube
variable {ι : Type*}

lemma signVal_eq_one_or_neg_one (b : Bool) : signVal b = 1 ∨ signVal b = -1 := by
  cases b <;> simp

private lemma signVal_sq (b : Bool) : signVal b ^ 2 = 1 := by
  rw [sq, signVal_mul_self]

lemma chi_eq_one_or_neg_one (S : Finset ι) (x : ι → Bool) :
    chi ℝ S x = 1 ∨ chi ℝ S x = -1 :=
  sq_eq_one_iff.mp (by rw [sq, chi_mul_self])

private lemma chi_sq (S : Finset ι) (x : ι → Bool) : chi ℝ S x ^ 2 = 1 := by
  rw [sq, chi_mul_self]

/-- Coordinatewise $\pm 1$ vector $x \mapsto (\mathrm{signVal}(x_i))_{i \in \iota}$ associated to a
Boolean hypercube point $x : \iota \to \mathrm{Bool}$ via `false ↦ 1` and `true ↦ -1`. -/
def boolSignVec (x : ι → Bool) (i : ι) : ℝ := signVal (x i)

lemma boolSignVec_apply (x : ι → Bool) (i : ι) : boolSignVec x i = signVal (x i) := by
  unfold boolSignVec; rfl

lemma boolSignVec_eq_one_or_neg_one (x : ι → Bool) (i : ι) :
    boolSignVec x i = 1 ∨ boolSignVec x i = -1 := signVal_eq_one_or_neg_one (x i)

@[simp, grind =] lemma boolSignVec_sq (x : ι → Bool) (i : ι) : (boolSignVec x i) ^ 2 = 1 :=
  signVal_sq (x i)

@[simp, grind =] lemma abs_boolSignVec (x : ι → Bool) (i : ι) : |boolSignVec x i| = 1 :=
  abs_signVal (x i)

lemma prod_boolSignVec_eq_chi (S : Finset ι) (x : ι → Bool) :
    (∏ i ∈ S, boolSignVec x i) = chi ℝ S x := (chi_eq_prod_signVal S x).symm

/-- Canonical bijection $(\iota \to \mathrm{Bool}) \simeq \{x : \iota \to \mathbb{R} \mid
\forall i,\, x_i = 1 \lor x_i = -1\}$ identifying Boolean assignments with $\pm 1$ vectors. -/
def boolCubeEquivPmOneCube (ι : Type*) :
    (ι → Bool) ≃ {x : ι → ℝ // ∀ i, x i = 1 ∨ x i = -1} where
  toFun x := ⟨boolSignVec x, boolSignVec_eq_one_or_neg_one x⟩
  invFun y i := by classical exact if y.1 i = 1 then false else true
  left_inv x := by funext i; cases hxi : x i <;> norm_num [hxi, boolSignVec]
  right_inv y := by
    ext i; rcases y.2 i with h1 | hm1 <;> [norm_num [h1, boolSignVec]; norm_num [hm1, boolSignVec]]

@[simp, grind =] lemma boolCubeEquivPmOneCube_apply_coe (x : ι → Bool) (i : ι) :
    (boolCubeEquivPmOneCube ι x).1 i = signVal (x i) := by
  unfold boolCubeEquivPmOneCube boolSignVec; rfl

@[simp] lemma boolCubeEquivPmOneCube_symm_apply
    (y : {x : ι → ℝ // ∀ i, x i = 1 ∨ x i = -1}) (i : ι) :
    signVal ((boolCubeEquivPmOneCube ι).symm y i) = y.1 i := by
  change (boolCubeEquivPmOneCube ι ((boolCubeEquivPmOneCube ι).symm y)).1 i = y.1 i
  rw [(boolCubeEquivPmOneCube ι).apply_symm_apply]
end SignCube

/-- Specialization of `boolCubeEquivPmOneCube` to $\mathrm{Fin}\,n \to \mathrm{Bool}$. -/
def finCubeEquivBoolCube (n : ℕ) :
    (Fin n → Bool) ≃ {x : Fin n → ℝ // ∀ i, x i = 1 ∨ x i = -1} := boolCubeEquivPmOneCube (Fin n)

@[simp, grind =] lemma finCubeEquivBoolCube_apply_coe (n : ℕ) (x : Fin n → Bool) (i : Fin n) :
    (finCubeEquivBoolCube n x).1 i = signVal (x i) := by
  unfold finCubeEquivBoolCube; exact boolCubeEquivPmOneCube_apply_coe x i

@[simp] lemma finCubeEquivBoolCube_symm_apply (n : ℕ)
    (y : {x : Fin n → ℝ // ∀ i, x i = 1 ∨ x i = -1}) (i : Fin n) :
    signVal ((finCubeEquivBoolCube n).symm y i) = y.1 i := boolCubeEquivPmOneCube_symm_apply y i

/-! ### Pseudo-Expectation Functional -/
private lemma sum_boolCube_eq_single {α : Type*} [Fintype α] [DecidableEq α] (y₀ : α → Bool)
    (g : (α → Bool) → ℝ) (h0 : ∀ y, y ≠ y₀ → g y = 0) : (∑ y : (α → Bool), g y) = g y₀ :=
  Finset.sum_eq_single_of_mem y₀ (Finset.mem_univ y₀) fun y _ hy ↦ h0 y hy

section PseudoExpect
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Pseudo-expectation functional $\tilde{\mathbb{E}}_D[f] := \sum_{x \in \{-1,1\}^\iota} D(x)f(x)$
associated to a signed weight $D : (\iota \to \mathrm{Bool}) \to \mathbb{R}$. -/
def pseudoExpect (D f : (ι → Bool) → ℝ) : ℝ := ∑ x : (ι → Bool), D x * f x

lemma pseudoExpect_def (D f : (ι → Bool) → ℝ) :
    pseudoExpect D f = ∑ x : (ι → Bool), D x * f x := by unfold pseudoExpect; rfl

/-- Compatibility of `pseudoExpect` with any `Fintype` instance on $\iota \to \mathrm{Bool}$. -/
lemma pseudoExpect_eq_sum [inst : Fintype (ι → Bool)] (D f : (ι → Bool) → ℝ) :
    pseudoExpect D f = @Finset.sum (ι → Bool) ℝ _ (@Finset.univ (ι → Bool) inst)
      (fun x ↦ D x * f x) := by
  rw [pseudoExpect_def]; congr 1; ext x; simp [@Finset.mem_univ _ inst]

@[simp, grind =] lemma pseudoExpect_zero (D : (ι → Bool) → ℝ) : pseudoExpect D 0 = 0 := by
  simp [pseudoExpect_def]

@[simp, grind =] lemma pseudoExpect_zero_left (f : (ι → Bool) → ℝ) : pseudoExpect 0 f = 0 := by
  simp [pseudoExpect_def]

@[simp] lemma pseudoExpect_const (D : (ι → Bool) → ℝ) (c : ℝ) :
    pseudoExpect D (fun _ ↦ c) = (∑ x : (ι → Bool), D x) * c := by
  rw [pseudoExpect_def, ← Finset.sum_mul]

@[simp] lemma pseudoExpect_add_pi (D f g : (ι → Bool) → ℝ) :
    pseudoExpect D (f + g) = pseudoExpect D f + pseudoExpect D g := by
  simp [pseudoExpect_def, mul_add, Finset.sum_add_distrib]

lemma pseudoExpect_add (D f g : (ι → Bool) → ℝ) :
    pseudoExpect D (fun x ↦ f x + g x) = pseudoExpect D f + pseudoExpect D g :=
  pseudoExpect_add_pi D f g

@[simp] lemma pseudoExpect_sub_pi (D f g : (ι → Bool) → ℝ) :
    pseudoExpect D (f - g) = pseudoExpect D f - pseudoExpect D g := by
  simp [pseudoExpect_def, mul_sub, Finset.sum_sub_distrib]

lemma pseudoExpect_sub (D f g : (ι → Bool) → ℝ) :
    pseudoExpect D (fun x ↦ f x - g x) = pseudoExpect D f - pseudoExpect D g :=
  pseudoExpect_sub_pi D f g

@[simp] lemma pseudoExpect_neg_pi (D f : (ι → Bool) → ℝ) :
    pseudoExpect D (-f) = -pseudoExpect D f := by simp [pseudoExpect_def]

lemma pseudoExpect_neg (D f : (ι → Bool) → ℝ) :
    pseudoExpect D (fun x ↦ -f x) = -pseudoExpect D f := pseudoExpect_neg_pi D f

@[simp] lemma pseudoExpect_smul_pi (D : (ι → Bool) → ℝ) (c : ℝ) (f : (ι → Bool) → ℝ) :
    pseudoExpect D (c • f) = c * pseudoExpect D f := by
  simp only [pseudoExpect_def, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ ↦ by ring

lemma pseudoExpect_smul (D : (ι → Bool) → ℝ) (c : ℝ) (f : (ι → Bool) → ℝ) :
    pseudoExpect D (fun x ↦ c * f x) = c * pseudoExpect D f := pseudoExpect_smul_pi D c f

lemma pseudoExpect_mul_const (D f : (ι → Bool) → ℝ) (c : ℝ) :
    pseudoExpect D (fun x ↦ f x * c) = pseudoExpect D f * c := by
  simp only [pseudoExpect_def, Finset.sum_mul, mul_assoc]

@[simp] lemma pseudoExpect_sum_pi {α : Type*} (D : (ι → Bool) → ℝ) (s : Finset α)
    (g : α → (ι → Bool) → ℝ) :
    pseudoExpect D (∑ a ∈ s, g a) = ∑ a ∈ s, pseudoExpect D (g a) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s has ih => rw [Finset.sum_insert has, pseudoExpect_add_pi, ih, Finset.sum_insert has]

lemma pseudoExpect_sum {α : Type*} (D : (ι → Bool) → ℝ) (s : Finset α) (g : α → (ι → Bool) → ℝ) :
    pseudoExpect D (fun x ↦ ∑ a ∈ s, g a x) = ∑ a ∈ s, pseudoExpect D (g a) := by
  rw [show (fun x ↦ ∑ a ∈ s, g a x) = ∑ a ∈ s, g a by ext x; simp, pseudoExpect_sum_pi]

lemma pseudoExpect_add_left (D₁ D₂ f : (ι → Bool) → ℝ) :
    pseudoExpect (fun x ↦ D₁ x + D₂ x) f = pseudoExpect D₁ f + pseudoExpect D₂ f := by
  simp [pseudoExpect_def, add_mul, Finset.sum_add_distrib]

lemma pseudoExpect_smul_left (c : ℝ) (D f : (ι → Bool) → ℝ) :
    pseudoExpect (fun x ↦ c * D x) f = c * pseudoExpect D f := by
  simp only [pseudoExpect_def, mul_assoc, Finset.mul_sum]

lemma pseudoExpect_sum_left {α : Type*} (s : Finset α) (D : α → (ι → Bool) → ℝ)
    (f : (ι → Bool) → ℝ) :
    pseudoExpect (fun x ↦ ∑ a ∈ s, D a x) f = ∑ a ∈ s, pseudoExpect (D a) f := by
  simp only [pseudoExpect_def, Finset.sum_mul]; exact Finset.sum_comm
end PseudoExpect

lemma pseudoExpect_fin_eq (n : ℕ) (D f : (Fin n → Bool) → ℝ) :
    pseudoExpect D f = ∑ x : Fin n → Bool, D x * f x := pseudoExpect_eq_sum D f

/-! ### $R$-Local Juntas -/
section LocalJunta
variable {ι : Type*}

private lemma dependsOn_mono {J₁ J₂ : Finset ι} {f : (ι → Bool) → ℝ}
    (hJ : J₁ ⊆ J₂) (hf : DependsOn f (J₁ : Set ι)) :
    DependsOn f (J₂ : Set ι) := fun _ _ hxy ↦ hf fun i hi ↦ hxy i (hJ hi)

private lemma dependsOn_const_finset (J : Finset ι) (c : ℝ) :
    DependsOn (fun _ : (ι → Bool) ↦ c) (J : Set ι) := fun _ _ _ ↦ rfl

private lemma dependsOn_add {J : Finset ι} {f g : (ι → Bool) → ℝ}
    (hf : DependsOn f (J : Set ι)) (hg : DependsOn g (J : Set ι)) :
    DependsOn (fun x ↦ f x + g x) (J : Set ι) :=
  fun _ _ hxy ↦ by dsimp only; rw [hf hxy, hg hxy]

private lemma dependsOn_sub {J : Finset ι} {f g : (ι → Bool) → ℝ}
    (hf : DependsOn f (J : Set ι)) (hg : DependsOn g (J : Set ι)) :
    DependsOn (fun x ↦ f x - g x) (J : Set ι) :=
  fun _ _ hxy ↦ by dsimp only; rw [hf hxy, hg hxy]

private lemma dependsOn_mul {J : Finset ι} {f g : (ι → Bool) → ℝ}
    (hf : DependsOn f (J : Set ι)) (hg : DependsOn g (J : Set ι)) :
    DependsOn (fun x ↦ f x * g x) (J : Set ι) :=
  fun _ _ hxy ↦ by dsimp only; rw [hf hxy, hg hxy]

private lemma dependsOn_smul {J : Finset ι} (c : ℝ) {f : (ι → Bool) → ℝ}
    (hf : DependsOn f (J : Set ι)) :
    DependsOn (fun x ↦ c * f x) (J : Set ι) := fun _ _ hxy ↦ by dsimp only; rw [hf hxy]

private lemma dependsOn_pow {J : Finset ι} {f : (ι → Bool) → ℝ}
    (hf : DependsOn f (J : Set ι)) (k : ℕ) :
    DependsOn (fun x ↦ f x ^ k) (J : Set ι) := fun _ _ hxy ↦ by dsimp only; rw [hf hxy]

private lemma dependsOn_chi (S : Finset ι) :
    DependsOn (chi ℝ S) (S : Set ι) := fun _ _ hxy ↦ by
  rw [chi_eq_prod_signVal, chi_eq_prod_signVal]
  exact Finset.prod_congr rfl fun i hi ↦ by rw [hxy i hi]

/-- Predicate asserting that $f : (\iota \to \mathrm{Bool}) \to \mathbb{R}$ depends on at most $R$
coordinates ($R$-local junta). -/
def IsLocalJunta (R : ℕ) (f : (ι → Bool) → ℝ) : Prop :=
  ∃ J : Finset ι, J.card ≤ R ∧ DependsOn f (J : Set ι)

lemma isLocalJunta_iff {R : ℕ} {f : (ι → Bool) → ℝ} :
    IsLocalJunta R f ↔ ∃ J : Finset ι, J.card ≤ R ∧ DependsOn f (J : Set ι) := Iff.rfl

lemma IsLocalJunta.mono {R₁ R₂ : ℕ} {f : (ι → Bool) → ℝ}
    (hf : IsLocalJunta R₁ f) (hR : R₁ ≤ R₂) : IsLocalJunta R₂ f :=
  let ⟨J, hJ, hdf⟩ := hf; ⟨J, hJ.trans hR, hdf⟩

lemma isLocalJunta_const (R : ℕ) (c : ℝ) : IsLocalJunta R (fun _ : (ι → Bool) ↦ c) :=
  ⟨∅, by simp, dependsOn_const_finset ∅ c⟩

lemma isLocalJunta_zero (R : ℕ) : IsLocalJunta R (0 : (ι → Bool) → ℝ) := isLocalJunta_const R 0

lemma isLocalJunta_one (R : ℕ) : IsLocalJunta R (1 : (ι → Bool) → ℝ) := isLocalJunta_const R 1

lemma IsLocalJunta.smul {R : ℕ} (c : ℝ) {f : (ι → Bool) → ℝ} (hf : IsLocalJunta R f) :
    IsLocalJunta R (fun x ↦ c * f x) := let ⟨J, hJ, hdf⟩ := hf; ⟨J, hJ, dependsOn_smul c hdf⟩

lemma IsLocalJunta.neg {R : ℕ} {f : (ι → Bool) → ℝ} (hf : IsLocalJunta R f) :
    IsLocalJunta R (fun x ↦ -f x) := by simpa using hf.smul (-1)

lemma IsLocalJunta.pow {R : ℕ} {f : (ι → Bool) → ℝ} (hf : IsLocalJunta R f) (k : ℕ) :
    IsLocalJunta R (fun x ↦ f x ^ k) := let ⟨J, hJ, hdf⟩ := hf; ⟨J, hJ, dependsOn_pow hdf k⟩

lemma IsLocalJunta.sq {R : ℕ} {f : (ι → Bool) → ℝ} (hf : IsLocalJunta R f) :
    IsLocalJunta R (fun x ↦ f x ^ 2) := hf.pow 2

lemma IsLocalJunta.add {R₁ R₂ : ℕ} {f g : (ι → Bool) → ℝ}
    (hf : IsLocalJunta R₁ f) (hg : IsLocalJunta R₂ g) :
    IsLocalJunta (R₁ + R₂) (fun x ↦ f x + g x) := by
  classical
  rcases hf with ⟨J₁, hJ₁, hdf⟩; rcases hg with ⟨J₂, hJ₂, hdg⟩
  exact ⟨J₁ ∪ J₂, (Finset.card_union_le J₁ J₂).trans (add_le_add hJ₁ hJ₂),
    dependsOn_add (dependsOn_mono Finset.subset_union_left hdf)
      (dependsOn_mono Finset.subset_union_right hdg)⟩

lemma IsLocalJunta.sub {R₁ R₂ : ℕ} {f g : (ι → Bool) → ℝ}
    (hf : IsLocalJunta R₁ f) (hg : IsLocalJunta R₂ g) :
    IsLocalJunta (R₁ + R₂) (fun x ↦ f x - g x) := by simpa [sub_eq_add_neg] using hf.add hg.neg

lemma IsLocalJunta.mul {R₁ R₂ : ℕ} {f g : (ι → Bool) → ℝ}
    (hf : IsLocalJunta R₁ f) (hg : IsLocalJunta R₂ g) :
    IsLocalJunta (R₁ + R₂) (fun x ↦ f x * g x) := by
  classical
  rcases hf with ⟨J₁, hJ₁, hdf⟩; rcases hg with ⟨J₂, hJ₂, hdg⟩
  exact ⟨J₁ ∪ J₂, (Finset.card_union_le J₁ J₂).trans (add_le_add hJ₁ hJ₂),
    dependsOn_mul (dependsOn_mono Finset.subset_union_left hdf)
      (dependsOn_mono Finset.subset_union_right hdg)⟩

lemma isLocalJunta_sum_le {α : Type*} (s : Finset α) (d : ℕ) (g : α → (ι → Bool) → ℝ)
    (hg : ∀ a ∈ s, IsLocalJunta d (g a)) :
    IsLocalJunta (d * s.card) (fun x ↦ ∑ a ∈ s, g a x) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using isLocalJunta_const 0 0
  | insert a s has ih =>
    have hsum := (hg a (Finset.mem_insert_self a s)).add
      (ih fun b hb ↦ hg b (Finset.mem_insert_of_mem hb))
    simp_rw [Finset.sum_insert has, Finset.card_insert_of_notMem has, mul_add, mul_one,
      add_comm (d * s.card) d]
    exact hsum

lemma isLocalJunta_chi (S : Finset ι) :
    IsLocalJunta S.card (chi ℝ S) := ⟨S, le_rfl, dependsOn_chi S⟩

lemma isLocalJunta_chi_of_le {S : Finset ι} {R : ℕ} (hS : S.card ≤ R) :
    IsLocalJunta R (chi ℝ S) := (isLocalJunta_chi S).mono hS
end LocalJunta

/-! ### $R$-Local Sherali–Adams Pseudo-Distributions -/
section LocalPseudoDist
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Predicate asserting that $D : (\iota \to \mathrm{Bool}) \to \mathbb{R}$ is an $R$-local
Sherali–Adams pseudo-distribution: $\tilde{\mathbb{E}}_D[1] = 1$ and $\tilde{\mathbb{E}}_D[f] \ge 0$
for every pointwise non-negative $R$-local junta $f$. -/
def IsLocalPseudoDist (R : ℕ) (D : (ι → Bool) → ℝ) : Prop :=
  pseudoExpect D (fun _ ↦ 1) = 1 ∧
    ∀ f : (ι → Bool) → ℝ, (∀ x, 0 ≤ f x) → IsLocalJunta R f → 0 ≤ pseudoExpect D f

lemma isLocalPseudoDist_iff {R : ℕ} {D : (ι → Bool) → ℝ} :
    IsLocalPseudoDist R D ↔ pseudoExpect D (fun _ ↦ 1) = 1 ∧
      ∀ f : (ι → Bool) → ℝ, (∀ x, 0 ≤ f x) → IsLocalJunta R f → 0 ≤ pseudoExpect D f := Iff.rfl

lemma IsLocalPseudoDist.pseudoExpect_one {R : ℕ} {D : (ι → Bool) → ℝ}
    (hD : IsLocalPseudoDist R D) : pseudoExpect D (fun _ ↦ 1) = 1 := hD.1

lemma IsLocalPseudoDist.sum_eq_one {R : ℕ} {D : (ι → Bool) → ℝ}
    (hD : IsLocalPseudoDist R D) : (∑ x : (ι → Bool), D x) = 1 := by
  have h := hD.pseudoExpect_one; rwa [pseudoExpect_const, mul_one] at h

lemma IsLocalPseudoDist.pseudoExpect_const {R : ℕ} {D : (ι → Bool) → ℝ}
    (hD : IsLocalPseudoDist R D) (c : ℝ) : pseudoExpect D (fun _ ↦ c) = c := by
  rw [_root_.CslibFrontier.Foundations.BooleanAnalysis.pseudoExpect_const, hD.sum_eq_one, one_mul]

lemma IsLocalPseudoDist.pseudoExpect_nonneg_of_isLocalJunta {R : ℕ} {D f : (ι → Bool) → ℝ}
    (hD : IsLocalPseudoDist R D) (hf0 : ∀ x, 0 ≤ f x) (hf : IsLocalJunta R f) :
    0 ≤ pseudoExpect D f := hD.2 f hf0 hf

lemma IsLocalPseudoDist.pseudoExpect_nonneg_of_dependsOn {R : ℕ} {D f : (ι → Bool) → ℝ}
    (hD : IsLocalPseudoDist R D) {J : Finset ι} (hJ : J.card ≤ R)
    (hf0 : ∀ x, 0 ≤ f x) (hf : DependsOn f (J : Set ι)) : 0 ≤ pseudoExpect D f :=
  hD.2 f hf0 ⟨J, hJ, hf⟩

lemma IsLocalPseudoDist.pseudoExpect_mono_of_dependsOn {R : ℕ} {D f g : (ι → Bool) → ℝ}
    (hD : IsLocalPseudoDist R D) {J : Finset ι} (hJ : J.card ≤ R)
    (hf : DependsOn f (J : Set ι)) (hg : DependsOn g (J : Set ι))
    (hfg : ∀ x, f x ≤ g x) : pseudoExpect D f ≤ pseudoExpect D g := by
  have hsub := hD.pseudoExpect_nonneg_of_dependsOn hJ
    (fun x ↦ sub_nonneg.mpr (hfg x)) (dependsOn_sub hg hf)
  rw [pseudoExpect_sub] at hsub; linarith

lemma IsLocalPseudoDist.of_le {R₁ R₂ : ℕ} {D : (ι → Bool) → ℝ}
    (hR : R₂ ≤ R₁) (hD : IsLocalPseudoDist R₁ D) : IsLocalPseudoDist R₂ D :=
  ⟨hD.1, fun f hf0 hf ↦ hD.2 f hf0 (hf.mono hR)⟩

/-- Every genuine probability distribution ($D \ge 0$, $\sum_x D(x) = 1$) is an $R$-local
Sherali–Adams pseudo-distribution for every locality $R$. -/
theorem isLocalPseudoDist_of_nonneg_of_sum_eq_one (R : ℕ) {D : (ι → Bool) → ℝ}
    (hD0 : ∀ x, 0 ≤ D x) (hD1 : (∑ x : (ι → Bool), D x) = 1) : IsLocalPseudoDist R D :=
  ⟨by simp [hD1], fun f hf0 _ ↦ Finset.sum_nonneg fun x _ ↦ mul_nonneg (hD0 x) (hf0 x)⟩
end LocalPseudoDist

/-- Uniform probability distribution $D(x) = 2^{-|\iota|}$ on $\iota \to \mathrm{Bool}$. -/
def uniformPseudoDist (ι : Type*) [Fintype ι] : (ι → Bool) → ℝ :=
  fun _ ↦ 1 / (2 : ℝ) ^ Fintype.card ι

section UniformPseudoDist
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma uniformPseudoDist_apply (x : ι → Bool) :
    uniformPseudoDist ι x = 1 / (2 : ℝ) ^ Fintype.card ι := by
  unfold uniformPseudoDist; rfl

@[simp] lemma pseudoExpect_uniformPseudoDist (f : (ι → Bool) → ℝ) :
    pseudoExpect (uniformPseudoDist ι) f = 𝔼 x : ι → Bool, f x := by
  simp only [pseudoExpect_def, uniformPseudoDist_apply, Finset.expect_eq_sum_div_card,
    Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Nat.cast_pow, Nat.cast_ofNat,
    one_div, inv_mul_eq_div, Finset.sum_div]

lemma isLocalPseudoDist_uniformPseudoDist (R : ℕ) :
    IsLocalPseudoDist R (uniformPseudoDist ι) :=
  ⟨by rw [pseudoExpect_uniformPseudoDist]; simp,
    fun f hf0 _ ↦ by
      rw [pseudoExpect_uniformPseudoDist]
      exact Finset.expect_nonneg fun x _ ↦ hf0 x⟩
end UniformPseudoDist

/-! ### Local Marginal Characterization and Fourier-Moment Gluing -/
section MarginalsAndMoments

/-- Restriction of $x : \iota \to \mathrm{Bool}$ to coordinates in $J : \mathrm{Finset}\,\iota$. -/
def cylinderRes {ι : Type*} (J : Finset ι) (x : ι → Bool) : J → Bool := fun i ↦ x i.1

lemma cylinderRes_apply {ι : Type*} (J : Finset ι) (x : ι → Bool) (i : J) :
    cylinderRes J x i = x i.1 := by unfold cylinderRes; rfl

private lemma chi_cylinderRes {ι : Type*} (J : Finset ι) (S : Finset J) (x : ι → Bool) :
    chi ℝ S (cylinderRes J x) =
      chi ℝ (S.map ⟨Subtype.val, Subtype.val_injective⟩) x := by
  simp [chi_eq_prod_signVal, cylinderRes_apply]

/-- Extension of a local assignment $y : J \to \mathrm{Bool}$ to $\iota \to \mathrm{Bool}$ by
padding coordinates outside $J$ with `false`. -/
def extendFromFinset {ι : Type*} (J : Finset ι) (y : J → Bool) (i : ι) : Bool := by
  classical exact if hi : i ∈ J then y ⟨i, hi⟩ else false

lemma extendFromFinset_mem {ι : Type*} {J : Finset ι} (y : J → Bool) {i : ι} (hi : i ∈ J) :
    extendFromFinset J y i = y ⟨i, hi⟩ := by classical simp [extendFromFinset, hi]

@[simp] lemma cylinderRes_extendFromFinset {ι : Type*} (J : Finset ι) (y : J → Bool) :
    cylinderRes J (extendFromFinset J y) = y := funext fun ⟨_, hi⟩ ↦ extendFromFinset_mem y hi

/-- Indicator function $\mathbf{1}_{x|_J = y}$ of the cylinder prescribed by $y : J \to
\mathrm{Bool}$. -/
def juntaIndicator {ι : Type*} (J : Finset ι) (y : J → Bool) (x : ι → Bool) : ℝ := by
  classical exact if cylinderRes J x = y then 1 else 0

lemma juntaIndicator_def {ι : Type*} (J : Finset ι) (y : J → Bool) (x : ι → Bool) :
    juntaIndicator J y x = (by classical exact if cylinderRes J x = y then 1 else 0) := by
  unfold juntaIndicator; rfl

lemma juntaIndicator_nonneg {ι : Type*} (J : Finset ι) (y : J → Bool) (x : ι → Bool) :
    0 ≤ juntaIndicator J y x := by classical rw [juntaIndicator_def]; split_ifs <;> norm_num

lemma dependsOn_juntaIndicator {ι : Type*} (J : Finset ι) (y : J → Bool) :
    DependsOn (juntaIndicator J y) (J : Set ι) := by
  classical intro x₁ x₂ hxy
  simp only [juntaIndicator_def, show cylinderRes J x₁ = cylinderRes J x₂ from
    funext fun ⟨i, hi⟩ ↦ hxy i hi]

lemma sum_juntaIndicator_eq_one {ι : Type*} [DecidableEq ι] (J : Finset ι) (x : ι → Bool) :
    (∑ y : (J → Bool), juntaIndicator J y x) = 1 := by
  rw [sum_boolCube_eq_single (cylinderRes J x)]
  · classical simp [juntaIndicator_def]
  · intro y hy; classical simp [juntaIndicator_def, hy.symm]

lemma junta_eq_sum_juntaIndicator {ι : Type*} [DecidableEq ι] {J : Finset ι}
    {f : (ι → Bool) → ℝ} (hf : DependsOn f (J : Set ι)) (x : ι → Bool) :
    f x = ∑ y : (J → Bool), f (extendFromFinset J y) * juntaIndicator J y x := by
  rw [sum_boolCube_eq_single (cylinderRes J x)]
  · have heq := hf fun i hi ↦ (extendFromFinset_mem (cylinderRes J x) hi).symm
    classical simp [juntaIndicator_def, heq]
  · intro y hy; classical simp [juntaIndicator_def, hy.symm]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Local marginal weight $D|_J(y) := \tilde{\mathbb{E}}_D[\mathbf{1}_{x|_J = y}]$ induced by $D$ on
assignments $y : J \to \mathrm{Bool}$. -/
def marginalDist (D : (ι → Bool) → ℝ) (J : Finset ι) (y : J → Bool) : ℝ :=
  pseudoExpect D (juntaIndicator J y)

lemma marginalDist_def (D : (ι → Bool) → ℝ) (J : Finset ι) (y : J → Bool) :
    marginalDist D J y = pseudoExpect D (juntaIndicator J y) := by unfold marginalDist; rfl

lemma sum_marginalDist_eq (D : (ι → Bool) → ℝ) (J : Finset ι) :
    (∑ y : (J → Bool), marginalDist D J y) = pseudoExpect D (fun _ ↦ 1) := by
  simp_rw [marginalDist_def, ← pseudoExpect_sum, sum_juntaIndicator_eq_one]

/-- Every $J$-junta's pseudo-expectation under $D$ equals its expectation under the local marginal
weight `marginalDist D J` on $J \to \mathrm{Bool}$. -/
theorem pseudoExpect_eq_sum_marginalDist (D : (ι → Bool) → ℝ) {J : Finset ι}
    {f : (ι → Bool) → ℝ} (hf : DependsOn f (J : Set ι)) :
    pseudoExpect D f = ∑ y : (J → Bool), marginalDist D J y * f (extendFromFinset J y) := by
  conv_lhs => rw [show f = fun x ↦ ∑ y : (J → Bool),
    f (extendFromFinset J y) * juntaIndicator J y x from funext (junta_eq_sum_juntaIndicator hf)]
  rw [pseudoExpect_sum]
  exact Finset.sum_congr rfl fun y _ ↦ by rw [pseudoExpect_smul, marginalDist_def, mul_comm]

lemma IsLocalPseudoDist.marginalDist_nonneg {R : ℕ} {D : (ι → Bool) → ℝ}
    (hD : IsLocalPseudoDist R D) {J : Finset ι} (hJ : J.card ≤ R) (y : J → Bool) :
    0 ≤ marginalDist D J y :=
  hD.pseudoExpect_nonneg_of_dependsOn hJ (juntaIndicator_nonneg J y)
    (dependsOn_juntaIndicator J y)

lemma IsLocalPseudoDist.sum_marginalDist_eq_one {R : ℕ} {D : (ι → Bool) → ℝ}
    (hD : IsLocalPseudoDist R D) (J : Finset ι) :
    (∑ y : (J → Bool), marginalDist D J y) = 1 :=
  (sum_marginalDist_eq D J).trans hD.pseudoExpect_one

lemma IsLocalPseudoDist.isLocalPseudoDist_marginalDist {R : ℕ} {D : (ι → Bool) → ℝ}
    (hD : IsLocalPseudoDist R D) {J : Finset ι} (hJ : J.card ≤ R) (R' : ℕ) :
    IsLocalPseudoDist R' (marginalDist D J) :=
  isLocalPseudoDist_of_nonneg_of_sum_eq_one R' (hD.marginalDist_nonneg hJ)
    (hD.sum_marginalDist_eq_one J)

/-- Characterization of $R$-local pseudo-distributions via non-negative local marginals on all
subsets $J \subseteq \iota$ of cardinality at most $R$. -/
theorem isLocalPseudoDist_iff_marginalDist_nonneg (R : ℕ) (D : (ι → Bool) → ℝ) :
    IsLocalPseudoDist R D ↔ pseudoExpect D (fun _ ↦ 1) = 1 ∧
      ∀ J : Finset ι, J.card ≤ R → ∀ y : (J → Bool), 0 ≤ marginalDist D J y := by
  refine ⟨fun hD ↦ ⟨hD.pseudoExpect_one, fun J hJ y ↦ hD.marginalDist_nonneg hJ y⟩, ?_⟩
  rintro ⟨hone, hmarg⟩; refine ⟨hone, fun f hf0 ⟨J, hJ, hdf⟩ ↦ ?_⟩
  rw [pseudoExpect_eq_sum_marginalDist D hdf]
  exact Finset.sum_nonneg fun y _ ↦ mul_nonneg (hmarg J hJ y) (hf0 _)

/-- Signed density $D(x) = 2^{-|\iota|} \sum_{S \subseteq \iota} m(S)\,\chi_S(x)$ with prescribed
Walsh–Fourier moments $m : \mathrm{Finset}\,\iota \to \mathbb{R}$. -/
def pseudoDistOfMoments (m : Finset ι → ℝ) (x : ι → Bool) : ℝ :=
  (∑ S : Finset ι, m S * chi ℝ S x) / (2 : ℝ) ^ Fintype.card ι

omit [DecidableEq ι] in
lemma pseudoDistOfMoments_def (m : Finset ι → ℝ) (x : ι → Bool) :
    pseudoDistOfMoments m x =
      (∑ S : Finset ι, m S * chi ℝ S x) / (2 : ℝ) ^ Fintype.card ι := by
  unfold pseudoDistOfMoments; rfl

/-- Pseudo-expectation of $f$ under `pseudoDistOfMoments m` equals $\sum_S m(S)\,\widehat{f}(S)$. -/
theorem pseudoExpect_pseudoDistOfMoments (m : Finset ι → ℝ) (f : (ι → Bool) → ℝ) :
    pseudoExpect (pseudoDistOfMoments m) f =
      ∑ S : Finset ι, m S * fourierCoeff f S := by
  simp_rw [pseudoExpect_def, pseudoDistOfMoments_def, Finset.sum_div, Finset.sum_mul,
    div_mul_eq_mul_div]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun S _ ↦ ?_
  rw [← Finset.sum_div, fourierCoeff_eq_sum, ← mul_div_assoc]
  congr 1; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ ↦ by ring

@[simp] lemma pseudoExpect_pseudoDistOfMoments_chi (m : Finset ι → ℝ) (S : Finset ι) :
    pseudoExpect (pseudoDistOfMoments m) (chi ℝ S) = m S := by
  classical rw [pseudoExpect_pseudoDistOfMoments]; simp_rw [fourierCoeff_chi]
  rw [Finset.sum_eq_single S (fun T _ hTS ↦ by simp [hTS.symm])
    (fun hnot ↦ absurd (Finset.mem_univ S) hnot)]; simp

lemma pseudoExpect_pseudoDistOfMoments_one (m : Finset ι → ℝ) :
    pseudoExpect (pseudoDistOfMoments m) (fun _ ↦ 1) = m ∅ := by
  rw [show (fun _ : (ι → Bool) ↦ (1 : ℝ)) = chi ℝ ∅ from funext fun x ↦ (chi_empty x).symm,
    pseudoExpect_pseudoDistOfMoments_chi]

/-- Reconstructing any weight $\mu$ from its Walsh–Fourier pseudo-moments. -/
theorem pseudoDistOfMoments_pseudoExpect_chi (μ : (ι → Bool) → ℝ) :
    pseudoDistOfMoments (fun S ↦ pseudoExpect μ (chi ℝ S)) = μ := by
  classical
  funext y
  have hN : ((2 : ℝ) ^ Fintype.card ι) ≠ 0 := by positivity
  have hm : ∀ S : Finset ι, pseudoExpect μ (chi ℝ S) =
      (2 : ℝ) ^ Fintype.card ι * fourierCoeff μ S := fun S ↦ by
    rw [fourierCoeff_eq_sum, mul_div_cancel₀ _ hN, pseudoExpect_def]
  simp_rw [pseudoDistOfMoments_def, hm, mul_assoc, ← Finset.mul_sum,
    mul_div_cancel_left₀ _ hN, sum_fourierCoeff_mul_chi μ y]

/-- For `pseudoDistOfMoments m`, the local marginal on $J$ is itself `pseudoDistOfMoments` of the
restricted moment function $S \mapsto m(S)$ on $\mathrm{Finset}\,J$. -/
theorem marginalDist_pseudoDistOfMoments (m : Finset ι → ℝ) (J : Finset ι) (y : J → Bool) :
    marginalDist (pseudoDistOfMoments m) J y =
      pseudoDistOfMoments (fun S : Finset J ↦
        m (S.map ⟨Subtype.val, Subtype.val_injective⟩)) y := by
  classical
  let δ : (J → Bool) → ℝ := fun z ↦ if z = y then 1 else 0
  have hexp : ∀ x : ι → Bool, juntaIndicator J y x = ∑ S : Finset J,
      fourierCoeff δ S * chi ℝ (S.map ⟨Subtype.val, Subtype.val_injective⟩) x := fun x ↦ by
    change δ (cylinderRes J x) = _
    exact (sum_fourierCoeff_mul_chi δ (cylinderRes J x)).symm.trans
      (Finset.sum_congr rfl fun S _ ↦ by rw [chi_cylinderRes])
  have hcoeff : ∀ S : Finset J, fourierCoeff δ S =
      chi ℝ S y / (2 : ℝ) ^ Fintype.card J := fun S ↦ by
    rw [fourierCoeff_eq_sum]; congr 1
    rw [sum_boolCube_eq_single y _ (fun z hzy ↦ by simp [δ, hzy])]; simp [δ]
  rw [marginalDist_def, show juntaIndicator J y = _ from funext hexp, pseudoExpect_sum,
    pseudoDistOfMoments_def]
  simp_rw [pseudoExpect_smul, pseudoExpect_pseudoDistOfMoments_chi, hcoeff,
    div_mul_eq_mul_div, ← Finset.sum_div]
  exact congr_arg (· / _) (Finset.sum_congr rfl fun _ _ ↦ mul_comm _ _)

/-- Exact criterion for `pseudoDistOfMoments m` to be an $R$-local pseudo-distribution. -/
theorem isLocalPseudoDist_pseudoDistOfMoments_iff (R : ℕ) (m : Finset ι → ℝ) :
    IsLocalPseudoDist R (pseudoDistOfMoments m) ↔ m ∅ = 1 ∧
      ∀ J : Finset ι, J.card ≤ R → ∀ y : (J → Bool),
        0 ≤ marginalDist (pseudoDistOfMoments m) J y := by
  rw [isLocalPseudoDist_iff_marginalDist_nonneg, pseudoExpect_pseudoDistOfMoments_one]

/-- Gluing constructor: if $m(\emptyset) = 1$ and on every subset $J$ of size at most $R$ the
moments $m$ match the Walsh–Fourier moments of a genuine probability distribution $\mu_J$ on
$J \to \mathrm{Bool}$, then `pseudoDistOfMoments m` is an $R$-local pseudo-distribution. -/
theorem isLocalPseudoDist_pseudoDistOfMoments_of_local_marginals (R : ℕ) (m : Finset ι → ℝ)
    (hm0 : m ∅ = 1) (hloc : ∀ J : Finset ι, J.card ≤ R → ∃ μ : (J → Bool) → ℝ,
      (∀ y, 0 ≤ μ y) ∧ (∑ y : (J → Bool), μ y) = 1 ∧
        ∀ S : Finset J, pseudoExpect μ (chi ℝ S) =
          m (S.map ⟨Subtype.val, Subtype.val_injective⟩)) :
    IsLocalPseudoDist R (pseudoDistOfMoments m) := by
  rw [isLocalPseudoDist_pseudoDistOfMoments_iff]
  refine ⟨hm0, fun J hJ y ↦ ?_⟩
  rcases hloc J hJ with ⟨μ, hμ0, _, hμm⟩
  rw [marginalDist_pseudoDistOfMoments,
    show (fun S : Finset J ↦ m (S.map ⟨Subtype.val, Subtype.val_injective⟩)) =
      fun S ↦ pseudoExpect μ (chi ℝ S) from funext fun S ↦ (hμm S).symm,
    pseudoDistOfMoments_pseudoExpect_chi]
  exact hμ0 y
end MarginalsAndMoments

/-! ### Local-Junta Pushforward and Monomial Substitution -/
section Pushforward

/-- Pushforward $g_* D$ of a signed hypercube weight $D : (\iota \to \mathrm{Bool}) \to \mathbb{R}$
along $g : (\iota \to \mathrm{Bool}) \to (\kappa \to \mathrm{Bool})$, defined by
$(g_* D)(y) = \sum_{x : g(x) = y} D(x)$. -/
def pushforwardPseudoDist {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (g : (ι → Bool) → (κ → Bool)) (D : (ι → Bool) → ℝ) (y : κ → Bool) : ℝ :=
  ∑ x : (ι → Bool), by classical exact if g x = y then D x else 0

lemma pushforwardPseudoDist_def {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (g : (ι → Bool) → (κ → Bool)) (D : (ι → Bool) → ℝ) (y : κ → Bool) :
    pushforwardPseudoDist g D y =
      ∑ x : (ι → Bool), (by classical exact if g x = y then D x else 0) := by
  unfold pushforwardPseudoDist; rfl

/-- Change-of-variables identity
$\tilde{\mathbb{E}}_{g_* D}[h] = \tilde{\mathbb{E}}_D[h \circ g]$. -/
@[simp] theorem pseudoExpect_pushforwardPseudoDist {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    (g : (ι → Bool) → (κ → Bool)) (D : (ι → Bool) → ℝ) (h : (κ → Bool) → ℝ) :
    pseudoExpect (pushforwardPseudoDist g D) h = pseudoExpect D (fun x ↦ h (g x)) := by
  simp_rw [pseudoExpect_def, pushforwardPseudoDist_def, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [sum_boolCube_eq_single (g x) _ (fun y hyg ↦ by classical simp [hyg.symm])]; classical simp

/-- Pushing forward a $(kR)$-local pseudo-distribution along a coordinate map $g$ each of whose
output coordinates depends on at most $k$ input coordinates yields an $R$-local
pseudo-distribution. -/
theorem IsLocalPseudoDist.pushforward {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] {k R : ℕ}
    {g : (ι → Bool) → (κ → Bool)} {D : (ι → Bool) → ℝ} (hD : IsLocalPseudoDist (k * R) D)
    (hg : ∀ a : κ, ∃ supp : Finset ι, supp.card ≤ k ∧
      ∀ ⦃x₁ x₂ : ι → Bool⦄, (∀ i ∈ supp, x₁ i = x₂ i) → g x₁ a = g x₂ a) :
    IsLocalPseudoDist R (pushforwardPseudoDist g D) := by
  classical
  refine ⟨by rw [pseudoExpect_pushforwardPseudoDist]; exact hD.pseudoExpect_one, ?_⟩
  intro h hh0 ⟨K, hK, hdh⟩; rw [pseudoExpect_pushforwardPseudoDist]
  choose supp hcard hdep using hg
  have hJcard : (K.biUnion supp).card ≤ k * R :=
    (Finset.card_biUnion_le.trans (Finset.sum_le_sum fun a _ ↦ hcard a)).trans
      (by simpa [Nat.mul_comm] using Nat.mul_le_mul_right k hK)
  exact hD.pseudoExpect_nonneg_of_dependsOn hJcard (fun x ↦ hh0 (g x)) fun x₁ x₂ hxy ↦
    hdh fun a ha ↦ hdep a fun i hi ↦ hxy i (Finset.mem_biUnion.mpr ⟨a, ha, hi⟩)

/-- Monomial substitution map sending $x : \iota \to \mathrm{Bool}$ to $y : \kappa \to
\mathrm{Bool}$ with $\mathrm{signVal}(y_a) = \chi_{S_a}(x) =
  \prod_{i \in S_a} \mathrm{signVal}(x_i)$. -/
def finsetParityMap {ι κ : Type*} (S : κ → Finset ι) (x : ι → Bool) (a : κ) : Bool := by
  classical exact if chi ℝ (S a) x = 1 then false else true

@[simp] lemma signVal_finsetParityMap {ι κ : Type*} (S : κ → Finset ι) (x : ι → Bool) (a : κ) :
    signVal (finsetParityMap S x a) = chi ℝ (S a) x := by
  classical rcases chi_eq_one_or_neg_one (S a) x with h1 | hm1 <;>
    [norm_num [finsetParityMap, h1]; norm_num [finsetParityMap, hm1]]

/-- Pushforward of a $(kR)$-local pseudo-distribution along `finsetParityMap S` ($|S_a| \le k$). -/
theorem IsLocalPseudoDist.pushforward_finsetParityMap {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    {k R : ℕ} {S : κ → Finset ι} {D : (ι → Bool) → ℝ} (hD : IsLocalPseudoDist (k * R) D)
    (hS : ∀ a : κ, (S a).card ≤ k) :
    IsLocalPseudoDist R (pushforwardPseudoDist (finsetParityMap S) D) :=
  hD.pushforward fun a ↦ ⟨S a, hS a, fun _ _ hxy ↦ by
    classical simp only [finsetParityMap, dependsOn_chi (S a) hxy]⟩

/-- List-parity substitution map sending $x : \iota \to \mathrm{Bool}$ to $y : \kappa \to
\mathrm{Bool}$ with $\mathrm{signVal}(y_a) = \prod_{i \in L_a} \mathrm{signVal}(x_i)$ (supporting
repeated indices). -/
def listParityMap {ι κ : Type*} (L : κ → List ι) (x : ι → Bool) (a : κ) : Bool :=
  (L a).foldr (fun i acc ↦ xor (x i) acc) false

@[simp] lemma signVal_listParityMap {ι κ : Type*} (L : κ → List ι) (x : ι → Bool) (a : κ) :
    signVal (listParityMap L x a) = ((L a).map (fun i ↦ signVal (x i))).prod := by
  unfold listParityMap; induction L a with
  | nil => simp
  | cons i l ih => simp [signVal_xor, ih]

/-- Pushforward of a $(kR)$-local pseudo-distribution along `listParityMap L`
($\ell(L_a) \le k$). -/
theorem IsLocalPseudoDist.pushforward_listParityMap {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    {k R : ℕ} {L : κ → List ι} {D : (ι → Bool) → ℝ} (hD : IsLocalPseudoDist (k * R) D)
    (hL : ∀ a : κ, (L a).length ≤ k) :
    IsLocalPseudoDist R (pushforwardPseudoDist (listParityMap L) D) := by
  classical
  refine hD.pushforward fun a ↦ ⟨(L a).toFinset, (List.toFinset_card_le (L a)).trans (hL a), ?_⟩
  intro x₁ x₂ hxy
  suffices ∀ l : List ι, (∀ i ∈ l, x₁ i = x₂ i) →
      l.foldr (fun i acc ↦ xor (x₁ i) acc) false = l.foldr (fun i acc ↦ xor (x₂ i) acc) false from
    this (L a) fun i hi ↦ hxy i (List.mem_toFinset.mpr hi)
  intro l hl; induction l with
  | nil => rfl
  | cons i l ih =>
    rw [List.foldr_cons, List.foldr_cons, hl i List.mem_cons_self,
      ih (fun j hj ↦ hl j (List.mem_cons_of_mem i hj))]

/-- Tuple-parity substitution map sending $x : \iota \to \mathrm{Bool}$ to $y : \kappa \to
\mathrm{Bool}$ with $\mathrm{signVal}(y_a) =
  \prod_{j : \mathrm{Fin}\,t} \mathrm{signVal}(x_{T_a(j)})$. -/
def tupleParityMap {ι κ : Type*} {t : ℕ} (T : κ → Fin t → ι) (x : ι → Bool) (a : κ) : Bool :=
  listParityMap (fun b ↦ List.ofFn (T b)) x a

@[simp] lemma signVal_tupleParityMap {ι κ : Type*} {t : ℕ} (T : κ → Fin t → ι)
    (x : ι → Bool) (a : κ) :
    signVal (tupleParityMap T x a) = ∏ j : Fin t, signVal (x (T a j)) := by
  rw [tupleParityMap, signVal_listParityMap, List.map_ofFn, List.prod_ofFn]; rfl

/-- Pushforward of a $(tR)$-local pseudo-distribution along `tupleParityMap T`. -/
theorem IsLocalPseudoDist.pushforward_tupleParityMap {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    {t R : ℕ} {T : κ → Fin t → ι} {D : (ι → Bool) → ℝ} (hD : IsLocalPseudoDist (t * R) D) :
    IsLocalPseudoDist R (pushforwardPseudoDist (tupleParityMap T) D) :=
  hD.pushforward_listParityMap fun _ ↦ by simp
end Pushforward

/-! ### Exact Local Cauchy–Schwarz Inequality and Fourier $\ell_1$ Norm -/
section LocalCSAndL1
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Exact local Cauchy–Schwarz inequality for an $s$-local junta $F$ and a $t$-local junta $G$
under an $R$-local pseudo-distribution $D$ whenever $s + t \le R$. -/
theorem local_cauchy_schwarz {R s t : ℕ} {D F G : (ι → Bool) → ℝ}
    (hD : IsLocalPseudoDist R D) (hF : IsLocalJunta s F) (hG : IsLocalJunta t G)
    (hst : s + t ≤ R) :
    0 ≤ pseudoExpect D (fun x ↦ F x ^ 2) ∧
      0 ≤ pseudoExpect D (fun x ↦ G x ^ 2) ∧
      |pseudoExpect D (fun x ↦ F x * G x)| ≤
        Real.sqrt (pseudoExpect D (fun x ↦ F x ^ 2)) *
          Real.sqrt (pseudoExpect D (fun x ↦ G x ^ 2)) := by
  refine ⟨hD.pseudoExpect_nonneg_of_isLocalJunta (fun x ↦ sq_nonneg (F x))
      (hF.sq.mono (le_trans (Nat.le_add_right s t) hst)),
    hD.pseudoExpect_nonneg_of_isLocalJunta (fun x ↦ sq_nonneg (G x))
      (hG.sq.mono (le_trans (Nat.le_add_left t s) hst)), ?_⟩
  rcases hF with ⟨J₁, hJ₁, hdF⟩; rcases hG with ⟨J₂, hJ₂, hdG⟩
  have ⟨J, hJ, hdFJ, hdGJ⟩ : ∃ J : Finset ι, J.card ≤ R ∧
      DependsOn F (J : Set ι) ∧ DependsOn G (J : Set ι) := by
    classical
    exact ⟨J₁ ∪ J₂, ((Finset.card_union_le J₁ J₂).trans (add_le_add hJ₁ hJ₂)).trans hst,
      dependsOn_mono Finset.subset_union_left hdF,
      dependsOn_mono Finset.subset_union_right hdG⟩
  rw [pseudoExpect_eq_sum_marginalDist D (dependsOn_mul hdFJ hdGJ),
    pseudoExpect_eq_sum_marginalDist D (dependsOn_pow hdFJ 2),
    pseudoExpect_eq_sum_marginalDist D (dependsOn_pow hdGJ 2)]
  let u : (J → Bool) → ℝ := fun y ↦ Real.sqrt (marginalDist D J y) * |F (extendFromFinset J y)|
  let v : (J → Bool) → ℝ := fun y ↦ Real.sqrt (marginalDist D J y) * |G (extendFromFinset J y)|
  have hw0 : ∀ y : (J → Bool), 0 ≤ marginalDist D J y := hD.marginalDist_nonneg hJ
  have habs : |∑ y : (J → Bool), marginalDist D J y *
      (F (extendFromFinset J y) * G (extendFromFinset J y))| ≤ ∑ y : (J → Bool), u y * v y := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun y _ ↦ le_of_eq ?_)
    rw [abs_mul, abs_mul, abs_of_nonneg (hw0 y), ← Real.mul_self_sqrt (hw0 y)]
    dsimp [u, v]; ring
  have hu2 : (∑ y : (J → Bool), u y ^ 2) =
      ∑ y : (J → Bool), marginalDist D J y * F (extendFromFinset J y) ^ 2 :=
    Finset.sum_congr rfl fun y _ ↦ by dsimp [u]; rw [mul_pow, Real.sq_sqrt (hw0 y), sq_abs]
  have hv2 : (∑ y : (J → Bool), v y ^ 2) =
      ∑ y : (J → Bool), marginalDist D J y * G (extendFromFinset J y) ^ 2 :=
    Finset.sum_congr rfl fun y _ ↦ by dsimp [v]; rw [mul_pow, Real.sq_sqrt (hw0 y), sq_abs]
  rw [← hu2, ← hv2]
  exact habs.trans (Real.sum_mul_le_sqrt_mul_sqrt Finset.univ u v)

/-- Standalone inequality projection of `local_cauchy_schwarz`. -/
theorem abs_pseudoExpect_mul_le_of_isLocalJunta {R s t : ℕ} {D F G : (ι → Bool) → ℝ}
    (hD : IsLocalPseudoDist R D) (hF : IsLocalJunta s F) (hG : IsLocalJunta t G)
    (hst : s + t ≤ R) :
    |pseudoExpect D (fun x ↦ F x * G x)| ≤
      Real.sqrt (pseudoExpect D (fun x ↦ F x ^ 2)) *
        Real.sqrt (pseudoExpect D (fun x ↦ G x ^ 2)) :=
  (local_cauchy_schwarz hD hF hG hst).2.2

/-- Walsh–Fourier (standard $\pm 1$ monomial basis) $\ell_1$ norm
$\|f\|_1 := \sum_{S \subseteq \iota} |\widehat{f}(S)|$. -/
def fourierL1Norm (f : (ι → Bool) → ℝ) : ℝ := ∑ S : Finset ι, |fourierCoeff f S|

lemma fourierL1Norm_def (f : (ι → Bool) → ℝ) :
    fourierL1Norm f = ∑ S : Finset ι, |fourierCoeff f S| := by unfold fourierL1Norm; rfl

lemma fourierL1Norm_nonneg (f : (ι → Bool) → ℝ) : 0 ≤ fourierL1Norm f :=
  Finset.sum_nonneg fun _ _ ↦ abs_nonneg _

@[simp, grind =] lemma fourierL1Norm_zero : fourierL1Norm (0 : (ι → Bool) → ℝ) = 0 := by
  have hz : ∀ S : Finset ι, fourierCoeff (0 : (ι → Bool) → ℝ) S = 0 := fun S ↦ by
    simp [fourierCoeff_eq_sum]
  simp [fourierL1Norm_def, hz]

lemma fourierL1Norm_eq_zero_iff {f : (ι → Bool) → ℝ} : fourierL1Norm f = 0 ↔ f = 0 := by
  classical
  refine ⟨fun h0 ↦ funext fun x ↦ ?_, fun hf ↦ hf ▸ fourierL1Norm_zero⟩
  have hall := (Finset.sum_eq_zero_iff_of_nonneg fun _ _ ↦ abs_nonneg _).mp h0
  rw [← sum_fourierCoeff_mul_chi f x]
  exact Finset.sum_eq_zero fun S hS ↦ by rw [abs_eq_zero.mp (hall S hS), zero_mul]

@[simp] lemma fourierL1Norm_const (c : ℝ) : fourierL1Norm (fun _ : (ι → Bool) ↦ c) = |c| := by
  classical
  rw [fourierL1Norm_def, Finset.sum_eq_single (∅ : Finset ι)]
  · simp
  · intro S _ hS; simp [fourierCoeff_const, hS]
  · intro hnot; exact absurd (Finset.mem_univ _) hnot

@[simp] lemma fourierL1Norm_chi (S : Finset ι) :
    fourierL1Norm (chi ℝ S) = 1 := by
  classical
  rw [fourierL1Norm_def, Finset.sum_eq_single S]
  · simp [fourierCoeff_chi]
  · intro T _ hTS; simp [fourierCoeff_chi, hTS.symm]
  · intro hnot; exact absurd (Finset.mem_univ S) hnot

@[simp] lemma fourierL1Norm_neg (f : (ι → Bool) → ℝ) :
    fourierL1Norm (fun x ↦ -f x) = fourierL1Norm f := by
  have hneg : ∀ S : Finset ι, fourierCoeff (fun x ↦ -f x) S = -fourierCoeff f S := fun S ↦ by
    simpa using fourierCoeff_const_mul (-1) f S
  simp [fourierL1Norm_def, hneg]

lemma fourierL1Norm_smul (c : ℝ) (f : (ι → Bool) → ℝ) :
    fourierL1Norm (fun x ↦ c * f x) = |c| * fourierL1Norm f := by
  simp_rw [fourierL1Norm_def, fourierCoeff_const_mul, abs_mul, ← Finset.mul_sum]

lemma fourierL1Norm_add_le (f g : (ι → Bool) → ℝ) :
    fourierL1Norm (fun x ↦ f x + g x) ≤ fourierL1Norm f + fourierL1Norm g := by
  rw [fourierL1Norm_def, fourierL1Norm_def, fourierL1Norm_def, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun S _ ↦ by rw [fourierCoeff_add]; exact abs_add_le _ _

lemma fourierL1Norm_eq_sum_filter_of_mem_lowDegree {d : ℕ} {f : (ι → Bool) → ℝ}
    (hf : f ∈ lowDegree ℝ ι d) :
    fourierL1Norm f = ∑ S ∈ Finset.univ.filter (fun S : Finset ι ↦ S.card ≤ d),
        |fourierCoeff f S| := by
  classical
  rw [fourierL1Norm_def]; symm
  refine Finset.sum_subset (Finset.subset_univ _) fun S _ hnot ↦ ?_
  have hlt : d < S.card :=
    lt_of_not_ge fun hle ↦ hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ S, hle⟩)
  simp [fourierCoeff_eq_zero_of_mem_lowDegree hf hlt]

lemma fourierCoeff_finset_sum {α : Type*} (s : Finset α) (g : α → (ι → Bool) → ℝ) (S : Finset ι) :
    fourierCoeff (fun x ↦ ∑ a ∈ s, g a x) S = ∑ a ∈ s, fourierCoeff (g a) S := by
  classical
  induction s using Finset.induction with
  | empty => simp [fourierCoeff_eq_sum]
  | insert a s has ih =>
    simp_rw [Finset.sum_insert has, fourierCoeff_add, ih]

/-- Pointwise supremum bound $|f(x)| \le \|f\|_1$. -/
theorem abs_le_fourierL1Norm (f : (ι → Bool) → ℝ) (x : ι → Bool) :
    |f x| ≤ fourierL1Norm f := abs_le_sum_abs_fourierCoeff f x

/-- Every Walsh character $\chi_S$ of size $|S| \le R$ has $|\tilde{\mathbb{E}}_D[\chi_S]| \le 1$
under any $R$-local pseudo-distribution $D$. -/
theorem IsLocalPseudoDist.abs_pseudoExpect_chi_le_one {R : ℕ} {D : (ι → Bool) → ℝ}
    (hD : IsLocalPseudoDist R D) {S : Finset ι} (hS : S.card ≤ R) :
    |pseudoExpect D (chi ℝ S)| ≤ 1 := by
  have hsub := hD.pseudoExpect_nonneg_of_dependsOn hS
    (fun x ↦ by rcases chi_eq_one_or_neg_one S x with h | h <;> linarith)
    (dependsOn_sub (dependsOn_const_finset S 1) (dependsOn_chi S))
  have hadd := hD.pseudoExpect_nonneg_of_dependsOn hS
    (fun x ↦ by rcases chi_eq_one_or_neg_one S x with h | h <;> linarith)
    (dependsOn_add (dependsOn_const_finset S 1) (dependsOn_chi S))
  rw [pseudoExpect_sub, hD.pseudoExpect_one] at hsub
  rw [pseudoExpect_add, hD.pseudoExpect_one] at hadd
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Triangle-inequality bound $|\tilde{\mathbb{E}}_D[f]| \le \|f\|_1$ when $\deg(f) \le d \le R$. -/
theorem abs_pseudoExpect_le_fourierL1Norm {d R : ℕ} {D f : (ι → Bool) → ℝ}
    (hf : f ∈ lowDegree ℝ ι d) (hdR : d ≤ R) (hD : IsLocalPseudoDist R D) :
    |pseudoExpect D f| ≤ fourierL1Norm f := by
  classical
  have htrunc : f = fun x ↦ ∑ S ∈ Finset.univ.filter (fun S : Finset ι ↦ S.card ≤ d),
      fourierCoeff f S * chi ℝ S x := funext fun x ↦ by
    rw [← sum_fourierCoeff_mul_chi f x]
    symm
    refine Finset.sum_subset (Finset.subset_univ _) fun S _ hnot ↦ ?_
    have hlt : d < S.card :=
      lt_of_not_ge fun hle ↦ hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ S, hle⟩)
    simp [fourierCoeff_eq_zero_of_mem_lowDegree hf hlt]
  conv_lhs => rw [htrunc]
  rw [fourierL1Norm_eq_sum_filter_of_mem_lowDegree hf, pseudoExpect_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun S hS ↦ ?_)
  rw [pseudoExpect_smul, abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _)
    (hD.abs_pseudoExpect_chi_le_one ((Finset.mem_filter.mp hS).2.trans hdR))
end LocalCSAndL1

/-! ### Approximate Cauchy–Schwarz Inequality -/
section ApproxCS
private def prodWeight {α : Type*} (s : ℕ) (p : α → ℝ) (ω : Fin s → α) : ℝ := ∏ ℓ : Fin s, p (ω ℓ)

private lemma prodWeight_nonneg {α : Type*} {s : ℕ} {p : α → ℝ} (hp0 : ∀ a, 0 ≤ p a)
    (ω : Fin s → α) : 0 ≤ prodWeight s p ω := Finset.prod_nonneg fun ℓ _ ↦ hp0 (ω ℓ)

private lemma sum_prodWeight_eq_one {α : Type*} [Fintype α] {s : ℕ} {p : α → ℝ}
    (hp1 : (∑ a : α, p a) = 1) : (∑ ω : (Fin s → α), prodWeight s p ω) = 1 := by
  unfold prodWeight; rw [← Fintype.prod_sum (fun (_ : Fin s) (a : α) ↦ p a)]; simp [hp1]

private lemma sum_prodWeight_coord {α : Type*} [Fintype α] {s : ℕ} {p : α → ℝ}
    (hp1 : (∑ a : α, p a) = 1) (ℓ₀ : Fin s) (ϕ : α → ℝ) :
    (∑ ω : (Fin s → α), prodWeight s p ω * ϕ (ω ℓ₀)) = ∑ a : α, p a * ϕ a := by
  let M : Fin s → α → ℝ := fun ℓ a ↦ if ℓ = ℓ₀ then p a * ϕ a else p a
  have hpt : ∀ ω : Fin s → α, (∏ ℓ : Fin s, M ℓ (ω ℓ)) = prodWeight s p ω * ϕ (ω ℓ₀) := fun ω ↦ by
    rw [← Finset.mul_prod_erase Finset.univ (fun ℓ ↦ M ℓ (ω ℓ)) (Finset.mem_univ ℓ₀)]
    have her : (∏ ℓ ∈ Finset.univ.erase ℓ₀, M ℓ (ω ℓ)) = ∏ ℓ ∈ Finset.univ.erase ℓ₀, p (ω ℓ) :=
      Finset.prod_congr rfl fun ℓ hℓ ↦ by simp [M, Finset.ne_of_mem_erase hℓ]
    simp only [M, ↓reduceIte, her]
    rw [mul_right_comm, Finset.mul_prod_erase Finset.univ (fun ℓ ↦ p (ω ℓ)) (Finset.mem_univ ℓ₀)]
    rfl
  simp_rw [← hpt, ← Fintype.prod_sum M]
  rw [← Finset.mul_prod_erase Finset.univ (fun ℓ ↦ ∑ a : α, M ℓ a) (Finset.mem_univ ℓ₀),
    Finset.prod_eq_one fun ℓ hℓ ↦ by simp [M, Finset.ne_of_mem_erase hℓ, hp1], mul_one]
  simp [M]

private lemma sum_prodWeight_pair_of_ne {α : Type*} [Fintype α] {s : ℕ} {p : α → ℝ}
    (hp1 : (∑ a : α, p a) = 1) {ℓ₁ ℓ₂ : Fin s} (hne : ℓ₁ ≠ ℓ₂) (ϕ₁ ϕ₂ : α → ℝ) :
    (∑ ω : (Fin s → α), prodWeight s p ω * (ϕ₁ (ω ℓ₁) * ϕ₂ (ω ℓ₂))) =
      (∑ a : α, p a * ϕ₁ a) * (∑ b : α, p b * ϕ₂ b) := by
  let M : Fin s → α → ℝ := fun ℓ a ↦
    if ℓ = ℓ₁ then p a * ϕ₁ a else if ℓ = ℓ₂ then p a * ϕ₂ a else p a
  have hmem₂ : ℓ₂ ∈ Finset.univ.erase ℓ₁ := Finset.mem_erase.mpr ⟨hne.symm, Finset.mem_univ ℓ₂⟩
  have hpt : ∀ ω : Fin s → α, (∏ ℓ : Fin s, M ℓ (ω ℓ)) =
      prodWeight s p ω * (ϕ₁ (ω ℓ₁) * ϕ₂ (ω ℓ₂)) := fun ω ↦ by
    rw [← Finset.mul_prod_erase Finset.univ (fun ℓ ↦ M ℓ (ω ℓ)) (Finset.mem_univ ℓ₁),
      ← Finset.mul_prod_erase (Finset.univ.erase ℓ₁) (fun ℓ ↦ M ℓ (ω ℓ)) hmem₂]
    have her : (∏ ℓ ∈ (Finset.univ.erase ℓ₁).erase ℓ₂, M ℓ (ω ℓ)) =
        ∏ ℓ ∈ (Finset.univ.erase ℓ₁).erase ℓ₂, p (ω ℓ) :=
      Finset.prod_congr rfl fun ℓ hℓ ↦ by
        simp [M, Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hℓ), Finset.ne_of_mem_erase hℓ]
    have hp_split : prodWeight s p ω = p (ω ℓ₁) * (p (ω ℓ₂) *
        ∏ ℓ ∈ (Finset.univ.erase ℓ₁).erase ℓ₂, p (ω ℓ)) := by
      unfold prodWeight; rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ ℓ₁),
        ← Finset.mul_prod_erase (Finset.univ.erase ℓ₁) _ hmem₂]
    simp only [M, ↓reduceIte, hne.symm, her, hp_split]; ring
  simp_rw [← hpt, ← Fintype.prod_sum M]
  rw [← Finset.mul_prod_erase Finset.univ (fun ℓ ↦ ∑ a : α, M ℓ a) (Finset.mem_univ ℓ₁),
    ← Finset.mul_prod_erase (Finset.univ.erase ℓ₁) (fun ℓ ↦ ∑ a : α, M ℓ a) hmem₂,
    Finset.prod_eq_one fun ℓ hℓ ↦ by
      simp [M, Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hℓ), Finset.ne_of_mem_erase hℓ, hp1],
    mul_one]
  simp [M, hne.symm]

private def realSign (r : ℝ) : ℝ := by classical exact if 0 ≤ r then 1 else -1

private lemma realSign_mul_abs (r : ℝ) : realSign r * |r| = r := by
  classical unfold realSign; split_ifs with hr
  · rw [one_mul, abs_of_nonneg hr]
  · rw [neg_one_mul, abs_of_neg (lt_of_not_ge hr), neg_neg]

private lemma realSign_sq (r : ℝ) : realSign r ^ 2 = 1 := by
  classical unfold realSign; split_ifs <;> norm_num

private lemma exists_local_sampling_estimator.{u} {ι : Type u} [Fintype ι] [DecidableEq ι] {d s : ℕ}
    {f : (ι → Bool) → ℝ} (hf : f ∈ lowDegree ℝ ι d)
    (hL : 0 < fourierL1Norm f) (hs : 0 < s) (D : (ι → Bool) → ℝ)
    (hone : pseudoExpect D (fun _ ↦ 1) = 1) :
    ∃ (Ωs : Type u) (_ : Fintype Ωs) (W : Ωs → ℝ) (F : Ωs → (ι → Bool) → ℝ),
      (∀ ω, 0 ≤ W ω) ∧ (∑ ω : Ωs, W ω) = 1 ∧ (∀ ω, IsLocalJunta (d * s) (F ω)) ∧
      (∀ x, (∑ ω : Ωs, W ω * F ω x) = f x) ∧
      (∑ ω : Ωs, W ω * pseudoExpect D (fun x ↦ F ω x ^ 2)) =
        (1 - 1 / (s : ℝ)) * pseudoExpect D (fun x ↦ f x ^ 2) +
          (1 / (s : ℝ)) * fourierL1Norm f ^ 2 := by
  classical
  let A : Type u := {S : Finset ι // S.card ≤ d}
  let L := fourierL1Norm f
  let p : A → ℝ := fun S ↦ |fourierCoeff f S.1| / L
  have hp0 : ∀ S : A, 0 ≤ p S := fun S ↦ div_nonneg (abs_nonneg _) hL.le
  have hsumA : ∀ g : Finset ι → ℝ, (∑ S : A, g S.1) =
      ∑ S ∈ Finset.univ.filter (fun S : Finset ι ↦ S.card ≤ d), g S := fun g ↦ by
    simpa using (Finset.sum_subtype (Finset.univ.filter (fun S : Finset ι ↦ S.card ≤ d))
      (fun _ ↦ Finset.mem_filter.trans (and_iff_right (Finset.mem_univ _))) g).symm
  have hp1 : (∑ S : A, p S) = 1 := by
    dsimp [p]; rw [← Finset.sum_div, hsumA (fun S ↦ |fourierCoeff f S|),
      ← fourierL1Norm_eq_sum_filter_of_mem_lowDegree hf]; exact div_self hL.ne'
  let X : A → (ι → Bool) → ℝ := fun S x ↦
    L * realSign (fourierCoeff f S.1) * chi ℝ S.1 x
  have hX1 : ∀ x : (ι → Bool), (∑ S : A, p S * X S x) = f x := fun x ↦ by
    have hterm : ∀ S : A, p S * X S x = fourierCoeff f S.1 * chi ℝ S.1 x := fun S ↦ by
      dsimp [p, X]; rw [← mul_assoc, ← mul_assoc, div_mul_cancel₀ _ hL.ne',
        mul_comm _ (realSign _), realSign_mul_abs]
    simp_rw [hterm]
    rw [hsumA (fun S ↦ fourierCoeff f S * chi ℝ S x), ← sum_fourierCoeff_mul_chi f x]
    refine Finset.sum_subset (Finset.subset_univ _) fun S _ hnot ↦ ?_
    have hlt : d < S.card :=
      lt_of_not_ge fun hle ↦ hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ S, hle⟩)
    simp [fourierCoeff_eq_zero_of_mem_lowDegree hf hlt]
  have hXsq : ∀ (S : A) (x : ι → Bool), X S x ^ 2 = L ^ 2 := fun S x ↦ by
    dsimp [X]; rw [mul_pow, mul_pow, realSign_sq, chi_sq, mul_one, mul_one]
  let Ωs : Type u := Fin s → A
  let W : Ωs → ℝ := prodWeight s p
  let F : Ωs → (ι → Bool) → ℝ := fun ω x ↦ (1 / (s : ℝ)) * ∑ ℓ : Fin s, X (ω ℓ) x
  have hs_pos : (0 : ℝ) < (s : ℝ) := Nat.cast_pos.mpr hs
  refine ⟨Ωs, inferInstance, W, F, prodWeight_nonneg hp0, sum_prodWeight_eq_one hp1, ?_, ?_, ?_⟩
  · intro ω; refine IsLocalJunta.smul (1 / (s : ℝ)) ?_
    simpa [Fintype.card_fin] using isLocalJunta_sum_le Finset.univ d
      (fun ℓ x ↦ X (ω ℓ) x) (fun ℓ _ ↦ (isLocalJunta_chi_of_le (ω ℓ).2).smul _)
  · intro x
    have hpull : (∑ ω : Ωs, W ω * F ω x) =
        (1 / (s : ℝ)) * ∑ ℓ : Fin s, ∑ ω : Ωs, W ω * X (ω ℓ) x := by
      dsimp [F]; rw [Finset.mul_sum]
      conv_lhs => arg 2; ext ω; rw [← mul_assoc, mul_comm (W ω) (1 / (s : ℝ)), mul_assoc,
        Finset.mul_sum, Finset.mul_sum]
      rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun _ _ ↦ (Finset.mul_sum _ _ _).symm
    have hcoord : ∀ ℓ : Fin s, (∑ ω : Ωs, W ω * X (ω ℓ) x) = f x :=
      fun ℓ ↦ (sum_prodWeight_coord hp1 ℓ (fun S ↦ X S x)).trans (hX1 x)
    rw [hpull]; simp_rw [hcoord, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp [hs_pos.ne']
  · have hFsq : ∀ ω : Ωs, pseudoExpect D (fun x ↦ F ω x ^ 2) =
        (1 / (s : ℝ) ^ 2) * ∑ ℓ₁ : Fin s, ∑ ℓ₂ : Fin s,
          pseudoExpect D (fun x ↦ X (ω ℓ₁) x * X (ω ℓ₂) x) := fun ω ↦ by
      have hexp : (fun x : (ι → Bool) ↦ F ω x ^ 2) = fun x ↦ (1 / (s : ℝ) ^ 2) *
          ∑ ℓ₁ : Fin s, ∑ ℓ₂ : Fin s, X (ω ℓ₁) x * X (ω ℓ₂) x := funext fun x ↦ by
        dsimp [F]; rw [mul_pow, one_div_pow, sq (∑ ℓ : Fin s, X (ω ℓ) x), Finset.sum_mul]
        exact congr_arg _ (Finset.sum_congr rfl fun _ _ ↦ Finset.mul_sum _ _ _)
      rw [hexp, pseudoExpect_smul, pseudoExpect_sum]
      exact congr_arg _ (Finset.sum_congr rfl fun _ _ ↦ pseudoExpect_sum _ _ _)
    simp_rw [hFsq, ← mul_assoc, mul_comm (W _) (1 / (s : ℝ) ^ 2), mul_assoc, ← Finset.mul_sum]
    have hpair : ∀ ℓ₁ ℓ₂ : Fin s,
        (∑ ω : Ωs, W ω * pseudoExpect D (fun x ↦ X (ω ℓ₁) x * X (ω ℓ₂) x)) =
          if ℓ₁ = ℓ₂ then L ^ 2 else pseudoExpect D (fun x ↦ f x ^ 2) := fun ℓ₁ ℓ₂ ↦ by
      split_ifs with heq
      · subst heq
        have hpeL : ∀ ω : Ωs,
            pseudoExpect D (fun x ↦ X (ω ℓ₁) x * X (ω ℓ₁) x) = L ^ 2 := fun ω ↦ by
          simp_rw [← sq, hXsq (ω ℓ₁), show (fun _ : (ι → Bool) ↦ L ^ 2) =
            fun _ ↦ L ^ 2 * (1 : ℝ) by ext; ring]
          rw [pseudoExpect_smul, hone, mul_one]
        simp_rw [hpeL]
        rw [← Finset.sum_mul, sum_prodWeight_eq_one hp1, one_mul]
      · simp_rw [pseudoExpect_def, Finset.mul_sum]; rw [Finset.sum_comm]
        have hinner : ∀ x : (ι → Bool),
            (∑ ω : Ωs, W ω * (D x * (X (ω ℓ₁) x * X (ω ℓ₂) x))) = D x * f x ^ 2 := fun x ↦ by
          simp_rw [← mul_assoc, mul_comm (W _) (D x), mul_assoc, ← Finset.mul_sum]
          rw [sum_prodWeight_pair_of_ne hp1 heq (fun S ↦ X S x) (fun S ↦ X S x), hX1 x, sq]
        simp_rw [hinner]
    have hswap : (∑ ω : Ωs, ∑ ℓ₁ : Fin s, ∑ ℓ₂ : Fin s,
        W ω * pseudoExpect D (fun x ↦ X (ω ℓ₁) x * X (ω ℓ₂) x)) =
        ∑ ℓ₁ : Fin s, ∑ ℓ₂ : Fin s,
          ∑ ω : Ωs, W ω * pseudoExpect D (fun x ↦ X (ω ℓ₁) x * X (ω ℓ₂) x) := by
      rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_comm
    conv_lhs => arg 2; arg 2; ext ω; rw [Finset.mul_sum]
    conv_lhs => arg 2; arg 2; ext ω; arg 2; ext ℓ₁; rw [Finset.mul_sum]
    rw [hswap]; simp_rw [hpair]
    have hrow : ∀ ℓ₁ : Fin s,
        (∑ ℓ₂ : Fin s, if ℓ₁ = ℓ₂ then L ^ 2 else pseudoExpect D (fun x ↦ f x ^ 2)) =
          L ^ 2 + (((s : ℝ) - 1) * pseudoExpect D (fun x ↦ f x ^ 2)) := fun ℓ₁ ↦ by
      rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ ℓ₁)]; simp only [↓reduceIte]
      rw [Finset.sum_congr rfl fun ℓ₂ hℓ₂ ↦ show (if ℓ₁ = ℓ₂ then L ^ 2 else
        pseudoExpect D (fun x ↦ f x ^ 2)) = pseudoExpect D (fun x ↦ f x ^ 2) by
          simp [(Finset.ne_of_mem_erase hℓ₂).symm],
        Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ ℓ₁), Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, Nat.cast_sub hs, Nat.cast_one]
    simp_rw [hrow, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    dsimp [L]; field_simp [hs_pos.ne']; ring

private lemma weighted_sum_sqrt_le {Ω : Type*} [Fintype Ω] {W a : Ω → ℝ}
    (hW0 : ∀ ω, 0 ≤ W ω) (hW1 : (∑ ω : Ω, W ω) = 1) (ha0 : ∀ ω, 0 ≤ a ω) :
    (∑ ω : Ω, W ω * Real.sqrt (a ω)) ≤ Real.sqrt (∑ ω : Ω, W ω * a ω) := by
  let u : Ω → ℝ := fun ω ↦ Real.sqrt (W ω)
  let v : Ω → ℝ := fun ω ↦ Real.sqrt (W ω * a ω)
  have huv : (∑ ω : Ω, W ω * Real.sqrt (a ω)) = ∑ ω : Ω, u ω * v ω :=
    Finset.sum_congr rfl fun ω _ ↦ by
      dsimp [u, v]; rw [Real.sqrt_mul (hW0 ω), ← mul_assoc, Real.mul_self_sqrt (hW0 ω)]
  have hu2 : (∑ ω : Ω, u ω ^ 2) = 1 := by
    rw [← hW1]; exact Finset.sum_congr rfl fun ω _ ↦ Real.sq_sqrt (hW0 ω)
  have hv2 : (∑ ω : Ω, v ω ^ 2) = ∑ ω : Ω, W ω * a ω :=
    Finset.sum_congr rfl fun ω _ ↦ Real.sq_sqrt (mul_nonneg (hW0 ω) (ha0 ω))
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ u v
  rw [hu2, hv2, Real.sqrt_one, one_mul] at hcs; exact huv.trans_le hcs

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Non-negativity of the sampling second-moment radicand
$(1 - 1/s)\,\tilde{\mathbb{E}}_D[f^2] + (1/s)\,\|f\|_1^2$ whenever $\deg(f) \le d$, $s > 0$, and
$d \cdot s \le R$. -/
theorem approx_cs_radicand_nonneg {d R s : ℕ} {D f : (ι → Bool) → ℝ}
    (hf : f ∈ lowDegree ℝ ι d) (hD : IsLocalPseudoDist R D)
    (hs : 0 < s) (hdR : d * s ≤ R) :
    0 ≤ (1 - 1 / (s : ℝ)) * pseudoExpect D (fun x ↦ f x ^ 2) +
      (1 / (s : ℝ)) * fourierL1Norm f ^ 2 := by
  rcases eq_or_lt_of_le (fourierL1Norm_nonneg f) with hL0 | hL
  · obtain rfl := fourierL1Norm_eq_zero_iff.mp hL0.symm; simp
  · obtain ⟨Ωs, _, W, F, hW0, _, hFloc, _, hsec⟩ :=
      exists_local_sampling_estimator hf hL hs D hD.pseudoExpect_one
    rw [← hsec]
    exact Finset.sum_nonneg fun ω _ ↦ mul_nonneg (hW0 ω)
      (hD.pseudoExpect_nonneg_of_isLocalJunta (fun x ↦ sq_nonneg (F ω x))
        ((hFloc ω).sq.mono hdR))

/-- Asymmetric-degree approximate Cauchy–Schwarz inequality: for polynomials $f$ of degree at most
$d_1$ and $g$ of degree at most $d_2$, any $R$-local pseudo-distribution $D$, and positive integers
$s, t$ with $d_1 s + d_2 t \le R$,
$|\tilde{\mathbb{E}}_D[fg]| \le \sqrt{(1 - 1/s)\tilde{\mathbb{E}}_D[f^2] + \|f\|_1^2 / s}
\,\sqrt{(1 - 1/t)\tilde{\mathbb{E}}_D[g^2] + \|g\|_1^2 / t}$. -/
theorem approx_cauchy_schwarz_asymmetric {d₁ d₂ R s t : ℕ} {D f g : (ι → Bool) → ℝ}
    (hf : f ∈ lowDegree ℝ ι d₁) (hg : g ∈ lowDegree ℝ ι d₂)
    (hD : IsLocalPseudoDist R D) (hs : 0 < s) (ht : 0 < t) (hR : d₁ * s + d₂ * t ≤ R) :
    |pseudoExpect D (fun x ↦ f x * g x)| ≤
      Real.sqrt ((1 - 1 / (s : ℝ)) * pseudoExpect D (fun x ↦ f x ^ 2) +
        (1 / (s : ℝ)) * fourierL1Norm f ^ 2) *
      Real.sqrt ((1 - 1 / (t : ℝ)) * pseudoExpect D (fun x ↦ g x ^ 2) +
        (1 / (t : ℝ)) * fourierL1Norm g ^ 2) := by
  rcases eq_or_lt_of_le (fourierL1Norm_nonneg f) with hLf0 | hLf
  · obtain rfl := fourierL1Norm_eq_zero_iff.mp hLf0.symm
    simp only [Pi.zero_apply, zero_mul, show (fun _ : (ι → Bool) ↦ (0 : ℝ)) = 0 from rfl,
      pseudoExpect_zero, abs_zero]; positivity
  rcases eq_or_lt_of_le (fourierL1Norm_nonneg g) with hLg0 | hLg
  · obtain rfl := fourierL1Norm_eq_zero_iff.mp hLg0.symm
    simp only [Pi.zero_apply, mul_zero, show (fun _ : (ι → Bool) ↦ (0 : ℝ)) = 0 from rfl,
      pseudoExpect_zero, abs_zero]; positivity
  obtain ⟨Ωs, _, W₁, F, hW₁0, hW₁1, hFloc, hF1, hF2⟩ :=
    exists_local_sampling_estimator hf hLf hs D hD.pseudoExpect_one
  obtain ⟨Ωt, _, W₂, G, hW₂0, hW₂1, hGloc, hG1, hG2⟩ :=
    exists_local_sampling_estimator hg hLg ht D hD.pseudoExpect_one
  have hfg_decomp : pseudoExpect D (fun x ↦ f x * g x) =
      ∑ ω₁ : Ωs, ∑ ω₂ : Ωt, W₁ ω₁ * W₂ ω₂ * pseudoExpect D (fun x ↦ F ω₁ x * G ω₂ x) := by
    have hpt : (fun x : (ι → Bool) ↦ f x * g x) =
        fun x ↦ ∑ ω₁ : Ωs, ∑ ω₂ : Ωt, (W₁ ω₁ * W₂ ω₂) * (F ω₁ x * G ω₂ x) := funext fun x ↦ by
      rw [← hF1 x, ← hG1 x, Finset.sum_mul]
      exact Finset.sum_congr rfl fun ω₁ _ ↦ by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun ω₂ _ ↦ by ring
    rw [hpt, pseudoExpect_sum]
    exact Finset.sum_congr rfl fun ω₁ _ ↦ by
      rw [pseudoExpect_sum]; exact Finset.sum_congr rfl fun ω₂ _ ↦ pseudoExpect_smul _ _ _
  have hstep1 : |pseudoExpect D (fun x ↦ f x * g x)| ≤
      (∑ ω₁ : Ωs, W₁ ω₁ * Real.sqrt (pseudoExpect D (fun x ↦ F ω₁ x ^ 2))) *
        (∑ ω₂ : Ωt, W₂ ω₂ * Real.sqrt (pseudoExpect D (fun x ↦ G ω₂ x ^ 2))) := by
    rw [hfg_decomp, Finset.sum_mul]
    conv_rhs => arg 2; ext ω₁; rw [Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun ω₁ _ ↦ ?_)
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun ω₂ _ ↦ ?_)
    rw [abs_mul, abs_of_nonneg (mul_nonneg (hW₁0 ω₁) (hW₂0 ω₂))]
    have hcs := abs_pseudoExpect_mul_le_of_isLocalJunta hD (hFloc ω₁) (hGloc ω₂) hR
    have hmul := mul_le_mul_of_nonneg_left hcs (mul_nonneg (hW₁0 ω₁) (hW₂0 ω₂))
    linarith [show (W₁ ω₁ * W₂ ω₂) *
      (Real.sqrt (pseudoExpect D (fun x ↦ F ω₁ x ^ 2)) *
        Real.sqrt (pseudoExpect D (fun x ↦ G ω₂ x ^ 2))) =
      W₁ ω₁ * Real.sqrt (pseudoExpect D (fun x ↦ F ω₁ x ^ 2)) *
        (W₂ ω₂ * Real.sqrt (pseudoExpect D (fun x ↦ G ω₂ x ^ 2))) by ring]
  have ha₁ : ∀ ω₁ : Ωs, 0 ≤ pseudoExpect D (fun x ↦ F ω₁ x ^ 2) := fun ω₁ ↦
    hD.pseudoExpect_nonneg_of_isLocalJunta (fun x ↦ sq_nonneg (F ω₁ x))
      ((hFloc ω₁).sq.mono (le_trans (Nat.le_add_right _ _) hR))
  have ha₂ : ∀ ω₂ : Ωt, 0 ≤ pseudoExpect D (fun x ↦ G ω₂ x ^ 2) := fun ω₂ ↦
    hD.pseudoExpect_nonneg_of_isLocalJunta (fun x ↦ sq_nonneg (G ω₂ x))
      ((hGloc ω₂).sq.mono (le_trans (Nat.le_add_left _ _) hR))
  have hb₁ := (weighted_sum_sqrt_le hW₁0 hW₁1 ha₁).trans_eq (congr_arg Real.sqrt hF2)
  have hb₂ := (weighted_sum_sqrt_le hW₂0 hW₂1 ha₂).trans_eq (congr_arg Real.sqrt hG2)
  exact hstep1.trans (mul_le_mul hb₁ hb₂
    (Finset.sum_nonneg fun ω₂ _ ↦ mul_nonneg (hW₂0 ω₂) (Real.sqrt_nonneg _))
    (Real.sqrt_nonneg _))

/-- Approximate Cauchy–Schwarz inequality for degree-$\le d$ polynomials $f, g$ on
$\iota \to \mathrm{Bool}$ under any $R$-local Sherali–Adams pseudo-distribution $D$ whenever
$s, t > 0$ and $d(s + t) \le R$. -/
theorem approx_cauchy_schwarz {d R s t : ℕ} {D f g : (ι → Bool) → ℝ}
    (hf : f ∈ lowDegree ℝ ι d) (hg : g ∈ lowDegree ℝ ι d)
    (hD : IsLocalPseudoDist R D) (hs : 0 < s) (ht : 0 < t) (hR : d * (s + t) ≤ R) :
    |pseudoExpect D (fun x ↦ f x * g x)| ≤
      Real.sqrt ((1 - 1 / (s : ℝ)) * pseudoExpect D (fun x ↦ f x ^ 2) +
        (1 / (s : ℝ)) * fourierL1Norm f ^ 2) *
      Real.sqrt ((1 - 1 / (t : ℝ)) * pseudoExpect D (fun x ↦ g x ^ 2) +
        (1 / (t : ℝ)) * fourierL1Norm g ^ 2) :=
  approx_cauchy_schwarz_asymmetric hf hg hD hs ht (by linarith [mul_add d s t])

/-- Single-polynomial approximate Cauchy–Schwarz bound ($g = 1$, $t = 1$): for any polynomial $f$
of degree at most $d$, any $R$-local pseudo-distribution $D$, and any $s > 0$ with
$d \cdot s \le R$,
$|\tilde{\mathbb{E}}_D[f]| \le \sqrt{(1 - 1/s)\tilde{\mathbb{E}}_D[f^2] + \|f\|_1^2 / s}$. -/
theorem abs_pseudoExpect_le_sqrt_approx_cs {d R s : ℕ} {D f : (ι → Bool) → ℝ}
    (hf : f ∈ lowDegree ℝ ι d) (hD : IsLocalPseudoDist R D)
    (hs : 0 < s) (hdR : d * s ≤ R) :
    |pseudoExpect D f| ≤
      Real.sqrt ((1 - 1 / (s : ℝ)) * pseudoExpect D (fun x ↦ f x ^ 2) +
        (1 / (s : ℝ)) * fourierL1Norm f ^ 2) := by
  have h1 : (fun _ : ι → Bool ↦ (1 : ℝ)) ∈ lowDegree ℝ ι 0 := by
    rw [show (fun _ : ι → Bool ↦ (1 : ℝ)) = chi ℝ ∅ from funext fun x ↦ (chi_empty x).symm]
    exact chi_mem_lowDegree (F := ℝ) (∅ : Finset ι)
  have hcs := approx_cauchy_schwarz_asymmetric hf h1 hD hs Nat.zero_lt_one (by simpa using hdR)
  simpa [fourierL1Norm_const] using hcs
end ApproxCS

/-- Specialization of `approx_cauchy_schwarz` to $\mathrm{Fin}\,n \to \mathrm{Bool}$. -/
theorem approx_cauchy_schwarz_fin {n d R s t : ℕ} {D f g : (Fin n → Bool) → ℝ}
    (hf : f ∈ lowDegree ℝ (Fin n) d) (hg : g ∈ lowDegree ℝ (Fin n) d)
    (hD : IsLocalPseudoDist R D) (hs : 0 < s) (ht : 0 < t) (hR : d * (s + t) ≤ R) :
    |pseudoExpect D (fun x ↦ f x * g x)| ≤
      Real.sqrt ((1 - 1 / (s : ℝ)) * pseudoExpect D (fun x ↦ f x ^ 2) +
        (1 / (s : ℝ)) * fourierL1Norm f ^ 2) *
      Real.sqrt ((1 - 1 / (t : ℝ)) * pseudoExpect D (fun x ↦ g x ^ 2) +
        (1 / (t : ℝ)) * fourierL1Norm g ^ 2) :=
  approx_cauchy_schwarz hf hg hD hs ht hR

/-- Specialization of `abs_pseudoExpect_le_sqrt_approx_cs` to
$\mathrm{Fin}\,n \to \mathrm{Bool}$. -/
theorem abs_pseudoExpect_le_sqrt_approx_cs_fin {n d R s : ℕ} {D f : (Fin n → Bool) → ℝ}
    (hf : f ∈ lowDegree ℝ (Fin n) d) (hD : IsLocalPseudoDist R D)
    (hs : 0 < s) (hdR : d * s ≤ R) :
    |pseudoExpect D f| ≤
      Real.sqrt ((1 - 1 / (s : ℝ)) * pseudoExpect D (fun x ↦ f x ^ 2) +
        (1 / (s : ℝ)) * fourierL1Norm f ^ 2) :=
  abs_pseudoExpect_le_sqrt_approx_cs hf hD hs hdR

/-! ### Linear Sum Polynomial, Tightness Upper Bound, and Signed $2$-Local Witness -/

/-- Homogeneous linear polynomial $p(x) := \sum_{i = 0}^{n - 1} \mathrm{signVal}(x_i)$ on
$\mathrm{Fin}\,n \to \mathrm{Bool}$. -/
def linearSumPoly (n : ℕ) (x : Fin n → Bool) : ℝ := ∑ i : Fin n, signVal (x i)

lemma linearSumPoly_def (n : ℕ) (x : Fin n → Bool) :
    linearSumPoly n x = ∑ i : Fin n, signVal (x i) := by unfold linearSumPoly; rfl

lemma fourierCoeff_linearSumPoly (n : ℕ) (S : Finset (Fin n)) :
    fourierCoeff (linearSumPoly n) S = if S.card = 1 then 1 else 0 := by
  have hchar : linearSumPoly n = fun x ↦ ∑ i : Fin n, chi ℝ {i} x :=
    funext fun x ↦ Finset.sum_congr rfl fun i _ ↦ (chi_singleton i x).symm
  rw [hchar, fourierCoeff_finset_sum]; simp_rw [fourierCoeff_chi]
  split_ifs with h1
  · obtain ⟨i₀, rfl⟩ := Finset.card_eq_one.mp h1
    rw [Finset.sum_eq_single i₀ (fun j _ hj ↦ by simp [Finset.singleton_inj.not.mpr hj])
      (fun hnot ↦ absurd (Finset.mem_univ i₀) hnot)]; simp
  · exact Finset.sum_eq_zero fun i _ ↦ by
      simp [show ({i} : Finset (Fin n)) ≠ S from fun h ↦ h1 (h ▸ Finset.card_singleton i)]

/-- `linearSumPoly n` has Walsh–Fourier degree at most $1$. -/
theorem linearSumPoly_mem_lowDegree_one (n : ℕ) :
    linearSumPoly n ∈ lowDegree ℝ (Fin n) 1 := by
  rw [mem_lowDegree_iff_fourierCoeff_eq_zero]
  intro S hS
  simp [fourierCoeff_linearSumPoly, Nat.ne_of_gt hS]

/-- The Fourier $\ell_1$ norm of `linearSumPoly n` equals $n$. -/
@[simp] theorem fourierL1Norm_linearSumPoly (n : ℕ) :
    fourierL1Norm (linearSumPoly n) = (n : ℝ) := by
  rw [fourierL1Norm_def]
  simp_rw [fourierCoeff_linearSumPoly, show ∀ S : Finset (Fin n),
    |(if S.card = 1 then (1 : ℝ) else 0)| = if S.card = 1 then 1 else 0 from fun S ↦ by
      split_ifs <;> norm_num]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one,
    Finset.univ_filter_card_eq, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin,
    Nat.choose_one_right]

/-- Upper bound $|\tilde{\mathbb{E}}_D[p]| \le n / \sqrt{R - 1}$ for
$p(x) = \sum_i \mathrm{signVal}(x_i)$ under any $R$-local pseudo-distribution $D$ ($R \ge 2$)
satisfying $\tilde{\mathbb{E}}_D[p^2] = 0$, obtained by applying `approx_cauchy_schwarz` with
$f = p$, $g = 1$, $d = 1$, $s = R - 1$, $t = 1$. -/
theorem abs_pseudoExpect_linearSumPoly_le {n R : ℕ} {D : (Fin n → Bool) → ℝ}
    (hR : 2 ≤ R) (hD : IsLocalPseudoDist R D)
    (hsq : pseudoExpect D (fun x ↦ linearSumPoly n x ^ 2) = 0) :
    |pseudoExpect D (linearSumPoly n)| ≤ (n : ℝ) / Real.sqrt ((R : ℝ) - 1) := by
  have h1 : (fun _ : Fin n → Bool ↦ (1 : ℝ)) ∈ lowDegree ℝ (Fin n) 1 := by
    refine lowDegree_mono (Nat.zero_le 1) ?_
    rw [show (fun _ : Fin n → Bool ↦ (1 : ℝ)) = chi ℝ ∅ from funext fun x ↦ (chi_empty x).symm]
    exact chi_mem_lowDegree (F := ℝ) (∅ : Finset (Fin n))
  have hcs := approx_cauchy_schwarz (f := linearSumPoly n) (g := fun _ ↦ 1) (D := D)
    (d := 1) (s := R - 1) (t := 1) (linearSumPoly_mem_lowDegree_one n) h1 hD (by omega)
    Nat.zero_lt_one (by omega)
  simp only [mul_one, hsq, fourierL1Norm_linearSumPoly, fourierL1Norm_const, abs_one, one_pow,
    Nat.cast_one, div_one, sub_self, zero_mul, mul_zero, zero_add, Real.sqrt_one] at hcs
  rw [Nat.cast_sub (by omega : 1 ≤ R), Nat.cast_one, one_div_mul_eq_div,
    Real.sqrt_div (sq_nonneg (n : ℝ)), Real.sqrt_sq (Nat.cast_nonneg n)] at hcs
  exact hcs

private def threeVarMoments (S : Finset (Fin 3)) : ℝ :=
  match S.card with | 0 => 1 | 1 => 1 / 4 | 2 => -1 / 2 | _ => 0

/-- Explicit signed $2$-local Sherali–Adams pseudo-distribution on $\mathrm{Fin}\,3 \to
\mathrm{Bool}$ witnessing the hypotheses of `abs_pseudoExpect_linearSumPoly_le` and strict failure
of exact Cauchy–Schwarz: $\tilde{\mathbb{E}}_D[p^2] = 0$, $\tilde{\mathbb{E}}_D[p] = 3 / 4 > 0$,
and $D$ takes strictly negative values. -/
theorem exists_two_local_counterexample_fin_three :
    ∃ D : (Fin 3 → Bool) → ℝ, IsLocalPseudoDist 2 D ∧
      pseudoExpect D (fun x ↦ linearSumPoly 3 x ^ 2) = 0 ∧
      pseudoExpect D (linearSumPoly 3) = 3 / 4 ∧ ∃ x, D x < 0 := by
  let D : (Fin 3 → Bool) → ℝ := pseudoDistOfMoments threeVarMoments
  have hloc : IsLocalPseudoDist 2 D := by
    rw [isLocalPseudoDist_pseudoDistOfMoments_iff]; refine ⟨rfl, fun J _ y ↦ ?_⟩
    rw [marginalDist_pseudoDistOfMoments, pseudoDistOfMoments_def]
    refine div_nonneg ?_ (by positivity)
    simp_rw [show ∀ S : Finset J,
      threeVarMoments (S.map ⟨Subtype.val, Subtype.val_injective⟩) =
        match S.card with | 0 => 1 | 1 => 1 / 4 | 2 => -1 / 2 | _ => 0 from
      fun S ↦ by simp [threeVarMoments]]
    match hJcard : J.card with
    | 0 =>
      obtain rfl := Finset.card_eq_zero.mp hJcard
      have huniv : (Finset.univ : Finset (Finset (∅ : Finset (Fin 3)))) = {∅} := by
        ext S; simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
        exact Finset.eq_empty_of_isEmpty S
      rw [huniv]; norm_num
    | 1 =>
      obtain ⟨i₀, rfl⟩ := Finset.card_eq_one.mp hJcard
      let a₀ : ({i₀} : Finset (Fin 3)) := ⟨i₀, Finset.mem_singleton_self i₀⟩
      have huniv : (Finset.univ : Finset (Finset ({i₀} : Finset (Fin 3)))) = {∅, {a₀}} := by
        ext S; simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
        by_cases h : a₀ ∈ S
        · exact Or.inr (Finset.ext fun ⟨j, hj⟩ ↦ by cases Finset.mem_singleton.mp hj; simp [a₀, h])
        · exact Or.inl (Finset.eq_empty_of_forall_notMem fun ⟨j, hj⟩ hmem ↦ by
            cases Finset.mem_singleton.mp hj; exact h hmem)
      rw [huniv, Finset.sum_pair (by simp)]
      rcases signVal_eq_one_or_neg_one (y a₀) with h | h <;>
        norm_num [chi_empty, chi_singleton, h]
    | 2 =>
      let e : Fin 2 ≃ J := (Fintype.equivFinOfCardEq (by simpa using hJcard)).symm
      rw [← e.finsetCongr.sum_comp]
      have huniv2 : (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} := by decide
      rw [huniv2, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
        Finset.sum_insert (by decide), Finset.sum_singleton]
      simp only [Equiv.finsetCongr_apply, Finset.card_map, chi_eq_prod_signVal,
        Finset.prod_map, Equiv.coe_toEmbedding]
      rw [show ({0, 1} : Finset (Fin 2)).card = 2 by decide, Finset.prod_pair Fin.zero_ne_one]
      rcases signVal_eq_one_or_neg_one (y (e 0)) with h0 | h0 <;>
        rcases signVal_eq_one_or_neg_one (y (e 1)) with h1 | h1 <;> norm_num [h0, h1]
    | _ + 3 => omega
  have hp1 : pseudoExpect D (linearSumPoly 3) = 3 / 4 := by
    rw [show linearSumPoly 3 = fun x ↦ chi ℝ {0} x + chi ℝ {1} x + chi ℝ {2} x from
        funext fun x ↦ by rw [linearSumPoly_def, Fin.sum_univ_three]; simp [chi_singleton],
      pseudoExpect_add, pseudoExpect_add]
    simp only [D, pseudoExpect_pseudoDistOfMoments_chi]; norm_num [threeVarMoments]
  have hp2 : pseudoExpect D (fun x ↦ linearSumPoly 3 x ^ 2) = 0 := by
    have hsq_id : (fun x : Fin 3 → Bool ↦ linearSumPoly 3 x ^ 2) = fun x ↦
        (3 : ℝ) + 2 * chi ℝ {0, 1} x + 2 * chi ℝ {0, 2} x + 2 * chi ℝ {1, 2} x :=
      funext fun x ↦ by
        rw [linearSumPoly_def, Fin.sum_univ_three,
          show chi ℝ ({0, 1} : Finset (Fin 3)) x = signVal (x 0) * signVal (x 1) by
            rw [chi_eq_prod_signVal, Finset.prod_pair (by decide)],
          show chi ℝ ({0, 2} : Finset (Fin 3)) x = signVal (x 0) * signVal (x 2) by
            rw [chi_eq_prod_signVal, Finset.prod_pair (by decide)],
          show chi ℝ ({1, 2} : Finset (Fin 3)) x = signVal (x 1) * signVal (x 2) by
            rw [chi_eq_prod_signVal, Finset.prod_pair (by decide)]]
        rcases signVal_eq_one_or_neg_one (x 0) with b0 | b0 <;>
          rcases signVal_eq_one_or_neg_one (x 1) with b1 | b1 <;>
          rcases signVal_eq_one_or_neg_one (x 2) with b2 | b2 <;> rw [b0, b1, b2] <;> ring
    rw [hsq_id, pseudoExpect_add, pseudoExpect_add, pseudoExpect_add,
      pseudoExpect_smul, pseudoExpect_smul, pseudoExpect_smul, hloc.pseudoExpect_const]
    simp only [D, pseudoExpect_pseudoDistOfMoments_chi]
    dsimp only [threeVarMoments]
    rw [show ({0, 1} : Finset (Fin 3)).card = 2 by decide,
      show ({0, 2} : Finset (Fin 3)).card = 2 by decide,
      show ({1, 2} : Finset (Fin 3)).card = 2 by decide]
    norm_num
  have hneg : ∃ x, D x < 0 := by
    by_contra! hnonneg
    have hglob : IsLocalPseudoDist 3 D :=
      isLocalPseudoDist_of_nonneg_of_sum_eq_one 3 hnonneg hloc.sum_eq_one
    have hjunta : IsLocalJunta 3 (linearSumPoly 3) :=
      ⟨Finset.univ, by simp, fun _ _ hxy ↦ Finset.sum_congr rfl fun i _ ↦ by
        rw [hxy i (Finset.mem_univ i)]⟩
    have hcs := abs_pseudoExpect_mul_le_of_isLocalJunta hglob hjunta (isLocalJunta_const 0 1)
      (by omega)
    simp only [mul_one, hp1, hp2, Real.sqrt_zero, zero_mul] at hcs; norm_num at hcs
  exact ⟨D, hloc, hp2, hp1, hneg⟩

end CslibFrontier.Foundations.BooleanAnalysis
