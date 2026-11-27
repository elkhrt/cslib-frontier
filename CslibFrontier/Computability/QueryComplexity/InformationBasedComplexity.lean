/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Basic.ENNReal.Operations

/-!
# Information-Based Query Complexity: Adaptive vs. Non-Adaptive Linear Information

This module formalizes core query-complexity structures and lower bounds from Information-Based
Complexity:

* `CslibFrontier.Computability.QueryComplexity.worstCaseError`: worst-case norm error of an
  algorithm `A : E → G` approximating a solution map `S : E → G` on a problem class `F : Set E`.
* `CslibFrontier.Computability.QueryComplexity.zeroKernelRadius`: intrinsic antipodal error
  $\sup_{f \in F, \, N(f) = 0} \|S(f)\|$ of an information operator `N`.
* `CslibFrontier.Computability.QueryComplexity.nonadaptiveComplexity`: optimal worst-case error over
  all non-adaptive `n`-query linear information maps `N : E →ₗ[𝕜] (Fin n → 𝕜)` and arbitrary
  (possibly nonlinear) reconstruction maps `φ : (Fin n → 𝕜) → G` (the Gelfand $n$-width).
* `CslibFrontier.Computability.QueryComplexity.AdaptiveLinearQueryTree`: height-`n` adaptive
  decision tree querying linear functionals `E →ₗ[𝕜] 𝕜` where each query may depend arbitrarily on
  all previous oracle answers, together with `adaptiveComplexity`.
* `CslibFrontier.Computability.QueryComplexity.zeroKernelRadius_le_worstCaseError`: antipodal lower
  bound showing that no nonlinear reconstruction map can beat `zeroKernelRadius`.
* `CslibFrontier.Computability.QueryComplexity.bakhvalov_adaptive_lower_bound`: Bakhvalov's
  adversarial zero-path theorem showing that every height-`n` adaptive linear query tree has
  worst-case error at least the infimal non-adaptive `zeroKernelRadius` of rank `n`.
* `CslibFrontier.Computability.QueryComplexity.adaptiveComplexity_le_nonadaptiveComplexity` and
  `CslibFrontier.Computability.QueryComplexity.nonadaptiveComplexity_le_linearSamplingComplexity`:
  the fundamental complexity hierarchy between adaptive queries, non-adaptive Gelfand queries, and
  linear standard-information (point-evaluation) algorithms.
-/

public section

noncomputable section

open scoped ENNReal

namespace CslibFrontier.Computability.QueryComplexity

/-- Worst-case extended-real error $\sup_{f \in F} \|S(f) - A(f)\|$ of an approximation algorithm
`A : E → G` for a target operator `S : E → G` on a problem class `F : Set E`. -/
@[expose]
def worstCaseError {E G : Type*} [SeminormedAddCommGroup G]
    (F : Set E) (S A : E → G) : ℝ≥0∞ :=
  ⨆ f ∈ F, ‖S f - A f‖ₑ

/-- Intrinsic zero-kernel radius $\sup_{f \in F, \, N(f) = 0} \|S(f)\|$ of an information map
`N : E → Y`. -/
@[expose]
def zeroKernelRadius {E Y G : Type*} [Zero Y] [SeminormedAddCommGroup G]
    (F : Set E) (S : E → G) (N : E → Y) : ℝ≥0∞ :=
  ⨆ f ∈ {x ∈ F | N x = 0}, ‖S f‖ₑ

/-- Radius of information $\inf_{\varphi : Y \to G} \sup_{f \in F} \|S(f) - \varphi(N(f))\|$ over
all (possibly nonlinear) reconstruction maps `φ : Y → G`. -/
@[expose]
def radiusOfInformation {E Y G : Type*} [SeminormedAddCommGroup G]
    (F : Set E) (S : E → G) (N : E → Y) : ℝ≥0∞ :=
  ⨅ φ : Y → G, worstCaseError F S (φ ∘ N)

/-- Non-adaptive `n`-query linear information complexity (Gelfand $n$-width) over `𝕜`:
$\inf_{N : E \to_{\mathrm{lin}} \mathbb{K}^n} \inf_{\varphi : \mathbb{K}^n \to G}
\sup_{f \in F} \|S(f) - \varphi(N(f))\|$. -/
@[expose]
def nonadaptiveComplexity {𝕜 E G : Type*} [Semiring 𝕜] [AddCommMonoid E] [Module 𝕜 E]
    [SeminormedAddCommGroup G] (n : ℕ) (F : Set E) (S : E → G) : ℝ≥0∞ :=
  ⨅ N : E →ₗ[𝕜] (Fin n → 𝕜), radiusOfInformation F S N

/-- Linear standard-information (sampling) complexity using `n` functionals from an allowed
dictionary `Λ : D → (E →ₗ[𝕜] 𝕜)` (such as point evaluations `f ↦ f(x_i)`) and linear
reconstructions `f ↦ ∑ i, Λ (x i) f • g i`. -/
@[expose]
def linearSamplingComplexity {𝕜 D E G : Type*} [Semiring 𝕜] [AddCommMonoid E] [Module 𝕜 E]
    [SeminormedAddCommGroup G] [Module 𝕜 G]
    (n : ℕ) (Λ : D → (E →ₗ[𝕜] 𝕜)) (F : Set E) (S : E → G) : ℝ≥0∞ :=
  ⨅ (x : Fin n → D) (g : Fin n → G),
    worstCaseError F S (fun f ↦ ∑ i : Fin n, Λ (x i) f • g i)

/-- Height-`n` adaptive linear query tree over `(E, 𝕜)` with output in `G`: at each step the
algorithm queries a linear functional `l : E →ₗ[𝕜] 𝕜` and branches arbitrarily on its answer in `𝕜`
to choose subsequent linear functionals. -/
inductive AdaptiveLinearQueryTree (𝕜 E G : Type*) [Semiring 𝕜] [AddCommMonoid E] [Module 𝕜 E] :
    ℕ → Type _
  | leaf (out : G) : AdaptiveLinearQueryTree 𝕜 E G 0
  | query {n : ℕ} (l : E →ₗ[𝕜] 𝕜) (branch : 𝕜 → AdaptiveLinearQueryTree 𝕜 E G n) :
      AdaptiveLinearQueryTree 𝕜 E G (n + 1)

namespace AdaptiveLinearQueryTree

/-- Execute an adaptive linear query tree on an input `f : E`. -/
@[expose]
def eval {𝕜 E G : Type*} [Semiring 𝕜] [AddCommMonoid E] [Module 𝕜 E] :
    {n : ℕ} → AdaptiveLinearQueryTree 𝕜 E G n → E → G
  | 0, .leaf out, _ => out
  | _ + 1, .query l branch, f => eval (branch (l f)) f

/-- Extract the non-adaptive `n`-tuple of linear functionals queried along the all-zero oracle
transcript `0, 0, …, 0`. -/
@[expose]
def zeroPathInfo {𝕜 E G : Type*} [Semiring 𝕜] [AddCommMonoid E] [Module 𝕜 E] :
    {n : ℕ} → AdaptiveLinearQueryTree 𝕜 E G n → (E →ₗ[𝕜] (Fin n → 𝕜))
  | 0, .leaf _ => 0
  | _ + 1, .query l branch =>
    LinearMap.pi (Fin.cons l (fun i ↦ (LinearMap.proj i).comp (zeroPathInfo (branch 0))))

/-- Embed any non-adaptive `n`-query linear information map `N : E →ₗ[𝕜] (Fin n → 𝕜)` and
reconstruction map `φ : (Fin n → 𝕜) → G` as a height-`n` adaptive linear query tree. -/
@[expose]
def ofNonadaptive {𝕜 E G : Type*} [Semiring 𝕜] [AddCommMonoid E] [Module 𝕜 E] :
    (n : ℕ) → (E →ₗ[𝕜] (Fin n → 𝕜)) → ((Fin n → 𝕜) → G) → AdaptiveLinearQueryTree 𝕜 E G n
  | 0, _, φ => .leaf (φ Fin.elim0)
  | n + 1, N, φ =>
    .query ((LinearMap.proj (0 : Fin (n + 1))).comp N) fun y₀ ↦
      ofNonadaptive n
        (LinearMap.pi fun i : Fin n ↦ (LinearMap.proj i.succ).comp N)
        (fun ys ↦ φ (Fin.cons y₀ ys))

/-- Evaluating `ofNonadaptive n N φ` on `f` equals `φ (N f)`. -/
@[simp]
theorem eval_ofNonadaptive {𝕜 E G : Type*} [Semiring 𝕜] [AddCommMonoid E] [Module 𝕜 E]
    (n : ℕ) (N : E →ₗ[𝕜] (Fin n → 𝕜)) (φ : (Fin n → 𝕜) → G) (f : E) :
    (ofNonadaptive n N φ).eval f = φ (N f) := by
  induction n with
  | zero =>
    change φ Fin.elim0 = φ (N f)
    congr 1
    ext i
    exact i.elim0
  | succ n ih =>
    simp only [ofNonadaptive, eval, LinearMap.comp_apply, LinearMap.proj_apply]
    rw [ih]
    congr 1
    ext i
    cases i using Fin.cases with
    | zero => rfl
    | succ j => rfl

/-- If `zeroPathInfo T f = 0`, then `T.eval f` equals the all-zero leaf `T.eval 0`. -/
theorem eval_eq_eval_zero_of_zeroPathInfo_eq_zero {𝕜 E G : Type*} [Semiring 𝕜]
    [AddCommMonoid E] [Module 𝕜 E] {n : ℕ} (T : AdaptiveLinearQueryTree 𝕜 E G n)
    {f : E} (hf : T.zeroPathInfo f = 0) :
    T.eval f = T.eval 0 := by
  induction n with
  | zero =>
    cases T
    rfl
  | succ n ih =>
    rcases T with _ | ⟨l, branch⟩
    have h0 : l f = 0 := by
      have := congrFun hf 0
      simpa [zeroPathInfo] using this
    have htail : (branch 0).zeroPathInfo f = 0 := by
      ext i
      have := congrFun hf i.succ
      simpa [zeroPathInfo] using this
    simp only [eval, h0, map_zero]
    exact ih (branch 0) htail

end AdaptiveLinearQueryTree

/-- Adaptive `n`-query linear complexity: minimal worst-case error over all height-`n` adaptive
linear query trees. -/
@[expose]
def adaptiveComplexity {𝕜 E G : Type*} [Semiring 𝕜] [AddCommMonoid E] [Module 𝕜 E]
    [SeminormedAddCommGroup G] (n : ℕ) (F : Set E) (S : E → G) : ℝ≥0∞ :=
  ⨅ T : AdaptiveLinearQueryTree 𝕜 E G n, worstCaseError F S T.eval

/-- **Antipodal zero-kernel lower bound**: in a real-normed target space `G`, if `F` is centrally
symmetric (`f ∈ F → -f ∈ F`) and `S : E → G` is odd (`S (-f) = -S f`), then for every map
`N : E → Y` satisfying `N f = 0 → N (-f) = 0` and every reconstruction map `φ : Y → G`,
`zeroKernelRadius F S N ≤ worstCaseError F S (φ ∘ N)`. -/
theorem zeroKernelRadius_le_worstCaseError {E Y G : Type*} [AddGroup E] [Zero Y]
    [SeminormedAddCommGroup G] [NormedSpace ℝ G] {F : Set E}
    (hF_symm : ∀ {f : E}, f ∈ F → -f ∈ F) {S : E → G} (hS_odd : ∀ f : E, S (-f) = -S f)
    {N : E → Y} (hN_zero : ∀ {f : E}, N f = 0 → N (-f) = 0) (φ : Y → G) :
    zeroKernelRadius F S N ≤ worstCaseError F S (φ ∘ N) := by
  refine iSup₂_le fun f hf ↦ ?_
  rcases hf with ⟨hfF, hNf⟩
  have hnegF : -f ∈ F := hF_symm hfF
  have hNneg : N (-f) = 0 := hN_zero hNf
  have h1 : ‖S f - φ 0‖ₑ ≤ worstCaseError F S (φ ∘ N) := by
    have hmem : ‖S f - (φ ∘ N) f‖ₑ ≤ worstCaseError F S (φ ∘ N) :=
      le_biSup (fun x ↦ ‖S x - (φ ∘ N) x‖ₑ) hfF
    rwa [Function.comp_apply, hNf] at hmem
  have h2 : ‖φ 0 - S (-f)‖ₑ ≤ worstCaseError F S (φ ∘ N) := by
    rw [eNorm_sub_rev]
    have hmem : ‖S (-f) - (φ ∘ N) (-f)‖ₑ ≤ worstCaseError F S (φ ∘ N) :=
      le_biSup (fun x ↦ ‖S x - (φ ∘ N) x‖ₑ) hnegF
    rwa [Function.comp_apply, hNneg] at hmem
  have hsum_vec : (S f - φ 0) + (φ 0 - S (-f)) = (2 : ℝ) • S f := by
    rw [hS_odd f, sub_neg_eq_add, two_smul]
    abel
  have hnorm2 : 2 * ‖S f‖ₑ = ‖(2 : ℝ) • S f‖ₑ := by
    rw [eNorm_smul, Real.eNorm_of_nonneg zero_le_two, ENNReal.ofReal_ofNat]
  have htwo : 2 * ‖S f‖ₑ ≤ 2 * worstCaseError F S (φ ∘ N) := by
    calc
      2 * ‖S f‖ₑ = ‖(S f - φ 0) + (φ 0 - S (-f))‖ₑ := by rw [hsum_vec, hnorm2]
      _ ≤ ‖S f - φ 0‖ₑ + ‖φ 0 - S (-f)‖ₑ := eNorm_add_le _ _
      _ ≤ worstCaseError F S (φ ∘ N) + worstCaseError F S (φ ∘ N) := add_le_add h1 h2
      _ = 2 * worstCaseError F S (φ ∘ N) := (two_mul _).symm
  exact (ENNReal.mul_le_mul_iff_right (by norm_num) (by norm_num)).mp htwo

/-- Zero-kernel lower bound for `radiusOfInformation`:
`zeroKernelRadius F S N ≤ radiusOfInformation F S N`. -/
theorem zeroKernelRadius_le_radiusOfInformation {E Y G : Type*} [AddGroup E] [Zero Y]
    [SeminormedAddCommGroup G] [NormedSpace ℝ G] {F : Set E}
    (hF_symm : ∀ {f : E}, f ∈ F → -f ∈ F) {S : E → G} (hS_odd : ∀ f : E, S (-f) = -S f)
    {N : E → Y} (hN_zero : ∀ {f : E}, N f = 0 → N (-f) = 0) :
    zeroKernelRadius F S N ≤ radiusOfInformation F S N :=
  le_iInf fun φ ↦ zeroKernelRadius_le_worstCaseError hF_symm hS_odd (N := N) hN_zero φ

/-- **Bakhvalov's Adaptive Zero-Path Lower Bound**: for every centrally symmetric problem class
`F ⊆ E`, every odd solution map `S : E → G` into a real-normed space `G`, and every height-`n`
adaptive linear query tree `T`, the worst-case error of `T` is bounded below by the infimal
non-adaptive `n`-query `zeroKernelRadius`:
$$\inf_{N : E \to_{\mathrm{lin}} \mathbb{K}^n} \sup_{f \in F, \, N(f) = 0} \|S(f)\|
  \le \mathrm{adaptiveComplexity}_n(F, S).$$ -/
theorem bakhvalov_adaptive_lower_bound {𝕜 E G : Type*} [Ring 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [SeminormedAddCommGroup G] [NormedSpace ℝ G] (n : ℕ) {F : Set E}
    (hF_symm : ∀ {f : E}, f ∈ F → -f ∈ F) {S : E → G} (hS_odd : ∀ f : E, S (-f) = -S f) :
    (⨅ N : E →ₗ[𝕜] (Fin n → 𝕜), zeroKernelRadius F S N) ≤ adaptiveComplexity (𝕜 := 𝕜) n F S := by
  refine le_iInf fun T ↦ ?_
  refine (iInf_le (fun N : E →ₗ[𝕜] (Fin n → 𝕜) ↦ zeroKernelRadius F S N) T.zeroPathInfo).trans ?_
  refine iSup₂_le fun f hf ↦ ?_
  rcases hf with ⟨hfF, hNf⟩
  have hnegF : -f ∈ F := hF_symm hfF
  have hNneg : T.zeroPathInfo (-f) = 0 := by rw [map_neg, hNf, neg_zero]
  have hev_f : T.eval f = T.eval 0 := T.eval_eq_eval_zero_of_zeroPathInfo_eq_zero hNf
  have hev_neg : T.eval (-f) = T.eval 0 := T.eval_eq_eval_zero_of_zeroPathInfo_eq_zero hNneg
  have h1 : ‖S f - T.eval 0‖ₑ ≤ worstCaseError F S T.eval := by
    rw [← hev_f]
    exact le_biSup (fun x ↦ ‖S x - T.eval x‖ₑ) hfF
  have h2 : ‖T.eval 0 - S (-f)‖ₑ ≤ worstCaseError F S T.eval := by
    rw [eNorm_sub_rev, ← hev_neg]
    exact le_biSup (fun x ↦ ‖S x - T.eval x‖ₑ) hnegF
  have hsum_vec : (S f - T.eval 0) + (T.eval 0 - S (-f)) = (2 : ℝ) • S f := by
    rw [hS_odd f, sub_neg_eq_add, two_smul]
    abel
  have hnorm2 : 2 * ‖S f‖ₑ = ‖(2 : ℝ) • S f‖ₑ := by
    rw [eNorm_smul, Real.eNorm_of_nonneg zero_le_two, ENNReal.ofReal_ofNat]
  have htwo : 2 * ‖S f‖ₑ ≤ 2 * worstCaseError F S T.eval := by
    calc
      2 * ‖S f‖ₑ = ‖(S f - T.eval 0) + (T.eval 0 - S (-f))‖ₑ := by rw [hsum_vec, hnorm2]
      _ ≤ ‖S f - T.eval 0‖ₑ + ‖T.eval 0 - S (-f)‖ₑ := eNorm_add_le _ _
      _ ≤ worstCaseError F S T.eval + worstCaseError F S T.eval := add_le_add h1 h2
      _ = 2 * worstCaseError F S T.eval := (two_mul _).symm
  exact (ENNReal.mul_le_mul_iff_right (by norm_num) (by norm_num)).mp htwo

/-- **Adaptive ≤ Non-Adaptive Complexity**: every non-adaptive `n`-query algorithm embeds into a
height-`n` adaptive query tree. -/
theorem adaptiveComplexity_le_nonadaptiveComplexity {𝕜 E G : Type*} [Semiring 𝕜] [AddCommMonoid E]
    [Module 𝕜 E] [SeminormedAddCommGroup G] (n : ℕ) (F : Set E) (S : E → G) :
    adaptiveComplexity (𝕜 := 𝕜) n F S ≤ nonadaptiveComplexity (𝕜 := 𝕜) n F S := by
  refine le_iInf fun N ↦ le_iInf fun φ ↦ ?_
  have heq : (AdaptiveLinearQueryTree.ofNonadaptive n N φ).eval = φ ∘ N :=
    funext fun f ↦ AdaptiveLinearQueryTree.eval_ofNonadaptive n N φ f
  rw [← heq]
  exact iInf_le (fun T : AdaptiveLinearQueryTree 𝕜 E G n ↦ worstCaseError F S T.eval) _

/-- **Non-Adaptive ≤ Linear Standard-Information Complexity**: every linear sampling algorithm
using `n` functionals from `Λ : D → (E →ₗ[𝕜] 𝕜)` is a special case of non-adaptive `n`-query
linear information. -/
theorem nonadaptiveComplexity_le_linearSamplingComplexity {𝕜 D E G : Type*} [Semiring 𝕜]
    [AddCommMonoid E] [Module 𝕜 E] [SeminormedAddCommGroup G] [Module 𝕜 G]
    (n : ℕ) (Λ : D → (E →ₗ[𝕜] 𝕜)) (F : Set E) (S : E → G) :
    nonadaptiveComplexity (𝕜 := 𝕜) n F S ≤ linearSamplingComplexity n Λ F S := by
  refine le_iInf fun x ↦ le_iInf fun g ↦ ?_
  let N : E →ₗ[𝕜] (Fin n → 𝕜) := LinearMap.pi fun i ↦ Λ (x i)
  let φ : (Fin n → 𝕜) → G := fun y ↦ ∑ i : Fin n, y i • g i
  exact (iInf_le (fun M : E →ₗ[𝕜] (Fin n → 𝕜) ↦ radiusOfInformation F S M) N).trans
    (iInf_le (fun ψ : (Fin n → 𝕜) → G ↦ worstCaseError F S (ψ ∘ N)) φ)

end CslibFrontier.Computability.QueryComplexity
