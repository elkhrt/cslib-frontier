/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FormalPapers Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Halting.Computable
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Halting.Partrec
public import CslibFrontier.Computability.PCP.TwoProverGame.CommutingValue
public import CslibFrontier.Foundations.Quantum.Algebra.Measurement
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Computability.PartrecCode
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Logic.Equiv.Nat
import Mathlib.Topology.ContinuousMap.Weierstrass

/-!
# GNS Equivalence and Almost-Commuting Quantum Values of Two-Prover Games

This module develops general C*-algebraic and Hilbert-space strategy theory for two-prover nonlocal
games (`Cslib.PCP.TwoProverGame`) together with a bridge from multi-tape Turing machines to
recursive computability:

1. **Multi-tape Turing machine to Mathlib `Computable` bridge**: every total function between
   `Primcodable` types computed by a `Cslib` multi-tape Turing machine with computable input and
   output encodings is `Computable` in Mathlib's recursive-function sense.
2. **Ozawa's symmetric product and general C*-algebraic game strategies**: defines winning
   probabilities for non-commuting POVM strategies via Ozawa's symmetric product
   `a • b = (1/2) (√a b √a + √b a √b)`, agreeing with `a * b` whenever `a` and `b` commute.
3. **Separable GNS realization and Hilbert-space characterization of `commutingValue`**: proves
   that the abstract C*-algebraic commuting-operator value `G.commutingValue` equals the supremum
   over commuting POVM strategies with unit vector states on separable Hilbert spaces.
4. **Almost-commuting game values and Krylov-subspace compression**: introduces the operator-norm
   and state almost-commuting quantum values, proves their ordering hierarchy, and establishes
   unconditionally that `stateAlmostCommutingValue G δ = finDimStateAlmostCommutingValue G δ` for
   every `δ > 0` via finite-dimensional polynomial Krylov-subspace POVM compression.

## Main definitions

* `CslibFrontier.PCP.ozawaProd`: Ozawa's symmetric product `(1 / 2) • (√a * b * √a + √b * a * √b)`.
* `CslibFrontier.PCP.CStarStrategy`: general C*-algebraic POVM strategy with an algebraic state.
* `CslibFrontier.PCP.hilbertCommutingValue`: commuting-operator game value over unit vector states
  on separable Hilbert spaces.
* `CslibFrontier.PCP.opAlmostCommutingValue`, `CslibFrontier.PCP.finDimOpAlmostCommutingValue`:
  `δ`-operator-almost commuting quantum game values (general and finite-dimensional).
* `CslibFrontier.PCP.stateAlmostCommutingValue`,
  `CslibFrontier.PCP.finDimStateAlmostCommutingValue`: `δ`-state-almost commuting quantum game
  values (general and finite-dimensional).

## Main results

* `CslibFrontier.PCP.computable_of_multiTapeTM`: total multi-tape Turing machine computability
  implies Mathlib `Computable`.
* `CslibFrontier.PCP.exists_hilbert_strategy_of_cstar`: separable GNS realization of any finite-set
  C*-algebraic POVM strategy as a unit-vector strategy on a separable Hilbert space.
* `CslibFrontier.PCP.commutingValue_eq_hilbertCommutingValue`: equivalence between the abstract
  C*-algebraic `commutingValue` and the separable Hilbert-space commuting-operator value.
* `CslibFrontier.PCP.commutingValue_le_opAlmostCommutingValue`,
  `CslibFrontier.PCP.opAlmostCommutingValue_le_stateAlmostCommutingValue`: hierarchy of commuting
  and almost-commuting game values.
* `CslibFrontier.PCP.exists_finDim_stateAlmostCommuting_approx`,
  `CslibFrontier.PCP.stateAlmostCommutingValue_eq_finDimStateAlmostCommutingValue`:
  finite-dimensional Krylov-subspace compression of `δ`-state-almost commuting strategies and
  equality of general and finite-dimensional `δ`-state-almost commuting values.
-/

public section

open Filter Topology Cslib.Quantum Cslib.PCP
open scoped ComplexOrder CStarAlgebra ENNReal InnerProductSpace

namespace CslibFrontier.PCP

universe u v

/-! ### Multi-tape Turing machines to Mathlib `Computable` -/

/-- Any function `f : α → β` between `Primcodable` types computed by a total multi-tape Turing
machine with computable input and output encodings is `Computable`. -/
theorem computable_of_multiTapeTM {α β : Type} [Primcodable α] [Primcodable β]
    {f : α → β} {encIn : α ↪ List Bool} {encOut : β ↪ List Bool}
    (hf : Turing.MultiTapeTM.IsComputable f encIn encOut)
    (hIn : Computable encIn) (hOut : Computable encOut) : Computable f := by
  have hw : Computable fun a ↦ encOut (f a) := hf.computable_enc hIn
  let decB : ℕ → Option β := Encodable.decode
  have hdec : Primrec decB := Primrec.decode
  let step : α → ℕ → Option β := fun a m ↦
    match decB m with
    | some b => bif decide (encOut b = encOut (f a)) then some b else none
    | none => none
  have hstep : Computable₂ step := Computable₂.mk <|
    (Computable.option_casesOn (hdec.to_comp.comp Computable.snd)
      (Computable.const none)
      (Computable.cond
        (Primrec.eq.decide.to_comp.comp (hOut.comp Computable.snd)
          (hw.comp (Computable.fst.comp Computable.fst)))
        (Primrec.option_some.to_comp.comp Computable.snd)
        (Computable.const none)).to₂).of_eq fun p ↦ by
      rcases p with ⟨a, m⟩; dsimp only [step]
      cases decB m <;> rfl
  have hdom : ∀ a, (Nat.rfindOpt (step a)).Dom := fun a ↦ by
    have hm : (step a (Encodable.encode (f a))).isSome = true := by simp [step, decB]
    have hrf : (Nat.rfind fun n ↦ Part.some (step a n).isSome).Dom :=
      Nat.rfind_dom.mpr ⟨Encodable.encode (f a), Part.mem_some_iff.mpr hm.symm, fun _ ↦ trivial⟩
    have hs : (step a ((Nat.rfind fun n ↦ Part.some (step a n).isSome).get hrf)).isSome = true :=
      (Part.mem_some_iff.mp (Nat.rfind_spec (Part.get_mem hrf))).symm
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp hs
    have hb' : step a ((Nat.rfind fun n ↦ Part.ofOption (some (step a n).isSome)).get hrf) =
        some b := hb
    rw [Nat.rfindOpt, Part.bind_dom]
    exact ⟨hrf, by rw [hb']; trivial⟩
  refine (Partrec.rfindOpt hstep).of_eq fun a ↦ ?_
  have hmem := Part.get_mem (hdom a)
  obtain ⟨m, hm⟩ := Nat.rfindOpt_spec hmem
  have hm' : step a m = some ((Nat.rfindOpt (step a)).get (hdom a)) := Option.mem_def.mp hm
  have heq_f : (Nat.rfindOpt (step a)).get (hdom a) = f a := by
    dsimp only [step] at hm'
    cases hd : decB m with
    | none => simp [hd] at hm'
    | some b' =>
      rw [hd] at hm'
      by_cases heq : encOut b' = encOut (f a)
      · simp only [heq, decide_true, Bool.cond_true, Option.some.injEq] at hm'
        exact hm'.symm.trans (encOut.injective heq)
      · simp [heq] at hm'
  exact Part.eq_some_iff.mpr (heq_f ▸ hmem)

/-! ### Vector states, commutators, and Ozawa's symmetric product -/

private theorem star_conj_nonneg {C : Type u} [CStarAlgebra C] [PartialOrder C]
    [StarOrderedRing C] {x : C} (hx : 0 ≤ x) (y : C) : 0 ≤ star y * x * y := by
  have h : star y * x * y = star (CFC.sqrt x * y) * (CFC.sqrt x * y) := by
    calc star y * x * y
        = star y * (CFC.sqrt x * CFC.sqrt x) * y := by rw [CFC.sqrt_mul_sqrt_self x hx]
      _ = (star y * star (CFC.sqrt x)) * (CFC.sqrt x * y) := by
          rw [(CFC.sqrt_nonneg x).isSelfAdjoint.star_eq, mul_assoc, mul_assoc, mul_assoc]
      _ = star (CFC.sqrt x * y) * (CFC.sqrt x * y) := by rw [star_mul]
  rw [h]
  exact star_mul_self_nonneg _

private theorem real_smul_nonneg {C : Type u} [CStarAlgebra C] [PartialOrder C]
    [StarOrderedRing C] {c : ℝ} (hc : 0 ≤ c) {x : C} (hx : 0 ≤ x) :
    0 ≤ (c : ℂ) • x := by
  let y : C := (Real.sqrt c : ℂ) • CFC.sqrt x
  have h : (c : ℂ) • x = star y * y := by
    simp only [y, star_smul, Complex.star_def, Complex.conj_ofReal,
      (CFC.sqrt_nonneg x).isSelfAdjoint.star_eq, smul_mul_smul_comm,
      CFC.sqrt_mul_sqrt_self x hx, ← Complex.ofReal_mul, Real.mul_self_sqrt hc]
  rw [h]
  exact star_mul_self_nonneg y

private theorem norm_algState_apply_le {C : Type u} [CStarAlgebra C] [PartialOrder C]
    [StarOrderedRing C] (φ : AlgState C) (a : C) : ‖φ a‖ ≤ ‖a‖ := by
  rcases subsingleton_or_nontrivial C with _ | _
  · rw [Subsingleton.elim a 0, map_zero, norm_zero, norm_zero]
  have hcs : ‖φ a‖ ≤ φ.norm a := by
    simpa [star_one, one_mul, φ.norm_one] using φ.norm_apply_star_mul_le (1 : C) a
  have hle : star a * a ≤ ((‖star a * a‖ : ℝ) : ℂ) • (1 : C) := by
    have hsa : IsSelfAdjoint (star a * a) := IsSelfAdjoint.star_mul_self a
    have hdiff : ((‖star a * a‖ : ℝ) : ℂ) • (1 : C) - star a * a =
        cfc (fun t : ℝ ↦ ‖star a * a‖ - t) (star a * a) := by
      have hc : cfc (fun _ : ℝ ↦ ‖star a * a‖) (star a * a) =
          ((‖star a * a‖ : ℝ) : ℂ) • (1 : C) := by
        rw [cfc_const ‖star a * a‖ (star a * a), Algebra.algebraMap_eq_smul_one,
          ← Complex.coe_smul]
      rw [cfc_sub (f := fun _ : ℝ ↦ ‖star a * a‖) (g := fun t ↦ t) (a := star a * a)
        (hf := continuousOn_const) (hg := continuousOn_id), hc, cfc_id' ℝ (star a * a)]
    rw [← sub_nonneg, hdiff]
    exact cfc_nonneg fun t ht ↦ by linarith [(abs_le.mp (spectrum.norm_le_norm_of_mem ht)).2]
  have hre : (φ (star a * a)).re ≤ ‖a‖ ^ 2 := by
    have hre0 : 0 ≤ (φ (((‖star a * a‖ : ℝ) : ℂ) • (1 : C) - star a * a)).re :=
      φ.re_apply_nonneg (sub_nonneg.mpr hle)
    rw [map_sub, map_smul, φ.map_one, smul_eq_mul, mul_one, Complex.sub_re, Complex.ofReal_re,
      CStarRing.norm_star_mul_self, ← sq] at hre0
    linarith
  have hsq : ‖φ a‖ ^ 2 ≤ ‖a‖ ^ 2 :=
    ((sq_le_sq₀ (norm_nonneg _) (φ.norm_nonneg a)).mpr hcs).trans ((φ.norm_sq a).trans_le hre)
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

/-- Additive commutator `[a, b] = a * b - b * a`. -/
def commBracket {R : Type u} [Ring R] (a b : R) : R := a * b - b * a

/-- Vector state `T ↦ ⟪ξ, T ξ⟫_ℂ` on `H →L[ℂ] H` defined by a unit vector `ξ : H`. -/
def vectorAlgState {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (ξ : H) (hξ : ‖ξ‖ = 1) : AlgState (H →L[ℂ] H) where
  toFun T := ⟪ξ, T ξ⟫_ℂ
  map_add' _ _ := by simp [inner_add_right]
  map_smul' _ _ := by simp [inner_smul_right]
  map_one' := by simp [inner_self_eq_norm_sq_to_K, hξ]
  monotone' A B hAB := by
    have hpos := ContinuousLinearMap.nonneg_iff_isPositive.mp (sub_nonneg.mpr hAB)
    have hnn : (0 : ℂ) ≤ ⟪ξ, (B - A) ξ⟫_ℂ := by
      rw [Complex.nonneg_iff]
      have hsym : ⟪(B - A) ξ, ξ⟫_ℂ = ⟪ξ, (B - A) ξ⟫_ℂ := hpos.1 ξ ξ
      refine ⟨by rw [← hsym]; exact hpos.2 ξ, ?_⟩
      have hconj := (inner_conj_symm ((B - A) ξ) ξ).trans hsym
      have him := congrArg Complex.im hconj
      simp only [Complex.conj_im] at him
      linarith
    have heq : ⟪ξ, B ξ⟫_ℂ - ⟪ξ, A ξ⟫_ℂ = ⟪ξ, (B - A) ξ⟫_ℂ := by
      rw [sub_apply, inner_sub_right]
    exact sub_nonneg.mp (heq.symm ▸ hnn)

/-- Ozawa's symmetric product `a • b = (1/2) (√a b √a + √b a √b)` on a unital C*-algebra. -/
noncomputable def ozawaProd {C : Type u} [CStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
    (a b : C) : C :=
  ((1 / 2 : ℝ) : ℂ) • (CFC.sqrt a * b * CFC.sqrt a + CFC.sqrt b * a * CFC.sqrt b)

/-- `ozawaProd` is symmetric. -/
theorem ozawaProd_comm {C : Type u} [CStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
    (a b : C) : ozawaProd a b = ozawaProd b a := by
  simp only [ozawaProd, add_comm]

/-- `ozawaProd a b ≥ 0` whenever `a ≥ 0` and `b ≥ 0`. -/
theorem ozawaProd_nonneg {C : Type u} [CStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
    {a b : C} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ ozawaProd a b := by
  have h1 : 0 ≤ CFC.sqrt a * b * CFC.sqrt a := by
    have h := star_conj_nonneg hb (CFC.sqrt a)
    rwa [(CFC.sqrt_nonneg a).isSelfAdjoint.star_eq] at h
  have h2 : 0 ≤ CFC.sqrt b * a * CFC.sqrt b := by
    have h := star_conj_nonneg ha (CFC.sqrt b)
    rwa [(CFC.sqrt_nonneg b).isSelfAdjoint.star_eq] at h
  exact real_smul_nonneg (by positivity) (add_nonneg h1 h2)

/-- When `a ≥ 0`, `b ≥ 0`, and `Commute a b`, `ozawaProd a b = a * b`. -/
theorem ozawaProd_eq_mul_of_commute {C : Type u} [CStarAlgebra C] [PartialOrder C]
    [StarOrderedRing C] {a b : C} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : Commute a b) :
    ozawaProd a b = a * b := by
  have hca : Commute (CFC.sqrt a) b := by
    rw [CFC.sqrt_eq_cfc]; exact Commute.cfc_nnreal h NNReal.sqrt
  have hcb : Commute (CFC.sqrt b) a := by
    rw [CFC.sqrt_eq_cfc]; exact Commute.cfc_nnreal h.symm NNReal.sqrt
  have h1 : CFC.sqrt a * b * CFC.sqrt a = a * b := by
    rw [mul_assoc, hca.symm.eq, ← mul_assoc, CFC.sqrt_mul_sqrt_self a ha]
  have h2 : CFC.sqrt b * a * CFC.sqrt b = a * b := by
    rw [mul_assoc, hcb.symm.eq, ← mul_assoc, CFC.sqrt_mul_sqrt_self b hb, h.symm.eq]
  rw [ozawaProd, h1, h2]
  simp only [← two_smul ℂ (a * b), smul_smul]
  norm_num

/-- Unital `⋆`-homomorphisms preserve `ozawaProd` on nonnegative elements. -/
theorem map_ozawaProd {C : Type u} {D : Type v} [CStarAlgebra C] [PartialOrder C]
    [StarOrderedRing C] [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
    (π : C →⋆ₐ[ℂ] D) {a b : C} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    π (ozawaProd a b) = ozawaProd (π a) (π b) := by
  have hmap_nn : ∀ {x : C}, 0 ≤ x → 0 ≤ π x := fun hx ↦ by
    obtain ⟨y, hy⟩ := (_root_.CStarAlgebra.nonneg_iff_eq_star_mul_self).mp hx
    rw [hy, map_mul, map_star]
    exact star_mul_self_nonneg (π y)
  have hsq : ∀ {x : C}, 0 ≤ x → π (CFC.sqrt x) = CFC.sqrt (π x) := fun {x} hx ↦
    ((CFC.sqrt_eq_iff (π x) (π (CFC.sqrt x)) (hmap_nn hx) (hmap_nn (CFC.sqrt_nonneg x))).mpr
      (by rw [← map_mul, CFC.sqrt_mul_sqrt_self x hx])).symm
  simp only [ozawaProd, map_smul, map_add, map_mul, hsq ha, hsq hb]

/-- For POVMs `P` and `Q` in a unital C*-algebra, `∑_{a, b} ozawaProd (P a) (Q b) = 1`. -/
theorem sum_ozawaProd_measurement {A B : Type*} [Fintype A] [Fintype B]
    {C : Type u} [CStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
    (P : Measurement A C) (Q : Measurement B C) :
    ∑ a : A, ∑ b : B, ozawaProd (P.effect a) (Q.effect b) = 1 := by
  simp only [ozawaProd, ← Finset.smul_sum, Finset.sum_add_distrib]
  have h1 : (∑ a : A, ∑ b : B,
      CFC.sqrt (P.effect a) * Q.effect b * CFC.sqrt (P.effect a)) = 1 := by
    calc _ = ∑ a : A, CFC.sqrt (P.effect a) * (∑ b : B, Q.effect b) * CFC.sqrt (P.effect a) :=
          Finset.sum_congr rfl fun a _ ↦ by rw [Finset.mul_sum, Finset.sum_mul]
      _ = ∑ a : A, P.effect a := Finset.sum_congr rfl fun a _ ↦ by
          rw [Q.sum_effect, mul_one, CFC.sqrt_mul_sqrt_self _ (P.nonneg a)]
      _ = 1 := P.sum_effect
  have h2 : (∑ a : A, ∑ b : B,
      CFC.sqrt (Q.effect b) * P.effect a * CFC.sqrt (Q.effect b)) = 1 := by
    rw [Finset.sum_comm]
    calc _ = ∑ b : B, CFC.sqrt (Q.effect b) * (∑ a : A, P.effect a) * CFC.sqrt (Q.effect b) :=
          Finset.sum_congr rfl fun b _ ↦ by rw [Finset.mul_sum, Finset.sum_mul]
      _ = ∑ b : B, Q.effect b := Finset.sum_congr rfl fun b _ ↦ by
          rw [P.sum_effect, mul_one, CFC.sqrt_mul_sqrt_self _ (Q.nonneg b)]
      _ = 1 := Q.sum_effect
  rw [h1, h2, ← two_smul ℂ (1 : C), smul_smul]
  norm_num

/-! ### Separable GNS helpers -/

private theorem separableSpace_adjoin_finite {C : Type u} [CStarAlgebra C]
    {S : Set C} (hS : S.Finite) :
    TopologicalSpace.SeparableSpace ((StarAlgebra.adjoin ℂ S).topologicalClosure) := by
  classical
  obtain ⟨F, hSF⟩ := hS.exists_finset_coe
  let D := (StarAlgebra.adjoin ℂ S).topologicalClosure
  let qToC : ℚ × ℚ → ℂ := fun q ↦ (q.1 : ℂ) + (q.2 : ℂ) * Complex.I
  have hq_approx : ∀ (z : ℂ) {δ : ℝ}, 0 < δ → ∃ q : ℚ × ℚ, ‖z - qToC q‖ < δ := fun z {δ} hδ ↦ by
    obtain ⟨_, ⟨q₁, rfl⟩, hq₁⟩ :=
      Metric.mem_closure_iff.mp (Rat.denseRange_cast z.re) (δ / 2) (half_pos hδ)
    obtain ⟨_, ⟨q₂, rfl⟩, hq₂⟩ :=
      Metric.mem_closure_iff.mp (Rat.denseRange_cast z.im) (δ / 2) (half_pos hδ)
    refine ⟨(q₁, q₂), ?_⟩
    have hz : z - qToC (q₁, q₂) = ((z.re - q₁ : ℝ) : ℂ) + ((z.im - q₂ : ℝ) : ℂ) * Complex.I := by
      apply Complex.ext <;> simp [qToC]
    rw [hz]
    calc ‖((z.re - q₁ : ℝ) : ℂ) + ((z.im - q₂ : ℝ) : ℂ) * Complex.I‖
        ≤ |z.re - q₁| + |z.im - q₂| := by
          refine (norm_add_le _ _).trans ?_
          simp only [norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs, le_rfl]
      _ < δ / 2 + δ / 2 := add_lt_add (by simpa [Real.dist_eq] using hq₁)
          (by simpa [Real.dist_eq] using hq₂)
      _ = δ := add_halves δ
  let atoms : List C := F.toList ++ F.toList.map star
  let evalPoly : List ((ℚ × ℚ) × List (Fin atoms.length)) → C := fun L ↦
    (L.map fun t ↦ qToC t.1 • (t.2.map atoms.get).prod).sum
  have hmem_D : ∀ L, evalPoly L ∈ D := fun L ↦ by
    refine StarSubalgebra.le_topologicalClosure _ (Subalgebra.list_sum_mem _ ?_)
    intro c hc
    obtain ⟨⟨_, w⟩, _, rfl⟩ := List.mem_map.mp hc
    refine Subalgebra.smul_mem _ (Subalgebra.list_prod_mem _ fun a ha ↦ ?_) _
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp ha
    have hmem : atoms.get i ∈ atoms := List.get_mem atoms i
    simp only [atoms, List.mem_append, List.mem_map, Finset.mem_toList] at hmem
    rcases hmem with h1 | ⟨y, hy, hyeq⟩
    · exact StarAlgebra.subset_adjoin ℂ S (hSF ▸ (h1 : _ ∈ (F : Set C)))
    · rw [← hyeq]
      exact (star_mem (StarAlgebra.subset_adjoin ℂ S (hSF ▸ (hy : y ∈ (F : Set C)))) :
        star y ∈ StarAlgebra.adjoin ℂ S)
  refine ⟨⟨Set.range fun L ↦ (⟨evalPoly L, hmem_D L⟩ : D), Set.countable_range _, ?_⟩⟩
  rintro ⟨x, hx⟩
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.mp hx (ε / 2) (half_pos hε)
  have hmul : ∀ L₁ L₂, ∃ L₃, evalPoly L₃ = evalPoly L₁ * evalPoly L₂ := by
    let qMul : ℚ × ℚ → ℚ × ℚ → ℚ × ℚ := fun a b ↦ (a.1 * b.1 - a.2 * b.2, a.1 * b.2 + a.2 * b.1)
    have hqMul : ∀ a b, qToC (qMul a b) = qToC a * qToC b := fun a b ↦ by
      simp only [qToC, qMul, Rat.cast_sub, Rat.cast_add, Rat.cast_mul]
      linear_combination (a.2 : ℂ) * (b.2 : ℂ) * (-Complex.I_sq)
    intro L₁ L₂
    induction L₁ with
    | nil => exact ⟨[], by simp [evalPoly]⟩
    | cons t₁ tl₁ ih =>
      obtain ⟨Ltl, hLtl⟩ := ih
      have hLhd : ∀ M : List ((ℚ × ℚ) × List (Fin atoms.length)),
          evalPoly (M.map fun t₂ ↦ (qMul t₁.1 t₂.1, t₁.2 ++ t₂.2)) =
            (qToC t₁.1 • (t₁.2.map atoms.get).prod) * evalPoly M := fun M ↦ by
        induction M with
        | nil => simp [evalPoly]
        | cons t₂ tl₂ ih₂ =>
          change qToC (qMul t₁.1 t₂.1) • ((t₁.2 ++ t₂.2).map atoms.get).prod +
              evalPoly (tl₂.map fun s ↦ (qMul t₁.1 s.1, t₁.2 ++ s.2)) =
            (qToC t₁.1 • (t₁.2.map atoms.get).prod) *
              (qToC t₂.1 • (t₂.2.map atoms.get).prod + evalPoly tl₂)
          rw [mul_add, hqMul, List.map_append, List.prod_append, smul_mul_smul_comm, ih₂]
      exact ⟨(L₂.map fun t₂ ↦ (qMul t₁.1 t₂.1, t₁.2 ++ t₂.2)) ++ Ltl, by
        simp only [evalPoly, List.map_append, List.sum_append, List.map_cons, List.sum_cons,
          add_mul]
        exact congrArg₂ (· + ·) (hLhd L₂) hLtl⟩
  have hcl : y ∈ closure (Set.range evalPoly) :=
    StarAlgebra.adjoin_induction (p := fun z _ ↦ z ∈ closure (Set.range evalPoly))
      (fun a ha ↦ by
        have haF : a ∈ F := by rw [← hSF] at ha; exact ha
        obtain ⟨i, hi⟩ := List.mem_iff_get.mp (List.mem_append_left _ (Finset.mem_toList.mpr haF))
        refine subset_closure ⟨[((1, 0), [i])], ?_⟩
        change qToC (1, 0) • (atoms.get i * 1) + 0 = a
        rw [hi]; simp [qToC])
      (fun z ↦ Metric.mem_closure_iff.mpr fun δ hδ ↦ by
        obtain ⟨q, hq⟩ := hq_approx z (by positivity : 0 < δ / (‖(1 : C)‖ + 1))
        refine ⟨evalPoly [(q, [])], ⟨[(q, [])], rfl⟩, ?_⟩
        rw [dist_eq_norm]
        simp only [evalPoly, List.map_cons, List.map_nil, List.prod_nil, List.sum_cons,
          List.sum_nil, add_zero, Algebra.algebraMap_eq_smul_one, ← sub_smul, norm_smul]
        calc ‖z - qToC q‖ * ‖(1 : C)‖
            ≤ ‖z - qToC q‖ * (‖(1 : C)‖ + 1) :=
              mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)
          _ < (δ / (‖(1 : C)‖ + 1)) * (‖(1 : C)‖ + 1) :=
              mul_lt_mul_of_pos_right hq (by positivity)
          _ = δ := by field_simp)
      (fun u w _ _ hu hw ↦ Metric.mem_closure_iff.mpr fun δ hδ ↦ by
        obtain ⟨_, ⟨L₁, rfl⟩, h₁⟩ := Metric.mem_closure_iff.mp hu (δ / 2) (half_pos hδ)
        obtain ⟨_, ⟨L₂, rfl⟩, h₂⟩ := Metric.mem_closure_iff.mp hw (δ / 2) (half_pos hδ)
        refine ⟨evalPoly (L₁ ++ L₂), ⟨L₁ ++ L₂, rfl⟩, ?_⟩
        rw [dist_eq_norm, show evalPoly (L₁ ++ L₂) = evalPoly L₁ + evalPoly L₂ by simp [evalPoly],
          show (u + w) - (evalPoly L₁ + evalPoly L₂) = (u - evalPoly L₁) + (w - evalPoly L₂) by
            abel]
        exact (norm_add_le _ _).trans_lt ((add_lt_add (by simpa [dist_eq_norm] using h₁)
          (by simpa [dist_eq_norm] using h₂)).trans_eq (add_halves δ)))
      (fun u w _ _ hu hw ↦ Metric.mem_closure_iff.mpr fun δ hδ ↦ by
        obtain ⟨_, ⟨L₁, rfl⟩, h₁⟩ := Metric.mem_closure_iff.mp hu
          (min 1 (δ / (2 * (‖w‖ + 1)))) (lt_min zero_lt_one (by positivity))
        obtain ⟨_, ⟨L₂, rfl⟩, h₂⟩ := Metric.mem_closure_iff.mp hw
          (δ / (2 * (‖u‖ + 2))) (by positivity)
        obtain ⟨L₃, hL₃⟩ := hmul L₁ L₂
        have hL₁_norm : ‖evalPoly L₁‖ ≤ ‖u‖ + 1 := by
          have h1 : ‖u - evalPoly L₁‖ < 1 :=
            (by simpa [dist_eq_norm] using h₁ : ‖u - evalPoly L₁‖ < _).trans_le (min_le_left _ _)
          calc ‖evalPoly L₁‖ = ‖u - (u - evalPoly L₁)‖ := by abel_nf
            _ ≤ ‖u‖ + ‖u - evalPoly L₁‖ := norm_sub_le _ _
            _ ≤ ‖u‖ + 1 := by linarith
        refine ⟨evalPoly L₃, ⟨L₃, rfl⟩, ?_⟩
        rw [dist_eq_norm, hL₃, show u * w - evalPoly L₁ * evalPoly L₂ =
          (u - evalPoly L₁) * w + evalPoly L₁ * (w - evalPoly L₂) by noncomm_ring]
        have h₁' : ‖u - evalPoly L₁‖ < δ / (2 * (‖w‖ + 1)) :=
          (by simpa [dist_eq_norm] using h₁ : ‖u - evalPoly L₁‖ < _).trans_le (min_le_right _ _)
        have h₂' : ‖w - evalPoly L₂‖ < δ / (2 * (‖u‖ + 2)) := by simpa [dist_eq_norm] using h₂
        calc ‖(u - evalPoly L₁) * w + evalPoly L₁ * (w - evalPoly L₂)‖
            ≤ ‖u - evalPoly L₁‖ * (‖w‖ + 1) + (‖u‖ + 2) * ‖w - evalPoly L₂‖ :=
              ((norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))).trans <|
                add_le_add (mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _))
                  (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))
          _ < (δ / (2 * (‖w‖ + 1))) * (‖w‖ + 1) + (‖u‖ + 2) * (δ / (2 * (‖u‖ + 2))) :=
              add_lt_add (mul_lt_mul_of_pos_right h₁' (by positivity))
                (mul_lt_mul_of_pos_left h₂' (by positivity))
          _ = δ := by field_simp; ring)
      (fun u _ hu ↦ Metric.mem_closure_iff.mpr fun δ hδ ↦ by
        have hex_flip : ∀ i : Fin atoms.length,
            ∃ j : Fin atoms.length, atoms.get j = star (atoms.get i) := fun i ↦ by
          have hi : atoms.get i ∈ atoms := List.get_mem atoms i
          simp only [atoms, List.mem_append, List.mem_map, Finset.mem_toList] at hi
          rcases hi with h1 | ⟨z, hz, hza⟩
          · exact List.mem_iff_get.mp (List.mem_append_right _
              (List.mem_map.mpr ⟨_, Finset.mem_toList.mpr h1, rfl⟩))
          · exact List.mem_iff_get.mp (List.mem_append_left _
              (by rw [← hza, star_star]; exact Finset.mem_toList.mpr hz))
        choose flipIdx hflipIdx using hex_flip
        obtain ⟨_, ⟨L, rfl⟩, hL⟩ := Metric.mem_closure_iff.mp hu δ hδ
        have hqstar : ∀ q : ℚ × ℚ, qToC (q.1, -q.2) = star (qToC q) := fun q ↦ by
          apply Complex.ext <;> simp [qToC]
        have hwstar : ∀ w : List (Fin atoms.length),
            ((w.reverse.map flipIdx).map atoms.get).prod = star (w.map atoms.get).prod := fun w ↦ by
          induction w with
          | nil => simp
          | cons i tl ih =>
            simp only [List.reverse_cons, List.map_append, List.prod_append, List.map_cons,
              List.map_nil, List.prod_cons, List.prod_nil, mul_one, star_mul, ih, hflipIdx]
        have haux : ∀ M : List ((ℚ × ℚ) × List (Fin atoms.length)),
            evalPoly (M.map fun t ↦ ((t.1.1, -t.1.2), t.2.reverse.map flipIdx)) =
              star (evalPoly M) := fun M ↦ by
          induction M with
          | nil => simp [evalPoly]
          | cons hd tl ih =>
            change qToC (hd.1.1, -hd.1.2) • ((hd.2.reverse.map flipIdx).map atoms.get).prod +
                evalPoly (tl.map fun t ↦ ((t.1.1, -t.1.2), t.2.reverse.map flipIdx)) =
              star (qToC hd.1 • (hd.2.map atoms.get).prod + evalPoly tl)
            rw [star_add, star_smul, hqstar, hwstar, ih]
        refine ⟨_, ⟨L.map fun t ↦ ((t.1.1, -t.1.2), t.2.reverse.map flipIdx), rfl⟩, ?_⟩
        rw [dist_eq_norm, haux L, ← star_sub, norm_star]
        simpa [dist_eq_norm] using hL)
      hy
  obtain ⟨_, ⟨L, rfl⟩, hyL⟩ := Metric.mem_closure_iff.mp hcl (ε / 2) (half_pos hε)
  refine ⟨⟨evalPoly L, hmem_D L⟩, ⟨L, rfl⟩, ?_⟩
  change dist x (evalPoly L) < ε
  exact (dist_triangle x y (evalPoly L)).trans_lt (by linarith)

private theorem exists_type0_hilbert_iso (K : Type u) [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] [TopologicalSpace.SeparableSpace K] :
    ∃ (H₀ : Type) (_ : NormedAddCommGroup H₀) (_ : InnerProductSpace ℂ H₀) (_ : CompleteSpace H₀)
      (_ : TopologicalSpace.SeparableSpace H₀), Nonempty (K ≃ₗᵢ[ℂ] H₀) := by
  obtain ⟨s, b, _⟩ := exists_hilbertBasis ℂ K
  have hb_orth : Orthonormal ℂ (b : s → K) := b.orthonormal
  have hcnt : Countable s := by
    obtain ⟨D₀, hD₀_cnt, hD₀_dense⟩ := TopologicalSpace.exists_countable_dense K
    have hex_pick : ∀ i : s, ∃ d : D₀, dist (b i) d.1 < 1 / 2 := fun i ↦ by
      obtain ⟨d, hd, hdist⟩ := Metric.mem_closure_iff.mp (hD₀_dense (b i)) (1 / 2) (by norm_num)
      exact ⟨⟨d, hd⟩, hdist⟩
    choose pick hpick using hex_pick
    have hinj : Function.Injective pick := fun i j hij ↦ by
      by_contra hne
      have hd2 : dist (b i) (b j) < 1 :=
        calc dist (b i) (b j) ≤ dist (b i) (pick i).1 + dist (pick j).1 (b j) := by
              rw [hij]; exact dist_triangle (b i) (pick j).1 (b j)
          _ < 1 / 2 + 1 / 2 := add_lt_add (hpick i) (by rw [dist_comm]; exact hpick j)
          _ = 1 := add_halves 1
      have hin : ⟪b i - b j, b i - b j⟫_ℂ = 2 := by
        have h3 : ⟪b i, b j⟫_ℂ = 0 := hb_orth.2 hne
        rw [inner_sub_left, inner_sub_right, inner_sub_right, h3,
          show ⟪b j, b i⟫_ℂ = 0 by rw [← inner_conj_symm, h3, map_zero],
          inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, hb_orth.1 i, hb_orth.1 j]
        norm_num
      rw [inner_self_eq_norm_sq_to_K] at hin
      have hsq : ‖b i - b j‖ ^ 2 = 2 := Complex.ofReal_injective (by simpa using hin)
      rw [dist_eq_norm] at hd2
      nlinarith [norm_nonneg (b i - b j)]
    have : Countable D₀ := hD₀_cnt.to_subtype
    exact hinj.countable
  by_cases hfin : Finite s
  · cases nonempty_fintype s
    let d := Fintype.card s
    let es : s ≃ Fin d := Fintype.equivFin s
    let e : lp (fun _ : s ↦ ℂ) 2 ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin d) :=
      { toFun := fun f ↦ WithLp.toLp 2 fun i ↦ f (es.symm i)
        invFun := fun v ↦ ⟨fun j ↦ v.ofLp (es j), Memℓp.all _⟩
        left_inv := fun f ↦ lp.ext (funext fun j ↦ by simp)
        right_inv := fun v ↦ PiLp.ext fun i ↦ by simp
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun _ _ ↦ rfl
        norm_map' := fun f ↦ by
          have h1 : ‖f‖ ^ 2 = ∑ j : s, ‖f j‖ ^ 2 := by
            simpa only [ENNReal.toReal_ofNat, Real.rpow_two, tsum_fintype] using
              lp.norm_rpow_eq_tsum (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal) f
          have h2 : ‖(WithLp.toLp 2 fun i ↦ f (es.symm i) : EuclideanSpace ℂ (Fin d))‖ ^ 2 =
              ∑ j : s, ‖f j‖ ^ 2 :=
            (EuclideanSpace.norm_sq_eq _).trans (Equiv.sum_comp es.symm fun j ↦ ‖f j‖ ^ 2)
          exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (h2.trans h1.symm) }
    let he := b.repr.trans e
    obtain ⟨cnt, hcnt, hd⟩ := TopologicalSpace.exists_countable_dense K
    exact ⟨EuclideanSpace ℂ (Fin d), inferInstance, inferInstance, inferInstance,
      ⟨⟨he '' cnt, hcnt.image he, he.surjective.denseRange.dense_image he.continuous hd⟩⟩, ⟨he⟩⟩
  · have : Infinite s := not_finite_iff_infinite.mp hfin
    obtain ⟨es⟩ := nonempty_equiv_of_countable (α := s) (β := ℕ)
    let L2 := lp (fun _ : ℕ ↦ ℂ) 2
    let e : lp (fun _ : s ↦ ℂ) 2 ≃ₗᵢ[ℂ] L2 :=
      { toFun := fun f ↦ ⟨fun n ↦ f (es.symm n),
          memℓp_gen (by
            simpa [Function.comp_def] using es.symm.summable_iff.mpr
              ((lp.memℓp f).summable (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal)))⟩
        invFun := fun g ↦ ⟨fun j ↦ g (es j),
          memℓp_gen (by
            simpa [Function.comp_def] using es.summable_iff.mpr
              ((lp.memℓp g).summable (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal)))⟩
        left_inv := fun f ↦ lp.ext (funext fun j ↦ by simp)
        right_inv := fun g ↦ lp.ext (funext fun n ↦ by simp)
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun _ _ ↦ rfl
        norm_map' := fun f ↦ by
          set g : L2 := ⟨fun n ↦ f (es.symm n), _⟩
          have h1 : ‖f‖ ^ 2 = ∑' j : s, ‖f j‖ ^ 2 := by
            simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
              lp.norm_rpow_eq_tsum (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal) f
          have hg : ‖g‖ ^ 2 = ∑' n : ℕ, ‖f (es.symm n)‖ ^ 2 := by
            simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
              lp.norm_rpow_eq_tsum (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal) g
          exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
            ((hg.trans (Equiv.tsum_eq es.symm fun j ↦ ‖f j‖ ^ 2)).trans h1.symm) }
    let he := b.repr.trans e
    obtain ⟨cnt, hcnt, hd⟩ := TopologicalSpace.exists_countable_dense K
    exact ⟨L2, inferInstance, inferInstance, inferInstance,
      ⟨⟨he '' cnt, hcnt.image he, he.surjective.denseRange.dense_image he.continuous hd⟩⟩, ⟨he⟩⟩

private def conjCLM {K : Type u} {H₀ : Type v} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] [NormedAddCommGroup H₀] [InnerProductSpace ℂ H₀] [CompleteSpace H₀]
    (e : K ≃ₗᵢ[ℂ] H₀) : (K →L[ℂ] K) →⋆ₐ[ℂ] (H₀ →L[ℂ] H₀) where
  toFun T := e.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (T.comp e.symm.toContinuousLinearEquiv.toContinuousLinearMap)
  map_one' := by ext x; simp
  map_mul' _ _ := by ext x; simp
  map_zero' := by ext x; simp
  map_add' _ _ := by ext x; simp
  commutes' z := by ext x; simp [Algebra.algebraMap_eq_smul_one]
  map_star' T := by
    let T' : H₀ →L[ℂ] H₀ := e.toContinuousLinearEquiv.toContinuousLinearMap.comp
      (T.comp e.symm.toContinuousLinearEquiv.toContinuousLinearMap)
    refine ContinuousLinearMap.ext fun y ↦ ext_inner_left ℂ fun x ↦ ?_
    change ⟪x, e ((star T) (e.symm y))⟫_ℂ = ⟪x, (star T') y⟫_ℂ
    calc ⟪x, e ((star T) (e.symm y))⟫_ℂ
        = ⟪e.symm x, (star T) (e.symm y)⟫_ℂ := by
            conv_lhs => rw [← e.apply_symm_apply x]
            exact e.inner_map_map _ _
      _ = ⟪T (e.symm x), e.symm y⟫_ℂ := by
            rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
      _ = ⟪T' x, y⟫_ℂ := by rw [← e.inner_map_map, e.apply_symm_apply]; rfl
      _ = ⟪x, (star T') y⟫_ℂ := by
            rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]

/-! ### General strategies, GNS equivalence, and almost-commuting game values -/

section GameValues

variable {X Y A B : Type} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/-- Push a `Measurement` forward along a unital `⋆`-homomorphism `π : C →⋆ₐ[ℂ] D`. -/
def mapMeasurement {I : Type*} [Fintype I] {C : Type u} {D : Type v}
    [CStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
    [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
    (π : C →⋆ₐ[ℂ] D) (M : Measurement I C) : Measurement I D where
  effect i := π (M.effect i)
  nonneg i := by
    obtain ⟨z, hz⟩ := (_root_.CStarAlgebra.nonneg_iff_eq_star_mul_self).mp (M.nonneg i)
    rw [hz, map_mul, map_star]
    exact star_mul_self_nonneg (π z)
  sum_effect := by rw [← map_sum, M.sum_effect, map_one]

/-- A general (not necessarily commuting) C*-algebraic strategy for a two-prover game. -/
structure CStarStrategy (X Y A B : Type) [Fintype A] [Fintype B]
    (C : Type u) [CStarAlgebra C] [PartialOrder C] [StarOrderedRing C] where
  /-- Alice's POVMs indexed by questions `x : X`. -/
  alice : X → Measurement A C
  /-- Bob's POVMs indexed by questions `y : Y`. -/
  bob : Y → Measurement B C
  /-- Shared algebraic state `φ : AlgState C`. -/
  state : AlgState C

/-- Convert a `CommutingStrategy` into a `CStarStrategy`. -/
def CStarStrategy.ofCommuting {C : Type u} [CStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
    (S : CommutingStrategy X Y A B C) : CStarStrategy X Y A B C where
  alice := S.alice
  bob := S.bob
  state := S.state

/-- Exact commutativity `[A^x_a, B^y_b] = 0` for all `x, y, a, b`. -/
def CStarStrategy.IsCommuting {C : Type u} [CStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
    (σ : CStarStrategy X Y A B C) : Prop :=
  ∀ x y a b, Commute ((σ.alice x).effect a) ((σ.bob y).effect b)

/-- `δ`-operator-norm-almost commutativity: `∑_{a, b} ‖[A^x_a, B^y_b]‖ < δ` for all `x, y`. -/
def CStarStrategy.IsOpAlmostCommuting {C : Type u} [CStarAlgebra C] [PartialOrder C]
    [StarOrderedRing C] (σ : CStarStrategy X Y A B C) (δ : ℝ) : Prop :=
  ∀ x y, ∑ a : A, ∑ b : B, ‖commBracket ((σ.alice x).effect a) ((σ.bob y).effect b)‖ < δ

/-- `δ`-state-almost commutativity: `∑_{a, b} ‖φ([A^x_a, B^y_b])‖ < δ` for all `x, y`. -/
def CStarStrategy.IsStateAlmostCommuting {C : Type u} [CStarAlgebra C] [PartialOrder C]
    [StarOrderedRing C] (σ : CStarStrategy X Y A B C) (δ : ℝ) : Prop :=
  ∀ x y, ∑ a : A, ∑ b : B,
    ‖σ.state (commBracket ((σ.alice x).effect a) ((σ.bob y).effect b))‖ < δ

/-- Convert a commuting `CStarStrategy` into a `Cslib.PCP.CommutingStrategy`. -/
def CStarStrategy.toCommuting {C : Type u} [CStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
    (σ : CStarStrategy X Y A B C) (h : σ.IsCommuting) : CommutingStrategy X Y A B C where
  alice := σ.alice
  bob := σ.bob
  state := σ.state
  commute := h

/-- Winning probability of a general `CStarStrategy` via Ozawa's symmetric product. -/
noncomputable def CStarStrategy.winProb (G : TwoProverGame X Y A B)
    {C : Type u} [CStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
    (σ : CStarStrategy X Y A B C) : ℝ := by
  classical
  exact ∑ x : X, ∑ y : Y, (G.questions (x, y)).toReal *
    ∑ a : A, ∑ b : B,
      if G.accepts x y a b then
        (σ.state (ozawaProd ((σ.alice x).effect a) ((σ.bob y).effect b))).re
      else 0

/-- For a commuting strategy, `σ.winProb G` agrees with `G.commutingWinProb (σ.toCommuting h)`. -/
theorem CStarStrategy.winProb_eq_commutingWinProb (G : TwoProverGame X Y A B)
    {C : Type u} [CStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
    (σ : CStarStrategy X Y A B C) (h : σ.IsCommuting) :
    σ.winProb G = G.commutingWinProb (σ.toCommuting h) := by
  classical
  simp only [CStarStrategy.winProb, TwoProverGame.commutingWinProb_eq_sum,
    CommutingStrategy.prob, CStarStrategy.toCommuting]
  refine Finset.sum_congr rfl fun x _ ↦ Finset.sum_congr rfl fun y _ ↦ congrArg (_ * ·) <|
    Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun b _ ↦ ?_
  rw [ozawaProd_eq_mul_of_commute ((σ.alice x).nonneg a) ((σ.bob y).nonneg b) (h x y a b)]

/-- Every `CStarStrategy` has winning probability in `[0, 1]`. -/
theorem CStarStrategy.winProb_mem_Icc (G : TwoProverGame X Y A B)
    {C : Type u} [CStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
    (σ : CStarStrategy X Y A B C) : σ.winProb G ∈ Set.Icc 0 1 := by
  classical
  have hterm_nn : ∀ x y a b,
      0 ≤ (σ.state (ozawaProd ((σ.alice x).effect a) ((σ.bob y).effect b))).re := fun x y a b ↦
    (Complex.nonneg_iff.mp (σ.state.apply_nonneg
      (ozawaProd_nonneg ((σ.alice x).nonneg a) ((σ.bob y).nonneg b)))).1
  constructor
  · exact Finset.sum_nonneg fun x _ ↦ Finset.sum_nonneg fun y _ ↦
      mul_nonneg ENNReal.toReal_nonneg <| Finset.sum_nonneg fun a _ ↦ Finset.sum_nonneg fun b _ ↦ by
        split_ifs <;> [exact hterm_nn x y a b; exact le_rfl]
  · have hrow : ∀ x y, (∑ a : A, ∑ b : B,
        if G.accepts x y a b then
          (σ.state (ozawaProd ((σ.alice x).effect a) ((σ.bob y).effect b))).re
        else 0) ≤ 1 := fun x y ↦
      calc _ ≤ ∑ a : A, ∑ b : B,
              (σ.state (ozawaProd ((σ.alice x).effect a) ((σ.bob y).effect b))).re :=
            Finset.sum_le_sum fun a _ ↦ Finset.sum_le_sum fun b _ ↦ by
              split_ifs <;> [exact le_rfl; exact hterm_nn x y a b]
        _ = (σ.state (∑ a : A, ∑ b : B,
              ozawaProd ((σ.alice x).effect a) ((σ.bob y).effect b))).re := by
            simp [map_sum]
        _ = 1 := by rw [sum_ozawaProd_measurement, σ.state.map_one, Complex.one_re]
    calc σ.winProb G
        ≤ ∑ x : X, ∑ y : Y, (G.questions (x, y)).toReal * 1 :=
          Finset.sum_le_sum fun x _ ↦ Finset.sum_le_sum fun y _ ↦
            mul_le_mul_of_nonneg_left (hrow x y) ENNReal.toReal_nonneg
      _ = ∑ p : X × Y, (G.questions p).toReal := by
          simp only [mul_one, ← Fintype.sum_prod_type']
      _ = 1 := by
          rw [← ENNReal.toReal_sum fun _ _ ↦ G.questions.apply_ne_top _,
            ← _root_.tsum_fintype (L := SummationFilter.unconditional _),
            G.questions.tsum_coe, ENNReal.toReal_one]

omit [Fintype X] [Fintype Y] in
/-- Every `δ`-op-almost commuting strategy is `δ`-state-almost commuting. -/
theorem CStarStrategy.IsOpAlmostCommuting.toState {C : Type u} [CStarAlgebra C] [PartialOrder C]
    [StarOrderedRing C] {σ : CStarStrategy X Y A B C} {δ : ℝ} (h : σ.IsOpAlmostCommuting δ) :
    σ.IsStateAlmostCommuting δ := fun x y ↦
  (Finset.sum_le_sum fun _ _ ↦ Finset.sum_le_sum fun _ _ ↦
    norm_algState_apply_le σ.state _).trans_lt (h x y)

omit [Fintype X] [Fintype Y] in
/-- Every commuting strategy is `δ`-op-almost commuting for every `δ > 0`. -/
theorem CStarStrategy.IsCommuting.toOpAlmostCommuting {C : Type u} [CStarAlgebra C]
    [PartialOrder C] [StarOrderedRing C] {σ : CStarStrategy X Y A B C} (h : σ.IsCommuting)
    {δ : ℝ} (hδ : 0 < δ) : σ.IsOpAlmostCommuting δ := fun x y ↦ by
  have h0 : ∀ a b, commBracket ((σ.alice x).effect a) ((σ.bob y).effect b) = 0 := fun a b ↦
    sub_eq_zero.mpr (h x y a b).eq
  simpa [h0] using hδ

/-- **Separable GNS realization theorem**: every strategy `σ` in any unital C*-algebra `C : Type u`
admits a unit-vector strategy `σ₀` in `H₀ →L[ℂ] H₀` on a separable Hilbert space `H₀ : Type` with
identical winning probability, identical state commutators, and non-increased operator-norm
commutators. -/
theorem exists_hilbert_strategy_of_cstar (G : TwoProverGame X Y A B)
    {C : Type u} [CStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
    (σ : CStarStrategy X Y A B C) :
    ∃ (H₀ : Type) (_ : NormedAddCommGroup H₀) (_ : InnerProductSpace ℂ H₀) (_ : CompleteSpace H₀)
      (_ : TopologicalSpace.SeparableSpace H₀) (ξ : H₀) (hξ : ‖ξ‖ = 1)
      (σ₀ : CStarStrategy X Y A B (H₀ →L[ℂ] H₀)),
      σ₀.state = vectorAlgState ξ hξ ∧
      σ₀.winProb G = σ.winProb G ∧
      (σ.IsCommuting → σ₀.IsCommuting) ∧
      (∀ δ, σ.IsOpAlmostCommuting δ → σ₀.IsOpAlmostCommuting δ) ∧
      (∀ δ, σ.IsStateAlmostCommuting δ → σ₀.IsStateAlmostCommuting δ) := by
  classical
  let S : Set C :=
    (Set.range fun p : X × A ↦ (σ.alice p.1).effect p.2) ∪
    (Set.range fun q : Y × B ↦ (σ.bob q.1).effect q.2)
  let D : StarSubalgebra ℂ C := (StarAlgebra.adjoin ℂ S).topologicalClosure
  have : IsClosed (D : Set C) := StarSubalgebra.isClosed_topologicalClosure _
  have : TopologicalSpace.SeparableSpace D :=
    separableSpace_adjoin_finite ((Set.finite_range _).union (Set.finite_range _))
  have : StarOrderedRing D := StarOrderedRing.of_nonneg_iff
    (fun {a b} hab c ↦ show (c : C) + a ≤ (c : C) + b from add_le_add_right hab _)
    fun d ↦ ⟨fun hd ↦ by
      have hdC : (0 : C) ≤ (d : C) := hd
      have hd_sa : IsSelfAdjoint d := Subtype.ext hdC.isSelfAdjoint.star_eq
      have hsr : ∀ t ∈ spectrum ℝ d, 0 ≤ t := fun t ht ↦ by
        have htC : t ∈ spectrum ℝ (d : C) := by
          rw [← spectrum.algebraMap_mem_iff ℂ] at ht ⊢
          exact StarSubalgebra.spectrum_eq (S := D) (a := d) ▸ ht
        have := hdC.isSelfAdjoint
        exact (cfc_nonneg_iff (fun s : ℝ ↦ s) (d : C)).mp (by rwa [cfc_id' ℝ (d : C)]) t htC
      let r : D := cfc Real.sqrt d
      have hr_sa : IsSelfAdjoint r := cfc_predicate Real.sqrt d
      refine AddSubmonoid.subset_closure ⟨r, ?_⟩
      change star r * r = d
      rw [hr_sa.star_eq]
      dsimp only [r]
      rw [← cfc_mul (hf := Real.continuous_sqrt.continuousOn)
        (hg := Real.continuous_sqrt.continuousOn),
        show cfc (fun t : ℝ ↦ Real.sqrt t * Real.sqrt t) d = cfc (fun t : ℝ ↦ t) d from
          cfc_congr fun t ht ↦ Real.mul_self_sqrt (hsr t ht), cfc_id' ℝ d],
      fun hmem ↦ AddSubmonoid.closure_induction
        (by rintro _ ⟨r, rfl⟩; exact star_mul_self_nonneg (r : C))
        le_rfl (fun _ _ _ _ ↦ add_nonneg) hmem⟩
  let aliceD : X → Measurement A D := fun x ↦
    { effect := fun a ↦ ⟨(σ.alice x).effect a, StarSubalgebra.le_topologicalClosure _
        (StarAlgebra.subset_adjoin ℂ _ (Set.mem_union_left _ ⟨(x, a), rfl⟩))⟩
      nonneg := fun a ↦ (σ.alice x).nonneg a
      sum_effect := Subtype.ext (by simpa using (σ.alice x).sum_effect) }
  let bobD : Y → Measurement B D := fun y ↦
    { effect := fun b ↦ ⟨(σ.bob y).effect b, StarSubalgebra.le_topologicalClosure _
        (StarAlgebra.subset_adjoin ℂ _ (Set.mem_union_right _ ⟨(y, b), rfl⟩))⟩
      nonneg := fun b ↦ (σ.bob y).nonneg b
      sum_effect := Subtype.ext (by simpa using (σ.bob y).sum_effect) }
  let f : D →ₚ[ℂ] ℂ :=
    { toFun := fun d ↦ σ.state d.1
      map_add' := fun d₁ d₂ ↦ map_add σ.state d₁.1 d₂.1
      map_smul' := fun c d ↦ map_smul σ.state c d.1
      monotone' := fun d₁ d₂ h ↦ by
        have := σ.state.apply_nonneg (sub_nonneg.mpr (show (d₁ : C) ≤ d₂ from h))
        rwa [map_sub, sub_nonneg] at this }
  let πGNS : D →⋆ₐ[ℂ] (f.GNS →L[ℂ] f.GNS) := f.gnsStarAlgHom
  let ζ : f.GNS := (f.toPreGNS 1 : f.GNS)
  have hζ_norm : ‖ζ‖ = 1 := by
    rw [UniformSpace.Completion.norm_coe]
    have hsq : ((‖f.toPreGNS 1‖ ^ 2 : ℝ) : ℂ) = 1 := by
      have hp := f.preGNS_norm_sq (f.toPreGNS 1)
      simp only [PositiveLinearMap.ofPreGNS_toPreGNS, star_one, one_mul] at hp
      push_cast
      exact hp.trans σ.state.map_one
    have hsq' : ‖f.toPreGNS 1‖ ^ 2 = 1 := by exact_mod_cast hsq
    nlinarith [norm_nonneg (f.toPreGNS 1)]
  have hζ_state : ∀ d : D, ⟪ζ, πGNS d ζ⟫_ℂ = f d := fun d ↦ by
    have happ : πGNS d ζ = (f.toPreGNS d : f.GNS) := by
      change f.gnsNonUnitalStarAlgHom d (f.toPreGNS 1 : f.GNS) = _
      rw [PositiveLinearMap.gnsNonUnitalStarAlgHom_apply_coe]; simp
    rw [happ, UniformSpace.Completion.inner_coe, PositiveLinearMap.preGNS_inner_def]; simp
  have : TopologicalSpace.SeparableSpace f.GNS := by
    let cls : D → f.GNS := fun d ↦ (f.toPreGNS d : f.GNS)
    have hcls_cont : Continuous cls :=
      (LipschitzWith.of_dist_le_mul (K := 1) fun d₁ d₂ ↦ by
        rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm,
          show cls d₁ - cls d₂ = (f.toPreGNS (d₁ - d₂) : f.GNS) by
            simp [cls, ← UniformSpace.Completion.coe_sub],
          UniformSpace.Completion.norm_coe, PositiveLinearMap.preGNS_norm_def']
        simp only [PositiveLinearMap.ofPreGNS_toPreGNS]
        have hbd : ‖f (star (d₁ - d₂) * (d₁ - d₂))‖ ≤ ‖d₁ - d₂‖ ^ 2 :=
          (norm_algState_apply_le σ.state _).trans_eq <| by
            change ‖star (d₁.1 - d₂.1) * (d₁.1 - d₂.1)‖ = ‖d₁.1 - d₂.1‖ ^ 2
            rw [CStarRing.norm_star_mul_self, ← sq]
        exact (Real.sqrt_le_sqrt hbd).trans_eq (Real.sqrt_sq (norm_nonneg _))).continuous
    obtain ⟨cnt, hcnt, hd⟩ := TopologicalSpace.exists_countable_dense D
    exact ⟨⟨cls '' cnt, hcnt.image cls,
      ((UniformSpace.Completion.denseRange_coe).comp f.toPreGNS.surjective.denseRange
        (UniformSpace.Completion.continuous_coe _)).dense_image hcls_cont hd⟩⟩
  obtain ⟨H₀, i1, i2, i3, i4, ⟨e⟩⟩ := exists_type0_hilbert_iso f.GNS
  let π₀ : D →⋆ₐ[ℂ] (H₀ →L[ℂ] H₀) := (conjCLM e).comp πGNS
  let ξ : H₀ := e ζ
  have hξ : ‖ξ‖ = 1 := (e.norm_map ζ).trans hζ_norm
  have hξ_state : ∀ d : D, ⟪ξ, π₀ d ξ⟫_ℂ = σ.state d.1 := fun d ↦ by
    change ⟪e ζ, e (πGNS d (e.symm (e ζ)))⟫_ℂ = f d
    rw [e.symm_apply_apply, e.inner_map_map, hζ_state]
  let σ₀ : CStarStrategy X Y A B (H₀ →L[ℂ] H₀) :=
    { alice := fun x ↦ mapMeasurement π₀ (aliceD x)
      bob := fun y ↦ mapMeasurement π₀ (bobD y)
      state := vectorAlgState ξ hξ }
  refine ⟨H₀, i1, i2, i3, i4, ξ, hξ, σ₀, rfl, ?_, ?_, ?_, ?_⟩
  · simp only [CStarStrategy.winProb]
    refine Finset.sum_congr rfl fun x _ ↦ Finset.sum_congr rfl fun y _ ↦ congrArg (_ * ·) <|
      Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun b _ ↦ ?_
    split_ifs <;> [skip; rfl]
    congr 1
    change ⟪ξ, ozawaProd (π₀ ((aliceD x).effect a)) (π₀ ((bobD y).effect b)) ξ⟫_ℂ = _
    rw [← map_ozawaProd π₀ ((aliceD x).nonneg a) ((bobD y).nonneg b), hξ_state]
    change σ.state (D.subtype (ozawaProd ((aliceD x).effect a) ((bobD y).effect b))) = _
    rw [map_ozawaProd D.subtype ((aliceD x).nonneg a) ((bobD y).nonneg b)]; rfl
  · intro hc x y a b
    exact (show Commute ((aliceD x).effect a) ((bobD y).effect b) from
      Subtype.ext (hc x y a b).eq).map π₀
  · intro δ hop x y
    refine (Finset.sum_le_sum fun a _ ↦ Finset.sum_le_sum fun b _ ↦ ?_).trans_lt (hop x y)
    have hm : commBracket ((σ₀.alice x).effect a) ((σ₀.bob y).effect b) =
        π₀ (commBracket ((aliceD x).effect a) ((bobD y).effect b)) := by
      simp [σ₀, commBracket, mapMeasurement]
    rw [hm]
    exact NonUnitalStarAlgHom.norm_apply_le π₀.toNonUnitalStarAlgHom _
  · intro δ hst x y
    have hm : ∀ a b, σ₀.state (commBracket ((σ₀.alice x).effect a) ((σ₀.bob y).effect b)) =
        σ.state (commBracket ((σ.alice x).effect a) ((σ.bob y).effect b)) := fun a b ↦ by
      have h1 : commBracket ((σ₀.alice x).effect a) ((σ₀.bob y).effect b) =
          π₀ (commBracket ((aliceD x).effect a) ((bobD y).effect b)) := by
        simp [σ₀, commBracket, mapMeasurement]
      rw [h1]; exact hξ_state _
    simpa only [hm] using hst x y

/-- The Hilbert-space unit-vector commuting-operator value of a two-prover game `G`. -/
noncomputable def hilbertCommutingValue (G : TwoProverGame X Y A B) : ℝ :=
  sSup { v : ℝ | ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
    (_ : CompleteSpace H) (_ : TopologicalSpace.SeparableSpace H)
    (ξ : H) (hξ : ‖ξ‖ = 1) (S : CommutingStrategy X Y A B (H →L[ℂ] H)),
    S.state = vectorAlgState ξ hξ ∧ v = G.commutingWinProb S }

omit [Fintype X] [Fintype Y] in
/-- **GNS equivalence for `TwoProverGame.commutingValue`**: for every finite two-prover game `G`,
the abstract C*-algebraic commuting value `G.commutingValue` equals the separable Hilbert-space
unit-vector commuting value `hilbertCommutingValue G`. -/
theorem commutingValue_eq_hilbertCommutingValue [Finite X] [Finite Y] [Nonempty A] [Nonempty B]
    (G : TwoProverGame X Y A B) :
    G.commutingValue = hilbertCommutingValue G := by
  classical
  cases nonempty_fintype X
  cases nonempty_fintype Y
  let a₀ : A := Classical.arbitrary A
  let b₀ : B := Classical.arbitrary B
  let H₁ := ℂ
  let e₀ : H₁ := 1
  have he₀ : ‖e₀‖ = 1 := norm_one
  let S₁ : CommutingStrategy X Y A B (H₁ →L[ℂ] H₁) :=
    { alice := fun _ ↦ Measurement.const a₀
      bob := fun _ ↦ Measurement.const b₀
      state := vectorAlgState e₀ he₀
      commute := fun _ _ a b ↦ by
        change Commute (if a = a₀ then (1 : H₁ →L[ℂ] H₁) else 0)
          (if b = b₀ then (1 : H₁ →L[ℂ] H₁) else 0)
        split_ifs <;> simp [Commute, SemiconjBy] }
  have hbdd : BddAbove { v : ℝ | ∃ (H : Type) (_ : NormedAddCommGroup H)
      (_ : InnerProductSpace ℂ H) (_ : CompleteSpace H) (_ : TopologicalSpace.SeparableSpace H)
      (ξ : H) (hξ : ‖ξ‖ = 1) (S : CommutingStrategy X Y A B (H →L[ℂ] H)),
      S.state = vectorAlgState ξ hξ ∧ v = G.commutingWinProb S } :=
    ⟨1, by rintro _ ⟨H, i1, i2, i3, _, _, _, S, _, rfl⟩; exact G.commutingWinProb_le_one S⟩
  have hmem₁ : G.commutingWinProb S₁ ∈ { v : ℝ | ∃ (H : Type) (_ : NormedAddCommGroup H)
      (_ : InnerProductSpace ℂ H) (_ : CompleteSpace H) (_ : TopologicalSpace.SeparableSpace H)
      (ξ : H) (hξ : ‖ξ‖ = 1) (S : CommutingStrategy X Y A B (H →L[ℂ] H)),
      S.state = vectorAlgState ξ hξ ∧ v = G.commutingWinProb S } :=
    ⟨H₁, inferInstance, inferInstance, inferInstance, inferInstance, e₀, he₀, S₁, rfl, rfl⟩
  refine le_antisymm ?_
    (csSup_le ⟨_, hmem₁⟩ fun _ ⟨H, i1, i2, i3, _, _, _, S, _, hv⟩ ↦ by
      rw [hv]; exact G.commutingWinProb_le_commutingValue S)
  refine G.commutingValue_le (c := hilbertCommutingValue G)
    ((G.commutingWinProb_nonneg S₁).trans (le_csSup hbdd hmem₁))
    fun {C} _ _ _ S ↦ ?_
  let σ : CStarStrategy X Y A B C := CStarStrategy.ofCommuting S
  have hσc : σ.IsCommuting := S.commute
  obtain ⟨H₀, i1, i2, i3, i4, ξ, hξ, σ₀, hst, hval, hc₀, _, _⟩ :=
    exists_hilbert_strategy_of_cstar G σ
  have heq : G.commutingWinProb S = G.commutingWinProb (σ₀.toCommuting (hc₀ hσc)) := by
    rw [← σ₀.winProb_eq_commutingWinProb G (hc₀ hσc), hval, σ.winProb_eq_commutingWinProb G hσc]
    rfl
  rw [heq]
  exact le_csSup hbdd ⟨H₀, i1, i2, i3, i4, ξ, hξ, σ₀.toCommuting (hc₀ hσc), hst, rfl⟩

/-- The `δ`-operator-norm-almost commuting value of a two-prover game over Hilbert spaces. -/
noncomputable def opAlmostCommutingValue (G : TwoProverGame X Y A B) (δ : ℝ) : ℝ :=
  sSup { v : ℝ | ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
    (_ : CompleteSpace H) (σ : CStarStrategy X Y A B (H →L[ℂ] H)),
    σ.IsOpAlmostCommuting δ ∧ v = σ.winProb G }

/-- The `δ`-operator-norm-almost commuting value over finite-dimensional Hilbert spaces. -/
noncomputable def finDimOpAlmostCommutingValue (G : TwoProverGame X Y A B) (δ : ℝ) : ℝ :=
  sSup { v : ℝ | ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
    (_ : CompleteSpace H) (_ : FiniteDimensional ℂ H) (σ : CStarStrategy X Y A B (H →L[ℂ] H)),
    σ.IsOpAlmostCommuting δ ∧ v = σ.winProb G }

/-- The `δ`-state-almost commuting value of a two-prover game over Hilbert spaces. -/
noncomputable def stateAlmostCommutingValue (G : TwoProverGame X Y A B) (δ : ℝ) : ℝ :=
  sSup { v : ℝ | ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
    (_ : CompleteSpace H) (σ : CStarStrategy X Y A B (H →L[ℂ] H)),
    σ.IsStateAlmostCommuting δ ∧ v = σ.winProb G }

/-- The `δ`-state-almost commuting value over finite-dimensional Hilbert spaces. -/
noncomputable def finDimStateAlmostCommutingValue (G : TwoProverGame X Y A B) (δ : ℝ) : ℝ :=
  sSup { v : ℝ | ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
    (_ : CompleteSpace H) (_ : FiniteDimensional ℂ H) (σ : CStarStrategy X Y A B (H →L[ℂ] H)),
    σ.IsStateAlmostCommuting δ ∧ v = σ.winProb G }

/-- `G.commutingValue ≤ opAlmostCommutingValue G δ` for every `δ > 0`. -/
theorem commutingValue_le_opAlmostCommutingValue [Nonempty A] [Nonempty B]
    (G : TwoProverGame X Y A B) {δ : ℝ} (hδ : 0 < δ) :
    G.commutingValue ≤ opAlmostCommutingValue G δ := by
  rw [commutingValue_eq_hilbertCommutingValue G]
  classical
  let a₀ : A := Classical.arbitrary A
  let b₀ : B := Classical.arbitrary B
  let H₁ := ℂ
  let e₀ : H₁ := 1
  have he₀ : ‖e₀‖ = 1 := norm_one
  let S₁ : CommutingStrategy X Y A B (H₁ →L[ℂ] H₁) :=
    { alice := fun _ ↦ Measurement.const a₀
      bob := fun _ ↦ Measurement.const b₀
      state := vectorAlgState e₀ he₀
      commute := fun _ _ a b ↦ by
        change Commute (if a = a₀ then (1 : H₁ →L[ℂ] H₁) else 0)
          (if b = b₀ then (1 : H₁ →L[ℂ] H₁) else 0)
        split_ifs <;> simp [Commute, SemiconjBy] }
  refine csSup_le_csSup
    ⟨1, by rintro _ ⟨H, i1, i2, i3, σ, _, rfl⟩; exact (σ.winProb_mem_Icc G).2⟩
    ⟨G.commutingWinProb S₁, H₁, inferInstance, inferInstance, inferInstance, inferInstance,
      e₀, he₀, S₁, rfl, rfl⟩ ?_
  rintro _ ⟨H, i1, i2, i3, _, _, _, S, _, rfl⟩
  let σ : CStarStrategy X Y A B (H →L[ℂ] H) := CStarStrategy.ofCommuting S
  have hc : σ.IsCommuting := S.commute
  exact ⟨H, i1, i2, i3, σ, hc.toOpAlmostCommuting hδ, (σ.winProb_eq_commutingWinProb G hc).symm⟩

/-- `opAlmostCommutingValue G δ ≤ stateAlmostCommutingValue G δ` for every `δ > 0`. -/
theorem opAlmostCommutingValue_le_stateAlmostCommutingValue [Nonempty A] [Nonempty B]
    (G : TwoProverGame X Y A B) {δ : ℝ} (hδ : 0 < δ) :
    opAlmostCommutingValue G δ ≤ stateAlmostCommutingValue G δ := by
  classical
  let a₀ : A := Classical.arbitrary A
  let b₀ : B := Classical.arbitrary B
  let H₁ := ℂ
  let e₀ : H₁ := 1
  have he₀ : ‖e₀‖ = 1 := norm_one
  let σ₁ : CStarStrategy X Y A B (H₁ →L[ℂ] H₁) :=
    { alice := fun _ ↦ Measurement.const a₀
      bob := fun _ ↦ Measurement.const b₀
      state := vectorAlgState e₀ he₀ }
  have hc₁ : σ₁.IsCommuting := fun _ _ a b ↦ by
    change Commute (if a = a₀ then (1 : H₁ →L[ℂ] H₁) else 0)
      (if b = b₀ then (1 : H₁ →L[ℂ] H₁) else 0)
    split_ifs <;> simp [Commute, SemiconjBy]
  exact csSup_le_csSup
    ⟨1, by rintro _ ⟨H, i1, i2, i3, σ, _, rfl⟩; exact (σ.winProb_mem_Icc G).2⟩
    ⟨σ₁.winProb G, H₁, inferInstance, inferInstance, inferInstance, σ₁,
      hc₁.toOpAlmostCommuting hδ, rfl⟩
    fun _ ⟨H, i1, i2, i3, σ, h, hv⟩ ↦ ⟨H, i1, i2, i3, σ, h.toState, hv⟩

private theorem spectrum_subset_unitInterval {W : Type} [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] [CompleteSpace W] {T : W →L[ℂ] W} (hT0 : 0 ≤ T) (hT1 : T ≤ 1) :
    spectrum ℝ T ⊆ Set.Icc 0 1 := fun t ht ↦ by
  have hT_sa : IsSelfAdjoint T := hT0.isSelfAdjoint
  have ht0 : 0 ≤ t := (cfc_nonneg_iff (fun s : ℝ ↦ s) T).mp (by rwa [cfc_id' ℝ T]) t ht
  have h1t : 1 - t ∈ spectrum ℝ (1 - T) := by
    rw [spectrum.mem_iff] at ht ⊢
    refine fun hu ↦ ht ?_
    have heq : algebraMap ℝ (W →L[ℂ] W) t - T =
        -(algebraMap ℝ (W →L[ℂ] W) (1 - t) - (1 - T)) := by rw [map_sub, map_one]; abel
    rw [heq]; exact hu.neg
  have : IsSelfAdjoint (1 - T) := (IsSelfAdjoint.one (W →L[ℂ] W)).sub hT_sa
  have ht1 : 0 ≤ 1 - t :=
    (cfc_nonneg_iff (fun s : ℝ ↦ s) (1 - T)).mp
      (by rw [cfc_id' ℝ (1 - T)]; exact sub_nonneg.mpr hT1) (1 - t) h1t
  exact ⟨ht0, by linarith⟩

private theorem norm_le_one_of_unitInterval {W : Type} [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] [CompleteSpace W] {T : W →L[ℂ] W} (h0 : 0 ≤ T) (h1 : T ≤ 1) :
    ‖T‖ ≤ 1 := by
  have : IsSelfAdjoint T := h0.isSelfAdjoint
  have hspec := spectrum_subset_unitInterval h0 h1
  rw [← cfc_id' ℝ T]
  refine norm_cfc_le zero_le_one fun t ht ↦ ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (hspec ht).1]
  exact (hspec ht).2

private theorem norm_aeval_sub_sqrt_le {W : Type} [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] [CompleteSpace W] {P : Polynomial ℝ} {η : ℝ} (hη : 0 ≤ η)
    (hP : ∀ t ∈ Set.Icc (0 : ℝ) 1, |P.eval t - Real.sqrt t| ≤ η)
    (T : W →L[ℂ] W) (hT0 : 0 ≤ T) (hT1 : T ≤ 1) :
    ‖Polynomial.aeval T P - CFC.sqrt T‖ ≤ η := by
  have : IsSelfAdjoint T := hT0.isSelfAdjoint
  have hspec := spectrum_subset_unitInterval hT0 hT1
  have haeval : ∀ Q : Polynomial ℝ, Polynomial.aeval T Q = cfc (fun t : ℝ ↦ Q.eval t) T :=
    fun Q ↦ by
      induction Q using Polynomial.induction_on' with
      | add p q hp hq =>
        rw [map_add, hp, hq, ← cfc_add (hf := p.continuous.continuousOn)
          (hg := q.continuous.continuousOn)]
        exact cfc_congr fun t _ ↦ by simp
      | monomial k c =>
        rw [Polynomial.aeval_monomial, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul,
          ← cfc_pow_id (R := ℝ) T k,
          ← cfc_smul (R := ℝ) c (fun t : ℝ ↦ t ^ k) T (hf := (continuous_pow k).continuousOn)]
        exact cfc_congr fun t _ ↦ by simp [Polynomial.eval_monomial, smul_eq_mul]
  have hsqrt_real : CFC.sqrt T = cfc Real.sqrt T :=
    (CFC.sqrt_eq_iff T (cfc Real.sqrt T) hT0
      (cfc_nonneg fun t _ ↦ Real.sqrt_nonneg t)).mpr <| by
      rw [← cfc_mul (hf := Real.continuous_sqrt.continuousOn)
        (hg := Real.continuous_sqrt.continuousOn),
        show cfc (fun t : ℝ ↦ Real.sqrt t * Real.sqrt t) T = cfc (fun t : ℝ ↦ t) T from
          cfc_congr fun t ht ↦ Real.mul_self_sqrt (hspec ht).1, cfc_id' ℝ T]
  rw [haeval P, hsqrt_real,
    ← cfc_sub (hf := P.continuous.continuousOn) (hg := Real.continuous_sqrt.continuousOn)]
  exact norm_cfc_le hη fun t ht ↦ by rw [Real.norm_eq_abs]; exact hP t (hspec ht)

private theorem norm_quad_compress_sub_le {H W : Type}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]
    (ιV : W →L[ℂ] H) (pV : H →L[ℂ] W)
    (hι_norm : ∀ u : W, ‖ιV u‖ = ‖u‖)
    (hinner : ∀ (u : W) (x : H), ⟪u, pV x⟫_ℂ = ⟪ιV u, x⟫_ℂ)
    (hpι : ∀ u : W, pV (ιV u) = u)
    {P : Polynomial ℝ} {η : ℝ} (hη : 0 ≤ η)
    (hP : ∀ t ∈ Set.Icc (0 : ℝ) 1, |P.eval t - Real.sqrt t| ≤ η)
    {ξV : W} (hξV : ‖ξV‖ = 1) {E F : H →L[ℂ] H}
    (hE0 : 0 ≤ E) (hE1 : E ≤ 1) (hF0 : 0 ≤ F) (hF1 : F ≤ 1)
    (hpow : ∀ j ≤ P.natDegree, ιV (pV ((E ^ j) (ιV ξV))) = (E ^ j) (ιV ξV)) :
    let compV : (H →L[ℂ] H) → (W →L[ℂ] W) := fun T ↦ pV.comp (T.comp ιV)
    ‖⟪ιV ξV, (CFC.sqrt E * F * CFC.sqrt E) (ιV ξV)⟫_ℂ -
      ⟪ξV, (CFC.sqrt (compV E) * compV F * CFC.sqrt (compV E)) ξV⟫_ℂ‖ ≤ 4 * η := by
  intro compV
  have hξ : ‖ιV ξV‖ = 1 := (hι_norm ξV).trans hξV
  have hcomp_star : ∀ T : H →L[ℂ] H, star (compV T) = compV (star T) := fun T ↦
    ContinuousLinearMap.ext fun v ↦ ext_inner_left ℂ fun u ↦ by
      rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
      change ⟪compV T u, v⟫_ℂ = ⟪u, pV ((star T) (ιV v))⟫_ℂ
      rw [hinner, ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
      change ⟪pV (T (ιV u)), v⟫_ℂ = ⟪T (ιV u), ιV v⟫_ℂ
      rw [← inner_conj_symm, hinner, inner_conj_symm]
  have hcomp_nn : ∀ {T : H →L[ℂ] H}, 0 ≤ T → 0 ≤ compV T := fun {T} hT ↦
    ContinuousLinearMap.nonneg_iff_isPositive.mpr
      ⟨ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
         (by change star (compV T) = compV T; rw [hcomp_star, hT.isSelfAdjoint.star_eq]),
       fun u ↦ by
         have hpos := ContinuousLinearMap.nonneg_iff_isPositive.mp hT
         have hin : ⟪compV T u, u⟫_ℂ = ⟪T (ιV u), ιV u⟫_ℂ := by
           rw [← inner_conj_symm, show ⟪u, compV T u⟫_ℂ = ⟪u, pV (T (ιV u))⟫_ℂ from rfl,
             hinner, inner_conj_symm]
         rw [ContinuousLinearMap.reApplyInnerSelf_apply, hin,
           ← ContinuousLinearMap.reApplyInnerSelf_apply]
         exact hpos.2 (ιV u)⟩
  have hcE0 : 0 ≤ compV E := hcomp_nn hE0
  have hcE1 : compV E ≤ 1 := by
    have h0 : 0 ≤ compV (1 - E) := hcomp_nn (sub_nonneg.mpr hE1)
    have hs : compV (1 - E) = 1 - compV E := by ext v; simp [compV, sub_apply, hpι v]
    rwa [hs, sub_nonneg] at h0
  have hcpow : ∀ j ≤ P.natDegree, ιV ((compV E ^ j) ξV) = (E ^ j) (ιV ξV) := fun j hj ↦ by
    induction j with
    | zero => rfl
    | succ k ih =>
      have happ : (compV E ^ (k + 1)) ξV = pV (E (ιV ((compV E ^ k) ξV))) := by rw [pow_succ']; rfl
      rw [happ, ih (by omega), show E ((E ^ k) (ιV ξV)) = (E ^ (k + 1)) (ιV ξV) by
        rw [pow_succ']; rfl]
      exact hpow (k + 1) hj
  have hpoly : ιV ((Polynomial.aeval (compV E) P) ξV) = (Polynomial.aeval E P) (ιV ξV) := by
    rw [Polynomial.aeval_eq_sum_range, Polynomial.aeval_eq_sum_range]
    simp only [sum_apply, smul_apply, map_sum]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    change ιV ((P.coeff j : ℂ) • (compV E ^ j) ξV) = (P.coeff j : ℂ) • (E ^ j) (ιV ξV)
    rw [map_smul, hcpow j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))]
  set u : H := CFC.sqrt E (ιV ξV)
  set w : H := ιV (CFC.sqrt (compV E) ξV)
  have huw : ‖u - w‖ ≤ 2 * η := by
    rw [norm_sub_rev]
    have h1 : ‖w - ιV ((Polynomial.aeval (compV E) P) ξV)‖ ≤ η := by
      rw [← map_sub, hι_norm, ← sub_apply, ← neg_sub, neg_apply, norm_neg]
      exact ((Polynomial.aeval (compV E) P - CFC.sqrt (compV E)).le_opNorm ξV).trans
        (by rw [hξV, mul_one]; exact norm_aeval_sub_sqrt_le hη hP (compV E) hcE0 hcE1)
    have h2 : ‖ιV ((Polynomial.aeval (compV E) P) ξV) - u‖ ≤ η := by
      rw [hpoly, ← sub_apply]
      exact ((Polynomial.aeval E P - CFC.sqrt E).le_opNorm (ιV ξV)).trans
        (by rw [hξ, mul_one]; exact norm_aeval_sub_sqrt_le hη hP E hE0 hE1)
    exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans ((add_le_add h1 h2).trans_eq (by ring))
  have hu : ‖u‖ ≤ 1 := by
    have hs : ‖CFC.sqrt E‖ * ‖CFC.sqrt E‖ ≤ 1 := by
      rw [← CStarRing.norm_star_mul_self, (CFC.sqrt_nonneg E).isSelfAdjoint.star_eq,
        CFC.sqrt_mul_sqrt_self E hE0]
      exact norm_le_one_of_unitInterval hE0 hE1
    exact ((CFC.sqrt E).le_opNorm (ιV ξV)).trans
      (by rw [hξ, mul_one]; nlinarith [norm_nonneg (CFC.sqrt E)])
  have hw : ‖w‖ ≤ 1 := by
    have hs : ‖CFC.sqrt (compV E)‖ * ‖CFC.sqrt (compV E)‖ ≤ 1 := by
      rw [← CStarRing.norm_star_mul_self, (CFC.sqrt_nonneg (compV E)).isSelfAdjoint.star_eq,
        CFC.sqrt_mul_sqrt_self _ hcE0]
      exact norm_le_one_of_unitInterval hcE0 hcE1
    rw [hι_norm]
    exact ((CFC.sqrt (compV E)).le_opNorm ξV).trans
      (by rw [hξV, mul_one]; nlinarith [norm_nonneg (CFC.sqrt (compV E))])
  have hFn : ‖F‖ ≤ 1 := norm_le_one_of_unitInterval hF0 hF1
  have h1 : ⟪ιV ξV, (CFC.sqrt E * F * CFC.sqrt E) (ιV ξV)⟫_ℂ = ⟪u, F u⟫_ℂ := by
    change ⟪ιV ξV, CFC.sqrt E (F u)⟫_ℂ = _
    rw [← (CFC.sqrt_nonneg E).isSelfAdjoint.star_eq, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_inner_right]
  have h2 : ⟪ξV, (CFC.sqrt (compV E) * compV F * CFC.sqrt (compV E)) ξV⟫_ℂ = ⟪w, F w⟫_ℂ := by
    change ⟪ξV, CFC.sqrt (compV E) (pV (F w))⟫_ℂ = _
    rw [← (CFC.sqrt_nonneg (compV E)).isSelfAdjoint.star_eq,
      ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right, hinner]
  rw [h1, h2, show ⟪u, F u⟫_ℂ - ⟪w, F w⟫_ℂ = ⟪u - w, F u⟫_ℂ + ⟪w, F (u - w)⟫_ℂ by
    simp [inner_sub_left, inner_sub_right]]
  have hFu : ‖F u‖ ≤ 1 := (F.le_opNorm u).trans (by nlinarith [norm_nonneg F, norm_nonneg u])
  have hFuw : ‖F (u - w)‖ ≤ ‖u - w‖ :=
    (F.le_opNorm (u - w)).trans
      ((mul_le_mul_of_nonneg_right hFn (norm_nonneg _)).trans_eq (one_mul _))
  calc ‖⟪u - w, F u⟫_ℂ + ⟪w, F (u - w)⟫_ℂ‖
      ≤ ‖u - w‖ * ‖F u‖ + ‖w‖ * ‖F (u - w)‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _))
    _ ≤ ‖u - w‖ * 1 + 1 * ‖u - w‖ :=
        add_le_add (mul_le_mul_of_nonneg_left hFu (norm_nonneg _))
          (mul_le_mul hw hFuw (norm_nonneg _) zero_le_one)
    _ ≤ 4 * η := by linarith

/-- **Polynomial Krylov finite-dimensional compression**: every `δ`-state-almost commuting
strategy `σ_in` for a finite two-prover game `G` can be approximated in winning probability within
any `ε > 0` by a finite-dimensional `δ`-state-almost commuting strategy with the exact same state
commutators. -/
theorem exists_finDim_stateAlmostCommuting_approx (G : TwoProverGame X Y A B)
    {C : Type u} [CStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
    (σ_in : CStarStrategy X Y A B C) {δ ε : ℝ}
    (hst_in : σ_in.IsStateAlmostCommuting δ) (hε : 0 < ε) :
    ∃ (V : Type) (_ : NormedAddCommGroup V) (_ : InnerProductSpace ℂ V)
      (_ : CompleteSpace V) (_ : FiniteDimensional ℂ V)
      (σV : CStarStrategy X Y A B (V →L[ℂ] V)),
      σV.IsStateAlmostCommuting δ ∧ σ_in.winProb G - σV.winProb G ≤ ε := by
  classical
  obtain ⟨H, _, _, _, _, ξ, hξ, σ₀, hstate₀, hval₀, _, _, hst₀⟩ :=
    exists_hilbert_strategy_of_cstar G σ_in
  have hσ₀ := hst₀ δ hst_in
  let cardAB : ℝ := (Fintype.card A * Fintype.card B : ℝ)
  let η : ℝ := ε / (4 * (cardAB + 1))
  have hη : 0 < η := by positivity
  let sqrtMap : C(Set.Icc (0 : ℝ) 1, ℝ) :=
    ⟨fun t ↦ Real.sqrt t.1, Real.continuous_sqrt.comp continuous_subtype_val⟩
  obtain ⟨P, hP⟩ := exists_polynomial_near_continuousMap 0 1 sqrtMap η hη
  have hP_approx : ∀ t ∈ Set.Icc (0 : ℝ) 1, |P.eval t - Real.sqrt t| ≤ η := fun t ht ↦ by
    have hlt := (ContinuousMap.dist_lt_iff hη).mp hP ⟨t, ht⟩
    exact (by simpa [sqrtMap, Polynomial.toContinuousMapOn, Polynomial.toContinuousMap,
      Real.dist_eq] using hlt : |P.eval t - Real.sqrt t| < η).le
  let d : ℕ := max P.natDegree 1
  let krylovA : X × A × Fin (d + 1) → H := fun ⟨x, a, j⟩ ↦ (((σ₀.alice x).effect a) ^ j.1) ξ
  let krylovB : Y × B × Fin (d + 1) → H := fun ⟨y, b, j⟩ ↦ (((σ₀.bob y).effect b) ^ j.1) ξ
  let V : Submodule ℂ H :=
    Submodule.span ℂ ({ξ} ∪ Set.range krylovA ∪ Set.range krylovB)
  have : FiniteDimensional ℂ V := Module.Finite.span_of_finite ℂ
    (((Set.finite_singleton ξ).union (Set.finite_range krylovA)).union (Set.finite_range krylovB))
  have : CompleteSpace V := FiniteDimensional.completeSpace ℂ V
  let pV : H →L[ℂ] V := V.orthogonalProjectionOnto
  let ιV : V →L[ℂ] H := V.subtypeL
  let compV : (H →L[ℂ] H) → (V →L[ℂ] V) := fun T ↦ pV.comp (T.comp ιV)
  have hpV_mem : ∀ {w : H} (hw : w ∈ V), pV w = ⟨w, hw⟩ := fun hw ↦
    Submodule.orthogonalProjectionOnto_mem_subspace_eq_self ⟨_, hw⟩
  have hcomp_one : compV 1 = 1 := by ext v; simp [compV, ιV, hpV_mem v.2]
  have hinner_pV : ∀ (u : V) (w : H), ⟪u, pV w⟫_ℂ = ⟪ιV u, w⟫_ℂ := fun u w ↦ by
    change ⟪(u : H), (V.starProjection w : H)⟫_ℂ = ⟪(u : H), w⟫_ℂ
    rw [← V.inner_starProjection_left_eq_right, V.starProjection_eq_self_iff.mpr u.2]
  have hcomp_star : ∀ T : H →L[ℂ] H, star (compV T) = compV (star T) := fun T ↦
    ContinuousLinearMap.ext fun v ↦ ext_inner_left ℂ fun u ↦ by
      rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
      change ⟪compV T u, v⟫_ℂ = ⟪u, pV ((star T) (ιV v))⟫_ℂ
      rw [hinner_pV, ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
      change ⟪pV (T (ιV u)), v⟫_ℂ = ⟪T (ιV u), ιV v⟫_ℂ
      rw [← inner_conj_symm, hinner_pV, inner_conj_symm]
  have hcomp_nonneg : ∀ {T : H →L[ℂ] H}, 0 ≤ T → 0 ≤ compV T := fun {T} hT ↦
    ContinuousLinearMap.nonneg_iff_isPositive.mpr
      ⟨ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
         (by change star (compV T) = compV T; rw [hcomp_star, hT.isSelfAdjoint.star_eq]),
       fun u ↦ by
         have hpos := ContinuousLinearMap.nonneg_iff_isPositive.mp hT
         have hin : ⟪compV T u, u⟫_ℂ = ⟪T (ιV u), ιV u⟫_ℂ := by
           rw [← inner_conj_symm, show ⟪u, compV T u⟫_ℂ = ⟪u, pV (T (ιV u))⟫_ℂ from rfl,
             hinner_pV, inner_conj_symm]
         rw [ContinuousLinearMap.reApplyInnerSelf_apply, hin,
           ← ContinuousLinearMap.reApplyInnerSelf_apply]
         exact hpos.2 (ιV u)⟩
  have hcomp_le_one : ∀ {T : H →L[ℂ] H}, T ≤ 1 → compV T ≤ 1 := fun {T} hT1 ↦ by
    have h0 : 0 ≤ compV (1 - T) := hcomp_nonneg (sub_nonneg.mpr hT1)
    have hsub : compV (1 - T) = 1 - compV T := by
      ext v; simp [compV, ιV, sub_apply, hpV_mem v.2]
    rwa [hsub, sub_nonneg] at h0
  let ξV : V := ⟨ξ, Submodule.subset_span (Set.mem_union_left _ (Set.mem_union_left _ rfl))⟩
  have hξV : ‖ξV‖ = 1 := hξ
  let σV : CStarStrategy X Y A B (V →L[ℂ] V) :=
    { alice := fun x ↦
        { effect := fun a ↦ compV ((σ₀.alice x).effect a)
          nonneg := fun a ↦ hcomp_nonneg ((σ₀.alice x).nonneg a)
          sum_effect := by
            have hs : (∑ a : A, compV ((σ₀.alice x).effect a)) =
                compV (∑ a : A, (σ₀.alice x).effect a) := by
              ext v; simp [compV, sum_apply, map_sum]
            rw [hs, (σ₀.alice x).sum_effect, hcomp_one] }
      bob := fun y ↦
        { effect := fun b ↦ compV ((σ₀.bob y).effect b)
          nonneg := fun b ↦ hcomp_nonneg ((σ₀.bob y).nonneg b)
          sum_effect := by
            have hs : (∑ b : B, compV ((σ₀.bob y).effect b)) =
                compV (∑ b : B, (σ₀.bob y).effect b) := by
              ext v; simp [compV, sum_apply, map_sum]
            rw [hs, (σ₀.bob y).sum_effect, hcomp_one] }
      state := vectorAlgState ξV hξV }
  have hσV_st : σV.IsStateAlmostCommuting δ := fun x y ↦ by
    have heq : ∀ a b, σV.state (commBracket ((σV.alice x).effect a) ((σV.bob y).effect b)) =
        σ₀.state (commBracket ((σ₀.alice x).effect a) ((σ₀.bob y).effect b)) := fun a b ↦ by
      set E := (σ₀.alice x).effect a
      set F := (σ₀.bob y).effect b
      have hEξ : E ξ ∈ V := Submodule.subset_span <| Set.mem_union_left _ <| Set.mem_union_right _
        ⟨(x, a, ⟨1, by omega⟩), by simp [krylovA, E]⟩
      have hFξ : F ξ ∈ V := Submodule.subset_span <| Set.mem_union_right _
        ⟨(y, b, ⟨1, by omega⟩), by simp [krylovB, F]⟩
      have hEF : ⟪ξV, (compV E * compV F) ξV⟫_ℂ = ⟪ξ, (E * F) ξ⟫_ℂ := by
        change ⟪ξV, pV (E (ιV (pV (F ξ))))⟫_ℂ = ⟪ξ, E (F ξ)⟫_ℂ
        rw [hinner_pV, hpV_mem hFξ]; rfl
      have hFE : ⟪ξV, (compV F * compV E) ξV⟫_ℂ = ⟪ξ, (F * E) ξ⟫_ℂ := by
        change ⟪ξV, pV (F (ιV (pV (E ξ))))⟫_ℂ = ⟪ξ, F (E ξ)⟫_ℂ
        rw [hinner_pV, hpV_mem hEξ]; rfl
      rw [hstate₀]
      change ⟪ξV, (compV E * compV F - compV F * compV E) ξV⟫_ℂ = ⟪ξ, (E * F - F * E) ξ⟫_ℂ
      rw [sub_apply, sub_apply, inner_sub_right, inner_sub_right, hEF, hFE]
    simpa only [heq] using hσ₀ x y
  have hterm : ∀ x y a b,
      |(σ₀.state (ozawaProd ((σ₀.alice x).effect a) ((σ₀.bob y).effect b))).re -
        (σV.state (ozawaProd ((σV.alice x).effect a) ((σV.bob y).effect b))).re| ≤ 4 * η := by
    intro x y a b
    have hιn : ∀ u : V, ‖ιV u‖ = ‖u‖ := fun _ ↦ rfl
    have hpι : ∀ u : V, pV (ιV u) = u := fun u ↦ hpV_mem u.2
    have hA1 : (σ₀.alice x).effect a ≤ 1 := (σ₀.alice x).effect_le_one a
    have hB1 : (σ₀.bob y).effect b ≤ 1 := (σ₀.bob y).effect_le_one b
    have h1 := norm_quad_compress_sub_le ιV pV hιn hinner_pV hpι hη.le hP_approx hξV
      ((σ₀.alice x).nonneg a) hA1 ((σ₀.bob y).nonneg b) hB1 fun j hj ↦ by
        have hm : (((σ₀.alice x).effect a) ^ j) ξ ∈ V := Submodule.subset_span <|
          Set.mem_union_left _ <| Set.mem_union_right _
            ⟨(x, a, ⟨j, Nat.lt_succ_of_le (hj.trans (le_max_left _ _))⟩), rfl⟩
        exact congrArg Subtype.val (hpV_mem hm)
    have h2 := norm_quad_compress_sub_le ιV pV hιn hinner_pV hpι hη.le hP_approx hξV
      ((σ₀.bob y).nonneg b) hB1 ((σ₀.alice x).nonneg a) hA1 fun j hj ↦ by
        have hm : (((σ₀.bob y).effect b) ^ j) ξ ∈ V := Submodule.subset_span <|
          Set.mem_union_right _
            ⟨(y, b, ⟨j, Nat.lt_succ_of_le (hj.trans (le_max_left _ _))⟩), rfl⟩
        exact congrArg Subtype.val (hpV_mem hm)
    rw [← Complex.sub_re]
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [hstate₀]
    change ‖⟪ξ, ozawaProd ((σ₀.alice x).effect a) ((σ₀.bob y).effect b) ξ⟫_ℂ -
      ⟪ξV, ozawaProd (compV ((σ₀.alice x).effect a)) (compV ((σ₀.bob y).effect b)) ξV⟫_ℂ‖ ≤ 4 * η
    simp only [ozawaProd, smul_apply, add_apply, inner_smul_right, inner_add_right]
    rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity),
      add_sub_add_comm]
    refine (mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add h1 h2))
      (by positivity)).trans_eq ?_
    ring
  have hdiff : σ_in.winProb G - σV.winProb G ≤ ε := by
    rw [← hval₀]
    simp only [CStarStrategy.winProb, ← Finset.sum_sub_distrib, ← mul_sub]
    calc _ ≤ ∑ x : X, ∑ y : Y, (G.questions (x, y)).toReal * (cardAB * (4 * η)) := by
          refine Finset.sum_le_sum fun x _ ↦ Finset.sum_le_sum fun y _ ↦
            mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
          calc _ ≤ ∑ _a : A, ∑ _b : B, (4 * η) :=
                Finset.sum_le_sum fun a _ ↦ Finset.sum_le_sum fun b _ ↦ by
                  split_ifs
                  · exact (le_abs_self _).trans (hterm x y a b)
                  · rw [sub_zero]; positivity
            _ = cardAB * (4 * η) := by simp [cardAB, mul_assoc]
      _ = (∑ p : X × Y, (G.questions p).toReal) * (cardAB * (4 * η)) := by
          simp only [← Finset.sum_mul, ← Fintype.sum_prod_type']
      _ = cardAB * (4 * η) := by
          rw [← ENNReal.toReal_sum fun _ _ ↦ G.questions.apply_ne_top _,
            ← _root_.tsum_fintype (L := SummationFilter.unconditional _),
            G.questions.tsum_coe, ENNReal.toReal_one, one_mul]
      _ ≤ ε := by
          have hc_nn : 0 ≤ cardAB := by positivity
          dsimp only [η]
          have hd_pos : 0 < 4 * (cardAB + 1) := by positivity
          rw [mul_div_assoc', mul_div_assoc', div_le_iff₀ hd_pos]
          nlinarith
  exact ⟨V, inferInstance, inferInstance, inferInstance, inferInstance, σV, hσV_st, hdiff⟩

/-- **Unconditional equality of general and finite-dimensional state-almost commuting values**:
for every finite two-prover game `G` and every `δ > 0`,
`stateAlmostCommutingValue G δ = finDimStateAlmostCommutingValue G δ`. -/
theorem stateAlmostCommutingValue_eq_finDimStateAlmostCommutingValue [Nonempty A] [Nonempty B]
    (G : TwoProverGame X Y A B) {δ : ℝ} (hδ : 0 < δ) :
    stateAlmostCommutingValue G δ = finDimStateAlmostCommutingValue G δ := by
  classical
  let a₀ : A := Classical.arbitrary A
  let b₀ : B := Classical.arbitrary B
  let H₁ := ℂ
  let e₀ : H₁ := 1
  have he₀ : ‖e₀‖ = 1 := norm_one
  let τ : CStarStrategy X Y A B (H₁ →L[ℂ] H₁) :=
    { alice := fun _ ↦ Measurement.const a₀
      bob := fun _ ↦ Measurement.const b₀
      state := vectorAlgState e₀ he₀ }
  have hτc : τ.IsCommuting := fun _ _ a b ↦ by
    change Commute (if a = a₀ then (1 : H₁ →L[ℂ] H₁) else 0)
      (if b = b₀ then (1 : H₁ →L[ℂ] H₁) else 0)
    split_ifs <;> simp [Commute, SemiconjBy]
  have hτ : τ.IsStateAlmostCommuting δ := (hτc.toOpAlmostCommuting hδ).toState
  have hbdd_fd : BddAbove { v : ℝ | ∃ (H : Type) (_ : NormedAddCommGroup H)
      (_ : InnerProductSpace ℂ H) (_ : CompleteSpace H) (_ : FiniteDimensional ℂ H)
      (σ : CStarStrategy X Y A B (H →L[ℂ] H)),
      σ.IsStateAlmostCommuting δ ∧ v = σ.winProb G } :=
    ⟨1, by rintro _ ⟨H, i1, i2, i3, _, σ, _, rfl⟩; exact (σ.winProb_mem_Icc G).2⟩
  have hbdd_co : BddAbove { v : ℝ | ∃ (H : Type) (_ : NormedAddCommGroup H)
      (_ : InnerProductSpace ℂ H) (_ : CompleteSpace H)
      (σ : CStarStrategy X Y A B (H →L[ℂ] H)),
      σ.IsStateAlmostCommuting δ ∧ v = σ.winProb G } :=
    ⟨1, by rintro _ ⟨H, i1, i2, i3, σ, _, rfl⟩; exact (σ.winProb_mem_Icc G).2⟩
  have hne_fd : { v : ℝ | ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (_ : CompleteSpace H) (_ : FiniteDimensional ℂ H)
      (σ : CStarStrategy X Y A B (H →L[ℂ] H)),
      σ.IsStateAlmostCommuting δ ∧ v = σ.winProb G }.Nonempty :=
    ⟨τ.winProb G, H₁, inferInstance, inferInstance, inferInstance, inferInstance, τ, hτ, rfl⟩
  refine le_antisymm ?_ (csSup_le_csSup hbdd_co hne_fd
    fun _ ⟨H, i1, i2, i3, _, σ, h, hv⟩ ↦ ⟨H, i1, i2, i3, σ, h, hv⟩)
  refine csSup_le ⟨τ.winProb G, H₁, inferInstance, inferInstance, inferInstance, τ, hτ, rfl⟩ ?_
  rintro _ ⟨H_in, _, _, _, σ_in, hst_in, rfl⟩
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  obtain ⟨V, i1, i2, i3, i4, σV, hσV_st, hdiff⟩ :=
    exists_finDim_stateAlmostCommuting_approx G σ_in hst_in hε
  have hV_le : σV.winProb G ≤ finDimStateAlmostCommutingValue G δ :=
    le_csSup hbdd_fd ⟨V, i1, i2, i3, i4, σV, hσV_st, rfl⟩
  linarith

end GameValues

end CslibFrontier.PCP

end
