/-
Copyright (c) 2026 Formal Papers contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Papers contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.TwoProverGame.CommutingValue
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute

/-!
# Almost-Commuting Operator Strategies and Ozawa's Symmetric Product

In the `δ`-almost commuting operator relaxation of two-prover one-round nonlocal games (Fox,
Goldbring, and Hart, building on Ozawa), Alice's and Bob's measurement effects `P_x^a`
and `Q_y^b` in a unital C⋆-algebra `𝒜` satisfy `‖P_x^a Q_y^b - Q_y^b P_x^a‖ < δ` rather than exact
commutation. Because `P_x^a Q_y^b` need not be positive or self-adjoint when `P_x^a` and `Q_y^b` do
not commute, joint outcome probabilities are defined via **Ozawa's symmetric product**:

`P • Q = (1 / 2) • (√P * Q * √P + √Q * P * √Q)`

(`Cslib.Quantum.ozawaProduct`). For any two nonnegative elements `P, Q ≥ 0` in a C⋆-algebra,
`P • Q ≥ 0`; for any two measurements `{P_a}` and `{Q_b}`, `∑_{a, b} (P_a • Q_b) = 1`, so
`Re φ(P_a • Q_b)` always defines a valid probability mass function
(`AlmostCommutingStrategy.answers`);
and whenever `P` and `Q` commute, `P • Q = P * Q` (`ozawaProduct_eq_mul_of_commute`), showing that
every `CommutingStrategy` is a `δ`-almost commuting strategy (`CommutingStrategy.toAlmostCommuting`)
with identical winning probability (`commutingValue_le_deltaOpCommutingValue`).

## Main definitions

* `Cslib.Quantum.ozawaProduct`: Ozawa's symmetric positive product `(√P Q √P + √Q P √Q) / 2`.
* `Cslib.PCP.AlmostCommutingStrategy`: a `δ`-almost commuting operator strategy in `𝒜`.
* `Cslib.PCP.AlmostCommutingStrategy.answers`: joint outcome `PMF (A × B)` via `ozawaProduct`.
* `Cslib.PCP.TwoProverGame.almostCommutingWinProb`: winning probability of an almost-commuting
  strategy.
* `Cslib.PCP.TwoProverGame.deltaOpCommutingValue`: the `(δ, op)`-almost commuting value of a game.

## Main results

* `Cslib.Quantum.ozawaProduct_nonneg`: `0 ≤ P • Q` for `0 ≤ P` and `0 ≤ Q`.
* `Cslib.Quantum.ozawaProduct_eq_mul_of_commute`: `P • Q = P * Q` when `0 ≤ P`, `0 ≤ Q`, and
  `Commute P Q`.
* `Cslib.Quantum.Measurement.sum_ozawaProduct`: `∑ a, ∑ b, (M.effect a • N.effect b) = 1`.
* `Cslib.PCP.TwoProverGame.commutingValue_le_deltaOpCommutingValue`: `G.commutingValue ≤
  G.deltaOpCommutingValue δ` for every `0 < δ`.
-/

public section

namespace Cslib.Quantum

section OzawaProduct

variable {𝒜 : Type*} [CStarAlgebra 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜]

/-- **Ozawa's symmetric product** `(1 / 2) • (√P * Q * √P + √Q * P * √Q)` of two observables in a
unital C⋆-algebra. -/
noncomputable def ozawaProduct (P Q : 𝒜) : 𝒜 :=
  ((2⁻¹ : ℝ) : ℂ) • (CFC.sqrt P * Q * CFC.sqrt P + CFC.sqrt Q * P * CFC.sqrt Q)

/-- Ozawa's symmetric product is symmetric in its two arguments. -/
theorem ozawaProduct_comm (P Q : 𝒜) : ozawaProduct P Q = ozawaProduct Q P := by
  simp only [ozawaProduct, add_comm]

/-- For nonnegative elements `0 ≤ P` and `0 ≤ Q`, `0 ≤ ozawaProduct P Q`. -/
theorem ozawaProduct_nonneg {P Q : 𝒜} (hP : 0 ≤ P) (hQ : 0 ≤ Q) :
    0 ≤ ozawaProduct P Q := by
  have hsP : IsSelfAdjoint (CFC.sqrt P) := (CFC.sqrt_nonneg P).isSelfAdjoint
  have hsQ : IsSelfAdjoint (CFC.sqrt Q) := (CFC.sqrt_nonneg Q).isSelfAdjoint
  have h1 : 0 ≤ CFC.sqrt P * Q * CFC.sqrt P := by
    have heq : CFC.sqrt P * Q * CFC.sqrt P =
        star (CFC.sqrt Q * CFC.sqrt P) * (CFC.sqrt Q * CFC.sqrt P) := by
      rw [star_mul, hsP.star_eq, hsQ.star_eq]
      calc
        CFC.sqrt P * Q * CFC.sqrt P
            = CFC.sqrt P * (CFC.sqrt Q * CFC.sqrt Q) * CFC.sqrt P := by
              rw [CFC.sqrt_mul_sqrt_self Q hQ]
        _ = (CFC.sqrt P * CFC.sqrt Q) * (CFC.sqrt Q * CFC.sqrt P) := by simp [mul_assoc]
    rw [heq]
    exact star_mul_self_nonneg _
  have h2 : 0 ≤ CFC.sqrt Q * P * CFC.sqrt Q := by
    have heq : CFC.sqrt Q * P * CFC.sqrt Q =
        star (CFC.sqrt P * CFC.sqrt Q) * (CFC.sqrt P * CFC.sqrt Q) := by
      rw [star_mul, hsP.star_eq, hsQ.star_eq]
      calc
        CFC.sqrt Q * P * CFC.sqrt Q
            = CFC.sqrt Q * (CFC.sqrt P * CFC.sqrt P) * CFC.sqrt Q := by
              rw [CFC.sqrt_mul_sqrt_self P hP]
        _ = (CFC.sqrt Q * CFC.sqrt P) * (CFC.sqrt P * CFC.sqrt Q) := by simp [mul_assoc]
    rw [heq]
    exact star_mul_self_nonneg _
  rw [ozawaProduct, Complex.coe_smul]
  exact smul_nonneg (by positivity : (0 : ℝ) ≤ 2⁻¹) (add_nonneg h1 h2)

/-- When `0 ≤ P`, `0 ≤ Q`, and `Commute P Q`, Ozawa's symmetric product coincides with `P * Q`. -/
theorem ozawaProduct_eq_mul_of_commute {P Q : 𝒜} (hP : 0 ≤ P) (hQ : 0 ≤ Q)
    (hcomm : Commute P Q) : ozawaProduct P Q = P * Q := by
  have hcP : Commute (CFC.sqrt P) Q := by
    rw [CFC.sqrt_eq_real_sqrt P hP]
    exact hP.isSelfAdjoint.commute_cfcₙ hcomm Real.sqrt
  have hcQ : Commute (CFC.sqrt Q) P := by
    rw [CFC.sqrt_eq_real_sqrt Q hQ]
    exact hQ.isSelfAdjoint.commute_cfcₙ hcomm.symm Real.sqrt
  have h1 : CFC.sqrt P * Q * CFC.sqrt P = P * Q := by
    calc
      CFC.sqrt P * Q * CFC.sqrt P = Q * CFC.sqrt P * CFC.sqrt P := by rw [hcP.eq]
      _ = Q * (CFC.sqrt P * CFC.sqrt P) := by rw [mul_assoc]
      _ = Q * P := by rw [CFC.sqrt_mul_sqrt_self P hP]
      _ = P * Q := hcomm.symm.eq
  have h2 : CFC.sqrt Q * P * CFC.sqrt Q = P * Q := by
    calc
      CFC.sqrt Q * P * CFC.sqrt Q = P * CFC.sqrt Q * CFC.sqrt Q := by rw [hcQ.eq]
      _ = P * (CFC.sqrt Q * CFC.sqrt Q) := by rw [mul_assoc]
      _ = P * Q := by rw [CFC.sqrt_mul_sqrt_self Q hQ]
  rw [ozawaProduct, h1, h2]
  module

/-- Summing `ozawaProduct (M.effect a) (N.effect b)` over all outcome pairs `(a, b)` of two
measurements yields `1`. -/
theorem Measurement.sum_ozawaProduct {α β : Type*} [Fintype α] [Fintype β]
    (M : Measurement α 𝒜) (N : Measurement β 𝒜) :
    ∑ a : α, ∑ b : β, ozawaProduct (M.effect a) (N.effect b) = 1 := by
  simp only [ozawaProduct]
  have h1 :
      (∑ a : α, ∑ b : β, CFC.sqrt (M.effect a) * N.effect b * CFC.sqrt (M.effect a)) = 1 := by
    calc
      (∑ a : α, ∑ b : β, CFC.sqrt (M.effect a) * N.effect b * CFC.sqrt (M.effect a))
          = ∑ a : α, CFC.sqrt (M.effect a) * (∑ b : β, N.effect b) * CFC.sqrt (M.effect a) := by
            refine Finset.sum_congr rfl fun a _ ↦ ?_
            simp [Finset.mul_sum, Finset.sum_mul]
      _ = ∑ a : α, M.effect a := by
        refine Finset.sum_congr rfl fun a _ ↦ ?_
        rw [N.sum_effect, mul_one, CFC.sqrt_mul_sqrt_self _ (M.nonneg a)]
      _ = 1 := M.sum_effect
  have h2 :
      (∑ a : α, ∑ b : β, CFC.sqrt (N.effect b) * M.effect a * CFC.sqrt (N.effect b)) = 1 := by
    rw [Finset.sum_comm]
    calc
      (∑ b : β, ∑ a : α, CFC.sqrt (N.effect b) * M.effect a * CFC.sqrt (N.effect b))
          = ∑ b : β, CFC.sqrt (N.effect b) * (∑ a : α, M.effect a) * CFC.sqrt (N.effect b) := by
            refine Finset.sum_congr rfl fun b _ ↦ ?_
            simp [Finset.mul_sum, Finset.sum_mul]
      _ = ∑ b : β, N.effect b := by
        refine Finset.sum_congr rfl fun b _ ↦ ?_
        rw [M.sum_effect, mul_one, CFC.sqrt_mul_sqrt_self _ (N.nonneg b)]
      _ = 1 := N.sum_effect
  simp_rw [← Finset.smul_sum, Finset.sum_add_distrib, h1, h2]
  module

end OzawaProduct

end Cslib.Quantum

namespace Cslib.PCP

open Finset Quantum

/-- A **`δ`-almost commuting operator strategy** in a unital C⋆-algebra `𝒜`: a state `φ`,
measurements `{P_x^a}` and `{Q_y^b}` for Alice and Bob, and summed operator-norm commutator bound
`∑_{a, b} ‖P_x^a Q_y^b - Q_y^b P_x^a‖ < δ` for every question pair `(x, y)`. -/
@[ext]
structure AlmostCommutingStrategy (X Y A B 𝒜 : Type*) (δ : ℝ) [Fintype A] [Fintype B]
    [CStarAlgebra 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜] where
  /-- The shared algebraic state. -/
  state : AlgState 𝒜
  /-- Alice's measurement on question `x`. -/
  alice : X → Measurement A 𝒜
  /-- Bob's measurement on question `y`. -/
  bob : Y → Measurement B 𝒜
  /-- Summed `(δ, op)`-almost commutation in operator norm. -/
  almost_commute : ∀ x y,
    (∑ a, ∑ b,
      ‖(alice x).effect a * (bob y).effect b - (bob y).effect b * (alice x).effect a‖) < δ

namespace AlmostCommutingStrategy

variable {X Y A B 𝒜 : Type*} {δ : ℝ} [Fintype A] [Fintype B]
  [CStarAlgebra 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜]

/-- Outcome probability `Re φ(P_x^a • Q_y^b)` defined via Ozawa's symmetric product. -/
noncomputable def prob (S : AlmostCommutingStrategy X Y A B 𝒜 δ) (x : X) (y : Y)
    (a : A) (b : B) : ℝ :=
  (S.state (ozawaProduct ((S.alice x).effect a) ((S.bob y).effect b))).re

/-- Outcome probabilities are always nonnegative. -/
theorem prob_nonneg (S : AlmostCommutingStrategy X Y A B 𝒜 δ) (x : X) (y : Y)
    (a : A) (b : B) : 0 ≤ S.prob x y a b :=
  S.state.re_apply_nonneg (ozawaProduct_nonneg ((S.alice x).nonneg a) ((S.bob y).nonneg b))

/-- Outcome probabilities sum to `1` over `(a, b) : A × B`. -/
theorem sum_prob (S : AlmostCommutingStrategy X Y A B 𝒜 δ) (x : X) (y : Y) :
    ∑ a : A, ∑ b : B, S.prob x y a b = 1 := by
  simp only [prob, ← Complex.re_sum, ← map_sum, Measurement.sum_ozawaProduct,
    AlgState.map_one, Complex.one_re]

/-- Joint answer distribution `PMF (A × B)` on questions `(x, y)`. -/
noncomputable def answers (S : AlmostCommutingStrategy X Y A B 𝒜 δ) (x : X) (y : Y) :
    PMF (A × B) :=
  PMF.ofFintype (fun ab ↦ ENNReal.ofReal (S.prob x y ab.1 ab.2)) <| by
    rw [← ENNReal.ofReal_sum_of_nonneg fun ab _ ↦ S.prob_nonneg x y ab.1 ab.2,
      Fintype.sum_prod_type, S.sum_prob, ENNReal.ofReal_one]

/-- Probability assigned by `answers` to `(a, b)`. -/
theorem answers_apply (S : AlmostCommutingStrategy X Y A B 𝒜 δ) (x : X) (y : Y)
    (a : A) (b : B) :
    S.answers x y (a, b) = ENNReal.ofReal (S.prob x y a b) := by
  rw [answers, PMF.ofFintype_apply]

end AlmostCommutingStrategy

/-- Every exact commuting-operator strategy is a `δ`-almost commuting strategy for any `δ > 0`. -/
def CommutingStrategy.toAlmostCommuting {X Y A B 𝒜 : Type*} {δ : ℝ} [Fintype A] [Fintype B]
    [CStarAlgebra 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜] (hδ : 0 < δ)
    (S : CommutingStrategy X Y A B 𝒜) : AlmostCommutingStrategy X Y A B 𝒜 δ where
  state := S.state
  alice := S.alice
  bob := S.bob
  almost_commute x y := by
    have h0 : (∑ a : A, ∑ b : B,
        ‖(S.alice x).effect a * (S.bob y).effect b -
          (S.bob y).effect b * (S.alice x).effect a‖) = 0 := by
      refine Finset.sum_eq_zero fun a _ ↦ Finset.sum_eq_zero fun b _ ↦ ?_
      rw [(S.commute x y a b).eq, sub_self, norm_zero]
    rw [h0]
    exact hδ

/-- Embedding an exact commuting strategy into `AlmostCommutingStrategy` preserves joint outcome
probabilities. -/
@[simp]
theorem CommutingStrategy.prob_toAlmostCommuting {X Y A B 𝒜 : Type*} {δ : ℝ}
    [Fintype A] [Fintype B] [CStarAlgebra 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
    (hδ : 0 < δ) (S : CommutingStrategy X Y A B 𝒜) (x : X) (y : Y) (a : A) (b : B) :
    (S.toAlmostCommuting hδ).prob x y a b = S.prob x y a b := by
  simp only [AlmostCommutingStrategy.prob, CommutingStrategy.prob, toAlmostCommuting]
  rw [ozawaProduct_eq_mul_of_commute ((S.alice x).nonneg a) ((S.bob y).nonneg b)
    (S.commute x y a b)]

/-- Embedding an exact commuting strategy into `AlmostCommutingStrategy` preserves `answers`. -/
@[simp]
theorem CommutingStrategy.answers_toAlmostCommuting {X Y A B 𝒜 : Type*} {δ : ℝ}
    [Fintype A] [Fintype B] [CStarAlgebra 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
    (hδ : 0 < δ) (S : CommutingStrategy X Y A B 𝒜) (x : X) (y : Y) :
    (S.toAlmostCommuting hδ).answers x y = S.answers x y := by
  ext ⟨a, b⟩
  rw [AlmostCommutingStrategy.answers_apply, CommutingStrategy.answers_apply,
    S.prob_toAlmostCommuting hδ]

namespace TwoProverGame

variable {X Y A B : Type} [Fintype A] [Fintype B] (G : TwoProverGame X Y A B)

/-- Winning probability of a `δ`-almost commuting strategy `S` in `G`. -/
noncomputable def almostCommutingWinProb {𝒜 : Type*} {δ : ℝ} [CStarAlgebra 𝒜]
    [PartialOrder 𝒜] [StarOrderedRing 𝒜] (S : AlmostCommutingStrategy X Y A B 𝒜 δ) : ℝ :=
  G.answersWinProb S.answers

/-- Winning probabilities of almost-commuting strategies are nonnegative. -/
theorem almostCommutingWinProb_nonneg {𝒜 : Type*} {δ : ℝ} [CStarAlgebra 𝒜]
    [PartialOrder 𝒜] [StarOrderedRing 𝒜] (S : AlmostCommutingStrategy X Y A B 𝒜 δ) :
    0 ≤ G.almostCommutingWinProb S :=
  G.answersWinProb_nonneg _

/-- Winning probabilities of almost-commuting strategies are at most `1`. -/
theorem almostCommutingWinProb_le_one {𝒜 : Type*} {δ : ℝ} [CStarAlgebra 𝒜]
    [PartialOrder 𝒜] [StarOrderedRing 𝒜] (S : AlmostCommutingStrategy X Y A B 𝒜 δ) :
    G.almostCommutingWinProb S ≤ 1 :=
  G.answersWinProb_le_one _

/-- Explicit sum formula for `almostCommutingWinProb` on finite question alphabets. -/
theorem almostCommutingWinProb_eq_sum {𝒜 : Type*} {δ : ℝ} [Fintype X] [Fintype Y]
    [∀ x y a b, Decidable (G.accepts x y a b)] [CStarAlgebra 𝒜] [PartialOrder 𝒜]
    [StarOrderedRing 𝒜] (S : AlmostCommutingStrategy X Y A B 𝒜 δ) :
    G.almostCommutingWinProb S = ∑ x, ∑ y, (G.questions (x, y)).toReal * ∑ a, ∑ b,
      if G.accepts x y a b then S.prob x y a b else 0 :=
  G.answersWinProb_eq_sum_of_ofReal _ _ S.prob_nonneg S.answers_apply

/-- The `(δ, op)`-almost commuting value `val^{co}_{δ, op}(G)` of a two-prover game: supremum of
`almostCommutingWinProb` over all unital C⋆-algebras `𝒜` and `δ`-almost commuting strategies. -/
noncomputable def deltaOpCommutingValue (δ : ℝ) : ℝ :=
  ⨆ (𝒜 : CStarAlg) (S : AlmostCommutingStrategy X Y A B 𝒜.carrier δ),
    G.almostCommutingWinProb S

/-- `deltaOpCommutingValue` is always nonnegative. -/
theorem deltaOpCommutingValue_nonneg (δ : ℝ) : 0 ≤ G.deltaOpCommutingValue δ :=
  Real.iSup_nonneg fun _ ↦ Real.iSup_nonneg fun S ↦ G.almostCommutingWinProb_nonneg S

/-- `deltaOpCommutingValue` is at most `1`. -/
theorem deltaOpCommutingValue_le_one (δ : ℝ) : G.deltaOpCommutingValue δ ≤ 1 :=
  Real.iSup_le
    (fun _ ↦ Real.iSup_le (fun S ↦ G.almostCommutingWinProb_le_one S) zero_le_one)
    zero_le_one

/-- Every `δ`-almost commuting strategy in a unital C⋆-algebra in `Type` achieves at most
`G.deltaOpCommutingValue δ`. -/
theorem almostCommutingWinProb_le_deltaOpCommutingValue {𝒜 : Type} {δ : ℝ} [CStarAlgebra 𝒜]
    [PartialOrder 𝒜] [StarOrderedRing 𝒜] (S : AlmostCommutingStrategy X Y A B 𝒜 δ) :
    G.almostCommutingWinProb S ≤ G.deltaOpCommutingValue δ := by
  have hb : ∀ 𝒜₀ : CStarAlg, BddAbove
      (Set.range fun S₀ : AlmostCommutingStrategy X Y A B 𝒜₀.carrier δ ↦
        G.almostCommutingWinProb S₀) :=
    fun 𝒜₀ ↦ ⟨1, by rintro _ ⟨S₀, rfl⟩; exact G.almostCommutingWinProb_le_one S₀⟩
  have hb' : BddAbove (Set.range fun 𝒜₀ : CStarAlg ↦
      ⨆ S₀ : AlmostCommutingStrategy X Y A B 𝒜₀.carrier δ, G.almostCommutingWinProb S₀) :=
    ⟨1, by
      rintro _ ⟨𝒜₀, rfl⟩
      exact Real.iSup_le (fun S₀ ↦ G.almostCommutingWinProb_le_one S₀) zero_le_one⟩
  exact (le_ciSup (hb ⟨𝒜⟩) S).trans (le_ciSup hb' ⟨𝒜⟩)

/-- For every `δ > 0`, the commuting-operator value is bounded above by the `(δ, op)`-almost
commuting value: `G.commutingValue ≤ G.deltaOpCommutingValue δ`. -/
theorem commutingValue_le_deltaOpCommutingValue {δ : ℝ} (hδ : 0 < δ) :
    G.commutingValue ≤ G.deltaOpCommutingValue δ := by
  refine G.commutingValue_le (G.deltaOpCommutingValue_nonneg δ) fun 𝒜 _ _ _ S ↦ ?_
  have heq : G.commutingWinProb S = G.almostCommutingWinProb (S.toAlmostCommuting hδ) := by
    rw [commutingWinProb, almostCommutingWinProb]
    exact congrArg G.answersWinProb
      (funext fun x ↦ funext fun y ↦ (S.answers_toAlmostCommuting hδ x y).symm)
  rw [heq]
  exact G.almostCommutingWinProb_le_deltaOpCommutingValue (S.toAlmostCommuting hδ)

end TwoProverGame

end Cslib.PCP
