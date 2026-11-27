module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.QMA

import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Quantum Witness Counting (`#BQP`) and Gapped Projector Verifiers

For a polynomial-time uniform family of quantum verifiers
`V : Cslib.Quantum.UniformVerifierFamily`, its **witness acceptance trace** on an input word
`x : List Bool` is the sum of acceptance probabilities over all computational-basis witness states
`|z⟩` (`z : Fin (V.witnessLength x.length) → Bool`). Because `V.acceptProb x ψ` is the squared
Euclidean norm of a linear map evaluated at `ψ` on the accepting measurement outcomes, Parseval's
identity implies that this sum equals the trace of the verifier's positive semidefinite acceptance
operator and is invariant under changing from the computational basis `ket` to any orthonormal
basis of `Qubits (V.witnessLength x.length)`, proved under standard Lean axioms.

## Main definitions

* `witnessAcceptTrace`: computational-basis acceptance trace
  `∑ z, V.acceptProb x (ket z)` of a `UniformVerifierFamily` on input `x`.
* `SharpBQP`: the quantum witness-counting class `#BQP` of functions `f : α → ℕ` whose
  values are approximated within `1 / 3` by `witnessAcceptTrace V (enc a)` for a polynomial-time
  uniform quantum verifier family `V`.
* `IsGappedProjectorVerifier`: predicate that on every input `a : α`, the witness Hilbert
  space `Qubits (V.witnessLength (enc a).length)` admits a subspace `W` of dimension `f a` on which
  unit states accept with probability at least `1 - ε` while unit states in `Wᗮ` accept with
  probability at most `ε`, with `0 ≤ ε` and `2 ^ (V.witnessLength (enc a).length) * ε ≤ 1 / 3`.

## Main results

* `sum_acceptProb_orthonormalBasis_eq_witnessAcceptTrace`: for every finite-index
  orthonormal basis `b` of `Qubits (V.witnessLength x.length)`,
  `∑ i, V.acceptProb x (b i) = witnessAcceptTrace V x`.
* `IsGappedProjectorVerifier.mem_QMA`: if `V` is a gapped projector verifier for `f`, then
  the positivity decision problem `{a | 0 < f a}` belongs to `Cslib.Complexity.QMA enc`.
* `IsGappedProjectorVerifier.mem_SharpBQP`: if `V` is a gapped projector verifier for `f`,
  then `f` belongs to `SharpBQP enc`.
* `eq_of_witnessAcceptTrace_approx`: an integer count `f a : ℕ` approximated within `1 / 3`
  by `witnessAcceptTrace V (enc a)` is uniquely determined by `V`.

## Tags

quantum complexity, QMA, SharpBQP, quantum witness counting, Parseval identity
-/

public section

open scoped InnerProductSpace
open Cslib Cslib.Quantum Cslib.Complexity

namespace CslibFrontier.Complexity

section Trace

/-- The **witness acceptance trace** of a uniform quantum verifier family `V` on input word `x`:
the sum of `V.acceptProb x (ket z)` over all computational-basis witness strings
`z : Fin (V.witnessLength x.length) → Bool`. -/
noncomputable def witnessAcceptTrace (V : UniformVerifierFamily) (x : List Bool) : ℝ :=
  ∑ z : Fin (V.witnessLength x.length) → Bool, V.acceptProb x (ket z)

/-- The witness acceptance trace is always nonnegative. -/
theorem witnessAcceptTrace_nonneg (V : UniformVerifierFamily) (x : List Bool) :
    0 ≤ witnessAcceptTrace V x :=
  Finset.sum_nonneg fun z _ ↦ V.acceptProb_nonneg x (ket z)

/-- The witness acceptance trace on input `x` is at most the witness Hilbert-space dimension
`2 ^ (V.witnessLength x.length)`. -/
theorem witnessAcceptTrace_le_two_pow (V : UniformVerifierFamily) (x : List Bool) :
    witnessAcceptTrace V x ≤ (2 : ℝ) ^ (V.witnessLength x.length) := by
  unfold witnessAcceptTrace
  calc ∑ z : Fin (V.witnessLength x.length) → Bool, V.acceptProb x (ket z)
      ≤ ∑ _z : Fin (V.witnessLength x.length) → Bool, (1 : ℝ) := by
        refine Finset.sum_le_sum fun z _ ↦ ?_
        simpa only [norm_ket, one_pow] using V.acceptProb_le x (ket z)
    _ = (2 : ℝ) ^ (V.witnessLength x.length) := by
        simp [Fintype.card_pi, Fintype.card_bool]

/-- Parseval's identity for any linear functional `L : Qubits m →ₗ[ℂ] ℂ`: summing `‖L (b i)‖ ^ 2`
over any orthonormal basis `b` of `Qubits m` yields `∑ z, ‖L (ket z)‖ ^ 2`. -/
private theorem sum_norm_sq_orthonormalBasis_eq_ket {m : ℕ} {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℂ (Qubits m)) (L : Qubits m →ₗ[ℂ] ℂ) :
    (∑ i : ι, ‖L (b i)‖ ^ 2) = ∑ z : Fin m → Bool, ‖L (ket z)‖ ^ 2 := by
  -- Represent `L` as `⟪v, ·⟫_ℂ` with `v = WithLp.toLp 2 (fun z ↦ star (L (ket z)))`.
  let v : Qubits m := WithLp.toLp 2 fun z ↦ star (L (ket z))
  have hLv : ∀ ψ : Qubits m, L ψ = ⟪v, ψ⟫_ℂ := by
    intro ψ
    conv_lhs => rw [← sum_smul_ket ψ, map_sum]
    rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct]
    refine Finset.sum_congr rfl fun z _ ↦ ?_
    rw [map_smul, smul_eq_mul, WithLp.ofLp_toLp, Pi.star_apply, star_star, mul_comm]
  simp_rw [hLv]
  have hnorm_b : (∑ i : ι, ‖⟪v, b i⟫_ℂ‖ ^ 2) = ‖v‖ ^ 2 := by
    have hparseval := b.sum_inner_mul_inner v v
    -- `∑ i, ⟪v, b i⟫ * ⟪b i, v⟫ = ⟪v, v⟫`
    have hre : (∑ i : ι, (⟪v, b i⟫_ℂ * ⟪b i, v⟫_ℂ).re) = RCLike.re ⟪v, v⟫_ℂ := by
      rw [← Complex.re_sum, hparseval]
      rfl
    rw [inner_self_eq_norm_sq] at hre
    rw [← hre]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← inner_conj_symm (b i) v, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_re]
  rw [hnorm_b, EuclideanSpace.norm_sq_eq]
  refine Finset.sum_congr rfl fun z _ ↦ ?_
  simp only [v, norm_star]
  have hket : ⟪v, ket z⟫_ℂ = L (ket z) := (hLv (ket z)).symm
  rw [hket]

/-- **Orthonormal-basis invariance of the witness acceptance trace**: for any uniform quantum
verifier family `V`, input word `x`, and orthonormal basis `b` of
`Qubits (V.witnessLength x.length)`, `∑ i, V.acceptProb x (b i) = witnessAcceptTrace V x`. -/
theorem sum_acceptProb_orthonormalBasis_eq_witnessAcceptTrace {ι : Type*} [Fintype ι]
    (V : UniformVerifierFamily) (x : List Bool)
    (b : OrthonormalBasis ι ℂ (Qubits (V.witnessLength x.length))) :
    (∑ i : ι, V.acceptProb x (b i)) = witnessAcceptTrace V x := by
  unfold witnessAcceptTrace UniformVerifierFamily.acceptProb measureProb
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ ↦ ?_
  let U : Qubits (V.witnessLength x.length) →ₗ[ℂ] Qubits (V.width x.length) :=
    (Quantum.Circuit.eval (Quantum.Circuit.ofCodes (V.width x.length)
      (V.gates x.length))).toLinearIsometry.toLinearMap.comp
      (embedState (V.witnessQubits x.length) (inputState (V.width x.length) x)).toLinearMap
  let projY : Qubits (V.width x.length) →ₗ[ℂ] ℂ :=
    { toFun := fun Φ ↦ Φ.ofLp y
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  exact sum_norm_sq_orthonormalBasis_eq_ket b (projY.comp U)

end Trace

section SharpBQP

variable {α : Type*}

/-- **`#BQP` (`SharpBQP`)**: the class of counting functions `f : α → ℕ` admitting a
polynomial-time uniform quantum verifier family `V` whose witness acceptance trace on `enc a`
approximates `f a` within additive error `1 / 3` for every instance `a : α`. -/
def SharpBQP (enc : α ↪ List Bool) : Set (α → ℕ) :=
  {f | ∃ V : UniformVerifierFamily,
    ∀ a : α, |witnessAcceptTrace V (enc a) - (f a : ℝ)| ≤ 1 / 3}

/-- Explicit characterization of `SharpBQP`. -/
theorem mem_SharpBQP_iff {enc : α ↪ List Bool} {f : α → ℕ} :
    f ∈ SharpBQP enc ↔
      ∃ V : UniformVerifierFamily,
        ∀ a : α, |witnessAcceptTrace V (enc a) - (f a : ℝ)| ≤ 1 / 3 :=
  Iff.rfl

/-- An integer value `n : ℕ` approximated within `1 / 3` by a real trace `t` is uniquely
determined. -/
theorem eq_of_witnessAcceptTrace_approx {t : ℝ} {n₁ n₂ : ℕ}
    (h₁ : |t - (n₁ : ℝ)| ≤ 1 / 3) (h₂ : |t - (n₂ : ℝ)| ≤ 1 / 3) : n₁ = n₂ := by
  have hdiff : |(n₁ : ℝ) - (n₂ : ℝ)| ≤ 2 / 3 := by
    calc |(n₁ : ℝ) - (n₂ : ℝ)|
        = |(t - (n₂ : ℝ)) - (t - (n₁ : ℝ))| := by ring_nf
      _ ≤ |t - (n₂ : ℝ)| + |t - (n₁ : ℝ)| := abs_sub _ _
      _ ≤ 1 / 3 + 1 / 3 := add_le_add h₂ h₁
      _ = 2 / 3 := by norm_num
  have hlt : |(n₁ : ℝ) - (n₂ : ℝ)| < 1 := hdiff.trans_lt (by norm_num)
  rw [abs_lt] at hlt
  have h1 : (n₁ : ℝ) < (n₂ : ℝ) + 1 := by linarith [hlt.2]
  have h2 : (n₂ : ℝ) < (n₁ : ℝ) + 1 := by linarith [hlt.1]
  have hn1 : n₁ < n₂ + 1 := by exact_mod_cast h1
  have hn2 : n₂ < n₁ + 1 := by exact_mod_cast h2
  omega

/-- A uniform quantum verifier family `V` is a **gapped projector verifier** for `f : α → ℕ` (with
respect to encoding `enc`) if on every input `a : α`, the witness space
`Qubits (V.witnessLength (enc a).length)` contains a subspace `W` of dimension `f a` such that unit
witnesses in `W` accept with probability at least `1 - ε`, unit witnesses in `Wᗮ` accept with
probability at most `ε`, and `2 ^ (V.witnessLength (enc a).length) * ε ≤ 1 / 3`. -/
def IsGappedProjectorVerifier (enc : α ↪ List Bool) (V : UniformVerifierFamily) (f : α → ℕ) :
    Prop :=
  ∀ a : α,
    ∃ (W : Submodule ℂ (Qubits (V.witnessLength (enc a).length))) (ε : ℝ),
      0 ≤ ε ∧
      (2 : ℝ) ^ (V.witnessLength (enc a).length) * ε ≤ 1 / 3 ∧
      Module.finrank ℂ W = f a ∧
      (∀ ψ ∈ W, ‖ψ‖ = 1 → 1 - ε ≤ V.acceptProb (enc a) ψ) ∧
      (∀ ψ ∈ Wᗮ, ‖ψ‖ = 1 → V.acceptProb (enc a) ψ ≤ ε)

/-- Explicit characterization of `IsGappedProjectorVerifier`. -/
theorem isGappedProjectorVerifier_iff {enc : α ↪ List Bool} {V : UniformVerifierFamily}
    {f : α → ℕ} :
    IsGappedProjectorVerifier enc V f ↔
      ∀ a : α,
        ∃ (W : Submodule ℂ (Qubits (V.witnessLength (enc a).length))) (ε : ℝ),
          0 ≤ ε ∧
          (2 : ℝ) ^ (V.witnessLength (enc a).length) * ε ≤ 1 / 3 ∧
          Module.finrank ℂ W = f a ∧
          (∀ ψ ∈ W, ‖ψ‖ = 1 → 1 - ε ≤ V.acceptProb (enc a) ψ) ∧
          (∀ ψ ∈ Wᗮ, ‖ψ‖ = 1 → V.acceptProb (enc a) ψ ≤ ε) :=
  Iff.rfl

/-- **Positivity decision in `QMA` from a gapped projector verifier**: if `V` is a gapped projector
verifier for `f : α → ℕ` (with `α : Type`), then `{a | 0 < f a} ∈ QMA enc`. -/
theorem IsGappedProjectorVerifier.mem_QMA {α : Type} {enc : α ↪ List Bool}
    {V : UniformVerifierFamily} {f : α → ℕ} (hV : IsGappedProjectorVerifier enc V f) :
    {a : α | 0 < f a} ∈ QMA enc := by
  rw [Cslib.Complexity.mem_QMA]
  refine ⟨V, fun a ↦ ⟨fun hpos ↦ ?_, fun hzero ψ hψ ↦ ?_⟩⟩
  · obtain ⟨W, ε, hε0, hε_bound, hdim, hW, _⟩ := hV a
    have hpow_ge1 : (1 : ℝ) ≤ (2 : ℝ) ^ (V.witnessLength (enc a).length) :=
      one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
    have hε_le : ε ≤ 1 / 3 := by nlinarith
    have hW_nontriv : Nontrivial W :=
      Module.nontrivial_of_finrank_pos (by rw [hdim]; exact hpos)
    obtain ⟨w, hw_ne⟩ := exists_ne (0 : W)
    have hw_val : (w : Qubits (V.witnessLength (enc a).length)) ≠ 0 :=
      fun h ↦ hw_ne (Subtype.ext h)
    have hw_norm : ‖(w : Qubits (V.witnessLength (enc a).length))‖ ≠ 0 :=
      norm_ne_zero_iff.mpr hw_val
    let ψ : Qubits (V.witnessLength (enc a).length) :=
      ((‖(w : Qubits (V.witnessLength (enc a).length))‖ : ℝ)⁻¹ : ℂ) •
        (w : Qubits (V.witnessLength (enc a).length))
    have hψ_mem : ψ ∈ W := W.smul_mem _ w.2
    have hψ_norm : ‖ψ‖ = 1 := by
      rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _),
        inv_mul_cancel₀ hw_norm]
    refine ⟨ψ, hψ_norm, ?_⟩
    have := hW ψ hψ_mem hψ_norm
    linarith
  · obtain ⟨W, ε, hε0, hε_bound, hdim, _, hWperp⟩ := hV a
    have hf0 : f a = 0 := Nat.eq_zero_of_not_pos hzero
    have hW_bot : W = ⊥ := Submodule.finrank_eq_zero.mp (hdim.trans hf0)
    have hperp_top : Wᗮ = ⊤ := by rw [hW_bot, Submodule.bot_orthogonal_eq_top]
    have hpow_ge1 : (1 : ℝ) ≤ (2 : ℝ) ^ (V.witnessLength (enc a).length) :=
      one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
    have hε_le : ε ≤ 1 / 3 := by nlinarith
    exact (hWperp ψ (by rw [hperp_top]; trivial) hψ).trans hε_le

/-- **Counting membership in `#BQP` from a gapped projector verifier**: if `V` is a gapped
projector verifier for `f : α → ℕ`, then `f ∈ SharpBQP enc`. -/
theorem IsGappedProjectorVerifier.mem_SharpBQP {enc : α ↪ List Bool}
    {V : UniformVerifierFamily} {f : α → ℕ} (hV : IsGappedProjectorVerifier enc V f) :
    f ∈ SharpBQP enc := by
  refine ⟨V, fun a ↦ ?_⟩
  obtain ⟨W, ε, hε0, hε_bound, hdim, hW, hWperp⟩ := hV a
  let m := V.witnessLength (enc a).length
  let bW := stdOrthonormalBasis ℂ W
  let bWp := stdOrthonormalBasis ℂ ↥Wᗮ
  -- Build a combined orthonormal basis on `Fin (finrank W) ⊕ Fin (finrank Wᗮ)` for `Qubits m`.
  let embSum : Fin (Module.finrank ℂ W) ⊕ Fin (Module.finrank ℂ ↥Wᗮ) → Qubits m :=
    Sum.elim (fun i ↦ (bW i : Qubits m)) (fun j ↦ (bWp j : Qubits m))
  have hortho : Orthonormal ℂ embSum := by
    rw [orthonormal_iff_ite]
    intro x y
    rcases x with i₁ | j₁ <;> rcases y with i₂ | j₂
    · simp only [embSum, Sum.elim_inl, Sum.inl.injEq]
      simpa only [Submodule.coe_inner] using orthonormal_iff_ite.mp bW.orthonormal i₁ i₂
    · simp only [embSum, Sum.elim_inl, Sum.elim_inr, reduceCtorEq, ↓reduceIte]
      exact (Submodule.mem_orthogonal W (bWp j₂).1).mp (bWp j₂).2 (bW i₁).1 (bW i₁).2
    · simp only [embSum, Sum.elim_inr, Sum.elim_inl, reduceCtorEq, ↓reduceIte]
      rw [← inner_conj_symm,
        (Submodule.mem_orthogonal W (bWp j₁).1).mp (bWp j₁).2 (bW i₂).1 (bW i₂).2, map_zero]
    · simp only [embSum, Sum.elim_inr, Sum.inr.injEq]
      simpa only [Submodule.coe_inner] using orthonormal_iff_ite.mp bWp.orthonormal j₁ j₂
  have hdim_tot : Module.finrank ℂ (Qubits m) = 2 ^ m := by
    simp [Qubits, Fintype.card_pi, Fintype.card_bool]
  have hcard : Fintype.card (Fin (Module.finrank ℂ W) ⊕ Fin (Module.finrank ℂ ↥Wᗮ)) =
      Module.finrank ℂ (Qubits m) := by
    rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin,
      Submodule.finrank_add_finrank_orthogonal W]
  have : Nonempty (Fin (Module.finrank ℂ W) ⊕ Fin (Module.finrank ℂ ↥Wᗮ)) :=
    Fintype.card_pos_iff.mp (by rw [hcard, hdim_tot]; positivity)
  let bBasis := basisOfOrthonormalOfCardEqFinrank hortho hcard
  have hbBasis : (bBasis : _ → Qubits m) = embSum :=
    coe_basisOfOrthonormalOfCardEqFinrank hortho hcard
  let bAll : OrthonormalBasis (Fin (Module.finrank ℂ W) ⊕ Fin (Module.finrank ℂ ↥Wᗮ)) ℂ
      (Qubits m) := bBasis.toOrthonormalBasis (hbBasis.symm ▸ hortho)
  have htrace := sum_acceptProb_orthonormalBasis_eq_witnessAcceptTrace V (enc a) bAll
  have hbAll_apply : ∀ idx, bAll idx = embSum idx := fun idx ↦ by
    change (bBasis.toOrthonormalBasis (hbBasis.symm ▸ hortho) : _ → Qubits m) idx = embSum idx
    rw [Module.Basis.coe_toOrthonormalBasis, hbBasis]
  rw [← htrace]
  simp_rw [hbAll_apply, Fintype.sum_sum_type, embSum, Sum.elim_inl, Sum.elim_inr]
  have hW_le_tot : Module.finrank ℂ W ≤ 2 ^ m :=
    (Submodule.finrank_le W).trans_eq hdim_tot
  have hWp_le_tot : Module.finrank ℂ ↥Wᗮ ≤ 2 ^ m :=
    (Submodule.finrank_le Wᗮ).trans_eq hdim_tot
  have hsumW_lo : ((f a : ℝ) * (1 - ε)) ≤
      ∑ i : Fin (Module.finrank ℂ W), V.acceptProb (enc a) (bW i : Qubits m) := by
    calc (f a : ℝ) * (1 - ε)
        = ∑ _i : Fin (Module.finrank ℂ W), (1 - ε) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, hdim, nsmul_eq_mul]
      _ ≤ ∑ i : Fin (Module.finrank ℂ W), V.acceptProb (enc a) (bW i : Qubits m) := by
          refine Finset.sum_le_sum fun i _ ↦ hW (bW i : Qubits m) (bW i).2 ?_
          exact bW.orthonormal.1 i
  have hsumW_hi :
      (∑ i : Fin (Module.finrank ℂ W), V.acceptProb (enc a) (bW i : Qubits m)) ≤ (f a : ℝ) := by
    calc ∑ i : Fin (Module.finrank ℂ W), V.acceptProb (enc a) (bW i : Qubits m)
        ≤ ∑ _i : Fin (Module.finrank ℂ W), (1 : ℝ) := by
          refine Finset.sum_le_sum fun i _ ↦ ?_
          have hnorm1 : ‖(bW i : Qubits m)‖ = 1 := bW.orthonormal.1 i
          simpa only [hnorm1, one_pow] using V.acceptProb_le (enc a) (bW i : Qubits m)
      _ = (f a : ℝ) := by simp [hdim]
  have hsumWp_lo : 0 ≤
      ∑ j : Fin (Module.finrank ℂ ↥Wᗮ), V.acceptProb (enc a) (bWp j : Qubits m) :=
    Finset.sum_nonneg fun j _ ↦ V.acceptProb_nonneg (enc a) _
  have hsumWp_hi :
      (∑ j : Fin (Module.finrank ℂ ↥Wᗮ), V.acceptProb (enc a) (bWp j : Qubits m)) ≤
        ((2 : ℝ) ^ m) * ε := by
    calc ∑ j : Fin (Module.finrank ℂ ↥Wᗮ), V.acceptProb (enc a) (bWp j : Qubits m)
        ≤ ∑ _j : Fin (Module.finrank ℂ ↥Wᗮ), ε := by
          refine Finset.sum_le_sum fun j _ ↦ hWperp (bWp j : Qubits m) (bWp j).2 ?_
          exact bWp.orthonormal.1 j
      _ = (Module.finrank ℂ ↥Wᗮ : ℝ) * ε := by simp
      _ ≤ ((2 : ℝ) ^ m) * ε := by
          refine mul_le_mul_of_nonneg_right ?_ hε0
          exact_mod_cast hWp_le_tot
  have hf_eps : (f a : ℝ) * ε ≤ 1 / 3 := by
    have hf_le : (f a : ℝ) ≤ (2 : ℝ) ^ m := by
      rw [← hdim]
      exact_mod_cast hW_le_tot
    exact (mul_le_mul_of_nonneg_right hf_le hε0).trans hε_bound
  rw [abs_le]
  constructor <;> linarith

/-- On a zero-witness verifier constructed from a `UniformCircuitFamily`, the witness acceptance
trace equals the circuit family's acceptance probability. -/
@[simp]
theorem witnessAcceptTrace_ofCircuitFamily (F : UniformCircuitFamily) (x : List Bool) :
    witnessAcceptTrace (UniformVerifierFamily.ofCircuitFamily F) x = F.acceptProb x := by
  unfold witnessAcceptTrace
  have : Unique (Fin ((UniformVerifierFamily.ofCircuitFamily F).witnessLength x.length) →
      Bool) := inferInstanceAs (Unique (Fin 0 → Bool))
  rw [Fintype.sum_unique, UniformVerifierFamily.acceptProb_ofCircuitFamily, norm_ket, one_pow,
    one_mul]

/-- Every `BQP`-decidable indicator function `(fun a ↦ if a ∈ A then 1 else 0)` belongs to
`SharpBQP enc` whenever `A` has a `BQP` circuit family with error at most `1 / 3`. -/
theorem indicator_mem_SharpBQP_of_mem_BQP {enc : α ↪ List Bool} {A : Set α}
    [DecidablePred (· ∈ A)]
    (hA : ∃ F : UniformCircuitFamily,
      ∀ a, (a ∈ A → 2 / 3 ≤ F.acceptProb (enc a)) ∧
        (a ∉ A → F.acceptProb (enc a) ≤ 1 / 3)) :
    (fun a ↦ if a ∈ A then 1 else 0) ∈ SharpBQP enc := by
  obtain ⟨F, hF⟩ := hA
  refine ⟨UniformVerifierFamily.ofCircuitFamily F, fun a ↦ ?_⟩
  rw [witnessAcceptTrace_ofCircuitFamily]
  have hle1 : F.acceptProb (enc a) ≤ 1 := by
    have := (UniformVerifierFamily.ofCircuitFamily F).acceptProb_le (enc a) (ket default)
    rwa [UniformVerifierFamily.acceptProb_ofCircuitFamily, norm_ket, one_pow, one_mul] at this
  have hge0 : 0 ≤ F.acceptProb (enc a) := by
    have := (UniformVerifierFamily.ofCircuitFamily F).acceptProb_nonneg (enc a) (ket default)
    rwa [UniformVerifierFamily.acceptProb_ofCircuitFamily, norm_ket, one_pow, one_mul] at this
  by_cases ha : a ∈ A
  · simp only [ha, ↓reduceIte, Nat.cast_one, abs_le]
    have := (hF a).1 ha
    constructor <;> linarith
  · simp only [ha, ↓reduceIte, Nat.cast_zero, sub_zero, abs_le]
    have := (hF a).2 ha
    constructor <;> linarith

end SharpBQP

end CslibFrontier.Complexity
