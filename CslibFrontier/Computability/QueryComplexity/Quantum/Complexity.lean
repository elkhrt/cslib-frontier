/-
Copyright (c) 2026 CslibFrontier contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CslibFrontier contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.QueryComplexity.Quantum.Polynomial
public import CslibFrontier.Computability.QueryComplexity.Quantum.SpectralAdversary
import CslibFrontier.Computability.QueryComplexity.Quantum.BitQuery
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Bounded-Error Quantum Query Complexity and Projection Reductions

This module defines the worst-case two-sided-error quantum query complexity $Q_\varepsilon(f)$ and
the standard bounded-error quantum query complexity $Q_2(f) = Q_{1/3}(f)$ of a total Boolean
function $f : \{0, 1\}^N \to \{0, 1\}$ in the controlled phase-oracle query model
(`Cslib.Quantum.State`, `Cslib.Quantum.run`), and establishes its foundational properties:

* Attainment, monotonicity in the error parameter, trivial upper bound $Q_\varepsilon(f) \le N$,
  characterization on constant and non-constant functions, and isometric subspace transport
  (`embedBasis`, `transportBasis`).
* Exact zero-overhead **projection reductions**: whenever every coordinate of
  $y \in \{0, 1\}^M$ is either a fixed Boolean constant or a (possibly negated) input bit of
  $x \in \{0, 1\}^N$, we have $Q_\varepsilon(h \circ \pi) \le Q_\varepsilon(h)$.
* The Høyer–Lee–Špalek negative-weight adversary lower bound
  $(1 - 2\sqrt{\varepsilon(1 - \varepsilon)})\,\mathrm{ADV}^{\pm}(f) \le 2\,Q_\varepsilon(f)$
  (giving $\mathrm{ADV}^{\pm}(f) \le 36\,Q_2(f)$ at $\varepsilon = 1/3$) and the Beals et al.
  disjunction lower bound $N \le 16\,Q_2(\mathrm{OR}_N)^2$.

## Main definitions

* `Cslib.Quantum.embedBasis`, `Cslib.Quantum.transportBasis`: isometric embedding
  of a computational-basis subspace and unitary extension mapping one embedded subspace to another.
* `Cslib.Quantum.ComputesWithinOn`, `Cslib.Quantum.ComputesWithin`: correctness of
  a $T$-query quantum algorithm within additive error $\varepsilon$ (on a promise domain or total).
* `Cslib.Quantum.IsQuantumComputable`: existence of a $T$-query quantum algorithm computing
  a total Boolean function within additive error $\varepsilon$.
* `Cslib.Quantum.queryComplexity`, `Cslib.Quantum.boundedQueryComplexity`:
  worst-case quantum query complexity $Q_\varepsilon(f)$ and $Q_2(f) = Q_{1/3}(f)$.
* `Cslib.Quantum.Literal`, `Cslib.Quantum.evalProjection`: coordinatewise constant
  or literal projection maps $\{0, 1\}^N \to \{0, 1\}^M$.
* `Cslib.Quantum.orBool`: the $N$-bit Boolean disjunction $\mathrm{OR}_N$.

## Main results

* `Cslib.Quantum.exists_isQuantumComputable_queryComplexity`,
  `Cslib.Quantum.queryComplexity_le_iff`, `Cslib.Quantum.le_queryComplexity_iff`:
  attainment and infimum characterizations of $Q_\varepsilon(f)$.
* `Cslib.Quantum.queryComplexity_le_length`: $Q_\varepsilon(f) \le N$ for
  $\varepsilon \ge 0$.
* `Cslib.Quantum.queryComplexity_comp_evalProjection_le`,
  `Cslib.Quantum.boundedQueryComplexity_comp_evalProjection_le`:
  $Q_\varepsilon(h \circ \pi) \le Q_\varepsilon(h)$ under literal projections.
* `Cslib.Quantum.one_sub_mul_generalAdversary_le_two_mul_queryComplexity`,
  `Cslib.Quantum.generalAdversary_le_thirty_six_mul_boundedQueryComplexity`:
  negative-weight adversary lower bound on $Q_\varepsilon(f)$ and $Q_2(f)$.
* `Cslib.Quantum.le_sixteen_mul_boundedQueryComplexity_orBool_sq`,
  `Cslib.Quantum.sqrt_le_four_mul_boundedQueryComplexity_orBool`:
  quantum query lower bound $Q_2(\mathrm{OR}_N) \ge \sqrt{N} / 4$.

## Tags

quantum query complexity, adversary bound, projection reduction, Boolean function, search bound
-/

public section

namespace Cslib.Quantum

open Finset Cslib Cslib.BitString

/-! ### Isometric subspace embeddings and unitary extensions -/

section SubspaceTransport

variable {α β : Type*} [Fintype α] [Fintype β]

/-- Promote a linear isometry on a finite-dimensional complex Euclidean space to a surjective
linear isometric equivalence. -/
noncomputable def linearIsometryToEquiv
    (L : EuclideanSpace ℂ α →ₗᵢ[ℂ] EuclideanSpace ℂ α) :
    EuclideanSpace ℂ α ≃ₗᵢ[ℂ] EuclideanSpace ℂ α :=
  LinearIsometryEquiv.ofSurjective L (LinearMap.injective_iff_surjective.1 L.injective)

@[simp]
theorem linearIsometryToEquiv_apply
    (L : EuclideanSpace ℂ α →ₗᵢ[ℂ] EuclideanSpace ℂ α) (ψ : EuclideanSpace ℂ α) :
    linearIsometryToEquiv L ψ = L ψ := by
  rfl

/-- Isometric embedding of `EuclideanSpace ℂ α` into `EuclideanSpace ℂ β` along an injective basis
map `e : α ↪ β`, extending by zero outside the range of `e`. -/
noncomputable def embedBasis (e : α ↪ β) : EuclideanSpace ℂ α →ₗᵢ[ℂ] EuclideanSpace ℂ β where
  toFun ψ := by
    classical
    exact WithLp.toLp 2 fun b ↦ if h : ∃ a, e a = b then ψ.ofLp h.choose else 0
  map_add' ψ φ := by
    classical
    ext b
    simp only [PiLp.add_apply]
    split_ifs <;> simp
  map_smul' c ψ := by
    classical
    ext b
    simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> simp
  norm_map' ψ := by
    classical
    refine (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    change ∑ b : β, ‖(if h : ∃ a, e a = b then ψ.ofLp h.choose else 0 : ℂ)‖ ^ 2 =
      ∑ a : α, ‖ψ.ofLp a‖ ^ 2
    have hsub : ∑ b : β, ‖(if h : ∃ a, e a = b then ψ.ofLp h.choose else 0 : ℂ)‖ ^ 2 =
        ∑ b ∈ univ.map e, ‖(if h : ∃ a, e a = b then ψ.ofLp h.choose else 0 : ℂ)‖ ^ 2 := by
      refine (sum_subset (subset_univ _) fun b _ hb ↦ ?_).symm
      have hne : ¬∃ a, e a = b := by simpa [mem_map] using hb
      simp [hne]
    rw [hsub, sum_map]
    refine sum_congr rfl fun a _ ↦ ?_
    split_ifs with hex
    · rw [e.injective hex.choose_spec]
    · exact (hex ⟨a, rfl⟩).elim

/-- Evaluating `embedBasis e ψ` at an embedded basis index `e a` returns `ψ.ofLp a`. -/
@[simp]
theorem embedBasis_apply_image (e : α ↪ β) (ψ : EuclideanSpace ℂ α) (a : α) :
    (embedBasis e ψ).ofLp (e a) = ψ.ofLp a := by
  classical
  change (if h : ∃ a', e a' = e a then ψ.ofLp h.choose else 0) = ψ.ofLp a
  split_ifs with hex
  · rw [e.injective hex.choose_spec]
  · exact (hex ⟨a, rfl⟩).elim

/-- Evaluating `embedBasis e ψ` outside the range of `e` yields `0`. -/
theorem embedBasis_apply_of_not_mem (e : α ↪ β) (ψ : EuclideanSpace ℂ α) {b : β}
    (hb : ∀ a, e a ≠ b) : (embedBasis e ψ).ofLp b = 0 := by
  classical
  change (if h : ∃ a, e a = b then ψ.ofLp h.choose else 0) = 0
  split_ifs with hex
  · exact (hb hex.choose hex.choose_spec).elim
  · rfl

/-- Measuring `embedBasis e ψ` on an embedded outcome set `S.map e` preserves probability. -/
@[simp]
theorem measureProb_embedBasis_map (e : α ↪ β) (ψ : EuclideanSpace ℂ α) (S : Finset α) :
    measureProb (embedBasis e ψ) (S.map e) = measureProb ψ S := by
  simp only [measureProb, sum_map, embedBasis_apply_image]

/-- Measuring `embedBasis e ψ` on any outcome set `T` reduces to its preimage under `e`. -/
theorem measureProb_embedBasis [DecidableEq β] (e : α ↪ β) (ψ : EuclideanSpace ℂ α)
    (T : Finset β) :
    measureProb (embedBasis e ψ) T = measureProb ψ (univ.filter fun a ↦ e a ∈ T) := by
  classical
  have hsplit : measureProb (embedBasis e ψ) T =
      ∑ b ∈ T.filter (fun b ↦ ∃ a, e a = b), ‖(embedBasis e ψ).ofLp b‖ ^ 2 := by
    rw [measureProb]
    refine (sum_subset (filter_subset _ _) fun b hb hnot ↦ ?_).symm
    have hna : ∀ a, e a ≠ b := not_exists.1 (by simpa [hb] using hnot)
    simp [embedBasis_apply_of_not_mem e ψ hna]
  have heq : T.filter (fun b ↦ ∃ a, e a = b) = (univ.filter fun a ↦ e a ∈ T).map e := by
    ext b
    simp only [mem_filter, mem_map, mem_univ, true_and]
    exact ⟨fun ⟨hb, a, ha⟩ ↦ ⟨a, ha ▸ hb, ha⟩, fun ⟨a, ha, hab⟩ ↦ ⟨hab ▸ ha, a, hab⟩⟩
  rw [hsplit, heq, ← measureProb, measureProb_embedBasis_map]

private noncomputable def complEquiv (e₁ e₂ : α ↪ β) :
    {b : β // ¬∃ a, e₁ a = b} ≃ {b : β // ¬∃ a, e₂ a = b} := by
  classical
  refine Fintype.equivOfCardEq ?_
  have hc (e : α ↪ β) : Fintype.card {b : β // ¬∃ a, e a = b} =
      Fintype.card β - Fintype.card α := by
    rw [Fintype.card_subtype_compl,
      show Fintype.card {b : β // ∃ a, e a = b} = #(univ.map e) by
        rw [← Fintype.card_coe]
        exact Fintype.card_congr (Equiv.subtypeEquivRight fun b ↦ by simp [mem_map]),
      card_map, card_univ]
  rw [hc e₁, hc e₂]

/-- Unitary extension on `EuclideanSpace ℂ β` transporting `embedBasis e₁ ψ` to
`embedBasis e₂ (L ψ)` while mapping the orthogonal complement bijectively. -/
noncomputable def transportBasis (e₁ e₂ : α ↪ β)
    (L : EuclideanSpace ℂ α ≃ₗᵢ[ℂ] EuclideanSpace ℂ α) :
    EuclideanSpace ℂ β →ₗᵢ[ℂ] EuclideanSpace ℂ β where
  toFun ψ := by
    classical
    exact WithLp.toLp 2 fun b ↦
      if h : ∃ a, e₂ a = b then
        (L (WithLp.toLp 2 fun a' ↦ ψ.ofLp (e₁ a'))).ofLp h.choose
      else
        ψ.ofLp ((complEquiv e₁ e₂).symm ⟨b, h⟩).1
  map_add' ψ φ := by
    classical
    ext b
    simp only [PiLp.add_apply]
    split_ifs with h
    · have hadd : (WithLp.toLp 2 fun a' ↦ ψ.ofLp (e₁ a') + φ.ofLp (e₁ a') :
          EuclideanSpace ℂ α) =
          (WithLp.toLp 2 fun a' ↦ ψ.ofLp (e₁ a')) +
          (WithLp.toLp 2 fun a' ↦ φ.ofLp (e₁ a')) := rfl
      rw [hadd, map_add, PiLp.add_apply]
    · rfl
  map_smul' c ψ := by
    classical
    ext b
    simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs with h
    · have hsm : (WithLp.toLp 2 fun a' ↦ c * ψ.ofLp (e₁ a') : EuclideanSpace ℂ α) =
          c • (WithLp.toLp 2 fun a' ↦ ψ.ofLp (e₁ a')) := rfl
      rw [hsm, map_smul, PiLp.smul_apply, smul_eq_mul]
    · rfl
  norm_map' ψ := by
    classical
    refine (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    set φ : EuclideanSpace ℂ α := WithLp.toLp 2 fun a' ↦ ψ.ofLp (e₁ a')
    let f : β → ℝ := fun b ↦
      ‖(if h : ∃ a, e₂ a = b then (L φ).ofLp h.choose
        else ψ.ofLp ((complEquiv e₁ e₂).symm ⟨b, h⟩).1 : ℂ)‖ ^ 2
    change ∑ b : β, f b = ∑ b : β, ‖ψ.ofLp b‖ ^ 2
    rw [← sum_filter_add_sum_filter_not univ (fun b ↦ ∃ a, e₂ a = b) f]
    have hpos : ∑ b with ∃ a, e₂ a = b, f b = ∑ a : α, ‖ψ.ofLp (e₁ a)‖ ^ 2 := by
      have hset : univ.filter (fun b : β ↦ ∃ a, e₂ a = b) = univ.map e₂ := by
        ext b; simp [mem_map]
      rw [hset, sum_map]
      have h1 : ∑ a : α, f (e₂ a) = ‖L φ‖ ^ 2 := by
        rw [EuclideanSpace.norm_sq_eq]
        refine sum_congr rfl fun a _ ↦ ?_
        dsimp only [f]
        split_ifs with hex
        · rw [e₂.injective hex.choose_spec]
        · exact (hex ⟨a, rfl⟩).elim
      rw [h1, L.norm_map, EuclideanSpace.norm_sq_eq]
    have hneg : ∑ b with ¬∃ a, e₂ a = b, f b =
        ∑ b with ¬∃ a, e₁ a = b, ‖ψ.ofLp b‖ ^ 2 := by
      rw [← sum_attach (univ.filter fun b : β ↦ ¬∃ a, e₂ a = b),
        ← sum_attach (univ.filter fun b : β ↦ ¬∃ a, e₁ a = b)]
      refine Fintype.sum_equiv
        ((Equiv.subtypeEquivRight (fun b ↦ by simp)).trans
          ((complEquiv e₁ e₂).symm.trans (Equiv.subtypeEquivRight (fun b ↦ by simp))))
        _ _ fun x ↦ ?_
      have hx : ¬∃ a, e₂ a = x.1 := (mem_filter.1 x.2).2
      simp only [f, hx, ↓reduceDIte, Equiv.trans_apply, Equiv.subtypeEquivRight_apply_coe]
      rfl
    have hrhs : ∑ a : α, ‖ψ.ofLp (e₁ a)‖ ^ 2 =
        ∑ b with ∃ a, e₁ a = b, ‖ψ.ofLp b‖ ^ 2 := by
      have hset : univ.filter (fun b : β ↦ ∃ a, e₁ a = b) = univ.map e₁ := by
        ext b; simp [mem_map]
      rw [hset, sum_map]
    rw [hpos, hrhs, hneg, sum_filter_add_sum_filter_not]

/-- `transportBasis e₁ e₂ L` maps `embedBasis e₁ ψ` to `embedBasis e₂ (L ψ)`. -/
@[simp]
theorem transportBasis_embedBasis (e₁ e₂ : α ↪ β)
    (L : EuclideanSpace ℂ α ≃ₗᵢ[ℂ] EuclideanSpace ℂ α) (ψ : EuclideanSpace ℂ α) :
    transportBasis e₁ e₂ L (embedBasis e₁ ψ) = embedBasis e₂ (L ψ) := by
  classical
  ext b
  have hres : (WithLp.toLp 2 fun a' ↦ (embedBasis e₁ ψ).ofLp (e₁ a')) = ψ := by
    ext a'; simp
  change (if h' : ∃ a', e₂ a' =
    b then (L (WithLp.toLp 2 fun a' ↦ (embedBasis e₁ ψ).ofLp (e₁ a'))).ofLp h'.choose
      else (embedBasis e₁ ψ).ofLp ((complEquiv e₁ e₂).symm ⟨b, h'⟩).1) =
    (embedBasis e₂ (L ψ)).ofLp b
  split_ifs with h
  · obtain ⟨a, rfl⟩ := h
    have hex : ∃ a', e₂ a' = e₂ a := ⟨a, rfl⟩
    rw [e₂.injective hex.choose_spec, hres, embedBasis_apply_image]
  · rw [embedBasis_apply_of_not_mem e₁ ψ (not_exists.1 ((complEquiv e₁ e₂).symm ⟨b, h⟩).2),
      embedBasis_apply_of_not_mem e₂ (L ψ) (not_exists.1 h)]

end SubspaceTransport

/-! ### Quantum query algorithms and worst-case query complexity -/

section Complexity

/-- A `T`-query quantum algorithm `(U, ψ₀, S)` computes a Boolean function `f` on a promise
predicate `P` within additive error `ε` if `ψ₀` is a unit vector and every valid input `x` is
accepted with probability within `ε` of `f x`. -/
@[expose]
def ComputesWithinOn {N : ℕ} {W : Type*} [Fintype W]
    (U : ℕ → State N W →ₗᵢ[ℂ] State N W) (ψ₀ : State N W) (T : ℕ)
    (S : Finset (Fin N × Bool × W)) (ε : ℝ) (P : BitString N → Prop)
    (f : BooleanFunction N) : Prop :=
  ‖ψ₀‖ = 1 ∧ ∀ x : BitString N, P x → |measureProb (run U ψ₀ x T) S - bitVal ℝ (f x)| ≤ ε

/-- A `T`-query quantum algorithm `(U, ψ₀, S)` computes a total Boolean function `f` within
additive error `ε`. -/
@[expose]
def ComputesWithin {N : ℕ} {W : Type*} [Fintype W]
    (U : ℕ → State N W →ₗᵢ[ℂ] State N W) (ψ₀ : State N W) (T : ℕ)
    (S : Finset (Fin N × Bool × W)) (ε : ℝ) (f : BooleanFunction N) : Prop :=
  ‖ψ₀‖ = 1 ∧ ∀ x : BitString N, |measureProb (run U ψ₀ x T) S - bitVal ℝ (f x)| ≤ ε

/-- Equivalence between `ComputesWithin` and `ComputesWithinOn` with the trivial promise. -/
theorem computesWithin_iff_on_true {N : ℕ} {W : Type*} [Fintype W]
    {U : ℕ → State N W →ₗᵢ[ℂ] State N W} {ψ₀ : State N W} {T : ℕ}
    {S : Finset (Fin N × Bool × W)} {ε : ℝ} {f : BooleanFunction N} :
    ComputesWithin U ψ₀ T S ε f ↔ ComputesWithinOn U ψ₀ T S ε (fun _ ↦ True) f := by
  simp [ComputesWithin, ComputesWithinOn]

/-- Transporting a workspace along a bijection `W₁ ≃ W₂` preserves `ComputesWithinOn`. -/
theorem ComputesWithinOn.equiv {N : ℕ} {W₁ W₂ : Type*} [Fintype W₁] [Fintype W₂]
    {U : ℕ → State N W₁ →ₗᵢ[ℂ] State N W₁} {ψ₀ : State N W₁} {T : ℕ}
    {S : Finset (Fin N × Bool × W₁)} {ε : ℝ} {P : BitString N → Prop} {f : BooleanFunction N}
    (h : ComputesWithinOn U ψ₀ T S ε P f) (e : W₁ ≃ W₂) :
    ∃ (U' : ℕ → State N W₂ →ₗᵢ[ℂ] State N W₂) (ψ₀' : State N W₂)
      (S' : Finset (Fin N × Bool × W₂)),
      ComputesWithinOn U' ψ₀' T S' ε P f := by
  let be : Fin N × Bool × W₁ ≃ Fin N × Bool × W₂ :=
    Equiv.prodCongr (Equiv.refl (Fin N)) (Equiv.prodCongr (Equiv.refl Bool) e)
  let se : State N W₁ ≃ₗᵢ[ℂ] State N W₂ := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ be
  have horacle (x : BitString N) (ψ : State N W₁) :
      phaseOracle x (se ψ) = se (phaseOracle x ψ) := by
    ext ⟨i, b, w₂⟩
    rfl
  let U' : ℕ → State N W₂ →ₗᵢ[ℂ] State N W₂ := fun t ↦
    se.toLinearIsometry.comp ((U t).comp se.symm.toLinearIsometry)
  have hrun (x : BitString N) (t : ℕ) : run U' (se ψ₀) x t = se (run U ψ₀ x t) := by
    induction t with
    | zero => simp [run, U']
    | succ t ih => simp [run, ih, horacle, U']
  have hprob (ψ : State N W₁) : measureProb (se ψ) (S.map be.toEmbedding) = measureProb ψ S := by
    simp only [measureProb, sum_map, Equiv.coe_toEmbedding]
    refine sum_congr rfl fun ⟨i, b, w₁⟩ _ ↦ ?_
    change ‖ψ.ofLp (be.symm (be (i, b, w₁)))‖ ^ 2 = ‖ψ.ofLp (i, b, w₁)‖ ^ 2
    rw [be.symm_apply_apply]
  refine ⟨U', se ψ₀, S.map be.toEmbedding, by rw [se.norm_map, h.1], fun x hx ↦ ?_⟩
  rw [hrun, hprob]
  exact h.2 x hx

/-- Transporting a workspace along a bijection `W₁ ≃ W₂` preserves `ComputesWithin`. -/
theorem ComputesWithin.equiv {N : ℕ} {W₁ W₂ : Type*} [Fintype W₁] [Fintype W₂]
    {U : ℕ → State N W₁ →ₗᵢ[ℂ] State N W₁} {ψ₀ : State N W₁} {T : ℕ}
    {S : Finset (Fin N × Bool × W₁)} {ε : ℝ} {f : BooleanFunction N}
    (h : ComputesWithin U ψ₀ T S ε f) (e : W₁ ≃ W₂) :
    ∃ (U' : ℕ → State N W₂ →ₗᵢ[ℂ] State N W₂) (ψ₀' : State N W₂)
      (S' : Finset (Fin N × Bool × W₂)),
      ComputesWithin U' ψ₀' T S' ε f := by
  obtain ⟨U', ψ₀', S', h'⟩ := (computesWithin_iff_on_true.1 h).equiv e
  exact ⟨U', ψ₀', S', computesWithin_iff_on_true.2 h'⟩

/-- Every algorithm computing a total Boolean function within error `ε` requires `0 ≤ ε`. -/
theorem ComputesWithin.err_nonneg {N : ℕ} {W : Type*} [Fintype W]
    {U : ℕ → State N W →ₗᵢ[ℂ] State N W} {ψ₀ : State N W} {T : ℕ}
    {S : Finset (Fin N × Bool × W)} {ε : ℝ} {f : BooleanFunction N}
    (h : ComputesWithin U ψ₀ T S ε f) : 0 ≤ ε :=
  (abs_nonneg _).trans (h.2 fun _ ↦ false)

/-- A total Boolean function `f : BooleanFunction N` is quantum-computable in `T` queries within
additive error `ε` if either `N = 0` (so `f` is constant on the singleton domain) with `0 ≤ ε`, or
some `T`-query algorithm on a finite workspace computes `f` within error `ε`. -/
def IsQuantumComputable {N : ℕ} (ε : ℝ) (f : BooleanFunction N) (T : ℕ) : Prop :=
  (N = 0 ∧ 0 ≤ ε) ∨
    ∃ (k : ℕ) (U : ℕ → State N (Fin k) →ₗᵢ[ℂ] State N (Fin k))
      (ψ₀ : State N (Fin k)) (S : Finset (Fin N × Bool × Fin k)),
      ComputesWithin U ψ₀ T S ε f

/-- Any `T`-query algorithm on an arbitrary finite workspace `(W : Type*) [Fintype W]` witnesses
`IsQuantumComputable ε f T`. -/
theorem ComputesWithin.isQuantumComputable {N : ℕ} {W : Type*} [Fintype W]
    {U : ℕ → State N W →ₗᵢ[ℂ] State N W} {ψ₀ : State N W} {T : ℕ}
    {S : Finset (Fin N × Bool × W)} {ε : ℝ} {f : BooleanFunction N}
    (h : ComputesWithin U ψ₀ T S ε f) : IsQuantumComputable ε f T := by
  obtain ⟨U', ψ₀', S', h'⟩ := h.equiv (Fintype.equivFin W)
  exact Or.inr ⟨Fintype.card W, U', ψ₀', S', h'⟩

/-- For `N > 0`, `IsQuantumComputable ε f T` is equivalent to the existence of a finite-workspace
`T`-query algorithm in any universe `u`. -/
theorem isQuantumComputable_pos_iff.{u} {N : ℕ} (hN : 0 < N) (ε : ℝ) (f : BooleanFunction N)
    (T : ℕ) :
    IsQuantumComputable ε f T ↔
      ∃ (W : Type u) (_ : Fintype W) (U : ℕ → State N W →ₗᵢ[ℂ] State N W)
        (ψ₀ : State N W) (S : Finset (Fin N × Bool × W)),
        ComputesWithin U ψ₀ T S ε f := by
  refine ⟨?_, fun ⟨_, _, _, _, _, h⟩ ↦ h.isQuantumComputable⟩
  rintro (⟨rfl, -⟩ | ⟨k, U, ψ₀, S, h⟩)
  · exact (lt_irrefl 0 hN).elim
  · obtain ⟨U', ψ₀', S', h'⟩ := h.equiv (Equiv.ulift.{u, 0}.symm : Fin k ≃ ULift.{u} (Fin k))
    exact ⟨ULift.{u} (Fin k), inferInstance, U', ψ₀', S', h'⟩

/-- `IsQuantumComputable ε f T` implies `0 ≤ ε`. -/
theorem IsQuantumComputable.err_nonneg {N : ℕ} {ε : ℝ} {f : BooleanFunction N} {T : ℕ}
    (h : IsQuantumComputable ε f T) : 0 ≤ ε := by
  rcases h with ⟨-, hε⟩ | ⟨_, _, _, _, hc⟩
  · exact hε
  · exact hc.err_nonneg

/-- `IsQuantumComputable` is monotone in the allowed additive error `ε`. -/
theorem IsQuantumComputable.mono_err {N : ℕ} {ε ε' : ℝ} {f : BooleanFunction N} {T : ℕ}
    (h : IsQuantumComputable ε f T) (hε : ε ≤ ε') : IsQuantumComputable ε' f T := by
  rcases h with ⟨hN, h0⟩ | ⟨k, U, ψ₀, S, hψ, hx⟩
  · exact Or.inl ⟨hN, h0.trans hε⟩
  · exact Or.inr ⟨k, U, ψ₀, S, hψ, fun x ↦ (hx x).trans hε⟩

/-- Every constant Boolean function is computable with `T` queries (in particular `0` queries) for
any `ε ≥ 0`. -/
theorem isQuantumComputable_const {N : ℕ} {ε : ℝ} (hε : 0 ≤ ε) (b : Bool) (T : ℕ) :
    IsQuantumComputable ε (fun _ : BitString N ↦ b) T := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · exact Or.inl ⟨rfl, hε⟩
  · let p₀ : Fin N × Bool × Fin 1 := (⟨0, hN⟩, false, 0)
    let U : ℕ → State N (Fin 1) →ₗᵢ[ℂ] State N (Fin 1) := fun _ ↦ LinearIsometry.id
    have hrun (x : BitString N) (t : ℕ) : run U (ket p₀) x t = ket p₀ := by
      induction t with
      | zero => rfl
      | succ t ih =>
        simp only [run, ih, U, LinearIsometry.id_apply]
        exact phaseOracle_eq_self fun i w ↦ by simp [p₀]
    refine ComputesWithin.isQuantumComputable
      (U := U) (ψ₀ := ket p₀) (S := if b then univ else ∅) ⟨norm_ket p₀, fun x ↦ ?_⟩
    rw [hrun, measureProb_ket]
    cases b <;> simpa [bitVal] using hε

/-- Any constant Boolean function `f` is quantum-computable in `T` queries for `ε ≥ 0`. -/
theorem isQuantumComputable_of_forall_eq {N : ℕ} {ε : ℝ} (hε : 0 ≤ ε) {f : BooleanFunction N}
    (b : Bool) (hf : ∀ x, f x = b) (T : ℕ) : IsQuantumComputable ε f T := by
  have heq : f = fun _ ↦ b := funext hf
  exact heq ▸ isQuantumComputable_const hε b T

private def storeCtrlPerm {N : ℕ} (j : Fin N) : Equiv.Perm (Fin N × Bool × BitString N) where
  toFun p := (p.1, p.2.2 j, Function.update p.2.2 j p.2.1)
  invFun p := (p.1, p.2.2 j, Function.update p.2.2 j p.2.1)
  left_inv := fun ⟨i, b, w⟩ ↦ by
    simp only [Function.update_self, Prod.mk.injEq, true_and]
    ext k; by_cases hk : k = j <;> simp [hk]
  right_inv := fun ⟨i, b, w⟩ ↦ by
    simp only [Function.update_self, Prod.mk.injEq, true_and]
    ext k; by_cases hk : k = j <;> simp [hk]

private def swapIdxPerm {N : ℕ} (j₁ j₂ : Fin N) : Equiv.Perm (Fin N × Bool × BitString N) :=
  Equiv.prodCongr (Equiv.swap j₁ j₂) (Equiv.refl (Bool × BitString N))

/-- Every total Boolean function `f : BooleanFunction N` is quantum-computable in `N` queries with
error `ε ≥ 0` (indeed with exact error `0`) by querying all `N` input coordinates. -/
theorem isQuantumComputable_length {N : ℕ} {ε : ℝ} (hε : 0 ≤ ε) (f : BooleanFunction N) :
    IsQuantumComputable ε f N := by
  cases N with
  | zero => exact Or.inl ⟨rfl, hε⟩
  | succ m =>
    classical
    have hN : 0 < m + 1 := Nat.succ_pos m
    let π : ℕ → Equiv.Perm (Fin (m + 1) × Bool × BitString (m + 1)) := fun t ↦
      if h0 : t = 0 then Equiv.refl _
      else if ht : t < m + 1 then
        swapIdxPerm ⟨t - 1, by omega⟩ ⟨t, ht⟩ * storeCtrlPerm ⟨t - 1, by omega⟩
      else if t = m + 1 then
        storeCtrlPerm ⟨m, by omega⟩
      else Equiv.refl _
    let wPrefix (x : BitString (m + 1)) (s : ℕ) : BitString (m + 1) :=
      fun j ↦ if j.1 < s then x j else false
    let p₀ : Fin (m + 1) × Bool × BitString (m + 1) := (⟨0, hN⟩, false, fun _ ↦ false)
    have hupd (x : BitString (m + 1)) (s : ℕ) (hs : s < m + 1) :
        Function.update (wPrefix x s) ⟨s, hs⟩ (x ⟨s, hs⟩) = wPrefix x (s + 1) := by
      ext j
      by_cases hj : j = ⟨s, hs⟩
      · subst hj; simp [wPrefix]
      · have hne : j.1 ≠ s := fun h ↦ hj (Fin.ext h)
        simp only [Function.update_of_ne hj, wPrefix]
        by_cases hlt : j.1 < s
        · simp [hlt, show j.1 < s + 1 by omega]
        · simp [hlt, show ¬j.1 < s + 1 by omega]
    have hstep (x : BitString (m + 1)) : ∀ t (ht : t < m + 1),
        bitQueryPerm π x t p₀ = (⟨t, ht⟩, false, wPrefix x t) := by
      intro t ht
      induction t with
      | zero =>
        simp only [bitQueryPerm_zero, π, ↓reduceDIte, Equiv.refl_apply, p₀, wPrefix,
          Nat.not_lt_zero, ↓reduceIte]
      | succ t ih =>
        rw [bitQueryPerm_succ, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ih (by omega),
          bitFlip_apply, Bool.false_xor]
        simp only [π, Nat.succ_ne_zero, ↓reduceDIte, ht, Nat.add_sub_cancel, Equiv.Perm.mul_apply,
          storeCtrlPerm, Equiv.coe_fn_mk, swapIdxPerm, Equiv.prodCongr_apply, Equiv.coe_refl,
          Prod.map_apply, Equiv.swap_apply_left, id_eq]
        have hfalse : wPrefix x t ⟨t, by omega⟩ = false := by simp [wPrefix]
        rw [hfalse, hupd x t (by omega)]
    have hfinal (x : BitString (m + 1)) :
        bitQueryPerm π x (m + 1) p₀ = (⟨m, by omega⟩, false, x) := by
      rw [bitQueryPerm_succ, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hstep x m (by omega),
        bitFlip_apply, Bool.false_xor]
      simp only [π, Nat.succ_ne_zero, ↓reduceDIte, lt_irrefl, ↓reduceIte, storeCtrlPerm,
        Equiv.coe_fn_mk]
      have hfalse : wPrefix x m ⟨m, by omega⟩ = false := by simp [wPrefix]
      have hfull : wPrefix x (m + 1) = x := by ext j; simp [wPrefix, j.2]
      rw [hfalse, hupd x m (by omega), hfull]
    let U := bitQueryAlg (m + 1) π LinearIsometry.id LinearIsometry.id
    let S : Finset (Fin (m + 1) × Bool × BitString (m + 1)) :=
      univ.filter fun p ↦ f p.2.2 = true
    refine ComputesWithin.isQuantumComputable (U := U) (ψ₀ := ket p₀) (S := S)
      ⟨norm_ket p₀, fun x ↦ ?_⟩
    rw [run_bitQueryAlg, LinearIsometry.id_apply, LinearIsometry.id_apply, permute_ket,
      hfinal x, measureProb_ket]
    cases hfx : f x <;> simpa [S, bitVal, hfx] using hε

/-- Worst-case quantum query complexity `Q_ε(f)`: the minimum number of phase-oracle queries made
by a quantum algorithm computing `f` within additive error `ε` on every input. -/
noncomputable def queryComplexity {N : ℕ} (ε : ℝ) (f : BooleanFunction N) : ℕ :=
  sInf {T : ℕ | IsQuantumComputable ε f T}

/-- Bounded-error two-sided quantum query complexity `Q_2(f) = Q_{1/3}(f)`. -/
@[expose]
noncomputable def boundedQueryComplexity {N : ℕ} (f : BooleanFunction N) : ℕ :=
  queryComplexity (1 / 3) f

/-- For `ε ≥ 0`, the quantum query complexity `Q_ε(f)` is attained by an algorithm making
`queryComplexity ε f` queries. -/
theorem exists_isQuantumComputable_queryComplexity {N : ℕ} {ε : ℝ} (hε : 0 ≤ ε)
    (f : BooleanFunction N) : IsQuantumComputable ε f (queryComplexity ε f) :=
  Nat.sInf_mem (s := {T : ℕ | IsQuantumComputable ε f T}) ⟨N, isQuantumComputable_length hε f⟩

/-- Bounded-error quantum query complexity `Q_2(f)` is always attained. -/
theorem isQuantumComputable_boundedQueryComplexity {N : ℕ} (f : BooleanFunction N) :
    IsQuantumComputable (1 / 3) f (boundedQueryComplexity f) :=
  exists_isQuantumComputable_queryComplexity (by norm_num) f

/-- Upper-bound step: any `T`-query algorithm computing `f` within error `ε` gives
`Q_ε(f) ≤ T`. -/
theorem IsQuantumComputable.queryComplexity_le {N : ℕ} {ε : ℝ} {f : BooleanFunction N} {T : ℕ}
    (h : IsQuantumComputable ε f T) : queryComplexity ε f ≤ T :=
  Nat.sInf_le h

/-- Lower-bound characterization of `queryComplexity ε f` for `ε ≥ 0`. -/
theorem le_queryComplexity_iff {N : ℕ} {ε : ℝ} (hε : 0 ≤ ε) {f : BooleanFunction N} {d : ℕ} :
    d ≤ queryComplexity ε f ↔ ∀ T, IsQuantumComputable ε f T → d ≤ T :=
  ⟨fun hd _ hT ↦ hd.trans hT.queryComplexity_le,
    fun h ↦ h _ (exists_isQuantumComputable_queryComplexity hε f)⟩

/-- Upper-bound characterization of `queryComplexity ε f` for `ε ≥ 0`. -/
theorem queryComplexity_le_iff {N : ℕ} {ε : ℝ} (hε : 0 ≤ ε) {f : BooleanFunction N} {d : ℕ} :
    queryComplexity ε f ≤ d ↔ ∃ T ≤ d, IsQuantumComputable ε f T :=
  ⟨fun hd ↦ ⟨queryComplexity ε f, hd, exists_isQuantumComputable_queryComplexity hε f⟩,
    fun ⟨_, hTd, hT⟩ ↦ hT.queryComplexity_le.trans hTd⟩

/-- Quantum query complexity is antitone in the error threshold `ε ≥ 0`. -/
theorem queryComplexity_antitone {N : ℕ} {ε ε' : ℝ} (hε : 0 ≤ ε) (hε' : ε ≤ ε')
    (f : BooleanFunction N) : queryComplexity ε' f ≤ queryComplexity ε f :=
  ((exists_isQuantumComputable_queryComplexity hε f).mono_err hε').queryComplexity_le

/-- Every `N`-variable Boolean function has quantum query complexity at most `N` for `ε ≥ 0`. -/
theorem queryComplexity_le_length {N : ℕ} {ε : ℝ} (hε : 0 ≤ ε) (f : BooleanFunction N) :
    queryComplexity ε f ≤ N :=
  (isQuantumComputable_length hε f).queryComplexity_le

/-- Every `N`-variable Boolean function has `Q_2(f) ≤ N`. -/
theorem boundedQueryComplexity_le_length {N : ℕ} (f : BooleanFunction N) :
    boundedQueryComplexity f ≤ N :=
  queryComplexity_le_length (by norm_num) f

/-- Every constant Boolean function has zero quantum query complexity. -/
@[simp]
theorem queryComplexity_const {N : ℕ} (ε : ℝ) (b : Bool) :
    queryComplexity ε (fun _ : BitString N ↦ b) = 0 := by
  by_cases hε : 0 ≤ ε
  · exact Nat.eq_zero_of_le_zero (isQuantumComputable_const hε b 0).queryComplexity_le
  · have hempty : {T : ℕ | IsQuantumComputable ε (fun _ : BitString N ↦ b) T} = ∅ :=
      Set.eq_empty_of_forall_notMem fun _ h ↦ hε h.err_nonneg
    simp [queryComplexity, hempty]

/-- Every constant Boolean function has `Q_2(f) = 0`. -/
theorem queryComplexity_eq_zero_of_forall_eq {N : ℕ} (ε : ℝ) {f : BooleanFunction N} (b : Bool)
    (hf : ∀ x, f x = b) : queryComplexity ε f = 0 := by
  rw [show f = fun _ ↦ b from funext hf, queryComplexity_const]

/-- A Boolean function on `0` variables has zero quantum query complexity. -/
@[simp]
theorem queryComplexity_zero_vars (ε : ℝ) (f : BooleanFunction 0) :
    queryComplexity ε f = 0 :=
  queryComplexity_eq_zero_of_forall_eq ε (f (fun i ↦ i.elim0)) fun x ↦
    congrArg f (Subsingleton.elim x _)

/-- Every non-constant Boolean function requires at least `1` query for any error `0 ≤ ε < 1/2`. -/
theorem one_le_queryComplexity_of_ne {N : ℕ} {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ε < 1 / 2)
    {f : BooleanFunction N} {x y : BitString N} (hxy : f x ≠ f y) :
    1 ≤ queryComplexity ε f := by
  refine (le_queryComplexity_iff hε0).2 fun T hT ↦ ?_
  by_contra hlt
  have hT0 : T = 0 := by omega
  subst hT0
  rcases hT with ⟨rfl, -⟩ | ⟨k, U, ψ₀, S, -, hx⟩
  · exact hxy (congrArg f (Subsingleton.elim x y))
  · have h1 := abs_le.1 (hx x)
    have h2 := abs_le.1 (hx y)
    simp only [run] at h1 h2
    cases hfx : f x <;> cases hfy : f y <;> simp_all [bitVal] <;> linarith

end Complexity

/-! ### Zero-overhead literal projection reductions -/

section Projection

/-- A literal over `N` Boolean variables: either a constant `Bool` or a (possibly negated)
coordinate `x i ^^ neg`. -/
inductive Literal (N : ℕ) : Type
  /-- Fixed Boolean constant requiring zero oracle queries. -/
  | const (val : Bool)
  /-- Input variable `x idx` XORed with `neg`, requiring one oracle query. -/
  | var (idx : Fin N) (neg : Bool)
  deriving DecidableEq

/-- Evaluate a `Literal N` on an input string `x : BitString N`. -/
def Literal.eval {N : ℕ} : Literal N → BitString N → Bool
  | .const b, _ => b
  | .var i neg, x => xor (x i) neg

@[simp]
theorem Literal.eval_const {N : ℕ} (b : Bool) (x : BitString N) :
    (Literal.const b : Literal N).eval x = b := by
  rfl

@[simp]
theorem Literal.eval_var {N : ℕ} (i : Fin N) (neg : Bool) (x : BitString N) :
    (Literal.var i neg).eval x = xor (x i) neg := by
  rfl

/-- Evaluate a coordinatewise literal projection `σ : Fin M → Literal N` on `x : BitString N`. -/
def evalProjection {M N : ℕ} (σ : Fin M → Literal N) (x : BitString N) : BitString M :=
  fun j ↦ (σ j).eval x

@[simp]
theorem evalProjection_apply {M N : ℕ} (σ : Fin M → Literal N) (x : BitString N) (j : Fin M) :
    evalProjection σ x j = (σ j).eval x := by
  rfl

private def projIdleEmb {M N : ℕ} {W : Type*} (i₀ : Fin N) :
    (Fin M × Bool × W) ↪ Fin N × Bool × (Fin M × Bool × W) where
  toFun q := (i₀, false, q)
  inj' _ _ h := (Prod.mk.inj (Prod.mk.inj h).2).2

private def projQueryFun {M N : ℕ} {W : Type*} (i₀ : Fin N) (σ : Fin M → Literal N)
    (q : Fin M × Bool × W) : Fin N × Bool × (Fin M × Bool × W) :=
  match q.2.1, σ q.1 with
  | true, .var i _ => (i, true, q)
  | _, _ => (i₀, false, q)

private def projQueryEmb {M N : ℕ} {W : Type*} (i₀ : Fin N) (σ : Fin M → Literal N) :
    (Fin M × Bool × W) ↪ Fin N × Bool × (Fin M × Bool × W) where
  toFun := projQueryFun i₀ σ
  inj' q₁ q₂ h := by
    dsimp only [projQueryFun] at h
    cases hc₁ : q₁.2.1 <;> cases hσ₁ : σ q₁.1 <;>
      cases hc₂ : q₂.2.1 <;> cases hσ₂ : σ q₂.1 <;>
      simp only [hc₁, hσ₁, hc₂, hσ₂] at h <;>
      exact (Prod.mk.inj (Prod.mk.inj h).2).2

private def projPhaseSign {M N : ℕ} (σ : Fin M → Literal N) (j : Fin M) (c : Bool) : ℂ :=
  match c, σ j with
  | true, .const true => -1
  | true, .var _ true => -1
  | _, _ => 1

private theorem projPhaseSign_mul_self {M N : ℕ} (σ : Fin M → Literal N) (j : Fin M) (c : Bool) :
    projPhaseSign σ j c * projPhaseSign σ j c = 1 := by
  dsimp only [projPhaseSign]
  cases c
  · norm_num
  · cases σ j with
    | const b => cases b <;> norm_num
    | var i neg => cases neg <;> norm_num

private theorem norm_projPhaseSign {M N : ℕ} (σ : Fin M → Literal N) (j : Fin M) (c : Bool) :
    ‖projPhaseSign σ j c‖ = 1 := by
  dsimp only [projPhaseSign]
  cases c
  · simp
  · cases σ j with
    | const b => cases b <;> simp
    | var i neg => cases neg <;> simp

private noncomputable def projFixPhase {M N : ℕ} {W : Type*} [Fintype W]
    (σ : Fin M → Literal N) : State M W ≃ₗᵢ[ℂ] State M W where
  toFun ψ := WithLp.toLp 2 fun q ↦ projPhaseSign σ q.1 q.2.1 * ψ.ofLp q
  invFun ψ := WithLp.toLp 2 fun q ↦ projPhaseSign σ q.1 q.2.1 * ψ.ofLp q
  map_add' ψ φ := by ext q; simp [mul_add]
  map_smul' c ψ := by ext q; simp [mul_left_comm]
  left_inv ψ := by
    ext ⟨j, c, w⟩
    change projPhaseSign σ j c * (projPhaseSign σ j c * ψ.ofLp (j, c, w)) = ψ.ofLp (j, c, w)
    rw [← mul_assoc, projPhaseSign_mul_self, one_mul]
  right_inv ψ := by
    ext ⟨j, c, w⟩
    change projPhaseSign σ j c * (projPhaseSign σ j c * ψ.ofLp (j, c, w)) = ψ.ofLp (j, c, w)
    rw [← mul_assoc, projPhaseSign_mul_self, one_mul]
  norm_map' ψ := by
    refine (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    refine sum_congr rfl fun ⟨j, c, w⟩ _ ↦ ?_
    change ‖projPhaseSign σ j c * ψ.ofLp (j, c, w)‖ ^ 2 = ‖ψ.ofLp (j, c, w)‖ ^ 2
    rw [norm_mul, norm_projPhaseSign, one_mul]

private theorem phaseOracle_projQueryEmb {M N : ℕ} {W : Type*} [Fintype W] (i₀ : Fin N)
    (σ : Fin M → Literal N) (x : BitString N) (ψ : State M W) :
    phaseOracle x (embedBasis (projQueryEmb i₀ σ) ψ) =
      embedBasis (projQueryEmb i₀ σ)
        ((projFixPhase σ).symm (phaseOracle (evalProjection σ x) ψ)) := by
  classical
  ext p
  by_cases hp : ∃ q : Fin M × Bool × W, projQueryEmb i₀ σ q = p
  · obtain ⟨⟨j, c, w⟩, rfl⟩ := hp
    rw [phaseOracle_apply, embedBasis_apply_image, embedBasis_apply_image]
    change (if (projQueryFun i₀ σ (j, c, w)).2.1 && x (projQueryFun i₀ σ (j, c, w)).1
        then -1 else 1) * ψ.ofLp (j, c, w) =
      projPhaseSign σ j c * ((if c && (σ j).eval x then -1 else 1) * ψ.ofLp (j, c, w))
    rw [← mul_assoc]
    refine congrArg (· * ψ.ofLp (j, c, w)) ?_
    have hmatch (lit : Literal N) (c' : Bool) :
        (if (match c', lit with
              | true, .var i _ => (i, true, (j, c', w))
              | _, _ => (i₀, false, (j, c', w))).2.1 &&
            x (match c', lit with
              | true, .var i _ => (i, true, (j, c', w))
              | _, _ => (i₀, false, (j, c', w))).1
          then (-1 : ℂ) else 1) =
        (match c', lit with
          | true, .const true => -1
          | true, .var _ true => -1
          | _, _ => 1) * (if c' && lit.eval x then -1 else 1) := by
      cases c' with
      | false => norm_num
      | true =>
        cases lit with
        | const b => cases b <;> simp
        | var i neg => cases neg <;> cases hx : x i <;> simp [hx]
    exact hmatch (σ j) c
  · rw [phaseOracle_apply, embedBasis_apply_of_not_mem _ _ (not_exists.1 hp),
      embedBasis_apply_of_not_mem _ _ (not_exists.1 hp), mul_zero]

/-- **Promise projection simulation**: if a `T`-query algorithm computes `h` within error `ε` on a
promise set `P`, and a literal projection `σ : Fin M → Literal N` maps every `x : BitString N`
into `P`, then `h ∘ evalProjection σ` is quantum-computable in `T` queries within error `ε`. -/
theorem ComputesWithinOn.isQuantumComputable_comp_evalProjection
    {M N : ℕ} {W : Type*} [Fintype W]
    {U : ℕ → State M W →ₗᵢ[ℂ] State M W} {ψ₀ : State M W} {T : ℕ}
    {S : Finset (Fin M × Bool × W)} {ε : ℝ} {P : BitString M → Prop} {h : BooleanFunction M}
    (hc : ComputesWithinOn U ψ₀ T S ε P h) (σ : Fin M → Literal N)
    (hP : ∀ x : BitString N, P (evalProjection σ x)) :
    IsQuantumComputable ε (h ∘ evalProjection σ) T := by
  have hε : 0 ≤ ε := (abs_nonneg _).trans (hc.2 _ (hP fun _ ↦ false))
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · exact Or.inl ⟨rfl, hε⟩
  · let i₀ : Fin N := ⟨0, hN⟩
    let eIdle := projIdleEmb (M := M) (W := W) i₀
    let eQry := projQueryEmb (W := W) i₀ σ
    let targetEmb (t : ℕ) := if t = T then eIdle else eQry
    let U' : ℕ → State N (Fin M × Bool × W) →ₗᵢ[ℂ] State N (Fin M × Bool × W) := fun t ↦
      if t = 0 then
        transportBasis eIdle (targetEmb 0) (linearIsometryToEquiv (U 0))
      else
        transportBasis eQry (targetEmb t)
          ((projFixPhase σ).trans (linearIsometryToEquiv (U t)))
    have hrun (x : BitString N) : ∀ t ≤ T,
        run U' (embedBasis eIdle ψ₀) x t =
          embedBasis (targetEmb t) (run U ψ₀ (evalProjection σ x) t) := by
      intro t ht
      induction t with
      | zero =>
        simp [run, U']
      | succ t ih =>
        have htne : t ≠ T := by omega
        simp only [run, ih (by omega), targetEmb, htne, ↓reduceIte, eQry, phaseOracle_projQueryEmb]
        simp only [U', Nat.succ_ne_zero, ↓reduceIte, eQry, transportBasis_embedBasis,
          LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.apply_symm_apply,
          linearIsometryToEquiv_apply, targetEmb]
    refine ComputesWithin.isQuantumComputable
      (U := U') (ψ₀ := embedBasis eIdle ψ₀) (S := S.map eIdle)
      ⟨by rw [LinearIsometry.norm_map, hc.1], fun x ↦ ?_⟩
    have hT : run U' (embedBasis eIdle ψ₀) x T =
        embedBasis eIdle (run U ψ₀ (evalProjection σ x) T) := by
      simpa [targetEmb] using hrun x T le_rfl
    rw [hT, measureProb_embedBasis_map]
    exact hc.2 (evalProjection σ x) (hP x)

/-- **Projection simulation**: if `h : BooleanFunction M` is quantum-computable in `T` queries
within error `ε`, then `h ∘ evalProjection σ` is also quantum-computable in `T` queries within
error `ε`, with zero query overhead. -/
theorem IsQuantumComputable.comp_evalProjection {M N : ℕ} {ε : ℝ} {h : BooleanFunction M}
    {T : ℕ} (hc : IsQuantumComputable ε h T) (σ : Fin M → Literal N) :
    IsQuantumComputable ε (h ∘ evalProjection σ) T := by
  rcases hc with ⟨rfl, hε⟩ | ⟨k, U, ψ₀, S, hU⟩
  · exact isQuantumComputable_of_forall_eq hε (h fun i ↦ i.elim0)
      (fun x ↦ congrArg h (Subsingleton.elim _ _)) T
  · exact (computesWithin_iff_on_true.1 hU).isQuantumComputable_comp_evalProjection σ
      (fun _ ↦ trivial)

/-- **Projection reduction for quantum query complexity**: `Q_ε(h ∘ σ) ≤ Q_ε(h)` for `ε ≥ 0`. -/
theorem queryComplexity_comp_evalProjection_le {M N : ℕ} {ε : ℝ} (hε : 0 ≤ ε)
    (h : BooleanFunction M) (σ : Fin M → Literal N) :
    queryComplexity ε (h ∘ evalProjection σ) ≤ queryComplexity ε h :=
  ((exists_isQuantumComputable_queryComplexity hε h).comp_evalProjection σ).queryComplexity_le

/-- **Projection reduction for bounded-error quantum query complexity**:
`Q_2(h ∘ σ) ≤ Q_2(h)`. -/
theorem boundedQueryComplexity_comp_evalProjection_le {M N : ℕ} (h : BooleanFunction M)
    (σ : Fin M → Literal N) :
    boundedQueryComplexity (h ∘ evalProjection σ) ≤ boundedQueryComplexity h :=
  queryComplexity_comp_evalProjection_le (by norm_num) h σ

end Projection

/-! ### Adversary and disjunction lower bounds on `queryComplexity` -/

section LowerBounds

/-- When `f` is constant on `P`, every adversary matrix is zero and `ADV±(P, f) = 0`. -/
theorem generalAdversary_eq_zero_of_subsingleton {N : ℕ} {α : Type*} {P : BitString N → Prop}
    {f : BitString N → α} (hf : ∀ x y, P x → P y → f x = f y) :
    generalAdversary P f = 0 := by
  refine le_antisymm ((generalAdversary_le_iff le_rfl).2 fun Γ _ hΓ ↦ ?_)
    (generalAdversary_nonneg P f)
  have h0 : Γ = 0 := Matrix.ext fun x y ↦ Classical.byContradiction fun hne ↦
    let ⟨hx, hy, hneq⟩ := hΓ x y hne
    hneq (hf x y hx hy)
  simp [h0]

/-- On `0` input variables, `ADV±(P, f) = 0`. -/
@[simp]
theorem generalAdversary_zero_vars {α : Type*} (P : BitString 0 → Prop) (f : BitString 0 → α) :
    generalAdversary P f = 0 :=
  generalAdversary_eq_zero_of_subsingleton fun x y _ _ ↦ congrArg f (Subsingleton.elim x y)

/-- **Negative-weight adversary lower bound on `Q_ε(f)`**:
for `0 ≤ ε ≤ 1/2`, `(1 - 2√(ε(1 - ε))) · ADV±(f) ≤ 2 · Q_ε(f)`.
-/
theorem one_sub_mul_generalAdversary_le_two_mul_queryComplexity {N : ℕ} {ε : ℝ}
    (hε0 : 0 ≤ ε) (hε : 2 * ε ≤ 1) (f : BooleanFunction N) :
    (1 - 2 * √(ε * (1 - ε))) * generalAdversary (fun _ ↦ True) f ≤
      2 * (queryComplexity ε f : ℝ) := by
  rcases exists_isQuantumComputable_queryComplexity hε0 f with ⟨rfl, -⟩ | ⟨k, U, ψ₀, S, hψ, hx⟩
  · simp
  · refine one_sub_mul_generalAdversary_le_boolean U hψ (queryComplexity ε f) S hε0 hε
      (fun x _ hfx ↦ ?_) (fun x _ hfx ↦ ?_)
    · have h := (abs_le.1 (hx x)).1
      simp only [hfx, bitVal_true] at h
      linarith
    · have h := (abs_le.1 (hx x)).2
      simp only [hfx, bitVal_false, sub_zero] at h
      exact h

/-- **Negative-weight adversary lower bound on `Q_2(f)`**: `ADV±(f) ≤ 36 · Q_2(f)`. -/
theorem generalAdversary_le_thirty_six_mul_boundedQueryComplexity {N : ℕ}
    (f : BooleanFunction N) :
    generalAdversary (fun _ ↦ True) f ≤ 36 * (boundedQueryComplexity f : ℝ) := by
  have hadv := one_sub_mul_generalAdversary_le_two_mul_queryComplexity
    (ε := 1 / 3) (by norm_num) (by norm_num) f
  have hsqrt : √((1 / 3 : ℝ) * (1 - 1 / 3)) ≤ 17 / 36 :=
    (Real.sqrt_le_left (by norm_num)).2 (by norm_num)
  have hnn := generalAdversary_nonneg (fun _ ↦ True) f
  change (1 - 2 * √((1 / 3 : ℝ) * (1 - 1 / 3))) * generalAdversary (fun _ ↦ True) f ≤
    2 * (boundedQueryComplexity f : ℝ) at hadv
  nlinarith

/-- The `N`-variable Boolean disjunction `OR_N(x) = true ↔ ∃ i, x i = true`, defined canonically
as the unit-threshold Boolean function `Cslib.BitString.threshold N 1`. -/
def orBool (N : ℕ) : BooleanFunction N :=
  threshold N 1

/-- Semantic characterization of `orBool N`: true iff at least one coordinate is `true`. -/
theorem orBool_eq_true_iff {N : ℕ} (x : BitString N) :
    orBool N x = true ↔ ∃ i : Fin N, x i = true := by
  rw [orBool, threshold_one_right, decide_eq_true_eq]

/-- Semantic characterization of `orBool N x = false`: every coordinate is `false`. -/
theorem orBool_eq_false_iff {N : ℕ} (x : BitString N) :
    orBool N x = false ↔ ∀ i : Fin N, x i = false := by
  rw [Bool.eq_false_iff, ne_eq, orBool_eq_true_iff]
  push Not
  simp

/-- **Quantum query lower bound for Boolean disjunction**:
`N ≤ 16 · Q_2(OR_N)²`.
-/
theorem le_sixteen_mul_boundedQueryComplexity_orBool_sq (N : ℕ) :
    N ≤ 16 * boundedQueryComplexity (orBool N) ^ 2 := by
  rcases isQuantumComputable_boundedQueryComplexity (orBool N) with ⟨rfl, -⟩ | ⟨k, U, ψ₀, S, hψ, hx⟩
  · simp
  · exact card_le_sixteen_mul_sq_of_threshold_one_right U hψ
      (boundedQueryComplexity (orBool N)) S hx

/-- Real square-root form of the disjunction lower bound: `√N ≤ 4 · Q_2(OR_N)`. -/
theorem sqrt_le_four_mul_boundedQueryComplexity_orBool (N : ℕ) :
    √(N : ℝ) ≤ 4 * (boundedQueryComplexity (orBool N) : ℝ) := by
  refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
  have h : (N : ℝ) ≤ 16 * (boundedQueryComplexity (orBool N) : ℝ) ^ 2 := by
    exact_mod_cast le_sixteen_mul_boundedQueryComplexity_orBool_sq N
  linarith

end LowerBounds

end Cslib.Quantum
