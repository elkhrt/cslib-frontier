/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import Cslib.Foundations.Data.BitString
public import CslibFrontier.Foundations.Quantum.DensityMatrix
public import CslibFrontier.Foundations.Quantum.POVM.Density
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import CslibFrontier.Foundations.Quantum.Stabilizer.PauliGroup
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Fintype.BigOperators
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Lagrangian Subspaces, Stabilizer States, and the Stabilizer 3-Design

This module establishes the unitary 3-design property of `n`-qubit stabilizer states from first
principles over `ZMod 2` and `ℂ`, building on
`CslibFrontier.Foundations.Quantum.Stabilizer.PauliGroup`:

* **Lagrangian subspaces and exact counting**: `CslibFrontier.Quantum.IsLagrangian` and the exact
  counting theorem: every `k`-dimensional isotropic subspace `W ⊆ SympVec n` (`k ≤ n`) is
  contained in exactly `lagrangianCount (n - k)` Lagrangian subspaces, where
  `lagrangianCount m = ∏_{j=1}^m (2^j + 1)`.
* **Stabilizer states and projective measurements**: for every Lagrangian subspace `L`, the
  `2^n` stabilizer sign functions `χ` define mutually orthogonal rank-1 projectors
  `stabProjector L χ = 2^{-n} ∑_{u ∈ L} (-1)^{χ(u)} P_u` forming an orthonormal stabilizer basis
  (and hence a projective POVM `stabPOVM L`).
* **Stabilizer 3-design trace identity**: averaging `Tr(A P) Tr(B P) Tr(C P)` over all `n`-qubit
  stabilizer projectors `P` equals
  `[Tr(A)Tr(B)Tr(C) + Tr(A)Tr(BC) + Tr(B)Tr(AC) + Tr(C)Tr(AB) + Tr(ABC) + Tr(ACB)] / (d(d+1)(d+2))`
  for `d = 2^n`.

All results are proved from first principles under standard Lean axioms.

## Main definitions

* `CslibFrontier.Quantum.IsLagrangian`, `CslibFrontier.Quantum.lagrangianCount`: Lagrangian
  subspaces and
  their counting function `∏_{j=1}^n (2^j + 1)`.
* `CslibFrontier.Quantum.StabState`, `CslibFrontier.Quantum.stabProjector`,
  `CslibFrontier.Quantum.stabPOVM`:
  `n`-qubit stabilizer states, rank-1 projectors, and projective stabilizer-basis POVMs.

## Main results

* `CslibFrontier.Quantum.card_lagrangian_containing`: exact count of Lagrangian subspaces containing
  a `k`-dimensional isotropic subspace.
* `CslibFrontier.Quantum.stabilizer_two_design_trace`: 2-design trace identity over stabilizer
  states.
* `CslibFrontier.Quantum.stabilizer_three_design_trace`: 3-design trace identity over stabilizer
  states.
* `CslibFrontier.Quantum.card_stabState_le`: `|StabState n| ≤ 2^(n + n * (n + 3) / 2)`.
-/

public section

namespace CslibFrontier.Quantum

open Matrix Finset Cslib Cslib.Quantum
open scoped MatrixOrder ComplexOrder

/-! ### Symplectic subspaces, Lagrangian subspaces, and exact counting -/

section Symplectic

private local instance instFactPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

private lemma zmod2_cases (x : ZMod 2) : x = 0 ∨ x = 1 := by
  fin_cases x
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- `sympForm` as a `ZMod 2`-bilinear form on `SympVec n`. -/
def sympFormLin (n : ℕ) : SympVec n →ₗ[ZMod 2] SympVec n →ₗ[ZMod 2] ZMod 2 where
  toFun u :=
    { toFun := fun v ↦ sympForm u v
      map_add' := fun v₁ v₂ ↦ sympForm_add_right u v₁ v₂
      map_smul' := fun r v ↦ by
        simpa only [RingHom.id_apply, smul_eq_mul] using sympForm_smul_right r u v }
  map_add' u₁ u₂ := by
    apply LinearMap.ext; intro v
    exact sympForm_add_left u₁ u₂ v
  map_smul' r u := by
    apply LinearMap.ext; intro v
    change sympForm (r • u) v = r * sympForm u v
    exact sympForm_smul_left r u v

/-- A subspace `L` of `SympVec n` is **Lagrangian** (maximal isotropic) iff it is isotropic
and has dimension `n` over `ZMod 2`. -/
def IsLagrangian {n : ℕ} (L : Submodule (ZMod 2) (SympVec n)) : Prop :=
  (∀ u ∈ L, ∀ v ∈ L, sympForm u v = 0) ∧ Module.finrank (ZMod 2) L = n

/-- Number of Lagrangian subspaces of `SympVec m`: `∏_{k=1}^m (2^k + 1)`. -/
def lagrangianCount : ℕ → ℕ
  | 0 => 1
  | m + 1 => (2 ^ (m + 1) + 1) * lagrangianCount m

@[simp]
theorem lagrangianCount_zero : lagrangianCount 0 = 1 := by rfl

theorem lagrangianCount_pos (m : ℕ) : 0 < lagrangianCount m := by
  induction m with
  | zero => exact Nat.one_pos
  | succ m ih => exact Nat.mul_pos (by positivity) ih

theorem lagrangianCount_le (n : ℕ) : lagrangianCount n ≤ 2 ^ (n * (n + 3) / 2) := by
  induction n with
  | zero => simp [lagrangianCount]
  | succ n ih =>
    have hstep : 2 ^ (n + 1) + 1 ≤ 2 ^ (n + 2) := by
      have h1 : 1 ≤ 2 ^ (n + 1) := Nat.one_le_pow _ _ (by norm_num)
      have h2 : 2 ^ (n + 2) = 2 ^ (n + 1) + 2 ^ (n + 1) := by rw [pow_succ]; omega
      omega
    have hexp : n + 2 + n * (n + 3) / 2 = (n + 1) * (n + 4) / 2 := by
      have hmul : (n + 1) * (n + 4) = n * (n + 3) + 2 * (n + 2) := by ring
      omega
    calc
      lagrangianCount (n + 1) = (2 ^ (n + 1) + 1) * lagrangianCount n := rfl
      _ ≤ 2 ^ (n + 2) * 2 ^ (n * (n + 3) / 2) := Nat.mul_le_mul hstep ih
      _ = 2 ^ (n + 2 + n * (n + 3) / 2) := (pow_add 2 _ _).symm
      _ = 2 ^ ((n + 1) * (n + 4) / 2) := by rw [hexp]

/-! #### Abstract finite symplectic spaces over `ZMod 2` -/

private structure SymplecticSpace (V : Type*) [AddCommGroup V] [Module (ZMod 2) V] where
  form : V →ₗ[ZMod 2] V →ₗ[ZMod 2] ZMod 2
  alt : ∀ v, form v v = 0
  nondeg : ∀ v, (∀ w, form v w = 0) → v = 0

private lemma SymplecticSpace.symm {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (S : SymplecticSpace V) (u v : V) : S.form u v = S.form v u := by
  have h := S.alt (u + v)
  simp only [map_add, LinearMap.add_apply, S.alt, zero_add, add_zero] at h
  have hchar : S.form v u + S.form v u = 0 := by
    generalize S.form v u = x
    rcases zmod2_cases x with rfl | rfl <;> decide
  have : S.form u v = S.form u v + (S.form v u + S.form v u) := by rw [hchar, add_zero]
  rw [add_comm (S.form v u)] at h
  rw [← add_assoc, h, zero_add] at this
  exact this

private def SymplecticSpace.perp {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (S : SymplecticSpace V) (W : Submodule (ZMod 2) V) : Submodule (ZMod 2) V where
  carrier := {v | ∀ w ∈ W, S.form v w = 0}
  add_mem' ha hb w hw := by simp [ha w hw, hb w hw]
  zero_mem' w _ := by simp
  smul_mem' c v hv w hw := by simp [hv w hw]

private lemma map_submoduleOf_eq {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    {W P : Submodule (ZMod 2) V} (h : W ≤ P) :
    (W.submoduleOf P).map P.subtype = W := by
  ext x
  simp only [Submodule.mem_map, Submodule.submoduleOf, Submodule.mem_comap, Submodule.coe_subtype,
    Subtype.exists, exists_and_right, exists_eq_right]
  exact ⟨fun ⟨_, hx⟩ ↦ hx, fun hx ↦ ⟨h hx, hx⟩⟩

private theorem SymplecticSpace.finrank_perp {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] (S : SymplecticSpace V) (W : Submodule (ZMod 2) V) :
    Module.finrank (ZMod 2) (S.perp W) + Module.finrank (ZMod 2) W =
      Module.finrank (ZMod 2) V := by
  classical
  let φ : V →ₗ[ZMod 2] Module.Dual (ZMod 2) W :=
    { toFun := fun v ↦ (S.form v).comp W.subtype
      map_add' := fun u v ↦ by ext ⟨w, hw⟩; simp
      map_smul' := fun c v ↦ by ext ⟨w, hw⟩; simp }
  have hker : LinearMap.ker φ = S.perp W := by
    ext v
    simp only [LinearMap.mem_ker, φ, LinearMap.ext_iff, LinearMap.coe_mk, AddHom.coe_mk,
      LinearMap.comp_apply, Submodule.coe_subtype, LinearMap.zero_apply, Subtype.forall]
    rfl
  let ψ : V →ₗ[ZMod 2] Module.Dual (ZMod 2) V := S.form
  have hψ_inj : Function.Injective ψ := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro v hv
    exact S.nondeg v (fun w ↦ by simpa [ψ] using LinearMap.congr_fun hv w)
  have hψ_surj : Function.Surjective ψ := by
    have hfin := LinearMap.finrank_range_add_finrank_ker ψ
    rw [LinearMap.ker_eq_bot.mpr hψ_inj, finrank_bot, add_zero] at hfin
    have hdual : Module.finrank (ZMod 2) (Module.Dual (ZMod 2) V) = Module.finrank (ZMod 2) V :=
      Subspace.dual_finrank_eq
    rw [← hdual] at hfin
    exact LinearMap.range_eq_top.mp (Submodule.eq_top_of_finrank_eq hfin)
  have hφ_surj : Function.Surjective φ := by
    intro g
    obtain ⟨g', hg'⟩ := g.exists_extend
    obtain ⟨v, hv⟩ := hψ_surj g'
    refine ⟨v, ?_⟩
    ext ⟨w, hw⟩
    exact (congrArg (fun f : Module.Dual (ZMod 2) V ↦ f w) hv).trans
      (by simpa using LinearMap.congr_fun hg' ⟨w, hw⟩)
  have hrk := LinearMap.finrank_range_add_finrank_ker φ
  rw [LinearMap.range_eq_top.mpr hφ_surj, finrank_top, Subspace.dual_finrank_eq, hker,
    add_comm] at hrk
  exact hrk

/-- Factored symplectic quotient reduction: for any isotropic subspace `W` of dimension `k` in a
`2m`-dimensional `ZMod 2`-symplectic space `(V, S)`, the quotient `Q = W⊥ / W` is a
`2(m - k)`-dimensional symplectic space whose Lagrangian subspaces correspond bijectively with
the Lagrangian subspaces of `V` containing `W`. -/
private theorem SymplecticSpace.exists_quotient_equiv {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (S : SymplecticSpace V) {m : ℕ} (hdim : Module.finrank (ZMod 2) V = 2 * m)
    (W : Submodule (ZMod 2) V) (hW_iso : W ≤ S.perp W) :
    let k := Module.finrank (ZMod 2) W
    let Wp := S.perp W
    let Q := Wp ⧸ W.submoduleOf Wp
    k ≤ m ∧ ∃ (SQ : SymplecticSpace Q),
      Module.finrank (ZMod 2) Q = 2 * (m - k) ∧
      Nonempty ({L : Submodule (ZMod 2) V //
          (∀ u ∈ L, ∀ v ∈ L, S.form u v = 0) ∧ Module.finrank (ZMod 2) L = m ∧ W ≤ L} ≃
        {M : Submodule (ZMod 2) Q //
          (∀ u ∈ M, ∀ w ∈ M, SQ.form u w = 0) ∧ Module.finrank (ZMod 2) M = m - k}) := by
  classical
  intro k Wp Q
  have hWp_dim : Module.finrank (ZMod 2) Wp + k = 2 * m := by
    simpa [hdim] using S.finrank_perp W
  have hk_le_m : k ≤ m := by
    have hle := Submodule.finrank_mono hW_iso
    dsimp only [k, Wp] at hWp_dim ⊢
    omega
  have hsubW_dim : Module.finrank (ZMod 2) (W.submoduleOf Wp) = k := by
    rw [LinearEquiv.finrank_eq (Submodule.equivMapOfInjective Wp.subtype Wp.injective_subtype
      (W.submoduleOf Wp)), map_submoduleOf_eq hW_iso]
  have hQ_dim : Module.finrank (ZMod 2) Q = 2 * (m - k) := by
    have h1 : Module.finrank (ZMod 2) Q + Module.finrank (ZMod 2) (W.submoduleOf Wp) =
        Module.finrank (ZMod 2) Wp := Submodule.finrank_quotient_add_finrank (W.submoduleOf Wp)
    rw [hsubW_dim] at h1
    omega
  let formWp : Wp →ₗ[ZMod 2] Wp →ₗ[ZMod 2] ZMod 2 :=
    { toFun := fun x ↦ (S.form x.1).comp Wp.subtype
      map_add' := fun x y ↦ by ext z; simp
      map_smul' := fun c x ↦ by ext z; simp }
  let formQ : Q →ₗ[ZMod 2] Q →ₗ[ZMod 2] ZMod 2 :=
    Submodule.liftQ _
      (LinearMap.flip (Submodule.liftQ _ (LinearMap.flip formWp) (by
        intro x hx; ext y
        exact y.2 x.1 hx)))
      (by
        intro x hx
        apply LinearMap.ext; intro q
        obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q
        change formWp x y = 0
        rw [show formWp x y = S.form x.1 y.1 from rfl, S.symm]
        exact y.2 x.1 hx)
  let hSQ : SymplecticSpace Q :=
    { form := formQ
      alt := fun q ↦ by
        obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
        exact S.alt x.1
      nondeg := fun q hq ↦ by
        obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
        rw [Submodule.Quotient.mk_eq_zero]
        change x.1 ∈ W
        have hx_perp : x.1 ∈ S.perp Wp := fun y hy ↦ hq (Submodule.Quotient.mk ⟨y, hy⟩)
        have hW_le_pp : W ≤ S.perp Wp := fun w hw y hy ↦ by rw [S.symm]; exact hy w hw
        have hdim_pp : Module.finrank (ZMod 2) (S.perp Wp) = k := by
          have h2 : Module.finrank (ZMod 2) (S.perp Wp) + Module.finrank (ZMod 2) Wp = 2 * m := by
            simpa [hdim] using S.finrank_perp Wp
          omega
        exact (Submodule.eq_of_le_of_finrank_eq hW_le_pp hdim_pp.symm) ▸ hx_perp }
  refine ⟨hk_le_m, hSQ, hQ_dim, ⟨?_⟩⟩
  refine
    { toFun := fun ⟨L, hL_iso, hL_dim, hWL⟩ ↦
        ⟨(L.submoduleOf Wp).map (Submodule.mkQ _), ?_, ?_⟩
      invFun := fun ⟨M, hM_iso, hM_dim⟩ ↦
        ⟨(M.comap (Submodule.mkQ _)).map Wp.subtype, ?_, ?_, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    exact hL_iso x.1 hx y.1 hy
  · have hL_le_Wp : L ≤ Wp := fun x hx w hw ↦ hL_iso x hx w (hWL hw)
    have hsub_dim : Module.finrank (ZMod 2) (L.submoduleOf Wp) = m := by
      rw [LinearEquiv.finrank_eq (Submodule.equivMapOfInjective Wp.subtype Wp.injective_subtype _),
        map_submoduleOf_eq hL_le_Wp, hL_dim]
    have h1 := LinearMap.finrank_range_add_finrank_ker
      ((Submodule.mkQ (W.submoduleOf Wp)).domRestrict (L.submoduleOf Wp))
    have hker_eq : LinearMap.ker ((Submodule.mkQ (W.submoduleOf Wp)).domRestrict
        (L.submoduleOf Wp)) = (W.submoduleOf Wp).submoduleOf (L.submoduleOf Wp) := by
      ext ⟨x, _⟩
      exact Submodule.Quotient.mk_eq_zero _
    have hrange_eq : LinearMap.range ((Submodule.mkQ (W.submoduleOf Wp)).domRestrict
        (L.submoduleOf Wp)) = (L.submoduleOf Wp).map (Submodule.mkQ _) := by
      ext q; simp
    have hker_dim : Module.finrank (ZMod 2) ((W.submoduleOf Wp).submoduleOf
        (L.submoduleOf Wp)) = k := by
      rw [LinearEquiv.finrank_eq (Submodule.equivMapOfInjective (L.submoduleOf Wp).subtype
        (L.submoduleOf Wp).injective_subtype _),
        map_submoduleOf_eq (show W.submoduleOf Wp ≤ L.submoduleOf Wp from fun x hx ↦ hWL hx),
        hsubW_dim]
    rw [hrange_eq, hker_eq, hker_dim, hsub_dim] at h1
    exact Nat.eq_sub_of_add_eq h1
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    exact hM_iso (Submodule.Quotient.mk x) hx (Submodule.Quotient.mk y) hy
  · rw [LinearEquiv.finrank_eq
      (Submodule.equivMapOfInjective Wp.subtype Wp.injective_subtype _).symm]
    have h1 := LinearMap.finrank_range_add_finrank_ker
      ((Submodule.mkQ (W.submoduleOf Wp)).domRestrict (M.comap (Submodule.mkQ _)))
    have hker_eq : LinearMap.ker ((Submodule.mkQ (W.submoduleOf Wp)).domRestrict
        (M.comap (Submodule.mkQ _))) =
        (W.submoduleOf Wp).submoduleOf (M.comap (Submodule.mkQ _)) := by
      ext ⟨x, _⟩
      exact Submodule.Quotient.mk_eq_zero _
    have hrange_eq : LinearMap.range ((Submodule.mkQ (W.submoduleOf Wp)).domRestrict
        (M.comap (Submodule.mkQ _))) = M := by
      ext q
      simp only [LinearMap.mem_range, LinearMap.domRestrict_apply, Submodule.mkQ_apply]
      exact ⟨fun ⟨⟨x, hx⟩, h⟩ ↦ h ▸ hx, fun hq ↦
        let ⟨x, hx⟩ := Submodule.Quotient.mk_surjective _ q
        ⟨⟨x, by simpa [hx] using hq⟩, hx⟩⟩
    have hW_le_comap : W.submoduleOf Wp ≤ M.comap (Submodule.mkQ _) := fun x hx ↦ by
      simp [Submodule.mem_comap, (Submodule.Quotient.mk_eq_zero _).mpr hx]
    have hker_dim : Module.finrank (ZMod 2) ((W.submoduleOf Wp).submoduleOf
        (M.comap (Submodule.mkQ _))) = k := by
      rw [LinearEquiv.finrank_eq (Submodule.equivMapOfInjective (M.comap (Submodule.mkQ _)).subtype
        (M.comap (Submodule.mkQ _)).injective_subtype _),
        map_submoduleOf_eq hW_le_comap, hsubW_dim]
    rw [hrange_eq, hker_eq, hker_dim, hM_dim] at h1
    omega
  · intro w hw
    refine ⟨⟨w, hW_iso hw⟩, ?_, rfl⟩
    simp [(Submodule.Quotient.mk_eq_zero _).mpr
      (show (⟨w, hW_iso hw⟩ : Wp) ∈ W.submoduleOf Wp from hw)]
  · rintro ⟨L, hL_iso, hL_dim, hWL⟩
    apply Subtype.ext; ext x
    have hL_le_Wp : L ≤ Wp := fun y hy w hw ↦ hL_iso y hy w (hWL hw)
    simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.mkQ_apply, Submodule.coe_subtype]
    refine ⟨?_, fun hx ↦ ⟨⟨x, hL_le_Wp hx⟩, ⟨⟨x, hL_le_Wp hx⟩, hx, rfl⟩, rfl⟩⟩
    rintro ⟨y, ⟨z, hz, hzy⟩, rfl⟩
    have hdiff : y.1 - z.1 ∈ W := (Submodule.Quotient.eq (p := W.submoduleOf Wp)).mp hzy.symm
    simpa only [Submodule.coe_subtype, add_sub_cancel] using L.add_mem hz (hWL hdiff)
  · rintro ⟨M, hM_iso, hM_dim⟩
    apply Subtype.ext; ext q
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    simp only [Submodule.submoduleOf]
    refine ⟨?_, fun hx ↦ ⟨x, ⟨x, hx, rfl⟩, rfl⟩⟩
    rintro ⟨y, ⟨z, hz, hzy⟩, hy⟩
    exact (Wp.injective_subtype hzy ▸ hy) ▸ hz

/-- Any finite-dimensional `ZMod 2` symplectic space of dimension `2m` has exactly
`lagrangianCount m` Lagrangian subspaces. -/
private theorem card_lagrangian_abstract :
    ∀ (m : ℕ) (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
      [Finite V] (S : SymplecticSpace V) (_ : Module.finrank (ZMod 2) V = 2 * m),
      Nat.card {L : Submodule (ZMod 2) V //
        (∀ u ∈ L, ∀ v ∈ L, S.form u v = 0) ∧ Module.finrank (ZMod 2) L = m} =
      lagrangianCount m := by
  intro m
  induction m with
  | zero =>
    intro V _ _ _ _ S hdim
    classical
    have : Fintype V := Fintype.ofFinite V
    rw [Nat.card_eq_fintype_card]
    have hsub : Subsingleton V := (Module.finrank_zero_iff (R := ZMod 2)).mp (by omega)
    have hcard : Fintype.card {L : Submodule (ZMod 2) V //
        (∀ u ∈ L, ∀ v ∈ L, S.form u v = 0) ∧ Module.finrank (ZMod 2) L = 0} = 1 := by
      rw [Fintype.card_eq_one_iff]
      refine ⟨⟨⊥, ⟨fun u hu _ _ ↦ by
        rw [Submodule.mem_bot] at hu; subst hu; simp, finrank_bot _ _⟩⟩, ?_⟩
      rintro ⟨L, _⟩
      exact Subtype.ext (Subsingleton.elim L ⊥)
    simpa [lagrangianCount] using hcard
  | succ m ih =>
    intro V _ _ _ _ S hdim
    classical
    have : Fintype V := Fintype.ofFinite V
    rw [Nat.card_eq_fintype_card]
    let Lag := {L : Submodule (ZMod 2) V //
      (∀ u ∈ L, ∀ v ∈ L, S.form u v = 0) ∧ Module.finrank (ZMod 2) L = m + 1}
    let Vnz := {v : V // v ≠ 0}
    have hfiber (v : Vnz) :
        Fintype.card {L : Lag // v.1 ∈ L.1} = lagrangianCount m := by
      let W : Submodule (ZMod 2) V := Submodule.span (ZMod 2) {v.1}
      have hW_dim : Module.finrank (ZMod 2) W = 1 := finrank_span_singleton v.2
      have hW_iso : W ≤ S.perp W := by
        intro x hx w hw
        rw [Submodule.mem_span_singleton] at hx hw
        obtain ⟨c, rfl⟩ := hx; obtain ⟨d, rfl⟩ := hw
        simp [S.alt]
      obtain ⟨_, SQ, hQ_dim, ⟨heq⟩⟩ := S.exists_quotient_equiv hdim W hW_iso
      rw [hW_dim, Nat.add_sub_cancel] at hQ_dim heq
      let e1 : {L : Lag // v.1 ∈ L.1} ≃
          {L : Submodule (ZMod 2) V //
            (∀ u ∈ L, ∀ v ∈ L, S.form u v = 0) ∧ Module.finrank (ZMod 2) L = m + 1 ∧ W ≤ L} :=
        { toFun := fun ⟨⟨L, h1, h2⟩, hv⟩ ↦
            ⟨L, h1, h2, Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hv)⟩
          invFun := fun ⟨L, h1, h2, hWL⟩ ↦
            ⟨⟨L, h1, h2⟩, hWL (Submodule.subset_span rfl)⟩
          left_inv := fun _ ↦ rfl
          right_inv := fun _ ↦ rfl }
      rw [Fintype.card_congr (e1.trans heq), ← Nat.card_eq_fintype_card]
      exact ih _ SQ hQ_dim
    have hcount1 :
        ∑ L : Lag, Fintype.card {v : Vnz // v.1 ∈ L.1} =
          Fintype.card Lag * (2 ^ (m + 1) - 1) := by
      have hLcard (L : Lag) : Fintype.card {v : Vnz // v.1 ∈ L.1} = 2 ^ (m + 1) - 1 := by
        have htot : Fintype.card L.1 = 2 ^ (m + 1) := by
          simpa [ZMod.card, L.2.2] using Module.card_eq_pow_finrank (K := ZMod 2) (V := L.1)
        let e : {v : Vnz // v.1 ∈ L.1} ≃ {x : L.1 // x ≠ 0} :=
          { toFun := fun ⟨⟨v, hv⟩, hvL⟩ ↦ ⟨⟨v, hvL⟩, fun h ↦ hv (congrArg Subtype.val h)⟩
            invFun := fun ⟨⟨v, hvL⟩, hv⟩ ↦ ⟨⟨v, fun h ↦ hv (Subtype.ext h)⟩, hvL⟩
            left_inv := fun _ ↦ rfl, right_inv := fun _ ↦ rfl }
        rw [Fintype.card_congr e, Fintype.card_subtype_compl, htot,
          Fintype.card_eq_one_iff.mpr ⟨⟨0, rfl⟩, fun ⟨_, h⟩ ↦ Subtype.ext h⟩]
      simp [hLcard]
    have hcount2 :
        ∑ v : Vnz, Fintype.card {L : Lag // v.1 ∈ L.1} =
          (2 ^ (2 * (m + 1)) - 1) * lagrangianCount m := by
      have hVcard : Fintype.card V = 2 ^ (2 * (m + 1)) := by
        simpa [ZMod.card, hdim] using Module.card_eq_pow_finrank (K := ZMod 2) (V := V)
      have hVnz : Fintype.card Vnz = 2 ^ (2 * (m + 1)) - 1 := by
        rw [Fintype.card_subtype_compl, hVcard,
          Fintype.card_eq_one_iff.mpr ⟨⟨0, rfl⟩, fun ⟨_, h⟩ ↦ Subtype.ext h⟩]
      simp [hfiber, hVnz]
    have hmul : Fintype.card Lag * (2 ^ (m + 1) - 1) =
        (2 ^ (2 * (m + 1)) - 1) * lagrangianCount m := by
      rw [← hcount1, ← hcount2]
      simp only [Fintype.card_subtype, Finset.card_filter]
      exact Finset.sum_comm
    have hfac : 2 ^ (2 * (m + 1)) - 1 = (2 ^ (m + 1) + 1) * (2 ^ (m + 1) - 1) := by
      have h1 : 1 ≤ 2 ^ (m + 1) := Nat.one_le_pow _ _ (by norm_num)
      rw [two_mul, pow_add]
      zify [h1, show 1 ≤ 2 ^ (m + 1) * 2 ^ (m + 1) from Nat.mul_pos h1 h1]; ring
    rw [hfac, mul_assoc, mul_comm (2 ^ (m + 1) - 1), ← mul_assoc] at hmul
    have hpos : 0 < 2 ^ (m + 1) - 1 := Nat.sub_pos_of_lt (by simp)
    simpa only [Lag, lagrangianCount, mul_comm] using Nat.eq_of_mul_eq_mul_right hpos hmul

/-- Finite enumeration of Lagrangian subspaces of `SympVec n`. -/
noncomputable instance instFintypeLagrangian (n : ℕ) :
    Fintype {L : Submodule (ZMod 2) (SympVec n) // IsLagrangian L} := by
  classical
  infer_instance

/-- Exact count of Lagrangian subspaces of `SympVec n` containing an isotropic subspace `W`
of dimension `k ≤ n`. -/
theorem card_lagrangian_containing {n : ℕ} (W : Submodule (ZMod 2) (SympVec n))
    (hW_iso : ∀ u ∈ W, ∀ v ∈ W, sympForm u v = 0) :
    Nat.card {L : Submodule (ZMod 2) (SympVec n) // IsLagrangian L ∧ W ≤ L} =
      lagrangianCount (n - Module.finrank (ZMod 2) W) := by
  classical
  rw [Nat.card_eq_fintype_card]
  let S : SymplecticSpace (SympVec n) :=
    ⟨sympFormLin n, sympForm_self, fun _ ↦ sympForm_nondegenerate⟩
  have hdimV : Module.finrank (ZMod 2) (SympVec n) = 2 * n := by
    rw [show Module.finrank (ZMod 2) (SympVec n) =
        Module.finrank (ZMod 2) (Fin n → ZMod 2) + Module.finrank (ZMod 2) (Fin n → ZMod 2) from
      Module.finrank_prod]
    simp [two_mul]
  obtain ⟨_, SQ, hQ_dim, ⟨heq⟩⟩ := S.exists_quotient_equiv hdimV W hW_iso
  let e0 : {L : Submodule (ZMod 2) (SympVec n) // IsLagrangian L ∧ W ≤ L} ≃
      {L : Submodule (ZMod 2) (SympVec n) //
        (∀ u ∈ L, ∀ v ∈ L, S.form u v = 0) ∧ Module.finrank (ZMod 2) L = n ∧ W ≤ L} :=
    { toFun := fun ⟨L, ⟨h1, h2⟩, h3⟩ ↦ ⟨L, h1, h2, h3⟩
      invFun := fun ⟨L, h1, h2, h3⟩ ↦ ⟨L, ⟨h1, h2⟩, h3⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  rw [Fintype.card_congr (e0.trans heq), ← Nat.card_eq_fintype_card]
  exact card_lagrangian_abstract (n - Module.finrank (ZMod 2) W) _ SQ hQ_dim

/-- Total number of Lagrangian subspaces of `SympVec n` is `lagrangianCount n`. -/
theorem card_lagrangian (n : ℕ) :
    Fintype.card {L : Submodule (ZMod 2) (SympVec n) // IsLagrangian L} = lagrangianCount n := by
  classical
  have h := card_lagrangian_containing (n := n) ⊥ (fun u hu _ _ ↦ by
    rw [Submodule.mem_bot] at hu; subst hu; exact sympForm_zero_left _)
  rw [Nat.card_eq_fintype_card, finrank_bot, Nat.sub_zero] at h
  have heq : Fintype.card {L : Submodule (ZMod 2) (SympVec n) // IsLagrangian L} =
      Fintype.card {L : Submodule (ZMod 2) (SympVec n) // IsLagrangian L ∧
        (⊥ : Submodule _ _) ≤ L} :=
    Fintype.card_congr
      { toFun := fun ⟨L, hL⟩ ↦ ⟨L, hL, bot_le⟩
        invFun := fun ⟨L, hL, _⟩ ↦ ⟨L, hL⟩
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl }
  exact heq.trans h

end Symplectic

/-! ### Stabilizer states, projective stabilizer POVMs, and the 3-design trace identity -/

section StabilizerStates

private local instance instFactPrimeTwo' : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- Sign value `±1` for a Boolean stabilizer sign bit (`false ↦ 1`, `true ↦ -1`). -/
def stabSignVal (b : Bool) : ℂ := if b then -1 else 1

@[simp]
theorem stabSignVal_false : stabSignVal false = 1 := by rfl

@[simp]
theorem stabSignVal_true : stabSignVal true = -1 := by rfl

/-- Complex sign coefficient `(-1)^{χ(u)}` inside `L`, and `0` outside `L`. -/
noncomputable def stabSignCoeff {n : ℕ} (L : Submodule (ZMod 2) (SympVec n))
    (χ : SympVec n → Bool) (u : SympVec n) : ℂ :=
  @ite _ (u ∈ L) (Classical.propDecidable _) (stabSignVal (χ u)) 0

/-- A valid Boolean stabilizer sign function on a Lagrangian subspace `L`: `χ(u) = false` outside
`L`, and `(-1)^{χ(u)} (-1)^{χ(v)} P_{u+v} = (-1)^{χ(u+v)} P_u P_v` for all `u, v ∈ L`. -/
def IsStabSign {n : ℕ} (L : Submodule (ZMod 2) (SympVec n)) (χ : SympVec n → Bool) : Prop :=
  (∀ u, u ∉ L → χ u = false) ∧
  (∀ u ∈ L, ∀ v ∈ L,
    (stabSignVal (χ u) * stabSignVal (χ v)) • pauli (u + v) =
      stabSignVal (χ (u + v)) • (pauli u * pauli v))

/-- Finite enumeration of valid Boolean stabilizer signs on a subspace `L`. -/
noncomputable instance instFintypeStabSign {n : ℕ} (L : Submodule (ZMod 2) (SympVec n)) :
    Fintype {χ : SympVec n → Bool // IsStabSign L χ} := by
  classical
  infer_instance

/-- An `n`-qubit stabilizer state, represented by its Lagrangian subspace `L` and sign `χ`. -/
structure StabState (n : ℕ) where
  /-- The Lagrangian stabilizer subspace `L ⊆ SympVec n`. -/
  L : Submodule (ZMod 2) (SympVec n)
  /-- Proof that `L` is Lagrangian. -/
  isLagrangian : IsLagrangian L
  /-- Stabilizer sign function `χ : SympVec n → Bool`. -/
  sign : SympVec n → Bool
  /-- Proof that `sign` is a valid stabilizer sign on `L`. -/
  isStabSign : IsStabSign L sign

/-- The rank-1 stabilizer state projector `P_{L,χ} = 2^{-n} ∑_{u ∈ L} (-1)^{χ(u)} P_u`. -/
noncomputable def stabProjector {n : ℕ} (s : StabState n) :
    Matrix (BitString n) (BitString n) ℂ :=
  (((2 : ℂ) ^ n)⁻¹) • ∑ u : SympVec n, stabSignCoeff s.L s.sign u • pauli u

private lemma stabSignVal_mul_self (b : Bool) : stabSignVal b * stabSignVal b = 1 := by
  cases b <;> simp [stabSignVal]

private lemma stabSign_zero {n : ℕ} {L : Submodule (ZMod 2) (SympVec n)} {χ : SympVec n → Bool}
    (hχ : IsStabSign L χ) : χ 0 = false := by
  have h := hχ.2 0 L.zero_mem 0 L.zero_mem
  rw [add_zero, pauli_zero, Matrix.one_mul] at h
  have h1 := congrFun (congrFun h (fun _ ↦ false)) (fun _ ↦ false)
  simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at h1
  cases h0 : χ 0
  · rfl
  · rw [h0] at h1; norm_num [stabSignVal] at h1

private lemma pauli_ne_zero {n : ℕ} (u : SympVec n) : pauli u ≠ 0 := by
  intro hz
  have hsq := pauli_mul_self u
  rw [hz, Matrix.mul_zero] at hsq
  have h1 := congrFun (congrFun hsq (fun _ ↦ false)) (fun _ ↦ false)
  simp only [Matrix.zero_apply, Matrix.one_apply_eq] at h1
  exact zero_ne_one h1

private lemma exists_dual_eq_one {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    {v : V} (hv : v ≠ 0) :
    ∃ φ : Module.Dual (ZMod 2) V, φ v = 1 := by
  let e : (ZMod 2) ≃ₗ[ZMod 2] Submodule.span (ZMod 2) {v} :=
    LinearEquiv.toSpanNonzeroSingleton (ZMod 2) V v hv
  obtain ⟨φ, hφ⟩ := e.symm.toLinearMap.exists_extend
  refine ⟨φ, ?_⟩
  have h1 : e 1 = ⟨v, Submodule.mem_span_singleton_self v⟩ := by
    simp [e, LinearEquiv.toSpanNonzeroSingleton_apply]
  have h2 := LinearMap.congr_fun hφ ⟨v, Submodule.mem_span_singleton_self v⟩
  rw [← h1] at h2
  have h3 : φ v = φ (e 1).1 := by rw [h1]
  rw [h3]
  simpa using h2

/-- Ordered product of matrices indexed by `Fin m`, avoiding `CommMonoid` requirements. -/
private def finMatProd {n : ℕ} :
    (m : ℕ) → (Fin m → Matrix (BitString n) (BitString n) ℂ) →
      Matrix (BitString n) (BitString n) ℂ
  | 0, _ => 1
  | m + 1, f => f 0 * finMatProd m (fun i ↦ f i.succ)

/-- Every Lagrangian subspace admits a valid stabilizer sign function. -/
theorem exists_stabSign {n : ℕ} (L : Submodule (ZMod 2) (SympVec n)) (hL : IsLagrangian L) :
    ∃ χ : SympVec n → Bool, IsStabSign L χ := by
  classical
  let b : Module.Basis (Fin n) (ZMod 2) L := Module.finBasisOfFinrankEq (ZMod 2) L hL.2
  let elem {m : ℕ} (v : Fin m → SympVec n) (c : Fin m → ZMod 2) (i : Fin m) :
      Matrix (BitString n) (BitString n) ℂ :=
    if c i = 0 then 1 else pauli (v i)
  let opOf (u : L) : Matrix (BitString n) (BitString n) ℂ :=
    finMatProd n (elem (fun i ↦ (b i).1) (b.repr u))
  have hb_comm (i j : Fin n) : pauli (b i).1 * pauli (b j).1 = pauli (b j).1 * pauli (b i).1 := by
    have h := pauli_comm (b i).1 (b j).1
    rw [hL.1 (b i).1 (b i).2 (b j).1 (b j).2] at h
    simpa using h
  have hcomm_prod : ∀ {m : ℕ} (v : Fin m → SympVec n) (c : Fin m → ZMod 2)
      (M : Matrix (BitString n) (BitString n) ℂ),
      (∀ j, M * pauli (v j) = pauli (v j) * M) →
      M * finMatProd m (elem v c) = finMatProd m (elem v c) * M := by
    intro m
    induction m with
    | zero => intro _ _ M _; simp [finMatProd]
    | succ m ih =>
      intro v c M hM
      simp only [finMatProd]
      have h0 : M * elem v c 0 = elem v c 0 * M := by
        dsimp only [elem]; split_ifs <;> simp [hM 0]
      rw [← Matrix.mul_assoc, h0, Matrix.mul_assoc,
        ih (fun j ↦ v j.succ) (fun j ↦ c j.succ) M (fun j ↦ hM j.succ), ← Matrix.mul_assoc]
  have hop_mul (u w : L) : opOf (u + w) = opOf u * opOf w := by
    have hgen : ∀ {m : ℕ} (v : Fin m → SympVec n)
        (hcomm : ∀ i j, pauli (v i) * pauli (v j) = pauli (v j) * pauli (v i))
        (c d : Fin m → ZMod 2),
        finMatProd m (elem v (c + d)) = finMatProd m (elem v c) * finMatProd m (elem v d) := by
      intro m
      induction m with
      | zero => intro _ _ _ _; simp [finMatProd]
      | succ m ih =>
        intro v hcomm c d
        simp only [finMatProd]
        have hih := ih (fun i ↦ v i.succ) (fun i j ↦ hcomm i.succ j.succ)
          (fun i ↦ c i.succ) (fun i ↦ d i.succ)
        change elem v (c + d) 0 * finMatProd m (elem (fun i ↦ v i.succ)
          ((fun i ↦ c i.succ) + fun i ↦ d i.succ)) = _
        rw [hih]
        have h0 : elem v (c + d) 0 = elem v c 0 * elem v d 0 := by
          have h10 : (1 : ZMod 2) ≠ 0 := by decide
          have h11 : (1 : ZMod 2) + 1 = 0 := by decide
          rcases zmod2_cases (c 0) with hc0 | hc0 <;> rcases zmod2_cases (d 0) with hd0 | hd0 <;>
            simp [elem, hc0, hd0, pauli_mul_self, h10, h11]
        have hc0 : elem v d 0 * finMatProd m (elem (fun i ↦ v i.succ) (fun i ↦ c i.succ)) =
            finMatProd m (elem (fun i ↦ v i.succ) (fun i ↦ c i.succ)) * elem v d 0 := by
          dsimp only [elem]
          split_ifs
          · simp
          · exact hcomm_prod (fun i ↦ v i.succ) (fun i ↦ c i.succ) (pauli (v 0))
              (fun j ↦ hcomm 0 j.succ)
        rw [h0, Matrix.mul_assoc (elem v c 0), ← Matrix.mul_assoc (elem v d 0), hc0,
          Matrix.mul_assoc, ← Matrix.mul_assoc]
    simpa [opOf, map_add] using hgen (fun i ↦ (b i).1) hb_comm (b.repr u) (b.repr w)
  have hop_eq (u : L) : ∃ s : Bool, opOf u = stabSignVal s • pauli u.1 := by
    have hgen : ∀ {m : ℕ} (v : Fin m → SympVec n) (f : Fin m → ZMod 2),
        ∃ c : ℂ, c ≠ 0 ∧
          finMatProd m (elem v f) = c • pauli (∑ i : Fin m, f i • v i) := by
      intro m
      induction m with
      | zero => intro _ _; exact ⟨1, one_ne_zero, by simp [finMatProd, pauli_zero]⟩
      | succ m ih =>
        intro v f
        obtain ⟨c, hc, hih⟩ := ih (fun i ↦ v i.succ) (fun i ↦ f i.succ)
        have hstep : finMatProd (m + 1) (elem v f) =
            elem v f 0 * (c • pauli (∑ i : Fin m, f i.succ • v i.succ)) := by
          simpa only [finMatProd] using congrArg (elem v f 0 * ·) hih
        rw [hstep, Fin.sum_univ_succ]
        dsimp only [elem]
        rcases zmod2_cases (f 0) with hf0 | hf0
        · exact ⟨c, hc, by simp [hf0]⟩
        · refine ⟨pauliPhase (v 0) (∑ i : Fin m, f i.succ • v i.succ) * c,
            mul_ne_zero ?_ hc, ?_⟩
          · intro hph
            have hmul := pauli_mul_eq_phase_smul (v 0) (∑ i : Fin m, f i.succ • v i.succ)
            rw [hph, zero_smul] at hmul
            refine pauli_ne_zero (∑ i : Fin m, f i.succ • v i.succ) ?_
            rw [← Matrix.one_mul (pauli _), ← pauli_mul_self (v 0), Matrix.mul_assoc, hmul,
              Matrix.mul_zero]
          · simp only [hf0, show (1 : ZMod 2) ≠ 0 by decide, ite_false, one_smul, Matrix.mul_smul,
              pauli_mul_eq_phase_smul, smul_smul, mul_comm]
    have hsum : ∑ i : Fin n, (b.repr u i) • (b i).1 = u.1 := by
      simpa only [Submodule.coe_sum, Submodule.coe_smul_of_tower] using
        congrArg Subtype.val (b.sum_repr u)
    obtain ⟨c, _, hce⟩ := hgen (fun i ↦ (b i).1) (b.repr u)
    rw [hsum] at hce
    change opOf u = c • pauli u.1 at hce
    have hsq : opOf u * opOf u = 1 := by
      have huu : u + u = 0 := by
        rw [← two_smul (ZMod 2) u, show (2 : ZMod 2) = 0 from rfl, zero_smul]
      rw [← hop_mul u u, huu]
      have hzero_prod : ∀ {m : ℕ} (v : Fin m → SympVec n), finMatProd m (elem v 0) = 1 := by
        intro m; induction m with
        | zero => intro _; rfl
        | succ m ih =>
          intro v; change elem v 0 0 * finMatProd m (elem (fun i ↦ v i.succ) 0) = 1
          rw [ih]; simp [elem]
      simpa [opOf] using hzero_prod (fun i ↦ (b i).1)
    rw [hce, Matrix.smul_mul, Matrix.mul_smul, smul_smul, pauli_mul_self] at hsq
    have hcc : c * c = 1 := by
      simpa [Matrix.one_apply] using congrFun (congrFun hsq (fun _ ↦ false)) (fun _ ↦ false)
    rcases mul_eq_zero.mp (show (c - 1) * (c + 1) = 0 by linear_combination hcc) with h1 | h2
    · exact ⟨false, by rw [sub_eq_zero.mp h1] at hce; simpa [stabSignVal] using hce⟩
    · exact ⟨true, by rw [eq_neg_of_add_eq_zero_left h2] at hce; simpa [stabSignVal] using hce⟩
  let χ : SympVec n → Bool := fun u ↦ if hu : u ∈ L then (hop_eq ⟨u, hu⟩).choose else false
  refine ⟨χ, fun u hu ↦ by simp [χ, hu], fun u hu v hv ↦ ?_⟩
  have huv : u + v ∈ L := L.add_mem hu hv
  simp only [χ, hu, hv, huv, dite_true]
  have hmul : stabSignVal (hop_eq ⟨u + v, huv⟩).choose • pauli (u + v) =
      (stabSignVal (hop_eq ⟨u, hu⟩).choose • pauli u) *
        (stabSignVal (hop_eq ⟨v, hv⟩).choose • pauli v) := by
    rw [← (hop_eq ⟨u + v, huv⟩).choose_spec, ← (hop_eq ⟨u, hu⟩).choose_spec,
      ← (hop_eq ⟨v, hv⟩).choose_spec]
    exact hop_mul ⟨u, hu⟩ ⟨v, hv⟩
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul] at hmul
  have hres := congrArg ((stabSignVal (hop_eq ⟨u, hu⟩).choose *
    stabSignVal (hop_eq ⟨v, hv⟩).choose * stabSignVal (hop_eq ⟨u + v, huv⟩).choose) • ·) hmul
  simp only [smul_smul] at hres
  have h1 : stabSignVal (hop_eq ⟨u, hu⟩).choose * stabSignVal (hop_eq ⟨v, hv⟩).choose *
      stabSignVal (hop_eq ⟨u + v, huv⟩).choose * stabSignVal (hop_eq ⟨u + v, huv⟩).choose =
      stabSignVal (hop_eq ⟨u, hu⟩).choose * stabSignVal (hop_eq ⟨v, hv⟩).choose := by
    rw [mul_assoc, stabSignVal_mul_self, mul_one]
  have h2 : stabSignVal (hop_eq ⟨u, hu⟩).choose * stabSignVal (hop_eq ⟨v, hv⟩).choose *
      stabSignVal (hop_eq ⟨u + v, huv⟩).choose *
        (stabSignVal (hop_eq ⟨u, hu⟩).choose * stabSignVal (hop_eq ⟨v, hv⟩).choose) =
      stabSignVal (hop_eq ⟨u + v, huv⟩).choose := by
    cases (hop_eq ⟨u, hu⟩).choose <;> cases (hop_eq ⟨v, hv⟩).choose <;>
      cases (hop_eq ⟨u + v, huv⟩).choose <;> norm_num [stabSignVal]
  rw [h1, h2] at hres
  exact hres

private lemma isStabSign_xor_dual {n : ℕ} {L : Submodule (ZMod 2) (SympVec n)}
    [DecidablePred (· ∈ L)] {χ : SympVec n → Bool} (hχ : IsStabSign L χ)
    (φ : Module.Dual (ZMod 2) L) :
    IsStabSign L (fun u ↦ if hu : u ∈ L then xor (χ u) (decide (φ ⟨u, hu⟩ = 1)) else false) := by
  refine ⟨fun u hu ↦ by simp [hu], fun u hu v hv ↦ ?_⟩
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  have huv : u + v ∈ L := L.add_mem hu hv
  simp only [hu, hv, huv, dite_true]
  have hφ : φ ⟨u + v, huv⟩ = φ ⟨u, hu⟩ + φ ⟨v, hv⟩ := φ.map_add ⟨u, hu⟩ ⟨v, hv⟩
  have hmul_s :
      stabSignVal (xor (χ u) (decide (φ ⟨u, hu⟩ = 1))) *
        stabSignVal (xor (χ v) (decide (φ ⟨v, hv⟩ = 1))) =
      (if φ ⟨u + v, huv⟩ = 1 then -1 else 1) * (stabSignVal (χ u) * stabSignVal (χ v)) := by
    rw [hφ]; generalize φ ⟨u, hu⟩ = a; generalize φ ⟨v, hv⟩ = b
    rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases b with rfl | rfl <;>
      cases χ u <;> cases χ v <;> simp [stabSignVal, h11]
  have hsing :
      stabSignVal (xor (χ (u + v)) (decide (φ ⟨u + v, huv⟩ = 1))) =
        (if φ ⟨u + v, huv⟩ = 1 then -1 else 1) * stabSignVal (χ (u + v)) := by
    generalize φ ⟨u + v, huv⟩ = c
    rcases zmod2_cases c with rfl | rfl <;> cases χ (u + v) <;> simp [stabSignVal]
  rw [hmul_s, hsing, ← smul_smul, hχ.2 u hu v hv, smul_smul]

/-- There are exactly `2^n` valid stabilizer sign functions on any Lagrangian subspace `L`. -/
theorem card_stabSign {n : ℕ} (L : Submodule (ZMod 2) (SympVec n)) (hL : IsLagrangian L) :
    Fintype.card {χ : SympVec n → Bool // IsStabSign L χ} = 2 ^ n := by
  classical
  obtain ⟨χ₀, hχ₀⟩ := exists_stabSign L hL
  let e : {χ : SympVec n → Bool // IsStabSign L χ} ≃ Module.Dual (ZMod 2) L :=
    { toFun := fun ⟨χ, hχ⟩ ↦
        { toFun := fun u ↦ if χ u.1 = χ₀ u.1 then 0 else 1
          map_add' := fun u v ↦ by
            have h1' : (stabSignVal (χ u.1) * stabSignVal (χ v.1) *
                stabSignVal (χ (u.1 + v.1))) • pauli (u.1 + v.1) = pauli u.1 * pauli v.1 := by
              have := congrArg (stabSignVal (χ (u.1 + v.1)) • ·) (hχ.2 u.1 u.2 v.1 v.2)
              simp only [smul_smul, stabSignVal_mul_self, one_smul] at this
              simpa [mul_comm, mul_assoc, mul_left_comm] using this
            have h2' : (stabSignVal (χ₀ u.1) * stabSignVal (χ₀ v.1) *
                stabSignVal (χ₀ (u.1 + v.1))) • pauli (u.1 + v.1) = pauli u.1 * pauli v.1 := by
              have := congrArg (stabSignVal (χ₀ (u.1 + v.1)) • ·) (hχ₀.2 u.1 u.2 v.1 v.2)
              simp only [smul_smul, stabSignVal_mul_self, one_smul] at this
              simpa [mul_comm, mul_assoc, mul_left_comm] using this
            have heq_sc : stabSignVal (χ u.1) * stabSignVal (χ v.1) *
                stabSignVal (χ (u.1 + v.1)) =
                stabSignVal (χ₀ u.1) * stabSignVal (χ₀ v.1) * stabSignVal (χ₀ (u.1 + v.1)) := by
              by_contra hne
              have hsub : ((stabSignVal (χ u.1) * stabSignVal (χ v.1) *
                  stabSignVal (χ (u.1 + v.1))) -
                  (stabSignVal (χ₀ u.1) * stabSignVal (χ₀ v.1) *
                  stabSignVal (χ₀ (u.1 + v.1)))) • pauli (u.1 + v.1) = 0 := by
                rw [sub_smul, h1', h2', sub_self]
              exact pauli_ne_zero _ ((smul_eq_zero.mp hsub).resolve_left (sub_ne_zero.mpr hne))
            change (if χ (u.1 + v.1) = χ₀ (u.1 + v.1) then (0 : ZMod 2) else 1) =
              (if χ u.1 = χ₀ u.1 then 0 else 1) + (if χ v.1 = χ₀ v.1 then 0 else 1)
            cases hcu : χ u.1 <;> cases hcv : χ v.1 <;> cases hcuv : χ (u.1 + v.1) <;>
              cases h0u : χ₀ u.1 <;> cases h0v : χ₀ v.1 <;> cases h0uv : χ₀ (u.1 + v.1) <;>
              simp only [hcu, hcv, hcuv, h0u, h0v, h0uv, stabSignVal, ite_true, ite_false,
                Bool.false_eq_true, Bool.true_eq_false] at heq_sc ⊢ <;>
              norm_num at heq_sc <;> decide
          map_smul' := fun r u ↦ by
            rcases zmod2_cases r with rfl | rfl
            · simp only [zero_smul, RingHom.id_apply, smul_eq_mul, zero_mul]
              have hz : (0 : L).1 = 0 := rfl
              rw [hz, stabSign_zero hχ, stabSign_zero hχ₀]; simp
            · simp }
      invFun := fun φ ↦ ⟨_, isStabSign_xor_dual hχ₀ φ⟩
      left_inv := fun ⟨χ, hχ⟩ ↦ by
        apply Subtype.ext; funext u
        by_cases hu : u ∈ L
        · simp only [hu, dite_true, LinearMap.coe_mk, AddHom.coe_mk]
          have hbool : ∀ a b : Bool,
              xor b (decide ((if a = b then (0 : ZMod 2) else 1) = 1)) = a := by
            intro a b; cases a <;> cases b <;> decide
          exact hbool (χ u) (χ₀ u)
        · simp only [hu, dite_false, hχ.1 u hu]
      right_inv := fun φ ↦ by
        ext ⟨u, hu⟩
        simp only [LinearMap.coe_mk, AddHom.coe_mk, hu, dite_true]
        generalize φ ⟨u, hu⟩ = x
        rcases zmod2_cases x with rfl | rfl <;> cases χ₀ u <;> simp }
  have : Finite (Module.Dual (ZMod 2) L) := Finite.of_injective DFunLike.coe DFunLike.coe_injective
  let : Fintype (Module.Dual (ZMod 2) L) := Fintype.ofFinite _
  rw [Fintype.card_congr e]
  have h := Module.card_eq_pow_finrank (K := ZMod 2) (V := Module.Dual (ZMod 2) L)
  rw [ZMod.card, Subspace.dual_finrank_eq, hL.2] at h
  exact h

/-- Averaging `(-1)^{χ(u) + χ(v) + χ(w)} P_w` over all valid signs `χ` on a Lagrangian `L` kills
every triple with `u + v + w ≠ 0`, and evaluates to `2^n P_u P_v` when `w = u + v`. -/
theorem sum_stabSign_triple {n : ℕ} (L : Submodule (ZMod 2) (SympVec n)) (hL : IsLagrangian L)
    (u v w : SympVec n) (hu : u ∈ L) (hv : v ∈ L) (hw : w ∈ L) :
    ∑ χ : {χ : SympVec n → Bool // IsStabSign L χ},
      (stabSignVal (χ.1 u) * stabSignVal (χ.1 v) * stabSignVal (χ.1 w)) • pauli w =
      if w = u + v then ((2 : ℂ) ^ n) • (pauli u * pauli v) else 0 := by
  classical
  have htriple (χ : {χ : SympVec n → Bool // IsStabSign L χ}) :
      (stabSignVal (χ.1 u) * stabSignVal (χ.1 v) * stabSignVal (χ.1 (u + v))) • pauli (u + v) =
        pauli u * pauli v := by
    have h1 := congrArg (stabSignVal (χ.1 (u + v)) • ·) (χ.2.2 u hu v hv)
    simp only [smul_smul, stabSignVal_mul_self, one_smul] at h1
    simpa [mul_comm, mul_assoc, mul_left_comm] using h1
  by_cases h : w = u + v
  · subst h
    simp only [ite_true]
    simp_rw [htriple]
    rw [Finset.sum_const, Finset.card_univ, card_stabSign L hL, ← Nat.cast_smul_eq_nsmul ℂ,
      Nat.cast_pow, Nat.cast_ofNat]
  · simp only [h, ite_false]
    have hne0 : (⟨u + v + w, L.add_mem (L.add_mem hu hv) hw⟩ : L) ≠ 0 := by
      intro h0
      have h0' : u + v + w = 0 := congrArg Subtype.val h0
      apply h
      have huv2 : (u + v) + (u + v) = 0 := by
        rw [← two_smul (ZMod 2) (u + v), show (2 : ZMod 2) = 0 from rfl, zero_smul]
      calc
        w = (u + v + w) + (u + v) := by
          have h1 : u + v + w + (u + v) = w + ((u + v) + (u + v)) := by abel
          rw [h1, huv2, add_zero]
        _ = u + v := by rw [h0', zero_add]
    obtain ⟨φ₀, hφ₀⟩ := exists_dual_eq_one hne0
    let τ : {χ : SympVec n → Bool // IsStabSign L χ} → {χ : SympVec n → Bool // IsStabSign L χ} :=
      fun ⟨χ, hχ⟩ ↦ ⟨_, isStabSign_xor_dual hχ φ₀⟩
    have hτ_invol : Function.Involutive τ := fun ⟨χ, hχ⟩ ↦ by
      apply Subtype.ext; funext x
      by_cases hx : x ∈ L
      · simp only [τ, hx, dite_true]; cases χ x <;> cases decide (φ₀ ⟨x, hx⟩ = 1) <;> rfl
      · simp only [τ, hx, dite_false, hχ.1 x hx]
    have hτ_neg (χ : {χ : SympVec n → Bool // IsStabSign L χ}) :
        stabSignVal ((τ χ).1 u) * stabSignVal ((τ χ).1 v) * stabSignVal ((τ χ).1 w) =
          -(stabSignVal (χ.1 u) * stabSignVal (χ.1 v) * stabSignVal (χ.1 w)) := by
      have h11 : (1 : ZMod 2) + 1 = 0 := by decide
      simp only [τ, hu, hv, hw, dite_true]
      have hadd : φ₀ ⟨u, hu⟩ + φ₀ ⟨v, hv⟩ + φ₀ ⟨w, hw⟩ = 1 := by
        calc
          φ₀ ⟨u, hu⟩ + φ₀ ⟨v, hv⟩ + φ₀ ⟨w, hw⟩
              = φ₀ (⟨u, hu⟩ + ⟨v, hv⟩) + φ₀ ⟨w, hw⟩ := by rw [← φ₀.map_add]
          _ = φ₀ (⟨u, hu⟩ + ⟨v, hv⟩ + ⟨w, hw⟩) := by rw [← φ₀.map_add]
          _ = 1 := hφ₀
      generalize φ₀ ⟨u, hu⟩ = a at hadd
      generalize φ₀ ⟨v, hv⟩ = b at hadd
      generalize φ₀ ⟨w, hw⟩ = c at hadd
      rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases b with rfl | rfl <;>
        rcases zmod2_cases c with rfl | rfl <;>
        cases χ.1 u <;> cases χ.1 v <;> cases χ.1 w <;>
        simp [stabSignVal, h11] at hadd ⊢
    have hsum_eq :
        ∑ χ : {χ : SympVec n → Bool // IsStabSign L χ},
          (stabSignVal (χ.1 u) * stabSignVal (χ.1 v) * stabSignVal (χ.1 w)) • pauli w =
        -(∑ χ : {χ : SympVec n → Bool // IsStabSign L χ},
          (stabSignVal (χ.1 u) * stabSignVal (χ.1 v) * stabSignVal (χ.1 w)) • pauli w) := by
      have hsum_eq' :
          ∑ χ : {χ : SympVec n → Bool // IsStabSign L χ},
            (stabSignVal ((τ χ).1 u) * stabSignVal ((τ χ).1 v) *
              stabSignVal ((τ χ).1 w)) • pauli w =
          ∑ χ : {χ : SympVec n → Bool // IsStabSign L χ},
            (stabSignVal (χ.1 u) * stabSignVal (χ.1 v) * stabSignVal (χ.1 w)) • pauli w :=
        Fintype.sum_equiv hτ_invol.toPerm
          (fun χ ↦ (stabSignVal ((τ χ).1 u) * stabSignVal ((τ χ).1 v) *
            stabSignVal ((τ χ).1 w)) • pauli w)
          (fun χ ↦ (stabSignVal (χ.1 u) * stabSignVal (χ.1 v) * stabSignVal (χ.1 w)) • pauli w)
          (fun _ ↦ rfl)
      conv_lhs => rw [← hsum_eq']
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun χ _ ↦ by rw [hτ_neg, neg_smul]
    have h2z : (2 : ℂ) • ∑ χ : {χ : SympVec n → Bool // IsStabSign L χ},
        (stabSignVal (χ.1 u) * stabSignVal (χ.1 v) * stabSignVal (χ.1 w)) • pauli w = 0 := by
      rw [two_smul]
      conv_rhs => rw [← add_neg_cancel (∑ χ : {χ : SympVec n → Bool // IsStabSign L χ},
        (stabSignVal (χ.1 u) * stabSignVal (χ.1 v) * stabSignVal (χ.1 w)) • pauli w)]
      rw [← hsum_eq]
    exact (smul_eq_zero.mp h2z).resolve_left (by norm_num)

/-- Every stabilizer projector is Hermitian, idempotent, PSD, and has trace `1`. -/
theorem stabProjector_isDensityMatrix {n : ℕ} (s : StabState n) :
    IsDensityMatrix (stabProjector s) := by
  classical
  have hH : (stabProjector s).IsHermitian := by
    unfold stabProjector
    have hsum : (∑ u : SympVec n, stabSignCoeff s.L s.sign u • pauli u).IsHermitian := by
      rw [Matrix.IsHermitian, conjTranspose_sum]
      refine Finset.sum_congr rfl fun u _ ↦ ?_
      rw [conjTranspose_smul, (pauli_isHermitian u).eq]
      unfold stabSignCoeff
      by_cases hu : u ∈ s.L
      · simp only [hu, ite_true]
        cases s.sign u <;> simp [stabSignVal]
      · simp [hu]
    have hc : star (((2 : ℂ) ^ n)⁻¹) = ((2 : ℂ) ^ n)⁻¹ := by
      have : (((2 : ℂ) ^ n)⁻¹) = ((((2 : ℝ) ^ n)⁻¹ : ℝ) : ℂ) := by push_cast; rfl
      rw [this, Complex.star_def, Complex.conj_ofReal]
    rw [Matrix.IsHermitian, conjTranspose_smul, hc, hsum.eq]
  have hsq : stabProjector s * stabProjector s = stabProjector s := by
    unfold stabProjector
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Finset.sum_mul]
    simp_rw [Finset.mul_sum, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    have hrestrict :
        ∑ u : SympVec n, ∑ v : SympVec n,
            (stabSignCoeff s.L s.sign u * stabSignCoeff s.L s.sign v) • (pauli u * pauli v) =
          ∑ u ∈ (Finset.univ.filter fun u ↦ u ∈ s.L),
            ∑ v ∈ (Finset.univ.filter fun v ↦ v ∈ s.L),
              stabSignVal (s.sign (u + v)) • pauli (u + v) := by
      simp_rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun u _ ↦ ?_
      by_cases hu : u ∈ s.L
      · simp only [hu, ite_true]
        refine Finset.sum_congr rfl fun v _ ↦ ?_
        by_cases hv : v ∈ s.L
        · simp only [hv, ite_true, stabSignCoeff, hu]
          have h1 := s.isStabSign.2 u hu v hv
          have h2 := congrArg (stabSignVal (s.sign (u + v)) • ·) h1
          simp only [smul_smul, stabSignVal_mul_self, one_smul] at h2
          rw [← h2, smul_smul]
          congr 1
          cases s.sign u <;> cases s.sign v <;> cases s.sign (u + v) <;> norm_num [stabSignVal]
        · simp [hv, stabSignCoeff]
      · simp [hu, stabSignCoeff]
    rw [hrestrict]
    have hreindex :
        ∑ u ∈ (Finset.univ.filter fun u ↦ u ∈ s.L),
          ∑ v ∈ (Finset.univ.filter fun v ↦ v ∈ s.L),
            stabSignVal (s.sign (u + v)) • pauli (u + v) =
        ((2 : ℂ) ^ n) • ∑ w : SympVec n, stabSignCoeff s.L s.sign w • pauli w := by
      have hcardL : (Finset.univ.filter fun u : SympVec n ↦ u ∈ s.L).card = 2 ^ n := by
        have h1 := Module.card_eq_pow_finrank (K := ZMod 2) (V := s.L)
        rw [ZMod.card, s.isLagrangian.2] at h1
        simpa [Fintype.card_subtype] using h1
      have hinner (u : SympVec n) (hu : u ∈ s.L) :
          ∑ v ∈ (Finset.univ.filter fun v ↦ v ∈ s.L),
            stabSignVal (s.sign (u + v)) • pauli (u + v) =
            ∑ w : SympVec n, stabSignCoeff s.L s.sign w • pauli w := by
        have hsub : ∑ w : SympVec n, stabSignCoeff s.L s.sign w • pauli w =
            ∑ w ∈ (Finset.univ.filter fun w ↦ w ∈ s.L),
              stabSignVal (s.sign w) • pauli w := by
          rw [Finset.sum_filter]
          refine Finset.sum_congr rfl fun w _ ↦ ?_
          by_cases hw : w ∈ s.L <;> simp [stabSignCoeff, hw]
        rw [hsub]
        refine Finset.sum_nbij (fun v ↦ u + v) (fun v hv ↦ by
          simp only [mem_filter, mem_univ, true_and] at hv ⊢
          exact s.L.add_mem hu hv) (fun _ _ _ _ h ↦ add_left_cancel h) (fun w hw ↦ by
          have hw' : w ∈ s.L := (mem_filter.mp hw).2
          refine ⟨u + w, mem_filter.mpr ⟨mem_univ _, s.L.add_mem hu hw'⟩, ?_⟩
          have huu : u + u = 0 := by
            rw [← two_smul (ZMod 2) u, show (2 : ZMod 2) = 0 from rfl, zero_smul]
          dsimp only
          rw [← add_assoc, huu, zero_add]) (fun _ _ ↦ rfl)
      rw [Finset.sum_congr rfl (fun u hu ↦ hinner u (mem_filter.mp hu).2), Finset.sum_const,
        hcardL, ← Nat.cast_smul_eq_nsmul ℂ, Nat.cast_pow, Nat.cast_ofNat]
    rw [hreindex, smul_smul, mul_assoc, inv_mul_cancel₀ (pow_ne_zero n (by norm_num)), mul_one]
  have htr : (stabProjector s).trace = 1 := by
    unfold stabProjector
    rw [trace_smul, trace_sum]
    simp_rw [trace_smul, pauli_trace]
    rw [Finset.sum_eq_single (0 : SympVec n)]
    · simp only [ite_true, stabSignCoeff, s.L.zero_mem, stabSign_zero s.isStabSign, stabSignVal,
        Bool.false_eq_true, ite_false, smul_eq_mul, one_mul]
      exact inv_mul_cancel₀ (pow_ne_zero n (by norm_num))
    · intro u _ hu; simp [hu]
    · intro h; exact absurd (mem_univ _) h
  have hpsd : (stabProjector s).PosSemidef := by
    have h1 : stabProjector s = (stabProjector s)ᴴ * stabProjector s := by
      rw [hH.eq, hsq]
    rw [h1]
    exact posSemidef_conjTranspose_mul_self _
  exact ⟨hpsd, htr⟩

/-- For any fixed Lagrangian subspace `L`, the `2^n` stabilizer projectors form a projective POVM
summing to the identity. -/
noncomputable def stabPOVM {n : ℕ} (L : Submodule (ZMod 2) (SympVec n)) (hL : IsLagrangian L) :
    POVM {χ : SympVec n → Bool // IsStabSign L χ} (BitString n) where
  effect χ := stabProjector ⟨L, hL, χ.1, χ.2⟩
  posSemidef χ := (stabProjector_isDensityMatrix ⟨L, hL, χ.1, χ.2⟩).posSemidef
  sum_effect := by
    classical
    simp only [stabProjector, ← Finset.smul_sum]
    rw [Finset.sum_comm]
    have hinner (u : SympVec n) :
        ∑ χ : {χ : SympVec n → Bool // IsStabSign L χ}, stabSignCoeff L χ.1 u • pauli u =
          if u = 0 then ((2 : ℂ) ^ n) • (1 : Matrix (BitString n) (BitString n) ℂ) else 0 := by
      by_cases hu : u ∈ L
      · have h := sum_stabSign_triple L hL 0 0 u L.zero_mem L.zero_mem hu
        have h0 (χ : {χ : SympVec n → Bool // IsStabSign L χ}) :
            stabSignVal (χ.1 0) = 1 := by simp [stabSign_zero χ.2, stabSignVal]
        simp_rw [h0, one_mul, add_zero, pauli_zero, Matrix.one_mul] at h
        simpa [stabSignCoeff, hu] using h
      · simp only [show u ≠ 0 from fun h0 ↦ hu (h0 ▸ L.zero_mem), ite_false]
        exact Finset.sum_eq_zero fun χ _ ↦ by simp [stabSignCoeff, hu]
    simp_rw [hinner]
    rw [Finset.sum_ite_eq' Finset.univ (0 : SympVec n)]
    simp only [mem_univ, ite_true, smul_smul]
    rw [inv_mul_cancel₀ (pow_ne_zero n (by norm_num)), one_smul]

/-- The `χ`-th effect of `stabPOVM L hL` is `stabProjector ⟨L, hL, χ.1, χ.2⟩`. -/
theorem stabPOVM_effect {n : ℕ} (L : Submodule (ZMod 2) (SympVec n)) (hL : IsLagrangian L)
    (χ : {χ : SympVec n → Bool // IsStabSign L χ}) :
    (stabPOVM L hL).effect χ = stabProjector ⟨L, hL, χ.1, χ.2⟩ := by rfl

/-- Bijection between `StabState n` and pairs `(L, χ)`. -/
noncomputable def stabStateEquiv (n : ℕ) :
    StabState n ≃ Σ L : {L : Submodule (ZMod 2) (SympVec n) // IsLagrangian L},
      {χ : SympVec n → Bool // IsStabSign L.1 χ} where
  toFun s := ⟨⟨s.L, s.isLagrangian⟩, ⟨s.sign, s.isStabSign⟩⟩
  invFun p := ⟨p.1.1, p.1.2, p.2.1, p.2.2⟩
  left_inv s := by cases s; rfl
  right_inv p := by rcases p with ⟨⟨_, _⟩, ⟨_, _⟩⟩; rfl

noncomputable instance instFintypeStabState (n : ℕ) : Fintype (StabState n) := by
  classical
  exact Fintype.ofEquiv _ (stabStateEquiv n).symm

theorem card_stabState (n : ℕ) :
    Fintype.card (StabState n) = 2 ^ n * lagrangianCount n := by
  classical
  rw [Fintype.card_congr (stabStateEquiv n), Fintype.card_sigma,
    Finset.sum_congr rfl (fun L _ ↦ card_stabSign L.1 L.2),
    Finset.sum_const, Finset.card_univ, card_lagrangian, smul_eq_mul, mul_comm]

theorem card_stabState_le (n : ℕ) :
    Fintype.card (StabState n) ≤ 2 ^ (n + n * (n + 3) / 2) := by
  rw [card_stabState, pow_add]
  exact Nat.mul_le_mul_left _ (lagrangianCount_le n)

/-- **Stabilizer 3-design trace identity**:
for all `n : ℕ` and matrices `A, B, C` on `BitString n`, with `d = 2^n`,
`∑_{s ∈ StabState n} Tr(A P_s) Tr(B P_s) Tr(C P_s)` equals
`|StabState n| / (d(d+1)(d+2)) * (Tr(A)Tr(B)Tr(C) + Tr(A)Tr(BC) + Tr(B)Tr(AC) + Tr(C)Tr(AB) +
  Tr(ABC) + Tr(ACB))`.
-/
theorem stabilizer_three_design_trace {n : ℕ}
    (A B C : Matrix (BitString n) (BitString n) ℂ) :
    (∑ s : StabState n, (A * stabProjector s).trace * (B * stabProjector s).trace *
        (C * stabProjector s).trace) =
      ((Fintype.card (StabState n) : ℂ) /
        ((2 : ℂ) ^ n * ((2 : ℂ) ^ n + 1) * ((2 : ℂ) ^ n + 2))) *
      (A.trace * B.trace * C.trace + A.trace * (B * C).trace + B.trace * (A * C).trace +
        C.trace * (A * B).trace + (A * B * C).trace + (A * C * B).trace) := by
  classical
  set d : ℂ := (2 : ℂ) ^ n
  set N0 : ℂ := (lagrangianCount n : ℂ)
  have hd_ne : d ≠ 0 := pow_ne_zero n (by norm_num)
  have hd1_ne : d + 1 ≠ 0 := by
    have : (0 : ℝ) < (2 : ℝ) ^ n + 1 := by positivity
    simpa [d] using Complex.ofReal_ne_zero.mpr this.ne'
  have hd2_ne : d + 2 ≠ 0 := by
    have : (0 : ℝ) < (2 : ℝ) ^ n + 2 := by positivity
    simpa [d] using Complex.ofReal_ne_zero.mpr this.ne'
  let f (u v : SympVec n) : ℂ :=
    (A * pauli u).trace * (B * pauli v).trace * (C * (pauli u * pauli v)).trace
  have hstep1 :
      (∑ s : StabState n, (A * stabProjector s).trace * (B * stabProjector s).trace *
          (C * stabProjector s).trace) =
        (d ^ 2)⁻¹ * ∑ L : {L : Submodule (ZMod 2) (SympVec n) // IsLagrangian L},
          ∑ u : SympVec n, ∑ v : SympVec n,
            if u ∈ L.1 ∧ v ∈ L.1 then f u v else 0 := by
    rw [← (stabStateEquiv n).symm.sum_comp, Fintype.sum_sigma]
    have hL_sum (L : {L : Submodule (ZMod 2) (SympVec n) // IsLagrangian L}) :
        (∑ χ : {χ : SympVec n → Bool // IsStabSign L.1 χ},
          (A * stabProjector ⟨L.1, L.2, χ.1, χ.2⟩).trace *
          (B * stabProjector ⟨L.1, L.2, χ.1, χ.2⟩).trace *
          (C * stabProjector ⟨L.1, L.2, χ.1, χ.2⟩).trace) =
        (d ^ 2)⁻¹ * ∑ u : SympVec n, ∑ v : SympVec n,
          if u ∈ L.1 ∧ v ∈ L.1 then f u v else 0 := by
      have hterm (χ : {χ : SympVec n → Bool // IsStabSign L.1 χ}) :
          (A * stabProjector ⟨L.1, L.2, χ.1, χ.2⟩).trace *
          (B * stabProjector ⟨L.1, L.2, χ.1, χ.2⟩).trace *
          (C * stabProjector ⟨L.1, L.2, χ.1, χ.2⟩).trace =
          (d ^ 3)⁻¹ * ∑ u : SympVec n, ∑ v : SympVec n, ∑ w : SympVec n,
            (A * pauli u).trace * (B * pauli v).trace *
              (C * ((stabSignCoeff L.1 χ.1 u * stabSignCoeff L.1 χ.1 v *
                stabSignCoeff L.1 χ.1 w) • pauli w)).trace := by
        unfold stabProjector
        simp only [Matrix.mul_smul, trace_smul, smul_eq_mul]
        have hd3 : ((2 : ℂ) ^ n)⁻¹ * (((2 : ℂ) ^ n)⁻¹ * ((2 : ℂ) ^ n)⁻¹) = (d ^ 3)⁻¹ := by
          dsimp only [d]; rw [← mul_inv, ← mul_inv]; congr 1; ring
        have hstepM (M : Matrix (BitString n) (BitString n) ℂ) :
            (M * ∑ u : SympVec n, stabSignCoeff L.1 χ.1 u • pauli u).trace =
              ∑ u : SympVec n, stabSignCoeff L.1 χ.1 u * (M * pauli u).trace := by
          simp only [Finset.mul_sum, trace_sum, Matrix.mul_smul, trace_smul, smul_eq_mul]
        rw [hstepM A, hstepM B, hstepM C]
        calc
          ((2 : ℂ) ^ n)⁻¹ * (∑ u, stabSignCoeff L.1 χ.1 u * (A * pauli u).trace) *
              (((2 : ℂ) ^ n)⁻¹ * (∑ v, stabSignCoeff L.1 χ.1 v * (B * pauli v).trace)) *
              (((2 : ℂ) ^ n)⁻¹ * (∑ w, stabSignCoeff L.1 χ.1 w * (C * pauli w).trace))
              = (d ^ 3)⁻¹ * ((∑ u, stabSignCoeff L.1 χ.1 u * (A * pauli u).trace) *
                ((∑ v, stabSignCoeff L.1 χ.1 v * (B * pauli v).trace) *
                (∑ w, stabSignCoeff L.1 χ.1 w * (C * pauli w).trace))) := by
            rw [← hd3]; ring
          _ = (d ^ 3)⁻¹ * ∑ u : SympVec n, ∑ v : SympVec n, ∑ w : SympVec n,
                (A * pauli u).trace * (B * pauli v).trace *
                  (stabSignCoeff L.1 χ.1 u * stabSignCoeff L.1 χ.1 v *
                    stabSignCoeff L.1 χ.1 w * (C * pauli w).trace) := by
            congr 1; simp_rw [Finset.sum_mul, Finset.mul_sum]
            refine Finset.sum_congr rfl fun u _ ↦ Finset.sum_congr rfl fun v _ ↦
              Finset.sum_congr rfl fun w _ ↦ by ring
      simp_rw [hterm]
      rw [← Finset.mul_sum]
      conv_lhs => arg 2; rw [Finset.sum_comm]
      have hswap1 :
          ∑ u : SympVec n,
            (∑ χ : {χ : SympVec n → Bool // IsStabSign L.1 χ},
              ∑ v : SympVec n, ∑ w : SympVec n,
                (A * pauli u).trace * (B * pauli v).trace *
                  (C * ((stabSignCoeff L.1 χ.1 u * stabSignCoeff L.1 χ.1 v *
                    stabSignCoeff L.1 χ.1 w) • pauli w)).trace) =
          ∑ u : SympVec n, ∑ v : SympVec n, ∑ w : SympVec n,
            (A * pauli u).trace * (B * pauli v).trace *
              (C * (∑ χ : {χ : SympVec n → Bool // IsStabSign L.1 χ},
                (stabSignCoeff L.1 χ.1 u * stabSignCoeff L.1 χ.1 v *
                  stabSignCoeff L.1 χ.1 w) • pauli w)).trace := by
        refine Finset.sum_congr rfl fun u _ ↦ ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun v _ ↦ ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun w _ ↦ ?_
        simp only [Finset.mul_sum, trace_sum]
      conv_lhs => arg 2; rw [hswap1]
      have hinner (u v : SympVec n) :
          ∑ w : SympVec n, (A * pauli u).trace * (B * pauli v).trace *
            (C * (∑ χ : {χ : SympVec n → Bool // IsStabSign L.1 χ},
              (stabSignCoeff L.1 χ.1 u * stabSignCoeff L.1 χ.1 v *
                stabSignCoeff L.1 χ.1 w) • pauli w)).trace =
          if u ∈ L.1 ∧ v ∈ L.1 then d * f u v else 0 := by
        by_cases huv : u ∈ L.1 ∧ v ∈ L.1
        · simp only [huv]
          have hw (w : SympVec n) :
              (∑ χ : {χ : SympVec n → Bool // IsStabSign L.1 χ},
                (stabSignCoeff L.1 χ.1 u * stabSignCoeff L.1 χ.1 v *
                  stabSignCoeff L.1 χ.1 w) • pauli w) =
              if w = u + v then d • (pauli u * pauli v) else 0 := by
            by_cases hwl : w ∈ L.1
            · simpa [stabSignCoeff, huv.1, huv.2, hwl] using
                sum_stabSign_triple L.1 L.2 u v w huv.1 huv.2 hwl
            · simp only [show w ≠ u + v from fun h ↦ hwl (h ▸ L.1.add_mem huv.1 huv.2), ite_false]
              exact Finset.sum_eq_zero fun χ _ ↦ by simp [stabSignCoeff, hwl]
          simp_rw [hw]
          rw [Finset.sum_eq_single (u + v)]
          · simp only [ite_true, and_self, Matrix.mul_smul, trace_smul, smul_eq_mul, f]
            ring
          · intro w _ hne; simp [hne]
          · intro h; exact absurd (mem_univ _) h
        · simp only [huv, ite_false]
          refine Finset.sum_eq_zero fun w _ ↦ ?_
          have h0 : ∑ χ : {χ : SympVec n → Bool // IsStabSign L.1 χ},
              (stabSignCoeff L.1 χ.1 u * stabSignCoeff L.1 χ.1 v *
                stabSignCoeff L.1 χ.1 w) • pauli w = 0 :=
            Finset.sum_eq_zero fun χ _ ↦ by
              by_cases hu : u ∈ L.1
              · have hv : v ∉ L.1 := fun hv ↦ huv ⟨hu, hv⟩
                simp [stabSignCoeff, hv]
              · simp [stabSignCoeff, hu]
          simp [h0]
      simp_rw [hinner]
      have hpull :
          ∑ u : SympVec n, ∑ v : SympVec n, (if u ∈ L.1 ∧ v ∈ L.1 then d * f u v else 0) =
          d * ∑ u : SympVec n, ∑ v : SympVec n, (if u ∈ L.1 ∧ v ∈ L.1 then f u v else 0) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun u _ ↦ ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun v _ ↦ by split_ifs <;> ring
      rw [hpull]
      field_simp [hd_ne]
    dsimp only [stabStateEquiv, Equiv.coe_fn_symm_mk]
    rw [Finset.sum_congr rfl (fun L _ ↦ hL_sum L), ← Finset.mul_sum]
  rw [hstep1]
  have hswap2 :
      ∑ L : {L : Submodule (ZMod 2) (SympVec n) // IsLagrangian L},
        ∑ u : SympVec n, ∑ v : SympVec n, (if u ∈ L.1 ∧ v ∈ L.1 then f u v else 0) =
      ∑ u : SympVec n, ∑ v : SympVec n,
        ((Fintype.card {L : Submodule (ZMod 2) (SympVec n) //
          IsLagrangian L ∧ u ∈ L ∧ v ∈ L} : ℂ) * f u v) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun u _ ↦ ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun v _ ↦ ?_
    have hcard :
        ∑ L : {L : Submodule (ZMod 2) (SympVec n) // IsLagrangian L},
          (if u ∈ L.1 ∧ v ∈ L.1 then f u v else 0) =
        ((Finset.univ.filter fun L : {L : Submodule (ZMod 2) (SympVec n) // IsLagrangian L} ↦
          u ∈ L.1 ∧ v ∈ L.1).card : ℂ) * f u v := by
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    rw [hcard]
    congr 1
    exact_mod_cast (by
      let e : {L : {L : Submodule (ZMod 2) (SympVec n) // IsLagrangian L} // u ∈ L.1 ∧ v ∈ L.1} ≃
          {L : Submodule (ZMod 2) (SympVec n) // IsLagrangian L ∧ u ∈ L ∧ v ∈ L} :=
        { toFun := fun ⟨⟨L, hL⟩, h⟩ ↦ ⟨L, hL, h⟩
          invFun := fun ⟨L, hL, h⟩ ↦ ⟨⟨L, hL⟩, h⟩
          left_inv := fun _ ↦ rfl
          right_inv := fun _ ↦ rfl }
      rw [← Fintype.card_subtype, Fintype.card_congr e])
  rw [hswap2]
  set N1 : ℂ := N0 / (d + 1)
  set c2 : ℂ := 2 * N0 / ((d + 1) * (d + 2))
  have hcount_uv (u v : SympVec n) :
      (Fintype.card {L : Submodule (ZMod 2) (SympVec n) //
        IsLagrangian L ∧ u ∈ L ∧ v ∈ L} : ℂ) =
      if sympForm u v = 0 then
        if u = 0 ∧ v = 0 then N0
        else if u = 0 ∨ v = 0 ∨ u = v then N1
        else c2
      else 0 := by
    by_cases hcomm : sympForm u v = 0
    · simp only [hcomm, ite_true]
      let W : Submodule (ZMod 2) (SympVec n) := Submodule.span (ZMod 2) {u, v}
      have hW_iso : ∀ x ∈ W, ∀ y ∈ W, sympForm x y = 0 := by
        have hgen : ∀ x ∈ ({u, v} : Set (SympVec n)), ∀ y ∈ ({u, v} : Set (SympVec n)),
            sympFormLin n x y = 0 := by
          rintro x (rfl | rfl) y (rfl | rfl)
          · exact sympForm_self _
          · exact hcomm
          · rw [show sympFormLin n _ _ = sympForm _ _ from rfl, sympForm_comm]; exact hcomm
          · exact sympForm_self _
        intro x hx y hy
        have h1 : ∀ z ∈ W, sympFormLin n x z = 0 := fun z hz ↦ by
          refine Submodule.span_induction (p := fun z _ ↦ sympFormLin n x z = 0) ?_ (map_zero _)
            (fun a b _ _ ha hb ↦ by rw [map_add, ha, hb, add_zero])
            (fun r a _ ha ↦ by rw [map_smul, ha, smul_zero]) hz
          intro z' hz'
          refine Submodule.span_induction (p := fun w _ ↦ sympFormLin n w z' = 0) ?_ (by simp)
            (fun a b _ _ ha hb ↦ by rw [map_add, LinearMap.add_apply, ha, hb, add_zero])
            (fun r a _ ha ↦ by rw [map_smul, LinearMap.smul_apply, ha, smul_zero]) hx
          intro w hw
          exact hgen w hw z' hz'
        exact h1 y hy
      have heq_sub :
          Fintype.card {L : Submodule (ZMod 2) (SympVec n) // IsLagrangian L ∧ u ∈ L ∧ v ∈ L} =
            Fintype.card {L : Submodule (ZMod 2) (SympVec n) // IsLagrangian L ∧ W ≤ L} :=
        Fintype.card_congr
          { toFun := fun ⟨L, hL, hu, hv⟩ ↦ ⟨L, hL, Submodule.span_le.mpr (by
              rintro x (rfl | rfl) <;> assumption)⟩
            invFun := fun ⟨L, hL, hWL⟩ ↦ ⟨L, hL, hWL (Submodule.subset_span (by simp)),
              hWL (Submodule.subset_span (by simp))⟩
            left_inv := fun _ ↦ rfl
            right_inv := fun _ ↦ rfl }
      rw [heq_sub, ← Nat.card_eq_fintype_card, card_lagrangian_containing W hW_iso]
      let hS : SymplecticSpace (SympVec n) :=
        ⟨sympFormLin n, sympForm_self, fun _ ↦ sympForm_nondegenerate⟩
      have hdimV : Module.finrank (ZMod 2) (SympVec n) = 2 * n := by
        rw [show Module.finrank (ZMod 2) (SympVec n) =
            Module.finrank (ZMod 2) (Fin n → ZMod 2) + Module.finrank (ZMod 2) (Fin n → ZMod 2) from
          Module.finrank_prod]
        simp [two_mul]
      have hW_le_n : Module.finrank (ZMod 2) W ≤ n := by
        have hp := hS.finrank_perp W
        have hle' := Submodule.finrank_mono (show W ≤
          hS.perp W from fun x hx y hy ↦ hW_iso x hx y hy)
        omega
      by_cases h00 : u = 0 ∧ v = 0
      · rcases h00 with ⟨rfl, rfl⟩
        have hW0 : W = ⊥ := by simp [W]
        rw [hW0, finrank_bot, Nat.sub_zero]
        simp only [and_self, ite_true]
        rfl
      · simp only [h00, ite_false]
        by_cases hdim1 : u = 0 ∨ v = 0 ∨ u = v
        · simp only [hdim1, ite_true]
          have hW1 : Module.finrank (ZMod 2) W = 1 := by
            rcases hdim1 with rfl | rfl | rfl
            · have hv0 : v ≠ 0 := fun hv ↦ h00 ⟨rfl, hv⟩
              rw [show W = Submodule.span (ZMod 2) {v} by
                simp [W, Submodule.span_insert_zero], finrank_span_singleton hv0]
            · have hu0 : u ≠ 0 := fun hu ↦ h00 ⟨hu, rfl⟩
              rw [show W = Submodule.span (ZMod 2) {u} by
                rw [show W = Submodule.span (ZMod 2) {u, 0} from rfl, Set.pair_comm,
                  Submodule.span_insert_zero], finrank_span_singleton hu0]
            · have hu0 : u ≠ 0 := fun hu ↦ h00 ⟨hu, hu⟩
              rw [show W = Submodule.span (ZMod 2) {u} by simp [W], finrank_span_singleton hu0]
          rw [hW1]
          have hrec : lagrangianCount n = (2 ^ n + 1) * lagrangianCount (n - 1) := by
            obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
            rfl
          have hrecC : N0 = (d + 1) * (lagrangianCount (n - 1) : ℂ) := by
            dsimp only [N0, d]; exact_mod_cast hrec
          simp only [N1, hrecC, mul_div_cancel_left₀ _ hd1_ne]
        · simp only [hdim1, ite_false]
          push Not at h00 hdim1
          rcases hdim1 with ⟨hu0, hv0, huv⟩
          have hW2 : Module.finrank (ZMod 2) W = 2 := by
            have hli : LinearIndependent (ZMod 2) ![u, v] := by
              rw [Fintype.linearIndependent_iff]
              intro c hc
              rw [Fin.sum_univ_two] at hc
              change c 0 • u + c 1 • v = 0 at hc
              have hne_both : ∀ a b : ZMod 2, a • u + b • v = 0 → a = 0 ∧ b = 0 := by
                intro a b hab
                rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases b with rfl | rfl
                · exact ⟨rfl, rfl⟩
                · simp only [zero_smul, one_smul, zero_add] at hab; exact absurd hab hv0
                · simp only [zero_smul, one_smul, add_zero] at hab; exact absurd hab hu0
                · simp only [one_smul] at hab
                  have huu : u + u = 0 := by
                    rw [← two_smul (ZMod 2) u, show (2 : ZMod 2) = 0 from rfl, zero_smul]
                  have heq_uv : u = v := by
                    have h1 := congrArg (u + ·) hab
                    rw [← add_assoc, huu, zero_add, add_zero] at h1
                    exact h1.symm
                  exact absurd heq_uv huv
              have hb := hne_both (c 0) (c 1) hc
              intro i; fin_cases i
              · exact hb.1
              · exact hb.2
            have hrange : W = Submodule.span (ZMod 2) (Set.range ![u, v]) := by
              dsimp only [W]; congr 1; ext x
              constructor
              · rintro (rfl | rfl)
                · exact ⟨0, rfl⟩
                · exact ⟨1, rfl⟩
              · rintro ⟨i, rfl⟩
                fin_cases i <;> simp
            rw [hrange, finrank_span_eq_card hli, Fintype.card_fin]
          rw [hW2]
          have hrec : 2 * lagrangianCount n =
              (2 ^ n + 1) * (2 ^ n + 2) * lagrangianCount (n - 2) := by
            obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (show 2 ≤ n by omega)
            have hk : 2 + k - 2 = k := by omega
            have hk1 : 2 + k = (k + 1) + 1 := by omega
            rw [hk, hk1]
            simp only [lagrangianCount]
            have h2 : 2 * (2 ^ (k + 1) + 1) = 2 ^ ((k + 1) + 1) + 2 := by rw [pow_succ]; ring
            calc
              2 * ((2 ^ (k + 1 + 1) + 1) * ((2 ^ (k + 1) + 1) * lagrangianCount k))
                  = (2 ^ (k + 1 + 1) + 1) * (2 * (2 ^ (k + 1) + 1)) * lagrangianCount k := by ring
              _ = (2 ^ (k + 1 + 1) + 1) * (2 ^ (k + 1 + 1) + 2) * lagrangianCount k := by rw [h2]
          have hrecC : 2 * N0 = (d + 1) * (d + 2) * (lagrangianCount (n - 2) : ℂ) := by
            dsimp only [N0, d]; exact_mod_cast hrec
          simp only [c2, hrecC, mul_div_cancel_left₀ _ (mul_ne_zero hd1_ne hd2_ne)]
    · simp only [hcomm, ite_false]
      have hempty : IsEmpty {L : Submodule (ZMod 2) (SympVec n) //
          IsLagrangian L ∧ u ∈ L ∧ v ∈ L} :=
        ⟨fun ⟨L, hL, hu, hv⟩ ↦ hcomm (hL.1 u hu v hv)⟩
      simp [Fintype.card_eq_zero]
  simp_rw [hcount_uv]
  have hdecomp :
      (∑ u : SympVec n, ∑ v : SympVec n,
        (if sympForm u v = 0 then
          if u = 0 ∧ v = 0 then N0 else if u = 0 ∨ v = 0 ∨ u = v then N1 else c2
        else 0) * f u v) =
      (N0 - 3 * N1 + 2 * c2) * f 0 0 +
      (N1 - c2) * ((∑ v : SympVec n, f 0 v) + (∑ u : SympVec n, f u 0) +
        (∑ u : SympVec n, f u u)) +
      c2 * (∑ u : SympVec n, ∑ v ∈ Finset.univ.filter (fun v ↦ sympForm u v = 0), f u v) := by
    have h0v_symp (v : SympVec n) : sympForm 0 v = 0 := sympForm_zero_left v
    have hu0_symp (u : SympVec n) : sympForm u 0 = 0 := sympForm_zero_right u
    have huu_symp (u : SympVec n) : sympForm u u = 0 := sympForm_self u
    have hrhs_rewrite :
        (∑ v : SympVec n, f 0 v) + (∑ u : SympVec n, f u 0) + (∑ u : SympVec n, f u u) =
        ∑ u : SympVec n, ∑ v : SympVec n,
          ((if u = 0 then (1 : ℂ) else 0) + (if v = 0 then 1 else 0) +
            (if u = v then 1 else 0)) * f u v := by
      simp only [add_mul, Finset.sum_add_distrib, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
        Finset.sum_ite_eq', Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.mem_univ, ite_true]
    have hf00 :
        f 0 0 = ∑ u : SympVec n, ∑ v : SympVec n,
          (if u = 0 ∧ v = 0 then (1 : ℂ) else 0) * f u v := by
      simp only [ite_and, ite_mul, one_mul, zero_mul, Finset.sum_ite_irrel, Finset.sum_const_zero,
        Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    have hcomm_sum :
        (∑ u : SympVec n, ∑ v ∈ Finset.univ.filter (fun v ↦ sympForm u v = 0), f u v) =
        ∑ u : SympVec n, ∑ v : SympVec n, (if sympForm u v = 0 then (1 : ℂ) else 0) * f u v := by
      simp only [Finset.sum_filter, ite_mul, one_mul, zero_mul]
    rw [hrhs_rewrite, hcomm_sum]
    conv_rhs => rw [hf00]
    simp_rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun u _ ↦ Finset.sum_congr rfl fun v _ ↦ ?_
    by_cases hcomm : sympForm u v = 0
    · by_cases h00 : u = 0 ∧ v = 0
      · rcases h00 with ⟨rfl, rfl⟩
        simp only [hcomm, ite_true, and_self]; ring
      · by_cases hu0 : u = 0
        · subst hu0
          have hv0 : v ≠ 0 := fun hv ↦ h00 ⟨rfl, hv⟩
          simp only [hcomm, ite_true, hv0, and_false, or_false, Ne.symm hv0, ite_false]
          ring
        · by_cases hv0 : v = 0
          · subst hv0
            simp only [hcomm, ite_true, hu0, false_and, false_or, true_or, ite_false]; ring
          · by_cases huv : u = v
            · subst huv
              simp only [hcomm, ite_true, hu0, and_self, false_or, ite_false]; ring
            · simp only [hcomm, ite_true, hu0, hv0, huv, and_self, or_self, ite_false]; ring
    · have hu0 : u ≠ 0 := fun hu ↦ hcomm (hu ▸ h0v_symp v)
      have hv0 : v ≠ 0 := fun hv ↦ hcomm (hv ▸ hu0_symp u)
      have huv : u ≠ v := fun huv ↦ hcomm (huv ▸ huu_symp u)
      simp only [hcomm, ite_false, hu0, hv0, huv, and_self, or_self]; ring
  rw [hdecomp]
  have hf00_val : f 0 0 = A.trace * B.trace * C.trace := by simp [f, pauli_zero]
  have hf0v_val : ∑ v : SympVec n, f 0 v = d * (A.trace * (B * C).trace) := by
    simp only [f, pauli_zero, Matrix.mul_one, Matrix.one_mul]
    simp_rw [mul_assoc, ← Finset.mul_sum]
    rw [sum_trace_pauli_mul_trace_pauli B C]; ring
  have hfu0_val : ∑ u : SympVec n, f u 0 = d * (B.trace * (A * C).trace) := by
    simp only [f, pauli_zero, Matrix.mul_one]
    rw [show (∑ u : SympVec n, (A * pauli u).trace * B.trace * (C * pauli u).trace) =
        B.trace * ∑ u : SympVec n, (A * pauli u).trace * (C * pauli u).trace from by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun u _ ↦ by ring,
      sum_trace_pauli_mul_trace_pauli A C]; ring
  have hfuu_val : ∑ u : SympVec n, f u u = d * (C.trace * (A * B).trace) := by
    simp only [f, pauli_mul_self, Matrix.mul_one]
    rw [show (∑ u : SympVec n, (A * pauli u).trace * (B * pauli u).trace * C.trace) =
        C.trace * ∑ u : SympVec n, (A * pauli u).trace * (B * pauli u).trace from by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun u _ ↦ by ring,
      sum_trace_pauli_mul_trace_pauli A B]; ring
  have hcomm_val :
      (∑ u : SympVec n, ∑ v ∈ Finset.univ.filter (fun v ↦ sympForm u v = 0), f u v) =
        (d ^ 2 / 2) * ((A * B * C).trace + (A * C * B).trace) :=
    sum_commuting_trace_pauli_triple A B C
  rw [hf00_val, hf0v_val, hfu0_val, hfuu_val, hcomm_val]
  have hcard_eq : (Fintype.card (StabState n) : ℂ) = d * N0 := by
    rw [card_stabState, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  rw [hcard_eq]
  dsimp only [N1, c2]
  field_simp [hd_ne, hd1_ne, hd2_ne]
  ring

/-- **Stabilizer 2-design trace identity**: obtained by setting `C = 1` in the 3-design identity:
`∑_{s ∈ StabState n} Tr(A P_s) Tr(B P_s) = (|StabState n| / (d(d+1))) (Tr(A)Tr(B) + Tr(AB))`. -/
theorem stabilizer_two_design_trace {n : ℕ}
    (A B : Matrix (BitString n) (BitString n) ℂ) :
    (∑ s : StabState n, (A * stabProjector s).trace * (B * stabProjector s).trace) =
      ((Fintype.card (StabState n) : ℂ) / ((2 : ℂ) ^ n * ((2 : ℂ) ^ n + 1))) *
      (A.trace * B.trace + (A * B).trace) := by
  have h3 := stabilizer_three_design_trace A B (1 : Matrix (BitString n) (BitString n) ℂ)
  have hP1 (s : StabState n) :
      ((1 : Matrix (BitString n) (BitString n) ℂ) * stabProjector s).trace = 1 := by
    rw [Matrix.one_mul, (stabProjector_isDensityMatrix s).trace_eq_one]
  simp only [hP1, mul_one, trace_one, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat] at h3
  rw [h3]
  set d : ℂ := (2 : ℂ) ^ n
  have hd_ne : d ≠ 0 := pow_ne_zero n (by norm_num)
  have hd1_ne : d + 1 ≠ 0 := by
    have : (0 : ℝ) < (2 : ℝ) ^ n + 1 := by positivity
    simpa [d] using Complex.ofReal_ne_zero.mpr this.ne'
  have hd2_ne : d + 2 ≠ 0 := by
    have : (0 : ℝ) < (2 : ℝ) ^ n + 2 := by positivity
    simpa [d] using Complex.ofReal_ne_zero.mpr this.ne'
  field_simp [hd_ne, hd1_ne, hd2_ne]
  ring

end StabilizerStates

end CslibFrontier.Quantum
