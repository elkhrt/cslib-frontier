module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.LinearAlgebra.Matrix.Permanent
public import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Fintype.Perm
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Bosonic Fock Space and the Photonic Permanent Homomorphism

Defines the `n`-photon `m`-mode bosonic Fock basis `FockState m n`, the repeated-row/column
submatrix `submatrixFock U S T`, and the monoid homomorphism `photonicHom m n` sending an
`m × m` complex matrix `U` to its `n`-photon bosonic lift `φ(U)` with entries
`⟨S | φ(U) | T⟩ = Per(U_{S,T}) / √(s₁! ⋯ sₘ! t₁! ⋯ tₘ!)`. Also establishes conjugate-transpose
compatibility, restriction to a unitary group homomorphism `U(m) →* U(Φ_{m,n})`, and locality
under mode-subset embeddings.

## Main definitions

* `CslibFrontier.Quantum.LinearOptics.FockState`: `n`-photon occupation tuples across `m` modes.
* `CslibFrontier.Quantum.LinearOptics.modeList`: canonical `Fin n → Fin m` listing mode `i` with
  multiplicity `S.occ i`.
* `CslibFrontier.Quantum.LinearOptics.submatrixFock`: repeated-row/column `n × n` submatrix.
* `CslibFrontier.Quantum.LinearOptics.photonicHom`: monoid homomorphism
  `Matrix (Fin m) (Fin m) ℂ →* Matrix (FockState m n) (FockState m n) ℂ`.
* `CslibFrontier.Quantum.LinearOptics.photonicHomUnitary`: unitary group homomorphism
  `unitaryGroup (Fin m) ℂ →* unitaryGroup (FockState m n) ℂ`.
* `CslibFrontier.Quantum.LinearOptics.embedModes`: embedding a `k × k` optical transformation onto
  `k` distinct modes of an `m`-mode system.

## Main results

* `CslibFrontier.Quantum.LinearOptics.permanent_submatrixFock_mul`: permanent composition identity
  for `submatrixFock (V * U) S T`.
* `CslibFrontier.Quantum.LinearOptics.photonicHom_conjTranspose`: `φ(Uᴴ) = φ(U)ᴴ`.
* `CslibFrontier.Quantum.LinearOptics.photonicHom_embedModes_eq_zero`,
  `CslibFrontier.Quantum.LinearOptics.photonicHom_embedModes`: off-support conservation and active
  mode locality of `φ`.
-/

public section

namespace CslibFrontier.Quantum.LinearOptics

open Matrix Finset
open scoped Nat

/-! ### Small helper lemmas for `Equiv.sigmaFiberEquiv` and `Equiv.sumCompl` -/

private theorem sigmaFiberEquiv_symm_eq {α β : Type*} (f : α → β) (a : α) :
    (Equiv.sigmaFiberEquiv f).symm a = ⟨f a, ⟨a, rfl⟩⟩ :=
  rfl

private theorem sumCompl_symm_pos {α : Type*} (p : α → Prop) [DecidablePred p] {a : α}
    (ha : p a) : (Equiv.sumCompl p).symm a = Sum.inl ⟨a, ha⟩ := by
  rw [Equiv.symm_apply_eq]
  rfl

private theorem sumCompl_symm_neg {α : Type*} (p : α → Prop) [DecidablePred p] {a : α}
    (ha : ¬p a) : (Equiv.sumCompl p).symm a = Sum.inr ⟨a, ha⟩ := by
  rw [Equiv.symm_apply_eq]
  rfl

/-! ### Fock basis states `Φ_{m,n}` -/

/-- An `n`-photon Fock basis state across `m` optical modes: an occupation tuple
`occ : Fin m → ℕ` summing to `n`. -/
@[ext]
structure FockState (m n : ℕ) where
  /-- Photon occupation number in each mode. -/
  occ : Fin m → ℕ
  /-- Conservation of total photon number `∑ i, occ i = n`. -/
  sum_occ : ∑ i : Fin m, occ i = n

instance instDecidableEqFockState {m n : ℕ} : DecidableEq (FockState m n) :=
  fun S T => decidable_of_iff (S.occ = T.occ) FockState.ext_iff.symm

/-- Reindex the total photon count of a `FockState` along an equality `n₁ = n₂`. -/
def FockState.cast {m n₁ n₂ : ℕ} (h : n₁ = n₂) (S : FockState m n₁) : FockState m n₂ where
  occ := S.occ
  sum_occ := S.sum_occ.trans h

@[simp]
theorem FockState.cast_occ {m n₁ n₂ : ℕ} (h : n₁ = n₂) (S : FockState m n₁) (i : Fin m) :
    (S.cast h).occ i = S.occ i := by
  simp [FockState.cast]

theorem FockState.occ_le {m n : ℕ} (S : FockState m n) (i : Fin m) : S.occ i ≤ n := by
  calc S.occ i ≤ ∑ j : Fin m, S.occ j :=
        Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    _ = n := S.sum_occ

/-- Equivalence identifying `FockState m n` with bounded tuples `{ f : Fin m → Fin (n + 1) // … }`,
yielding a canonical `Fintype` instance. -/
def fockStateEquivSubtype (m n : ℕ) :
    FockState m n ≃ { f : Fin m → Fin (n + 1) // ∑ i : Fin m, (f i).val = n } where
  toFun S := ⟨fun i => ⟨S.occ i, Nat.lt_succ_of_le (S.occ_le i)⟩, S.sum_occ⟩
  invFun f := ⟨fun i => (f.1 i).val, f.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance instFintypeFockState (m n : ℕ) : Fintype (FockState m n) :=
  Fintype.ofEquiv _ (fockStateEquivSubtype m n).symm

/-- Product of occupation factorials `s₁! ⋯ sₘ!` for a Fock state `S`. -/
def fockFact {m n : ℕ} (S : FockState m n) : ℕ :=
  ∏ i : Fin m, (S.occ i)!

theorem fockFact_eq {m n : ℕ} (S : FockState m n) :
    fockFact S = ∏ i : Fin m, (S.occ i)! := by
  simp [fockFact]

theorem fockFact_cast {m n₁ n₂ : ℕ} (h : n₁ = n₂) (S : FockState m n₁) :
    fockFact (S.cast h) = fockFact S := by
  simp [fockFact]

theorem fockFact_pos {m n : ℕ} (S : FockState m n) : 0 < fockFact S :=
  Finset.prod_pos fun i _ => Nat.factorial_pos (S.occ i)

theorem fockFact_ne_zero {m n : ℕ} (S : FockState m n) : fockFact S ≠ 0 :=
  (fockFact_pos S).ne'

/-- The histogram `FockState m n` recording the fiber cardinalities of a function
`f : Fin n → Fin m`. -/
def histogram {m n : ℕ} (f : Fin n → Fin m) : FockState m n where
  occ i := (Finset.univ.filter fun k : Fin n => f k = i).card
  sum_occ := by
    have h := Finset.card_eq_sum_card_fiberwise (f := f) (s := Finset.univ) (t := Finset.univ)
      (fun k _ => Finset.mem_univ (f k))
    simpa [Fintype.card_fin] using h.symm

@[simp]
theorem histogram_occ {m n : ℕ} (f : Fin n → Fin m) (i : Fin m) :
    (histogram f).occ i = (Finset.univ.filter fun k : Fin n => f k = i).card := by
  simp [histogram]

theorem histogram_comp_perm {m n : ℕ} (f : Fin n → Fin m) (σ : Equiv.Perm (Fin n)) :
    histogram (f ∘ σ) = histogram f := by
  ext i
  simp only [histogram_occ]
  refine Finset.card_bij (fun k _ => σ k) ?_ ?_ ?_
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.comp_apply] at hk ⊢
    exact hk
  · intro k₁ _ k₂ _ h
    exact σ.injective h
  · intro k hk
    refine ⟨σ.symm k, ?_, σ.apply_symm_apply k⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.comp_apply] at hk ⊢
    simpa using hk

/-! ### Canonical mode list `modeList` and repeated submatrix `U_{S,T}` -/

private def modeListRaw {m n : ℕ} (S : FockState m n) : List (Fin m) :=
  (List.finRange m).flatMap fun i => List.replicate (S.occ i) i

private theorem length_modeListRaw {m n : ℕ} (S : FockState m n) :
    (modeListRaw S).length = n := by
  rw [modeListRaw, List.length_flatMap]
  have hmap : ((List.finRange m).map fun i => (List.replicate (S.occ i) i).length) =
      (List.finRange m).map S.occ := by
    simp
  rw [hmap, ← Fin.sum_univ_def, S.sum_occ]

private theorem count_modeListRaw {m n : ℕ} (S : FockState m n) (i : Fin m) :
    (modeListRaw S).count i = S.occ i := by
  rw [modeListRaw, List.count_flatMap]
  have hmap : ((List.finRange m).map (List.count i ∘ fun j => List.replicate (S.occ j) j)) =
      (List.finRange m).map fun j => if j = i then S.occ j else 0 := by
    refine List.map_congr_left fun j _ => ?_
    simp only [Function.comp_apply, List.count_replicate]
    by_cases h : j = i <;> simp [h]
  rw [hmap, ← Fin.sum_univ_def]
  simp

/-- Canonical function `Fin n → Fin m` taking each value `i : Fin m` exactly `S.occ i` times. -/
def modeList {m n : ℕ} (S : FockState m n) : Fin n → Fin m :=
  fun k => (modeListRaw S)[k.val]'(by rw [length_modeListRaw]; exact k.isLt)

theorem histogram_modeList {m n : ℕ} (S : FockState m n) : histogram (modeList S) = S := by
  ext i
  rw [histogram_occ, ← count_modeListRaw S i]
  have hlen : (modeListRaw S).length = n := length_modeListRaw S
  rw [List.count_eq_length_filter]
  have hofFn : List.ofFn (modeList S) = modeListRaw S := by
    refine List.ext_getElem (by simp [hlen]) fun k hk₁ hk₂ => ?_
    simp [modeList]
  rw [← hofFn]
  have hcard : (Finset.univ.filter fun k : Fin n => modeList S k = i).card =
      ((List.finRange n).filter fun k : Fin n => decide (modeList S k = i)).length := by
    rw [← List.toFinset_card_of_nodup ((List.nodup_finRange n).filter _)]
    congr 1
    ext k
    simp
  rw [hcard, List.ofFn_eq_map, List.filter_map, List.length_map]
  rfl

/-- The `n × n` submatrix `U_{S,T}` obtained by repeating row `i` of `U` `S.occ i` times and
column `j` of `U` `T.occ j` times. -/
def submatrixFock {R : Type*} {m n : ℕ} (U : Matrix (Fin m) (Fin m) R)
    (S T : FockState m n) : Matrix (Fin n) (Fin n) R :=
  U.submatrix (modeList S) (modeList T)

@[simp]
theorem submatrixFock_apply {R : Type*} {m n : ℕ} (U : Matrix (Fin m) (Fin m) R)
    (S T : FockState m n) (a b : Fin n) :
    submatrixFock U S T a b = U (modeList S a) (modeList T b) := by
  simp [submatrixFock]

/-- Row-indexed permanent formula `Per(M) = ∑ σ, ∏ a, M a (σ a)` (via `Matrix.permanent_transpose`).
-/
theorem permanent_eq_sum_row {R : Type*} [CommRing R] {n : ℕ} (M : Matrix (Fin n) (Fin n) R) :
    M.permanent = ∑ σ : Equiv.Perm (Fin n), ∏ a : Fin n, M a (σ a) := by
  rw [← Matrix.permanent_transpose, Matrix.permanent]
  rfl

/-- Fiber-preserving permutation equivalence via `Equiv.sigmaFiberEquiv`: permutations `π` with
`g ∘ π = f` correspond bijectively to families of bijections between the fibers of `f` and `g`. -/
private def permCompEquiv {m n : ℕ} (f g : Fin n → Fin m) :
    { π : Equiv.Perm (Fin n) // g ∘ π = f } ≃
      (∀ i : Fin m, { k : Fin n // f k = i } ≃ { k : Fin n // g k = i }) where
  toFun π i :=
    { toFun := fun k => ⟨π.1 k.1, by
        have h := congrFun π.2 k.1
        simpa [Function.comp_apply, k.2] using h⟩
      invFun := fun k => ⟨π.1.symm k.1, by
        have h := congrFun π.2 (π.1.symm k.1)
        simpa [Function.comp_apply, k.2] using h.symm⟩
      left_inv := fun k => Subtype.ext (π.1.symm_apply_apply k.1)
      right_inv := fun k => Subtype.ext (π.1.apply_symm_apply k.1) }
  invFun e :=
    ⟨(Equiv.sigmaFiberEquiv f).symm.trans
        ((Equiv.sigmaCongrRight e).trans (Equiv.sigmaFiberEquiv g)),
      by
        funext k
        simp only [Function.comp_apply, Equiv.trans_apply, sigmaFiberEquiv_symm_eq,
          Equiv.sigmaCongrRight_apply, Equiv.sigmaFiberEquiv_apply]
        exact (e (f k) ⟨k, rfl⟩).2⟩
  left_inv π := by
    apply Subtype.ext
    ext k
    simp only [Equiv.trans_apply, sigmaFiberEquiv_symm_eq, Equiv.sigmaCongrRight_apply,
      Equiv.sigmaFiberEquiv_apply]
    rfl
  right_inv e := by
    funext i
    ext ⟨k, hk⟩
    subst hk
    simp only [Equiv.trans_apply, sigmaFiberEquiv_symm_eq, Equiv.sigmaCongrRight_apply,
      Equiv.sigmaFiberEquiv_apply]
    rfl

/-- Number of permutations `π ∈ S_n` satisfying `g ∘ π = f` when `f` and `g` have the same
histogram `R` is `fockFact R = ∏ i, (R.occ i)!`. -/
theorem card_perm_comp_eq {m n : ℕ} {f g : Fin n → Fin m} (hfg : histogram f = histogram g) :
    (Finset.univ.filter fun π : Equiv.Perm (Fin n) => g ∘ π = f).card = fockFact (histogram g) := by
  classical
  rw [← Fintype.card_subtype, Fintype.card_congr (permCompEquiv f g), Fintype.card_pi]
  unfold fockFact
  refine Finset.prod_congr rfl fun i _ => ?_
  have hcf : Fintype.card { k : Fin n // f k = i } = (histogram g).occ i := by
    rw [Fintype.card_subtype, ← histogram_occ f i, hfg]
  have hcg : Fintype.card { k : Fin n // g k = i } = (histogram g).occ i := by
    rw [Fintype.card_subtype, histogram_occ]
  let ef : { k : Fin n // f k = i } ≃ Fin ((histogram g).occ i) := Fintype.equivFinOfCardEq hcf
  let eg : { k : Fin n // g k = i } ≃ Fin ((histogram g).occ i) := Fintype.equivFinOfCardEq hcg
  rw [Fintype.card_congr (Equiv.equivCongr ef eg), Fintype.card_perm, Fintype.card_fin]

/-- Summing any function `G` over all `g ∘ π` (`π ∈ S_n`) counts each `f` with `histogram f = R`
exactly `fockFact R` times. -/
theorem sum_perm_comp_eq {m n : ℕ} {M : Type*} [AddCommMonoid M]
    (R : FockState m n) (G : (Fin n → Fin m) → M) :
    ∑ π : Equiv.Perm (Fin n), G (modeList R ∘ π) =
      fockFact R • ∑ f ∈ Finset.univ.filter (fun f : Fin n → Fin m => histogram f = R), G f := by
  classical
  have hfib := Finset.sum_fiberwise_of_maps_to (s := Finset.univ)
    (t := Finset.univ.filter fun f : Fin n → Fin m => histogram f = R)
    (g := fun π : Equiv.Perm (Fin n) => modeList R ∘ π)
    (f := fun π => G (modeList R ∘ π))
    (fun π _ => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [histogram_comp_perm, histogram_modeList])
  rw [← hfib, Finset.smul_sum]
  refine Finset.sum_congr rfl fun f hf => ?_
  rw [Finset.mem_filter] at hf
  have hconst : ∑ π ∈ Finset.univ.filter (fun π : Equiv.Perm (Fin n) => modeList R ∘ π = f),
      G (modeList R ∘ π) =
      (Finset.univ.filter (fun π : Equiv.Perm (Fin n) => modeList R ∘ π = f)).card • G f := by
    rw [← Finset.sum_const]
    exact Finset.sum_congr rfl fun π hπ => by rw [(Finset.mem_filter.mp hπ).2]
  rw [hconst, card_perm_comp_eq (hf.2.trans (histogram_modeList R).symm), histogram_modeList]

/-- Cleared-denominator permanent composition identity over any commutative ring `R`. -/
theorem permanent_submatrixFock_mul_cleared {R : Type*} [CommRing R] {m n : ℕ}
    (V U : Matrix (Fin m) (Fin m) R) (S T : FockState m n) :
    ∑ K : FockState m n,
      (fockFact K : R) *
        (∑ f ∈ Finset.univ.filter (fun f : Fin n → Fin m => histogram f = K),
          ∑ σ : Equiv.Perm (Fin n),
            ∏ a : Fin n, V (modeList S a) (f a) * U (f a) (modeList T (σ a))) =
      ∑ K : FockState m n,
        (submatrixFock V S K).permanent * (submatrixFock U K T).permanent := by
  refine Finset.sum_congr rfl fun K _ => ?_
  rw [← nsmul_eq_mul, ← sum_perm_comp_eq K (fun f =>
    ∑ σ : Equiv.Perm (Fin n), ∏ a : Fin n, V (modeList S a) (f a) * U (f a) (modeList T (σ a)))]
  simp only [permanent_eq_sum_row, submatrixFock_apply, Function.comp_apply]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun π _ => ?_
  rw [Finset.mul_sum]
  refine Fintype.sum_equiv (Equiv.mulRight π⁻¹)
    (fun σ => ∏ a : Fin n,
      V (modeList S a) (modeList K (π a)) * U (modeList K (π a)) (modeList T (σ a)))
    (fun τ => (∏ a : Fin n, V (modeList S a) (modeList K (π a))) *
      ∏ b : Fin n, U (modeList K b) (modeList T (τ b)))
    fun σ => ?_
  rw [Finset.prod_mul_distrib]
  congr 1
  exact Fintype.prod_equiv π
    (fun a => U (modeList K (π a)) (modeList T (σ a)))
    (fun b => U (modeList K b) (modeList T ((σ * π⁻¹) b)))
    fun a => by simp [Equiv.Perm.mul_apply]

/-- General permanent composition identity for repeated-row/column Fock submatrices over `ℂ`. -/
theorem permanent_submatrixFock_mul {m n : ℕ}
    (V U : Matrix (Fin m) (Fin m) ℂ) (S T : FockState m n) :
    (submatrixFock (V * U) S T).permanent =
      ∑ K : FockState m n,
        ((submatrixFock V S K).permanent * (submatrixFock U K T).permanent) /
          (fockFact K : ℂ) := by
  classical
  have hlhs : (submatrixFock (V * U) S T).permanent =
      ∑ K : FockState m n,
        ∑ f ∈ Finset.univ.filter (fun f : Fin n → Fin m => histogram f = K),
          ∑ σ : Equiv.Perm (Fin n),
            ∏ a : Fin n, V (modeList S a) (f a) * U (f a) (modeList T (σ a)) := by
    simp only [permanent_eq_sum_row, submatrixFock_apply, Matrix.mul_apply, Fintype.prod_sum]
    rw [Finset.sum_comm]
    have hfib := Finset.sum_fiberwise_of_maps_to
      (s := (Finset.univ : Finset (Fin n → Fin m)))
      (t := (Finset.univ : Finset (FockState m n)))
      (g := histogram)
      (f := fun f : Fin n → Fin m =>
        ∑ σ : Equiv.Perm (Fin n),
          ∏ a : Fin n, V (modeList S a) (f a) * U (f a) (modeList T (σ a)))
      (fun _ _ => Finset.mem_univ _)
    exact hfib.symm
  rw [hlhs]
  refine Finset.sum_congr rfl fun K _ => ?_
  have hK : (fockFact K : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (fockFact_ne_zero K)
  rw [eq_div_iff hK, mul_comm]
  rw [← nsmul_eq_mul, ← sum_perm_comp_eq K (fun f =>
    ∑ σ : Equiv.Perm (Fin n), ∏ a : Fin n, V (modeList S a) (f a) * U (f a) (modeList T (σ a)))]
  simp only [permanent_eq_sum_row, submatrixFock_apply, Function.comp_apply]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun π _ => ?_
  rw [Finset.mul_sum]
  refine Fintype.sum_equiv (Equiv.mulRight π⁻¹)
    (fun σ => ∏ a : Fin n,
      V (modeList S a) (modeList K (π a)) * U (modeList K (π a)) (modeList T (σ a)))
    (fun τ => (∏ a : Fin n, V (modeList S a) (modeList K (π a))) *
      ∏ b : Fin n, U (modeList K b) (modeList T (τ b)))
    fun σ => ?_
  rw [Finset.prod_mul_distrib]
  congr 1
  exact Fintype.prod_equiv π
    (fun a => U (modeList K (π a)) (modeList T (σ a)))
    (fun b => U (modeList K b) (modeList T ((σ * π⁻¹) b)))
    fun a => by simp [Equiv.Perm.mul_apply]

/-! ### The bosonic photonic homomorphism `φ` -/

/-- Normalization factor `√(s₁! ⋯ sₘ!)` for a Fock basis state `S`. -/
noncomputable def fockNorm {m n : ℕ} (S : FockState m n) : ℂ :=
  (Real.sqrt (fockFact S : ℝ) : ℂ)

theorem fockNorm_eq {m n : ℕ} (S : FockState m n) :
    fockNorm S = (Real.sqrt (fockFact S : ℝ) : ℂ) := by
  simp [fockNorm]

theorem fockNorm_cast {m n₁ n₂ : ℕ} (h : n₁ = n₂) (S : FockState m n₁) :
    fockNorm (S.cast h) = fockNorm S := by
  simp [fockNorm, fockFact_cast]

theorem fockNorm_ne_zero {m n : ℕ} (S : FockState m n) : fockNorm S ≠ 0 := by
  unfold fockNorm
  exact Complex.ofReal_ne_zero.mpr
    (Real.sqrt_ne_zero'.mpr (Nat.cast_pos.mpr (fockFact_pos S)))

theorem fockNorm_mul_self {m n : ℕ} (S : FockState m n) :
    fockNorm S * fockNorm S = (fockFact S : ℂ) := by
  unfold fockNorm
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg _), Complex.ofReal_natCast]

theorem fockNorm_mul_fockNorm {m n : ℕ} (S T : FockState m n) :
    fockNorm S * fockNorm T = (Real.sqrt ((fockFact S * fockFact T : ℕ) : ℝ) : ℂ) := by
  unfold fockNorm
  rw [← Complex.ofReal_mul, ← Real.sqrt_mul (Nat.cast_nonneg _), Nat.cast_mul]

/-- The `n`-photon Fock-space transition matrix `φ(U)` with entries
`⟨S|φ(U)|T⟩ = Per(U_{S,T}) / √(s₁!⋯sₘ! t₁!⋯tₘ!)`. -/
noncomputable def photonicHomMatrix {m : ℕ} (n : ℕ) (U : Matrix (Fin m) (Fin m) ℂ) :
    Matrix (FockState m n) (FockState m n) ℂ :=
  Matrix.of fun S T => (submatrixFock U S T).permanent / (fockNorm S * fockNorm T)

theorem photonicHomMatrix_apply {m : ℕ} (n : ℕ) (U : Matrix (Fin m) (Fin m) ℂ)
    (S T : FockState m n) :
    photonicHomMatrix n U S T = (submatrixFock U S T).permanent / (fockNorm S * fockNorm T) := by
  simp [photonicHomMatrix]

/-- Fock-space transition amplitude written with a single denominator square root. -/
theorem photonicHomMatrix_apply_sqrt {m : ℕ} (n : ℕ) (U : Matrix (Fin m) (Fin m) ℂ)
    (S T : FockState m n) :
    photonicHomMatrix n U S T =
      (submatrixFock U S T).permanent /
        (Real.sqrt ((fockFact S * fockFact T : ℕ) : ℝ) : ℂ) := by
  rw [photonicHomMatrix_apply, fockNorm_mul_fockNorm]

/-- Multiplicativity of `φ`: `φ(V U) = φ(V) φ(U)`. -/
theorem photonicHomMatrix_mul {m : ℕ} (n : ℕ) (V U : Matrix (Fin m) (Fin m) ℂ) :
    photonicHomMatrix n (V * U) = photonicHomMatrix n V * photonicHomMatrix n U := by
  ext S T
  rw [photonicHomMatrix_apply, permanent_submatrixFock_mul, Matrix.mul_apply, Finset.sum_div]
  refine Finset.sum_congr rfl fun K _ => ?_
  rw [photonicHomMatrix_apply, photonicHomMatrix_apply]
  have hS : fockNorm S ≠ 0 := fockNorm_ne_zero S
  have hT : fockNorm T ≠ 0 := fockNorm_ne_zero T
  have hK : fockNorm K ≠ 0 := fockNorm_ne_zero K
  rw [← fockNorm_mul_self K]
  field_simp

/-- `φ(1) = 1`. -/
theorem photonicHomMatrix_one (m n : ℕ) :
    photonicHomMatrix n (1 : Matrix (Fin m) (Fin m) ℂ) = 1 := by
  classical
  ext S T
  rw [photonicHomMatrix_apply, Matrix.one_apply]
  have hperm : (submatrixFock (1 : Matrix (Fin m) (Fin m) ℂ) S T).permanent =
      if S = T then (fockFact S : ℂ) else 0 := by
    simp only [permanent_eq_sum_row, submatrixFock_apply, Matrix.one_apply]
    have hterm (σ : Equiv.Perm (Fin n)) :
        (∏ a : Fin n, if modeList S a = modeList T (σ a) then (1 : ℂ) else 0) =
          if modeList T ∘ σ = modeList S then 1 else 0 := by
      by_cases h : modeList T ∘ σ = modeList S
      · rw [ite_eq_left h]
        refine Finset.prod_eq_one fun a _ => ?_
        exact ite_eq_left (congrFun h a).symm
      · rw [ite_eq_right h]
        have hex : ∃ a : Fin n, modeList S a ≠ modeList T (σ a) := by
          by_contra hall
          push Not at hall
          exact h (funext fun a => (hall a).symm)
        obtain ⟨a, ha⟩ := hex
        exact Finset.prod_eq_zero (Finset.mem_univ a) (ite_eq_right ha)
    simp_rw [hterm]
    rw [Finset.sum_boole]
    split_ifs with hST
    · subst hST
      rw [card_perm_comp_eq rfl, histogram_modeList]
    · have hempty : (Finset.univ.filter fun σ : Equiv.Perm (Fin n) =>
          modeList T ∘ σ = modeList S) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro σ _ hσ
        apply hST
        have h1 := congrArg histogram hσ
        rw [histogram_comp_perm, histogram_modeList, histogram_modeList] at h1
        exact h1.symm
      rw [hempty, Finset.card_empty, Nat.cast_zero]
  rw [hperm]
  split_ifs with hST
  · subst hST
    rw [fockNorm_mul_self, div_self (Nat.cast_ne_zero.mpr (fockFact_ne_zero S))]
  · simp

/-- The bosonic photonic homomorphism `φ` from `m × m` complex matrices to operators on the
`n`-photon `m`-mode Fock basis. -/
noncomputable def photonicHom (m n : ℕ) :
    Matrix (Fin m) (Fin m) ℂ →* Matrix (FockState m n) (FockState m n) ℂ where
  toFun := photonicHomMatrix n
  map_one' := photonicHomMatrix_one m n
  map_mul' := photonicHomMatrix_mul n

theorem photonicHom_apply {m n : ℕ} (U : Matrix (Fin m) (Fin m) ℂ) (S T : FockState m n) :
    photonicHom m n U S T = (submatrixFock U S T).permanent / (fockNorm S * fockNorm T) := by
  simp [photonicHom, photonicHomMatrix]

/-- `φ` commutes with conjugate transpose: `φ(Uᴴ) = φ(U)ᴴ`. -/
theorem photonicHom_conjTranspose {m n : ℕ} (U : Matrix (Fin m) (Fin m) ℂ) :
    photonicHom m n Uᴴ = (photonicHom m n U)ᴴ := by
  ext S T
  rw [photonicHom_apply, conjTranspose_apply, photonicHom_apply]
  have hstar_norm (X : FockState m n) : star (fockNorm X) = fockNorm X := by
    simp [fockNorm, Complex.conj_ofReal]
  have hsub : submatrixFock Uᴴ S T = (submatrixFock U T S)ᴴ := by
    ext a b
    simp [submatrixFock_apply, conjTranspose_apply]
  have hperm : (submatrixFock U T S)ᴴ.permanent = star (submatrixFock U T S).permanent := by
    rw [permanent_eq_sum_row, Matrix.permanent]
    simp only [conjTranspose_apply, star_sum, star_prod]
  rw [hsub, hperm, star_div₀, star_mul', hstar_norm, hstar_norm, mul_comm (fockNorm T)]

/-- Restriction of the photonic homomorphism `φ` to the unitary group: `U(m) →* U(Φ_{m,n})`. -/
noncomputable def photonicHomUnitary (m n : ℕ) :
    unitaryGroup (Fin m) ℂ →* unitaryGroup (FockState m n) ℂ where
  toFun U := ⟨photonicHom m n (U : Matrix (Fin m) (Fin m) ℂ), by
    rw [mem_unitaryGroup_iff, star_eq_conjTranspose, ← photonicHom_conjTranspose, ← map_mul]
    have hU : (U : Matrix (Fin m) (Fin m) ℂ) * (U : Matrix (Fin m) (Fin m) ℂ)ᴴ = 1 :=
      mem_unitaryGroup_iff.mp U.2
    rw [hU, map_one]⟩
  map_one' := Subtype.ext (map_one (photonicHom m n))
  map_mul' U V := Subtype.ext (map_mul (photonicHom m n) U.1 V.1)

/-! ### Mode-subset embedding and locality of `φ` -/

/-- Embed a `k × k` optical matrix `A` on the `k` distinct modes `e : Fin k ↪ Fin m`, acting as
the identity on all other modes. -/
noncomputable def embedModes {R : Type*} [Zero R] [One R] {k m : ℕ} (e : Fin k ↪ Fin m)
    (A : Matrix (Fin k) (Fin k) R) : Matrix (Fin m) (Fin m) R :=
  Matrix.of fun r c =>
    if hr : r ∈ Set.range e then
      if hc : c ∈ Set.range e then
        A (Classical.choose hr) (Classical.choose hc)
      else 0
    else
      if r = c then 1 else 0

theorem embedModes_apply_active {R : Type*} [Zero R] [One R] {k m : ℕ} (e : Fin k ↪ Fin m)
    (A : Matrix (Fin k) (Fin k) R) (i j : Fin k) :
    embedModes e A (e i) (e j) = A i j := by
  have hi : e i ∈ Set.range e := ⟨i, rfl⟩
  have hj : e j ∈ Set.range e := ⟨j, rfl⟩
  simp only [embedModes, Matrix.of_apply, hi, hj, ↓reduceDIte]
  rw [e.injective (Classical.choose_spec hi), e.injective (Classical.choose_spec hj)]

theorem embedModes_apply_of_not_mem_left {R : Type*} [Zero R] [One R] {k m : ℕ}
    (e : Fin k ↪ Fin m) (A : Matrix (Fin k) (Fin k) R) {r : Fin m} (hr : r ∉ Set.range e)
    (c : Fin m) :
    embedModes e A r c = if r = c then 1 else 0 := by
  unfold embedModes
  simp only [Matrix.of_apply, dite_eq_right_iff]
  intro h
  exact absurd h hr

theorem embedModes_apply_of_not_mem_right {R : Type*} [Zero R] [One R] {k m : ℕ}
    (e : Fin k ↪ Fin m) (A : Matrix (Fin k) (Fin k) R) (r : Fin m) {c : Fin m}
    (hc : c ∉ Set.range e) :
    embedModes e A r c = if r = c then 1 else 0 := by
  by_cases hr : r ∈ Set.range e
  · have hne : r ≠ c := fun h => hc (h ▸ hr)
    unfold embedModes
    simp only [Matrix.of_apply, hr, hc, ↓reduceDIte, hne, ↓reduceIte]
  · exact embedModes_apply_of_not_mem_left e A hr c

theorem embedModes_one {R : Type*} [Zero R] [One R] {k m : ℕ} (e : Fin k ↪ Fin m) :
    embedModes e (1 : Matrix (Fin k) (Fin k) R) = 1 := by
  ext r c
  by_cases hr : r ∈ Set.range e
  · obtain ⟨i, rfl⟩ := hr
    by_cases hc : c ∈ Set.range e
    · obtain ⟨j, rfl⟩ := hc
      rw [embedModes_apply_active, Matrix.one_apply, Matrix.one_apply]
      exact if_congr e.injective.eq_iff.symm rfl rfl
    · rw [embedModes_apply_of_not_mem_right e _ _ hc, Matrix.one_apply]
  · rw [embedModes_apply_of_not_mem_left e _ hr, Matrix.one_apply]

theorem embedModes_mul {R : Type*} [Semiring R] {k m : ℕ} (e : Fin k ↪ Fin m)
    (A B : Matrix (Fin k) (Fin k) R) :
    embedModes e (A * B) = embedModes e A * embedModes e B := by
  classical
  ext r c
  rw [Matrix.mul_apply]
  by_cases hr : r ∈ Set.range e
  · obtain ⟨i, rfl⟩ := hr
    have hsum : ∑ x : Fin m, embedModes e A (e i) x * embedModes e B x c =
        ∑ l : Fin k, embedModes e A (e i) (e l) * embedModes e B (e l) c := by
      rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image e))]
      · rw [Finset.sum_image (fun a _ b _ h => e.injective h)]
      · intro x _ hx
        have hxr : x ∉ Set.range e := by
          rintro ⟨l, rfl⟩; exact hx (Finset.mem_image_of_mem e (Finset.mem_univ l))
        have hne : e i ≠ x := fun h => hxr (h ▸ ⟨i, rfl⟩)
        rw [embedModes_apply_of_not_mem_right e _ _ hxr, ite_eq_right hne, zero_mul]
    rw [hsum]
    by_cases hc : c ∈ Set.range e
    · obtain ⟨j, rfl⟩ := hc
      rw [embedModes_apply_active, Matrix.mul_apply]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [embedModes_apply_active, embedModes_apply_active]
    · have hne : e i ≠ c := fun h => hc (h ▸ ⟨i, rfl⟩)
      rw [embedModes_apply_of_not_mem_right e _ _ hc, ite_eq_right hne]
      refine (Finset.sum_eq_zero fun l _ => ?_).symm
      have hnel : e l ≠ c := fun h => hc (h ▸ ⟨l, rfl⟩)
      rw [embedModes_apply_of_not_mem_right e _ _ hc, ite_eq_right hnel, mul_zero]
  · rw [embedModes_apply_of_not_mem_left e _ hr]
    rw [Finset.sum_eq_single r]
    · rw [embedModes_apply_of_not_mem_left e _ hr, ite_eq_left rfl, one_mul,
        embedModes_apply_of_not_mem_left e _ hr]
    · intro x _ hxr
      rw [embedModes_apply_of_not_mem_left e _ hr, ite_eq_right hxr.symm, zero_mul]
    · intro hmem; exact absurd (Finset.mem_univ r) hmem

theorem embedModes_conjTranspose {k m : ℕ} (e : Fin k ↪ Fin m) (A : Matrix (Fin k) (Fin k) ℂ) :
    (embedModes e A)ᴴ = embedModes e Aᴴ := by
  ext r c
  rw [conjTranspose_apply]
  by_cases hr : r ∈ Set.range e
  · obtain ⟨i, rfl⟩ := hr
    by_cases hc : c ∈ Set.range e
    · obtain ⟨j, rfl⟩ := hc
      rw [embedModes_apply_active, embedModes_apply_active, conjTranspose_apply]
    · rw [embedModes_apply_of_not_mem_left e _ hc, embedModes_apply_of_not_mem_right e _ _ hc]
      have hne : e i ≠ c := fun h => hc (h ▸ ⟨i, rfl⟩)
      simp [hne, hne.symm]
  · rw [embedModes_apply_of_not_mem_right e _ _ hr, embedModes_apply_of_not_mem_left e _ hr]
    by_cases hrc : r = c
    · subst hrc; simp only [↓reduceIte, star_one]
    · simp only [hrc, Ne.symm hrc, ↓reduceIte]
      exact star_zero ℂ

theorem embedModes_mem_unitaryGroup {k m : ℕ} (e : Fin k ↪ Fin m)
    {A : Matrix (Fin k) (Fin k) ℂ} (hA : A ∈ unitaryGroup (Fin k) ℂ) :
    embedModes e A ∈ unitaryGroup (Fin m) ℂ := by
  rw [mem_unitaryGroup_iff, star_eq_conjTranspose, embedModes_conjTranspose, ← embedModes_mul]
  have h1 : A * Aᴴ = 1 := mem_unitaryGroup_iff.mp hA
  rw [h1, embedModes_one]

/-- Restrict a Fock state `S : FockState m n` to the active mode subset `e : Fin k ↪ Fin m`. -/
def restrictFock {k m n : ℕ} (e : Fin k ↪ Fin m) (S : FockState m n) :
    FockState k (∑ i : Fin k, S.occ (e i)) where
  occ i := S.occ (e i)
  sum_occ := rfl

@[simp]
theorem restrictFock_occ {k m n : ℕ} (e : Fin k ↪ Fin m) (S : FockState m n) (i : Fin k) :
    (restrictFock e S).occ i = S.occ (e i) := by
  simp [restrictFock]

/-- Off-support occupation conservation: if `S` and `T` disagree on any mode outside `e`, then
`⟨S|φ(embedModes e A)|T⟩ = 0`. -/
theorem photonicHom_embedModes_eq_zero {k m n : ℕ} (e : Fin k ↪ Fin m)
    (A : Matrix (Fin k) (Fin k) ℂ) {S T : FockState m n}
    (hdiff : ∃ j : Fin m, j ∉ Set.range e ∧ S.occ j ≠ T.occ j) :
    photonicHom m n (embedModes e A) S T = 0 := by
  classical
  rw [photonicHom_apply]
  suffices hperm : (submatrixFock (embedModes e A) S T).permanent = 0 by
    rw [hperm, zero_div]
  obtain ⟨j, hj, hne⟩ := hdiff
  rw [permanent_eq_sum_row]
  refine Finset.sum_eq_zero fun σ _ => ?_
  by_contra hprod
  have hnonzero : ∀ a : Fin n, embedModes e A (modeList S a) (modeList T (σ a)) ≠ 0 := by
    intro a ha
    exact hprod (Finset.prod_eq_zero (Finset.mem_univ a) (by rw [submatrixFock_apply]; exact ha))
  have hiff : ∀ a : Fin n, modeList S a = j ↔ modeList T (σ a) = j := by
    intro a
    constructor
    · intro hSa
      have hnz := hnonzero a
      rw [hSa, embedModes_apply_of_not_mem_left e _ hj] at hnz
      by_contra hTa
      exact hnz (ite_eq_right (Ne.symm hTa))
    · intro hTa
      have hnz := hnonzero a
      rw [hTa, embedModes_apply_of_not_mem_right e _ _ hj] at hnz
      by_contra hSa
      exact hnz (ite_eq_right hSa)
  have hcard : S.occ j = T.occ j := by
    have hS : S.occ j = (Finset.univ.filter fun a : Fin n => modeList S a = j).card := by
      rw [← histogram_occ, histogram_modeList]
    have hT : T.occ j = (Finset.univ.filter fun b : Fin n => modeList T b = j).card := by
      rw [← histogram_occ, histogram_modeList]
    rw [hS, hT]
    refine Finset.card_bij (fun a _ => σ a) ?_ ?_ ?_
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
      exact (hiff a).mp ha
    · intro a₁ _ a₂ _ h
      exact σ.injective h
    · intro b hb
      refine ⟨σ.symm b, ?_, σ.apply_symm_apply b⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
      exact (hiff (σ.symm b)).mpr (by simpa using hb)
  exact hne hcard

/-- Helper: given a Fock state `X : FockState m n` and a target `Y : FockState k nA` with
`Y.occ i = X.occ (e i)`, construct a bijection `{a // modeList X a ∈ range e} ≃ Fin nA`
intertwining `modeList X` and `e ∘ modeList Y`. -/
private theorem exists_activeEquiv {k m n nA : ℕ} (e : Fin k ↪ Fin m)
    (X : FockState m n) (Y : FockState k nA) (hocc : ∀ i : Fin k, Y.occ i = X.occ (e i)) :
    ∃ φ : { a : Fin n // modeList X a ∈ Set.range e } ≃ Fin nA,
      ∀ a : { a : Fin n // modeList X a ∈ Set.range e },
        e (modeList Y (φ a)) = modeList X a.1 := by
  classical
  have hfib (i : Fin k) :
      Fintype.card { a : { a : Fin n // modeList X a ∈ Set.range e } // modeList X a.1 = e i } =
        Fintype.card { r : Fin nA // modeList Y r = i } := by
    have h1 :
        Fintype.card { a : { a : Fin n // modeList X a ∈ Set.range e } // modeList X a.1 = e i } =
          X.occ (e i) := by
      have hX : X.occ (e i) = (Finset.univ.filter fun a : Fin n => modeList X a = e i).card := by
        rw [← histogram_occ, histogram_modeList]
      rw [hX, Fintype.card_subtype]
      refine Finset.card_bij (fun a _ => a.1) ?_ ?_ ?_
      · intro a ha
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
        exact ha
      · intro a₁ _ a₂ _ h; exact Subtype.ext h
      · intro a ha
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
        exact ⟨⟨a, ⟨i, ha.symm⟩⟩, by simp [ha], rfl⟩
    have h2 : Fintype.card { r : Fin nA // modeList Y r = i } = X.occ (e i) := by
      rw [Fintype.card_subtype, ← histogram_occ, histogram_modeList Y, hocc i]
    rw [h1, h2]
  let eq_i (i : Fin k) :
      { a : { a : Fin n // modeList X a ∈ Set.range e } // modeList X a.1 = e i } ≃
        { r : Fin nA // modeList Y r = i } :=
    Fintype.equivOfCardEq (hfib i)
  let gX : { a : Fin n // modeList X a ∈ Set.range e } → Fin k :=
    fun a => Classical.choose a.2
  have hgX (a : { a : Fin n // modeList X a ∈ Set.range e }) : e (gX a) = modeList X a.1 :=
    Classical.choose_spec a.2
  have hfib_eq (i : Fin k) :
      { a : { a : Fin n // modeList X a ∈ Set.range e } // gX a = i } ≃
        { a : { a : Fin n // modeList X a ∈ Set.range e } // modeList X a.1 = e i } :=
    Equiv.subtypeEquivRight fun a =>
      ⟨fun h => by rw [← hgX a, h], fun h => e.injective ((hgX a).trans h)⟩
  let φ : { a : Fin n // modeList X a ∈ Set.range e } ≃ Fin nA :=
    (Equiv.sigmaFiberEquiv gX).symm.trans
      ((Equiv.sigmaCongrRight fun i => (hfib_eq i).trans (eq_i i)).trans
        (Equiv.sigmaFiberEquiv (modeList Y)))
  refine ⟨φ, fun a => ?_⟩
  have hval : φ a = ((hfib_eq (gX a)).trans (eq_i (gX a)) ⟨a, rfl⟩).1 := rfl
  rw [hval]
  have hspec := ((hfib_eq (gX a)).trans (eq_i (gX a)) ⟨a, rfl⟩).2
  rw [hspec, hgX a]

/-- Factoring the permanent of `embedModes e A` on `S, T` agreeing outside `e`. -/
theorem permanent_submatrixFock_embedModes {k m n : ℕ} (e : Fin k ↪ Fin m)
    (A : Matrix (Fin k) (Fin k) ℂ) {S T : FockState m n}
    (hagree : ∀ j : Fin m, j ∉ Set.range e → S.occ j = T.occ j) :
    ∃ hsum : (∑ i : Fin k, T.occ (e i)) = (∑ i : Fin k, S.occ (e i)),
      (submatrixFock (embedModes e A) S T).permanent =
        ((∏ j ∈ Finset.univ.filter (fun j : Fin m => j ∉ Set.range e), (S.occ j)! : ℕ) : ℂ) *
          (submatrixFock A (restrictFock e S) ((restrictFock e T).cast hsum)).permanent := by
  classical
  have hsum : (∑ i : Fin k, T.occ (e i)) = (∑ i : Fin k, S.occ (e i)) := by
    have hsplit (X : FockState m n) :
        (∑ i : Fin k, X.occ (e i)) +
          (∑ j ∈ Finset.univ.filter (fun j : Fin m => j ∉ Set.range e), X.occ j) = n := by
      have himg : ∑ i : Fin k, X.occ (e i) =
          ∑ j ∈ Finset.univ.filter (fun j : Fin m => j ∈ Set.range e), X.occ j := by
        rw [← Finset.sum_image (f := X.occ) (g := e) (fun a _ b _ h => e.injective h)]
        congr 1
        ext j
        simp [Set.mem_range]
      rw [himg, Finset.sum_filter_add_sum_filter_not, X.sum_occ]
    have hS := hsplit S
    have hT := hsplit T
    have hoff : (∑ j ∈ Finset.univ.filter (fun j : Fin m => j ∉ Set.range e), S.occ j) =
        (∑ j ∈ Finset.univ.filter (fun j : Fin m => j ∉ Set.range e), T.occ j) :=
      Finset.sum_congr rfl fun j hj => hagree j (Finset.mem_filter.mp hj).2
    omega
  refine ⟨hsum, ?_⟩
  let nA := ∑ i : Fin k, S.occ (e i)
  let S' : FockState k nA := restrictFock e S
  let T' : FockState k nA := (restrictFock e T).cast hsum
  let pS : Fin n → Prop := fun a => modeList S a ∈ Set.range e
  let pT : Fin n → Prop := fun b => modeList T b ∈ Set.range e
  obtain ⟨φS, hφS⟩ := exists_activeEquiv e S S' (fun _ => rfl)
  obtain ⟨φT, hφT⟩ := exists_activeEquiv e T T' (fun i => by simp [T'])
  have hcardS_act : Fintype.card { a : Fin n // pS a } = nA := by
    rw [Fintype.card_congr φS, Fintype.card_fin]
  have hcardT_act : Fintype.card { b : Fin n // pT b } = nA := by
    rw [Fintype.card_congr φT, Fintype.card_fin]
  let Good (σ : Equiv.Perm (Fin n)) : Prop :=
    ∀ a : Fin n, ¬pS a → modeList T (σ a) = modeList S a
  have hbad : ∀ σ : Equiv.Perm (Fin n), ¬Good σ →
      (∏ a : Fin n, embedModes e A (modeList S a) (modeList T (σ a))) = 0 := by
    intro σ hσ
    simp only [Good, not_forall] at hσ
    obtain ⟨a, ha, hne⟩ := hσ
    refine Finset.prod_eq_zero (Finset.mem_univ a) ?_
    rw [embedModes_apply_of_not_mem_left e _ ha, ite_eq_right (Ne.symm hne)]
  have hgood_pT : ∀ {σ : Equiv.Perm (Fin n)}, Good σ → ∀ a : Fin n, pT (σ a) ↔ pS a := by
    intro σ hσ a
    constructor
    · intro hTa
      by_contra hSa
      have heq : modeList T (σ a) = modeList S a := hσ a hSa
      have hmem : modeList S a ∈ Set.range e := by rw [← heq]; exact hTa
      exact hSa hmem
    · intro hSa
      by_contra hTa
      have hcardS : (Finset.univ.filter fun x : Fin n => ¬pS x).card = n - nA := by
        have h1 : (Finset.univ.filter pS).card = nA := by
          rw [← Fintype.card_subtype]; exact hcardS_act
        have h2 := Finset.card_filter_add_card_filter_not (s := Finset.univ) (p := pS)
        simp only [Finset.card_univ, Fintype.card_fin] at h2
        omega
      have hcardT : (Finset.univ.filter fun y : Fin n => ¬pT y).card = n - nA := by
        have h1 : (Finset.univ.filter pT).card = nA := by
          rw [← Fintype.card_subtype]; exact hcardT_act
        have h2 := Finset.card_filter_add_card_filter_not (s := Finset.univ) (p := pT)
        simp only [Finset.card_univ, Fintype.card_fin] at h2
        omega
      have hsub : (Finset.univ.filter fun x : Fin n => ¬pS x).image σ ⊆
          Finset.univ.filter fun y : Fin n => ¬pT y := by
        intro y hy
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
        have hx' : ¬pS x := (Finset.mem_filter.mp hx).2
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        intro hTx
        have hmem : modeList S x ∈ Set.range e := by rw [← hσ x hx']; exact hTx
        exact hx' hmem
      have heq : (Finset.univ.filter fun x : Fin n => ¬pS x).image σ =
          Finset.univ.filter fun y : Fin n => ¬pT y :=
        Finset.eq_of_subset_of_card_le hsub
          (by rw [Finset.card_image_of_injective _ σ.injective, hcardS, hcardT])
      have hmem : σ a ∈ (Finset.univ.filter fun x : Fin n => ¬pS x).image σ := by
        rw [heq]
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hTa⟩
      obtain ⟨x, hx, hxa⟩ := Finset.mem_image.mp hmem
      have hax : x = a := σ.injective hxa
      subst hax
      exact (Finset.mem_filter.mp hx).2 hSa
  have hprod_good (σ : Equiv.Perm (Fin n)) (hσ : Good σ) :
      (∏ a : Fin n, embedModes e A (modeList S a) (modeList T (σ a))) =
        ∏ r : Fin nA,
          A (modeList S' r)
            (modeList T' (φT ⟨σ (φS.symm r).1, (hgood_pT hσ _).mpr (φS.symm r).2⟩)) := by
    rw [← Finset.prod_filter_mul_prod_filter_not (s := Finset.univ) (p := pS)]
    have hinact : (∏ a ∈ Finset.univ.filter (fun a : Fin n => ¬pS a),
        embedModes e A (modeList S a) (modeList T (σ a))) = 1 := by
      refine Finset.prod_eq_one fun a ha => ?_
      have hna : ¬pS a := (Finset.mem_filter.mp ha).2
      rw [embedModes_apply_of_not_mem_left e _ hna, ite_eq_left (hσ a hna).symm]
    rw [hinact, mul_one]
    refine Finset.prod_bij (fun a ha => φS ⟨a, (Finset.mem_filter.mp ha).2⟩) ?_ ?_ ?_ ?_
    · intro _ _; exact Finset.mem_univ _
    · intro a₁ ha₁ a₂ ha₂ h
      exact congrArg Subtype.val (φS.injective h)
    · intro r _
      exact ⟨(φS.symm r).1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (φS.symm r).2⟩,
        φS.apply_symm_apply r⟩
    · intro a ha
      have ha' : pS a := (Finset.mem_filter.mp ha).2
      have h1 : modeList S a = e (modeList S' (φS ⟨a, ha'⟩)) := (hφS ⟨a, ha'⟩).symm
      have h2 : modeList T (σ a) =
          e (modeList T' (φT ⟨σ (φS.symm (φS ⟨a, ha'⟩)).1,
            (hgood_pT hσ _).mpr (φS.symm (φS ⟨a, ha'⟩)).2⟩)) := by
        simpa [φS.symm_apply_apply] using (hφT ⟨σ a, (hgood_pT hσ a).mpr ha'⟩).symm
      rw [h1, h2, embedModes_apply_active]
  let InactiveMode := { j : Fin m // j ∉ Set.range e }
  let fS_inact : { a : Fin n // ¬pS a } → InactiveMode := fun a => ⟨modeList S a.1, a.2⟩
  let fT_inact : { b : Fin n // ¬pT b } → InactiveMode := fun b => ⟨modeList T b.1, b.2⟩
  let InactivePerms := ∀ j : InactiveMode,
    { a : { a : Fin n // ¬pS a } // fS_inact a = j } ≃
      { b : { b : Fin n // ¬pT b } // fT_inact b = j }
  let goodEquiv : { σ : Equiv.Perm (Fin n) // Good σ } ≃ Equiv.Perm (Fin nA) × InactivePerms :=
    { toFun := fun ⟨σ, hσ⟩ =>
        ( { toFun := fun r => φT ⟨σ (φS.symm r).1, (hgood_pT hσ _).mpr (φS.symm r).2⟩
            invFun := fun r => φS ⟨σ.symm (φT.symm r).1,
              (hgood_pT hσ (σ.symm (φT.symm r).1)).mp (by
                rw [σ.apply_symm_apply]; exact (φT.symm r).2)⟩
            left_inv := fun r => by simp
            right_inv := fun r => by simp },
          fun j =>
            { toFun := fun ⟨⟨a, hna⟩, ha⟩ =>
                ⟨⟨σ a, fun h => hna ((hgood_pT hσ a).mp h)⟩,
                  Subtype.ext ((hσ a hna).trans (congrArg Subtype.val ha))⟩
              invFun := fun ⟨⟨b, hnb⟩, hb⟩ =>
                ⟨⟨σ.symm b, fun h => hnb (by
                    have h1 := (hgood_pT hσ (σ.symm b)).mpr h
                    rwa [σ.apply_symm_apply] at h1)⟩,
                  Subtype.ext (by
                    have hna : ¬pS (σ.symm b) := fun h => hnb (by
                      have h1 := (hgood_pT hσ (σ.symm b)).mpr h
                      rwa [σ.apply_symm_apply] at h1)
                    have h1 : modeList T b = modeList S (σ.symm b) := by
                      simpa [σ.apply_symm_apply] using hσ (σ.symm b) hna
                    have h2 : modeList T b = j.1 := congrArg Subtype.val hb
                    exact h1.symm.trans h2)⟩
              left_inv := fun ⟨⟨a, _⟩, _⟩ => Subtype.ext (Subtype.ext (σ.symm_apply_apply a))
              right_inv := fun ⟨⟨b, _⟩, _⟩ => Subtype.ext (Subtype.ext (σ.apply_symm_apply b)) } )
      invFun := fun ⟨τ, ψ⟩ =>
        let actEq : { a : Fin n // pS a } ≃ { b : Fin n // pT b } :=
          φS.trans (τ.trans φT.symm)
        let inactEq : { a : Fin n // ¬pS a } ≃ { b : Fin n // ¬pT b } :=
          (Equiv.sigmaFiberEquiv fS_inact).symm.trans
            ((Equiv.sigmaCongrRight ψ).trans (Equiv.sigmaFiberEquiv fT_inact))
        ⟨(Equiv.sumCompl pS).symm.trans ((Equiv.sumCongr actEq inactEq).trans (Equiv.sumCompl pT)),
          fun a hna => by
            have h1 : ((Equiv.sumCompl pS).symm.trans
                ((Equiv.sumCongr actEq inactEq).trans (Equiv.sumCompl pT))) a =
                (inactEq ⟨a, hna⟩).1 := by
              simp [Equiv.trans_apply, sumCompl_symm_neg pS hna]
            rw [h1]
            have h2 : inactEq ⟨a, hna⟩ = (ψ (fS_inact ⟨a, hna⟩) ⟨⟨a, hna⟩, rfl⟩).1 := rfl
            rw [h2]
            exact congrArg Subtype.val (ψ (fS_inact ⟨a, hna⟩) ⟨⟨a, hna⟩, rfl⟩).2⟩
      left_inv := fun ⟨σ, hσ⟩ => by
        apply Subtype.ext
        ext a
        by_cases ha : pS a
        · simp [Equiv.trans_apply, sumCompl_symm_pos pS ha]
        · simp [Equiv.trans_apply, sumCompl_symm_neg pS ha, sigmaFiberEquiv_symm_eq]
      right_inv := fun ⟨τ, ψ⟩ => by
        ext r
        · simp [Equiv.trans_apply]
        · rename_i j a
          obtain ⟨⟨aval, hna⟩, ha⟩ := a
          subst ha
          simp [Equiv.trans_apply, sigmaFiberEquiv_symm_eq] }
  have hcardInactive : Fintype.card InactivePerms =
      ∏ j ∈ Finset.univ.filter (fun j : Fin m => j ∉ Set.range e), (S.occ j)! := by
    rw [Fintype.card_pi]
    have hfactor : ∀ j : InactiveMode,
        Fintype.card ({ a : { a : Fin n // ¬pS a } // fS_inact a = j } ≃
          { b : { b : Fin n // ¬pT b } // fT_inact b = j }) = (S.occ j.1)! := by
      intro j
      have h1 : Fintype.card { a : { a : Fin n // ¬pS a } // fS_inact a = j } = S.occ j.1 := by
        have hS : S.occ j.1 = (Finset.univ.filter fun a : Fin n => modeList S a = j.1).card := by
          rw [← histogram_occ, histogram_modeList]
        rw [hS, Fintype.card_subtype]
        refine Finset.card_bij (fun a _ => a.1) ?_ ?_ ?_
        · intro a ha
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
          exact congrArg Subtype.val ha
        · intro a₁ _ a₂ _ h; exact Subtype.ext h
        · intro a ha
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
          have hna : ¬pS a := by
            change modeList S a ∉ Set.range e
            rw [ha]
            exact j.2
          exact ⟨⟨a, hna⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Subtype.ext ha⟩, rfl⟩
      have h2 : Fintype.card { b : { b : Fin n // ¬pT b } // fT_inact b = j } = S.occ j.1 := by
        have hT : T.occ j.1 = (Finset.univ.filter fun b : Fin n => modeList T b = j.1).card := by
          rw [← histogram_occ, histogram_modeList]
        rw [hagree j.1 j.2, hT, Fintype.card_subtype]
        refine Finset.card_bij (fun b _ => b.1) ?_ ?_ ?_
        · intro b hb
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
          exact congrArg Subtype.val hb
        · intro b₁ _ b₂ _ h; exact Subtype.ext h
        · intro b hb
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
          have hnb : ¬pT b := by
            change modeList T b ∉ Set.range e
            rw [hb]
            exact j.2
          exact ⟨⟨b, hnb⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Subtype.ext hb⟩, rfl⟩
      rw [Fintype.card_congr (Equiv.equivCongr (Fintype.equivFinOfCardEq h1)
        (Fintype.equivFinOfCardEq h2)), Fintype.card_perm, Fintype.card_fin]
    calc (∏ j : InactiveMode,
            Fintype.card ({ a : { a : Fin n // ¬pS a } // fS_inact a = j } ≃
              { b : { b : Fin n // ¬pT b } // fT_inact b = j }))
        = ∏ j : InactiveMode, (S.occ j.1)! := Finset.prod_congr rfl fun j _ => hfactor j
      _ = ∏ j ∈ Finset.univ.filter (fun j : Fin m => j ∉ Set.range e), (S.occ j)! :=
          (Finset.prod_subtype (Finset.univ.filter fun j : Fin m => j ∉ Set.range e)
            (fun j => by simp) (fun j => (S.occ j)!)).symm
  rw [permanent_eq_sum_row]
  have hfilt : (∑ σ : Equiv.Perm (Fin n),
      ∏ a : Fin n, submatrixFock (embedModes e A) S T a (σ a)) =
      ∑ σ : { σ : Equiv.Perm (Fin n) // Good σ },
        ∏ a : Fin n, embedModes e A (modeList S a) (modeList T (σ.1 a)) := by
    simp only [submatrixFock_apply]
    have hsub := (Finset.sum_subset (Finset.filter_subset Good Finset.univ) fun σ _ hσ =>
      hbad σ (by simpa using hσ)).symm
    rw [hsub]
    exact Finset.sum_subtype (Finset.univ.filter Good) (fun _ => by simp)
      (fun σ => ∏ a : Fin n, embedModes e A (modeList S a) (modeList T (σ a)))
  rw [hfilt]
  rw [Fintype.sum_equiv goodEquiv _
    (fun p : Equiv.Perm (Fin nA) × InactivePerms =>
      ∏ r : Fin nA, A (modeList S' r) (modeList T' (p.1 r)))
    (fun ⟨σ, hσ⟩ => hprod_good σ hσ)]
  rw [Fintype.sum_prod_type_right]
  dsimp only
  rw [Finset.sum_const, Finset.card_univ, hcardInactive, nsmul_eq_mul, permanent_eq_sum_row]
  simp only [submatrixFock_apply]
  rfl

/-- Locality of `φ`: when `S` and `T` agree outside the active modes `e : Fin k ↪ Fin m`,
`⟨S|φ(embedModes e A)|T⟩ = ⟨S|_e|φ(A)|T|_e⟩`. -/
theorem photonicHom_embedModes {k m n : ℕ} (e : Fin k ↪ Fin m)
    (A : Matrix (Fin k) (Fin k) ℂ) {S T : FockState m n}
    (hagree : ∀ j : Fin m, j ∉ Set.range e → S.occ j = T.occ j) :
    ∃ hsum : (∑ i : Fin k, T.occ (e i)) = (∑ i : Fin k, S.occ (e i)),
      photonicHom m n (embedModes e A) S T =
        photonicHom k (∑ i : Fin k, S.occ (e i)) A (restrictFock e S)
          ((restrictFock e T).cast hsum) := by
  classical
  obtain ⟨hsum, hperm⟩ := permanent_submatrixFock_embedModes e A hagree
  refine ⟨hsum, ?_⟩
  rw [photonicHom_apply, photonicHom_apply, hperm]
  have hsplitFact (X : FockState m n) :
      fockFact X =
        (∏ j ∈ Finset.univ.filter (fun j : Fin m => j ∉ Set.range e), (X.occ j)!) *
          fockFact (restrictFock e X) := by
    unfold fockFact
    rw [← Finset.prod_filter_mul_prod_filter_not (s := Finset.univ)
      (p := fun j : Fin m => j ∉ Set.range e)]
    congr 1
    simp only [restrictFock_occ]
    rw [← Finset.prod_image (f := fun j => (X.occ j)!) (g := e) (fun a _ b _ h => e.injective h)]
    congr 1
    ext j
    simp [Set.mem_range]
  have hoffFact :
      (∏ j ∈ Finset.univ.filter (fun j : Fin m => j ∉ Set.range e), (S.occ j)!) =
        ∏ j ∈ Finset.univ.filter (fun j : Fin m => j ∉ Set.range e), (T.occ j)! :=
    Finset.prod_congr rfl fun j hj => by rw [hagree j (Finset.mem_filter.mp hj).2]
  set off := ∏ j ∈ Finset.univ.filter (fun j : Fin m => j ∉ Set.range e), (S.occ j)!
  have hoff_pos : 0 < off := Finset.prod_pos fun j _ => Nat.factorial_pos _
  have hoff_ne : (off : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hoff_pos.ne'
  have hnormS : fockNorm S = (Real.sqrt (off : ℝ) : ℂ) * fockNorm (restrictFock e S) := by
    unfold fockNorm
    rw [hsplitFact S, Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg _), Complex.ofReal_mul]
  have hnormT : fockNorm T =
      (Real.sqrt (off : ℝ) : ℂ) * fockNorm ((restrictFock e T).cast hsum) := by
    rw [fockNorm_cast]
    unfold fockNorm
    rw [hsplitFact T, ← hoffFact, Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg _),
      Complex.ofReal_mul]
  have hsq : (Real.sqrt (off : ℝ) : ℂ) * (Real.sqrt (off : ℝ) : ℂ) = (off : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg _), Complex.ofReal_natCast]
  rw [hnormS, hnormT]
  calc (off : ℂ) *
        (submatrixFock A (restrictFock e S) ((restrictFock e T).cast hsum)).permanent /
        ((Real.sqrt (off : ℝ) : ℂ) * fockNorm (restrictFock e S) *
          ((Real.sqrt (off : ℝ) : ℂ) * fockNorm ((restrictFock e T).cast hsum)))
      = (off : ℂ) *
          (submatrixFock A (restrictFock e S) ((restrictFock e T).cast hsum)).permanent /
          (((Real.sqrt (off : ℝ) : ℂ) * (Real.sqrt (off : ℝ) : ℂ)) *
            (fockNorm (restrictFock e S) * fockNorm ((restrictFock e T).cast hsum))) := by ring
    _ = (off : ℂ) *
          (submatrixFock A (restrictFock e S) ((restrictFock e T).cast hsum)).permanent /
          ((off : ℂ) *
            (fockNorm (restrictFock e S) * fockNorm ((restrictFock e T).cast hsum))) := by
        rw [hsq]
    _ = _ := mul_div_mul_left _ _ hoff_ne

end CslibFrontier.Quantum.LinearOptics
