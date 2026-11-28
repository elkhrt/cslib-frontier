module

public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Data.ENat.Lattice
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
import CslibFrontier.Computability.Circuit.Arithmetic.DeterminantalComplexity
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Padded Determinantal Projections and Border Determinantal Complexity

Defines padded linear projections between homogeneous multivariate polynomials, the
general linear group orbit and affine Zariski orbit closure of the generic determinant
polynomial, exact padded determinantal complexity, and border determinantal complexity
over an arbitrary field `K`.

## Main definitions

* `CslibFrontier.Computability.Circuit.Arithmetic.HomogeneousPoly`: the space of
  homogeneous polynomials of degree `m` in `M` variables over a commutative ring `K`.
* `CslibFrontier.Computability.Circuit.Arithmetic.detPoly`: the generic `n × n`
  determinant viewed as a homogeneous degree-`n` polynomial in `n * n` variables.
* `CslibFrontier.Computability.Circuit.Arithmetic.detOrbit`,
  `CslibFrontier.Computability.Circuit.Arithmetic.detEndOrbit`,
  `CslibFrontier.Computability.Circuit.Arithmetic.detOrbitClosure`: the `GL_{n^2}`-orbit,
  endomorphism orbit, and affine Zariski orbit closure of `detPoly`.
* `CslibFrontier.Computability.Circuit.Arithmetic.IsPaddedLift`: relation asserting that
  a homogeneous degree-`n` polynomial is a padded linear projection `ℓ^(n - m) * P ∘ π`
  of a homogeneous degree-`m` polynomial `P`.
* `CslibFrontier.Computability.Circuit.Arithmetic.paddedDetComplexity`,
  `CslibFrontier.Computability.Circuit.Arithmetic.borderDetComplexity`: exact padded
  determinantal complexity and border determinantal complexity valued in `ℕ∞`.

## Main results

* `CslibFrontier.Computability.Circuit.Arithmetic.detEndOrbit_subset_detOrbitClosure`:
  over any infinite field `K`, every endomorphism translate of `detPoly` lies in the
  affine Zariski closure of the `GL_{n^2}(K)`-orbit of `detPoly`.
* `CslibFrontier.Computability.Circuit.Arithmetic.borderDetComplexity_le_paddedDetComplexity`:
  over any infinite field `K`, border determinantal complexity never exceeds padded
  determinantal complexity.
* `CslibFrontier.Computability.Circuit.Arithmetic.paddedDetComplexity_lt_top`,
  `CslibFrontier.Computability.Circuit.Arithmetic.borderDetComplexity_lt_top`: over any
  infinite field `K`, every homogeneous polynomial has finite padded and border
  determinantal complexity.
* `CslibFrontier.Computability.Circuit.Arithmetic.paddedDetComplexity_detPoly_le`,
  `CslibFrontier.Computability.Circuit.Arithmetic.borderDetComplexity_detPoly_le`:
  the `n × n` determinant has padded and border determinantal complexity at most `n`.
-/

public section

namespace CslibFrontier.Computability.Circuit.Arithmetic

open MvPolynomial Matrix Polynomial

/-- Multi-indices of total degree `d` in `N` variables. -/
abbrev MonomialIdx (N d : ℕ) : Type :=
  {s : Fin N →₀ ℕ // s ∈ (Finset.univ : Finset (Fin N)).finsuppAntidiag d}

/-- Homogeneous polynomials of degree `d` in `N` variables over `K`. -/
abbrev HomogeneousPoly (K : Type*) [CommRing K] (N d : ℕ) : Type _ :=
  MvPolynomial.homogeneousSubmodule (Fin N) K d

/-- Polynomial coordinate ring on the space of homogeneous degree-`d` polynomials in `N`
variables. -/
abbrev PolyCoordRing (K : Type*) [CommRing K] (N d : ℕ) : Type _ :=
  MvPolynomial (MonomialIdx N d) K

/-- Coordinate vector of coefficients of a homogeneous polynomial `P`. -/
def polyCoords {K : Type*} [CommRing K] {N d : ℕ}
    (P : HomogeneousPoly K N d) : MonomialIdx N d → K :=
  fun α => P.1.coeff α.1

/-- Evaluation of a coordinate polynomial `F` at a homogeneous polynomial `P`. -/
noncomputable def evalAtPoly {K : Type*} [CommRing K] {N d : ℕ}
    (P : HomogeneousPoly K N d) : PolyCoordRing K N d →ₐ[K] K :=
  MvPolynomial.aeval (polyCoords P)

/-- Affine Zariski closure of a subset of `HomogeneousPoly K N d`. -/
def affineZariskiClosure {K : Type*} [CommRing K] {N d : ℕ}
    (S : Set (HomogeneousPoly K N d)) : Set (HomogeneousPoly K N d) :=
  {P | ∀ F : PolyCoordRing K N d, (∀ Q ∈ S, evalAtPoly Q F = 0) → evalAtPoly P F = 0}

/-- Every subset is contained in its affine Zariski closure. -/
theorem subset_affineZariskiClosure {K : Type*} [CommRing K] {N d : ℕ}
    (S : Set (HomogeneousPoly K N d)) : S ⊆ affineZariskiClosure S :=
  fun _ hP _ hF => hF _ hP

/-- Linear change of variables `X i ↦ ∑ j, A i j • X j` on `MvPolynomial (Fin N) K`. -/
noncomputable def linearSubstMat {K : Type*} [CommRing K] {N : ℕ}
    (A : Matrix (Fin N) (Fin N) K) :
    MvPolynomial (Fin N) K →ₐ[K] MvPolynomial (Fin N) K :=
  MvPolynomial.aeval fun i => ∑ j : Fin N, MvPolynomial.C (A i j) * MvPolynomial.X j

/-- Evaluation of `linearSubstMat A P` at a vector `x` equals evaluation of `P` at `A *ᵥ x`. -/
theorem eval_linearSubstMat {K : Type*} [CommRing K] {N : ℕ}
    (A : Matrix (Fin N) (Fin N) K) (P : MvPolynomial (Fin N) K) (x : Fin N → K) :
    MvPolynomial.eval x (linearSubstMat A P) = MvPolynomial.eval (A *ᵥ x) P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [linearSubstMat]
  | add p q hp hq => simp [map_add, hp, hq]
  | mul_X p i hp =>
    rw [map_mul, map_mul, map_mul, hp]
    congr 1
    simp [linearSubstMat, Matrix.mulVec, dotProduct]

/-- Linear substitution preserves homogeneity of degree `d`. -/
theorem isHomogeneous_linearSubstMat {K : Type*} [CommRing K] {N d : ℕ}
    (A : Matrix (Fin N) (Fin N) K) {P : MvPolynomial (Fin N) K} (hP : P.IsHomogeneous d) :
    (linearSubstMat A P).IsHomogeneous d := by
  have hlin : ∀ i : Fin N,
      (∑ j : Fin N, MvPolynomial.C (A i j) * MvPolynomial.X j).IsHomogeneous 1 := fun i =>
    MvPolynomial.IsHomogeneous.sum _ _ _ fun j _ => by
      simpa [zero_add] using
        (MvPolynomial.isHomogeneous_C (Fin N) (A i j)).mul (MvPolynomial.isHomogeneous_X K j)
  simpa [linearSubstMat] using hP.aeval _ hlin

/-- Right endomorphism action `(u · P)(w) = P(u *ᵥ w)` on homogeneous polynomials. -/
noncomputable def endAction {K : Type*} [CommRing K] {N d : ℕ}
    (u : Matrix (Fin N) (Fin N) K) (P : HomogeneousPoly K N d) : HomogeneousPoly K N d :=
  ⟨linearSubstMat u P.1, isHomogeneous_linearSubstMat u P.2⟩

/-- Evaluation of `endAction u P` at `x` equals evaluation of `P` at `u *ᵥ x`. -/
theorem eval_endAction {K : Type*} [CommRing K] {N d : ℕ}
    (u : Matrix (Fin N) (Fin N) K) (P : HomogeneousPoly K N d) (x : Fin N → K) :
    MvPolynomial.eval x (endAction u P).1 = MvPolynomial.eval (u *ᵥ x) P.1 :=
  eval_linearSubstMat u P.1 x

/-- The generic `n × n` matrix of indeterminates indexed by `Fin (n * n)`. -/
noncomputable def genericMat (K : Type*) [CommRing K] (n : ℕ) :
    Matrix (Fin n) (Fin n) (MvPolynomial (Fin (n * n)) K) :=
  Matrix.of fun i j => MvPolynomial.X (finProdFinEquiv (i, j))

/-- The generic `n × n` determinant as a homogeneous polynomial of degree `n` in `n * n`
variables. -/
noncomputable def detPoly (K : Type*) [CommRing K] (n : ℕ) : HomogeneousPoly K (n * n) n :=
  ⟨(genericMat K n).det, by
    rw [Matrix.det_apply]
    refine MvPolynomial.IsHomogeneous.sum _ _ _ fun σ _ => ?_
    have hprod : (∏ i : Fin n, genericMat K n (σ i) i).IsHomogeneous n := by
      simpa using MvPolynomial.IsHomogeneous.prod Finset.univ
        (fun i => genericMat K n (σ i) i) (fun _ => 1)
        (fun i _ => MvPolynomial.isHomogeneous_X K (finProdFinEquiv (σ i, i)))
    have hsign : (Equiv.Perm.sign σ • ∏ i : Fin n, genericMat K n (σ i) i) =
        MvPolynomial.C ((Equiv.Perm.sign σ : ℤ) : K) * ∏ i : Fin n, genericMat K n (σ i) i := by
      rw [Units.smul_def, zsmul_eq_mul, map_intCast]
    rw [hsign]
    simpa [zero_add] using
      (MvPolynomial.isHomogeneous_C (Fin (n * n)) ((Equiv.Perm.sign σ : ℤ) : K)).mul hprod⟩

/-- Evaluation of `detPoly K n` on a matrix `M` recovers `M.det`. -/
theorem eval_detPoly {K : Type*} [CommRing K] (n : ℕ) (M : Matrix (Fin n) (Fin n) K) :
    MvPolynomial.eval
      (fun k => M (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2)
      (detPoly K n).1 = M.det := by
  change MvPolynomial.eval _ (genericMat K n).det = M.det
  rw [RingHom.map_det]
  congr 1; ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, genericMat, Matrix.of_apply,
    MvPolynomial.eval_X, Equiv.symm_apply_apply]

/-- The `GL_{n^2}(K)`-orbit of `detPoly K n`. -/
def detOrbit (K : Type*) [CommRing K] (n : ℕ) : Set (HomogeneousPoly K (n * n) n) :=
  {Q | ∃ g : GL (Fin (n * n)) K, Q = endAction g.1 (detPoly K n)}

/-- The `End(K^(n^2))`-orbit of `detPoly K n`. -/
def detEndOrbit (K : Type*) [CommRing K] (n : ℕ) : Set (HomogeneousPoly K (n * n) n) :=
  {Q | ∃ u : Matrix (Fin (n * n)) (Fin (n * n)) K, Q = endAction u (detPoly K n)}

/-- The affine Zariski closure of the `GL_{n^2}(K)`-orbit of `detPoly K n`. -/
def detOrbitClosure (K : Type*) [CommRing K] (n : ℕ) : Set (HomogeneousPoly K (n * n) n) :=
  affineZariskiClosure (detOrbit K n)

/-- Every `GL_{n^2}(K)`-orbit element belongs to `detEndOrbit K n`. -/
theorem detOrbit_subset_detEndOrbit (K : Type*) [CommRing K] (n : ℕ) :
    detOrbit K n ⊆ detEndOrbit K n := by
  rintro _ ⟨g, rfl⟩
  exact ⟨g.1, rfl⟩

/-- `Q` is a padded linear lift of `P` if `m ≤ n` and there exist a split linear inclusion
`f : K^M ↪ K^N` with retraction `π : K^N → K^M` and an independent padding linear form
`ℓ : K^N → K` (nontrivial whenever `m < n`) such that `Q(w) = ℓ(w)^(n - m) * P(π w)` for
all `w`. -/
def IsPaddedLift {K : Type*} [CommRing K] {M m N n : ℕ}
    (P : HomogeneousPoly K M m) (Q : HomogeneousPoly K N n) : Prop :=
  m ≤ n ∧
    ∃ (f : (Fin M → K) →ₗ[K] (Fin N → K)) (ℓ : (Fin N → K) →ₗ[K] K),
      Function.Injective f ∧
      (m < n → ℓ ≠ 0 ∧ ∀ x, ℓ (f x) = 0) ∧
      ∃ π : (Fin N → K) →ₗ[K] (Fin M → K),
        (∀ x, π (f x) = x) ∧
        (m < n → ∃ v₀, π v₀ = 0 ∧ ℓ v₀ = 1) ∧
        ∀ w, MvPolynomial.eval w Q.1 = (ℓ w) ^ (n - m) * MvPolynomial.eval (π w) P.1

/-- Reflexivity of `IsPaddedLift`. -/
theorem isPaddedLift_refl {K : Type*} [CommRing K] {M m : ℕ} (P : HomogeneousPoly K M m) :
    IsPaddedLift P P :=
  ⟨le_rfl, LinearMap.id, 0, Function.injective_id, fun h => absurd h (lt_irrefl _),
    LinearMap.id, fun _ => rfl, fun h => absurd h (lt_irrefl _), fun w => by simp⟩

/-- Set of sizes `n` such that `P` admits a padded lift in `detEndOrbit K n`. -/
def paddedDetComplexitySet {K : Type*} [CommRing K] {M m : ℕ}
    (P : HomogeneousPoly K M m) : Set ℕ :=
  {n | ∃ Q ∈ detEndOrbit K n, IsPaddedLift P Q}

/-- Set of sizes `n` such that `P` admits a padded lift in `detOrbitClosure K n`. -/
def borderDetComplexitySet {K : Type*} [CommRing K] {M m : ℕ}
    (P : HomogeneousPoly K M m) : Set ℕ :=
  {n | ∃ Q ∈ detOrbitClosure K n, IsPaddedLift P Q}

/-- Exact padded determinantal complexity of a homogeneous polynomial `P`, valued in `ℕ∞`. -/
noncomputable def paddedDetComplexity {K : Type*} [CommRing K] {M m : ℕ}
    (P : HomogeneousPoly K M m) : ℕ∞ :=
  ⨅ (n : ℕ) (_ : n ∈ paddedDetComplexitySet P), (n : ℕ∞)

/-- Border determinantal complexity of a homogeneous polynomial `P`, valued in `ℕ∞`. -/
noncomputable def borderDetComplexity {K : Type*} [CommRing K] {M m : ℕ}
    (P : HomogeneousPoly K M m) : ℕ∞ :=
  ⨅ (n : ℕ) (_ : n ∈ borderDetComplexitySet P), (n : ℕ∞)

/-- Over any infinite field `K`, every endomorphism translate of `detPoly K n` lies in the
affine Zariski closure of the `GL_{n^2}(K)`-orbit of `detPoly K n`. -/
theorem detEndOrbit_subset_detOrbitClosure {K : Type*} [Field K] [Infinite K] (n : ℕ) :
    detEndOrbit K n ⊆ detOrbitClosure K n := by
  classical
  rintro _ ⟨u, rfl⟩ F hF
  let uPoly : Matrix (Fin (n * n)) (Fin (n * n)) K[X] :=
    u.map (Polynomial.C : K →+* K[X]) +
      (Polynomial.X : K[X]) • (1 : Matrix (Fin (n * n)) (Fin (n * n)) K[X])
  have hdet_ne : uPoly.det ≠ 0 := by
    have hch : uPoly.det = (-u).charpoly := by
      rw [Matrix.charpoly, Matrix.charmatrix]
      congr 1; ext i j
      by_cases hij : i = j <;> simp [uPoly, Matrix.scalar_apply, hij]
      ring
    rw [hch]
    exact (Matrix.charpoly_monic (-u)).ne_zero
  let endPoly (t : K) : HomogeneousPoly K (n * n) n := endAction (u + t • 1) (detPoly K n)
  let p : K[X] := MvPolynomial.eval₂ (Polynomial.C : K →+* K[X])
    (fun α : MonomialIdx (n * n) n =>
      (MvPolynomial.aeval (fun i : Fin (n * n) =>
        ∑ j : Fin (n * n), MvPolynomial.C (uPoly i j) * MvPolynomial.X j)
        (MvPolynomial.map Polynomial.C (detPoly K n).1)).coeff α.1) F
  have hp_eval : ∀ t : K, p.eval t = evalAtPoly (endPoly t) F := by
    intro t
    have hcoeff : ∀ α : MonomialIdx (n * n) n,
        ((MvPolynomial.aeval (fun i : Fin (n * n) =>
          ∑ j : Fin (n * n), MvPolynomial.C (uPoly i j) * MvPolynomial.X j)
          (MvPolynomial.map Polynomial.C (detPoly K n).1)).coeff α.1).eval t =
        (endPoly t).1.coeff α.1 := fun α => by
      let ev : K[X] →+* K := Polynomial.evalRingHom t
      change ev _ = _
      rw [← MvPolynomial.coeff_map]
      have hmap : ∀ Q : MvPolynomial (Fin (n * n)) K,
          MvPolynomial.map ev
            (MvPolynomial.aeval (fun i : Fin (n * n) =>
              ∑ j : Fin (n * n), MvPolynomial.C (uPoly i j) * MvPolynomial.X j)
              (MvPolynomial.map Polynomial.C Q)) =
          linearSubstMat (u + t • 1) Q := by
        intro Q
        induction Q using MvPolynomial.induction_on with
        | C c => simp [linearSubstMat, ev]
        | add a b ha hb => simp [map_add, ha, hb]
        | mul_X a k ha =>
          rw [map_mul, map_mul, map_mul, map_mul, ha]
          congr 1
          simp only [MvPolynomial.map_X, MvPolynomial.aeval_X, map_sum, map_mul,
            MvPolynomial.map_C, linearSubstMat, uPoly, Matrix.add_apply, Matrix.map_apply,
            Matrix.smul_apply, Matrix.one_apply, ev, Polynomial.coe_evalRingHom,
            smul_eq_mul]
          refine Finset.sum_congr rfl fun j _ => by split_ifs <;> simp
      exact congrArg (fun q => q.coeff α.1) (hmap (detPoly K n).1)
    have hp_gen : ∀ G : PolyCoordRing K (n * n) n,
        (MvPolynomial.eval₂ (Polynomial.C : K →+* K[X])
          (fun α : MonomialIdx (n * n) n =>
            (MvPolynomial.aeval (fun i : Fin (n * n) =>
              ∑ j : Fin (n * n), MvPolynomial.C (uPoly i j) * MvPolynomial.X j)
              (MvPolynomial.map Polynomial.C (detPoly K n).1)).coeff α.1) G).eval t =
        evalAtPoly (endPoly t) G := by
      intro G
      induction G using MvPolynomial.induction_on with
      | C c => simp [evalAtPoly]
      | add a b ha hb =>
        rw [MvPolynomial.eval₂_add, Polynomial.eval_add, map_add, ha, hb]
      | mul_X a α ha =>
        rw [MvPolynomial.eval₂_mul, Polynomial.eval_mul, map_mul, ha, MvPolynomial.eval₂_X]
        congr 1
        simpa [evalAtPoly, polyCoords] using hcoeff α
    exact hp_gen F
  have hp0 : p = 0 := by
    apply Polynomial.eq_of_infinite_eval_eq
    refine Set.Infinite.mono (s := {t : K | uPoly.det.eval t ≠ 0}) ?_ ?_
    · intro t ht
      simp only [Set.mem_ofPred_eq, Polynomial.eval_zero]
      rw [hp_eval t]
      have hdet_t : (u + t • 1).det ≠ 0 := by
        have hev : uPoly.det.eval t = (u + t • 1).det := by
          change Polynomial.evalRingHom t uPoly.det = _
          rw [RingHom.map_det]
          congr 1; ext i j
          simp [uPoly, Matrix.one_apply]
          split_ifs <;> simp
        rwa [← hev]
      let g : GL (Fin (n * n)) K := Matrix.GeneralLinearGroup.mkOfDetNeZero (u + t • 1) hdet_t
      exact hF (endPoly t) ⟨g, rfl⟩
    · have hfin : {t : K | uPoly.det.eval t = 0}.Finite := by
        have hsub : {t : K | uPoly.det.eval t = 0} ⊆ (uPoly.det.roots.toFinset : Set K) := by
          intro t ht
          simp only [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots hdet_ne]
          exact ht
        exact (uPoly.det.roots.toFinset.finite_toSet).subset hsub
      have hcompl : {t : K | uPoly.det.eval t ≠ 0} = ({t : K | uPoly.det.eval t = 0})ᶜ := rfl
      rw [hcompl]
      simpa [Set.sdiff_eq_compl_inter] using Set.infinite_univ.sdiff hfin
  have h0 := congrArg (fun q : K[X] => q.eval 0) hp0
  rw [hp_eval 0, Polynomial.eval_zero] at h0
  simpa [endPoly] using h0

/-- Over any infinite field `K`, border determinantal complexity is at most exact padded
determinantal complexity. -/
theorem borderDetComplexity_le_paddedDetComplexity {K : Type*} [Field K] [Infinite K]
    {M m : ℕ} (P : HomogeneousPoly K M m) :
    borderDetComplexity P ≤ paddedDetComplexity P := by
  refine le_iInf₂ fun n hn => iInf₂_le n ?_
  rcases hn with ⟨Q, hQ, hlift⟩
  exact ⟨Q, detEndOrbit_subset_detOrbitClosure n hQ, hlift⟩

/-- The `n × n` determinant has padded determinantal complexity at most `n`. -/
theorem paddedDetComplexity_detPoly_le (K : Type*) [CommRing K] (n : ℕ) :
    paddedDetComplexity (detPoly K n) ≤ n :=
  iInf₂_le n ⟨detPoly K n, ⟨1, by
    apply Subtype.ext
    change (detPoly K n).1 =
      linearSubstMat (1 : Matrix (Fin (n * n)) (Fin (n * n)) K) (detPoly K n).1
    have hlin : linearSubstMat (1 : Matrix (Fin (n * n)) (Fin (n * n)) K) = AlgHom.id K _ := by
      ext i
      simp [linearSubstMat, Matrix.one_apply]
    rw [hlin, AlgHom.id_apply]⟩, isPaddedLift_refl _⟩

/-- Over any infinite field `K`, the `n × n` determinant has border determinantal complexity
at most `n`. -/
theorem borderDetComplexity_detPoly_le {K : Type*} [Field K] [Infinite K] (n : ℕ) :
    borderDetComplexity (detPoly K n) ≤ n :=
  (borderDetComplexity_le_paddedDetComplexity _).trans (paddedDetComplexity_detPoly_le K n)

/-- Over any infinite field `K`, every homogeneous polynomial admits a finite padded
determinantal representation. -/
theorem paddedDetComplexitySet_nonempty {K : Type*} [Field K] [Infinite K]
    {M m : ℕ} (P : HomogeneousPoly K M m) :
    (paddedDetComplexitySet P).Nonempty := by
  classical
  obtain ⟨r, A, hdeg, hdet⟩ :=
    Cslib.Circuits.Arithmetic.exists_hasDeterminantalRepresentation P.1
  let n : ℕ := max (max r (m + 1)) (M + 1)
  have hrn : r ≤ n := le_trans (le_max_left _ _) (le_max_left _ _)
  have hmn : m < n := by
    have : m + 1 ≤ n := le_trans (le_max_right _ _) (le_max_left _ _)
    omega
  have hMn : M + 1 ≤ n := le_max_right _ _
  have hn_le_nn : n ≤ n * n := Nat.le_mul_self n
  let f : (Fin M → K) →ₗ[K] (Fin (n * n) → K) :=
    { toFun := fun x k => if hk : k.1 < M then x ⟨k.1, hk⟩ else 0
      map_add' := fun x y => by ext k; simp only [Pi.add_apply]; split_ifs <;> simp
      map_smul' := fun c x => by
        ext k; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; split_ifs <;> simp }
  let π : (Fin (n * n) → K) →ₗ[K] (Fin M → K) :=
    { toFun := fun w i => w ⟨i.1, by omega⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let ℓ : (Fin (n * n) → K) →ₗ[K] K :=
    { toFun := fun w => w ⟨M, by omega⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hA_affine : ∀ (i j : Fin r) (x : Fin M → K),
      MvPolynomial.eval x (A i j) =
        (A i j).coeff 0 + ∑ k : Fin M, (A i j).coeff (Finsupp.single k 1) * x k := by
    intro i j x
    have hdeg1 := hdeg i j
    conv_lhs => rw [(A i j).as_sum, map_sum]
    have hsupp : (A i j).support ⊆
        insert 0 (Finset.univ.image (fun k : Fin M => Finsupp.single k 1)) := by
      intro s hs
      have hle : ∑ l ∈ s.support, s l ≤ 1 := (MvPolynomial.le_totalDegree hs).trans hdeg1
      by_cases hs0 : s = 0
      · subst hs0; exact Finset.mem_insert_self 0 _
      · refine Finset.mem_insert_of_mem ?_
        obtain ⟨k, hk⟩ := Finsupp.support_nonempty_iff.mpr hs0
        have hk1 : s k = 1 := by
          have hpos : 1 ≤ s k := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hk)
          have hle2 := Finset.single_le_sum (f := fun l => s l) (fun _ _ => Nat.zero_le _) hk
          omega
        refine Finset.mem_image.mpr ⟨k, Finset.mem_univ k, ?_⟩
        ext l
        by_cases hlk : l = k
        · subst hlk; simp [hk1]
        · rw [Finsupp.single_eq_of_ne hlk]
          symm
          by_contra hl0
          have hsub : ({k, l} : Finset (Fin M)) ⊆ s.support := by
            intro a ha; simp only [Finset.mem_insert, Finset.mem_singleton] at ha
            rcases ha with rfl | rfl
            · exact hk
            · exact Finsupp.mem_support_iff.mpr hl0
          have hle2 := Finset.sum_le_sum_of_subset_of_nonneg (f := fun a => s a)
            hsub (fun _ _ _ => Nat.zero_le _)
          rw [Finset.sum_pair (Ne.symm hlk)] at hle2
          have : 1 ≤ s l := Nat.pos_of_ne_zero hl0
          omega
    rw [Finset.sum_subset hsupp (fun s _ hnot => by
      simp [MvPolynomial.notMem_support_iff.mp hnot])]
    rw [Finset.sum_insert (by simp)]
    congr 1
    · simp
    · rw [Finset.sum_image (fun k₁ _ k₂ _ heq => by
        by_contra hne
        have := congrFun (congrArg DFunLike.coe heq) k₁
        rw [Finsupp.single_eq_same, Finsupp.single_eq_of_ne hne] at this
        exact one_ne_zero this)]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [MvPolynomial.eval_monomial]
      simp [Finsupp.prod_single_index]
  let L : (Fin (n * n) → K) →ₗ[K] (Fin (n * n) → K) :=
    { toFun := fun w idx =>
        let p := finProdFinEquiv.symm idx
        if hi : p.1.1 < r then
          if hj : p.2.1 < r then
            (A ⟨p.1.1, hi⟩ ⟨p.2.1, hj⟩).coeff 0 * ℓ w +
              ∑ k : Fin M, (A ⟨p.1.1, hi⟩ ⟨p.2.1, hj⟩).coeff (Finsupp.single k 1) * π w k
          else 0
        else if p.1 = p.2 then ℓ w else 0
      map_add' := fun w₁ w₂ => by
        ext idx
        simp only [Pi.add_apply]
        split_ifs
        · simp only [map_add, Pi.add_apply, mul_add, Finset.sum_add_distrib]
          ring
        · simp
        · simp [map_add]
        · simp
      map_smul' := fun c w => by
        ext idx
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        split_ifs
        · simp only [map_smul, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_add]
          congr 1
          · ring
          · refine Finset.sum_congr rfl fun k _ => by ring
        · simp
        · simp [map_smul, smul_eq_mul]
        · simp }
  let u : Matrix (Fin (n * n)) (Fin (n * n)) K := LinearMap.toMatrix' L
  let Q : HomogeneousPoly K (n * n) n := endAction u (detPoly K n)
  refine ⟨n, Q, ⟨u, rfl⟩, le_of_lt hmn, f, ℓ, ?_, ?_, π, ?_, ?_, ?_⟩
  · intro x y hxy; ext i
    simpa [f, i.2] using congrFun hxy ⟨i.1, by omega⟩
  · intro _
    refine ⟨fun h0 => ?_, fun x => by simp [ℓ, f]⟩
    have := congrFun (congrArg DFunLike.coe h0) (Pi.single ⟨M, by omega⟩ 1)
    simp [ℓ] at this
  · intro x; ext i; simp [π, f, i.2]
  · intro _
    refine ⟨Pi.single ⟨M, by omega⟩ 1, ?_, by simp [ℓ]⟩
    ext i
    simp only [π, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply]
    have hne : (⟨i.1, by omega⟩ : Fin (n * n)) ≠ ⟨M, by omega⟩ := fun h => by
      have := congrArg (Fin.val : Fin (n * n) → ℕ) h; simp at this; omega
    exact Pi.single_eq_of_ne hne _
  · intro w
    have hnz : ∀ w' : Fin (n * n) → K, ℓ w' ≠ 0 →
        MvPolynomial.eval w' Q.1 = (ℓ w') ^ (n - m) * MvPolynomial.eval (π w') P.1 := by
      intro w' hℓ'
      rw [eval_endAction, show u *ᵥ w' = L w' from LinearMap.toMatrix'_mulVec L w']
      have hev_det : MvPolynomial.eval (L w') (detPoly K n).1 =
          (Matrix.of fun i j : Fin n => L w' (finProdFinEquiv (i, j))).det := by
        change MvPolynomial.eval (L w') (genericMat K n).det = _
        rw [RingHom.map_det]
        congr 1; ext i j
        simp [RingHom.mapMatrix_apply, genericMat]
      rw [hev_det]
      let B : Matrix (Fin n) (Fin n) K := Matrix.of fun i j => L w' (finProdFinEquiv (i, j))
      let eSplit : Fin r ⊕ Fin (n - r) ≃ Fin n :=
        (finSumFinEquiv (m := r) (n := n - r)).trans (finCongr (Nat.add_sub_of_le hrn))
      have hB_block : B.submatrix eSplit eSplit =
          Matrix.fromBlocks
            (ℓ w' • (A.map (MvPolynomial.eval ((ℓ w')⁻¹ • π w'))))
            0 0
            (ℓ w' • (1 : Matrix (Fin (n - r)) (Fin (n - r)) K)) := by
        ext a b
        rcases a with i | i <;> rcases b with j | j
        · simp only [Matrix.submatrix_apply, B, Matrix.of_apply, L, LinearMap.coe_mk,
            AddHom.coe_mk, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₁, Matrix.smul_apply,
            Matrix.map_apply, smul_eq_mul, eSplit, Equiv.trans_apply, finSumFinEquiv_apply_left,
            finCongr_apply, Fin.val_cast, Fin.val_castAdd, i.2, j.2, ↓reduceDIte]
          rw [hA_affine i j ((ℓ w')⁻¹ • π w'), mul_add, Finset.mul_sum]
          congr 1
          · ring
          · refine Finset.sum_congr rfl fun k _ => ?_
            simp only [Pi.smul_apply, smul_eq_mul]
            field_simp [hℓ']
        · have hnotj : ¬ r + j.1 < r := by omega
          simp only [Matrix.submatrix_apply, B, Matrix.of_apply, L, LinearMap.coe_mk,
            AddHom.coe_mk, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₂, Matrix.zero_apply,
            eSplit, Equiv.trans_apply, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right,
            finCongr_apply, Fin.val_cast, Fin.val_castAdd, Fin.val_natAdd, i.2, hnotj, ↓reduceDIte]
        · have hnoti : ¬ r + i.1 < r := by omega
          simp only [Matrix.submatrix_apply, B, Matrix.of_apply, L, LinearMap.coe_mk,
            AddHom.coe_mk, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply,
            eSplit, Equiv.trans_apply, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right,
            finCongr_apply, Fin.val_cast, Fin.val_natAdd, hnoti, ↓reduceDIte]
          have hne' : (Fin.cast (Nat.add_sub_of_le hrn) (Fin.natAdd r i)) ≠
              (Fin.cast (Nat.add_sub_of_le hrn) (Fin.castAdd (n - r) j)) := fun h => by
            have := congrArg (Fin.val : Fin n → ℕ) h; simp at this; omega
          simp only [hne', ↓reduceIte]
        · have hnoti : ¬ r + i.1 < r := by omega
          simp only [Matrix.submatrix_apply, B, Matrix.of_apply, L, LinearMap.coe_mk,
            AddHom.coe_mk, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₂₂, Matrix.smul_apply,
            Matrix.one_apply, smul_eq_mul, eSplit, Equiv.trans_apply, finSumFinEquiv_apply_right,
            finCongr_apply, Fin.val_cast, Fin.val_natAdd, hnoti, ↓reduceDIte]
          by_cases hij : i = j
          · subst hij; simp
          · have hne' : (Fin.cast (Nat.add_sub_of_le hrn) (Fin.natAdd r i)) ≠
                (Fin.cast (Nat.add_sub_of_le hrn) (Fin.natAdd r j)) := fun h =>
              hij (Fin.ext (by have := congrArg (Fin.val : Fin n → ℕ) h; simp at this; omega))
            simp [hij, hne']
      have hdet_B : B.det = (B.submatrix eSplit eSplit).det :=
        (Matrix.det_reindex_self eSplit.symm B).symm
      rw [hdet_B, hB_block, Matrix.det_fromBlocks_zero₂₁, Matrix.det_smul, Matrix.det_smul,
        Matrix.det_one, mul_one, Fintype.card_fin, Fintype.card_fin]
      have hdet_A : (A.map (MvPolynomial.eval ((ℓ w')⁻¹ • π w'))).det =
          MvPolynomial.eval ((ℓ w')⁻¹ • π w') P.1 := by
        rw [← hdet, RingHom.map_det]; rfl
      rw [hdet_A, P.2.eval_smul, inv_pow]
      field_simp [hℓ']
      have h1 : (ℓ w') ^ r * (ℓ w') ^ (n - r) = (ℓ w') ^ n := by
        rw [← pow_add, Nat.add_sub_of_le hrn]
      have h2 : (ℓ w') ^ (n - m) * (ℓ w') ^ m = (ℓ w') ^ n := by
        rw [← pow_add, Nat.sub_add_cancel (le_of_lt hmn)]
      calc
        (ℓ w') ^ r * MvPolynomial.eval (π w') P.1 * (ℓ w') ^ (n - r)
            = ((ℓ w') ^ r * (ℓ w') ^ (n - r)) * MvPolynomial.eval (π w') P.1 := by ring
        _ = ((ℓ w') ^ (n - m) * (ℓ w') ^ m) * MvPolynomial.eval (π w') P.1 := by rw [h1, h2]
        _ = (ℓ w') ^ m * MvPolynomial.eval (π w') P.1 * (ℓ w') ^ (n - m) := by ring
    let v₀ : Fin (n * n) → K := Pi.single ⟨M, by omega⟩ 1
    let p₁ : K[X] := MvPolynomial.aeval
      (fun k => Polynomial.C (w k) + Polynomial.C (v₀ k) * Polynomial.X) Q.1
    let p₂ : K[X] := (Polynomial.C (ℓ w) + Polynomial.X) ^ (n - m) *
      Polynomial.C (MvPolynomial.eval (π w) P.1)
    have hp₁_eval : ∀ t : K, p₁.eval t = MvPolynomial.eval (t • v₀ + w) Q.1 := fun t => by
      simp only [p₁]
      induction Q.1 using MvPolynomial.induction_on with
      | C c => simp
      | add a b ha hb => simp [map_add, ha, hb]
      | mul_X a k ha =>
        simp only [map_mul, Polynomial.eval_mul, ha, MvPolynomial.aeval_X, Polynomial.eval_add,
          Polynomial.eval_C, Polynomial.eval_X, MvPolynomial.eval_X, Pi.add_apply, Pi.smul_apply,
          smul_eq_mul]
        ring
    have hEq : p₁ = p₂ := by
      apply Polynomial.eq_of_infinite_eval_eq
      refine Set.Infinite.mono (s := (Set.univ \ {-ℓ w} : Set K)) ?_
        (Set.infinite_univ.sdiff (Set.finite_singleton _))
      intro t ht
      have htne : t ≠ -ℓ w := by simpa using ht.2
      simp only [Set.mem_ofPred_eq]
      have hℓt : ℓ (t • v₀ + w) = t + ℓ w := by simp [ℓ, v₀]
      have hπt : π (t • v₀ + w) = π w := by
        ext i
        have hne : (⟨i.1, by omega⟩ : Fin (n * n)) ≠ ⟨M, by omega⟩ := fun h => by
          have := congrArg (Fin.val : Fin (n * n) → ℕ) h; simp at this; omega
        simp [π, v₀, Pi.single_eq_of_ne hne]
      have hℓ_ne : ℓ (t • v₀ + w) ≠ 0 := by
        rw [hℓt]; intro h0; exact htne (eq_neg_of_add_eq_zero_left h0)
      rw [hp₁_eval t, hnz _ hℓ_ne, hℓt, hπt]
      simp only [p₂, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add,
        Polynomial.eval_C, Polynomial.eval_X]
      ring
    have h0 := congrArg (fun q : K[X] => q.eval 0) hEq
    rw [hp₁_eval 0] at h0
    simpa [p₂] using h0

/-- Over any infinite field `K`, every homogeneous polynomial has finite padded determinantal
complexity. -/
theorem paddedDetComplexity_lt_top {K : Type*} [Field K] [Infinite K]
    {M m : ℕ} (P : HomogeneousPoly K M m) :
    paddedDetComplexity P < ⊤ := by
  obtain ⟨n, hn⟩ := paddedDetComplexitySet_nonempty P
  exact lt_of_le_of_lt (iInf₂_le n hn) (WithTop.coe_lt_top n)

/-- Over any infinite field `K`, every homogeneous polynomial has finite border determinantal
complexity. -/
theorem borderDetComplexity_lt_top {K : Type*} [Field K] [Infinite K]
    {M m : ℕ} (P : HomogeneousPoly K M m) :
    borderDetComplexity P < ⊤ :=
  lt_of_le_of_lt (borderDetComplexity_le_paddedDetComplexity P) (paddedDetComplexity_lt_top P)

end CslibFrontier.Computability.Circuit.Arithmetic

end
