module

public import CslibFrontier.Computability.Machines.Turing.MultiTape.PolyTime
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Unary
public import CslibFrontier.Computability.Complexity.Problems.LinearProgramming.EllipsoidUpdate
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.NatLength
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeLoops
import CslibFrontier.Foundations.Data.List.Blocks
import CslibFrontier.Foundations.Data.List.DotProduct
import CslibFrontier.Foundations.Data.List.GetD
import Mathlib.Data.List.GetD

/-!
# Fixed-Precision Dyadic Rounding of Khachiyan's Ellipsoid Step

This module formalizes bounded binary-search integer square roots and a single fixed-precision
dyadic rounded step of Khachiyan's ellipsoid method
, proved strictly under standard Lean axioms.

Representing an ellipsoid center `c = 2 ^ (-p) • cVec` and symmetric shape matrix
`E = 2 ^ (-p) • mMat` by integer lists at a uniform grid scale `2 ^ (-p)`, the rounded update
computes the integer square root of `2 ^ (3 * p) * (aᵀ mMat a)` by binary search, rounds the
inflated rank-one shape update `(1 + (16 * n ^ 3)⁻¹) • exactEllipsoidMatrix E a` by floor division,
and adds `(n + 1) * 2 ^ (-p) • 1` on the diagonal to preserve half-ellipsoid containment,
two-sided spectral bounds, and determinant contraction `≤ exp (-1 / (12 * n ^ 2))`.

## Main definitions

* `CslibFrontier.Complexity.LinearProgramming.isqrtBounded`: bounded binary-search integer square
  root.
* `CslibFrontier.Complexity.LinearProgramming.dyadicListToVec`,
  `CslibFrontier.Complexity.LinearProgramming.dyadicListToMat`: real vector and
  matrix interpretations of integer lists at dyadic scale `2 ^ (-p)`.
* `CslibFrontier.Complexity.LinearProgramming.dyadicEllipsoidCenterUpdate`,
    `CslibFrontier.Complexity.LinearProgramming.dyadicEllipsoidMatUpdate`: fixed-precision integer
  updates for the center
  and shape matrix of a rounded Khachiyan half-ellipsoid step.

## Main results

* `CslibFrontier.Complexity.LinearProgramming.isqrtBounded_eq_sqrt`,
    `CslibFrontier.Complexity.LinearProgramming.computableInPolyTime_isqrtBounded`: correctness and
  multi-tape Turing
  machine polynomial-time computability of bounded binary-search integer square root.
* `CslibFrontier.Complexity.LinearProgramming.dyadicEllipsoidStep_spec`: spectral invariants,
  entrywise magnitude bounds,
  multiplicative determinant contraction, and half-ellipsoid containment for one rounded step.
-/

public section

open Matrix Turing.MultiTapeTM ComputableInPolyTime
open scoped BigOperators

namespace CslibFrontier.Complexity.LinearProgramming

/-! ### Bounded binary-search integer square root -/

private def isqrtStep (x : ℕ) (st : ℕ × ℕ) : ℕ × ℕ :=
  let mid := (st.1 + st.2) / 2
  if mid * mid ≤ x then (mid, st.2) else (st.1, mid)

/-- Compute `Nat.sqrt x` in `k` binary-search halving steps for any input with `x < 4 ^ k`. -/
def isqrtBounded (k x : ℕ) : ℕ :=
  ((isqrtStep x)^[k] (0, ((2 : ℤ) ^ k).toNat)).1

private theorem toNat_two_pow (k : ℕ) : ((2 : ℤ) ^ k).toNat = 2 ^ k := by
  have h : ((2 : ℤ) ^ k) = ((2 ^ k : ℕ) : ℤ) := by push_cast; rfl
  rw [h, Int.toNat_natCast]

private theorem isqrtStep_invariant {k x : ℕ} (hx : x < 4 ^ k) :
    ∀ t ≤ k,
      let st := (isqrtStep x)^[t] (0, 2 ^ k)
      st.2 = st.1 + 2 ^ (k - t) ∧ st.1 * st.1 ≤ x ∧ x < st.2 * st.2 := by
  intro t ht
  induction t with
  | zero =>
    have h4 : 2 ^ k * 2 ^ k = 4 ^ k := by rw [← mul_pow]; rfl
    exact ⟨by simp, by simp, lt_of_lt_of_eq hx h4.symm⟩
  | succ t ih =>
    obtain ⟨hdiff, hlo, hhi⟩ := ih (by omega)
    simp only [Function.iterate_succ_apply']
    set st := (isqrtStep x)^[t] (0, 2 ^ k)
    have hpow : 2 ^ (k - t) = 2 * 2 ^ (k - (t + 1)) := by
      rw [show k - t = (k - (t + 1)) + 1 by omega, pow_succ']
    have hmid : (st.1 + st.2) / 2 = st.1 + 2 ^ (k - (t + 1)) := by omega
    dsimp [isqrtStep]
    rw [hmid]
    split_ifs with hle
    · exact ⟨by omega, hle, hhi⟩
    · exact ⟨rfl, hlo, not_le.mp hle⟩

/-- `isqrtBounded k x` equals `Nat.sqrt x` whenever `x < 4 ^ k`. -/
theorem isqrtBounded_eq_sqrt {k x : ℕ} (hx : x < 4 ^ k) :
    isqrtBounded k x = Nat.sqrt x := by
  dsimp [isqrtBounded]
  rw [toNat_two_pow]
  obtain ⟨hdiff, hlo, hhi⟩ := isqrtStep_invariant hx k le_rfl
  simp only [Nat.sub_self, pow_zero] at hdiff
  rw [hdiff] at hhi
  exact Nat.eq_sqrt.mpr ⟨hlo, hhi⟩

/-- `isqrtBounded` runs in deterministic polynomial time on a multi-tape Turing machine when `k` is
encoded in unary and `x` is encoded in binary. -/
theorem computableInPolyTime_isqrtBounded {α : Type} {encIn : α ↪ List Bool}
    {k x : α → ℕ} (hk : ComputableInPolyTime k encIn encUnary)
    (hx : ComputableInPolyTime x encIn encNat) :
    ComputableInPolyTime (fun a => isqrtBounded (k a) (x a)) encIn encNat := by
  have hinit : ComputableInPolyTime (fun a => (0, ((2 : ℤ) ^ k a).toNat))
      encIn (encPair encNat encNat) :=
    (const 0).prod (intBin_toNat.comp (intBin_pow' (const 2) hk))
  have hstep : ComputableInPolyTime (fun p : ℕ × (ℕ × ℕ) => isqrtStep p.1 p.2)
      (encPair encNat (encPair encNat encNat)) (encPair encNat encNat) := by
    have hmid : ComputableInPolyTime (fun p : ℕ × (ℕ × ℕ) => (p.2.1 + p.2.2) / 2)
        (encPair encNat (encPair encNat encNat)) encNat :=
      binary_div' (binary_add' (by fun_prop) (by fun_prop)) (const 2)
    have hcond : ComputableInPolyTime
        (fun p : ℕ × (ℕ × ℕ) => decide (p.1 < ((p.2.1 + p.2.2) / 2) * ((p.2.1 + p.2.2) / 2)))
        (encPair encNat (encPair encNat encNat)) encBool :=
      binary_lt' (by fun_prop) (binary_mul' hmid hmid)
    have heq : (fun p : ℕ × (ℕ × ℕ) => isqrtStep p.1 p.2) = fun p =>
        if decide (p.1 < ((p.2.1 + p.2.2) / 2) * ((p.2.1 + p.2.2) / 2)) then
          (p.2.1, (p.2.1 + p.2.2) / 2)
        else
          ((p.2.1 + p.2.2) / 2, p.2.2) := by
      funext p; dsimp [isqrtStep]
      by_cases h : ((p.2.1 + p.2.2) / 2) * ((p.2.1 + p.2.2) / 2) ≤ p.1
      · simp [h, not_lt.mpr h]
      · simp [h, lt_of_not_ge h]
    rw [heq]
    exact ite hcond ((by fun_prop : ComputableInPolyTime _ _ encNat).prod hmid)
      (hmid.prod (by fun_prop))
  have hpoly : PolyBounded (fun a => (encIn a).length) (fun a => 4 * (k a + 2)) :=
    (PolyBounded.const 4).mul (hk.polyBounded.add (PolyBounded.const 2))
  have hloop := (iterateWith_spec hx hk hinit hstep
    (fun a _ st => st.1 ≤ 2 ^ k a ∧ st.2 ≤ 2 ^ k a)
    (fun a => by simp [toNat_two_pow])
    (fun a _ st _ ⟨h1, h2⟩ => by dsimp [isqrtStep]; split_ifs <;> exact ⟨by omega, by omega⟩)
    hpoly
    (fun a _ st _ ⟨h1, h2⟩ => by
      have hpos : 1 ≤ 2 ^ k a := Nat.one_le_two_pow
      have hl1 : (encNat st.1).length ≤ k a + 1 :=
        length_encNat_le_of_lt_two_pow (by rw [pow_succ]; omega)
      have hl2 : (encNat st.2).length ≤ k a + 1 :=
        length_encNat_le_of_lt_two_pow (by rw [pow_succ]; omega)
      rw [length_encPair]; omega)).1
  exact (fst encNat encNat).comp hloop

/-! ### Fixed-precision dyadic representation and rounded ellipsoid step -/

/-- Interpret an integer list `v` as a vector in `Fin n → ℝ` at dyadic scale `2 ^ (-p)`. -/
noncomputable def dyadicListToVec (n p : ℕ) (v : List ℤ) : Fin n → ℝ :=
  fun i => ((v.getD i.1 0 : ℤ) : ℝ) / (2 : ℝ) ^ p

/-- Coordinate formula for `dyadicListToVec`. -/
@[simp] theorem dyadicListToVec_apply (n p : ℕ) (v : List ℤ) (i : Fin n) :
    dyadicListToVec n p v i = ((v.getD i.1 0 : ℤ) : ℝ) / (2 : ℝ) ^ p := by
  rfl

/-- Interpret a nested integer list `M` as an `n × n` real matrix at dyadic scale `2 ^ (-p)`. -/
noncomputable def dyadicListToMat (n p : ℕ) (M : List (List ℤ)) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => (((M.getD i.1 []).getD j.1 0 : ℤ) : ℝ) / (2 : ℝ) ^ p

/-- Entry formula for `dyadicListToMat`. -/
@[simp] theorem dyadicListToMat_apply (n p : ℕ) (M : List (List ℤ)) (i j : Fin n) :
    dyadicListToMat n p M i j = (((M.getD i.1 []).getD j.1 0 : ℤ) : ℝ) / (2 : ℝ) ^ p := by
  rfl

/-- Fixed-precision integer update of the ellipsoid shape matrix `M = 2 ^ p • E` along `bVec = M a`
with quadratic value `S = a ⬝ᵥ bVec`. -/
@[expose] def dyadicEllipsoidMatUpdate (n : ℕ) (S : ℤ) (bVec : List ℤ) (mMat : List (List ℤ)) :
    List (List ℤ) :=
  let nZ : ℤ := n
  let numFac : ℤ := (16 * nZ * nZ * nZ + 1) * (nZ * nZ)
  let den : ℤ := 16 * nZ * nZ * nZ * (nZ * nZ - 1) * (nZ + 1) * S
  (List.range n).map fun i =>
    let rowI := mMat.getD i []
    let bi := bVec.getD i 0
    (List.range n).map fun j =>
      let mij := rowI.getD j 0
      let bj := bVec.getD j 0
      let num := numFac * ((nZ + 1) * S * mij - 2 * bi * bj)
      num.ediv den + (if decide (i = j) then nZ + 1 else 0)

/-- Fixed-precision integer update of the ellipsoid center `cVec = 2 ^ p • c` along `bVec = M a`
with `scale2 = 2 ^ (2 * p)`, `scale3 = 2 ^ (3 * p)`, and `S = a ⬝ᵥ bVec`. -/
@[expose] def dyadicEllipsoidCenterUpdate (n kSqrt : ℕ) (scale2 scale3 S : ℤ)
    (cVec bVec : List ℤ) : List ℤ :=
  let q := isqrtBounded kSqrt (scale3 * S).toNat
  let denC : ℤ := ((n + 1 : ℕ) : ℤ) * ((q + 1 : ℕ) : ℤ)
  (List.range n).map fun i => cVec.getD i 0 - (scale2 * bVec.getD i 0).ediv denC

private theorem getD_map_range {α : Type*} (n : ℕ) (f : ℕ → α) (d : α) {i : ℕ} (hi : i < n) :
    ((List.range n).map f).getD i d = f i := by
  have hlen : i < ((List.range n).map f).length := by simp [hi]
  rw [List.getD_eq_getElem _ d hlen, List.getElem_map, List.getElem_range]

private theorem int_ediv_real_bounds (x : ℤ) {d : ℤ} (hd : 0 < d) :
    ((x.ediv d : ℤ) : ℝ) ≤ (x : ℝ) / (d : ℝ) ∧
      (x : ℝ) / (d : ℝ) < ((x.ediv d : ℤ) : ℝ) + 1 := by
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hdivR : (d : ℝ) * ((x.ediv d : ℤ) : ℝ) + ((x.emod d : ℤ) : ℝ) = (x : ℝ) :=
    by exact_mod_cast Int.mul_ediv_add_emod x d
  have h0R : (0 : ℝ) ≤ ((x.emod d : ℤ) : ℝ) := by exact_mod_cast Int.emod_nonneg x hd.ne'
  have hltR : ((x.emod d : ℤ) : ℝ) < (d : ℝ) := by exact_mod_cast Int.emod_lt_of_pos x hd
  exact ⟨(le_div_iff₀ hdR).mpr (by linarith), (div_lt_iff₀ hdR).mpr (by linarith)⟩

private theorem nat_le_two_pow (k : ℕ) : k ≤ 2 ^ k := by
  induction k with
  | zero => simp
  | succ k ih => have : 1 ≤ 2 ^ k := Nat.one_le_two_pow; rw [pow_succ]; omega

private theorem dyadicMatUpdate_spec {n p N ρ k : ℕ} (hn : 2 ≤ n) (hk : k < N)
    (hp : p = 3 * N + 8 * n + 16) {mMat : List (List ℤ)}
    (hE_pos : (dyadicListToMat n p mMat).PosDef)
    (hE_low : ∀ v, (2 : ℝ) ^ (2 * ρ) / (4 : ℝ) ^ k * (v ⬝ᵥ v) ≤
      v ⬝ᵥ (dyadicListToMat n p mMat *ᵥ v))
    (hE_hi : ∀ v, v ⬝ᵥ (dyadicListToMat n p mMat *ᵥ v) ≤ (2 : ℝ) ^ (k + 2 * ρ) * (v ⬝ᵥ v))
    {a : Fin n → ℝ} (ha_ne : a ≠ 0) {bVec : List ℤ}
    (hbVec : ∀ i : Fin n, ((bVec.getD i.1 0 : ℤ) : ℝ) =
      (2 : ℝ) ^ p * (dyadicListToMat n p mMat *ᵥ a) i)
    {S : ℤ} (hS_pos : 0 < S)
    (hS_real : (S : ℝ) = (2 : ℝ) ^ p * (a ⬝ᵥ (dyadicListToMat n p mMat *ᵥ a))) :
    let mNext := dyadicEllipsoidMatUpdate n S bVec mMat
    let E := dyadicListToMat n p mMat
    let E' := dyadicListToMat n p mNext
    let ξ : ℝ := 1 + 1 / (16 * (n : ℝ) ^ 3)
    mNext.length = n ∧ (∀ r ∈ mNext, r.length = n) ∧ E'.PosDef ∧
      (∀ v, v ⬝ᵥ ((ξ • exactEllipsoidMatrix E a) *ᵥ v) ≤ v ⬝ᵥ (E' *ᵥ v)) ∧
      (∀ v, (2 : ℝ) ^ (2 * ρ) / (4 : ℝ) ^ (k + 1) * (v ⬝ᵥ v) ≤ v ⬝ᵥ (E' *ᵥ v)) ∧
      (∀ v, v ⬝ᵥ (E' *ᵥ v) ≤ (2 : ℝ) ^ (k + 1 + 2 * ρ) * (v ⬝ᵥ v)) ∧
      (∀ r ∈ mNext, ∀ z ∈ r, |z| ≤ (2 : ℤ) ^ (p + (k + 1) + 2 * ρ)) ∧
      E'.det ≤ Real.exp (-1 / (12 * (n : ℝ) ^ 2)) * E.det := by
  intro mNext E E' ξ
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn3_ge : (8 : ℝ) ≤ (n : ℝ) ^ 3 :=
    (show (8 : ℝ) = 2 ^ 3 by norm_num) ▸ pow_le_pow_left₀ zero_le_two hn2 3
  set lamK : ℝ := (2 : ℝ) ^ (2 * ρ) / (4 : ℝ) ^ k
  set Λk : ℝ := (2 : ℝ) ^ (k + 2 * ρ)
  have hlamK_pos : 0 < lamK := by positivity
  have hlamK_ge : (1 : ℝ) / (2 : ℝ) ^ (2 * N) ≤ lamK := by
    dsimp [lamK]
    have h4 : (4 : ℝ) ^ k ≤ (2 : ℝ) ^ (2 * N) := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul]
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    exact (div_le_div_of_nonneg_left zero_le_one (by positivity) h4).trans
      (div_le_div_of_nonneg_right (one_le_pow₀ (by norm_num)) (by positivity))
  set σ : ℝ := a ⬝ᵥ (E *ᵥ a)
  have hσ_pos : 0 < σ := hE_pos.dotProduct_mulVec_pos ha_ne
  set F := exactEllipsoidMatrix E a
  have hF_pos : F.PosDef := exactEllipsoidMatrix_posDef hn hE_pos ha_ne
  have hξ_pos : 0 < ξ := by positivity
  set Etilde : Matrix (Fin n) (Fin n) ℝ := ξ • F
  set Δ : Matrix (Fin n) (Fin n) ℝ := E' - (Etilde + ((n + 1 : ℝ) / (2 : ℝ) ^ p) • 1)
  let nZ : ℤ := (n : ℤ)
  let numFac : ℤ := (16 * nZ * nZ * nZ + 1) * (nZ * nZ)
  let den : ℤ := 16 * nZ * nZ * nZ * (nZ * nZ - 1) * (nZ + 1) * S
  have hget_mNext : ∀ u v : Fin n, (mNext.getD u.1 []).getD v.1 0 =
      (numFac * ((nZ + 1) * S * (mMat.getD u.1 []).getD v.1 0 -
        2 * bVec.getD u.1 0 * bVec.getD v.1 0)).ediv den +
        (if decide (u.1 = v.1) then nZ + 1 else 0) := by
    intro u v
    dsimp only [mNext, dyadicEllipsoidMatUpdate]
    rw [getD_map_range n _ [] u.2, getD_map_range n _ 0 v.2]
  have hΔ_abs : ∀ i j : Fin n, |Δ i j| ≤ 1 / (2 : ℝ) ^ p := by
    intro i j
    have hnZ : (2 : ℤ) ≤ nZ := Int.ofNat_le.mpr hn
    have h1 : 0 < 16 * nZ * nZ * nZ :=
      mul_pos (mul_pos (mul_pos (by decide) (by omega)) (by omega)) (by omega)
    have hden_pos : 0 < den := mul_pos (mul_pos (mul_pos h1 (by nlinarith)) (by omega)) hS_pos
    set mij := (mMat.getD i.1 []).getD j.1 0
    set bi := bVec.getD i.1 0
    set bj := bVec.getD j.1 0
    set num : ℤ := numFac * ((nZ + 1) * S * mij - 2 * bi * bj)
    have hE'ij : E' i j = ((num.ediv den : ℤ) : ℝ) / (2 : ℝ) ^ p +
        (if i = j then ((n : ℝ) + 1) / (2 : ℝ) ^ p else 0) := by
      simp only [E', dyadicListToMat_apply, hget_mNext i j, Fin.ext_iff]
      by_cases hij : i.1 = j.1 <;> simp [hij, num, nZ, add_div, mij, bi, bj]
    have hEtij : Etilde i j = ((num : ℝ) / (den : ℝ)) / (2 : ℝ) ^ p := by
      have hmij : (mij : ℝ) = (2 : ℝ) ^ p * E i j := by
        dsimp [mij, E]; rw [dyadicListToMat_apply]; field_simp
      simp only [Etilde, ξ, Matrix.smul_apply, smul_eq_mul, F, exactEllipsoidMatrix_apply,
        num, numFac, den, nZ]
      push_cast
      rw [hmij, hbVec i, hbVec j, hS_real]
      have hp0 : (2 : ℝ) ^ p ≠ 0 := by positivity
      have hσ0 : σ ≠ 0 := hσ_pos.ne'
      have hn0 : (n : ℝ) ≠ 0 := by linarith
      have hn21 : (n : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
      have hnp : (n : ℝ) + 1 ≠ 0 := by linarith
      have hσeq : a ⬝ᵥ (E *ᵥ a) = σ := rfl
      rw [hσeq]; field_simp; ring
    have hΔij : Δ i j = (((num.ediv den : ℤ) : ℝ) - (num : ℝ) / (den : ℝ)) / (2 : ℝ) ^ p := by
      simp only [Δ, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
        smul_eq_mul, hE'ij, hEtij]
      by_cases hij : i = j <;> simp [hij, sub_div]
    obtain ⟨hb1, hb2⟩ := int_ediv_real_bounds num hden_pos
    rw [hΔij, abs_div, abs_of_pos (by positivity : (0 : ℝ) < (2 : ℝ) ^ p)]
    exact div_le_div_of_nonneg_right (abs_le.mpr ⟨by linarith, by linarith⟩) (by positivity)
  have hE'_symm : E'.IsHermitian := by
    have hET : Eᵀ = E := by simpa [Matrix.IsHermitian] using hE_pos.isHermitian
    have hm_sym : ∀ i j : Fin n,
        (mMat.getD i.1 []).getD j.1 0 = (mMat.getD j.1 []).getD i.1 0 := fun i j => by
      have hEij : E i j = E j i := congrFun (congrFun hET j) i
      simp only [E, dyadicListToMat_apply] at hEij
      exact Int.cast_injective ((div_left_inj₀ (by positivity : (2 : ℝ) ^ p ≠ 0)).mp hEij)
    change E'ᵀ = E'
    ext i j
    simp only [Matrix.transpose_apply, E', dyadicListToMat_apply, hget_mNext j i, hget_mNext i j]
    congr 2
    rw [hm_sym j i,
      show 2 * bVec.getD j.1 0 * bVec.getD i.1 0 = 2 * bVec.getD i.1 0 * bVec.getD j.1 0 by ring,
      show decide (j.1 = i.1) = decide (i.1 = j.1) by simp [eq_comm]]
  have hE'_quad : ∀ v : Fin n → ℝ,
      v ⬝ᵥ (Etilde *ᵥ v) ≤ v ⬝ᵥ (E' *ᵥ v) ∧
        v ⬝ᵥ (E' *ᵥ v) ≤ v ⬝ᵥ (Etilde *ᵥ v) + ((2 * (n : ℝ) + 1) / (2 : ℝ) ^ p) * (v ⬝ᵥ v) := by
    intro v
    have hv0 : 0 ≤ v ⬝ᵥ v := Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)
    have hpert := abs_le.mp (symm_quad_perturbation_le Δ (by positivity) hΔ_abs v)
    have hexp : v ⬝ᵥ (E' *ᵥ v) =
        v ⬝ᵥ (Etilde *ᵥ v) + ((n + 1 : ℝ) / (2 : ℝ) ^ p) * (v ⬝ᵥ v) + v ⬝ᵥ (Δ *ᵥ v) := by
      have hrel : E' = Etilde + ((n + 1 : ℝ) / (2 : ℝ) ^ p) • 1 + Δ := by simp [Δ]
      conv_lhs => rw [hrel]
      simp [Matrix.add_mulVec, Matrix.smul_mulVec, dotProduct_add, dotProduct_smul]
    have hsub1 : (n : ℝ) * (1 / (2 : ℝ) ^ p) * (v ⬝ᵥ v) ≤
        ((n + 1 : ℝ) / (2 : ℝ) ^ p) * (v ⬝ᵥ v) :=
      mul_le_mul_of_nonneg_right
        (by rw [mul_one_div]; exact div_le_div_of_nonneg_right (by linarith) (by positivity)) hv0
    have hadd1 : ((n + 1 : ℝ) / (2 : ℝ) ^ p) * (v ⬝ᵥ v) +
        (n : ℝ) * (1 / (2 : ℝ) ^ p) * (v ⬝ᵥ v) =
        ((2 * (n : ℝ) + 1) / (2 : ℝ) ^ p) * (v ⬝ᵥ v) := by ring
    exact ⟨by linarith, by linarith⟩
  have hF_low : ∀ v : Fin n → ℝ, (lamK / 4) * (v ⬝ᵥ v) ≤ v ⬝ᵥ (F *ᵥ v) := fun v => by
    have hfac : (1 / 4 : ℝ) ≤ (n : ℝ) ^ 2 / ((n : ℝ) + 1) ^ 2 := by
      rw [div_le_div_iff₀ (by norm_num) (by positivity)]; nlinarith
    calc (lamK / 4) * (v ⬝ᵥ v) = (1 / 4 : ℝ) * (lamK * (v ⬝ᵥ v)) := by ring
      _ ≤ ((n : ℝ) ^ 2 / ((n : ℝ) + 1) ^ 2) * (v ⬝ᵥ (E *ᵥ v)) :=
          mul_le_mul hfac (hE_low v)
            (mul_nonneg hlamK_pos.le (Finset.sum_nonneg fun _ _ => mul_self_nonneg _))
            (by positivity)
      _ ≤ v ⬝ᵥ (F *ᵥ v) := (exactEllipsoidMatrix_quad_bounds hn hE_pos ha_ne v).1
  have hE'_low : ∀ v, (2 : ℝ) ^ (2 * ρ) / (4 : ℝ) ^ (k + 1) * (v ⬝ᵥ v) ≤ v ⬝ᵥ (E' *ᵥ v) := by
    intro v
    rw [show (2 : ℝ) ^ (2 * ρ) / (4 : ℝ) ^ (k + 1) = lamK / 4 by dsimp [lamK]; rw [pow_succ]; ring]
    have hFv : 0 ≤ v ⬝ᵥ (F *ᵥ v) :=
      (mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => mul_self_nonneg _)).trans (hF_low v)
    have hEt : v ⬝ᵥ (F *ᵥ v) ≤ v ⬝ᵥ (Etilde *ᵥ v) := by
      simp only [Etilde, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
      have h1 : (1 : ℝ) ≤ ξ := by
        dsimp [ξ]; linarith [show 0 < 1 / (16 * (n : ℝ) ^ 3) by positivity]
      nlinarith
    exact (hF_low v).trans (hEt.trans (hE'_quad v).1)
  have hE'_pos : E'.PosDef := posDef_of_quad_lower hE'_symm (by positivity) hE'_low
  have hround_small : (2 * (n : ℝ) + 1) / (2 : ℝ) ^ p ≤ (1 / (16 * (n : ℝ) ^ 3)) * (lamK / 4) := by
    have h1 : (1 : ℝ) / (2 : ℝ) ^ (2 * N + 2) ≤ lamK / 4 := by
      rw [show (1 : ℝ) / (2 : ℝ) ^ (2 * N + 2) = (1 / (2 : ℝ) ^ (2 * N)) / 4 by
        rw [pow_add]; norm_num; ring]
      exact div_le_div_of_nonneg_right hlamK_ge (by norm_num)
    refine le_trans ?_ (mul_le_mul_of_nonneg_left h1 (by positivity))
    rw [one_div_mul_one_div, div_le_div_iff₀ (by positivity) (by positivity), one_mul]
    have hn4 : (n : ℝ) ^ 4 ≤ ((2 : ℝ) ^ n) ^ 4 :=
      pow_le_pow_left₀ (by positivity) (by exact_mod_cast nat_le_two_pow n) 4
    have hpoly : (2 * (n : ℝ) + 1) * (16 * (n : ℝ) ^ 3) ≤ (2 : ℝ) ^ (4 * n + 6) := by
      calc (2 * (n : ℝ) + 1) * (16 * (n : ℝ) ^ 3)
          ≤ (4 * (n : ℝ)) * (16 * (n : ℝ) ^ 3) :=
            mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        _ = 64 * (n : ℝ) ^ 4 := by ring
        _ ≤ 64 * ((2 : ℝ) ^ n) ^ 4 := by linarith
        _ = (2 : ℝ) ^ (4 * n + 6) := by rw [← pow_mul, pow_add, mul_comm n 4]; norm_num; ring
    calc (2 * (n : ℝ) + 1) * (16 * (n : ℝ) ^ 3 * (2 : ℝ) ^ (2 * N + 2))
        ≤ (2 : ℝ) ^ (4 * n + 6) * (2 : ℝ) ^ (2 * N + 2) := by
          rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hpoly (by positivity)
      _ = (2 : ℝ) ^ (2 * N + 4 * n + 8) := by rw [← pow_add]; congr 1; omega
      _ ≤ (2 : ℝ) ^ p := pow_le_pow_right₀ (by norm_num) (by omega)
  have hE'_le_xi2F : ∀ v : Fin n → ℝ, v ⬝ᵥ (E' *ᵥ v) ≤ v ⬝ᵥ ((ξ ^ 2 • F) *ᵥ v) := fun v => by
    have hv0 : 0 ≤ v ⬝ᵥ v := Finset.sum_nonneg fun _ _ => mul_self_nonneg _
    have h1 := (hE'_quad v).2
    have h2 : ((2 * (n : ℝ) + 1) / (2 : ℝ) ^ p) * (v ⬝ᵥ v) ≤
        (1 / (16 * (n : ℝ) ^ 3)) * (v ⬝ᵥ (F *ᵥ v)) :=
      (mul_le_mul_of_nonneg_right hround_small hv0).trans
        (by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (hF_low v) (by positivity))
    have hFv : 0 ≤ v ⬝ᵥ (F *ᵥ v) := (mul_nonneg (by positivity) hv0).trans (hF_low v)
    simp only [Etilde, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul] at h1 ⊢
    have hxi2 : ξ + 1 / (16 * (n : ℝ) ^ 3) ≤ ξ ^ 2 := by
      dsimp [ξ]; nlinarith [show 0 < 1 / (16 * (n : ℝ) ^ 3) by positivity]
    nlinarith
  have hE'_hi : ∀ v, v ⬝ᵥ (E' *ᵥ v) ≤ (2 : ℝ) ^ (k + 1 + 2 * ρ) * (v ⬝ᵥ v) := fun v => by
    have hv0 : 0 ≤ v ⬝ᵥ v := Finset.sum_nonneg fun _ _ => mul_self_nonneg _
    have hxi_le : ξ ≤ 9 / 8 := by
      dsimp [ξ]
      linarith [one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 128)
        (by linarith : (128 : ℝ) ≤ 16 * (n : ℝ) ^ 3)]
    have hn_rat : (n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - 1) ≤ 4 / 3 := by
      rw [div_le_div_iff₀ (by nlinarith) (by norm_num)]; nlinarith
    have hfac : ξ ^ 2 * ((n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - 1)) ≤ 2 :=
      (mul_le_mul (pow_le_pow_left₀ hξ_pos.le hxi_le 2) hn_rat
        (div_nonneg (by nlinarith) (by nlinarith)) (by norm_num)).trans (by norm_num)
    calc v ⬝ᵥ (E' *ᵥ v) ≤ ξ ^ 2 * (v ⬝ᵥ (F *ᵥ v)) := by
            simpa [Matrix.smul_mulVec, dotProduct_smul] using hE'_le_xi2F v
      _ ≤ ξ ^ 2 * (((n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - 1)) * (Λk * (v ⬝ᵥ v))) :=
            mul_le_mul_of_nonneg_left
              ((exactEllipsoidMatrix_quad_bounds hn hE_pos ha_ne v).2.trans
                (mul_le_mul_of_nonneg_left (hE_hi v) (div_nonneg (by nlinarith) (by nlinarith))))
              (sq_nonneg ξ)
      _ ≤ 2 * (Λk * (v ⬝ᵥ v)) := by
            rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hfac (by positivity)
      _ = (2 : ℝ) ^ (k + 1 + 2 * ρ) * (v ⬝ᵥ v) := by
            dsimp [Λk]; rw [show k + 1 + 2 * ρ = (k + 2 * ρ) + 1 by omega, pow_succ]; ring
  have hmNext_abs : ∀ r ∈ mNext, ∀ z ∈ r, |z| ≤ (2 : ℤ) ^ (p + (k + 1) + 2 * ρ) := by
    intro r hr z hz
    simp only [mNext, dyadicEllipsoidMatUpdate, List.mem_map, List.mem_range] at hr
    obtain ⟨i0, hi0, rfl⟩ := hr
    simp only [List.mem_map, List.mem_range] at hz
    obtain ⟨j0, hj0, rfl⟩ := hz
    let i : Fin n := ⟨i0, hi0⟩
    let j : Fin n := ⟨j0, hj0⟩
    have hE'ij := posDef_entry_abs_le hE'_pos hE'_hi i j
    have hget : (((mNext.getD i.1 []).getD j.1 0 : ℤ) : ℝ) = (2 : ℝ) ^ p * E' i j := by
      simp only [E', dyadicListToMat_apply]; field_simp
    have hR : |(((mNext.getD i.1 []).getD j.1 0 : ℤ) : ℝ)| ≤
        (((2 : ℤ) ^ (p + (k + 1) + 2 * ρ) : ℤ) : ℝ) := by
      rw [hget, abs_mul, abs_of_pos (by positivity)]
      refine (mul_le_mul_of_nonneg_left hE'ij (by positivity)).trans_eq ?_
      push_cast; rw [← pow_add]; congr 1; omega
    have hZ : |(mNext.getD i.1 []).getD j.1 0| ≤ (2 : ℤ) ^ (p + (k + 1) + 2 * ρ) := by
      rw [← Int.cast_abs] at hR; exact_mod_cast hR
    rwa [hget_mNext i j] at hZ
  have hdet_shrink : E'.det ≤ Real.exp (-1 / (12 * (n : ℝ) ^ 2)) * E.det := by
    have hxi2F_pos : (ξ ^ 2 • F).PosDef :=
      posDef_of_quad_lower (by
        have hFT : Fᵀ = F := by simpa [Matrix.IsHermitian] using hF_pos.isHermitian
        change (ξ ^ 2 • F)ᵀ = _; rw [Matrix.transpose_smul, hFT])
        (show 0 < ξ ^ 2 * (lamK / 4) by positivity)
        (fun v => by
          simp only [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, mul_assoc]
          exact mul_le_mul_of_nonneg_left (hF_low v) (sq_nonneg ξ))
    calc E'.det ≤ (ξ ^ 2 • F).det := posDef_det_le_det hE'_pos hxi2F_pos hE'_le_xi2F
      _ = ξ ^ (2 * n) * F.det := by rw [Matrix.det_smul, Fintype.card_fin, pow_mul]
      _ ≤ ξ ^ (2 * n) * (Real.exp (-1 / (2 * ((n : ℝ) + 1) ^ 2)) * E.det) :=
          mul_le_mul_of_nonneg_left (det_exactEllipsoidMatrix_le hn hE_pos ha_ne) (by positivity)
      _ ≤ Real.exp (-1 / (12 * (n : ℝ) ^ 2)) * E.det := by
          rw [← mul_assoc]
          exact mul_le_mul_of_nonneg_right (ellipsoid_shrink_factor_le hn) hE_pos.det_pos.le
  refine ⟨by simp [mNext, dyadicEllipsoidMatUpdate], ?_, hE'_pos, fun v => (hE'_quad v).1,
    hE'_low, hE'_hi, hmNext_abs, hdet_shrink⟩
  intro r hr
  simp only [mNext, dyadicEllipsoidMatUpdate, List.mem_map] at hr
  obtain ⟨_, _, rfl⟩ := hr; simp

/-- **Correctness of one rounded dyadic Khachiyan step.** Preserves shape dimensions, positive
definiteness, two-sided spectral bounds, entrywise bit-size invariants, multiplicative determinant
contraction `≤ exp (-1 / (12 * n ^ 2))`, and half-ellipsoid containment. -/
theorem dyadicEllipsoidStep_spec {n p kSqrt N ρ k eA : ℕ} (hn : 2 ≤ n)
    (hk : k < N) (hp : p = 3 * N + 8 * n + 16)
    (hkSqrt : 2 * p + N + ρ + eA + n + 2 ≤ kSqrt)
    {cVec : List ℤ} {mMat : List (List ℤ)} (hcLen : cVec.length = n) (hmLen : mMat.length = n)
    (hE_pos : (dyadicListToMat n p mMat).PosDef)
    (hE_low : ∀ v, (2 : ℝ) ^ (2 * ρ) / (4 : ℝ) ^ k * (v ⬝ᵥ v) ≤
      v ⬝ᵥ (dyadicListToMat n p mMat *ᵥ v))
    (hE_hi : ∀ v, v ⬝ᵥ (dyadicListToMat n p mMat *ᵥ v) ≤ (2 : ℝ) ^ (k + 2 * ρ) * (v ⬝ᵥ v))
    (hc_abs : ∀ z ∈ cVec, |z| ≤ (k : ℤ) * (2 : ℤ) ^ (p + N + ρ + 1))
    {aList : List ℤ} (haLen : aList.length = n) (haAbs : ∀ z ∈ aList, |z| ≤ (2 : ℤ) ^ eA)
    (haNe : ∃ j : Fin n, aList.getD j.1 0 ≠ 0)
    {bVec : List ℤ}
    (hbVec_def : bVec = mMat.map fun mRow => ∑ j : Fin n, mRow.getD j.1 0 * aList.getD j.1 0)
    {S : ℤ} (hS_def : S = ∑ j : Fin n, aList.getD j.1 0 * bVec.getD j.1 0) :
    let cNext := dyadicEllipsoidCenterUpdate n kSqrt ((2 : ℤ) ^ (2 * p)) ((2 : ℤ) ^ (3 * p))
      S cVec bVec
    let mNext := dyadicEllipsoidMatUpdate n S bVec mMat
    let E := dyadicListToMat n p mMat
    let c := dyadicListToVec n p cVec
    let E' := dyadicListToMat n p mNext
    let c' := dyadicListToVec n p cNext
    let a : Fin n → ℝ := fun j => (aList.getD j.1 0 : ℝ)
    cNext.length = n ∧ mNext.length = n ∧ (∀ r ∈ mNext, r.length = n) ∧ E'.PosDef ∧
      (∀ v, (2 : ℝ) ^ (2 * ρ) / (4 : ℝ) ^ (k + 1) * (v ⬝ᵥ v) ≤ v ⬝ᵥ (E' *ᵥ v)) ∧
      (∀ v, v ⬝ᵥ (E' *ᵥ v) ≤ (2 : ℝ) ^ (k + 1 + 2 * ρ) * (v ⬝ᵥ v)) ∧
      (∀ z ∈ cNext, |z| ≤ ((k + 1 : ℕ) : ℤ) * (2 : ℤ) ^ (p + N + ρ + 1)) ∧
      (∀ r ∈ mNext, ∀ z ∈ r, |z| ≤ (2 : ℤ) ^ (p + (k + 1) + 2 * ρ)) ∧
      E'.det ≤ Real.exp (-1 / (12 * (n : ℝ) ^ 2)) * E.det ∧
      (∀ x ∈ ellipsoidSet c E, a ⬝ᵥ x ≤ a ⬝ᵥ c → x ∈ ellipsoidSet c' E') := by
  intro cNext mNext E c E' c' a
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn3_ge : (8 : ℝ) ≤ (n : ℝ) ^ 3 :=
    (show (8 : ℝ) = 2 ^ 3 by norm_num) ▸ pow_le_pow_left₀ zero_le_two hn2 3
  set lamK : ℝ := (2 : ℝ) ^ (2 * ρ) / (4 : ℝ) ^ k
  set Λk : ℝ := (2 : ℝ) ^ (k + 2 * ρ)
  have hlamK_pos : 0 < lamK := by positivity
  have hlamK_ge : (1 : ℝ) / (2 : ℝ) ^ (2 * N) ≤ lamK := by
    dsimp [lamK]
    have h4 : (4 : ℝ) ^ k ≤ (2 : ℝ) ^ (2 * N) := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul]
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    exact (div_le_div_of_nonneg_left zero_le_one (by positivity) h4).trans
      (div_le_div_of_nonneg_right (one_le_pow₀ (by norm_num)) (by positivity))
  have ha_ne : a ≠ 0 := by
    obtain ⟨j, hj⟩ := haNe
    intro h0
    have h0j : (aList.getD j.1 0 : ℝ) = 0 := congrFun h0 j
    exact hj (by exact_mod_cast h0j)
  have ha_norm_ge : (1 : ℝ) ≤ a ⬝ᵥ a := by
    obtain ⟨j, hj⟩ := haNe
    have hR : (1 : ℝ) ≤ |a j| := by
      have hcast : ((1 : ℤ) : ℝ) ≤ ((|aList.getD j.1 0| : ℤ) : ℝ) :=
        Int.cast_le.mpr (Int.one_le_abs hj)
      simpa only [a, Int.cast_one, Int.cast_abs] using hcast
    have h1 : (1 : ℝ) ≤ a j * a j := by
      have := mul_le_mul hR hR zero_le_one (abs_nonneg _)
      rwa [one_mul, ← abs_mul, abs_of_nonneg (mul_self_nonneg _)] at this
    exact h1.trans (Finset.single_le_sum (f := fun i : Fin n => a i * a i)
      (fun i _ => mul_self_nonneg (a i)) (Finset.mem_univ j))
  have hbVec_get : ∀ i : Fin n, ((bVec.getD i.1 0 : ℤ) : ℝ) = (2 : ℝ) ^ p * (E *ᵥ a) i := by
    intro i
    have hi : i.1 < mMat.length := by rw [hmLen]; exact i.2
    have hbget :
        bVec.getD i.1 0 = ∑ j : Fin n, (mMat.getD i.1 []).getD j.1 0 * aList.getD j.1 0 := by
      rw [hbVec_def, List.getD_eq_getElem _ 0 (by simp [hi]), List.getElem_map,
        List.getD_eq_getElem mMat [] hi]
    rw [hbget, Int.cast_sum]
    simp only [E, Matrix.mulVec, dotProduct, dyadicListToMat_apply, a, Finset.mul_sum, Int.cast_mul]
    refine Finset.sum_congr rfl fun _ _ => ?_
    have : (2 : ℝ) ^ p ≠ 0 := by positivity
    field_simp
  set σ : ℝ := a ⬝ᵥ (E *ᵥ a)
  have hS_real : (S : ℝ) = (2 : ℝ) ^ p * σ := by
    rw [hS_def, Int.cast_sum]
    simp only [Int.cast_mul, hbVec_get, σ, dotProduct, a, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  have hσ_ge : lamK ≤ σ :=
    (by simpa using mul_le_mul_of_nonneg_left ha_norm_ge hlamK_pos.le : lamK ≤ lamK * (a ⬝ᵥ a))
      |>.trans (hE_low a)
  have hσ_pos : 0 < σ := hlamK_pos.trans_le hσ_ge
  have hS_pos : (0 : ℤ) < S := by
    have hSR : (1 : ℝ) ≤ (S : ℝ) := by
      rw [hS_real]
      calc (1 : ℝ) = (2 : ℝ) ^ (2 * N) * (1 / (2 : ℝ) ^ (2 * N)) := by field_simp
        _ ≤ (2 : ℝ) ^ p * σ :=
            mul_le_mul (pow_le_pow_right₀ (by norm_num) (by omega)) (hlamK_ge.trans hσ_ge)
              (by positivity) (by positivity)
    have h1 : (1 : ℤ) ≤ S := by exact_mod_cast hSR
    omega
  obtain ⟨hmNext_len, hmNext_row, hE'_pos, hE'_ge_Et, hE'_low, hE'_hi, hmNext_abs, hdet_shrink⟩ :=
    dyadicMatUpdate_spec hn hk hp hE_pos hE_low hE_hi ha_ne hbVec_get hS_pos hS_real
  have hS_lt_4k : ((2 : ℤ) ^ (3 * p) * S).toNat < 4 ^ kSqrt := by
    have ha_norm_le : a ⬝ᵥ a ≤ (n : ℝ) * (2 : ℝ) ^ (2 * eA) := by
      calc ∑ j : Fin n, a j * a j
          ≤ ∑ _j : Fin n, ((2 : ℝ) ^ eA) ^ 2 := Finset.sum_le_sum fun j _ => by
            have hji : j.1 < aList.length := by rw [haLen]; exact j.2
            have hj : |a j| ≤ (2 : ℝ) ^ eA := by
              have h1 : ((|aList.getD j.1 0| : ℤ) : ℝ) ≤ (((2 : ℤ) ^ eA : ℤ) : ℝ) :=
                Int.cast_le.mpr (haAbs _ (List.getD_mem 0 hji))
              simpa only [a, Int.cast_abs, Int.cast_pow, Int.cast_ofNat] using h1
            rw [← sq]
            exact sq_le_sq.mpr (by rwa [abs_of_pos (by positivity : (0 : ℝ) < (2 : ℝ) ^ eA)])
        _ = (n : ℝ) * (2 : ℝ) ^ (2 * eA) := by simp [← pow_mul, mul_comm eA 2]
    have hSR_le : (S : ℝ) ≤ (n : ℝ) * (2 : ℝ) ^ (p + N + 2 * ρ + 2 * eA) := by
      rw [hS_real]
      calc (2 : ℝ) ^ p * σ ≤ (2 : ℝ) ^ p * (Λk * (a ⬝ᵥ a)) :=
              mul_le_mul_of_nonneg_left (hE_hi a) (by positivity)
        _ ≤ (2 : ℝ) ^ p * ((2 : ℝ) ^ (N + 2 * ρ) * ((n : ℝ) * (2 : ℝ) ^ (2 * eA))) :=
              mul_le_mul_of_nonneg_left
                (mul_le_mul (pow_le_pow_right₀ (by norm_num) (by omega)) ha_norm_le
                  (Finset.sum_nonneg fun _ _ => mul_self_nonneg _) (by positivity))
                (by positivity)
        _ = (n : ℝ) * (2 : ℝ) ^ (p + N + 2 * ρ + 2 * eA) := by simp only [pow_add]; ring
    have hn_lt : (n : ℝ) < (2 : ℝ) ^ (2 * n) := by
      exact_mod_cast (nat_le_two_pow n).trans_lt (Nat.pow_lt_pow_right (by norm_num) (by omega))
    have hprod_lt : ((((2 : ℤ) ^ (3 * p) * S).toNat : ℕ) : ℝ) < (4 : ℝ) ^ kSqrt := by
      have hz := Int.toNat_of_nonneg (mul_nonneg (by positivity : (0 : ℤ) ≤ 2 ^ (3 * p)) hS_pos.le)
      have hcast : ((((2 : ℤ) ^ (3 * p) * S).toNat : ℕ) : ℝ) = (2 : ℝ) ^ (3 * p) * (S : ℝ) := by
        have hR := congrArg (Int.cast (R := ℝ)) hz
        simp only [Int.cast_natCast, Int.cast_mul, Int.cast_pow, Int.cast_ofNat] at hR
        exact hR
      rw [hcast]
      calc (2 : ℝ) ^ (3 * p) * (S : ℝ)
          < (2 : ℝ) ^ (3 * p) * ((2 : ℝ) ^ (2 * n) * (2 : ℝ) ^ (p + N + 2 * ρ + 2 * eA)) :=
            mul_lt_mul_of_pos_left
              (hSR_le.trans_lt (mul_lt_mul_of_pos_right hn_lt (by positivity))) (by positivity)
        _ = (2 : ℝ) ^ (4 * p + N + 2 * ρ + 2 * eA + 2 * n) := by simp only [pow_add]; ring
        _ ≤ (2 : ℝ) ^ (2 * kSqrt) := pow_le_pow_right₀ (by norm_num) (by omega)
        _ = (4 : ℝ) ^ kSqrt := by rw [pow_mul]; norm_num
    exact_mod_cast hprod_lt
  set cex := exactEllipsoidCenter c E a
  have hEa_bound : ∀ i : Fin n, |(E *ᵥ a) i| ≤ Real.sqrt Λk * Real.sqrt σ :=
    posDef_mulVec_coord_abs_le hE_pos (by positivity) hE_hi a
  have hcNext_get : ∀ i : Fin n,
      cNext.getD i.1 0 = cVec.getD i.1 0 -
        ((2 : ℤ) ^ (2 * p) * bVec.getD i.1 0).ediv
          (((n + 1 : ℕ) : ℤ) *
            ((isqrtBounded kSqrt ((2 : ℤ) ^ (3 * p) * S).toNat + 1 : ℕ) : ℤ)) :=
    fun i => getD_map_range n _ 0 i.2
  have hc_err : ∀ i : Fin n, |c' i - cex i| ≤ 2 / (2 : ℝ) ^ p := by
    intro i
    set Rnat := ((2 : ℤ) ^ (3 * p) * S).toNat
    set q := isqrtBounded kSqrt Rnat
    have hq_eq : q = Nat.sqrt Rnat := isqrtBounded_eq_sqrt hS_lt_4k
    have hRnat_real : (Rnat : ℝ) = (2 : ℝ) ^ (4 * p) * σ := by
      have hz := Int.toNat_of_nonneg (mul_nonneg (by positivity : (0 : ℤ) ≤ 2 ^ (3 * p)) hS_pos.le)
      have hR := congrArg (Int.cast (R := ℝ)) hz
      simp only [Int.cast_natCast, Int.cast_mul, Int.cast_pow, Int.cast_ofNat] at hR
      dsimp only [Rnat]; rw [hR, hS_real, ← mul_assoc, ← pow_add]; congr 2; omega
    have hsqrtR : Real.sqrt (Rnat : ℝ) = (2 : ℝ) ^ (2 * p) * Real.sqrt σ := by
      rw [hRnat_real, Real.sqrt_mul (by positivity),
        show (2 : ℝ) ^ (4 * p) = ((2 : ℝ) ^ (2 * p)) ^ 2 by rw [← pow_mul]; congr 1; omega,
        Real.sqrt_sq (by positivity)]
    have hsqrt_pos : 0 < Real.sqrt (Rnat : ℝ) := by
      rw [hsqrtR]; exact mul_pos (by positivity) (Real.sqrt_pos.mpr hσ_pos)
    have hq1_pos : (0 : ℝ) < (q : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) q]
    have hq_hi : Real.sqrt (Rnat : ℝ) < (q : ℝ) + 1 := by
      rw [Real.sqrt_lt' hq1_pos, sq]
      have hcast : (Rnat : ℝ) < (((q + 1) * (q + 1) : ℕ) : ℝ) :=
        Nat.cast_lt.mpr (hq_eq ▸ Nat.lt_succ_sqrt Rnat)
      simpa using hcast
    set denC : ℤ := ((n + 1 : ℕ) : ℤ) * ((q + 1 : ℕ) : ℤ)
    have hdenC_pos : 0 < denC := by positivity
    set numC : ℤ := (2 : ℤ) ^ (2 * p) * bVec.getD i.1 0
    have hnumR : (numC : ℝ) = (2 : ℝ) ^ (3 * p) * (E *ᵥ a) i := by
      simp only [numC, Int.cast_mul, Int.cast_pow, Int.cast_ofNat, hbVec_get]
      rw [← mul_assoc, ← pow_add]; congr 2; omega
    have hc'i : c' i = c i - ((numC.ediv denC : ℤ) : ℝ) / (2 : ℝ) ^ p := by
      simp only [c', c, dyadicListToVec_apply, hcNext_get i, Int.cast_sub, sub_div]; rfl
    have hcexi : cex i =
        c i - ((numC : ℝ) / (((n : ℝ) + 1) * Real.sqrt (Rnat : ℝ))) / (2 : ℝ) ^ p := by
      simp only [cex, exactEllipsoidCenter_apply, hnumR, hsqrtR]
      congr 1
      rw [show (2 : ℝ) ^ (3 * p) = (2 : ℝ) ^ (2 * p) * (2 : ℝ) ^ p by
        rw [← pow_add]; congr 1; omega]
      have hp0 : (2 : ℝ) ^ p ≠ 0 := by positivity
      have hs0 : Real.sqrt σ ≠ 0 := (Real.sqrt_pos.mpr hσ_pos).ne'
      have hnp : (n : ℝ) + 1 ≠ 0 := by linarith
      have hσeq : a ⬝ᵥ (E *ᵥ a) = σ := rfl
      rw [hσeq]; field_simp
    rw [hc'i, hcexi, show c i - ((numC.ediv denC : ℤ) : ℝ) / (2 : ℝ) ^ p -
        (c i - ((numC : ℝ) / (((n : ℝ) + 1) * Real.sqrt (Rnat : ℝ))) / (2 : ℝ) ^ p) =
        (((numC : ℝ) / (denC : ℝ) - ((numC.ediv denC : ℤ) : ℝ)) +
          ((numC : ℝ) / (((n : ℝ) + 1) * Real.sqrt (Rnat : ℝ)) - (numC : ℝ) / (denC : ℝ))) /
          (2 : ℝ) ^ p by ring, abs_div, abs_of_pos (by positivity : (0 : ℝ) < (2 : ℝ) ^ p)]
    refine div_le_div_of_nonneg_right ((abs_add_le _ _).trans ?_) (by positivity)
    obtain ⟨hd1, hd2⟩ := int_ediv_real_bounds numC hdenC_pos
    have hp1 : |(numC : ℝ) / (denC : ℝ) - ((numC.ediv denC : ℤ) : ℝ)| ≤ 1 :=
      abs_le.mpr ⟨by linarith, by linarith⟩
    have hp2 :
        |(numC : ℝ) / (((n : ℝ) + 1) * Real.sqrt (Rnat : ℝ)) - (numC : ℝ) / (denC : ℝ)| ≤ 1 := by
      have hdenCR : (denC : ℝ) = ((n : ℝ) + 1) * ((q : ℝ) + 1) := by dsimp [denC]; push_cast; rfl
      have hdenom_pos : 0 < ((n : ℝ) + 1) * Real.sqrt (Rnat : ℝ) * ((q : ℝ) + 1) :=
        mul_pos (mul_pos (by linarith) hsqrt_pos) hq1_pos
      have hfrac : (numC : ℝ) / (((n : ℝ) + 1) * Real.sqrt (Rnat : ℝ)) - (numC : ℝ) / (denC : ℝ) =
          (numC : ℝ) * (((q : ℝ) + 1 - Real.sqrt (Rnat : ℝ)) /
            (((n : ℝ) + 1) * Real.sqrt (Rnat : ℝ) * ((q : ℝ) + 1))) := by
        rw [hdenCR]
        have h1 : (n : ℝ) + 1 ≠ 0 := by linarith
        have h2 : Real.sqrt (Rnat : ℝ) ≠ 0 := hsqrt_pos.ne'
        have h3 : (q : ℝ) + 1 ≠ 0 := hq1_pos.ne'
        field_simp
      rw [hfrac, abs_mul, hnumR, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (2 : ℝ) ^ (3 * p)),
        abs_of_pos (div_pos (by linarith) hdenom_pos)]
      have hden2_pos : 0 < ((n : ℝ) + 1) * Real.sqrt (Rnat : ℝ) * Real.sqrt (Rnat : ℝ) :=
        mul_pos (mul_pos (by linarith) hsqrt_pos) hsqrt_pos
      have hq_lo : (q : ℝ) ≤ Real.sqrt (Rnat : ℝ) := by
        rw [Real.le_sqrt (Nat.cast_nonneg q) (Nat.cast_nonneg Rnat), sq]
        exact_mod_cast (hq_eq ▸ Nat.sqrt_le Rnat)
      calc (2 : ℝ) ^ (3 * p) * |(E *ᵥ a) i| *
            (((q : ℝ) + 1 - Real.sqrt (Rnat : ℝ)) /
              (((n : ℝ) + 1) * Real.sqrt (Rnat : ℝ) * ((q : ℝ) + 1)))
          ≤ (2 : ℝ) ^ (3 * p) * (Real.sqrt Λk * Real.sqrt σ) *
              (1 / (((n : ℝ) + 1) * Real.sqrt (Rnat : ℝ) * Real.sqrt (Rnat : ℝ))) :=
            mul_le_mul (mul_le_mul_of_nonneg_left (hEa_bound i) (by positivity))
              (div_le_div₀ zero_le_one (by linarith) hden2_pos
                (mul_le_mul_of_nonneg_left hq_hi.le (mul_pos (by linarith) hsqrt_pos).le))
              (div_pos (by linarith) hdenom_pos).le (by positivity)
        _ = Real.sqrt (Λk / σ) / (((n : ℝ) + 1) * (2 : ℝ) ^ p) := by
            rw [hsqrtR, Real.sqrt_div (by positivity),
              show (2 : ℝ) ^ (3 * p) = (2 : ℝ) ^ (2 * p) * (2 : ℝ) ^ p by
                rw [← pow_add]; congr 1; omega,
              show (2 : ℝ) ^ (2 * p) = (2 : ℝ) ^ p * (2 : ℝ) ^ p by
                rw [← pow_add]; congr 1; omega]
            have hp0 : (2 : ℝ) ^ p ≠ 0 := by positivity
            have hs0 : Real.sqrt σ ≠ 0 := (Real.sqrt_pos.mpr hσ_pos).ne'
            have hnp : (n : ℝ) + 1 ≠ 0 := by linarith
            field_simp
        _ ≤ 1 := by
            rw [div_le_one (mul_pos (by linarith) (by positivity))]
            have hrat : Λk / σ ≤ ((2 : ℝ) ^ (2 * N)) ^ 2 := by
              calc Λk / σ ≤ Λk / lamK := div_le_div_of_nonneg_left (by positivity) hlamK_pos hσ_ge
                _ = (2 : ℝ) ^ (3 * k) := by
                    dsimp [Λk, lamK]
                    rw [show (4 : ℝ) ^ k = (2 : ℝ) ^ (2 * k) by
                      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul],
                      pow_add, div_div_eq_mul_div,
                      show (2 : ℝ) ^ k * (2 : ℝ) ^ (2 * ρ) * (2 : ℝ) ^ (2 * k) =
                        (2 : ℝ) ^ (2 * ρ) * ((2 : ℝ) ^ k * (2 : ℝ) ^ (2 * k)) by ring,
                      mul_div_cancel_left₀ _ (by positivity : (2 : ℝ) ^ (2 * ρ) ≠ 0), ← pow_add]
                    congr 1; omega
                _ ≤ ((2 : ℝ) ^ (2 * N)) ^ 2 := by
                    rw [← pow_mul]; exact pow_le_pow_right₀ (by norm_num) (by omega)
            calc Real.sqrt (Λk / σ) ≤ (2 : ℝ) ^ (2 * N) :=
                    (Real.sqrt_le_sqrt hrat).trans_eq (Real.sqrt_sq (by positivity))
              _ ≤ (2 : ℝ) ^ p := pow_le_pow_right₀ (by norm_num) (by omega)
              _ ≤ ((n : ℝ) + 1) * (2 : ℝ) ^ p :=
                    by nlinarith [show (0 : ℝ) < (2 : ℝ) ^ p by positivity]
    linarith
  have hcNext_abs : ∀ z ∈ cNext, |z| ≤ ((k + 1 : ℕ) : ℤ) * (2 : ℤ) ^ (p + N + ρ + 1) := by
    intro z hz
    simp only [cNext, dyadicEllipsoidCenterUpdate, List.mem_map, List.mem_range] at hz
    obtain ⟨i0, hi0, rfl⟩ := hz
    let i : Fin n := ⟨i0, hi0⟩
    have hci_old : |cVec.getD i.1 0| ≤ (k : ℤ) * (2 : ℤ) ^ (p + N + ρ + 1) :=
      hc_abs _ (List.getD_mem 0 (by rw [hcLen]; exact i.2))
    have h1 : |cex i - c i| ≤ (2 : ℝ) ^ (N + ρ) := by
      have hs0 : 0 < Real.sqrt σ := Real.sqrt_pos.mpr hσ_pos
      have hpos_d : 0 < ((n : ℝ) + 1) * Real.sqrt σ := mul_pos (by linarith) hs0
      have hσeq : a ⬝ᵥ (E *ᵥ a) = σ := rfl
      simp only [cex, exactEllipsoidCenter_apply, hσeq, sub_sub_cancel_left, abs_neg, abs_mul,
        abs_inv, abs_of_pos hpos_d]
      rw [inv_mul_eq_div, div_le_iff₀ hpos_d]
      have hΛ_le : Real.sqrt Λk ≤ (2 : ℝ) ^ (N + ρ) := by
        rw [Real.sqrt_le_left (by positivity), ← pow_mul]
        exact pow_le_pow_right₀ (by norm_num) (by omega)
      calc |(E *ᵥ a) i| ≤ (2 : ℝ) ^ (N + ρ) * Real.sqrt σ :=
              (hEa_bound i).trans (mul_le_mul_of_nonneg_right hΛ_le hs0.le)
        _ ≤ (2 : ℝ) ^ (N + ρ) * (((n : ℝ) + 1) * Real.sqrt σ) :=
              mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
    have h2 : |c' i - cex i| ≤ 1 :=
      (hc_err i).trans ((div_le_one (by positivity)).mpr
        (le_trans (by norm_num : (2 : ℝ) ≤ 2 ^ 1) (pow_le_pow_right₀ (by norm_num) (by omega))))
    have hstep_c : |c' i - c i| ≤ (2 : ℝ) ^ (N + ρ + 1) := by
      have htri : |c' i - c i| ≤ |c' i - cex i| + |cex i - c i| := by
        simpa using abs_add_le (c' i - cex i) (cex i - c i)
      have h3 : (1 : ℝ) ≤ (2 : ℝ) ^ (N + ρ) := one_le_pow₀ (by norm_num)
      rw [pow_succ]; linarith
    have hR : |((cNext.getD i.1 0 : ℤ) : ℝ) - ((cVec.getD i.1 0 : ℤ) : ℝ)| ≤
        (((2 : ℤ) ^ (p + N + ρ + 1) : ℤ) : ℝ) := by
      have hg1 : ((cNext.getD i.1 0 : ℤ) : ℝ) = (2 : ℝ) ^ p * c' i := by
        simp only [c', dyadicListToVec_apply]; field_simp
      have hg2 : ((cVec.getD i.1 0 : ℤ) : ℝ) = (2 : ℝ) ^ p * c i := by
        simp only [c, dyadicListToVec_apply]; field_simp
      rw [hg1, hg2, ← mul_sub, abs_mul, abs_of_pos (by positivity)]
      refine (mul_le_mul_of_nonneg_left hstep_c (by positivity)).trans_eq ?_
      push_cast; rw [← pow_add]; congr 1; omega
    have hZ : |cNext.getD i.1 0 - cVec.getD i.1 0| ≤ (2 : ℤ) ^ (p + N + ρ + 1) := by
      rw [← Int.cast_sub, ← Int.cast_abs] at hR; exact_mod_cast hR
    have htot : |cNext.getD i.1 0| ≤ ((k + 1 : ℕ) : ℤ) * (2 : ℤ) ^ (p + N + ρ + 1) := by
      have htri : |cNext.getD i.1 0| ≤
          |cVec.getD i.1 0| + |cNext.getD i.1 0 - cVec.getD i.1 0| := by
        simpa using abs_add_le (cVec.getD i.1 0) (cNext.getD i.1 0 - cVec.getD i.1 0)
      push_cast; linarith
    rwa [hcNext_get i] at htot
  have hcontain : ∀ x ∈ ellipsoidSet c E, a ⬝ᵥ x ≤ a ⬝ᵥ c → x ∈ ellipsoidSet c' E' := by
    intro x hx hcut
    set F := exactEllipsoidMatrix E a
    have hF_pos : F.PosDef := exactEllipsoidMatrix_posDef hn hE_pos ha_ne
    have hF_low : ∀ v : Fin n → ℝ, (lamK / 4) * (v ⬝ᵥ v) ≤ v ⬝ᵥ (F *ᵥ v) := fun v => by
      have hfac : (1 / 4 : ℝ) ≤ (n : ℝ) ^ 2 / ((n : ℝ) + 1) ^ 2 := by
        rw [div_le_div_iff₀ (by norm_num) (by positivity)]; nlinarith
      calc (lamK / 4) * (v ⬝ᵥ v) = (1 / 4 : ℝ) * (lamK * (v ⬝ᵥ v)) := by ring
        _ ≤ ((n : ℝ) ^ 2 / ((n : ℝ) + 1) ^ 2) * (v ⬝ᵥ (E *ᵥ v)) :=
            mul_le_mul hfac (hE_low v)
              (mul_nonneg hlamK_pos.le (Finset.sum_nonneg fun _ _ => mul_self_nonneg _))
              (by positivity)
        _ ≤ v ⬝ᵥ (F *ᵥ v) := (exactEllipsoidMatrix_quad_bounds hn hE_pos ha_ne v).1
    have hF_mem : (x - cex) ⬝ᵥ (F⁻¹ *ᵥ (x - cex)) ≤ 1 :=
      mem_ellipsoidSet_iff.mp (mem_exactEllipsoidSet_of_halfspace hn hE_pos ha_ne hx hcut)
    set δc : Fin n → ℝ := c' - cex
    have hδc_norm : δc ⬝ᵥ δc ≤ 4 * (n : ℝ) / (2 : ℝ) ^ (2 * p) := by
      calc ∑ i : Fin n, δc i * δc i
          ≤ ∑ _i : Fin n, (2 / (2 : ℝ) ^ p) ^ 2 := Finset.sum_le_sum fun i _ => (by
            rw [← sq]
            exact sq_le_sq.mpr (by
              rw [abs_of_pos (by positivity : (0 : ℝ) < 2 / (2 : ℝ) ^ p)]
              exact hc_err i))
        _ = 4 * (n : ℝ) / (2 : ℝ) ^ (2 * p) := by simp [div_pow, ← pow_mul]; ring
    set η : ℝ := 1 / (64 * (n : ℝ) ^ 3)
    have hη_pos : 0 < η := by positivity
    have hδc_Finv : δc ⬝ᵥ (F⁻¹ *ᵥ δc) ≤ η ^ 2 := by
      have hinv : (lamK / 4)⁻¹ ≤ (2 : ℝ) ^ (2 * N + 2) := by
        have hge : (1 : ℝ) / (2 : ℝ) ^ (2 * N + 2) ≤ lamK / 4 := by
          rw [show (1 : ℝ) / (2 : ℝ) ^ (2 * N + 2) = (1 / (2 : ℝ) ^ (2 * N)) / 4 by
            rw [pow_add]; norm_num; ring]
          exact div_le_div_of_nonneg_right hlamK_ge (by norm_num)
        simpa using inv_anti₀ (by positivity) hge
      calc δc ⬝ᵥ (F⁻¹ *ᵥ δc) ≤ (2 : ℝ) ^ (2 * N + 2) * (4 * (n : ℝ) / (2 : ℝ) ^ (2 * p)) :=
              (posDef_inv_quad_le hF_pos (by positivity) hF_low δc).trans
                (mul_le_mul hinv hδc_norm (Finset.sum_nonneg fun _ _ => mul_self_nonneg _)
                  (by positivity))
        _ ≤ η ^ 2 := by
            change _ ≤ (1 / (64 * (n : ℝ) ^ 3)) ^ 2
            rw [div_pow, one_pow, mul_div,
              div_le_div_iff₀ (by positivity) (by positivity), one_mul]
            have hn7 : (n : ℝ) ^ 7 ≤ ((2 : ℝ) ^ n) ^ 7 :=
              pow_le_pow_left₀ (by positivity) (by exact_mod_cast nat_le_two_pow n) 7
            calc (2 : ℝ) ^ (2 * N + 2) * (4 * (n : ℝ)) * (64 * (n : ℝ) ^ 3) ^ 2
                = ((2 : ℝ) ^ 12 * (n : ℝ) ^ 7) * (2 : ℝ) ^ (2 * N + 4) := by
                  rw [show (2 : ℝ) ^ (2 * N + 4) = (2 : ℝ) ^ (2 * N + 2) * 4 by
                    rw [pow_add]; ring]; ring
              _ ≤ ((2 : ℝ) ^ 12 * ((2 : ℝ) ^ n) ^ 7) * (2 : ℝ) ^ (2 * N + 4) :=
                  mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hn7 (by positivity))
                    (by positivity)
              _ = (2 : ℝ) ^ (2 * N + 7 * n + 16) := by
                  rw [← pow_mul, ← pow_add, ← pow_add]; congr 1; omega
              _ ≤ (2 : ℝ) ^ (2 * p) := pow_le_pow_right₀ (by norm_num) (by omega)
    set ξ : ℝ := 1 + 1 / (16 * (n : ℝ) ^ 3)
    have hξ_pos : 0 < ξ := by positivity
    have hshift := posDef_center_shift_quad_le hF_pos (x - cex) δc hη_pos
    rw [show x - cex - δc = x - c' by simp [δc]] at hshift
    have hFinv_c' : (x - c') ⬝ᵥ (F⁻¹ *ᵥ (x - c')) ≤ ξ := by
      have ht1 : (1 + η) * ((x - cex) ⬝ᵥ (F⁻¹ *ᵥ (x - cex))) ≤ 1 + η := by
        simpa using mul_le_mul_of_nonneg_left hF_mem (by positivity : 0 ≤ 1 + η)
      have ht2 : (1 + η⁻¹) * (δc ⬝ᵥ (F⁻¹ *ᵥ δc)) ≤ η + η ^ 2 :=
        (mul_le_mul_of_nonneg_left hδc_Finv (by positivity)).trans_eq
          (by have := hη_pos.ne'; field_simp; ring)
      have hη1 : η ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
      have hη2 : η ^ 2 ≤ η := by nlinarith
      have h4η : 1 + 4 * η = ξ := by dsimp [η, ξ]; ring
      linarith
    have hEt_pos : (ξ • F).PosDef :=
      posDef_of_quad_lower (by
        have hFT : Fᵀ = F := by simpa [Matrix.IsHermitian] using hF_pos.isHermitian
        change (ξ • F)ᵀ = _; rw [Matrix.transpose_smul, hFT])
        (show 0 < ξ * (lamK / 4) by positivity)
        (fun v => by
          simp only [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, mul_assoc]
          exact mul_le_mul_of_nonneg_left (hF_low v) hξ_pos.le)
    have hEt_inv : (ξ • F)⁻¹ = ξ⁻¹ • F⁻¹ :=
      Matrix.inv_eq_right_inv (by
        rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hξ_pos.ne', one_smul,
          Matrix.mul_nonsing_inv F (isUnit_iff_ne_zero.mpr hF_pos.det_pos.ne')])
    rw [mem_ellipsoidSet_iff]
    refine (posDef_inv_quad_anti hEt_pos hE'_pos hE'_ge_Et (x - c')).trans ?_
    rw [hEt_inv, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
    exact (inv_mul_le_one₀ hξ_pos).mpr hFinv_c'
  exact ⟨by simp [cNext, dyadicEllipsoidCenterUpdate], hmNext_len, hmNext_row, hE'_pos, hE'_low,
    hE'_hi, hcNext_abs, hmNext_abs, hdet_shrink, hcontain⟩

-- Non-vacuity witness: bounded binary-search square root on a nontrivial input.
example : isqrtBounded 4 144 = 12 := by
  rw [isqrtBounded_eq_sqrt (by decide), show (144 : ℕ) = 12 * 12 by rfl, Nat.sqrt_eq]

end CslibFrontier.Complexity.LinearProgramming
