/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FormalPapers Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.Code.ParityCheck
public import CslibFrontier.Foundations.Data.Code.ReedSolomon
import Mathlib.Algebra.Algebra.ZMod
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.LinearAlgebra.Dimension.Free

/-!
# Unique-decoding checksums from linear and Reed–Solomon parity-check codes

A function `cksum : (ι → α) → β` on a finite Hamming space is a *`ρ`-unique decoding checksum*
(`Cslib.Code.IsUniqueDecodingChecksum`) if inside every Hamming ball of radius `ρ`, distinct words
have distinct digests. When `H : Matrix (Fin r) (Fin k) F` has parity-check minimum distance
`D > 2 * ρ`, blockwise encoding followed by `H *ᵥ ·` and symbolwise decoding yields a `ρ`-unique
decoding checksum (`isUniqueDecodingChecksum_syndromeChecksum`). Instantiating `H` with a `2ρ × k`
Vandermonde matrix over any finite field `F` of cardinality `2 ^ s ≥ k` yields an explicit
`Bool`-additive (`XOR`-linear) `ρ`-unique decoding checksum
`(Fin k → Bool) → (Fin (s * (2 * ρ)) → Bool)` (`exists_reedSolomon_uniqueDecodingChecksum`).

## Main definitions

* `Cslib.Code.IsUniqueDecodingChecksum`: `ρ`-unique decoding checksum predicate.
* `Cslib.Code.syndromeChecksum`: blockwise parity-check syndrome checksum.
* `Cslib.Code.vandermondeParityCheck`: `t × k` Vandermonde parity-check matrix `(α i) ^ r`.
* `Cslib.Code.LinearBitChecksum`: `Bool`-additive matrix checksum `(Fin k → Bool) → (Fin L → Bool)`.

## Main results

* `Cslib.Code.isUniqueDecodingChecksum_syndromeChecksum`: linear-code syndrome unique decoding for
  `2 * ρ < D`.
* `Cslib.Code.lt_minDist_vandermondeParityCheck`:
  `t < minDist (parityCheckCode (vandermondeParityCheck α t))`.
* `Cslib.Code.exists_reedSolomon_uniqueDecodingChecksum`: existence of `Bool`-additive Reed–Solomon
  `2ρ`-checksums over finite fields of cardinality `2 ^ s ≥ k`.
-/

public section

namespace Cslib.Code

open Finset Matrix Polynomial

/-- A map `cksum : (ι → α) → β` is a *`ρ`-unique decoding checksum* if inside every `ρ`-Hamming
ball, distinct words receive distinct digests. -/
def IsUniqueDecodingChecksum {ι α β : Type*} [Fintype ι] [DecidableEq α]
    (ρ : ℕ) (cksum : (ι → α) → β) : Prop :=
  ∀ m m' m'' : ι → α,
    hammingDist m' m ≤ ρ → hammingDist m'' m ≤ ρ → m' ≠ m'' → cksum m' ≠ cksum m''

/-- At radius `0`, every map is a `0`-unique decoding checksum. -/
theorem isUniqueDecodingChecksum_zero {ι α β : Type*} [Fintype ι] [DecidableEq α]
    (cksum : (ι → α) → β) : IsUniqueDecodingChecksum 0 cksum := by
  intro m m' m'' h₁ h₂ hne
  have hm' : m' = m := hammingDist_eq_zero.mp (Nat.eq_zero_of_le_zero h₁)
  have hm'' : m'' = m := hammingDist_eq_zero.mp (Nat.eq_zero_of_le_zero h₂)
  exact absurd (hm'.trans hm''.symm) hne

/-- Every injective map is a `ρ`-unique decoding checksum for all `ρ`. -/
theorem isUniqueDecodingChecksum_of_injective {ι α β : Type*} [Fintype ι] [DecidableEq α]
    (ρ : ℕ) {cksum : (ι → α) → β} (hinj : Function.Injective cksum) :
    IsUniqueDecodingChecksum ρ cksum :=
  fun _ _ _ _ _ hne hck ↦ hne (hinj hck)

/-- Blockwise parity-check syndrome checksum over `F`. -/
def syndromeChecksum {k r s : ℕ} {F : Type*} [Semiring F]
    (H : Matrix (Fin r) (Fin k) F)
    (enc : (Fin s → Bool) → F) (dec : F → (Fin s → Bool))
    (m : Fin k × Fin s → Bool) : Fin r × Fin s → Bool :=
  fun p ↦ dec ((H *ᵥ fun i ↦ enc (fun j ↦ m (i, j))) p.1) p.2

private lemma block_hammingDist_le {k s : ℕ} {F : Type*} [DecidableEq F]
    (enc : (Fin s → Bool) → F) (m₁ m₂ : Fin k × Fin s → Bool) :
    hammingDist (fun i : Fin k ↦ enc (fun j ↦ m₁ (i, j)))
      (fun i : Fin k ↦ enc (fun j ↦ m₂ (i, j))) ≤ hammingDist m₁ m₂ := by
  classical
  by_cases hs : s = 0
  · subst hs
    have heq : m₁ = m₂ := funext fun ⟨_, j⟩ ↦ Fin.elim0 j
    simp [heq]
  · let j₀ : Fin s := ⟨0, Nat.pos_of_ne_zero hs⟩
    let diffBlocks : Finset (Fin k) :=
      Finset.univ.filter fun i ↦ enc (fun j ↦ m₁ (i, j)) ≠ enc (fun j ↦ m₂ (i, j))
    have hexists : ∀ i ∈ diffBlocks, ∃ j : Fin s, m₁ (i, j) ≠ m₂ (i, j) := by
      intro i hi
      by_contra h_all
      push Not at h_all
      exact (Finset.mem_filter.mp hi).2 (congrArg enc (funext h_all))
    choose witness hwitness using hexists
    refine Finset.card_le_card_of_injOn
      (fun i ↦ (i, if hi : i ∈ diffBlocks then witness i hi else j₀)) ?_ ?_
    · intro i hi
      have hi' : i ∈ diffBlocks := Finset.mem_coe.mp hi
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
      split_ifs
      exact hwitness i hi'
    · intro i₁ _ i₂ _ heq
      exact (Prod.mk.inj heq).1

/-- **Linear-code syndrome unique decoding**: if `D ≤ minDist (parityCheckCode H)` and `2 * ρ < D`,
then `syndromeChecksum H enc dec` is `ρ`-unique decoding. -/
theorem isUniqueDecodingChecksum_syndromeChecksum {k r s D ρ : ℕ} {F : Type*} [CommRing F]
    [DecidableEq F] (H : Matrix (Fin r) (Fin k) F)
    (enc : (Fin s → Bool) → F) (dec : F → (Fin s → Bool))
    (henc : Function.Injective enc) (hdec : Function.Injective dec)
    (hD : (D : ℕ∞) ≤ minDist (parityCheckCode H : Set (Fin k → F)))
    (hρ : 2 * ρ < D) :
    IsUniqueDecodingChecksum ρ (syndromeChecksum H enc dec) := by
  intro m m' m'' hm' hm'' hne hck
  let v' : Fin k → F := fun i ↦ enc (fun j ↦ m' (i, j))
  let v'' : Fin k → F := fun i ↦ enc (fun j ↦ m'' (i, j))
  have hv_ne : v' ≠ v'' := fun hv ↦ hne (funext fun ⟨i, j⟩ ↦ congrFun (henc (congrFun hv i)) j)
  have hHv : H *ᵥ v' = H *ᵥ v'' := funext fun a ↦ hdec (funext fun b ↦ congrFun hck (a, b))
  have hker : H *ᵥ (v' - v'') = 0 := by rw [Matrix.mulVec_sub, hHv, sub_self]
  have hdist_bits : hammingDist m' m'' ≤ 2 * ρ := by
    have htri := hammingDist_triangle m' m m''
    rw [hammingDist_comm m m''] at htri
    omega
  have hnorm_le : hammingNorm (v' - v'') ≤ 2 * ρ := by
    rw [← hammingDist_zero_right]
    have hsub : hammingDist (v' - v'') 0 = hammingDist v' v'' := by simp [hammingDist, sub_eq_zero]
    rw [hsub]
    exact (block_hammingDist_le enc m' m'').trans hdist_bits
  have hlt_min : (2 * ρ : ℕ∞) < minDist (parityCheckCode H : Set (Fin k → F)) :=
    lt_of_lt_of_le (by exact_mod_cast hρ) hD
  have hgt := (lt_minDist_parityCheckCode_iff H).mp hlt_min (v' - v'')
    (sub_ne_zero.mpr hv_ne) hker
  exact absurd hgt (not_lt.mpr hnorm_le)

/-- The `t × k` Vandermonde parity-check matrix `H r i = (α i) ^ r`. -/
def vandermondeParityCheck {F : Type*} [Field F] {k : ℕ} (α : Fin k → F) (t : ℕ) :
    Matrix (Fin t) (Fin k) F :=
  Matrix.of fun r i ↦ (α i) ^ (r : ℕ)

private lemma natDegree_prod_X_sub_C_le {F ι : Type*} [Field F] (S : Finset ι) (f : ι → F) :
    (∏ j ∈ S, (Polynomial.X - Polynomial.C (f j))).natDegree ≤ S.card := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha]
    refine (Polynomial.natDegree_mul_le).trans ?_
    have hdeg1 : (Polynomial.X - Polynomial.C (f a)).natDegree ≤ 1 :=
      Polynomial.natDegree_X_sub_C_le (f a)
    omega

/-- **Vandermonde parity-check minimum distance**: for distinct points `α : Fin k → F`,
`t < minDist (parityCheckCode (vandermondeParityCheck α t))`. -/
theorem lt_minDist_vandermondeParityCheck {F : Type*} [Field F] [DecidableEq F]
    {k : ℕ} {α : Fin k → F} (hα : Function.Injective α) (t : ℕ) :
    (t : ℕ∞) < minDist (parityCheckCode (vandermondeParityCheck α t) : Set (Fin k → F)) := by
  rw [lt_minDist_parityCheckCode_iff]
  intro x hx0 hker
  by_contra hle
  push Not at hle
  let S : Finset (Fin k) := Finset.univ.filter fun i ↦ x i ≠ 0
  have hScard : S.card ≤ t := hle
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hx0
  have hi₀S : i₀ ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ i₀, hi₀⟩
  have hposS : 0 < S.card := Finset.card_pos.mpr ⟨i₀, hi₀S⟩
  let S' : Finset (Fin k) := S.erase i₀
  let P : F[X] := ∏ j ∈ S', (Polynomial.X - Polynomial.C (α j))
  have hPdeg : P.natDegree < t := by
    have h1 : P.natDegree ≤ S'.card := natDegree_prod_X_sub_C_le S' α
    have h2 : S'.card = S.card - 1 := Finset.card_erase_of_mem hi₀S
    omega
  have hsum_zero : ∑ i : Fin k, x i * P.eval (α i) = 0 := by
    have hPsum : P = ∑ r ∈ Finset.range t, Polynomial.monomial r (P.coeff r) :=
      Polynomial.as_sum_range' P t (Nat.lt_of_lt_of_le hPdeg le_rfl)
    calc ∑ i : Fin k, x i * P.eval (α i)
        = ∑ i : Fin k, x i *
            (∑ r ∈ Finset.range t, Polynomial.monomial r (P.coeff r)).eval (α i) := by
          rw [← hPsum]
      _ = ∑ i : Fin k, ∑ r : Fin t, P.coeff r * ((α i) ^ (r : ℕ) * x i) := by
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          have heval_sum :
              (∑ r ∈ Finset.range t, Polynomial.monomial r (P.coeff r)).eval (α i) =
                ∑ r ∈ Finset.range t, (Polynomial.monomial r (P.coeff r)).eval (α i) := by
            simpa only [Polynomial.coe_evalRingHom] using
              map_sum (Polynomial.evalRingHom (α i))
                (fun r ↦ Polynomial.monomial r (P.coeff r)) (Finset.range t)
          rw [heval_sum, ← Fin.sum_univ_eq_sum_range, Finset.mul_sum]
          refine Finset.sum_congr rfl fun r _ ↦ ?_
          rw [Polynomial.eval_monomial]
          ring
      _ = ∑ r : Fin t, P.coeff r * ∑ i : Fin k, (α i) ^ (r : ℕ) * x i := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun r _ ↦ by rw [Finset.mul_sum]
      _ = ∑ r : Fin t, P.coeff r * (vandermondeParityCheck α t *ᵥ x) r := rfl
      _ = 0 := by simp [hker]
  have hsum_single : ∑ i : Fin k, x i * P.eval (α i) = x i₀ * P.eval (α i₀) := by
    refine Finset.sum_eq_single i₀ (fun i _ hne_i ↦ ?_) (fun h ↦ absurd (Finset.mem_univ i₀) h)
    by_cases hiS : i ∈ S
    · have hiS' : i ∈ S' := Finset.mem_erase.mpr ⟨hne_i, hiS⟩
      have heval0 : P.eval (α i) = 0 := by
        rw [Polynomial.eval_prod]
        exact Finset.prod_eq_zero hiS' (by simp)
      simp [heval0]
    · have hxi : x i = 0 := by simpa [S] using hiS
      simp [hxi]
  have heval_ne : P.eval (α i₀) ≠ 0 := by
    rw [Polynomial.eval_prod, Finset.prod_ne_zero_iff]
    intro j hj
    rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    exact sub_ne_zero.mpr (hα.ne (Finset.mem_erase.mp hj).1.symm)
  exact mul_ne_zero hi₀ heval_ne (hsum_single.symm.trans hsum_zero)

/-- A `Bool`-additive matrix checksum `(Fin k → Bool) → (Fin outLen → Bool)`. -/
@[ext]
structure LinearBitChecksum (k outLen : ℕ) where
  /-- Matrix over the Boolean ring `Bool` (`xor`, `and`). -/
  matrix : Matrix (Fin outLen) (Fin k) Bool

/-- Evaluate `LinearBitChecksum` by Boolean matrix-vector multiplication. -/
def LinearBitChecksum.eval {k outLen : ℕ} (C : LinearBitChecksum k outLen) (m : Fin k → Bool) :
    Fin outLen → Bool :=
  C.matrix *ᵥ m

private noncomputable def bitAddEquivOfCharTwo {F : Type*} [Field F] [Fintype F] [CharP F 2]
    {s : ℕ} (hcard : Fintype.card F = 2 ^ s) : (Fin s → Bool) ≃+ F :=
  letI : Algebra (ZMod 2) F := ZMod.algebra F 2
  let B := Module.Free.chooseBasis (ZMod 2) F
  have hcardB : Fintype.card F = 2 ^ Fintype.card (Module.Free.ChooseBasisIndex (ZMod 2) F) := by
    have h1 := Fintype.card_congr B.equivFun.toEquiv
    rw [Fintype.card_fun, ZMod.card 2] at h1
    exact h1
  have hidx : Fintype.card (Module.Free.ChooseBasisIndex (ZMod 2) F) = s :=
    Nat.pow_right_injective (by norm_num : 2 ≤ 2) (hcardB.symm.trans hcard)
  let eIdx : Module.Free.ChooseBasisIndex (ZMod 2) F ≃ Fin s :=
    Fintype.equivOfCardEq (by rw [hidx, Fintype.card_fin])
  let eZMod : F ≃+ (Fin s → ZMod 2) :=
    B.equivFun.toAddEquiv.trans (AddEquiv.arrowCongr eIdx (AddEquiv.refl (ZMod 2)))
  (Cslib.BitString.toZModSpace (Fin s)).toAddEquiv.trans eZMod.symm

/-- **Reed–Solomon unique-decoding checksums**: for any finite field `F` with `|F| = 2 ^ s ≥ k`,
there exists a `Bool`-additive `ρ`-unique decoding checksum
`(Fin k → Bool) → (Fin (s * (2 * ρ)) → Bool)`. -/
theorem exists_reedSolomon_uniqueDecodingChecksum {F : Type*} [Field F] [Fintype F]
    (k ρ : ℕ) {s : ℕ} (hcard : Fintype.card F = 2 ^ s)
    (hk : k ≤ Fintype.card F) :
    ∃ C : LinearBitChecksum k (s * (2 * ρ)), IsUniqueDecodingChecksum ρ C.eval := by
  classical
  have hs_pos : 0 < s := by
    have hgt : 1 < Fintype.card F := Fintype.one_lt_card
    by_contra hs
    rw [Nat.eq_zero_of_not_pos hs, pow_zero] at hcard
    omega
  by_cases hρ0 : ρ = 0
  · subst hρ0
    exact ⟨⟨0⟩, isUniqueDecodingChecksum_zero _⟩
  by_cases hsmall : 2 * ρ < k
  · have htwo : (2 : F) = 0 := by
      have hnsmul : Fintype.card F • (1 : F) = 0 := card_nsmul_eq_zero
      rw [hcard, nsmul_one, Nat.cast_pow, Nat.cast_ofNat] at hnsmul
      clear hcard hk hsmall hs_pos
      induction s with
      | zero => simp at hnsmul
      | succ s ih =>
        rw [pow_succ] at hnsmul
        rcases mul_eq_zero.mp hnsmul with h | h
        · exact ih h
        · exact h
    have hringChar : ringChar F = 2 := by
      have hprime : Nat.Prime (ringChar F) := CharP.char_is_prime F (ringChar F)
      have hdvd : ringChar F ∣ 2 := CharP.cast_eq_zero_iff F (ringChar F) 2 |>.mp htwo
      exact (Nat.Prime.dvd_iff_eq Nat.prime_two hprime.ne_one).mp hdvd |>.symm
    have hchar2 : CharP F 2 := hringChar ▸ inferInstance
    let eBit : (Fin s → Bool) ≃+ F := @bitAddEquivOfCharTwo F _ _ hchar2 s hcard
    obtain ⟨α⟩ := Function.Embedding.nonempty_of_card_le (α := Fin k) (β := F) (by simpa using hk)
    let H : Matrix (Fin (2 * ρ)) (Fin k) F := vandermondeParityCheck α (2 * ρ)
    let M : Matrix (Fin (s * (2 * ρ))) (Fin k) Bool :=
      Matrix.of fun idx i ↦
        let p := finProdFinEquiv.symm idx
        eBit.symm (H p.2 i) p.1
    refine ⟨⟨M⟩, ?_⟩
    have heval : ∀ m : Fin k → Bool, ∀ r : Fin (2 * ρ), ∀ b : Fin s,
        (⟨M⟩ : LinearBitChecksum k (s * (2 * ρ))).eval m (finProdFinEquiv (b, r)) =
          eBit.symm ((H *ᵥ fun i ↦ if m i then (1 : F) else 0) r) b := by
      intro m r b
      simp only [LinearBitChecksum.eval, M, Matrix.mulVec, dotProduct, Matrix.of_apply,
        finProdFinEquiv.symm_apply_apply]
      have hmap : eBit.symm (∑ i : Fin k, H r i * (if m i then (1 : F) else 0)) b =
          ∑ i : Fin k, eBit.symm (H r i * (if m i then (1 : F) else 0)) b := by
        rw [map_sum eBit.symm]
        exact Finset.sum_apply b Finset.univ _
      rw [hmap]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      cases hm : m i
      · simp only [Bool.false_eq_true, ↓reduceIte, mul_zero, map_zero, Pi.zero_apply]
        cases eBit.symm (H r i) b <;> rfl
      · simp only [↓reduceIte, mul_one]
        cases eBit.symm (H r i) b <;> rfl
    intro m m' m'' hm' hm'' hne hck
    let v' : Fin k → F := fun i ↦ if m' i then 1 else 0
    let v'' : Fin k → F := fun i ↦ if m'' i then 1 else 0
    have hv_ne : v' ≠ v'' := by
      intro hv
      apply hne
      ext i
      have hi := congrFun hv i
      cases h1 : m' i <;> cases h2 : m'' i <;> simp [v', v'', h1, h2] at hi
      all_goals rfl
    have hHv : H *ᵥ v' = H *ᵥ v'' := by
      ext r
      refine eBit.symm.injective (funext fun b ↦ ?_)
      have hidx := congrFun hck (finProdFinEquiv (b, r))
      rwa [heval m' r b, heval m'' r b] at hidx
    have hker : H *ᵥ (v' - v'') = 0 := by rw [Matrix.mulVec_sub, hHv, sub_self]
    have hnorm : hammingNorm (v' - v'') ≤ 2 * ρ := by
      have htri := hammingDist_triangle m' m m''
      rw [hammingDist_comm m m''] at htri
      have heq_norm : hammingNorm (v' - v'') = hammingDist m' m'' := by
        simp only [hammingNorm, hammingDist]
        congr 1
        ext i
        cases h1 : m' i <;> cases h2 : m'' i <;> simp [v', v'', h1, h2]
      omega
    have hmin := lt_minDist_vandermondeParityCheck α.injective (2 * ρ)
    have hgt := (lt_minDist_parityCheckCode_iff H).mp hmin (v' - v'')
      (sub_ne_zero.mpr hv_ne) hker
    exact absurd hgt (not_lt.mpr hnorm)
  · push Not at hsmall
    have hk_le : k ≤ s * (2 * ρ) :=
      hsmall.trans (by simpa using Nat.mul_le_mul_right (2 * ρ) hs_pos)
    let M : Matrix (Fin (s * (2 * ρ))) (Fin k) Bool :=
      Matrix.of fun idx i ↦ decide ((idx : ℕ) = (i : ℕ))
    refine ⟨⟨M⟩, isUniqueDecodingChecksum_of_injective ρ fun m₁ m₂ heq ↦ ?_⟩
    ext i
    let idx : Fin (s * (2 * ρ)) := ⟨i.val, lt_of_lt_of_le i.isLt hk_le⟩
    have hidx := congrFun heq idx
    have eval_at (m : Fin k → Bool) :
        (⟨M⟩ : LinearBitChecksum k (s * (2 * ρ))).eval m idx = m i := by
      simp only [LinearBitChecksum.eval, M, Matrix.mulVec, dotProduct, Matrix.of_apply, idx]
      rw [Finset.sum_eq_single i]
      · simp only [decide_true]
        cases m i <;> rfl
      · intro j _ hji
        simp only [Fin.val_ne_of_ne hji.symm, decide_false]
        cases m j <;> rfl
      · intro hi
        exact absurd (Finset.mem_univ i) hi
    rwa [eval_at m₁, eval_at m₂] at hidx

end Cslib.Code
