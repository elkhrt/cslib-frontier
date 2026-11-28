module

public import CslibFrontier.Foundations.Data.BitString.Basic
public import Mathlib.Data.ZMod.Basic

import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.Ring

/-!
# Sipser Isolating Linear Hash Families over `GF(2)`

This module formalizes Sipser's isolating linear hashing lemma over `GF(2)` for subsets
`S ⊆ {0, 1}^N`:

* **Soundness** (`card_le_of_isIsolatingHash`): if a `t`-tuple of `m × N` binary matrices isolates
  every point of `S`, then `#S ≤ t * 2^m`.
* **Completeness** (`exists_isIsolatingHash`): if `#S ≤ M` and `8 * M ≤ 2^m`, then there exists an
  `(N + 1)`-tuple of `m × N` binary matrices isolating every point of `S`.

## Main definitions

* `CslibFrontier.Computability.Complexity.SipserIsolation.boolToZ2`, `matVecZ2`:
  matrix-vector multiplication over `GF(2)` for binary matrices on `BitString N`.
* `CslibFrontier.Computability.Complexity.SipserIsolation.IsIsolatingHash`:
  the Sipser isolation property for a family of linear hash maps.

## Main results

* `CslibFrontier.Computability.Complexity.SipserIsolation.card_le_of_isIsolatingHash`:
  upper bound on the cardinality of any isolated set.
* `CslibFrontier.Computability.Complexity.SipserIsolation.exists_isIsolatingHash`:
  existence of isolating hash families for bounded-size subsets.
-/

public section

namespace CslibFrontier.Computability.Complexity.SipserIsolation

open Cslib Cslib.BitString Finset

/-- Embedding `Bool → ZMod 2` sending `false ↦ 0` and `true ↦ 1`. -/
def boolToZ2 (b : Bool) : ZMod 2 := if b then 1 else 0

/-- Matrix-vector product `(A * x) : Fin m → ZMod 2` over `GF(2)`. -/
def matVecZ2 {m N : ℕ} (A : Fin m → Fin N → Bool) (x : BitString N) : Fin m → ZMod 2 :=
  fun i => ∑ j : Fin N, boolToZ2 (A i j) * boolToZ2 (x j)

/-- A `t`-tuple of `m × N` binary matrices `H` isolates `S ⊆ {0,1}^N` if every `u ∈ S` is
mapped distinctly from every other `v ∈ S` by at least one matrix `H i`. -/
def IsIsolatingHash {t m N : ℕ} (H : Fin t → Fin m → Fin N → Bool)
    (S : Finset (BitString N)) : Prop :=
  ∀ u ∈ S, ∃ i : Fin t, ∀ v ∈ S, v ≠ u → matVecZ2 (H i) u ≠ matVecZ2 (H i) v

/-- **Sipser soundness:** any set isolated by `t` matrices of `m` rows has size at most
`t * 2 ^ m`. -/
theorem card_le_of_isIsolatingHash {t m N : ℕ} {H : Fin t → Fin m → Fin N → Bool}
    {S : Finset (BitString N)} (hiso : IsIsolatingHash H S) :
    #S ≤ t * 2 ^ m := by
  classical
  have hchoose : ∀ u : {u : BitString N // u ∈ S},
      ∃ i : Fin t, ∀ v ∈ S, v ≠ u.1 → matVecZ2 (H i) u.1 ≠ matVecZ2 (H i) v :=
    fun u => hiso u.1 u.2
  choose idx hidx using hchoose
  let φ : {u : BitString N // u ∈ S} → Fin t × (Fin m → ZMod 2) :=
    fun u => (idx u, matVecZ2 (H (idx u)) u.1)
  have hinj : Function.Injective φ := by
    intro u₁ u₂ heq
    simp only [φ, Prod.mk.injEq] at heq
    obtain ⟨hi, hv⟩ := heq
    by_contra hne
    have hval : u₂.1 ≠ u₁.1 := fun h => hne (Subtype.ext h.symm)
    rw [← hi] at hv
    exact hidx u₁ u₂.1 u₂.2 hval hv
  have hle := Fintype.card_le_of_injective φ hinj
  simpa [Fintype.card_coe, Fintype.card_prod, Fintype.card_fun, ZMod.card] using hle

private lemma boolToZ2_sub_eq_one_of_ne {a b : Bool} (h : a ≠ b) :
    boolToZ2 a - boolToZ2 b = 1 := by
  cases a <;> cases b <;> simp [boolToZ2] at h ⊢

private lemma boolToZ2_injective : Function.Injective boolToZ2 := by
  intro a b h
  cases a <;> cases b <;> simp [boolToZ2] at h ⊢

private lemma boolToZ2_surjective : Function.Surjective boolToZ2 := by
  intro z
  fin_cases z
  · exact ⟨false, rfl⟩
  · exact ⟨true, rfl⟩

private lemma boolToZ2_decide_eq_one (z : ZMod 2) :
    boolToZ2 (decide (z = 1)) = z := by
  obtain ⟨b, rfl⟩ := boolToZ2_surjective z
  cases b <;> rfl

private lemma zmod2_eq_of_decide_eq_one {a b : ZMod 2}
    (h : decide (a = 1) = decide (b = 1)) : a = b := by
  obtain ⟨x, rfl⟩ := boolToZ2_surjective a
  obtain ⟨y, rfl⟩ := boolToZ2_surjective b
  cases x <;> cases y <;> simp_all [boolToZ2]

/-- Exact pairwise collision count over uniformly random `m × N` binary matrices: for any
distinct `u ≠ v`, exactly `1 / 2^m` of all matrices satisfy `A u = A v`. -/
private lemma two_pow_mul_card_matVecZ2_eq {m N : ℕ} {u v : BitString N} (huv : u ≠ v) :
    2 ^ m * #{A : Fin m → Fin N → Bool | matVecZ2 A u = matVecZ2 A v} =
      Fintype.card (Fin m → Fin N → Bool) := by
  classical
  have hex : ∃ j₀ : Fin N, u j₀ ≠ v j₀ := by
    by_contra h
    push Not at h
    exact huv (funext h)
  obtain ⟨j₀, hj₀⟩ := hex
  have hdiff : boolToZ2 (u j₀) - boolToZ2 (v j₀) = 1 := boolToZ2_sub_eq_one_of_ne hj₀
  -- Split a matrix `A` into column `j₀` and all remaining columns `j ≠ j₀`.
  let Rest := Fin m → {j : Fin N // j ≠ j₀} → Bool
  let targetZ2 (R : Rest) (i : Fin m) : ZMod 2 :=
    -(∑ j : {j : Fin N // j ≠ j₀}, boolToZ2 (R i j) * (boolToZ2 (u j.1) - boolToZ2 (v j.1)))
  let targetCol (R : Rest) : Fin m → Bool := fun i => decide (targetZ2 R i = 1)
  have htarget_val (R : Rest) (i : Fin m) : boolToZ2 (targetCol R i) = targetZ2 R i :=
    boolToZ2_decide_eq_one (targetZ2 R i)
  let buildMat (R : Rest) : Fin m → Fin N → Bool :=
    fun i j => if h : j = j₀ then targetCol R i else R i ⟨j, h⟩
  have hbuild_col (A : Fin m → Fin N → Bool) :
      matVecZ2 A u = matVecZ2 A v ↔
        A = buildMat (fun i j => A i j.1) := by
    have hrow (i : Fin m) :
        matVecZ2 A u i = matVecZ2 A v i ↔
          A i j₀ = targetCol (fun i j => A i j.1) i := by
      have hsub : matVecZ2 A u i - matVecZ2 A v i =
          boolToZ2 (A i j₀) +
            ∑ j : {j : Fin N // j ≠ j₀},
              boolToZ2 (A i j.1) * (boolToZ2 (u j.1) - boolToZ2 (v j.1)) := by
        simp only [matVecZ2, ← Finset.sum_sub_distrib, ← mul_sub]
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j₀), hdiff, mul_one]
        congr 1
        refine Finset.sum_bij (fun j hj => ⟨j, (Finset.mem_erase.mp hj).1⟩)
          (fun _ _ => Finset.mem_univ _) (fun _ _ _ _ h => congrArg Subtype.val h)
          (fun j _ => ⟨j.1, Finset.mem_erase.mpr ⟨j.2, Finset.mem_univ _⟩, rfl⟩)
          (fun _ _ => rfl)
      rw [← sub_eq_zero, hsub, add_eq_zero_iff_eq_neg]
      change boolToZ2 (A i j₀) = targetZ2 (fun i j => A i j.1) i ↔ _
      rw [← htarget_val (fun i j => A i j.1) i]
      exact boolToZ2_injective.eq_iff
    constructor
    · intro h
      funext i j
      by_cases hj : j = j₀
      · subst hj
        simp only [buildMat, ↓reduceDIte]
        exact (hrow i).mp (congrFun h i)
      · simp [buildMat, hj]
    · intro h
      funext i
      rw [hrow i]
      have := congrFun (congrFun h i) j₀
      simpa [buildMat] using this
  have hbij : #{A : Fin m → Fin N → Bool | matVecZ2 A u = matVecZ2 A v} = Fintype.card Rest := by
    refine Finset.card_bij (fun A _ => fun i (j : {j : Fin N // j ≠ j₀}) => A i j.1)
      (fun _ _ => Finset.mem_univ _)
      (fun A₁ h₁ A₂ h₂ h => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h₁ h₂
        rw [(hbuild_col A₁).mp h₁, (hbuild_col A₂).mp h₂, h])
      (fun R _ => ⟨buildMat R, ?_, by funext i j; simp [buildMat, j.2]⟩)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hbuild_col (buildMat R)]
    have hrest : (fun i (j : {j : Fin N // j ≠ j₀}) => buildMat R i j.1) = R := by
      funext i j; simp [buildMat, j.2]
    rw [hrest]
  rw [hbij]
  have hcard_sub : Fintype.card {j : Fin N // j ≠ j₀} + 1 = N := by
    have h1 : Fintype.card {j : Fin N // j ≠ j₀} = (Finset.univ.erase j₀).card := by
      rw [Fintype.card_subtype]
      congr 1; ext j; simp
    rw [h1, Finset.card_erase_of_mem (Finset.mem_univ j₀), Finset.card_univ, Fintype.card_fin]
    have hN : 1 ≤ N := Fin.pos j₀
    omega
  have hcard_rest : Fintype.card Rest = 2 ^ (m * Fintype.card {j : Fin N // j ≠ j₀}) := by
    simp only [Rest, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, ← pow_mul, mul_comm]
  have hcard_mat : Fintype.card (Fin m → Fin N → Bool) = 2 ^ (m * N) := by
    simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, ← pow_mul, mul_comm]
  rw [hcard_rest, hcard_mat, ← pow_add]
  congr 1
  have : m + m * Fintype.card {j : Fin N // j ≠ j₀} =
      m * (Fintype.card {j : Fin N // j ≠ j₀} + 1) := by ring
  rw [this, hcard_sub]

/-- **Sipser completeness:** for any `S ⊆ {0,1}^N` with `#S ≤ M`, if `8 * M ≤ 2 ^ m` and
`t = N + 1`, then there exists a `t`-tuple of `m × N` binary matrices isolating `S`. -/
theorem exists_isIsolatingHash {m N M : ℕ} {S : Finset (BitString N)}
    (hSM : #S ≤ M) (hm : 8 * M ≤ 2 ^ m) :
    ∃ H : Fin (N + 1) → Fin m → Fin N → Bool, IsIsolatingHash H S := by
  classical
  let Mat := Fin m → Fin N → Bool
  let t := N + 1
  let BadSingle (u : BitString N) : Finset Mat :=
    Finset.univ.filter fun A => ∃ v ∈ S, v ≠ u ∧ matVecZ2 A u = matVecZ2 A v
  have hbad_single (u : BitString N) : 8 * #(BadSingle u) ≤ Fintype.card Mat := by
    have hsub : BadSingle u ⊆ (S.erase u).biUnion
        (fun v => Finset.univ.filter fun A : Mat => matVecZ2 A u = matVecZ2 A v) := by
      intro A hA
      simp only [BadSingle, Finset.mem_filter, Finset.mem_univ, true_and] at hA
      obtain ⟨v, hvS, hvu, heq⟩ := hA
      exact Finset.mem_biUnion.mpr ⟨v, Finset.mem_erase.mpr ⟨hvu, hvS⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, heq⟩⟩
    have hcard_le : 2 ^ m * #(BadSingle u) ≤ #(S.erase u) * Fintype.card Mat := by
      calc 2 ^ m * #(BadSingle u)
          ≤ 2 ^ m * ∑ v ∈ S.erase u, #{A : Mat | matVecZ2 A u = matVecZ2 A v} :=
            Nat.mul_le_mul_left _ ((Finset.card_le_card hsub).trans Finset.card_biUnion_le)
        _ = ∑ v ∈ S.erase u, (2 ^ m * #{A : Mat | matVecZ2 A u = matVecZ2 A v}) :=
            Finset.mul_sum _ _ _
        _ = ∑ _v ∈ S.erase u, Fintype.card Mat :=
            Finset.sum_congr rfl fun v hv =>
              two_pow_mul_card_matVecZ2_eq (Finset.mem_erase.mp hv).1.symm
        _ = #(S.erase u) * Fintype.card Mat := by simp
    have hM_le : #(S.erase u) ≤ M := (Finset.card_erase_le).trans hSM
    have h1 : 2 ^ m * #(BadSingle u) ≤ M * Fintype.card Mat :=
      hcard_le.trans (Nat.mul_le_mul_right _ hM_le)
    have h2 : 8 * M * #(BadSingle u) ≤ 2 ^ m * #(BadSingle u) := Nat.mul_le_mul_right _ hm
    by_cases hM0 : M = 0
    · subst hM0
      have hS0 : S = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hSM)
      have hb0 : BadSingle u = ∅ := by
        ext A; simp [BadSingle, hS0]
      simp [hb0]
    · have hMpos : 0 < M := Nat.pos_of_ne_zero hM0
      have h3 : M * (8 * #(BadSingle u)) ≤ M * Fintype.card Mat := by
        calc M * (8 * #(BadSingle u)) = 8 * M * #(BadSingle u) := by ring
          _ ≤ M * Fintype.card Mat := h2.trans h1
      exact Nat.le_of_mul_le_mul_left h3 hMpos
  let BadTuple (u : BitString N) : Finset (Fin t → Mat) :=
    Fintype.piFinset fun _ : Fin t => BadSingle u
  have hbad_tuple (u : BitString N) : 8 ^ t * #(BadTuple u) ≤ Fintype.card (Fin t → Mat) := by
    have hcard : #(BadTuple u) = (#(BadSingle u)) ^ t := by
      simp [BadTuple, Fintype.card_piFinset]
    rw [hcard, ← mul_pow, Fintype.card_fun, Fintype.card_fin]
    exact Nat.pow_le_pow_left (hbad_single u) t
  let BadAll : Finset (Fin t → Mat) := S.biUnion BadTuple
  have hbad_all : 8 ^ t * #BadAll ≤ #S * Fintype.card (Fin t → Mat) := by
    calc 8 ^ t * #BadAll
        ≤ 8 ^ t * ∑ u ∈ S, #(BadTuple u) := Nat.mul_le_mul_left _ Finset.card_biUnion_le
      _ = ∑ u ∈ S, (8 ^ t * #(BadTuple u)) := Finset.mul_sum _ _ _
      _ ≤ ∑ _u ∈ S, Fintype.card (Fin t → Mat) := Finset.sum_le_sum fun u _ => hbad_tuple u
      _ = #S * Fintype.card (Fin t → Mat) := by simp
  have hS_le_2N : #S ≤ 2 ^ N := (Finset.card_le_univ S).trans_eq (by simp [BitString])
  have h2N_lt_8t : 2 ^ N < 8 ^ t := by
    have h1 : 2 ^ N ≤ 8 ^ N := Nat.pow_le_pow_left (by norm_num) N
    have h2 : 8 ^ N < 8 ^ (N + 1) := by
      rw [pow_succ]; have := Nat.one_le_pow N 8 (by norm_num); omega
    exact lt_of_le_of_lt h1 h2
  have hcard_pos : 0 < Fintype.card (Fin t → Mat) := Fintype.card_pos
  have hlt : #BadAll < Fintype.card (Fin t → Mat) := by
    have h1 : 8 ^ t * #BadAll < 8 ^ t * Fintype.card (Fin t → Mat) :=
      lt_of_le_of_lt (hbad_all.trans (Nat.mul_le_mul_right _ hS_le_2N))
        (Nat.mul_lt_mul_of_pos_right h2N_lt_8t hcard_pos)
    exact Nat.lt_of_mul_lt_mul_left h1
  have hne : (Finset.univ \ BadAll).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hemp
    have hsub : (Finset.univ : Finset (Fin t → Mat)) ⊆ BadAll :=
      Finset.sdiff_eq_empty_iff_subset.mp hemp
    have := Finset.card_le_card hsub
    rw [Finset.card_univ] at this
    omega
  obtain ⟨H, hH⟩ := hne
  have hnotbad : H ∉ BadAll := (Finset.mem_sdiff.mp hH).2
  refine ⟨H, fun u hu => ?_⟩
  have hnt : H ∉ BadTuple u := fun h => hnotbad (Finset.mem_biUnion.mpr ⟨u, hu, h⟩)
  simp only [BadTuple, Fintype.mem_piFinset, not_forall] at hnt
  obtain ⟨i, hi⟩ := hnt
  simp only [BadSingle, Finset.mem_filter, Finset.mem_univ, true_and, not_exists, not_and] at hi
  exact ⟨i, fun v hvS hvu => hi v hvS hvu⟩


end CslibFrontier.Computability.Complexity.SipserIsolation
