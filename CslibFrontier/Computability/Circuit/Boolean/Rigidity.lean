module

public import CslibFrontier.Computability.Circuit.Boolean.NaturalProof
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Positivity

/-!
# Rigidity Hierarchy for Boolean Function Properties

Defines the five-tier rigidity hierarchy for Boolean function properties (`IsNonrigid`,
`IsMildlyRigid`, `IsStronglyMildlyRigid`, `IsRigid`, `IsStronglyRigid`, `IsExtremelyRigid`) and
connects it to the Razborov–Rudich natural proofs framework (`Cslib.Circuits.Boolean.NaturalProof`).

## Main definitions

* `CslibFrontier.Computability.Circuit.Boolean.IsNonrigid`: truth-table density at least
  `2 ^ N / N ^ c` for some `c` (equivalent to `Cslib.Circuits.Boolean.NaturalProof.IsLarge`).
* `CslibFrontier.Computability.Circuit.Boolean.IsMildlyRigid`, `IsStronglyMildlyRigid`:
  sub-polynomially (resp. sub-quasipolynomially) dense properties `|UP_n| ≤ 2 ^ N / N ^ c`
  (resp. `2 ^ N / 2 ^ (n ^ a)` with `1 < a`).
* `CslibFrontier.Computability.Circuit.Boolean.IsRigid`: `|UP_n| ≤ 2 ^ (ε * N)` for some
  `0 ≤ ε < 1`.
* `CslibFrontier.Computability.Circuit.Boolean.IsStronglyRigid`: `|UP_n| ≤ 2 ^ (N ^ ε)` for some
  `0 ≤ ε < 1`.
* `CslibFrontier.Computability.Circuit.Boolean.IsExtremelyRigid`: `|UP_n| ≤ 2 ^ (n ^ a)` for some
  `a > 0`.

## Main results

* `isNonrigid_iff_isLarge`: `IsNonrigid` coincides with `NaturalProof.IsLarge`.
* `IsExtremelyRigid.isStronglyRigid`, `IsStronglyRigid.isRigid`,
  `IsRigid.isStronglyMildlyRigid`, `IsStronglyMildlyRigid.isMildlyRigid`: containment chain.
* `IsMildlyRigid.not_isLarge`, `IsMildlyRigid.not_isNatural`: every mildly rigid property fails
  Razborov–Rudich largeness and therefore cannot form a natural proof.
* `exists_isStronglyMildlyRigid_not_isRigid`, `exists_isRigid_not_isStronglyRigid`,
  `exists_isStronglyRigid_not_isExtremelyRigid`: strict separation witnesses across all tiers.
-/

public section

namespace CslibFrontier.Computability.Circuit.Boolean

open Filter Topology
open Cslib Cslib.Circuits.Boolean

section Definitions

variable (UP : ∀ n, Set (BooleanFunction n))

/-- A Boolean function property `UP` is *nonrigid* if for some constant `c`, eventually
`|UP_n| ≥ 2 ^ N / N ^ c` where `N = 2 ^ n` is the truth-table length. -/
def IsNonrigid : Prop :=
  ∃ c : ℕ, ∀ᶠ n in atTop, 2 ^ 2 ^ n ≤ 2 ^ (c * n) * (UP n).ncard

/-- A Boolean function property `UP` is *mildly rigid* if for every constant `c`, eventually
`|UP_n| ≤ 2 ^ N / N ^ c`. -/
def IsMildlyRigid : Prop :=
  ∀ c : ℕ, ∀ᶠ n in atTop, 2 ^ (c * n) * (UP n).ncard ≤ 2 ^ 2 ^ n

/-- The stronger form of mild rigidity:
there exists `a > 1` such that eventually `|UP_n| ≤ 2 ^ N / 2 ^ (n ^ a)`.
(Note: `a = 1` gives `2 ^ N / N`, which is nonrigid with `c = 1`.) -/
def IsStronglyMildlyRigid : Prop :=
  ∃ a : ℕ, 1 < a ∧ ∀ᶠ n in atTop, 2 ^ (n ^ a) * (UP n).ncard ≤ 2 ^ 2 ^ n

/-- A Boolean function property `UP` is *rigid* if for some `0 ≤ ε < 1`, eventually
`|UP_n| ≤ 2 ^ (ε * N)`. -/
def IsRigid : Prop :=
  ∃ ε : ℝ, 0 ≤ ε ∧ ε < 1 ∧ ∀ᶠ n in atTop, ((UP n).ncard : ℝ) ≤ (2 : ℝ) ^ (ε * (2 ^ n : ℝ))

/-- A Boolean function property `UP` is *strongly rigid* if for some `0 ≤ ε < 1`, eventually
`|UP_n| ≤ 2 ^ (N ^ ε)`. -/
def IsStronglyRigid : Prop :=
  ∃ ε : ℝ, 0 ≤ ε ∧ ε < 1 ∧ ∀ᶠ n in atTop, ((UP n).ncard : ℝ) ≤ (2 : ℝ) ^ ((2 ^ n : ℝ) ^ ε)

/-- A Boolean function property `UP` is *extremely rigid* if for some `a > 0`, eventually
`|UP_n| ≤ 2 ^ (n ^ a)`. -/
def IsExtremelyRigid : Prop :=
  ∃ a : ℕ, 0 < a ∧ ∀ᶠ n in atTop, (UP n).ncard ≤ 2 ^ (n ^ a)

end Definitions

section Hierarchy

variable {UP UP' : ∀ n, Set (BooleanFunction n)}

/-- `IsNonrigid` is identical to Razborov–Rudich largeness `NaturalProof.IsLarge`. -/
theorem isNonrigid_iff_isLarge : IsNonrigid UP ↔ NaturalProof.IsLarge UP :=
  Iff.rfl

/-- Nonrigidity is upward-closed under inclusion. -/
theorem IsNonrigid.mono (h : IsNonrigid UP) (hsub : ∀ n, UP n ⊆ UP' n) : IsNonrigid UP' :=
  NaturalProof.IsLarge.mono h hsub

/-- Mild rigidity is downward-closed under inclusion. -/
theorem IsMildlyRigid.anti (h : IsMildlyRigid UP) (hsub : ∀ n, UP' n ⊆ UP n) :
    IsMildlyRigid UP' := fun c =>
  (h c).mono fun n hn =>
    (Nat.mul_le_mul_left _ (Set.ncard_le_ncard (hsub n))).trans hn

/-- Strong mild rigidity is downward-closed under inclusion. -/
theorem IsStronglyMildlyRigid.anti (h : IsStronglyMildlyRigid UP) (hsub : ∀ n, UP' n ⊆ UP n) :
    IsStronglyMildlyRigid UP' :=
  let ⟨a, ha, hfa⟩ := h
  ⟨a, ha, hfa.mono fun n hn =>
    (Nat.mul_le_mul_left _ (Set.ncard_le_ncard (hsub n))).trans hn⟩

/-- Rigidity is downward-closed under inclusion. -/
theorem IsRigid.anti (h : IsRigid UP) (hsub : ∀ n, UP' n ⊆ UP n) : IsRigid UP' :=
  let ⟨ε, h0, h1, hfe⟩ := h
  ⟨ε, h0, h1, hfe.mono fun n hn =>
    (Nat.cast_le.mpr (Set.ncard_le_ncard (hsub n))).trans hn⟩

/-- Strong rigidity is downward-closed under inclusion. -/
theorem IsStronglyRigid.anti (h : IsStronglyRigid UP) (hsub : ∀ n, UP' n ⊆ UP n) :
    IsStronglyRigid UP' :=
  let ⟨ε, h0, h1, hfe⟩ := h
  ⟨ε, h0, h1, hfe.mono fun n hn =>
    (Nat.cast_le.mpr (Set.ncard_le_ncard (hsub n))).trans hn⟩

/-- Extreme rigidity is downward-closed under inclusion. -/
theorem IsExtremelyRigid.anti (h : IsExtremelyRigid UP) (hsub : ∀ n, UP' n ⊆ UP n) :
    IsExtremelyRigid UP' :=
  let ⟨a, ha, hfa⟩ := h
  ⟨a, ha, hfa.mono fun n hn => (Set.ncard_le_ncard (hsub n)).trans hn⟩

/-- Every mildly rigid property fails Razborov–Rudich largeness. -/
theorem IsMildlyRigid.not_isLarge (h : IsMildlyRigid UP) : ¬ NaturalProof.IsLarge UP := by
  rintro ⟨c, hc⟩
  have hlt := (hc.and (h (c + 1))).and (eventually_ge_atTop 1)
  obtain ⟨n, ⟨hlarge, hmild⟩, hn1⟩ := hlt.exists
  have hpos : 0 < (UP n).ncard := by
    by_contra h0
    have hcard : (UP n).ncard = 0 := Nat.eq_zero_of_not_pos h0
    rw [hcard, mul_zero] at hlarge
    exact absurd hlarge (not_le_of_gt (by positivity))
  have h1 : 2 ^ ((c + 1) * n) * (UP n).ncard ≤ 2 ^ (c * n) * (UP n).ncard :=
    hmild.trans hlarge
  have h2 : 2 ^ ((c + 1) * n) ≤ 2 ^ (c * n) := Nat.le_of_mul_le_mul_right h1 hpos
  have h3 : (c + 1) * n ≤ c * n := (Nat.pow_le_pow_iff_right (by omega : 1 < 2)).mp h2
  have : c * n + n ≤ c * n := by rwa [Nat.add_mul, one_mul] at h3
  omega

/-- Every mildly rigid property fails to be `Γ`-natural for any class `Γ`. -/
theorem IsMildlyRigid.not_isNatural (h : IsMildlyRigid UP) (Γ : Set (Language Bool)) :
    ¬ NaturalProof.IsNatural Γ UP := by
  rintro ⟨D, hDU, hlarge, -⟩
  exact h.not_isLarge (hlarge.mono hDU)

private lemma tendsto_pow_div_two_rpow_half (a : ℕ) :
    Tendsto (fun n : ℕ => ((n : ℝ) ^ a) / (2 : ℝ) ^ ((n : ℝ) / 2)) atTop (𝓝 0) := by
  have hbase : (1 : ℝ) < (2 : ℝ) ^ ((1 : ℝ) / 2) := by
    rw [Real.one_lt_rpow_iff_of_pos (by norm_num : (0 : ℝ) < 2)]
    left
    norm_num
  have hlim := tendsto_pow_const_div_const_pow_of_one_lt a hbase
  refine hlim.congr fun n => ?_
  have hpow : ((2 : ℝ) ^ ((1 : ℝ) / 2)) ^ n = (2 : ℝ) ^ ((n : ℝ) / 2) := by
    rw [← Real.rpow_natCast ((2 : ℝ) ^ ((1 : ℝ) / 2)) n, ← Real.rpow_mul (by norm_num)]
    ring_nf
  rw [hpow]

private lemma tendsto_sq_div_two_pow :
    Tendsto (fun n : ℕ => ((n ^ 2 : ℕ) : ℝ) / ((2 : ℝ) ^ n)) atTop (𝓝 0) := by
  simpa only [Nat.cast_pow] using
    tendsto_pow_const_div_const_pow_of_one_lt 2 (by norm_num : (1 : ℝ) < 2)

private lemma sq_le_two_pow_of_four_le {n : ℕ} (hn : 4 ≤ n) : n ^ 2 ≤ 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
    have h1 : (m + 1) ^ 2 ≤ 2 * m ^ 2 := by nlinarith
    calc (m + 1) ^ 2 ≤ 2 * m ^ 2 := h1
      _ ≤ 2 * 2 ^ m := Nat.mul_le_mul_left 2 ih
      _ = 2 ^ (m + 1) := by ring

/-- Every extremely rigid property is strongly rigid. -/
theorem IsExtremelyRigid.isStronglyRigid (h : IsExtremelyRigid UP) : IsStronglyRigid UP := by
  obtain ⟨a, _, hfa⟩ := h
  refine ⟨1 / 2, by norm_num, by norm_num, ?_⟩
  have hev := (tendsto_pow_div_two_rpow_half a).eventually (Iio_mem_nhds one_pos)
  filter_upwards [hfa, hev] with n hn hlt
  have hpos : (0 : ℝ) < (2 : ℝ) ^ ((n : ℝ) / 2) := by positivity
  have hpow : ((n ^ a : ℕ) : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) / 2) := by
    rw [Nat.cast_pow]
    exact (div_le_one hpos).mp (le_of_lt hlt)
  have h1 : ((UP n).ncard : ℝ) ≤ (2 : ℝ) ^ ((n ^ a : ℕ) : ℝ) := by
    rw [Real.rpow_natCast]
    exact_mod_cast hn
  have h2 : (2 : ℝ) ^ ((n : ℝ) / 2) = ((2 : ℝ) ^ n) ^ ((1 : ℝ) / 2) := by
    rw [← Real.rpow_natCast (2 : ℝ) n, ← Real.rpow_mul (by norm_num)]
    ring_nf
  rw [h2] at hpow
  exact h1.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) hpow)

/-- Every strongly rigid property is rigid. -/
theorem IsStronglyRigid.isRigid (h : IsStronglyRigid UP) : IsRigid UP := by
  obtain ⟨ε, h0, h1, hfe⟩ := h
  refine ⟨1 / 2, by norm_num, by norm_num, ?_⟩
  have hdiff : 0 < 1 - ε := by linarith
  have hlim : Tendsto (fun n : ℕ => ((2 : ℝ) ^ n) ^ (1 - ε)) atTop atTop :=
    (tendsto_rpow_atTop hdiff).comp
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2))
  have hev := hlim.eventually_ge_atTop (2 : ℝ)
  filter_upwards [hfe, hev] with n hn hge
  have hpos : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have hexp : ((2 : ℝ) ^ n) ^ ε ≤ (1 / 2 : ℝ) * (2 : ℝ) ^ n := by
    have hsplit : ((2 : ℝ) ^ n) ^ ε * ((2 : ℝ) ^ n) ^ (1 - ε) = (2 : ℝ) ^ n := by
      rw [← Real.rpow_add hpos]
      ring_nf
      exact Real.rpow_one _
    have h2 : ((2 : ℝ) ^ n) ^ ε * 2 ≤ ((2 : ℝ) ^ n) ^ ε * ((2 : ℝ) ^ n) ^ (1 - ε) :=
      mul_le_mul_of_nonneg_left hge (by positivity)
    rw [hsplit] at h2
    linarith
  exact hn.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp)

/-- Every rigid property is strongly mildly rigid. -/
theorem IsRigid.isStronglyMildlyRigid (h : IsRigid UP) : IsStronglyMildlyRigid UP := by
  obtain ⟨ε, _, h1, hfe⟩ := h
  refine ⟨2, by omega, ?_⟩
  have hgap : 0 < 1 - ε := by linarith
  have hev := tendsto_sq_div_two_pow.eventually (Iio_mem_nhds hgap)
  filter_upwards [hfe, hev] with n hn hdiv
  have hpos : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have hle : ((n ^ 2 : ℕ) : ℝ) ≤ (1 - ε) * (2 : ℝ) ^ n :=
    (div_le_iff₀ hpos).mp (le_of_lt hdiv)
  have hreal : ((2 ^ (n ^ 2) * (UP n).ncard : ℕ) : ℝ) ≤ ((2 ^ 2 ^ n : ℕ) : ℝ) := by
    push_cast
    calc
      (2 : ℝ) ^ (n ^ 2) * ((UP n).ncard : ℝ)
          ≤ (2 : ℝ) ^ (n ^ 2) * (2 : ℝ) ^ (ε * (2 : ℝ) ^ n) :=
        mul_le_mul_of_nonneg_left hn (by positivity)
      _ = (2 : ℝ) ^ (((n ^ 2 : ℕ) : ℝ) + ε * (2 : ℝ) ^ n) := by
        rw [← Real.rpow_natCast (2 : ℝ) (n ^ 2), ← Real.rpow_add (by norm_num)]
      _ ≤ (2 : ℝ) ^ ((2 : ℝ) ^ n) := by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        linarith
      _ = (2 : ℝ) ^ (2 ^ n) := by
        rw [← Real.rpow_natCast (2 : ℝ) (2 ^ n), Nat.cast_pow, Nat.cast_ofNat]
  exact_mod_cast hreal

/-- Every strongly mildly rigid property is mildly rigid. -/
theorem IsStronglyMildlyRigid.isMildlyRigid (h : IsStronglyMildlyRigid UP) :
    IsMildlyRigid UP := by
  obtain ⟨a, ha, hfa⟩ := h
  intro c
  filter_upwards [hfa, eventually_ge_atTop (max c 1)] with n hn hnc
  have hpow : c * n ≤ n ^ a := by
    have h1 : c * n ≤ n * n := Nat.mul_le_mul_right n (le_trans (le_max_left _ _) hnc)
    have h2 : n * n = n ^ 2 := (sq n).symm
    have h3 : n ^ 2 ≤ n ^ a := Nat.pow_le_pow_right (le_trans (le_max_right _ _) hnc) ha
    omega
  exact (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) hpow)).trans hn

/-- Every extremely rigid property bypasses the Razborov–Rudich natural proofs barrier. -/
theorem IsExtremelyRigid.not_isNatural (h : IsExtremelyRigid UP) (Γ : Set (Language Bool)) :
    ¬ NaturalProof.IsNatural Γ UP :=
  h.isStronglyRigid.isRigid.isStronglyMildlyRigid.isMildlyRigid.not_isNatural Γ

end Hierarchy

section Separations

/-- Truth-table prefix constraint: Boolean functions vanishing on the first `k n` inputs
under the canonical `BitString n ≃ Fin (2 ^ n)` indexing. -/
noncomputable def zeroPrefixProperty (k : ℕ → ℕ) (n : ℕ) : Set (BooleanFunction n) :=
  {f | ∀ x : BitString n, (Fintype.equivFin (BitString n) x).val < k n → f x = false}

/-- The cardinality of `zeroPrefixProperty k n` is `2 ^ (2 ^ n - k n)`. -/
theorem ncard_zeroPrefixProperty (k : ℕ → ℕ) (n : ℕ) :
    (zeroPrefixProperty k n).ncard = 2 ^ (2 ^ n - k n) := by
  classical
  let eB : BitString n ≃ Fin (2 ^ n) :=
    (Fintype.equivFin (BitString n)).trans
      (finCongr (by rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]))
  have hfin : ∀ x : BitString n,
      (Fintype.equivFin (BitString n) x).val = (eB x).val := fun _ => rfl
  let S : Set (Fin (2 ^ n) → Bool) := {T | ∀ i : Fin (2 ^ n), i.val < k n → T i = false}
  have heq : (zeroPrefixProperty k n).ncard = S.ncard := by
    let eFun : BooleanFunction n ≃ (Fin (2 ^ n) → Bool) := Equiv.arrowCongr eB (Equiv.refl Bool)
    have hbij : zeroPrefixProperty k n = eFun.symm '' S := by
      ext f
      simp only [zeroPrefixProperty, Set.mem_ofPred_eq, Set.mem_image, S, eFun]
      constructor
      · intro hf
        refine ⟨eFun f, fun i hi => ?_, eFun.symm_apply_apply f⟩
        exact hf (eB.symm i) (by rw [hfin, Equiv.apply_symm_apply]; exact hi)
      · rintro ⟨g, hg, rfl⟩ x hx
        simpa [eFun] using hg (eB x) (by rwa [← hfin])
    rw [hbij, Set.ncard_image_of_injective _ eFun.symm.injective]
  rw [heq, Set.ncard_eq_toFinset_card']
  let e : {T : Fin (2 ^ n) → Bool // T ∈ S} ≃ ({i : Fin (2 ^ n) // ¬ i.val < k n} → Bool) :=
    { toFun := fun ⟨T, _⟩ i => T i.1
      invFun := fun g =>
        ⟨fun i => if hi : i.val < k n then false else g ⟨i, hi⟩,
          fun i hi => dite_eq_left hi⟩
      left_inv := fun ⟨T, hT⟩ => by
        ext i
        by_cases hi : i.val < k n
        · simp [hi, hT i hi]
        · simp [hi]
      right_inv := fun g => by
        ext ⟨i, hi⟩
        simp [hi] }
  have hcard : S.toFinset.card = Fintype.card {T : Fin (2 ^ n) → Bool // T ∈ S} := by
    rw [Fintype.card_subtype]
    congr 1
    ext T
    simp
  rw [hcard, Fintype.card_congr e, Fintype.card_fun, Fintype.card_bool]
  congr 1
  have hsub : Fintype.card {i : Fin (2 ^ n) // ¬ i.val < k n} =
      (Finset.univ.filter fun i : Fin (2 ^ n) => ¬ i.val < k n).card :=
    Fintype.card_subtype _
  rw [hsub]
  have hcompl : (Finset.univ.filter fun i : Fin (2 ^ n) => i.val < k n).card +
      (Finset.univ.filter fun i : Fin (2 ^ n) => ¬ i.val < k n).card = 2 ^ n := by
    have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin (2 ^ n))))
      (p := fun i : Fin (2 ^ n) => i.val < k n)
    simpa only [Finset.card_univ, Fintype.card_fin] using this
  have hlt : (Finset.univ.filter fun i : Fin (2 ^ n) => i.val < k n).card = min (k n) (2 ^ n) := by
    let g : Fin (min (k n) (2 ^ n)) ↪ Fin (2 ^ n) :=
      ⟨fun i => ⟨i.val, lt_of_lt_of_le i.isLt (min_le_right _ _)⟩,
        fun a b h => Fin.ext (by simpa using congrArg Fin.val h)⟩
    have hset : (Finset.univ.filter fun i : Fin (2 ^ n) => i.val < k n) =
        Finset.univ.map g := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map, g]
      constructor
      · intro hi
        exact ⟨⟨i.val, lt_min hi i.isLt⟩, rfl⟩
      · rintro ⟨j, rfl⟩
        exact lt_of_lt_of_le j.isLt (min_le_left _ _)
    rw [hset, Finset.card_map, Finset.card_univ, Fintype.card_fin]
  omega

/-- Every singleton property `{f n}` is extremely rigid (and hence bypasses natural proofs). -/
theorem singleton_isExtremelyRigid (f : ∀ n, BooleanFunction n) :
    IsExtremelyRigid (fun n => {f n}) :=
  ⟨1, by omega, Eventually.of_forall fun n => by
    rw [Set.ncard_singleton]
    exact Nat.one_le_two_pow⟩

/-- The full property `Set.univ` is nonrigid (and hence not mildly rigid). -/
theorem univ_isNonrigid : IsNonrigid (fun _ => Set.univ) := by
  refine ⟨0, Eventually.of_forall fun n => ?_⟩
  rw [zero_mul, pow_zero, one_mul, Set.ncard_univ, Nat.card_eq_fintype_card,
    Fintype.card_fun, Fintype.card_bool, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]

/-- Boundary sharpness: setting `a = 1` gives `|UP_n| = 2 ^ N / 2 ^ n =
2 ^ N / N`, which is nonrigid (`c = 1`) and not mildly rigid. -/
theorem zeroPrefix_id_isNonrigid : IsNonrigid (zeroPrefixProperty id) := by
  refine ⟨1, ?_⟩
  filter_upwards [eventually_ge_atTop 1] with n _
  rw [ncard_zeroPrefixProperty, id_eq, one_mul, ← pow_add]
  have hle : n ≤ 2 ^ n := Nat.le_of_lt Nat.lt_two_pow_self
  rw [Nat.add_sub_of_le hle]

/-- Strict separation: there exists a strongly mildly rigid property that is not rigid. -/
theorem exists_isStronglyMildlyRigid_not_isRigid :
    ∃ UP : ∀ n, Set (BooleanFunction n), IsStronglyMildlyRigid UP ∧ ¬ IsRigid UP := by
  refine ⟨zeroPrefixProperty (fun n => n ^ 2), ?_, ?_⟩
  · refine ⟨2, by omega, ?_⟩
    filter_upwards [eventually_ge_atTop 4] with n hn
    rw [ncard_zeroPrefixProperty, ← pow_add, Nat.add_sub_of_le (sq_le_two_pow_of_four_le hn)]
  · rintro ⟨ε, _, h1, hfe⟩
    have hgap : 0 < 1 - ε := by linarith
    have hev := (hfe.and (tendsto_sq_div_two_pow.eventually (Iio_mem_nhds hgap))).and
      (eventually_ge_atTop 4)
    obtain ⟨n, ⟨hn, hdiv⟩, hn4⟩ := hev.exists
    rw [ncard_zeroPrefixProperty] at hn
    have hle : n ^ 2 ≤ 2 ^ n := sq_le_two_pow_of_four_le hn4
    have hpos : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
    have hlt : ((n ^ 2 : ℕ) : ℝ) < (1 - ε) * (2 : ℝ) ^ n := (div_lt_iff₀ hpos).mp hdiv
    have hcast : ((2 ^ (2 ^ n - n ^ 2) : ℕ) : ℝ) = (2 : ℝ) ^ (((2 ^ n - n ^ 2 : ℕ) : ℝ)) := by
      rw [Real.rpow_natCast]
      push_cast
      rfl
    rw [hcast] at hn
    have hexp := (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mp hn
    rw [Nat.cast_sub hle, Nat.cast_pow, Nat.cast_ofNat] at hexp
    linarith

/-- Strict separation: there exists a rigid property that is not strongly rigid. -/
theorem exists_isRigid_not_isStronglyRigid :
    ∃ UP : ∀ n, Set (BooleanFunction n), IsRigid UP ∧ ¬ IsStronglyRigid UP := by
  refine ⟨zeroPrefixProperty (fun n => 2 ^ n / 2), ?_, ?_⟩
  · refine ⟨1 / 2, by norm_num, by norm_num, ?_⟩
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [ncard_zeroPrefixProperty]
    have hdiv : 2 ^ n - 2 ^ n / 2 = 2 ^ (n - 1) := by
      cases n with
      | zero => omega
      | succ m =>
        simp only [Nat.add_sub_cancel]
        have : 2 ^ (m + 1) = 2 * 2 ^ m := by ring
        omega
    rw [hdiv]
    have hcast : ((2 ^ 2 ^ (n - 1) : ℕ) : ℝ) = (2 : ℝ) ^ ((2 ^ (n - 1) : ℕ) : ℝ) := by
      rw [Real.rpow_natCast]
      push_cast
      rfl
    rw [hcast]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    cases n with
    | zero => omega
    | succ m =>
      simp only [Nat.add_sub_cancel, Nat.cast_pow, Nat.cast_ofNat]
      ring_nf
      exact le_rfl
  · rintro ⟨ε, _, h1, hfe⟩
    have hdiff : 0 < 1 - ε := by linarith
    have hlim : Tendsto (fun n : ℕ => ((2 : ℝ) ^ n) ^ (1 - ε)) atTop atTop :=
      (tendsto_rpow_atTop hdiff).comp
        (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2))
    have hev := (hfe.and (hlim.eventually_gt_atTop (2 : ℝ))).and (eventually_ge_atTop 1)
    obtain ⟨n, ⟨hn, hgt⟩, hn1⟩ := hev.exists
    rw [ncard_zeroPrefixProperty] at hn
    have hdiv : 2 ^ n - 2 ^ n / 2 = 2 ^ (n - 1) := by
      cases n with
      | zero => omega
      | succ m =>
        simp only [Nat.add_sub_cancel]
        have : 2 ^ (m + 1) = 2 * 2 ^ m := by ring
        omega
    rw [hdiv] at hn
    have hcast : ((2 ^ 2 ^ (n - 1) : ℕ) : ℝ) = (2 : ℝ) ^ ((2 ^ (n - 1) : ℕ) : ℝ) := by
      rw [Real.rpow_natCast]
      push_cast
      rfl
    rw [hcast] at hn
    have hexp := (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mp hn
    have hhalf : ((2 ^ (n - 1) : ℕ) : ℝ) = (2 : ℝ) ^ n / 2 := by
      cases n with
      | zero => omega
      | succ m =>
        simp only [Nat.add_sub_cancel, Nat.cast_pow, Nat.cast_ofNat]
        ring
    rw [hhalf] at hexp
    have hpos : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
    have hsplit : ((2 : ℝ) ^ n) ^ ε * ((2 : ℝ) ^ n) ^ (1 - ε) = (2 : ℝ) ^ n := by
      rw [← Real.rpow_add hpos]
      ring_nf
      exact Real.rpow_one _
    have hmul : ((2 : ℝ) ^ n) ^ ε * 2 < ((2 : ℝ) ^ n) ^ ε * ((2 : ℝ) ^ n) ^ (1 - ε) :=
      mul_lt_mul_of_pos_left hgt (by positivity)
    rw [hsplit] at hmul
    linarith

/-- Strict separation: there exists a strongly rigid property that is not extremely rigid. -/
theorem exists_isStronglyRigid_not_isExtremelyRigid :
    ∃ UP : ∀ n, Set (BooleanFunction n), IsStronglyRigid UP ∧ ¬ IsExtremelyRigid UP := by
  refine ⟨zeroPrefixProperty (fun n => 2 ^ n - 2 ^ (n / 2)), ?_, ?_⟩
  · refine ⟨1 / 2, by norm_num, by norm_num, ?_⟩
    filter_upwards with n
    rw [ncard_zeroPrefixProperty]
    have hle : 2 ^ (n / 2) ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) (Nat.div_le_self n 2)
    rw [Nat.sub_sub_self hle]
    have hcast : ((2 ^ 2 ^ (n / 2) : ℕ) : ℝ) = (2 : ℝ) ^ ((2 ^ (n / 2) : ℕ) : ℝ) := by
      rw [Real.rpow_natCast]
      push_cast
      rfl
    rw [hcast]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have h1 : ((2 ^ (n / 2) : ℕ) : ℝ) = (2 : ℝ) ^ ((n / 2 : ℕ) : ℝ) := by
      rw [Real.rpow_natCast]
      push_cast
      rfl
    have h2 : ((2 : ℝ) ^ n) ^ ((1 : ℝ) / 2) = (2 : ℝ) ^ ((n : ℝ) / 2) := by
      rw [← Real.rpow_natCast (2 : ℝ) n, ← Real.rpow_mul (by norm_num)]
      ring_nf
    rw [h1, h2]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have : 2 * (n / 2) ≤ n := Nat.mul_div_le n 2
    have : (2 : ℝ) * ((n / 2 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast this
    linarith
  · rintro ⟨a, _, hfa⟩
    have hev := (hfa.and ((tendsto_pow_div_two_rpow_half a).eventually
      (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)))).and (eventually_ge_atTop 2)
    obtain ⟨n, ⟨hn, hlt⟩, _⟩ := hev.exists
    rw [ncard_zeroPrefixProperty] at hn
    have hle : 2 ^ (n / 2) ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) (Nat.div_le_self n 2)
    rw [Nat.sub_sub_self hle] at hn
    have hexp : 2 ^ (n / 2) ≤ n ^ a := (Nat.pow_le_pow_iff_right (by omega : 1 < 2)).mp hn
    have hpos : (0 : ℝ) < (2 : ℝ) ^ ((n : ℝ) / 2) := by positivity
    have hlt2 : (n : ℝ) ^ a < (1 / 2 : ℝ) * (2 : ℝ) ^ ((n : ℝ) / 2) :=
      (div_lt_iff₀ hpos).mp hlt
    have hge : (1 / 2 : ℝ) * (2 : ℝ) ^ ((n : ℝ) / 2) ≤ ((2 ^ (n / 2) : ℕ) : ℝ) := by
      have hsub : (n : ℝ) / 2 - 1 ≤ ((n / 2 : ℕ) : ℝ) := by
        have : n ≤ 2 * (n / 2) + 1 := by omega
        have : (n : ℝ) ≤ 2 * ((n / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast this
        linarith
      calc
        (1 / 2 : ℝ) * (2 : ℝ) ^ ((n : ℝ) / 2)
            = (2 : ℝ) ^ (-1 : ℝ) * (2 : ℝ) ^ ((n : ℝ) / 2) := by norm_num
        _ = (2 : ℝ) ^ ((n : ℝ) / 2 - 1) := by
          rw [← Real.rpow_add (by norm_num)]
          ring_nf
        _ ≤ (2 : ℝ) ^ ((n / 2 : ℕ) : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hsub
        _ = ((2 ^ (n / 2) : ℕ) : ℝ) := by
          rw [Real.rpow_natCast]
          push_cast
          rfl
    have hexpR : ((2 ^ (n / 2) : ℕ) : ℝ) ≤ (n : ℝ) ^ a := by exact_mod_cast hexp
    linarith

end Separations

end CslibFrontier.Computability.Circuit.Boolean
