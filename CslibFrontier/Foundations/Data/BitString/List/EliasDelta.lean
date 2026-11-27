module

public import CslibFrontier.Foundations.Data.BitString.List.PrefixFree
public import Mathlib.Analysis.SpecialFunctions.Log.Base
import CslibFrontier.Foundations.Data.Nat.Bits
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Elias Delta Prefix-Free Integer Coding and Tuple Header Bounds

This module defines the computable Elias $\delta$ universal integer code `eliasDelta` and its
left inverse `decodeEliasDelta` on top of `Cslib.BitString.eliasGamma`, proves prefix-freeness
and exact codeword lengths, and establishes linear and Jensen-concavity length bounds for
prefix-free tuple concatenations.

## Main definitions

* `CslibFrontier.Foundations.Data.BitString.List.eliasDelta`: the Elias $\delta$ codeword for a
  positive integer `m ≥ 1`, built from `eliasGamma (Nat.log 2 m + 1)` and `lowBits (Nat.log 2 m) m`.
* `CslibFrontier.Foundations.Data.BitString.List.decodeEliasDelta`: computable left inverse of
  `eliasDelta`.
* `CslibFrontier.Foundations.Data.BitString.List.encodePrefixFreeTuple`: separator-free
  concatenation of a prefix-free integer code over a finite tuple `Fin t → ℕ`.

## Main results

* `CslibFrontier.Foundations.Data.BitString.List.length_eliasDelta`: exact length
  `Nat.log 2 m + 2 * Nat.log 2 (Nat.log 2 m + 1) + 1`.
* `CslibFrontier.Foundations.Data.BitString.List.decodeEliasDelta_eliasDelta`: left-inverse
  property for `1 ≤ m`.
* `CslibFrontier.Foundations.Data.BitString.List.isPrefixFree_eliasDelta`: prefix-freeness of
  `eliasDelta` on positive integers.
* `CslibFrontier.Foundations.Data.BitString.List.length_eliasGamma_le_real` and
  `CslibFrontier.Foundations.Data.BitString.List.length_eliasDelta_le_real`: real-valued
  logarithmic upper bounds for `eliasGamma` and `eliasDelta`.
* `CslibFrontier.Foundations.Data.BitString.List.isPrefixFree_encodePrefixFreeTuple`: prefix-free
  tuple concatenation preserves prefix-freeness and injectivity.
* `CslibFrontier.Foundations.Data.BitString.List.length_encodePrefixFreeTuple_le_linear` and
  `CslibFrontier.Foundations.Data.BitString.List.length_encodePrefixFreeTuple_le_jensen`: linear and
  concavity-sharpened upper bounds on the total header length of a tuple.
-/

public section

namespace CslibFrontier.Foundations.Data.BitString.List

open Cslib.BitString _root_.InformationTheory

/-! ### Elias delta encoding and decoding -/

/-- Elias $\delta$ codeword for a positive integer `m ≥ 1`: concatenates
`eliasGamma (Nat.log 2 m + 1)` with the `Nat.log 2 m` low-order binary bits of `m`. -/
def eliasDelta (m : ℕ) : List Bool :=
  let k := Nat.log 2 m
  eliasGamma (k + 1) ++ lowBits k m

/-- Computable left inverse of `eliasDelta` on positive integers: reads the leading unary prefix
length `r` of the Elias $\gamma$ header, decodes `k + 1`, and folds the following `k` bits. -/
def decodeEliasDelta (code : List Bool) : ℕ :=
  let r := (code.takeWhile (fun b => !b)).length
  let gLen := 2 * r + 1
  let k := decodeEliasGamma (code.take gLen) - 1
  ((code.drop gLen).take k).foldr Nat.bit 1

/-- Exact bit length of `eliasDelta m`. -/
@[simp]
theorem length_eliasDelta (m : ℕ) :
    (eliasDelta m).length = Nat.log 2 m + 2 * Nat.log 2 (Nat.log 2 m + 1) + 1 := by
  simp only [eliasDelta, List.length_append, length_eliasGamma, length_lowBits]
  ring

/-- Every `eliasDelta` codeword is nonempty. -/
theorem eliasDelta_ne_nil (m : ℕ) : eliasDelta m ≠ [] := by
  simp [← List.length_pos_iff]

private theorem takeWhile_not_replicate_false (r : ℕ) :
    (List.replicate r false).takeWhile (fun b => !b) = List.replicate r false := by
  induction r with
  | zero => rfl
  | succ r ih => simp [List.replicate_succ, ih]

private theorem takeWhile_not_eliasDelta (m : ℕ) :
    ((eliasDelta m).takeWhile (fun b => !b)).length = Nat.log 2 (Nat.log 2 m + 1) := by
  simp only [eliasDelta, eliasGamma]
  have h1 :
      ((List.replicate (Nat.log 2 (Nat.log 2 m + 1)) false ++
        true :: lowBits (Nat.log 2 (Nat.log 2 m + 1)) (Nat.log 2 m + 1)) ++
        lowBits (Nat.log 2 m) m).takeWhile (fun b => !b) =
      List.replicate (Nat.log 2 (Nat.log 2 m + 1)) false := by
    rw [List.append_assoc, List.takeWhile_append, takeWhile_not_replicate_false]
    simp
  rw [h1, List.length_replicate]

/-- `decodeEliasDelta` recovers every positive integer `m ≥ 1` from `eliasDelta m`. -/
@[simp]
theorem decodeEliasDelta_eliasDelta {m : ℕ} (hm : 1 ≤ m) :
    decodeEliasDelta (eliasDelta m) = m := by
  set k := Nat.log 2 m
  set r := Nat.log 2 (k + 1)
  have htw : ((eliasDelta m).takeWhile (fun b => !b)).length = r :=
    takeWhile_not_eliasDelta m
  have htake : (eliasDelta m).take (2 * r + 1) = eliasGamma (k + 1) := by
    simp only [eliasDelta]
    have hlen : (eliasGamma (k + 1)).length = 2 * r + 1 := length_eliasGamma (k + 1)
    rw [← hlen, List.take_left]
  have hdrop : (eliasDelta m).drop (2 * r + 1) = lowBits k m := by
    simp only [eliasDelta]
    have hlen : (eliasGamma (k + 1)).length = 2 * r + 1 := length_eliasGamma (k + 1)
    rw [← hlen, List.drop_left]
  have hdec : decodeEliasGamma (eliasGamma (k + 1)) = k + 1 :=
    decodeEliasGamma_eliasGamma (by omega)
  have htake_low : (lowBits k m).take k = lowBits k m := by
    rw [List.take_of_length_le (by simp [length_lowBits])]
  simp only [decodeEliasDelta, htw, htake, hdec, Nat.add_sub_cancel, hdrop, htake_low]
  have hge : 2 ^ k ≤ m := Nat.pow_log_le_self 2 (by omega)
  have hlt : m < 2 ^ (k + 1) := Nat.lt_pow_succ_log_self Nat.one_lt_two m
  have hdiv : m / 2 ^ k = 1 := by
    apply le_antisymm
    · exact Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul (Nat.two_pow_pos k)).mpr
        (by simpa only [Nat.pow_succ'] using hlt))
    · exact (Nat.le_div_iff_mul_le (Nat.two_pow_pos k)).mpr (by simpa using hge)
  have hbitk : m.testBit k = true := by
    rw [Nat.testBit_eq_decide_div_mod_eq, hdiv]
    decide
  have hsize : m.size ≤ k + 1 := Nat.size_le.mpr hlt
  have hrec := Nat.foldr_bit_testBit hsize
  rw [List.range_succ, List.map_append, List.map_singleton, List.foldr_append, hbitk] at hrec
  exact hrec

/-- `eliasDelta` is injective on positive integers `{m : ℕ | 1 ≤ m}`. -/
theorem injOn_eliasDelta : Set.InjOn eliasDelta {m : ℕ | 1 ≤ m} := by
  intro m₁ hm₁ m₂ hm₂ heq
  rw [← decodeEliasDelta_eliasDelta hm₁, ← decodeEliasDelta_eliasDelta hm₂, heq]

/-- The image of positive integers under `eliasDelta` is prefix-free. -/
theorem isPrefixFree_eliasDelta : IsPrefixFree (eliasDelta '' {m : ℕ | 1 ≤ m}) := by
  have h1 : IsPrefixFree ((fun m => eliasGamma (Nat.log 2 m + 1)) '' {m : ℕ | 1 ≤ m}) :=
    isPrefixFree_range_eliasGamma.anti (by rintro _ ⟨m, _, rfl⟩; exact ⟨Nat.log 2 m + 1, rfl⟩)
  have h2 : ∀ m ∈ ({m : ℕ | 1 ≤ m} : Set ℕ),
      IsPrefixFree ((fun y => lowBits (Nat.log 2 y) y) ''
        {y ∈ ({m : ℕ | 1 ≤ m} : Set ℕ) |
          eliasGamma (Nat.log 2 y + 1) = eliasGamma (Nat.log 2 m + 1)}) := by
    intro m _
    apply isPrefixFree_of_length_eq (k := Nat.log 2 m)
    rintro _ ⟨y, ⟨_, hy⟩, rfl⟩
    have hlog : Nat.log 2 y + 1 = Nat.log 2 m + 1 :=
      injOn_eliasGamma (by simp) (by simp) hy
    rw [length_lowBits]
    omega
  exact isPrefixFree_image_append h1 h2

/-! ### Logarithmic real-valued upper bounds for Elias gamma and delta -/

private theorem natLog_two_le_logb {u : ℕ} (hu : 1 ≤ u) :
    (Nat.log 2 u : ℝ) ≤ Real.logb 2 (u : ℝ) := by
  have hpow : (2 : ℝ) ^ (Nat.log 2 u) ≤ (u : ℝ) := by
    exact_mod_cast Nat.pow_log_le_self 2 (by omega)
  have hlog := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by positivity) hpow
  rwa [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one] at hlog

private theorem natLog_two_succ_le (k : ℕ) : Nat.log 2 (k + 1) ≤ k := by
  have hlt : k + 1 < 2 ^ (k + 1) := by
    induction k with
    | zero => norm_num
    | succ n ih =>
      have h1 : 1 ≤ 2 ^ (n + 1) := Nat.one_le_pow _ _ (by norm_num)
      rw [Nat.pow_succ]
      omega
  exact Nat.le_of_lt_succ (Nat.log_lt_of_lt_pow (by omega) hlt)

private theorem two_mul_natLog_two_succ_le (k : ℕ) : 2 * Nat.log 2 (k + 1) ≤ k + 2 := by
  suffices h : k + 1 < 2 ^ (k / 2 + 2) by
    have hlog : Nat.log 2 (k + 1) < k / 2 + 2 := Nat.log_lt_of_lt_pow (by omega) h
    omega
  have hpow : ∀ n : ℕ, 2 * n + 2 < 2 ^ (n + 2) := by
    intro n
    induction n with
    | zero => norm_num
    | succ m ih =>
      rw [Nat.pow_succ]
      omega
  have := hpow (k / 2)
  omega

/-- Real-valued upper bound `ℓ_γ(u) ≤ 2 log₂ u + 1` for `u ≥ 1`. -/
theorem length_eliasGamma_le_real {u : ℕ} (hu : 1 ≤ u) :
    ((eliasGamma u).length : ℝ) ≤ 2 * Real.logb 2 (u : ℝ) + 1 := by
  rw [length_eliasGamma]
  push_cast
  linarith [natLog_two_le_logb hu]

/-- Real-valued linear-logarithmic upper bound `ℓ_δ(u) ≤ 3 + 2 log₂ u` for `u ≥ 1`. -/
theorem length_eliasDelta_le_real {u : ℕ} (hu : 1 ≤ u) :
    ((eliasDelta u).length : ℝ) ≤ 3 + 2 * Real.logb 2 (u : ℝ) := by
  rw [length_eliasDelta]
  have h2 : 2 * Nat.log 2 (Nat.log 2 u + 1) ≤ Nat.log 2 u + 2 :=
    two_mul_natLog_two_succ_le (Nat.log 2 u)
  have hnat : Nat.log 2 u + 2 * Nat.log 2 (Nat.log 2 u + 1) + 1 ≤ 2 * Nat.log 2 u + 3 := by omega
  have hreal : ((Nat.log 2 u + 2 * Nat.log 2 (Nat.log 2 u + 1) + 1 : ℕ) : ℝ) ≤
      2 * (Nat.log 2 u : ℝ) + 3 := by exact_mod_cast hnat
  linarith [natLog_two_le_logb hu]

/-- Alternative slope-3 real-valued bound `ℓ_δ(u) ≤ 1 + 3 log₂ u` for `u ≥ 1`. -/
theorem length_eliasDelta_le_one_add_three_logb {u : ℕ} (hu : 1 ≤ u) :
    ((eliasDelta u).length : ℝ) ≤ 1 + 3 * Real.logb 2 (u : ℝ) := by
  rw [length_eliasDelta]
  have h1 : Nat.log 2 (Nat.log 2 u + 1) ≤ Nat.log 2 u := natLog_two_succ_le (Nat.log 2 u)
  have hnat : Nat.log 2 u + 2 * Nat.log 2 (Nat.log 2 u + 1) + 1 ≤ 3 * Nat.log 2 u + 1 := by omega
  have hreal : ((Nat.log 2 u + 2 * Nat.log 2 (Nat.log 2 u + 1) + 1 : ℕ) : ℝ) ≤
      3 * (Nat.log 2 u : ℝ) + 1 := by exact_mod_cast hnat
  linarith [natLog_two_le_logb hu]

/-! ### Prefix-free tuple concatenation and length bounds -/

/-- Separator-free concatenation of an integer code `enc` applied to each entry of a tuple
`a : Fin t → ℕ`, encoded at `a i + 1` so positive-integer codes apply uniformly to all `ℕ`. -/
def encodePrefixFreeTuple (enc : ℕ → List Bool) {t : ℕ} (a : Fin t → ℕ) : List Bool :=
  (List.ofFn (fun i => enc (a i + 1))).flatten

/-- The length of `encodePrefixFreeTuple enc a` is the sum of its entry codeword lengths. -/
@[simp]
theorem length_encodePrefixFreeTuple (enc : ℕ → List Bool) {t : ℕ} (a : Fin t → ℕ) :
    (encodePrefixFreeTuple enc a).length = ∑ i : Fin t, (enc (a i + 1)).length := by
  induction t with
  | zero => simp [encodePrefixFreeTuple]
  | succ t ih =>
    simp only [encodePrefixFreeTuple, List.ofFn_succ, List.flatten_cons, List.length_append,
      Fin.sum_univ_succ]
    congr 1
    exact ih (fun i => a i.succ)

/-- Prefix-free concatenation of a prefix-free positive-integer code is prefix-free on tuples
of any fixed arity `t`. -/
theorem isPrefixFree_encodePrefixFreeTuple {enc : ℕ → List Bool}
    (hpf : IsPrefixFree (enc '' {m : ℕ | 1 ≤ m})) (t : ℕ) :
    IsPrefixFree (Set.range (encodePrefixFreeTuple enc (t := t))) := by
  induction t with
  | zero =>
    apply isPrefixFree_of_length_eq (k := 0)
    rintro _ ⟨a, rfl⟩
    simp
  | succ t ih =>
    have hsplit : ∀ a : Fin (t + 1) → ℕ,
        encodePrefixFreeTuple enc a =
          enc (a 0 + 1) ++ encodePrefixFreeTuple enc (fun i => a i.succ) := fun a => by
      simp [encodePrefixFreeTuple, List.ofFn_succ]
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ hp
    rw [hsplit a, hsplit b] at hp ⊢
    have ha0 : enc (a 0 + 1) ∈ enc '' {m : ℕ | 1 ≤ m} := ⟨a 0 + 1, by simp, rfl⟩
    have hb0 : enc (b 0 + 1) ∈ enc '' {m : ℕ | 1 ≤ m} := ⟨b 0 + 1, by simp, rfl⟩
    obtain ⟨h0, htail⟩ := prefix_append_of_isPrefixFree hpf ha0 hb0 hp
    have hrest := ih _ ⟨fun i => a i.succ, rfl⟩ _ ⟨fun i => b i.succ, rfl⟩ htail
    rw [h0, hrest]

/-- Prefix-free concatenation of an injective prefix-free positive-integer code is injective on
tuples of any fixed arity `t`. -/
theorem injective_encodePrefixFreeTuple {enc : ℕ → List Bool}
    (hpf : IsPrefixFree (enc '' {m : ℕ | 1 ≤ m}))
    (hinj : Set.InjOn enc {m : ℕ | 1 ≤ m}) (t : ℕ) :
    Function.Injective (encodePrefixFreeTuple enc (t := t)) := by
  induction t with
  | zero =>
    intro a b _
    funext i
    exact Fin.elim0 i
  | succ t ih =>
    intro a b heq
    have hsplit : ∀ c : Fin (t + 1) → ℕ,
        encodePrefixFreeTuple enc c =
          enc (c 0 + 1) ++ encodePrefixFreeTuple enc (fun i => c i.succ) := fun c => by
      simp [encodePrefixFreeTuple, List.ofFn_succ]
    rw [hsplit a, hsplit b] at heq
    have ha0 : enc (a 0 + 1) ∈ enc '' {m : ℕ | 1 ≤ m} := ⟨a 0 + 1, by simp, rfl⟩
    have hb0 : enc (b 0 + 1) ∈ enc '' {m : ℕ | 1 ≤ m} := ⟨b 0 + 1, by simp, rfl⟩
    obtain ⟨h0, htail⟩ := append_inj_of_isPrefixFree hpf ha0 hb0 heq
    have ha0_eq : a 0 = b 0 := by
      have := hinj (by simp : 1 ≤ a 0 + 1) (by simp : 1 ≤ b 0 + 1) h0
      omega
    have hsucc : (fun i : Fin t => a i.succ) = (fun i : Fin t => b i.succ) := ih htail
    funext i
    refine Fin.cases ha0_eq (fun j => congrFun hsucc j) i

/-- Linear upper bound on the length of a prefix-free tuple header: if
`∀ u ≥ 1, (enc u).length ≤ C₀ + C₁ * log₂ u` with `0 ≤ C₁` and `∑ i, a i ≤ c * log₂ N`, then
the total encoded bit length is at most `C₀ * t + (C₁ * c / ln 2) * log₂ N`. -/
theorem length_encodePrefixFreeTuple_le_linear {enc : ℕ → List Bool} {C₀ C₁ c N : ℝ}
    (hC₁ : 0 ≤ C₁) (henc : ∀ u : ℕ, 1 ≤ u → ((enc u).length : ℝ) ≤ C₀ + C₁ * Real.logb 2 u)
    {t : ℕ} (a : Fin t → ℕ) (hsum : (∑ i : Fin t, (a i : ℝ)) ≤ c * Real.logb 2 N) :
    ((encodePrefixFreeTuple enc a).length : ℝ) ≤
      C₀ * t + (C₁ * c / Real.log 2) * Real.logb 2 N := by
  rw [length_encodePrefixFreeTuple, Nat.cast_sum]
  have hstep : ∑ i : Fin t, ((enc (a i + 1)).length : ℝ) ≤
      ∑ i : Fin t, (C₀ + C₁ * Real.logb 2 ((a i + 1 : ℕ) : ℝ)) :=
    Finset.sum_le_sum fun i _ => henc (a i + 1) (by omega)
  have hlog : ∀ i : Fin t, Real.logb 2 ((a i + 1 : ℕ) : ℝ) ≤ (a i : ℝ) / Real.log 2 := by
    intro i
    rw [Real.logb]
    have hpos : (0 : ℝ) < (a i : ℝ) + 1 := by positivity
    have hle : Real.log ((a i : ℝ) + 1) ≤ (a i : ℝ) := by
      have := Real.log_le_sub_one_of_pos hpos
      linarith
    have hcast : ((a i + 1 : ℕ) : ℝ) = (a i : ℝ) + 1 := by push_cast; ring
    rw [hcast]
    exact div_le_div_of_nonneg_right hle (le_of_lt (Real.log_pos (by norm_num)))
  have hlog_sum : ∑ i : Fin t, Real.logb 2 ((a i + 1 : ℕ) : ℝ) ≤
      (∑ i : Fin t, (a i : ℝ)) / Real.log 2 := by
    rw [Finset.sum_div]
    exact Finset.sum_le_sum fun i _ => hlog i
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hmul : C₁ * (∑ i : Fin t, Real.logb 2 ((a i + 1 : ℕ) : ℝ)) ≤
      (C₁ * c / Real.log 2) * Real.logb 2 N := by
    have h1 : (∑ i : Fin t, (a i : ℝ)) / Real.log 2 ≤ (c * Real.logb 2 N) / Real.log 2 :=
      div_le_div_of_nonneg_right hsum hlog2_pos.le
    calc
      C₁ * ∑ i : Fin t, Real.logb 2 ((a i + 1 : ℕ) : ℝ)
          ≤ C₁ * ((c * Real.logb 2 N) / Real.log 2) :=
            mul_le_mul_of_nonneg_left (hlog_sum.trans h1) hC₁
      _ = (C₁ * c / Real.log 2) * Real.logb 2 N := by ring
  calc
    ∑ i : Fin t, ((enc (a i + 1)).length : ℝ)
        ≤ ∑ i : Fin t, (C₀ + C₁ * Real.logb 2 ((a i + 1 : ℕ) : ℝ)) := hstep
    _ = C₀ * t + C₁ * ∑ i : Fin t, Real.logb 2 ((a i + 1 : ℕ) : ℝ) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul, ← Finset.mul_sum]
        ring
    _ ≤ C₀ * t + (C₁ * c / Real.log 2) * Real.logb 2 N := by linarith

/-- Jensen concavity-sharpened upper bound on the length of a prefix-free tuple header: for
`t ≥ 1`, `∀ u ≥ 1, (enc u).length ≤ C₀ + C₁ * log₂ u` with `0 ≤ C₁`, and
`∑ i, a i ≤ c * log₂ N`, the total bit length is at most
`C₀ * t + C₁ * t * log₂ (1 + c * log₂ N / t)`. -/
theorem length_encodePrefixFreeTuple_le_jensen {enc : ℕ → List Bool} {C₀ C₁ c N : ℝ}
    (hC₁ : 0 ≤ C₁) (henc : ∀ u : ℕ, 1 ≤ u → ((enc u).length : ℝ) ≤ C₀ + C₁ * Real.logb 2 u)
    {t : ℕ} (ht : 1 ≤ t) (a : Fin t → ℕ) (hsum : (∑ i : Fin t, (a i : ℝ)) ≤ c * Real.logb 2 N) :
    ((encodePrefixFreeTuple enc a).length : ℝ) ≤
      C₀ * t + C₁ * t * Real.logb 2 (1 + c * Real.logb 2 N / t) := by
  rw [length_encodePrefixFreeTuple, Nat.cast_sum]
  have ht_pos : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hstep : ∑ i : Fin t, ((enc (a i + 1)).length : ℝ) ≤
      ∑ i : Fin t, (C₀ + C₁ * Real.logb 2 ((a i + 1 : ℕ) : ℝ)) :=
    Finset.sum_le_sum fun i _ => henc (a i + 1) (by omega)
  have hjensen : ∑ i : Fin t, Real.logb 2 ((a i + 1 : ℕ) : ℝ) ≤
      (t : ℝ) * Real.logb 2 (1 + (∑ i : Fin t, (a i : ℝ)) / (t : ℝ)) := by
    set μ : ℝ := 1 + (∑ i : Fin t, (a i : ℝ)) / (t : ℝ)
    have hμ_pos : 0 < μ := by
      have hnonneg : (0 : ℝ) ≤ (∑ i : Fin t, (a i : ℝ)) / (t : ℝ) :=
        div_nonneg (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _) ht_pos.le
      linarith
    have hpt : ∀ i : Fin t,
        Real.log ((a i + 1 : ℕ) : ℝ) - Real.log μ ≤ ((a i + 1 : ℕ) : ℝ) / μ - 1 := by
      intro i
      have hx : 0 < ((a i + 1 : ℕ) : ℝ) := by positivity
      have hdiv_pos : 0 < ((a i + 1 : ℕ) : ℝ) / μ := div_pos hx hμ_pos
      have h1 := Real.log_le_sub_one_of_pos hdiv_pos
      rwa [Real.log_div hx.ne' hμ_pos.ne'] at h1
    have hsum_log :
        (∑ i : Fin t, Real.log ((a i + 1 : ℕ) : ℝ)) - (t : ℝ) * Real.log μ ≤ 0 := by
      have h1 := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hpt i
      simp only [Finset.sum_sub_distrib, ← Finset.sum_div, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, mul_one] at h1
      have htot : (∑ i : Fin t, ((a i + 1 : ℕ) : ℝ)) / μ = (t : ℝ) := by
        have hcast : ∑ i : Fin t, ((a i + 1 : ℕ) : ℝ) =
            (∑ i : Fin t, (a i : ℝ)) + (t : ℝ) := by
          simp only [Nat.cast_add, Nat.cast_one, Finset.sum_add_distrib, Finset.sum_const,
            Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
        rw [hcast, div_eq_iff hμ_pos.ne']
        simp only [μ]
        field_simp [ht_pos.ne']
        ring
      linarith
    have hdiv := div_le_div_of_nonneg_right (by linarith :
      ∑ i : Fin t, Real.log ((a i + 1 : ℕ) : ℝ) ≤ (t : ℝ) * Real.log μ) hlog2_pos.le
    simpa only [Real.logb, ← Finset.sum_div, mul_div_assoc] using hdiv
  have hmono : Real.logb 2 (1 + (∑ i : Fin t, (a i : ℝ)) / (t : ℝ)) ≤
      Real.logb 2 (1 + c * Real.logb 2 N / (t : ℝ)) := by
    apply Real.logb_le_logb_of_le (by norm_num)
    · have hnonneg : (0 : ℝ) ≤ (∑ i : Fin t, (a i : ℝ)) / (t : ℝ) :=
        div_nonneg (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _) ht_pos.le
      linarith
    · linarith [div_le_div_of_nonneg_right hsum ht_pos.le]
  calc
    ∑ i : Fin t, ((enc (a i + 1)).length : ℝ)
        ≤ ∑ i : Fin t, (C₀ + C₁ * Real.logb 2 ((a i + 1 : ℕ) : ℝ)) := hstep
    _ = C₀ * t + C₁ * ∑ i : Fin t, Real.logb 2 ((a i + 1 : ℕ) : ℝ) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul, ← Finset.mul_sum]
        ring
    _ ≤ C₀ * t + C₁ * ((t : ℝ) * Real.logb 2 (1 + (∑ i : Fin t, (a i : ℝ)) / (t : ℝ))) := by
        gcongr
    _ ≤ C₀ * t + C₁ * ((t : ℝ) * Real.logb 2 (1 + c * Real.logb 2 N / (t : ℝ))) := by
        gcongr
    _ = C₀ * t + C₁ * t * Real.logb 2 (1 + c * Real.logb 2 N / t) := by ring

private theorem eliasDelta_sanity_example :
    decodeEliasDelta (eliasDelta 6) = 6 ∧ (eliasDelta 6).length = 5 := by
  exact ⟨decodeEliasDelta_eliasDelta (by norm_num), by decide⟩

end CslibFrontier.Foundations.Data.BitString.List
