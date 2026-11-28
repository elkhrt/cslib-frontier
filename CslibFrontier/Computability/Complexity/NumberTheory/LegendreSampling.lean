module

public import CslibFrontier.Computability.Complexity.Classes.P
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.PowMod
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.IntBinary
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Unary
public import CslibFrontier.Foundations.Data.BitString.Basic
public import CslibFrontier.Foundations.Data.BitString.List.Binary
public import Mathlib.Data.ZMod.Basic
public import Mathlib.NumberTheory.LegendreSymbol.Basic
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import CslibFrontier.Computability.Complexity.Problems.Primes
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.EqualityPrimitives
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeBinaryPrimitives
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeOptionPrimitives
import CslibFrontier.Foundations.Combinatorics.MajorityVote
import CslibFrontier.Foundations.Data.BitString.WordCount
import CslibFrontier.Foundations.NumberTheory.PrimeDensity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Polynomial-Time Legendre Symbol, Random Prime Sampling, and Modular Sampling

Algorithmic number-theory primitives computable in deterministic polynomial time on binary
encodings:

1. **Euler-criterion Legendre symbol**: evaluating `a ^ ((p - 1) / 2) mod p` via
   `Turing.MultiTapeTM.powMod` computes the Legendre symbol `legendreSym p a` and the quadratic
   nonresidue test `quadraticChar (ZMod p) a = -1` in deterministic polynomial time.
2. **Randomized `k`-bit prime generation**: parsing `T = 3 * s * k` independent `(k - 1)`-bit
   blocks into candidates in `[2 ^ (k - 1), 2 ^ k)` and selecting the first prime via a
   polynomial-time primality decider (`Cslib.Complexity.primes_mem_P`) succeeds with probability
   at least `1 - 2 ^ (-s)` by `Nat.two_pow_sub_one_le_three_mul_card_primes`.
3. **Nearly uniform modular sampling**: reducing a uniform `(k + e)`-bit string modulo any
   positive `p ≤ 2 ^ k` hits every predicate `P : ZMod p → Prop` with probability at least
   `(1 - 2 ^ (-e)) * |{b | P b}| / p`.

## Main definitions

* `CslibFrontier.Complexity.legendrePowMod`: Euler-criterion evaluation of the Legendre symbol
  via modular exponentiation.
* `CslibFrontier.Complexity.isQuadraticNonresidueMod`: Boolean quadratic nonresidue test modulo
  an odd prime.
* `CslibFrontier.Complexity.windowCandidates`, `CslibFrontier.Complexity.firstPrimeInWindow`:
  extracting the first `k`-bit prime from `T` random `(k - 1)`-bit blocks.

## Main results

* `CslibFrontier.Complexity.legendrePowMod_eq_quadraticChar`,
  `CslibFrontier.Complexity.legendrePowMod_eq_legendreSym`,
  `CslibFrontier.Complexity.isQuadraticNonresidueMod_eq_true_iff`: correctness of modular
  exponentiation for the Legendre symbol.
* `CslibFrontier.Complexity.computableInPolyTime_legendrePowMod`,
  `CslibFrontier.Complexity.computableInPolyTime_isQuadraticNonresidueMod`: polynomial-time
  computability on binary inputs.
* `CslibFrontier.Complexity.firstPrimeInWindow_spec`,
  `CslibFrontier.Complexity.two_pow_mul_card_filter_firstPrimeInWindow_eq_zero_le`,
  `CslibFrontier.Complexity.computableInPolyTime_firstPrimeInWindow`: soundness, `2 ^ (-s)`
  failure-probability bound, and polynomial-time computability of random `k`-bit prime sampling.
* `CslibFrontier.Complexity.card_filter_binaryValue_mod_ge`,
  `CslibFrontier.Complexity.density_binaryValue_mod_ge`: integer and real lower bounds for
  modular sampling from `(k + e)`-bit strings.
-/

public section

namespace CslibFrontier.Complexity

open Finset Turing.MultiTapeTM Cslib Cslib.BitString

/-- Compute the Legendre symbol modulo an odd prime `p` using modular exponentiation
`a ^ ((p - 1) / 2) mod p`. Returns `0` for `p ≤ 2`. -/
def legendrePowMod (p a : ℕ) : ℤ :=
  if p ≤ 2 then 0
  else if powMod p a ((p - 1) / 2) = 1 then 1
  else if powMod p a ((p - 1) / 2) = p - 1 then -1
  else 0

/-- Polynomial-time Boolean predicate testing `quadraticChar (ZMod p) a = -1` via modular
exponentiation `a ^ ((p - 1) / 2) mod p = p - 1`. Returns `false` for `p < 3`. -/
def isQuadraticNonresidueMod (p a : ℕ) : Bool :=
  decide (3 ≤ p) && decide (powMod p a ((p - 1) / 2) = p - 1)

private lemma powMod_half_eq_val_quadraticChar {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (a : ℕ) :
    ((powMod p a ((p - 1) / 2) : ℕ) : ZMod p) =
      (quadraticChar (ZMod p) (a : ZMod p) : ZMod p) := by
  have hp : p.Prime := Fact.out
  have hodd : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two hp2)
  have hdiv : (p - 1) / 2 = p / 2 := by omega
  have hrc : ringChar (ZMod p) ≠ 2 := by rwa [ZMod.ringChar_zmod_n]
  rw [powMod_of_ne_zero hp.ne_zero, hdiv, ZMod.natCast_mod, Nat.cast_pow,
    quadraticChar_eq_pow_of_char_ne_two' hrc, ZMod.card]

/-- Correctness of Euler-criterion modular exponentiation: for every odd prime `p` and `a : ℕ`,
`legendrePowMod p a = quadraticChar (ZMod p) (a : ZMod p)`. -/
theorem legendrePowMod_eq_quadraticChar {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (a : ℕ) :
    legendrePowMod p a = quadraticChar (ZMod p) (a : ZMod p) := by
  have hp : p.Prime := Fact.out
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hlt : powMod p a ((p - 1) / 2) < p := by
    rw [powMod_of_ne_zero hp.ne_zero]
    exact Nat.mod_lt _ hp.pos
  have hcast := powMod_half_eq_val_quadraticChar hp2 a
  unfold legendrePowMod
  simp only [show ¬ p ≤ 2 by omega, ↓reduceIte]
  by_cases ha0 : (a : ZMod p) = 0
  · rw [ha0, quadraticChar_zero, Int.cast_zero] at hcast
    rw [ha0, quadraticChar_zero]
    have hval0 : powMod p a ((p - 1) / 2) = 0 := by
      have hmod := (ZMod.natCast_eq_zero_iff _ _).mp hcast
      exact Nat.eq_zero_of_dvd_of_lt hmod hlt
    rw [hval0]
    simp only [show (0 : ℕ) ≠ 1 by omega, show (0 : ℕ) ≠ p - 1 by omega, ↓reduceIte]
  · rcases quadraticChar_dichotomy ha0 with h1 | hm1
    · rw [h1, Int.cast_one] at hcast
      rw [h1]
      have hval1 : powMod p a ((p - 1) / 2) = 1 := by
        have h1cast : ((powMod p a ((p - 1) / 2) : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) := by
          simpa using hcast
        have hmod := (ZMod.natCast_eq_natCast_iff' _ _ _).mp h1cast
        rwa [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt (by omega : 1 < p)] at hmod
      simp only [hval1, ↓reduceIte]
    · rw [hm1, Int.cast_neg, Int.cast_one] at hcast
      rw [hm1]
      have hneg1 : ((-1 : ZMod p)) = ((p - 1 : ℕ) : ZMod p) := by
        rw [Nat.cast_sub (by omega : 1 ≤ p), ZMod.natCast_self, Nat.cast_one, zero_sub]
      rw [hneg1] at hcast
      have hvalm1 : powMod p a ((p - 1) / 2) = p - 1 := by
        have hmod := (ZMod.natCast_eq_natCast_iff' _ _ _).mp hcast
        rwa [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt (by omega : p - 1 < p)] at hmod
      rw [hvalm1]
      simp only [show p - 1 ≠ 1 by omega, ↓reduceIte]

/-- Agreement of `legendrePowMod` with Mathlib's `legendreSym` for every odd prime `p`. -/
theorem legendrePowMod_eq_legendreSym {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (a : ℕ) :
    legendrePowMod p a = legendreSym p (a : ℤ) := by
  rw [legendrePowMod_eq_quadraticChar hp2 a, legendreSym, Int.cast_natCast]

/-- Correctness of `isQuadraticNonresidueMod`: for every odd prime `p` and `a : ℕ`,
`isQuadraticNonresidueMod p a = true ↔ quadraticChar (ZMod p) (a : ZMod p) = -1`. -/
theorem isQuadraticNonresidueMod_eq_true_iff {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (a : ℕ) :
    isQuadraticNonresidueMod p a = true ↔ quadraticChar (ZMod p) (a : ZMod p) = -1 := by
  have hp : p.Prime := Fact.out
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  rw [← legendrePowMod_eq_quadraticChar hp2 a]
  unfold isQuadraticNonresidueMod legendrePowMod
  simp only [hp3, show ¬ p ≤ 2 by omega, decide_true, Bool.true_and, ↓reduceIte, decide_eq_true_eq]
  by_cases h1 : powMod p a ((p - 1) / 2) = 1
  · simp only [h1, ↓reduceIte]
    exact ⟨fun h ↦ by omega, fun h ↦ by norm_num at h⟩
  · by_cases hm1 : powMod p a ((p - 1) / 2) = p - 1
    · simp only [hm1, show p - 1 ≠ 1 by omega, ↓reduceIte]
    · simp only [h1, hm1, ↓reduceIte]
      exact ⟨False.elim, fun h ↦ by norm_num at h⟩

/-- Computing `legendrePowMod` via modular exponentiation runs in polynomial time on binary
inputs. -/
theorem computableInPolyTime_legendrePowMod :
    ComputableInPolyTime (fun x : ℕ × ℕ ↦ legendrePowMod x.1 x.2)
      (encPair encNat encNat) encIntBin := by
  have hP : ComputableInPolyTime (fun x : ℕ × ℕ ↦ x.1) (encPair encNat encNat) encNat := by
    fun_prop
  have hA : ComputableInPolyTime (fun x : ℕ × ℕ ↦ x.2) (encPair encNat encNat) encNat := by
    fun_prop
  have hPm1 : ComputableInPolyTime (fun x : ℕ × ℕ ↦ x.1 - 1) (encPair encNat encNat) encNat :=
    ComputableInPolyTime.binary_sub' hP (.const 1)
  have hExp : ComputableInPolyTime (fun x : ℕ × ℕ ↦ (x.1 - 1) / 2)
      (encPair encNat encNat) encNat :=
    ComputableInPolyTime.binary_div' hPm1 (.const 2)
  have hPow : ComputableInPolyTime (fun x : ℕ × ℕ ↦ powMod x.1 x.2 ((x.1 - 1) / 2))
      (encPair encNat encNat) encNat :=
    computableInPolyTime_powMod hP hA hExp
  unfold legendrePowMod
  exact ComputableInPolyTime.ite_decide
    (ComputableInPolyTime.binary_le' hP (.const 2))
    (.const (0 : ℤ))
    (ComputableInPolyTime.ite_decide
      (ComputableInPolyTime.decide_eq' hPow (.const 1))
      (.const (1 : ℤ))
      (ComputableInPolyTime.ite_decide
        (ComputableInPolyTime.decide_eq' hPow hPm1)
        (.const (-1 : ℤ))
        (.const (0 : ℤ))))

/-- Testing quadratic nonresiduosity via modular exponentiation runs in polynomial time on binary
inputs. -/
theorem computableInPolyTime_isQuadraticNonresidueMod :
    ComputableInPolyTime (fun x : ℕ × ℕ ↦ isQuadraticNonresidueMod x.1 x.2)
      (encPair encNat encNat) encBool := by
  have hP : ComputableInPolyTime (fun x : ℕ × ℕ ↦ x.1) (encPair encNat encNat) encNat := by
    fun_prop
  have hA : ComputableInPolyTime (fun x : ℕ × ℕ ↦ x.2) (encPair encNat encNat) encNat := by
    fun_prop
  have hPm1 : ComputableInPolyTime (fun x : ℕ × ℕ ↦ x.1 - 1) (encPair encNat encNat) encNat :=
    ComputableInPolyTime.binary_sub' hP (.const 1)
  have hExp : ComputableInPolyTime (fun x : ℕ × ℕ ↦ (x.1 - 1) / 2)
      (encPair encNat encNat) encNat :=
    ComputableInPolyTime.binary_div' hPm1 (.const 2)
  have hPow : ComputableInPolyTime (fun x : ℕ × ℕ ↦ powMod x.1 x.2 ((x.1 - 1) / 2))
      (encPair encNat encNat) encNat :=
    computableInPolyTime_powMod hP hA hExp
  unfold isQuadraticNonresidueMod
  exact ComputableInPolyTime.bool_and'
    (ComputableInPolyTime.binary_le' (.const 3) hP)
    (ComputableInPolyTime.decide_eq' hPow hPm1)

/-- The `T` candidate `k`-bit integers in `[2 ^ (k - 1), 2 ^ k)` parsed from `T` blocks of
`k - 1` bits in `bits`. -/
def windowCandidates (k T : ℕ) (bits : List Bool) : List ℕ :=
  (listRows T (k - 1) bits).map fun row ↦ 2 ^ (k - 1) + binaryValue row

/-- The first prime candidate in `windowCandidates k T bits` accepted by `isPrime`, or `0` if none
is accepted. -/
def firstPrimeInWindow (isPrime : ℕ → Bool) (k T : ℕ) (bits : List Bool) : ℕ :=
  ((windowCandidates k T bits).find? isPrime).getD 0

private lemma mem_windowCandidates_bounds {k T c : ℕ} {bits : List Bool} (hk : 1 ≤ k)
    (hc : c ∈ windowCandidates k T bits) : 2 ^ (k - 1) ≤ c ∧ c < 2 ^ k := by
  obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp hc
  have hlen : row.length = k - 1 := by
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hrow
    simp [listRow]
  have hlt : binaryValue row < 2 ^ (k - 1) := by
    simpa [hlen] using binaryValue_lt_two_pow row
  have hpow : 2 ^ k = 2 ^ (k - 1) + 2 ^ (k - 1) := by
    have : k = (k - 1) + 1 := by omega
    conv_lhs => rw [this, pow_succ, mul_two]
  omega

/-- If `firstPrimeInWindow isPrime k T bits` returns a nonzero integer `p` (with `k ≥ 1` and
`isPrime` deciding primality), then `p` is a prime in `[2 ^ (k - 1), 2 ^ k)`. -/
theorem firstPrimeInWindow_spec {isPrime : ℕ → Bool}
    (hisPrime : ∀ n, isPrime n = true ↔ n.Prime) {k T : ℕ} (hk : 1 ≤ k) (bits : List Bool)
    (hne : firstPrimeInWindow isPrime k T bits ≠ 0) :
    (firstPrimeInWindow isPrime k T bits).Prime ∧
      2 ^ (k - 1) ≤ firstPrimeInWindow isPrime k T bits ∧
      firstPrimeInWindow isPrime k T bits < 2 ^ k := by
  unfold firstPrimeInWindow at hne ⊢
  cases hfind : (windowCandidates k T bits).find? isPrime with
  | none =>
    simp [hfind] at hne
  | some p =>
    simp only [Option.getD_some]
    have hp_mem : p ∈ windowCandidates k T bits := List.mem_of_find?_eq_some hfind
    have hp_prime : p.Prime := (hisPrime p).mp (List.find?_some hfind)
    exact ⟨hp_prime, mem_windowCandidates_bounds hk hp_mem⟩

/-- `firstPrimeInWindow` returns `0` if and only if no candidate block produces a prime. -/
theorem firstPrimeInWindow_eq_zero_iff {isPrime : ℕ → Bool}
    (hisPrime : ∀ n, isPrime n = true ↔ n.Prime) {k T : ℕ} (bits : List Bool) :
    firstPrimeInWindow isPrime k T bits = 0 ↔
      ∀ c ∈ windowCandidates k T bits, ¬ c.Prime := by
  unfold firstPrimeInWindow
  cases hfind : (windowCandidates k T bits).find? isPrime with
  | none =>
    simp only [Option.getD_none, true_iff]
    intro c hc hpc
    have := List.find?_eq_none.mp hfind c hc
    exact this ((hisPrime c).mpr hpc)
  | some p =>
    simp only [Option.getD_some]
    have hp_mem : p ∈ windowCandidates k T bits := List.mem_of_find?_eq_some hfind
    have hp_prime : p.Prime := (hisPrime p).mp (List.find?_some hfind)
    exact ⟨fun hp0 _ _ ↦ absurd hp0 hp_prime.ne_zero, fun hall ↦ absurd hp_prime (hall p hp_mem)⟩

private lemma card_filter_block_prime {k : ℕ} (hk : 1 ≤ k) :
    (Finset.univ.filter fun u : BitString (k - 1) ↦
        (2 ^ (k - 1) + binaryValue (List.ofFn u)).Prime).card =
      ((Finset.Ico (2 ^ (k - 1)) (2 ^ k)).filter Nat.Prime).card := by
  have hpow : 2 ^ k = 2 ^ (k - 1) + 2 ^ (k - 1) := by
    have : k = (k - 1) + 1 := by omega
    conv_lhs => rw [this, pow_succ, mul_two]
  refine Finset.card_bij (fun u _ ↦ 2 ^ (k - 1) + binaryValue (List.ofFn u)) ?_ ?_ ?_
  · intro u hu
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
    have hlt : binaryValue (List.ofFn u) < 2 ^ (k - 1) := by
      simpa using binaryValue_lt_two_pow (List.ofFn u)
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by omega, by omega⟩, hu⟩
  · intro u₁ _ u₂ _ heq
    have hbv : binaryValue (List.ofFn u₁) = binaryValue (List.ofFn u₂) := by omega
    have hlist := binaryValue_injective_of_length_eq (by simp) hbv
    exact List.ofFn_inj.mp hlist
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_Ico] at hp
    obtain ⟨u, hu⟩ := exists_binaryValue_eq (t := k - 1) (k := p - 2 ^ (k - 1)) (by omega)
    refine ⟨u, ?_, by omega⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have : 2 ^ (k - 1) + binaryValue (List.ofFn u) = p := by omega
    simpa [this] using hp.2

/-- Failure probability of random `k`-bit prime sampling: for `1 < k` and `s : ℕ`, testing
`T = 3 * s * k` independent random `(k - 1)`-bit blocks for primality fails to produce a `k`-bit
prime with probability at most `2 ^ (-s)`. -/
theorem two_pow_mul_card_filter_firstPrimeInWindow_eq_zero_le {isPrime : ℕ → Bool}
    (hisPrime : ∀ n, isPrime n = true ↔ n.Prime) {k : ℕ} (hk : 1 < k) (s : ℕ) :
    2 ^ s * (Finset.univ.filter fun r : BitString (3 * s * k * (k - 1)) ↦
        firstPrimeInWindow isPrime k (3 * s * k) (List.ofFn r) = 0).card ≤
      2 ^ (3 * s * k * (k - 1)) := by
  have h1 : 1 ≤ k := by omega
  set T := 3 * s * k with hT
  have hfilt :
      (Finset.univ.filter fun r : BitString (T * (k - 1)) ↦
          firstPrimeInWindow isPrime k T (List.ofFn r) = 0) =
        Finset.univ.filter fun r : BitString (T * (k - 1)) ↦
          ∀ i : Fin T, ¬ (2 ^ (k - 1) + binaryValue (List.ofFn (block r i))).Prime := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      firstPrimeInWindow_eq_zero_iff hisPrime, windowCandidates, listRows_ofFn,
      List.mem_map, List.mem_ofFn]
    constructor
    · intro h i
      exact h _ ⟨List.ofFn (block r i), ⟨i, rfl⟩, rfl⟩
    · rintro h c ⟨row, ⟨i, rfl⟩, rfl⟩
      exact h i
  rw [hfilt, card_filter_forall_block T (k - 1)
    (fun u ↦ ¬ (2 ^ (k - 1) + binaryValue (List.ofFn u)).Prime)]
  set P := (Finset.univ.filter fun u : BitString (k - 1) ↦
    (2 ^ (k - 1) + binaryValue (List.ofFn u)).Prime).card with hP
  set F := (Finset.univ.filter fun u : BitString (k - 1) ↦
    ¬ (2 ^ (k - 1) + binaryValue (List.ofFn u)).Prime).card with hF
  have hPF : P + F = 2 ^ (k - 1) := by
    have hsp := Finset.card_filter_add_card_filter_not (s :=
      (Finset.univ : Finset (BitString (k - 1))))
      (fun u ↦ (2 ^ (k - 1) + binaryValue (List.ofFn u)).Prime)
    simpa [hP, hF] using hsp
  have hdens : 2 ^ (k - 1) ≤ 3 * k * P := by
    rw [hP, card_filter_block_prime h1]
    exact Nat.two_pow_sub_one_le_three_mul_card_primes hk
  have hstep : 2 * F ^ (3 * k) ≤ (2 ^ (k - 1)) ^ (3 * k) := by
    have hpos : (0 : ℝ) < (2 : ℝ) ^ (k - 1) := by positivity
    let x : ℝ := (P : ℝ) / (2 : ℝ) ^ (k - 1)
    have hx0 : 0 ≤ x := by positivity
    have hx1 : x ≤ 1 := (div_le_one hpos).mpr (by exact_mod_cast (by omega : P ≤ 2 ^ (k - 1)))
    have hkx : (1 : ℝ) ≤ (3 * k : ℕ) * x := by
      rw [← mul_div_assoc, le_div_iff₀ hpos, one_mul]
      exact_mod_cast hdens
    have hB := Cslib.one_sub_pow_mul_one_add_mul_le_one hx0 hx1 (3 * k)
    have hFr : (F : ℝ) = (2 : ℝ) ^ (k - 1) * (1 - x) := by
      have : (P : ℝ) + (F : ℝ) = (2 : ℝ) ^ (k - 1) := by exact_mod_cast hPF
      rw [mul_sub, mul_one, mul_div_cancel₀ _ hpos.ne']
      linarith
    suffices (2 : ℝ) * (F : ℝ) ^ (3 * k) ≤ ((2 : ℝ) ^ (k - 1)) ^ (3 * k) by exact_mod_cast this
    rw [hFr, mul_pow]
    have hpow_nonneg : 0 ≤ (1 - x) ^ (3 * k) := pow_nonneg (sub_nonneg.mpr hx1) _
    have htwo_le : (2 : ℝ) * (1 - x) ^ (3 * k) ≤ 1 := by nlinarith
    have h2pow_pos : (0 : ℝ) < ((2 : ℝ) ^ (k - 1)) ^ (3 * k) := by positivity
    nlinarith
  have hpow_step : (2 * F ^ (3 * k)) ^ s ≤ ((2 ^ (k - 1)) ^ (3 * k)) ^ s :=
    Nat.pow_le_pow_left hstep s
  rw [mul_pow, ← pow_mul, ← pow_mul, ← pow_mul] at hpow_step
  have hE1 : 3 * k * s = T := by rw [hT]; ring
  rw [hE1, mul_comm (k - 1) T] at hpow_step
  exact hpow_step

/-- Extracting `firstPrimeInWindow` is computable in polynomial time whenever `isPrime` is a
polynomial-time primality test. -/
theorem computableInPolyTime_firstPrimeInWindow {α : Type} {input : α ↪ List Bool}
    {isPrime : ℕ → Bool} (hisPrime : ComputableInPolyTime isPrime encNat encBool)
    {k T : α → ℕ} {bits : α → List Bool}
    (hk : ComputableInPolyTime k input encUnary)
    (hT : ComputableInPolyTime T input encUnary)
    (hbits : ComputableInPolyTime bits input encBits) :
    ComputableInPolyTime (fun a ↦ firstPrimeInWindow isPrime (k a) (T a) (bits a))
      input encNat := by
  have hk1 : ComputableInPolyTime (fun a ↦ k a - 1) input encUnary :=
    ComputableInPolyTime.unary_sub' hk (.const 1)
  have hpow : ComputableInPolyTime (fun a ↦ 2 ^ (k a - 1)) input encNat :=
    ComputableInPolyTime.binary_two_pow.comp hk1
  have hrows : ComputableInPolyTime (fun a ↦ listRows (T a) (k a - 1) (bits a))
      input (encList encBits) :=
    ComputableInPolyTime.bitsRowsWithInput hT hk1 hbits
  have hcand : ComputableInPolyTime (fun a ↦ windowCandidates (k a) (T a) (bits a))
      input (encList encNat) := by
    unfold windowCandidates
    exact ComputableInPolyTime.mapWith
      (f := fun p : ℕ × List Bool ↦ p.1 + binaryValue p.2)
      (ComputableInPolyTime.binary_add' (.fst encNat encBits)
        (ComputableInPolyTime.bitsBinaryValue.comp (.snd encNat encBits)))
      hpow hrows
  have hfind : ComputableInPolyTime
      (fun a ↦ (windowCandidates (k a) (T a) (bits a)).find? isPrime)
      input (encOption encNat) :=
    ComputableInPolyTime.findWith (encP := encBool) (encA := encNat)
      (test := fun p : Bool × ℕ ↦ isPrime p.2)
      (hisPrime.comp (.snd encBool encNat)) (.const false) hcand
  unfold firstPrimeInWindow
  exact ComputableInPolyTime.optionGetDWithInput hfind (.const 0)

/-- Existence of a deterministic polynomial-time primality decider from
`Cslib.Complexity.primes_mem_P`. -/
theorem exists_computableInPolyTime_isPrime :
    ∃ isPrime : ℕ → Bool,
      ComputableInPolyTime isPrime encNat encBool ∧ ∀ n : ℕ, isPrime n = true ↔ n.Prime := by
  obtain ⟨f, hf, hspec⟩ := Cslib.Complexity.primes_mem_P
  exact ⟨f, hf, fun n ↦ (hspec n).symm⟩

/-- Exact integer lower bound for modular sampling: reducing a uniform `(k + e)`-bit string modulo
any positive `p` hits any predicate `P : ZMod p → Prop` at least `(2 ^ (k + e) / p) * |{b | P b}|`
times. -/
theorem card_filter_binaryValue_mod_ge {p k e : ℕ} [NeZero p]
    (P : ZMod p → Prop) [DecidablePred P] :
    (2 ^ (k + e) / p) * (Finset.univ.filter P).card ≤
      (Finset.univ.filter fun r : BitString (k + e) ↦
        P (binaryValue (List.ofFn r) : ZMod p)).card := by
  have hp : 0 < p := NeZero.pos p
  set q := 2 ^ (k + e) / p with hq
  have hqp : q * p ≤ 2 ^ (k + e) := Nat.div_mul_le_self (2 ^ (k + e)) p
  let A : Finset (Fin p) := Finset.univ.filter fun b : Fin p ↦ P (b.val : ZMod p)
  have hAcard : A.card = (Finset.univ.filter P).card := by
    refine Finset.card_bij (fun b _ ↦ (b.val : ZMod p)) ?_ ?_ ?_
    · intro b hb
      simpa [A] using hb
    · intro b₁ _ b₂ _ heq
      have hmod := (ZMod.natCast_eq_natCast_iff' b₁.val b₂.val p).mp heq
      rw [Nat.mod_eq_of_lt b₁.isLt, Nat.mod_eq_of_lt b₂.isLt] at hmod
      exact Fin.ext hmod
    · intro z hz
      refine ⟨⟨z.val, ZMod.val_lt z⟩, ?_, by simp⟩
      simpa [A] using hz
  have hlt (j : Fin q) (b : Fin p) : j.val * p + b.val < 2 ^ (k + e) := by
    have h1 : j.val * p + b.val < (j.val + 1) * p := by
      rw [Nat.add_mul, Nat.one_mul]
      omega
    have h2 : (j.val + 1) * p ≤ q * p := Nat.mul_le_mul_right p j.isLt
    omega
  let embed : Fin q × Fin p → BitString (k + e) := fun jb i ↦
    (binaryWord (k + e) (jb.1.val * p + jb.2.val))[i.val]'(by
      rw [length_binaryWord (hlt jb.1 jb.2)]
      exact i.isLt)
  have hembed_val (jb : Fin q × Fin p) :
      binaryValue (List.ofFn (embed jb)) = jb.1.val * p + jb.2.val := by
    have hlist : List.ofFn (embed jb) = binaryWord (k + e) (jb.1.val * p + jb.2.val) :=
      List.ext_getElem (by simp [length_binaryWord (hlt jb.1 jb.2)]) fun i _ _ ↦ by simp [embed]
    rw [hlist, binaryValue_binaryWord]
  have hembed_inj : Function.Injective embed := by
    intro jb₁ jb₂ heq
    have hval : jb₁.1.val * p + jb₁.2.val = jb₂.1.val * p + jb₂.2.val := by
      rw [← hembed_val jb₁, ← hembed_val jb₂, heq]
    have hb : jb₁.2.val = jb₂.2.val := by
      have h1 := congrArg (· % p) hval
      simp only [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt jb₁.2.isLt,
        Nat.mod_eq_of_lt jb₂.2.isLt] at h1
      exact h1
    have hj : jb₁.1.val = jb₂.1.val := by
      have hmul : jb₁.1.val * p = jb₂.1.val * p := by omega
      exact Nat.eq_of_mul_eq_mul_right hp hmul
    exact Prod.ext (Fin.ext hj) (Fin.ext hb)
  have hsub : ((Finset.univ : Finset (Fin q)) ×ˢ A).image embed ⊆
      Finset.univ.filter fun r : BitString (k + e) ↦ P (binaryValue (List.ofFn r) : ZMod p) := by
    intro r hr
    obtain ⟨⟨j, b⟩, hjb, rfl⟩ := Finset.mem_image.mp hr
    have hb : P (b.val : ZMod p) := by
      simpa [A] using (Finset.mem_product.mp hjb).2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hembed_val, Nat.cast_add,
      Nat.cast_mul, ZMod.natCast_self, mul_zero, zero_add]
    exact hb
  calc q * (Finset.univ.filter P).card
      = ((Finset.univ : Finset (Fin q)) ×ˢ A).card := by
        rw [Finset.card_product, Finset.card_univ, Fintype.card_fin, hAcard]
    _ = (((Finset.univ : Finset (Fin q)) ×ˢ A).image embed).card :=
        (Finset.card_image_of_injective _ hembed_inj).symm
    _ ≤ (Finset.univ.filter fun r : BitString (k + e) ↦
          P (binaryValue (List.ofFn r) : ZMod p)).card := Finset.card_le_card hsub

/-- Real density bound for modular sampling: for any `0 < p ≤ 2 ^ k`, reducing a uniform
`(k + e)`-bit string modulo `p` hits `P : ZMod p → Prop` with probability at least
`(1 - 1 / 2 ^ e) * |{b | P b}| / p`. -/
theorem density_binaryValue_mod_ge {p k e : ℕ} [NeZero p] (hp_le : p ≤ 2 ^ k)
    (P : ZMod p → Prop) [DecidablePred P] :
    (1 - 1 / (2 : ℝ) ^ e) * ((Finset.univ.filter P).card : ℝ) / (p : ℝ) ≤
      ((Finset.univ.filter fun r : BitString (k + e) ↦
        P (binaryValue (List.ofFn r) : ZMod p)).card : ℝ) / (2 : ℝ) ^ (k + e) := by
  have hp : 0 < p := NeZero.pos p
  have hp_pos : (0 : ℝ) < p := Nat.cast_pos.mpr hp
  have h2ke_pos : (0 : ℝ) < (2 : ℝ) ^ (k + e) := by positivity
  have h2e_pos : (0 : ℝ) < (2 : ℝ) ^ e := by positivity
  have hnat := card_filter_binaryValue_mod_ge (k := k) (e := e) P
  have hdiv_mod : 2 ^ (k + e) = (2 ^ (k + e) / p) * p + 2 ^ (k + e) % p := by
    rw [mul_comm]
    exact (Nat.div_add_mod (2 ^ (k + e)) p).symm
  have hrem_lt : 2 ^ (k + e) % p < p := Nat.mod_lt _ hp
  have hqp_ge : 2 ^ (k + e) - 2 ^ k ≤ (2 ^ (k + e) / p) * p := by omega
  have h2k_le : 2 ^ k ≤ 2 ^ (k + e) := Nat.pow_le_pow_right (by norm_num) (Nat.le_add_right k e)
  have hqp_real : (1 - 1 / (2 : ℝ) ^ e) * (2 : ℝ) ^ (k + e) ≤ ((2 ^ (k + e) / p : ℕ) : ℝ) * p := by
    have hsub : ((2 ^ (k + e) - 2 ^ k : ℕ) : ℝ) ≤ ((2 ^ (k + e) / p : ℕ) : ℝ) * p := by
      exact_mod_cast hqp_ge
    rw [Nat.cast_sub h2k_le, Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat] at hsub
    have heq : (1 - 1 / (2 : ℝ) ^ e) * (2 : ℝ) ^ (k + e) = (2 : ℝ) ^ (k + e) - (2 : ℝ) ^ k := by
      rw [pow_add]
      field_simp
    linarith
  have hnat_real : ((2 ^ (k + e) / p : ℕ) : ℝ) * ((Finset.univ.filter P).card : ℝ) ≤
      ((Finset.univ.filter fun r : BitString (k + e) ↦
        P (binaryValue (List.ofFn r) : ZMod p)).card : ℝ) := by
    exact_mod_cast hnat
  rw [div_le_div_iff₀ hp_pos h2ke_pos]
  calc (1 - 1 / (2 : ℝ) ^ e) * ((Finset.univ.filter P).card : ℝ) * (2 : ℝ) ^ (k + e)
      = ((1 - 1 / (2 : ℝ) ^ e) * (2 : ℝ) ^ (k + e)) * ((Finset.univ.filter P).card : ℝ) := by
        ring
    _ ≤ (((2 ^ (k + e) / p : ℕ) : ℝ) * p) * ((Finset.univ.filter P).card : ℝ) :=
        mul_le_mul_of_nonneg_right hqp_real (Nat.cast_nonneg _)
    _ = (((2 ^ (k + e) / p : ℕ) : ℝ) * ((Finset.univ.filter P).card : ℝ)) * (p : ℝ) := by ring
    _ ≤ ((Finset.univ.filter fun r : BitString (k + e) ↦
          P (binaryValue (List.ofFn r) : ZMod p)).card : ℝ) * (p : ℝ) :=
        mul_le_mul_of_nonneg_right hnat_real hp_pos.le

end CslibFrontier.Complexity
