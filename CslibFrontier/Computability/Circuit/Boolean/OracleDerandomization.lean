module

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Pair
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Unary
public import CslibFrontier.Computability.Circuit.Boolean.OracleHardness
import CslibFrontier.Computability.Complexity.Classes.BPP.Derandomization.Generator
import CslibFrontier.Computability.Complexity.HardnessEncoding.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log
import CslibFrontier.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial.Automation
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Uniform Relativized Nisan–Wigderson Hitting Generators and Range Avoidance

Building on the relativized oracle-circuit hardness amplification of
`CslibFrontier.Computability.Circuit.Boolean.OracleHardness`, this module constructs uniform
polynomial-time logarithmic-seed Nisan–Wigderson hitting-set generators avoiding every sparse slice
of an `NP` language under `ENPHypothesis`, and derives uniform polynomial-time range-avoidance
bounds for arbitrary strictly increasing stretching maps (`exists_polyTime_avoid_polyStretch_of_enp`
and its one-bit-stretch specialization `exists_polyTime_avoid_stretching_of_enp`) under standard
Lean axioms.

## Main results

* `CslibFrontier.Computability.exists_polyTime_hittingGenerator_of_oracleHard`: from `L ∈ E`
  avoiding `i.o.-Size^A(2^{ε n})`, builds a uniform polynomial-time logarithmic-seed hitting
  generator avoiding every slice of `A` of density at most `3 / 4`.
* `CslibFrontier.Computability.exists_polyTime_rangeAvoidance_of_enp`: specializes hitting-set
  generation under `ENPHypothesis` to arbitrary `A ∈ NP`.
* `CslibFrontier.Computability.exists_polyTime_avoid_polyStretch_of_enp`: under `ENPHypothesis`,
  every uniform polynomial-time stretching generator `g_n : {0,1}^n → {0,1}^{m(n)}` (with `n < m(n)`
  and `m` strictly increasing) admits a uniform polynomial-time logarithmic-seed map `H` hitting
  outside `Rng(g_n)` for every `n ≥ 1`.
* `CslibFrontier.Computability.exists_polyTime_avoid_stretching_of_enp`: specialization to one-bit
  stretch `m(N) = N + 1` with seeds of length `c * ⌊log₂ N⌋`.


-/

public section

namespace CslibFrontier.Computability

open Filter Finset
open Cslib Cslib.Circuits Cslib.Circuits.Boolean Cslib.Complexity
open Cslib.Crypto.PRG.NisanWigderson Cslib.HardnessEncoding
open Turing.MultiTapeTM

private theorem nw_hitting_bounds {c M τ : ℕ} (hc : 0 < c) (hτ3 : 3 ≤ τ)
    (hBτ : 8 * (M + 6) ≤ 2 ^ τ) :
    M ≤ (greedyMasks ((2 ^ (8 * c + 1) + 1) * τ) (c * (4 * τ)) (τ - 1)).length ∧
    1 + 1 + M * (2 ^ (τ - 1) * (2 * (τ - 1) + 3) + 1) + 1 ≤ 2 ^ (4 * τ) ∧
    (M : ℝ) < 1 / 6 * ((2 ^ (4 * τ) : ℕ) : ℝ) ∧
    M ≤ 2 ^ (4 * τ) := by
  set b := 2 ^ (8 * c + 1) with hb
  set P := 2 ^ τ with hP
  have hP8 : 8 ≤ P := (Nat.pow_le_pow_right two_pos hτ3).trans_eq' rfl
  have hc4 : c * 4 ≤ b + 1 := by
    have h₁ : c < 2 ^ c := Nat.lt_two_pow_self
    have h₂ : 2 ^ c * 4 ≤ b := by
      rw [hb, show 2 ^ c * 4 = 2 ^ (c + 2) by rw [pow_add]; rfl]
      exact Nat.pow_le_pow_right two_pos (by omega)
    omega
  have hlen : M ≤ (greedyMasks ((b + 1) * τ) (c * (4 * τ)) (τ - 1)).length := by
    refine le_length_greedyMasks (by omega) (by nlinarith) (by nlinarith) ?_
    calc 4 ^ (c * (4 * τ)) * M ≤ 4 ^ (c * (4 * τ)) * P := Nat.mul_le_mul_left _ (by omega)
      _ = b ^ τ := by
        rw [hb, hP, ← pow_mul, show (4 : ℕ) = 2 ^ 2 by rfl, ← pow_mul, ← pow_add]; ring_nf
  have hY : 2 ^ (τ - 1) * (2 * (τ - 1) + 3) + 1 ≤ P ^ 2 := by
    have hQ : 2 ^ (τ - 1) * 2 = P := by rw [hP, ← pow_succ, Nat.sub_add_cancel (by omega)]
    have := Nat.lt_two_pow_self (n := τ - 1)
    have := @Nat.one_le_two_pow (τ - 1)
    rw [← hQ]; nlinarith
  have h₂ : 8 * (M * P ^ 2) ≤ P ^ 3 :=
    calc 8 * (M * P ^ 2) = 8 * M * P ^ 2 := by ring
      _ ≤ P * P ^ 2 := Nat.mul_le_mul_right _ (by omega)
      _ = P ^ 3 := by ring
  have h₃ : 8 * P ^ 3 ≤ P ^ 4 := by
    rw [pow_succ P 3, mul_comm (P ^ 3)]; exact Nat.mul_le_mul_right _ hP8
  have h₄ : P ≤ P ^ 4 := Nat.le_self_pow (by norm_num) P
  have h₁ := Nat.mul_le_mul_left M hY
  have hP4 : 2 ^ (4 * τ) = P ^ 4 := by rw [mul_comm 4 τ, pow_mul, hP]
  have h6M : 6 * M < 2 ^ (4 * τ) := by rw [hP4]; omega
  refine ⟨hlen, by rw [hP4]; omega, ?_, by rw [hP4]; omega⟩
  have h6M' : (6 * M : ℝ) < ((2 ^ (4 * τ) : ℕ) : ℝ) := by exact_mod_cast h6M
  linarith

private theorem eight_mul_add_six_le_two_pow (K₀ M : ℕ) (hM2 : 2 ≤ M) :
    8 * (M + 6) ≤ 2 ^ (K₀ + 6 + 2 * (Nat.log 2 M + 1)) := by
  have hlt : M + 1 ≤ 2 ^ (Nat.log 2 M + 1) := Nat.lt_pow_succ_log_self one_lt_two M
  set R := 2 ^ (Nat.log 2 M + 1)
  have hR4 : 4 ≤ R := by omega
  have h64 : 64 ≤ 2 ^ (K₀ + 6) :=
    (show 64 = 2 ^ 6 by norm_num) ▸ Nat.pow_le_pow_right two_pos (Nat.le_add_left 6 K₀)
  calc 8 * (M + 6) ≤ 64 * (R * R) := by nlinarith
    _ ≤ 2 ^ (K₀ + 6) * (R * R) := Nat.mul_le_mul_right _ h64
    _ = 2 ^ (K₀ + 6 + 2 * (Nat.log 2 M + 1)) := by
        dsimp only [R]; rw [← pow_add, two_mul, ← pow_add]

/-- **Relativized Nisan–Wigderson polynomial-time hitting-set generator.** Let `L ∈ E` avoid
`i.o.-Size^A(2^{ε n})` for some `ε > 0`. Then there exist a constant `c ≥ 1` and a uniform
polynomial-time map `H : ℕ × List Bool → List Bool` (taking target output length `M` in unary and
seed `z` as a bitstring) such that:
1. `(H (M, z)).length = M` for all `M` and `z`;
2. for all `M ≥ 2`, if `A`'s slice at length `M` contains at most `(3 / 4) * 2 ^ M` strings, then
   some seed `z` of length `c * ⌊log₂ M⌋` yields `H (M, List.ofFn z) ∉ A`. -/
theorem exists_polyTime_hittingGenerator_of_oracleHard {A L : Language Bool}
    (hL : (L : Set (List Bool)) ∈ E encBits) {ε : ℝ} (hε : 0 < ε)
    (hard : L ∉ oracleSIZEInfOften A (fun n => (2 : ℝ) ^ (ε * (n : ℝ)))) :
    ∃ (c : ℕ) (H : ℕ × List Bool → List Bool),
      1 ≤ c ∧
      ComputableInPolyTime H (encPair encUnary encBits) encBits ∧
      (∀ M z, (H (M, z)).length = M) ∧
      ∀ M, 2 ≤ M → ((#{y : BitString M | A.slice M y = true} : ℕ) : ℝ) ≤ 3 / 4 * (2 : ℝ) ^ M →
        ∃ z : BitString (c * Nat.log 2 M), H (M, List.ofFn z) ∉ A := by
  set M₀ := oracleBlockFactor ε
  set d := oracleHardnessDivisor ε
  have hd : 0 < d := oracleHardnessDivisor_pos ε
  set L' := encodedLanguage L M₀
  have hL' : (L' : Set (List Bool)) ∈ E encBits := encodedLanguage_mem_E hL M₀
  obtain ⟨k, hk⟩ := mem_E_iff.1 hL'
  obtain ⟨g, hgL', hg⟩ := exists_computableInO_of_mem_DTIME hk
  have hslice (K : ℕ) : (fun y : Fin K → Bool => g (List.ofFn y)) = L'.slice K := by
    funext y; rw [Bool.eq_iff_iff, Language.slice_eq_true_iff, ← hgL']; rfl
  obtain ⟨K₀, hK₀⟩ := eventually_atTop.1 (eventually_isOracleAverageCaseHard_encodedSlice hε hard)
  let τ : ℕ → ℕ := fun M => K₀ + 6 + 2 * (Nat.log 2 M + 1)
  let b : ℕ := 2 ^ (8 * d + 1)
  let seedLen : ℕ → ℕ := fun M => (b + 1) * τ M
  let blockLen : ℕ → ℕ := fun M => d * (4 * τ M)
  let overlapLen : ℕ → ℕ := fun M => τ M - 1
  let c : ℕ := (b + 1) * (K₀ + 10)
  have hc1 : 1 ≤ c := Nat.mul_pos (Nat.succ_pos b) (by omega)
  let raw : ℕ × List Bool → List Bool := fun p =>
    listGenerator g (blockLen p.1)
      ((greedyMasks (seedLen p.1) (blockLen p.1) (overlapLen p.1)).take p.1)
      ((p.2 ++ List.replicate (seedLen p.1) false).take (seedLen p.1))
  let H : ℕ × List Bool → List Bool := fun p =>
    (raw p ++ List.replicate p.1 false).take p.1
  have hlog2 : ComputableInPolyTime (fun M : ℕ => Nat.log 2 M) encUnary encUnary :=
    ComputableInPolyTime.binary_log_two.comp ComputableInPolyTime.unary_to_binary
  have hτ : ComputableInPolyTime τ encUnary encUnary := by dsimp only [τ]; fun_prop
  have hseed : ComputableInPolyTime seedLen encUnary encUnary := by dsimp only [seedLen]; fun_prop
  have hblock : ComputableInPolyTime blockLen encUnary encUnary := by
    dsimp only [blockLen]; fun_prop
  have hoverlap : ComputableInPolyTime overlapLen encUnary encUnary := by
    dsimp only [overlapLen]; fun_prop
  have hseedB : PolyBounded (fun M : ℕ => (encUnary M).length) (fun M => 2 ^ seedLen M) := by
    dsimp only [seedLen, τ]; growth_poly
  have hblockB : PolyBounded (fun M : ℕ => (encUnary M).length)
      (fun M => 2 ^ (k * blockLen M)) := by
    dsimp only [blockLen, τ]; growth_poly
  have hgen := computableInPolyTime_listGenerator_greedyMasks (enc := encUnary)
    (fun _ _ h => Nat.pow_le_pow_right two_pos (Nat.mul_le_mul_left k h))
    hg hseed hblock hoverlap .id' hseedB hblockB
  have hpadSeed : ComputableInPolyTime
      (fun p : ℕ × List Bool => (p.2 ++ List.replicate (seedLen p.1) false).take (seedLen p.1))
      (encPair encUnary encBits) encBits := by
    have hs1 := hseed.comp (.fst encUnary encBits)
    exact ComputableInPolyTime.bitsTakeWithInput
      (ComputableInPolyTime.bitsAppend (.snd encUnary encBits)
        ((ComputableInPolyTime.bitsReplicate false).comp hs1)) hs1
  have hraw : ComputableInPolyTime raw (encPair encUnary encBits) encBits :=
    hgen.comp ((ComputableInPolyTime.fst encUnary encBits).prod hpadSeed)
  have hH : ComputableInPolyTime H (encPair encUnary encBits) encBits := by
    have hm1 := ComputableInPolyTime.fst encUnary encBits
    exact ComputableInPolyTime.bitsTakeWithInput
      (ComputableInPolyTime.bitsAppend hraw
        ((ComputableInPolyTime.bitsReplicate false).comp hm1)) hm1
  refine ⟨c, H, hc1, hH, fun M z => by simp [H], fun M hM2 hdens => ?_⟩
  obtain ⟨hmask, hs, hεs, hrle⟩ :=
    nw_hitting_bounds hd (by omega) (eight_mul_add_six_le_two_pow K₀ M hM2)
  have hKle : K₀ ≤ blockLen M :=
    calc K₀ ≤ 4 * τ M := by dsimp only [τ]; omega
      _ = 1 * (4 * τ M) := (one_mul _).symm
      _ ≤ d * (4 * τ M) := Nat.mul_le_mul_right _ hd
  have hhardK : IsOracleAverageCaseHard A (L'.slice (blockLen M)) M (2 ^ (4 * τ M)) := by
    have h1 := hK₀ (blockLen M) hKle
    rw [Nat.mul_div_cancel_left _ hd] at h1
    simpa only [L', slice_encodedLanguage] using h1 M hrle
  have hgap := abs_card_div_sub_card_div_lt_boundedOracle A
    (Design.greedy (seedLen M) (blockLen M) (overlapLen M) M hmask)
    hhardK hs hεs (A.slice M) (complexity_boundedOracle_slice_le_one A M)
  have hdiv : ((#{y : BitString M | A.slice M y = true} : ℕ) : ℝ) / 2 ^ M ≤ 3 / 4 := by
    rwa [div_le_iff₀ (by positivity)]
  have hlt1 : ((#{z : BitString (seedLen M) |
      A.slice M (generator (Design.greedy (seedLen M) (blockLen M) (overlapLen M) M hmask)
        (L'.slice (blockLen M)) z) = true} : ℕ) : ℝ) < (2 : ℝ) ^ seedLen M := by
    have h1 : ((#{z : BitString (seedLen M) |
        A.slice M (generator (Design.greedy (seedLen M) (blockLen M) (overlapLen M) M hmask)
          (L'.slice (blockLen M)) z) = true} : ℕ) : ℝ) / 2 ^ seedLen M < 1 := by
      linarith [(abs_lt.1 hgap).2, hdiv]
    rwa [div_lt_one (by positivity)] at h1
  have hcard_lt : #{z : BitString (seedLen M) |
      A.slice M (generator (Design.greedy (seedLen M) (blockLen M) (overlapLen M) M hmask)
        (L'.slice (blockLen M)) z) = true} < #(univ : Finset (BitString (seedLen M))) := by
    rw [card_univ, BitString.card]; exact_mod_cast hlt1
  obtain ⟨z₀, -, hz₀⟩ := exists_mem_notMem_of_card_lt_card hcard_lt
  simp only [mem_filter, mem_univ, true_and, Language.slice_eq_true_iff] at hz₀
  have hseed_le : seedLen M ≤ c * Nat.log 2 M := by
    have hlog1 : 1 ≤ Nat.log 2 M := Nat.log_pos one_lt_two hM2
    have hτle : τ M ≤ (K₀ + 10) * Nat.log 2 M :=
      calc τ M = (K₀ + 8) + 2 * Nat.log 2 M := by dsimp only [τ]; ring
        _ ≤ (K₀ + 8) * Nat.log 2 M + 2 * Nat.log 2 M :=
            Nat.add_le_add_right (le_mul_of_one_le_right (Nat.zero_le _) hlog1) _
        _ = (K₀ + 10) * Nat.log 2 M := by ring
    exact (Nat.mul_le_mul_left (b + 1) hτle).trans_eq (Nat.mul_assoc _ _ _).symm
  let z : BitString (c * Nat.log 2 M) := fun i =>
    if hi : i.val < seedLen M then z₀ ⟨i.val, hi⟩ else false
  refine ⟨z, ?_⟩
  have htake : ((List.ofFn z ++ List.replicate (seedLen M) false).take (seedLen M)) =
      List.ofFn z₀ :=
    List.ext_getElem (by
      rw [List.length_take, List.length_append, List.length_replicate, List.length_ofFn,
        List.length_ofFn, Nat.min_eq_left (Nat.le_add_left _ _)])
      fun i _ h₂ => by
      simp only [List.length_ofFn] at h₂
      have hic : i < (List.ofFn z).length := by rw [List.length_ofFn]; exact h₂.trans_le hseed_le
      rw [List.getElem_take, List.getElem_append_left hic, List.getElem_ofFn, List.getElem_ofFn]
      simp [z, h₂]
  have hraw_eq : raw (M, List.ofFn z) =
      List.ofFn (generator (Design.greedy (seedLen M) (blockLen M) (overlapLen M) M hmask)
        (L'.slice (blockLen M)) z₀) := by
    dsimp only [raw]
    rw [htake, listGenerator_take_greedyMasks hmask, hslice]
  have hHeq : H (M, List.ofFn z) = raw (M, List.ofFn z) := by
    simp only [H, hraw_eq]
    rw [List.take_append_of_le_length (by simp), List.take_of_length_le (by simp)]
  rwa [hHeq, hraw_eq]

/-- **Polynomial-time range avoidance against `NP` from `(E-NP)`.** Assuming `ENPHypothesis`,
for every `A ∈ NP` there exist a constant `c ≥ 1` and a uniform polynomial-time hitting-set map
`H : ℕ × List Bool → List Bool` with `(H (M, z)).length = M` such that for every `M ≥ 2` whose
`M`-bit slice of `A` has cardinality at most `(3 / 4) * 2 ^ M`, some seed `z` of length
`c * ⌊log₂ M⌋` satisfies `H (M, List.ofFn z) ∉ A`. -/
theorem exists_polyTime_rangeAvoidance_of_enp (hENP : ENPHypothesis) {A : Language Bool}
    (hA : (A : Set (List Bool)) ∈ NP encBits) :
    ∃ (c : ℕ) (H : ℕ × List Bool → List Bool),
      1 ≤ c ∧
      ComputableInPolyTime H (encPair encUnary encBits) encBits ∧
      (∀ M z, (H (M, z)).length = M) ∧
      ∀ M, 2 ≤ M → ((#{y : BitString M | A.slice M y = true} : ℕ) : ℝ) ≤ 3 / 4 * (2 : ℝ) ^ M →
        ∃ z : BitString (c * Nat.log 2 M), H (M, List.ofFn z) ∉ A := by
  obtain ⟨L, hL, hLA⟩ := hENP
  obtain ⟨ε, hε, hhard⟩ := hLA A hA
  exact exists_polyTime_hittingGenerator_of_oracleHard hL hε hhard

/-- **Nisan–Wigderson range avoidance for polynomial-time stretching generators.** Assuming
`ENPHypothesis`, let `m : ℕ → ℕ` be strictly increasing and computable in unary polynomial time with
`n < m n` for all `n`, and let `g : ℕ × List Bool → List Bool` be computable in polynomial time with
`(g (n, List.ofFn x)).length = m n` for all `x : BitString n`. Then there exist `c ≥ 1` and a
uniform polynomial-time map `H : ℕ × List Bool → List Bool` with `(H (n, z)).length = m n` such that
for every `n ≥ 1`, some seed `z : BitString (c * ⌊log₂ (m n)⌋)` avoids `{g (n, List.ofFn x) | x :
BitString n}`. -/
theorem exists_polyTime_avoid_polyStretch_of_enp (hENP : ENPHypothesis) {m : ℕ → ℕ}
    (hm_poly : ComputableInPolyTime m encUnary encUnary)
    (hm_mono : StrictMono m) (hm_stretch : ∀ n, n < m n)
    {g : ℕ × List Bool → List Bool}
    (hg : ComputableInPolyTime g (encPair encUnary encBits) encBits)
    (hlen : ∀ n (x : BitString n), (g (n, List.ofFn x)).length = m n) :
    ∃ (c : ℕ) (H : ℕ × List Bool → List Bool),
      1 ≤ c ∧
      ComputableInPolyTime H (encPair encUnary encBits) encBits ∧
      (∀ n z, (H (n, z)).length = m n) ∧
      ∀ n, 1 ≤ n → ∃ z : BitString (c * Nat.log 2 (m n)),
        ∀ x : BitString n, H (n, List.ofFn z) ≠ g (n, List.ofFn x) := by
  classical
  let A : Language Bool :=
    {y : List Bool | ∃ w : List Bool, w.length < y.length ∧ m w.length = y.length ∧
      g (w.length, w) = y}
  have hA : (A : Set (List Bool)) ∈ NP encBits := by
    let firstTrue (u : List Bool) : ℕ :=
      (((List.range u.length).find? fun i => u.getD i false).getD u.length) + 1
    let unpad (u : List Bool) : List Bool := u.drop (firstTrue u)
    let V : List Bool × List Bool → Bool := fun p =>
      let w := unpad p.2
      decide (w.length < p.1.length) && decide (m w.length = p.1.length) &&
        decide (g (w.length, w) = p.1)
    have hV : ComputableInPolyTime V (encPair encBits encBits) encBool := by
      let EP := encPair encBits encBits
      have hy := ComputableInPolyTime.fst encBits encBits
      have hu := ComputableInPolyTime.snd encBits encBits
      have hlenu := ComputableInPolyTime.length_bits.comp hu
      have hpred : ComputableInPolyTime
          (fun q : (List Bool × List Bool) × ℕ => q.1.2.getD q.2 false)
          (encPair EP encUnary) encBool :=
        ComputableInPolyTime.bitsGetDWithInput (hu.comp (.fst EP encUnary)) (.snd EP encUnary) false
      have hfind : ComputableInPolyTime
          (fun p : List Bool × List Bool => (List.range p.2.length).find? fun i => p.2.getD i false)
          EP (encOption encUnary) :=
        ComputableInPolyTime.findWithInput (ComputableInPolyTime.range.comp hlenu) hpred
      have hidx := ComputableInPolyTime.unary_add'
        (ComputableInPolyTime.optionGetDWithInput hfind hlenu) (.const 1)
      have hw := ComputableInPolyTime.bitsDropWithInput hu hidx
      have hleny := ComputableInPolyTime.length_bits.comp hy
      have hlenw := ComputableInPolyTime.length_bits.comp hw
      have hmw := hm_poly.comp hlenw
      have hgcall := hg.comp (hlenw.prod hw)
      exact ComputableInPolyTime.bool_and'
        (ComputableInPolyTime.bool_and'
          (ComputableInPolyTime.unary_lt' hlenw hleny)
          (ComputableInPolyTime.decide_eq' hmw hleny))
        (ComputableInPolyTime.decide_eq' hgcall hy)
    have hunpad (k : ℕ) (w : List Bool) :
        unpad (List.replicate k false ++ (true :: w)) = w := by
      set u := List.replicate k false ++ (true :: w)
      have hk_lt : k < u.length := by simp [u]
      have hfind_eq : ((List.range u.length).find? fun i => u.getD i false) = some k := by
        rw [List.find?_eq_some_iff_append]
        refine ⟨by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk_lt, Option.getD_some,
            List.getElem_append_right (by simp)]; simp,
          List.range k, (List.range u.length).drop (k + 1), ?_, fun j hj => ?_⟩
        · refine List.ext_getElem (by simp; omega) fun j h₁ h₂ => ?_
          rw [List.getElem_range]
          by_cases hjk : j < k
          · rw [List.getElem_append_left (by simp [hjk]), List.getElem_range]
          · rw [List.getElem_append_right (by simp; omega)]
            have hjl : j < u.length := by simpa only [List.length_range] using h₁
            by_cases hje : j = k
            · subst hje; simp
            · have hsub : j - (List.range k).length = (j - k - 1) + 1 := by
                rw [List.length_range]; omega
              simp only [hsub, List.getElem_cons_succ, List.getElem_drop, List.getElem_range]
              omega
        · have hjk : j < k := List.mem_range.1 hj
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some,
            List.getElem_append_left (by simp [hjk]), List.getElem_replicate]
          rfl
      simp only [unpad, firstTrue, hfind_eq, Option.getD_some]
      rw [show u = (List.replicate k false ++ [true]) ++ w by simp [u],
        List.drop_left' (by simp)]
    refine ⟨Polynomial.X, V, hV, fun y => ⟨fun ⟨w, hlt, hmw, hgw⟩ => ?_, fun ⟨u, _, hacc⟩ => ?_⟩⟩
    · refine ⟨List.replicate (y.length - w.length - 1) false ++ (true :: w),
        by simp; omega, ?_⟩
      simp only [V, hunpad, hlt, hmw, hgw, decide_true, Bool.and_self]
    · simp only [V, Bool.and_eq_true, decide_eq_true_eq] at hacc
      exact ⟨unpad u, hacc.1.1, hacc.1.2, hacc.2⟩
  obtain ⟨c, H₀, hc, hH₀, hlen₀, havoid₀⟩ := exists_polyTime_rangeAvoidance_of_enp hENP hA
  let H : ℕ × List Bool → List Bool :=
    fun p => H₀ (m p.1, p.2.take (c * Nat.log 2 (m p.1)))
  have hH : ComputableInPolyTime H (encPair encUnary encBits) encBits := by
    have hmn := hm_poly.comp (.fst encUnary encBits)
    have hlog : ComputableInPolyTime (fun p : ℕ × List Bool => c * Nat.log 2 (m p.1))
        (encPair encUnary encBits) encUnary := by
      have hlg := ComputableInPolyTime.binary_log_two.comp
        (ComputableInPolyTime.unary_to_binary.comp hmn)
      exact ComputableInPolyTime.unary_mul' (.const c) hlg
    exact hH₀.comp (hmn.prod (ComputableInPolyTime.bitsTakeWithInput (.snd encUnary encBits) hlog))
  refine ⟨c, H, hc, hH, fun n z => hlen₀ (m n) _, fun n hn1 => ?_⟩
  have hmn2 : 2 ≤ m n := by have := hm_stretch n; omega
  have hcard : #{y : BitString (m n) | A.slice (m n) y = true} ≤ 2 ^ n := by
    let img : Finset (BitString (m n)) :=
      univ.image fun x : BitString n => BitString.ofList (m n) (g (n, List.ofFn x))
    have hsub : (univ.filter fun y : BitString (m n) => A.slice (m n) y = true) ⊆ img := by
      intro y hy
      simp only [mem_filter, mem_univ, true_and, Language.slice_eq_true_iff] at hy
      obtain ⟨w, -, hmw, hgw⟩ := hy
      simp only [List.length_ofFn] at hmw
      have hwn : w.length = n := hm_mono.injective hmw
      let x : BitString n := fun i => w[i.val]'(by omega)
      have hwx : List.ofFn x = w := List.ext_getElem (by simp [hwn]) fun _ _ _ => by simp [x]
      have hgw' : g (n, List.ofFn x) = List.ofFn y := by
        calc g (n, List.ofFn x) = g (w.length, w) := by congr 1; exact Prod.ext hwn.symm hwx
          _ = List.ofFn y := hgw
      refine mem_image.2 ⟨x, mem_univ x, funext fun i => ?_⟩
      rw [hgw']
      have hof : List.ofFn (BitString.ofList (m n) (List.ofFn y)) = List.ofFn y := by
        rw [BitString.ofFn_ofList_eq_take,
          List.take_append_of_le_length (by rw [List.length_ofFn]),
          List.take_of_length_le (by rw [List.length_ofFn])]
      have hidx := congrArg (fun l => l[i.val]?) hof
      simp only [List.getElem?_ofFn, i.isLt, dite_true] at hidx
      exact Option.some.inj hidx
    calc #{y : BitString (m n) | A.slice (m n) y = true} ≤ #img := card_le_card hsub
      _ ≤ #(univ : Finset (BitString n)) := card_image_le
      _ = 2 ^ n := by rw [card_univ, BitString.card]
  have hdens : ((#{y : BitString (m n) | A.slice (m n) y = true} : ℕ) : ℝ) ≤
      3 / 4 * (2 : ℝ) ^ m n := by
    have h2 : 2 ^ n * 2 ≤ 2 ^ m n := by
      rw [← pow_succ]; exact Nat.pow_le_pow_right two_pos (hm_stretch n)
    have hcast : ((#{y : BitString (m n) | A.slice (m n) y = true} : ℕ) : ℝ) * 2 ≤
        (2 : ℝ) ^ m n := by exact_mod_cast (Nat.mul_le_mul_right 2 hcard).trans h2
    linarith
  obtain ⟨z, hz⟩ := havoid₀ (m n) hmn2 hdens
  refine ⟨z, fun x hx => hz ?_⟩
  have hHeq : H (n, List.ofFn z) = H₀ (m n, List.ofFn z) := by
    dsimp only [H]; rw [List.take_of_length_le (by rw [List.length_ofFn])]
  rw [← hHeq, hx]
  exact ⟨List.ofFn x, by simp [hlen n x, hm_stretch n], by simp [hlen n x], by simp⟩

/-- **One-bit-stretch specialization of Nisan–Wigderson range avoidance.** Assuming
`ENPHypothesis`, every uniform polynomial-time map `g (N, ·) : BitString N → BitString (N + 1)`
admits `c ≥ 1` and a uniform polynomial-time map `H` with `(H (N, z)).length = N + 1` such that for
every `N ≥ 2`, some seed `z : BitString (c * ⌊log₂ N⌋)` avoids `{g (N, List.ofFn x) | x}`. -/
theorem exists_polyTime_avoid_stretching_of_enp (hENP : ENPHypothesis)
    {g : ℕ × List Bool → List Bool}
    (hg : ComputableInPolyTime g (encPair encUnary encBits) encBits)
    (hlen : ∀ N (x : BitString N), (g (N, List.ofFn x)).length = N + 1) :
    ∃ (c : ℕ) (H : ℕ × List Bool → List Bool),
      1 ≤ c ∧
      ComputableInPolyTime H (encPair encUnary encBits) encBits ∧
      (∀ N z, (H (N, z)).length = N + 1) ∧
      ∀ N, 2 ≤ N → ∃ z : BitString (c * Nat.log 2 N),
        ∀ x : BitString N, H (N, List.ofFn z) ≠ g (N, List.ofFn x) := by
  obtain ⟨c₀, H₀, hc₀, hH₀, hlen₀, havoid₀⟩ := exists_polyTime_avoid_polyStretch_of_enp hENP
    (m := fun N => N + 1) (by fun_prop) (fun _ _ h => Nat.succ_lt_succ h) Nat.lt_succ_self hg hlen
  let H : ℕ × List Bool → List Bool :=
    fun p => H₀ (p.1, p.2.take (c₀ * Nat.log 2 (p.1 + 1)))
  have hH : ComputableInPolyTime H (encPair encUnary encBits) encBits := by
    have hsucc : ComputableInPolyTime (fun p : ℕ × List Bool => p.1 + 1)
        (encPair encUnary encBits) encUnary := by fun_prop
    have hlog : ComputableInPolyTime (fun p : ℕ × List Bool => c₀ * Nat.log 2 (p.1 + 1))
        (encPair encUnary encBits) encUnary :=
      ComputableInPolyTime.unary_mul' (.const c₀)
        (ComputableInPolyTime.binary_log_two.comp
          (ComputableInPolyTime.unary_to_binary.comp hsucc))
    exact hH₀.comp ((ComputableInPolyTime.fst encUnary encBits).prod
      (ComputableInPolyTime.bitsTakeWithInput (.snd encUnary encBits) hlog))
  refine ⟨2 * c₀, H, by omega, hH, fun N _ => hlen₀ N _, fun N hN2 => ?_⟩
  obtain ⟨z₀, hz₀⟩ := havoid₀ N (by omega)
  have hlog_le : c₀ * Nat.log 2 (N + 1) ≤ 2 * c₀ * Nat.log 2 N := by
    have h1 : 1 ≤ Nat.log 2 N := Nat.log_pos one_lt_two hN2
    have h2 : N + 1 < 2 ^ (Nat.log 2 N + 2) := by
      have := Nat.lt_pow_succ_log_self one_lt_two N
      rw [show Nat.log 2 N + 2 = (Nat.log 2 N + 1) + 1 by omega, pow_succ]; omega
    have h3 : Nat.log 2 (N + 1) ≤ Nat.log 2 N + 1 :=
      Nat.lt_succ_iff.1 ((Nat.log_lt_iff_lt_pow one_lt_two (by omega)).2 h2)
    nlinarith
  let z : BitString (2 * c₀ * Nat.log 2 N) :=
    fun i => if hi : i.val < c₀ * Nat.log 2 (N + 1) then z₀ ⟨i.val, hi⟩ else false
  have htake : (List.ofFn z).take (c₀ * Nat.log 2 (N + 1)) = List.ofFn z₀ :=
    List.ext_getElem (by simp [hlog_le]) fun i _ h₂ => by
      simp only [List.length_ofFn] at h₂; simp [z, h₂]
  exact ⟨z, fun x hx => hz₀ x (by simpa [H, htake] using hx)⟩

end CslibFrontier.Computability
