module

public import CslibFrontier.Computability.Complexity.Classes.EXP
public import CslibFrontier.Computability.Complexity.Classes.Oracle
import CslibFrontier.Computability.Complexity.Classes.Oracle.BinarySearch
import CslibFrontier.Computability.Complexity.Classes.Oracle.Closure
import CslibFrontier.Computability.Complexity.Classes.Oracle.Function
import CslibFrontier.Computability.Complexity.Classes.Oracle.ListOracle
import CslibFrontier.Computability.Complexity.Classes.Oracle.Lowness
import CslibFrontier.Computability.Complexity.Classes.Oracle.Monotone
import CslibFrontier.Computability.Complexity.Classes.Oracle.Substitution
import CslibFrontier.Computability.Complexity.Classes.Padding.Tally
import CslibFrontier.Computability.Complexity.Classes.Time.Verifier
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.TwoPow
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder.Partial
import CslibFrontier.Computability.Probabilistic.Oracle.Composition
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Collapse of the Strong Exponential Hierarchy

Proves the census-technique collapse of the strong exponential hierarchy under standard Lean
axioms, establishing `NP^{NE} = coNP^{NE} = NP^{coNP^{NE}} = P^{NE}` and collapsing all levels
`Σ_r`, `Π_r`, `Δ_r` (`r ≥ 2`) to `P^{NE}`, together with the padding identity `P^{NE} = P^{NEXP}`.

## Main definitions

* `CslibFrontier.Complexity.PNE`: languages decidable in polynomial time with an `NE` oracle.
* `CslibFrontier.Complexity.NPNE`: languages in `NP` with an `NE` oracle.
* `CslibFrontier.Complexity.coNPNE`: languages in `coNP` with an `NE` oracle.
* `CslibFrontier.Complexity.SEHSigma`, `SEHDelta`, `SEHPi`: levels of the strong exponential
  hierarchy `E, NE, P^{NE}, NP^{NE}, P^{NP^{NE}}, NP^{NP^{NE}}, ...`.
* `CslibFrontier.Complexity.PNEXP`: languages decidable in polynomial time with an `NEXP` oracle.

## Main results

* `CslibFrontier.Complexity.setOf_exists_two_pow_mem_NE`: polynomial-time verifier with
  exponentially bounded certificate length places a language in `NE`.
* `CslibFrontier.Complexity.NPWithOracle_subset_PNE_of_mem_NE`: for every `A ∈ NE`,
  `NP^A ⊆ P^{NE}` via census binary search and exact truth-table verification.
* `CslibFrontier.Complexity.NPNE_eq_PNE`, `CslibFrontier.Complexity.coNPNE_eq_PNE`,
  `CslibFrontier.Complexity.NP_coNP_NE_eq_PNE`, `CslibFrontier.Complexity.NP_NP_NE_eq_PNE`:
  `NP^{NE} = coNP^{NE} = NP^{coNP^{NE}} = NP^{NP^{NE}} = P^{NE}`.
* `CslibFrontier.Complexity.SEH_collapse`: every level `Σ_r`, `Π_r`, `Δ_r` (`r ≥ 2`) of the
  strong exponential hierarchy collapses to `P^{NE}`.
* `CslibFrontier.Complexity.exists_NE_polyTimeReducible_of_mem_NEXP`,
  `CslibFrontier.Complexity.PNE_eq_PNEXP`: padding yields `P^{NE} = P^{NEXP}`.
-/

public section

namespace CslibFrontier.Complexity

open Cslib Cslib.Complexity Cslib.Probability Turing.MultiTapeTM

/-! ### Exponential-certificate membership in `NE` -/

/-- If `L a` is computable in unary in polynomial time and linearly bounded by `|enc a|`, and
`V : α × List Bool → Bool` is polynomial-time, then accepting certificates of length `2 ^ L a`
defines a language in `NE enc`. -/
theorem setOf_exists_two_pow_mem_NE {α : Type} {enc : α ↪ List Bool}
    {L : α → ℕ} {V : α × List Bool → Bool} {K C₀ : ℕ}
    (hL : ComputableInPolyTime L enc encUnary)
    (hL_le : ∀ a, L a ≤ K * (enc a).length + C₀)
    (hV : ComputableInPolyTime V (encPair enc encBits) encBool) :
    {a | ∃ w : List Bool, w.length = 2 ^ L a ∧ V (a, w) = true} ∈ NE enc := by
  obtain ⟨Cℓ, hℓ⟩ := hL.exists_computableInO_unary_two_pow
  obtain ⟨T, S, hT, -, hVO⟩ := hV.exists_computableInO
  obtain ⟨cT, dT, hTle⟩ := hT.exists_le
  let k : ℕ := (K + 1) * dT + 2 * K + 2
  let M : ℕ := 1 + Cℓ + 2 ^ (2 * C₀) + cT * (4 * 2 ^ C₀) ^ dT
  refine mem_NE_iff.mpr ⟨k, setOf_exists_mem_NTIME hℓ hVO (C := M) fun a w hw ↦ ?_⟩
  set n := (enc a).length
  have hLn : L a ≤ K * n + C₀ := hL_le a
  have h2L : 2 ^ L a ≤ 2 ^ C₀ * 2 ^ (K * n) := by
    calc 2 ^ L a ≤ 2 ^ (K * n + C₀) := Nat.pow_le_pow_right (by omega) hLn
      _ = 2 ^ C₀ * 2 ^ (K * n) := by rw [pow_add, Nat.mul_comm]
  have h4L : 4 ^ L a ≤ 2 ^ (2 * C₀) * 2 ^ (2 * K * n) := by
    have h4 : 4 ^ L a = 2 ^ (2 * L a) := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
    rw [h4]
    have h2Ln : 2 * L a ≤ 2 * K * n + 2 * C₀ := by
      have : 2 * (K * n + C₀) = 2 * K * n + 2 * C₀ := by ring
      omega
    calc 2 ^ (2 * L a) ≤ 2 ^ (2 * K * n + 2 * C₀) := Nat.pow_le_pow_right (by omega) h2Ln
      _ = 2 ^ (2 * C₀) * 2 ^ (2 * K * n) := by rw [pow_add, Nat.mul_comm]
  have hpair : (encPair enc encBits (a, w)).length + 1 ≤ 4 * 2 ^ C₀ * 2 ^ ((K + 1) * n) := by
    rw [length_encPair, encBits_apply, hw]
    have hn2 : 2 * n + 2 ≤ 3 * 2 ^ n := by
      have := Nat.lt_two_pow_self (n := n)
      omega
    have hpos : 1 ≤ 2 ^ C₀ := Nat.one_le_two_pow
    have hposK : 1 ≤ 2 ^ (K * n) := Nat.one_le_two_pow
    have hposn : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    have hprod : 2 ^ n * 2 ^ (K * n) = 2 ^ ((K + 1) * n) := by
      rw [← pow_add]
      congr 1
      ring
    calc 2 * n + 1 + 2 ^ L a + 1 = (2 * n + 2) + 2 ^ L a := by omega
      _ ≤ 3 * 2 ^ n + 2 ^ C₀ * 2 ^ (K * n) := Nat.add_le_add hn2 h2L
      _ ≤ 3 * (2 ^ C₀ * (2 ^ n * 2 ^ (K * n))) + 2 ^ C₀ * (2 ^ n * 2 ^ (K * n)) := by
          apply Nat.add_le_add
          · have : 2 ^ n ≤ 2 ^ C₀ * (2 ^ n * 2 ^ (K * n)) := by
              calc 2 ^ n = 1 * (2 ^ n * 1) := by ring
                _ ≤ 2 ^ C₀ * (2 ^ n * 2 ^ (K * n)) :=
                    Nat.mul_le_mul hpos (Nat.mul_le_mul_left _ hposK)
            omega
          · exact Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ hposn)
      _ = 4 * 2 ^ C₀ * 2 ^ ((K + 1) * n) := by rw [hprod]; ring
  have hTbound : T (a, w) ≤ cT * (4 * 2 ^ C₀) ^ dT * 2 ^ ((K + 1) * dT * n) := by
    calc T (a, w) ≤ cT * ((encPair enc encBits (a, w)).length + 1) ^ dT := hTle (a, w)
      _ ≤ cT * (4 * 2 ^ C₀ * 2 ^ ((K + 1) * n)) ^ dT :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hpair dT)
      _ = cT * (4 * 2 ^ C₀) ^ dT * 2 ^ ((K + 1) * dT * n) := by
          rw [mul_pow, ← pow_mul]
          have : (K + 1) * n * dT = (K + 1) * dT * n := by ring
          rw [this, ← mul_assoc]
  have hk1 : n ≤ k * n := by
    simpa only [one_mul] using Nat.mul_le_mul_right n (by dsimp [k]; omega : 1 ≤ k)
  have hk2K : 2 * K * n ≤ k * n := Nat.mul_le_mul_right n (by dsimp [k]; omega)
  have hkKdT : (K + 1) * dT * n ≤ k * n := Nat.mul_le_mul_right n (by dsimp [k]; omega)
  have hn_le : n ≤ 2 ^ (k * n) :=
    Nat.lt_two_pow_self.le.trans (Nat.pow_le_pow_right (by omega) hk1)
  have h2n_le : 2 ^ n ≤ 2 ^ (k * n) := Nat.pow_le_pow_right (by omega) hk1
  have h2Kn_le : 2 ^ (2 * K * n) ≤ 2 ^ (k * n) := Nat.pow_le_pow_right (by omega) hk2K
  have hKdT_le : 2 ^ ((K + 1) * dT * n) ≤ 2 ^ (k * n) := Nat.pow_le_pow_right (by omega) hkKdT
  calc n + (Cℓ * 2 ^ n + 4 ^ L a) + T (a, w)
      ≤ 2 ^ (k * n) + (Cℓ * 2 ^ (k * n) + 2 ^ (2 * C₀) * 2 ^ (k * n)) +
          cT * (4 * 2 ^ C₀) ^ dT * 2 ^ (k * n) := by
        have h1 : Cℓ * 2 ^ n ≤ Cℓ * 2 ^ (k * n) := Nat.mul_le_mul_left _ h2n_le
        have h2 : 4 ^ L a ≤ 2 ^ (2 * C₀) * 2 ^ (k * n) :=
          h4L.trans (Nat.mul_le_mul_left _ h2Kn_le)
        have h3 : T (a, w) ≤ cT * (4 * 2 ^ C₀) ^ dT * 2 ^ (k * n) :=
          hTbound.trans (Nat.mul_le_mul_left _ hKdT_le)
        omega
    _ = M * 2 ^ (k * n) := by dsimp [M]; ring
    _ ≤ M * 2 ^ (k * n) + M := Nat.le_add_right _ _

/-! ### Canonical enumeration of short bit strings and census -/

/-- Canonical bijection from `i : ℕ` to bit strings: `i ↦ (i + 1).bits.dropLast`.
Restricts to a bijection between `{0, ..., 2 ^ (m + 1) - 2}` and `{u : List Bool | u.length ≤ m}`.
-/
private def codeWord (i : ℕ) : List Bool :=
  (i + 1).bits.dropLast

private theorem bits_eq_dropLast_concat_true {k : ℕ} (hk : k ≠ 0) :
    k.bits = k.bits.dropLast ++ [true] := by
  induction k using Nat.binaryRec with
  | zero => exact absurd rfl hk
  | bit b m ih =>
    rcases eq_or_ne m 0 with rfl | hm
    · cases b with
      | false => simp at hk
      | true => simp
    · rw [Nat.bits_append_bit _ _ (fun h ↦ absurd h hm)]
      have hne : m.bits ≠ [] := by simpa [Nat.bits_eq_nil_iff] using hm
      rw [List.dropLast_cons_of_ne_nil hne, List.cons_append, ← ih hm]

private theorem tallyCode_pos (u : List Bool) : 0 < tallyCode u := by
  by_contra h
  have h0 : tallyCode u = 0 := by omega
  have hb := bits_tallyCode u
  rw [h0] at hb
  simp at hb

private theorem codeWord_tallyCode (u : List Bool) : codeWord (tallyCode u - 1) = u := by
  have hpos := tallyCode_pos u
  simp only [codeWord, Nat.sub_add_cancel hpos, bits_tallyCode, List.dropLast_concat]

private theorem tallyCode_codeWord (i : ℕ) : tallyCode (codeWord i) = i + 1 := by
  apply encNat.injective
  simp only [encNat_apply, bits_tallyCode, codeWord]
  exact (bits_eq_dropLast_concat_true (Nat.succ_ne_zero i)).symm

private theorem codeWord_injective : Function.Injective codeWord := fun i j h ↦ by
  have := congrArg tallyCode h
  rw [tallyCode_codeWord, tallyCode_codeWord] at this
  omega

private theorem length_codeWord_le {m i : ℕ} (hi : i < 2 ^ (m + 1) - 1) :
    (codeWord i).length ≤ m := by
  have hlt : i + 1 < 2 ^ (m + 1) := by
    have : 1 ≤ 2 ^ (m + 1) := Nat.one_le_two_pow
    omega
  have hsize : (i + 1).bits.length ≤ m + 1 := by
    rw [Nat.size_eq_bits_len]
    exact Nat.size_le.mpr hlt
  simp only [codeWord, List.length_dropLast]
  omega

private theorem tallyCode_sub_one_lt {u : List Bool} {m : ℕ} (hu : u.length ≤ m) :
    tallyCode u - 1 < 2 ^ (m + 1) - 1 := by
  have hpos := tallyCode_pos u
  have hlt : tallyCode u < 2 ^ (m + 1) :=
    (tallyCode_lt u).trans_le (Nat.pow_le_pow_right (by omega) (by omega))
  omega

/-- The census of `A` up to length `m`: the number of bit strings of length at most `m` in `A`. -/
private noncomputable def census (A : Set (List Bool)) (m : ℕ) : ℕ :=
  let _ := Classical.propDecidable
  (List.range (2 ^ (m + 1) - 1)).countP fun i ↦ decide (codeWord i ∈ A)

private theorem census_lt (A : Set (List Bool)) (m : ℕ) : census A m < 2 ^ (m + 1) := by
  classical
  have hle : census A m ≤ (List.range (2 ^ (m + 1) - 1)).length := List.countP_le_length
  rw [List.length_range] at hle
  have hpos : 1 ≤ 2 ^ (m + 1) := Nat.one_le_two_pow
  omega

/-- Any duplicate-free list of at least `census A m` strings of length at most `m` lying in `A`
contains precisely the members of `A` of length at most `m`. -/
private theorem mem_iff_of_card_ge_census {A : Set (List Bool)} {m : ℕ} {ℓ : List (List Bool)}
    (hnodup : ℓ.Nodup) (hsub : ∀ u ∈ ℓ, u.length ≤ m ∧ u ∈ A) (hcard : census A m ≤ ℓ.length) :
    ∀ u : List Bool, u.length ≤ m → (u ∈ ℓ ↔ u ∈ A) := by
  classical
  let S : Finset ℕ := (Finset.range (2 ^ (m + 1) - 1)).filter fun i ↦ codeWord i ∈ A
  let f : List Bool → ℕ := fun u ↦ tallyCode u - 1
  have hf_inj : Function.Injective f := fun u v h ↦ by
    have := congrArg codeWord h
    simpa only [f, codeWord_tallyCode] using this
  let T : Finset ℕ := (ℓ.map f).toFinset
  have hS_card : S.card = census A m := by
    simp only [S, census, List.countP_eq_length_filter]
    rw [← List.toFinset_card_of_nodup (List.nodup_range.filter _)]
    congr 1
    ext i
    simp [List.mem_range, Finset.mem_filter, Finset.mem_range]
  have hT_card : T.card = ℓ.length := by
    rw [List.toFinset_card_of_nodup (hnodup.map hf_inj), List.length_map]
  have hTS : T ⊆ S := by
    intro i hi
    simp only [T, List.mem_toFinset, List.mem_map] at hi
    obtain ⟨u, huℓ, rfl⟩ := hi
    obtain ⟨hlen, huA⟩ := hsub u huℓ
    simp only [S, Finset.mem_filter, Finset.mem_range, f, codeWord_tallyCode]
    exact ⟨tallyCode_sub_one_lt hlen, huA⟩
  have hTeqS : T = S := Finset.eq_of_subset_of_card_le hTS (by omega)
  intro u hu
  have hiff : f u ∈ T ↔ f u ∈ S := by rw [hTeqS]
  simp only [T, S, List.mem_toFinset, List.mem_map, Finset.mem_filter, Finset.mem_range,
    f, codeWord_tallyCode] at hiff
  constructor
  · intro huℓ
    exact (hsub u huℓ).2
  · intro huA
    obtain ⟨v, hvℓ, hfv⟩ := hiff.mpr ⟨tallyCode_sub_one_lt hu, huA⟩
    exact hf_inj hfv ▸ hvℓ

private theorem computableInPolyTime_codeWord :
    ComputableInPolyTime codeWord encUnary encBits := by
  have h : codeWord = fun i ↦ ((i + 1).bits.reverse.tail).reverse := by
    funext i
    simp [codeWord, List.tail_reverse]
  rw [h]
  fun_prop

/-! ### Fixed-width table slicing and census-verifier machinery -/

private theorem drop_take_flatMap_fixed {W : ℕ} (rows : List (List Bool))
    (hrows : ∀ r ∈ rows, r.length = W) (rest : List Bool) {i : ℕ} (hi : i < rows.length) :
    ((rows.flatten ++ rest).drop (i * W)).take W = rows[i] := by
  induction rows generalizing i with
  | nil => simp at hi
  | cons r rows ih =>
    have hr : r.length = W := hrows r (by simp)
    cases i with
    | zero =>
      simp only [Nat.zero_mul, List.drop_zero, List.flatten_cons, List.append_assoc,
        List.take_left' hr, List.getElem_cons_zero]
    | succ i =>
      simp only [Nat.succ_mul, Nat.add_comm (i * W) W, List.flatten_cons, List.append_assoc]
      rw [← List.drop_drop, List.drop_left' hr]
      exact ih (fun r' hr' ↦ hrows r' (by simp [hr'])) (by simpa using hi)

private theorem censusCert_ge (kA cA m : ℕ) (u : List Bool) (hu : u.length ≤ m) :
    cA * 2 ^ (kA * u.length) + cA ≤ 2 ^ (kA * m + (cA + cA + 1) + 1) - 1 := by
  set c₀ := cA + cA + 1
  have hpow_u : 2 ^ (kA * u.length) ≤ 2 ^ (kA * m) :=
    Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_left kA hu)
  have hc₀_le : 2 * cA + 1 ≤ 2 ^ c₀ := by
    have h1 : 2 * cA + 1 = c₀ := by omega
    rw [h1]
    exact Nat.lt_two_pow_self.le
  have hpos : 1 ≤ 2 ^ (kA * m) := Nat.one_le_two_pow
  have h1 : cA * 2 ^ (kA * u.length) + cA ≤ 2 * cA * 2 ^ (kA * m) := by nlinarith
  have h12 : 2 * cA * 2 ^ (kA * m) ≤ (2 * cA + 1) * 2 ^ (kA * m) :=
    Nat.mul_le_mul_right _ (by omega)
  have h2 : (2 * cA + 1) * 2 ^ (kA * m) ≤ 2 ^ (kA * m + c₀) := by
    rw [pow_add, Nat.mul_comm]
    exact Nat.mul_le_mul_left _ hc₀_le
  have h3 : 2 ^ (kA * m + c₀) + 1 ≤ 2 ^ (kA * m + c₀ + 1) := by
    rw [pow_succ]
    have : 1 ≤ 2 ^ (kA * m + c₀) := Nat.one_le_two_pow
    omega
  omega

private def censusNumStr (m : ℕ) (cert : List Bool) : ℕ :=
  min cert.length (2 ^ (m + 1) - 1)

private def censusRowW (kA c₀ m : ℕ) (cert : List Bool) : ℕ :=
  min cert.length (2 ^ (kA * m + c₀ + 1))

private def censusHalfL (kA c₀ m : ℕ) (cert : List Bool) : ℕ :=
  min cert.length (2 ^ ((kA + 1) * m + c₀ + 2))

private def censusGetRow (kA c₀ m : ℕ) (cert : List Bool) (i : ℕ) : List Bool :=
  (cert.drop (i * censusRowW kA c₀ m cert)).take (censusRowW kA c₀ m cert)

private def censusTableValid (VA : List Bool × List Bool → Bool) (kA c₀ m : ℕ)
    (cert : List Bool) : Bool :=
  (List.range (censusNumStr m cert)).all fun i ↦
    let r := censusGetRow kA c₀ m cert i
    !(r.headD false) || VA (codeWord i, r.tail)

private def censusTableWords (kA c₀ m : ℕ) (cert : List Bool) : List (List Bool) :=
  ((List.range (censusNumStr m cert)).filter fun i ↦
    (censusGetRow kA c₀ m cert i).headD false).map codeWord

private theorem computableInPolyTime_censusNumStr :
    ComputableInPolyTime (fun z : ℕ × List Bool ↦ censusNumStr z.1 z.2)
      (encPair encUnary encBits) encUnary := by
  dsimp only [censusNumStr]
  exact ComputableInPolyTime.binary_min_unary'
    (ComputableInPolyTime.length_bits.comp (ComputableInPolyTime.snd encUnary encBits))
    (ComputableInPolyTime.binary_sub'
      (ComputableInPolyTime.binary_two_pow.comp
        (ComputableInPolyTime.unary_add' (ComputableInPolyTime.fst encUnary encBits)
          (ComputableInPolyTime.const 1)))
      (ComputableInPolyTime.const 1))

private theorem computableInPolyTime_censusRowW (kA c₀ : ℕ) :
    ComputableInPolyTime (fun z : ℕ × List Bool ↦ censusRowW kA c₀ z.1 z.2)
      (encPair encUnary encBits) encUnary := by
  dsimp only [censusRowW]
  have hexp : ComputableInPolyTime (fun z : ℕ × List Bool ↦ kA * z.1 + c₀ + 1)
      (encPair encUnary encBits) encUnary :=
    ComputableInPolyTime.unary_add'
      (ComputableInPolyTime.unary_add'
        (ComputableInPolyTime.unary_mul' (ComputableInPolyTime.const kA)
          (ComputableInPolyTime.fst encUnary encBits))
        (ComputableInPolyTime.const c₀))
      (ComputableInPolyTime.const 1)
  exact ComputableInPolyTime.binary_min_unary'
    (ComputableInPolyTime.length_bits.comp (ComputableInPolyTime.snd encUnary encBits))
    (ComputableInPolyTime.binary_two_pow.comp hexp)

private theorem computableInPolyTime_censusHalfL (kA c₀ : ℕ) :
    ComputableInPolyTime (fun z : ℕ × List Bool ↦ censusHalfL kA c₀ z.1 z.2)
      (encPair encUnary encBits) encUnary := by
  dsimp only [censusHalfL]
  have hexp : ComputableInPolyTime (fun z : ℕ × List Bool ↦ (kA + 1) * z.1 + c₀ + 2)
      (encPair encUnary encBits) encUnary :=
    ComputableInPolyTime.unary_add'
      (ComputableInPolyTime.unary_add'
        (ComputableInPolyTime.unary_mul' (ComputableInPolyTime.const (kA + 1))
          (ComputableInPolyTime.fst encUnary encBits))
        (ComputableInPolyTime.const c₀))
      (ComputableInPolyTime.const 2)
  exact ComputableInPolyTime.binary_min_unary'
    (ComputableInPolyTime.length_bits.comp (ComputableInPolyTime.snd encUnary encBits))
    (ComputableInPolyTime.binary_two_pow.comp hexp)

private theorem computableInPolyTime_censusGetRow (kA c₀ : ℕ) :
    ComputableInPolyTime (fun z : (ℕ × List Bool) × ℕ ↦ censusGetRow kA c₀ z.1.1 z.1.2 z.2)
      (encPair (encPair encUnary encBits) encUnary) encBits := by
  dsimp only [censusGetRow]
  have hcert : ComputableInPolyTime (fun z : (ℕ × List Bool) × ℕ ↦ z.1.2)
      (encPair (encPair encUnary encBits) encUnary) encBits :=
    (ComputableInPolyTime.fst _ _).snd'
  have hW : ComputableInPolyTime (fun z : (ℕ × List Bool) × ℕ ↦ censusRowW kA c₀ z.1.1 z.1.2)
      (encPair (encPair encUnary encBits) encUnary) encUnary :=
    (computableInPolyTime_censusRowW kA c₀).comp (ComputableInPolyTime.fst _ _)
  have hdrop := ComputableInPolyTime.bitsDropWithInput hcert
    (ComputableInPolyTime.unary_mul' (ComputableInPolyTime.snd _ _) hW)
  exact ComputableInPolyTime.bitsTakeWithInput hdrop hW

private theorem computableInPolyTime_censusTableValid {VA : List Bool × List Bool → Bool}
    (hVA : ComputableInPolyTime VA (encPair encBits encBits) encBool) (kA c₀ : ℕ) :
    ComputableInPolyTime (fun z : ℕ × List Bool ↦ censusTableValid VA kA c₀ z.1 z.2)
      (encPair encUnary encBits) encBool := by
  dsimp only [censusTableValid]
  refine ComputableInPolyTime.allWithInput
    (ComputableInPolyTime.range.comp computableInPolyTime_censusNumStr) ?_
  have hrow := computableInPolyTime_censusGetRow kA c₀
  have hhead : ComputableInPolyTime
      (fun z : (ℕ × List Bool) × ℕ ↦ (censusGetRow kA c₀ z.1.1 z.1.2 z.2).headD false)
      (encPair (encPair encUnary encBits) encUnary) encBool :=
    (ComputableInPolyTime.headD (encA := encBool) (encL := encBits) false).comp hrow
  have htail : ComputableInPolyTime
      (fun z : (ℕ × List Bool) × ℕ ↦ (censusGetRow kA c₀ z.1.1 z.1.2 z.2).tail)
      (encPair (encPair encUnary encBits) encUnary) encBits :=
    ComputableInPolyTime.bitsTail.comp hrow
  have hcw : ComputableInPolyTime (fun z : (ℕ × List Bool) × ℕ ↦ codeWord z.2)
      (encPair (encPair encUnary encBits) encUnary) encBits :=
    computableInPolyTime_codeWord.comp (ComputableInPolyTime.snd _ _)
  exact ComputableInPolyTime.bool_or' (ComputableInPolyTime.bool_not.comp hhead)
    (hVA.comp (hcw.prod htail))

private theorem computableInPolyTime_censusTableWords (kA c₀ : ℕ) :
    ComputableInPolyTime (fun z : ℕ × List Bool ↦ censusTableWords kA c₀ z.1 z.2)
      (encPair encUnary encBits) (encList encBits) := by
  dsimp only [censusTableWords]
  have hhead : ComputableInPolyTime
      (fun z : (ℕ × List Bool) × ℕ ↦ (censusGetRow kA c₀ z.1.1 z.1.2 z.2).headD false)
      (encPair (encPair encUnary encBits) encUnary) encBool :=
    (ComputableInPolyTime.headD (encA := encBool) (encL := encBits) false).comp
      (computableInPolyTime_censusGetRow kA c₀)
  have hfilt := ComputableInPolyTime.filterWithInput
    (test := fun (z : ℕ × List Bool) (i : ℕ) ↦ (censusGetRow kA c₀ z.1 z.2 i).headD false)
    (ComputableInPolyTime.range.comp computableInPolyTime_censusNumStr) hhead
  exact (ComputableInPolyTime.map computableInPolyTime_codeWord).comp hfilt

private def decPairUC : PartialDecoder (encPair encBits encNat) :=
  PartialDecoder.pair (PartialDecoder.ofDecoder Decoder.bits) (PartialDecoder.ofDecoder Decoder.nat)

private def decUnaryStrict : PartialDecoder encUnary :=
  PartialDecoder.ofDecoder Decoder.unary

private def decXM : PartialDecoder (encPair encBits encUnary) :=
  PartialDecoder.pair (PartialDecoder.ofDecoder Decoder.bits) decUnaryStrict

/-- Extract the unary parameter `m` from a raw oracle query `raw : List Bool` (`0` if malformed). -/
private def parseM (raw : List Bool) : ℕ :=
  (decPairUC.decode raw).elim 0 fun uc ↦
    if uc.1.isEmpty then 0
    else if uc.1.headD false then
      (decXM.decode uc.1.tail).elim 0 fun xm ↦ xm.2
    else
      (decUnaryStrict.decode uc.1.tail).getD 0

private theorem parseM_le (raw : List Bool) : parseM raw ≤ raw.length := by
  dsimp only [parseM]
  cases huc : decPairUC.decode raw with
  | none => exact Nat.zero_le _
  | some uc =>
    have hraw := (decPairUC.decode_eq_some_iff raw uc).mp huc
    have hu_le : uc.1.length ≤ raw.length := by
      rw [← hraw, length_encPair, encBits_apply]
      omega
    have htail_le : uc.1.tail.length ≤ uc.1.length := by
      rw [List.length_tail]
      exact Nat.sub_le _ 1
    simp only [Option.elim_some]
    split_ifs with hempty hhead
    · exact Nat.zero_le _
    · cases hxm : decXM.decode uc.1.tail with
      | none => exact Nat.zero_le _
      | some xm =>
        have htail := (decXM.decode_eq_some_iff uc.1.tail xm).mp hxm
        have hxm_le : xm.2 ≤ uc.1.tail.length := by
          rw [← htail, length_encPair, encUnary_apply, List.length_replicate]
          omega
        simp only [Option.elim_some]
        exact hxm_le.trans (htail_le.trans hu_le)
    · cases hm : decUnaryStrict.decode uc.1.tail with
      | none => exact Nat.zero_le _
      | some m =>
        have htail := (decUnaryStrict.decode_eq_some_iff uc.1.tail m).mp hm
        have hm_le : m ≤ uc.1.tail.length := by
          rw [← htail, encUnary_apply, List.length_replicate]
        simp only [Option.getD_some]
        exact hm_le.trans (htail_le.trans hu_le)

private theorem computableInPolyTime_parseM :
    ComputableInPolyTime parseM encBits encUnary := by
  unfold parseM
  refine decPairUC.computable.optionElimWithInput (ComputableInPolyTime.const 0) ?_
  have hu : ComputableInPolyTime (fun s : List Bool × (List Bool × ℕ) ↦ s.2.1)
      (encPair encBits (encPair encBits encNat)) encBits :=
    (ComputableInPolyTime.snd _ _).fst'
  have hutail : ComputableInPolyTime (fun s : List Bool × (List Bool × ℕ) ↦ s.2.1.tail)
      (encPair encBits (encPair encBits encNat)) encBits :=
    ComputableInPolyTime.bitsTail.comp hu
  have htrue : ComputableInPolyTime
      (fun s : List Bool × (List Bool × ℕ) ↦ (decXM.decode s.2.1.tail).elim 0 fun xm ↦ xm.2)
      (encPair encBits (encPair encBits encNat)) encUnary :=
    (decXM.computable.comp hutail).optionElimWithInput (ComputableInPolyTime.const 0)
      (ComputableInPolyTime.snd _ _).snd'
  have hfalse : ComputableInPolyTime
      (fun s : List Bool × (List Bool × ℕ) ↦ (decUnaryStrict.decode s.2.1.tail).getD 0)
      (encPair encBits (encPair encBits encNat)) encUnary :=
    ComputableInPolyTime.optionGetDWithInput (decUnaryStrict.computable.comp hutail)
      (ComputableInPolyTime.const 0)
  exact ComputableInPolyTime.ite' (ComputableInPolyTime.bitsIsEmpty.comp hu)
    (ComputableInPolyTime.const 0)
    (ComputableInPolyTime.ite'
      ((ComputableInPolyTime.headD (encA := encBool) (encL := encBits) false).comp hu)
      htrue hfalse)

private theorem parseM_census (m c : ℕ) :
    parseM (encPair encBits encNat (false :: encUnary m, c)) = m := by
  dsimp only [parseM]
  rw [decPairUC.decode_enc]
  simp only [Option.elim_some, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte,
    List.headD_cons, List.tail_cons]
  rw [decUnaryStrict.decode_enc]
  rfl

private theorem parseM_sim (x : List Bool) (m c : ℕ) :
    parseM (encPair encBits encNat (true :: encPair encBits encUnary (x, m), c)) = m := by
  dsimp only [parseM]
  rw [decPairUC.decode_enc]
  simp only [Option.elim_some, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte,
    List.headD_cons, List.tail_cons]
  rw [decXM.decode_enc]
  rfl

private def censusVerifier (VA : List Bool × List Bool → Bool) (kA c₀ : ℕ) (p : Polynomial ℕ)
    (F : (List Bool × List Bool) × List (List Bool) → Bool)
    (rc : List Bool × List Bool) : Bool :=
  (decPairUC.decode rc.1).elim false fun uc ↦
    if uc.1.isEmpty then false
    else if uc.1.headD false then
      (decXM.decode uc.1.tail).elim false fun xm ↦
        decide (p.eval xm.1.length ≤ xm.2) &&
          censusTableValid VA kA c₀ xm.2 rc.2 &&
          decide (uc.2 ≤ (censusTableWords kA c₀ xm.2 rc.2).length) &&
          F ((xm.1, (rc.2.drop (censusHalfL kA c₀ xm.2 rc.2)).take (p.eval xm.1.length)),
            censusTableWords kA c₀ xm.2 rc.2)
    else
      (decUnaryStrict.decode uc.1.tail).elim false fun m ↦
        censusTableValid VA kA c₀ m rc.2 && decide (uc.2 ≤ (censusTableWords kA c₀ m rc.2).length)

private theorem computableInPolyTime_censusVerifier
    {VA : List Bool × List Bool → Bool}
    (hVA : ComputableInPolyTime VA (encPair encBits encBits) encBool)
    (kA c₀ : ℕ) (p : Polynomial ℕ)
    {F : (List Bool × List Bool) × List (List Bool) → Bool}
    (hF : ComputableInPolyTime F (encPair (encPair encBits encBits) (encList encBits)) encBool) :
    ComputableInPolyTime (censusVerifier VA kA c₀ p F) (encPair encBits encBits) encBool := by
  unfold censusVerifier
  refine (decPairUC.computable.comp (ComputableInPolyTime.fst _ _)).optionElimWithInput
    (ComputableInPolyTime.const false) ?_
  let encS := encPair (encPair encBits encBits) (encPair encBits encNat)
  have hcert : ComputableInPolyTime (fun s : (List Bool × List Bool) × (List Bool × ℕ) ↦ s.1.2)
      encS encBits := (ComputableInPolyTime.fst _ _).snd'
  have hu : ComputableInPolyTime (fun s : (List Bool × List Bool) × (List Bool × ℕ) ↦ s.2.1)
      encS encBits := (ComputableInPolyTime.snd _ _).fst'
  have hc : ComputableInPolyTime (fun s : (List Bool × List Bool) × (List Bool × ℕ) ↦ s.2.2)
      encS encNat := (ComputableInPolyTime.snd _ _).snd'
  have hutail : ComputableInPolyTime
      (fun s : (List Bool × List Bool) × (List Bool × ℕ) ↦ s.2.1.tail)
      encS encBits := ComputableInPolyTime.bitsTail.comp hu
  have htrue : ComputableInPolyTime
      (fun s : (List Bool × List Bool) × (List Bool × ℕ) ↦
        (decXM.decode s.2.1.tail).elim false fun xm ↦
          decide (p.eval xm.1.length ≤ xm.2) &&
            censusTableValid VA kA c₀ xm.2 s.1.2 &&
            decide (s.2.2 ≤ (censusTableWords kA c₀ xm.2 s.1.2).length) &&
            F ((xm.1, (s.1.2.drop (censusHalfL kA c₀ xm.2 s.1.2)).take (p.eval xm.1.length)),
              censusTableWords kA c₀ xm.2 s.1.2))
      encS encBool := by
    refine (decXM.computable.comp hutail).optionElimWithInput
      (ComputableInPolyTime.const false) ?_
    let encT := encPair encS (encPair encBits encUnary)
    have hcert' : ComputableInPolyTime
        (fun t : ((List Bool × List Bool) × (List Bool × ℕ)) × (List Bool × ℕ) ↦ t.1.1.2)
        encT encBits := hcert.comp (ComputableInPolyTime.fst _ _)
    have hc' : ComputableInPolyTime
        (fun t : ((List Bool × List Bool) × (List Bool × ℕ)) × (List Bool × ℕ) ↦ t.1.2.2)
        encT encNat := hc.comp (ComputableInPolyTime.fst _ _)
    have hx' : ComputableInPolyTime
        (fun t : ((List Bool × List Bool) × (List Bool × ℕ)) × (List Bool × ℕ) ↦ t.2.1)
        encT encBits := (ComputableInPolyTime.snd _ _).fst'
    have hm' : ComputableInPolyTime
        (fun t : ((List Bool × List Bool) × (List Bool × ℕ)) × (List Bool × ℕ) ↦ t.2.2)
        encT encUnary := (ComputableInPolyTime.snd _ _).snd'
    have hmc : ComputableInPolyTime
        (fun t : ((List Bool × List Bool) × (List Bool × ℕ)) × (List Bool × ℕ) ↦
          (t.2.2, t.1.1.2))
        encT (encPair encUnary encBits) := hm'.prod hcert'
    have hp_eval : ComputableInPolyTime
        (fun t : ((List Bool × List Bool) × (List Bool × ℕ)) × (List Bool × ℕ) ↦
          p.eval t.2.1.length)
        encT encUnary :=
      (ComputableInPolyTime.unary_eval p).comp (ComputableInPolyTime.length_bits.comp hx')
    have hchk1 := ComputableInPolyTime.unary_le' hp_eval hm'
    have hchk2 := (computableInPolyTime_censusTableValid hVA kA c₀).comp hmc
    have hwords := (computableInPolyTime_censusTableWords kA c₀).comp hmc
    have hchk3 := ComputableInPolyTime.binary_le' hc'
      (ComputableInPolyTime.unary_to_binary.comp
        ((ComputableInPolyTime.length encBits).comp hwords))
    have hwit := ComputableInPolyTime.bitsTakeWithInput
      (ComputableInPolyTime.bitsDropWithInput hcert'
        ((computableInPolyTime_censusHalfL kA c₀).comp hmc)) hp_eval
    have hchk4 := hF.comp ((hx'.prod hwit).prod hwords)
    exact ComputableInPolyTime.bool_and'
      (ComputableInPolyTime.bool_and' (ComputableInPolyTime.bool_and' hchk1 hchk2) hchk3) hchk4
  have hfalse : ComputableInPolyTime
      (fun s : (List Bool × List Bool) × (List Bool × ℕ) ↦
        (decUnaryStrict.decode s.2.1.tail).elim false fun m ↦
          censusTableValid VA kA c₀ m s.1.2 &&
            decide (s.2.2 ≤ (censusTableWords kA c₀ m s.1.2).length))
      encS encBool := by
    refine (decUnaryStrict.computable.comp hutail).optionElimWithInput
      (ComputableInPolyTime.const false) ?_
    let encT := encPair encS encUnary
    have hmc : ComputableInPolyTime
        (fun t : ((List Bool × List Bool) × (List Bool × ℕ)) × ℕ ↦ (t.2, t.1.1.2))
        encT (encPair encUnary encBits) :=
      (ComputableInPolyTime.snd _ _).prod (hcert.comp (ComputableInPolyTime.fst _ _))
    have hc' : ComputableInPolyTime
        (fun t : ((List Bool × List Bool) × (List Bool × ℕ)) × ℕ ↦ t.1.2.2)
        encT encNat := hc.comp (ComputableInPolyTime.fst _ _)
    have hwords := (computableInPolyTime_censusTableWords kA c₀).comp hmc
    exact ComputableInPolyTime.bool_and'
      ((computableInPolyTime_censusTableValid hVA kA c₀).comp hmc)
      (ComputableInPolyTime.binary_le' hc'
        (ComputableInPolyTime.unary_to_binary.comp
          ((ComputableInPolyTime.length encBits).comp hwords)))
  exact ComputableInPolyTime.ite' (ComputableInPolyTime.bitsIsEmpty.comp hu)
    (ComputableInPolyTime.const false)
    (ComputableInPolyTime.ite'
      ((ComputableInPolyTime.headD (encA := encBool) (encL := encBits) false).comp hu)
      htrue hfalse)

private theorem exists_censusTable {A : Set (List Bool)} {VA : List Bool × List Bool → Bool}
    {kA cA : ℕ}
    (hVA_spec : ∀ a L, cA * 2 ^ (kA * a.length) + cA ≤ L →
      (a ∈ A ↔ ∃ w : List Bool, w.length = L ∧ VA (a, w) = true))
    (m : ℕ) :
    let c₀ := cA + cA + 1
    ∃ tbl : List Bool, tbl.length = 2 ^ ((kA + 1) * m + c₀ + 2) ∧
      ∀ rest : List Bool, rest.length = 2 ^ ((kA + 1) * m + c₀ + 2) →
        censusTableValid VA kA c₀ m (tbl ++ rest) = true ∧
        (∀ u, u.length ≤ m → (u ∈ censusTableWords kA c₀ m (tbl ++ rest) ↔ u ∈ A)) ∧
        (censusTableWords kA c₀ m (tbl ++ rest)).length = census A m := by
  classical
  set c₀ := cA + cA + 1
  let N := 2 ^ (m + 1) - 1
  let W := 2 ^ (kA * m + c₀ + 1)
  let half := 2 ^ ((kA + 1) * m + c₀ + 2)
  have hNW_le : N * W ≤ half := by
    have h1 : N ≤ 2 ^ (m + 1) := Nat.sub_le _ _
    calc N * W ≤ 2 ^ (m + 1) * 2 ^ (kA * m + c₀ + 1) := Nat.mul_le_mul_right W h1
      _ = half := by
        dsimp [half]
        rw [← pow_add]
        congr 1
        ring
  have hrow_ex : ∀ i : ℕ, ∃ r : List Bool, r.length = W ∧
      (i < N → (r.headD false = decide (codeWord i ∈ A)) ∧
        (codeWord i ∈ A → VA (codeWord i, r.tail) = true)) := by
    intro i
    by_cases hi : i < N
    · by_cases hmem : codeWord i ∈ A
      · have hge := censusCert_ge kA cA m (codeWord i) (length_codeWord_le hi)
        obtain ⟨w, hwlen, hVw⟩ := (hVA_spec (codeWord i) (W - 1) hge).mp hmem
        refine ⟨true :: w, ?_, fun _ ↦ ⟨by simp [hmem], fun _ ↦ by simpa using hVw⟩⟩
        have hWpos : 1 ≤ W := Nat.one_le_two_pow
        simp [hwlen]
        omega
      · refine ⟨List.replicate W false, List.length_replicate,
          fun _ ↦ ⟨?_, fun h ↦ absurd h hmem⟩⟩
        have hWpos : 1 ≤ W := Nat.one_le_two_pow
        rw [show W = (W - 1) + 1 by omega, List.replicate_succ]
        simp [hmem]
    · exact ⟨List.replicate W false, List.length_replicate, fun h ↦ absurd h hi⟩
  choose rowFn hrow_len hrow_spec using hrow_ex
  let rows := (List.range N).map rowFn
  have hflat_len : rows.flatten.length = N * W := by
    rw [List.length_flatten, List.map_map]
    have hmap : (List.range N).map (List.length ∘ rowFn) = List.replicate N W := by
      apply List.ext_getElem (by simp)
      intro j hj _
      simp [hrow_len]
    rw [hmap, List.sum_replicate, smul_eq_mul]
  let tbl := rows.flatten ++ List.replicate (half - N * W) false
  have htbl_len : tbl.length = half := by
    simp [tbl, hflat_len]
    omega
  refine ⟨tbl, htbl_len, fun rest hrest ↦ ?_⟩
  have hcert_len : (tbl ++ rest).length = 2 * half := by
    rw [List.length_append, htbl_len, hrest]
    omega
  have hN_eq : censusNumStr m (tbl ++ rest) = N := by
    dsimp only [censusNumStr]
    have : N ≤ 2 * half := by
      have hWpos : 1 ≤ W := Nat.one_le_two_pow
      nlinarith
    exact Nat.min_eq_right (by omega)
  have hW_eq : censusRowW kA c₀ m (tbl ++ rest) = W := by
    dsimp only [censusRowW]
    have : W ≤ 2 * half := by
      have : kA * m + c₀ + 1 ≤ (kA + 1) * m + c₀ + 2 := by nlinarith
      have : W ≤ half := Nat.pow_le_pow_right (by omega) this
      omega
    exact Nat.min_eq_right (by omega)
  have hgetRow (i : ℕ) (hi : i < N) : censusGetRow kA c₀ m (tbl ++ rest) i = rowFn i := by
    dsimp only [censusGetRow, tbl]
    rw [hW_eq, List.append_assoc]
    have hrows_all : ∀ r ∈ rows, r.length = W := by
      intro r hr
      obtain ⟨j, -, rfl⟩ := List.mem_map.mp hr
      exact hrow_len j
    have hi' : i < rows.length := by simpa [rows] using hi
    simpa [rows] using drop_take_flatMap_fixed rows hrows_all
      (List.replicate (half - N * W) false ++ rest) hi'
  have hvalid : censusTableValid VA kA c₀ m (tbl ++ rest) = true := by
    simp only [censusTableValid, hN_eq, List.all_eq_true, List.mem_range, Bool.or_eq_true,
      Bool.not_eq_true']
    intro i hi
    rw [hgetRow i hi, (hrow_spec i hi).1]
    by_cases hmem : codeWord i ∈ A
    · exact Or.inr ((hrow_spec i hi).2 hmem)
    · exact Or.inl (by simp [hmem])
  have hfilt_eq :
      ((List.range N).filter fun i ↦ (censusGetRow kA c₀ m (tbl ++ rest) i).headD false) =
      (List.range N).filter fun i ↦ decide (codeWord i ∈ A) := by
    apply List.filter_congr
    intro i hi
    rw [List.mem_range] at hi
    rw [hgetRow i hi, (hrow_spec i hi).1]
  have hwords_mem : ∀ u, u.length ≤ m → (u ∈ censusTableWords kA c₀ m (tbl ++ rest) ↔ u ∈ A) := by
    intro u hu
    simp only [censusTableWords, hN_eq, hfilt_eq, List.mem_map, List.mem_filter, List.mem_range,
      decide_eq_true_eq]
    constructor
    · rintro ⟨i, ⟨-, hiA⟩, rfl⟩
      exact hiA
    · intro huA
      refine ⟨tallyCode u - 1, ⟨tallyCode_sub_one_lt hu, ?_⟩, codeWord_tallyCode u⟩
      simpa only [codeWord_tallyCode] using huA
  have hwords_len : (censusTableWords kA c₀ m (tbl ++ rest)).length = census A m := by
    simp only [censusTableWords, hN_eq, hfilt_eq, List.length_map, census,
      List.countP_eq_length_filter]
    rfl
  exact ⟨hvalid, hwords_mem, hwords_len⟩

private theorem censusTable_sound {A : Set (List Bool)} {VA : List Bool × List Bool → Bool}
    {kA cA m : ℕ} {cert : List Bool}
    (hVA_spec : ∀ a L, cA * 2 ^ (kA * a.length) + cA ≤ L →
      (a ∈ A ↔ ∃ w : List Bool, w.length = L ∧ VA (a, w) = true))
    (hlen : cert.length = 2 ^ ((kA + 1) * m + (cA + cA + 1) + 3))
    (hvalid : censusTableValid VA kA (cA + cA + 1) m cert = true) :
    (censusTableWords kA (cA + cA + 1) m cert).Nodup ∧
      (∀ u ∈ censusTableWords kA (cA + cA + 1) m cert, u.length ≤ m ∧ u ∈ A) ∧
      (censusTableWords kA (cA + cA + 1) m cert).length ≤ census A m := by
  classical
  set c₀ := cA + cA + 1
  let N := 2 ^ (m + 1) - 1
  let W := 2 ^ (kA * m + c₀ + 1)
  have hN_eq : censusNumStr m cert = N := by
    dsimp only [censusNumStr]
    have : N ≤ cert.length := by
      rw [hlen]
      exact (Nat.sub_le _ _).trans (Nat.pow_le_pow_right (by omega) (by nlinarith))
    exact Nat.min_eq_right this
  have hW_eq : censusRowW kA c₀ m cert = W := by
    dsimp only [censusRowW]
    have : W ≤ cert.length := by
      rw [hlen]
      exact Nat.pow_le_pow_right (by omega) (by nlinarith)
    exact Nat.min_eq_right this
  have hnodup : (censusTableWords kA c₀ m cert).Nodup :=
    (List.nodup_range.filter _).map codeWord_injective
  have hsub : ∀ u ∈ censusTableWords kA c₀ m cert, u.length ≤ m ∧ u ∈ A := by
    intro u hu
    simp only [censusTableWords, hN_eq, List.mem_map, List.mem_filter, List.mem_range] at hu
    obtain ⟨i, ⟨hiN, hhead⟩, rfl⟩ := hu
    have hulen : (codeWord i).length ≤ m := length_codeWord_le hiN
    simp only [censusTableValid, hN_eq, List.all_eq_true, List.mem_range, Bool.or_eq_true,
      Bool.not_eq_true'] at hvalid
    have hVA_true : VA (codeWord i, (censusGetRow kA c₀ m cert i).tail) = true :=
      (hvalid i hiN).resolve_left (by rw [hhead]; decide)
    have hNW : (i + 1) * W ≤ cert.length := by
      rw [hlen]
      calc (i + 1) * W ≤ 2 ^ (m + 1) * 2 ^ (kA * m + c₀ + 1) := by
            apply Nat.mul_le_mul_right
            have : 1 ≤ 2 ^ (m + 1) := Nat.one_le_two_pow
            omega
        _ = 2 ^ ((kA + 1) * m + c₀ + 2) := by rw [← pow_add]; congr 1; ring
        _ ≤ 2 ^ ((kA + 1) * m + c₀ + 3) := Nat.pow_le_pow_right (by omega) (by omega)
    have hrow_len : (censusGetRow kA c₀ m cert i).length = W := by
      dsimp only [censusGetRow]
      rw [hW_eq, List.length_take, List.length_drop]
      have : W ≤ cert.length - i * W := by
        have : i * W + W = (i + 1) * W := by ring
        omega
      exact Nat.min_eq_left this
    have htail_len : (censusGetRow kA c₀ m cert i).tail.length = W - 1 := by
      rw [List.length_tail, hrow_len]
    have hmem : codeWord i ∈ A :=
      (hVA_spec (codeWord i) (W - 1) (censusCert_ge kA cA m (codeWord i) hulen)).mpr
        ⟨(censusGetRow kA c₀ m cert i).tail, htail_len, hVA_true⟩
    exact ⟨hulen, hmem⟩
  have hcard_le : (censusTableWords kA c₀ m cert).length ≤ census A m := by
    let S : Finset ℕ := (Finset.range N).filter fun i ↦ codeWord i ∈ A
    let T : Finset ℕ :=
      ((List.range N).filter fun i ↦ (censusGetRow kA c₀ m cert i).headD false).toFinset
    have hTS : T ⊆ S := by
      intro i hi
      simp only [T, List.mem_toFinset, List.mem_filter, List.mem_range] at hi
      have hmem : codeWord i ∈ censusTableWords kA c₀ m cert := by
        simp only [censusTableWords, hN_eq, List.mem_map, List.mem_filter, List.mem_range]
        exact ⟨i, hi, rfl⟩
      simp only [S, Finset.mem_filter, Finset.mem_range]
      exact ⟨hi.1, (hsub _ hmem).2⟩
    have hT_card : T.card = (censusTableWords kA c₀ m cert).length := by
      simp only [T, censusTableWords, hN_eq, List.length_map]
      exact List.toFinset_card_of_nodup (List.nodup_range.filter _)
    have hS_card : S.card = census A m := by
      simp only [S, N, census, List.countP_eq_length_filter]
      rw [← List.toFinset_card_of_nodup (List.nodup_range.filter _)]
      congr 1
      ext i
      simp [List.mem_range, Finset.mem_filter, Finset.mem_range]
    rw [← hT_card, ← hS_card]
    exact Finset.card_le_card hTS
  exact ⟨hnodup, hsub, hcard_le⟩

/-! ### Census collapse: `NP^{NE} ⊆ P^{NE}` -/

private theorem NPWithOracle_encBits_subset_PNE {A L : Set (List Bool)}
    (hA : A ∈ NE encBits) (hL : L ∈ NPWithOracle A encBits) :
    ∃ O ∈ NE encBits, L ∈ PWithOracle O encBits := by
  classical
  obtain ⟨kA, hAk⟩ := mem_NE_iff.mp hA
  obtain ⟨VA, cA, hVAO, hVA_spec⟩ := exists_verifier_of_mem_NTIME hAk
  have hVA : ComputableInPolyTime VA (encPair encBits encBits) encBool :=
    hVAO.computableInPolyTime
      (PolyBounded.of_forall_le 1 1 fun _ ↦ by simp)
      (PolyBounded.of_forall_le 1 1 fun _ ↦ by simp)
  obtain ⟨p, VL, hVL_pt, hVL_ver⟩ := hL
  obtain ⟨F, q, hF_pt, hF_spec⟩ := hVL_pt.exists_listOracle_bool
  set c₀ : ℕ := cA + cA + 1
  let expO (raw : List Bool) : ℕ := (kA + 1) * parseM raw + c₀ + 3
  let O : Set (List Bool) :=
    {raw | ∃ cert : List Bool, cert.length = 2 ^ expO raw ∧
      censusVerifier VA kA c₀ p F (raw, cert) = true}
  have hO_NE : O ∈ NE encBits := by
    have hexpO : ComputableInPolyTime expO encBits encUnary :=
      ComputableInPolyTime.unary_add'
        (ComputableInPolyTime.unary_add'
          (ComputableInPolyTime.unary_mul' (ComputableInPolyTime.const (kA + 1))
            computableInPolyTime_parseM)
          (ComputableInPolyTime.const c₀))
        (ComputableInPolyTime.const 3)
    refine setOf_exists_two_pow_mem_NE (L := expO) (K := kA + 1) (C₀ := c₀ + 3) hexpO ?_
      (computableInPolyTime_censusVerifier hVA kA c₀ p hF_pt)
    intro raw
    have := parseM_le raw
    simp only [expO, encBits_apply]
    nlinarith
  have hO_census (m c : ℕ) :
      encPair encBits encNat (false :: encUnary m, c) ∈ O ↔ c ≤ census A m := by
    have hV_eq (cert : List Bool) :
        censusVerifier VA kA c₀ p F (encPair encBits encNat (false :: encUnary m, c), cert) =
          (censusTableValid VA kA c₀ m cert &&
            decide (c ≤ (censusTableWords kA c₀ m cert).length)) := by
      dsimp only [censusVerifier]
      rw [decPairUC.decode_enc]
      simp only [Option.elim_some, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte,
        List.headD_cons, List.tail_cons]
      rw [decUnaryStrict.decode_enc]
      rfl
    simp only [O, Set.mem_ofPred_eq, expO, parseM_census, hV_eq, Bool.and_eq_true,
      decide_eq_true_eq]
    constructor
    · rintro ⟨cert, hlen, hvalid, hcle⟩
      exact hcle.trans (censusTable_sound hVA_spec hlen hvalid).2.2
    · intro hcle
      obtain ⟨tbl, htbl_len, htbl⟩ := exists_censusTable hVA_spec m
      let rest := List.replicate (2 ^ ((kA + 1) * m + c₀ + 2)) false
      refine ⟨tbl ++ rest, ?_, (htbl rest List.length_replicate).1, ?_⟩
      · rw [List.length_append, htbl_len, List.length_replicate, pow_succ]
        ring
      · rw [(htbl rest List.length_replicate).2.2]
        exact hcle
  let mBound (x : List Bool) : ℕ :=
    max (p.eval x.length) (q.eval (2 * x.length + 1 + p.eval x.length))
  have hO_sim (x : List Bool) :
      encPair encBits encNat
        (true :: encPair encBits encUnary (x, mBound x), census A (mBound x)) ∈ O ↔ x ∈ L := by
    set m := mBound x
    have hpm : p.eval x.length ≤ m := le_max_left _ _
    have hqm : q.eval (2 * x.length + 1 + p.eval x.length) ≤ m := le_max_right _ _
    have hV_eq (cert : List Bool) :
        censusVerifier VA kA c₀ p F
          (encPair encBits encNat (true :: encPair encBits encUnary (x, m), census A m), cert) =
          (decide (p.eval x.length ≤ m) &&
            censusTableValid VA kA c₀ m cert &&
            decide (census A m ≤ (censusTableWords kA c₀ m cert).length) &&
            F ((x, (cert.drop (censusHalfL kA c₀ m cert)).take (p.eval x.length)),
              censusTableWords kA c₀ m cert)) := by
      dsimp only [censusVerifier]
      rw [decPairUC.decode_enc]
      simp only [Option.elim_some, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte,
        List.headD_cons, List.tail_cons]
      rw [decXM.decode_enc]
      rfl
    simp only [O, Set.mem_ofPred_eq, expO, parseM_sim, hV_eq, Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨cert, hlen, ⟨⟨-, hvalid⟩, hge⟩, hFtrue⟩
      obtain ⟨hnodup, hsub, -⟩ := censusTable_sound hVA_spec hlen hvalid
      have hexact := mem_iff_of_card_ge_census hnodup hsub hge
      have hhalf_eq : censusHalfL kA c₀ m cert = 2 ^ ((kA + 1) * m + c₀ + 2) := by
        dsimp only [censusHalfL]
        rw [hlen, pow_succ]
        exact Nat.min_eq_right (by omega)
      have hpm_half : p.eval x.length ≤ 2 ^ ((kA + 1) * m + c₀ + 2) := by
        have hm2 : m ≤ 2 ^ m := Nat.lt_two_pow_self.le
        exact hpm.trans (hm2.trans (Nat.pow_le_pow_right (by omega) (by nlinarith)))
      let w_wit := (cert.drop (censusHalfL kA c₀ m cert)).take (p.eval x.length)
      have hw_len : w_wit.length = p.eval x.length := by
        dsimp only [w_wit]
        rw [List.length_take, List.length_drop, hhalf_eq, hlen, pow_succ]
        exact Nat.min_eq_left (by omega)
      have hF_eq : F ((x, w_wit), censusTableWords kA c₀ m cert) = VL (x, w_wit) := by
        apply hF_spec (x, w_wit) (censusTableWords kA c₀ m cert)
        intro u hu
        have hu' : u.length ≤ m := by
          rw [length_encPair, encBits_apply, encBits_apply, hw_len] at hu
          exact hu.trans hqm
        exact hexact u hu'
      rw [hVL_ver x]
      exact ⟨w_wit, by simpa [encBits_apply] using hw_len, hF_eq ▸ hFtrue⟩
    · intro hxL
      obtain ⟨w_wit, hw_len, hVL_true⟩ := (hVL_ver x).mp hxL
      simp only [encBits_apply] at hw_len
      obtain ⟨tbl, htbl_len, htbl⟩ := exists_censusTable hVA_spec m
      let half := 2 ^ ((kA + 1) * m + c₀ + 2)
      have hw_half : w_wit.length ≤ half := by
        rw [hw_len]
        have hm2 : m ≤ 2 ^ m := Nat.lt_two_pow_self.le
        exact hpm.trans (hm2.trans (Nat.pow_le_pow_right (by omega) (by nlinarith)))
      let rest := w_wit ++ List.replicate (half - w_wit.length) false
      have hrest_len : rest.length = half := by
        simp [rest]
        omega
      obtain ⟨hvalid, hexact, hlen_eq⟩ := htbl rest hrest_len
      have hcert_len : (tbl ++ rest).length = 2 ^ ((kA + 1) * m + c₀ + 3) := by
        rw [List.length_append, htbl_len, hrest_len, pow_succ]
        ring
      have hhalf_eq : censusHalfL kA c₀ m (tbl ++ rest) = half := by
        dsimp only [censusHalfL]
        rw [hcert_len, pow_succ]
        exact Nat.min_eq_right (by omega)
      have hw_rec :
          ((tbl ++ rest).drop (censusHalfL kA c₀ m (tbl ++ rest))).take (p.eval x.length) =
            w_wit := by
        rw [hhalf_eq, List.drop_left' htbl_len]
        dsimp only [rest]
        rw [← hw_len, List.take_left]
      have hF_eq : F ((x, w_wit), censusTableWords kA c₀ m (tbl ++ rest)) = VL (x, w_wit) := by
        apply hF_spec (x, w_wit) (censusTableWords kA c₀ m (tbl ++ rest))
        intro u hu
        have hu' : u.length ≤ m := by
          rw [length_encPair, encBits_apply, encBits_apply, hw_len] at hu
          exact hu.trans hqm
        exact hexact u hu'
      refine ⟨tbl ++ rest, hcert_len, ⟨⟨hpm, hvalid⟩, le_of_eq hlen_eq.symm⟩, ?_⟩
      rw [hw_rec, hF_eq, hVL_true]
  have hp_pt : ComputableInPolyTime (fun x : List Bool ↦ p.eval x.length) encBits encUnary :=
    (ComputableInPolyTime.unary_eval p).comp ComputableInPolyTime.length_bits
  have hq_pt : ComputableInPolyTime
      (fun x : List Bool ↦ q.eval (2 * x.length + 1 + p.eval x.length)) encBits encUnary :=
    (ComputableInPolyTime.unary_eval q).comp
      (ComputableInPolyTime.unary_add'
        (ComputableInPolyTime.unary_add'
          (ComputableInPolyTime.unary_mul' (ComputableInPolyTime.const 2)
            ComputableInPolyTime.length_bits)
          (ComputableInPolyTime.const 1))
        hp_pt)
  have h_mBound_pt : ComputableInPolyTime mBound encBits encUnary :=
    ComputableInPolyTime.unary_max.comp (hp_pt.prod hq_pt)
  have h_census_comp :
      ComputableInPolyTimeWithOracle O
        (fun x : List Bool ↦ census A (mBound x)) encBits encNat := by
    let uTag (x : List Bool) : List Bool := false :: encUnary (mBound x)
    let Nbits (x : List Bool) : ℕ := mBound x + 1
    have huTag : ComputableInPolyTime uTag encBits encBits :=
      ComputableInPolyTime.bitsCons (ComputableInPolyTime.const false)
        ((ComputableInPolyTime.of_eq (f := encUnary) fun _ ↦ rfl).comp h_mBound_pt)
    have hNbits : ComputableInPolyTime Nbits encBits encUnary :=
      ComputableInPolyTime.unary_add' h_mBound_pt (ComputableInPolyTime.const 1)
    refine ⟨fun x ↦ BinarySearch.search (uTag x) (Nbits x),
      BinarySearch.isOraclePPTOn_search huTag hNbits, fun x ↦ ?_⟩
    exact BinarySearch.interpret_id_search (hO_census (mBound x)) (census_lt A (mBound x))
  have h_query_prep :
      ComputableInPolyTime
        (fun xc : List Bool × ℕ ↦
          encPair encBits encNat (true :: encPair encBits encUnary (xc.1, mBound xc.1), xc.2))
        (encPair encBits encNat) encBits := by
    have hx : ComputableInPolyTime (fun xc : List Bool × ℕ ↦ xc.1)
        (encPair encBits encNat) encBits := ComputableInPolyTime.fst _ _
    have hc : ComputableInPolyTime (fun xc : List Bool × ℕ ↦ xc.2)
        (encPair encBits encNat) encNat := ComputableInPolyTime.snd _ _
    have hxm : ComputableInPolyTime
        (fun xc : List Bool × ℕ ↦ encPair encBits encUnary (xc.1, mBound xc.1))
        (encPair encBits encNat) encBits :=
      (ComputableInPolyTime.of_eq (f := encPair encBits encUnary) fun _ ↦ rfl).comp
        (hx.prod (h_mBound_pt.comp hx))
    have htag : ComputableInPolyTime
        (fun xc : List Bool × ℕ ↦ true :: encPair encBits encUnary (xc.1, mBound xc.1))
        (encPair encBits encNat) encBits :=
      ComputableInPolyTime.bitsCons (ComputableInPolyTime.const true) hxm
    exact (ComputableInPolyTime.of_eq (f := encPair encBits encNat) fun _ ↦ rfl).comp
      (htag.prod hc)
  have h_dec_O : ComputableInPolyTimeWithOracle O
      (fun x : List Bool ↦
        decide (encPair encBits encNat
          (true :: encPair encBits encUnary (x, mBound x), census A (mBound x)) ∈ O))
      encBits encBool :=
    ((computableInPolyTimeWithOracle_mem O).preprocess h_query_prep).comp_with h_census_comp
  refine ⟨O, hO_NE, _, h_dec_O, fun x ↦ ?_⟩
  simp only [decide_eq_true_eq, hO_sim x]

/-! ### Strong exponential hierarchy classes and collapse -/

/-- `P^{NE}`: languages decidable in polynomial time relative to an oracle in `NE`. -/
def PNE {α : Type} (enc : α ↪ List Bool) : Set (Set α) :=
  ⋃ A ∈ NE encBits, PWithOracle A enc

/-- `NP^{NE}`: languages in `NP` relative to an oracle in `NE`. -/
def NPNE {α : Type} (enc : α ↪ List Bool) : Set (Set α) :=
  ⋃ A ∈ NE encBits, NPWithOracle A enc

/-- `coNP^{NE}`: languages in `coNP` relative to an oracle in `NE`. -/
def coNPNE {α : Type} (enc : α ↪ List Bool) : Set (Set α) :=
  ⋃ A ∈ NE encBits, {L | Lᶜ ∈ NPWithOracle A enc}

/-- Membership in `PNE enc`. -/
theorem mem_PNE {α : Type} {enc : α ↪ List Bool} {L : Set α} :
    L ∈ PNE enc ↔ ∃ A ∈ NE encBits, L ∈ PWithOracle A enc := by
  simp only [PNE, Set.mem_iUnion, exists_prop]

/-- Membership in `NPNE enc`. -/
theorem mem_NPNE {α : Type} {enc : α ↪ List Bool} {L : Set α} :
    L ∈ NPNE enc ↔ ∃ A ∈ NE encBits, L ∈ NPWithOracle A enc := by
  simp only [NPNE, Set.mem_iUnion, exists_prop]

/-- Membership in `coNPNE enc`. -/
theorem mem_coNPNE {α : Type} {enc : α ↪ List Bool} {L : Set α} :
    L ∈ coNPNE enc ↔ ∃ A ∈ NE encBits, Lᶜ ∈ NPWithOracle A enc := by
  simp only [coNPNE, Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]

/-- **Census collapse (`NP^A ⊆ P^{NE}` for every `A ∈ NE`)**: proved for arbitrary
encodings `enc` by extending the `NP^A` verifier to raw bit strings and applying census search. -/
theorem NPWithOracle_subset_PNE_of_mem_NE {α : Type} {enc : α ↪ List Bool}
    {A : Set (List Bool)} (hA : A ∈ NE encBits) :
    NPWithOracle A enc ⊆ PNE enc := by
  rintro L ⟨p, V, hV, hver⟩
  obtain ⟨Vraw, hVraw, hVeq⟩ := hV.exists_bool_extension
  let Vbits (xw : List Bool × List Bool) : Bool := Vraw (encPair encBits encBits xw)
  have hVbits : ComputableInPolyTimeWithOracle A Vbits (encPair encBits encBits) encBool :=
    hVraw.preprocess (ComputableInPolyTime.of_eq fun _ ↦ rfl)
  let Lbits : Set (List Bool) :=
    {x | ∃ w : List Bool, w.length = p.eval x.length ∧ Vbits (x, w) = true}
  have hLbits : Lbits ∈ NPWithOracle A encBits :=
    ⟨p, Vbits, hVbits, fun _ ↦ Iff.rfl⟩
  obtain ⟨O, hO_NE, hLbits_O⟩ := NPWithOracle_encBits_subset_PNE hA hLbits
  have hred : PolyTimeReducible enc encBits L Lbits := by
    refine ⟨enc, ComputableInPolyTime.of_eq fun _ ↦ rfl, fun a ↦ ?_⟩
    rw [hver a]
    simp only [Lbits, Set.mem_ofPred_eq, Vbits]
    refine exists_congr fun w ↦ and_congr_right fun _ ↦ ?_
    have hpair_eq : encPair encBits encBits (enc a, w) = encPair enc encBits (a, w) := rfl
    rw [hpair_eq, hVeq (a, w)]
  exact mem_PNE.mpr ⟨O, hO_NE, hred.mem_PWithOracle hLbits_O⟩

/-- **`NP^{NE} = P^{NE}`**. -/
theorem NPNE_eq_PNE {α : Type} (enc : α ↪ List Bool) : NPNE enc = PNE enc := by
  apply Set.Subset.antisymm
  · exact Set.iUnion₂_subset fun _ hA ↦ NPWithOracle_subset_PNE_of_mem_NE hA
  · exact Set.iUnion₂_mono fun A _ ↦ PWithOracle_subset_NPWithOracle A enc

/-- `P^{NE}` is closed under complement. -/
theorem compl_mem_PNE {α : Type} {enc : α ↪ List Bool} {L : Set α} (hL : L ∈ PNE enc) :
    Lᶜ ∈ PNE enc := by
  obtain ⟨A, hA, hLA⟩ := mem_PNE.mp hL
  exact mem_PNE.mpr ⟨A, hA, compl_mem_PWithOracle hLA⟩

/-- **`coNP^{NE} = P^{NE}`**. -/
theorem coNPNE_eq_PNE {α : Type} (enc : α ↪ List Bool) : coNPNE enc = PNE enc := by
  apply Set.Subset.antisymm
  · intro L hL
    obtain ⟨A, hA, hLc⟩ := mem_coNPNE.mp hL
    have hLc_PNE : Lᶜ ∈ PNE enc := NPWithOracle_subset_PNE_of_mem_NE hA hLc
    simpa only [compl_compl] using compl_mem_PNE hLc_PNE
  · intro L hL
    obtain ⟨A, hA, hLA⟩ := mem_PNE.mp hL
    exact mem_coNPNE.mpr ⟨A, hA, PWithOracle_subset_NPWithOracle A enc (compl_mem_PWithOracle hLA)⟩

/-- **`P^{P^{NE}} = P^{NE}`**: oracle substitution preserves `P^{NE}`. -/
theorem PWithOracle_subset_PNE_of_mem_PNE {α : Type} {enc : α ↪ List Bool}
    {B : Set (List Bool)} (hB : B ∈ PNE encBits) :
    PWithOracle B enc ⊆ PNE enc := by
  obtain ⟨A, hA, hBA⟩ := mem_PNE.mp hB
  exact fun _ hL ↦ mem_PNE.mpr ⟨A, hA, PWithOracle_subset_of_mem_PWithOracle hBA enc hL⟩

/-- **`NP^{P^{NE}} = P^{NE}`**: an `NP` machine with a `P^{NE}` oracle collapses to `P^{NE}`. -/
theorem NPWithOracle_subset_PNE_of_mem_PNE {α : Type} {enc : α ↪ List Bool}
    {B : Set (List Bool)} (hB : B ∈ PNE encBits) :
    NPWithOracle B enc ⊆ PNE enc := by
  obtain ⟨A, hA, hBA⟩ := mem_PNE.mp hB
  exact (NPWithOracle_subset_of_mem_PWithOracle hBA enc).trans
    (NPWithOracle_subset_PNE_of_mem_NE hA)

/-- **`NP^{coNP^{NE}} = P^{NE}`** (and equivalently `NP^{NP^{NE}} = P^{NE}`). -/
theorem NP_coNP_NE_eq_PNE {α : Type} (enc : α ↪ List Bool) :
    (⋃ B ∈ coNPNE encBits, NPWithOracle B enc) = PNE enc := by
  apply Set.Subset.antisymm
  · refine Set.iUnion₂_subset fun B hB ↦ ?_
    rw [coNPNE_eq_PNE] at hB
    exact NPWithOracle_subset_PNE_of_mem_PNE hB
  · intro L hL
    obtain ⟨A, hA, hLA⟩ := mem_PNE.mp hL
    exact Set.mem_iUnion₂.mpr
      ⟨A, mem_coNPNE.mpr
        ⟨A, hA, PWithOracle_subset_NPWithOracle A encBits
          (compl_mem_PWithOracle (mem_PWithOracle_self A))⟩,
        PWithOracle_subset_NPWithOracle A enc hLA⟩

/-- **`NP^{NP^{NE}} = P^{NE}`**. -/
theorem NP_NP_NE_eq_PNE {α : Type} (enc : α ↪ List Bool) :
    (⋃ B ∈ NPNE encBits, NPWithOracle B enc) = PNE enc := by
  rw [NPNE_eq_PNE]
  apply Set.Subset.antisymm
  · exact Set.iUnion₂_subset fun _ hB ↦ NPWithOracle_subset_PNE_of_mem_PNE hB
  · intro L hL
    obtain ⟨A, hA, hLA⟩ := mem_PNE.mp hL
    exact Set.mem_iUnion₂.mpr
      ⟨A, mem_PNE.mpr ⟨A, hA, mem_PWithOracle_self A⟩, PWithOracle_subset_NPWithOracle A enc hLA⟩

/-- The `Σ_r` levels of the strong exponential hierarchy: `E`, `NE`, `NP^{NE}`,
`NP^{NP^{NE}}`, ... -/
def SEHSigma : ℕ → ∀ {α : Type}, (α ↪ List Bool) → Set (Set α)
  | 0, _, enc => E enc
  | 1, _, enc => NE enc
  | r + 2, _, enc => ⋃ A ∈ SEHSigma (r + 1) encBits, NPWithOracle A enc

/-- The `Δ_r` levels of the strong exponential hierarchy: `E`, `E`, `P^{NE}`, `P^{NP^{NE}}`, ... -/
def SEHDelta : ℕ → ∀ {α : Type}, (α ↪ List Bool) → Set (Set α)
  | 0, _, enc => E enc
  | 1, _, enc => E enc
  | r + 2, _, enc => ⋃ A ∈ SEHSigma (r + 1) encBits, PWithOracle A enc

/-- The `Π_r` levels of the strong exponential hierarchy: complements of `Σ_r`. -/
def SEHPi (r : ℕ) {α : Type} (enc : α ↪ List Bool) : Set (Set α) :=
  {L | Lᶜ ∈ SEHSigma r enc}

/-- **Full collapse of the Strong Exponential Hierarchy**: for every `r ≥ 2`,
`Σ_r^{SEH} = Π_r^{SEH} = Δ_r^{SEH} = P^{NE}`. -/
theorem SEH_collapse (r : ℕ) (hr : 2 ≤ r) {α : Type} (enc : α ↪ List Bool) :
    SEHSigma r enc = PNE enc ∧ SEHPi r enc = PNE enc ∧ SEHDelta r enc = PNE enc := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hr
  have hSigma : ∀ n : ℕ, ∀ {β : Type} (e : β ↪ List Bool), SEHSigma (n + 2) e = PNE e := by
    intro n
    induction n with
    | zero =>
      intro β e
      exact NPNE_eq_PNE e
    | succ n ih =>
      intro β e
      change (⋃ A ∈ SEHSigma (n + 2) encBits, NPWithOracle A e) = PNE e
      rw [ih encBits, ← NPNE_eq_PNE encBits]
      exact NP_NP_NE_eq_PNE e
  have hS : SEHSigma (m + 2) enc = PNE enc := hSigma m enc
  have hP : SEHPi (m + 2) enc = PNE enc := by
    ext L
    simp only [SEHPi, Set.mem_ofPred_eq, hS]
    exact ⟨fun h ↦ by simpa only [compl_compl] using compl_mem_PNE h, compl_mem_PNE⟩
  have hD : SEHDelta (m + 2) enc = PNE enc := by
    cases m with
    | zero => rfl
    | succ m =>
      change (⋃ A ∈ SEHSigma (m + 2) encBits, PWithOracle A enc) = PNE enc
      rw [hSigma m encBits]
      apply Set.Subset.antisymm
      · exact Set.iUnion₂_subset fun _ hB ↦ PWithOracle_subset_PNE_of_mem_PNE hB
      · intro L hL
        obtain ⟨A, hA, hLA⟩ := mem_PNE.mp hL
        exact Set.mem_iUnion₂.mpr ⟨A, mem_PNE.mpr ⟨A, hA, mem_PWithOracle_self A⟩, hLA⟩
  exact ⟨hS, hP, hD⟩

/-! ### Padding equivalence `P^{NE} = P^{NEXP}` -/

/-- `P^{NEXP}`: languages decidable in polynomial time relative to an oracle in `NEXP`. -/
def PNEXP {α : Type} (enc : α ↪ List Bool) : Set (Set α) :=
  ⋃ A ∈ NEXP encBits, PWithOracle A enc

/-- Every language in `NEXP` polynomial-time many-one reduces to a padded language in `NE`. -/
theorem exists_NE_polyTimeReducible_of_mem_NEXP {A : Set (List Bool)} (hA : A ∈ NEXP encBits) :
    ∃ B ∈ NE encBits, PolyTimeReducible encBits encBits A B := by
  obtain ⟨k, hAk⟩ := mem_NEXP_iff.mp hA
  obtain ⟨VA, cA, hVAO, hVA_spec⟩ := exists_verifier_of_mem_NTIME hAk
  have hVA : ComputableInPolyTime VA (encPair encBits encBits) encBool :=
    hVAO.computableInPolyTime
      (PolyBounded.of_forall_le 1 1 fun _ ↦ by simp)
      (PolyBounded.of_forall_le 1 1 fun _ ↦ by simp)
  let c₀ : ℕ := cA + cA + 1
  let Vpad (p : List Bool × List Bool) : Bool :=
    decide ((unframe p.1).length ^ k ≤ p.1.length) && VA (unframe p.1, p.2)
  let B : Set (List Bool) :=
    {y | ∃ w : List Bool, w.length = 2 ^ (y.length + c₀) ∧ Vpad (y, w) = true}
  have hB_NE : B ∈ NE encBits := by
    have hL : ComputableInPolyTime (fun y : List Bool ↦ y.length + c₀) encBits encUnary :=
      ComputableInPolyTime.unary_add' ComputableInPolyTime.length_bits
        (ComputableInPolyTime.const c₀)
    have hVpad : ComputableInPolyTime Vpad (encPair encBits encBits) encBool := by
      dsimp only [Vpad]
      have hunf : ComputableInPolyTime (fun p : List Bool × List Bool ↦ unframe p.1)
          (encPair encBits encBits) encBits :=
        ComputableInPolyTime.unframe.comp (ComputableInPolyTime.fst encBits encBits)
      have hguard : ComputableInPolyTime
          (fun p : List Bool × List Bool ↦ decide ((unframe p.1).length ^ k ≤ p.1.length))
          (encPair encBits encBits) encBool :=
        ComputableInPolyTime.unary_le'
          ((ComputableInPolyTime.unary_pow k).comp
            (ComputableInPolyTime.length_bits.comp hunf))
          (ComputableInPolyTime.length_bits.comp (ComputableInPolyTime.fst encBits encBits))
      exact ComputableInPolyTime.bool_and' hguard
        (hVA.comp (hunf.prod (ComputableInPolyTime.snd encBits encBits)))
    exact setOf_exists_two_pow_mem_NE (L := fun y : List Bool ↦ y.length + c₀) (V := Vpad)
      (K := 1) (C₀ := c₀) hL (fun y ↦ by simp) hVpad
  let pad (x : List Bool) : List Bool := frame x ++ List.replicate (x.length ^ k) true
  have hpad_pt : ComputableInPolyTime pad encBits encBits :=
    ComputableInPolyTime.bitsAppend ComputableInPolyTime.frame
      ((ComputableInPolyTime.bitsReplicate true).comp
        ((ComputableInPolyTime.unary_pow k).comp ComputableInPolyTime.length_bits))
  refine ⟨B, hB_NE, pad, hpad_pt, fun x ↦ ?_⟩
  have hunf_pad : unframe (pad x) = x := unframe_frame_append x _
  have hlen_pad : x.length ^ k ≤ (pad x).length := by
    simp only [pad, List.length_append, length_frame, List.length_replicate]
    omega
  have hge : cA * 2 ^ (x.length ^ k) + cA ≤ 2 ^ ((pad x).length + c₀) := by
    have hpow : 2 ^ (x.length ^ k) ≤ 2 ^ (pad x).length :=
      Nat.pow_le_pow_right (by omega) hlen_pad
    have hc₀_le : 2 * cA + 1 ≤ 2 ^ c₀ := by
      have h1 : 2 * cA + 1 = c₀ := by omega
      rw [h1]
      exact Nat.lt_two_pow_self.le
    have hpos : 1 ≤ 2 ^ (pad x).length := Nat.one_le_two_pow
    calc cA * 2 ^ (x.length ^ k) + cA ≤ 2 * cA * 2 ^ (pad x).length := by nlinarith
      _ ≤ 2 ^ c₀ * 2 ^ (pad x).length := Nat.mul_le_mul_right _ (by omega)
      _ = 2 ^ ((pad x).length + c₀) := by rw [Nat.mul_comm, ← pow_add]
  simp only [B, Vpad, Set.mem_ofPred_eq, hunf_pad, hlen_pad, decide_true, Bool.true_and]
  exact hVA_spec x (2 ^ ((pad x).length + c₀)) hge

/-- **`P^{NE} = P^{NEXP}`**:
by padding, an oracle in `NEXP` adds no power to `P` beyond an oracle in `NE`. -/
theorem PNE_eq_PNEXP {α : Type} (enc : α ↪ List Bool) : PNE enc = PNEXP enc := by
  apply Set.Subset.antisymm
  · exact Set.iUnion₂_subset fun A hA ↦
      Set.subset_iUnion₂_of_subset A (NE_subset_NEXP hA) Set.Subset.rfl
  · refine Set.iUnion₂_subset fun A hA ↦ ?_
    obtain ⟨B, hB, hred⟩ := exists_NE_polyTimeReducible_of_mem_NEXP hA
    exact (hred.PWithOracle_subset enc).trans (Set.subset_iUnion₂_of_subset B hB Set.Subset.rfl)

end CslibFrontier.Complexity
