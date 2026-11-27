module

public import CslibFrontier.Foundations.Data.Code.SmallBias.ExpanderSmallBias
public import CslibFrontier.Computability.PolyTime.BitString.SmallBias
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.RotationMap.Family

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Max
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Finite
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Eq
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Fin
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Finite
import CslibFrontier.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial.Automation
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Polynomial-Time Row Evaluator for Small-Bias Codes

This module provides a uniform polynomial-time executable row evaluator for the explicit
linear-length
 small-bias binary linear codes constructed in
`CslibFrontier.Foundations.Data.Code.ExpanderSmallBias`, together with a bit-for-bit correctness
theorem tying the executable evaluator to `abnnrGenMap`.

All results are proved under standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`).

## Main definitions

* `CslibFrontier.Foundations.Data.Code.paddedJustesenRowEval`: single-row evaluator for the
  zero-padded binary Justesen code.
* `CslibFrontier.Foundations.Data.Code.abnnrRowEval`: single-row evaluator for `abnnrGenMap k t`.
* `CslibFrontier.Foundations.Data.Code.abnnrPuncturedMatrix`: evaluates a list of rows of
  `abnnrGenMap k t`.

## Main results

* `CslibFrontier.Foundations.Data.Code.paddedJustesenRowEval_eq`
* `CslibFrontier.Foundations.Data.Code.abnnrRowEval_eq`
* `CslibFrontier.Foundations.Data.Code.computableInPolyTime_paddedJustesenRowEval`
* `CslibFrontier.Foundations.Data.Code.computableInPolyTime_abnnrRowEval`
* `CslibFrontier.Foundations.Data.Code.computableInPolyTime_abnnrPuncturedMatrix`

## Tags

small-bias space, expander walk, ABNNR, polynomial time, row evaluator, coding theory
-/

public section

namespace CslibFrontier.Foundations.Data.Code

open Finset

section ABNNRPolyTime

/-- Executable single-row evaluator for the zero-padded Justesen code at vertex `v` for
dimension `k` using a precomputed binary-field multiplication table `tab` of degree `w`. -/
def paddedJustesenRowEval (tab : List (List (List Bool))) (k w N₀ v : ℕ) : List Bool :=
  if v < N₀ then
    let uIdx := v / (2 * w)
    let rem := v % (2 * w)
    let half := rem / w
    let bit := rem % w
    let uBits := bitsOfNat w (uIdx + 1)
    (List.range k).map fun r ↦
      let j := r / w
      let d := r % w
      let uPow := Cslib.BitString.powerWord tab uBits (j + half)
      let prod := Cslib.BinaryField.fieldMul tab uPow (List.replicate d false ++ [true])
      prod.getD bit false
  else List.replicate k false

@[simp]
theorem length_paddedJustesenRowEval (tab : List (List (List Bool))) (k w N₀ v : ℕ) :
    (paddedJustesenRowEval tab k w N₀ v).length = k := by
  unfold paddedJustesenRowEval
  split_ifs <;> simp

/-- `paddedJustesenRowEval` agrees bit-for-bit with `paddedJustesenMap k` on all standard
basis vectors `Pi.single r 1`. -/
theorem paddedJustesenRowEval_eq (k : ℕ) (v : Fin (paddedJustesenLen k)) (r : Fin k) :
    let s := justesenScale k
    let w := 16 * s
    (paddedJustesenRowEval (Cslib.BinaryField.fieldTable w) k w (justesenLen k) v.val).getD r.val
        false =
      Cslib.BitString.bitEquiv (paddedJustesenMap k (Pi.single r 1) v) := by
  set s := justesenScale k
  set w := 16 * s
  have hw : w ≠ 0 := by have := justesenScale_pos k; omega
  have htab := Cslib.BinaryField.isMulTable_fieldTable hw
  unfold paddedJustesenRowEval
  rw [paddedJustesenMap_apply]
  by_cases hv : v.val < justesenLen k
  · simp only [hv, ↓reduceIte, dite_true]
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range r.isLt]
    simp only [Option.map_some, Option.getD_some]
    set uIdx := v.val / (2 * w)
    set rem := v.val % (2 * w)
    set half := rem / w
    set bit := rem % w
    have hidx : justesenIndexEquiv k ⟨v.val, hv⟩ =
        (binaryFieldUnitsEquiv hw ⟨uIdx, by
            have h1 : v.val < (2 ^ w - 1) * (2 * w) := by
              have : justesenLen k = (2 ^ w - 1) * (2 * w) := by
                rw [justesenLen_eq]; dsimp [w, s]; ring
              omega
            exact Nat.div_lt_of_lt_mul (by rwa [mul_comm])⟩,
          (⟨half, by
              have hrem : rem < 2 * w := Nat.mod_lt _ (by omega)
              exact Nat.div_lt_of_lt_mul (by rwa [mul_comm])⟩,
            ⟨bit, Nat.mod_lt _ (by omega)⟩)) := by
      simpa [uIdx, rem, half, bit, w, s] using justesenIndexEquiv_apply k ⟨v.val, hv⟩
    rw [hidx]
    set u : Cslib.BinaryField w :=
      Cslib.BinaryField.fieldOfBits (Cslib.BinaryField.basis hw) (bitsOfNat w (uIdx + 1))
    set j : ℕ := r.val / w
    set d : ℕ := r.val % w
    have hpoly : (justesenOuterPoly k (Pi.single r 1)).eval u =
        Cslib.BinaryField.basis hw ⟨d, Nat.mod_lt _ (by omega)⟩ * u ^ j := by
      rw [justesenOuterPoly_eq, ← Polynomial.coe_evalRingHom, map_sum]
      simp only [Polynomial.coe_evalRingHom]
      have hdim : k ≤ 8 * s * 2 ^ (16 * s) := le_dim_justesenScale k
      have hr_lt : r.val < w * 2 ^ (w - 1) := by
        have hpow : 2 ^ w = 2 * 2 ^ (w - 1) := by rw [← pow_succ']; congr 1; omega
        have : 8 * s * 2 ^ (16 * s) = w * 2 ^ (w - 1) := by
          change 8 * s * 2 ^ w = w * 2 ^ (w - 1); rw [hpow]; dsimp [w]; ring
        omega
      set jFin : Fin (2 ^ (w - 1)) := ⟨j, Nat.div_lt_of_lt_mul (mul_comm w _ ▸ hr_lt)⟩
      set dFin : Fin w := ⟨d, Nat.mod_lt _ (by omega)⟩
      rw [Finset.sum_eq_single jFin]
      · simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
        congr 1
        rw [Finset.sum_eq_single dFin]
        · have hjd : jFin.val * w + dFin.val = r.val := by
            dsimp [jFin, dFin, j, d]; rw [mul_comm, Nat.div_add_mod]
          change (if h : jFin.val * w + dFin.val < k then
              Pi.single (M := fun _ ↦ ZMod 2) r 1 ⟨jFin.val * w + dFin.val, h⟩
            else 0) • Cslib.BinaryField.basis hw dFin = Cslib.BinaryField.basis hw dFin
          simp only [hjd, r.isLt, ↓reduceDIte, Pi.single_eq_same, one_smul]
        · intro d' _ hd'
          split_ifs with hlt
          · have hne : (⟨jFin.val * w + d'.val, hlt⟩ : Fin k) ≠ r := by
              intro heq
              have hval := congrArg Fin.val heq
              have hmod : d'.val = d := by
                have := congrArg (· % w) hval
                simp only [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt d'.isLt] at this
                exact this
              exact hd' (Fin.ext hmod)
            change (Pi.single (M := fun _ ↦ ZMod 2) r 1 ⟨jFin.val * w + d'.val, hlt⟩) •
              Cslib.BinaryField.basis hw d' = 0
            rw [Pi.single_eq_of_ne hne, zero_smul]
          · exact zero_smul _ _
        · intro h; exact (h (Finset.mem_univ _)).elim
      · intro j' _ hj'
        simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
        have hzero : ∑ d' : Fin w,
            (if h : j'.val * w + d'.val < k then
              Pi.single (M := fun _ ↦ ZMod 2) r 1 ⟨j'.val * w + d'.val, h⟩
            else (0 : ZMod 2)) • Cslib.BinaryField.basis hw d' = 0 := by
          refine Finset.sum_eq_zero fun d' _ ↦ ?_
          split_ifs with hlt
          · have hne : (⟨j'.val * w + d'.val, hlt⟩ : Fin k) ≠ r := by
              intro heq
              have hval := congrArg Fin.val heq
              dsimp only at hval
              have hdiv : j'.val = j := by
                have := congrArg (· / w) hval
                rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega),
                  Nat.div_eq_of_lt d'.isLt, zero_add] at this
                exact this
              exact hj' (Fin.ext hdiv)
            simp [Pi.single_eq_of_ne hne]
          · simp
        rw [hzero, zero_mul]
      · intro h; exact (h (Finset.mem_univ _)).elim
    have hpow_eval : Cslib.BinaryField.fieldOfBits (Cslib.BinaryField.basis hw)
        (Cslib.BitString.powerWord (Cslib.BinaryField.fieldTable w) (bitsOfNat w (uIdx + 1))
          (j + half)) = u ^ (j + half) := by
      have h1 : ∀ e, Cslib.BinaryField.fieldOfBits (Cslib.BinaryField.basis hw)
          (Cslib.BitString.powerWord (Cslib.BinaryField.fieldTable w) (bitsOfNat w (uIdx + 1)) e) =
            u ^ e := by
        intro e
        induction e with
        | zero => simp [Cslib.BitString.powerWord, Cslib.BinaryField.fieldOfBits_one hw]
        | succ e ihe =>
          rw [Cslib.BitString.powerWord, Function.iterate_succ_apply', ← Cslib.BitString.powerWord,
            Cslib.BinaryField.fieldOfBits_fieldMul htab, ihe, pow_succ]
      exact h1 (j + half)
    have hbasis_eval : Cslib.BinaryField.fieldOfBits (Cslib.BinaryField.basis hw)
        (List.replicate d false ++ [true]) =
          Cslib.BinaryField.basis hw ⟨d, Nat.mod_lt _ (by omega)⟩ := by
      have hd_lt : d < w := Nat.mod_lt _ (by omega)
      rw [Cslib.BinaryField.fieldOfBits, Cslib.BinaryField.ofBits,
        Finset.sum_eq_single ⟨d, hd_lt⟩]
      · simp
      · intro d' _ hd'
        have hget : (List.replicate d false ++ [true])[d'.val]?.getD false = false := by
          by_cases hlt : d'.val < d
          · rw [List.getElem?_append_left (by simp [hlt]), List.getElem?_replicate]
            simp [hlt]
          · have hgt : d < d'.val := by
              have : d'.val ≠ d := fun h ↦ hd' (Fin.ext h)
              omega
            rw [List.getElem?_append_right (by simp; omega), List.length_replicate,
              List.getElem?_eq_none (by simp; omega)]
            rfl
        simp only [List.getD_eq_getElem?_getD, smul_eq_zero, EmbeddingLike.map_eq_zero_iff]
        left; rw [hget]; rfl
      · intro h; exact (h (Finset.mem_univ _)).elim
    have hprod_eval : Cslib.BinaryField.fieldOfBits (Cslib.BinaryField.basis hw)
        (Cslib.BinaryField.fieldMul (Cslib.BinaryField.fieldTable w)
          (Cslib.BitString.powerWord (Cslib.BinaryField.fieldTable w) (bitsOfNat w (uIdx + 1))
            (j + half))
          (List.replicate d false ++ [true])) =
          (if half = 0 then (justesenOuterPoly k (Pi.single r 1)).eval u
            else u * (justesenOuterPoly k (Pi.single r 1)).eval u) := by
      rw [Cslib.BinaryField.fieldOfBits_fieldMul htab, hpow_eval, hbasis_eval, hpoly]
      have hhalf_lt : half < 2 := by
        have hrem : rem < 2 * w := Nat.mod_lt _ (by omega)
        exact Nat.div_lt_of_lt_mul (by rwa [mul_comm])
      rcases Nat.eq_zero_or_pos half with h0 | hpos
      · simp [h0, mul_comm]
      · have h1 : half = 1 := by omega
        simp only [h1, Nat.one_ne_zero, ↓reduceIte, pow_add, pow_one]
        ring
    have hbit_lt : bit < w := Nat.mod_lt _ (by omega)
    have heq := congrFun (congrArg (Cslib.BinaryField.equivBits hw) hprod_eval) ⟨bit, hbit_lt⟩
    rw [Cslib.BinaryField.equivBits_fieldOfBits] at heq
    rw [heq]
    simp only [Cslib.Code.justesen, Cslib.Code.concat, Cslib.Code.wozencraft,
      binaryFieldUnitsEquiv_val, u]
    by_cases hh : half = 0
    · simp [hh]
    · have hh' : (⟨half, by
        have hrem : rem < 2 * w := Nat.mod_lt _ (by omega)
        exact Nat.div_lt_of_lt_mul (by rwa [mul_comm])⟩ : Fin 2) ≠ 0 :=
        fun h ↦ hh (congrArg Fin.val h)
      simp [hh, hh']
  · simp only [hv, ↓reduceIte, dite_false, map_zero]
    rw [List.getD_eq_getElem?_getD, List.getElem?_replicate]
    simp [r.isLt]
    rfl

/-- `justesenScale` is uniformly polynomial-time on unary input. -/
theorem computableInPolyTime_justesenScale :
    Turing.MultiTapeTM.ComputableInPolyTime justesenScale
      Turing.MultiTapeTM.encUnary Turing.MultiTapeTM.encUnary := by
  open Turing.MultiTapeTM ComputableInPolyTime in
  have hlog : ComputableInPolyTime (fun k : ℕ ↦ Nat.log 2 k + 2) encUnary encUnary :=
    unary_add' (binary_log_two.comp unary_to_binary) (const 2)
  have hpred : ComputableInPolyTime
      (fun q : ℕ × ℕ ↦ decide (1 ≤ q.2 ∧ q.1 ≤ 8 * q.2 * 2 ^ (16 * q.2)))
      (encPair encUnary encUnary) encBool := by
    have h1 : ComputableInPolyTime (fun q : ℕ × ℕ ↦ decide (1 ≤ q.2))
        (encPair encUnary encUnary) encBool := by fun_prop
    have h2 : ComputableInPolyTime (fun q : ℕ × ℕ ↦ decide (q.1 ≤ 8 * q.2 * 2 ^ (16 * q.2)))
        (encPair encUnary encUnary) encBool := by
      have hk_bin : ComputableInPolyTime (fun q : ℕ × ℕ ↦ q.1)
          (encPair encUnary encUnary) encNat := unary_to_binary.comp (fst _ _)
      have hrhs_bin : ComputableInPolyTime (fun q : ℕ × ℕ ↦ 8 * q.2 * 2 ^ (16 * q.2))
          (encPair encUnary encUnary) encNat :=
        binary_mul' (unary_to_binary.comp (by fun_prop :
            ComputableInPolyTime (fun q : ℕ × ℕ ↦ 8 * q.2) _ encUnary))
          (binary_two_pow.comp (by fun_prop :
            ComputableInPolyTime (fun q : ℕ × ℕ ↦ 16 * q.2) _ encUnary))
      exact binary_le.comp (hk_bin.prod hrhs_bin)
    exact bool_and.comp (h1.prod h2)
  have hfind : ComputableInPolyTime
      (fun k : ℕ ↦ ((List.range (Nat.log 2 k + 2)).find?
        fun s ↦ decide (1 ≤ s ∧ k ≤ 8 * s * 2 ^ (16 * s))).getD (Nat.log 2 k + 1))
      encUnary encUnary := by
    have hfilt := filterWithInput
      (test := fun k s ↦ decide (1 ≤ s ∧ k ≤ 8 * s * 2 ^ (16 * s)))
      (unary_range' hlog) hpred
    have hfind_head : ∀ (l : List ℕ) (p : ℕ → Bool) (d : ℕ),
        (l.find? p).getD d = (l.filter p).headD d := by
      intro l p d
      induction l with
      | nil => rfl
      | cons a l ih =>
        simp only [List.find?_cons, List.filter_cons]
        cases p a
        · exact ih
        · rfl
    have hdef : ComputableInPolyTime (fun k : ℕ ↦ Nat.log 2 k + 1) encUnary encUnary :=
      unary_add' (binary_log_two.comp unary_to_binary) (const 1)
    exact (listHeadDWithInput hfilt hdef).of_enc_eq fun k ↦ by
      rw [← hfind_head]
  exact hfind.of_enc_eq fun k ↦ by rw [justesenScale_eq]

/-- `paddedJustesenRowEval` is uniformly polynomial-time on unary `(k, v)`. -/
theorem computableInPolyTime_paddedJustesenRowEval :
    Turing.MultiTapeTM.ComputableInPolyTime
      (fun p : ℕ × ℕ ↦
        let w := 16 * justesenScale p.1
        paddedJustesenRowEval (Cslib.BinaryField.fieldTable w) p.1 w (justesenLen p.1) p.2)
      (Turing.MultiTapeTM.encPair Turing.MultiTapeTM.encUnary Turing.MultiTapeTM.encUnary)
      Turing.MultiTapeTM.encBits := by
  open Turing.MultiTapeTM ComputableInPolyTime in
  let enc := encPair encUnary encUnary
  have hs : ComputableInPolyTime (fun p : ℕ × ℕ ↦ justesenScale p.1) enc encUnary :=
    computableInPolyTime_justesenScale.comp (fst encUnary encUnary)
  have hw : ComputableInPolyTime (fun p : ℕ × ℕ ↦ 16 * justesenScale p.1) enc encUnary := by
    fun_prop
  have hpow_w : ComputableInPolyTime (fun p : ℕ × ℕ ↦ 2 ^ (16 * justesenScale p.1)) enc encUnary :=
    binary_to_unary_bounded (binary_two_pow.comp hw)
      (bound := fun p ↦ 2 ^ 16 * (p.1 + 1)) (by fun_prop) fun p ↦ by
        have h := two_pow_sixteen_justesenScale_le p.1
        have : max 1 p.1 ≤ p.1 + 1 := max_le (by omega) (by omega)
        exact h.trans (Nat.mul_le_mul_left _ this)
  have hpow_w1 : ComputableInPolyTime
      (fun p : ℕ × ℕ ↦ 2 ^ (16 * justesenScale p.1 + 1)) enc encUnary := by
    have : ∀ p : ℕ × ℕ, 2 ^ (16 * justesenScale p.1 + 1) = 2 * 2 ^ (16 * justesenScale p.1) :=
      fun p ↦ by rw [pow_succ, mul_comm]
    simp_rw [this]; fun_prop
  have hN0 : ComputableInPolyTime (fun p : ℕ × ℕ ↦ justesenLen p.1) enc encUnary := by
    simp_rw [justesenLen_eq]; fun_prop
  have htab : ComputableInPolyTime
      (fun p : ℕ × ℕ ↦ Cslib.BinaryField.fieldTable (16 * justesenScale p.1)) enc
      Cslib.BinaryField.encTable := by
    have hmod := Cslib.BinaryField.computableInPolyTime_bits_unary.comp
      (Cslib.BinaryField.computableInPolyTime_leastIrreducibleCode.comp (hpow_w1.prod hw))
    simpa only [Cslib.BinaryField.fieldTable, Cslib.BinaryField.modulusBits, Function.comp_def]
      using Cslib.BinaryField.computableInPolyTime_powerMulTable.comp hmod
  unfold paddedJustesenRowEval
  have hbitsOfNat : ComputableInPolyTime
      (fun q : ℕ × ℕ ↦ bitsOfNat q.1 q.2) (encPair encUnary encNat) encBits := by
    simp_rw [bitsOfNat_eq]
    refine mapToBitsWithInput (unary_range' (fst _ _)) ?_
    exact binary_testBit ((snd encUnary encNat).comp (fst _ _)) (snd _ _)
  have hbranch : ComputableInPolyTime
      (fun p : ℕ × ℕ ↦
        let w := 16 * justesenScale p.1
        (List.range p.1).map fun r ↦
          let j := r / w
          let d := r % w
          let uPow := Cslib.BitString.powerWord (Cslib.BinaryField.fieldTable w)
            (bitsOfNat w (p.2 / (2 * w) + 1)) (j + (p.2 % (2 * w)) / w)
          let prod := Cslib.BinaryField.fieldMul (Cslib.BinaryField.fieldTable w) uPow
            (List.replicate d false ++ [true])
          prod.getD ((p.2 % (2 * w)) % w) false) enc encBits := by
    refine mapToBitsWithInput (unary_range' (fst _ _)) ?_
    have htab' := htab.comp (fst enc encUnary)
    have hw' := hw.comp (fst enc encUnary)
    have hv' := (snd encUnary encUnary).comp (fst enc encUnary)
    have hr' := snd enc encUnary
    have hw2' : ComputableInPolyTime
        (fun q : (ℕ × ℕ) × ℕ ↦ 2 * (16 * justesenScale q.1.1))
        (encPair enc encUnary) encUnary := unary_mul' (const 2) hw'
    have hrem' : ComputableInPolyTime
        (fun q : (ℕ × ℕ) × ℕ ↦ q.1.2 % (2 * (16 * justesenScale q.1.1)))
        (encPair enc encUnary) encUnary := unary_mod' hv' hw2'
    have huBits : ComputableInPolyTime
        (fun q : (ℕ × ℕ) × ℕ ↦ bitsOfNat (16 * justesenScale q.1.1)
          (q.1.2 / (2 * (16 * justesenScale q.1.1)) + 1))
        (encPair enc encUnary) encBits :=
      hbitsOfNat.comp (hw'.prod (unary_to_binary.comp (unary_add' (unary_div' hv' hw2') (const 1))))
    have hexp : ComputableInPolyTime
        (fun q : (ℕ × ℕ) × ℕ ↦ q.2 / (16 * justesenScale q.1.1) +
          (q.1.2 % (2 * (16 * justesenScale q.1.1))) / (16 * justesenScale q.1.1))
        (encPair enc encUnary) encUnary :=
      unary_add' (unary_div' hr' hw') (unary_div' hrem' hw')
    have hpowWord : ComputableInPolyTime
        (fun q : (ℕ × ℕ) × ℕ ↦
          Cslib.BitString.powerWord (Cslib.BinaryField.fieldTable (16 * justesenScale q.1.1))
            (bitsOfNat (16 * justesenScale q.1.1)
              (q.1.2 / (2 * (16 * justesenScale q.1.1)) + 1))
            (q.2 / (16 * justesenScale q.1.1) +
              (q.1.2 % (2 * (16 * justesenScale q.1.1))) / (16 * justesenScale q.1.1)))
        (encPair enc encUnary) encBits := by
      unfold Cslib.BitString.powerWord
      refine iterateWithInput_of_bounded_growth hexp (const [true]) ?_
        ⟨((length_list (encList encBits)).comp htab').polyBounded, fun a z ↦ by
          simp [Cslib.BinaryField.length_fieldMul]⟩
      exact Cslib.BinaryField.computableInPolyTime_fieldMul' (htab'.comp (fst _ _))
        (snd _ _) (huBits.comp (fst _ _))
    have hbasis : ComputableInPolyTime
        (fun q : (ℕ × ℕ) × ℕ ↦
          List.replicate (q.2 % (16 * justesenScale q.1.1)) false ++ [true])
        (encPair enc encUnary) encBits :=
      bitsAppend ((bitsReplicate false).comp (unary_mod' hr' hw')) (const [true])
    have hprod := Cslib.BinaryField.computableInPolyTime_fieldMul' htab' hpowWord hbasis
    have hbit : ComputableInPolyTime
        (fun q : (ℕ × ℕ) × ℕ ↦
          (q.1.2 % (2 * (16 * justesenScale q.1.1))) % (16 * justesenScale q.1.1))
        (encPair enc encUnary) encUnary := unary_mod' hrem' hw'
    exact bitsGetDWithInput hprod hbit false
  have hcond : ComputableInPolyTime (fun p : ℕ × ℕ ↦ decide (p.2 < justesenLen p.1))
      enc encBool := unary_lt.comp ((snd encUnary encUnary).prod hN0)
  have helse : ComputableInPolyTime (fun p : ℕ × ℕ ↦ List.replicate p.1 false) enc encBits :=
    (bitsReplicate false).comp (fst encUnary encUnary)
  exact hcond.ite_decide hbranch helse

private lemma computableInPolyTime_iterate_const {α : Type} {enc : α ↪ List Bool}
    {f : α → α} (hf : Turing.MultiTapeTM.ComputableInPolyTime f enc enc) (steps : ℕ) :
    Turing.MultiTapeTM.ComputableInPolyTime (f^[steps]) enc enc := by
  induction steps with
  | zero => exact Turing.MultiTapeTM.ComputableInPolyTime.id'
  | succ s ih =>
    rw [Function.iterate_succ]
    exact ih.comp hf

private noncomputable def abnnrStep (k i : ℕ) (st : ℕ × ℕ × List Bool) : ℕ × ℕ × List Bool :=
  let N := paddedJustesenLen k
  let D := abnnrBaseDegree
  let walkCode := i / N
  let labelEquiv := Fintype.equivFin (Cslib.RotationMap.AffinePlaneFamilyLabel (ZMod 257) 257)
  let hdeg : Fintype.card (Cslib.RotationMap.AffinePlaneFamilyLabel (ZMod 257) 257) = D :=
    (Cslib.RotationMap.card_affinePlaneFamilyLabel
      (ZMod.finEquiv 257).toEquiv.symm).trans abnnrBaseDegree_eq.symm
  let stepLabel :=
    labelEquiv.symm ⟨(walkCode / D ^ st.1) % D,
      by rw [hdeg]; exact Nat.mod_lt _ abnnrBaseDegree_pos⟩
  let w := 16 * justesenScale k
  let tab := Cslib.BinaryField.fieldTable w
  let N₀ := justesenLen k
  let vNext := (Cslib.RotationMap.arithmeticExpanderRotate (N, st.2.1, stepLabel)).1
  let accNext :=
    if (st.1 + 1) % (2 * abnnrExpanderPow) = abnnrExpanderPow then
      st.2.2.zipWith xor (paddedJustesenRowEval tab k w N₀ vNext)
    else st.2.2
  (st.1 + 1, vNext, accNext)

/-- Executable ABNNR92 row evaluator for fixed walk parameter `t`, taking unary `(k, i)` and
returning the `i`-th row (length `k` bit list) of `abnnrGenMap k t`. -/
noncomputable def abnnrRowEval (t k i : ℕ) : List Bool :=
  ((abnnrStep k i)^[2 * abnnrExpanderPow * t]
    (0, i % paddedJustesenLen k, List.replicate k false)).2.2

@[simp]
theorem length_abnnrRowEval (t k i : ℕ) : (abnnrRowEval t k i).length = k := by
  unfold abnnrRowEval
  have hinv : ∀ (s : ℕ) (st : ℕ × ℕ × List Bool), st.2.2.length = k →
      ((abnnrStep k i)^[s] st).2.2.length = k := by
    intro s
    induction s with
    | zero => intro st h; exact h
    | succ s ih =>
      intro st h
      rw [Function.iterate_succ_apply]
      refine ih _ ?_
      unfold abnnrStep
      dsimp only
      split_ifs
      · rw [List.length_zipWith, h, length_paddedJustesenRowEval, min_self]
      · exact h
  exact hinv _ (0, i % paddedJustesenLen k, List.replicate k false) List.length_replicate

private lemma walkAt_pow_eq {V D : Type*} (G : Cslib.RotationMap V D) {P T : ℕ}
    (v0 : V) (lbl : Fin T → Fin P → D) :
    ∀ s ≤ T,
      (G.pow P).walkAt (v0, lbl) s =
        G.walkAt (v0, fun l : Fin (T * P) ↦ lbl ⟨l.val / P, Nat.div_lt_of_lt_mul (by
          simpa only [mul_comm] using l.isLt)⟩ ⟨l.val % P, Nat.mod_lt _ (by
            by_contra h0; have hP : P = 0 := by omega
            have hlt : l.val < 0 := by simpa [hP] using l.isLt
            omega)⟩) (s * P) := by
  intro s hs
  induction s with
  | zero => simp
  | succ s ih =>
    have hs_lt : s < T := by omega
    rw [Cslib.RotationMap.walkAt_succ_of_lt _ _ hs_lt, ih hs_lt.le]
    rcases Nat.eq_zero_or_pos P with rfl | hP_pos
    · simp [Cslib.RotationMap.neighbor, Cslib.RotationMap.pow, Cslib.RotationMap.powRot]
    · -- Direct induction on `m ≤ P` proving `walkAt` advances `m` steps matching `powRot`:
      have hstep_pow : ∀ (m : ℕ) (hm : m ≤ P) (v : V) (f : Fin m → D) (off : ℕ)
          (hoff : off + m ≤ T * P)
          (hv : v = G.walkAt (v0, fun l : Fin (T * P) ↦ lbl ⟨l.val / P, Nat.div_lt_of_lt_mul (by
            simpa only [mul_comm] using l.isLt)⟩ ⟨l.val % P, Nat.mod_lt _ hP_pos⟩) off)
          (hagree : ∀ r : Fin m, f r = lbl ⟨(off + r.val) / P, Nat.div_lt_of_lt_mul (by
            rw [mul_comm]; omega)⟩ ⟨(off + r.val) % P, Nat.mod_lt _ hP_pos⟩),
          (Cslib.RotationMap.powRot G.rot m (v, f)).1 =
            G.walkAt (v0, fun l : Fin (T * P) ↦ lbl ⟨l.val / P, Nat.div_lt_of_lt_mul (by
              simpa only [mul_comm] using l.isLt)⟩ ⟨l.val % P, Nat.mod_lt _ hP_pos⟩) (off + m) := by
        intro m
        induction m with
        | zero =>
          intro _ v _ off _ hv _
          simpa [Cslib.RotationMap.powRot] using hv
        | succ m ihm =>
          intro hm v f off hoff hv hagree
          rw [Cslib.RotationMap.powRot_succ]
          have hstep0 : (G.rot (v, f 0)).1 =
              G.walkAt (v0, fun l : Fin (T * P) ↦ lbl ⟨l.val / P, Nat.div_lt_of_lt_mul (by
                simpa only [mul_comm] using l.isLt)⟩ ⟨l.val % P, Nat.mod_lt _ hP_pos⟩)
                (off + 1) := by
            rw [Cslib.RotationMap.walkAt_succ_of_lt _ _ (by omega : off < T * P), ← hv]
            have h0 := hagree 0
            simp only [Fin.val_zero, add_zero] at h0
            rw [h0]; rfl
          have hrec := ihm (by omega) ((G.rot (v, f 0)).1) (Fin.tail f) (off + 1) (by omega) hstep0
            (fun r ↦ by
              have hr := hagree r.succ
              simpa [Fin.tail, Nat.add_assoc, Nat.add_comm 1 r.val] using hr)
          simpa [Nat.add_assoc, Nat.add_comm 1 m] using hrec
      have h := hstep_pow P le_rfl _ (lbl ⟨s, hs_lt⟩) (s * P) (by nlinarith) rfl (fun r ↦ by
        have hdiv : (s * P + r.val) / P = s := by
          rw [Nat.add_comm, Nat.add_mul_div_right _ _ hP_pos, Nat.div_eq_of_lt r.isLt, zero_add]
        have hmod : (s * P + r.val) % P = r.val := by
          rw [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt r.isLt]
        simp [hdiv, hmod])
      simpa [Cslib.RotationMap.neighbor, Cslib.RotationMap.pow, Nat.succ_mul] using h

/-- `abnnrRowEval` agrees bit-for-bit with `abnnrGenMap k t` on all standard basis vectors
`Pi.single r 1`. -/
theorem abnnrRowEval_eq (t k : ℕ) (i : Fin (abnnrLen k t)) (r : Fin k) :
    (abnnrRowEval t k i.val).getD r.val false =
      Cslib.BitString.bitEquiv (abnnrGenMap k t (Pi.single r 1) i) := by
  set N := paddedJustesenLen k
  set P := abnnrExpanderPow
  set D := abnnrBaseDegree
  set L := 2 * P * t
  set Gbase := Cslib.RotationMap.arithmeticExpander N
  set lblEquiv := Fintype.equivFin (Cslib.RotationMap.AffinePlaneFamilyLabel (ZMod 257) 257)
  have hdeg : Fintype.card (Cslib.RotationMap.AffinePlaneFamilyLabel (ZMod 257) 257) = D :=
    (Cslib.RotationMap.card_affinePlaneFamilyLabel
      (ZMod.finEquiv 257).toEquiv.symm).trans abnnrBaseDegree_eq.symm
  have hD_pos : 0 < D := abnnrBaseDegree_pos
  have hP_pos : 0 < P := abnnrExpanderPow_pos
  set p := abnnrWalkEquiv k t i
  have hp1 : p.1.val = i.val % N := abnnrWalkEquiv_fst k t i
  have hp2 : ∀ (j : Fin (2 * t)) (s : Fin P),
      p.2 j s = lblEquiv.symm ⟨((i.val / N) / D ^ (j.val * P + s.val)) % D,
        by rw [hdeg]; exact Nat.mod_lt _ hD_pos⟩ :=
    fun j s ↦ abnnrWalkEquiv_snd k t i j s
  let stepLabel (l : ℕ) :=
    lblEquiv.symm ⟨((i.val / N) / D ^ l) % D, by rw [hdeg]; exact Nat.mod_lt _ hD_pos⟩
  let flatLbl : Fin (2 * t * P) → Cslib.RotationMap.AffinePlaneFamilyLabel (ZMod 257) 257 :=
    fun l ↦ p.2 ⟨l.val / P, Nat.div_lt_of_lt_mul (by simpa only [mul_comm] using l.isLt)⟩
      ⟨l.val % P, Nat.mod_lt _ hP_pos⟩
  have hflat : ∀ (l : Fin (2 * t * P)), flatLbl l = stepLabel l.val := by
    intro l
    dsimp only [flatLbl, stepLabel]
    rw [hp2]
    have hmul : l.val / P * P + l.val % P = l.val := by
      rw [mul_comm]; exact Nat.div_add_mod l.val P
    simp only [hmul]
  let w := 16 * justesenScale k
  let tab := Cslib.BinaryField.fieldTable w
  let N₀ := justesenLen k
  let stepFn (st : ℕ × ℕ × List Bool) : ℕ × ℕ × List Bool :=
    let l := st.1
    let v := st.2.1
    let acc := st.2.2
    let vNext := (Cslib.RotationMap.arithmeticExpanderRotate (N, v, stepLabel l)).1
    let accNext :=
      if (l + 1) % (2 * P) = P then
        acc.zipWith xor (paddedJustesenRowEval tab k w N₀ vNext)
      else acc
    (l + 1, vNext, accNext)
  -- Track loop invariant through `s ≤ L`:
  have hinv : ∀ s ≤ L,
      let st := stepFn^[s] (0, i.val % N, List.replicate k false)
      st.1 = s ∧
      st.2.1 = (Gbase.walkAt (p.1, flatLbl) s).val ∧
      st.2.2.length = k ∧
      st.2.2.getD r.val false =
        Cslib.BitString.bitEquiv
          (∑ j ∈ Finset.univ.filter (fun j : Fin t ↦ (2 * j.val + 1) * P ≤ s),
            paddedJustesenMap k (Pi.single r 1) (Gbase.walkAt (p.1, flatLbl) ((2 * j.val +
              1) * P))) := by
    intro s hs
    induction s with
    | zero =>
      refine ⟨rfl, ?_, List.length_replicate, ?_⟩
      · simp [Cslib.RotationMap.walkAt_zero, hp1]
      · have hfilt : (Finset.univ.filter fun j : Fin t ↦ (2 * j.val + 1) * P ≤ 0) = ∅ := by
          ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
            iff_false, not_le]
          exact Nat.mul_pos (by omega) hP_pos
        dsimp only [Function.iterate_zero, id_eq]
        rw [hfilt, Finset.sum_empty, map_zero, List.getD_eq_getElem?_getD,
          List.getElem?_replicate]
        simp [r.isLt]
        rfl
    | succ s ih =>
      obtain ⟨h1, h2, hlen, hacc⟩ := ih (by omega)
      rw [Function.iterate_succ_apply']
      set st := stepFn^[s] (0, i.val % N, List.replicate k false)
      have hs_lt : s < 2 * t * P := by
        have hcomm_L : 2 * P * t = 2 * t * P := by ring
        dsimp only [L] at hs; omega
      have hv_eq : (Cslib.RotationMap.arithmeticExpanderRotate (N, st.2.1, stepLabel st.1)).1 =
          (Gbase.walkAt (p.1, flatLbl) (s + 1)).val := by
        rw [h1, h2, ← hflat ⟨s, hs_lt⟩,
          Cslib.RotationMap.arithmeticExpanderRotate_eq N (Gbase.walkAt (p.1, flatLbl) s)
            (flatLbl ⟨s, hs_lt⟩),
          Cslib.RotationMap.walkAt_succ_of_lt _ _ hs_lt]
        rfl
      refine ⟨by dsimp [stepFn]; omega, hv_eq, ?_, ?_⟩
      · dsimp [stepFn]
        split_ifs
        · rw [List.length_zipWith, hlen, length_paddedJustesenRowEval, min_self]
        · exact hlen
      · dsimp only [stepFn]
        rw [h1]
        split_ifs with hmod
        · -- Case `(s + 1) % (2 * P) = P`: so `s + 1 = (2 * j₀ + 1) * P` for a unique `j₀ : Fin t`.
          have hj0_lt : (s + 1) / (2 * P) < t := by
            have hle_L : s + 1 ≤ 2 * P * t := hs
            exact Nat.div_lt_of_lt_mul (by
              have hne : s + 1 ≠ 2 * P * t := by
                intro heq
                have h0 : (2 * P * t) % (2 * P) = 0 := by
                  rw [mul_comm]; exact Nat.mul_mod_left _ _
                rw [heq, h0] at hmod
                omega
              omega)
          let j₀ : Fin t := ⟨(s + 1) / (2 * P), hj0_lt⟩
          have hj0_eq : (2 * j₀.val + 1) * P = s + 1 := by
            have hdivmod := Nat.div_add_mod (s + 1) (2 * P)
            dsimp [j₀]
            linarith
          have hfilt_eq :
              (Finset.univ.filter fun j : Fin t ↦ (2 * j.val + 1) * P ≤ s + 1) =
                insert j₀ (Finset.univ.filter fun j : Fin t ↦ (2 * j.val + 1) * P ≤ s) := by
            ext j
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
            constructor
            · intro hle
              by_cases heq : (2 * j.val + 1) * P = s + 1
              · left; apply Fin.ext
                have : 2 * j.val + 1 = 2 * j₀.val + 1 :=
                  Nat.eq_of_mul_eq_mul_right hP_pos (heq.trans hj0_eq.symm)
                omega
              · right; omega
            · rintro (rfl | hle)
              · exact le_of_eq hj0_eq
              · omega
          have hj0_notmem : j₀ ∉ Finset.univ.filter (fun j : Fin t ↦ (2 * j.val + 1) * P ≤ s) := by
            simp [hj0_eq]
          rw [hfilt_eq, Finset.sum_insert hj0_notmem, hj0_eq]
          -- Show `bitEquiv (a + b) = xor (bitEquiv a) (bitEquiv b)` and `getD` of `zipWith xor`:
          have hget_zip :
              (st.2.2.zipWith xor (paddedJustesenRowEval tab k w N₀
                (Cslib.RotationMap.arithmeticExpanderRotate (N, st.2.1, stepLabel s)).1)).getD
                  r.val false =
                xor (st.2.2.getD r.val false)
                  ((paddedJustesenRowEval tab k w N₀
                    (Cslib.RotationMap.arithmeticExpanderRotate (N, st.2.1, stepLabel s)).1).getD
                      r.val false) := by
            have hlt1 : r.val < st.2.2.length := by rw [hlen]; exact r.isLt
            have hlt2 : r.val < (paddedJustesenRowEval tab k w N₀
                (Cslib.RotationMap.arithmeticExpanderRotate (N, st.2.1,
                  stepLabel s)).1).length := by
              rw [length_paddedJustesenRowEval]; exact r.isLt
            rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
              List.getElem?_zipWith, List.getElem?_eq_getElem hlt1, List.getElem?_eq_getElem hlt2]
            rfl
          have hv_eq_s :
              (Cslib.RotationMap.arithmeticExpanderRotate (N, st.2.1, stepLabel s)).1 =
                (Gbase.walkAt (p.1, flatLbl) (s + 1)).val := by
            have htmp := hv_eq
            rw [h1] at htmp
            exact htmp
          rw [hget_zip, hacc, hv_eq_s, paddedJustesenRowEval_eq k
            (Gbase.walkAt (p.1, flatLbl) (s + 1)) r]
          -- `xor (bitEquiv x) (bitEquiv y) = bitEquiv (y + x)` on `ZMod 2`:
          have hxor : ∀ a b : ZMod 2,
              xor (Cslib.BitString.bitEquiv a) (Cslib.BitString.bitEquiv b) =
                Cslib.BitString.bitEquiv (b + a) := by decide
          exact hxor _ _
        · -- Case `(s + 1) % (2 * P) ≠ P`: no new `j` reaches `(2 * j + 1) * P = s + 1`.
          have hfilt_eq :
              (Finset.univ.filter fun j : Fin t ↦ (2 * j.val + 1) * P ≤ s + 1) =
                (Finset.univ.filter fun j : Fin t ↦ (2 * j.val + 1) * P ≤ s) := by
            ext j
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            constructor
            · intro hle
              by_contra hgt
              have heq : (2 * j.val + 1) * P = s + 1 := by omega
              have hrem : ((2 * j.val + 1) * P) % (2 * P) = P := by
                rw [add_mul, one_mul, show 2 * j.val * P = j.val * (2 * P) by ring,
                  Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt (by omega : P < 2 * P)]
              exact hmod (heq ▸ hrem)
            · intro hle; omega
          rw [hfilt_eq, hacc]
  have hL := (hinv L le_rfl).2.2.2
  have hall : (Finset.univ.filter fun j : Fin t ↦ (2 * j.val + 1) * P ≤ L) = Finset.univ := by
    ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    have : 2 * j.val + 1 ≤ 2 * t := by omega
    calc (2 * j.val + 1) * P ≤ (2 * t) * P := Nat.mul_le_mul_right P this
      _ = L := by dsimp [L]; ring
  rw [hall] at hL
  have hsum_eq :
      (∑ j : Fin t, paddedJustesenMap k (Pi.single r 1)
          (Gbase.walkAt (p.1, flatLbl) ((2 * j.val + 1) * P))) =
        abnnrGenMap k t (Pi.single r 1) i := by
    rw [abnnrGenMap_apply]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    exact congrArg (paddedJustesenMap k (Pi.single r 1))
      (walkAt_pow_eq Gbase p.1 p.2 (2 * j.val + 1) (by omega)).symm
  rw [← hsum_eq]
  exact hL

/-- `paddedJustesenLen` is uniformly polynomial-time on unary input. -/
theorem computableInPolyTime_paddedJustesenLen :
    Turing.MultiTapeTM.ComputableInPolyTime paddedJustesenLen
      Turing.MultiTapeTM.encUnary Turing.MultiTapeTM.encUnary := by
  open Turing.MultiTapeTM ComputableInPolyTime in
  have hs0 := computableInPolyTime_justesenScale
  have hpow_w : ComputableInPolyTime (fun k : ℕ ↦ 2 ^ (16 * justesenScale k))
      encUnary encUnary :=
    binary_to_unary_bounded (binary_two_pow.comp (by fun_prop))
      (bound := fun k ↦ 2 ^ 16 * (k + 1)) (by fun_prop) fun k ↦
        (two_pow_sixteen_justesenScale_le k).trans
          (Nat.mul_le_mul_left _ (max_le (by omega) (by omega)))
  have hN0 : ComputableInPolyTime justesenLen encUnary encUnary := by
    simp_rw [show justesenLen = _ from funext justesenLen_eq]
    fun_prop
  simp_rw [show paddedJustesenLen = _ from funext paddedJustesenLen_eq]
  fun_prop

/-- For any fixed walk parameter `t`, `abnnrRowEval t` is uniformly polynomial-time on unary
`(k, i)`. -/
theorem computableInPolyTime_abnnrRowEval (t : ℕ) :
    Turing.MultiTapeTM.ComputableInPolyTime
      (fun p : ℕ × ℕ ↦ abnnrRowEval t p.1 p.2)
      (Turing.MultiTapeTM.encPair Turing.MultiTapeTM.encUnary Turing.MultiTapeTM.encUnary)
      Turing.MultiTapeTM.encBits := by
  open Turing.MultiTapeTM ComputableInPolyTime in
  let enc := encPair encUnary encUnary
  let lblEnc : Cslib.RotationMap.AffinePlaneFamilyLabel (ZMod 257) 257 ↪ List Bool :=
    encFinite _
  let stEnc := encPair encUnary (encPair encUnary encBits)
  let fullEnc := encPair enc stEnc
  have hrot := Cslib.RotationMap.polytime_arithmeticExpanderRotate lblEnc
  have hN : ComputableInPolyTime (fun p : ℕ × ℕ ↦ paddedJustesenLen p.1) enc encUnary :=
    computableInPolyTime_paddedJustesenLen.comp (fst encUnary encUnary)
  let stepQ : (ℕ × ℕ) × (ℕ × ℕ × List Bool) → (ℕ × ℕ) × (ℕ × ℕ × List Bool) :=
    fun q ↦
      let p := q.1; let st := q.2
      let N := paddedJustesenLen p.1
      let D := abnnrBaseDegree
      let walkCode := p.2 / N
      let labelEquiv := Fintype.equivFin
        (Cslib.RotationMap.AffinePlaneFamilyLabel (ZMod 257) 257)
      let hdeg : Fintype.card (Cslib.RotationMap.AffinePlaneFamilyLabel (ZMod 257) 257) = D :=
        (Cslib.RotationMap.card_affinePlaneFamilyLabel
          (ZMod.finEquiv 257).toEquiv.symm).trans abnnrBaseDegree_eq.symm
      let stepLabel := labelEquiv.symm ⟨(walkCode / D ^ st.1) % D,
        by rw [hdeg]; exact Nat.mod_lt _ abnnrBaseDegree_pos⟩
      let vNext := (Cslib.RotationMap.arithmeticExpanderRotate (N, st.2.1, stepLabel)).1
      let w := 16 * justesenScale p.1
      let accNext :=
        if (st.1 + 1) % (2 * abnnrExpanderPow) = abnnrExpanderPow then
          st.2.2.zipWith xor (paddedJustesenRowEval (Cslib.BinaryField.fieldTable w)
            p.1 w (justesenLen p.1) vNext)
        else st.2.2
      (p, (st.1 + 1, vNext, accNext))
  have hstep : ComputableInPolyTime (fun q : (ℕ × ℕ) × (ℕ × ℕ × List Bool) ↦
      (q.1, abnnrStep q.1.1 q.1.2 q.2)) fullEnc fullEnc := by
    change ComputableInPolyTime stepQ fullEnc fullEnc
    have hp := fst enc stEnc
    have hst := snd enc stEnc
    have hNp := hN.comp hp
    have hl := hst.fst'
    have hv := hst.snd'.fst'
    have hacc := hst.snd'.snd'
    have hwalkCode : ComputableInPolyTime (fun q : (ℕ × ℕ) × (ℕ × ℕ × List Bool) ↦
        q.1.2 / paddedJustesenLen q.1.1) fullEnc encUnary :=
      unary_div' (hp.snd') hNp
    have hDpow : ComputableInPolyTime
        (fun q : (ℕ × ℕ) × (ℕ × ℕ × List Bool) ↦ abnnrBaseDegree ^ q.2.1) fullEnc encNat :=
      binary_pow' (const abnnrBaseDegree) hl
    have hstepIdx : ComputableInPolyTime
        (fun q : (ℕ × ℕ) × (ℕ × ℕ × List Bool) ↦
          ((q.1.2 / paddedJustesenLen q.1.1) / abnnrBaseDegree ^ q.2.1) % abnnrBaseDegree)
        fullEnc encUnary :=
      binary_to_unary_bounded
        (binary_mod' (binary_div' (unary_to_binary.comp hwalkCode) hDpow) (const abnnrBaseDegree))
        (bound := fun _ ↦ abnnrBaseDegree) (const abnnrBaseDegree) fun _ ↦
          (Nat.mod_lt _ abnnrBaseDegree_pos).le
    have hlbl : ComputableInPolyTime
        (fun q : (ℕ × ℕ) × (ℕ × ℕ × List Bool) ↦
          (Fintype.equivFin (Cslib.RotationMap.AffinePlaneFamilyLabel (ZMod 257) 257)).symm
            ⟨((q.1.2 / paddedJustesenLen q.1.1) / abnnrBaseDegree ^ q.2.1) % abnnrBaseDegree, by
              rw [Cslib.RotationMap.card_affinePlaneFamilyLabel (ZMod.finEquiv 257).toEquiv.symm,
                ← abnnrBaseDegree_eq]
              exact Nat.mod_lt _ abnnrBaseDegree_pos⟩)
        fullEnc lblEnc := by
      have hfin : ComputableInPolyTime
          (fun n : ℕ ↦
            (Fintype.equivFin (Cslib.RotationMap.AffinePlaneFamilyLabel (ZMod 257) 257)).symm
              ⟨n % abnnrBaseDegree, by
                rw [Cslib.RotationMap.card_affinePlaneFamilyLabel (ZMod.finEquiv 257).toEquiv.symm,
                  ← abnnrBaseDegree_eq]
                exact Nat.mod_lt _ abnnrBaseDegree_pos⟩)
          encUnary lblEnc :=
        (of_finite (encIn := encFinEnum (Fin abnnrBaseDegree)) (encOut := lblEnc)
          (fun m : Fin abnnrBaseDegree ↦
            (Fintype.equivFin (Cslib.RotationMap.AffinePlaneFamilyLabel (ZMod 257) 257)).symm
              ⟨m.val, by
                rw [Cslib.RotationMap.card_affinePlaneFamilyLabel (ZMod.finEquiv 257).toEquiv.symm,
                  ← abnnrBaseDegree_eq]
                exact m.isLt⟩)).comp
          (unary_finMod abnnrBaseDegree_pos (encFinEnum (Fin abnnrBaseDegree)))
      have heq_m : ∀ q : (ℕ × ℕ) × (ℕ × ℕ × List Bool),
          (((q.1.2 / paddedJustesenLen q.1.1) / abnnrBaseDegree ^ q.2.1) % abnnrBaseDegree) %
            abnnrBaseDegree =
          ((q.1.2 / paddedJustesenLen q.1.1) / abnnrBaseDegree ^ q.2.1) % abnnrBaseDegree :=
        fun _ ↦ Nat.mod_mod _ _
      simpa only [Function.comp_def, heq_m] using hfin.comp hstepIdx
    have hvNext := (hrot.comp (hNp.prod (hv.prod hlbl))).fst'
    have hrow := computableInPolyTime_paddedJustesenRowEval.comp (hp.fst'.prod hvNext)
    have hxor := bitsZipWithInput xor hacc hrow
    have hcond : ComputableInPolyTime
        (fun q : (ℕ × ℕ) × (ℕ × ℕ × List Bool) ↦
          decide ((q.2.1 + 1) % (2 * abnnrExpanderPow) = abnnrExpanderPow)) fullEnc encBool :=
      unary_eq' (unary_mod' (unary_add' hl (const 1)) (const (2 * abnnrExpanderPow)))
        (const abnnrExpanderPow)
    have haccNext := hcond.ite_decide hxor hacc
    exact hp.prod ((unary_add' hl (const 1)).prod (hvNext.prod haccNext))
  have hiter := computableInPolyTime_iterate_const hstep (2 * abnnrExpanderPow * t)
  have hinit : ComputableInPolyTime
      (fun p : ℕ × ℕ ↦ (p, (0, p.2 % paddedJustesenLen p.1, List.replicate p.1 false)))
      enc fullEnc := by
    have hv0 := unary_mod' (snd encUnary encUnary) hN
    have hrep : ComputableInPolyTime (fun p : ℕ × ℕ ↦ List.replicate p.1 false) enc encBits :=
      (bitsReplicate false).comp (fst encUnary encUnary)
    exact id'.prod ((const 0).prod (hv0.prod hrep))
  have hproj := (snd encUnary encBits).comp ((snd encUnary _).comp ((snd enc stEnc).comp
    (hiter.comp hinit)))
  have hcomm : ∀ p : ℕ × ℕ,
      (((fun q : (ℕ × ℕ) × (ℕ × ℕ × List Bool) ↦
        (q.1, abnnrStep q.1.1 q.1.2 q.2))^[2 * abnnrExpanderPow * t]
        (p, (0, p.2 % paddedJustesenLen p.1, List.replicate p.1 false))).2).2.2 =
      abnnrRowEval t p.1 p.2 := by
    intro p
    unfold abnnrRowEval
    have hfst_step : ∀ (s : ℕ) (st : ℕ × ℕ × List Bool),
        ((fun q : (ℕ × ℕ) × (ℕ × ℕ × List Bool) ↦
          (q.1, abnnrStep q.1.1 q.1.2 q.2))^[s] (p, st)).2 =
          (abnnrStep p.1 p.2)^[s] st := by
      intro s
      induction s with
      | zero => intro st; rfl
      | succ s ih =>
        intro st
        rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
        exact ih _
    exact congrArg (fun x ↦ x.2.2) (hfst_step _ _)
  simpa only [Function.comp_def, hcomm] using hproj

/-- Evaluate the `n`-row punctured binary generator matrix (rows listed in `rows`) in
polynomial time for any fixed walk parameter `t`. -/
noncomputable def abnnrPuncturedMatrix (t k : ℕ) (rows : List ℕ) : List (List Bool) :=
  rows.map (abnnrRowEval t k)

theorem computableInPolyTime_abnnrPuncturedMatrix (t : ℕ) :
    Turing.MultiTapeTM.ComputableInPolyTime
      (fun p : ℕ × List ℕ ↦ abnnrPuncturedMatrix t p.1 p.2)
      (Turing.MultiTapeTM.encPair Turing.MultiTapeTM.encUnary
        (Turing.MultiTapeTM.encList Turing.MultiTapeTM.encUnary))
      (Turing.MultiTapeTM.encList Turing.MultiTapeTM.encBits) := by
  open Turing.MultiTapeTM ComputableInPolyTime in
  unfold abnnrPuncturedMatrix
  exact mapWithInput (snd encUnary (encList encUnary))
    ((computableInPolyTime_abnnrRowEval t).comp
      (((fst encUnary (encList encUnary)).comp (fst _ _)).prod (snd _ _)))

end ABNNRPolyTime

end CslibFrontier.Foundations.Data.Code
