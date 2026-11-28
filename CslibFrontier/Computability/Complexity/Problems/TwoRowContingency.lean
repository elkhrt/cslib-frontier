module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.SharpP
public import CslibFrontier.Computability.Complexity.Classes.SharpP.Completeness
public import CslibFrontier.Computability.Complexity.Problems.OneInThreeSAT
public import CslibFrontier.Computability.Complexity.Reduction.CountingTuring
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.Bits
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Pair
import CslibFrontier.Computability.Complexity.Classes.SharpP.Closure
import CslibFrontier.Computability.Complexity.Problems.OneInThreeSAT.Reduction
import CslibFrontier.Computability.Complexity.Problems.SAT.PolyTime
import CslibFrontier.Computability.Complexity.Problems.SharpThreeSAT
import CslibFrontier.Computability.Complexity.Problems.SubsetSum
import CslibFrontier.Computability.Complexity.Problems.SubsetSum.Digits
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Choose
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Foundations.Data.Nat.Bits
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# #P-Completeness of Counting Two-Row Contingency Tables

Proves that counting nonnegative integer `2 × m` contingency tables with prescribed row sums and
column sums (`TwoRowContingency`) is `#P`-complete under polynomial-time counting Turing
reductions, using only standard Lean axioms.

## Main definitions

* `Cslib.Complexity.encTwoRowContingency`: binary encoding of `(R, c) : ℕ × List ℕ`.
* `Cslib.Complexity.TwoRowContingency`: number of tuples `x : Fin c.length → ℕ` with
  `x i ≤ c[i]` and `∑ i, x i = R`.

## Main results

* `Cslib.Complexity.twoRowContingency_mem_SharpP`: `TwoRowContingency ∈ SharpP`.
* `Cslib.Complexity.countingTuringReducible_sharpOneInThree_twoRowContingency`:
  batch-oracle counting Turing reduction from `SharpPositiveOneInExactThreeSATThree` to
  `TwoRowContingency`.
* `Cslib.Complexity.twoRowContingency_countingTuringHard` and
  `Cslib.Complexity.twoRowContingency_countingTuringComplete`: `#P`-hardness and
  `#P`-completeness of `TwoRowContingency` under counting Turing reductions.
* `Cslib.Complexity.countingTuringReducible_sharpOneInThree_of_parsimonious`:
  composing the batch-oracle reduction with any parsimonious reduction `TwoRowContingency ≤_par g`.
-/

public section

namespace Cslib.Complexity

open Cslib.Logic.PL Finset Turing.MultiTapeTM ComputableInPolyTime

/-! ### Definition and basic combinatorial properties -/

/-- Binary encoding of a two-row contingency table instance `(R, c) : ℕ × List ℕ`. -/
@[expose]
def encTwoRowContingency : ℕ × List ℕ ↪ List Bool :=
  encPair encNat (encList encNat)

/-- Number of `2 × m` nonnegative integer contingency tables with first row sum `R` and column sums
`c = [c₀, …, c_{m-1}]` (the second row is uniquely determined as `cᵢ - xᵢ`, with sum `∑ cᵢ - R`).
-/
@[expose]
noncomputable def TwoRowContingency (p : ℕ × List ℕ) : ℕ :=
  Fintype.card {x : (i : Fin p.2.length) → Fin (p.2[i] + 1) // ∑ i, (x i : ℕ) = p.1}

/-- When `R = 0`, the all-zero first row is the unique two-row contingency table. -/
theorem twoRowContingency_zero (c : List ℕ) : TwoRowContingency (0, c) = 1 := by
  unfold TwoRowContingency
  refine Fintype.card_eq_one_iff.mpr ⟨⟨fun _ => ⟨0, Nat.succ_pos _⟩, by simp⟩, fun ⟨x, hx⟩ => ?_⟩
  refine Subtype.ext (funext fun i => Fin.ext ?_)
  have h0 : ∀ j ∈ (Finset.univ : Finset (Fin c.length)), (x j : ℕ) = 0 :=
    Finset.sum_eq_zero_iff.mp hx
  exact h0 i (Finset.mem_univ i)

/-- On an empty column list, there is `1` table if `R = 0` and `0` otherwise. -/
theorem twoRowContingency_nil (R : ℕ) :
    TwoRowContingency (R, []) = if R = 0 then 1 else 0 := by
  cases R with
  | zero => simpa using twoRowContingency_zero []
  | succ k =>
    simp only [Nat.succ_ne_zero, ↓reduceIte, TwoRowContingency]
    rw [Fintype.card_eq_zero_iff]
    exact ⟨fun ⟨_, hx⟩ => by simp at hx⟩

/-- Recursive decomposition along the first column of `c`. -/
theorem twoRowContingency_cons (R a : ℕ) (l : List ℕ) :
    TwoRowContingency (R, a :: l) =
      ∑ v : Fin (a + 1), if (v : ℕ) ≤ R then TwoRowContingency (R - v, l) else 0 := by
  unfold TwoRowContingency
  let e :
      {x : (i : Fin (a :: l).length) → Fin ((a :: l)[i] + 1) // ∑ i, (x i : ℕ) = R} ≃
        Σ v : Fin (a + 1),
          {y : (i : Fin l.length) → Fin (l[i] + 1) // (v : ℕ) + ∑ i, (y i : ℕ) = R} :=
    { toFun := fun ⟨x, hx⟩ =>
        ⟨x ⟨0, Nat.succ_pos _⟩,
          ⟨fun i => x i.succ, by simpa [Fin.sum_univ_succ] using hx⟩⟩
      invFun := fun ⟨v, ⟨y, hy⟩⟩ =>
        ⟨fun i => Fin.cases (motive := fun j : Fin (a :: l).length => Fin ((a :: l)[j] + 1)) v y i,
          by
            change (∑ i : Fin (l.length + 1),
              ((Fin.cases (motive := fun j : Fin (l.length + 1) => Fin ((a :: l)[j] + 1))
                v y i : Fin ((a :: l)[i] + 1)) : ℕ)) = R
            rw [Fin.sum_univ_succ]
            exact hy⟩
      left_inv := fun ⟨x, _⟩ => by
        refine Subtype.ext (funext fun i => ?_)
        cases i using Fin.cases with
        | zero => rfl
        | succ _ => rfl
      right_inv := fun ⟨v, ⟨y, _⟩⟩ => by
        refine Sigma.ext rfl (heq_of_eq (Subtype.ext (funext fun _ => rfl))) }
  rw [Fintype.card_congr e, Fintype.card_sigma]
  refine Finset.sum_congr rfl fun v _ => ?_
  by_cases hv : (v : ℕ) ≤ R
  · simp only [hv, ↓reduceIte]
    exact Fintype.card_congr (Equiv.subtypeEquivRight fun _ => by omega)
  · simp only [hv, ↓reduceIte, Fintype.card_eq_zero_iff]
    exact ⟨fun ⟨_, hy⟩ => hv (by omega)⟩

/-- When `c.sum < R`, there are no two-row contingency tables with row sum `R`. -/
theorem twoRowContingency_eq_zero_of_sum_lt {R : ℕ} {c : List ℕ} (h : c.sum < R) :
    TwoRowContingency (R, c) = 0 := by
  induction c generalizing R with
  | nil =>
    simp only [List.sum_nil] at h
    rw [twoRowContingency_nil]
    simp [show R ≠ 0 by omega]
  | cons a l ih =>
    simp only [List.sum_cons] at h
    rw [twoRowContingency_cons]
    refine Finset.sum_eq_zero fun v _ => ?_
    split_ifs with hv
    · exact ih (by have := v.2; omega)
    · rfl

/-- Upper bound `TwoRowContingency (R, c) ≤ ∏ i, (c[i] + 1)`. -/
theorem twoRowContingency_le_prod (R : ℕ) (c : List ℕ) :
    TwoRowContingency (R, c) ≤ ∏ i : Fin c.length, (c[i] + 1) := by
  unfold TwoRowContingency
  calc
    Fintype.card {x : (i : Fin c.length) → Fin (c[i] + 1) // ∑ i, (x i : ℕ) = R}
      ≤ Fintype.card ((i : Fin c.length) → Fin (c[i] + 1)) := Fintype.card_subtype_le _
    _ = ∏ i : Fin c.length, (c[i] + 1) := by simp [Fintype.card_pi, Fintype.card_fin]

/-- Permuting column sums preserves `TwoRowContingency`. -/
theorem twoRowContingency_perm {c₁ c₂ : List ℕ} (h : c₁.Perm c₂) (R : ℕ) :
    TwoRowContingency (R, c₁) = TwoRowContingency (R, c₂) := by
  induction h generalizing R with
  | nil => rfl
  | @cons a l₁ l₂ _ ih =>
    rw [twoRowContingency_cons, twoRowContingency_cons]
    refine Finset.sum_congr rfl fun v _ => ?_
    split_ifs <;> simp [ih]
  | swap a b l =>
    rw [twoRowContingency_cons, twoRowContingency_cons]
    have hexp (x y : ℕ) :
        ∑ v : Fin (x + 1), (if (v : ℕ) ≤ R then TwoRowContingency (R - v, y :: l) else 0) =
          ∑ v : Fin (x + 1), ∑ w : Fin (y + 1),
            if (v : ℕ) + w ≤ R then TwoRowContingency (R - (v + w), l) else 0 := by
      refine Finset.sum_congr rfl fun v _ => ?_
      by_cases hv : (v : ℕ) ≤ R
      · simp only [hv, ↓reduceIte, twoRowContingency_cons]
        refine Finset.sum_congr rfl fun w _ => ?_
        by_cases hvw : (v : ℕ) + w ≤ R
        · have hw : (w : ℕ) ≤ R - v := by omega
          simp only [hw, hvw, ↓reduceIte, Nat.sub_sub]
        · have hw : ¬ (w : ℕ) ≤ R - v := by omega
          simp only [hw, hvw, ↓reduceIte]
      · simp only [hv, ↓reduceIte]
        symm
        refine Finset.sum_eq_zero fun w _ => ?_
        have hvw : ¬ (v : ℕ) + w ≤ R := by omega
        simp only [hvw, ↓reduceIte]
    rw [hexp b a, hexp a b, Finset.sum_comm]
    refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun w _ => ?_
    simp only [Nat.add_comm]
  | trans _ _ ih₁ ih₂ => exact (ih₁ R).trans (ih₂ R)

/-- Removing zero column sums does not change `TwoRowContingency`. -/
theorem twoRowContingency_filter_pos (R : ℕ) (c : List ℕ) :
    TwoRowContingency (R, c.filter fun x => decide (0 < x)) = TwoRowContingency (R, c) := by
  induction c generalizing R with
  | nil => rfl
  | cons a l ih =>
    cases a with
    | zero =>
      simp only [List.filter_cons, lt_self_iff_false, decide_false, Bool.false_eq_true, ↓reduceIte]
      rw [twoRowContingency_cons, Fin.sum_univ_one]
      simp [ih]
    | succ k =>
      simp only [List.filter_cons, Nat.succ_pos, decide_true, ↓reduceIte]
      rw [twoRowContingency_cons, twoRowContingency_cons]
      refine Finset.sum_congr rfl fun v _ => ?_
      split_ifs <;> simp [ih]

/-! ### Membership in `#P` -/

section Membership

/-- Extracting the `j`-th bit of `l.foldr Nat.bit 0` returns `l.getD j false`. -/
private theorem testBit_foldr_bit (l : List Bool) (j : ℕ) :
    (l.foldr Nat.bit 0).testBit j = l.getD j false := by
  induction l generalizing j with
  | nil => simp
  | cons b l ih =>
    cases j with
    | zero => simp
    | succ j => simp [Nat.testBit_bit_succ, ih]

/-- Fixed-width decoding of `m` binary entries of bit-width `W` from certificate `w`. -/
private def tableWidth (c : List ℕ) : ℕ :=
  (encList encNat c).length + 1

private def tableEntries (c : List ℕ) (w : List Bool) : List ℕ :=
  let W := tableWidth c
  (List.range c.length).map fun i => ofBits ((w.drop (i * W)).take W)

/-- Verifier for `TwoRowContingency`: checks that the decoded entries satisfy `xᵢ ≤ cᵢ` and
`∑ xᵢ = R`. -/
private def contingencyVerifier (x : (ℕ × List ℕ) × List Bool) : Bool :=
  let xs := tableEntries x.1.2 x.2
  ((List.range x.1.2.length).all fun i => decide (xs.getD i 0 ≤ x.1.2.getD i 0)) &&
    (xs.sum == x.1.1)

private theorem computableInPolyTime_tableWidth :
    ComputableInPolyTime tableWidth (encList encNat) encUnary := by
  have hlen : ComputableInPolyTime (fun c : List ℕ => (encList encNat c).length)
      (encList encNat) encUnary :=
    (ComputableInPolyTime.length encBool).comp
      (ComputableInPolyTime.encoding_comp ComputableInPolyTime.id')
  exact ComputableInPolyTime.unary_add' hlen (ComputableInPolyTime.const 1)

private theorem computableInPolyTime_tableEntries :
    ComputableInPolyTime (fun x : (ℕ × List ℕ) × List Bool => tableEntries x.1.2 x.2)
      (encPair encTwoRowContingency encBits) (encList encNat) := by
  unfold tableEntries encTwoRowContingency
  have hW : ComputableInPolyTime (fun x : ((ℕ × List ℕ) × List Bool) × ℕ => tableWidth x.1.1.2)
      (encPair (encPair (encPair encNat (encList encNat)) encBits) encUnary) encUnary :=
    computableInPolyTime_tableWidth.comp (by fun_prop)
  have hlen : ComputableInPolyTime (fun x : (ℕ × List ℕ) × List Bool => x.1.2.length)
      (encPair (encPair encNat (encList encNat)) encBits) encUnary := by
    fun_prop
  refine ComputableInPolyTime.mapWithInput (ComputableInPolyTime.range.comp hlen) ?_
  exact ComputableInPolyTime.bitsToNat.comp <|
    ComputableInPolyTime.bitsTakeWithInput
      (ComputableInPolyTime.bitsDropWithInput (by fun_prop)
        (ComputableInPolyTime.unary_mul' (by fun_prop) hW)) hW

private theorem sum_map_range_eq_sum_fin (n : ℕ) (f : ℕ → ℕ) :
    ((List.range n).map f).sum = ∑ i : Fin n, f i.1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.map_singleton, List.sum_append, List.sum_singleton,
      ih, Fin.sum_univ_castSucc]
    rfl

private theorem computableInPolyTime_contingencyVerifier :
    ComputableInPolyTime contingencyVerifier (encPair encTwoRowContingency encBits) encBool := by
  unfold contingencyVerifier encTwoRowContingency
  have hxs : ComputableInPolyTime (fun x : (ℕ × List ℕ) × List Bool => tableEntries x.1.2 x.2)
      (encPair (encPair encNat (encList encNat)) encBits) (encList encNat) :=
    computableInPolyTime_tableEntries
  have hall : ComputableInPolyTime
      (fun x : (ℕ × List ℕ) × List Bool =>
        (List.range x.1.2.length).all fun i =>
          decide ((tableEntries x.1.2 x.2).getD i 0 ≤ x.1.2.getD i 0))
      (encPair (encPair encNat (encList encNat)) encBits) encBool := by
    refine ComputableInPolyTime.allWithInput
      (ComputableInPolyTime.range.comp
        ((ComputableInPolyTime.length encNat).comp
          ((ComputableInPolyTime.snd encNat (encList encNat)).comp
            (ComputableInPolyTime.fst (encPair encNat (encList encNat)) encBits)))) ?_
    exact ComputableInPolyTime.binary_le'
      (ComputableInPolyTime.listGetDWithInput
        (hxs.comp (ComputableInPolyTime.fst _ encUnary))
        (ComputableInPolyTime.snd _ encUnary) 0)
      (ComputableInPolyTime.listGetDWithInput
        ((ComputableInPolyTime.snd encNat (encList encNat)).comp
          ((ComputableInPolyTime.fst _ encBits).comp
            (ComputableInPolyTime.fst _ encUnary)))
        (ComputableInPolyTime.snd _ encUnary) 0)
  have hsum : ComputableInPolyTime
      (fun x : (ℕ × List ℕ) × List Bool => (tableEntries x.1.2 x.2).sum == x.1.1)
      (encPair (encPair encNat (encList encNat)) encBits) encBool :=
    ComputableInPolyTime.beq (ComputableInPolyTime.binary_sum.comp hxs)
      ((ComputableInPolyTime.fst encNat (encList encNat)).comp
        (ComputableInPolyTime.fst (encPair encNat (encList encNat)) encBits))
  have hand : (fun x : (ℕ × List ℕ) × List Bool =>
      ((List.range x.1.2.length).all fun i =>
        decide ((tableEntries x.1.2 x.2).getD i 0 ≤ x.1.2.getD i 0)) &&
        ((tableEntries x.1.2 x.2).sum == x.1.1)) =
      (fun x => if ((List.range x.1.2.length).all fun i =>
        decide ((tableEntries x.1.2 x.2).getD i 0 ≤ x.1.2.getD i 0)) then
        ((tableEntries x.1.2 x.2).sum == x.1.1) else false) := by
    funext x; cases ((List.range x.1.2.length).all _) <;> rfl
  rw [hand]
  exact ComputableInPolyTime.ite hall hsum (ComputableInPolyTime.const false)

private theorem acceptCount_contingencyVerifier (p : ℕ × List ℕ) :
    acceptCount contingencyVerifier p (p.2.length * tableWidth p.2) = TwoRowContingency p := by
  rcases p with ⟨R, c⟩
  set W := tableWidth c
  have hW_pos : 0 < W := Nat.succ_pos _
  have hW_ge (i : Fin c.length) : c[i].size ≤ W := by
    have hmem : c[i] ∈ c := List.getElem_mem i.2
    have hle := length_le_encList_of_mem encNat hmem
    simp only [encNat_apply, Nat.size_eq_bits_len] at hle
    exact le_trans hle (Nat.le_succ _)
  -- Bijection between accepting certificates `w : Fin (c.length * W) → Bool` and valid tables `x`
  unfold acceptCount TwoRowContingency
  have hentry (w : Fin (c.length * W) → Bool) (i : Fin c.length) :
      (tableEntries c (List.ofFn w)).getD i.1 0 =
        ofBits (((List.ofFn w).drop (i.1 * W)).take W) := by
    simp [tableEntries, i.2, W]
  have hsum_entries (w : Fin (c.length * W) → Bool) :
      (tableEntries c (List.ofFn w)).sum =
        ∑ i : Fin c.length, ofBits (((List.ofFn w).drop (i.1 * W)).take W) := by
    rw [tableEntries, sum_map_range_eq_sum_fin]
  have hacc_iff (w : Fin (c.length * W) → Bool) :
      contingencyVerifier ((R, c), List.ofFn w) = true ↔
        (∀ i : Fin c.length, ofBits (((List.ofFn w).drop (i.1 * W)).take W) ≤ c[i]) ∧
          ∑ i : Fin c.length, ofBits (((List.ofFn w).drop (i.1 * W)).take W) = R := by
    simp only [contingencyVerifier, Bool.and_eq_true, List.all_eq_true, List.mem_range,
      decide_eq_true_eq, beq_iff_eq, hsum_entries]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨fun i => ?_, h2⟩
      have hi := h1 i.1 i.2
      rw [hentry, List.getD_eq_getElem _ _ i.2] at hi
      exact hi
    · rintro ⟨h1, h2⟩
      refine ⟨fun i hi => ?_, h2⟩
      have hi' := h1 ⟨i, hi⟩
      rw [hentry w ⟨i, hi⟩, List.getD_eq_getElem _ _ hi]
      exact hi'
  have hdiv_lt (k : Fin (c.length * W)) : k.1 / W < c.length :=
    Nat.div_lt_of_lt_mul (Nat.mul_comm c.length W ▸ k.2)
  rw [← Fintype.card_subtype]
  refine Fintype.card_congr
    { toFun := fun ⟨w, hw⟩ =>
        let h := (hacc_iff w).mp hw
        ⟨fun i => ⟨ofBits (((List.ofFn w).drop (i.1 * W)).take W), Nat.lt_succ_of_le (h.1 i)⟩,
          h.2⟩
      invFun := fun ⟨x, hx⟩ =>
        ⟨fun k =>
          (x ⟨k.1 / W, hdiv_lt k⟩ : ℕ).testBit (k.1 % W),
          (hacc_iff _).mpr <| by
            have hslice (i : Fin c.length) :
                ofBits (((List.ofFn fun k : Fin (c.length * W) =>
                  (x ⟨k.1 / W, hdiv_lt k⟩ : ℕ).testBit
                    (k.1 % W)).drop (i.1 * W)).take W) = (x i : ℕ) := by
              have hlist :
                  ((List.ofFn fun k : Fin (c.length * W) =>
                    (x ⟨k.1 / W, hdiv_lt k⟩ : ℕ).testBit
                      (k.1 % W)).drop (i.1 * W)).take W =
                    (List.range W).map (x i : ℕ).testBit := by
                refine List.ext_getElem ?_ fun j hj1 hj2 => ?_
                · simp only [List.length_take, List.length_drop, List.length_ofFn,
                    List.length_map, List.length_range]
                  have : i.1 * W + W ≤ c.length * W := by
                    calc i.1 * W + W = (i.1 + 1) * W := by ring
                      _ ≤ c.length * W := Nat.mul_le_mul_right W i.2
                  omega
                · simp only [List.length_map, List.length_range] at hj2
                  simp only [List.getElem_take, List.getElem_drop, List.getElem_ofFn,
                    List.getElem_map, List.getElem_range]
                  have hdiv : (i.1 * W + j) / W = i.1 := by
                    rw [Nat.mul_comm, Nat.mul_add_div hW_pos, Nat.div_eq_of_lt hj2, add_zero]
                  have hmod : (i.1 * W + j) % W = j := by
                    rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hj2]
                  have hlt_ij : i.1 * W + j < c.length * W := by
                    calc i.1 * W + j < i.1 * W + W := by omega
                      _ = (i.1 + 1) * W := by ring
                      _ ≤ c.length * W := Nat.mul_le_mul_right W i.2
                  have hfin : (⟨(i.1 * W + j) / W, hdiv_lt ⟨i.1 * W + j, hlt_ij⟩⟩ :
                      Fin c.length) = i :=
                    Fin.ext hdiv
                  rw [hfin, hmod]
              rw [hlist]
              have hsize : (x i : ℕ).size ≤ W :=
                le_trans (Nat.size_le_size (Nat.le_of_lt_succ (x i).2)) (hW_ge i)
              exact Nat.foldr_bit_testBit hsize
            refine ⟨fun i => ?_, ?_⟩
            · rw [hslice i]; exact Nat.le_of_lt_succ (x i).2
            · simp only [hslice]; exact hx⟩
      left_inv := fun ⟨w, hw⟩ => by
        refine Subtype.ext (funext fun k => ?_)
        set i : Fin c.length := ⟨k.1 / W, hdiv_lt k⟩
        set j : ℕ := k.1 % W
        have hj : j < W := Nat.mod_lt k.1 hW_pos
        have hkj : i.1 * W + j = k.1 := by
          have := Nat.div_add_mod k.1 W
          dsimp [i, j]; linarith
        change (ofBits (((List.ofFn w).drop (i.1 * W)).take W)).testBit j = w k
        rw [ofBits, testBit_foldr_bit]
        have hlen : (((List.ofFn w).drop (i.1 * W)).take W).length = W := by
          simp only [List.length_take, List.length_drop, List.length_ofFn]
          have : i.1 * W + W ≤ c.length * W := by
            calc i.1 * W + W = (i.1 + 1) * W := by ring
              _ ≤ c.length * W := Nat.mul_le_mul_right W i.2
          omega
        rw [List.getD_eq_getElem _ _ (by omega)]
        simp only [List.getElem_take, List.getElem_drop, List.getElem_ofFn]
        congr 1; exact Fin.ext hkj
      right_inv := fun ⟨x, hx⟩ => by
        refine Subtype.ext (funext fun i => Fin.ext ?_)
        change ofBits (((List.ofFn fun k : Fin (c.length * W) =>
          (x ⟨k.1 / W, hdiv_lt k⟩ : ℕ).testBit
            (k.1 % W)).drop (i.1 * W)).take W) = (x i : ℕ)
        have hlist :
            ((List.ofFn fun k : Fin (c.length * W) =>
              (x ⟨k.1 / W, hdiv_lt k⟩ : ℕ).testBit
                (k.1 % W)).drop (i.1 * W)).take W =
              (List.range W).map (x i : ℕ).testBit := by
          refine List.ext_getElem ?_ fun j hj1 hj2 => ?_
          · simp only [List.length_take, List.length_drop, List.length_ofFn,
              List.length_map, List.length_range]
            have : i.1 * W + W ≤ c.length * W := by
              calc i.1 * W + W = (i.1 + 1) * W := by ring
                _ ≤ c.length * W := Nat.mul_le_mul_right W i.2
            omega
          · simp only [List.length_map, List.length_range] at hj2
            simp only [List.getElem_take, List.getElem_drop, List.getElem_ofFn,
              List.getElem_map, List.getElem_range]
            have hdiv : (i.1 * W + j) / W = i.1 := by
              rw [Nat.mul_comm, Nat.mul_add_div hW_pos, Nat.div_eq_of_lt hj2, add_zero]
            have hmod : (i.1 * W + j) % W = j := by
              rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hj2]
            have hlt_ij : i.1 * W + j < c.length * W := by
              calc i.1 * W + j < i.1 * W + W := by omega
                _ = (i.1 + 1) * W := by ring
                _ ≤ c.length * W := Nat.mul_le_mul_right W i.2
            have hfin : (⟨(i.1 * W + j) / W, hdiv_lt ⟨i.1 * W + j, hlt_ij⟩⟩ :
                Fin c.length) = i :=
              Fin.ext hdiv
            rw [hfin, hmod]
        rw [hlist]
        exact Nat.foldr_bit_testBit
          (le_trans (Nat.size_le_size (Nat.le_of_lt_succ (x i).2)) (hW_ge i)) }

/-- **`TwoRowContingency` belongs to `#P`**. -/
theorem twoRowContingency_mem_SharpP : TwoRowContingency ∈ SharpP encTwoRowContingency := by
  have hr : ComputableInPolyTime (fun p : ℕ × List ℕ => p.2.length * tableWidth p.2)
      encTwoRowContingency encUnary := by
    unfold encTwoRowContingency
    exact ComputableInPolyTime.unary_mul' (by fun_prop)
      (computableInPolyTime_tableWidth.comp (by fun_prop))
  have h := mem_SharpP_of_polyTime_length (enc := encTwoRowContingency)
    computableInPolyTime_contingencyVerifier hr
  simpa only [acceptCount_contingencyVerifier] using h

end Membership

/-! ### Polynomial generating-function identity -/

section GeneratingFunction

open Polynomial

/-- Generating function for `TwoRowContingency (s, ws.map (· - 1))`:
`[X^s] ∏_{i} (1 + X + … + X^{w_i - 1}) = TwoRowContingency (s, ws.map (· - 1))`. -/
private theorem coeff_prod_geom_eq_twoRowContingency (ws : List ℕ) (hpos : ∀ w ∈ ws, 1 ≤ w)
    (s : ℕ) :
    (∏ i : Fin ws.length, ∑ a ∈ Finset.range ws[i], (X : Polynomial ℤ) ^ a).coeff s =
      (TwoRowContingency (s, ws.map (· - 1)) : ℤ) := by
  induction ws generalizing s with
  | nil =>
    simp only [List.length_nil, Finset.univ_eq_empty, Finset.prod_empty, List.map_nil,
      twoRowContingency_nil, Polynomial.coeff_one]
    split_ifs <;> simp
  | cons w l ih =>
    have hw : 1 ≤ w := hpos w List.mem_cons_self
    have hl : ∀ u ∈ l, 1 ≤ u := fun u hu => hpos u (List.mem_cons_of_mem w hu)
    rw [List.map_cons, twoRowContingency_cons]
    have hprod :
        (∏ i : Fin (w :: l).length, ∑ a ∈ Finset.range (w :: l)[i], (X : Polynomial ℤ) ^ a) =
          (∑ a ∈ Finset.range w, (X : Polynomial ℤ) ^ a) *
            (∏ i : Fin l.length, ∑ a ∈ Finset.range l[i], (X : Polynomial ℤ) ^ a) := by
      change (∏ i : Fin (l.length + 1), _) = _
      rw [Fin.prod_univ_succ]; rfl
    rw [hprod, Finset.sum_mul]
    have hcoeff_sum : (∑ x ∈ Finset.range w,
        (X : Polynomial ℤ) ^ x *
          ∏ i : Fin l.length, ∑ a ∈ Finset.range l[i], (X : Polynomial ℤ) ^ a).coeff s =
        ∑ x ∈ Finset.range w,
          ((X : Polynomial ℤ) ^ x *
            ∏ i : Fin l.length, ∑ a ∈ Finset.range l[i], (X : Polynomial ℤ) ^ a).coeff s := by
      simp
    rw [hcoeff_sum]
    have hfin : (w - 1) + 1 = w := by omega
    rw [Nat.cast_sum]
    simp_rw [Nat.cast_ite, Nat.cast_zero]
    rw [Fin.sum_univ_eq_sum_range
      (fun a => if a ≤ s then (TwoRowContingency (s - a, l.map (· - 1)) : ℤ) else 0)
      ((w - 1) + 1), hfin]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Polynomial.coeff_X_pow_mul']
    split_ifs with ha
    · exact ih hl (s - a)
    · rfl

/-- Core polynomial identity linking `TwoRowContingency` to signed subset-sum counts:
`∑_{k=0}^N (-1)^k C(N, k) · [k ≤ T] · TwoRowContingency(T - k, ws.map (· - 1))`
equals `∑_{S ⊆ Fin N, ∑_{i∈S} ws[i] = T} (-1)^{|S|}`. -/
private theorem sum_choose_twoRowContingency_eq_signed_subsetSum (ws : List ℕ)
    (hpos : ∀ w ∈ ws, 1 ≤ w) (T : ℕ) :
    ∑ k ∈ Finset.range (ws.length + 1),
        (-1 : ℤ) ^ k * (ws.length.choose k : ℤ) *
          (if k ≤ T then (TwoRowContingency (T - k, ws.map (· - 1)) : ℤ) else 0) =
      ∑ S ∈ (Finset.univ : Finset (Fin ws.length)).powerset,
        if (∑ i ∈ S, ws[i]) = T then (-1 : ℤ) ^ S.card else 0 := by
  let F : Polynomial ℤ :=
    ∏ i : Fin ws.length, ∑ a ∈ Finset.range ws[i], (X : Polynomial ℤ) ^ a
  have hid : (1 - (X : Polynomial ℤ)) ^ ws.length * F =
      ∏ i : Fin ws.length, (1 - (X : Polynomial ℤ) ^ ws[i]) := by
    have hpow : (1 - (X : Polynomial ℤ)) ^ ws.length =
        ∏ _i : Fin ws.length, (1 - (X : Polynomial ℤ)) := by
      simp
    rw [hpow, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [mul_comm]
    exact geom_sum_mul_neg (X : Polynomial ℤ) ws[i]
  have hlhs : ((1 - (X : Polynomial ℤ)) ^ ws.length * F).coeff T =
      ∑ k ∈ Finset.range (ws.length + 1),
        (-1 : ℤ) ^ k * (ws.length.choose k : ℤ) *
          (if k ≤ T then (TwoRowContingency (T - k, ws.map (· - 1)) : ℤ) else 0) := by
    have hbin : (1 - (X : Polynomial ℤ)) ^ ws.length =
        ∑ k ∈ Finset.range (ws.length + 1),
          Polynomial.C ((-1 : ℤ) ^ k * (ws.length.choose k : ℤ)) * (X : Polynomial ℤ) ^ k := by
      rw [sub_eq_add_neg, add_comm, add_pow]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [one_pow, mul_one, neg_pow, map_mul, map_pow, map_neg, map_one, map_natCast]
      ring
    rw [hbin, Finset.sum_mul]
    have hcs : (∑ x ∈ Finset.range (ws.length + 1),
        Polynomial.C ((-1 : ℤ) ^ x * (ws.length.choose x : ℤ)) * (X : Polynomial ℤ) ^ x *
          F).coeff T =
        ∑ x ∈ Finset.range (ws.length + 1),
          (Polynomial.C ((-1 : ℤ) ^ x * (ws.length.choose x : ℤ)) * (X : Polynomial ℤ) ^ x *
            F).coeff T := by
      simp
    rw [hcs]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_assoc, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_mul']
    split_ifs with hk
    · rw [coeff_prod_geom_eq_twoRowContingency ws hpos (T - k)]
    · rw [mul_zero]
  have hrhs : (∏ i : Fin ws.length, (1 - (X : Polynomial ℤ) ^ ws[i])).coeff T =
      ∑ S ∈ (Finset.univ : Finset (Fin ws.length)).powerset,
        if (∑ i ∈ S, ws[i]) = T then (-1 : ℤ) ^ S.card else 0 := by
    have hexp : ∏ i : Fin ws.length, (1 - (X : Polynomial ℤ) ^ ws[i]) =
        ∑ S ∈ (Finset.univ : Finset (Fin ws.length)).powerset,
          Polynomial.C ((-1 : ℤ) ^ S.card) * (X : Polynomial ℤ) ^ (∑ i ∈ S, ws[i]) := by
      have h1 : ∀ i : Fin ws.length,
          1 - (X : Polynomial ℤ) ^ ws[i] = (-(X : Polynomial ℤ) ^ ws[i]) + 1 := fun i => by ring
      simp_rw [h1, Finset.prod_add]
      refine Finset.sum_congr rfl fun S _ => ?_
      rw [Finset.prod_const_one, mul_one, Finset.prod_neg, Finset.prod_pow_eq_pow_sum]
      simp [map_pow]
    rw [hexp]
    have hcs : (∑ S ∈ (Finset.univ : Finset (Fin ws.length)).powerset,
        Polynomial.C ((-1 : ℤ) ^ S.card) * (X : Polynomial ℤ) ^ (∑ i ∈ S, ws[i])).coeff T =
        ∑ S ∈ (Finset.univ : Finset (Fin ws.length)).powerset,
          (Polynomial.C ((-1 : ℤ) ^ S.card) * (X : Polynomial ℤ) ^ (∑ i ∈ S, ws[i])).coeff T := by
      simp
    rw [hcs]
    refine Finset.sum_congr rfl fun S _ => ?_
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, mul_ite, mul_one, mul_zero]
    simp only [eq_comm]
  rw [← hlhs, hid, hrhs]

end GeneratingFunction

/-! ### Counting Turing reduction from `SharpPositiveOneInExactThreeSATThree` -/

section Reduction

/-- Literal weights for `φ`: for each distinct variable index `i < v`, the two base-8 digit numbers
corresponding to assigning variable `i` to `true` or `false`. -/
private def oneInThreeWeights (φ : CNF ℕ) : List ℕ :=
  (List.range φ.distinctVars.length).flatMap fun i =>
    [ThreeSAT.octal (ThreeSAT.literalDigits φ i true),
      ThreeSAT.octal (ThreeSAT.literalDigits φ i false)]

/-- Column sums `c_r = w_r - 1` for the two-row contingency table reduction. -/
private def oneInThreeCols (φ : CNF ℕ) : List ℕ :=
  (oneInThreeWeights φ).map (· - 1)

/-- Target integer with base-8 digit `1` at every variable position `0, …, v - 1` and every clause
position `v, …, v + m - 1`. -/
private def oneInThreeTarget (φ : CNF ℕ) : ℕ :=
  ((List.range φ.distinctVars.length).map (8 ^ ·)).sum +
    ((List.range φ.length).map fun j => 8 ^ (φ.distinctVars.length + j)).sum

/-- Oracle query list `(T - k, cs)` for `k = 0, …, 2v`. -/
private def oneInThreeQueries (φ : CNF ℕ) : List (ℕ × List ℕ) :=
  if PositiveOneInExactThreeSATThree.syntaxCheck φ then
    (List.range (2 * φ.distinctVars.length + 1)).map fun k =>
      (oneInThreeTarget φ - k, oneInThreeCols φ)
  else
    []

/-- Unary upper bound on the binary bit-length of every oracle answer. -/
private def oneInThreeBound (φ : CNF ℕ) : ℕ :=
  3 * (2 * φ.distinctVars.length) * (φ.distinctVars.length + φ.length) + 1

/-- Polynomial-time post-processing combining the `2v + 1` oracle answers via inclusion-exclusion.
-/
private def oneInThreeCombine (p : CNF ℕ × List ℕ) : ℕ :=
  let φ := p.1
  let ans := p.2
  if PositiveOneInExactThreeSATThree.syntaxCheck φ then
    let v := φ.distinctVars.length
    let N := 2 * v
    let T := oneInThreeTarget φ
    let term (k : ℕ) : ℕ :=
      if decide (k ≤ T) then N.choose k * ans.getD k 0 else 0
    let sEven := (((List.range (N + 1)).filter fun k => k % 2 == 0).map term).sum
    let sOdd := (((List.range (N + 1)).filter fun k => k % 2 == 1).map term).sum
    if v % 2 == 0 then sEven - sOdd else sOdd - sEven
  else
    0

@[local fun_prop]
private theorem computableInPolyTime_eight_pow :
    ComputableInPolyTime (fun p : ℕ => 8 ^ p) encUnary encNat := by
  fun_prop

@[local fun_prop]
private theorem computableInPolyTime_oneInThreeWeights :
    ComputableInPolyTime oneInThreeWeights encCNF (encList encNat) := by
  unfold oneInThreeWeights
  exact ComputableInPolyTime.flatMapWithInput (by fun_prop) (by fun_prop)

@[local fun_prop]
private theorem computableInPolyTime_oneInThreeCols :
    ComputableInPolyTime oneInThreeCols encCNF (encList encNat) := by
  unfold oneInThreeCols
  exact ComputableInPolyTime.mapWithInput computableInPolyTime_oneInThreeWeights
    (ComputableInPolyTime.binary_sub' (by fun_prop) (ComputableInPolyTime.const 1))

@[local fun_prop]
private theorem computableInPolyTime_oneInThreeTarget :
    ComputableInPolyTime oneInThreeTarget encCNF encNat := by
  fun_prop [oneInThreeTarget]

private theorem computableInPolyTime_oneInThreeQueries :
    ComputableInPolyTime oneInThreeQueries encCNF (encList encTwoRowContingency) := by
  unfold oneInThreeQueries encTwoRowContingency
  refine ComputableInPolyTime.ite (by fun_prop) ?_ (ComputableInPolyTime.const [])
  refine ComputableInPolyTime.mapWithInput (by fun_prop) ?_
  exact (ComputableInPolyTime.binary_sub'
      (computableInPolyTime_oneInThreeTarget.comp (by fun_prop))
      (ComputableInPolyTime.unary_to_binary.comp (by fun_prop))).prod
    (computableInPolyTime_oneInThreeCols.comp (by fun_prop))

private theorem computableInPolyTime_oneInThreeBound :
    ComputableInPolyTime oneInThreeBound encCNF encUnary := by
  unfold oneInThreeBound
  fun_prop

private theorem computableInPolyTime_oneInThreeCombine :
    ComputableInPolyTime oneInThreeCombine (encPair encCNF (encList encNat)) encNat := by
  unfold oneInThreeCombine
  have hv_p : ComputableInPolyTime (fun p : CNF ℕ × List ℕ => p.1.distinctVars.length)
      (encPair encCNF (encList encNat)) encUnary := by
    have h1 : ComputableInPolyTime (fun φ : CNF ℕ => φ.distinctVars.length) encCNF encUnary := by
      fun_prop
    exact h1.comp (ComputableInPolyTime.fst encCNF (encList encNat))
  have h2v_p : ComputableInPolyTime (fun p : CNF ℕ × List ℕ => 2 * p.1.distinctVars.length)
      (encPair encCNF (encList encNat)) encUnary :=
    ComputableInPolyTime.unary_mul' (ComputableInPolyTime.const 2) hv_p
  have hrange_p : ComputableInPolyTime
      (fun p : CNF ℕ × List ℕ => List.range (2 * p.1.distinctVars.length + 1))
      (encPair encCNF (encList encNat)) (encList encUnary) :=
    ComputableInPolyTime.range.comp
      (ComputableInPolyTime.unary_add' h2v_p (ComputableInPolyTime.const 1))
  have hsyn_p : ComputableInPolyTime
      (fun p : CNF ℕ × List ℕ => PositiveOneInExactThreeSATThree.syntaxCheck p.1)
      (encPair encCNF (encList encNat)) encBool := by
    have h1 : ComputableInPolyTime PositiveOneInExactThreeSATThree.syntaxCheck encCNF encBool := by
      fun_prop
    exact h1.comp (ComputableInPolyTime.fst encCNF (encList encNat))
  refine ComputableInPolyTime.ite hsyn_p ?_ (ComputableInPolyTime.const 0)
  have hterm : ComputableInPolyTime
      (fun q : (CNF ℕ × List ℕ) × ℕ =>
        if decide (q.2 ≤ oneInThreeTarget q.1.1) then
          (2 * q.1.1.distinctVars.length).choose q.2 * q.1.2.getD q.2 0
        else 0)
      (encPair (encPair encCNF (encList encNat)) encUnary) encNat := by
    refine ComputableInPolyTime.ite
      (ComputableInPolyTime.binary_le'
        (ComputableInPolyTime.unary_to_binary.comp
          (ComputableInPolyTime.snd (encPair encCNF (encList encNat)) encUnary))
        (computableInPolyTime_oneInThreeTarget.comp
          ((ComputableInPolyTime.fst encCNF (encList encNat)).comp
            (ComputableInPolyTime.fst (encPair encCNF (encList encNat)) encUnary))))
      (ComputableInPolyTime.binary_mul'
        (ComputableInPolyTime.binary_choose'
          (h2v_p.comp (ComputableInPolyTime.fst (encPair encCNF (encList encNat)) encUnary))
          (ComputableInPolyTime.snd (encPair encCNF (encList encNat)) encUnary))
        (ComputableInPolyTime.listGetDWithInput
          ((ComputableInPolyTime.snd encCNF (encList encNat)).comp
            (ComputableInPolyTime.fst (encPair encCNF (encList encNat)) encUnary))
          (ComputableInPolyTime.snd (encPair encCNF (encList encNat)) encUnary) 0))
      (ComputableInPolyTime.const 0)
  have hmod2 : ComputableInPolyTime (fun q : (CNF ℕ × List ℕ) × ℕ => q.2 % 2)
      (encPair (encPair encCNF (encList encNat)) encUnary) encUnary :=
    ComputableInPolyTime.unary_mod.comp
      ((ComputableInPolyTime.snd (encPair encCNF (encList encNat)) encUnary).prod
        (ComputableInPolyTime.const 2))
  have heven : ComputableInPolyTime
      (fun p : CNF ℕ × List ℕ =>
        (((List.range (2 * p.1.distinctVars.length + 1)).filter fun k => k % 2 == 0).map fun k =>
          if decide (k ≤ oneInThreeTarget p.1) then
            (2 * p.1.distinctVars.length).choose k * p.2.getD k 0
          else 0).sum)
      (encPair encCNF (encList encNat)) encNat :=
    ComputableInPolyTime.binary_sum.comp <|
      ComputableInPolyTime.mapWithInput
        (ComputableInPolyTime.filterWithInput hrange_p
          (ComputableInPolyTime.beq hmod2 (ComputableInPolyTime.const 0)))
        hterm
  have hodd : ComputableInPolyTime
      (fun p : CNF ℕ × List ℕ =>
        (((List.range (2 * p.1.distinctVars.length + 1)).filter fun k => k % 2 == 1).map fun k =>
          if decide (k ≤ oneInThreeTarget p.1) then
            (2 * p.1.distinctVars.length).choose k * p.2.getD k 0
          else 0).sum)
      (encPair encCNF (encList encNat)) encNat :=
    ComputableInPolyTime.binary_sum.comp <|
      ComputableInPolyTime.mapWithInput
        (ComputableInPolyTime.filterWithInput hrange_p
          (ComputableInPolyTime.beq hmod2 (ComputableInPolyTime.const 1)))
        hterm
  exact ComputableInPolyTime.ite
    (ComputableInPolyTime.beq
      (ComputableInPolyTime.unary_mod.comp (hv_p.prod (ComputableInPolyTime.const 2)))
      (ComputableInPolyTime.const 0))
    (ComputableInPolyTime.binary_sub' heven hodd)
    (ComputableInPolyTime.binary_sub' hodd heven)

private theorem oneInThreeWeights_length (φ : CNF ℕ) :
    (oneInThreeWeights φ).length = 2 * φ.distinctVars.length := by
  unfold oneInThreeWeights
  rw [List.length_flatMap]
  simp [Nat.mul_comm]

private theorem oneInThreeWeights_pos (φ : CNF ℕ) :
    ∀ w ∈ oneInThreeWeights φ, 1 ≤ w := by
  intro w hw
  unfold oneInThreeWeights at hw
  rw [List.mem_flatMap] at hw
  obtain ⟨i, _, hmem⟩ := hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl <;>
    simp only [ThreeSAT.octal, ThreeSAT.literalDigits, List.map_cons, List.sum_cons] <;>
    exact le_trans (Nat.one_le_pow i 8 (by omega)) (Nat.le_add_right _ _)

private theorem oneInThreeWeights_lt (φ : CNF ℕ) :
    ∀ w ∈ oneInThreeWeights φ, w < 8 ^ (φ.distinctVars.length + φ.length) := by
  intro w hw
  unfold oneInThreeWeights at hw
  rw [List.mem_flatMap] at hw
  obtain ⟨i, hi, hmem⟩ := hw
  rw [List.mem_range] at hi
  have hlt (b : Bool) : ThreeSAT.octal (ThreeSAT.literalDigits φ i b) <
      8 ^ (φ.distinctVars.length + φ.length) := by
    have hnodup : (ThreeSAT.literalDigits φ i b).Nodup := by
      refine List.nodup_cons.2 ⟨fun h => ?_, ((List.nodup_range).filter _).map
        (fun _ _ h => Nat.add_left_cancel h)⟩
      obtain ⟨j, -, hEq⟩ := List.mem_map.1 h
      omega
    have hsub : (ThreeSAT.literalDigits φ i b).toFinset ⊆
        Finset.range (φ.distinctVars.length + φ.length) := by
      intro p hp
      rw [List.mem_toFinset] at hp
      rw [Finset.mem_range]
      simp only [ThreeSAT.literalDigits, List.mem_cons, List.mem_map, List.mem_filter,
        List.mem_range] at hp
      rcases hp with rfl | ⟨j, ⟨hj, _⟩, rfl⟩ <;> omega
    have hsum_eq : ThreeSAT.octal (ThreeSAT.literalDigits φ i b) =
        ∑ p ∈ Finset.range (φ.distinctVars.length + φ.length),
          (if p ∈ (ThreeSAT.literalDigits φ i b).toFinset then 1 else 0) * 8 ^ p := by
      simp_rw [ite_mul, one_mul, zero_mul]
      rw [ThreeSAT.octal, ← List.sum_toFinset _ hnodup, ← Finset.sum_filter,
        Finset.filter_mem_eq_inter, Finset.inter_eq_right.2 hsub]
    rw [hsum_eq]
    exact Nat.sum_range_mul_pow_lt fun p _ => by split_ifs <;> omega
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl
  · exact hlt true
  · exact hlt false

private theorem oneInThreeQueries_size (φ : CNF ℕ) (q : ℕ × List ℕ)
    (hq : q ∈ oneInThreeQueries φ) :
    (TwoRowContingency q).size ≤ oneInThreeBound φ := by
  unfold oneInThreeQueries at hq
  split_ifs at hq with hsyn
  · rw [List.mem_map] at hq
    obtain ⟨k, _, rfl⟩ := hq
    have hprod_le : TwoRowContingency (oneInThreeTarget φ - k, oneInThreeCols φ) ≤
        ∏ i : Fin (oneInThreeCols φ).length, ((oneInThreeCols φ)[i] + 1) :=
      twoRowContingency_le_prod _ _
    have hterm_lt : ∀ i : Fin (oneInThreeCols φ).length,
        (oneInThreeCols φ)[i] + 1 ≤ 2 ^ (3 * (φ.distinctVars.length + φ.length)) := by
      intro i
      have hi : i.1 < (oneInThreeWeights φ).length := by
        simpa [oneInThreeCols] using i.2
      have hw_eq : (oneInThreeCols φ)[i] + 1 = (oneInThreeWeights φ)[i.1]'hi := by
        have hget : (oneInThreeCols φ)[i] = (oneInThreeWeights φ)[i.1]'hi - 1 := by
          unfold oneInThreeCols
          exact List.getElem_map (f := fun x => x - 1) (l := oneInThreeWeights φ)
            (i := i.1) (h := i.2)
        have hpos := oneInThreeWeights_pos φ _ (List.getElem_mem hi)
        omega
      rw [hw_eq]
      have hlt := oneInThreeWeights_lt φ _ (List.getElem_mem hi)
      have h8 : 8 ^ (φ.distinctVars.length + φ.length) =
          2 ^ (3 * (φ.distinctVars.length + φ.length)) := by
        rw [show (8 : ℕ) = 2 ^ 3 by rfl, ← pow_mul]
      omega
    have hlt_pow : TwoRowContingency (oneInThreeTarget φ - k, oneInThreeCols φ) <
        2 ^ oneInThreeBound φ := by
      calc TwoRowContingency (oneInThreeTarget φ - k, oneInThreeCols φ)
          ≤ ∏ i : Fin (oneInThreeCols φ).length, ((oneInThreeCols φ)[i] + 1) := hprod_le
        _ ≤ ∏ _i : Fin (oneInThreeCols φ).length,
            2 ^ (3 * (φ.distinctVars.length + φ.length)) :=
          Finset.prod_le_prod fun i _ => hterm_lt i
        _ = (2 ^ (3 * (φ.distinctVars.length + φ.length))) ^ (oneInThreeCols φ).length := by
          simp
        _ = 2 ^ (3 * (φ.distinctVars.length + φ.length) * (2 * φ.distinctVars.length)) := by
          rw [← pow_mul, oneInThreeCols, List.length_map, oneInThreeWeights_length]
        _ < 2 ^ oneInThreeBound φ := by
          refine Nat.pow_lt_pow_right (by omega) ?_
          unfold oneInThreeBound
          nlinarith
    exact Nat.size_le.mpr hlt_pow
  · simp at hq

/-- Weight indexing equivalence: `(oneInThreeWeights φ)[2 * i] = octal(literalDigits φ i true)`
and `(oneInThreeWeights φ)[2 * i + 1] = octal(literalDigits φ i false)`. -/
private theorem oneInThreeWeights_getElem (φ : CNF ℕ) (r : Fin (oneInThreeWeights φ).length) :
    (oneInThreeWeights φ)[r] =
      ThreeSAT.octal (ThreeSAT.literalDigits φ (r.1 / 2) (r.1 % 2 == 0)) := by
  have hr_lt : r.1 < 2 * φ.distinctVars.length := by
    simpa [oneInThreeWeights_length] using r.2
  have hi : r.1 / 2 < φ.distinctVars.length := by omega
  unfold oneInThreeWeights
  -- Prove by induction on `n` for `(List.range n).flatMap fun i => [f i true, f i false]`
  have hgen : ∀ (n : ℕ) (f : ℕ → Bool → ℕ) (k : ℕ) (hk : k < 2 * n),
      ((List.range n).flatMap fun i => [f i true, f i false])[k]'(by
          rw [List.length_flatMap]; simp; omega) =
        f (k / 2) (k % 2 == 0) := by
    intro n f
    induction n with
    | zero => intro k hk; omega
    | succ n ih =>
      intro k hk
      have hrew : ((List.range (n + 1)).flatMap fun i => [f i true, f i false]) =
          ((List.range n).flatMap fun i => [f i true, f i false]) ++ [f n true, f n false] := by
        rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
      simp only [hrew]
      by_cases hkn : k < 2 * n
      · rw [List.getElem_append_left (by rw [List.length_flatMap]; simp; omega)]
        exact ih k hkn
      · rw [List.getElem_append_right (by rw [List.length_flatMap]; simp; omega)]
        have hlen : ((List.range n).flatMap fun i => [f i true, f i false]).length = 2 * n := by
          rw [List.length_flatMap]; simp [Nat.mul_comm]
        have hsub : k - 2 * n = 0 ∨ k - 2 * n = 1 := by omega
        rcases hsub with h0 | h1
        · have hk_eq : k = 2 * n := by omega
          subst hk_eq
          simp [hlen]
        · have hk_eq : k = 2 * n + 1 := by omega
          subst hk_eq
          simp [hlen, show (2 * n + 1) / 2 = n by omega, show (2 * n + 1) % 2 = 1 by omega]
  exact hgen φ.distinctVars.length (fun i b => ThreeSAT.octal (ThreeSAT.literalDigits φ i b))
    r.1 hr_lt

/-- Exact signed subset-sum count for a valid positive 1-in-3-SAT formula equals
`(-1)^v * SharpPositiveOneInExactThreeSATThree φ`. -/
private theorem signed_subsetSum_eq_sharpOneInThree (φ : CNF ℕ)
    (hsyn : PositiveOneInExactThreeSATThree.syntaxCheck φ = true) :
    (∑ S ∈ (Finset.univ : Finset (Fin (oneInThreeWeights φ).length)).powerset,
        if (∑ r ∈ S, (oneInThreeWeights φ)[r]) = oneInThreeTarget φ then
          (-1 : ℤ) ^ S.card
        else 0) =
      (-1 : ℤ) ^ φ.distinctVars.length * (SharpPositiveOneInExactThreeSATThree φ : ℤ) := by
  obtain ⟨hclauses, hpos_lit, _⟩ := (PositiveOneInExactThreeSATThree.syntaxCheck_iff φ).mp hsyn
  rw [OneSAT.positiveCheck_iff] at hpos_lit
  set v := φ.distinctVars.length
  set m := φ.length
  -- Reindex `Fin (oneInThreeWeights φ).length` to `Fin v × Bool` via `r ↔ (r / 2, r % 2 == 0)`
  let idxEquiv : Fin (oneInThreeWeights φ).length ≃ Fin v × Bool :=
    { toFun := fun r =>
        (⟨r.1 / 2, by
            have hr : r.1 < 2 * v := oneInThreeWeights_length φ ▸ r.2
            omega⟩,
          r.1 % 2 == 0)
      invFun := fun ⟨⟨i, hi⟩, b⟩ =>
        ⟨2 * i + if b then 0 else 1, by
          rw [oneInThreeWeights_length]
          cases b <;> simp <;> omega⟩
      left_inv := fun r => Fin.ext (by
        dsimp
        by_cases h : r.1 % 2 = 0 <;> simp [h] <;> omega)
      right_inv := fun ⟨⟨i, hi⟩, b⟩ => by
        cases b
        · exact Prod.ext (Fin.ext (by dsimp; omega))
            (by dsimp; rw [show (2 * i + 1) % 2 = 1 by omega]; decide)
        · exact Prod.ext (Fin.ext (by dsimp; omega))
            (by dsimp; rw [show (2 * i) % 2 = 0 by omega]; decide) }
  let col : Fin v × Bool → Finset ℕ := fun p => (ThreeSAT.literalDigits φ p.1.1 p.2).toFinset
  have hweight (r : Fin (oneInThreeWeights φ).length) :
      (oneInThreeWeights φ)[r] = ∑ p ∈ col (idxEquiv r), 8 ^ p := by
    rw [oneInThreeWeights_getElem]
    have hnodup : (ThreeSAT.literalDigits φ (idxEquiv r).1.1 (idxEquiv r).2).Nodup := by
      refine List.nodup_cons.2 ⟨fun h => ?_, ((List.nodup_range).filter _).map
        (fun _ _ h => Nat.add_left_cancel h)⟩
      obtain ⟨j, -, hEq⟩ := List.mem_map.1 h
      have := (idxEquiv r).1.2
      omega
    exact (List.sum_toFinset _ hnodup).symm
  have hT_eq : oneInThreeTarget φ = ∑ p ∈ Finset.range (v + m), 1 * 8 ^ p := by
    unfold oneInThreeTarget
    simp only [one_mul, Finset.sum_range_add]
    rw [sum_map_range_eq_sum_fin, Fin.sum_univ_eq_sum_range (fun x => 8 ^ x),
      sum_map_range_eq_sum_fin, Fin.sum_univ_eq_sum_range (fun x => 8 ^ (v + x))]
  have hcol_sub : ∀ x ∈ (Finset.univ : Finset (Fin v × Bool)), col x ⊆ Finset.range (v + m) := by
    intro ⟨⟨i, hi⟩, b⟩ _ p hp
    simp only [col, List.mem_toFinset, ThreeSAT.literalDigits, List.mem_cons, List.mem_map,
      List.mem_filter, List.mem_range] at hp
    rw [Finset.mem_range]
    rcases hp with rfl | ⟨j, ⟨hj, _⟩, rfl⟩ <;> omega
  have hmem_col_var (x : Fin v × Bool) {i : ℕ} (hi : i < v) :
      i ∈ col x ↔ x.1.1 = i := by
    simp only [col, List.mem_toFinset, ThreeSAT.literalDigits, List.mem_cons, List.mem_map,
      List.mem_filter, List.mem_range]
    constructor
    · rintro (rfl | ⟨j, _, hEq⟩)
      · rfl
      · omega
    · intro h; exact Or.inl h.symm
  have hmem_col_clause (x : Fin v × Bool) {j : ℕ} (hj : j < m) :
      v + j ∈ col x ↔ ThreeSAT.covers φ x.1.1 x.2 j = true := by
    simp only [col, List.mem_toFinset, ThreeSAT.literalDigits, List.mem_cons, List.mem_map,
      List.mem_filter, List.mem_range]
    constructor
    · rintro (hEq | ⟨j', ⟨_, hc⟩, hEq⟩)
      · have := x.1.2; omega
      · have : j' = j := by omega
        subst this; exact hc
    · intro hc; exact Or.inr ⟨j, ⟨hj, hc⟩, rfl⟩
  have hU : ∀ p < v + m, #{x ∈ (Finset.univ : Finset (Fin v × Bool)) | p ∈ col x} < 8 := by
    intro p hp
    by_cases hpv : p < v
    · have hcard : #{x ∈ (Finset.univ : Finset (Fin v × Bool)) | p ∈ col x} ≤ 2 := by
        calc #{x ∈ (Finset.univ : Finset (Fin v × Bool)) | p ∈ col x}
            ≤ #({(⟨p, hpv⟩, true), (⟨p, hpv⟩, false)} : Finset (Fin v × Bool)) := by
              refine Finset.card_le_card fun x hx => ?_
              have hx' := (hmem_col_var x hpv).mp (Finset.mem_filter.mp hx).2
              rcases x with ⟨⟨i, hi⟩, b⟩
              have hip : i = p := hx'
              subst hip; cases b <;> simp
          _ ≤ 2 := Finset.card_le_two
      omega
    · set j := p - v
      have hj : j < m := by omega
      have hp_eq : p = v + j := by omega
      rw [hp_eq]
      have hsub_c : #{x ∈ (Finset.univ : Finset (Fin v × Bool)) | v + j ∈ col x} ≤
          (φ.getD j []).length := by
        calc #{x ∈ (Finset.univ : Finset (Fin v × Bool)) | v + j ∈ col x}
            ≤ #(((φ.getD j []).map fun l =>
                (φ.distinctVars.idxOf l.1, l.2)).toFinset) := by
              have hinj : Set.InjOn (fun x : Fin v × Bool => (x.1.1, x.2))
                  (Finset.univ.filter fun x => v + j ∈ col x : Set (Fin v × Bool)) := by
                intro a _ b _ hEq
                simp only [Prod.mk.injEq] at hEq
                exact Prod.ext (Fin.ext hEq.1) hEq.2
              rw [← Finset.card_image_of_injOn hinj]
              refine Finset.card_le_card fun y hy => ?_
              rw [Finset.mem_image] at hy
              obtain ⟨x, hx, rfl⟩ := hy
              have hcov := (hmem_col_clause x hj).mp (Finset.mem_filter.mp hx).2
              obtain ⟨l, hl, hi, hb⟩ := ThreeSAT.covers_eq_true_iff.mp hcov
              exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨l, hl, by rw [hi, hb]⟩)
          _ ≤ (φ.getD j []).length := (List.toFinset_card_le _).trans (List.length_map ..).le
      have hlen3 : (φ.getD j []).length = 3 := by
        rw [List.getD_eq_getElem _ _ hj]
        exact (hclauses φ[j] (List.getElem_mem hj)).1
      omega
  -- Transport the powerset sum via `idxEquiv`!
  have hsum_trans :
      (∑ S ∈ (Finset.univ : Finset (Fin (oneInThreeWeights φ).length)).powerset,
          if (∑ r ∈ S, (oneInThreeWeights φ)[r]) = oneInThreeTarget φ then
            (-1 : ℤ) ^ S.card
          else 0) =
        ∑ F ∈ (Finset.univ : Finset (Fin v × Bool)).powerset,
          if (∑ x ∈ F, ∑ p ∈ col x, 8 ^ p) = ∑ p ∈ Finset.range (v + m), 1 * 8 ^ p then
            (-1 : ℤ) ^ F.card
          else 0 := by
    refine Finset.sum_bij (fun S _ => S.image idxEquiv) ?_ ?_ ?_ ?_
    · intro S _; exact Finset.mem_powerset.mpr (Finset.subset_univ _)
    · intro S₁ _ S₂ _ hEq
      ext r
      have := Finset.ext_iff.mp hEq (idxEquiv r)
      simpa [Finset.mem_image, idxEquiv.injective.eq_iff] using this
    · intro F _
      refine ⟨F.image idxEquiv.symm, Finset.mem_powerset.mpr (Finset.subset_univ _), ?_⟩
      ext x
      simp only [Finset.mem_image]
      constructor
      · rintro ⟨a, ⟨y, hy, rfl⟩, rfl⟩
        simpa using hy
      · intro hx
        exact ⟨idxEquiv.symm x, ⟨x, hx, rfl⟩, idxEquiv.apply_symm_apply x⟩
    · intro S _
      rw [Finset.card_image_of_injective S idxEquiv.injective,
        Finset.sum_image (fun _ _ _ _ h => idxEquiv.injective h), hT_eq]
      have hs : ∑ r ∈ S, (oneInThreeWeights φ)[r] = ∑ r ∈ S, ∑ p ∈ col (idxEquiv r), 8 ^ p :=
        Finset.sum_congr rfl fun r _ => hweight r
      rw [hs]
  rw [hsum_trans]
  -- Every valid `F` has `F.card = v`!
  have hcard_valid : ∀ F ∈ (Finset.univ : Finset (Fin v × Bool)).powerset,
      (∑ x ∈ F, ∑ p ∈ col x, 8 ^ p) = ∑ p ∈ Finset.range (v + m), 1 * 8 ^ p →
      F.card = v := by
    intro F _ hsum
    have hcnt := (sum_sum_pow_eq_iff (Finset.subset_univ F)
      hcol_sub hU (fun _ _ => by omega)).mp hsum
    have hpart : F.card = ∑ i : Fin v, #{x ∈ F | x.1 = i} := by
      rw [← Finset.card_biUnion]
      · congr 1; ext x; simp
      · intro i _ j _ hij
        change Disjoint _ _
        rw [Finset.disjoint_left]; intro x h1 h2
        simp only [Finset.mem_filter] at h1 h2
        exact hij (h1.2.symm.trans h2.2)
    rw [hpart]
    have h1 : ∀ i : Fin v, #{x ∈ F | x.1 = i} = 1 := by
      intro i
      have hi := hcnt i.1 (by have := i.2; omega)
      convert hi using 2
      ext x
      simp only [Finset.mem_filter, hmem_col_var x i.2, Fin.ext_iff]
    simp [h1]
  have hrhs_pull :
      (∑ F ∈ (Finset.univ : Finset (Fin v × Bool)).powerset,
          if (∑ x ∈ F, ∑ p ∈ col x, 8 ^ p) = ∑ p ∈ Finset.range (v + m), 1 * 8 ^ p then
            (-1 : ℤ) ^ F.card
          else 0) =
        (-1 : ℤ) ^ v *
          ((Finset.univ.filter fun F : Finset (Fin v × Bool) =>
              (∑ x ∈ F, ∑ p ∈ col x, 8 ^ p) = ∑ p ∈ Finset.range (v + m), 1 * 8 ^ p).card : ℤ) := by
    rw [Finset.card_filter, Nat.cast_sum, Finset.mul_sum]
    have hpow_univ : (Finset.univ : Finset (Fin v × Bool)).powerset = Finset.univ := by
      ext F; simp
    rw [hpow_univ]
    refine Finset.sum_congr rfl fun F _ => ?_
    split_ifs with h
    · rw [hcard_valid F (by simp) h, Nat.cast_one, mul_one]
    · simp
  rw [hrhs_pull]
  congr 1
  simp only [SharpPositiveOneInExactThreeSATThree, hsyn, ↓reduceIte, SharpOneSAT]
  congr 1
  -- Show `φ.oneModelCount = #{F : Finset (Fin v × Bool) | ∑ x ∈ F, ∑ p ∈ col x, 8^p = T}`!
  symm
  refine CNF.oneModelCount_eq_card_filter
    (f := fun σ => Finset.univ.filter fun x : Fin v × Bool => σ φ.distinctVars[x.1] = x.2)
    (P := fun F => (∑ x ∈ F, ∑ p ∈ col x, 8 ^ p) = ∑ p ∈ Finset.range (v + m), 1 * 8 ^ p) ?_ ?_
  · intro σ τ _ _
    constructor
    · intro hEq u hu
      have hu_d : u ∈ φ.distinctVars := CNF.mem_distinctVars.mpr hu
      set i : Fin v := ⟨φ.distinctVars.idxOf u, List.idxOf_lt_length_iff.mpr hu_d⟩
      have hget : φ.distinctVars[i] = u := List.getElem_idxOf (List.idxOf_lt_length_iff.mpr hu_d)
      have hmem := Finset.ext_iff.mp hEq (i, σ u)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hget, true_iff] at hmem
      exact hmem.symm
    · intro hEq
      ext ⟨i, b⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have hmem : φ.distinctVars[i] ∈ φ.vars :=
        CNF.mem_distinctVars.mp (List.getElem_mem i.2)
      rw [hEq _ hmem]
  · intro F
    rw [sum_sum_pow_eq_iff (Finset.subset_univ F) hcol_sub hU
      (fun _ _ => by omega)]
    -- Helper: for any `σ : ℕ → Bool`, `φ.evalOne σ = true` iff for every clause `j < m`,
    -- `#{x ∈ F_σ | v + j ∈ col x} = 1`!
    have hevalOne_iff (σ : ℕ → Bool) :
        φ.evalOne σ = true ↔
          ∀ j : Fin m,
            #{x ∈ Finset.univ.filter (fun x : Fin v × Bool => σ φ.distinctVars[x.1] = x.2) |
                v + j.1 ∈ col x} = 1 := by
      have hcard_eq : ∀ (j : ℕ) (hj : j < m),
          #{x ∈ Finset.univ.filter (fun x : Fin v × Bool => σ φ.distinctVars[x.1] = x.2) |
              v + j ∈ col x} =
            φ[j].countP (Literal.eval σ) := by
        intro j hj
        have hpos_j := hpos_lit φ[j] (List.getElem_mem hj)
        have hnodup_j := (hclauses φ[j] (List.getElem_mem hj)).2
        rw [List.countP_eq_length_filter]
        have hnodup_c : φ[j].Nodup := List.Nodup.of_map Prod.fst hnodup_j
        rw [← List.toFinset_card_of_nodup (hnodup_c.filter _)]
        refine Finset.card_bij (fun x _ => (φ.distinctVars[x.1], x.2)) ?_ ?_ ?_
        · intro x hx
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
          have hcov := (hmem_col_clause x hj).mp hx.2
          obtain ⟨l, hl, hi, hb⟩ := ThreeSAT.covers_eq_true_iff.mp hcov
          rw [List.getD_eq_getElem _ _ hj] at hl
          have hl_d : l.1 ∈ φ.distinctVars := CNF.mem_distinctVars.mpr
            (List.mem_map.mpr ⟨l, List.mem_flatten.mpr ⟨φ[j], List.getElem_mem hj, hl⟩, rfl⟩)
          have hget : φ.distinctVars[x.1] = l.1 := by
            have : x.1.1 = φ.distinctVars.idxOf l.1 := hi.symm
            simp [this]
          have hpair : (φ.distinctVars[x.1], x.2) = l := Prod.ext hget hb.symm
          rw [hpair, List.mem_toFinset, List.mem_filter]
          refine ⟨hl, ?_⟩
          have hlt : l.2 = true := hpos_j l hl
          simp only [Literal.eval, hlt]
          rw [← hget, hx.1, ← hb, hlt]
          rfl
        · intro x₁ _ x₂ _ hEq
          simp only [Prod.mk.injEq] at hEq
          have h1 : x₁.1 = x₂.1 := Fin.ext (by
            have := (List.nodup_iff_injective_getElem.mp (CNF.nodup_distinctVars φ)) hEq.1
            exact congrArg Fin.val this)
          exact Prod.ext h1 hEq.2
        · intro l hl
          rw [List.mem_toFinset, List.mem_filter] at hl
          have hl_d : l.1 ∈ φ.distinctVars := CNF.mem_distinctVars.mpr
            (List.mem_map.mpr ⟨l, List.mem_flatten.mpr ⟨φ[j], List.getElem_mem hj, hl.1⟩, rfl⟩)
          let i : Fin v := ⟨φ.distinctVars.idxOf l.1, List.idxOf_lt_length_iff.mpr hl_d⟩
          have hget : φ.distinctVars[i] = l.1 := List.getElem_idxOf i.2
          have hlt : l.2 = true := hpos_j l hl.1
          have hσ : σ l.1 = l.2 := by
            have hval := hl.2
            simp only [Literal.eval, hlt, beq_iff_eq] at hval
            rw [hval, hlt]
          refine ⟨(i, l.2), ?_, Prod.ext hget rfl⟩
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, hget, hσ, true_and]
          rw [hmem_col_clause (i, l.2) hj, ThreeSAT.covers_eq_true_iff]
          exact ⟨l, by rw [List.getD_eq_getElem _ _ hj]; exact hl.1, rfl, rfl⟩
      simp only [CNF.evalOne, List.all_eq_true]
      constructor
      · intro h j
        rw [hcard_eq j.1 j.2]
        simpa [Clause.evalOne] using h φ[j.1] (List.getElem_mem j.2)
      · intro h c hc
        obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hc
        simp only [Clause.evalOne, beq_iff_eq]
        rw [← hcard_eq j hj]
        exact h ⟨j, hj⟩
    constructor
    · intro hcnt
      let σ : ℕ → Bool := fun u =>
        if hu : u ∈ φ.distinctVars then
          decide ((⟨φ.distinctVars.idxOf u, List.idxOf_lt_length_iff.mpr hu⟩, true) ∈ F)
        else false
      have hF_eq :
          Finset.univ.filter (fun x : Fin v × Bool => σ φ.distinctVars[x.1] = x.2) = F := by
        ext ⟨i, b⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        have hi_mem : φ.distinctVars[i] ∈ φ.distinctVars := List.getElem_mem i.2
        have hidx : (⟨φ.distinctVars.idxOf φ.distinctVars[i],
            List.idxOf_lt_length_iff.mpr hi_mem⟩ : Fin v) = i :=
          (List.nodup_iff_injective_getElem.mp (CNF.nodup_distinctVars φ))
            (List.getElem_idxOf (List.idxOf_lt_length_iff.mpr hi_mem))
        have hσi : σ φ.distinctVars[i] = decide ((i, true) ∈ F) := by
          simp only [σ, hi_mem, ↓reduceDIte, hidx]
        rw [hσi]
        -- Use `#{x ∈ F | x.1 = i} = 1`!
        have h1 : #{x ∈ F | x.1 = i} = 1 := by
          have hi := hcnt i.1 (by have := i.2; omega)
          convert hi using 2
          ext x
          simp only [Finset.mem_filter, hmem_col_var x i.2, Fin.ext_iff]
        have hpair_card : #{x ∈ F | x.1 = i} =
            (if (i, true) ∈ F then 1 else 0) + (if (i, false) ∈ F then 1 else 0) := by
          have hfilt : F.filter (fun x => x.1 = i) =
              ({(i, true), (i, false)} : Finset (Fin v × Bool)).filter (· ∈ F) := by
            ext ⟨i', b'⟩
            simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
            constructor
            · rintro ⟨hx, rfl⟩; cases b' <;> simp [hx]
            · rintro ⟨h | h, hx⟩ <;> exact ⟨hx, congrArg Prod.fst h⟩
          rw [hfilt, Finset.filter_insert, Finset.filter_singleton]
          have hne_tf : ((i, true) : Fin v × Bool) ≠ (i, false) :=
            fun h => Bool.noConfusion (congrArg Prod.snd h)
          split_ifs with h1t h2f
          · rw [Finset.card_insert_of_notMem (by simp [hne_tf]), Finset.card_singleton]
          · simp
          · simp
          · simp
        cases b
        · simp only [decide_eq_false_iff_not]
          rw [h1] at hpair_card
          by_cases ht : (i, true) ∈ F <;> by_cases hf : (i, false) ∈ F
          · simp [ht, hf] at hpair_card
          · simp [ht, hf]
          · simp [ht, hf]
          · simp [ht, hf] at hpair_card
        · simp only [decide_eq_true_eq]
      refine ⟨σ, (hevalOne_iff σ).mpr fun j => ?_, hF_eq⟩
      rw [hF_eq]
      exact hcnt (v + j.1) (by omega)
    · rintro ⟨σ, hσ, rfl⟩ p hp
      by_cases hpv : p < v
      · have hfilt : (Finset.univ.filter fun x : Fin v × Bool =>
            σ φ.distinctVars[x.1] = x.2).filter (fun x => p ∈ col x) =
            {(⟨p, hpv⟩, σ φ.distinctVars[p])} := by
          ext ⟨i, b⟩
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, hmem_col_var _ hpv,
            Finset.mem_singleton, Prod.mk.injEq, Fin.ext_iff]
          constructor
          · rintro ⟨hb, rfl⟩; exact ⟨rfl, hb.symm⟩
          · rintro ⟨rfl, rfl⟩; exact ⟨rfl, rfl⟩
        rw [hfilt, Finset.card_singleton]
      · set j := p - v
        have hj : j < m := by omega
        have hp_eq : p = v + j := by omega
        rw [hp_eq]
        exact (hevalOne_iff σ).mp hσ ⟨j, hj⟩

/-- Specification of the batch-oracle reduction for `TwoRowContingency`. -/
private theorem oneInThreeCombine_spec (φ : CNF ℕ) :
    oneInThreeCombine (φ, (oneInThreeQueries φ).map TwoRowContingency) =
      SharpPositiveOneInExactThreeSATThree φ := by
  unfold oneInThreeCombine oneInThreeQueries
  by_cases hsyn : PositiveOneInExactThreeSATThree.syntaxCheck φ = true
  · simp only [hsyn, ↓reduceIte]
    set v := φ.distinctVars.length
    set N := 2 * v
    set T := oneInThreeTarget φ
    have hN_eq : (oneInThreeWeights φ).length = N := oneInThreeWeights_length φ
    have hpoly := sum_choose_twoRowContingency_eq_signed_subsetSum (oneInThreeWeights φ)
      (oneInThreeWeights_pos φ) T
    rw [signed_subsetSum_eq_sharpOneInThree φ hsyn] at hpoly
    -- Rewrite the LHS sum over `range (N + 1)` as `sEven - sOdd`!
    set ans := ((List.range (N + 1)).map fun k => (T - k, oneInThreeCols φ)).map TwoRowContingency
    let term (k : ℕ) : ℕ := if decide (k ≤ T) then N.choose k * ans.getD k 0 else 0
    have hans (k : ℕ) (hk : k < N + 1) :
        ans.getD k 0 = TwoRowContingency (T - k, oneInThreeCols φ) := by
      simp [ans, hk]
    have hterm_eq (k : ℕ) (hk : k < N + 1) :
        (term k : ℤ) = (N.choose k : ℤ) *
          (if k ≤ T then (TwoRowContingency (T - k, oneInThreeCols φ) : ℤ) else 0) := by
      dsimp only [term]
      by_cases hle : k ≤ T
      · simp only [hle, decide_true, ↓reduceIte, hans k hk, Nat.cast_mul]
      · simp only [hle, decide_false, Bool.false_eq_true, ↓reduceIte, Nat.cast_zero, mul_zero]
    have hsplit_list (r : ℕ) :
        ((((List.range (N + 1)).filter fun k => k % 2 == r).map term).sum : ℤ) =
          ∑ k ∈ (Finset.range (N + 1)).filter (fun k => k % 2 = r), (term k : ℤ) := by
      rw [← List.sum_toFinset _ ((List.nodup_range.filter _))]
      · rw [Nat.cast_sum]
        congr 1; ext k; simp [List.mem_toFinset]
    have hdiff :
        ((((List.range (N + 1)).filter fun k => k % 2 == 0).map term).sum : ℤ) -
        ((((List.range (N + 1)).filter fun k => k % 2 == 1).map term).sum : ℤ) =
          (-1 : ℤ) ^ v * (SharpPositiveOneInExactThreeSATThree φ : ℤ) := by
      rw [hsplit_list 0, hsplit_list 1, ← hpoly]
      have hdisj : Disjoint ((Finset.range (N + 1)).filter fun k => k % 2 = 0)
          ((Finset.range (N + 1)).filter fun k => k % 2 = 1) := by
        rw [Finset.disjoint_left]; intro k h1 h2
        simp only [Finset.mem_filter] at h1 h2; omega
      have hunion : (Finset.range (N + 1)).filter (fun k => k % 2 = 0) ∪
          (Finset.range (N + 1)).filter (fun k => k % 2 = 1) = Finset.range (N + 1) := by
        ext k
        simp only [Finset.mem_union, Finset.mem_filter]
        constructor
        · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
        · intro h
          have hmod : k % 2 = 0 ∨ k % 2 = 1 := by omega
          rcases hmod with h0 | h1
          · exact Or.inl ⟨h, h0⟩
          · exact Or.inr ⟨h, h1⟩
      rw [hN_eq]
      conv_rhs => rw [← hunion, Finset.sum_union hdisj]
      have h0 : ∑ k ∈ (Finset.range (N + 1)).filter (fun k => k % 2 = 0),
          (-1 : ℤ) ^ k * (N.choose k : ℤ) *
            (if k ≤ T then (TwoRowContingency (T - k, oneInThreeCols φ) : ℤ) else 0) =
          ∑ k ∈ (Finset.range (N + 1)).filter (fun k => k % 2 = 0), (term k : ℤ) := by
        refine Finset.sum_congr rfl fun k hk => ?_
        have hk' := Finset.mem_filter.mp hk
        have heven : Even k := Nat.even_iff.mpr hk'.2
        rw [heven.neg_one_pow, one_mul, hterm_eq k (Finset.mem_range.mp hk'.1)]
      have h1 : ∑ k ∈ (Finset.range (N + 1)).filter (fun k => k % 2 = 1),
          (-1 : ℤ) ^ k * (N.choose k : ℤ) *
            (if k ≤ T then (TwoRowContingency (T - k, oneInThreeCols φ) : ℤ) else 0) =
          -(∑ k ∈ (Finset.range (N + 1)).filter (fun k => k % 2 = 1), (term k : ℤ)) := by
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun k hk => ?_
        have hk' := Finset.mem_filter.mp hk
        have hodd : Odd k := Nat.odd_iff.mpr hk'.2
        rw [hodd.neg_one_pow, neg_one_mul, hterm_eq k (Finset.mem_range.mp hk'.1), neg_mul]
      change _ = (∑ x ∈ (Finset.range (N + 1)).filter (fun k => k % 2 = 0),
          (-1 : ℤ) ^ x * (N.choose x : ℤ) *
            (if x ≤ T then (TwoRowContingency (T - x, oneInThreeCols φ) : ℤ) else 0)) +
        ∑ x ∈ (Finset.range (N + 1)).filter (fun k => k % 2 = 1),
          (-1 : ℤ) ^ x * (N.choose x : ℤ) *
            (if x ≤ T then (TwoRowContingency (T - x, oneInThreeCols φ) : ℤ) else 0)
      rw [h0, h1, sub_eq_add_neg]
    by_cases hv : v % 2 = 0
    · simp only [hv, beq_self_eq_true, ↓reduceIte]
      have hEv : Even v := Nat.even_iff.mpr hv
      rw [hEv.neg_one_pow, one_mul] at hdiff
      dsimp only [term] at hdiff
      omega
    · have hv1 : (v % 2 == 0) = false := by simp [hv]
      simp only [hv1, Bool.false_eq_true, ↓reduceIte]
      have hOd : Odd v := Nat.odd_iff.mpr (by omega)
      rw [hOd.neg_one_pow, neg_one_mul] at hdiff
      dsimp only [term] at hdiff
      omega
  · simp only [hsyn, Bool.false_eq_true, ↓reduceIte, SharpPositiveOneInExactThreeSATThree]

/-- **Batch-oracle counting Turing reduction**
`SharpPositiveOneInExactThreeSATThree ≤_T^#P TwoRowContingency`. -/
theorem countingTuringReducible_sharpOneInThree_twoRowContingency :
    CountingTuringReducible encCNF encTwoRowContingency
      SharpPositiveOneInExactThreeSATThree TwoRowContingency :=
  PolyTimeOracleProgram.of_batchNatBits
    oneInThreeQueries oneInThreeBound oneInThreeCombine
    computableInPolyTime_oneInThreeQueries
    computableInPolyTime_oneInThreeBound
    computableInPolyTime_oneInThreeCombine
    oneInThreeQueries_size
    oneInThreeCombine_spec

/-- Composing the batch-oracle reduction
`SharpPositiveOneInExactThreeSATThree ≤_T^#P TwoRowContingency`
with any parsimonious reduction `TwoRowContingency ≤_par g` gives
`SharpPositiveOneInExactThreeSATThree ≤_T^#P g`. -/
theorem countingTuringReducible_sharpOneInThree_of_parsimonious
    {β : Type} {encB : β ↪ List Bool} {g : β → ℕ}
    (hred : ParsimoniousReducible encTwoRowContingency encB TwoRowContingency g) :
    CountingTuringReducible encCNF encB SharpPositiveOneInExactThreeSATThree g := by
  obtain ⟨r, hr, hfg⟩ := hred
  refine PolyTimeOracleProgram.of_batchNatBits
    (fun φ => (oneInThreeQueries φ).map r)
    oneInThreeBound
    oneInThreeCombine
    (ComputableInPolyTime.mapWithInput computableInPolyTime_oneInThreeQueries
      (hr.comp (ComputableInPolyTime.snd _ _)))
    computableInPolyTime_oneInThreeBound
    computableInPolyTime_oneInThreeCombine
    (fun φ b hb => by
      rw [List.mem_map] at hb
      obtain ⟨q, hq, rfl⟩ := hb
      rw [← hfg q]
      exact oneInThreeQueries_size φ q hq)
    (fun φ => by
      have hmap : ((oneInThreeQueries φ).map r).map g =
          (oneInThreeQueries φ).map TwoRowContingency := by
        rw [List.map_map]
        exact List.map_congr_left fun q _ => (hfg q).symm
      rw [hmap]
      exact oneInThreeCombine_spec φ)

/-- `SharpPositiveOneInExactThreeSATThree` is parsimoniously `#P`-hard. -/
theorem sharpPositiveOneInExactThreeSATThree_sharpPHard :
    SharpPHard encCNF SharpPositiveOneInExactThreeSATThree :=
  SharpThreeSAT_sharpPComplete.2.trans
    parsimoniousReducible_SharpThreeSAT_SharpPositiveOneInExactThreeSATThree

/-- **`TwoRowContingency` is `#P`-hard under polynomial-time counting Turing reductions**. -/
theorem twoRowContingency_countingTuringHard :
    CountingTuringHard encTwoRowContingency TwoRowContingency :=
  sharpPositiveOneInExactThreeSATThree_sharpPHard.trans_countingTuring
    countingTuringReducible_sharpOneInThree_twoRowContingency

/-- **`TwoRowContingency` is `#P`-complete under polynomial-time counting Turing reductions**. -/
theorem twoRowContingency_countingTuringComplete :
    CountingTuringComplete encTwoRowContingency TwoRowContingency :=
  ⟨twoRowContingency_mem_SharpP, twoRowContingency_countingTuringHard⟩

/-- Any counting problem `g` to which `TwoRowContingency` reduces parsimoniously is `#P`-hard
under polynomial-time counting Turing reductions. -/
theorem countingTuringHard_of_parsimonious_from_twoRowContingency
    {β : Type} {encB : β ↪ List Bool} {g : β → ℕ}
    (hred : ParsimoniousReducible encTwoRowContingency encB TwoRowContingency g) :
    CountingTuringHard encB g :=
  sharpPositiveOneInExactThreeSATThree_sharpPHard.trans_countingTuring
    (countingTuringReducible_sharpOneInThree_of_parsimonious hred)

end Reduction

end Cslib.Complexity
