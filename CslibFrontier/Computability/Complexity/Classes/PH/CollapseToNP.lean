module

public import CslibFrontier.Computability.Circuit.Boolean.PPoly
public import CslibFrontier.Computability.Complexity.Classes.EXP
public import CslibFrontier.Computability.Complexity.Classes.PH
public import CslibFrontier.Computability.Complexity.Classes.Oracle.Counting
public import CslibFrontier.Computability.Complexity.Problems.Permanent.Basic
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List
import Cslib.Computability.Circuit.Boolean.Shannon
import CslibFrontier.Computability.Complexity.Classes.Oracle.Lowness
import CslibFrontier.Computability.Complexity.Classes.Padding
import CslibFrontier.Computability.Complexity.Classes.Toda
import CslibFrontier.Computability.Complexity.Problems.Permanent.Valiant
import CslibFrontier.Computability.MCSP.NP
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Max
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder
import Mathlib.Data.Nat.Choose.Sum

/-!
# Polynomial Hierarchy Collapse to `NP` and `NEXP ⊄ P/poly`

Structural complexity theorems connecting collapses of the polynomial hierarchy to circuit lower
bounds for `NEXP` and the permanent:

## Main results

* `CslibFrontier.Complexity.not_NEXP_subset_PPoly_of_PH_subset_NP`: if `PH ⊆ NP`, then
  `NEXP ⊄ P/poly`. The proof defines a padded version of the lexicographically first hard truth
  table language in `Σ₃ ⊆ PH`, transfers it into `NEXP` via exponential padding, and separates it
  from `P/poly` via Shannon's counting lower bound.
* `CslibFrontier.Complexity.PH_subset_NP_of_zeroOnePermanent_mem_NP_inter_coNP`: if the bit graph
  of `ZeroOnePermanent` belongs to `NP ∩ coNP`, then `PH ⊆ NP`, via Toda's theorem, Valiant's
  `#P`-hardness of the zero-one permanent, and oracle lowness of `NP ∩ coNP`.
* `CslibFrontier.Complexity.not_NEXP_subset_PPoly_of_zeroOnePermanent_mem_NP_inter_coNP`: if the
  bit graph of `ZeroOnePermanent` belongs to `NP ∩ coNP`, then `NEXP ⊄ P/poly`.
-/

public section

namespace CslibFrontier.Complexity

open Cslib Cslib.Complexity Cslib.Circuits Cslib.Circuits.Boolean
open Turing.MultiTapeTM

/-! ### Padded hard-truth-table language in `Σ₃` -/

/-- Effective arity read from a padded word `y`: `min (unframe y).length (Nat.log 2 y.length)`. -/
def padArity (y : List Bool) : ℕ :=
  min (unframe y).length (Nat.log 2 y.length)

/-- Circuit-size threshold `2 ^ (padArity y / 2)` associated with a padded word `y`. -/
def padThreshold (y : List Bool) : ℕ :=
  2 ^ (padArity y / 2)

/-- Block length for truth tables in the `Σ₃` verifier for `paddedHardLang`. -/
def padTableBound (L : ℕ) : ℕ := L + 1

/-- Block length for circuit certificates in the `Σ₃` verifier for `paddedHardLang`. -/
def padCertBound (L : ℕ) : ℕ := certLength (L + 1) (L + 1)

/-- Truth table of length `2 ^ padArity y` extracted from the prefix of `w`. -/
def padTable (y w : List Bool) : List Bool :=
  w.take (2 ^ padArity y)

/-- A truth table `T` on `m` inputs whose Boolean function requires more than `2 ^ (m / 2)`
gates. -/
def IsHardAt (m : ℕ) (T : List Bool) : Prop :=
  T.length = 2 ^ m ∧
    2 ^ (m / 2) < complexity interpretation (single (MCSP.tableFunction m T))

/-- The lexicographically first hard truth table on `m` inputs (least in MSB-first binary value). -/
def IsFirstHardAt (m : ℕ) (T : List Bool) : Prop :=
  IsHardAt m T ∧ ∀ T', IsHardAt m T' → BitString.binaryValue T ≤ BitString.binaryValue T'

/-- Padded hard-truth-table language in `Σ₃`: on word `y`, take the first hard truth table `T`
on `m = padArity y` inputs (threshold `2 ^ (m / 2)`) and evaluate `T` on `(unframe y).take m`. -/
def paddedHardLang : Set (List Bool) :=
  {y | ∃ T, IsFirstHardAt (padArity y) T ∧
    MCSP.tableValue T ((unframe y).take (padArity y)) = true}

/-- Exponentially padded preimage of `paddedHardLang`, lying in `NEXP` whenever `PH ⊆ NP`. -/
def expHardLang : Language Bool :=
  (fun x : List Bool ↦ frame x ++ List.replicate (2 ^ x.length) true) ⁻¹' paddedHardLang

private theorem two_pow_padArity_le (y : List Bool) :
    2 ^ padArity y ≤ padTableBound y.length := by
  unfold padArity padTableBound
  rcases Nat.eq_zero_or_pos y.length with h0 | hpos
  · simp [h0]
  · calc
      2 ^ min (unframe y).length (Nat.log 2 y.length)
        ≤ 2 ^ Nat.log 2 y.length := Nat.pow_le_pow_right (by omega) (Nat.min_le_right _ _)
      _ ≤ y.length := Nat.pow_log_le_self 2 (Nat.ne_of_gt hpos)
      _ ≤ y.length + 1 := Nat.le_succ _

private theorem padArity_le_tableBound (y : List Bool) :
    padArity y ≤ y.length + 1 := by
  unfold padArity
  have h1 : Nat.log 2 y.length ≤ y.length := by
    rcases Nat.eq_zero_or_pos y.length with h0 | hpos
    · simp [h0]
    · exact (Nat.log_lt_self 2 (Nat.ne_of_gt hpos)).le
  exact (Nat.min_le_right _ _).trans (h1.trans (Nat.le_succ _))

private theorem padThreshold_le_tableBound (y : List Bool) :
    padThreshold y ≤ y.length + 1 := by
  unfold padThreshold
  exact (Nat.pow_le_pow_right (by omega) (Nat.div_le_self _ 2)).trans (two_pow_padArity_le y)

private theorem certLength_pad_le (y : List Bool) :
    certLength (padArity y) (MCSP.budget (padArity y) (padThreshold y)) ≤
      padCertBound y.length := by
  have hm := padArity_le_tableBound y
  have hs : MCSP.budget (padArity y) (padThreshold y) ≤ y.length + 1 :=
    (Nat.min_le_left _ _).trans (padThreshold_le_tableBound y)
  unfold padCertBound certLength
  gcongr

private theorem IsFirstHardAt.unique {m : ℕ} {T₁ T₂ : List Bool}
    (h₁ : IsFirstHardAt m T₁) (h₂ : IsFirstHardAt m T₂) : T₁ = T₂ :=
  BitString.binaryValue_injective_of_length_eq (h₁.1.1.trans h₂.1.1.symm)
    ((h₁.2 _ h₂.1).antisymm (h₂.2 _ h₁.1))

private theorem exists_isFirstHardAt {m : ℕ} (h : ∃ T, IsHardAt m T) :
    ∃ T, IsFirstHardAt m T := by
  classical
  have hex : ∃ v, ∃ T, IsHardAt m T ∧ BitString.binaryValue T = v :=
    let ⟨T, hT⟩ := h
    ⟨_, T, hT, rfl⟩
  obtain ⟨T, hT, hv⟩ := Nat.find_spec hex
  exact ⟨T, hT, fun T' hT' ↦ hv ▸ Nat.find_min' hex ⟨T', hT', rfl⟩⟩

private theorem padTable_length {y w : List Bool} (hw : 2 ^ padArity y ≤ w.length) :
    (padTable y w).length = 2 ^ padArity y := by
  rw [padTable, List.length_take, Nat.min_eq_left hw]

private theorem padTable_append {y T : List Bool} (hT : T.length = 2 ^ padArity y)
    (w : List Bool) : padTable y (T ++ w) = T := by
  rw [padTable, ← hT, List.take_left]

/-- `Σ₃` verifier for `paddedHardLang`. -/
def padVerifier (p : List Bool × List Bool) : Bool :=
  (!MCSP.tableVerifier ((padTable p.1 p.2, padThreshold p.1),
      p.2.drop (2 * padTableBound p.1.length)) &&
    (!decide (BitString.binaryValue (padTable p.1 (p.2.drop (padTableBound p.1.length))) <
        BitString.binaryValue (padTable p.1 p.2)) ||
      MCSP.tableVerifier ((padTable p.1 (p.2.drop (padTableBound p.1.length)),
        padThreshold p.1),
        p.2.drop (2 * padTableBound p.1.length + padCertBound p.1.length)))) &&
    MCSP.tableValue (padTable p.1 p.2) ((unframe p.1).take (padArity p.1))

private theorem padVerifier_append (y : List Bool) {w₁ w₂ : List Bool}
    (h₁ : w₁.length = padTableBound y.length)
    (h₂ : w₂.length = padTableBound y.length + padCertBound y.length) (w₃ : List Bool) :
    padVerifier (y, w₁ ++ (w₂ ++ w₃)) =
      ((!MCSP.tableVerifier ((padTable y w₁, padThreshold y),
          w₂.drop (padTableBound y.length) ++ w₃) &&
        (!decide (BitString.binaryValue (padTable y w₂) <
            BitString.binaryValue (padTable y w₁)) ||
          MCSP.tableVerifier ((padTable y w₂, padThreshold y), w₃))) &&
        MCSP.tableValue (padTable y w₁) ((unframe y).take (padArity y))) := by
  have hM := two_pow_padArity_le y
  have hw₁ : padTable y (w₁ ++ (w₂ ++ w₃)) = padTable y w₁ :=
    List.take_append_of_le_length (by rw [h₁]; exact hM)
  have hw₂ : padTable y ((w₁ ++ (w₂ ++ w₃)).drop (padTableBound y.length)) = padTable y w₂ := by
    rw [← h₁, List.drop_left]
    exact List.take_append_of_le_length (by rw [h₂]; exact hM.trans (Nat.le_add_right _ _))
  have hc : (w₁ ++ (w₂ ++ w₃)).drop (2 * padTableBound y.length) =
      w₂.drop (padTableBound y.length) ++ w₃ := by
    rw [Nat.two_mul, ← List.drop_drop, ← h₁, List.drop_left, h₁,
      List.drop_append_of_le_length (by rw [h₂]; exact Nat.le_add_right _ _)]
  have hc' : (w₁ ++ (w₂ ++ w₃)).drop (2 * padTableBound y.length + padCertBound y.length) = w₃ := by
    rw [← List.append_assoc]
    exact List.drop_left' (by rw [List.length_append, h₁, h₂]; ring)
  simp only [padVerifier, hw₁, hw₂, hc, hc']

private noncomputable def padTablePoly : Polynomial ℕ :=
  Polynomial.X + 1

private noncomputable def padCertPoly : Polynomial ℕ :=
  (Polynomial.X + 1) + ((Polynomial.X + 1) + (Polynomial.X + 1)) +
    (Polynomial.X + 1) * (3 + 2 * ((Polynomial.X + 1) + (Polynomial.X + 1)))

private theorem eval_padTablePoly (L : ℕ) : padTablePoly.eval L = padTableBound L := by
  simp [padTablePoly, padTableBound]

private theorem eval_padCertPoly (L : ℕ) : padCertPoly.eval L = padCertBound L := by
  simp [padCertPoly, padCertBound, certLength]

private theorem isAlternatingVerifier_padVerifier :
    IsAlternatingVerifier encBits true [padTablePoly, padTablePoly + padCertPoly, padCertPoly]
      padVerifier paddedHardLang := by
  intro y
  simp only [List.map_cons, List.map_nil, encBits_apply, Polynomial.eval_add, eval_padTablePoly,
    eval_padCertPoly, alternation_true_cons, alternation_false_cons, alternation_nil,
    List.append_nil]
  have hM : 2 ^ padArity y ≤ padTableBound y.length := two_pow_padArity_le y
  constructor
  · rintro ⟨T, hT, hval⟩
    refine ⟨T ++ List.replicate (padTableBound y.length - 2 ^ padArity y) false,
      by simp [hT.1.1]; omega, fun w₂ h₂ ↦ ?_⟩
    have hT' : (padTable y w₂).length = 2 ^ padArity y :=
      padTable_length (by rw [h₂]; exact hM.trans (Nat.le_add_right _ _))
    obtain ⟨w₃, h₃, hw₃⟩ : ∃ w₃ : List Bool, w₃.length = padCertBound y.length ∧
        (BitString.binaryValue (padTable y w₂) < BitString.binaryValue T →
          MCSP.tableVerifier ((padTable y w₂, padThreshold y), w₃) = true) := by
      by_cases hlt : BitString.binaryValue (padTable y w₂) < BitString.binaryValue T
      · have heasy : complexity interpretation
            (single (MCSP.tableFunction (padArity y) (padTable y w₂))) ≤ padThreshold y :=
          not_lt.1 fun h ↦ absurd (hT.2 _ ⟨hT', h⟩) (not_le.2 hlt)
        obtain ⟨u, hu, hV⟩ := MCSP.exists_tableVerifier_append hT' heasy
        refine ⟨u ++ List.replicate (padCertBound y.length - u.length) false, ?_, fun _ ↦ hV _⟩
        have := certLength_pad_le y
        simp only [List.length_append, List.length_replicate]
        omega
      · exact ⟨List.replicate (padCertBound y.length) false, by simp, fun h ↦ absurd h hlt⟩
    refine ⟨w₃, h₃, ?_⟩
    rw [padVerifier_append y (by simp [hT.1.1]; omega) h₂, padTable_append hT.1.1]
    simp only [Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_true, decide_eq_false_iff_not,
      not_lt]
    refine ⟨⟨?_, ?_⟩, hval⟩
    · cases hc : MCSP.tableVerifier ((T, padThreshold y),
        w₂.drop (padTableBound y.length) ++ w₃)
      · rfl
      · exact absurd (MCSP.complexity_le_of_tableVerifier hT.1.1 hc) (not_le.2 hT.1.2)
    · by_cases hlt : BitString.binaryValue (padTable y w₂) < BitString.binaryValue T
      · exact Or.inr (hw₃ hlt)
      · exact Or.inl (not_lt.1 hlt)
  · rintro ⟨w₁, h₁, h⟩
    have hT : (padTable y w₁).length = 2 ^ padArity y := padTable_length (by rw [h₁]; exact hM)
    have key (w₂ : List Bool) (h₂ : w₂.length = padTableBound y.length + padCertBound y.length) :
        ∃ w₃ : List Bool, w₃.length = padCertBound y.length ∧
          MCSP.tableVerifier ((padTable y w₁, padThreshold y),
            w₂.drop (padTableBound y.length) ++ w₃) = false ∧
          (BitString.binaryValue (padTable y w₂) < BitString.binaryValue (padTable y w₁) →
            MCSP.tableVerifier ((padTable y w₂, padThreshold y), w₃) = true) ∧
          MCSP.tableValue (padTable y w₁) ((unframe y).take (padArity y)) = true := by
      obtain ⟨w₃, h₃, hV⟩ := h w₂ h₂
      rw [padVerifier_append y h₁ h₂] at hV
      simp only [Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_true, decide_eq_false_iff_not,
        not_lt] at hV
      exact ⟨w₃, h₃, hV.1.1, fun hlt ↦ hV.1.2.resolve_left (not_le.2 hlt), hV.2⟩
    have hpad (u : List Bool) (hu : u.length ≤ padTableBound y.length + padCertBound y.length) :
        (u ++ List.replicate (padTableBound y.length + padCertBound y.length - u.length)
          false).length = padTableBound y.length + padCertBound y.length := by
      simp only [List.length_append, List.length_replicate]
      omega
    refine ⟨padTable y w₁, ⟨⟨hT, ?_⟩, fun T' hT' ↦ ?_⟩, ?_⟩
    · by_contra hle
      have hle' : complexity interpretation
          (single (MCSP.tableFunction (padArity y) (padTable y w₁))) ≤ padThreshold y :=
        not_lt.1 hle
      obtain ⟨u, hu, hV⟩ := MCSP.exists_tableVerifier_append hT hle'
      have hlen : (List.replicate (padTableBound y.length) false ++ u).length ≤
          padTableBound y.length + padCertBound y.length := by
        have := certLength_pad_le y
        simp only [List.length_append, List.length_replicate]
        omega
      obtain ⟨w₃, -, hw, -⟩ := key _ (hpad _ hlen)
      rw [List.append_assoc, List.drop_left' (by simp), List.append_assoc, hV] at hw
      exact Bool.noConfusion hw
    · by_contra hlt
      have hlen : T'.length ≤ padTableBound y.length + padCertBound y.length := by
        rw [hT'.1]
        exact hM.trans (Nat.le_add_right _ _)
      obtain ⟨w₃, -, -, hw, -⟩ := key _ (hpad _ hlen)
      rw [padTable_append hT'.1] at hw
      exact absurd (MCSP.complexity_le_of_tableVerifier hT'.1 (hw (not_le.1 hlt)))
        (not_le.2 hT'.2)
    · obtain ⟨w₃, -, -, -, hw⟩ := key _ (hpad [] (Nat.zero_le _))
      exact hw

attribute [local irreducible] ComputableInPolyTime

open ComputableInPolyTime in
private theorem computableInPolyTime_padVerifier :
    ComputableInPolyTime padVerifier (encPair encBits encBits) encBool := by
  have hy := fst encBits encBits
  have hw := snd encBits encBits
  have hunf : ComputableInPolyTime (fun p : List Bool × List Bool ↦ unframe p.1)
      (encPair encBits encBits) encBits :=
    unframe.comp hy
  have hm : ComputableInPolyTime (fun p : List Bool × List Bool ↦ padArity p.1)
      (encPair encBits encBits) encUnary :=
    unary_min' (length_bits.comp hunf) (by fun_prop)
  have htb : ComputableInPolyTime (fun p : List Bool × List Bool ↦ padTableBound p.1.length)
      (encPair encBits encBits) encUnary := by
    unfold padTableBound
    fun_prop
  have hcb : ComputableInPolyTime (fun p : List Bool × List Bool ↦ padCertBound p.1.length)
      (encPair encBits encBits) encUnary := by
    unfold padCertBound certLength
    fun_prop
  have hs : ComputableInPolyTime (fun p : List Bool × List Bool ↦ padThreshold p.1)
      (encPair encBits encBits) encNat :=
    binary_two_pow.comp ((unary_div_const 2).comp hm)
  have hM := binary_to_unary_bounded (binary_two_pow.comp hm) htb fun p ↦ two_pow_padArity_le p.1
  have hT := bitsTakeWithInput hw hM
  have hT' := bitsTakeWithInput (bitsDropWithInput hw htb) hM
  have hc := bitsDropWithInput hw
    (show ComputableInPolyTime (fun p : List Bool × List Bool ↦ 2 * padTableBound p.1.length)
      (encPair encBits encBits) encUnary by unfold padTableBound; fun_prop)
  have hc' := bitsDropWithInput hw
    (show ComputableInPolyTime
      (fun p : List Bool × List Bool ↦ 2 * padTableBound p.1.length + padCertBound p.1.length)
      (encPair encBits encBits) encUnary by unfold padTableBound padCertBound certLength; fun_prop)
  have hval := MCSP.computableInPolyTime_tableValue.comp (hT.prod (bitsTakeWithInput hunf hm))
  unfold padVerifier
  have hnotVerifier := bool_not.comp'
    (MCSP.computableInPolyTime_tableVerifier.comp' ((hT.prod hs).prod hc))
  have hlt := bool_not.comp' (binary_lt' (bitsBinaryValue.comp' hT') (bitsBinaryValue.comp' hT))
  have hverifier' := MCSP.computableInPolyTime_tableVerifier.comp' ((hT'.prod hs).prod hc')
  exact bool_and' (bool_and' hnotVerifier (bool_or' hlt hverifier')) hval

/-- `paddedHardLang` belongs to `Σ₃ ⊆ PH`. -/
theorem paddedHardLang_mem_SigmaP_three :
    paddedHardLang ∈ SigmaP 3 encBits :=
  ⟨_, padVerifier, rfl, computableInPolyTime_padVerifier, isAlternatingVerifier_padVerifier⟩

/-! ### Exponential separation from `P/poly` under `PH ⊆ NP` -/

private theorem n_lt_two_pow_sub_half (n : ℕ) (hn : 12 ≤ n) :
    n < 2 ^ (n - n / 2) := by
  have hge : 6 ≤ n - n / 2 := by omega
  have h2k : ∀ k : ℕ, 6 ≤ k → 2 * k < 2 ^ k := by
    intro k hk
    induction k with
    | zero => omega
    | succ k ih =>
      by_cases hk6 : 6 ≤ k
      · have hprev := ih hk6
        rw [pow_succ]
        omega
      · have : k = 5 := by omega
        subst this
        norm_num
  have h := h2k (n - n / 2) hge
  omega

private theorem exists_isHardAt_of_ge (N : ℕ)
    (hN : ∀ n ≥ N, ∃ f : BooleanFunction n,
      (2 ^ n : ℝ) / n < complexity interpretation (single f))
    {n : ℕ} (hnN : N ≤ n) (hn12 : 12 ≤ n) :
    ∃ T, IsHardAt n T := by
  obtain ⟨f, hf⟩ := hN n hnN
  refine ⟨List.ofFn (MCSP.truthTable n f), by simp, ?_⟩
  rw [MCSP.tableFunction_ofFn_truthTable]
  have hn0 : (0 : ℝ) < n := by positivity
  have hmul : 2 ^ (n / 2) * n < 2 ^ n := by
    calc
      2 ^ (n / 2) * n < 2 ^ (n / 2) * 2 ^ (n - n / 2) :=
        Nat.mul_lt_mul_of_pos_left (n_lt_two_pow_sub_half n hn12) (Nat.two_pow_pos _)
      _ = 2 ^ n := by rw [← pow_add, Nat.add_sub_of_le (Nat.div_le_self n 2)]
  have hdiv : ((2 ^ (n / 2) : ℕ) : ℝ) < (2 ^ n : ℝ) / n := by
    rw [lt_div_iff₀ hn0]
    exact_mod_cast hmul
  exact_mod_cast hdiv.trans hf

private theorem exists_poly_le_two_pow_half (c M : ℕ) :
    ∃ n ≥ M, c * (n + 1) ^ c ≤ 2 ^ (n / 2) := by
  let d := c + 1
  let K := 3 ^ d * d.factorial
  have hK_pos : 0 < K := by positivity
  let t := max (2 * d) (max M (c * 3 ^ c * K + 2))
  have ht_ge_2d : 2 * d ≤ t := le_max_left _ _
  have ht_ge_M : M ≤ t := (le_max_left _ _).trans (le_max_right _ _)
  have ht_ge_big : c * 3 ^ c * K + 2 ≤ t := (le_max_right _ _).trans (le_max_right _ _)
  have ht_pos : 1 ≤ t := by omega
  have hchoose_le : t.choose d ≤ 2 ^ t := by
    rw [← Nat.sum_range_choose t]
    exact Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_range.mpr (by omega))
  have hdesc_ge : (t / 2) ^ d ≤ t.descFactorial d := by
    have haux : ∀ k ≤ d, (t / 2) ^ k ≤ t.descFactorial k := by
      intro k
      induction k with
      | zero => intro _; simp
      | succ k ih =>
        intro hk
        rw [pow_succ', Nat.descFactorial_succ]
        have hstep : t / 2 ≤ t - k := by omega
        exact Nat.mul_le_mul hstep (ih (by omega))
    exact haux d le_rfl
  have hpow_half : (t / 2) ^ d ≤ d.factorial * 2 ^ t := by
    calc
      (t / 2) ^ d ≤ t.descFactorial d := hdesc_ge
      _ = d.factorial * t.choose d := Nat.descFactorial_eq_factorial_mul_choose t d
      _ ≤ d.factorial * 2 ^ t := Nat.mul_le_mul_left _ hchoose_le
  have ht_le_3half : t ≤ 3 * (t / 2) := by omega
  have ht_pow_le : t ^ d ≤ K * 2 ^ t := by
    calc
      t ^ d ≤ (3 * (t / 2)) ^ d := Nat.pow_le_pow_left ht_le_3half d
      _ = 3 ^ d * (t / 2) ^ d := Nat.mul_pow 3 (t / 2) d
      _ ≤ 3 ^ d * (d.factorial * 2 ^ t) := Nat.mul_le_mul_left _ hpow_half
      _ = K * 2 ^ t := by ring
  refine ⟨2 * t, by omega, ?_⟩
  have hhalf : 2 * t / 2 = t := by omega
  rw [hhalf]
  have h3t : 2 * t + 1 ≤ 3 * t := by omega
  have h1 : c * (2 * t + 1) ^ c ≤ c * 3 ^ c * t ^ c := by
    calc
      c * (2 * t + 1) ^ c ≤ c * (3 * t) ^ c := Nat.mul_le_mul_left c (Nat.pow_le_pow_left h3t c)
      _ = c * 3 ^ c * t ^ c := by rw [Nat.mul_pow]; ring
  have h2 : K * (c * 3 ^ c * t ^ c) ≤ K * 2 ^ t := by
    calc
      K * (c * 3 ^ c * t ^ c) = (c * 3 ^ c * K) * t ^ c := by ring
      _ ≤ t * t ^ c := Nat.mul_le_mul_right _ (by omega)
      _ = t ^ d := by rw [pow_succ']
      _ ≤ K * 2 ^ t := ht_pow_le
  exact h1.trans (Nat.le_of_mul_le_mul_left h2 hK_pos)

private theorem padArity_expPad (x : List Bool) :
    padArity (frame x ++ List.replicate (2 ^ x.length) true) = x.length := by
  unfold padArity
  rw [unframe_frame_append]
  have hlen : 2 ^ x.length ≤ (frame x ++ List.replicate (2 ^ x.length) true).length := by
    simp
  have hlog : x.length ≤ Nat.log 2 (frame x ++ List.replicate (2 ^ x.length) true).length :=
    (Nat.le_log_iff_pow_le (by norm_num) (by
      have := Nat.two_pow_pos x.length; omega)).mpr hlen
  exact Nat.min_eq_left hlog

private theorem slice_expHardLang {n : ℕ} {T : List Bool} (hT : IsFirstHardAt n T) :
    expHardLang.slice n = MCSP.tableFunction n T := by
  funext x
  rw [Bool.eq_iff_iff, Language.slice_eq_true_iff]
  change (frame (List.ofFn x) ++ List.replicate (2 ^ (List.ofFn x).length) true) ∈
      paddedHardLang ↔ MCSP.tableFunction n T x = true
  unfold paddedHardLang
  rw [Set.mem_ofPred_eq, padArity_expPad, unframe_frame_append, List.take_length, List.length_ofFn]
  change (∃ T', IsFirstHardAt n T' ∧ MCSP.tableValue T' (List.ofFn x) = true) ↔
    MCSP.tableValue T (List.ofFn x) = true
  exact ⟨fun ⟨T', hT', h⟩ ↦ hT.unique hT' ▸ h, fun h ↦ ⟨T, hT, h⟩⟩

/-- `expHardLang` does not have polynomial-size Boolean circuits (`expHardLang ∉ P/poly`). -/
theorem expHardLang_notMem_PPolyOn :
    (expHardLang : Set (List Bool)) ∉ PPolyOn encBits := by
  intro hP
  obtain ⟨L, hLP, hEq⟩ := mem_PPolyOn.mp hP
  have hL_eq : L = expHardLang := Set.ext fun a ↦ (hEq a).symm
  subst hL_eq
  obtain ⟨c, hc⟩ := mem_PPoly_iff_exists_mem_SIZE.mp hLP
  obtain ⟨N, hN⟩ := Shannon.lt_complexity
  obtain ⟨n, hn, hpoly_le⟩ := exists_poly_le_two_pow_half c (max N 12)
  obtain ⟨T₀, hT₀⟩ := exists_isHardAt_of_ge N hN ((le_max_left _ _).trans hn)
    ((le_max_right _ _).trans hn)
  obtain ⟨T, hT⟩ := exists_isFirstHardAt ⟨T₀, hT₀⟩
  have hslice := slice_expHardLang hT
  have hgt : 2 ^ (n / 2) < complexity interpretation (single (expHardLang.slice n)) := by
    rw [hslice]
    exact hT.1.2
  have hle : complexity interpretation (single (expHardLang.slice n)) ≤ c * (n + 1) ^ c := hc n
  omega

/-- Structural complexity collapse theorem: if `PH ⊆ NP`, then `NEXP ⊄ P/poly`. -/
theorem not_NEXP_subset_PPoly_of_PH_subset_NP
    (hPH : PH encBits ⊆ NP encBits) :
    ¬ (NEXP encBits ⊆ PPolyOn encBits) := by
  intro hsub
  have hpad_NP : paddedHardLang ∈ NP encBits :=
    hPH (mem_PH.mpr ⟨3, paddedHardLang_mem_SigmaP_three⟩)
  have hexp_NEXP : (expHardLang : Set (List Bool)) ∈ NEXP encBits :=
    preimage_pad_mem_NEXP (enc := encBits) (f := id) hpad_NP (by fun_prop) (fun _ ↦ le_rfl)
  exact expHardLang_notMem_PPolyOn (hsub hexp_NEXP)

/-! ### From `ZeroOnePermanent ∈ NP ∩ coNP` to `PH ⊆ NP` -/

/-- If the bit graph of `ZeroOnePermanent` lies in `NP ∩ coNP`, then `PH ⊆ NP`. -/
theorem PH_subset_NP_of_zeroOnePermanent_mem_NP_inter_coNP
    (hNP : bitGraph encBoolTable ZeroOnePermanent ∈ NP encBits)
    (hcoNP : bitGraph encBoolTable ZeroOnePermanent ∈ coNP encBits) :
    PH encBits ⊆ NP encBits := by
  intro L hL
  have hBP : L ∈ BPOp encBits (ParityP (encPair encBits encBits)) := PH_subset_BPOp_ParityP hL
  obtain ⟨f, hf, p, hL_iff⟩ := exists_SharpP_testBit_of_mem_BPOp_ParityP hBP
  have horacle : ComputableInPolyTimeWithOracle (bitGraph encBoolTable ZeroOnePermanent)
      f encBits encNat :=
    zeroOnePermanent_computableInPolyTimeWithOracle hf
  let P : List Bool × List Bool → Bool := fun x ↦
    let y := Decoder.nat.decode x.2
    y.testBit (min y.size (p.eval x.1.length))
  have hP : ComputableInPolyTime P (encPair encBits encBits) encBool := by
    have hdec : ComputableInPolyTime (fun x : List Bool × List Bool ↦ Decoder.nat.decode x.2)
        (encPair encBits encBits) encNat :=
      Decoder.nat.computableInPolyTime.comp (ComputableInPolyTime.snd encBits encBits)
    have hsize :
        ComputableInPolyTime (fun x : List Bool × List Bool ↦ (Decoder.nat.decode x.2).size)
          (encPair encBits encBits) encUnary := by
      have hbits := (ComputableInPolyTime.of_eq (encIn := encNat) (encOut := encBits)
        (f := Nat.bits) fun _ ↦ rfl).comp hdec
      simpa only [Function.comp_def, Nat.size_eq_bits_len] using
        ComputableInPolyTime.length_bits_comp hbits
    have hp : ComputableInPolyTime (fun x : List Bool × List Bool ↦ p.eval x.1.length)
        (encPair encBits encBits) encUnary := by
      have hlen : ComputableInPolyTime (fun x : List Bool × List Bool ↦ x.1.length)
          (encPair encBits encBits) encUnary :=
        ComputableInPolyTime.length_bits.comp (ComputableInPolyTime.fst encBits encBits)
      exact (ComputableInPolyTime.unary_eval p).comp hlen
    have hidx : ComputableInPolyTime
        (fun x : List Bool × List Bool ↦ min (Decoder.nat.decode x.2).size (p.eval x.1.length))
        (encPair encBits encBits) encUnary :=
      ComputableInPolyTime.unary_min' hsize hp
    exact ComputableInPolyTime.binary_testBit hdec hidx
  have hmem := horacle.encoded_mem_NP hNP hcoNP hP
  have hset : {a : List Bool | P (a, encNat (f a)) = true} = L := by
    ext a
    simp only [Set.mem_ofPred_eq, P, Decoder.decode_enc]
    have hmin : (f a).testBit (min (f a).size (p.eval a.length)) =
        (f a).testBit (p.eval a.length) := by
      rcases le_total (p.eval a.length) (f a).size with hle | hle
      · rw [min_eq_right hle]
      · rw [min_eq_left hle, Nat.testBit_eq_false_of_lt (Nat.lt_size_self (f a)),
          Nat.testBit_eq_false_of_lt ((Nat.lt_size_self (f a)).trans_le
            (Nat.pow_le_pow_right two_pos hle))]
    rw [hmin]
    exact (hL_iff a).symm
  rwa [hset] at hmem

/-- Corollary: if the bit graph of `ZeroOnePermanent` lies in `NP ∩ coNP`, then
`NEXP ⊄ P/poly`. -/
theorem not_NEXP_subset_PPoly_of_zeroOnePermanent_mem_NP_inter_coNP
    (hNP : bitGraph encBoolTable ZeroOnePermanent ∈ NP encBits)
    (hcoNP : bitGraph encBoolTable ZeroOnePermanent ∈ coNP encBits) :
    ¬ (NEXP encBits ⊆ PPolyOn encBits) :=
  not_NEXP_subset_PPoly_of_PH_subset_NP
    (PH_subset_NP_of_zeroOnePermanent_mem_NP_inter_coNP hNP hcoNP)

end CslibFrontier.Complexity
