module

public import CslibFrontier.Computability.Complexity.Classes.Oracle
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Unary
import CslibFrontier.Computability.Complexity.Classes.NP
import CslibFrontier.Computability.Complexity.Classes.Oracle.Closure
import CslibFrontier.Computability.Complexity.Classes.Oracle.Lowness
import CslibFrontier.Computability.Complexity.Classes.Oracle.Substitution
import CslibFrontier.Computability.Complexity.Classes.Oracle.Function
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder.Partial
import CslibFrontier.Computability.Probabilistic.Oracle.Composition
import Cslib.Foundations.Data.Polynomial.Monotone

/-!
# Brute-force prefix-search uniformity for nonuniform families

Formalizes the general brute-force prefix-search uniformity construction: if a language `A` admits
polynomial-length valid descriptions (for any polynomial-time syntax/resource checker `check` and
polynomial-time evaluator `eval`), then a valid description for each input length `n` can be
generated in `FP^{NP^{coNP^A}}` (equivalently `FP^{NP^{NP^A}}`) via bit-by-bit lexicographic
prefix search.

## Main definitions

* `CslibFrontier.Complexity.correctOracle`: the `coNP^A` oracle testing whether `(n, w)` encodes
  a valid description agreeing with `A` on all `n`-bit inputs.
* `CslibFrontier.Complexity.prefixOracle`: the `NP^{coNP^A}` oracle supporting exact membership
  and prefix-extension queries for bounded-length descriptions in `correctOracle`.

## Main results

* `CslibFrontier.Complexity.compl_correctOracle_mem_NPWithOracle`:
  `(correctOracle A check eval)ᶜ ∈ NPWithOracle A encBits`.
* `CslibFrontier.Complexity.prefixOracle_mem_NPWithOracle_correctOracle`:
  `prefixOracle A check eval p ∈ NPWithOracle (correctOracle A check eval) encBits`.
* `CslibFrontier.Complexity.exists_FP_NP_coNP_uniform_of_nonuniform`,
  `CslibFrontier.Complexity.exists_FP_NP_NP_uniform_of_nonuniform`: general brute-force
  `FP^{NP^{coNP^A}}` and `FP^{NP^{NP^A}}` uniformity from nonuniform existence.
-/

public section

namespace CslibFrontier.Complexity

open Cslib Cslib.Complexity Cslib.Probability Turing.MultiTapeTM

/-! ### Auxiliary helpers -/

private theorem polynomial_eval_mono {p : Polynomial ℕ} {a b : ℕ} (hab : a ≤ b) :
    p.eval a ≤ p.eval b := by
  rw [Polynomial.eval_eq_sum_range, Polynomial.eval_eq_sum_range]
  refine Finset.sum_le_sum fun i _ ↦ ?_
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hab i)

private def decNW : PartialDecoder (encPair encUnary encBits) :=
  PartialDecoder.pair (PartialDecoder.ofDecoder Decoder.unary)
    (PartialDecoder.ofDecoder Decoder.bits)

/-! ### The `coNP^A` correctness oracle -/

/-- The `coNP^A` correctness oracle: contains `encPair encUnary encBits (n, w)` precisely when
`check (n, w) = true` and `eval (w, x)` decides `A` on all inputs `x` of length `n`. -/
def correctOracle (A : Set (List Bool)) (check : ℕ × List Bool → Bool)
    (eval : List Bool × List Bool → Bool) : Set (List Bool) :=
  {raw | ∃ n w, encPair encUnary encBits (n, w) = raw ∧ check (n, w) = true ∧
    ∀ x : List Bool, x.length = n → (eval (w, x) = true ↔ x ∈ A)}

/-- Characterization of `correctOracle` on encoded pairs `(n, w)`. -/
theorem encPair_mem_correctOracle_iff {A : Set (List Bool)} {check : ℕ × List Bool → Bool}
    {eval : List Bool × List Bool → Bool} {n : ℕ} {w : List Bool} :
    encPair encUnary encBits (n, w) ∈ correctOracle A check eval ↔
      check (n, w) = true ∧ ∀ x : List Bool, x.length = n → (eval (w, x) = true ↔ x ∈ A) := by
  constructor
  · rintro ⟨n', w', heq, hchk, heval⟩
    have hp : (n', w') = (n, w) := (encPair encUnary encBits).injective heq
    cases hp
    exact ⟨hchk, heval⟩
  · rintro ⟨hchk, heval⟩
    exact ⟨n, w, rfl, hchk, heval⟩

/-- **`(correctOracle A check eval)ᶜ ∈ NP^A`** (`correctOracle ∈ coNP^A`) whenever `check` and
`eval` are polynomial-time. -/
theorem compl_correctOracle_mem_NPWithOracle (A : Set (List Bool))
    {check : ℕ × List Bool → Bool} {eval : List Bool × List Bool → Bool}
    (hcheck : ComputableInPolyTime check (encPair encUnary encBits) encBool)
    (heval : ComputableInPolyTime eval (encPair encBits encBits) encBool) :
    (correctOracle A check eval)ᶜ ∈ NPWithOracle A encBits := by
  classical
  let queryWord (rx : List Bool × List Bool) : List Bool :=
    (decNW.decode rx.1).elim [] fun nw ↦ rx.2.take nw.1
  let combine (rxa : (List Bool × List Bool) × Bool) : Bool :=
    (decNW.decode rxa.1.1).elim true fun nw ↦
      !(check nw) || decide (eval (nw.2, rxa.1.2.take nw.1) ≠ rxa.2)
  let V (rx : List Bool × List Bool) : Bool := combine (rx, decide (queryWord rx ∈ A))
  have hquery : ComputableInPolyTime queryWord (encPair encBits encBits) encBits := by
    dsimp only [queryWord]
    refine (decNW.computable.comp (ComputableInPolyTime.fst _ _)).optionElimWithInput
      (ComputableInPolyTime.const []) ?_
    exact ComputableInPolyTime.bitsTakeWithInput
      ((ComputableInPolyTime.fst _ _).snd') ((ComputableInPolyTime.snd _ _).fst')
  have hcombine : ComputableInPolyTime combine
      (encPair (encPair encBits encBits) encBool) encBool := by
    dsimp only [combine]
    refine (decNW.computable.comp
      ((ComputableInPolyTime.fst _ _).fst')).optionElimWithInput
      (ComputableInPolyTime.const true) ?_
    let encT := encPair (encPair (encPair encBits encBits) encBool) (encPair encUnary encBits)
    have hnw : ComputableInPolyTime
        (fun t : ((List Bool × List Bool) × Bool) × (ℕ × List Bool) ↦ t.2)
        encT (encPair encUnary encBits) := ComputableInPolyTime.snd _ _
    have hx : ComputableInPolyTime
        (fun t : ((List Bool × List Bool) × Bool) × (ℕ × List Bool) ↦ t.1.1.2.take t.2.1)
        encT encBits :=
      ComputableInPolyTime.bitsTakeWithInput
        (((ComputableInPolyTime.fst _ _).fst').snd') hnw.fst'
    have hans : ComputableInPolyTime
        (fun t : ((List Bool × List Bool) × Bool) × (ℕ × List Bool) ↦ t.1.2)
        encT encBool := (ComputableInPolyTime.fst _ _).snd'
    have hchk : ComputableInPolyTime
        (fun t : ((List Bool × List Bool) × Bool) × (ℕ × List Bool) ↦ !(check t.2))
        encT encBool := ComputableInPolyTime.bool_not.comp (hcheck.comp hnw)
    have hneq : ComputableInPolyTime
        (fun t : ((List Bool × List Bool) × Bool) × (ℕ × List Bool) ↦
          decide (eval (t.2.2, t.1.1.2.take t.2.1) ≠ t.1.2))
        encT encBool :=
      (ComputableInPolyTime.bool_not.comp
        (ComputableInPolyTime.decide_eq' (heval.comp (hnw.snd'.prod hx)) hans)).of_enc_eq
        fun t ↦ by simp
    exact ComputableInPolyTime.bool_or' hchk hneq
  have hV : ComputableInPolyTimeWithOracle A V (encPair encBits encBits) encBool :=
    (hcombine.computableInPolyTimeWithOracle A).comp_with
      ((computableInPolyTimeWithOracle_mem A).preprocess hquery)
  refine ⟨Polynomial.X, V, hV, IsVerifier.of_padding (fun raw xc hlen hVt ↦ ?_) (fun raw hnot ↦ ?_)⟩
  · intro hmem
    obtain ⟨n, w, hraw, hchk, hspec⟩ := hmem
    have hdec : decNW.decode raw = some (n, w) := by
      rw [← hraw]
      exact decNW.decode_enc (n, w)
    have hn_le : n ≤ raw.length := by
      rw [← hraw, length_encPair, encUnary_apply, List.length_replicate]
      omega
    have hx_len : (xc.take n).length = n := by
      rw [List.length_take]
      simp only [Polynomial.eval_X, encBits_apply] at hlen
      omega
    have hiff := hspec (xc.take n) hx_len
    simp only [V, combine, queryWord, hdec, Option.elim_some, hchk, Bool.not_true, Bool.false_or,
      decide_eq_true_eq] at hVt
    apply hVt
    cases h : eval (w, xc.take n) with
    | false =>
      rw [h] at hiff
      simp only [Bool.false_eq_true, false_iff] at hiff
      simp [hiff]
    | true =>
      rw [h] at hiff
      simp only [true_iff] at hiff
      simp [hiff]
  · cases hdec : decNW.decode raw with
    | none =>
      refine ⟨[], by simp, fun k ↦ ?_⟩
      simp [V, combine, hdec]
    | some nw =>
      rcases nw with ⟨n, w⟩
      have hraw := (decNW.decode_eq_some_iff raw (n, w)).mp hdec
      have hn_le : n ≤ raw.length := by
        rw [← hraw, length_encPair, encUnary_apply, List.length_replicate]
        omega
      by_cases hchk : check (n, w) = true
      · have hbad : ∃ x : List Bool, x.length = n ∧ ¬(eval (w, x) = true ↔ x ∈ A) := by
          by_contra hall
          push Not at hall
          exact hnot ⟨n, w, hraw, hchk, hall⟩
        obtain ⟨x, hxlen, hneq⟩ := hbad
        refine ⟨x, by simp [hxlen, hn_le], fun k ↦ ?_⟩
        have htake : (x ++ List.replicate k false).take n = x := List.take_left' hxlen
        simp only [V, combine, queryWord, hdec, Option.elim_some, htake, Bool.or_eq_true,
          decide_eq_true_eq]
        right
        intro heq
        apply hneq
        rw [heq, decide_eq_true_eq]
      · refine ⟨[], by simp, fun k ↦ ?_⟩
        simp only [V, combine, queryWord, hdec, Option.elim_some, Bool.or_eq_true,
          Bool.not_eq_true']
        left
        cases h : check (n, w)
        · rfl
        · exact absurd h hchk

/-! ### The `NP^{coNP^A}` prefix-extension oracle -/

/-- The `NP^{coNP^A}` oracle answering exact-validity queries (`false :: (n, α)`) and
bounded-length prefix-extension queries (`true :: (n, α)`) against `correctOracle A check eval`. -/
def prefixOracle (A : Set (List Bool)) (check : ℕ × List Bool → Bool)
    (eval : List Bool × List Bool → Bool) (p : Polynomial ℕ) : Set (List Bool) :=
  {raw | ∃ (tag : Bool) (n : ℕ) (α : List Bool),
    tag :: encPair encUnary encBits (n, α) = raw ∧
    if tag then
      ∃ β : List Bool, α.length + β.length ≤ p.eval n ∧
        encPair encUnary encBits (n, α ++ β) ∈ correctOracle A check eval
    else
      encPair encUnary encBits (n, α) ∈ correctOracle A check eval}

private theorem mem_prefixOracle_false_iff {A : Set (List Bool)}
    {check : ℕ × List Bool → Bool} {eval : List Bool × List Bool → Bool} {p : Polynomial ℕ}
    {n : ℕ} {α : List Bool} :
    false :: encPair encUnary encBits (n, α) ∈ prefixOracle A check eval p ↔
      encPair encUnary encBits (n, α) ∈ correctOracle A check eval := by
  constructor
  · rintro ⟨tag, n', α', heq, hbody⟩
    have htag : tag = false := List.cons.inj heq |>.1
    have hp : (n', α') = (n, α) := (encPair encUnary encBits).injective (List.cons.inj heq |>.2)
    subst htag
    cases hp
    simpa using hbody
  · intro h
    exact ⟨false, n, α, rfl, h⟩

private theorem mem_prefixOracle_true_iff {A : Set (List Bool)}
    {check : ℕ × List Bool → Bool} {eval : List Bool × List Bool → Bool} {p : Polynomial ℕ}
    {n : ℕ} {α : List Bool} :
    true :: encPair encUnary encBits (n, α) ∈ prefixOracle A check eval p ↔
      ∃ β : List Bool, α.length + β.length ≤ p.eval n ∧
        encPair encUnary encBits (n, α ++ β) ∈ correctOracle A check eval := by
  constructor
  · rintro ⟨tag, n', α', heq, hbody⟩
    have htag : tag = true := List.cons.inj heq |>.1
    have hp : (n', α') = (n, α) := (encPair encUnary encBits).injective (List.cons.inj heq |>.2)
    subst htag
    cases hp
    simpa using hbody
  · intro h
    exact ⟨true, n, α, rfl, h⟩

/-- **`prefixOracle A check eval p ∈ NP^{correctOracle A check eval}`.** -/
theorem prefixOracle_mem_NPWithOracle_correctOracle (A : Set (List Bool))
    (check : ℕ × List Bool → Bool) (eval : List Bool × List Bool → Bool) (p : Polynomial ℕ) :
    prefixOracle A check eval p ∈ NPWithOracle (correctOracle A check eval) encBits := by
  classical
  let C := correctOracle A check eval
  let queryPref (rc : List Bool × List Bool) : List Bool :=
    if rc.1.isEmpty then []
    else
      (decNW.decode rc.1.tail).elim [] fun nα ↦
        if rc.1.headD false then
          encPair encUnary encBits (nα.1, nα.2 ++ unframe rc.2)
        else
          encPair encUnary encBits nα
  let combinePref (rca : (List Bool × List Bool) × Bool) : Bool :=
    if rca.1.1.isEmpty then false
    else
      (decNW.decode rca.1.1.tail).elim false fun nα ↦
        if rca.1.1.headD false then
          decide (nα.2.length + (unframe rca.1.2).length ≤ p.eval nα.1) && rca.2
        else
          rca.2
  let V (rc : List Bool × List Bool) : Bool := combinePref (rc, decide (queryPref rc ∈ C))
  have hquery : ComputableInPolyTime queryPref (encPair encBits encBits) encBits := by
    dsimp only [queryPref]
    have hraw : ComputableInPolyTime (fun rc : List Bool × List Bool ↦ rc.1)
        (encPair encBits encBits) encBits := ComputableInPolyTime.fst _ _
    have htail : ComputableInPolyTime (fun rc : List Bool × List Bool ↦ rc.1.tail)
        (encPair encBits encBits) encBits := ComputableInPolyTime.bitsTail.comp hraw
    refine ComputableInPolyTime.ite' (ComputableInPolyTime.bitsIsEmpty.comp hraw)
      (ComputableInPolyTime.const []) ?_
    refine (decNW.computable.comp htail).optionElimWithInput (ComputableInPolyTime.const []) ?_
    let encT := encPair (encPair encBits encBits) (encPair encUnary encBits)
    have hraw' : ComputableInPolyTime
        (fun t : (List Bool × List Bool) × (ℕ × List Bool) ↦ t.1.1) encT encBits :=
      (ComputableInPolyTime.fst _ _).fst'
    have hcert' : ComputableInPolyTime
        (fun t : (List Bool × List Bool) × (ℕ × List Bool) ↦ t.1.2) encT encBits :=
      (ComputableInPolyTime.fst _ _).snd'
    have hnα : ComputableInPolyTime
        (fun t : (List Bool × List Bool) × (ℕ × List Bool) ↦ t.2) encT (encPair encUnary encBits) :=
      ComputableInPolyTime.snd _ _
    have htrue : ComputableInPolyTime
        (fun t : (List Bool × List Bool) × (ℕ × List Bool) ↦
          encPair encUnary encBits (t.2.1, t.2.2 ++ unframe t.1.2)) encT encBits :=
      (ComputableInPolyTime.of_eq (f := encPair encUnary encBits) fun _ ↦ rfl).comp
        (hnα.fst'.prod
          (ComputableInPolyTime.bitsAppend hnα.snd' (ComputableInPolyTime.unframe.comp hcert')))
    have hfalse : ComputableInPolyTime
        (fun t : (List Bool × List Bool) × (ℕ × List Bool) ↦ encPair encUnary encBits t.2)
        encT encBits :=
      (ComputableInPolyTime.of_eq (f := encPair encUnary encBits) fun _ ↦ rfl).comp hnα
    exact ComputableInPolyTime.ite'
      ((ComputableInPolyTime.headD (encA := encBool) (encL := encBits) false).comp hraw')
      htrue hfalse
  have hcombine : ComputableInPolyTime combinePref
      (encPair (encPair encBits encBits) encBool) encBool := by
    dsimp only [combinePref]
    have hraw : ComputableInPolyTime (fun rca : (List Bool × List Bool) × Bool ↦ rca.1.1)
        (encPair (encPair encBits encBits) encBool) encBits := (ComputableInPolyTime.fst _ _).fst'
    have htail : ComputableInPolyTime (fun rca : (List Bool × List Bool) × Bool ↦ rca.1.1.tail)
        (encPair (encPair encBits encBits) encBool) encBits :=
      ComputableInPolyTime.bitsTail.comp hraw
    refine ComputableInPolyTime.ite' (ComputableInPolyTime.bitsIsEmpty.comp hraw)
      (ComputableInPolyTime.const false) ?_
    refine (decNW.computable.comp htail).optionElimWithInput
      (ComputableInPolyTime.const false) ?_
    let encT := encPair (encPair (encPair encBits encBits) encBool) (encPair encUnary encBits)
    have hraw' : ComputableInPolyTime
        (fun t : ((List Bool × List Bool) × Bool) × (ℕ × List Bool) ↦ t.1.1.1) encT encBits :=
      ((ComputableInPolyTime.fst _ _).fst').fst'
    have hcert' : ComputableInPolyTime
        (fun t : ((List Bool × List Bool) × Bool) × (ℕ × List Bool) ↦ t.1.1.2) encT encBits :=
      ((ComputableInPolyTime.fst _ _).fst').snd'
    have hans : ComputableInPolyTime
        (fun t : ((List Bool × List Bool) × Bool) × (ℕ × List Bool) ↦ t.1.2) encT encBool :=
      (ComputableInPolyTime.fst _ _).snd'
    have hnα : ComputableInPolyTime
        (fun t : ((List Bool × List Bool) × Bool) × (ℕ × List Bool) ↦ t.2)
        encT (encPair encUnary encBits) := ComputableInPolyTime.snd _ _
    have hlen_chk : ComputableInPolyTime
        (fun t : ((List Bool × List Bool) × Bool) × (ℕ × List Bool) ↦
          decide (t.2.2.length + (unframe t.1.1.2).length ≤ p.eval t.2.1))
        encT encBool :=
      ComputableInPolyTime.unary_le'
        (ComputableInPolyTime.unary_add'
          (ComputableInPolyTime.length_bits.comp hnα.snd')
          (ComputableInPolyTime.length_bits.comp (ComputableInPolyTime.unframe.comp hcert')))
        ((ComputableInPolyTime.unary_eval p).comp hnα.fst')
    exact ComputableInPolyTime.ite'
      ((ComputableInPolyTime.headD (encA := encBool) (encL := encBits) false).comp hraw')
      (ComputableInPolyTime.bool_and' hlen_chk hans) hans
  have hV : ComputableInPolyTimeWithOracle C V (encPair encBits encBits) encBool :=
    (hcombine.computableInPolyTimeWithOracle C).comp_with
      ((computableInPolyTimeWithOracle_mem C).preprocess hquery)
  let q_pref : Polynomial ℕ := Polynomial.C 2 * p + 1
  refine ⟨q_pref, V, hV,
    IsVerifier.of_padding (fun raw cert _ hVt ↦ ?_) (fun raw hmem ↦ ?_)⟩
  · cases raw with
    | nil => simp [V, combinePref] at hVt
    | cons tag rest =>
      simp only [V, combinePref, queryPref, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte,
        List.tail_cons, List.headD_cons] at hVt
      cases hdec : decNW.decode rest with
      | none => simp [hdec] at hVt
      | some nα =>
        rcases nα with ⟨n, α⟩
        have hrest := (decNW.decode_eq_some_iff rest (n, α)).mp hdec
        simp only [hdec, Option.elim_some] at hVt
        cases tag with
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte, decide_eq_true_eq] at hVt
          exact ⟨false, n, α, congrArg (List.cons false) hrest, hVt⟩
        | true =>
          simp only [↓reduceIte, Bool.and_eq_true, decide_eq_true_eq] at hVt
          exact ⟨true, n, α, congrArg (List.cons true) hrest, unframe cert, hVt.1, hVt.2⟩
  · obtain ⟨tag, n, α, rfl, hbody⟩ := hmem
    have hdec : decNW.decode (encPair encUnary encBits (n, α)) = some (n, α) :=
      decNW.decode_enc (n, α)
    cases tag with
    | false =>
      refine ⟨[], by simp, fun k ↦ ?_⟩
      simp only [V, combinePref, queryPref, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte,
        List.tail_cons, List.headD_cons, hdec, Option.elim_some, decide_eq_true_eq]
      exact hbody
    | true =>
      obtain ⟨β, hβlen, hβmem⟩ := hbody
      have hn_le : n ≤ (true :: encPair encUnary encBits (n, α)).length := by
        simp only [List.length_cons, length_encPair, encUnary_apply, List.length_replicate]
        omega
      have hp_mono : p.eval n ≤ p.eval (true :: encPair encUnary encBits (n, α)).length :=
        polynomial_eval_mono hn_le
      refine ⟨frame β, ?_, fun k ↦ ?_⟩
      · simp only [q_pref, encBits_apply, length_frame, Polynomial.eval_add, Polynomial.eval_mul,
          Polynomial.eval_C, Polynomial.eval_one]
        omega
      · simp only [V, combinePref, queryPref, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte,
          List.tail_cons, List.headD_cons, hdec, Option.elim_some, unframe_frame_append,
          Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨hβlen, hβmem⟩

/-- `prefixOracle A check eval p` lies in `NP^{coNP^A}`. -/
theorem prefixOracle_mem_NP_coNP (A : Set (List Bool))
    {check : ℕ × List Bool → Bool} {eval : List Bool × List Bool → Bool}
    (hcheck : ComputableInPolyTime check (encPair encUnary encBits) encBool)
    (heval : ComputableInPolyTime eval (encPair encBits encBits) encBool) (p : Polynomial ℕ) :
    prefixOracle A check eval p ∈
      ⋃ B ∈ {S : Set (List Bool) | Sᶜ ∈ NPWithOracle A encBits}, NPWithOracle B encBits :=
  Set.mem_iUnion₂.mpr
    ⟨correctOracle A check eval, compl_correctOracle_mem_NPWithOracle A hcheck heval,
      prefixOracle_mem_NPWithOracle_correctOracle A check eval p⟩

/-- `prefixOracle A check eval p` lies in `NP^{NP^A}`. -/
theorem prefixOracle_mem_NP_NP (A : Set (List Bool))
    {check : ℕ × List Bool → Bool} {eval : List Bool × List Bool → Bool}
    (hcheck : ComputableInPolyTime check (encPair encUnary encBits) encBool)
    (heval : ComputableInPolyTime eval (encPair encBits encBits) encBool) (p : Polynomial ℕ) :
    prefixOracle A check eval p ∈ ⋃ B ∈ NPWithOracle A encBits, NPWithOracle B encBits := by
  refine Set.mem_iUnion₂.mpr
    ⟨(correctOracle A check eval)ᶜ, compl_correctOracle_mem_NPWithOracle A hcheck heval, ?_⟩
  have hsub := NPWithOracle_subset_of_mem_PWithOracle
    (by simpa only [compl_compl] using mem_PWithOracle_compl_self (correctOracle A check eval)ᶜ)
    encBits
  exact hsub (prefixOracle_mem_NPWithOracle_correctOracle A check eval p)

/-! ### Lexicographic prefix search in `FP^{prefixOracle}` -/

/-- One step of lexicographic prefix search for a valid description of length at most `p(n)`. -/
private def prefixStep (n : ℕ) (α : List Bool) : WordQueryComp Unit (List Bool) :=
  (List.take 1 <$> OracleComp.query ((), false :: encPair encUnary encBits (n, α))) >>= fun r1 ↦
    if r1 = [true] then
      pure α
    else
      (fun r2 ↦ if r2 = [true] then α ++ [false] else α ++ [true]) <$>
        (List.take 1 <$>
          OracleComp.query ((), true :: encPair encUnary encBits (n, α ++ [false])))

private theorem interpret_prefixStep (n : ℕ) (α : List Bool) :
    OracleComp.interpret ProbOracleComp.query (prefixStep n α) =
      ((List.take 1 <$> ProbOracleComp.query (spec := fun _ : Unit × List Bool ↦ List Bool)
          ((), false :: encPair encUnary encBits (n, α))) >>= fun r1 ↦
        if r1 = [true] then
          pure α
        else
          (fun r2 ↦ if r2 = [true] then α ++ [false] else α ++ [true]) <$>
            (List.take 1 <$>
              ProbOracleComp.query (spec := fun _ : Unit × List Bool ↦ List Bool)
                ((), true :: encPair encUnary encBits (n, α ++ [false])))) := by
  unfold prefixStep
  rw [OracleComp.interpret_bind, OracleComp.interpret_map, OracleComp.interpret_query]
  congr 1
  funext r1
  split
  · rfl
  · rw [OracleComp.interpret_map, OracleComp.interpret_map, OracleComp.interpret_query]

private theorem isOraclePPTOn_prefixStep :
    IsOraclePPTOn (encPair encUnary encBits) encBits
      (fun pair : ℕ × List Bool ↦
        OracleComp.interpret ProbOracleComp.query (prefixStep pair.1 pair.2)) := by
  simp only [interpret_prefixStep]
  have hreq1 : ComputableInPolyTime
      (fun pair : ℕ × List Bool ↦ false :: encPair encUnary encBits pair)
      (encPair encUnary encBits) encBits :=
    ComputableInPolyTime.bitsCons (ComputableInPolyTime.const false)
      (ComputableInPolyTime.of_eq fun _ ↦ rfl)
  have hfirst : IsOraclePPTOn (encPair encUnary encBits) encBits
      (fun pair : ℕ × List Bool ↦
        List.take 1 <$> ProbOracleComp.query (spec := fun _ : Unit × List Bool ↦ List Bool)
          ((), false :: encPair encUnary encBits pair)) :=
    IsOraclePPTOn.query_take (Operation := Unit) () hreq1 (ComputableInPolyTime.const 1)
  refine IsOraclePPTOn.bind_with hfirst ?_
  let encS := encPair (encPair encUnary encBits) encBits
  have hcond : ComputableInPolyTime
      (fun s : (ℕ × List Bool) × List Bool ↦ decide (s.2 = [true])) encS encBool :=
    ComputableInPolyTime.decide_eq' (ComputableInPolyTime.snd _ _)
      (ComputableInPolyTime.const [true])
  have hyes : IsOraclePPTOn encS encBits
      (fun s : (ℕ × List Bool) × List Bool ↦ (pure s.1.2 : WordOracleComp Unit (List Bool))) :=
    ((ComputableInPolyTime.fst _ _).snd').isOraclePPTOn
  have hreq2 : ComputableInPolyTime
      (fun s : (ℕ × List Bool) × List Bool ↦
        true :: encPair encUnary encBits (s.1.1, s.1.2 ++ [false])) encS encBits :=
    ComputableInPolyTime.bitsCons (ComputableInPolyTime.const true)
      ((ComputableInPolyTime.of_eq (f := encPair encUnary encBits) fun _ ↦ rfl).comp
        (((ComputableInPolyTime.fst _ _).fst').prod
          (ComputableInPolyTime.bitsAppend ((ComputableInPolyTime.fst _ _).snd')
            (ComputableInPolyTime.const [false]))))
  have hpost : ComputableInPolyTime
      (fun q : ((ℕ × List Bool) × List Bool) × List Bool ↦
        if q.2 = [true] then q.1.1.2 ++ [false] else q.1.1.2 ++ [true])
      (encPair encS encBits) encBits :=
    (ComputableInPolyTime.ite'
      (ComputableInPolyTime.decide_eq' (ComputableInPolyTime.snd encS encBits)
        (ComputableInPolyTime.const [true]))
      (ComputableInPolyTime.bitsAppend (((ComputableInPolyTime.fst encS encBits).fst').snd')
        (ComputableInPolyTime.const [false]))
      (ComputableInPolyTime.bitsAppend (((ComputableInPolyTime.fst encS encBits).fst').snd')
        (ComputableInPolyTime.const [true]))).of_enc_eq fun q ↦ by
      by_cases h : q.2 = [true] <;> simp [h]
  have hno : IsOraclePPTOn encS encBits
      (fun s : (ℕ × List Bool) × List Bool ↦
        (fun r2 ↦ if r2 = [true] then s.1.2 ++ [false] else s.1.2 ++ [true]) <$>
          (List.take 1 <$> ProbOracleComp.query (spec := fun _ : Unit × List Bool ↦ List Bool)
            ((), true :: encPair encUnary encBits (s.1.1, s.1.2 ++ [false])))) :=
    IsOraclePPTOn.map_with
      (IsOraclePPTOn.query_take (Operation := Unit) () hreq2 (ComputableInPolyTime.const 1)) hpost
  exact IsOraclePPTOn.ite hcond hyes hno

private theorem prefixStep_growth (n : ℕ) (α next : List Bool)
    (hnext : next ∈ OracleComp.support
      (OracleComp.interpret ProbOracleComp.query (prefixStep n α))) :
    (encBits next).length ≤ (encBits α).length + 1 := by
  rw [interpret_prefixStep] at hnext
  obtain ⟨r1, -, hnext⟩ := OracleComp.mem_supportWith_bind_iff.mp hnext
  split_ifs at hnext with hr1
  · have hEq : next = α := OracleComp.eq_of_mem_supportWith_pure hnext
    subst hEq
    simp
  · rw [Functor.map_map] at hnext
    obtain ⟨r2, -, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hnext
    split_ifs <;> simp

private theorem interpret_id_prefixStep {A : Set (List Bool)}
    {check : ℕ × List Bool → Bool} {eval : List Bool × List Bool → Bool} {p : Polynomial ℕ}
    (n : ℕ) (α : List Bool) :
    let _ := Classical.propDecidable
    OracleComp.interpret (m := Id) (languageOracle (prefixOracle A check eval p))
        (prefixStep n α) =
      if encPair encUnary encBits (n, α) ∈ correctOracle A check eval then α
      else if ∃ β : List Bool, α.length + 1 + β.length ≤ p.eval n ∧
          encPair encUnary encBits (n, α ++ false :: β) ∈ correctOracle A check eval then
        α ++ [false]
      else
        α ++ [true] := by
  classical
  unfold prefixStep
  rw [OracleComp.interpret_bind, OracleComp.interpret_map, OracleComp.interpret_query]
  change (OracleComp.interpret (m := Id) (languageOracle (prefixOracle A check eval p))
    (if List.take 1 (languageOracle (prefixOracle A check eval p)
        ((), false :: encPair encUnary encBits (n, α))) = [true] then
      pure α
    else
      (fun r2 ↦ if r2 = [true] then α ++ [false] else α ++ [true]) <$>
        (List.take 1 <$> OracleComp.query
          ((), true :: encPair encUnary encBits (n, α ++ [false]))))) = _
  rw [languageOracle_apply]
  simp only [List.take_succ_cons, List.take_zero, List.cons.injEq, and_true, decide_eq_true_eq,
    mem_prefixOracle_false_iff]
  by_cases h1 : encPair encUnary encBits (n, α) ∈ correctOracle A check eval
  · simp only [h1, ↓reduceIte]
    rfl
  · simp only [h1, ↓reduceIte]
    rw [OracleComp.interpret_map, OracleComp.interpret_map, OracleComp.interpret_query]
    change (if List.take 1 (languageOracle (prefixOracle A check eval p)
        ((), true :: encPair encUnary encBits (n, α ++ [false]))) = [true] then
      α ++ [false] else α ++ [true]) = _
    rw [languageOracle_apply]
    simp only [List.take_succ_cons, List.take_zero, List.cons.injEq, and_true, decide_eq_true_eq,
      mem_prefixOracle_true_iff, List.length_append, List.length_singleton, List.append_assoc,
      List.singleton_append]

/-- **General brute-force uniformity (`FP^{NP^{coNP^A}}`)**:
if a language `A` has polynomial-length descriptions verified by polynomial-time `check` and
evaluated by polynomial-time `eval`, then a valid description for each input length `n` is
computable in polynomial time relative to `prefixOracle A check eval p ∈ NP^{coNP^A}`. -/
theorem exists_FP_NP_coNP_uniform_of_nonuniform (A : Set (List Bool))
    {check : ℕ × List Bool → Bool} {eval : List Bool × List Bool → Bool}
    (hcheck : ComputableInPolyTime check (encPair encUnary encBits) encBool)
    (heval : ComputableInPolyTime eval (encPair encBits encBits) encBool)
    (p : Polynomial ℕ)
    (hex : ∀ n, ∃ w : List Bool, w.length ≤ p.eval n ∧ check (n, w) = true ∧
      ∀ x : List Bool, x.length = n → (eval (w, x) = true ↔ x ∈ A)) :
    ∃ B : Set (List Bool), Bᶜ ∈ NPWithOracle A encBits ∧
      ∃ O ∈ NPWithOracle B encBits, ∃ gen : ℕ → List Bool,
      ComputableInPolyTimeWithOracle O gen encUnary encBits ∧
      ∀ n, (gen n).length ≤ p.eval n ∧ check (n, gen n) = true ∧
        ∀ x : List Bool, x.length = n → (eval (gen n, x) = true ↔ x ∈ A) := by
  classical
  let B := correctOracle A check eval
  let O := prefixOracle A check eval p
  let prog (n : ℕ) : WordQueryComp Unit (List Bool) :=
    OracleComp.iterate (p.eval n) (prefixStep n) []
  let gen (n : ℕ) : List Bool :=
    OracleComp.interpret (m := Id) (languageOracle O) (prog n)
  have hgen_pt : ComputableInPolyTimeWithOracle O gen encUnary encBits := by
    refine ⟨prog, ?_, fun _ ↦ rfl⟩
    simp only [prog, OracleComp.interpret_iterate]
    exact IsOraclePPTOn.iterateWith_of_bounded_growth
      (step := fun n α ↦ OracleComp.interpret ProbOracleComp.query (prefixStep n α))
      (ComputableInPolyTime.unary_eval p) (ComputableInPolyTime.const [])
      isOraclePPTOn_prefixStep (growth := fun _ ↦ 1) (PolyBounded.const 1)
      prefixStep_growth
  have hgen_ok (n : ℕ) :
      (gen n).length ≤ p.eval n ∧ encPair encUnary encBits (n, gen n) ∈ B := by
    let stepFn (α : List Bool) : List Bool :=
      OracleComp.interpret (m := Id) (languageOracle O) (prefixStep n α)
    have hInv : ∀ k, ∃ w : List Bool, w.length ≤ p.eval n ∧
        encPair encUnary encBits (n, w) ∈ B ∧
        stepFn^[k] [] <+: w ∧ (stepFn^[k] [] = w ∨ (stepFn^[k] []).length = k) := by
      intro k
      induction k with
      | zero =>
        obtain ⟨w, hwlen, hchk, hspec⟩ := hex n
        exact ⟨w, hwlen, encPair_mem_correctOracle_iff.mpr ⟨hchk, hspec⟩,
          List.nil_prefix, Or.inr rfl⟩
      | succ k ih =>
        obtain ⟨w, hwlen, hwB, hpref, hcase⟩ := ih
        set α := stepFn^[k] []
        rw [Function.iterate_succ_apply']
        have hstep_eq : stepFn α =
            if encPair encUnary encBits (n, α) ∈ B then α
            else if ∃ β : List Bool, α.length + 1 + β.length ≤ p.eval n ∧
                encPair encUnary encBits (n, α ++ false :: β) ∈ B then
              α ++ [false]
            else
              α ++ [true] := interpret_id_prefixStep n α
        rw [hstep_eq]
        by_cases hαB : encPair encUnary encBits (n, α) ∈ B
        · simp only [hαB, ↓reduceIte]
          exact ⟨α, hpref.length_le.trans hwlen, hαB, List.prefix_refl α, Or.inl rfl⟩
        · simp only [hαB, ↓reduceIte]
          have hne : α ≠ w := fun h ↦ hαB (h ▸ hwB)
          have hαlen : α.length = k := hcase.resolve_left hne
          by_cases h0 : ∃ β : List Bool, α.length + 1 + β.length ≤ p.eval n ∧
              encPair encUnary encBits (n, α ++ false :: β) ∈ B
          · simp only [h0, ↓reduceIte]
            obtain ⟨β, hβlen, hβB⟩ := h0
            refine ⟨α ++ false :: β, ?_, hβB, ?_, Or.inr (by simp [hαlen])⟩
            · simp only [List.length_append, List.length_cons]
              omega
            · exact ⟨β, by simp⟩
          · simp only [h0, ↓reduceIte]
            obtain ⟨t, ht⟩ := hpref
            cases t with
            | nil =>
              simp only [List.append_nil] at ht
              exact absurd ht hne
            | cons b rest =>
              cases b with
              | false =>
                exfalso
                apply h0
                refine ⟨rest, ?_, ht ▸ hwB⟩
                have := congrArg List.length ht
                simp only [List.length_append, List.length_cons] at this
                omega
              | true =>
                refine ⟨w, hwlen, hwB, ⟨rest, by simpa using ht⟩, Or.inr (by simp [hαlen])⟩
    obtain ⟨w, hwlen, hwB, hpref, hcase⟩ := hInv (p.eval n)
    have hiter : ∀ k, OracleComp.interpret (m := Id) (languageOracle O)
        (OracleComp.iterate k (prefixStep n) []) = stepFn^[k] [] := by
      intro k
      induction k with
      | zero => rfl
      | succ k ih =>
        rw [OracleComp.iterate_succ, OracleComp.interpret_bind, Function.iterate_succ_apply']
        exact congrArg stepFn ih
    have hgen_eq : gen n = stepFn^[p.eval n] [] := hiter (p.eval n)
    rw [hgen_eq]
    rcases hcase with hEq | hlen
    · exact ⟨hEq ▸ hwlen, hEq ▸ hwB⟩
    · obtain ⟨t, ht⟩ := hpref
      have ht_nil : t = [] := by
        have := congrArg List.length ht
        rw [List.length_append, hlen] at this
        exact List.eq_nil_of_length_eq_zero (by omega)
      have hEq : stepFn^[p.eval n] [] = w := by simpa [ht_nil] using ht
      exact ⟨hEq ▸ hwlen, hEq ▸ hwB⟩
  refine ⟨B, compl_correctOracle_mem_NPWithOracle A hcheck heval,
    O, prefixOracle_mem_NPWithOracle_correctOracle A check eval p, gen, hgen_pt, fun n ↦ ?_⟩
  obtain ⟨hlen, hmem⟩ := hgen_ok n
  obtain ⟨hchk, hspec⟩ := encPair_mem_correctOracle_iff.mp hmem
  exact ⟨hlen, hchk, hspec⟩

/-- Equivalent `FP^{NP^{NP^A}}` formulation of general brute-force uniformity. -/
theorem exists_FP_NP_NP_uniform_of_nonuniform (A : Set (List Bool))
    {check : ℕ × List Bool → Bool} {eval : List Bool × List Bool → Bool}
    (hcheck : ComputableInPolyTime check (encPair encUnary encBits) encBool)
    (heval : ComputableInPolyTime eval (encPair encBits encBits) encBool)
    (p : Polynomial ℕ)
    (hex : ∀ n, ∃ w : List Bool, w.length ≤ p.eval n ∧ check (n, w) = true ∧
      ∀ x : List Bool, x.length = n → (eval (w, x) = true ↔ x ∈ A)) :
    ∃ B ∈ NPWithOracle A encBits, ∃ O ∈ NPWithOracle B encBits, ∃ gen : ℕ → List Bool,
      ComputableInPolyTimeWithOracle O gen encUnary encBits ∧
      ∀ n, (gen n).length ≤ p.eval n ∧ check (n, gen n) = true ∧
        ∀ x : List Bool, x.length = n → (eval (gen n, x) = true ↔ x ∈ A) := by
  obtain ⟨B, hBc, O, hO, gen, hgen_pt, hgen_ok⟩ :=
    exists_FP_NP_coNP_uniform_of_nonuniform A hcheck heval p hex
  have hOBc : O ∈ NPWithOracle Bᶜ encBits :=
    NPWithOracle_subset_of_mem_PWithOracle
      (by simpa only [compl_compl] using mem_PWithOracle_compl_self Bᶜ) encBits hO
  exact ⟨Bᶜ, hBc, O, hOBc, gen, hgen_pt, hgen_ok⟩

end CslibFrontier.Complexity
