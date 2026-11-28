module

public import CslibFrontier.Computability.Circuit.Boolean.PPoly
public import CslibFrontier.Computability.Circuit.Boolean.EvaluationTime
public import CslibFrontier.Computability.Complexity.Classes.P
public import CslibFrontier.Computability.Complexity.Classes.NP
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Unary
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.Bits
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Option

import CslibFrontier.Computability.Complexity.Classes.NP.Witness
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeNatFrontends
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder.Basic
import Mathlib.Tactic.Linarith

/-!
# Circuit Obstruction Families and Explicitness Hierarchy

Formalizes abstract obstruction families for Boolean circuit lower bounds, their explicitness
hierarchy (explicit, strongly explicit, and extremely explicit), and the associated decision
problem complexity classifications in `P` and `NP`.

## Main definitions

* `CslibFrontier.Computability.Circuit.Boolean.IsTrivialObstruction`: counterexample table against
  circuits of size at most `m`.
* `CslibFrontier.Computability.Circuit.Boolean.ObstructionFamily`: sound family of bitstring
  obstructions with a decoding map producing counterexamples against small circuits.
* `CslibFrontier.Computability.Circuit.Boolean.ObstructionFamily.IsExplicit`,
  `IsStronglyExplicit`, `IsExtremelyExplicit`: polynomial-shortness, polynomial-time verification,
  polynomial-time search, and polynomial-time decoding properties.
* `CslibFrontier.Computability.Circuit.Boolean.ObstructionFamily.dpOH`: decision problem asking
  whether an obstruction exists at `(n, m)` with `m < 2 ^ n`.

## Main results

* `exists_isTrivialObstruction_iff`: trivial obstructions exist iff circuit complexity exceeds `m`.
* `ObstructionFamily.not_mem_PPoly_of_obstructionHypothesis`: an obstruction family satisfying
  the obstruction hypothesis witnesses `f ∉ P/poly`.
* `ObstructionFamily.dpOH_mem_NP_of_isExplicit`: explicit obstruction families place `dpOH ∈ NP`.
* `ObstructionFamily.dpOH_mem_P_of_isStronglyExplicit`: strongly explicit families place
  `dpOH ∈ P`.
* `ObstructionFamily.local_counterexample_of_isExtremelyExplicit`: extremely explicit global
  obstructions yield polynomial-time local counterexample finders.
* `xorFirstTwoObstructionFamily_isStronglyExplicit`: concrete strongly explicit uniform witness.
-/

public section

namespace CslibFrontier.Computability.Circuit.Boolean

open Filter
open Cslib Cslib.Circuits Cslib.Circuits.Boolean Cslib.Complexity
open Turing.MultiTapeTM

section TrivialObstruction

/-- A *trivial obstruction* to computing `f : BooleanFunction n` by
circuits of size at most `m`: a table assigning to each size-`≤ m` Boolean circuit `c` a
counterexample input `tbl c` where `c` disagrees with `f`. -/
def IsTrivialObstruction {n : ℕ} (f : BooleanFunction n) (m : ℕ)
    (tbl : Circuit signature n 1 → BitString n) : Prop :=
  ∀ c : Circuit signature n 1, c.size ≤ m → c.eval interpretation (tbl c) 0 ≠ f (tbl c)

/-- A trivial obstruction against size-`m` circuits exists if and only if the Boolean circuit
complexity of `f` strictly exceeds `m`. -/
theorem exists_isTrivialObstruction_iff {n : ℕ} (f : BooleanFunction n) (m : ℕ) :
    (∃ tbl, IsTrivialObstruction f m tbl) ↔ m < complexity interpretation (single f) := by
  classical
  constructor
  · rintro ⟨tbl, htbl⟩
    by_contra hle
    push Not at hle
    obtain ⟨c, hc_comp, hc_size⟩ :=
      (complexity_le_iff (I := interpretation) (f := single f) (k := m)).mp hle
    have heq : c.eval interpretation (tbl c) 0 = f (tbl c) := by
      have := congrFun (hc_comp (tbl c)) 0
      simpa [single] using this
    exact htbl c hc_size heq
  · intro hlt
    have hdis : ∀ c : Circuit signature n 1, c.size ≤ m →
        ∃ x : BitString n, c.eval interpretation x 0 ≠ f x := by
      intro c hcm
      by_contra hall
      push Not at hall
      have hcomp : c.Computes interpretation (single f) := by
        intro x
        funext j
        fin_cases j
        simpa [single] using hall x
      have hle : complexity interpretation (single f) ≤ m :=
        (complexity_le_of_computes c hcomp).trans hcm
      omega
    refine ⟨fun c => if h : c.size ≤ m then (hdis c h).choose else fun _ => false, ?_⟩
    intro c hcm
    simpa only [dite_eq_left hcm] using (hdis c hcm).choose_spec

end TrivialObstruction

section ObstructionFamilies

/-- An *obstruction family* to efficient Boolean
circuit computation of `f : ∀ n, BooleanFunction n` consists of sets of bitstring specifications
`specs n m` together with a decoding map `decode` producing a verified trivial obstruction for
every valid specification. -/
structure ObstructionFamily (f : ∀ n, BooleanFunction n) where
  /-- Valid bitstring specifications `[O_{n,m}]` of obstructions in `O_{n,m}`. -/
  specs : ℕ → ℕ → Set (List Bool)
  /-- Decoding algorithm mapping `(n, m, [O_{n,m}])` to a trivial obstruction table. -/
  decode : ∀ n, ℕ → List Bool → Circuit signature n 1 → BitString n
  /-- Correctness guarantee: every `x ∈ specs n m` decodes to a trivial obstruction. -/
  sound : ∀ n m x, x ∈ specs n m → IsTrivialObstruction (f n) m (decode n m x)

variable {f : ∀ n, BooleanFunction n}

/-- An obstruction family is *uniform* if all obstruction specifications
have `O(1)` bitlength. -/
def ObstructionFamily.IsUniform (O : ObstructionFamily f) : Prop :=
  ∃ C : ℕ, ∀ n m x, x ∈ O.specs n m → x.length ≤ C

/-- Shortness: whenever `m < 2 ^ n` and
`O_{n,m}` is nonempty, there exists an obstruction specification of length `≤ p(n)`, independent
of `m`. -/
def ObstructionFamily.IsShort (O : ObstructionFamily f) : Prop :=
  ∃ p : Polynomial ℕ, ∀ n m, m < 2 ^ n → (O.specs n m).Nonempty →
    ∃ x ∈ O.specs n m, x.length ≤ p.eval n

/-- The verification language for `O`: triples `(n, m, x)` with `m < 2 ^ n` and
`x ∈ O.specs n m`. -/
def ObstructionFamily.verifySet (O : ObstructionFamily f) : Set ((ℕ × ℕ) × List Bool) :=
  {t | t.1.2 < 2 ^ t.1.1 ∧ t.2 ∈ O.specs t.1.1 t.1.2}

/-- Easy-to-verify: given `n` in unary,
`m` in binary, and bitstring `x`, deciding whether `x ∈ O.specs n m` (for `m < 2 ^ n`) belongs
to `P` (hence runs in `poly(n, ⟨x⟩)` time, since `⟨m⟩ ≤ n`). -/
def ObstructionFamily.IsEasyToVerify (O : ObstructionFamily f) : Prop :=
  O.verifySet ∈ Complexity.P (encPair (encPair encUnary encNat) encBits)

/-- An obstruction family is *explicit* if it
is short and easy to verify. -/
def ObstructionFamily.IsExplicit (O : ObstructionFamily f) : Prop :=
  O.IsShort ∧ O.IsEasyToVerify

/-- An explicit obstruction family
is *strongly explicit* if there is a polynomial-time discovery algorithm (in unary `n` and binary
`m`) deciding nonemptiness of `O_{n,m}` and outputting a valid specification whenever one exists. -/
def ObstructionFamily.IsStronglyExplicit (O : ObstructionFamily f) : Prop :=
  O.IsExplicit ∧
    ∃ discover : ℕ × ℕ → Option (List Bool),
      ComputableInPolyTime discover (encPair encUnary encNat) (encOption encBits) ∧
      ∀ n m, m < 2 ^ n →
        (∀ x, discover (n, m) = some x → x ∈ O.specs n m) ∧
        ((O.specs n m).Nonempty → (discover (n, m)).isSome = true)

/-- Easy-to-decode: given `n, m` in unary, a specification `x`,
and a size-`≤ m` circuit `c`, the decoding algorithm produces a counterexample bitstring in
`poly(n, m, ⟨x⟩)` time. -/
def ObstructionFamily.IsEasyToDecode (O : ObstructionFamily f) : Prop :=
  ∃ dec : (ℕ × ℕ) × List Bool × (Σ n, Circuit signature n 1) → List Bool,
    ComputableInPolyTime dec
      (encPair (encPair encUnary encUnary) (encPair encBits (encCircuit 1))) encBits ∧
    ∀ n m x (c : Circuit signature n 1), x ∈ O.specs n m → c.size ≤ m →
      dec ((n, m), x, ⟨n, c⟩) = List.ofFn (O.decode n m x c)

/-- A strongly explicit obstruction
family is *extremely explicit* if its obstructions are also easy to decode. -/
def ObstructionFamily.IsExtremelyExplicit (O : ObstructionFamily f) : Prop :=
  O.IsStronglyExplicit ∧ O.IsEasyToDecode

/-- The obstruction decision problem `dpOH`: given `n` in unary and `m` in binary with
`m < 2 ^ n`, decide whether `O_{n,m}` is nonempty. -/
def ObstructionFamily.dpOH (O : ObstructionFamily f) : Set (ℕ × ℕ) :=
  {nm | nm.2 < 2 ^ nm.1 ∧ (O.specs nm.1 nm.2).Nonempty}

/-- Obstruction hypothesis: for every polynomial bound `m = poly(n)`,
`O_{n, m(n)}` is eventually nonempty. -/
def ObstructionFamily.ObstructionHypothesis (O : ObstructionFamily f) : Prop :=
  ∀ p : ℕ → ℕ, PolynomiallyBounded p → ∀ᶠ n in atTop, (O.specs n (p n)).Nonempty

/-- Existence of any obstruction in `O.specs n m` guarantees circuit complexity strictly exceeding
`m`. -/
theorem ObstructionFamily.complexity_gt_of_mem (O : ObstructionFamily f) {n m : ℕ}
    {x : List Bool} (hx : x ∈ O.specs n m) :
    m < complexity interpretation (single (f n)) :=
  (exists_isTrivialObstruction_iff (f n) m).mp ⟨O.decode n m x, O.sound n m x hx⟩

/-- If an obstruction
family for `f` satisfies the Obstruction Hypothesis, then the language of slices of `f` does not
belong to `P/poly`. -/
theorem ObstructionFamily.not_mem_PPoly_of_obstructionHypothesis (O : ObstructionFamily f)
    (hOH : O.ObstructionHypothesis) : Language.ofSlices f ∉ PPoly := by
  intro hPPoly
  rw [mem_PPoly] at hPPoly
  have hbound : PolynomiallyBounded fun n => complexity interpretation (single (f n)) := by
    simpa only [Language.slice_ofSlices] using hPPoly
  obtain ⟨n, ⟨x, hx⟩⟩ := (hOH _ hbound).exists
  exact (lt_irrefl _ (O.complexity_gt_of_mem hx))

/-- Bitlength characterization of `m < 2 ^ n` for the binary encoding `encNat m = m.bits`. -/
private lemma length_encNat_le_iff_lt_two_pow (m n : ℕ) :
    (encNat m).length ≤ n ↔ m < 2 ^ n := by
  rw [encNat_apply]
  induction m using Nat.binaryRec' generalizing n with
  | zero => simp
  | bit b k h ih =>
    have hne : Nat.bit b k ≠ 0 := Nat.bit_ne_zero_iff.mpr h
    rw [Nat.bits_append_bit k b h, List.length_cons]
    cases n with
    | zero =>
      simp only [pow_zero, Nat.lt_one_iff]
      exact ⟨fun h0 => absurd h0 (Nat.not_succ_le_zero _), fun h0 => absurd h0 hne⟩
    | succ n =>
      rw [Nat.succ_le_succ_iff, ih, Nat.bit_lt_two_pow_succ_iff]

/-- Monotonicity of polynomial evaluation on `ℕ`. -/
private lemma polynomial_eval_mono (p : Polynomial ℕ) {a b : ℕ} (hab : a ≤ b) :
    p.eval a ≤ p.eval b := by
  rw [Polynomial.eval_eq_sum_range, Polynomial.eval_eq_sum_range]
  exact Finset.sum_le_sum fun i _ => Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hab i)

/-- If `O` is an explicit obstruction family, then
its decision problem `DP(OH)` belongs to `NP` (with `n` in unary and `m` in binary). -/
theorem ObstructionFamily.dpOH_mem_NP_of_isExplicit (O : ObstructionFamily f)
    (hExp : O.IsExplicit) : O.dpOH ∈ Complexity.NP (encPair encUnary encNat) := by
  obtain ⟨⟨p, hp⟩, hVer⟩ := hExp
  obtain ⟨V, hV_poly, hV_spec⟩ := Complexity.mem_P.mp hVer
  refine Complexity.mem_NP_of_check (enc := encPair encUnary encNat) (encW := encBits)
    Decoder.bits (p := p) (check := V) hV_poly ?_ ?_
  · intro nm x hVx
    have hmem : (nm, x) ∈ O.verifySet := (hV_spec (nm, x)).mpr hVx
    exact ⟨hmem.1, x, hmem.2⟩
  · intro nm ⟨hm, hne⟩
    obtain ⟨x, hx, hlen⟩ := hp nm.1 nm.2 hm hne
    refine ⟨x, (hV_spec (nm, x)).mp ⟨hm, hx⟩, ?_⟩
    have hle : nm.1 ≤ (encPair encUnary encNat nm).length := by
      have h1 := length_le_encPair_left encUnary encNat nm
      simpa only [encUnary_apply, List.length_replicate] using h1
    simpa only [encBits_apply] using hlen.trans (polynomial_eval_mono p hle)

/-- If `O` is a strongly explicit obstruction family,
then its decision problem `DP(OH)` belongs to `P` (with `n` in unary and `m` in binary). -/
theorem ObstructionFamily.dpOH_mem_P_of_isStronglyExplicit (O : ObstructionFamily f)
    (hStr : O.IsStronglyExplicit) : O.dpOH ∈ Complexity.P (encPair encUnary encNat) := by
  obtain ⟨_, discover, hdisc_poly, hdisc_spec⟩ := hStr
  rw [Complexity.mem_P]
  let decBound : ℕ × ℕ → Bool := fun nm => decide ((encNat nm.2).length ≤ nm.1)
  have hlen_m : ComputableInPolyTime (fun nm : ℕ × ℕ => (encNat nm.2).length)
      (encPair encUnary encNat) encUnary :=
    (ComputableInPolyTime.encoding_length encNat).comp (ComputableInPolyTime.snd encUnary encNat)
  have hbound_poly : ComputableInPolyTime decBound (encPair encUnary encNat) encBool :=
    ComputableInPolyTime.unary_le' hlen_m (ComputableInPolyTime.fst encUnary encNat)
  have hisSome_poly : ComputableInPolyTime (fun nm : ℕ × ℕ => (discover nm).isSome)
      (encPair encUnary encNat) encBool :=
    ComputableInPolyTime.optionIsSome hdisc_poly
  refine ⟨fun nm => decBound nm && (discover nm).isSome,
    ComputableInPolyTime.bool_and' hbound_poly hisSome_poly, ?_⟩
  intro ⟨n, m⟩
  simp only [ObstructionFamily.dpOH, Set.mem_ofPred_eq, Bool.and_eq_true, decBound,
    decide_eq_true_eq, length_encNat_le_iff_lt_two_pow]
  constructor
  · rintro ⟨hm, hne⟩
    exact ⟨hm, (hdisc_spec n m hm).2 hne⟩
  · rintro ⟨hm, hsome⟩
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hsome
    exact ⟨hm, x, (hdisc_spec n m hm).1 x hx⟩

/-- If `O`
is an extremely explicit obstruction family, then given `(n, m)` in unary and a size-`≤ m` circuit
`c`, a counterexample bitstring on which `c` disagrees with `f n` can be constructed in
polynomial time in `(n, m, |c|)`. -/
theorem ObstructionFamily.local_counterexample_of_isExtremelyExplicit (O : ObstructionFamily f)
    (hExt : O.IsExtremelyExplicit) :
    ∃ find : (ℕ × ℕ) × (Σ n, Circuit signature n 1) → List Bool,
      ComputableInPolyTime find
        (encPair (encPair encUnary encUnary) (encCircuit 1)) encBits ∧
      ∀ n m (c : Circuit signature n 1), m < 2 ^ n → (O.specs n m).Nonempty → c.size ≤ m →
        ∃ x : BitString n, find ((n, m), ⟨n, c⟩) = List.ofFn x ∧
          c.eval interpretation x 0 ≠ f n x := by
  obtain ⟨⟨_, discover, hdisc_poly, hdisc_spec⟩, dec, hdec_poly, hdec_spec⟩ := hExt
  let encIn := encPair (encPair encUnary encUnary) (encCircuit 1)
  have hnm : ComputableInPolyTime
      (fun p : (ℕ × ℕ) × (Σ n, Circuit signature n 1) => p.1) encIn (encPair encUnary encUnary) :=
    ComputableInPolyTime.fst _ _
  have hn : ComputableInPolyTime
      (fun p : (ℕ × ℕ) × (Σ n, Circuit signature n 1) => p.1.1) encIn encUnary :=
    ComputableInPolyTime.fst' hnm
  have hm_unary : ComputableInPolyTime
      (fun p : (ℕ × ℕ) × (Σ n, Circuit signature n 1) => p.1.2) encIn encUnary :=
    ComputableInPolyTime.snd' hnm
  have hm_bin : ComputableInPolyTime
      (fun p : (ℕ × ℕ) × (Σ n, Circuit signature n 1) => p.1.2) encIn encNat :=
    ComputableInPolyTime.unary_to_binary.comp hm_unary
  have hdisc_in : ComputableInPolyTime
      (fun p : (ℕ × ℕ) × (Σ n, Circuit signature n 1) => discover (p.1.1, p.1.2))
      encIn (encOption encBits) :=
    hdisc_poly.comp (ComputableInPolyTime.prod hn hm_bin)
  have hspec_in : ComputableInPolyTime
      (fun p : (ℕ × ℕ) × (Σ n, Circuit signature n 1) => (discover (p.1.1, p.1.2)).getD [])
      encIn encBits :=
    ComputableInPolyTime.optionGetDWithInput hdisc_in (ComputableInPolyTime.const [])
  have hcirc_in : ComputableInPolyTime
      (fun p : (ℕ × ℕ) × (Σ n, Circuit signature n 1) => p.2) encIn (encCircuit 1) :=
    ComputableInPolyTime.snd _ _
  let find : (ℕ × ℕ) × (Σ n, Circuit signature n 1) → List Bool :=
    fun p => dec (p.1, (discover (p.1.1, p.1.2)).getD [], p.2)
  have hfind_poly : ComputableInPolyTime find encIn encBits :=
    hdec_poly.comp (ComputableInPolyTime.prod hnm (ComputableInPolyTime.prod hspec_in hcirc_in))
  refine ⟨find, hfind_poly, ?_⟩
  intro n m c hm hne hcm
  have hsome : (discover (n, m)).isSome = true := (hdisc_spec n m hm).2 hne
  obtain ⟨spec, hspec⟩ := Option.isSome_iff_exists.mp hsome
  have hspec_mem : spec ∈ O.specs n m := (hdisc_spec n m hm).1 spec hspec
  refine ⟨O.decode n m spec c, ?_, O.sound n m spec hspec_mem c hcm⟩
  simp only [find, hspec, Option.getD_some]
  exact hdec_spec n m spec c hspec_mem hcm

end ObstructionFamilies

section NonVacuity

/-- Concrete non-constant Boolean function family `x_0 ⊕ x_1` (for `n ≥ 2`). -/
def xorFirstTwo (n : ℕ) : BooleanFunction n :=
  fun x => if h : 2 ≤ n then xor (x ⟨0, by omega⟩) (x ⟨1, by omega⟩) else false

/-- Any Boolean circuit of size `0` on `n` inputs evaluates to a single input variable. -/
private lemma size_zero_eval_eq_input {n : ℕ} (c : Circuit signature n 1) (h0 : c.size = 0) :
    ∃ k : Fin n, ∀ y : BitString n, c.eval interpretation y 0 = y k := by
  cases h : c.outputs 0 with
  | input k =>
    exact ⟨k, fun y => by simp [Circuit.eval, h]⟩
  | gate j =>
    exact (Nat.not_lt_zero j.val (h0 ▸ j.isLt)).elim

/-- Explicit counterexample input against any size-`0` circuit for `xorFirstTwo n` (`n ≥ 2`). -/
private def xorZeroCounterexample (n : ℕ) (c : Circuit signature n 1) : BitString n :=
  let zeroIn : BitString n := fun _ => false
  let e0 : BitString n := fun i => decide (i.val = 0)
  let e1 : BitString n := fun i => decide (i.val = 1)
  if c.eval interpretation zeroIn 0 ≠ xorFirstTwo n zeroIn then zeroIn
  else if c.eval interpretation e0 0 ≠ xorFirstTwo n e0 then e0
  else e1

private lemma xorZeroCounterexample_sound {n : ℕ} (hn : 2 ≤ n) (c : Circuit signature n 1)
    (h0 : c.size ≤ 0) :
    c.eval interpretation (xorZeroCounterexample n c) 0 ≠
      xorFirstTwo n (xorZeroCounterexample n c) := by
  have hsize : c.size = 0 := Nat.eq_zero_of_le_zero h0
  obtain ⟨k, hk⟩ := size_zero_eval_eq_input c hsize
  let zeroIn : BitString n := fun _ => false
  let e0 : BitString n := fun i => decide (i.val = 0)
  let e1 : BitString n := fun i => decide (i.val = 1)
  dsimp only [xorZeroCounterexample]
  split_ifs with h1 h2
  · exact h1
  · exact h2
  · push Not at h1 h2
    have hxe0 : xorFirstTwo n e0 = true := by
      simp [xorFirstTwo, hn, e0]
    have hxe1 : xorFirstTwo n e1 = true := by
      simp [xorFirstTwo, hn, e1]
    have hk0 : e0 k = true := by
      rw [← hk e0, h2, hxe0]
    have hkval : k.val = 0 := by
      simpa [e0] using hk0
    rw [hk e1, hxe1]
    simp [e1, hkval]

/-- Concrete obstruction family for `xorFirstTwo`: for `n ≥ 2` and `m = 0`, the empty bitstring
`[]` is a valid size-`0` obstruction specification. -/
def xorFirstTwoObstructionFamily : ObstructionFamily xorFirstTwo where
  specs n m := if 2 ≤ n ∧ m = 0 then {[]} else ∅
  decode n _ _ c := xorZeroCounterexample n c
  sound n m x hx := by
    by_cases hnm : 2 ≤ n ∧ m = 0
    · intro c hcm
      exact xorZeroCounterexample_sound hnm.1 c (hnm.2 ▸ hcm)
    · simp [hnm] at hx

/-- Non-vacuity witness: `xorFirstTwoObstructionFamily` is unconditionally strongly explicit,
uniform, and has nonempty `dpOH` at every `n ≥ 2` (with `m = 0`). -/
theorem xorFirstTwoObstructionFamily_isStronglyExplicit :
    xorFirstTwoObstructionFamily.IsStronglyExplicit ∧
      xorFirstTwoObstructionFamily.IsUniform ∧
      ∀ n, 2 ≤ n → (n, 0) ∈ xorFirstTwoObstructionFamily.dpOH := by
  have hShort : xorFirstTwoObstructionFamily.IsShort := by
    refine ⟨0, fun n m _ hne => ?_⟩
    obtain ⟨x, hx⟩ := hne
    by_cases hnm : 2 ≤ n ∧ m = 0
    · simp only [xorFirstTwoObstructionFamily, ite_eq_left hnm, Set.mem_singleton_iff] at hx
      exact ⟨[], by simp [xorFirstTwoObstructionFamily, hnm], by simp⟩
    · simp [xorFirstTwoObstructionFamily, hnm] at hx
  have hVer : xorFirstTwoObstructionFamily.IsEasyToVerify := by
    rw [ObstructionFamily.IsEasyToVerify, Complexity.mem_P]
    let encIn := encPair (encPair encUnary encNat) encBits
    have hnm := ComputableInPolyTime.fst (encPair encUnary encNat) encBits
    have hn : ComputableInPolyTime (fun t : (ℕ × ℕ) × List Bool => t.1.1) encIn encUnary :=
      ComputableInPolyTime.fst' hnm
    have hm : ComputableInPolyTime (fun t : (ℕ × ℕ) × List Bool => t.1.2) encIn encNat :=
      ComputableInPolyTime.snd' hnm
    have hx : ComputableInPolyTime (fun t : (ℕ × ℕ) × List Bool => t.2) encIn encBits :=
      ComputableInPolyTime.snd (encPair encUnary encNat) encBits
    have hge2 : ComputableInPolyTime (fun t : (ℕ × ℕ) × List Bool => decide (2 ≤ t.1.1))
        encIn encBool :=
      ComputableInPolyTime.unary_le' (ComputableInPolyTime.const 2) hn
    have hm0 : ComputableInPolyTime
        (fun t : (ℕ × ℕ) × List Bool => decide ((encNat t.1.2).length ≤ 0)) encIn encBool :=
      ComputableInPolyTime.unary_le' ((ComputableInPolyTime.encoding_length encNat).comp hm)
        (ComputableInPolyTime.const 0)
    have hx0 : ComputableInPolyTime (fun t : (ℕ × ℕ) × List Bool => decide (t.2.length ≤ 0))
        encIn encBool :=
      ComputableInPolyTime.unary_le' (ComputableInPolyTime.length_bits_comp hx)
        (ComputableInPolyTime.const 0)
    refine ⟨fun t => decide (2 ≤ t.1.1) && decide ((encNat t.1.2).length ≤ 0) &&
        decide (t.2.length ≤ 0),
      ComputableInPolyTime.bool_and' (ComputableInPolyTime.bool_and' hge2 hm0) hx0, ?_⟩
    intro ⟨⟨n, m⟩, x⟩
    simp only [ObstructionFamily.verifySet, xorFirstTwoObstructionFamily, Set.mem_ofPred_eq,
      Bool.and_eq_true, decide_eq_true_eq]
    rw [length_encNat_le_iff_lt_two_pow, pow_zero, Nat.lt_one_iff, Nat.le_zero,
      List.length_eq_zero_iff]
    constructor
    · rintro ⟨_, hx_mem⟩
      by_cases hnm : 2 ≤ n ∧ m = 0
      · simp only [ite_eq_left hnm, Set.mem_singleton_iff] at hx_mem
        exact ⟨⟨hnm.1, hnm.2⟩, hx_mem⟩
      · simp [hnm] at hx_mem
    · rintro ⟨⟨hn2, rfl⟩, rfl⟩
      refine ⟨Nat.two_pow_pos n, ?_⟩
      simp [hn2]
  have hStr : xorFirstTwoObstructionFamily.IsStronglyExplicit := by
    refine ⟨⟨hShort, hVer⟩, fun nm => if 2 ≤ nm.1 ∧ (encNat nm.2).length ≤ 0 then some [] else none,
      ?_, ?_⟩
    · have hn : ComputableInPolyTime (fun nm : ℕ × ℕ => nm.1)
          (encPair encUnary encNat) encUnary :=
        ComputableInPolyTime.fst encUnary encNat
      have hm : ComputableInPolyTime (fun nm : ℕ × ℕ => nm.2)
          (encPair encUnary encNat) encNat :=
        ComputableInPolyTime.snd encUnary encNat
      have hge2 := ComputableInPolyTime.unary_le' (ComputableInPolyTime.const 2) hn
      have hm0 := ComputableInPolyTime.unary_le'
        ((ComputableInPolyTime.encoding_length encNat).comp hm) (ComputableInPolyTime.const 0)
      have hcond : ComputableInPolyTime
          (fun nm : ℕ × ℕ => decide (2 ≤ nm.1 ∧ (encNat nm.2).length ≤ 0))
          (encPair encUnary encNat) encBool :=
        ComputableInPolyTime.decide_and hge2 hm0
      exact ComputableInPolyTime.ite_decide hcond
        (ComputableInPolyTime.const (some [])) (ComputableInPolyTime.const none)
    · intro n m _
      simp only [length_encNat_le_iff_lt_two_pow, pow_zero, Nat.lt_one_iff,
        xorFirstTwoObstructionFamily]
      constructor
      · intro x hx
        by_cases hnm : 2 ≤ n ∧ m = 0
        · simp only [ite_eq_left hnm, Option.some.injEq] at hx
          subst hx
          simp [hnm]
        · simp [hnm] at hx
      · intro hne
        by_cases hnm : 2 ≤ n ∧ m = 0
        · simp [hnm]
        · simp [hnm] at hne
  refine ⟨hStr, ⟨0, fun n m x hx => ?_⟩, fun n hn => ⟨Nat.two_pow_pos n, ⟨[], by
      simp [xorFirstTwoObstructionFamily, hn]⟩⟩⟩
  by_cases hnm : 2 ≤ n ∧ m = 0
  · simp only [xorFirstTwoObstructionFamily, ite_eq_left hnm, Set.mem_singleton_iff] at hx
    simp [hx]
  · simp [xorFirstTwoObstructionFamily, hnm] at hx

end NonVacuity

end CslibFrontier.Computability.Circuit.Boolean
