/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import CslibFrontier.Computability.Circuit.Boolean.Advice
public import CslibFrontier.Computability.Circuit.Boolean.PPoly
public import CslibFrontier.Computability.Complexity.Classes.CountingHierarchy
public import CslibFrontier.Computability.Complexity.Classes.PP.Characterization
public import CslibFrontier.Computability.Complexity.Classes.SharpP
public import CslibFrontier.Computability.Complexity.Classes.Space
public import Mathlib.Algebra.Polynomial.Eval.Defs

import CslibFrontier.Computability.Complexity.Classes.CountingHierarchy.Space
import CslibFrontier.Computability.Complexity.Classes.Oracle.Closure
import CslibFrontier.Computability.Complexity.Classes.Oracle.Deterministic
import CslibFrontier.Computability.Complexity.Classes.Oracle.PolyTime
import CslibFrontier.Computability.Complexity.Classes.PP.Closure
import CslibFrontier.Computability.Complexity.Classes.SharpP.Closure
import CslibFrontier.Computability.Complexity.Classes.SharpP.Oracle
import CslibFrontier.Computability.Complexity.Classes.TruncatedVerifier
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Iteration
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.OutputLength
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder
import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.Replay.Simulation
import CslibFrontier.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial.Automation
import CslibFrontier.Foundations.Data.Nat.PolynomialBound.Closure
import Cslib.Foundations.Data.Polynomial.Monotone
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Nonuniform Counting Classes, Wagner's Hierarchy, and Karp–Lipton Advice

Defines nonuniform counting and gap classes (`#P/poly` and `GapP/poly`), Wagner's majority
operator `C` and counting-hierarchy levels `C_i P`, and Karp–Lipton polynomial advice classes
`K/poly`, `CH/poly`, and `P/poly`. Proves the equivalence between Wagner's `C`-operator
formulation of the counting hierarchy and the oracle-based `CountingLevel` hierarchy, the
equivalence between `P/poly` via advice strings and polynomial-size Boolean circuits, and the
collapse `CH/poly = P/poly` under `PP ⊆ P/poly`.

## Main definitions

* `CslibFrontier.Complexity.SharpPPoly`, `GapPPoly`: nonuniform counting and gap classes
  `#P/poly` and `GapP/poly`.
* `CslibFrontier.Complexity.COp`, `WagnerLevel`, `CH`: Wagner's majority operator `C`, the levels
  `C_i P`, and the counting hierarchy `CH = ⋃ i, C_i P`.
* `CslibFrontier.Complexity.WithPolyAdvice`, `CHPoly`, `PPolyClass`: Karp–Lipton nonuniform advice
  classes `K/poly`, `CH/poly`, and `P/poly`.

## Main results

* `CslibFrontier.Complexity.WagnerLevel_one_eq_PP`: `C_1 P = PP`.
* `CslibFrontier.Complexity.CH_eq_iUnion_CountingLevel`: equivalence between Wagner's `C`-operator
  hierarchy `CH` and the oracle-based hierarchy `⋃ a, CountingLevel a encBits`.
* `CslibFrontier.Complexity.PPolyClass_eq_PPoly`: equivalence between `WithPolyAdvice (P encBits)`
  and `Cslib.Circuits.Boolean.PPoly`.
* `CslibFrontier.Complexity.CHPoly_eq_PPoly_of_PP_subset_PPoly`: collapse `CH/poly = P/poly`
  whenever `PP ⊆ P/poly`.
-/

public section

namespace CslibFrontier.Complexity

open Cslib Cslib.Complexity Cslib.Circuits.Boolean
open Turing Turing.MultiTapeMachine Turing.MultiTapeTM Turing.MultiTapePTM
open scoped BigOperators

private theorem decPair_frame (x y : List Bool) :
    (Decoder.pair Decoder.bits Decoder.bits).decode (frame x ++ y) = (x, y) :=
  (Decoder.pair Decoder.bits Decoder.bits).decode_enc (x, y)

private theorem length_encList_bits (l : List (List Bool)) :
    (encList encBits l).length = (l.map fun w => (frame w).length).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [encList_cons, List.length_append, ih, List.map_cons, List.sum_cons, encBits_apply]

/-! ### Nonuniform `#P/poly` and `GapP/poly` -/

/-- Nonuniform counting class `#P/poly` with respect to an encoding `enc`: functions computed by a
`#P` function receiving a polynomially bounded advice string depending only on the encoded input
length. -/
def SharpPPoly {α : Type} (enc : α ↪ List Bool) : Set (α → ℕ) :=
  {f | ∃ (p : Polynomial ℕ) (a : ℕ → List Bool) (g : List Bool × α → ℕ),
    (∀ n, (a n).length ≤ p.eval n) ∧
    g ∈ SharpP (encPair encBits enc) ∧
    ∀ x, f x = g (a (enc x).length, x)}

/-- Nonuniform gap class `GapP/poly`: differences of two functions in `#P/poly`. -/
def GapPPoly {α : Type} (enc : α ↪ List Bool) : Set (α → ℤ) :=
  {h | ∃ f₁ ∈ SharpPPoly enc, ∃ f₂ ∈ SharpPPoly enc, ∀ x, h x = (f₁ x : ℤ) - f₂ x}

/-- Every uniform `#P` function belongs to `#P/poly`. -/
theorem SharpP_subset_SharpPPoly {α : Type} (enc : α ↪ List Bool) :
    SharpP enc ⊆ SharpPPoly enc := by
  rintro f ⟨p, V, hV, hf⟩
  let g : List Bool × α → ℕ :=
    fun q => acceptCount (fun r : (List Bool × α) × List Bool => V (r.1.2, r.2)) q
      (p.eval (enc q.2).length)
  refine ⟨0, fun _ => [], g, fun _ => by simp, ?_, fun x => ?_⟩
  · have hlen : ComputableInPolyTime (fun q : List Bool × α => p.eval (enc q.2).length)
        (encPair encBits enc) encUnary :=
      (ComputableInPolyTime.unary_eval p).comp
        ((ComputableInPolyTime.encoding_length enc).comp (.snd _ _))
    obtain ⟨Q, hQ⟩ := (ComputableInPolyTime.snd encBits enc).exists_polynomial_eval_length_le p
    refine ⟨Q, padVerifier (fun q => p.eval (enc q.2).length)
        (fun r => V (r.1.2, r.2)), ?_, fun q => ?_⟩
    · exact computableInPolyTime_padVerifier hlen
        (hV.comp (((ComputableInPolyTime.snd encBits enc).comp (.fst _ _)).prod (.snd _ _)))
    · exact (acceptCount_padVerifier_of_le (k := fun q : List Bool × α => p.eval (enc q.2).length)
        (V := fun r : (List Bool × α) × List Bool => V (r.1.2, r.2)) (a := q) (hQ q)).symm
  · rw [hf x]; rfl

/-- Every uniform `GapP` function belongs to `GapP/poly`. -/
theorem GapP_subset_GapPPoly {α : Type} (enc : α ↪ List Bool) :
    GapP enc ⊆ GapPPoly enc := by
  rintro h ⟨f₁, h₁, f₂, h₂, hh⟩
  exact ⟨f₁, SharpP_subset_SharpPPoly enc h₁, f₂, SharpP_subset_SharpPPoly enc h₂, hh⟩

/-- A `0/1`-valued function whose true-set lies in `P/poly` belongs to `#P/poly`. -/
theorem boolToNat_mem_SharpPPoly_of_mem_PPoly {α : Type} {enc : α ↪ List Bool}
    {f : α → Bool} (hf : {w | ∃ x, enc x = w ∧ f x = true} ∈ PPoly) :
    (fun x => (f x).toNat) ∈ SharpPPoly enc := by
  obtain ⟨α_adv, hα, A, ⟨dec, hdec, hA⟩, hL⟩ := PPoly_subset_PAdvice hf
  obtain ⟨c, d, hcd⟩ := polynomiallyBounded_iff_le.mp hα
  let p : Polynomial ℕ := Polynomial.C c * (Polynomial.X + 1) ^ d
  refine ⟨p, α_adv, fun q => (dec (q.1, enc q.2)).toNat, fun n => ?_, ?_, fun x => ?_⟩
  · simpa [p] using hcd n
  · refine ⟨0, fun r => dec (r.1.1, enc r.1.2), ?_, fun q => ?_⟩
    · have hpair : ComputableInPolyTime (fun r : (List Bool × α) × List Bool =>
          (r.1.1, enc r.1.2))
          (encPair (encPair encBits enc) encBits) (encPair encBits encBits) :=
        ((ComputableInPolyTime.fst encBits enc).comp (.fst _ _)).prod
          ((ComputableInPolyTime.of_eq (f := enc) (encOut := encBits) fun _ => rfl).comp
            ((ComputableInPolyTime.snd encBits enc).comp (.fst _ _)))
      exact hdec.comp hpair
    · simp only [Polynomial.eval_zero, acceptCount_zero]
      cases dec (q.1, enc q.2) <;> rfl
  · have hiff : f x = true ↔ dec (α_adv (enc x).length, enc x) = true := by
      have h1 : enc x ∈ {w | ∃ y, enc y = w ∧ f y = true} ↔ f x = true :=
        ⟨fun ⟨y, hy, hfy⟩ => enc.injective hy ▸ hfy, fun hfx => ⟨x, rfl, hfx⟩⟩
      exact h1.symm.trans ((hL (enc x)).trans (hA _))
    cases hfx : f x <;> cases hdx : dec (α_adv (enc x).length, enc x) <;> simp_all

/-- Zero belongs to `#P/poly`. -/
theorem SharpPPoly.zero_mem {α : Type} (enc : α ↪ List Bool) :
    (0 : α → ℕ) ∈ SharpPPoly enc :=
  SharpP_subset_SharpPPoly enc SharpP.zero_mem

/-- A `{0, 1}`-valued integer function whose support is in `P/poly` belongs to `GapP/poly`. -/
theorem boolToInt_mem_GapPPoly_of_mem_PPoly {α : Type} {enc : α ↪ List Bool}
    {f : α → Bool} (hf : {w | ∃ x, enc x = w ∧ f x = true} ∈ PPoly) :
    (fun x => ((f x).toNat : ℤ)) ∈ GapPPoly enc :=
  ⟨fun x => (f x).toNat, boolToNat_mem_SharpPPoly_of_mem_PPoly hf,
    0, SharpPPoly.zero_mem enc, fun x => by simp⟩

/-- A `{-1, 0, 1}`-valued integer function whose positive and negative supports lie in `P/poly`
belongs to `GapP/poly`. -/
theorem signedBool_mem_GapPPoly_of_mem_PPoly {α : Type} {enc : α ↪ List Bool}
    {pos neg : α → Bool}
    (hpos : {w | ∃ x, enc x = w ∧ pos x = true} ∈ PPoly)
    (hneg : {w | ∃ x, enc x = w ∧ neg x = true} ∈ PPoly) :
    (fun x => ((pos x).toNat : ℤ) - ((neg x).toNat : ℤ)) ∈ GapPPoly enc :=
  ⟨fun x => (pos x).toNat, boolToNat_mem_SharpPPoly_of_mem_PPoly hpos,
    fun x => (neg x).toNat, boolToNat_mem_SharpPPoly_of_mem_PPoly hneg, fun _ => rfl⟩

/-! ### Wagner's Counting Hierarchy `CH` -/

/-- Wagner's counting operator `C.K`: languages `A` for which there exist `B ∈ K` and a polynomial
`p` such that `x ∈ A ↔ #{y ∈ {0, 1}^{p(|x|)} : (x, y) ∈ B} ≥ 2^{p(|x|)-1}` (written without
integer-division truncation as `2^{p(|x|)} ≤ 2 * #{...}`). -/
def COp (K : Set (Set (List Bool))) : Set (Set (List Bool)) :=
  {A | ∃ B ∈ K, ∃ p : Polynomial ℕ,
    ∀ x, x ∈ A ↔ 2 ^ p.eval x.length ≤
      2 * acceptCount (fun q => @decide (encPair encBits encBits q ∈ B)
        (Classical.propDecidable _)) x (p.eval x.length)}

/-- Equivalence between `acceptCount` in `COp` and the `Finset.filter` cardinality over
`Fin m → Bool`. -/
theorem acceptCount_mem_eq_card_filter (B : Set (List Bool)) (x : List Bool) (m : ℕ) :
    let _ := Classical.propDecidable
    acceptCount (fun q => decide (encPair encBits encBits q ∈ B)) x m =
      (Finset.univ.filter fun w : Fin m → Bool =>
        encPair encBits encBits (x, List.ofFn w) ∈ B).card := by
  classical
  unfold acceptCount
  congr 1; ext w
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq]

/-- For positive witness length `1 ≤ p(|x|)`, the `2^m ≤ 2 * c` condition in `COp` is identical
to `2^(m - 1) ≤ c`. -/
theorem two_pow_le_two_mul_iff {m c : ℕ} (hm : 1 ≤ m) :
    2 ^ m ≤ 2 * c ↔ 2 ^ (m - 1) ≤ c := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hm
  simp only [Nat.add_sub_cancel, pow_succ']
  omega

/-- The `i`-th level `C_i P` of Wagner's counting hierarchy (`C_0 P = P`,
`C_{i+1} P = C.(C_i P)`). -/
@[expose] def WagnerLevel : ℕ → Set (Set (List Bool))
  | 0 => P encBits
  | i + 1 => COp (WagnerLevel i)

/-- The counting hierarchy `CH = ⋃ i, C_i P`. -/
def CH : Set (Set (List Bool)) :=
  ⋃ i, WagnerLevel i

@[simp]
theorem WagnerLevel_zero : WagnerLevel 0 = P encBits := rfl

@[simp]
theorem WagnerLevel_succ (i : ℕ) : WagnerLevel (i + 1) = COp (WagnerLevel i) := rfl

/-- Level 1 of Wagner's counting hierarchy equals `PP`. -/
theorem WagnerLevel_one_eq_PP : WagnerLevel 1 = PP encBits := by
  classical
  ext A
  rw [WagnerLevel_succ, WagnerLevel_zero, mem_PP_iff_decidesByNonstrictMajority]
  constructor
  · rintro ⟨B, ⟨V, hV, hVB⟩, p, hA⟩
    refine ⟨p, fun q => V (encPair encBits encBits q),
      hV.comp (ComputableInPolyTime.of_eq (f := encPair encBits encBits)
        (encOut := encBits) fun _ => rfl), fun x => ?_⟩
    rw [hA x]
    have hcongr : acceptCount (fun q => decide (encPair encBits encBits q ∈ B)) x
        (p.eval x.length) =
        acceptCount (fun q => V (encPair encBits encBits q)) x (p.eval x.length) :=
      acceptCount_congr (fun w => Bool.eq_iff_iff.mpr (by rw [decide_eq_true_eq, hVB])) _
    simp only [encBits_apply]
    rw [hcongr]
  · rintro ⟨p, V, hV, hA⟩
    let decPair := Decoder.pair Decoder.bits Decoder.bits
    refine ⟨{z | V (decPair.decode z) = true},
      ⟨fun z => V (decPair.decode z), hV.comp decPair.computableInPolyTime,
        fun _ => Iff.rfl⟩, p, fun x => ?_⟩
    rw [hA x]
    simp only [encBits_apply]
    suffices h : acceptCount V x (p.eval x.length) =
        acceptCount (fun q => @decide _ (Classical.propDecidable
          (encPair encBits encBits q ∈ {z | V (decPair.decode z) = true}))) x
          (p.eval x.length) by
      rw [h]
    exact acceptCount_congr (fun w => by
      rw [Bool.eq_iff_iff, @decide_eq_true_eq _ (Classical.propDecidable _), Set.mem_ofPred_eq,
        encPair_apply, encBits_apply, decPair_frame]
      rfl) _

/-- Non-strict majority with a `take`-prefix of random bits scales both sides by the same power
of two. -/
private theorem nonstrictMajority_take_iff {V : List Bool × List Bool → Bool}
    {V' : List Bool × List Bool → Bool} {a b : List Bool} {k K : ℕ} (hk : k ≤ K)
    (hV : ∀ w, V' (a, w) = V (b, w.take k)) :
    (2 ^ K ≤ 2 * acceptCount V' a K) ↔ (2 ^ k ≤ 2 * acceptCount V b k) := by
  rw [acceptCount_eq_two_pow_mul_of_take hk hV, ← pow_sub_mul_pow 2 hk, mul_left_comm 2]
  exact ⟨fun h => Nat.le_of_mul_le_mul_left h (by positivity),
    fun h => Nat.mul_le_mul_left _ h⟩

/-- Every level `WagnerLevel i` is closed under polynomial-time many-one reductions. -/
theorem PolyTimeReducible.mem_WagnerLevel {i : ℕ} {L M : Set (List Bool)}
    (h : PolyTimeReducible encBits encBits L M) (hM : M ∈ WagnerLevel i) :
    L ∈ WagnerLevel i := by
  classical
  induction i generalizing L M with
  | zero => exact h.mem_P hM
  | succ i ih =>
    obtain ⟨f, hf, hLM⟩ := h
    obtain ⟨B, hB, p, hMB⟩ := hM
    obtain ⟨q, hpq⟩ := hf.exists_polynomial_eval_length_le p
    let decPair := Decoder.pair Decoder.bits Decoder.bits
    let g : List Bool → List Bool := fun z =>
      let xy := decPair.decode z
      encPair encBits encBits (f xy.1, xy.2.take (p.eval (f xy.1).length))
    have hg : ComputableInPolyTime g encBits encBits := by
      have h1 : ComputableInPolyTime (fun z => f (decPair.decode z).1) encBits encBits :=
        hf.comp ((ComputableInPolyTime.fst encBits encBits).comp decPair.computableInPolyTime)
      have h2 : ComputableInPolyTime
          (fun z => (decPair.decode z).2.take (p.eval (f (decPair.decode z).1).length))
          encBits encBits :=
        ComputableInPolyTime.bitsTakeWithInput
          ((ComputableInPolyTime.snd encBits encBits).comp decPair.computableInPolyTime)
          ((ComputableInPolyTime.unary_eval p).comp (ComputableInPolyTime.length_bits_comp h1))
      exact (ComputableInPolyTime.of_eq (f := encPair encBits encBits) (encOut := encBits)
        fun _ => rfl).comp (h1.prod h2)
    have hB' : g ⁻¹' B ∈ WagnerLevel i := ih ⟨g, hg, fun _ => Iff.rfl⟩ hB
    refine ⟨g ⁻¹' B, hB', q, fun x => ?_⟩
    rw [hLM x, hMB (f x)]
    have hle : p.eval (f x).length ≤ q.eval x.length := by simpa [encBits_apply] using hpq x
    refine (nonstrictMajority_take_iff hle (fun w => ?_)).symm
    simp only [Set.mem_preimage, g, decPair.decode_enc]

/-- Each Wagner level is contained in the next. -/
theorem WagnerLevel_subset_succ (i : ℕ) : WagnerLevel i ⊆ WagnerLevel (i + 1) := by
  classical
  intro B hB
  let decPair := Decoder.pair Decoder.bits Decoder.bits
  have hB' : (fun z => (decPair.decode z).1) ⁻¹' B ∈ WagnerLevel i :=
    PolyTimeReducible.mem_WagnerLevel
      ⟨fun z => (decPair.decode z).1,
        (ComputableInPolyTime.fst encBits encBits).comp decPair.computableInPolyTime,
        fun _ => Iff.rfl⟩ hB
  refine ⟨(fun z => (decPair.decode z).1) ⁻¹' B, hB', 0, fun x => ?_⟩
  simp only [Polynomial.eval_zero, pow_zero, acceptCount_zero, Set.mem_preimage,
    decPair.decode_enc]
  by_cases hx : x ∈ B <;> simp [hx]

/-- Monotonicity of Wagner levels. -/
theorem WagnerLevel_mono {i j : ℕ} (hij : i ≤ j) : WagnerLevel i ⊆ WagnerLevel j := by
  induction hij with
  | refl => exact Set.Subset.rfl
  | step _ ih => exact ih.trans (WagnerLevel_subset_succ _)

/-- `P` is contained in every Wagner level. -/
theorem P_subset_WagnerLevel (i : ℕ) : P encBits ⊆ WagnerLevel i :=
  WagnerLevel_mono (Nat.zero_le i)

/-- The empty language is in every Wagner level. -/
theorem empty_mem_WagnerLevel (i : ℕ) : (∅ : Set (List Bool)) ∈ WagnerLevel i :=
  P_subset_WagnerLevel i empty_mem_P

/-- The universal language is in every Wagner level. -/
theorem univ_mem_WagnerLevel (i : ℕ) : (Set.univ : Set (List Bool)) ∈ WagnerLevel i :=
  P_subset_WagnerLevel i ⟨fun _ => true, .const true, fun _ => by simp⟩

/-- Every Wagner level is closed under complement. -/
theorem compl_mem_WagnerLevel {i : ℕ} {A : Set (List Bool)} (hA : A ∈ WagnerLevel i) :
    Aᶜ ∈ WagnerLevel i := by
  classical
  induction i generalizing A with
  | zero =>
    obtain ⟨f, hf, hAf⟩ := hA
    exact ⟨fun x => !f x, ComputableInPolyTime.bool_not.comp hf, fun x => by
      simp [Set.mem_compl_iff, hAf x]⟩
  | succ i ih =>
    obtain ⟨B, hB, p, hAB⟩ := hA
    have hBc : Bᶜ ∈ WagnerLevel i := ih hB
    by_cases hEmpty : Bᶜ = ∅
    · have hAuniv : A = Set.univ := Set.ext fun x => by
        rw [hAB x]; simp only [Set.mem_univ, iff_true]
        have hBuniv : B = Set.univ := by
          ext w; have := Set.ext_iff.mp hEmpty w; simpa using this
        have hacc : acceptCount (fun q => decide (encPair encBits encBits q ∈ B)) x
            (p.eval x.length) = 2 ^ p.eval x.length := by
          simp [hBuniv, acceptCount_true]
        rw [hacc]; omega
      rw [hAuniv, Set.compl_univ]; exact empty_mem_WagnerLevel (i + 1)
    · by_cases hUniv : Bᶜ = Set.univ
      · have hAempty : A = ∅ := Set.ext fun x => by
          rw [hAB x]; simp only [Set.mem_empty_iff_false, iff_false]
          have hBemp : B = ∅ := by
            ext w; have := Set.ext_iff.mp hUniv w; simpa using this
          have hacc : acceptCount (fun q => decide (encPair encBits encBits q ∈ B)) x
              (p.eval x.length) = 0 := by
            simp [hBemp, acceptCount_false]
          rw [hacc]; have := Nat.one_le_two_pow (n := p.eval x.length); omega
        rw [hAempty, Set.compl_empty]; exact univ_mem_WagnerLevel (i + 1)
      · obtain ⟨yin, hyin⟩ := Set.nonempty_iff_ne_empty.mpr hEmpty
        obtain ⟨yout, hyout⟩ : ∃ y, y ∉ Bᶜ := by
          by_contra! hall; exact hUniv (Set.eq_univ_of_forall hall)
        let decPair := Decoder.pair Decoder.bits Decoder.bits
        let g : List Bool → List Bool := fun z =>
          let xy := decPair.decode z
          if xy.2.headD false then
            encPair encBits encBits (xy.1, xy.2.tail.tail)
          else if !(xy.2.tail.headD false) && (xy.2.tail.tail.any fun b => b) then
            yin
          else
            yout
        have hg : ComputableInPolyTime g encBits encBits := by
          have hx := (ComputableInPolyTime.fst encBits encBits).comp decPair.computableInPolyTime
          have hw := (ComputableInPolyTime.snd encBits encBits).comp decPair.computableInPolyTime
          have hwt := ComputableInPolyTime.bitsTail.comp hw
          have hwtt := ComputableInPolyTime.bitsTail.comp hwt
          have hb1 := (ComputableInPolyTime.headD (encA := encBool) false).comp hw
          have hb2 := (ComputableInPolyTime.headD (encA := encBool) false).comp hwt
          have hany := ComputableInPolyTime.bitsAnyWithInput (test := fun _ b => b) hwtt (.snd _ _)
          have hcond2 := ComputableInPolyTime.bool_and.comp
            ((ComputableInPolyTime.bool_not.comp hb2).prod hany)
          have hbranch1 := (ComputableInPolyTime.of_eq (f := encPair encBits encBits)
            (encOut := encBits) fun _ => rfl).comp (hx.prod hwtt)
          exact ComputableInPolyTime.ite' hb1 hbranch1
            (ComputableInPolyTime.ite' hcond2 (.const yin) (.const yout))
        have hB' : g ⁻¹' Bᶜ ∈ WagnerLevel i :=
          PolyTimeReducible.mem_WagnerLevel ⟨g, hg, fun _ => Iff.rfl⟩ hBc
        refine ⟨g ⁻¹' Bᶜ, hB', p + 2, fun x => ?_⟩
        rw [Set.mem_compl_iff, hAB x]
        set m := p.eval x.length
        let V : List Bool × List Bool → Bool := fun q => decide (encPair encBits encBits q ∈ B)
        let V' : List Bool × List Bool → Bool := fun q =>
          decide (encPair encBits encBits q ∈ g ⁻¹' Bᶜ)
        have hzero : (Finset.univ.filter fun w : Fin m → Bool =>
            ((List.ofFn w).any fun b => b) = true).card = 2 ^ m - 1 := by
          have hall : (Finset.univ.filter fun w : Fin m → Bool =>
              ¬(((List.ofFn w).any fun b => b) = true)).card = 1 := by
            refine Finset.card_eq_one.mpr ⟨fun _ => false, Finset.ext fun w => ?_⟩
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Bool.not_eq_true,
              List.any_eq_false, List.mem_ofFn, forall_exists_index, forall_apply_eq_imp_iff,
              Finset.mem_singleton]
            exact ⟨fun h => funext h, fun h j => by rw [h]⟩
          have hpart := Finset.card_filter_add_card_filter_not
            (s := (Finset.univ : Finset (Fin m → Bool)))
            (p := fun w => ((List.ofFn w).any fun b => b) = true)
          rw [hall, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
            Fintype.card_fin] at hpart
          omega
        have hcount : acceptCount V' x (m + 1 + 1) =
            2 * acceptCount (fun q => !V q) x m + (2 ^ m - 1) := by
          rw [acceptCount, BitString.card_filter_ofFn_succ (m + 1) fun l => V' (x, l) = true,
            BitString.card_filter_ofFn_succ m fun l => V' (x, false :: l) = true,
            BitString.card_filter_ofFn_succ m fun l => V' (x, true :: l) = true]
          have h1 : (Finset.univ.filter fun w : Fin m → Bool =>
              V' (x, false :: false :: List.ofFn w) = true).card = 2 ^ m - 1 := by
            rw [← hzero]; congr 1; ext w
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, V', Set.mem_preimage, g,
              decPair, encPair_apply, encBits_apply, decPair_frame, List.headD_cons, List.tail_cons,
              Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.true_and, decide_eq_true_eq]
            by_cases h : ((List.ofFn w).any fun b => b) = true
            · rw [ite_eq_left h]; exact iff_of_true hyin h
            · rw [ite_eq_right h]; exact iff_of_false hyout h
          have h2 : (Finset.univ.filter fun w : Fin m → Bool =>
              V' (x, false :: true :: List.ofFn w) = true).card = 0 := by
            refine Finset.card_eq_zero.mpr (Finset.filter_eq_empty_iff.mpr fun w _ => ?_)
            simp only [V', Set.mem_preimage, g, decPair, encPair_apply, encBits_apply,
              decPair_frame, List.headD_cons, List.tail_cons, Bool.false_eq_true, ↓reduceIte,
              Bool.not_true, Bool.false_and, decide_eq_true_eq]
            exact hyout
          have h3 : (Finset.univ.filter fun w : Fin m → Bool =>
              V' (x, true :: false :: List.ofFn w) = true).card =
              acceptCount (fun q => !V q) x m := by
            unfold acceptCount; congr 1; ext w
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, V', V, Set.mem_preimage, g,
              decPair, encPair_apply, encBits_apply, decPair_frame, List.headD_cons, List.tail_cons,
              ↓reduceIte, decide_eq_true_eq, Set.mem_compl_iff, Bool.not_eq_true']
            exact decide_eq_false_iff_not.symm
          have h4 : (Finset.univ.filter fun w : Fin m → Bool =>
              V' (x, true :: true :: List.ofFn w) = true).card =
              acceptCount (fun q => !V q) x m := by
            unfold acceptCount; congr 1; ext w
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, V', V, Set.mem_preimage, g,
              decPair, encPair_apply, encBits_apply, decPair_frame, List.headD_cons, List.tail_cons,
              ↓reduceIte, decide_eq_true_eq, Set.mem_compl_iff, Bool.not_eq_true']
            exact decide_eq_false_iff_not.symm
          rw [h1, h2, h3, h4]; ring
        have hsum := acceptCount_add_acceptCount_not V x m
        have hpow : 1 ≤ 2 ^ m := Nat.one_le_two_pow
        have heval : (p + 2).eval x.length = m + 1 + 1 := by simp [m]
        rw [heval]
        change ¬(2 ^ m ≤ 2 * acceptCount V x m) ↔ 2 ^ (m + 1 + 1) ≤ 2 * acceptCount V' x (m + 1 + 1)
        rw [hcount, pow_succ, pow_succ]
        omega

/-- Every Wagner level is closed under tagged union. -/
theorem taggedUnion_mem_WagnerLevel {i : ℕ} {L₀ L₁ : Set (List Bool)}
    (h₀ : L₀ ∈ WagnerLevel i) (h₁ : L₁ ∈ WagnerLevel i) :
    taggedUnion L₀ L₁ ∈ WagnerLevel i := by
  classical
  induction i generalizing L₀ L₁ with
  | zero => exact taggedUnion_mem_CountingLevel (a := 0) h₀ h₁
  | succ i ih =>
    obtain ⟨B₀, hB₀, p₀, hL₀⟩ := h₀
    obtain ⟨B₁, hB₁, p₁, hL₁⟩ := h₁
    let decPair := Decoder.pair Decoder.bits Decoder.bits
    let g : List Bool → List Bool := fun z =>
      let xy := decPair.decode z
      if xy.1.headD false then
        true :: encPair encBits encBits (xy.1.tail, xy.2.take (p₁.eval xy.1.tail.length))
      else
        false :: encPair encBits encBits (xy.1.tail, xy.2.take (p₀.eval xy.1.tail.length))
    have hg : ComputableInPolyTime g encBits encBits := by
      have hx := (ComputableInPolyTime.fst encBits encBits).comp decPair.computableInPolyTime
      have hxt := ComputableInPolyTime.bitsTail.comp hx
      have hw := (ComputableInPolyTime.snd encBits encBits).comp decPair.computableInPolyTime
      have ht₀ := ComputableInPolyTime.bitsTakeWithInput hw
        ((ComputableInPolyTime.unary_eval p₀).comp (ComputableInPolyTime.length_bits_comp hxt))
      have ht₁ := ComputableInPolyTime.bitsTakeWithInput hw
        ((ComputableInPolyTime.unary_eval p₁).comp (ComputableInPolyTime.length_bits_comp hxt))
      have henc : ComputableInPolyTime (encPair encBits encBits) (encPair encBits encBits)
          encBits :=
        ComputableInPolyTime.of_eq (f := encPair encBits encBits) (encOut := encBits) fun _ => rfl
      exact ComputableInPolyTime.ite'
        ((ComputableInPolyTime.headD (encA := encBool) false).comp hx)
        (ComputableInPolyTime.bitsCons (.const true) (henc.comp (hxt.prod ht₁)))
        (ComputableInPolyTime.bitsCons (.const false) (henc.comp (hxt.prod ht₀)))
    have hB' : g ⁻¹' taggedUnion B₀ B₁ ∈ WagnerLevel i :=
      PolyTimeReducible.mem_WagnerLevel ⟨g, hg, fun _ => Iff.rfl⟩ (ih hB₀ hB₁)
    refine ⟨g ⁻¹' taggedUnion B₀ B₁, hB', p₀ + p₁, fun x => ?_⟩
    have htail : x.tail.length ≤ x.length := by simp only [List.length_tail]; omega
    have hp₀ : p₀.eval x.tail.length ≤ (p₀ + p₁).eval x.length := by
      simp only [Polynomial.eval_add]
      exact (Polynomial.eval_mono p₀ htail).trans (Nat.le_add_right _ _)
    have hp₁ : p₁.eval x.tail.length ≤ (p₀ + p₁).eval x.length := by
      simp only [Polynomial.eval_add]
      exact (Polynomial.eval_mono p₁ htail).trans (Nat.le_add_left _ _)
    change (if x.headD false then x.tail ∈ L₁ else x.tail ∈ L₀) ↔ _
    cases ht : x.headD false
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [hL₀ x.tail]
      refine (nonstrictMajority_take_iff hp₀ (fun w => ?_)).symm
      simp only [Set.mem_preimage, g, decPair, encPair_apply, encBits_apply, decPair_frame, ht,
        Bool.false_eq_true, ↓reduceIte, taggedUnion, Set.mem_ofPred_eq, List.headD_cons,
        List.tail_cons]
      exact decide_eq_decide.mpr Iff.rfl
    · simp only [↓reduceIte]
      rw [hL₁ x.tail]
      refine (nonstrictMajority_take_iff hp₁ (fun w => ?_)).symm
      simp only [Set.mem_preimage, g, decPair, encPair_apply, encBits_apply, decPair_frame, ht,
        ↓reduceIte, taggedUnion, Set.mem_ofPred_eq, List.headD_cons, List.tail_cons]
      exact decide_eq_decide.mpr Iff.rfl

/-- Universal quantification over polynomial-length bitstrings adds at most one Wagner level. -/
theorem forall_bits_mem_WagnerLevel {i : ℕ} {B : Set (List Bool)} (hB : B ∈ WagnerLevel i)
    (p : Polynomial ℕ) :
    {x | ∀ w : Fin (p.eval x.length) → Bool, encPair encBits encBits (x, List.ofFn w) ∈ B} ∈
      WagnerLevel (i + 1) := by
  classical
  by_cases hUniv : B = Set.univ
  · have : {x | ∀ w : Fin (p.eval x.length) → Bool,
        encPair encBits encBits (x, List.ofFn w) ∈ B} = Set.univ := by
      ext x; simp [hUniv]
    rw [this]; exact univ_mem_WagnerLevel (i + 1)
  · obtain ⟨yout, hyout⟩ : ∃ y, y ∉ B := by
      by_contra! hall; exact hUniv (Set.eq_univ_of_forall hall)
    let decPair := Decoder.pair Decoder.bits Decoder.bits
    let g : List Bool → List Bool := fun z =>
      let xy := decPair.decode z
      if xy.2.headD false then encPair encBits encBits (xy.1, xy.2.tail) else yout
    have hg : ComputableInPolyTime g encBits encBits := by
      have hx := (ComputableInPolyTime.fst encBits encBits).comp decPair.computableInPolyTime
      have hw := (ComputableInPolyTime.snd encBits encBits).comp decPair.computableInPolyTime
      have henc : ComputableInPolyTime (encPair encBits encBits) (encPair encBits encBits)
          encBits :=
        ComputableInPolyTime.of_eq (f := encPair encBits encBits) (encOut := encBits) fun _ => rfl
      exact ComputableInPolyTime.ite'
        ((ComputableInPolyTime.headD (encA := encBool) false).comp hw)
        (henc.comp (hx.prod (ComputableInPolyTime.bitsTail.comp hw)))
        (.const yout)
    have hB' : g ⁻¹' B ∈ WagnerLevel i :=
      PolyTimeReducible.mem_WagnerLevel ⟨g, hg, fun _ => Iff.rfl⟩ hB
    refine ⟨g ⁻¹' B, hB', p + 1, fun x => ?_⟩
    set m := p.eval x.length
    have heval : (p + 1).eval x.length = m + 1 := by simp [m]
    rw [heval]
    have hcount : acceptCount (fun q => decide (encPair encBits encBits q ∈ g ⁻¹' B)) x (m + 1) =
        (Finset.univ.filter fun w : Fin m → Bool =>
          encPair encBits encBits (x, List.ofFn w) ∈ B).card := by
      rw [acceptCount, BitString.card_filter_ofFn_succ m
        (fun l => decide (encPair encBits encBits (x, l) ∈ g ⁻¹' B) = true)]
      have hfalse : (Finset.univ.filter fun w : Fin m → Bool =>
          decide (encPair encBits encBits (x, false :: List.ofFn w) ∈ g ⁻¹' B) = true).card = 0 :=
        Finset.card_eq_zero.mpr (Finset.filter_eq_empty_iff.mpr fun w _ => by
          simp only [Set.mem_preimage, g, decPair, encPair_apply, encBits_apply, decPair_frame,
            List.headD_cons, Bool.false_eq_true, ↓reduceIte, decide_eq_true_eq]
          exact hyout)
      have htrue : (Finset.univ.filter fun w : Fin m → Bool =>
          decide (encPair encBits encBits (x, true :: List.ofFn w) ∈ g ⁻¹' B) = true).card =
          (Finset.univ.filter fun w : Fin m → Bool =>
            encPair encBits encBits (x, List.ofFn w) ∈ B).card := by
        congr 1; ext w
        rw [Finset.mem_filter, Finset.mem_filter]
        simp only [Finset.mem_univ, true_and, Set.mem_preimage, g, decPair,
          encPair_apply, encBits_apply, decPair_frame, List.headD_cons, List.tail_cons, ↓reduceIte,
          decide_eq_true_eq]
      rw [hfalse, htrue, add_zero]
    rw [hcount, pow_succ']
    have hcard_le : (Finset.univ.filter fun w : Fin m → Bool =>
        encPair encBits encBits (x, List.ofFn w) ∈ B).card ≤ 2 ^ m := by
      calc _ ≤ (Finset.univ : Finset (Fin m → Bool)).card := Finset.card_filter_le _ _
        _ = 2 ^ m := by simp
    have hcard_eq : (Finset.univ.filter fun w : Fin m → Bool =>
        encPair encBits encBits (x, List.ofFn w) ∈ B).card = 2 ^ m ↔
        ∀ w : Fin m → Bool, encPair encBits encBits (x, List.ofFn w) ∈ B := by
      rw [← show (Finset.univ : Finset (Fin m → Bool)).card = 2 ^ m by simp,
        Finset.card_filter_eq_iff]
      simp
    simp only [Set.mem_ofPred_eq]
    constructor
    · intro hall; rw [hcard_eq.mpr hall]
    · intro hle; exact hcard_eq.mp (by omega)

/-- Existential quantification over polynomial-length bitstrings adds at most one Wagner level. -/
theorem exists_bits_mem_WagnerLevel {i : ℕ} {B : Set (List Bool)} (hB : B ∈ WagnerLevel i)
    (p : Polynomial ℕ) :
    {x | ∃ w : Fin (p.eval x.length) → Bool, encPair encBits encBits (x, List.ofFn w) ∈ B} ∈
      WagnerLevel (i + 1) := by
  have hfor := forall_bits_mem_WagnerLevel (compl_mem_WagnerLevel hB) p
  have hcomp := compl_mem_WagnerLevel hfor
  convert hcomp using 1
  ext x
  simp [Set.mem_compl_iff]

/-- One step of simulating an oracle machine using a pre-supplied bitstring `replies` of oracle
answers indexed by the step counter `idx`. -/
private def replayStep {k m : ℕ} (machine : MultiTapePTM k Bool (Fin m) Unit)
    (replies : List Bool) (state : FiniteConfig k Bool (Fin m) Unit × ℕ) :
    FiniteConfig k Bool (Fin m) Unit × ℕ :=
  let nextCfg :=
    if (machine.pendingQuery state.1).isSome then
      machine.receiveBit (state.1, replies.getD state.2 false)
    else
      machine.localStep state.1
  (nextCfg, state.2 + 1)

private theorem replayStep_snd {k m : ℕ} (machine : MultiTapePTM k Bool (Fin m) Unit)
    (replies : List Bool) (cfg : FiniteConfig k Bool (Fin m) Unit) (t : ℕ) :
    ((replayStep machine replies)^[t] (cfg, 0)).2 = t := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply']; simp [replayStep, ih]

private theorem spaceBound_replayStep_fst {k m : ℕ} (machine : MultiTapePTM k Bool (Fin m) Unit)
    (replies : List Bool) (input : List Bool) (t : ℕ) :
    FiniteConfig.SpaceBound input.length t 1
      (((replayStep machine replies)^[t] (FiniteConfig.init machine.initial input, 0)).1) := by
  induction t with
  | zero => exact FiniteConfig.spaceBound_init _ _ _
  | succ t ih =>
    rw [Function.iterate_succ_apply']
    simp only [replayStep]
    split_ifs with hq
    · unfold MultiTapePTM.receiveBit
      cases hp : machine.pendingQuery _ with
      | none => exact ih.mono le_rfl (Nat.le_succ _) le_rfl
      | some opnext => exact ih.receive _ _ _ (by simp)
    · unfold MultiTapePTM.localStep
      cases _ : ((replayStep machine replies)^[t]
          (FiniteConfig.init machine.initial input, 0)).1.tapes.state with
      | none => exact ih.mono le_rfl (Nat.le_succ _) le_rfl
      | some ctrl =>
        simp only [Option.map_some]
        cases machine.tr ctrl _ _ _ false with
        | step a s mv => exact ih.step _ _ _
        | query _ _ => exact ih.mono le_rfl (Nat.le_succ _) le_rfl

private theorem spaceBound_iterate_languageOracle {k m : ℕ}
    (machine : MultiTapePTM k Bool (Fin m) Unit) (A : Set (List Bool)) (input : List Bool) (t : ℕ) :
    FiniteConfig.SpaceBound input.length t 1
      ((machine.answerStep (languageOracle A))^[t] (FiniteConfig.init machine.initial input)) := by
  classical
  induction t with
  | zero => exact FiniteConfig.spaceBound_init _ _ _
  | succ t ih =>
    rw [Function.iterate_succ_apply']
    exact machine.spaceBound_answerStep (fun w => decide (w ∈ A)) ih

private theorem replayStep_fst_eq_answerStep {k m : ℕ}
    (machine : MultiTapePTM k Bool (Fin m) Unit) (A : Set (List Bool))
    (replies : List Bool) (input : List Bool) :
    ∀ t, (∀ s < t,
      let cfg := ((replayStep machine replies)^[s] (FiniteConfig.init machine.initial input, 0)).1
      (machine.pendingQuery cfg).isSome = true →
      replies.getD s false =
        @decide (machine.pendingRequest cfg ∈ A) (Classical.propDecidable _)) →
      ((replayStep machine replies)^[t] (FiniteConfig.init machine.initial input, 0)).1 =
        (machine.answerStep (languageOracle A))^[t] (FiniteConfig.init machine.initial input) := by
  classical
  intro t
  induction t with
  | zero => intro _; rfl
  | succ t ih =>
    intro hgood
    have hprev := ih fun s hs => hgood s (Nat.lt_succ_of_lt hs)
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    have hbit := machine.answerStep_bit (fun w => decide (w ∈ A))
      ((machine.answerStep (languageOracle A))^[t] (FiniteConfig.init machine.initial input))
    have horacle : (fun q : Unit × List Bool => [decide (q.2 ∈ A)]) = languageOracle A := rfl
    rw [horacle] at hbit
    rw [hbit, ← hprev]
    simp only [replayStep, replayStep_snd]
    split_ifs with hq
    · rw [hgood t (Nat.lt_succ_self t) hq]
    · rfl

private theorem computableInPolyTime_replay {k m : ℕ}
    (machine : MultiTapePTM k Bool (Fin m) Unit) :
    ComputableInPolyTime
      (fun p : (List Bool × List Bool) × ℕ =>
        ((replayStep machine p.1.2)^[p.2] (FiniteConfig.init machine.initial p.1.1, 0)).1)
      (encPair (encPair encBits encBits) encUnary) encFiniteConfig := by
  obtain ⟨cf, hcf⟩ := length_encFiniteConfig_le (k := k) (State := Fin m) (Oracle := Unit)
  let encCfg := encFiniteConfig (k := k) (State := Fin m) (Oracle := Unit)
  have hstep : ComputableInPolyTime
      (fun q : List Bool × (FiniteConfig k Bool (Fin m) Unit × ℕ) =>
        replayStep machine q.1 q.2)
      (encPair encBits (encPair encCfg encUnary))
      (encPair encCfg encUnary) := by
    have hrep := ComputableInPolyTime.fst encBits (encPair encCfg encUnary)
    have hcfg := (ComputableInPolyTime.fst encCfg encUnary).comp
      (ComputableInPolyTime.snd encBits (encPair encCfg encUnary))
    have hidx := (ComputableInPolyTime.snd encCfg encUnary).comp
      (ComputableInPolyTime.snd encBits (encPair encCfg encUnary))
    have hcond : ComputableInPolyTime
        (fun q : List Bool × (FiniteConfig k Bool (Fin m) Unit × ℕ) =>
          (machine.pendingQuery q.2.1).isSome)
        (encPair encBits (encPair encCfg encUnary)) encBool :=
      ((ComputableInPolyTime.of_finite (α := Option (Unit × Fin m)) (encOut := encBool)
        Option.isSome).comp machine.pendingQuery_pt).comp hcfg
    have hbit := ComputableInPolyTime.bitsGetDWithInput hrep hidx false
    have hnext := ComputableInPolyTime.ite' hcond
      (machine.receiveBit_pt.comp (hcfg.prod hbit))
      (machine.localStep_pt.comp hcfg)
    have hsucc : ComputableInPolyTime
        (fun q : List Bool × (FiniteConfig k Bool (Fin m) Unit × ℕ) => q.2.2 + 1)
        (encPair encBits (encPair encCfg encUnary)) encUnary :=
      ((ComputableInPolyTime.unary_eval (Polynomial.X + 1)).of_enc_eq fun n => by simp).comp hidx
    exact hnext.prod hsucc
  have hpar := (ComputableInPolyTime.snd encBits encBits).comp
    (ComputableInPolyTime.fst (encPair encBits encBits) encUnary)
  have hcount := ComputableInPolyTime.snd (encPair encBits encBits) encUnary
  have hinit : ComputableInPolyTime
      (fun p : (List Bool × List Bool) × ℕ => (FiniteConfig.init machine.initial p.1.1, 0))
      (encPair (encPair encBits encBits) encUnary) (encPair encCfg encUnary) :=
    (ComputableInPolyTime.finiteConfig_init (k := k) (State := Fin m) (Oracle := Unit)
      ((ComputableInPolyTime.fst encBits encBits).comp
        (ComputableInPolyTime.fst (encPair encBits encBits) encUnary))
      machine.initial).prod (.const 0)
  have hbound : PolyBounded
      (fun p : (List Bool × List Bool) × ℕ =>
        (encPair (encPair encBits encBits) encUnary p).length)
      (fun p => 2 * (cf * (p.1.1.length + p.2 + 1 + 1)) + 1 + p.2) := by
    refine PolyBounded.of_forall_le (2 * cf + 4) 1 fun p => ?_
    simp only [length_encPair, encBits_apply, encUnary_apply, List.length_replicate, pow_one]
    nlinarith
  have hit := ComputableInPolyTime.iterateWith hpar hcount hinit hstep hbound fun p t ht => by
    simp only [Function.comp_apply, length_encPair, encUnary_apply, List.length_replicate,
      replayStep_snd]
    have hsb := spaceBound_replayStep_fst machine p.1.2 p.1.1 t
    have hlen : (encCfg (((replayStep machine p.1.2)^[t]
        (FiniteConfig.init machine.initial p.1.1, 0)).1)).length ≤
        cf * (p.1.1.length + p.2 + 1 + 1) :=
      (hcf _ _ _ _ hsb).trans (Nat.mul_le_mul_left cf (by omega))
    omega
  exact (ComputableInPolyTime.fst encCfg encUnary).comp hit

/-- Deterministic polynomial time relative to a Wagner-level oracle adds at most two Wagner
levels: guess the polynomial-length oracle reply transcript and universally verify every step. -/
theorem PWithOracle_subset_WagnerLevel {i : ℕ} {A : Set (List Bool)} (hA : A ∈ WagnerLevel i) :
    PWithOracle A encBits ⊆ WagnerLevel (i + 2) := by
  classical
  rintro L ⟨f, ⟨program, hcert, hprog⟩, hL⟩
  obtain ⟨k, m, machine, c, d, hrun⟩ := hcert.exists_fin_run_pure_false
  let pT : Polynomial ℕ := Polynomial.C c * (Polynomial.X + 1) ^ d
  have hpT (x : List Bool) : pT.eval x.length = c * (x.length + 1) ^ d := by simp [pT]
  let decPair := Decoder.pair Decoder.bits Decoder.bits
  let U : Set (List Bool) := taggedUnion A Aᶜ
  have hU : U ∈ WagnerLevel i := taggedUnion_mem_WagnerLevel hA (compl_mem_WagnerLevel hA)
  obtain ⟨yin, hyin, yout, hyout⟩ : ∃ yin ∈ U, ∃ yout, yout ∉ U := by
    by_cases h0 : ([] : List Bool) ∈ A
    · exact ⟨false :: [], by simpa [U, taggedUnion], true :: [], by simp [U, taggedUnion, h0]⟩
    · exact ⟨true :: [], by simpa [U, taggedUnion], false :: [], by simp [U, taggedUnion, h0]⟩
  let simCfg : (List Bool × List Bool) × ℕ → FiniteConfig k Bool (Fin m) Unit :=
    fun p => ((replayStep machine p.1.2)^[p.2] (FiniteConfig.init machine.initial p.1.1, 0)).1
  have hsim := computableInPolyTime_replay machine
  let checkMap : List Bool → List Bool := fun z =>
    let xru := decPair.decode z
    let xr := decPair.decode xru.1
    let T := pT.eval xr.1.length
    if !decide ((simCfg (xr, T)).tapes.output = [true]) then
      yout
    else
      let t := BitString.boundedBinaryValue T xru.2
      if decide (t < T) then
        let cfg := simCfg (xr, t)
        if (machine.pendingQuery cfg).isSome then
          if xr.2.getD t false then false :: machine.pendingRequest cfg
          else true :: machine.pendingRequest cfg
        else yin
      else yin
  have hcheckMap : ComputableInPolyTime checkMap encBits encBits := by
    have hxru := decPair.computableInPolyTime
    have hxr := decPair.computableInPolyTime.comp ((ComputableInPolyTime.fst _ _).comp hxru)
    have hx := (ComputableInPolyTime.fst _ _).comp hxr
    have hr := (ComputableInPolyTime.snd _ _).comp hxr
    have hu := (ComputableInPolyTime.snd _ _).comp hxru
    have hT := (ComputableInPolyTime.unary_eval pT).comp (ComputableInPolyTime.length_bits_comp hx)
    have houtBits : ComputableInPolyTime
        (fun cfg : FiniteConfig k Bool (Fin m) Unit => cfg.tapes.output)
        encFiniteConfig encBits := by fun_prop
    have hout := (houtBits.comp (hsim.comp (hxr.prod hT))).decide_eq' (.const [true])
    have ht := ComputableInPolyTime.bitsBoundedBinaryValueWithInput hT hu
    have hlt : ComputableInPolyTime (fun z => decide (BitString.boundedBinaryValue
        (pT.eval (decPair.decode (decPair.decode z).1).1.length) (decPair.decode z).2 <
        pT.eval (decPair.decode (decPair.decode z).1).1.length)) encBits encBool :=
      (show ComputableInPolyTime (fun p : ℕ × ℕ => decide (p.1 < p.2))
        (encPair encUnary encUnary) encBool by fun_prop).comp (ht.prod hT)
    have hcfg := hsim.comp (hxr.prod ht)
    have hisQ : ComputableInPolyTime
        (fun z => (machine.pendingQuery (simCfg (decPair.decode (decPair.decode z).1,
          BitString.boundedBinaryValue
            (pT.eval (decPair.decode (decPair.decode z).1).1.length) (decPair.decode z).2))).isSome)
        encBits encBool :=
      ((ComputableInPolyTime.of_finite (α := Option (Unit × Fin m)) (encOut := encBool)
        Option.isSome).comp machine.pendingQuery_pt).comp hcfg
    have hreq := machine.pendingRequest_pt.comp hcfg
    have hrbit := ComputableInPolyTime.bitsGetDWithInput hr ht false
    exact ComputableInPolyTime.ite' (ComputableInPolyTime.bool_not.comp hout) (.const yout)
      (ComputableInPolyTime.ite' hlt
        (ComputableInPolyTime.ite' hisQ
          (ComputableInPolyTime.ite' hrbit
            (ComputableInPolyTime.bitsCons (.const false) hreq)
            (ComputableInPolyTime.bitsCons (.const true) hreq))
          (.const yin))
        (.const yin))
  have hCheck : checkMap ⁻¹' U ∈ WagnerLevel i :=
    PolyTimeReducible.mem_WagnerLevel ⟨checkMap, hcheckMap, fun _ => Iff.rfl⟩ hU
  have hValid := forall_bits_mem_WagnerLevel hCheck pT
  have hAcc := exists_bits_mem_WagnerLevel hValid pT
  convert hAcc using 1
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_preimage]
  have hfx : (f x = true) ↔
      ((machine.answerStep (languageOracle A))^[pT.eval x.length]
        (FiniteConfig.init machine.initial x)).tapes.output = [true] := by
    have hrunx := hrun x (languageOracle A)
    simp only [encBits_apply] at hrunx
    rw [hprog x, ← hpT x,
      machine.interpret_run_pure_false (languageOracle A) (pT.eval x.length) x] at hrunx
    rw [hrunx]
    cases f x <;> simp
  rw [hL x, hfx]
  set T := pT.eval x.length
  constructor
  · intro hout
    let trueRep : Fin T → Bool := fun s =>
      decide (machine.pendingRequest ((machine.answerStep (languageOracle A))^[s.val]
        (FiniteConfig.init machine.initial x)) ∈ A)
    refine ⟨trueRep, fun u => ?_⟩
    have hagree : ∀ s ≤ T,
        simCfg ((x, List.ofFn trueRep), s) =
          (machine.answerStep (languageOracle A))^[s] (FiniteConfig.init machine.initial x) := by
      intro s
      induction s with
      | zero => intro _; rfl
      | succ s ih =>
        intro hs
        have hprev := ih (Nat.le_of_succ_le hs)
        change ((replayStep machine (List.ofFn trueRep))^[s + 1]
          (FiniteConfig.init machine.initial x, 0)).1 = _
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
        have hbit := machine.answerStep_bit (fun w => decide (w ∈ A))
          ((machine.answerStep (languageOracle A))^[s] (FiniteConfig.init machine.initial x))
        have horacle : (fun q : Unit × List Bool => [decide (q.2 ∈ A)]) = languageOracle A := rfl
        rw [horacle] at hbit
        rw [hbit]
        simp only [replayStep, replayStep_snd]
        change (if (machine.pendingQuery (simCfg ((x, List.ofFn trueRep), s))).isSome then
            machine.receiveBit (simCfg ((x, List.ofFn trueRep), s),
              (List.ofFn trueRep).getD s false)
          else machine.localStep (simCfg ((x, List.ofFn trueRep), s))) = _
        rw [hprev]
        have hget : (List.ofFn trueRep).getD s false = trueRep ⟨s, by omega⟩ := by
          simp [List.getD_eq_getElem?_getD, Nat.lt_of_succ_le hs]
        rw [hget]
    have hout' : (simCfg ((x, List.ofFn trueRep), T)).tapes.output = [true] := by
      rw [hagree T le_rfl, hout]
    have hdec1 : decPair.decode (encPair encBits encBits
        (encPair encBits encBits (x, List.ofFn trueRep), List.ofFn u)) =
        (encPair encBits encBits (x, List.ofFn trueRep), List.ofFn u) := decPair.decode_enc _
    have hdec2 : decPair.decode (encPair encBits encBits (x, List.ofFn trueRep)) =
        (x, List.ofFn trueRep) := decPair.decode_enc _
    dsimp only [checkMap]
    rw [hdec1, hdec2]
    change (if (!decide ((simCfg ((x, List.ofFn trueRep), T)).tapes.output = [true])) = true then
      yout else _) ∈ U
    rw [ite_eq_right (by simp [hout'])]
    set t := BitString.boundedBinaryValue T (List.ofFn u)
    by_cases htT : t < T
    · rw [ite_eq_left (by rw [decide_eq_true_eq]; exact htT)]
      by_cases hq : (machine.pendingQuery (simCfg ((x, List.ofFn trueRep), t))).isSome = true
      · rw [ite_eq_left hq]
        have hget : (List.ofFn trueRep).getD t false = trueRep ⟨t, htT⟩ := by
          rw [List.getD_eq_getElem _ _ (by simp [htT])]; simp
        rw [hget, hagree t htT.le]
        by_cases hmem : machine.pendingRequest ((machine.answerStep (languageOracle A))^[t]
            (FiniteConfig.init machine.initial x)) ∈ A
        · have htr : trueRep ⟨t, htT⟩ = true := decide_eq_true hmem
          rw [ite_eq_left htr]
          simpa [U, taggedUnion] using hmem
        · have htr : trueRep ⟨t, htT⟩ = false := decide_eq_false hmem
          rw [ite_eq_right (by rw [htr]; decide)]
          simpa [U, taggedUnion] using hmem
      · rw [ite_eq_right hq]; exact hyin
    · rw [ite_eq_right (by rw [decide_eq_true_eq]; exact htT)]; exact hyin
  · rintro ⟨r, hall⟩
    set M := pT.eval (encPair encBits encBits (x, List.ofFn r)).length
    have hTM : T ≤ M := Polynomial.eval_mono pT (by
      simp only [length_encPair, encBits_apply]; omega)
    have houtOk : (simCfg ((x, List.ofFn r), T)).tapes.output = [true] := by
      by_contra hne
      have h0 := hall (fun _ => false)
      have hdec1 : decPair.decode (encPair encBits encBits
          (encPair encBits encBits (x, List.ofFn r), List.ofFn fun _ : Fin M => false)) =
          (encPair encBits encBits (x, List.ofFn r), List.ofFn fun _ : Fin M => false) :=
        decPair.decode_enc _
      have hdec2 : decPair.decode (encPair encBits encBits (x, List.ofFn r)) =
          (x, List.ofFn r) := decPair.decode_enc _
      dsimp only [checkMap] at h0
      rw [hdec1, hdec2] at h0
      change (if (!decide ((simCfg ((x, List.ofFn r), T)).tapes.output = [true])) = true then
        yout else _) ∈ U at h0
      rw [ite_eq_left (by simp [hne])] at h0
      exact hyout h0
    have hgood : ∀ s < T,
        (machine.pendingQuery (simCfg ((x, List.ofFn r), s))).isSome = true →
        (List.ofFn r).getD s false =
          decide (machine.pendingRequest (simCfg ((x, List.ofFn r), s)) ∈ A) := by
      intro s hs hq
      have hsM : s < 2 ^ M := (hs.trans_le hTM).trans Nat.lt_two_pow_self
      let bw := BitString.binaryWord M s
      have hbwLen : bw.length = M := BitString.length_binaryWord hsM
      let u : Fin M → Bool := fun j => bw[j.val]'(by omega)
      have huList : List.ofFn u = bw :=
        List.ext_getElem (by simp [hbwLen]) fun j _ _ => by simp [u]
      have hbv : BitString.boundedBinaryValue T (List.ofFn u) = s := by
        rw [huList, BitString.boundedBinaryValue_eq, BitString.binaryValue_binaryWord M s,
          Nat.min_eq_right hs.le]
      have hu := hall u
      have hdec1 : decPair.decode (encPair encBits encBits
          (encPair encBits encBits (x, List.ofFn r), List.ofFn u)) =
          (encPair encBits encBits (x, List.ofFn r), List.ofFn u) := decPair.decode_enc _
      have hdec2 : decPair.decode (encPair encBits encBits (x, List.ofFn r)) =
          (x, List.ofFn r) := decPair.decode_enc _
      dsimp only [checkMap] at hu
      rw [hdec1, hdec2] at hu
      change (if (!decide ((simCfg ((x, List.ofFn r), T)).tapes.output = [true])) = true then
        yout else if decide (BitString.boundedBinaryValue T (List.ofFn u) < T) = true then _
        else yin) ∈ U at hu
      rw [ite_eq_right (by simp [houtOk]), hbv, ite_eq_left (by simp [hs]), ite_eq_left hq] at hu
      cases hrbit : (List.ofFn r).getD s false
      · rw [ite_eq_right (by rw [hrbit]; decide)] at hu
        exact (decide_eq_false (by simpa [U, taggedUnion] using hu)).symm
      · rw [ite_eq_left hrbit] at hu
        exact (decide_eq_true (by simpa [U, taggedUnion] using hu)).symm
    have heq := replayStep_fst_eq_answerStep machine A (List.ofFn r) x T hgood
    simpa [simCfg, heq] using houtOk

/-- `PP` relative to a Wagner-level oracle adds at most three Wagner levels. -/
theorem PPWithOracle_subset_WagnerLevel {i : ℕ} {A : Set (List Bool)} (hA : A ∈ WagnerLevel i) :
    PPWithOracle A encBits ⊆ WagnerLevel (i + 3) := by
  classical
  rintro L ⟨p, V, hV, hL⟩
  let decPair := Decoder.pair Decoder.bits Decoder.bits
  have hBV : {z | V (decPair.decode z) = true} ∈ PWithOracle A encBits :=
    ⟨fun z => V (decPair.decode z), hV.preprocess decPair.computableInPolyTime, fun _ => Iff.rfl⟩
  have hBVc : ({z | V (decPair.decode z) = true})ᶜ ∈ WagnerLevel (i + 2) :=
    compl_mem_WagnerLevel (PWithOracle_subset_WagnerLevel hA hBV)
  have hLc : Lᶜ ∈ WagnerLevel (i + 3) := by
    refine ⟨({z | V (decPair.decode z) = true})ᶜ, hBVc, p, fun x => ?_⟩
    rw [Set.mem_compl_iff, hL x]
    have hsum := acceptCount_add_acceptCount_not V x (p.eval x.length)
    simp only [encBits_apply]
    suffices h : acceptCount (fun q => @decide _ (Classical.propDecidable
        (encPair encBits encBits q ∈ ({z | V (decPair.decode z) = true})ᶜ))) x
        (p.eval x.length) = acceptCount (fun q => !V q) x (p.eval x.length) by
      rw [h]; omega
    exact acceptCount_congr (fun w => by
      rw [Bool.eq_iff_iff, @decide_eq_true_eq _ (Classical.propDecidable _), Set.mem_compl_iff,
        Set.mem_ofPred_eq, encPair_apply, encBits_apply, decPair_frame, Bool.not_eq_true',
        Bool.eq_false_iff]
      rfl) _
  simpa using compl_mem_WagnerLevel hLc

/-- Every Wagner level `C_i P` is contained in the oracle-based counting level `CountingLevel i`. -/
theorem WagnerLevel_subset_CountingLevel (i : ℕ) : WagnerLevel i ⊆ CountingLevel i encBits := by
  classical
  induction i with
  | zero => exact Set.Subset.rfl
  | succ i ih =>
    rintro A ⟨B, hB, p, hAB⟩
    refine ⟨B, ih hB, ?_⟩
    rw [mem_PPWithOracle_iff_exists_GapPWithOracle]
    let V : List Bool × List Bool → Bool := fun q => decide (encPair encBits encBits q ∈ B)
    have hV : ComputableInPolyTimeWithOracle B V (encPair encBits encBits) encBool :=
      (computableInPolyTimeWithOracle_mem B).preprocess
        (ComputableInPolyTime.of_eq (f := encPair encBits encBits) (encOut := encBits) fun _ => rfl)
    let f : List Bool → ℕ := fun x => acceptCount V x (p.eval x.length)
    have hf : f ∈ SharpPWithOracle B encBits := ⟨p, V, hV, fun _ => rfl⟩
    let one : List Bool → ℕ := fun _ => 1
    have hone : one ∈ SharpPWithOracle B encBits :=
      SharpP_subset_SharpPWithOracle B encBits
        ⟨0, fun _ => true, .const true, fun x => by simp [one, acceptCount_zero]⟩
    have hpow : (fun x : List Bool => 2 ^ p.eval x.length) ∈ SharpPWithOracle B encBits :=
      SharpP_subset_SharpPWithOracle B encBits
        ⟨p, fun _ => true, .const true, fun x => by simp [acceptCount_true]⟩
    let f1 : List Bool → ℕ := f + f + one
    have hf1 : f1 ∈ SharpPWithOracle B encBits :=
      SharpPWithOracle.add_mem (SharpPWithOracle.add_mem hf hf) hone
    refine ⟨fun x => (f1 x : ℤ) - ((2 ^ p.eval x.length : ℕ) : ℤ),
      ⟨f1, hf1, fun x => 2 ^ p.eval x.length, hpow, fun _ => rfl⟩, fun x => ?_⟩
    rw [hAB x]
    simp only [f1, Pi.add_apply, f, one, V]
    omega

/-- Every oracle-based counting level `CountingLevel a` lies in `WagnerLevel (3 * a)`. -/
theorem CountingLevel_subset_WagnerLevel (a : ℕ) :
    CountingLevel a encBits ⊆ WagnerLevel (3 * a) := by
  induction a with
  | zero => exact Set.Subset.rfl
  | succ a ih =>
    rintro L ⟨A, hA, hL⟩
    exact PPWithOracle_subset_WagnerLevel (ih hA) hL

/-- **Equivalence of counting hierarchies**: Wagner's `C`-operator hierarchy `CH = ⋃ i, C_i P`
equals the oracle-based counting hierarchy `⋃ a, CountingLevel a encBits`. -/
theorem CH_eq_iUnion_CountingLevel : CH = ⋃ a, CountingLevel a encBits := by
  ext L
  simp only [CH, Set.mem_iUnion]
  exact ⟨fun ⟨i, hi⟩ => ⟨i, WagnerLevel_subset_CountingLevel i hi⟩,
    fun ⟨a, ha⟩ => ⟨3 * a, CountingLevel_subset_WagnerLevel a ha⟩⟩

/-- Every oracle-based counting level is contained in `CH`. -/
theorem CountingLevel_subset_CH (a : ℕ) : CountingLevel a encBits ⊆ CH :=
  fun _ h => CH_eq_iUnion_CountingLevel ▸ Set.mem_iUnion.mpr ⟨a, h⟩

/-- Every Boolean `CountingFunction` defines a decision language in `CH`. -/
theorem CountingFunction.mem_CH {a : ℕ} {f : List Bool → Bool}
    (hf : f ∈ CountingFunction a encBits encBool) : {x | f x = true} ∈ CH :=
  CountingLevel_subset_CH (a + 1) (CountingFunction.decision hf)

/-- `CH` is closed under polynomial-time many-one reductions. -/
theorem PolyTimeReducible.mem_CH {L M : Set (List Bool)}
    (h : PolyTimeReducible encBits encBits L M) (hM : M ∈ CH) : L ∈ CH := by
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hM
  exact Set.mem_iUnion.mpr ⟨i, PolyTimeReducible.mem_WagnerLevel h hi⟩

/-- `CH` is closed under complement. -/
theorem compl_mem_CH {A : Set (List Bool)} (hA : A ∈ CH) : Aᶜ ∈ CH := by
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hA
  exact Set.mem_iUnion.mpr ⟨i, compl_mem_WagnerLevel hi⟩

/-- `CH` is closed under tagged union. -/
theorem taggedUnion_mem_CH {A B : Set (List Bool)} (hA : A ∈ CH) (hB : B ∈ CH) :
    taggedUnion A B ∈ CH := by
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hA
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hB
  exact Set.mem_iUnion.mpr ⟨max i j,
    taggedUnion_mem_WagnerLevel (WagnerLevel_mono (le_max_left _ _) hi)
      (WagnerLevel_mono (le_max_right _ _) hj)⟩

/-- `P ⊆ CH`. -/
theorem P_subset_CH : P encBits ⊆ CH :=
  fun _ h => Set.mem_iUnion.mpr ⟨0, h⟩

/-- `PP ⊆ CH`. -/
theorem PP_subset_CH : PP encBits ⊆ CH :=
  fun _ h => Set.mem_iUnion.mpr ⟨1, WagnerLevel_one_eq_PP.symm ▸ h⟩

/-- `CH ⊆ PSPACE`. -/
theorem CH_subset_PSPACE : CH ⊆ PSPACE encBits := by
  rw [CH_eq_iUnion_CountingLevel]
  exact Set.iUnion_subset fun a => CountingLevel_subset_PSPACE a

/-! ### Karp–Lipton Advice Classes `K/poly`, `P/poly`, and `CH/poly` -/

/-- Karp–Lipton nonuniform advice operator `K/poly`: languages `A` decided by a language `B ∈ K`
given a polynomially bounded advice word `a(|x|)` paired with `x`. -/
def WithPolyAdvice (K : Set (Set (List Bool))) : Set (Set (List Bool)) :=
  {A | ∃ B ∈ K, ∃ (p : Polynomial ℕ) (a : ℕ → List Bool),
    (∀ n, (a n).length ≤ p.eval n) ∧
    ∀ x, x ∈ A ↔ encPair encBits encBits (x, a x.length) ∈ B}

/-- The nonuniform counting hierarchy `CH/poly`. -/
def CHPoly : Set (Set (List Bool)) :=
  WithPolyAdvice CH

/-- The nonuniform polynomial-time class `P/poly` defined via Karp–Lipton advice. -/
def PPolyClass : Set (Set (List Bool)) :=
  WithPolyAdvice (P encBits)

/-- Monotonicity of `WithPolyAdvice`. -/
theorem WithPolyAdvice.mono {K₁ K₂ : Set (Set (List Bool))} (h : K₁ ⊆ K₂) :
    WithPolyAdvice K₁ ⊆ WithPolyAdvice K₂ := by
  rintro A ⟨B, hB, p, a, ha, hAB⟩
  exact ⟨B, h hB, p, a, ha, hAB⟩

/-- Any language in a class `K` closed under polynomial-time reductions lies in `K/poly`. -/
theorem subset_WithPolyAdvice {K : Set (Set (List Bool))}
    (hK : ∀ {L M}, PolyTimeReducible encBits encBits L M → M ∈ K → L ∈ K) :
    K ⊆ WithPolyAdvice K := by
  intro A hA
  let decPair := Decoder.pair Decoder.bits Decoder.bits
  refine ⟨(fun z => (decPair.decode z).1) ⁻¹' A,
    hK ⟨fun z => (decPair.decode z).1,
      (ComputableInPolyTime.fst encBits encBits).comp decPair.computableInPolyTime,
      fun _ => Iff.rfl⟩ hA,
    0, fun _ => [], fun _ => by simp, fun x => ?_⟩
  simp only [Set.mem_preimage, encPair_apply, encBits_apply, decPair, decPair_frame]

/-- `P/poly` via Karp–Lipton advice equals circuit `P/poly` (`Cslib.Circuits.Boolean.PPoly`). -/
theorem PPolyClass_eq_PPoly : PPolyClass = PPoly := by
  rw [PPoly_eq_PAdvice]
  ext L
  let decPair := Decoder.pair Decoder.bits Decoder.bits
  constructor
  · rintro ⟨B, ⟨f, hf, hBf⟩, p, a, ha, hLB⟩
    refine ⟨a, PolynomiallyBounded.mono_of_le (g := fun n => p.eval n) (by fun_prop) ha,
      {q : List Bool × List Bool | encPair encBits encBits (q.2, q.1) ∈ B}, ?_, fun x => hLB x⟩
    refine ⟨fun q => f (encPair encBits encBits (q.2, q.1)), ?_, fun q => ?_⟩
    · exact hf.comp ((ComputableInPolyTime.of_eq (f := encPair encBits encBits)
        (encOut := encBits) fun _ => rfl).comp
        ((ComputableInPolyTime.snd encBits encBits).prod
          (ComputableInPolyTime.fst encBits encBits)))
    · exact hBf (encPair encBits encBits (q.2, q.1))
  · rintro ⟨a, ha, A, ⟨f, hf, hAf⟩, hLA⟩
    obtain ⟨c, d, hcd⟩ := polynomiallyBounded_iff_le.mp ha
    let p : Polynomial ℕ := Polynomial.C c * (Polynomial.X + 1) ^ d
    refine ⟨{z | f ((decPair.decode z).2, (decPair.decode z).1) = true},
      ⟨fun z => f ((decPair.decode z).2, (decPair.decode z).1),
        hf.comp (((ComputableInPolyTime.snd encBits encBits).comp
          decPair.computableInPolyTime).prod
          ((ComputableInPolyTime.fst encBits encBits).comp decPair.computableInPolyTime)),
        fun _ => Iff.rfl⟩,
      p, a, fun n => by simpa [p] using hcd n, fun x => ?_⟩
    have h1 : x ∈ (L : Language Bool) ↔ (a x.length, x) ∈ A := hLA x
    rw [show (x ∈ L) = (x ∈ (L : Language Bool)) from rfl, h1, hAf]
    simp only [Set.mem_ofPred_eq, encPair_apply, encBits_apply, decPair, decPair_frame]

/-- `P/poly ⊆ CH/poly`. -/
theorem PPolyClass_subset_CHPoly : PPolyClass ⊆ CHPoly :=
  WithPolyAdvice.mono P_subset_CH

/-- `CH ⊆ CH/poly`. -/
theorem CH_subset_CHPoly : CH ⊆ CHPoly :=
  subset_WithPolyAdvice fun h hM => PolyTimeReducible.mem_CH h hM

/-- `P ⊆ PPolyClass`. -/
theorem P_subset_PPolyClass : P encBits ⊆ PPolyClass :=
  subset_WithPolyAdvice fun h hM => h.mem_P hM

/-- Helper: any advice class `WithPolyAdvice K` is closed under polynomial-time many-one
reductions whenever `K` is. -/
theorem PolyTimeReducible.mem_WithPolyAdvice {K : Set (Set (List Bool))}
    (hK : ∀ {L M}, PolyTimeReducible encBits encBits L M → M ∈ K → L ∈ K)
    {L M : Set (List Bool)} (h : PolyTimeReducible encBits encBits L M)
    (hM : M ∈ WithPolyAdvice K) : L ∈ WithPolyAdvice K := by
  obtain ⟨f, hf, hLM⟩ := h
  obtain ⟨B, hB, p, a, ha, hMB⟩ := hM
  obtain ⟨q, hq⟩ := hf.exists_polynomial_eval_length_le Polynomial.X
  have hflen (x : List Bool) : (f x).length ≤ q.eval x.length := by
    simpa [encBits_apply] using hq x
  let a' : ℕ → List Bool := fun n => encList encBits ((List.range (q.eval n + 1)).map a)
  have ha' : ∃ p' : Polynomial ℕ, ∀ n, (a' n).length ≤ p'.eval n := by
    have hpoly : PolynomiallyBounded (fun n => (a' n).length) := by
      have hlen_le (n : ℕ) : (a' n).length ≤ (q.eval n + 1) * (2 * p.eval (q.eval n) + 1) := by
        rw [show (a' n).length =
            ((List.range (q.eval n + 1)).map fun k => (frame (a k)).length).sum by
          rw [length_encList_bits, List.map_map]; rfl]
        calc ((List.range (q.eval n + 1)).map fun k => (frame (a k)).length).sum
            ≤ ((List.range (q.eval n + 1)).map fun _ => 2 * p.eval (q.eval n) + 1).sum := by
              apply List.sum_le_sum
              intro k hk
              have hk' : k ≤ q.eval n := Nat.lt_succ_iff.mp (List.mem_range.mp hk)
              rw [length_frame]
              have := (ha k).trans (Polynomial.eval_mono p hk')
              omega
          _ = (q.eval n + 1) * (2 * p.eval (q.eval n) + 1) := by
              simp [List.sum_replicate, smul_eq_mul]
      exact PolynomiallyBounded.mono_of_le (g := fun n =>
        (q.eval n + 1) * (2 * p.eval (q.eval n) + 1)) (by fun_prop) hlen_le
    obtain ⟨c, d, hcd⟩ := polynomiallyBounded_iff_le.mp hpoly
    exact ⟨Polynomial.C c * (Polynomial.X + 1) ^ d, fun n => by simpa using hcd n⟩
  obtain ⟨p', hp'⟩ := ha'
  let decPair := Decoder.pair Decoder.bits Decoder.bits
  let decList := Decoder.list Decoder.bits
  let red : List Bool → List Bool := fun z =>
    let xy := decPair.decode z
    let fx := f xy.1
    let tbl := decList.decode xy.2
    encPair encBits encBits (fx, tbl.getD fx.length [])
  have hred : ComputableInPolyTime red encBits encBits := by
    have hx := (ComputableInPolyTime.fst encBits encBits).comp decPair.computableInPolyTime
    have hfx := hf.comp hx
    have htbl := decList.computableInPolyTime.comp
      ((ComputableInPolyTime.snd encBits encBits).comp decPair.computableInPolyTime)
    have hget : ComputableInPolyTime (fun z => (decList.decode (decPair.decode z).2).getD
        (f (decPair.decode z).1).length []) encBits encBits :=
      (ComputableInPolyTime.listGetD (encA := encBits) []).comp
        (htbl.prod (ComputableInPolyTime.length_bits_comp hfx))
    exact (ComputableInPolyTime.of_eq (f := encPair encBits encBits) (encOut := encBits)
      fun _ => rfl).comp (hfx.prod hget)
  refine ⟨red ⁻¹' B, hK ⟨red, hred, fun _ => Iff.rfl⟩ hB, p', a', hp', fun x => ?_⟩
  rw [hLM x, hMB (f x)]
  simp only [Set.mem_preimage, red, decPair.decode_enc, a', decList.decode_enc]
  have hlt : (f x).length < ((List.range (q.eval x.length + 1)).map a).length := by
    simp [hflen x]
  have hget : ((List.range (q.eval x.length + 1)).map a).getD (f x).length [] = a (f x).length := by
    rw [List.getD_eq_getElem _ _ hlt]; simp
  rw [hget]

/-- `CH/poly` is closed under polynomial-time many-one reductions. -/
theorem PolyTimeReducible.mem_CHPoly {L M : Set (List Bool)}
    (h : PolyTimeReducible encBits encBits L M) (hM : M ∈ CHPoly) : L ∈ CHPoly :=
  PolyTimeReducible.mem_WithPolyAdvice (fun h' hM' => PolyTimeReducible.mem_CH h' hM') h hM

/-- `P/poly` is closed under polynomial-time many-one reductions. -/
theorem PolyTimeReducible.mem_PPolyClass {L M : Set (List Bool)}
    (h : PolyTimeReducible encBits encBits L M) (hM : M ∈ PPolyClass) : L ∈ PPolyClass :=
  PolyTimeReducible.mem_WithPolyAdvice (fun h' hM' => h'.mem_P hM') h hM

/-- `CH/poly` is closed under complement. -/
theorem compl_mem_CHPoly {A : Set (List Bool)} (hA : A ∈ CHPoly) : Aᶜ ∈ CHPoly := by
  obtain ⟨B, hB, p, a, ha, hAB⟩ := hA
  exact ⟨Bᶜ, compl_mem_CH hB, p, a, ha, fun x => by simp [Set.mem_compl_iff, hAB x]⟩

/-- One step of simulating an oracle machine using `evalAdvice` for a `P/poly` oracle. -/
private def adviceOracleStep {k m : ℕ} (machine : MultiTapePTM k Bool (Fin m) Unit)
    (S W : Polynomial ℕ) (par : ℕ × List Bool)
    (cfg : FiniteConfig k Bool (Fin m) Unit) : FiniteConfig k Bool (Fin m) Unit :=
  machine.answerStep (fun q => [evalAdvice (S.eval par.1) (W.eval par.1) par.2 q.2]) cfg

private theorem computableInPolyTime_adviceOracleStep {k m : ℕ}
    (machine : MultiTapePTM k Bool (Fin m) Unit) (S W : Polynomial ℕ) :
    ComputableInPolyTime
      (fun p : (ℕ × List Bool) × FiniteConfig k Bool (Fin m) Unit =>
        adviceOracleStep machine S W p.1 p.2)
      (encPair (encPair encUnary encBits) encFiniteConfig) encFiniteConfig := by
  have hpar := ComputableInPolyTime.fst (encPair encUnary encBits)
    (encFiniteConfig (k := k) (State := Fin m) (Oracle := Unit))
  have hn := (ComputableInPolyTime.fst encUnary encBits).comp hpar
  have hu := (ComputableInPolyTime.snd encUnary encBits).comp hpar
  have hcfg := ComputableInPolyTime.snd (encPair encUnary encBits)
    (encFiniteConfig (k := k) (State := Fin m) (Oracle := Unit))
  have hcond : ComputableInPolyTime
      (fun p : (ℕ × List Bool) × FiniteConfig k Bool (Fin m) Unit =>
        (machine.pendingQuery p.2).isSome)
      (encPair (encPair encUnary encBits) encFiniteConfig) encBool :=
    ((ComputableInPolyTime.of_finite (α := Option (Unit × Fin m)) (encOut := encBool)
      Option.isSome).comp machine.pendingQuery_pt).comp hcfg
  have hreq := machine.pendingRequest_pt.comp hcfg
  have heval := computableInPolyTime_evalAdvice_eval S W hn hu hreq
  refine (ComputableInPolyTime.ite' hcond
    (machine.receiveBit_pt.comp (hcfg.prod heval))
    (machine.localStep_pt.comp hcfg)).of_enc_eq fun p => ?_
  exact congrArg encFiniteConfig
    (machine.answerStep_bit (fun w => evalAdvice (S.eval p.1.1) (W.eval p.1.1) p.1.2 w) p.2)

/-- If `PP ⊆ P/poly`, then every oracle-based counting level `CountingLevel a` lies in `P/poly`. -/
theorem CountingLevel_subset_PPoly_of_PP_subset_PPoly (hPP : PP encBits ⊆ PPoly) (a : ℕ) :
    CountingLevel a encBits ⊆ PPoly := by
  classical
  induction a with
  | zero =>
    rw [CountingLevel_zero, ← PPolyClass_eq_PPoly]
    exact P_subset_PPolyClass
  | succ a ih =>
    rintro L ⟨A, hA, p, V, ⟨program, hcert, hprog⟩, hVL⟩
    have hAPPoly : A ∈ PPoly := ih hA
    obtain ⟨k, m, machine, c, d, hrun⟩ := hcert.exists_fin_run_pure_false
    let N : Polynomial ℕ := Polynomial.C c * (2 * Polynomial.X + p + 2) ^ d
    obtain ⟨S, W, P_len, α, hαlen, hαpoly, hαeval⟩ := PPoly.exists_evalAdvice hAPPoly N
    obtain ⟨cf, hcf⟩ := length_encFiniteConfig_le (k := k) (State := Fin m) (Oracle := Unit)
    let decPair := Decoder.pair Decoder.bits Decoder.bits
    let inp : List Bool × List Bool → List Bool := fun zr =>
      let ux := decPair.decode zr.1
      encPair encBits encBits (ux.2, zr.2.take (p.eval ux.2.length))
    let clock : List Bool × List Bool → ℕ := fun zr => c * ((inp zr).length + 1) ^ d
    let runCfg : List Bool × List Bool → FiniteConfig k Bool (Fin m) Unit := fun zr =>
      let ux := decPair.decode zr.1
      (adviceOracleStep machine S W (ux.2.length, ux.1))^[clock zr]
        (FiniteConfig.init machine.initial (inp zr))
    let Vraw : List Bool × List Bool → Bool := fun zr => (runCfg zr).tapes.output.headD false
    have hVraw : ComputableInPolyTime Vraw (encPair encBits encBits) encBool := by
      have hz := ComputableInPolyTime.fst encBits encBits
      have hr := ComputableInPolyTime.snd encBits encBits
      have hux := decPair.computableInPolyTime.comp hz
      have hu := (ComputableInPolyTime.fst encBits encBits).comp hux
      have hx := (ComputableInPolyTime.snd encBits encBits).comp hux
      have hxlen := ComputableInPolyTime.length_bits_comp hx
      have hrtake := ComputableInPolyTime.bitsTakeWithInput hr
        ((ComputableInPolyTime.unary_eval p).comp hxlen)
      have hinp : ComputableInPolyTime inp (encPair encBits encBits) encBits :=
        (ComputableInPolyTime.of_eq (f := encPair encBits encBits) (encOut := encBits)
          fun _ => rfl).comp (hx.prod hrtake)
      have hclock : ComputableInPolyTime clock (encPair encBits encBits) encUnary :=
        ((ComputableInPolyTime.unary_eval (Polynomial.C c * (Polynomial.X + 1) ^ d)).comp
          (ComputableInPolyTime.length_bits_comp hinp)).of_enc_eq fun zr => by simp [clock]
      have hinit : ComputableInPolyTime
          (fun zr : List Bool × List Bool => FiniteConfig.init machine.initial (inp zr))
          (encPair encBits encBits) encFiniteConfig :=
        ComputableInPolyTime.finiteConfig_init (k := k) (State := Fin m) (Oracle := Unit)
          hinp machine.initial
      obtain ⟨c1, d1, h1⟩ := hinp.polyBounded_length.exists_le
      obtain ⟨c2, d2, h2⟩ := hclock.polyBounded.exists_le
      have hbound : PolyBounded
          (fun zr : List Bool × List Bool => (encPair encBits encBits zr).length)
          (fun zr => cf * ((inp zr).length + clock zr + 1 + 1)) := by
        refine PolyBounded.of_forall_le (cf * (c1 + c2 + 2)) (d1 + d2) fun zr => ?_
        set L := (encPair encBits encBits zr).length
        have hL1 : (L + 1) ^ d1 ≤ (L + 1) ^ (d1 + d2) :=
          Nat.pow_le_pow_right (Nat.succ_pos L) (Nat.le_add_right _ _)
        have hL2 : (L + 1) ^ d2 ≤ (L + 1) ^ (d1 + d2) :=
          Nat.pow_le_pow_right (Nat.succ_pos L) (Nat.le_add_left _ _)
        have hL0 : 1 ≤ (L + 1) ^ (d1 + d2) := Nat.one_le_pow _ _ (Nat.succ_pos L)
        have h1' : (inp zr).length ≤ c1 * (L + 1) ^ d1 := h1 zr
        have h2' : clock zr ≤ c2 * (L + 1) ^ d2 := h2 zr
        calc cf * ((inp zr).length + clock zr + 1 + 1)
            ≤ cf * ((c1 + c2 + 2) * (L + 1) ^ (d1 + d2)) :=
              Nat.mul_le_mul_left cf (by nlinarith)
          _ = cf * (c1 + c2 + 2) * (L + 1) ^ (d1 + d2) := by ring
      have hrunCfg : ComputableInPolyTime runCfg (encPair encBits encBits) encFiniteConfig :=
        ComputableInPolyTime.iterateWith (hxlen.prod hu) hclock hinit
          (computableInPolyTime_adviceOracleStep machine S W) hbound fun zr i hi => by
          have hsb : FiniteConfig.SpaceBound (inp zr).length i 1
              ((adviceOracleStep machine S W
                ((decPair.decode zr.1).2.length, (decPair.decode zr.1).1))^[i]
                (FiniteConfig.init machine.initial (inp zr))) := by
            clear hi
            induction i with
            | zero => exact FiniteConfig.spaceBound_init _ _ _
            | succ i ih =>
              rw [Function.iterate_succ_apply']
              exact machine.spaceBound_answerStep _ ih
          exact (hcf _ _ _ _ hsb).trans (Nat.mul_le_mul_left cf (by omega))
      have hout : ComputableInPolyTime
          (fun cfg : FiniteConfig k Bool (Fin m) Unit => cfg.tapes.output.headD false)
          encFiniteConfig encBool := by fun_prop
      exact hout.comp hrunCfg
    let Mraw : Set (List Bool) :=
      {z | 2 ^ p.eval z.length < 2 * acceptCount Vraw z (p.eval z.length)}
    have hMraw_PP : Mraw ∈ PP encBits := ⟨p, Vraw, hVraw, fun _ => Iff.rfl⟩
    have hMraw_PPoly : Mraw ∈ PPoly := hPP hMraw_PP
    refine PPoly.of_advice hMraw_PPoly α hαpoly fun x => ?_
    set z := frame (α x.length) ++ x
    have hz_eq : z = encPair encBits encBits (α x.length, x) := rfl
    have hlen_le : x.length ≤ z.length := by simp [z, length_frame]
    have hple : p.eval x.length ≤ p.eval z.length := Polynomial.eval_mono p hlen_le
    have hVeq : ∀ w : List Bool, w.length = p.eval z.length →
        Vraw (z, w) = V (x, w.take (p.eval x.length)) := by
      intro w hw
      set r := w.take (p.eval x.length)
      have hrlen : r.length = p.eval x.length := by
        simp [r, List.length_take, hw, Nat.min_eq_left hple]
      have hinp_eq : inp (z, w) = encPair encBits encBits (x, r) := by
        simp only [inp, z, decPair, decPair_frame, r]
      have hclock_eq : clock (z, w) = c * ((encPair encBits encBits (x, r)).length + 1) ^ d := by
        simp [clock, hinp_eq]
      have hclock_le_N : clock (z, w) ≤ N.eval x.length := by
        rw [hclock_eq]
        have hpairLen : (encPair encBits encBits (x, r)).length + 1 =
            2 * x.length + p.eval x.length + 2 := by
          simp only [length_encPair, encBits_apply, hrlen]; omega
        rw [hpairLen]
        simp only [N, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
          Polynomial.eval_add, Polynomial.eval_ofNat, Polynomial.eval_X, le_rfl]
      have hiter : ∀ s ≤ clock (z, w),
          (adviceOracleStep machine S W (x.length, α x.length))^[s]
            (FiniteConfig.init machine.initial (encPair encBits encBits (x, r))) =
          (machine.answerStep (languageOracle A))^[s]
            (FiniteConfig.init machine.initial (encPair encBits encBits (x, r))) := by
        intro s
        induction s with
        | zero => intro _; rfl
        | succ s ih =>
          intro hs
          rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih (Nat.le_of_succ_le hs)]
          set cur := (machine.answerStep (languageOracle A))^[s]
            (FiniteConfig.init machine.initial (encPair encBits encBits (x, r)))
          have hsb := spaceBound_iterate_languageOracle machine A (encPair encBits encBits (x, r)) s
          have hreq_le : (machine.pendingRequest cur).length ≤ N.eval x.length :=
            (machine.length_pendingRequest_le hsb).trans (by omega)
          have hbit1 := machine.answerStep_bit
            (fun q => evalAdvice (S.eval x.length) (W.eval x.length) (α x.length) q) cur
          have hbit2 := machine.answerStep_bit (fun q => decide (q ∈ A)) cur
          have hagree : evalAdvice (S.eval x.length) (W.eval x.length) (α x.length)
              (machine.pendingRequest cur) = decide (machine.pendingRequest cur ∈ A) :=
            Bool.eq_iff_iff.mpr ((hαeval x.length _ hreq_le).trans decide_eq_true_iff.symm)
          change machine.answerStep (fun q =>
            [evalAdvice (S.eval x.length) (W.eval x.length) (α x.length) q.2]) cur =
            machine.answerStep (fun q => [decide (q.2 ∈ A)]) cur
          rw [hbit1, hbit2, hagree]
      have hrun_eq : (runCfg (z, w)).tapes.output = encBool (V (x, r)) := by
        dsimp only [runCfg]
        rw [show decPair.decode z = (α x.length, x) from decPair_frame _ _,
          hinp_eq, hiter (clock (z, w)) le_rfl, hclock_eq,
          ← machine.interpret_run_pure_false (languageOracle A),
          hrun (x, r) (languageOracle A), hprog (x, r)]
      simp only [Vraw, hrun_eq, encBool_apply, List.headD_cons]
    have hcount_eq : acceptCount Vraw z (p.eval z.length) =
        2 ^ (p.eval z.length - p.eval x.length) * acceptCount V x (p.eval x.length) := by
      have h1 : acceptCount Vraw z (p.eval z.length) =
          acceptCount (fun q => V (x, q.2.take (p.eval x.length))) z (p.eval z.length) := by
        unfold acceptCount; congr 1; ext w
        simp [hVeq (List.ofFn w) (by simp)]
      rw [h1, acceptCount_eq_two_pow_mul_of_take hple (fun _ => rfl)]
    have hL_iff : x ∈ (L : Set (List Bool)) ↔
        2 ^ p.eval x.length < 2 * acceptCount V x (p.eval x.length) := hVL x
    change x ∈ (L : Set (List Bool)) ↔
      2 ^ p.eval z.length < 2 * acceptCount Vraw z (p.eval z.length)
    rw [hL_iff, hcount_eq, ← pow_sub_mul_pow 2 hple, mul_left_comm 2]
    exact (Nat.mul_lt_mul_left (by positivity)).symm

/-- **Counting hierarchy collapse under `PP ⊆ P/poly`**: if `PP ⊆ P/poly`, then
`CH/poly = P/poly`. -/
theorem CHPoly_eq_PPoly_of_PP_subset_PPoly (hPP : PP encBits ⊆ PPoly) :
    CHPoly = PPolyClass := by
  refine Set.Subset.antisymm ?_ PPolyClass_subset_CHPoly
  rw [PPolyClass_eq_PPoly]
  rintro L ⟨B, hB, p, a, ha, hLB⟩
  rw [CH_eq_iUnion_CountingLevel, Set.mem_iUnion] at hB
  obtain ⟨k, hk⟩ := hB
  have hBPPoly : B ∈ PPoly := CountingLevel_subset_PPoly_of_PP_subset_PPoly hPP k hk
  let Bswap : Set (List Bool) := {z |
    let ux := (Decoder.pair Decoder.bits Decoder.bits).decode z
    encPair encBits encBits (ux.2, ux.1) ∈ B}
  have hBswap_PPoly : Bswap ∈ PPoly := by
    rw [← PPolyClass_eq_PPoly]
    refine PolyTimeReducible.mem_PPolyClass (M := B) ?_ (PPolyClass_eq_PPoly.symm ▸ hBPPoly)
    let decPair := Decoder.pair Decoder.bits Decoder.bits
    refine ⟨fun z => encPair encBits encBits ((decPair.decode z).2, (decPair.decode z).1),
      (ComputableInPolyTime.of_eq (f := encPair encBits encBits) (encOut := encBits)
        fun _ => rfl).comp
        (((ComputableInPolyTime.snd _ _).comp decPair.computableInPolyTime).prod
          ((ComputableInPolyTime.fst _ _).comp decPair.computableInPolyTime)),
      fun _ => Iff.rfl⟩
  refine PPoly.of_advice hBswap_PPoly a
    (PolynomiallyBounded.mono_of_le (g := fun n => p.eval n) (by fun_prop) ha) fun x => ?_
  change x ∈ L ↔
    encPair encBits encBits
      (((Decoder.pair Decoder.bits Decoder.bits).decode (frame (a x.length) ++ x)).2,
       ((Decoder.pair Decoder.bits Decoder.bits).decode (frame (a x.length) ++ x)).1) ∈ B
  rw [decPair_frame]
  exact hLB x

/-- Membership characterization for `SharpPPoly`. -/
theorem mem_SharpPPoly {α : Type} {enc : α ↪ List Bool} {f : α → ℕ} :
    f ∈ SharpPPoly enc ↔
      ∃ (p : Polynomial ℕ) (a : ℕ → List Bool) (g : List Bool × α → ℕ),
        (∀ n, (a n).length ≤ p.eval n) ∧
        g ∈ SharpP (encPair encBits enc) ∧
        ∀ x, f x = g (a (enc x).length, x) :=
  Iff.rfl

/-- Membership characterization for `GapPPoly`. -/
theorem mem_GapPPoly {α : Type} {enc : α ↪ List Bool} {h : α → ℤ} :
    h ∈ GapPPoly enc ↔
      ∃ f₁ ∈ SharpPPoly enc, ∃ f₂ ∈ SharpPPoly enc, ∀ x, h x = (f₁ x : ℤ) - f₂ x :=
  Iff.rfl

/-- Membership characterization for `WithPolyAdvice`. -/
theorem mem_WithPolyAdvice {K : Set (Set (List Bool))} {A : Set (List Bool)} :
    A ∈ WithPolyAdvice K ↔
      ∃ B ∈ K, ∃ (p : Polynomial ℕ) (a : ℕ → List Bool),
        (∀ n, (a n).length ≤ p.eval n) ∧
        ∀ x, x ∈ A ↔ encPair encBits encBits (x, a x.length) ∈ B :=
  Iff.rfl

/-- Membership characterization for `CHPoly`. -/
theorem mem_CHPoly {A : Set (List Bool)} :
    A ∈ CHPoly ↔
      ∃ B ∈ CH, ∃ (p : Polynomial ℕ) (a : ℕ → List Bool),
        (∀ n, (a n).length ≤ p.eval n) ∧
        ∀ x, x ∈ A ↔ encPair encBits encBits (x, a x.length) ∈ B :=
  Iff.rfl

/-- Membership characterization for `PPolyClass`. -/
theorem mem_PPolyClass {A : Set (List Bool)} :
    A ∈ PPolyClass ↔
      ∃ B ∈ P encBits, ∃ (p : Polynomial ℕ) (a : ℕ → List Bool),
        (∀ n, (a n).length ≤ p.eval n) ∧
        ∀ x, x ∈ A ↔ encPair encBits encBits (x, a x.length) ∈ B :=
  Iff.rfl

end CslibFrontier.Complexity
