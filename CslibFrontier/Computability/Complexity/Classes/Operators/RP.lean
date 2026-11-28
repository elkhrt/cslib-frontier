module

public import CslibFrontier.Computability.Complexity.Classes.Operators
public import CslibFrontier.Computability.Complexity.Classes.ParityP
public import CslibFrontier.Computability.Complexity.Classes.RelaxedError
public import CslibFrontier.Computability.Complexity.Classes.ValiantVazirani
public import CslibFrontier.Computability.Complexity.Problems.CountingSAT
import CslibFrontier.Computability.Complexity.Classes.Oracle.Closure
import CslibFrontier.Computability.Complexity.Classes.ParityP.Closure
import CslibFrontier.Computability.Complexity.Classes.SharpP.Combinators
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Existential and One-Sided Randomized Complexity-Class Operators

Defines the existential operator `∃·C` (`ExistsOp`), the parameterized one-sided randomized
operator `RP_ρ·C` (`RPOpWithSuccess`), and the canonical one-sided randomized operator `RP·C`
(`RPOp`), extending the bounded-error and parity operators `Cslib.Complexity.BPOp` and
`Cslib.Complexity.ParityOp`.

Establishes monotonicity, exact identifications over `P` (`∃·P = NP`, `RP·P = RP`,
`RP_ρ·P = RP_ρ`), constant-trial one-sided amplification over `⊕P` (`RP_{3/8}·⊕P ⊆ RP·⊕P`),
single-query oracle simulation (`RP·⊕P ⊆ RP^{⊕SAT}`), and bounded-error inclusion
(`RP·⊕P ⊆ BP·⊕P`).

## Main definitions

* `CslibFrontier.Complexity.ExistsOp`: the existential complexity-class operator `∃·C`.
* `CslibFrontier.Complexity.RPOpWithSuccess`: the one-sided randomized operator `RP_ρ·C` with
  success probability threshold `ρ`.
* `CslibFrontier.Complexity.RPOp`: the one-sided randomized operator `RP·C` with threshold `1 / 2`.

## Main results

* `CslibFrontier.Complexity.ExistsOp_mono`, `CslibFrontier.Complexity.RPOpWithSuccess_mono`,
  `CslibFrontier.Complexity.RPOp_mono`: monotonicity in the base class `C`.
* `CslibFrontier.Complexity.RPOpWithSuccess_mono_threshold`: antimonotonicity in the success
  threshold `ρ`.
* `CslibFrontier.Complexity.ExistsOp_P_eq_NP`, `CslibFrontier.Complexity.RPOp_P_eq_RP`,
  `CslibFrontier.Complexity.RPOpWithSuccess_P_eq_RPWithSuccess`: characterizations over `P`.
* `CslibFrontier.Complexity.RPOpWithSuccess_three_eighths_ParityP_subset_RPOp_ParityP`:
  two-trial amplification from success probability `3 / 8` to `1 / 2` over `⊕P`.
* `CslibFrontier.Complexity.RPOp_ParityP_subset_RPWithOracle_ParitySAT`:
  inclusion of `RP·⊕P` in `RP` with a single query to the `⊕P`-complete oracle `ParitySAT`.
* `CslibFrontier.Complexity.RPOp_ParityP_subset_BPOp_ParityP`:
  two-trial error reduction showing `RP·⊕P ⊆ BP·⊕P`.
-/

public section

namespace CslibFrontier.Complexity

open Cslib Cslib.Complexity Turing.MultiTapeTM

variable {α : Type}

/-- The existential complexity-class operator `∃·C`: `L ∈ ExistsOp enc C` when there exist a
polynomial `p` and a pair language `L' ∈ C` such that
`a ∈ L ↔ ∃ w : List Bool, w.length = p.eval (enc a).length ∧ (a, w) ∈ L'`. -/
def ExistsOp (enc : α ↪ List Bool) (C : Set (Set (α × List Bool))) : Set (Set α) :=
  {L | ∃ (p : Polynomial ℕ), ∃ L' ∈ C,
    ∀ a, a ∈ L ↔ ∃ w : List Bool, w.length = p.eval (enc a).length ∧ (a, w) ∈ L'}

/-- The parameterized one-sided randomized operator `RP_ρ·C`: `L ∈ RPOpWithSuccess enc ρ C` when
there exist a polynomial `p` and `L' ∈ C` such that membership in `L'` decides `L` with one-sided
error and acceptance probability at least `ρ (enc a).length` on yes-instances. -/
def RPOpWithSuccess (enc : α ↪ List Bool) (ρ : ℕ → ℝ) (C : Set (Set (α × List Bool))) :
    Set (Set α) :=
  {L | ∃ (p : Polynomial ℕ), ∃ L' ∈ C,
    DecidesWithOneSidedSuccess enc ρ p (fun x ↦ @decide (x ∈ L') (Classical.propDecidable _)) L}

/-- The one-sided randomized operator `RP·C` with threshold `1 / 2`: `L ∈ RPOp enc C` when there
exist a polynomial `p` and `L' ∈ C` such that membership in `L'` decides `L` with one-sided error
(`Cslib.Complexity.DecidesWithOneSidedError`). -/
def RPOp (enc : α ↪ List Bool) (C : Set (Set (α × List Bool))) : Set (Set α) :=
  {L | ∃ (p : Polynomial ℕ), ∃ L' ∈ C,
    DecidesWithOneSidedError enc p (fun x ↦ @decide (x ∈ L') (Classical.propDecidable _)) L}

/-- Membership characterization for `ExistsOp`. -/
theorem mem_ExistsOp {enc : α ↪ List Bool} {C : Set (Set (α × List Bool))} {L : Set α} :
    L ∈ ExistsOp enc C ↔ ∃ (p : Polynomial ℕ), ∃ L' ∈ C,
      ∀ a, a ∈ L ↔ ∃ w : List Bool, w.length = p.eval (enc a).length ∧ (a, w) ∈ L' := by
  unfold ExistsOp
  rfl

/-- Membership characterization for `RPOpWithSuccess`. -/
theorem mem_RPOpWithSuccess {enc : α ↪ List Bool} {ρ : ℕ → ℝ} {C : Set (Set (α × List Bool))}
    {L : Set α} :
    L ∈ RPOpWithSuccess enc ρ C ↔ ∃ (p : Polynomial ℕ), ∃ L' ∈ C,
      DecidesWithOneSidedSuccess enc ρ p
        (fun x ↦ @decide (x ∈ L') (Classical.propDecidable _)) L := by
  unfold RPOpWithSuccess
  rfl

/-- Membership characterization for `RPOp`. -/
theorem mem_RPOp {enc : α ↪ List Bool} {C : Set (Set (α × List Bool))} {L : Set α} :
    L ∈ RPOp enc C ↔ ∃ (p : Polynomial ℕ), ∃ L' ∈ C,
      DecidesWithOneSidedError enc p
        (fun x ↦ @decide (x ∈ L') (Classical.propDecidable _)) L := by
  unfold RPOp
  rfl

/-- `ExistsOp` is monotone in the base class. -/
theorem ExistsOp_mono {enc : α ↪ List Bool} {C D : Set (Set (α × List Bool))} (h : C ⊆ D) :
    ExistsOp enc C ⊆ ExistsOp enc D :=
  fun _ ⟨p, L', hL', hL⟩ ↦ ⟨p, L', h hL', hL⟩

/-- `RPOpWithSuccess` is monotone in the base class. -/
theorem RPOpWithSuccess_mono {enc : α ↪ List Bool} {ρ : ℕ → ℝ} {C D : Set (Set (α × List Bool))}
    (h : C ⊆ D) : RPOpWithSuccess enc ρ C ⊆ RPOpWithSuccess enc ρ D :=
  fun _ ⟨p, L', hL', hL⟩ ↦ ⟨p, L', h hL', hL⟩

/-- `RPOpWithSuccess` is antimonotone in the success threshold `ρ`. -/
theorem RPOpWithSuccess_mono_threshold {enc : α ↪ List Bool} {ρ₁ ρ₂ : ℕ → ℝ}
    {C : Set (Set (α × List Bool))} (hρ : ∀ n, ρ₂ n ≤ ρ₁ n) :
    RPOpWithSuccess enc ρ₁ C ⊆ RPOpWithSuccess enc ρ₂ C := by
  rintro L ⟨p, L', hL', hdec⟩
  refine ⟨p, L', hL', fun a ↦ ⟨fun ha ↦ ?_, (hdec a).2⟩⟩
  exact (mul_le_mul_of_nonneg_right (hρ (enc a).length) (by positivity)).trans ((hdec a).1 ha)

/-- `RPOp` is monotone in the base class. -/
theorem RPOp_mono {enc : α ↪ List Bool} {C D : Set (Set (α × List Bool))} (h : C ⊆ D) :
    RPOp enc C ⊆ RPOp enc D :=
  fun _ ⟨p, L', hL', hL⟩ ↦ ⟨p, L', h hL', hL⟩

/-- Existential quantification over `P` yields `NP`. -/
theorem ExistsOp_P_eq_NP (enc : α ↪ List Bool) :
    ExistsOp enc (P (encPair enc encBits)) = NP enc := by
  ext L
  constructor
  · rintro ⟨p, L', ⟨V, hV, hL'⟩, hL⟩
    refine mem_NP.mpr ⟨p, V, hV, fun a ↦ ?_⟩
    simpa only [hL'] using hL a
  · intro hL
    obtain ⟨p, V, hV, hspec⟩ := mem_NP.mp hL
    exact ⟨p, {x | V x = true}, ⟨V, hV, fun _ ↦ Iff.rfl⟩, hspec⟩

/-- One-sided randomized quantification over `P` yields `RP`. -/
theorem RPOp_P_eq_RP (enc : α ↪ List Bool) :
    RPOp enc (P (encPair enc encBits)) = RP enc := by
  classical
  ext L
  constructor
  · rintro ⟨p, L', ⟨V, hV, hL'⟩, hdec⟩
    refine ⟨p, V, hV, ?_⟩
    convert hdec using 1
    funext x
    simp [hL' x]
  · rintro ⟨p, V, hV, hdec⟩
    refine ⟨p, {x | V x = true}, ⟨V, hV, fun _ ↦ Iff.rfl⟩, ?_⟩
    convert hdec using 1
    funext x
    simp

/-- Parameterized one-sided randomized quantification over `P` yields `RPWithSuccess`. -/
theorem RPOpWithSuccess_P_eq_RPWithSuccess (enc : α ↪ List Bool) (ρ : ℕ → ℝ) :
    RPOpWithSuccess enc ρ (P (encPair enc encBits)) = RPWithSuccess enc ρ := by
  classical
  ext L
  constructor
  · rintro ⟨p, L', ⟨V, hV, hL'⟩, hdec⟩
    refine ⟨p, V, hV, ?_⟩
    convert hdec using 1
    funext x
    simp [hL' x]
  · rintro ⟨p, V, hV, hdec⟩
    refine ⟨p, {x | V x = true}, ⟨V, hV, fun _ ↦ Iff.rfl⟩, ?_⟩
    convert hdec using 1
    funext x
    simp

/-- Two-trial amplification for `RP_c · ⊕P`: any language in `RP_{3/8} · ⊕P` belongs to
`RP · ⊕P` (threshold `1 / 2`), since `(1 - 3 / 8) ^ 2 = 25 / 64 < 1 / 2` and `⊕P` is closed under
union (`Cslib.Complexity.union_mem_ParityP`). -/
theorem RPOpWithSuccess_three_eighths_ParityP_subset_RPOp_ParityP (enc : α ↪ List Bool) :
    RPOpWithSuccess enc (fun _ ↦ (3 : ℝ) / 8) (ParityP (encPair enc encBits)) ⊆
      RPOp enc (ParityP (encPair enc encBits)) := by
  classical
  rintro L ⟨ρ, L', hL', hdec⟩
  let f₁ : α × List Bool → α × List Bool := fun x ↦ (x.1, x.2.take (ρ.eval (enc x.1).length))
  let f₂ : α × List Bool → α × List Bool := fun x ↦ (x.1, x.2.drop (ρ.eval (enc x.1).length))
  have hf₁ : ComputableInPolyTime f₁ (encPair enc encBits) (encPair enc encBits) := by
    have ha := ComputableInPolyTime.fst enc encBits
    have hr := ComputableInPolyTime.snd enc encBits
    have hρ := (ComputableInPolyTime.unary_eval ρ).comp
      ((ComputableInPolyTime.encoding_length enc).comp ha)
    exact ha.prod (ComputableInPolyTime.bitsTakeWithInput hr hρ)
  have hf₂ : ComputableInPolyTime f₂ (encPair enc encBits) (encPair enc encBits) := by
    have ha := ComputableInPolyTime.fst enc encBits
    have hr := ComputableInPolyTime.snd enc encBits
    have hρ := (ComputableInPolyTime.unary_eval ρ).comp
      ((ComputableInPolyTime.encoding_length enc).comp ha)
    exact ha.prod (ComputableInPolyTime.bitsDropWithInput hr hρ)
  let L₁ : Set (α × List Bool) := {x | f₁ x ∈ L'}
  let L₂ : Set (α × List Bool) := {x | f₂ x ∈ L'}
  have hL₁ : L₁ ∈ ParityP (encPair enc encBits) :=
    PolyTimeReducible.mem_ParityP ⟨f₁, hf₁, fun _ ↦ Iff.rfl⟩ hL'
  have hL₂ : L₂ ∈ ParityP (encPair enc encBits) :=
    PolyTimeReducible.mem_ParityP ⟨f₂, hf₂, fun _ ↦ Iff.rfl⟩ hL'
  have hU : L₁ ∪ L₂ ∈ ParityP (encPair enc encBits) := union_mem_ParityP hL₁ hL₂
  refine ⟨ρ + ρ, L₁ ∪ L₂, hU, fun a ↦ ⟨fun ha ↦ ?_, fun ha r ↦ ?_⟩⟩
  · set m := ρ.eval (enc a).length with hm
    have heval : (ρ + ρ).eval (enc a).length = m + m := by
      simp [hm]
    rw [heval]
    have hV : ∀ w : List Bool, @decide ((a, w) ∈ L₁ ∪ L₂) (Classical.propDecidable _) =
        orVerifier (fun x ↦ ρ.eval (enc x).length)
          (fun x ↦ @decide (x ∈ L') (Classical.propDecidable _))
          (fun x ↦ @decide (x ∈ L') (Classical.propDecidable _)) (a, w) := by
      intro w
      simp [orVerifier, L₁, L₂, f₁, f₂]
    rw [acceptCount_congr hV]
    have hor := acceptCount_orVerifier (fun x ↦ ρ.eval (enc x).length)
      (fun x ↦ @decide (x ∈ L') (Classical.propDecidable _))
      (fun x ↦ @decide (x ∈ L') (Classical.propDecidable _)) a m
    rw [← hm] at hor
    have hcomp := acceptCount_add_acceptCount_not
      (fun x ↦ @decide (x ∈ L') (Classical.propDecidable _)) a m
    have hgood_r : (3 : ℝ) / 8 * (2 : ℝ) ^ m ≤
        (acceptCount (fun x ↦ @decide (x ∈ L') (Classical.propDecidable _)) a m : ℝ) :=
      (hdec a).1 ha
    have hgood_nat : 3 * 2 ^ m ≤
        8 * acceptCount (fun x ↦ @decide (x ∈ L') (Classical.propDecidable _)) a m := by
      have h : (3 : ℝ) * (2 : ℝ) ^ m ≤
          8 * (acceptCount (fun x ↦ @decide (x ∈ L') (Classical.propDecidable _)) a m : ℝ) := by
        linarith
      exact_mod_cast h
    set bad := acceptCount (fun x ↦ !@decide (x ∈ L') (Classical.propDecidable _)) a m
    have hbad : 8 * bad ≤ 5 * 2 ^ m := by omega
    have hbad_sq : 64 * (bad * bad) ≤ 25 * 2 ^ (m + m) := by
      calc 64 * (bad * bad) = (8 * bad) * (8 * bad) := by ring
        _ ≤ (5 * 2 ^ m) * (5 * 2 ^ m) := Nat.mul_le_mul hbad hbad
        _ = 25 * (2 ^ m * 2 ^ m) := by ring
        _ = 25 * 2 ^ (m + m) := by rw [pow_add]
    have hacc_le : bad * bad ≤ 2 ^ (m + m) := by omega
    have h2 : 2 ^ (m + m) ≤ 2 * (2 ^ (m + m) - bad * bad) := by omega
    omega
  · rw [decide_eq_false_iff_not]
    rintro (h1 | h2)
    · have := (hdec a).2 ha (fun i : Fin (ρ.eval (enc a).length) ↦
        r ⟨i.val, by simp only [Polynomial.eval_add]; omega⟩)
      have htake : (List.ofFn r).take (ρ.eval (enc a).length) =
          List.ofFn (fun i : Fin (ρ.eval (enc a).length) ↦
            r ⟨i.val, by simp only [Polynomial.eval_add]; omega⟩) := by
        apply List.ext_getElem
        · simp only [List.length_take, List.length_ofFn, Polynomial.eval_add]
          omega
        · intro i hi _
          simp
      simp only [L₁, Set.mem_ofPred_eq, f₁, htake] at h1
      simp [h1] at this
    · have := (hdec a).2 ha (fun i : Fin (ρ.eval (enc a).length) ↦
        r ⟨ρ.eval (enc a).length + i.val, by simp only [Polynomial.eval_add]; omega⟩)
      have hdrop : (List.ofFn r).drop (ρ.eval (enc a).length) =
          List.ofFn (fun i : Fin (ρ.eval (enc a).length) ↦
            r ⟨ρ.eval (enc a).length + i.val, by simp only [Polynomial.eval_add]; omega⟩) := by
        apply List.ext_getElem
        · simp only [List.length_drop, List.length_ofFn, Polynomial.eval_add]
          omega
        · intro i hi _
          simp
      simp only [L₂, Set.mem_ofPred_eq, f₂, hdrop] at h2
      simp [h2] at this

/-- Every language in `RP · ⊕P` belongs to `RP` relative to the `⊕P`-complete oracle
`encCNF '' ParitySAT`, using a single oracle query per random string. -/
theorem RPOp_ParityP_subset_RPWithOracle_ParitySAT (enc : α ↪ List Bool) :
    RPOp enc (ParityP (encPair enc encBits)) ⊆ RPWithOracle (encCNF '' ParitySAT) enc := by
  classical
  rintro L ⟨ρ, L', hL', hdec⟩
  obtain ⟨f, hf, hiff⟩ := ParitySAT_parityPComplete.2 (encPair enc encBits) L' hL'
  have hV : ComputableInPolyTimeWithOracle (encCNF '' ParitySAT)
      (fun x : α × List Bool ↦ decide (encCNF (f x) ∈ encCNF '' ParitySAT))
      (encPair enc encBits) encBool :=
    (computableInPolyTimeWithOracle_mem (encCNF '' ParitySAT)).preprocess
      ((ComputableInPolyTime.of_eq (f := encCNF) (encOut := encBits) fun _ ↦ rfl).comp hf)
  refine ⟨ρ, _, hV, ?_⟩
  convert hdec using 1
  funext x
  simp [encCNF.injective.mem_set_image, hiff x]

/-- Two independent runs of an `RP · ⊕P` verifier reduce the one-sided error from `1 / 2` to
`1 / 4 < 1 / 3` via `Cslib.Complexity.union_mem_ParityP`, yielding `RP · ⊕P ⊆ BP · ⊕P`. -/
theorem RPOp_ParityP_subset_BPOp_ParityP (enc : α ↪ List Bool) :
    RPOp enc (ParityP (encPair enc encBits)) ⊆ BPOp enc (ParityP (encPair enc encBits)) := by
  classical
  rintro L ⟨ρ, L', hL', hdec⟩
  let f₁ : α × List Bool → α × List Bool := fun x ↦ (x.1, x.2.take (ρ.eval (enc x.1).length))
  let f₂ : α × List Bool → α × List Bool := fun x ↦ (x.1, x.2.drop (ρ.eval (enc x.1).length))
  have hf₁ : ComputableInPolyTime f₁ (encPair enc encBits) (encPair enc encBits) := by
    have ha := ComputableInPolyTime.fst enc encBits
    have hr := ComputableInPolyTime.snd enc encBits
    have hρ := (ComputableInPolyTime.unary_eval ρ).comp
      ((ComputableInPolyTime.encoding_length enc).comp ha)
    exact ha.prod (ComputableInPolyTime.bitsTakeWithInput hr hρ)
  have hf₂ : ComputableInPolyTime f₂ (encPair enc encBits) (encPair enc encBits) := by
    have ha := ComputableInPolyTime.fst enc encBits
    have hr := ComputableInPolyTime.snd enc encBits
    have hρ := (ComputableInPolyTime.unary_eval ρ).comp
      ((ComputableInPolyTime.encoding_length enc).comp ha)
    exact ha.prod (ComputableInPolyTime.bitsDropWithInput hr hρ)
  let L₁ : Set (α × List Bool) := {x | f₁ x ∈ L'}
  let L₂ : Set (α × List Bool) := {x | f₂ x ∈ L'}
  have hU : L₁ ∪ L₂ ∈ ParityP (encPair enc encBits) :=
    union_mem_ParityP
      (PolyTimeReducible.mem_ParityP ⟨f₁, hf₁, fun _ ↦ Iff.rfl⟩ hL')
      (PolyTimeReducible.mem_ParityP ⟨f₂, hf₂, fun _ ↦ Iff.rfl⟩ hL')
  refine ⟨ρ + ρ, L₁ ∪ L₂, hU, fun a ↦ ⟨fun ha ↦ ?_, fun ha ↦ ?_⟩⟩
  · set m := ρ.eval (enc a).length with hm
    have heval : (ρ + ρ).eval (enc a).length = m + m := by simp [hm]
    simp only [BoundedErrorAt]
    have hV : ∀ w : List Bool, @decide ((a, w) ∈ L₁ ∪ L₂) (Classical.propDecidable _) =
        orVerifier (fun x ↦ ρ.eval (enc x).length)
          (fun x ↦ @decide (x ∈ L') (Classical.propDecidable _))
          (fun x ↦ @decide (x ∈ L') (Classical.propDecidable _)) (a, w) := by
      intro w
      simp [orVerifier, L₁, L₂, f₁, f₂]
    have hacc_eq : (Finset.univ.filter fun r : BitString ((ρ + ρ).eval (enc a).length) ↦
        @decide ((a, List.ofFn r) ∈ L₁ ∪ L₂) (Classical.propDecidable _) = true).card =
        acceptCount (orVerifier (fun x ↦ ρ.eval (enc x).length)
          (fun x ↦ @decide (x ∈ L') (Classical.propDecidable _))
          (fun x ↦ @decide (x ∈ L') (Classical.propDecidable _))) a (m + m) := by
      change acceptCount (fun x ↦ @decide (x ∈ L₁ ∪ L₂) (Classical.propDecidable _)) a
        ((ρ + ρ).eval (enc a).length) = _
      rw [heval]
      exact acceptCount_congr hV (m + m)
    rw [hacc_eq, heval]
    have hor := acceptCount_orVerifier (fun x ↦ ρ.eval (enc x).length)
      (fun x ↦ @decide (x ∈ L') (Classical.propDecidable _))
      (fun x ↦ @decide (x ∈ L') (Classical.propDecidable _)) a m
    rw [← hm] at hor
    have hcomp := acceptCount_add_acceptCount_not
      (fun x ↦ @decide (x ∈ L') (Classical.propDecidable _)) a m
    have hgood := (hdec a).1 ha
    rw [← hm] at hgood
    set bad := acceptCount (fun x ↦ !@decide (x ∈ L') (Classical.propDecidable _)) a m
    have hbad : 2 * bad ≤ 2 ^ m := by omega
    have hbad_sq : 4 * (bad * bad) ≤ 2 ^ (m + m) := by
      calc 4 * (bad * bad) = (2 * bad) * (2 * bad) := by ring
        _ ≤ 2 ^ m * 2 ^ m := Nat.mul_le_mul hbad hbad
        _ = 2 ^ (m + m) := (pow_add 2 m m).symm
    omega
  · simp only [BoundedErrorAt]
    have hall : ∀ r : BitString ((ρ + ρ).eval (enc a).length),
        @decide ((a, List.ofFn r) ∈ L₁ ∪ L₂) (Classical.propDecidable _) = false := by
      intro r
      rw [decide_eq_false_iff_not]
      rintro (h1 | h2)
      · have := (hdec a).2 ha (fun i : Fin (ρ.eval (enc a).length) ↦
          r ⟨i.val, by simp only [Polynomial.eval_add]; omega⟩)
        have htake : (List.ofFn r).take (ρ.eval (enc a).length) =
            List.ofFn (fun i : Fin (ρ.eval (enc a).length) ↦
              r ⟨i.val, by simp only [Polynomial.eval_add]; omega⟩) := by
          apply List.ext_getElem
          · simp only [List.length_take, List.length_ofFn, Polynomial.eval_add]
            omega
          · intro i hi _
            simp
        simp only [L₁, Set.mem_ofPred_eq, f₁, htake] at h1
        simp [h1] at this
      · have := (hdec a).2 ha (fun i : Fin (ρ.eval (enc a).length) ↦
          r ⟨ρ.eval (enc a).length + i.val, by simp only [Polynomial.eval_add]; omega⟩)
        have hdrop : (List.ofFn r).drop (ρ.eval (enc a).length) =
            List.ofFn (fun i : Fin (ρ.eval (enc a).length) ↦
              r ⟨ρ.eval (enc a).length + i.val, by simp only [Polynomial.eval_add]; omega⟩) := by
          apply List.ext_getElem
          · simp only [List.length_drop, List.length_ofFn, Polynomial.eval_add]
            omega
          · intro i hi _
            simp
        simp only [L₂, Set.mem_ofPred_eq, f₂, hdrop] at h2
        simp [h2] at this
    rw [Finset.filter_true_of_mem fun r _ ↦ hall r, Finset.card_univ, Fintype.card_fun,
      Fintype.card_bool, Fintype.card_fin]
    omega

end CslibFrontier.Complexity
