module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.SharpP
public import CslibFrontier.Computability.Complexity.Classes.SharpP.Metric
public import CslibFrontier.Computability.Complexity.Problems.Permanent.Basic
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Primitives
import CslibFrontier.Computability.Complexity.Classes.SharpP.Closure
import CslibFrontier.Computability.Complexity.Problems.Permanent.Membership
import CslibFrontier.Computability.Complexity.Problems.Permanent.ThreeSAT
import CslibFrontier.Computability.Complexity.Problems.Permanent.ZeroOne
import CslibFrontier.Computability.Complexity.Problems.SharpThreeSAT
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.BinaryDiv
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Max
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Foundations.Data.Matrix.Permanent.Blocks
import Mathlib.Data.ZMod.Basic

/-!
# Strict Many-One Counting Reductions and #P-Completeness of the 0/1 Permanent

Defines strict many-one counting reductions (`ManyOneCountingReducible`), `#P`-hardness and
`#P`-completeness under strict many-one reductions (`SharpPManyOneHard`, `SharpPManyOneComplete`),
their ordering between parsimonious and metric reductions, polynomial-time integer root-floor
recovery (`nthRootFloor`) for size-tier decoding, and `#P`-completeness of the 0/1 permanent under
strict many-one counting reductions (`zeroOnePermanent_sharpPManyOneComplete`).
-/

public section

namespace CslibFrontier.Computability.Complexity

open Cslib Cslib.Complexity Cslib.Logic.PL Turing.MultiTapeTM ComputableInPolyTime

/-! ### Strict many-one counting reductions -/

/-- A *many-one counting reduction* from $f$ to $g$:
a pair of polynomial-time computable functions $\sigma : \alpha \to \beta$ and
$\tau : \mathbb{N} \to \mathbb{N}$ such that $f(x) = \tau(g(\sigma(x)))$ for all $x$. -/
@[expose] public def ManyOneCountingReducible {α β : Type} (encA : α ↪ List Bool)
    (encB : β ↪ List Bool) (f : α → ℕ) (g : β → ℕ) : Prop :=
  ∃ (σ : α → β) (τ : ℕ → ℕ),
    ComputableInPolyTime σ encA encB ∧
    ComputableInPolyTime τ encNat encNat ∧
    ∀ x, f x = τ (g (σ x))

/-- Reflexivity of many-one counting reductions. -/
public theorem ManyOneCountingReducible.refl {α : Type} (encA : α ↪ List Bool) (f : α → ℕ) :
    ManyOneCountingReducible encA encA f f :=
  ⟨id, id, ComputableInPolyTime.id', ComputableInPolyTime.id', fun _ => rfl⟩

/-- Transitivity of many-one counting reductions. -/
public theorem ManyOneCountingReducible.trans {α β γ : Type} {encA : α ↪ List Bool}
    {encB : β ↪ List Bool} {encC : γ ↪ List Bool} {f : α → ℕ} {g : β → ℕ} {h : γ → ℕ}
    (hfg : ManyOneCountingReducible encA encB f g)
    (hgh : ManyOneCountingReducible encB encC g h) :
    ManyOneCountingReducible encA encC f h := by
  obtain ⟨σ₁, τ₁, hσ₁, hτ₁, heq₁⟩ := hfg
  obtain ⟨σ₂, τ₂, hσ₂, hτ₂, heq₂⟩ := hgh
  exact ⟨σ₂ ∘ σ₁, τ₁ ∘ τ₂, hσ₂.comp hσ₁, hτ₁.comp hτ₂, fun x => by
    simp only [Function.comp_apply, ← heq₂, ← heq₁]⟩

/-- Every parsimonious reduction is a many-one counting reduction (with $\tau = \mathrm{id}$). -/
public theorem ParsimoniousReducible.manyOneCountingReducible {α β : Type}
    {encA : α ↪ List Bool} {encB : β ↪ List Bool} {f : α → ℕ} {g : β → ℕ}
    (h : ParsimoniousReducible encA encB f g) : ManyOneCountingReducible encA encB f g :=
  let ⟨σ, hσ, heq⟩ := h
  ⟨σ, id, hσ, ComputableInPolyTime.id', heq⟩

/-- Every many-one counting reduction is a metric reduction (ignoring the first argument in
`post`). -/
public theorem ManyOneCountingReducible.metricReducible {α β : Type}
    {encA : α ↪ List Bool} {encB : β ↪ List Bool} {f : α → ℕ} {g : β → ℕ}
    (h : ManyOneCountingReducible encA encB f g) :
    MetricReducible encA encB encNat encNat f g := by
  obtain ⟨σ, τ, hσ, hτ, heq⟩ := h
  exact ⟨σ, fun p => τ p.2, hσ, hτ.comp (ComputableInPolyTime.snd encA encNat), heq⟩

/-- A counting problem $g$ is `#P`-hard under many-one counting reductions. -/
@[expose] public def SharpPManyOneHard {β : Type} (encB : β ↪ List Bool) (g : β → ℕ) : Prop :=
  ∀ (α : Type) (encA : α ↪ List Bool) (f : α → ℕ), f ∈ SharpP encA →
    ManyOneCountingReducible encA encB f g

/-- A counting problem $g$ is `#P`-complete under many-one counting reductions. -/
@[expose] public def SharpPManyOneComplete {β : Type} (encB : β ↪ List Bool) (g : β → ℕ) : Prop :=
  g ∈ SharpP encB ∧ SharpPManyOneHard encB g

/-- `#P`-hardness under many-one counting reductions transfers along many-one reductions. -/
public theorem SharpPManyOneHard.trans {β γ : Type} {encB : β ↪ List Bool} {encC : γ ↪ List Bool}
    {g : β → ℕ} {h : γ → ℕ} (hg : SharpPManyOneHard encB g)
    (hgh : ManyOneCountingReducible encB encC g h) : SharpPManyOneHard encC h :=
  fun α encA f hf => (hg α encA f hf).trans hgh

/-- Parsimonious `#P`-hardness implies many-one `#P`-hardness. -/
public theorem SharpPHard.sharpPManyOneHard {β : Type} {encB : β ↪ List Bool} {g : β → ℕ}
    (hg : SharpPHard encB g) : SharpPManyOneHard encB g :=
  fun _ encA f hf => ParsimoniousReducible.manyOneCountingReducible (hg encA f hf)

/-- Many-one `#P`-hardness implies metric `#P`-hardness. -/
public theorem SharpPManyOneHard.sharpPMetricHard {β : Type} {encB : β ↪ List Bool} {g : β → ℕ}
    (hg : SharpPManyOneHard encB g) : SharpPMetricHard encB encNat g :=
  fun _ encA f hf => (hg _ encA f hf).metricReducible

/-! ### Part 1: Polynomial-time integer root-floor recovery for size-tier decoding -/

/-- Exact floor of the `d`-th root of a unary natural `s`: counts `k ∈ {0, ..., s}` with
`(k + 1) ^ d ≤ s`. -/
@[expose] public def nthRootFloor (d s : ℕ) : ℕ :=
  ((List.range (s + 1)).filter fun k => decide ((k + 1) ^ d ≤ s)).length

private theorem length_filter_range_lt (n r : ℕ) :
    ((List.range n).filter fun k => decide (k < r)).length = min n r := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.range_succ, List.filter_append, List.length_append, ih]
      simp only [List.filter_cons, List.filter_nil]
      by_cases h : n < r
      · simp [h]; omega
      · simp [h]; omega

/-- If `d ≥ 1` and `r ^ d ≤ s < (r + 1) ^ d`, then `nthRootFloor d s = r`. -/
public theorem nthRootFloor_eq {d r s : ℕ} (hd : 1 ≤ d) (hlo : r ^ d ≤ s)
    (hhi : s < (r + 1) ^ d) : nthRootFloor d s = r := by
  unfold nthRootFloor
  have hcongr : (List.range (s + 1)).filter (fun k => decide ((k + 1) ^ d ≤ s)) =
      (List.range (s + 1)).filter (fun k => decide (k < r)) := by
    refine List.filter_congr fun k _ => ?_
    rw [Bool.eq_iff_iff]
    simp only [decide_eq_true_eq]
    constructor
    · intro h
      by_contra hge
      have hle : r + 1 ≤ k + 1 := by omega
      have hpow : (r + 1) ^ d ≤ (k + 1) ^ d := Nat.pow_le_pow_left hle d
      omega
    · intro hlt
      have hle : k + 1 ≤ r := by omega
      exact (Nat.pow_le_pow_left hle d).trans hlo
  rw [hcongr, length_filter_range_lt]
  have hr_le : r ≤ r ^ d := Nat.le_self_pow (by omega) r
  omega

/-- If `d ≥ 1`, `r ≥ 1`, and `2 ^ (r ^ d) ≤ Z < 2 ^ ((r + 1) ^ d)`, then
`nthRootFloor d (Z.size - 1) = r`. -/
public theorem nthRootFloor_size_sub_one {d r Z : ℕ} (hd : 1 ≤ d) (hr : 1 ≤ r)
    (hlo : 2 ^ (r ^ d) ≤ Z) (hhi : Z < 2 ^ ((r + 1) ^ d)) :
    nthRootFloor d (Z.size - 1) = r := by
  have hlt : r ^ d < Z.size := Nat.lt_size.2 hlo
  have hle : Z.size ≤ (r + 1) ^ d := Nat.size_le.2 hhi
  have hrpos : 1 ≤ r ^ d := Nat.one_le_pow d r hr
  exact nthRootFloor_eq hd (by omega) (by omega)

/-- `nthRootFloor d` is polynomial-time computable in unary for every fixed `d`. -/
@[fun_prop]
public theorem computableInPolyTime_nthRootFloor (d : ℕ) :
    ComputableInPolyTime (nthRootFloor d) encUnary encUnary := by
  have hpred : ComputableInPolyTime (fun p : ℕ × ℕ => decide ((p.2 + 1) ^ d ≤ p.1))
      (encPair encUnary encUnary) encBool := by
    have hpow : ComputableInPolyTime (fun p : ℕ × ℕ => (p.2 + 1) ^ d)
        (encPair encUnary encUnary) encUnary :=
      (unary_pow d).comp (unary_add' (snd encUnary encUnary) (const 1))
    exact unary_le.comp (hpow.prod (fst encUnary encUnary))
  have hfilt : ComputableInPolyTime
      (fun s : ℕ => (List.range (s + 1)).filter fun k => decide ((k + 1) ^ d ≤ s))
      encUnary (encList encUnary) :=
    filterWithInput (range.comp (unary_add' id' (const 1))) hpred
  exact (length_list encUnary).comp hfilt

/-- Recovering `nthRootFloor d (Z.size - 1)` from a binary natural `Z` is polynomial-time. -/
@[fun_prop]
public theorem computableInPolyTime_nthRootFloor_size (d : ℕ) :
    ComputableInPolyTime (fun Z : ℕ => nthRootFloor d (Z.size - 1)) encNat encUnary :=
  (computableInPolyTime_nthRootFloor d).comp (unary_sub' binary_size (const 1))

/-! ### Part 2: Strict many-one `#P`-completeness of `ZeroOnePermanent` -/

/-- Scale parameter `r` for the strict many-one reduction `#3SAT ≤_m^#P ZeroOnePermanent`. -/
private def permScaleParam (φ : CNF ℕ) : ℕ :=
  max (max (cnfToPermanentTable φ).length φ.length) φ.flatten.length + 20

private theorem computableInPolyTime_permScaleParam :
    ComputableInPolyTime permScaleParam encCNF encUnary := by
  have hA : ComputableInPolyTime (fun φ => (cnfToPermanentTable φ).length) encCNF encUnary :=
    (length_list (encList encIntBin)).comp computableInPolyTime_cnfToPermanentTable
  have hm : ComputableInPolyTime (fun φ : CNF ℕ => φ.length) encCNF encUnary :=
    length_list (encList (encPair encNat encBool))
  have hv : ComputableInPolyTime (fun φ : CNF ℕ => φ.flatten.length) encCNF encUnary :=
    (length_list (encPair encNat encBool)).comp (flatten (encPair encNat encBool))
  unfold permScaleParam
  exact unary_add' (unary_max' (unary_max' hA hm) hv) (const 20)

/-- Natural-number matrix entry for the strict many-one `#3SAT → ZeroOnePermanent` table:
block-diagonal `[[2^(r^4)]] ⊕ ((cnfToPermanentTable φ mod 2^(5*r)) + 2^(5*r) I_n) ⊕ 12 I_{r-m}`. -/
private def zankoNatEntry (φ : CNF ℕ) (i j : ℕ) : ℕ :=
  let A := cnfToPermanentTable φ
  let n := A.length
  let r := permScaleParam φ
  let Q : ℕ := 2 ^ (5 * r)
  if i = 0 ∧ j = 0 then 2 ^ (r ^ 4)
  else if 1 ≤ i ∧ i ≤ n ∧ 1 ≤ j ∧ j ≤ n then
    (intTableEntry A (i - 1) (j - 1) % (Q : ℤ)).toNat + if i = j then Q else 0
  else if n < i ∧ i = j then 12
  else 0

/-- Dimension `1 + n + (r - m)` of the Zankó natural-number table. -/
private def zankoNatDim (φ : CNF ℕ) : ℕ :=
  1 + (cnfToPermanentTable φ).length + (permScaleParam φ - φ.length)

/-- The Zankó natural-number table for `φ : CNF ℕ`. -/
private def zankoNatTable (φ : CNF ℕ) : List (List ℕ) :=
  (List.range (zankoNatDim φ)).map fun i =>
    (List.range (zankoNatDim φ)).map fun j => zankoNatEntry φ i j

/-- Strict many-one query map `σ : CNF ℕ → List (List Bool)` from `#3SAT` to `ZeroOnePermanent`. -/
private def sharpThreeSATToZeroOnePerm (φ : CNF ℕ) : List (List Bool) :=
  natTableToZeroOne (zankoNatTable φ)

/-- Strict many-one post-processing map `τ : ℕ → ℕ` recovering `#3SAT(φ)` from the 0/1 permanent
alone. -/
private def recoverSharpThreeSATFromPerm (Z : ℕ) : ℕ :=
  let r := nthRootFloor 4 (Z.size - 1)
  ((Z / 2 ^ (r ^ 4)) % 2 ^ (5 * r)) / (12 ^ r)

private theorem computableInPolyTime_zankoNatDim :
    ComputableInPolyTime zankoNatDim encCNF encUnary := by
  have hA : ComputableInPolyTime (fun φ => (cnfToPermanentTable φ).length) encCNF encUnary :=
    (length_list (encList encIntBin)).comp computableInPolyTime_cnfToPermanentTable
  have hm : ComputableInPolyTime (fun φ : CNF ℕ => φ.length) encCNF encUnary :=
    length_list (encList (encPair encNat encBool))
  have hr := computableInPolyTime_permScaleParam
  unfold zankoNatDim
  fun_prop

private theorem computableInPolyTime_zankoNatTable :
    ComputableInPolyTime zankoNatTable encCNF encNatTable := by
  have hdim := computableInPolyTime_zankoNatDim
  have hA := computableInPolyTime_cnfToPermanentTable
  have hr := computableInPolyTime_permScaleParam
  have hentry : ComputableInPolyTime
      (fun p : (CNF ℕ × ℕ) × ℕ => zankoNatEntry p.1.1 p.1.2 p.2)
      (encPair (encPair encCNF encUnary) encUnary) encNat := by
    let encIn := encPair (encPair encCNF encUnary) encUnary
    have hφ : ComputableInPolyTime (fun p : (CNF ℕ × ℕ) × ℕ => p.1.1) encIn encCNF := by fun_prop
    have hi : ComputableInPolyTime (fun p : (CNF ℕ × ℕ) × ℕ => p.1.2) encIn encUnary := by fun_prop
    have hj : ComputableInPolyTime (fun p : (CNF ℕ × ℕ) × ℕ => p.2) encIn encUnary := by fun_prop
    have hAp : ComputableInPolyTime (fun p : (CNF ℕ × ℕ) × ℕ => cnfToPermanentTable p.1.1)
        encIn encIntTable := hA.comp hφ
    have hnp : ComputableInPolyTime (fun p : (CNF ℕ × ℕ) × ℕ => (cnfToPermanentTable p.1.1).length)
        encIn encUnary := (length_list (encList encIntBin)).comp hAp
    have hrp : ComputableInPolyTime (fun p : (CNF ℕ × ℕ) × ℕ => permScaleParam p.1.1)
        encIn encUnary := hr.comp hφ
    have hQ : ComputableInPolyTime (fun p : (CNF ℕ × ℕ) × ℕ => 2 ^ (5 * permScaleParam p.1.1))
        encIn encNat := binary_two_pow.comp (unary_mul' (const 5) hrp)
    have hscale : ComputableInPolyTime
        (fun p : (CNF ℕ × ℕ) × ℕ => 2 ^ ((permScaleParam p.1.1) ^ 4)) encIn encNat :=
      binary_two_pow.comp ((unary_pow 4).comp hrp)
    have hAij : ComputableInPolyTime
        (fun p : (CNF ℕ × ℕ) × ℕ => intTableEntry (cnfToPermanentTable p.1.1) (p.1.2 - 1) (p.2 - 1))
        encIn encIntBin := by
      unfold intTableEntry
      fun_prop
    have hmod : ComputableInPolyTime
        (fun p : (CNF ℕ × ℕ) × ℕ =>
          (intTableEntry (cnfToPermanentTable p.1.1) (p.1.2 - 1) (p.2 - 1) %
            ((2 ^ (5 * permScaleParam p.1.1) : ℕ) : ℤ)).toNat) encIn encNat :=
      intBin_emodNat' hAij hQ
    have hdiagQ : ComputableInPolyTime
        (fun p : (CNF ℕ × ℕ) × ℕ =>
          if p.1.2 = p.2 then 2 ^ (5 * permScaleParam p.1.1) else 0) encIn encNat :=
      ((unary_beq hi hj).ite' hQ (const 0)).of_enc_eq fun p => congrArg encNat <| by
        by_cases h : p.1.2 = p.2 <;> simp [h]
    have hmid : ComputableInPolyTime
        (fun p : (CNF ℕ × ℕ) × ℕ =>
          (intTableEntry (cnfToPermanentTable p.1.1) (p.1.2 - 1) (p.2 - 1) %
            ((2 ^ (5 * permScaleParam p.1.1) : ℕ) : ℤ)).toNat +
            if p.1.2 = p.2 then 2 ^ (5 * permScaleParam p.1.1) else 0) encIn encNat :=
      binary_add' hmod hdiagQ
    have hc1 : ComputableInPolyTime
        (fun p : (CNF ℕ × ℕ) × ℕ => (p.1.2 == 0) && (p.2 == 0)) encIn encBool :=
      (unary_beq hi (const 0)).bool_and' (unary_beq hj (const 0))
    have hc2 : ComputableInPolyTime
        (fun p : (CNF ℕ × ℕ) × ℕ =>
          decide (1 ≤ p.1.2) && decide (p.1.2 ≤ (cnfToPermanentTable p.1.1).length) &&
            decide (1 ≤ p.2) && decide (p.2 ≤ (cnfToPermanentTable p.1.1).length))
        encIn encBool := by fun_prop
    have hc3 : ComputableInPolyTime
        (fun p : (CNF ℕ × ℕ) × ℕ =>
          decide ((cnfToPermanentTable p.1.1).length < p.1.2) && (p.1.2 == p.2))
        encIn encBool := by fun_prop
    have h12 : ComputableInPolyTime
        (fun p : (CNF ℕ × ℕ) × ℕ =>
          if decide ((cnfToPermanentTable p.1.1).length < p.1.2) && (p.1.2 == p.2) then 12 else 0)
        encIn encNat :=
      hc3.ite' (const 12) (const 0)
    have h2 : ComputableInPolyTime
        (fun p : (CNF ℕ × ℕ) × ℕ =>
          if decide (1 ≤ p.1.2) && decide (p.1.2 ≤ (cnfToPermanentTable p.1.1).length) &&
              decide (1 ≤ p.2) && decide (p.2 ≤ (cnfToPermanentTable p.1.1).length) then
            (intTableEntry (cnfToPermanentTable p.1.1) (p.1.2 - 1) (p.2 - 1) %
              ((2 ^ (5 * permScaleParam p.1.1) : ℕ) : ℤ)).toNat +
              if p.1.2 = p.2 then 2 ^ (5 * permScaleParam p.1.1) else 0
          else if decide ((cnfToPermanentTable p.1.1).length < p.1.2) && (p.1.2 == p.2) then 12
          else 0) encIn encNat :=
      hc2.ite' hmid h12
    have hall := hc1.ite' hscale h2
    refine hall.of_enc_eq fun p => congrArg encNat ?_
    simp only [zankoNatEntry, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
    by_cases h0 : p.1.2 = 0 ∧ p.2 = 0
    · rw [ite_eq_left h0, ite_eq_left h0]
    · rw [ite_eq_right h0, ite_eq_right h0]
      by_cases h1 : 1 ≤ p.1.2 ∧ p.1.2 ≤ (cnfToPermanentTable p.1.1).length ∧
          1 ≤ p.2 ∧ p.2 ≤ (cnfToPermanentTable p.1.1).length
      · have h1' : ((1 ≤ p.1.2 ∧ p.1.2 ≤ (cnfToPermanentTable p.1.1).length) ∧ 1 ≤ p.2) ∧
            p.2 ≤ (cnfToPermanentTable p.1.1).length := ⟨⟨⟨h1.1, h1.2.1⟩, h1.2.2.1⟩, h1.2.2.2⟩
        rw [ite_eq_left h1, ite_eq_left h1']
      · have h1' : ¬(((1 ≤ p.1.2 ∧ p.1.2 ≤ (cnfToPermanentTable p.1.1).length) ∧ 1 ≤ p.2) ∧
            p.2 ≤ (cnfToPermanentTable p.1.1).length) := fun h =>
          h1 ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩
        rw [ite_eq_right h1, ite_eq_right h1']
  unfold zankoNatTable
  exact mapWithInput (range.comp hdim)
    (mapWithInput (range.comp (hdim.comp (fst encCNF encUnary))) hentry)

private theorem computableInPolyTime_sharpThreeSATToZeroOnePerm :
    ComputableInPolyTime sharpThreeSATToZeroOnePerm encCNF encBoolTable :=
  computableInPolyTime_natTableToZeroOne.comp computableInPolyTime_zankoNatTable

private theorem computableInPolyTime_recoverSharpThreeSATFromPerm :
    ComputableInPolyTime recoverSharpThreeSATFromPerm encNat encNat := by
  have hr := computableInPolyTime_nthRootFloor_size 4
  have h1 : ComputableInPolyTime (fun Z : ℕ => 2 ^ (nthRootFloor 4 (Z.size - 1) ^ 4))
      encNat encNat :=
    binary_two_pow.comp ((unary_pow 4).comp hr)
  have h2 : ComputableInPolyTime (fun Z : ℕ => 2 ^ (5 * nthRootFloor 4 (Z.size - 1)))
      encNat encNat :=
    binary_two_pow.comp (unary_mul' (const 5) hr)
  have h3 : ComputableInPolyTime (fun Z : ℕ => 12 ^ nthRootFloor 4 (Z.size - 1))
      encNat encNat :=
    binary_pow' (const 12) hr
  unfold recoverSharpThreeSATFromPerm
  exact binary_div' (binary_mod' (binary_div' id' h1) h2) h3

private theorem natPermanent_range_map (N : ℕ) (f : ℕ → ℕ → ℕ) :
    NatPermanent ((List.range N).map fun i => (List.range N).map (f i)) =
      (Matrix.of fun i j : Fin N => f i j).permanent := by
  have hlen : ((List.range N).map fun i => (List.range N).map (f i)).length = N := by simp
  rw [NatPermanent, ← Matrix.permanent_submatrix_equiv_equiv (finCongr hlen.symm)
    (finCongr hlen.symm)]
  congr 1
  ext i j
  simp [tableMatrix_apply, List.getD_eq_getElem?_getD]

private theorem permanent_diag_const {R : Type*} [CommSemiring R] (k : ℕ) (c : R) :
    (Matrix.of fun i j : Fin k => if i = j then c else 0).permanent = c ^ k := by
  rw [Matrix.permanent]
  have hsingle : ∀ σ : Equiv.Perm (Fin k),
      (∏ i : Fin k, if σ i = i then c else 0) = if σ = 1 then c ^ k else 0 := by
    intro σ
    by_cases hσ : σ = 1
    · subst hσ; simp
    · rw [ite_eq_right hσ]
      have hne : ∃ i : Fin k, σ i ≠ i := by
        by_contra hall
        push Not at hall
        exact hσ (Equiv.ext hall)
      obtain ⟨i, hi⟩ := hne
      exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)
  simp [hsingle]

private theorem natPermanent_zankoNatTable (φ : CNF ℕ) :
    let A := cnfToPermanentTable φ
    let n := A.length
    let r := permScaleParam φ
    let Q : ℕ := 2 ^ (5 * r)
    let M : Matrix (Fin n) (Fin n) ℕ := Matrix.of fun i j =>
      (intTableEntry A i j % (Q : ℤ)).toNat + if i = j then Q else 0
    NatPermanent (zankoNatTable φ) = 2 ^ (r ^ 4) * (M.permanent * 12 ^ (r - φ.length)) := by
  dsimp only
  set A := cnfToPermanentTable φ
  set n := A.length
  set r := permScaleParam φ
  set m := φ.length
  set Q : ℕ := 2 ^ (5 * r)
  set M : Matrix (Fin n) (Fin n) ℕ := Matrix.of fun i j =>
    (intTableEntry A i j % (Q : ℤ)).toNat + if i = j then Q else 0
  set D : Matrix (Fin (r - m)) (Fin (r - m)) ℕ := Matrix.of fun i j => if i = j then 12 else 0
  set B0 : Matrix (Fin 1) (Fin 1) ℕ := Matrix.of fun _ _ => 2 ^ (r ^ 4)
  rw [zankoNatTable, natPermanent_range_map]
  let e1 : Fin 1 ⊕ (Fin n ⊕ Fin (r - m)) ≃ Fin (zankoNatDim φ) :=
    (Equiv.sumCongr (Equiv.refl (Fin 1)) finSumFinEquiv).trans
      (finSumFinEquiv.trans (finCongr (by dsimp only [zankoNatDim, n, A, r, m]; omega)))
  rw [← Matrix.permanent_submatrix_equiv e1]
  have hsub : (Matrix.of fun i j : Fin (zankoNatDim φ) => zankoNatEntry φ i j).submatrix e1 e1 =
      Matrix.fromBlocks B0 0 0 (Matrix.fromBlocks M 0 0 D) := by
    have hnA : n = (cnfToPermanentTable φ).length := rfl
    ext x y
    rcases x with i0 | (i1 | i2) <;> rcases y with j0 | (j1 | j2)
    · fin_cases i0; fin_cases j0
      simp only [Matrix.submatrix_apply, Matrix.of_apply, Matrix.fromBlocks_apply₁₁, e1,
        Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl, Equiv.refl_apply,
        finSumFinEquiv_apply_left, finCongr_apply, Fin.val_cast, Fin.val_castAdd,
        zankoNatEntry, B0, and_self, ↓reduceIte, r]
    · fin_cases i0
      simp only [Matrix.submatrix_apply, Matrix.of_apply, Matrix.fromBlocks_apply₁₂,
        Matrix.zero_apply, e1, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr,
        Equiv.refl_apply, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, finCongr_apply,
        Fin.val_cast, Fin.val_natAdd, Fin.val_castAdd, zankoNatEntry]
      split_ifs <;> omega
    · fin_cases i0
      simp only [Matrix.submatrix_apply, Matrix.of_apply, Matrix.fromBlocks_apply₁₂,
        Matrix.zero_apply, e1, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr,
        Equiv.refl_apply, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, finCongr_apply,
        Fin.val_cast, Fin.val_natAdd, Fin.val_castAdd, zankoNatEntry]
      split_ifs <;> omega
    · fin_cases j0
      simp only [Matrix.submatrix_apply, Matrix.of_apply, Matrix.fromBlocks_apply₂₁,
        Matrix.zero_apply, e1, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr,
        Equiv.refl_apply, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, finCongr_apply,
        Fin.val_cast, Fin.val_natAdd, Fin.val_castAdd, zankoNatEntry]
      split_ifs <;> omega
    · simp only [Matrix.submatrix_apply, Matrix.of_apply, Matrix.fromBlocks_apply₂₂,
        Matrix.fromBlocks_apply₁₁, e1, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inr,
        finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, finCongr_apply, Fin.val_cast,
        Fin.val_natAdd, Fin.val_castAdd, zankoNatEntry, M, A, n, r, Q]
      have h0 : ¬ (1 + i1.1 = 0 ∧ 1 + j1.1 = 0) := by omega
      have h1 : 1 ≤ 1 + i1.1 ∧ 1 + i1.1 ≤ (cnfToPermanentTable φ).length ∧
          1 ≤ 1 + j1.1 ∧ 1 + j1.1 ≤ (cnfToPermanentTable φ).length := by omega
      have heq : (1 + i1.1 = 1 + j1.1) ↔ i1 = j1 := by
        constructor
        · intro h; exact Fin.ext (by omega)
        · intro h; subst h; rfl
      rw [ite_eq_right h0, ite_eq_left h1, Nat.add_sub_cancel_left, Nat.add_sub_cancel_left]
      simp only [heq]
    · simp only [Matrix.submatrix_apply, Matrix.of_apply, Matrix.fromBlocks_apply₂₂,
        Matrix.fromBlocks_apply₁₂, Matrix.zero_apply, e1, Equiv.trans_apply, Equiv.sumCongr_apply,
        Sum.map_inr, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, finCongr_apply,
        Fin.val_cast, Fin.val_natAdd, Fin.val_castAdd, zankoNatEntry, n, A]
      split_ifs <;> omega
    · fin_cases j0
      simp only [Matrix.submatrix_apply, Matrix.of_apply, Matrix.fromBlocks_apply₂₁,
        Matrix.zero_apply, e1, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr,
        Equiv.refl_apply, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, finCongr_apply,
        Fin.val_cast, Fin.val_natAdd, Fin.val_castAdd, zankoNatEntry]
      split_ifs <;> omega
    · simp only [Matrix.submatrix_apply, Matrix.of_apply, Matrix.fromBlocks_apply₂₂,
        Matrix.fromBlocks_apply₂₁, Matrix.zero_apply, e1, Equiv.trans_apply, Equiv.sumCongr_apply,
        Sum.map_inr, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, finCongr_apply,
        Fin.val_cast, Fin.val_natAdd, Fin.val_castAdd, zankoNatEntry, n, A]
      split_ifs <;> omega
    · simp only [Matrix.submatrix_apply, Matrix.of_apply, Matrix.fromBlocks_apply₂₂,
        e1, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inr,
        finSumFinEquiv_apply_right, finCongr_apply, Fin.val_cast, Fin.val_natAdd,
        zankoNatEntry, D, n, A]
      have h0 : ¬ (1 + ((cnfToPermanentTable φ).length + i2.1) = 0 ∧
          1 + ((cnfToPermanentTable φ).length + j2.1) = 0) := by omega
      have h1 : ¬ (1 ≤ 1 + ((cnfToPermanentTable φ).length + i2.1) ∧
          1 + ((cnfToPermanentTable φ).length + i2.1) ≤ (cnfToPermanentTable φ).length ∧
          1 ≤ 1 + ((cnfToPermanentTable φ).length + j2.1) ∧
          1 + ((cnfToPermanentTable φ).length + j2.1) ≤ (cnfToPermanentTable φ).length) := by omega
      have hgt : (cnfToPermanentTable φ).length < 1 + ((cnfToPermanentTable φ).length + i2.1) := by
        omega
      have heq : (1 + ((cnfToPermanentTable φ).length + i2.1) =
          1 + ((cnfToPermanentTable φ).length + j2.1)) ↔ i2 = j2 := by
        constructor
        · intro h; exact Fin.ext (by omega)
        · intro h; subst h; rfl
      rw [ite_eq_right h0, ite_eq_right h1]
      simp only [hgt, true_and, heq]
  rw [hsub, Matrix.permanent_fromBlocks_zero, Matrix.permanent_fromBlocks_zero]
  have hB0 : B0.permanent = 2 ^ (r ^ 4) := by
    simp [B0, Matrix.permanent]
  rw [hB0, permanent_diag_const]

private theorem sharpThreeSAT_le_two_pow_flatten (φ : CNF ℕ) :
    SharpThreeSAT φ ≤ 2 ^ φ.flatten.length := by
  unfold SharpThreeSAT SharpSAT
  split_ifs
  · refine (CNF.modelCount_le_two_pow_numVars φ).trans ?_
    refine Nat.pow_le_pow_right (by omega) ?_
    have h1 : φ.numVars ≤ φ.vars.length := List.toFinset_card_le φ.vars
    have h2 : φ.vars.length = φ.flatten.length := by
      simp [CNF.vars, List.length_flatten, List.map_map, Function.comp_def]
    omega
  · exact Nat.zero_le _

private theorem sharpThreeSAT_eq_recover (φ : CNF ℕ) :
    SharpThreeSAT φ =
      recoverSharpThreeSATFromPerm (ZeroOnePermanent (sharpThreeSATToZeroOnePerm φ)) := by
  set A := cnfToPermanentTable φ
  set n := A.length
  set m := φ.length
  obtain ⟨r, hr_eq⟩ : ∃ r, r = permScaleParam φ := ⟨permScaleParam φ, rfl⟩
  set Q : ℕ := 2 ^ (5 * r)
  set M : Matrix (Fin n) (Fin n) ℕ := Matrix.of fun i j =>
    (intTableEntry A i j % (Q : ℤ)).toNat + if i = j then Q else 0
  have hr20 : 20 ≤ r := by rw [hr_eq]; simp [permScaleParam]
  have hn_le : n ≤ r := by rw [hr_eq]; simp [permScaleParam, n, A]; omega
  have hm_le : m ≤ r := by rw [hr_eq]; simp [permScaleParam, m]; omega
  have hv_le : φ.flatten.length ≤ r := by rw [hr_eq]; simp [permScaleParam]; omega
  have hQpos : 0 < Q := Nat.pow_pos (by omega)
  have hZ : ZeroOnePermanent (sharpThreeSATToZeroOnePerm φ) =
      2 ^ (r ^ 4) * (M.permanent * 12 ^ (r - m)) := by
    rw [sharpThreeSATToZeroOnePerm, zeroOnePermanent_natTableToZeroOne]
    have hnat := natPermanent_zankoNatTable φ
    dsimp only at hnat
    change NatPermanent (zankoNatTable φ) = _
    simpa only [← hr_eq, A, n, m, Q, M] using hnat
  set H := M.permanent * 12 ^ (r - m)
  have hH_pos : 1 ≤ H := by
    have hM_pos : 1 ≤ M.permanent := by
      rw [Matrix.permanent]
      calc 1 ≤ ∏ i : Fin n, M ((1 : Equiv.Perm (Fin n)) i) i := by
            refine Finset.one_le_prod fun i _ => ?_
            simp only [Equiv.Perm.coe_one, id_eq, M, Matrix.of_apply, ↓reduceIte]
            omega
        _ ≤ ∑ σ : Equiv.Perm (Fin n), ∏ i : Fin n, M (σ i) i :=
            Finset.single_le_sum (f := fun σ : Equiv.Perm (Fin n) => ∏ i : Fin n, M (σ i) i)
              (fun _ _ => Nat.zero_le _) (Finset.mem_univ 1)
    have h12_pos : 1 ≤ 12 ^ (r - m) := Nat.one_le_pow _ _ (by omega)
    exact Nat.mul_le_mul hM_pos h12_pos
  have hH_lt : H < 2 ^ (r ^ 3) := by
    have hM_le : M.permanent ≤ n.factorial * (2 ^ (5 * r + 1)) ^ n := by
      rw [Matrix.permanent]
      have hterm : ∀ σ : Equiv.Perm (Fin n),
          ∏ i : Fin n, M (σ i) i ≤ (2 ^ (5 * r + 1)) ^ n := fun σ => by
        calc ∏ i : Fin n, M (σ i) i
            ≤ ∏ _i : Fin n, (2 ^ (5 * r + 1)) := Finset.prod_le_prod fun i _ => by
              simp only [M, Matrix.of_apply]
              have hlt : (intTableEntry A (σ i) i % (Q : ℤ)).toNat < Q := by
                have hQposZ : (0 : ℤ) < (Q : ℤ) := Nat.cast_pos.2 hQpos
                have := Int.emod_lt_of_pos (intTableEntry A (σ i) i) hQposZ
                have hnn := Int.emod_nonneg (intTableEntry A (σ i) i) hQposZ.ne'
                omega
              have h2Q : 2 * Q = 2 ^ (5 * r + 1) := (Nat.pow_succ' (m := 2) (n := 5 * r)).symm
              split_ifs <;> omega
          _ = (2 ^ (5 * r + 1)) ^ n := by simp
      calc ∑ σ : Equiv.Perm (Fin n), ∏ i : Fin n, M (σ i) i
          ≤ ∑ _σ : Equiv.Perm (Fin n), (2 ^ (5 * r + 1)) ^ n :=
            Finset.sum_le_sum fun σ _ => hterm σ
        _ = n.factorial * (2 ^ (5 * r + 1)) ^ n := by
            simp [Finset.card_univ, Fintype.card_perm]
    have hfac : n.factorial ≤ 2 ^ (r ^ 2) := by
      have h1 : n.factorial ≤ n ^ n := Nat.factorial_le_pow n
      have h2 : n ≤ 2 ^ r := hn_le.trans (Nat.lt_two_pow_self.le)
      calc n.factorial ≤ n ^ n := h1
        _ ≤ (2 ^ r) ^ n := Nat.pow_le_pow_left h2 n
        _ = 2 ^ (r * n) := (Nat.pow_mul 2 r n).symm
        _ ≤ 2 ^ (r ^ 2) := Nat.pow_le_pow_right (by omega)
            (by rw [sq]; exact Nat.mul_le_mul_left r hn_le)
    have hpowM : (2 ^ (5 * r + 1)) ^ n ≤ 2 ^ ((5 * r + 1) * r) := by
      rw [← Nat.pow_mul]
      exact Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_left _ hn_le)
    have h12 : 12 ^ (r - m) ≤ 2 ^ (4 * r) := by
      calc 12 ^ (r - m) ≤ 16 ^ (r - m) := Nat.pow_le_pow_left (by omega) _
        _ = (2 ^ 4) ^ (r - m) := by norm_num
        _ = 2 ^ (4 * (r - m)) := (Nat.pow_mul 2 4 _).symm
        _ ≤ 2 ^ (4 * r) := Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_left 4 (Nat.sub_le r m))
    have hexp : r ^ 2 + (5 * r + 1) * r + 4 * r < r ^ 3 := by nlinarith
    calc H ≤ (n.factorial * (2 ^ (5 * r + 1)) ^ n) * 12 ^ (r - m) :=
          Nat.mul_le_mul_right _ hM_le
      _ ≤ (2 ^ (r ^ 2) * 2 ^ ((5 * r + 1) * r)) * 2 ^ (4 * r) :=
          Nat.mul_le_mul (Nat.mul_le_mul hfac hpowM) h12
      _ = 2 ^ (r ^ 2 + (5 * r + 1) * r + 4 * r) := by rw [← Nat.pow_add, ← Nat.pow_add]
      _ < 2 ^ (r ^ 3) := Nat.pow_lt_pow_right (by omega) hexp
  have hZ_lo : 2 ^ (r ^ 4) ≤ ZeroOnePermanent (sharpThreeSATToZeroOnePerm φ) := by
    rw [hZ]
    exact Nat.le_mul_of_pos_right _ (by omega)
  have hZ_hi : ZeroOnePermanent (sharpThreeSATToZeroOnePerm φ) < 2 ^ ((r + 1) ^ 4) := by
    rw [hZ]
    have hpow : r ^ 4 + r ^ 3 < (r + 1) ^ 4 := by
      have : (r + 1) ^ 4 = r ^ 4 + 4 * r ^ 3 + 6 * r ^ 2 + 4 * r + 1 := by ring
      nlinarith
    calc 2 ^ (r ^ 4) * H < 2 ^ (r ^ 4) * 2 ^ (r ^ 3) :=
          Nat.mul_lt_mul_of_pos_left hH_lt (Nat.pow_pos (by omega))
      _ = 2 ^ (r ^ 4 + r ^ 3) := (Nat.pow_add 2 _ _).symm
      _ < 2 ^ ((r + 1) ^ 4) := Nat.pow_lt_pow_right (by omega) hpow
  have hr_rec : nthRootFloor 4 ((ZeroOnePermanent (sharpThreeSATToZeroOnePerm φ)).size - 1) = r :=
    nthRootFloor_size_sub_one (by omega) (by omega) hZ_lo hZ_hi
  have hmod : (H : ZMod Q) = ((12 ^ r * SharpThreeSAT φ : ℕ) : ZMod Q) := by
    have hMmod : (M.permanent : ZMod Q) = (IntPermanent A : ZMod Q) := by
      have h1 : (M.permanent : ZMod Q) = (M.map (Nat.castRingHom (ZMod Q))).permanent := by
        simpa using (Nat.castRingHom (ZMod Q)).map_permanent M
      have h2 : (IntPermanent A : ZMod Q) =
          ((tableMatrix A).map (Int.castRingHom (ZMod Q))).permanent := by
        simpa [IntPermanent] using (Int.castRingHom (ZMod Q)).map_permanent (tableMatrix A)
      rw [h1, h2]
      refine congrArg Matrix.permanent (Matrix.ext fun i j => ?_)
      simp only [Matrix.map_apply, eq_natCast, eq_intCast, M, Matrix.of_apply,
        tableMatrix_eq_intTableEntry]
      have hnn : (0 : ℤ) ≤ intTableEntry A i j % (Q : ℤ) :=
        Int.emod_nonneg _ (Nat.cast_ne_zero.2 hQpos.ne')
      have hto : (((intTableEntry A i j % (Q : ℤ)).toNat : ℕ) : ZMod Q) =
          ((intTableEntry A i j % (Q : ℤ) : ℤ) : ZMod Q) := by
        rw [← Int.cast_natCast, Int.toNat_of_nonneg hnn]
      split_ifs
      · push_cast
        rw [hto, ZMod.intCast_mod, ZMod.natCast_self, add_zero]
      · rw [add_zero, hto, ZMod.intCast_mod]
    have hIA : IntPermanent A = (12 : ℤ) ^ m * (SharpThreeSAT φ : ℤ) :=
      intPermanent_cnfToPermanentTable φ
    calc (H : ZMod Q) = (M.permanent : ZMod Q) * ((12 ^ (r - m) : ℕ) : ZMod Q) := by
          simp [H]
      _ = (IntPermanent A : ZMod Q) * ((12 ^ (r - m) : ℕ) : ZMod Q) := by rw [hMmod]
      _ = (((12 ^ m * SharpThreeSAT φ : ℕ) : ℕ) : ZMod Q) * ((12 ^ (r - m) : ℕ) : ZMod Q) := by
          rw [hIA]; push_cast; rfl
      _ = ((12 ^ m * 12 ^ (r - m) * SharpThreeSAT φ : ℕ) : ZMod Q) := by
          push_cast; ring
      _ = ((12 ^ r * SharpThreeSAT φ : ℕ) : ZMod Q) := by
          rw [← Nat.pow_add, Nat.add_sub_of_le hm_le]
  have hHmod : H % Q = 12 ^ r * SharpThreeSAT φ := by
    have heq : H % Q = (12 ^ r * SharpThreeSAT φ) % Q :=
      (ZMod.natCast_eq_natCast_iff' H (12 ^ r * SharpThreeSAT φ) Q).1 hmod
    rw [heq, Nat.mod_eq_of_lt]
    have hS : SharpThreeSAT φ ≤ 2 ^ r :=
      (sharpThreeSAT_le_two_pow_flatten φ).trans (Nat.pow_le_pow_right (by omega) hv_le)
    calc 12 ^ r * SharpThreeSAT φ ≤ 12 ^ r * 2 ^ r := Nat.mul_le_mul_left _ hS
      _ = 24 ^ r := by rw [← Nat.mul_pow]
      _ < 32 ^ r := Nat.pow_lt_pow_left (by omega) (by omega)
      _ = Q := by rw [show (32 : ℕ) = 2 ^ 5 by norm_num, ← Nat.pow_mul]
  rw [recoverSharpThreeSATFromPerm, hr_rec, hZ, Nat.mul_div_cancel_left H (Nat.pow_pos (by omega)),
    hHmod, Nat.mul_div_cancel_left _ (Nat.pow_pos (by omega))]

/-- Strict many-one counting reduction from `#3SAT` to `ZeroOnePermanent`. -/
private theorem manyOne_sharpThreeSAT_zeroOnePermanent :
    ManyOneCountingReducible encCNF encBoolTable SharpThreeSAT ZeroOnePermanent :=
  ⟨sharpThreeSATToZeroOnePerm, recoverSharpThreeSATFromPerm,
    computableInPolyTime_sharpThreeSATToZeroOnePerm,
    computableInPolyTime_recoverSharpThreeSATFromPerm, sharpThreeSAT_eq_recover⟩

/-- The 0/1 permanent is `#P`-complete under strict many-one counting reductions. -/
public theorem zeroOnePermanent_sharpPManyOneComplete :
    SharpPManyOneComplete encBoolTable ZeroOnePermanent :=
  ⟨ZeroOnePermanent.mem_SharpP,
    (SharpPHard.sharpPManyOneHard SharpThreeSAT_sharpPComplete.2).trans
      manyOne_sharpThreeSAT_zeroOnePermanent⟩

end CslibFrontier.Computability.Complexity
