module

public import Cslib.Computability.Circuit.Boolean.Basic
public import CslibFrontier.Computability.MCSP.Basic
public import Mathlib.InformationTheory.Hamming
import Cslib.Computability.Circuit.Boolean.Counting
import Cslib.Computability.Circuit.Boolean.Synthesis
import CslibFrontier.Computability.Circuit.Boolean.Synthesis
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Data.Fintype.Perm
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Tight De Morgan Circuit Counting and Single-Point Truth-Table Flipping

Establishes a tight upper bound on the number of `n`-variable Boolean functions computable by
De Morgan circuits of size at most `g`, together with a linear gate upper bound for flipping a
single entry of a Boolean function's truth table:

* `StronglyIrredundant`: a Boolean program whose `n + g` input and gate wires compute pairwise
  distinct Boolean functions.
* `exists_stronglyIrredundant`: every De Morgan program reduces without increasing gate count to a
  strongly irredundant program realizing all original wire functions.
* `circuitCount n g`: cardinality of the set of `n`-variable Boolean functions computable with at
  most `g` De Morgan gates.
* `circuitCount_lt_pow_mul_exp`: for all positive integers `n` and `g`,
  `circuitCount n g < g ^ g * exp (g + 4 * n)`.
* `complexity_le_of_hammingDist_le_one`: flipping a single entry of a truth table increases
  De Morgan circuit complexity by at most `2 * n + 5` gates.

## Main definitions

* `CslibFrontier.Circuits.Boolean.StronglyIrredundant`
* `CslibFrontier.Circuits.Boolean.circuitCount`

## Main results

* `CslibFrontier.Circuits.Boolean.exists_stronglyIrredundant`
* `CslibFrontier.Circuits.Boolean.circuitCount_lt_pow_mul_exp`
* `CslibFrontier.Circuits.Boolean.complexity_le_of_hammingDist_le_one`
-/

public section

namespace CslibFrontier.Circuits.Boolean

open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open scoped BigOperators Finset

/-- Number of `n`-variable Boolean functions computable by De Morgan circuits with at most `g`
gates. -/
noncomputable def circuitCount (n g : ℕ) : ℕ :=
  (computableFunctions n g).ncard

/-- Definitional characterization of `circuitCount n g`. -/
theorem circuitCount_eq_ncard (n g : ℕ) : circuitCount n g = (computableFunctions n g).ncard := by
  unfold circuitCount
  rfl

/-- `circuitCount n g` is monotone in the gate budget `g`. -/
theorem circuitCount_mono {n g₁ g₂ : ℕ} (h : g₁ ≤ g₂) :
    circuitCount n g₁ ≤ circuitCount n g₂ := by
  unfold circuitCount
  refine Set.ncard_le_ncard fun f hf => ?_
  rw [mem_computableFunctions_iff_complexity_le] at hf ⊢
  exact hf.trans h

/-- `circuitCount n g` is bounded above by the total number `2 ^ (2 ^ n)` of `n`-bit functions. -/
theorem circuitCount_le_two_pow_two_pow (n g : ℕ) : circuitCount n g ≤ 2 ^ 2 ^ n := by
  unfold circuitCount
  calc (computableFunctions n g).ncard
      ≤ (Set.univ : Set (BooleanFunction n)).ncard := Set.ncard_le_ncard (Set.subset_univ _)
    _ = 2 ^ 2 ^ n := by
      rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_bool,
        Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]

/-- A Boolean program is strongly irredundant when all `n + g` input and gate wires compute
pairwise distinct Boolean functions. -/
@[expose] def StronglyIrredundant {n g : ℕ} (p : Program signature n g) : Prop :=
  Function.Injective (p.wireFunction interpretation)

private theorem input_wireFunction_injective (n : ℕ) :
    Function.Injective (fun i : Fin n => fun x : BitString n => x i) := by
  intro i j hij
  by_contra hne
  have hval := congrFun hij (fun k => decide (k = i))
  simp at hval
  exact hne hval.symm

/-- Every Boolean program reduces without increasing gate count to a strongly irredundant program
computing every original wire function. -/
theorem exists_stronglyIrredundant {n g : ℕ} (p : Program signature n g) :
    ∃ k ≤ g, ∃ q : Program signature n k, ∃ ρ : Wire.Renaming n g k,
      (∀ x w, q.trace interpretation x (ρ w) = p.trace interpretation x w) ∧
        StronglyIrredundant q := by
  induction p with
  | empty =>
    refine ⟨0, le_rfl, .empty, .id, by simp, ?_⟩
    intro w₁ w₂ hw
    cases w₁ with
    | input i =>
      cases w₂ with
      | input j => exact congrArg Wire.input (input_wireFunction_injective n hw)
      | gate g => exact Fin.elim0 g
    | gate g => exact Fin.elim0 g
  | @gate g p line ih =>
    obtain ⟨k, hk, q, ρ, hρ, hq⟩ := ih
    let l := line.mapWires ρ
    have hl (x : BitString n) :
        l.eval interpretation x (q.eval interpretation x) =
          line.eval interpretation x (p.eval interpretation x) :=
      line.eval_mapWires ρ interpretation x x (p.eval interpretation x) (q.eval interpretation x)
        (hρ x)
    by_cases h : ∃ w : Wire n k, q.wireFunction interpretation w =
        fun x => l.eval interpretation x (q.eval interpretation x)
    · obtain ⟨w, hw⟩ := h
      refine ⟨k, by omega, q, ρ.skipLast w, ?_, hq⟩
      intro x v
      refine Wire.lastCases ?_ (fun v => ?_) v
      · simpa [Program.wireFunction] using (congrFun hw x).trans (hl x)
      · simpa using hρ x v
    · refine ⟨k + 1, by omega, q.gate l, ρ.appendLast, ?_, ?_⟩
      · intro x v
        refine Wire.lastCases ?_ (fun v => ?_) v
        · simpa using hl x
        · simpa using hρ x v
      · intro w₁ w₂ hw
        have hcast (u : Wire n k) :
            (q.gate l).wireFunction interpretation u.castSucc = q.wireFunction interpretation u :=
          funext fun x => Program.trace_gate_castSucc q l interpretation x u
        have hlast : (q.gate l).wireFunction interpretation (.gate (Fin.last k)) =
            fun x => l.eval interpretation x (q.eval interpretation x) :=
          funext fun x => Program.eval_gate_last q l interpretation x
        revert hw
        refine Wire.lastCases ?_ (fun u₁ => ?_) w₁
        · refine Wire.lastCases (fun _ => rfl) (fun u₂ hw => ?_) w₂
          rw [hlast, hcast] at hw
          exact absurd ⟨u₂, hw.symm⟩ h
        · refine Wire.lastCases (fun hw => ?_) (fun u₂ hw => ?_) w₂
          · rw [hcast, hlast] at hw
            exact absurd ⟨u₁, hw⟩ h
          · rw [hcast, hcast] at hw
            exact congrArg Wire.castSucc (hq hw)

private theorem lines_wire_ne_self {n s : ℕ} (p : Program signature n s)
    (a : Fin s) (r : Fin (signature.Arity (p.lines a).op)) :
    (p.lines a).wires r ≠ Wire.gate a := by
  induction p with
  | empty => exact Fin.elim0 a
  | @gate g p line ih =>
    revert r
    refine Fin.lastCases ?_ (fun prior => ?_) a
    · intro r
      generalize hl : (p.gate line).lines (Fin.last g) = l at r ⊢
      rw [Program.lines_gate_last] at hl
      subst hl
      change (line.wires r).castSucc ≠ Wire.gate (Fin.last g)
      cases line.wires r with
      | input i => intro h; cases h
      | gate j =>
        intro h
        exact Fin.castSucc_ne_last j (Wire.gate.inj h)
    · intro r
      generalize hl : (p.gate line).lines prior.castSucc = l at r ⊢
      rw [Program.lines_gate_castSucc] at hl
      subst hl
      change ((p.lines prior).wires r).castSucc ≠ Wire.gate prior.castSucc
      have hne := ih prior r
      cases hw : (p.lines prior).wires r with
      | input i => intro h; cases h
      | gate j =>
        rw [hw] at hne
        intro h
        exact hne (congrArg Wire.gate (Fin.castSucc_inj.mp (Wire.gate.inj h)))

private theorem stronglyIrredundant_binary_wires_ne {n s : ℕ} (p : Program signature n s)
    (hp : StronglyIrredundant p) (a : Fin s)
    (hop : (p.lines a).op = .and ∨ (p.lines a).op = .or) :
    (p.lines a).wires ⟨0, by rcases hop with h | h <;> simp [h]⟩ ≠
      (p.lines a).wires ⟨1, by rcases hop with h | h <;> simp [h]⟩ := by
  have hev_all : ∀ x, (p.lines a).eval interpretation x (p.eval interpretation x) =
      p.wireFunction interpretation (.gate a) x := fun x => p.lines_eval interpretation x a
  have hne_self : ∀ r, (p.lines a).wires r ≠ Wire.gate a := lines_wire_ne_self p a
  revert hop hev_all hne_self
  cases hline : p.lines a with
  | mk op wires =>
    intro hop hev_all hne_self heq
    dsimp only at hop hev_all hne_self heq
    rcases hop with rfl | rfl
    · have hfun : p.wireFunction interpretation (.gate a) =
          p.wireFunction interpretation (wires ⟨0, by decide⟩) := by
        funext x
        rw [← hev_all x, Line.eval]
        change (Wire.elim x (p.eval interpretation x) (wires ⟨0, by decide⟩) &&
          Wire.elim x (p.eval interpretation x) (wires ⟨1, by decide⟩)) = _
        rw [← heq, Bool.and_self]
        rfl
      exact hne_self ⟨0, by decide⟩ (hp hfun).symm
    · have hfun : p.wireFunction interpretation (.gate a) =
          p.wireFunction interpretation (wires ⟨0, by decide⟩) := by
        funext x
        rw [← hev_all x, Line.eval]
        change (Wire.elim x (p.eval interpretation x) (wires ⟨0, by decide⟩) ||
          Wire.elim x (p.eval interpretation x) (wires ⟨1, by decide⟩)) = _
        rw [← heq, Bool.or_self]
        rfl
      exact hne_self ⟨0, by decide⟩ (hp hfun).symm

private def wireIndex {n s : ℕ} : Wire n s → ℕ
  | .input i => i.val
  | .gate j => n + j.val

private theorem wireIndex_injective {n s : ℕ} : Function.Injective (@wireIndex n s) := by
  intro w₁ w₂ h
  cases w₁ with
  | input i =>
    cases w₂ with
    | input j => exact congrArg Wire.input (Fin.ext h)
    | gate j => dsimp [wireIndex] at h; omega
  | gate i =>
    cases w₂ with
    | input j => dsimp [wireIndex] at h; omega
    | gate j =>
      dsimp [wireIndex] at h
      exact congrArg Wire.gate (Fin.ext (by omega))

private inductive CanonLine (n s : ℕ) (a : Fin s) where
  | const (b : Bool)
  | not (w : {w : Wire n s // w ≠ .gate a})
  | and (u v : {w : Wire n s // w ≠ .gate a}) (hlt : wireIndex u.1 < wireIndex v.1)
  | or (u v : {w : Wire n s // w ≠ .gate a}) (hlt : wireIndex u.1 < wireIndex v.1)

private def CanonLine.eval {n s : ℕ} {a : Fin s} (l : CanonLine n s a)
    (x : BitString n) (v : Fin s → Bool) : Bool :=
  match l with
  | .const b => b
  | .not w => !Wire.elim x v w.1
  | .and u w _ => Wire.elim x v u.1 && Wire.elim x v w.1
  | .or u w _ => Wire.elim x v u.1 || Wire.elim x v w.1

private def canonLineEncode {n s : ℕ} {a : Fin s} :
    CanonLine n s a → Bool ⊕ ({w : Wire n s // w ≠ .gate a} × {w : Wire n s // w ≠ .gate a})
  | .const b => Sum.inl b
  | .not w => Sum.inr (w, w)
  | .and u v _ => Sum.inr (u, v)
  | .or u v _ => Sum.inr (v, u)

private theorem canonLineEncode_injective {n s : ℕ} {a : Fin s} :
    Function.Injective (@canonLineEncode n s a) := by
  intro l₁ l₂ h
  cases l₁ <;> cases l₂ <;> simp only [canonLineEncode, Sum.inl.injEq, Sum.inr.injEq,
    Prod.mk.injEq, reduceCtorEq] at h
  · exact congrArg CanonLine.const h
  · exact congrArg CanonLine.not h.1
  · rcases h with ⟨rfl, h2⟩; subst h2; omega
  · rcases h with ⟨rfl, h2⟩; subst h2; omega
  · rcases h with ⟨rfl, h2⟩; subst h2; omega
  · rcases h with ⟨rfl, rfl⟩; rfl
  · rcases h with ⟨rfl, rfl⟩; omega
  · rcases h with ⟨rfl, h2⟩; subst h2; omega
  · rcases h with ⟨rfl, rfl⟩; omega
  · rcases h with ⟨rfl, rfl⟩; rfl

private instance {n s : ℕ} {a : Fin s} : Finite (CanonLine n s a) :=
  Finite.of_injective canonLineEncode canonLineEncode_injective

private theorem card_canonLine_le {n s : ℕ} (hn : 1 ≤ n) (hs : 1 ≤ s) (a : Fin s) :
    Nat.card (CanonLine n s a) ≤ (n + s) ^ 2 := by
  have h1 := Nat.card_le_card_of_injective _ (@canonLineEncode_injective n s a)
  have hW : Nat.card {w : Wire n s // w ≠ .gate a} = n + s - 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Wire.card, Fintype.card_subtype_eq]
  have hsum : Nat.card (Bool ⊕ ({w : Wire n s // w ≠ .gate a} × {w : Wire n s // w ≠ .gate a})) =
      2 + (n + s - 1) ^ 2 := by
    rw [Nat.card_sum, Nat.card_prod, hW, Nat.card_eq_fintype_card, Fintype.card_bool, sq]
  rw [hsum] at h1
  have hM : 2 ≤ n + s := by omega
  have hsq : 2 + (n + s - 1) ^ 2 ≤ (n + s) ^ 2 := by
    obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le' hM
    rw [hm]
    have : m + 2 - 1 = m + 1 := by omega
    rw [this]
    nlinarith
  exact h1.trans hsq

private def exactMinFunctions (n s : ℕ) : Set (BooleanFunction n) :=
  {f | complexity interpretation (single f) = s}

private instance (n s : ℕ) : Finite (exactMinFunctions n s) :=
  Set.Finite.to_subtype <| (Boolean.computableFunctions n s).toFinite.subset fun _ hf =>
    mem_computableFunctions_iff_complexity_le.mpr hf.le

private theorem exactMinFunctions_zero_card_le (n : ℕ) :
    (exactMinFunctions n 0).ncard ≤ n := by
  have hsub : exactMinFunctions n 0 ⊆ Set.range (fun i : Fin n => fun x : BitString n => x i) := by
    intro f hf
    have hcomp : f ∈ Boolean.computableFunctions n 0 :=
      mem_computableFunctions_iff_complexity_le.mpr hf.le
    rcases Boolean.mem_computableFunctions.mp hcomp with ⟨c, hc, hs⟩
    have hs0 : c.size = 0 := Nat.eq_zero_of_le_zero hs
    cases h : c.outputs 0 with
    | input i =>
      refine ⟨i, funext fun x => ?_⟩
      have h0 := congrFun (hc x) 0
      simpa [Circuit.eval, h] using h0
    | gate j =>
      have := j.isLt
      omega
  calc (exactMinFunctions n 0).ncard
      ≤ (Set.range (fun i : Fin n => fun x : BitString n => x i)).ncard :=
        Set.ncard_le_ncard hsub (Set.finite_range _)
    _ = ((fun i : Fin n => fun x : BitString n => x i) '' Set.univ).ncard := by
        rw [Set.image_univ]
    _ ≤ (Set.univ : Set (Fin n)).ncard := Set.ncard_image_le (Set.toFinite _)
    _ = n := by simp

private theorem exists_canon_rep {n s : ℕ} (hs : 1 ≤ s) {f : BooleanFunction n}
    (hf : f ∈ exactMinFunctions n s) :
    ∃ p : Program signature n s, ∃ out : Fin s,
      (∀ x, p.eval interpretation x out = f x) ∧ StronglyIrredundant p := by
  obtain ⟨c, hc, hcsize⟩ := exists_computes_size_eq_complexity (I := interpretation) (f := single f)
  rw [hf] at hcsize
  obtain ⟨k, hk, q, ρ, hρ, hq⟩ := exists_stronglyIrredundant c.program
  have hk_ge : s ≤ k := by
    have hle : complexity interpretation (single f) ≤ k :=
      complexity_le_iff.mpr ⟨⟨q, ρ ∘ c.outputs⟩,
        fun x => funext fun o => (hρ x (c.outputs o)).trans (congrFun (hc x) o), le_rfl⟩
    rw [hf] at hle
    exact hle
  have hk_eq : k = s := by omega
  subst hk_eq
  cases hout : ρ (c.outputs 0) with
  | input i =>
    exfalso
    have h0 : complexity interpretation (single f) = 0 := by
      refine Nat.eq_zero_of_le_zero
        (complexity_le_iff.mpr ⟨⟨.empty, fun _ => .input i⟩, ?_, le_rfl⟩)
      intro x
      funext o
      fin_cases o
      have h1 := hρ x (c.outputs 0)
      rw [hout] at h1
      simpa [Circuit.eval, Program.trace] using h1.trans (congrFun (hc x) 0)
    rw [hf] at h0
    omega
  | gate out =>
    refine ⟨q, out, fun x => ?_, hq⟩
    have h1 := hρ x (c.outputs 0)
    rw [hout] at h1
    exact h1.trans (congrFun (hc x) 0)

private def toCanonLine {n s : ℕ} {a : Fin s} (l : Line signature n s)
    (hne_self : ∀ r, l.wires r ≠ .gate a)
    (hne_bin : ∀ (hop : l.op = .and ∨ l.op = .or),
      l.wires ⟨0, by rcases hop with h | h <;> simp [h]⟩ ≠
        l.wires ⟨1, by rcases hop with h | h <;> simp [h]⟩) : CanonLine n s a :=
  match hop : l.op with
  | .const b => .const b
  | .not => .not ⟨l.wires ⟨0, by simp [hop]⟩, hne_self _⟩
  | .and =>
    let u : {w : Wire n s // w ≠ .gate a} := ⟨l.wires ⟨0, by simp [hop]⟩, hne_self _⟩
    let v : {w : Wire n s // w ≠ .gate a} := ⟨l.wires ⟨1, by simp [hop]⟩, hne_self _⟩
    if hlt : wireIndex u.1 < wireIndex v.1 then .and u v hlt
    else .and v u (by
      have hne : u.1 ≠ v.1 := hne_bin (Or.inl hop)
      have hidx : wireIndex u.1 ≠ wireIndex v.1 := fun h => hne (wireIndex_injective h)
      omega)
  | .or =>
    let u : {w : Wire n s // w ≠ .gate a} := ⟨l.wires ⟨0, by simp [hop]⟩, hne_self _⟩
    let v : {w : Wire n s // w ≠ .gate a} := ⟨l.wires ⟨1, by simp [hop]⟩, hne_self _⟩
    if hlt : wireIndex u.1 < wireIndex v.1 then .or u v hlt
    else .or v u (by
      have hne : u.1 ≠ v.1 := hne_bin (Or.inr hop)
      have hidx : wireIndex u.1 ≠ wireIndex v.1 := fun h => hne (wireIndex_injective h)
      omega)

private theorem toCanonLine_eval {n s : ℕ} {a : Fin s} (l : Line signature n s)
    (hne_self : ∀ r, l.wires r ≠ .gate a)
    (hne_bin : ∀ (hop : l.op = .and ∨ l.op = .or),
      l.wires ⟨0, by rcases hop with h | h <;> simp [h]⟩ ≠
        l.wires ⟨1, by rcases hop with h | h <;> simp [h]⟩)
    (x : BitString n) (v : Fin s → Bool) :
    (toCanonLine l hne_self hne_bin).eval x v = l.eval interpretation x v := by
  rcases l with ⟨op, wires⟩
  cases op with
  | const b => rfl
  | not => rfl
  | and =>
    unfold toCanonLine
    dsimp only
    split_ifs
    · rfl
    · simp only [CanonLine.eval, Line.eval, interpretation, Function.comp_apply]
      exact Bool.and_comm _ _
  | or =>
    unfold toCanonLine
    dsimp only
    split_ifs
    · rfl
    · simp only [CanonLine.eval, Line.eval, interpretation, Function.comp_apply]
      exact Bool.or_comm _ _

private theorem ofPermutation_injective {n s : ℕ} (π : Equiv.Perm (Fin s)) :
    Function.Injective (Wire.Renaming.ofPermutation π : Wire n s → Wire n s) := by
  intro w₁ w₂ h
  cases w₁ with
  | input i =>
    cases w₂ with
    | input j => simpa using h
    | gate j => simp [Wire.Renaming.ofPermutation] at h
  | gate i =>
    cases w₂ with
    | input j => simp [Wire.Renaming.ofPermutation] at h
    | gate j =>
      simp only [Wire.Renaming.ofPermutation_gate, Wire.gate.injEq] at h
      exact congrArg Wire.gate (π.injective h)

private theorem card_exactMinFunctions_mul_factorial_le {n s : ℕ} (hn : 1 ≤ n) (hs : 1 ≤ s) :
    (exactMinFunctions n s).ncard * s.factorial ≤ (n + s) ^ (2 * s) * s := by
  classical
  let rep : exactMinFunctions n s →
      {q : Program signature n s × Fin s // StronglyIrredundant q.1} := fun f =>
    let h := exists_canon_rep hs f.property
    ⟨(h.choose, h.choose_spec.choose), h.choose_spec.choose_spec.2⟩
  have hrep_eval (f : exactMinFunctions n s) (x : BitString n) :
      (rep f).1.1.eval interpretation x (rep f).1.2 = f.1 x :=
    (exists_canon_rep hs f.property).choose_spec.choose_spec.1 x
  let encode : exactMinFunctions n s × Equiv.Perm (Fin s) →
      (∀ a : Fin s, CanonLine n s a) × Fin s := fun ⟨f, π⟩ =>
    let p := (rep f).1.1
    let hp := (rep f).2
    (fun a =>
      let l' := (p.lines (π.symm a)).mapWires (Wire.Renaming.ofPermutation π)
      have hself : ∀ r, l'.wires r ≠ .gate a := fun r h => by
        have h1 : (Wire.Renaming.ofPermutation π : Wire n s → Wire n s)
            ((p.lines (π.symm a)).wires r) =
            (Wire.Renaming.ofPermutation π : Wire n s → Wire n s) (.gate (π.symm a)) :=
          h.trans (by simp [Wire.Renaming.ofPermutation])
        exact lines_wire_ne_self p (π.symm a) r (ofPermutation_injective π h1)
      have hbin : ∀ (hop : l'.op = .and ∨ l'.op = .or),
          l'.wires ⟨0, by rcases hop with h | h <;> simp [h]⟩ ≠
            l'.wires ⟨1, by rcases hop with h | h <;> simp [h]⟩ := fun hop h =>
        stronglyIrredundant_binary_wires_ne p hp (π.symm a) hop (ofPermutation_injective π h)
      toCanonLine l' hself hbin,
      π (rep f).1.2)
  have hencode_eval (f : exactMinFunctions n s) (π : Equiv.Perm (Fin s))
      (x : BitString n) (v : Fin s → Bool) (a : Fin s) :
      ((encode (f, π)).1 a).eval x v =
        ((rep f).1.1.lines (π.symm a)).eval interpretation x (v ∘ π) := by
    dsimp only [encode]
    rw [toCanonLine_eval]
    exact Line.eval_mapRenaming _ _ _ _ _ _ fun _ => rfl
  have hencode_unique (f : exactMinFunctions n s) (π : Equiv.Perm (Fin s))
      (x : BitString n) (v : Fin s → Bool)
      (hv : ∀ a, ((encode (f, π)).1 a).eval x v = v a) :
      v = (rep f).1.1.eval interpretation x ∘ π.symm := by
    have hcomp : v ∘ π = (rep f).1.1.eval interpretation x :=
      (rep f).1.1.eq_eval_of_forall_lines_eval interpretation x _ fun a => by
        simpa [hencode_eval] using hv (π a)
    funext a
    simpa using congrFun hcomp (π.symm a)
  have hinj : Function.Injective encode := by
    rintro ⟨f, π⟩ ⟨f', τ⟩ heq
    have hvals (x : BitString n) :
        (rep f).1.1.eval interpretation x ∘ π.symm =
          (rep f').1.1.eval interpretation x ∘ τ.symm := by
      apply hencode_unique f' τ x
      intro a
      have hlines := congrFun (congrArg Prod.fst heq) a
      rw [← hlines, hencode_eval]
      simpa [Function.comp_def] using (rep f).1.1.lines_eval interpretation x (π.symm a)
    have hf_eq : f = f' := by
      apply Subtype.ext
      funext x
      have hout := congrArg Prod.snd heq
      dsimp only [encode] at hout
      rw [← hrep_eval f x, ← hrep_eval f' x]
      have h1 := congrFun (hvals x) (π (rep f).1.2)
      simp only [Function.comp_apply, Equiv.symm_apply_apply] at h1
      rw [hout, Equiv.symm_apply_apply] at h1
      exact h1
    subst hf_eq
    have hperm : π.symm = τ.symm := by
      apply Equiv.ext
      intro a
      have hfun : (rep f).1.1.wireFunction interpretation (.gate (π.symm a)) =
          (rep f).1.1.wireFunction interpretation (.gate (τ.symm a)) :=
        funext fun x => congrFun (hvals x) a
      exact Wire.gate.inj ((rep f).2 hfun)
    exact Prod.ext rfl (by simpa using congrArg Equiv.symm hperm)
  have hcard := Nat.card_le_card_of_injective encode hinj
  rw [Nat.card_prod, Nat.card_coe_set_eq, Nat.card_prod, Nat.card_pi,
    Nat.card_eq_fintype_card (α := Equiv.Perm (Fin s)), Fintype.card_perm, Fintype.card_fin,
    Nat.card_eq_fintype_card (α := Fin s), Fintype.card_fin] at hcard
  refine hcard.trans (Nat.mul_le_mul_right s ?_)
  calc ∏ a : Fin s, Nat.card (CanonLine n s a)
      ≤ ∏ _a : Fin s, (n + s) ^ 2 :=
        Finset.prod_le_prod fun a _ => card_canonLine_le hn hs a
    _ = ((n + s) ^ 2) ^ s := by simp
    _ = (n + s) ^ (2 * s) := by rw [← pow_mul]

private theorem pow_div_exp_le_factorial (s : ℕ) (hs : 1 ≤ s) :
    ((s : ℝ) / Real.exp 1) ^ s ≤ (s.factorial : ℝ) := by
  have hst := Stirling.le_factorial_stirling s
  have hpi : (1 : ℝ) ≤ Real.sqrt (2 * Real.pi * (s : ℝ)) := by
    rw [Real.one_le_sqrt]
    have h2pi : (3 : ℝ) < Real.pi := Real.pi_gt_three
    have hs1 : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
    nlinarith
  have hpos : 0 ≤ ((s : ℝ) / Real.exp 1) ^ s := by positivity
  nlinarith

private theorem exactMinFunctions_real_le {n s : ℕ} (hn : 1 ≤ n) (hs : 1 ≤ s) :
    ((exactMinFunctions n s).ncard : ℝ) ≤
      (s : ℝ) * (s : ℝ) ^ s * Real.exp ((s : ℝ) + 2 * (n : ℝ)) := by
  have hnat : (((exactMinFunctions n s).ncard * s.factorial : ℕ) : ℝ) ≤
      (((n + s) ^ (2 * s) * s : ℕ) : ℝ) :=
    Nat.cast_le.mpr (card_exactMinFunctions_mul_factorial_le hn hs)
  push_cast at hnat
  have hs_pos : (0 : ℝ) < (s : ℝ) := by positivity
  have hst := pow_div_exp_le_factorial s hs
  have h1 : ((exactMinFunctions n s).ncard : ℝ) * ((s : ℝ) / Real.exp 1) ^ s ≤
      ((n : ℝ) + (s : ℝ)) ^ (2 * s) * (s : ℝ) := by
    calc ((exactMinFunctions n s).ncard : ℝ) * ((s : ℝ) / Real.exp 1) ^ s
        ≤ ((exactMinFunctions n s).ncard : ℝ) * (s.factorial : ℝ) :=
          mul_le_mul_of_nonneg_left hst (Nat.cast_nonneg _)
      _ ≤ ((n : ℝ) + (s : ℝ)) ^ (2 * s) * (s : ℝ) := hnat
  have hexp_ns : ((n : ℝ) + (s : ℝ)) ^ (2 * s) ≤
      (s : ℝ) ^ (2 * s) * Real.exp (2 * (n : ℝ)) := by
    have hbase : (n : ℝ) + (s : ℝ) = (s : ℝ) * ((n : ℝ) / (s : ℝ) + 1) := by
      field_simp [hs_pos.ne']
    have hone : (n : ℝ) / (s : ℝ) + 1 ≤ Real.exp ((n : ℝ) / (s : ℝ)) :=
      Real.add_one_le_exp _
    rw [hbase, mul_pow]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    calc ((n : ℝ) / (s : ℝ) + 1) ^ (2 * s)
        ≤ (Real.exp ((n : ℝ) / (s : ℝ))) ^ (2 * s) :=
          pow_le_pow_left₀ (by positivity) hone (2 * s)
      _ = Real.exp ((2 * s : ℕ) * ((n : ℝ) / (s : ℝ))) := (Real.exp_nat_mul _ _).symm
      _ = Real.exp (2 * (n : ℝ)) := by
          congr 1
          push_cast
          field_simp [hs_pos.ne']
  have hdiv_eq : ((s : ℝ) / Real.exp 1) ^ s = (s : ℝ) ^ s / Real.exp (s : ℝ) := by
    rw [div_pow, ← Real.exp_nat_mul, mul_one]
  rw [hdiv_eq] at h1
  have h2 : ((exactMinFunctions n s).ncard : ℝ) * (s : ℝ) ^ s ≤
      ((n : ℝ) + (s : ℝ)) ^ (2 * s) * (s : ℝ) * Real.exp (s : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_right h1 (Real.exp_pos (s : ℝ)).le
    rwa [← mul_div_assoc, div_mul_cancel₀ _ (Real.exp_pos _).ne'] at hmul
  have h3 : ((exactMinFunctions n s).ncard : ℝ) * (s : ℝ) ^ s ≤
      ((s : ℝ) * (s : ℝ) ^ s * Real.exp ((s : ℝ) + 2 * (n : ℝ))) * (s : ℝ) ^ s := by
    calc ((exactMinFunctions n s).ncard : ℝ) * (s : ℝ) ^ s
        ≤ ((n : ℝ) + (s : ℝ)) ^ (2 * s) * (s : ℝ) * Real.exp (s : ℝ) := h2
      _ ≤ ((s : ℝ) ^ (2 * s) * Real.exp (2 * (n : ℝ))) * (s : ℝ) * Real.exp (s : ℝ) := by
          gcongr
      _ = ((s : ℝ) * (s : ℝ) ^ s * (Real.exp (s : ℝ) * Real.exp (2 * (n : ℝ)))) *
            (s : ℝ) ^ s := by
          rw [show 2 * s = s + s by omega, pow_add]
          ring
      _ = ((s : ℝ) * (s : ℝ) ^ s * Real.exp ((s : ℝ) + 2 * (n : ℝ))) * (s : ℝ) ^ s := by
          rw [Real.exp_add]
  exact le_of_mul_le_mul_right h3 (by positivity)

private theorem circuitCount_le_sum_exactMinFunctions (n g : ℕ) :
    circuitCount n g ≤ ∑ s ∈ Finset.range (g + 1), (exactMinFunctions n s).ncard := by
  induction g with
  | zero =>
    rw [Finset.sum_range_one, circuitCount_eq_ncard]
    refine Set.ncard_le_ncard fun f hf => ?_
    rw [mem_computableFunctions_iff_complexity_le] at hf
    exact Nat.eq_zero_of_le_zero hf
  | succ g ih =>
    rw [Finset.sum_range_succ, circuitCount_eq_ncard]
    have hsub : Boolean.computableFunctions n (g + 1) ⊆
        Boolean.computableFunctions n g ∪ exactMinFunctions n (g + 1) := by
      intro f hf
      rw [mem_computableFunctions_iff_complexity_le] at hf
      rcases Nat.lt_or_eq_of_le hf with hlt | heq
      · exact Or.inl (mem_computableFunctions_iff_complexity_le.mpr (Nat.lt_succ_iff.mp hlt))
      · exact Or.inr heq
    calc (Boolean.computableFunctions n (g + 1)).ncard
        ≤ (Boolean.computableFunctions n g ∪ exactMinFunctions n (g + 1)).ncard :=
          Set.ncard_le_ncard hsub
      _ ≤ (Boolean.computableFunctions n g).ncard + (exactMinFunctions n (g + 1)).ncard :=
          Set.ncard_union_le _ _
      _ = circuitCount n g + (exactMinFunctions n (g + 1)).ncard := by rw [circuitCount_eq_ncard]
      _ ≤ ∑ s ∈ Finset.range (g + 1), (exactMinFunctions n s).ncard +
            (exactMinFunctions n (g + 1)).ncard := Nat.add_le_add_right ih _

/-- Tight upper bound on the number of `n`-variable Boolean functions computable by De Morgan
circuits with at most `g` gates: for all positive integers `n` and `g`,
`circuitCount n g < g ^ g * exp (g + 4 * n)`. -/
theorem circuitCount_lt_pow_mul_exp {n g : ℕ} (hn : 1 ≤ n) (hg : 1 ≤ g) :
    (circuitCount n g : ℝ) < (g : ℝ) ^ g * Real.exp ((g : ℝ) + 4 * (n : ℝ)) := by
  by_cases hbig : 2 ^ n ≤ g
  · have htriv : (circuitCount n g : ℝ) ≤ (2 : ℝ) ^ (2 ^ n) := by
      exact_mod_cast circuitCount_le_two_pow_two_pow n g
    have hg2 : (2 : ℝ) ≤ (g : ℝ) := by
      have : 2 ≤ 2 ^ n := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) hn
      exact_mod_cast this.trans hbig
    have hpow : (2 : ℝ) ^ (2 ^ n) ≤ (g : ℝ) ^ g := by
      calc (2 : ℝ) ^ (2 ^ n)
          ≤ (2 : ℝ) ^ g := pow_le_pow_right₀ (by norm_num) hbig
        _ ≤ (g : ℝ) ^ g := pow_le_pow_left₀ (by norm_num) hg2 g
    have hexp : (1 : ℝ) < Real.exp ((g : ℝ) + 4 * (n : ℝ)) := by
      rw [Real.one_lt_exp_iff]
      positivity
    calc (circuitCount n g : ℝ) ≤ (2 : ℝ) ^ (2 ^ n) := htriv
      _ ≤ (g : ℝ) ^ g := hpow
      _ = (g : ℝ) ^ g * 1 := (mul_one _).symm
      _ < (g : ℝ) ^ g * Real.exp ((g : ℝ) + 4 * (n : ℝ)) :=
          mul_lt_mul_of_pos_left hexp (by positivity)
  · push Not at hbig
    have hsum_nat : (circuitCount n g : ℝ) ≤
        ∑ s ∈ Finset.range (g + 1), ((exactMinFunctions n s).ncard : ℝ) := by
      exact_mod_cast circuitCount_le_sum_exactMinFunctions n g
    rw [Finset.sum_range_succ'] at hsum_nat
    have hzero : ((exactMinFunctions n 0).ncard : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast exactMinFunctions_zero_card_le n
    have hpos_sum : ∑ s ∈ Finset.range g, ((exactMinFunctions n (s + 1)).ncard : ℝ) ≤
        (g : ℝ) ^ 2 * (g : ℝ) ^ g * Real.exp ((g : ℝ) + 2 * (n : ℝ)) := by
      have hterm : ∀ s ∈ Finset.range g,
          ((exactMinFunctions n (s + 1)).ncard : ℝ) ≤
            (g : ℝ) * (g : ℝ) ^ g * Real.exp ((g : ℝ) + 2 * (n : ℝ)) := by
        intro s hs
        have hs_le : s + 1 ≤ g := Finset.mem_range.mp hs
        have h1 := exactMinFunctions_real_le hn (Nat.succ_pos s)
        have hgs : ((s + 1 : ℕ) : ℝ) ≤ (g : ℝ) := by exact_mod_cast hs_le
        have hpow_le : ((s + 1 : ℕ) : ℝ) ^ (s + 1) ≤ (g : ℝ) ^ g := by
          calc ((s + 1 : ℕ) : ℝ) ^ (s + 1)
              ≤ (g : ℝ) ^ (s + 1) := pow_le_pow_left₀ (by positivity) hgs _
            _ ≤ (g : ℝ) ^ g := pow_le_pow_right₀ (by exact_mod_cast hg) hs_le
        have hexp_le : Real.exp (((s + 1 : ℕ) : ℝ) + 2 * (n : ℝ)) ≤
            Real.exp ((g : ℝ) + 2 * (n : ℝ)) := Real.exp_le_exp.mpr (by linarith)
        calc ((exactMinFunctions n (s + 1)).ncard : ℝ)
            ≤ ((s + 1 : ℕ) : ℝ) * ((s + 1 : ℕ) : ℝ) ^ (s + 1) *
                Real.exp (((s + 1 : ℕ) : ℝ) + 2 * (n : ℝ)) := h1
          _ ≤ (g : ℝ) * (g : ℝ) ^ g * Real.exp ((g : ℝ) + 2 * (n : ℝ)) := by gcongr
      calc ∑ s ∈ Finset.range g, ((exactMinFunctions n (s + 1)).ncard : ℝ)
          ≤ ∑ _s ∈ Finset.range g, ((g : ℝ) * (g : ℝ) ^ g * Real.exp ((g : ℝ) + 2 * (n : ℝ))) :=
            Finset.sum_le_sum hterm
        _ = (g : ℝ) ^ 2 * (g : ℝ) ^ g * Real.exp ((g : ℝ) + 2 * (n : ℝ)) := by
            simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            ring
    have hn_lt : (n : ℝ) < (g : ℝ) ^ g * Real.exp ((g : ℝ) + 2 * (n : ℝ)) := by
      have hg1 : (1 : ℝ) ≤ (g : ℝ) ^ g := one_le_pow₀ (by exact_mod_cast hg)
      have hn_exp : (n : ℝ) < Real.exp ((g : ℝ) + 2 * (n : ℝ)) := by
        have hle := Real.add_one_le_exp ((g : ℝ) + 2 * (n : ℝ))
        have hg_pos : (0 : ℝ) < (g : ℝ) := by positivity
        linarith
      nlinarith
    have h4_lt_e2 : (4 : ℝ) < Real.exp 2 := by
      have he : (2.7 : ℝ) < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
      have hsq : Real.exp 2 = (Real.exp 1) ^ 2 := by
        rw [sq, ← Real.exp_add]; norm_num
      rw [hsq]
      nlinarith
    have h1_g2_le : (1 : ℝ) + (g : ℝ) ^ 2 ≤ (4 : ℝ) ^ n := by
      have hnat : 1 + g ^ 2 ≤ 4 ^ n := by
        have hg_le : g ≤ 2 ^ n - 1 := by omega
        have h2n_ge : 2 ≤ 2 ^ n := by
          calc 2 = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) hn
        have h4eq : 4 ^ n = (2 ^ n) ^ 2 := by
          rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, mul_comm, pow_mul]
        rw [h4eq]
        have hsub : (2 ^ n - 1) ^ 2 + 1 ≤ (2 ^ n) ^ 2 := by
          obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le' h2n_ge
          rw [hm]
          have : m + 2 - 1 = m + 1 := by omega
          rw [this]
          nlinarith
        rw [add_comm]
        exact (Nat.add_le_add_right (Nat.pow_le_pow_left hg_le 2) 1).trans hsub
      exact_mod_cast hnat
    have h4n_lt : (4 : ℝ) ^ n < Real.exp (2 * (n : ℝ)) := by
      rw [show (2 : ℝ) * (n : ℝ) = (n : ℕ) * (2 : ℝ) by ring, Real.exp_nat_mul]
      exact pow_lt_pow_left₀ h4_lt_e2 (by norm_num) (by omega)
    calc (circuitCount n g : ℝ)
        ≤ (g : ℝ) ^ 2 * (g : ℝ) ^ g * Real.exp ((g : ℝ) + 2 * (n : ℝ)) + (n : ℝ) := by linarith
      _ < (g : ℝ) ^ 2 * (g : ℝ) ^ g * Real.exp ((g : ℝ) + 2 * (n : ℝ)) +
            (g : ℝ) ^ g * Real.exp ((g : ℝ) + 2 * (n : ℝ)) := by linarith
      _ = (1 + (g : ℝ) ^ 2) * ((g : ℝ) ^ g * Real.exp ((g : ℝ) + 2 * (n : ℝ))) := by ring
      _ ≤ (4 : ℝ) ^ n * ((g : ℝ) ^ g * Real.exp ((g : ℝ) + 2 * (n : ℝ))) := by gcongr
      _ < Real.exp (2 * (n : ℝ)) * ((g : ℝ) ^ g * Real.exp ((g : ℝ) + 2 * (n : ℝ))) :=
          mul_lt_mul_of_pos_right h4n_lt (by positivity)
      _ = (g : ℝ) ^ g * (Real.exp ((g : ℝ) + 2 * (n : ℝ)) * Real.exp (2 * (n : ℝ))) := by ring
      _ = (g : ℝ) ^ g * Real.exp ((g : ℝ) + 4 * (n : ℝ)) := by
          rw [← Real.exp_add]
          congr 2; ring

/-- Flipping a single entry of a Boolean function's truth table increases its De Morgan circuit
complexity by at most `2 * n + 5` gates. -/
theorem complexity_le_of_hammingDist_le_one {n : ℕ} {f f' : BooleanFunction n}
    (hdist : hammingDist (MCSP.truthTable n f) (MCSP.truthTable n f') ≤ 1) :
    complexity interpretation (single f') ≤ complexity interpretation (single f) + (2 * n + 5) := by
  by_cases heq : f = f'
  · subst heq; omega
  · have hne_tt : MCSP.truthTable n f ≠ MCSP.truthTable n f' := fun h =>
      heq ((MCSP.truthTable n).injective h)
    have hpos : 0 < hammingDist (MCSP.truthTable n f) (MCSP.truthTable n f') :=
      Nat.pos_of_ne_zero (fun h => hne_tt (eq_of_hammingDist_eq_zero h))
    have hcard : #(Finset.univ.filter fun i : Fin (2 ^ n) =>
        MCSP.truthTable n f i ≠ MCSP.truthTable n f' i) = 1 := by
      rw [← hammingDist]
      omega
    obtain ⟨idx, hidx⟩ := Finset.card_eq_one.mp hcard
    let a : BitString n := (BitString.equivFin n).symm idx
    have hxor : f' = fun x => f x ^^ decide (x = a) := by
      funext x
      by_cases hx : x = a
      · subst hx
        have hmem : idx ∈ Finset.univ.filter (fun i : Fin (2 ^ n) =>
            MCSP.truthTable n f i ≠ MCSP.truthTable n f' i) := by
          rw [hidx]; exact Finset.mem_singleton_self idx
        have hneq : f a ≠ f' a := by
          simpa [MCSP.truthTable, a] using (Finset.mem_filter.mp hmem).2
        cases hfa : f a <;> cases hfa' : f' a <;> simp_all
      · have hnot : BitString.equivFin n x ∉ Finset.univ.filter (fun i : Fin (2 ^ n) =>
            MCSP.truthTable n f i ≠ MCSP.truthTable n f' i) := by
          rw [hidx, Finset.mem_singleton]
          intro he
          exact hx (by simpa [a] using congrArg (BitString.equivFin n).symm he)
        have hfx : f x = f' x := by
          by_contra hne
          exact hnot (Finset.mem_filter.mpr
            ⟨Finset.mem_univ _, by simpa [MCSP.truthTable] using hne⟩)
        simp [hx, hfx]
    have hminterm : complexity interpretation (single fun x : BitString n => decide (x = a)) ≤
        2 * n + 1 :=
      (Boolean.synthesis_minterm (n := n) (k := n) id a).complexity_le
    rw [hxor]
    have hcomb := Boolean.complexity_xor_le f (fun x => decide (x = a))
    exact hcomb.trans (by omega)

end CslibFrontier.Circuits.Boolean
