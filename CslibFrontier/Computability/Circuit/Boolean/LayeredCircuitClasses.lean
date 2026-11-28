/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.AlgebraicBranchingProgram
public import Cslib.Computability.Circuit.Basic
public import Cslib.Computability.Circuit.Composition
public import Cslib.Computability.Languages.Slice
public import CslibFrontier.Computability.Circuit.Boolean.ACC0.Basic
public import CslibFrontier.Computability.Circuit.Boolean.ACC0.Simulation
public import CslibFrontier.Computability.Circuit.Boolean.DepthClasses
public import CslibFrontier.Computability.Circuit.Boolean.Formula
public import CslibFrontier.Computability.Circuit.Boolean.PPoly
public import CslibFrontier.Computability.Circuit.CompositionDepth
public import CslibFrontier.Computability.Circuit.Monotone.Basic
public import CslibFrontier.Computability.Circuit.Monotone.DualRail
public import CslibFrontier.Foundations.Data.Nat.PolynomialBound.Closure
public import CslibFrontier.Foundations.Data.Nat.PolynomialBound.Log

import CslibFrontier.Computability.Circuit.Pi
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Layered Boolean Circuit Classes, Monotone Composition, and ABP Simulation in `NC²`

This module defines the layered circuit composition framework (`GateFamily`, `gateComp`,
`langClass`) and concrete nonuniform circuit classes over `Bool` used in algebraic circuit
complexity:

* `MON`, `BAR c`, `MMON` (`BAR c ∘ MON`),
* `CCHeight h m` (`CC_h[m]`) and `CC0`,
* `ACHeightMod h m` (`AC_h[m]`),
* `NuDet p` (languages recognized by polynomial-size ABPs over `ZMod p`), `NuDetChain`, and
  `NuItDet` (iterated determinant classes),
* `NC2CompMON` (`NC² ∘ MON`) and `NuItDetCompMON` (`NuItDet ∘ MON`).

It proves under standard Lean axioms:
* Closure of `MMON` under complement, bitwise complement (via De Morgan duality on monotone
  circuits), and outer bounded-arity composition.
* Simulation of `AND_d` and `BAR_c` gates by single `MOD_m` gates and `CC0 ⊆ ACC0 ⊆ NC 2 ⊆ PPoly`.

## Main definitions

* `CslibFrontier.Computability.Circuit.GateFamily`, `gateComp`, `gateCompList`, `langClass`.
* `CslibFrontier.Computability.Circuit.barGate`, `andGate`, `modGateFamily`, `monGate`,
  `deMorganGate`, `nc2Gate`, `abpGate`.
* `CslibFrontier.Computability.Circuit.MON`, `BAR`, `MMON`, `CCHeight`, `CC0`, `NuDet`,
  `NuDetChain`, `NuItDet`, `NC2CompMON`, `NuItDetCompMON`, `ACHeightMod`.

## Main results

* `CslibFrontier.Computability.Circuit.gateComp_assoc`: exact associativity of layered gate
  composition preserving size.
* `CslibFrontier.Computability.Circuit.MMON_compl_closed`,
  `CslibFrontier.Computability.Circuit.MMON_bitwiseCompl_closed`.
* `CslibFrontier.Computability.Circuit.CC0_subset_ACC0`.
-/

public section

namespace CslibFrontier.Computability.Circuit

open Cslib
open Cslib.Circuits
open Cslib.Circuits.Boolean
open Cslib.Circuits.Monotone
open scoped Matrix

/-! ### Layered Gate Families and Exact Size-Preserving Composition -/

/-- A size-parameterized family of Boolean functions (`n` inputs, size bound `s`). -/
public abbrev GateFamily : Type := (n : ℕ) → (s : ℕ) → Set ((Fin n → Bool) → Bool)

/-- Layered composition `G ∘ H`: an outer `G`-gate of arity `k` and size `sg` fed by `k` inner
`H`-gates of sizes `sh i`, with total size `sg + ∑ i, sh i + k ≤ s` (gates plus wires). -/
@[expose]
public def gateComp (G H : GateFamily) : GateFamily :=
  fun n s =>
    { f | ∃ (k : ℕ) (g : (Fin k → Bool) → Bool) (hs : Fin k → (Fin n → Bool) → Bool)
        (sg : ℕ) (sh : Fin k → ℕ),
        g ∈ G k sg ∧ (∀ i, hs i ∈ H n (sh i)) ∧
        sg + (∑ i : Fin k, sh i) + k ≤ s ∧
        ∀ x : Fin n → Bool, f x = g (fun i => hs i x) }

/-- Right-associated composition of a list of gate families. -/
@[expose]
public def gateCompList : List GateFamily → GateFamily
  | [] => fun n s => { f | 1 ≤ s ∧ ∃ i : Fin n, ∀ x, f x = x i }
  | [G] => G
  | G :: Gs => gateComp G (gateCompList Gs)

@[simp]
public theorem gateCompList_singleton (G : GateFamily) : gateCompList [G] = G := by exact rfl

@[simp]
public theorem gateCompList_cons_cons (G H : GateFamily) (Gs : List GateFamily) :
    gateCompList (G :: H :: Gs) = gateComp G (gateCompList (H :: Gs)) := by exact rfl

/-- Monotonicity of a gate family in the size bound `s`. -/
@[expose]
public def GateFamily.IsMono (G : GateFamily) : Prop :=
  ∀ ⦃n s₁ s₂ : ℕ⦄, s₁ ≤ s₂ → G n s₁ ⊆ G n s₂

/-- Nonuniform language class determined by a gate family at polynomial size. -/
@[expose]
public def langClass (G : GateFamily) : Set (Language Bool) :=
  { L | ∃ s : ℕ → ℕ, PolynomiallyBounded s ∧ ∀ n, L.slice n ∈ G n (s n) }

public theorem gateComp_mono {G₁ G₂ H₁ H₂ : GateFamily}
    (hG : ∀ n s, G₁ n s ⊆ G₂ n s) (hH : ∀ n s, H₁ n s ⊆ H₂ n s) :
    ∀ n s, gateComp G₁ H₁ n s ⊆ gateComp G₂ H₂ n s := by
  intro n s f ⟨k, g, hs, sg, sh, hg, hhs, hsz, heval⟩
  exact ⟨k, g, hs, sg, sh, hG k sg hg, fun i => hH n (sh i) (hhs i), hsz, heval⟩

public theorem langClass_mono {G₁ G₂ : GateFamily} (h : ∀ n s, G₁ n s ⊆ G₂ n s) :
    langClass G₁ ⊆ langClass G₂ := by
  rintro L ⟨s, hs, hL⟩
  exact ⟨s, hs, fun n => h n (s n) (hL n)⟩

/-- Closure of a gate family under input reindexing (`mapInputs`). -/
@[expose]
public def GateFamily.IsMapInputsClosed (G : GateFamily) : Prop :=
  ∀ ⦃n m s : ℕ⦄ (ρ : Fin n → Fin m) {f : (Fin n → Bool) → Bool},
    f ∈ G n s → (fun y => f (y ∘ ρ)) ∈ G m s

/-- Exact associativity of `gateComp`: `(G₁ ∘ (G₂ ∘ G₃)) n s ⊆ ((G₁ ∘ G₂) ∘ G₃) n s`
whenever `G₂` is closed under input reindexing. -/
public theorem gateComp_assoc_left (G₁ G₂ G₃ : GateFamily) (hG₂ : G₂.IsMapInputsClosed) (n s : ℕ) :
    gateComp G₁ (gateComp G₂ G₃) n s ⊆ gateComp (gateComp G₁ G₂) G₃ n s := by
  rintro f ⟨k₁, g₁, hs₁, sg₁, sh₁, hg₁, hhs₁, hsz₁, hf⟩
  choose k₂ g₂ hs₂ sg₂ sh₂ hg₂ hhs₂ hsz₂ heval₂ using hhs₁
  let e : (Σ i : Fin k₁, Fin (k₂ i)) ≃ Fin (∑ i : Fin k₁, k₂ i) :=
    Fintype.equivFinOfCardEq (by simp [Fintype.card_sigma])
  let gOut : (Fin (∑ i, k₂ i) → Bool) → Bool := fun y =>
    g₁ (fun i => g₂ i (fun j => y (e ⟨i, j⟩)))
  let hIn : Fin (∑ i, k₂ i) → (Fin n → Bool) → Bool := fun idx =>
    hs₂ (e.symm idx).1 (e.symm idx).2
  let shIn : Fin (∑ i, k₂ i) → ℕ := fun idx => sh₂ (e.symm idx).1 (e.symm idx).2
  refine ⟨∑ i, k₂ i, gOut, hIn, sg₁ + (∑ i, sg₂ i) + k₁, shIn, ?_, ?_, ?_, ?_⟩
  · refine ⟨k₁, g₁, fun i y => g₂ i (fun j => y (e ⟨i, j⟩)), sg₁, sg₂, hg₁, ?_, le_rfl,
      fun _ => rfl⟩
    intro i
    exact hG₂ (fun j => e ⟨i, j⟩) (hg₂ i)
  · intro idx; exact hhs₂ (e.symm idx).1 (e.symm idx).2
  · have hsum_sh : (∑ idx : Fin (∑ i, k₂ i), shIn idx) =
        ∑ i : Fin k₁, ∑ j : Fin (k₂ i), sh₂ i j := by
      rw [← e.sum_comp]
      simp only [shIn, Fintype.sum_sigma]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [e.symm_apply_apply]
    rw [hsum_sh]
    have hsum_step : (∑ i : Fin k₁, sg₂ i) + (∑ i : Fin k₁, ∑ j : Fin (k₂ i), sh₂ i j) +
        (∑ i : Fin k₁, k₂ i) = ∑ i : Fin k₁, (sg₂ i + (∑ j : Fin (k₂ i), sh₂ i j) + k₂ i) := by
      simp [Finset.sum_add_distrib]
    have hle_sum : (∑ i : Fin k₁, (sg₂ i + (∑ j : Fin (k₂ i), sh₂ i j) + k₂ i)) ≤
        ∑ i : Fin k₁, sh₁ i := Finset.sum_le_sum fun i _ => hsz₂ i
    omega
  · intro x
    rw [hf x]
    simp only [gOut, hIn]
    congr 1; funext i
    rw [heval₂ i x]
    congr 1; funext j; rw [e.symm_apply_apply]

/-! ### Concrete Gate Families -/

/-- Bounded-arity Boolean gate (`BAR_c`): any Boolean function depending on at most `c` input
coordinates (size `1`). -/
@[expose]
public def barGate (c : ℕ) : GateFamily :=
  fun n s =>
    { f | 1 ≤ s ∧ ∃ I : Finset (Fin n), I.card ≤ c ∧
        ∀ x y : Fin n → Bool, (∀ i ∈ I, x i = y i) → f x = f y }

/-- Conjunction gate of arity at most `d` (`AND_d`, size `1`). -/
@[expose]
public def andGate (d : ℕ) : GateFamily :=
  fun n s =>
    { f | 1 ≤ s ∧ ∃ (k : ℕ) (sel : Fin k → Fin n), k ≤ d ∧
        ∀ x : Fin n → Bool, f x = decide (∀ j : Fin k, x (sel j) = true) }

/-- `MOD_m` gate with arbitrary accepting set `S ⊆ ZMod m`, counting `k` input wires plus `1`
for the gate itself (`1 + k ≤ s`). -/
@[expose]
public def modGateFamily (m : ℕ) : GateFamily :=
  fun n s =>
    { f | ∃ (k : ℕ) (sel : Fin k → Fin n) (S : Set (ZMod m)),
        1 + k ≤ s ∧
        let := Classical.propDecidable
        ∀ x : Fin n → Bool,
          f x = decide ((∑ j : Fin k, if x (sel j) then (1 : ZMod m) else 0) ∈ S) }

/-- Monotone Boolean circuit gate (`MON`). -/
@[expose]
public def monGate : GateFamily :=
  fun n s =>
    { f | ∃ C : Circuit Monotone.signature n 1,
        C.size ≤ s ∧ C.Computes Monotone.interpretation (single f) }

/-- De Morgan Boolean circuit gate with explicit depth envelope `D : ℕ → ℕ`. -/
@[expose]
public def deMorganGate (D : ℕ → ℕ) : GateFamily :=
  fun n s =>
    { f | ∃ C : Circuit Boolean.signature n 1,
        C.size ≤ s ∧ C.depth ≤ D n ∧ C.Computes Boolean.interpretation (single f) }

/-- `NC²` gate family with depth constant `c` (`depth ≤ c * (log₂ n + 1)²`). -/
@[expose]
public def nc2Gate (c : ℕ) : GateFamily :=
  deMorganGate (fun n => c * (Nat.log 2 n + 1) ^ 2)

/-- `GABP_p` gate: ABP over `ZMod p` with accepting set `S ⊆ ZMod p` and size `P.size ≤ s`. -/
@[expose]
public def abpGate (p : ℕ) : GateFamily :=
  fun n s =>
    { f | ∃ (P : ABP (ZMod p) (Fin n)) (S : Set (ZMod p)),
        P.size ≤ s ∧
        let := Classical.propDecidable
        ∀ x : Fin n → Bool, f x = decide (P.eval (fun i => if x i then 1 else 0) ∈ S) }

/-- Unbounded-fan-in `AC[m]` single-layer gate (`AND`, `OR`, `NOT`, or `MOD_m` with arbitrary
accepting set `S ⊆ ZMod m`, counting wires + 1). -/
@[expose]
public def acModSingleGate (m : ℕ) : GateFamily :=
  fun n s =>
    modGateFamily m n s ∪
    { f | ∃ (k : ℕ) (sel : Fin k → Fin n), 1 + k ≤ s ∧
        ((∀ x, f x = decide (∀ j, x (sel j) = true)) ∨
         (∀ x, f x = decide (∃ j, x (sel j) = true))) } ∪
    { f | 1 ≤ s ∧ (∃ i : Fin n, (∀ x, f x = x i) ∨ (∀ x, f x = !x i)) }

/-! ### Standard Nonuniform Complexity Classes -/

/-- `MON`: languages recognized by polynomial-size monotone Boolean circuits. -/
@[expose]
public def MON : Set (Language Bool) := langClass monGate

/-- `BAR_c`: languages recognized by Boolean functions of essential arity at most `c`. -/
@[expose]
public def BAR (c : ℕ) : Set (Language Bool) := langClass (barGate c)

/-- `MMON`: languages recognized by circuits of the form `BAR_c ∘ MON` for some constant `c`. -/
@[expose]
public def MMON : Set (Language Bool) :=
  ⋃ c : ℕ, langClass (gateComp (barGate c) monGate)

/-- `CC_h[m]`: languages recognized by polynomial-size `h`-layer circuits of `MOD_m` gates. -/
@[expose]
public def CCHeight (h m : ℕ) : Set (Language Bool) :=
  langClass (gateCompList (List.replicate h (modGateFamily m)))

/-- `CC⁰`: union of `CC_h[m]` over all constant depths `h` and moduli `m ≥ 2`. -/
@[expose]
public def CC0 : Set (Language Bool) :=
  ⋃ (h : ℕ) (m : ℕ) (_ : 2 ≤ m), CCHeight h m

/-- Membership characterization for `CC⁰`. -/
public theorem mem_CC0_iff {L : Language Bool} :
    L ∈ CC0 ↔ ∃ (h m : ℕ), 2 ≤ m ∧ L ∈ CCHeight h m := by
  simp only [CC0, Set.mem_iUnion, exists_prop]

/-- `AC_h[m]`: languages recognized by polynomial-size `h`-layer circuits of `AND`, `OR`, `NOT`,
and `MOD_m` gates. -/
@[expose]
public def ACHeightMod (h m : ℕ) : Set (Language Bool) :=
  langClass (gateCompList (List.replicate h (acModSingleGate m)))

/-- `NuDet p`: languages recognized by polynomial-size ABPs over `ZMod p`. -/
@[expose]
public def NuDet (p : ℕ) : Set (Language Bool) := langClass (abpGate p)

/-- `NuDet p₁ ∘ ... ∘ NuDet p_h`: constant-height composition of ABP layers over `ps`. -/
@[expose]
public def NuDetChain (ps : List ℕ) : Set (Language Bool) :=
  langClass (gateCompList (ps.map abpGate))

/-- `NuItDet`: union of `NuDet p₁ ∘ ... ∘ NuDet p_h` over all finite lists of primes. -/
@[expose]
public def NuItDet : Set (Language Bool) :=
  ⋃ (ps : List ℕ) (_ : ∀ p ∈ ps, Nat.Prime p), NuDetChain ps

/-- Membership characterization for `NuItDet`. -/
public theorem mem_NuItDet_iff {L : Language Bool} :
    L ∈ NuItDet ↔ ∃ ps : List ℕ, (∀ p ∈ ps, Nat.Prime p) ∧ L ∈ NuDetChain ps := by
  simp only [NuItDet, Set.mem_iUnion, exists_prop]

/-- `NC² ∘ MON`: languages recognized by polynomial-size `NC²` outer circuits over `MON` inputs. -/
@[expose]
public def NC2CompMON : Set (Language Bool) :=
  ⋃ c : ℕ, langClass (gateComp (nc2Gate c) monGate)

/-- `NuItDet ∘ MON`: languages recognized by `NuItDet` outer circuits over `MON` inputs. -/
@[expose]
public def NuItDetCompMON : Set (Language Bool) :=
  ⋃ (ps : List ℕ) (_ : ∀ p ∈ ps, Nat.Prime p),
    langClass (gateComp (gateCompList (ps.map abpGate)) monGate)

/-! ### `MON` and `MMON` Properties (De Morgan Duality & Closure) -/

/-- Monotone circuits are closed under replacing every input by its negation via De Morgan
duality: `f (!x) = !(g x)` for a monotone circuit `g` of the same size! -/
public theorem monGate_dual {n s : ℕ} {f : (Fin n → Bool) → Bool} (hf : f ∈ monGate n s) :
    (fun x : Fin n → Bool => !f (fun i => !x i)) ∈ monGate n s := by
  -- Dualizing every gate in `C` (`and ↔ or`, `const b ↦ const (!b)`) preserves size and computes
  -- `x ↦ !C.eval (fun i => !x i)`.
  obtain ⟨C, hsz, hcomp⟩ := hf
  let dualOp : Monotone.Op → Monotone.Op
    | .const b => .const (!b)
    | .and => .or
    | .or => .and
  let φ : Monotone.signature.Hom Monotone.signature :=
    ⟨dualOp, fun op => by cases op <;> rfl⟩
  let C' : Circuit Monotone.signature n 1 := C.mapOp φ
  refine ⟨C', by simpa [C'] using hsz, ?_⟩
  -- Prove by induction on `C.program` that `(P.mapOp φ).trace x = !P.trace (!x)`.
  have hwire : ∀ {g : ℕ} (P : Program Monotone.signature n g) (x : Fin n → Bool) (w : Wire n g),
      (P.mapOp φ).trace Monotone.interpretation x w =
      !(P.trace Monotone.interpretation (fun i => !x i) w) := by
    intro g P x
    induction P with
    | empty =>
      intro w; cases w with
      | input i => simp [Program.trace]
      | gate j => exact j.elim0
    | @gate g P line ih =>
      intro w
      induction w using Wire.lastCases with
      | castSucc w' =>
        simp only [Program.mapOp_gate, Program.trace_gate_castSucc]
        exact ih w'
      | last =>
        change (P.mapOp φ |>.gate (line.mapOp φ)).eval Monotone.interpretation x (Fin.last g) =
          !((P.gate line).eval Monotone.interpretation (fun i => !x i) (Fin.last g))
        rw [Program.eval_gate_last, Program.eval_gate_last]
        rcases line with ⟨op, wires⟩
        cases op with
        | const b => rfl
        | and =>
          have h0 : Wire.elim x ((P.mapOp φ).eval Monotone.interpretation x) (wires 0) =
              !(Wire.elim (fun i => !x i) (P.eval Monotone.interpretation (fun i => !x i))
                (wires 0)) := ih (wires 0)
          have h1 : Wire.elim x ((P.mapOp φ).eval Monotone.interpretation x) (wires 1) =
              !(Wire.elim (fun i => !x i) (P.eval Monotone.interpretation (fun i => !x i))
                (wires 1)) := ih (wires 1)
          change (Wire.elim x ((P.mapOp φ).eval Monotone.interpretation x) (wires 0) ||
              Wire.elim x ((P.mapOp φ).eval Monotone.interpretation x) (wires 1)) =
            !(Wire.elim (fun i => !x i) (P.eval Monotone.interpretation (fun i => !x i))
                (wires 0) &&
              Wire.elim (fun i => !x i) (P.eval Monotone.interpretation (fun i => !x i))
                (wires 1))
          rw [h0, h1]
          cases Wire.elim (fun i => !x i) (P.eval Monotone.interpretation (fun i => !x i))
            (wires 0) <;>
          cases Wire.elim (fun i => !x i) (P.eval Monotone.interpretation (fun i => !x i))
            (wires 1) <;> rfl
        | or =>
          have h0 : Wire.elim x ((P.mapOp φ).eval Monotone.interpretation x) (wires 0) =
              !(Wire.elim (fun i => !x i) (P.eval Monotone.interpretation (fun i => !x i))
                (wires 0)) := ih (wires 0)
          have h1 : Wire.elim x ((P.mapOp φ).eval Monotone.interpretation x) (wires 1) =
              !(Wire.elim (fun i => !x i) (P.eval Monotone.interpretation (fun i => !x i))
                (wires 1)) := ih (wires 1)
          change (Wire.elim x ((P.mapOp φ).eval Monotone.interpretation x) (wires 0) &&
              Wire.elim x ((P.mapOp φ).eval Monotone.interpretation x) (wires 1)) =
            !(Wire.elim (fun i => !x i) (P.eval Monotone.interpretation (fun i => !x i))
                (wires 0) ||
              Wire.elim (fun i => !x i) (P.eval Monotone.interpretation (fun i => !x i))
                (wires 1))
          rw [h0, h1]
          cases Wire.elim (fun i => !x i) (P.eval Monotone.interpretation (fun i => !x i))
            (wires 0) <;>
          cases Wire.elim (fun i => !x i) (P.eval Monotone.interpretation (fun i => !x i))
            (wires 1) <;> rfl
  intro x
  funext j
  have hev : C'.eval Monotone.interpretation x j =
      !C.eval Monotone.interpretation (fun i => !x i) j :=
    hwire C.program x (C.outputs j)
  have hc := congrFun (hcomp (fun i => !x i)) j
  simpa [single_apply, hev] using congrArg (! ·) hc

/-- Every monotone circuit evaluates to a monotone Boolean function. -/
public theorem monotone_of_mem_monGate {n s : ℕ} {f : (Fin n → Bool) → Bool}
    (hf : f ∈ monGate n s) : Monotone f := by
  obtain ⟨C, -, hcomp⟩ := hf
  have hwire : ∀ {g : ℕ} (P : Program Monotone.signature n g) (x y : Fin n → Bool),
      (∀ i, x i ≤ y i) → ∀ w : Wire n g,
        P.trace Monotone.interpretation x w ≤ P.trace Monotone.interpretation y w := by
    intro g P x y hxy
    induction P with
    | empty =>
      intro w; cases w with
      | input i => exact hxy i
      | gate j => exact j.elim0
    | @gate g P line ih =>
      intro w
      induction w using Wire.lastCases with
      | castSucc w' =>
        simp only [Program.trace_gate_castSucc]
        exact ih w'
      | last =>
        change (P.gate line).eval Monotone.interpretation x (Fin.last g) ≤
          (P.gate line).eval Monotone.interpretation y (Fin.last g)
        rw [Program.eval_gate_last, Program.eval_gate_last]
        exact Monotone.interpretation_mono line.op fun a => ih (line.wires a)
  intro x y hxy
  have hx := congrFun (hcomp x) 0
  have hy := congrFun (hcomp y) 0
  simp only [single_apply] at hx hy
  rw [← hx, ← hy]
  exact hwire C.program x y hxy (C.outputs 0)

/-- `MON ⊆ MMON`. -/
public theorem MON_subset_MMON : MON ⊆ MMON := by
  rintro L ⟨s, hs, hL⟩
  refine Set.mem_iUnion.mpr ⟨1, ⟨fun n => s n + 2, by fun_prop, fun n => ?_⟩⟩
  refine ⟨1, fun y => y 0, fun _ => L.slice n, 1, fun _ => s n, ?_, fun _ => hL n, by simp; omega,
    fun _ => rfl⟩
  exact ⟨le_rfl, {0}, by simp, fun x y h => h 0 (by simp)⟩

/-- `MMON` is closed under complement (`L ∈ MMON → Lᶜ ∈ MMON`). -/
public theorem MMON_compl_closed {L : Language Bool} (hL : L ∈ MMON) : Lᶜ ∈ MMON := by
  obtain ⟨c, s, hs, hC⟩ := Set.mem_iUnion.mp hL
  refine Set.mem_iUnion.mpr ⟨c, s, hs, fun n => ?_⟩
  obtain ⟨k, g, hf, sg, sh, ⟨hsg, I, hI, hg⟩, hhf, hsz, heval⟩ := hC n
  refine ⟨k, fun y => !g y, hf, sg, sh, ⟨hsg, I, hI, fun x y hxy => congrArg (! ·) (hg x y hxy)⟩,
    hhf, hsz, fun x => ?_⟩
  have hslice : Lᶜ.slice n x = !(L.slice n x) := by
    rw [Bool.eq_iff_iff, Language.slice_eq_true_iff, Bool.not_eq_true',
      Bool.eq_false_iff, ne_eq, Language.slice_eq_true_iff]
    rfl
  rw [hslice, heval x]

/-- `MMON` is closed under bitwise input complement. -/
public theorem MMON_bitwiseCompl_closed {L : Language Bool} (hL : L ∈ MMON) :
    Language.ofSlices (fun n x => L.slice n (fun i => !x i)) ∈ MMON := by
  obtain ⟨c, s, hs, hC⟩ := Set.mem_iUnion.mp hL
  refine Set.mem_iUnion.mpr ⟨c, s, hs, fun n => ?_⟩
  obtain ⟨k, g, hf, sg, sh, ⟨hsg, I, hI, hg⟩, hhf, hsz, heval⟩ := hC n
  refine ⟨k, fun y => g (fun i => !y i), fun i x => !hf i (fun j => !x j), sg, sh,
    ⟨hsg, I, hI, fun x y hxy => hg _ _ (fun i hi => congrArg (! ·) (hxy i hi))⟩,
    fun i => monGate_dual (hhf i), hsz, fun x => ?_⟩
  simp only [Language.slice_ofSlices, heval (fun i => !x i), Bool.not_not]

/-- Output projection never increases circuit depth. -/
public theorem depth_comapOutputs_le {σ : Signature} {n m m' : ℕ}
    (f : Fin m' → Fin m) (c : Circuit σ n m) :
    (c.comapOutputs f).depth ≤ c.depth :=
  (Circuit.depth_le_iff _).mpr fun j => c.outputDepths_le_depth (f j)

/-- Input relabeling preserves circuit depth. -/
public theorem depth_mapInputs {σ : Signature} {n n' m : ℕ}
    (f : Fin n → Fin n') (c : Circuit σ n m) :
    (c.mapInputs f).depth = c.depth := by
  have hprog : ∀ {g : ℕ} (p : Program σ n g) (w : Wire n g),
      (p.mapInputs f).wireDepths (w.mapInputs f) = p.wireDepths w := by
    intro g p
    induction p with
    | empty =>
      intro w; cases w with
      | input i => rfl
      | gate j => exact j.elim0
    | @gate g p line ih =>
      intro w
      induction w using Wire.lastCases with
      | castSucc w' =>
        have hcast : (w'.castSucc).mapInputs f = (w'.mapInputs f).castSucc := by
          cases w' <;> rfl
        rw [hcast, Program.mapInputs_gate, Program.wireDepths_gate_castSucc,
          Program.wireDepths_gate_castSucc]
        exact ih w'
      | last =>
        have hlast : (Wire.gate (Fin.last g)).mapInputs f = Wire.gate (Fin.last g) := rfl
        rw [hlast, Program.mapInputs_gate, Program.wireDepths_gateWire,
          Program.wireDepths_gateWire, Program.depths_gate_last, Program.depths_gate_last]
        simp only [Line.depth, Line.mapInputs_op, Line.mapInputs_wires, Function.comp_apply]
        congr 1
        refine congrArg (fun fn => Fin.foldl _ fn 0) ?_
        funext depth k
        rw [ih (line.wires k)]
  have hout : (c.mapInputs f).outputDepths = c.outputDepths := by
    funext j
    exact hprog c.program (c.outputs j)
  change Fin.foldl _ (fun depth k => max depth ((c.mapInputs f).outputDepths k)) 0 =
    Fin.foldl _ (fun depth k => max depth (c.outputDepths k)) 0
  rw [hout]

/-- Parallel composition of `m` circuits sharing the same `n` inputs, yielding `m * w` outputs. -/
@[expose]
public def appendCircuits {σ : Signature} {n w : ℕ} :
    ∀ {m : ℕ}, (Fin m → Circuit σ n w) → Circuit σ n (m * w)
  | 0, _ => (Circuit.wiring σ Fin.elim0).comapOutputs (fun j => Fin.elim0 (j.cast (by simp)))
  | m + 1, cs =>
    (((appendCircuits (fun i : Fin m => cs i.castSucc)).append (cs (Fin.last m)))).comapOutputs
      (fun j => j.cast (by ring))

public theorem eval_appendCircuits {σ : Signature} {U : Type*} (I : Interpretation σ U)
    {n w m : ℕ} (cs : Fin m → Circuit σ n w) (x : Fin n → U) (i : Fin m) (j : Fin w) :
    (appendCircuits cs).eval I x (finProdFinEquiv (i, j)) = (cs i).eval I x j := by
  induction m with
  | zero => exact i.elim0
  | succ m ih =>
    simp only [appendCircuits, Circuit.eval_comapOutputs, Circuit.eval_append]
    refine Fin.lastCases ?_ ?_ i
    · have hcast : (finProdFinEquiv (Fin.last m, j)).cast (by ring) = Fin.natAdd (m * w) j := by
        ext; simp [finProdFinEquiv]; ring
      simp [hcast]
    · intro i'
      have hcast : (finProdFinEquiv (i'.castSucc, j)).cast (by ring) =
          Fin.castAdd w (finProdFinEquiv (i', j)) := by
        ext; simp [finProdFinEquiv]
      simp [hcast, ih]

public theorem size_appendCircuits {σ : Signature} {n w m : ℕ} (cs : Fin m → Circuit σ n w) :
    (appendCircuits cs).size = ∑ i : Fin m, (cs i).size := by
  induction m with
  | zero => simp [appendCircuits]
  | succ m ih =>
    simp only [appendCircuits, Circuit.comapOutputs_size, Circuit.size_append,
      Fin.sum_univ_castSucc]
    rw [ih]

public theorem depth_appendCircuits_le {σ : Signature} {n w m : ℕ}
    (cs : Fin m → Circuit σ n w) {D : ℕ} (hD : ∀ i, (cs i).depth ≤ D) :
    (appendCircuits cs).depth ≤ D := by
  induction m with
  | zero =>
    exact (depth_comapOutputs_le _ _).trans (by simp)
  | succ m ih =>
    exact (depth_comapOutputs_le _ _).trans
      ((Circuit.depth_append_le _ _).trans
        (max_le (ih _ (fun i => hD i.castSucc)) (hD (Fin.last m))))

/-- Any Boolean function `f : (Fin c → Bool) → Bool` on `c` variables has a De Morgan formula
(DNF) of size at most `2 ^ c * (2 * c + 2) + 1`. -/
private noncomputable def dnfFormula {c : ℕ} (f : (Fin c → Bool) → Bool) :
    Formula Boolean.signature c :=
  Formula.orList <| ((Finset.univ : Finset (Fin c → Bool)).filter (fun a => f a = true)).toList.map
    fun a => Formula.andList <| (List.finRange c).map fun i =>
      if a i then Formula.input i else (Formula.input i).not

private theorem eval_dnfFormula {c : ℕ} (f : (Fin c → Bool) → Bool) (x : Fin c → Bool) :
    (dnfFormula f).eval Boolean.interpretation x = f x := by
  rw [Bool.eq_iff_iff]
  simp only [dnfFormula, Formula.eval_orList, List.any_map, List.any_eq_true, Function.comp_apply,
    Finset.mem_toList, Finset.mem_filter, Finset.mem_univ, true_and, Formula.eval_andList,
    List.all_map, List.all_eq_true, List.mem_finRange, true_implies]
  have hterm : ∀ a : Fin c → Bool,
      (∀ i : Fin c, (if a i then Formula.input i else (Formula.input i).not).eval
        Boolean.interpretation x = true) ↔ x = a := by
    intro a
    constructor
    · intro hall; funext i
      have hi := hall i
      cases ha : a i
      · simp only [ha, Bool.false_eq_true, ↓reduceIte, Formula.eval_not, Formula.eval_input,
          Bool.not_eq_true'] at hi
        exact hi
      · simp only [ha, ↓reduceIte, Formula.eval_input] at hi
        exact hi
    · rintro rfl i
      cases hx : x i <;> simp [hx, Formula.eval_input, Formula.eval_not]
  simp only [hterm]
  exact ⟨fun ⟨a, ha, hx⟩ => hx ▸ ha, fun hx => ⟨x, hx, rfl⟩⟩

private theorem size_dnfFormula_le {c : ℕ} (f : (Fin c → Bool) → Bool) :
    (dnfFormula f).size ≤ 2 ^ c * (2 * c + 2) + 1 := by
  have h1 : (dnfFormula f).size ≤
      (((Finset.univ : Finset (Fin c → Bool)).filter (fun a => f a = true)).toList.map fun a =>
        (Formula.andList <| (List.finRange c).map fun i =>
          if a i then Formula.input i else (Formula.input i).not).size).sum +
      ((Finset.univ : Finset (Fin c → Bool)).filter (fun a => f a = true)).toList.length + 1 := by
    -- `size (orList l) ≤ (l.map size).sum + l.length + 1`
    have hor : ∀ l : List (Formula Boolean.signature c),
        (Formula.orList l).size ≤ (l.map Formula.size).sum + l.length + 1 := by
      intro l
      cases l with
      | nil => simp [Formula.orList, Formula.balanced_nil]
      | cons a as =>
        have hne : a :: as ≠ [] := List.cons_ne_nil _ _
        have h := Formula.size_balanced_add_one (op := Boolean.Op.or) (hop := rfl)
          (Formula.const false) hne
        simp only [Formula.orList]
        omega
    have h0 := hor (((Finset.univ : Finset (Fin c → Bool)).filter
      (fun a => f a = true)).toList.map fun a =>
        Formula.andList <| (List.finRange c).map fun i =>
          if a i then Formula.input i else (Formula.input i).not)
    simpa only [dnfFormula, List.map_map, Function.comp_def, List.length_map] using h0
  have hterm : ∀ a : Fin c → Bool,
      (Formula.andList <| (List.finRange c).map fun i =>
        if a i then Formula.input i else (Formula.input i).not).size ≤ 2 * c + 1 := by
    intro a
    have hand : ∀ l : List (Formula Boolean.signature c),
        (Formula.andList l).size ≤ (l.map Formula.size).sum + l.length + 1 := by
      intro l
      cases l with
      | nil => simp [Formula.andList, Formula.balanced_nil]
      | cons b bs =>
        have hne : b :: bs ≠ [] := List.cons_ne_nil _ _
        have h := Formula.size_balanced_add_one (op := Boolean.Op.and) (hop := rfl)
          (Formula.const true) hne
        simp only [Formula.andList]; omega
    have hle := hand ((List.finRange c).map fun i =>
      if a i then Formula.input i else (Formula.input i).not)
    have hsum : (((List.finRange c).map fun i =>
        (if a i then Formula.input i else (Formula.input i).not).size)).sum ≤ c := by
      calc _ ≤ ((List.finRange c).map fun _ => 1).sum := by
            refine List.sum_le_sum fun i _ => ?_
            split_ifs <;> simp [Formula.size_input, Formula.size_not]
        _ = c := by simp [List.sum_replicate]
    simp only [List.map_map, Function.comp_def, List.length_map, List.length_finRange] at hle
    omega
  have hlen : ((Finset.univ : Finset (Fin c → Bool)).filter
      (fun a => f a = true)).toList.length ≤ 2 ^ c := by
    rw [Finset.length_toList]
    exact (Finset.card_filter_le _ _).trans (by simp)
  have hsum_all : ((((Finset.univ : Finset (Fin c → Bool)).filter (fun a => f a = true)).toList.map
      fun a => (Formula.andList <| (List.finRange c).map fun i =>
        if a i then Formula.input i else (Formula.input i).not).size)).sum ≤
      2 ^ c * (2 * c + 1) := by
    calc _ ≤ ((((Finset.univ : Finset (Fin c → Bool)).filter (fun a => f a = true)).toList.map
          fun _ => 2 * c + 1)).sum := List.sum_le_sum fun a _ => hterm a
      _ = _ * (2 * c + 1) := by simp [List.sum_replicate]
      _ ≤ 2 ^ c * (2 * c + 1) := Nat.mul_le_mul_right _ hlen
  nlinarith

/-- `MMON ⊆ PPoly`. -/
public theorem MMON_subset_PPoly : MMON ⊆ PPoly := by
  rintro L ⟨_, ⟨c, rfl⟩, ⟨s, hs, hC⟩⟩
  rw [mem_PPoly_iff_exists_circuits]
  have hbuild : ∀ n, ∃ C : Circuit Boolean.signature n 1,
      C.size ≤ s n + 2 ^ c * (2 * c + 2) + 1 ∧
      C.Computes Boolean.interpretation (single (L.slice n)) := by
    intro n
    obtain ⟨k, g, hf, sg, sh, ⟨hsg, I, hI, hg⟩, hhf, hsz, heval⟩ := hC n
    choose Cm hCm_sz hCm_comp using hhf
    let eI : Fin I.card ≃ I := (Fintype.equivFinOfCardEq (Fintype.card_coe I)).symm
    let gSmall : (Fin I.card → Bool) → Bool := fun y =>
      g (fun i => if hi : i ∈ I then y (eI.symm ⟨i, hi⟩) else false)
    let Cg : Circuit Boolean.signature I.card 1 := (dnfFormula gSmall).toCircuit
    let Cin : Circuit Boolean.signature n I.card :=
      (appendCircuits (fun j : Fin I.card => (Cm (eI j).1).mapOp Monotone.toDeMorgan)).comapOutputs
        (fun j => finProdFinEquiv (j, 0))
    let C : Circuit Boolean.signature n 1 := Cg.comp Cin
    refine ⟨C, ?_, ?_⟩
    · have hCin_sz : Cin.size ≤ ∑ i : Fin k, sh i := by
        simp only [Cin, Circuit.comapOutputs_size, size_appendCircuits, Circuit.size_mapOp]
        calc ∑ j : Fin I.card, (Cm (eI j).1).size
            ≤ ∑ j : Fin I.card, sh (eI j).1 := Finset.sum_le_sum fun j _ => hCm_sz _
          _ = ∑ i ∈ I, sh i := by
              rw [← Finset.sum_coe_sort I sh]
              exact eI.sum_comp (fun x : I => sh x.1)
          _ ≤ ∑ i : Fin k, sh i := Finset.sum_le_univ_sum_of_nonneg (fun _ => Nat.zero_le _)
      have hCg_sz : Cg.size ≤ 2 ^ c * (2 * c + 2) + 1 := by
        simp only [Cg, Formula.size_toCircuit]
        have h1 := size_dnfFormula_le gSmall
        have hpow : 2 ^ I.card ≤ 2 ^ c := Nat.pow_le_pow_right (by omega) hI
        have hmul : 2 ^ I.card * (2 * I.card + 2) ≤ 2 ^ c * (2 * c + 2) :=
          Nat.mul_le_mul hpow (by omega)
        omega
      simp only [C, Circuit.size_comp]
      omega
    · intro x
      funext o
      obtain rfl : o = 0 := Subsingleton.elim o 0
      simp only [C, Circuit.eval_comp, Cg, Formula.eval_toCircuit, eval_dnfFormula, gSmall,
        single_apply]
      rw [heval x]
      refine hg _ _ fun i hi => ?_
      simp only [hi, ↓reduceDIte, Cin, Circuit.eval_comapOutputs, Function.comp_apply,
        eval_appendCircuits]
      rw [Circuit.eval_mapOp (I := Monotone.interpretation)]
      have hc := congrFun (hCm_comp i x) 0
      simpa [single_apply, eI] using hc
  choose C hC_sz hC_comp using hbuild
  refine ⟨C, fun n => s n + 2 ^ c * (2 * c + 2) + 1, by fun_prop, fun n => ⟨hC_sz n, hC_comp n⟩⟩

/-! ### `MOD_m` Gate Simulations and `CC⁰ ⊆ ACC⁰` -/

/-- `AND_d` is simulated by a single `MOD_{d + 1}` gate with accepting set `{d}`! -/
public theorem andGate_subset_modGate (d : ℕ) (n s : ℕ) :
    andGate d n s ⊆ modGateFamily (d + 1) n (s + d) := by
  rintro f ⟨hs, k, sel, hk, hf⟩
  refine ⟨k, sel, {(k : ZMod (d + 1))}, by omega, fun x => ?_⟩
  rw [hf x]
  simp only [Set.mem_singleton_iff]
  congr 1
  rw [propext_iff]
  have hle : (Finset.univ.filter fun j : Fin k => x (sel j) = true).card ≤ k :=
    (Finset.card_filter_le _ _).trans (by simp)
  have hsum : (∑ j : Fin k, if x (sel j) = true then (1 : ZMod (d + 1)) else 0) =
      ((Finset.univ.filter fun j : Fin k => x (sel j) = true).card : ZMod (d + 1)) := by
    simp [Finset.sum_boole]
  have hsum' : (∑ j : Fin k, @ite _ (x (sel j) = true) (Classical.propDecidable _)
      (1 : ZMod (d + 1)) 0) =
      ((Finset.univ.filter fun j : Fin k => x (sel j) = true).card : ZMod (d + 1)) := by
    rw [← hsum]; exact Finset.sum_congr rfl fun j _ => by split_ifs <;> rfl
  rw [hsum']
  constructor
  · intro hall
    have huniv : Finset.univ.filter (fun j : Fin k => x (sel j) = true) = Finset.univ := by
      ext j; simp [hall j]
    rw [huniv, Finset.card_univ, Fintype.card_fin]
  · intro heq
    have hmod : (Finset.univ.filter fun j : Fin k => x (sel j) = true).card % (d + 1) =
        k % (d + 1) := by
      have := (ZMod.natCast_eq_natCast_iff' _ _ (d + 1)).mp heq
      exact this
    have hcard : (Finset.univ.filter fun j : Fin k => x (sel j) = true).card = k := by
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hmod
      exact hmod
    intro j
    have hmem : j ∈ Finset.univ.filter (fun j : Fin k => x (sel j) = true) := by
      have huniv : Finset.univ.filter (fun j : Fin k => x (sel j) = true) = Finset.univ :=
        Finset.eq_univ_of_card _ (by simpa using hcard)
      rw [huniv]; exact Finset.mem_univ j
    exact (Finset.mem_filter.mp hmem).2

/-- `MOD_q` is simulated by `MOD_m` whenever `q ∣ m` and `0 < m` (multiplying weights by
`m / q`). -/
public theorem modGate_dvd_sim {q m : ℕ} (hm : 0 < m) (hdvd : q ∣ m) (n s : ℕ) :
    modGateFamily q n s ⊆ modGateFamily m n (1 + (m / q) * s) := by
  rintro f ⟨k, sel, S, hks, hf⟩
  let r := m / q
  have hr : q * r = m := Nat.mul_div_cancel' hdvd
  let e : Fin k × Fin r ≃ Fin (k * r) := finProdFinEquiv
  let sel' : Fin (k * r) → Fin n := fun idx => sel (e.symm idx).1
  let S' : Set (ZMod m) := { z | ∃ y ∈ S, (r : ZMod m) * (y.val : ZMod m) = z }
  refine ⟨k * r, sel', S', ?_, fun x => ?_⟩
  · have h1 : k * r ≤ s * r := Nat.mul_le_mul_right r (by omega)
    rw [mul_comm r s]; omega
  · rw [hf x]
    have hsum : (∑ idx : Fin (k * r), if x (sel' idx) = true then (1 : ZMod m) else 0) =
        (r : ZMod m) * (∑ j : Fin k, if x (sel j) = true then (1 : ZMod m) else 0) := by
      rw [← e.sum_comp]
      simp only [sel', e.symm_apply_apply, Fintype.sum_prod_type, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      split_ifs <;> simp
    have hsum' : (∑ idx : Fin (k * r), @ite _ (x (sel' idx) = true) (Classical.propDecidable _)
        (1 : ZMod m) 0) =
        (r : ZMod m) * (∑ j : Fin k, if x (sel j) = true then (1 : ZMod m) else 0) := by
      rw [← hsum]; exact Finset.sum_congr rfl fun _ _ => by split_ifs <;> rfl
    rw [hsum']
    -- `((r : ZMod m) * ∑_j b_j) ∈ S' ↔ (∑_j b_j : ZMod q) ∈ S` since
    -- `r * y ≡ r * z (mod q*r) ↔ y ≡ z (mod q)`.
    have hq_pos : 0 < q := Nat.pos_of_dvd_of_pos hdvd hm
    have : NeZero m := ⟨Nat.ne_of_gt hm⟩
    have : NeZero q := ⟨Nat.ne_of_gt hq_pos⟩
    have hiff : ((r : ZMod m) * ∑ j : Fin k, if x (sel j) = true then (1 : ZMod m) else 0) ∈ S' ↔
        (∑ j : Fin k, @ite _ (x (sel j) = true) (Classical.propDecidable _)
          (1 : ZMod q) 0) ∈ S := by
      let c := (Finset.univ.filter fun j : Fin k => x (sel j) = true).card
      have hc_m : (∑ j : Fin k, if x (sel j) = true then (1 : ZMod m) else 0) = (c : ZMod m) := by
        simp [c, Finset.sum_boole]
      have hc_q : (∑ j : Fin k, @ite _ (x (sel j) = true) (Classical.propDecidable _)
          (1 : ZMod q) 0) = (c : ZMod q) := by
        have h1 : (∑ j : Fin k, if x (sel j) = true then (1 : ZMod q) else 0) = (c : ZMod q) := by
          simp [c, Finset.sum_boole]
        rw [← h1]; exact Finset.sum_congr rfl fun _ _ => by split_ifs <;> rfl
      rw [hc_m, hc_q]
      constructor
      · rintro ⟨y, hyS, hy_eq⟩
        have hmod : (r * y.val) % m = (r * c) % m :=
          (ZMod.natCast_eq_natCast_iff' (r * y.val) (r * c) m).mp
            (by simpa [Nat.cast_mul] using hy_eq)
        have hr_pos : 0 < r := Nat.div_pos (Nat.le_of_dvd hm hdvd) hq_pos
        rw [← hr, mul_comm q r, Nat.mul_mod_mul_left, Nat.mul_mod_mul_left] at hmod
        have hmod' := Nat.eq_of_mul_eq_mul_left hr_pos hmod
        have hyc : y = (c : ZMod q) := by
          rw [← ZMod.natCast_zmod_val y]
          exact (ZMod.natCast_eq_natCast_iff' _ _ q).mpr hmod'
        exact hyc ▸ hyS
      · intro hS
        refine ⟨(c : ZMod q), hS, ?_⟩
        rw [ZMod.val_natCast]
        have hmod : (r * (c % q)) % m = (r * c) % m := by
          rw [← hr, mul_comm q r, Nat.mul_mod_mul_left, Nat.mul_mod_mul_left, Nat.mod_mod]
        simpa [Nat.cast_mul] using (ZMod.natCast_eq_natCast_iff' _ _ m).mpr hmod
    rw [Bool.eq_iff_iff, @decide_eq_true_iff _ (Classical.propDecidable _),
      @decide_eq_true_iff _ (Classical.propDecidable _)]
    exact hiff.symm

/-- Single-gate circuit for a single operation `op` of signature `σ`. -/
private def singleOpCircuit (σ : Signature) (op : σ.Op) : Circuit σ (σ.Arity op) 1 :=
  Circuit.oneGate (σ := σ) op id

private theorem eval_singleOpCircuit {σ : Signature} {U : Type*} (I : Interpretation σ U)
    (op : σ.Op) (x : Fin (σ.Arity op) → U) (j : Fin 1) :
    (singleOpCircuit σ op).eval I x j = I op x := by
  simp [singleOpCircuit]

private theorem size_singleOpCircuit (σ : Signature) (op : σ.Op) :
    (singleOpCircuit σ op).size = 1 := rfl

private theorem depth_singleOpCircuit (σ : Signature) (op : σ.Op) :
    (singleOpCircuit σ op).depth ≤ 1 := by
  simp [singleOpCircuit]

/-- Helper: `Circuit` over `Unbounded.extSignature` testing `∑_j y_j ∈ S` over `ZMod m`
in depth `≤ 4` and size `≤ 3 * m + 2`. -/
private def modAcceptExtCircuit (m k : ℕ) (S : Set (ZMod m)) [DecidablePred (· ∈ S)] :
    Circuit Unbounded.extSignature k 1 :=
  let constTrue : Circuit Unbounded.extSignature k 1 :=
    (singleOpCircuit Unbounded.extSignature (.ac (.and 0))).mapInputs Fin.elim0
  let testR (r : Fin m) : Circuit Unbounded.extSignature k 1 :=
    let pad := (m - r.1) % m
    let padCirc : Circuit Unbounded.extSignature k pad :=
      (appendCircuits (fun _ : Fin pad => constTrue)).comapOutputs (fun j => finProdFinEquiv (j, 0))
    let allWires : Circuit Unbounded.extSignature k (k + pad) :=
      (Circuit.id Unbounded.extSignature k).append padCirc
    let mg := singleOpCircuit Unbounded.extSignature (.gate (k + pad))
    let neg := singleOpCircuit Unbounded.extSignature (.ac .not)
    (neg.comp mg).comp allWires
  let rs : List (Fin m) := (List.finRange m).filter (fun r => decide ((r.1 : ZMod m) ∈ S))
  let tests : Circuit Unbounded.extSignature k rs.length :=
    (appendCircuits (fun idx : Fin rs.length => testR (rs.get idx))).comapOutputs
      (fun j => finProdFinEquiv (j, 0))
  (singleOpCircuit Unbounded.extSignature (.ac (.or rs.length))).comp tests

private theorem eval_modAcceptExtCircuit (m k : ℕ) [NeZero m] (S : Set (ZMod m))
    [DecidablePred (· ∈ S)] (y : Fin k → Bool) :
    (modAcceptExtCircuit m k S).eval (Unbounded.extInterpretation (modGate m)) y 0 =
      decide ((∑ j : Fin k, if y j then (1 : ZMod m) else 0) ∈ S) := by
  have hm : 0 < m := NeZero.pos m
  have htest : ∀ (r : Fin m),
      ((singleOpCircuit Unbounded.extSignature (.ac .not)).comp
        (singleOpCircuit Unbounded.extSignature (.gate (k + (m - r.1) % m))) |>.comp
        ((Circuit.id Unbounded.extSignature k).append
          ((appendCircuits (fun _ : Fin ((m - r.1) % m) =>
            (singleOpCircuit Unbounded.extSignature (.ac (.and 0))).mapInputs
              Fin.elim0)).comapOutputs
            (fun j => finProdFinEquiv (j, 0))))).eval
          (Unbounded.extInterpretation (modGate m)) y 0 =
        decide ((∑ j : Fin k, if y j then (1 : ZMod m) else 0) = (r.1 : ZMod m)) := by
    intro r
    simp only [Circuit.eval_comp, eval_singleOpCircuit, Unbounded.extInterpretation_ac,
      Unbounded.interpretation_not, Unbounded.extInterpretation_gate, modGate, ne_eq]
    -- Count true entries in `Fin.append y (fun _ => true)`:
    have hcard :
        (Finset.univ.filter fun i : Fin (k + (m - r.1) % m) =>
          ((Circuit.id Unbounded.extSignature k).append
            ((appendCircuits (fun _ : Fin ((m - r.1) % m) =>
              (singleOpCircuit Unbounded.extSignature (.ac (.and 0))).mapInputs
                Fin.elim0)).comapOutputs
              (fun j => finProdFinEquiv (j, 0)))).eval
            (Unbounded.extInterpretation (modGate m)) y i = true).card =
        (Finset.univ.filter fun j : Fin k => y j = true).card + (m - r.1) % m := by
      have heval_app : ∀ i : Fin (k + (m - r.1) % m),
          ((Circuit.id Unbounded.extSignature k).append
            ((appendCircuits (fun _ : Fin ((m - r.1) % m) =>
              (singleOpCircuit Unbounded.extSignature (.ac (.and 0))).mapInputs
                Fin.elim0)).comapOutputs
              (fun j => finProdFinEquiv (j, 0)))).eval
            (Unbounded.extInterpretation (modGate m)) y i =
          Fin.append y (fun _ => true) i := by
        intro i
        simp only [Circuit.eval_append, Circuit.eval_wiring, Function.comp_id]
        refine Fin.addCases (fun j => by simp) (fun j => ?_) i
        simp [Circuit.eval_comapOutputs, eval_appendCircuits, Circuit.eval_mapInputs,
          eval_singleOpCircuit, Unbounded.extInterpretation_ac, Unbounded.interpretation_and]
      simp only [heval_app]
      -- Split `Fin (k + pad)` filter into left (`y j = true`) + right (`true = true`):
      rw [← Fintype.card_subtype, ← Fintype.card_subtype]
      have hsum_card :
          (Finset.univ.filter fun i : Fin (k + (m - r.1) % m) =>
            Fin.append y (fun _ => true) i = true).card =
          (Finset.univ.filter fun j : Fin k => y j = true).card + (m - r.1) % m := by
        have h1 : (Finset.univ.filter fun i : Fin (k + (m - r.1) % m) =>
            Fin.append y (fun _ => true) i = true).card =
            ∑ i : Fin (k + (m - r.1) % m),
              if Fin.append y (fun _ => true) i = true then 1 else 0 := by
          simp [Finset.sum_boole]
        rw [h1, Fin.sum_univ_add]
        simp [Finset.sum_boole]
      exact by simpa [Fintype.card_subtype] using hsum_card
    have hsum : (∑ j : Fin k, if y j = true then (1 : ZMod m) else 0) =
        ((Finset.univ.filter fun j : Fin k => y j = true).card : ZMod m) := by
      simp [Finset.sum_boole]
    rw [hcard, hsum]
    have hiff : ((Finset.univ.filter fun j : Fin k => y j = true).card + (m - r.1) % m) % m = 0 ↔
        ((Finset.univ.filter fun j : Fin k => y j = true).card : ZMod m) = (r.1 : ZMod m) := by
      have hpad : (((m - r.1) % m : ℕ) : ZMod m) = -(r.1 : ZMod m) := by
        rw [(ZMod.natCast_eq_natCast_iff' _ _ m).mpr (Nat.mod_mod _ _),
          Nat.cast_sub r.2.le, ZMod.natCast_self, zero_sub]
      rw [← Nat.dvd_iff_mod_eq_zero, ← ZMod.natCast_eq_zero_iff, Nat.cast_add, hpad,
        add_neg_eq_zero]
    rw [Bool.eq_iff_iff, Bool.not_eq_true', decide_eq_false_iff_not, not_not, decide_eq_true_iff]
    exact hiff
  rw [modAcceptExtCircuit, Circuit.eval_comp, eval_singleOpCircuit,
    Unbounded.extInterpretation_ac, Unbounded.interpretation_or]
  simp only [Circuit.eval_comapOutputs, Function.comp_apply, eval_appendCircuits, htest]
  have hiff : (∃ j : Fin ((List.finRange m).filter fun r => decide ((r.1 : ZMod m) ∈ S)).length,
      decide ((∑ i : Fin k, if y i then (1 : ZMod m) else 0) =
        ((((List.finRange m).filter fun r =>
          decide ((r.1 : ZMod m) ∈ S)).get j).1 : ZMod m)) = true) ↔
      (∑ i : Fin k, if y i then (1 : ZMod m) else 0) ∈ S := by
    constructor
    · rintro ⟨j, hj⟩
      have heq := of_decide_eq_true hj
      have hmem := ((List.mem_filter.mp (List.get_mem _ j)).2)
      rw [heq]; exact of_decide_eq_true hmem
    · intro hS
      let a := ∑ i : Fin k, if y i then (1 : ZMod m) else 0
      let r : Fin m := ⟨a.val, a.val_lt⟩
      have hr_eq : (r.1 : ZMod m) = a := ZMod.natCast_zmod_val a
      have hr_mem : r ∈ (List.finRange m).filter (fun r => decide ((r.1 : ZMod m) ∈ S)) :=
        List.mem_filter.mpr ⟨List.mem_finRange r, decide_eq_true (hr_eq.symm ▸ hS)⟩
      obtain ⟨j, hj⟩ := List.mem_iff_get.mp hr_mem
      exact ⟨j, decide_eq_true (by rw [hj]; exact hr_eq.symm)⟩
  rw [Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff]
  exact hiff

private theorem size_modAcceptExtCircuit_le (m k : ℕ) [NeZero m] (S : Set (ZMod m))
    [DecidablePred (· ∈ S)] :
    (modAcceptExtCircuit m k S).size ≤ m * (m + 3) + 1 := by
  rw [modAcceptExtCircuit, Circuit.size_comp, size_singleOpCircuit,
    Circuit.comapOutputs_size, size_appendCircuits]
  have htest_le : ∀ r : Fin m,
      ((singleOpCircuit Unbounded.extSignature (.ac .not)).comp
        (singleOpCircuit Unbounded.extSignature (.gate (k + (m - r.1) % m))) |>.comp
        ((Circuit.id Unbounded.extSignature k).append
          ((appendCircuits (fun _ : Fin ((m - r.1) % m) =>
            (singleOpCircuit Unbounded.extSignature (.ac (.and 0))).mapInputs
              Fin.elim0)).comapOutputs
            (fun j => finProdFinEquiv (j, 0))))).size ≤ m + 2 := by
    intro r
    simp only [Circuit.size_comp, size_singleOpCircuit, Circuit.size_append, Circuit.size_wiring,
      Circuit.comapOutputs_size, size_appendCircuits, Circuit.mapInputs_size, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one, zero_add]
    have := Nat.mod_lt (m - r.1) (NeZero.pos m)
    omega
  have hsum : (∑ idx : Fin ((List.finRange m).filter
        fun r => decide ((r.1 : ZMod m) ∈ S)).length,
      ((singleOpCircuit Unbounded.extSignature (.ac .not)).comp
        (singleOpCircuit Unbounded.extSignature
          (.gate (k + (m - (((List.finRange m).filter
            fun r => decide ((r.1 : ZMod m) ∈ S)).get idx).1) % m))) |>.comp
        ((Circuit.id Unbounded.extSignature k).append
          ((appendCircuits (fun _ : Fin ((m - (((List.finRange m).filter
            fun r => decide ((r.1 : ZMod m) ∈ S)).get idx).1) % m) =>
            (singleOpCircuit Unbounded.extSignature (.ac (.and 0))).mapInputs
              Fin.elim0)).comapOutputs
            (fun j => finProdFinEquiv (j, 0))))).size) ≤
      ((List.finRange m).filter fun r => decide ((r.1 : ZMod m) ∈ S)).length * (m + 2) := by
    calc _ ≤ ∑ _ : Fin _, (m + 2) := Finset.sum_le_sum fun idx _ => htest_le _
      _ = _ * (m + 2) := by simp
  have hlen : ((List.finRange m).filter fun r => decide ((r.1 : ZMod m) ∈ S)).length ≤ m :=
    (List.length_filter_le _ _).trans (by simp)
  nlinarith

private theorem depth_modAcceptExtCircuit_le (m k : ℕ) (S : Set (ZMod m))
    [DecidablePred (· ∈ S)] :
    (modAcceptExtCircuit m k S).depth ≤ 4 := by
  simp only [modAcceptExtCircuit]
  refine (Circuit.depth_comp_le _ _).trans ?_
  have h1 := depth_singleOpCircuit Unbounded.extSignature
    (.ac (.or ((List.finRange m).filter (fun r => decide ((r.1 : ZMod m) ∈ S))).length))
  refine (add_le_add h1 (show _ ≤ 3 from ?_)).trans (by omega)
  refine (depth_comapOutputs_le _ _).trans ?_
  refine depth_appendCircuits_le _ fun idx => ?_
  refine (Circuit.depth_comp_le _ _).trans ?_
  refine (add_le_add
    (show _ ≤ 2 from (Circuit.depth_comp_le _ _).trans
      (add_le_add (depth_singleOpCircuit _ _) (depth_singleOpCircuit _ _)))
    (show _ ≤ 1 from ?_)).trans (by omega)
  refine (Circuit.depth_append_le _ _).trans (max_le (by simp) ?_)
  refine (depth_comapOutputs_le _ _).trans ?_
  refine depth_appendCircuits_le _ fun _ => ?_
  rw [depth_mapInputs]
  exact depth_singleOpCircuit Unbounded.extSignature (.ac (.and 0))

/-- `CC⁰ ⊆ ACC⁰` (hence `CC⁰ ⊆ NC² ⊆ P/poly`). -/
public theorem CC0_subset_ACC0 : CC0 ⊆ ACC0 := by
  classical
  rintro L ⟨_, ⟨h, rfl⟩, _, ⟨m, rfl⟩, _, ⟨hm2, rfl⟩, s, hs, hL⟩
  have : NeZero m := ⟨by omega⟩
  -- Show every `f ∈ gateCompList (List.replicate h (modGateFamily m)) n s` has an `AC0Mod m`
  -- circuit of depth `≤ 4 * h` and size `≤ (m * (m + 3) + 2) * s`.
  have hsim : ∀ (h' n' s' : ℕ) (f : (Fin n' → Bool) → Bool),
      f ∈ gateCompList (List.replicate h' (modGateFamily m)) n' s' →
      ∃ C : Circuit Unbounded.extSignature n' 1,
        C.Computes (Unbounded.extInterpretation (modGate m)) (single f) ∧
        C.depth ≤ 4 * h' ∧ C.size ≤ (m * (m + 3) + 2) * s' := by
    intro h'
    induction h' with
    | zero =>
      intro n' s' f ⟨_, i, hf⟩
      refine ⟨Circuit.wiring Unbounded.extSignature (fun _ => i), fun x => ?_, by simp, by simp⟩
      funext o; obtain rfl : o = 0 := Subsingleton.elim o 0; simp [single_apply, hf]
    | succ h' ih =>
      cases h' with
      | zero =>
        intro n' s' f ⟨k, sel, S, hks, hf⟩
        let C : Circuit Unbounded.extSignature n' 1 := (modAcceptExtCircuit m k S).mapInputs sel
        refine ⟨C, fun x => ?_, ?_, ?_⟩
        · funext o; obtain rfl : o = 0 := Subsingleton.elim o 0
          simp only [C, Circuit.eval_mapInputs, eval_modAcceptExtCircuit, single_apply, hf,
            Function.comp_apply]
          rw [Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff]
          have hsum_eq : (∑ j : Fin k, if x (sel j) = true then (1 : ZMod m) else 0) =
              ∑ j : Fin k, @ite _ (x (sel j) = true) (Classical.propDecidable _)
                (1 : ZMod m) 0 :=
            Finset.sum_congr rfl fun _ _ => by split_ifs <;> rfl
          rw [hsum_eq]
        · rw [depth_mapInputs]
          exact (depth_modAcceptExtCircuit_le m k S).trans (by omega)
        · rw [Circuit.mapInputs_size]
          have hsz := size_modAcceptExtCircuit_le m k S
          have hs1 : 1 ≤ s' := by omega
          nlinarith
      | succ h'' =>
        intro n' s' f ⟨k, g, hs_fn, sg, sh, ⟨k', sel, S, hks, hg⟩, hhs, hsz, hf⟩
        have hsub : ∀ i : Fin k, ∃ Ci : Circuit Unbounded.extSignature n' 1,
            Ci.Computes (Unbounded.extInterpretation (modGate m)) (single (hs_fn i)) ∧
            Ci.depth ≤ 4 * (h'' + 1) ∧ Ci.size ≤ (m * (m + 3) + 2) * sh i :=
          fun i => ih n' (sh i) (hs_fn i) (hhs i)
        choose Ci hCi_comp hCi_d hCi_s using hsub
        let C_in : Circuit Unbounded.extSignature n' k :=
          (appendCircuits Ci).comapOutputs (fun j => finProdFinEquiv (j, 0))
        let C_out : Circuit Unbounded.extSignature k 1 := (modAcceptExtCircuit m k' S).mapInputs sel
        let C : Circuit Unbounded.extSignature n' 1 := C_out.comp C_in
        refine ⟨C, fun x => ?_, ?_, ?_⟩
        · funext o; obtain rfl : o = 0 := Subsingleton.elim o 0
          simp only [C, Circuit.eval_comp, C_out, Circuit.eval_mapInputs, eval_modAcceptExtCircuit,
            single_apply, hf, hg]
          rw [Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff]
          have hsum_eq :
              (∑ j : Fin k', if (C_in.eval (Unbounded.extInterpretation (modGate m)) x ∘ sel) j =
                  true then (1 : ZMod m) else 0) =
              ∑ j : Fin k', @ite _ (hs_fn (sel j) x = true) (Classical.propDecidable _)
                (1 : ZMod m) 0 := by
            refine Finset.sum_congr rfl fun j _ => ?_
            have hj : (C_in.eval (Unbounded.extInterpretation (modGate m)) x ∘ sel) j =
                hs_fn (sel j) x := by
              simp only [C_in, Circuit.eval_comapOutputs, Function.comp_apply, eval_appendCircuits]
              have := congrFun (hCi_comp (sel j) x) 0
              simpa [single_apply] using this
            rw [hj]; split_ifs <;> rfl
          rw [hsum_eq]
        · refine (Circuit.depth_comp_le _ _).trans ?_
          have hd1 : C_out.depth ≤ 4 := by
            rw [depth_mapInputs]; exact depth_modAcceptExtCircuit_le m k' S
          have hd2 : C_in.depth ≤ 4 * (h'' + 1) :=
            (depth_comapOutputs_le _ _).trans (depth_appendCircuits_le Ci hCi_d)
          omega
        · simp only [C, Circuit.size_comp, C_out, Circuit.mapInputs_size, C_in,
            Circuit.comapOutputs_size, size_appendCircuits]
          have hs1 := size_modAcceptExtCircuit_le m k' S
          have hs2 : ∑ i : Fin k, (Ci i).size ≤ (m * (m + 3) + 2) * ∑ i : Fin k, sh i := by
            rw [Finset.mul_sum]; exact Finset.sum_le_sum fun i _ => hCi_s i
          have hsum_le : 1 + ∑ i : Fin k, sh i ≤ s' := by omega
          nlinarith
  refine mem_ACC0_iff.mpr ⟨m, hm2, ?_⟩
  rw [AC0Mod, ConstDepth.mem_iff]
  refine ⟨4 * h, fun n => (m * (m + 3) + 2) * s n, by fun_prop, fun n => ?_⟩
  exact hsim h n (s n) (L.slice n) (hL n)

end CslibFrontier.Computability.Circuit
