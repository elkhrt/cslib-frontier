module

public import Cslib.Computability.Circuit.Boolean.Basic
public import CslibFrontier.Computability.Circuit.Boolean.Encoding
public import CslibFrontier.Computability.Circuit.Boolean.EvaluationTime
public import CslibFrontier.Computability.Circuit.Boolean.PPoly
public import CslibFrontier.Computability.Circuit.Boolean.Substitution
public import CslibFrontier.Computability.Circuit.Frontier.Nondeterministic
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime
public import Mathlib.Computability.Language
public import Mathlib.Order.Filter.AtTopBot.Defs
import CslibFrontier.Computability.Circuit.Boolean.CodeComposition
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeNatFrontends
import Mathlib.Data.Fin.VecNotation

/-!
# Nondeterministic and Co-Nondeterministic Boolean Circuits, Uniformity, and Refuters

This module develops the textbook theory of nondeterministic and co-nondeterministic Boolean
circuits (`NSIZE`, `coNSIZE`, `i.o.-coNSIZE`), `P`-uniform circuit families
(`PUniformNSIZE`, `PUniformCoNSIZE`), complementation dualities, truth-table synthesis,
input-ignoring/hardwiring gadgets, and complexity-theoretic refuters on top of
`Cslib.Circuits.Circuit` (`Boolean.signature`).

## Main definitions

* `CslibFrontier.Computability.Circuit.WitnessCircuit`: a De Morgan Boolean circuit on `n`
  primary inputs and `witnessLen` auxiliary witness inputs.
* `CslibFrontier.Computability.Circuit.WitnessCircuit.NondetAccepts`,
  `CslibFrontier.Computability.Circuit.WitnessCircuit.CoNondetAccepts`: nondeterministic
  (`∃ y`) and co-nondeterministic (`∀ y`) acceptance semantics.
* `CslibFrontier.Computability.Circuit.NSIZE`, `CslibFrontier.Computability.Circuit.coNSIZE`,
  `CslibFrontier.Computability.Circuit.ioCoNSIZE`: nonuniform nondeterministic and
  co-nondeterministic circuit size classes.
* `CslibFrontier.Computability.Circuit.PUniformNSIZE`,
  `CslibFrontier.Computability.Circuit.PUniformCoNSIZE`: `P`-uniform nondeterministic and
  co-nondeterministic circuit size classes.
* `CslibFrontier.Computability.Circuit.IsUniformRefuter`,
  `CslibFrontier.Computability.Circuit.IsNonuniformRefuter`: uniform and nonuniform refuters.

## Main results

* `CslibFrontier.Computability.Circuit.compl_mem_NSIZE_of_mem_coNSIZE`,
  `CslibFrontier.Computability.Circuit.compl_mem_coNSIZE_of_mem_NSIZE`:
  complementation duality for `NSIZE` and `coNSIZE` (up to the `+1` negation gate).
* `CslibFrontier.Computability.Circuit.compl_mem_PUniformNSIZE_of_mem_PUniformCoNSIZE`,
  `CslibFrontier.Computability.Circuit.compl_mem_PUniformCoNSIZE_of_mem_PUniformNSIZE`:
  complementation duality for `P`-uniform nondeterministic circuit classes.
* `CslibFrontier.Computability.Circuit.SIZE_subset_NSIZE`,
  `CslibFrontier.Computability.Circuit.SIZE_subset_coNSIZE`: deterministic circuits are both
  nondeterministic and co-nondeterministic.
* `CslibFrontier.Computability.Circuit.exists_muxTree_circuit`: every Boolean function on `n`
  bits has a De Morgan circuit of size at most `5 * 2 ^ n`.
-/

public section

namespace CslibFrontier.Computability.Circuit

open Cslib.Circuits Cslib.Circuits.Boolean Turing.MultiTapeTM Filter

/-! ### Witness Circuits (`NSIZE` / `coNSIZE`) -/

/-- A Boolean circuit on `n` primary inputs and `witnessLen` auxiliary witness inputs
(used for both nondeterministic and co-nondeterministic evaluation). -/
@[ext]
structure WitnessCircuit (n : ℕ) where
  /-- Number of auxiliary (nondeterministic or co-nondeterministic) witness input bits. -/
  witnessLen : ℕ
  /-- Underlying De Morgan Boolean circuit on `n + witnessLen` inputs and `1` output. -/
  circuit : Circuit Boolean.signature (n + witnessLen) 1

namespace WitnessCircuit

/-- Effective size of a witness circuit, bounding both its gate count and witness arity. -/
@[expose] def size {n : ℕ} (c : WitnessCircuit n) : ℕ :=
  max c.circuit.size c.witnessLen

/-- Nondeterministic acceptance: `∃ y`, `c(x, y) = true`. -/
@[expose] def NondetAccepts {n : ℕ} (c : WitnessCircuit n) (x : Fin n → Bool) : Prop :=
  ∃ y : Fin c.witnessLen → Bool,
    c.circuit.eval Boolean.interpretation (Fin.append x y) 0 = true

/-- Co-nondeterministic acceptance: `∀ y`, `c(x, y) = true`. -/
@[expose] def CoNondetAccepts {n : ℕ} (c : WitnessCircuit n) (x : Fin n → Bool) : Prop :=
  ∀ y : Fin c.witnessLen → Bool,
    c.circuit.eval Boolean.interpretation (Fin.append x y) 0 = true

theorem nondetAccepts_iff_nondeterministicDecides {n : ℕ} (c : WitnessCircuit n)
    (S : Set (Fin n → Bool)) :
    (∀ x, x ∈ S ↔ c.NondetAccepts x) ↔
      c.circuit.NondeterministicDecides Boolean.interpretation {true} S := by
  simp [Circuit.NondeterministicDecides, NondetAccepts]

/-- View a deterministic Boolean circuit as a witness circuit with `0` witness bits. -/
def ofDeterministic {n : ℕ} (d : Circuit Boolean.signature n 1) : WitnessCircuit n where
  witnessLen := 0
  circuit := d.mapInputs (Fin.cast (Nat.add_zero n).symm)

@[simp]
theorem size_ofDeterministic {n : ℕ} (d : Circuit Boolean.signature n 1) :
    (ofDeterministic d).size = d.size := by
  simp [size, ofDeterministic]

theorem nondetAccepts_ofDeterministic {n : ℕ} (d : Circuit Boolean.signature n 1)
    (x : Fin n → Bool) :
    (ofDeterministic d).NondetAccepts x ↔ d.eval Boolean.interpretation x 0 = true := by
  simp only [NondetAccepts, ofDeterministic, Circuit.eval_mapInputs]
  constructor
  · rintro ⟨y, hy⟩
    have hfun : Fin.append x y ∘ Fin.cast (Nat.add_zero n).symm = x := by
      funext i
      exact Fin.append_left x y i
    rwa [hfun] at hy
  · intro hx
    refine ⟨Fin.elim0, ?_⟩
    have hfun : Fin.append x Fin.elim0 ∘ Fin.cast (Nat.add_zero n).symm = x := by
      funext i
      exact Fin.append_left x Fin.elim0 i
    rwa [hfun]

theorem coNondetAccepts_ofDeterministic {n : ℕ} (d : Circuit Boolean.signature n 1)
    (x : Fin n → Bool) :
    (ofDeterministic d).CoNondetAccepts x ↔ d.eval Boolean.interpretation x 0 = true := by
  simp only [CoNondetAccepts, ofDeterministic, Circuit.eval_mapInputs]
  constructor
  · intro h
    have hfun : Fin.append x Fin.elim0 ∘ Fin.cast (Nat.add_zero n).symm = x := by
      funext i
      exact Fin.append_left x Fin.elim0 i
    simpa [hfun] using h Fin.elim0
  · intro hx y
    have hfun : Fin.append x y ∘ Fin.cast (Nat.add_zero n).symm = x := by
      funext i
      exact Fin.append_left x y i
    rwa [hfun]

/-- Negate the output wire of a witness circuit by composing with a single NOT gate. -/
@[expose] def negate {n : ℕ} (c : WitnessCircuit n) : WitnessCircuit n where
  witnessLen := c.witnessLen
  circuit := (Circuit.oneGate (σ := Boolean.signature) Boolean.Op.not (fun _ => 0)).comp c.circuit

@[simp]
theorem witnessLen_negate {n : ℕ} (c : WitnessCircuit n) :
    c.negate.witnessLen = c.witnessLen := rfl

theorem size_negate_le {n : ℕ} (c : WitnessCircuit n) :
    c.negate.size ≤ c.size + 1 := by
  simp only [size, negate, Circuit.size_comp, Circuit.size_oneGate]
  omega

/-- Semantic characterization of `WitnessCircuit.size`. -/
theorem coNondetAccepts_iff {n : ℕ} (c : WitnessCircuit n) (x : Fin n → Bool) :
    c.CoNondetAccepts x ↔ ∀ y : Fin c.witnessLen → Bool,
      c.circuit.eval Boolean.interpretation (Fin.append x y) 0 = true := Iff.rfl

theorem size_eq {n : ℕ} (c : WitnessCircuit n) :
    c.size = max c.circuit.size c.witnessLen := rfl

theorem eval_negate {n : ℕ} (c : WitnessCircuit n) (z : Fin (n + c.witnessLen) → Bool) :
    c.negate.circuit.eval Boolean.interpretation z 0 =
      !(c.circuit.eval Boolean.interpretation z 0) := by
  simp only [negate, Circuit.eval_comp, Circuit.eval_oneGate]
  rfl

theorem coNondetAccepts_negate {n : ℕ} (c : WitnessCircuit n) (x : Fin n → Bool) :
    c.negate.CoNondetAccepts x ↔ ¬ c.NondetAccepts x := by
  rcases c with ⟨w, c⟩
  simp only [CoNondetAccepts, NondetAccepts, not_exists]
  refine forall_congr' fun y => ?_
  have hev : (WitnessCircuit.mk w c).negate.circuit.eval Boolean.interpretation (Fin.append x y) 0 =
      !(c.eval Boolean.interpretation (Fin.append x y) 0) := eval_negate ⟨w, c⟩ (Fin.append x y)
  rw [hev]
  cases c.eval Boolean.interpretation (Fin.append x y) 0 <;> simp

theorem nondetAccepts_negate {n : ℕ} (c : WitnessCircuit n) (x : Fin n → Bool) :
    c.negate.NondetAccepts x ↔ ¬ c.CoNondetAccepts x := by
  rcases c with ⟨w, c⟩
  simp only [CoNondetAccepts, NondetAccepts, not_forall]
  refine exists_congr fun y => ?_
  have hev : (WitnessCircuit.mk w c).negate.circuit.eval Boolean.interpretation (Fin.append x y) 0 =
      !(c.eval Boolean.interpretation (Fin.append x y) 0) := eval_negate ⟨w, c⟩ (Fin.append x y)
  rw [hev]
  cases c.eval Boolean.interpretation (Fin.append x y) 0 <;> simp

/-- Hardwire primary input `x` into `c` and ignore a new primary input of length `m`,
preserving the witness input string. -/
@[expose] def hardwireAndIgnore {n : ℕ} (c : WitnessCircuit n) (x : Fin n → Bool) (m : ℕ) :
    WitnessCircuit m where
  witnessLen := c.witnessLen
  circuit :=
    c.circuit.comp
      (substituteCircuit (fun j : Fin (n + c.witnessLen) =>
        Fin.addCases (fun i => Sum.inr (x i))
          (fun k => Sum.inl (Fin.natAdd m k)) j))

theorem size_hardwireAndIgnore_le {n : ℕ} (c : WitnessCircuit n) (x : Fin n → Bool) (m : ℕ) :
    (c.hardwireAndIgnore x m).size ≤ c.size + 2 := by
  simp only [size, hardwireAndIgnore, Circuit.size_comp, size_substituteCircuit]
  omega

theorem coNondetAccepts_hardwireAndIgnore {n : ℕ} (c : WitnessCircuit n)
    (x : Fin n → Bool) (m : ℕ) (u : Fin m → Bool) :
    (c.hardwireAndIgnore x m).CoNondetAccepts u ↔ c.CoNondetAccepts x := by
  simp only [CoNondetAccepts, hardwireAndIgnore, Circuit.eval_comp, eval_substituteCircuit]
  refine forall_congr' fun y => ?_
  have hsub :
      substitute (fun j : Fin (n + c.witnessLen) =>
        Fin.addCases (fun i => Sum.inr (x i))
          (fun k => Sum.inl (Fin.natAdd m k)) j) (Fin.append u y) =
      Fin.append x y := by
    funext j
    refine Fin.addCases (fun i => ?_) (fun k => ?_) j
    · simp [substitute, Fin.append_left]
    · simp [substitute, Fin.append_right]
  rw [hsub]

/-- Binary encoding of a witness circuit of arbitrary primary arity `n`:
`encPair encUnary (encCircuit 1)` storing `(n, ⟨n + witnessLen, circuit⟩)`. -/
@[expose] def encWitnessCircuit : (Σ n, WitnessCircuit n) ↪ List Bool :=
  ⟨fun c => encPair encUnary (encCircuit 1) (c.1, ⟨c.1 + c.2.witnessLen, c.2.circuit⟩), by
    rintro ⟨n₁, ⟨w₁, c₁⟩⟩ ⟨n₂, ⟨w₂, c₂⟩⟩ hab
    have hp := (encPair encUnary (encCircuit 1)).injective hab
    have h1 : n₁ = n₂ := congrArg Prod.fst hp
    subst h1
    have h2 : (⟨n₁ + w₁, c₁⟩ : Σ m, Circuit Boolean.signature m 1) = ⟨n₁ + w₂, c₂⟩ :=
      congrArg Prod.snd hp
    have hw : w₁ = w₂ := by
      have := congrArg Sigma.fst h2
      dsimp at this; omega
    subst hw
    have hc : c₁ = c₂ := eq_of_heq (Sigma.mk.inj_iff.mp h2).2
    subst hc; rfl⟩

/-- Semantic characterization of `WitnessCircuit.hardwireAndIgnore` witness length. -/
@[simp] theorem hardwireAndIgnore_witnessLen {n : ℕ} (c : WitnessCircuit n)
    (x : Fin n → Bool) (m : ℕ) : (c.hardwireAndIgnore x m).witnessLen = c.witnessLen := rfl

/-- Semantic characterization of `WitnessCircuit.hardwireAndIgnore` underlying circuit. -/
theorem hardwireAndIgnore_circuit_eq {n : ℕ} (c : WitnessCircuit n) (x : Fin n → Bool) (m : ℕ) :
    (c.hardwireAndIgnore x m).circuit =
      c.circuit.comp (substituteCircuit (Fin.addCases (fun i => Sum.inr (x i))
        (fun k => Sum.inl (Fin.natAdd m k)))) := rfl

/-- Semantic characterization of `WitnessCircuit.encWitnessCircuit`. -/
theorem encWitnessCircuit_apply (c : Σ n, WitnessCircuit n) :
    WitnessCircuit.encWitnessCircuit c =
      encPair encUnary (encCircuit 1) (c.1, ⟨c.1 + c.2.witnessLen, c.2.circuit⟩) := rfl

end WitnessCircuit

/-! ### Circuit Size Complexity Classes (`NSIZE`, `coNSIZE`, `PUniform`) -/

/-- Languages decidable by nondeterministic Boolean circuits of size at most `s n`. -/
def NSIZE (s : ℕ → ℕ) : Set (Language Bool) :=
  {L | ∀ n, ∃ c : WitnessCircuit n, c.size ≤ s n ∧
    ∀ x : Fin n → Bool, List.ofFn x ∈ L ↔ c.NondetAccepts x}

/-- Languages decidable by co-nondeterministic Boolean circuits of size at most `s n`. -/
def coNSIZE (s : ℕ → ℕ) : Set (Language Bool) :=
  {L | ∀ n, ∃ c : WitnessCircuit n, c.size ≤ s n ∧
    ∀ x : Fin n → Bool, List.ofFn x ∈ L ↔ c.CoNondetAccepts x}

/-- Languages decidable infinitely often by co-nondeterministic Boolean circuits of size `s n`. -/
def ioCoNSIZE (s : ℕ → ℕ) : Set (Language Bool) :=
  {L | ∃ᶠ n in atTop, ∃ c : WitnessCircuit n, c.size ≤ s n ∧
    ∀ x : Fin n → Bool, List.ofFn x ∈ L ↔ c.CoNondetAccepts x}

/-- Languages decidable by a `P`-uniform family of nondeterministic circuits of size `s n`. -/
@[expose] def PUniformNSIZE (s : ℕ → ℕ) : Set (Language Bool) :=
  {L | ∃ (gen : ℕ → Σ n, WitnessCircuit n) (hgen : ∀ n, (gen n).1 = n),
    ComputableInPolyTime gen encUnary WitnessCircuit.encWitnessCircuit ∧
    (∀ n, (gen n).2.size ≤ s n) ∧
    (∀ n (x : Fin n → Bool),
      List.ofFn x ∈ L ↔ (gen n).2.NondetAccepts (x ∘ Fin.cast (hgen n)))}

/-- Languages decidable by a `P`-uniform family of co-nondeterministic circuits of size `s n`. -/
@[expose] def PUniformCoNSIZE (s : ℕ → ℕ) : Set (Language Bool) :=
  {L | ∃ (gen : ℕ → Σ n, WitnessCircuit n) (hgen : ∀ n, (gen n).1 = n),
    ComputableInPolyTime gen encUnary WitnessCircuit.encWitnessCircuit ∧
    (∀ n, (gen n).2.size ≤ s n) ∧
    (∀ n (x : Fin n → Bool),
      List.ofFn x ∈ L ↔ (gen n).2.CoNondetAccepts (x ∘ Fin.cast (hgen n)))}

theorem NSIZE_mono {s₁ s₂ : ℕ → ℕ} (h : ∀ n, s₁ n ≤ s₂ n) : NSIZE s₁ ⊆ NSIZE s₂ :=
  fun _ hL n => let ⟨c, hc, hdec⟩ := hL n; ⟨c, hc.trans (h n), hdec⟩

theorem coNSIZE_mono {s₁ s₂ : ℕ → ℕ} (h : ∀ n, s₁ n ≤ s₂ n) : coNSIZE s₁ ⊆ coNSIZE s₂ :=
  fun _ hL n => let ⟨c, hc, hdec⟩ := hL n; ⟨c, hc.trans (h n), hdec⟩

theorem SIZE_subset_NSIZE (s : ℕ → ℕ) : Boolean.SIZE s ⊆ NSIZE s := by
  intro L hL n
  obtain ⟨c, hcomp, hsize⟩ :=
    exists_computes_size_eq_complexity (I := Boolean.interpretation) (f := single (L.slice n))
  refine ⟨WitnessCircuit.ofDeterministic c, ?_, fun x => ?_⟩
  · simpa [hsize] using hL n
  · rw [WitnessCircuit.nondetAccepts_ofDeterministic]
    have hslice := congrFun (hcomp x) 0
    rw [hslice]
    simp [Language.slice]

theorem SIZE_subset_coNSIZE (s : ℕ → ℕ) : Boolean.SIZE s ⊆ coNSIZE s := by
  intro L hL n
  obtain ⟨c, hcomp, hsize⟩ :=
    exists_computes_size_eq_complexity (I := Boolean.interpretation) (f := single (L.slice n))
  refine ⟨WitnessCircuit.ofDeterministic c, ?_, fun x => ?_⟩
  · simpa [hsize] using hL n
  · rw [WitnessCircuit.coNondetAccepts_ofDeterministic]
    have hslice := congrFun (hcomp x) 0
    rw [hslice]
    simp [Language.slice]

theorem compl_mem_NSIZE_of_mem_coNSIZE {L : Language Bool} {s : ℕ → ℕ}
    (hL : L ∈ coNSIZE s) : Lᶜ ∈ NSIZE (fun n => s n + 1) := by
  intro n
  obtain ⟨c, hc, hdec⟩ := hL n
  refine ⟨c.negate, (c.size_negate_le).trans (Nat.add_le_add_right hc 1), fun x => ?_⟩
  rw [WitnessCircuit.nondetAccepts_negate, ← hdec x]
  rfl

theorem compl_mem_coNSIZE_of_mem_NSIZE {L : Language Bool} {s : ℕ → ℕ}
    (hL : L ∈ NSIZE s) : Lᶜ ∈ coNSIZE (fun n => s n + 1) := by
  intro n
  obtain ⟨c, hc, hdec⟩ := hL n
  refine ⟨c.negate, (c.size_negate_le).trans (Nat.add_le_add_right hc 1), fun x => ?_⟩
  rw [WitnessCircuit.coNondetAccepts_negate, ← hdec x]
  rfl

/-- Negating every circuit in a `P`-uniform family preserves polynomial-time uniformity. -/
theorem computableInPolyTime_negate {α : Type} {enc : α ↪ List Bool}
    {gen : α → Σ n, WitnessCircuit n}
    (hgen : ComputableInPolyTime gen enc WitnessCircuit.encWitnessCircuit) :
    ComputableInPolyTime (fun a => ⟨(gen a).1, (gen a).2.negate⟩)
      enc WitnessCircuit.encWitnessCircuit := by
  let notGate : Circuit Boolean.signature 1 1 :=
    Circuit.oneGate (σ := Boolean.signature) Boolean.Op.not (fun _ => 0)
  let unpack : (Σ n, WitnessCircuit n) → ℕ × (ℕ × Cslib.Complexity.CircuitCode) :=
    fun p => (p.1, (p.1 + p.2.witnessLen, p.2.circuit.code))
  have hunpack : ComputableInPolyTime unpack WitnessCircuit.encWitnessCircuit
      (encPair encUnary (encPair encUnary encCode)) :=
    (ComputableInPolyTime.id' (encIn := WitnessCircuit.encWitnessCircuit)).of_enc_eq fun p => by
      dsimp only [unpack, WitnessCircuit.encWitnessCircuit]
      simp [encCircuit_apply]
  have hcur := hunpack.comp hgen
  have h1 : ComputableInPolyTime (fun a => (gen a).1) enc encUnary :=
    (ComputableInPolyTime.fst _ _).comp hcur
  have h2 : ComputableInPolyTime (fun a => (gen a).1 + (gen a).2.witnessLen) enc encUnary :=
    ((ComputableInPolyTime.fst _ _).comp ((ComputableInPolyTime.snd _ _).comp hcur))
  have h2nat : ComputableInPolyTime (fun a => (gen a).1 + (gen a).2.witnessLen) enc encNat :=
    ComputableInPolyTime.unary_to_binary.comp h2
  have hcode : ComputableInPolyTime (fun a => (gen a).2.circuit.code) enc encCode :=
    (ComputableInPolyTime.snd _ _).comp ((ComputableInPolyTime.snd _ _).comp hcur)
  have hcomp : ComputableInPolyTime
      (fun a => Boolean.compCode ((gen a).1 + (gen a).2.witnessLen) notGate.code
        (gen a).2.circuit.code) enc encCode :=
    Boolean.computableInPolyTime_compCode h2nat (ComputableInPolyTime.const _) hcode
  have hpack : ComputableInPolyTime
      (fun a => ((gen a).1, ((gen a).1 + (gen a).2.witnessLen,
        Boolean.compCode ((gen a).1 + (gen a).2.witnessLen) notGate.code
          (gen a).2.circuit.code)))
      enc (encPair encUnary (encPair encUnary encCode)) :=
    h1.prod (h2.prod hcomp)
  refine hpack.of_enc_eq fun a => ?_
  dsimp only [WitnessCircuit.encWitnessCircuit, WitnessCircuit.negate, notGate]
  simp only [encPair_apply, encCircuit_apply, Boolean.compCode_code]
  rfl

theorem compl_mem_PUniformNSIZE_of_mem_PUniformCoNSIZE {L : Language Bool} {s : ℕ → ℕ}
    (hL : L ∈ PUniformCoNSIZE s) : Lᶜ ∈ PUniformNSIZE (fun n => s n + 1) := by
  obtain ⟨gen, hgen, hpoly, hsize, hdec⟩ := hL
  refine ⟨fun n => ⟨(gen n).1, (gen n).2.negate⟩, hgen,
    computableInPolyTime_negate hpoly,
    fun n => ((gen n).2.size_negate_le).trans (Nat.add_le_add_right (hsize n) 1),
    fun n x => ?_⟩
  rw [WitnessCircuit.nondetAccepts_negate, ← hdec n x]
  rfl

theorem compl_mem_PUniformCoNSIZE_of_mem_PUniformNSIZE {L : Language Bool} {s : ℕ → ℕ}
    (hL : L ∈ PUniformNSIZE s) : Lᶜ ∈ PUniformCoNSIZE (fun n => s n + 1) := by
  obtain ⟨gen, hgen, hpoly, hsize, hdec⟩ := hL
  refine ⟨fun n => ⟨(gen n).1, (gen n).2.negate⟩, hgen,
    computableInPolyTime_negate hpoly,
    fun n => ((gen n).2.size_negate_le).trans (Nat.add_le_add_right (hsize n) 1),
    fun n x => ?_⟩
  rw [WitnessCircuit.coNondetAccepts_negate, ← hdec n x]
  rfl

/-! ### Truth-Table Circuit Synthesis (`≤ 5 * 2 ^ n`) -/

/-- Constant Boolean circuit on `n` inputs with `1` gate. -/
private def constCircuit (n : ℕ) (b : Bool) : Circuit Boolean.signature n 1 :=
  Circuit.oneGate (.const b) Fin.elim0

private lemma eval_constCircuit (n : ℕ) (b : Bool) (x : Fin n → Bool) :
    (constCircuit n b).eval Boolean.interpretation x 0 = b := by
  simp only [constCircuit, Circuit.eval_oneGate]
  rfl

/-- One-bit multiplexer circuit `if sel then t else f` on 3 inputs (`sel, t, f`), size `4`. -/
private def muxGadget : Circuit Boolean.signature 3 1 :=
  -- wire 0 = sel, wire 1 = t, wire 2 = f
  -- gate 0 (wire 3): ¬sel
  -- gate 1 (wire 4): sel ∧ t
  -- gate 2 (wire 5): ¬sel ∧ f
  -- gate 3 (wire 6): (sel ∧ t) ∨ (¬sel ∧ f)
  let p0 : Program Boolean.signature 3 0 := .empty
  let p1 : Program Boolean.signature 3 1 := p0.gate ⟨.not, fun _ => .input 0⟩
  let p2 : Program Boolean.signature 3 2 :=
    p1.gate ⟨.and, ![.input 0, .input 1]⟩
  let p3 : Program Boolean.signature 3 3 :=
    p2.gate ⟨.and, ![.gate ⟨0, by omega⟩, .input 2]⟩
  let p4 : Program Boolean.signature 3 4 :=
    p3.gate ⟨.or, ![.gate ⟨1, by omega⟩, .gate ⟨2, by omega⟩]⟩
  ⟨p4, fun _ => .gate ⟨3, by omega⟩⟩

private lemma eval_muxGadget (z : Fin 3 → Bool) :
    muxGadget.eval Boolean.interpretation z 0 = if z 0 then z 1 else z 2 := by
  have h : muxGadget.eval Boolean.interpretation z 0 =
      ((z 0 && z 1) || (!z 0 && z 2)) := rfl
  rw [h]
  cases z 0 <;> simp

private lemma exists_muxTree_circuit_aux :
    ∀ (n : ℕ) (f : (Fin n → Bool) → Bool),
      ∃ c : Circuit Boolean.signature n 1,
        c.size ≤ 5 * 2 ^ n - 4 ∧ ∀ x, c.eval Boolean.interpretation x 0 = f x
  | 0, f => by
    refine ⟨constCircuit 0 (f Fin.elim0), by simp [constCircuit], fun x => ?_⟩
    rw [eval_constCircuit, Subsingleton.elim x Fin.elim0]
  | n + 1, f => by
    obtain ⟨c0, hs0, he0⟩ := exists_muxTree_circuit_aux n (fun x => f (Fin.cons false x))
    obtain ⟨c1, hs1, he1⟩ := exists_muxTree_circuit_aux n (fun x => f (Fin.cons true x))
    let sel : Circuit Boolean.signature (n + 1) 1 := Circuit.wiring _ (fun _ => 0)
    let c1' : Circuit Boolean.signature (n + 1) 1 := c1.mapInputs Fin.succ
    let c0' : Circuit Boolean.signature (n + 1) 1 := c0.mapInputs Fin.succ
    let bundle : Circuit Boolean.signature (n + 1) 3 :=
      Circuit.pi ![sel, c1', c0']
    let c : Circuit Boolean.signature (n + 1) 1 := muxGadget.comp bundle
    refine ⟨c, ?_, fun x => ?_⟩
    · have hsize : c.size = c1.size + c0.size + 4 := by
        simp [c, bundle, muxGadget, sel, c1', c0', Circuit.size_comp, Circuit.size_pi,
          Fin.sum_univ_three]
      have hpow : 1 ≤ 2 ^ n := Nat.one_le_two_pow
      rw [hsize, pow_succ]
      omega
    · simp only [c, bundle, sel, c1', c0', Circuit.eval_comp, eval_muxGadget,
        Circuit.eval_pi, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
        Circuit.eval_wiring, Circuit.eval_mapInputs, Function.comp_apply]
      have htail : x ∘ Fin.succ = Fin.tail x := rfl
      rw [htail, he1, he0]
      cases hx : x 0 with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        congr 1; funext i; refine Fin.cases hx.symm (fun _ => rfl) i
      | true =>
        simp only [↓reduceIte]
        congr 1; funext i; refine Fin.cases hx.symm (fun _ => rfl) i

/-- Every Boolean function on `n` inputs has a deterministic De Morgan circuit of size
at most `5 * 2 ^ n` (constructed recursively by a binary multiplexer tree). -/
theorem exists_muxTree_circuit (n : ℕ) (f : (Fin n → Bool) → Bool) :
    ∃ c : Circuit Boolean.signature n 1,
      c.size ≤ 5 * 2 ^ n ∧ ∀ x, c.eval Boolean.interpretation x 0 = f x := by
  obtain ⟨c, hs, he⟩ := exists_muxTree_circuit_aux n f
  exact ⟨c, hs.trans (Nat.sub_le _ _), he⟩

/-! ### Complexity-Theoretic Refuters -/

/-- A uniform refuter `R(n, code)` for a language `L` against co-nondeterministic circuits
of size at most `s n` succeeding from input length `n₀` onwards. -/
def IsUniformRefuter (L : Language Bool) (s : ℕ → ℕ)
    (R : ℕ × (Σ m, WitnessCircuit m) → List Bool) (n₀ : ℕ) : Prop :=
  ∀ n ≥ n₀, ∀ c : WitnessCircuit n, c.size ≤ s n →
    let w := R (n, ⟨n, c⟩)
    w.length = n ∧ ((w ∈ L) ↔ ¬ c.CoNondetAccepts (fun i => w.getD i.val false))

/-- A nonuniform refuter family of deterministic circuits of size at most `r n` for `L`
against co-nondeterministic circuits of size at most `s n` (given under a fixed-length
encoding of size-`s n` witness circuits). -/
def IsNonuniformRefuter (L : Language Bool) (s r : ℕ → ℕ) (n₀ : ℕ)
    (codeLen : ℕ → ℕ) (encode : ∀ n, WitnessCircuit n → Fin (codeLen n) → Bool) : Prop :=
  ∀ n ≥ n₀, ∃ R : Circuit Boolean.signature (codeLen n) n,
    R.size ≤ r n ∧
    ∀ c : WitnessCircuit n, c.size ≤ s n →
      let w := R.eval Boolean.interpretation (encode n c)
      (List.ofFn w ∈ L) ↔ ¬ c.CoNondetAccepts w

end CslibFrontier.Computability.Circuit
