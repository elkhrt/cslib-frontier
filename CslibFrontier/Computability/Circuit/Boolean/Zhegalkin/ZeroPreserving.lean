/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FormalPapers Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Cslib.Computability.Circuit.Complexity
public import Cslib.Computability.Circuit.Simulation
public import CslibFrontier.Computability.Circuit.Boolean.Zhegalkin.Basis

/-!
# The Zero-Preserving Zhegalkin Boolean Basis `{⊕, ∧}` and Post's Clone `T₀`

Defines the constant-free algebraic Boolean circuit basis `{⊕, ∧}` (`ZeroPreserving.Op`,
`ZeroPreserving.signature`, `ZeroPreserving.interpretation`), proves that every wire and output
evaluates to `false` on the all-`false` input (`¬ interpretation.IsComplete`), and establishes the
necessary and sufficient Post-`T₀` / positive-Davio completeness criterion: a single-output Boolean
function `f : BooleanFunction n` is computable over `{⊕, ∧}` if and only if `0 < n` and
`f (fun _ => false) = false`.

## Main definitions

* `Cslib.Circuits.Boolean.Zhegalkin.ZeroPreserving.Op`,
  `Cslib.Circuits.Boolean.Zhegalkin.ZeroPreserving.signature`,
  `Cslib.Circuits.Boolean.Zhegalkin.ZeroPreserving.interpretation`: the constant-free Boolean
  basis `{⊕, ∧}`.
* `Cslib.Circuits.Boolean.Zhegalkin.ZeroPreserving.IsZeroPreserving`: Post's clone `T₀` predicate
  `f (fun _ => false) = false`.

## Main results

* `Cslib.Circuits.Boolean.Zhegalkin.ZeroPreserving.program_eval_false`,
  `circuit_eval_false`, `isZeroPreserving_of_computes`, `not_isComplete`: zero-preservation
  invariant and functional incompleteness of `{⊕, ∧}`.
* `Cslib.Circuits.Boolean.Zhegalkin.ZeroPreserving.isEmpty_circuit_zero`: emptiness of
  `Circuit signature 0 (m + 1)`.
* `Cslib.Circuits.Boolean.Zhegalkin.ZeroPreserving.synthesis_of_isZeroPreserving`,
  `exists_circuit_iff`, `ecomplexity_ne_top_iff`: positive-Davio synthesis (`≤ 4 * 2^n - 3` gates
  on `n + 1` variables) and exact computability characterization.
* `Cslib.Circuits.Boolean.Zhegalkin.ZeroPreserving.zhegalkin_simulatesWithCost`,
  `exists_circuit_size_ge`: unit-cost simulation by `{1, ⊕, ∧}` and arbitrarily large equivalent
  `{⊕, ∧}`-circuits.
-/

public section

namespace Cslib.Circuits.Boolean.Zhegalkin.ZeroPreserving

/-- Binary operations of the constant-free algebraic Boolean basis `{⊕, ∧}`. -/
inductive Op where
  /-- Binary exclusive-or `⊕` (addition in `GF(2)`). -/
  | xor
  /-- Binary conjunction `∧` (multiplication in `GF(2)`). -/
  | and
  deriving DecidableEq

/-- Finite enumeration of `Op`. -/
instance : Fintype Op :=
  ⟨{.xor, .and}, fun op => by cases op <;> simp⟩

/-- Signature of `{⊕, ∧}`, where both operations have arity `2`. -/
abbrev signature : Signature where
  Op := Op
  Arity
    | .xor | .and => 2

/-- Standard Boolean interpretation of `{⊕, ∧}` over `Bool`. -/
@[expose] def interpretation : Interpretation signature Bool
  | .xor, x => x 0 ^^ x 1
  | .and, x => x 0 && x 1

/-- Under `interpretation`, `.xor` evaluates to `x 0 ^^ x 1`. -/
@[simp] theorem interpretation_xor (x : Fin 2 → Bool) :
    interpretation .xor x = (x 0 ^^ x 1) := rfl

/-- Under `interpretation`, `.and` evaluates to `x 0 && x 1`. -/
@[simp] theorem interpretation_and (x : Fin 2 → Bool) :
    interpretation .and x = (x 0 && x 1) := rfl

/-- A Boolean function `f : BooleanFunction n` is zero-preserving (Post's clone `T₀`) if it maps
the all-`false` vector to `false`. -/
def IsZeroPreserving {n : ℕ} (f : BooleanFunction n) : Prop :=
  f (fun _ => false) = false

theorem isZeroPreserving_iff {n : ℕ} (f : BooleanFunction n) :
    IsZeroPreserving f ↔ f (fun _ => false) = false := Iff.rfl

instance {n : ℕ} (f : BooleanFunction n) : Decidable (IsZeroPreserving f) :=
  inferInstanceAs (Decidable (f (fun _ => false) = false))

/-- Every internal gate of a `{⊕, ∧}`-program evaluates to `false` on `fun _ => false`. -/
theorem program_eval_false {n g : ℕ} (p : Program signature n g) :
    p.eval interpretation (fun _ => false) = fun _ => false := by
  induction p with
  | empty =>
    funext i
    exact i.elim0
  | gate p line ih =>
    funext j
    refine Fin.lastCases ?_ ?_ j
    · rw [Program.eval_gate_last]
      have harg : ∀ k : Fin (signature.Arity line.op),
          Wire.elim (fun _ : Fin n => false) (p.eval interpretation (fun _ => false))
            (line.wires k) = false := by
        intro k
        rw [ih]
        cases line.wires k <;> rfl
      rcases line with ⟨op, wires⟩
      cases op <;> simp [Line.eval, harg]
    · intro i
      rw [Program.eval_gate_castSucc, ih]

/-- Every output of a `{⊕, ∧}`-circuit evaluates to `false` on `fun _ => false`. -/
theorem circuit_eval_false {n m : ℕ} (c : Circuit signature n m) :
    c.eval interpretation (fun _ => false) = fun _ => false := by
  funext k
  dsimp [Circuit.eval, Program.trace]
  rw [program_eval_false]
  cases c.outputs k <;> rfl

/-- Any Boolean function computed by a `{⊕, ∧}`-circuit is zero-preserving. -/
theorem isZeroPreserving_of_computes {n : ℕ} {f : BooleanFunction n} {c : Circuit signature n 1}
    (hc : c.Computes interpretation (single f)) :
    IsZeroPreserving f := by
  have h0 := congrFun (hc (fun _ => false)) 0
  rw [circuit_eval_false] at h0
  exact h0.symm

/-- On `0` inputs, every `{⊕, ∧}`-program has `0` gates because every operation has arity `2`. -/
theorem program_zero_gateCount_eq_zero {g : ℕ} (p : Program signature 0 g) : g = 0 := by
  induction p with
  | empty => rfl
  | gate q line ih =>
    subst ih
    have w := line.wires ⟨0, by cases line.op <;> decide⟩
    rcases w with ⟨i⟩ | ⟨j⟩
    · exact i.elim0
    · exact j.elim0

/-- There is no `{⊕, ∧}`-circuit with `0` inputs and `m + 1` outputs. -/
theorem isEmpty_circuit_zero (m : ℕ) : IsEmpty (Circuit signature 0 (m + 1)) := by
  refine ⟨fun c => ?_⟩
  have hz : c.size = 0 := program_zero_gateCount_eq_zero c.program
  have w : Wire 0 c.size := c.outputs 0
  rw [hz] at w
  rcases w with ⟨i⟩ | ⟨j⟩
  · exact i.elim0
  · exact j.elim0

/-- The constant-free basis `{⊕, ∧}` is not functionally complete over `Bool`. -/
theorem not_isComplete : ¬ interpretation.IsComplete := by
  intro hcomp
  obtain ⟨c, hc⟩ := hcomp.exists_computes_single (n := 1) (fun _ => true)
  have hz := isZeroPreserving_of_computes hc
  change true = false at hz
  exact Bool.noConfusion hz

private theorem synthesis_xor {n a b : ℕ} {s : Set (BooleanFunction n)}
    {f g : BooleanFunction n}
    (hf : Synthesis interpretation s {f} a) (hg : Synthesis interpretation s {g} b) :
    Synthesis interpretation s {fun x => f x ^^ g x} (a + b + 1) := by
  have h := Synthesis.binary hf hg Op.xor
  convert h using 2
  funext x
  simp [interpretation]

private theorem synthesis_and {n a b : ℕ} {s : Set (BooleanFunction n)}
    {f g : BooleanFunction n}
    (hf : Synthesis interpretation s {f} a) (hg : Synthesis interpretation s {g} b) :
    Synthesis interpretation s {fun x => f x && g x} (a + b + 1) := by
  have h := Synthesis.binary hf hg Op.and
  convert h using 2
  funext x
  simp [interpretation]

private theorem synthesis_restrict_castSucc {n cost : ℕ} {f : BooleanFunction n}
    (hf : Synthesis interpretation (inputs n) {f} cost) :
    Synthesis interpretation (inputs (n + 1)) {fun x : Fin (n + 1) → Bool => f (x ∘ Fin.castSucc)}
      cost := by
  obtain ⟨c, hc, hsize⟩ := hf.exists_circuit
  let c' : Circuit signature (n + 1) 1 := c.mapInputs Fin.castSucc
  have hc' : c'.Computes interpretation
      (single fun x : Fin (n + 1) → Bool => f (x ∘ Fin.castSucc)) := by
    intro x
    rw [Circuit.eval_mapInputs, hc (x ∘ Fin.castSucc)]
    rfl
  have havail : (fun x : Fin (n + 1) → Bool => f (x ∘ Fin.castSucc)) ∈
      available interpretation c'.program := by
    rw [mem_available]
    refine ⟨c'.outputs 0, fun x => ?_⟩
    exact congrFun (hc' x) 0
  have hprog : ∀ {g : ℕ} (p : Program signature (n + 1) g),
      Synthesis interpretation (inputs (n + 1)) (available interpretation p) g := by
    intro g p
    induction p with
    | empty =>
      refine Synthesis.of_subset (t := available interpretation .empty) ?_
      rintro _ ⟨w, rfl⟩
      rcases w with ⟨i⟩ | ⟨j⟩
      · exact ⟨i, rfl⟩
      · exact j.elim0
    | @gate g q line ih =>
      have hline : Synthesis interpretation (available interpretation q)
          {fun x => line.eval interpretation x (q.eval interpretation x)} 1 :=
        Synthesis.gate (I := interpretation) (s := available interpretation q) line.op
          (fun k x => q.trace interpretation x (line.wires k))
          (fun k => mem_available.mpr ⟨line.wires k, fun _ => rfl⟩)
      have hcomp := ih.comp (hline.mono Set.subset_union_right Set.Subset.rfl le_rfl)
      refine hcomp.mono Set.Subset.rfl ?_ le_rfl
      rintro _ ⟨w, rfl⟩
      rcases w with ⟨i⟩ | ⟨j⟩
      · exact Or.inl ⟨.input i, rfl⟩
      · refine Fin.lastCases ?_ ?_ j
        · refine Or.inr ?_
          ext x
          simp [Program.trace, Program.wireFunction]
        · intro j₀
          refine Or.inl (mem_available.mpr ⟨.gate j₀, fun x => ?_⟩)
          simp [Program.trace]
  have hsz : c'.size ≤ cost := by simpa [c', Circuit.mapInputs] using hsize
  exact (hprog c'.program).mono Set.Subset.rfl (Set.singleton_subset_iff.mpr havail) hsz

private theorem positive_davio_even (b u d : Bool) :
    (u ^^ (b && d)) = if b then (u ^^ d) else u := by
  cases b <;> cases u <;> cases d <;> rfl

private theorem positive_davio_odd (b u g : Bool) :
    (u ^^ (b ^^ (b && g))) = if b then (u ^^ !g) else u := by
  cases b <;> cases u <;> cases g <;> rfl

/-- Positive-Davio synthesis theorem: every zero-preserving Boolean function on `n + 1` variables
can be synthesized over `{⊕, ∧}` using at most `4 * 2 ^ n - 3` gates. -/
theorem synthesis_of_isZeroPreserving :
    ∀ {n : ℕ} {f : BooleanFunction (n + 1)},
      IsZeroPreserving f →
        Synthesis interpretation (inputs (n + 1)) {f} (4 * 2 ^ n - 3)
  | 0, f, hf => by
    rw [isZeroPreserving_iff] at hf
    have hx0 : (fun x : Fin 1 → Bool => x 0) ∈ (inputs 1 : Set (BooleanFunction 1)) := ⟨0, rfl⟩
    by_cases h1 : f (fun _ => true) = true
    · have hfeq : f = fun x : Fin 1 → Bool => x 0 := by
        funext x
        have hx : x = (fun _ => x 0) := by
          funext i
          exact congrArg x (Fin.ext (by omega))
        rw [hx]
        cases x 0
        · exact hf
        · exact h1
      rw [hfeq]
      exact (Synthesis.of_mem hx0).mono Set.Subset.rfl Set.Subset.rfl (by omega)
    · have h1f : f (fun _ => true) = false := Bool.eq_false_iff.mpr h1
      have hfeq : f = fun x : Fin 1 → Bool => (x 0 ^^ x 0) := by
        funext x
        have hx : x = (fun _ => x 0) := by
          funext i
          exact congrArg x (Fin.ext (by omega))
        rw [hx]
        cases x 0
        · simpa using hf
        · simpa using h1f
      rw [hfeq]
      have h0 := synthesis_xor (Synthesis.of_mem hx0) (Synthesis.of_mem hx0)
      exact h0.mono Set.Subset.rfl Set.Subset.rfl (by omega)
  | n + 1, f, hf => by
    rw [isZeroPreserving_iff] at hf
    let f₀ : BooleanFunction (n + 1) := fun y => f (Fin.snoc y false)
    let f₁ : BooleanFunction (n + 1) := fun y => f (Fin.snoc y true)
    have hf₀ : IsZeroPreserving f₀ := by
      rw [isZeroPreserving_iff]
      dsimp [f₀]
      have hsnoc : Fin.snoc (fun _ : Fin (n + 1) => false) false = fun _ => false := by
        funext i
        exact Fin.lastCases (by simp) (fun _ => by simp) i
      rw [hsnoc]
      exact hf
    have ih₀ := synthesis_restrict_castSucc (synthesis_of_isZeroPreserving hf₀)
    have hlast : (fun x : Fin (n + 2) → Bool => x (Fin.last (n + 1))) ∈
        (inputs (n + 2) : Set (BooleanFunction (n + 2))) := ⟨Fin.last (n + 1), rfl⟩
    let d : BooleanFunction (n + 1) := fun y => f₀ y ^^ f₁ y
    by_cases hd0 : d (fun _ => false) = false
    · have hdzp : IsZeroPreserving d := (isZeroPreserving_iff d).mpr hd0
      have ihd := synthesis_restrict_castSucc (synthesis_of_isZeroPreserving hdzp)
      have hand := synthesis_and (Synthesis.of_mem hlast) ihd
      have htot := synthesis_xor ih₀ hand
      have hfeq : (fun x : Fin (n + 2) → Bool =>
          f₀ (x ∘ Fin.castSucc) ^^ (x (Fin.last (n + 1)) && d (x ∘ Fin.castSucc))) = f := by
        funext x
        rw [positive_davio_even]
        dsimp [f₀, f₁, d]
        cases hxl : x (Fin.last (n + 1))
        · have hx : Fin.snoc (x ∘ Fin.castSucc) false = x := by
            rw [← hxl]; exact Fin.snoc_init_self x
          rw [hx]; rfl
        · have hxor : ∀ a b : Bool, (a ^^ (a ^^ b)) = b := by
            intro a b; cases a <;> cases b <;> rfl
          rw [hxor]
          have hx : Fin.snoc (x ∘ Fin.castSucc) true = x := by
            rw [← hxl]; exact Fin.snoc_init_self x
          rw [hx]; rfl
      rw [hfeq] at htot
      refine htot.mono Set.Subset.rfl Set.Subset.rfl ?_
      have hpow : 1 ≤ 2 ^ n := Nat.one_le_two_pow
      rw [Nat.pow_succ]
      omega
    · have hd1 : d (fun _ => false) = true := by
        cases h : d (fun _ => false)
        · exact False.elim (hd0 h)
        · rfl
      let g : BooleanFunction (n + 1) := fun y => !d y
      have hg0 : IsZeroPreserving g := by
        rw [isZeroPreserving_iff]
        dsimp [g]
        rw [hd1]; rfl
      have ihg := synthesis_restrict_castSucc (synthesis_of_isZeroPreserving hg0)
      have hand := synthesis_and (Synthesis.of_mem hlast) ihg
      have hbx := synthesis_xor (Synthesis.of_mem hlast) hand
      have htot := synthesis_xor ih₀ hbx
      have hfeq : (fun x : Fin (n + 2) → Bool =>
          f₀ (x ∘ Fin.castSucc) ^^
            (x (Fin.last (n + 1)) ^^ (x (Fin.last (n + 1)) && g (x ∘ Fin.castSucc)))) = f := by
        funext x
        rw [positive_davio_odd]
        dsimp [f₀, f₁, d, g]
        cases hxl : x (Fin.last (n + 1))
        · have hx : Fin.snoc (x ∘ Fin.castSucc) false = x := by
            rw [← hxl]; exact Fin.snoc_init_self x
          rw [hx]; rfl
        · have hxor : ∀ a b : Bool, (a ^^ !!(a ^^ b)) = b := by
            intro a b; cases a <;> cases b <;> rfl
          rw [hxor]
          have hx : Fin.snoc (x ∘ Fin.castSucc) true = x := by
            rw [← hxl]; exact Fin.snoc_init_self x
          rw [hx]; rfl
      rw [hfeq] at htot
      refine htot.mono Set.Subset.rfl Set.Subset.rfl ?_
      have hpow : 1 ≤ 2 ^ n := Nat.one_le_two_pow
      rw [Nat.pow_succ]
      omega

/-- Necessary and sufficient characterization of `n`-ary Boolean functions computable by a
single-output circuit over `{⊕, ∧}`. -/
theorem exists_circuit_iff {n : ℕ} (f : BooleanFunction n) :
    (∃ c : Circuit signature n 1, c.Computes interpretation (single f)) ↔
      0 < n ∧ IsZeroPreserving f := by
  constructor
  · rintro ⟨c, hc⟩
    cases n with
    | zero => exact False.elim ((isEmpty_circuit_zero 0).false c)
    | succ m => exact ⟨Nat.succ_pos m, isZeroPreserving_of_computes hc⟩
  · rintro ⟨hn, hf⟩
    cases n with
    | zero => omega
    | succ m =>
      obtain ⟨c, hc, _⟩ := (synthesis_of_isZeroPreserving hf).exists_circuit
      exact ⟨c, hc⟩

/-- Extended circuit complexity over `{⊕, ∧}` is finite if and only if `0 < n` and `f` is
zero-preserving. -/
theorem ecomplexity_ne_top_iff {n : ℕ} (f : BooleanFunction n) :
    ecomplexity interpretation (single f) ≠ ⊤ ↔ 0 < n ∧ IsZeroPreserving f := by
  rw [Cslib.Circuits.ecomplexity_ne_top_iff]
  exact exists_circuit_iff f

/-- The full Zhegalkin basis `{1, ⊕, ∧}` simulates `{⊕, ∧}` with unit gate cost. -/
theorem zhegalkin_simulatesWithCost :
    Cslib.Circuits.Boolean.Zhegalkin.interpretation.SimulatesWithCost
      interpretation (fun _ => 1) := by
  intro op
  cases op
  · let p : Program Cslib.Circuits.Boolean.Zhegalkin.signature 2 1 :=
      Program.empty.gate ⟨.xor, fun i => .input i⟩
    refine ⟨⟨p, fun _ => .gate 0⟩, ?_, le_rfl⟩
    intro x
    funext k
    rw [Subsingleton.elim k 0]
    rfl
  · let p : Program Cslib.Circuits.Boolean.Zhegalkin.signature 2 1 :=
      Program.empty.gate ⟨.and, fun i => .input i⟩
    refine ⟨⟨p, fun _ => .gate 0⟩, ?_, le_rfl⟩
    intro x
    funext k
    rw [Subsingleton.elim k 0]
    rfl

/-- Every `{⊕, ∧}`-computable Boolean function admits `{⊕, ∧}`-circuits of arbitrarily large gate
count. -/
theorem exists_circuit_size_ge {n : ℕ} {f : BooleanFunction n} (hn : 0 < n)
    (hf : IsZeroPreserving f) (m : ℕ) :
    ∃ c : Circuit signature n 1, c.Computes interpretation (single f) ∧ m ≤ c.size := by
  obtain ⟨c₀, hc₀⟩ := (exists_circuit_iff f).mpr ⟨hn, hf⟩
  induction m with
  | zero => exact ⟨c₀, hc₀, Nat.zero_le _⟩
  | succ m ih =>
    obtain ⟨c, hc, hm⟩ := ih
    let c' : Circuit signature n 1 :=
      { size := c.size + 1
        program := c.program.gate ⟨.and, fun _ => c.outputs 0⟩
        outputs := fun _ => .gate (Fin.last c.size) }
    refine ⟨c', ?_, by dsimp [c']; omega⟩
    intro x
    funext k
    rw [Subsingleton.elim k 0]
    have hval : c.eval interpretation x 0 = f x := congrFun (hc x) 0
    have htrace : Wire.elim x (c.program.eval interpretation x) (c.outputs 0) = f x := hval
    simp [c', Circuit.eval, Program.trace, Line.eval, htrace]

end Cslib.Circuits.Boolean.Zhegalkin.ZeroPreserving
