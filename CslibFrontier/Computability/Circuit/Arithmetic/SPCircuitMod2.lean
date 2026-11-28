/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.SPCircuit
public import CslibFrontier.Computability.Circuit.Boolean.Smolensky
public import CslibFrontier.Foundations.BooleanAnalysis.BooleanQuotient

/-!
# Gate-by-Gate Simulation of `SPCircuit (ZMod 2)` by Boolean `AC⁰[2]` Circuits

Over `ZMod 2`, every element is `0` or `1`, so every unbounded-fan-in arithmetic circuit
`C : SPCircuit (ZMod 2) n` translates gate-for-gate into a Boolean `AC⁰[2]` circuit
(`Circuit Unbounded.extSignature n 1`) of identical gate count `size` and depth at most `C.depth`
(`spCircuitToAC0Mod2`, `spCircuitToAC0Mod2_spec`). Combining this simulation with the
Razborov–Smolensky lower bound (`Smolensky.two_mul_two_pow_le_size_of_computes_modGate`) yields
exponential size lower bounds against constant-depth `SPCircuit (ZMod 2)` circuits computing
`MOD_p` for every odd prime `p` (`two_mul_two_pow_le_spCircuit_size_of_computes_modGate`).
-/

public section

namespace CslibFrontier.Computability.Circuit.Arithmetic

open Finset MvPolynomial
open Cslib Cslib.BitString Cslib.Circuits Cslib.Circuits.Arithmetic Cslib.Circuits.Boolean

/-- Translate a single `SPCircuit (ZMod 2)` gate line into an equivalent `AC⁰[2]` gate line. -/
noncomputable def lineToAC0Mod2 {n g : ℕ} (line : Line (sigmaPiSignature (ZMod 2)) n g) :
    Line Unbounded.extSignature n g :=
  match line with
  | ⟨.const a, _⟩ =>
    if a = 0 then ⟨.ac (.or 0), Fin.elim0⟩ else ⟨.ac (.and 0), Fin.elim0⟩
  | ⟨.mul m, wires⟩ =>
    ⟨.ac (.and m), wires⟩
  | ⟨.add m c, wires⟩ =>
    let act := univ.filter fun j : Fin m => c j ≠ 0
    ⟨.gate act.card, fun r => wires (act.equivFin.symm r)⟩

/-- Gate-by-gate translation of a program over `sigmaPiSignature (ZMod 2)` to `AC⁰[2]`. -/
noncomputable def progToAC0Mod2 {n : ℕ} :
    ∀ {g : ℕ}, Program (sigmaPiSignature (ZMod 2)) n g → Program Unbounded.extSignature n g
  | 0, .empty => .empty
  | _ + 1, .gate p line => .gate (progToAC0Mod2 p) (lineToAC0Mod2 line)

/-- Every `SPCircuit (ZMod 2) n` translates 1-to-1 to an `AC⁰[2]` circuit of equal `size` and depth
at most `C.depth`. -/
noncomputable def spCircuitToAC0Mod2 {n : ℕ} (C : SPCircuit (ZMod 2) n) :
    Circuit Unbounded.extSignature n 1 :=
  { size := C.size
    program := progToAC0Mod2 C.program
    outputs := C.outputs }

private theorem fin_foldl_max_le : ∀ (m B : ℕ) (f : Fin m → ℕ),
    (∀ k : Fin m, f k ≤ B) → Fin.foldl m (fun d k => max d (f k)) 0 ≤ B
  | 0, _, _, _ => Nat.zero_le _
  | m + 1, B, f, hf => by
      rw [Fin.foldl_succ_last]
      exact max_le (fin_foldl_max_le m B (f ∘ Fin.castSucc) fun k => hf k.castSucc)
        (hf (Fin.last m))

private theorem le_fin_foldl_max : ∀ (m : ℕ) (f : Fin m → ℕ) (t : Fin m),
    f t ≤ Fin.foldl m (fun d k => max d (f k)) 0
  | 0, _, t => t.elim0
  | m + 1, f, t => by
      rw [Fin.foldl_succ_last]
      induction t using Fin.lastCases with
      | last => exact le_max_right _ _
      | cast k => exact (le_fin_foldl_max m (f ∘ Fin.castSucc) k).trans (le_max_left _ _)

private theorem program_wireDepths_gate_last {σ : Signature.{0}} {n g : ℕ}
    (q : Program σ n g) (ln : Line σ n g) :
    (q.gate ln).wireDepths (.gate (Fin.last g)) = ln.depth q.wireDepths := by
  simp [Program.wireDepths, Program.depths]

private theorem program_trace_gate_last {σ : Signature.{0}} {U : Type} {n g : ℕ}
    (q : Program σ n g) (ln : Line σ n g) (interp : Interpretation σ U) (inp : Fin n → U) :
    (q.gate ln).trace interp inp (.gate (Fin.last g)) =
      interp ln.op (fun s => q.trace interp inp (ln.wires s)) := by
  simp [Program.trace, Line.eval, Function.comp_def]

theorem spCircuitToAC0Mod2_spec {n : ℕ} (C : SPCircuit (ZMod 2) n) :
    (spCircuitToAC0Mod2 C).size = C.size ∧
      (spCircuitToAC0Mod2 C).depth ≤ C.depth ∧
      ∀ x : BitString n,
        bitVal (ZMod 2)
            ((spCircuitToAC0Mod2 C).eval (Unbounded.extInterpretation (modGate 2)) x 0) =
          eval (bitPoint x) C.polynomial := by
  have hprog : ∀ {g : ℕ} (P : Program (sigmaPiSignature (ZMod 2)) n g),
      (∀ w : Wire n g, (progToAC0Mod2 P).wireDepths w ≤ P.wireDepths w) ∧
      (∀ (x : BitString n) (w : Wire n g),
        bitVal (ZMod 2)
            ((progToAC0Mod2 P).trace (Unbounded.extInterpretation (modGate 2)) x w) =
          P.trace (sigmaPiInterpretation (ZMod 2)) (bitPoint x) w) := by
    intro g P
    induction P with
    | empty =>
      refine ⟨fun w => ?_, fun x w => ?_⟩
      · cases w with | input _ => rfl | gate k => exact k.elim0
      · cases w with | input _ => rfl | gate k => exact k.elim0
    | @gate g p line ih =>
      obtain ⟨ih_dep, ih_tr⟩ := ih
      have hread_sub : ∀ s, ∃ t, (lineToAC0Mod2 line).wires s = line.wires t := by
        rcases line with ⟨op, wires⟩
        cases op with
        | const a =>
          intro s
          by_cases ha : a = 0
          · simp [lineToAC0Mod2, ha] at s; exact s.elim0
          · simp [lineToAC0Mod2, ha] at s; exact s.elim0
        | mul m => intro s; exact ⟨s, rfl⟩
        | add m c =>
          intro s
          exact ⟨((univ.filter fun j : Fin m => c j ≠ 0).equivFin.symm s).1, rfl⟩
      refine ⟨?_, ?_⟩
      · intro w
        cases w with
        | input _ => rfl
        | gate k =>
          induction k using Fin.lastCases with
          | last =>
            rw [progToAC0Mod2, program_wireDepths_gate_last, program_wireDepths_gate_last]
            unfold Line.depth
            refine Nat.succ_le_succ (fin_foldl_max_le _ _ _ fun s => ?_)
            obtain ⟨t, ht⟩ := hread_sub s
            rw [ht]
            exact (ih_dep (line.wires t)).trans
              (le_fin_foldl_max _ (fun k => p.wireDepths (line.wires k)) t)
          | cast k =>
            simpa [progToAC0Mod2, Program.wireDepths, Program.depths] using ih_dep (.gate k)
      · intro x w
        cases w with
        | input _ => rfl
        | gate k =>
          induction k using Fin.lastCases with
          | last =>
            rw [progToAC0Mod2, program_trace_gate_last, program_trace_gate_last]
            rcases line with ⟨op, wires⟩
            cases op with
            | const a =>
              have ha01 : a = 0 ∨ a = 1 := (by decide : ∀ z : ZMod 2, z = 0 ∨ z = 1) a
              rcases ha01 with rfl | rfl <;>
                simp [lineToAC0Mod2, Unbounded.extInterpretation, Unbounded.interpretation,
                  Unbounded.Op.arity, sigmaPiInterpretation, sigmaPiInterpretationWith, bitVal]
            | mul m =>
              simp_rw [← ih_tr x]
              simp only [lineToAC0Mod2, Unbounded.extInterpretation, Unbounded.interpretation,
                sigmaPiInterpretation, sigmaPiInterpretationWith]
              by_cases hall : ∀ j : Fin m,
                  (progToAC0Mod2 p).trace (Unbounded.extInterpretation (modGate 2)) x (wires j) =
                    true
              · simp [hall, bitVal, Unbounded.Op.arity]
              · have hall' : ¬ ∀ j : Fin (Unbounded.Op.and m).arity,
                    (progToAC0Mod2 p).trace (Unbounded.extInterpretation (modGate 2)) x (wires j) =
                      true := hall
                rw [decide_eq_false hall', bitVal_false]
                push Not at hall
                obtain ⟨j, hj⟩ := hall
                have hjf : (progToAC0Mod2 p).trace
                    (Unbounded.extInterpretation (modGate 2)) x (wires j) = false :=
                  Bool.eq_false_iff.mpr hj
                exact (prod_eq_zero (mem_univ j) (by rw [hjf, bitVal_false])).symm
            | add m c =>
              simp_rw [← ih_tr x]
              set act := univ.filter fun j : Fin m => c j ≠ 0
              simp only [lineToAC0Mod2, Unbounded.extInterpretation, modGate,
                sigmaPiInterpretation, sigmaPiInterpretationWith, id_eq]
              have hc1 : ∀ j ∈ act, c j = 1 := by
                intro j hj
                have hne : c j ≠ 0 := (mem_filter.mp hj).2
                rcases (by decide : ∀ z : ZMod 2, z = 0 ∨ z = 1) (c j) with h0 | h1
                · exact absurd h0 hne
                · exact h1
              set u := fun j : Fin m =>
                (progToAC0Mod2 p).trace (Unbounded.extInterpretation (modGate 2)) x (wires j)
              have hrhs :
                  (∑ j : Fin m, c j * bitVal (ZMod 2) (u j)) =
                    ((act.filter fun j => u j = true).card : ZMod 2) := by
                rw [← sum_filter_add_sum_filter_not univ (fun j : Fin m => c j ≠ 0)]
                have h0 : (∑ j ∈ univ.filter (fun j : Fin m => ¬ c j ≠ 0),
                    c j * bitVal (ZMod 2) (u j)) = 0 :=
                  sum_eq_zero fun j hj => by
                    have hcj0 : c j = 0 := not_not.mp (mem_filter.mp hj).2
                    rw [hcj0, zero_mul]
                rw [h0, add_zero]
                change (∑ j ∈ act, c j * bitVal (ZMod 2) (u j)) = _
                rw [sum_congr rfl fun j hj => by rw [hc1 j hj, one_mul]]
                rw [Finset.card_filter, Nat.cast_sum]
                exact sum_congr rfl fun j _ => by cases u j <;> simp [bitVal]
              change bitVal (ZMod 2)
                (decide ((univ.filter fun r : Fin act.card =>
                  u (act.equivFin.symm r) = true).card % 2 ≠ 0)) =
                ∑ j : Fin m, c j * bitVal (ZMod 2) (u j)
              rw [hrhs]
              have hcard_eq :
                  (univ.filter fun r : Fin act.card => u (act.equivFin.symm r) = true).card =
                    (act.filter fun j => u j = true).card := by
                refine card_bij (fun r _ => (act.equivFin.symm r).1)
                  (fun r hr => mem_filter.mpr ⟨(act.equivFin.symm r).2, (mem_filter.mp hr).2⟩)
                  (fun r₁ _ r₂ _ h => act.equivFin.symm.injective (Subtype.ext h))
                  (fun j hj => ⟨act.equivFin ⟨j, (mem_filter.mp hj).1⟩,
                    mem_filter.mpr ⟨mem_univ _, by simpa using (mem_filter.mp hj).2⟩, by simp⟩)
              rw [hcard_eq]
              have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
              have hmod := Smolensky.natCast_pow_eq_bitVal
                (R := ZMod 2) (p := 2) (act.filter fun j => u j = true).card
              simpa using hmod.symm
          | cast k =>
            simpa [progToAC0Mod2, Program.trace, Program.eval] using ih_tr x (.gate k)
  obtain ⟨hdep_w, htr_w⟩ := hprog C.program
  refine ⟨rfl, ?_, ?_⟩
  · simp only [spCircuitToAC0Mod2, Circuit.depth, Fin.foldl_succ_last, Fin.foldl_zero,
      Nat.zero_max, Circuit.outputDepths, Function.comp_apply]
    exact hdep_w (C.outputs 0)
  · intro x
    have htr := htr_w x (C.outputs 0)
    have heval_poly :
        eval (bitPoint x) C.polynomial =
          C.eval (sigmaPiInterpretation (ZMod 2)) (bitPoint x) 0 := by
      rw [← SPCircuit.polynomial_toFormula, SPFormula.eval_polynomial, Circuit.eval_toFormula]
    rw [heval_poly]
    exact htr

/-- **Razborov–Smolensky lower bound for `SPCircuit (ZMod 2)`**: for any odd prime `p ≠ 2`, an
unbounded-fan-in arithmetic circuit `C : SPCircuit (ZMod 2) n` agreeing with `modGate p n` on
`{0, 1}^n` satisfies `2 * 2 ^ ℓ ≤ 5 * (p - 1) * 2 ^ (p - 1) * C.size` whenever `1 ≤ ℓ` and
`100 * (ℓ ^ C.depth + 1) ^ 2 + (p - 1) ≤ n + 1`. -/
theorem two_mul_two_pow_le_spCircuit_size_of_computes_modGate {p n ℓ : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) {C : SPCircuit (ZMod 2) n}
    (hC : ∀ x : BitString n, eval (bitPoint x) C.polynomial = bitVal (ZMod 2) (modGate p n x))
    (hℓ : 1 ≤ ℓ) (hn : 100 * (ℓ ^ C.depth + 1) ^ 2 + (p - 1) ≤ n + 1) :
    2 * 2 ^ ℓ ≤ 5 * (p - 1) * 2 ^ (p - 1) * C.size := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hsz, hdep, hevalC⟩ := spCircuitToAC0Mod2_spec C
  have hcomp : (spCircuitToAC0Mod2 C).Computes
      (Unbounded.extInterpretation (modGate 2)) (single (modGate p n)) := by
    intro x
    funext o
    fin_cases o
    have hbit := (hevalC x).trans (hC x)
    cases h1 : (spCircuitToAC0Mod2 C).eval (Unbounded.extInterpretation (modGate 2)) x 0 <;>
      cases h2 : modGate p n x <;> simp [h1, h2, bitVal] at hbit ⊢
  have hn_bc :
      100 * (((2 - 1) * ℓ) ^ (spCircuitToAC0Mod2 C).depth + 1) ^ 2 + (p - 1) ≤ n + 1 := by
    simp only [Nat.reduceSub, one_mul]
    have hpow := Nat.pow_le_pow_right hℓ hdep
    have hsq := Nat.pow_le_pow_left (Nat.add_le_add_right hpow 1) 2
    omega
  have hsmol := Smolensky.two_mul_two_pow_le_size_of_computes_modGate hp2 hcomp hℓ hn_bc
  rwa [hsz] at hsmol

end CslibFrontier.Computability.Circuit.Arithmetic
