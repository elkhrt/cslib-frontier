module

public import CslibFrontier.Computability.Circuit.Monotone.Basic
public import CslibFrontier.Computability.Circuit.MapOp
public import CslibFrontier.Computability.Circuit.Encoding.Basic
import CslibFrontier.Computability.Circuit.Encoding.Evaluation
import CslibFrontier.Computability.Circuit.Monotone.Formula
import Mathlib.Data.List.GetD

/-!
# Unbounded-fan-in monotone circuits

This module defines the unbounded-fan-in monotone circuit basis whose gates are `m`-ary conjunction
(`Op.and m`, with `Op.and 0` evaluating to `true`) and `m`-ary disjunction (`Op.or m`, with
`Op.or 0` evaluating to `false`), proves monotonicity of every program and circuit over both the
unbounded-fan-in and binary monotone bases, constructs a semantics-preserving signature homomorphism
`binaryToUnbounded` from `Cslib.Circuits.Monotone.signature`, characterizes the Boolean functions
computable by unbounded-fan-in monotone circuits as exactly the monotone Boolean functions, and
simulates every multi-output unbounded-fan-in monotone circuit by an equivalent binary monotone
circuit with size bounded by the sum of `max 1` of each gate's fan-in.

## Main definitions

* `CslibFrontier.Computability.Circuit.Monotone.Unbounded.Op`: `m`-ary conjunction and disjunction
  operations.
* `CslibFrontier.Computability.Circuit.Monotone.Unbounded.signature`: the unbounded-fan-in monotone
  circuit signature.
* `CslibFrontier.Computability.Circuit.Monotone.Unbounded.interpretation`: Boolean semantics of
  `signature`.
* `CslibFrontier.Computability.Circuit.Monotone.Unbounded.binaryToUnbounded`: semantics-preserving
  signature homomorphism from `Cslib.Circuits.Monotone.signature` into `signature`.

## Main results

* `CslibFrontier.Computability.Circuit.Monotone.Unbounded.interpretation_mono`: every operation in
  the unbounded-fan-in monotone basis is monotone.
* `CslibFrontier.Computability.Circuit.Monotone.Unbounded.monotone_eval_circuit`: every
  single-output unbounded-fan-in monotone circuit computes a monotone Boolean function.
* `CslibFrontier.Computability.Circuit.Monotone.Unbounded.monotone_eval_binary_circuit`: every
  single-output binary monotone circuit computes a monotone Boolean function.
* `CslibFrontier.Computability.Circuit.Monotone.Unbounded.exists_computes_iff_monotone`: a Boolean
  function is computed by an unbounded-fan-in monotone circuit iff it is monotone.
* `CslibFrontier.Computability.Circuit.Monotone.Unbounded.exists_binary_of_unbounded`: every
  multi-output unbounded-fan-in monotone circuit is equivalent to a binary monotone circuit of size
  at most the sum of `max 1 (arity g)` over its gates `g`.
-/

public section

namespace CslibFrontier.Computability.Circuit.Monotone.Unbounded

open Cslib Cslib.Circuits

/-- Operations of the unbounded-fan-in monotone basis: `m`-ary conjunction and disjunction for any
arity `m : ℕ` (with `and 0 = true` and `or 0 = false`). -/
inductive Op where
  /-- Conjunction of `m` Boolean arguments (`m = 0` is constant `true`). -/
  | and (m : ℕ)
  /-- Disjunction of `m` Boolean arguments (`m = 0` is constant `false`). -/
  | or (m : ℕ)
  deriving DecidableEq

/-- Arity of an unbounded-fan-in monotone operation. -/
abbrev Op.arity : Op → ℕ
  | .and m => m
  | .or m => m

/-- The unbounded-fan-in monotone circuit signature. -/
abbrev signature : Signature := ⟨Op, Op.arity⟩

/-- Boolean semantics of the unbounded-fan-in monotone basis. -/
@[expose] def interpretation : Interpretation signature Bool
  | .and _, x => decide (∀ j, x j = true)
  | .or _, x => decide (∃ j, x j = true)

/-- Evaluating an `m`-ary conjunction gate. -/
@[simp] theorem interpretation_and (m : ℕ) (x : Fin m → Bool) :
    interpretation (.and m) x = decide (∀ j, x j = true) := rfl

/-- Evaluating an `m`-ary disjunction gate. -/
@[simp] theorem interpretation_or (m : ℕ) (x : Fin m → Bool) :
    interpretation (.or m) x = decide (∃ j, x j = true) := rfl

/-- Every operation in the unbounded-fan-in monotone basis is monotone. -/
theorem interpretation_mono (op : Op) {x y : Fin (signature.Arity op) → Bool}
    (h : ∀ i, x i ≤ y i) : interpretation op x ≤ interpretation op y := by
  cases op with
  | and m =>
    rw [interpretation_and, interpretation_and, Bool.le_iff_imp, decide_eq_true_eq,
      decide_eq_true_eq]
    intro hx j
    exact Bool.eq_true_of_true_le (hx j ▸ h j)
  | or m =>
    rw [interpretation_or, interpretation_or, Bool.le_iff_imp, decide_eq_true_eq,
      decide_eq_true_eq]
    rintro ⟨j, hj⟩
    exact ⟨j, Bool.eq_true_of_true_le (hj ▸ h j)⟩

/-- Every program over `signature` evaluates monotonically in its input bits. -/
theorem monotone_eval_program {n g : ℕ} (p : Program signature n g) :
    Monotone (p.eval interpretation) := by
  induction p with
  | empty => intro _ _ _ j; exact Fin.elim0 j
  | gate p line ih =>
    intro x y hxy j
    refine Fin.lastCases ?_ (fun k ↦ ?_) j
    · simp only [Program.eval_gate_last, Line.eval]
      refine interpretation_mono line.op fun a ↦ ?_
      simp only [Function.comp_apply]
      cases line.wires a with
      | input i => exact hxy i
      | gate k => exact ih hxy k
    · simp only [Program.eval_gate_castSucc]
      exact ih hxy k

/-- Every single-output circuit over `signature` computes a monotone Boolean function. -/
theorem monotone_eval_circuit {n : ℕ} (C : Circuit signature n 1) :
    Monotone fun x ↦ C.eval interpretation x 0 := by
  intro x y hxy
  unfold Circuit.eval Program.trace
  simp only [Function.comp_apply]
  cases C.outputs 0 with
  | input i => exact hxy i
  | gate j => exact monotone_eval_program C.program hxy j

/-- Embedding the binary monotone basis `Cslib.Circuits.Monotone.signature` into `signature`. -/
@[expose] def binaryToUnbounded : Monotone.signature.Hom signature where
  toFun
    | .const true => .and 0
    | .const false => .or 0
    | .and => .and 2
    | .or => .or 2
  arity_eq op := by rcases op with (_ | _) | _ | _ <;> rfl

/-- `binaryToUnbounded` preserves Boolean semantics. -/
instance instPreservesBinaryToUnbounded :
    binaryToUnbounded.Preserves Monotone.interpretation interpretation where
  interpret_eq op x := by
    rcases op with (_ | _) | _ | _
    · exact decide_eq_false fun ⟨j, _⟩ ↦ j.elim0
    · exact decide_eq_true fun j ↦ j.elim0
    · change decide (∀ j : Fin 2, x j = true) = (x 0 && x 1)
      rw [Bool.eq_iff_iff, decide_eq_true_eq, Fin.forall_fin_two, Bool.and_eq_true]
    · change decide (∃ j : Fin 2, x j = true) = (x 0 || x 1)
      rw [Bool.eq_iff_iff, decide_eq_true_eq, Fin.exists_fin_two, Bool.or_eq_true]

/-- Mapping a binary monotone circuit along `binaryToUnbounded` preserves evaluation. -/
theorem eval_mapOp_binaryToUnbounded {n m : ℕ} (C : Circuit Monotone.signature n m)
    (x : BitString n) :
    (C.mapOp binaryToUnbounded).eval interpretation x = C.eval Monotone.interpretation x :=
  Circuit.eval_mapOp (I := Monotone.interpretation) C x

/-- Every single-output binary monotone circuit computes a monotone Boolean function. -/
theorem monotone_eval_binary_circuit {n : ℕ} (C : Circuit Monotone.signature n 1) :
    Monotone fun x ↦ C.eval Monotone.interpretation x 0 := by
  intro x y hxy
  have hx := congrFun (eval_mapOp_binaryToUnbounded C x) 0
  have hy := congrFun (eval_mapOp_binaryToUnbounded C y) 0
  dsimp only
  rw [← hx, ← hy]
  exact monotone_eval_circuit (C.mapOp binaryToUnbounded) hxy

/-- A Boolean function is computed by an unbounded-fan-in monotone circuit iff it is monotone. -/
theorem exists_computes_iff_monotone {n : ℕ} (f : BooleanFunction n) :
    (∃ C : Circuit signature n 1, C.Computes interpretation (single f)) ↔ Monotone f := by
  constructor
  · rintro ⟨C, hC⟩ x y hxy
    have hx := congrFun (hC x) 0
    have hy := congrFun (hC y) 0
    simp only [single_apply] at hx hy
    rw [← hx, ← hy]
    exact monotone_eval_circuit C hxy
  · intro hf
    obtain ⟨F, hF⟩ := Monotone.exists_computes_of_monotone hf
    refine ⟨F.toCircuit.mapOp binaryToUnbounded, fun x ↦ ?_⟩
    rw [eval_mapOp_binaryToUnbounded]
    funext j
    fin_cases j
    simpa only [Formula.eval_toCircuit, single_apply] using hF x

/-! ### Simulation of Unbounded-Fan-In Monotone Circuits by Binary Monotone Circuits -/

section ToBinary

private def emitBinaryFoldAux (numInputs : ℕ) (op : Monotone.Op) :
    ℕ → List ℕ → List (Monotone.Op × List ℕ) → ℕ × List (Monotone.Op × List ℕ)
  | acc, [], gates => (acc, gates)
  | acc, w :: ws, gates =>
    let idx := numInputs + gates.length
    emitBinaryFoldAux numInputs op idx ws (gates ++ [(op, [acc, w])])

private def emitBinaryFold (numInputs : ℕ) (op : Monotone.Op) (emptyVal : Bool) :
    List ℕ → List (Monotone.Op × List ℕ) → ℕ × List (Monotone.Op × List ℕ)
  | [], gates => (numInputs + gates.length, gates ++ [(.const emptyVal, [])])
  | w :: ws, gates => emitBinaryFoldAux numInputs op w ws gates

private def compileGates (numInputs : ℕ) :
    List (Op × List ℕ) → List ℕ → List (Monotone.Op × List ℕ) →
    List ℕ × List (Monotone.Op × List ℕ)
  | [], wireMap, gates => (wireMap, gates)
  | (op, args) :: rest, wireMap, gates =>
    let mapped := args.map fun i ↦ wireMap.getD i 0
    let (outW, gates₁) := match op with
      | .and _ => emitBinaryFold numInputs .and true mapped gates
      | .or _ => emitBinaryFold numInputs .or false mapped gates
    compileGates numInputs rest (wireMap ++ [outW]) gates₁

private theorem getD_evalCode_of_prefix {n : ℕ} (x : List Bool) (hx : x.length = n)
    {g₁ g₂ : List (Monotone.Op × List ℕ)} (hpre : g₁ <+: g₂)
    {u : ℕ} (hu : u < n + g₁.length) :
    (evalCode Monotone.interpretation false x g₂).getD u false =
      (evalCode Monotone.interpretation false x g₁).getD u false := by
  obtain ⟨t, rfl⟩ := hpre
  have hlt : u < (evalCode Monotone.interpretation false x g₁).length := by
    rw [length_evalCode, hx]; exact hu
  rw [evalCode_append, getD_evalCode_of_lt _ _ _ _ hlt]

private theorem isCodeFrom_append_const {n : ℕ} {gates : List (Monotone.Op × List ℕ)}
    (hg : Program.IsCodeFrom Monotone.signature n 0 gates) (b : Bool) :
    Program.IsCodeFrom Monotone.signature n 0 (gates ++ [(.const b, [])]) := by
  rw [Program.isCodeFrom_append]
  exact ⟨hg, ⟨rfl, fun _ h ↦ nomatch h⟩, trivial⟩

private theorem isCodeFrom_append_binary {n : ℕ} {gates : List (Monotone.Op × List ℕ)}
    (hg : Program.IsCodeFrom Monotone.signature n 0 gates)
    {op : Monotone.Op} (har : Monotone.signature.Arity op = 2)
    {w₁ w₂ : ℕ} (h₁ : w₁ < n + gates.length) (h₂ : w₂ < n + gates.length) :
    Program.IsCodeFrom Monotone.signature n 0 (gates ++ [(op, [w₁, w₂])]) := by
  rw [Program.isCodeFrom_append]
  refine ⟨hg, ⟨har.symm, ?_⟩, trivial⟩
  intro i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl <;> simpa

private theorem emitBinaryFoldAux_and_spec (numInputs acc : ℕ) (ws : List ℕ)
    (gates : List (Monotone.Op × List ℕ))
    (hg : Program.IsCodeFrom Monotone.signature numInputs 0 gates)
    (hacc : acc < numInputs + gates.length)
    (hws : ∀ w ∈ ws, w < numInputs + gates.length) :
    let res := emitBinaryFoldAux numInputs .and acc ws gates
    Program.IsCodeFrom Monotone.signature numInputs 0 res.2 ∧
    gates <+: res.2 ∧
    res.2.length = gates.length + ws.length ∧
    res.1 < numInputs + res.2.length ∧
    ∀ (x : List Bool), x.length = numInputs →
      (evalCode Monotone.interpretation false x res.2).getD res.1 false =
        ((evalCode Monotone.interpretation false x gates).getD acc false &&
          decide (∀ w ∈ ws, (evalCode Monotone.interpretation false x gates).getD w false =
            true)) := by
  induction ws generalizing acc gates with
  | nil =>
    refine ⟨hg, List.prefix_refl _, by simp [emitBinaryFoldAux], hacc, fun x _ ↦ ?_⟩
    simp [emitBinaryFoldAux]
  | cons w ws ih =>
    have hw : w < numInputs + gates.length := hws w (List.mem_cons_self ..)
    set idx := numInputs + gates.length
    set gates₁ := gates ++ [(.and, [acc, w])]
    have hg₁ : Program.IsCodeFrom Monotone.signature numInputs 0 gates₁ :=
      isCodeFrom_append_binary hg rfl hacc hw
    have hlen₁ : gates₁.length = gates.length + 1 := by simp [gates₁]
    have hidx : idx < numInputs + gates₁.length := by omega
    have hws₁ : ∀ u ∈ ws, u < numInputs + gates₁.length := fun u hu ↦
      lt_trans (hws u (List.mem_cons_of_mem _ hu)) (by omega)
    obtain ⟨hg₂, hpre₂, hlen₂, hout, hev₂⟩ := ih idx gates₁ hg₁ hidx hws₁
    dsimp only [emitBinaryFoldAux]
    refine ⟨hg₂, (List.prefix_append _ _).trans hpre₂, ?_, hout, fun x hx ↦ ?_⟩
    · change (emitBinaryFoldAux numInputs _ idx ws gates₁).2.length = _
      rw [hlen₂, hlen₁]
      simp only [List.length_cons]
      omega
    · rw [hev₂ x hx]
      have hlv : (evalCode Monotone.interpretation false x gates).length = idx := by
        rw [length_evalCode, hx]
      have hidx_ev : (evalCode Monotone.interpretation false x gates₁).getD idx false =
          ((evalCode Monotone.interpretation false x gates).getD acc false &&
            (evalCode Monotone.interpretation false x gates).getD w false) := by
        rw [show gates₁ = gates ++ [(.and, [acc, w])] from rfl, evalCode_append_singleton]
        change (evalCode Monotone.interpretation false x gates ++
          [(evalCode Monotone.interpretation false x gates).getD acc false &&
            (evalCode Monotone.interpretation false x gates).getD w false]).getD idx false = _
        rw [← hlv, List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self, List.getD_cons_zero]
      rw [hidx_ev, Bool.and_assoc]
      congr 1
      rw [Bool.eq_iff_iff, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
      constructor
      · rintro ⟨hw_t, hrest⟩ u hu
        rcases List.mem_cons.mp hu with rfl | hu'
        · exact hw_t
        · have hu_ev := getD_evalCode_of_prefix x hx (List.prefix_append gates [(.and, [acc, w])])
            (hws u (List.mem_cons_of_mem _ hu'))
          rw [← hu_ev]; exact hrest u hu'
      · intro hall
        refine ⟨hall w (List.mem_cons_self ..), fun u hu' ↦ ?_⟩
        rw [getD_evalCode_of_prefix x hx (List.prefix_append gates _)
          (hws u (List.mem_cons_of_mem _ hu'))]
        exact hall u (List.mem_cons_of_mem _ hu')

private theorem emitBinaryFoldAux_or_spec (numInputs acc : ℕ) (ws : List ℕ)
    (gates : List (Monotone.Op × List ℕ))
    (hg : Program.IsCodeFrom Monotone.signature numInputs 0 gates)
    (hacc : acc < numInputs + gates.length)
    (hws : ∀ w ∈ ws, w < numInputs + gates.length) :
    let res := emitBinaryFoldAux numInputs .or acc ws gates
    Program.IsCodeFrom Monotone.signature numInputs 0 res.2 ∧
    gates <+: res.2 ∧
    res.2.length = gates.length + ws.length ∧
    res.1 < numInputs + res.2.length ∧
    ∀ (x : List Bool), x.length = numInputs →
      (evalCode Monotone.interpretation false x res.2).getD res.1 false =
        ((evalCode Monotone.interpretation false x gates).getD acc false ||
          decide (∃ w ∈ ws, (evalCode Monotone.interpretation false x gates).getD w false =
            true)) := by
  induction ws generalizing acc gates with
  | nil =>
    refine ⟨hg, List.prefix_refl _, by simp [emitBinaryFoldAux], hacc, fun x _ ↦ ?_⟩
    simp [emitBinaryFoldAux]
  | cons w ws ih =>
    have hw : w < numInputs + gates.length := hws w (List.mem_cons_self ..)
    set idx := numInputs + gates.length
    set gates₁ := gates ++ [(.or, [acc, w])]
    have hg₁ : Program.IsCodeFrom Monotone.signature numInputs 0 gates₁ :=
      isCodeFrom_append_binary hg rfl hacc hw
    have hlen₁ : gates₁.length = gates.length + 1 := by simp [gates₁]
    have hidx : idx < numInputs + gates₁.length := by omega
    have hws₁ : ∀ u ∈ ws, u < numInputs + gates₁.length := fun u hu ↦
      lt_trans (hws u (List.mem_cons_of_mem _ hu)) (by omega)
    obtain ⟨hg₂, hpre₂, hlen₂, hout, hev₂⟩ := ih idx gates₁ hg₁ hidx hws₁
    dsimp only [emitBinaryFoldAux]
    refine ⟨hg₂, (List.prefix_append _ _).trans hpre₂, ?_, hout, fun x hx ↦ ?_⟩
    · change (emitBinaryFoldAux numInputs _ idx ws gates₁).2.length = _
      rw [hlen₂, hlen₁]
      simp only [List.length_cons]
      omega
    · rw [hev₂ x hx]
      have hlv : (evalCode Monotone.interpretation false x gates).length = idx := by
        rw [length_evalCode, hx]
      have hidx_ev : (evalCode Monotone.interpretation false x gates₁).getD idx false =
          ((evalCode Monotone.interpretation false x gates).getD acc false ||
            (evalCode Monotone.interpretation false x gates).getD w false) := by
        rw [show gates₁ = gates ++ [(.or, [acc, w])] from rfl, evalCode_append_singleton]
        change (evalCode Monotone.interpretation false x gates ++
          [(evalCode Monotone.interpretation false x gates).getD acc false ||
            (evalCode Monotone.interpretation false x gates).getD w false]).getD idx false = _
        rw [← hlv, List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self, List.getD_cons_zero]
      rw [hidx_ev, Bool.or_assoc]
      congr 1
      rw [Bool.eq_iff_iff, Bool.or_eq_true, decide_eq_true_eq, decide_eq_true_eq]
      constructor
      · rintro (hw_t | ⟨u, hu', hu_t⟩)
        · exact ⟨w, List.mem_cons_self .., hw_t⟩
        · rw [getD_evalCode_of_prefix x hx (List.prefix_append gates _)
            (hws u (List.mem_cons_of_mem _ hu'))] at hu_t
          exact ⟨u, List.mem_cons_of_mem _ hu', hu_t⟩
      · rintro ⟨u, hu, hu_t⟩
        rcases List.mem_cons.mp hu with rfl | hu'
        · exact Or.inl hu_t
        · right
          refine ⟨u, hu', ?_⟩
          rwa [getD_evalCode_of_prefix x hx (List.prefix_append gates _)
            (hws u (List.mem_cons_of_mem _ hu'))]

private theorem compileGates_spec (numInputs : ℕ) (src : List (Op × List ℕ))
    (wireMap : List ℕ) (gates : List (Monotone.Op × List ℕ))
    (prev : List (Op × List ℕ))
    (hsrc : Program.IsCodeFrom signature numInputs prev.length src)
    (hwm_len : wireMap.length = numInputs + prev.length)
    (hg : Program.IsCodeFrom Monotone.signature numInputs 0 gates)
    (hwm_lt : ∀ u ∈ wireMap, u < numInputs + gates.length)
    (hwm_ev : ∀ (x : List Bool), x.length = numInputs →
      ∀ (i : ℕ), i < wireMap.length →
        (evalCode Monotone.interpretation false x gates).getD (wireMap.getD i 0) false =
          (evalCode interpretation false x prev).getD i false) :
    let res := compileGates numInputs src wireMap gates
    Program.IsCodeFrom Monotone.signature numInputs 0 res.2 ∧
    gates <+: res.2 ∧
    res.2.length ≤ gates.length + (src.map fun g ↦ max 1 g.2.length).sum ∧
    res.1.length = wireMap.length + src.length ∧
    (∀ u ∈ res.1, u < numInputs + res.2.length) ∧
    ∀ (x : List Bool), x.length = numInputs →
      ∀ (i : ℕ), i < res.1.length →
        (evalCode Monotone.interpretation false x res.2).getD (res.1.getD i 0) false =
          (evalCode interpretation false x (prev ++ src)).getD i false := by
  induction src generalizing wireMap gates prev with
  | nil =>
    refine ⟨hg, List.prefix_refl _, by simp [compileGates], by simp [compileGates], hwm_lt,
      fun x hx i hi ↦ ?_⟩
    simpa [compileGates] using hwm_ev x hx i hi
  | cons g rest ih =>
    rcases g with ⟨op, args⟩
    obtain ⟨⟨har, hargs⟩, hrest⟩ := (Program.isCodeFrom_cons ..).mp hsrc
    dsimp only at har hargs
    set mapped := args.map fun i ↦ wireMap.getD i 0
    have hmap_lt : ∀ w ∈ mapped, w < numInputs + gates.length := by
      intro w hw
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hw
      have hjlt : j < wireMap.length := by have := hargs j hj; omega
      exact hwm_lt _ (by rw [List.getD_eq_getElem _ _ hjlt]; exact List.getElem_mem hjlt)
    have hstep :
        let p := match op with
          | .and _ => emitBinaryFold numInputs .and true mapped gates
          | .or _ => emitBinaryFold numInputs .or false mapped gates
        Program.IsCodeFrom Monotone.signature numInputs 0 p.2 ∧
        gates <+: p.2 ∧
        p.2.length ≤ gates.length + max 1 args.length ∧
        p.1 < numInputs + p.2.length ∧
        ∀ (x : List Bool), x.length = numInputs →
          (evalCode Monotone.interpretation false x p.2).getD p.1 false =
            interpretation op (fun a : Fin (signature.Arity op) ↦
              (evalCode interpretation false x prev).getD (args.getD a.1 0) false) := by
      cases op with
      | and m =>
        dsimp only
        cases hmap : mapped with
        | nil =>
          dsimp only [emitBinaryFold]
          have hargs_nil : args = [] := List.map_eq_nil_iff.mp hmap
          have hm0 : m = 0 := by rw [hargs_nil] at har; exact har.symm
          subst hm0
          refine ⟨isCodeFrom_append_const hg true, List.prefix_append _ _, by simp, by simp,
            fun x hx ↦ ?_⟩
          have hlv : (evalCode Monotone.interpretation false x gates).length =
              numInputs + gates.length := by rw [length_evalCode, hx]
          rw [evalCode_append_singleton]
          change (evalCode Monotone.interpretation false x gates ++ [true]).getD
            (numInputs + gates.length) false = decide (∀ j : Fin 0, _)
          rw [← hlv, List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self, List.getD_cons_zero]
          exact (decide_eq_true fun j ↦ j.elim0).symm
        | cons w ws =>
          dsimp only [emitBinaryFold]
          have hw : w < numInputs + gates.length := hmap_lt w (hmap ▸ List.mem_cons_self ..)
          have hws : ∀ u ∈ ws, u < numInputs + gates.length := fun u hu ↦
            hmap_lt u (hmap ▸ List.mem_cons_of_mem _ hu)
          obtain ⟨hg1, hpre1, hlen1, hout1, hev1⟩ :=
            emitBinaryFoldAux_and_spec numInputs w ws gates hg hw hws
          have hmlen : (w :: ws).length = args.length := by rw [← hmap]; exact List.length_map ..
          refine ⟨hg1, hpre1, by simp only [List.length_cons] at hmlen; omega, hout1,
            fun x hx ↦ ?_⟩
          rw [hev1 x hx, interpretation_and, Bool.eq_iff_iff, Bool.and_eq_true, decide_eq_true_eq,
            decide_eq_true_eq]
          have hmem_map : ∀ u, u ∈ w :: ws ↔ ∃ j ∈ args, wireMap.getD j 0 = u := by
            intro u; rw [← hmap, List.mem_map]
          constructor
          · rintro ⟨hw_t, hrest_t⟩ a
            have ha_lt : a.1 < args.length := by rw [har]; exact a.2
            have ha_mem : args.getD a.1 0 ∈ args := by
              rw [List.getD_eq_getElem _ _ ha_lt]; exact List.getElem_mem ha_lt
            have ha_bnd : args.getD a.1 0 < wireMap.length := by
              have := hargs _ ha_mem; omega
            rw [← hwm_ev x hx (args.getD a.1 0) ha_bnd]
            have hm' : wireMap.getD (args.getD a.1 0) 0 ∈ w :: ws :=
              (hmem_map _).mpr ⟨_, ha_mem, rfl⟩
            rcases List.mem_cons.mp hm' with hEq | hmem_ws
            · exact hEq ▸ hw_t
            · exact hrest_t _ hmem_ws
          · intro hall
            have hfor : ∀ u ∈ w :: ws,
                (evalCode Monotone.interpretation false x gates).getD u false = true := by
              intro u hu
              obtain ⟨j, hj, rfl⟩ := (hmem_map u).mp hu
              obtain ⟨k, hk, hkj⟩ := List.getElem_of_mem hj
              have hk' : k < m := by change args.length = m at har; omega
              have hj_bnd : j < wireMap.length := by have := hargs j hj; omega
              rw [hwm_ev x hx j hj_bnd]
              have hget : args.getD k 0 = j := by rw [List.getD_eq_getElem _ _ hk, hkj]
              rw [← hget]
              exact hall ⟨k, hk'⟩
            exact ⟨hfor w (List.mem_cons_self ..),
              fun u hu ↦ hfor u (List.mem_cons_of_mem _ hu)⟩
      | or m =>
        dsimp only
        cases hmap : mapped with
        | nil =>
          dsimp only [emitBinaryFold]
          have hargs_nil : args = [] := List.map_eq_nil_iff.mp hmap
          have hm0 : m = 0 := by rw [hargs_nil] at har; exact har.symm
          subst hm0
          refine ⟨isCodeFrom_append_const hg false, List.prefix_append _ _, by simp, by simp,
            fun x hx ↦ ?_⟩
          have hlv : (evalCode Monotone.interpretation false x gates).length =
              numInputs + gates.length := by rw [length_evalCode, hx]
          rw [evalCode_append_singleton]
          change (evalCode Monotone.interpretation false x gates ++ [false]).getD
            (numInputs + gates.length) false = decide (∃ j : Fin 0, _)
          rw [← hlv, List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self, List.getD_cons_zero]
          exact (decide_eq_false fun ⟨j, _⟩ ↦ j.elim0).symm
        | cons w ws =>
          dsimp only [emitBinaryFold]
          have hw : w < numInputs + gates.length := hmap_lt w (hmap ▸ List.mem_cons_self ..)
          have hws : ∀ u ∈ ws, u < numInputs + gates.length := fun u hu ↦
            hmap_lt u (hmap ▸ List.mem_cons_of_mem _ hu)
          obtain ⟨hg1, hpre1, hlen1, hout1, hev1⟩ :=
            emitBinaryFoldAux_or_spec numInputs w ws gates hg hw hws
          have hmlen : (w :: ws).length = args.length := by rw [← hmap]; exact List.length_map ..
          refine ⟨hg1, hpre1, by simp only [List.length_cons] at hmlen; omega, hout1,
            fun x hx ↦ ?_⟩
          rw [hev1 x hx, interpretation_or, Bool.eq_iff_iff, Bool.or_eq_true, decide_eq_true_eq,
            decide_eq_true_eq]
          have hmem_map : ∀ u, u ∈ w :: ws ↔ ∃ j ∈ args, wireMap.getD j 0 = u := by
            intro u; rw [← hmap, List.mem_map]
          constructor
          · rintro (hw_t | ⟨u, hu', hu_t⟩)
            · obtain ⟨j, hj, hju⟩ := (hmem_map w).mp (List.mem_cons_self ..)
              obtain ⟨k, hk, hkj⟩ := List.getElem_of_mem hj
              have hk' : k < m := by change args.length = m at har; omega
              have hj_bnd : j < wireMap.length := by have := hargs j hj; omega
              refine ⟨⟨k, hk'⟩, ?_⟩
              have hget : args.getD k 0 = j := by rw [List.getD_eq_getElem _ _ hk, hkj]
              rw [hget, ← hwm_ev x hx j hj_bnd, hju]
              exact hw_t
            · obtain ⟨j, hj, hju⟩ := (hmem_map u).mp (List.mem_cons_of_mem _ hu')
              obtain ⟨k, hk, hkj⟩ := List.getElem_of_mem hj
              have hk' : k < m := by change args.length = m at har; omega
              have hj_bnd : j < wireMap.length := by have := hargs j hj; omega
              refine ⟨⟨k, hk'⟩, ?_⟩
              have hget : args.getD k 0 = j := by rw [List.getD_eq_getElem _ _ hk, hkj]
              rw [hget, ← hwm_ev x hx j hj_bnd, hju]
              exact hu_t
          · rintro ⟨a, ha_t⟩
            have ha_lt : a.1 < args.length := by rw [har]; exact a.2
            have ha_mem : args.getD a.1 0 ∈ args := by
              rw [List.getD_eq_getElem _ _ ha_lt]; exact List.getElem_mem ha_lt
            have ha_bnd : args.getD a.1 0 < wireMap.length := by
              have := hargs _ ha_mem; omega
            rw [← hwm_ev x hx (args.getD a.1 0) ha_bnd] at ha_t
            have hm' : wireMap.getD (args.getD a.1 0) 0 ∈ w :: ws :=
              (hmem_map _).mpr ⟨_, ha_mem, rfl⟩
            rcases List.mem_cons.mp hm' with hEq | hmem_ws
            · exact Or.inl (hEq ▸ ha_t)
            · exact Or.inr ⟨_, hmem_ws, ha_t⟩
    set p := match op with
      | .and _ => emitBinaryFold numInputs .and true mapped gates
      | .or _ => emitBinaryFold numInputs .or false mapped gates
    obtain ⟨hg1, hpre1, hlen1, hout1, hev1⟩ := hstep
    have hprev1_len : (prev ++ [(op, args)]).length = prev.length + 1 := by simp
    have hrest' : Program.IsCodeFrom signature numInputs (prev ++ [(op, args)]).length rest := by
      rwa [hprev1_len]
    have hwm1_len : (wireMap ++ [p.1]).length = numInputs + (prev ++ [(op, args)]).length := by
      simp [hwm_len, Nat.add_assoc]
    have hwm1_lt : ∀ u ∈ wireMap ++ [p.1], u < numInputs + p.2.length := by
      intro u hu
      rcases List.mem_append.mp hu with hu | hu
      · exact lt_of_lt_of_le (hwm_lt u hu) (Nat.add_le_add_left hpre1.length_le _)
      · simp only [List.mem_singleton] at hu; exact hu ▸ hout1
    have hwm1_ev : ∀ (x : List Bool), x.length = numInputs →
        ∀ i < (wireMap ++ [p.1]).length,
          (evalCode Monotone.interpretation false x p.2).getD ((wireMap ++ [p.1]).getD i 0) false =
            (evalCode interpretation false x (prev ++ [(op, args)])).getD i false := by
      intro x hx i hi
      simp only [List.length_append, List.length_singleton] at hi
      rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hi) with hilt | rfl
      · rw [List.getD_append _ _ _ _ hilt]
        have hu_lt : wireMap.getD i 0 < numInputs + gates.length :=
          hwm_lt _ (by rw [List.getD_eq_getElem _ _ hilt]; exact List.getElem_mem hilt)
        rw [getD_evalCode_of_prefix x hx hpre1 hu_lt, hwm_ev x hx i hilt]
        have hlt_prev : i < (evalCode interpretation false x prev).length := by
          rw [length_evalCode, hx]; omega
        rw [evalCode_append, getD_evalCode_of_lt _ _ _ _ hlt_prev]
      · rw [List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self, List.getD_cons_zero, hev1 x hx]
        have hlv : (evalCode interpretation false x prev).length = wireMap.length := by
          rw [length_evalCode, hx, hwm_len]
        rw [evalCode_append_singleton, ← hlv, List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self,
          List.getD_cons_zero]
        dsimp only [evalCodeStep]
        congr 1
        funext a
        have ha : a.1 < args.length := har.symm ▸ a.2
        rw [List.getD_eq_getElem _ _ ha, List.getElem?_eq_getElem ha]
        rfl
    obtain ⟨hg2, hpre2, hlen2, hwmlen2, hwm2_lt, hev2⟩ :=
      ih (wireMap ++ [p.1]) p.2 (prev ++ [(op, args)]) hrest' hwm1_len hg1 hwm1_lt hwm1_ev
    dsimp only [compileGates]
    refine ⟨hg2, hpre1.trans hpre2, ?_, ?_, hwm2_lt, ?_⟩
    · dsimp only [p, mapped] at hlen1 hlen2 ⊢
      simp only [List.map_cons, List.sum_cons]
      omega
    · change (compileGates numInputs rest (wireMap ++ [p.1]) p.2).1.length = _
      rw [hwmlen2]
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    · intro x hx i hi
      have := hev2 x hx i hi
      simpa only [List.append_assoc, List.singleton_append] using this

end ToBinary

/-- Every multi-output unbounded-fan-in monotone circuit `C` can be simulated by an equivalent
binary monotone circuit `C'` of size at most the sum of `max 1` of the arities of the gates of
`C`. -/
theorem exists_binary_of_unbounded {n m : ℕ} (C : Circuit signature n m) :
    ∃ C' : Circuit Monotone.signature n m,
      (∀ x : BitString n, C'.eval Monotone.interpretation x = C.eval interpretation x) ∧
      C'.size ≤ (C.program.code.map fun g ↦ max 1 g.2.length).sum := by
  have hcode : Program.IsCodeFrom signature n 0 C.program.code :=
    (Program.isSome_ofCode_iff (σ := signature)).mp (by simp)
  set initMap : List ℕ := List.range n
  have hinit_len : initMap.length = n + ([] : List (Op × List ℕ)).length := by simp [initMap]
  have hinit_lt : ∀ u ∈ initMap, u < n + ([] : List (Monotone.Op × List ℕ)).length := by
    intro u hu; simpa [initMap] using hu
  have hinit_ev : ∀ (x : List Bool), x.length = n → ∀ i < initMap.length,
      (evalCode Monotone.interpretation false x []).getD (initMap.getD i 0) false =
        (evalCode interpretation false x []).getD i false := by
    intro x _ i hi
    have hget : initMap.getD i 0 = i := by
      rw [List.getD_eq_getElem _ _ hi]
      simp [initMap]
    rw [hget]
    rfl
  obtain ⟨hg, -, hlen, hwmlen, hwm_lt, hev⟩ :=
    compileGates_spec n C.program.code initMap [] [] hcode hinit_len trivial hinit_lt hinit_ev
  set res := compileGates n C.program.code initMap []
  set outs : List ℕ := List.ofFn fun j : Fin m ↦ res.1.getD (C.outputs j).toNat 0
  have hsome : (Circuit.ofCode (σ := Monotone.signature) n m (res.2, outs)).isSome = true := by
    rw [Circuit.isSome_ofCode_iff]
    refine ⟨hg, by simp [outs], fun u hu ↦ ?_⟩
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hu
    have hj_lt : (C.outputs j).toNat < res.1.length := by
      have := Wire.toNat_lt (C.outputs j)
      have hplen : C.program.code.length = C.size := Program.length_code C.program
      simp only [initMap, List.length_range] at hwmlen
      omega
    exact hwm_lt _ (by rw [List.getD_eq_getElem _ _ hj_lt]; exact List.getElem_mem hj_lt)
  obtain ⟨C', hC'_eq⟩ := Option.isSome_iff_exists.mp hsome
  have hC'_code : C'.code = (res.2, outs) := Circuit.code_of_ofCode_eq_some hC'_eq
  have hC'_size : C'.size ≤ (C.program.code.map fun g ↦ max 1 g.2.length).sum := by
    rw [← Circuit.length_code_fst C', hC'_code]
    simpa using hlen
  refine ⟨C', fun x ↦ ?_, hC'_size⟩
  funext j
  have hC'_out : (C'.outputs j).toNat = res.1.getD (C.outputs j).toNat 0 := by
    have h2 := congrArg (fun p : List (Monotone.Op × List ℕ) × List ℕ ↦ p.2.getD j.1 0) hC'_code
    simp only [Circuit.code, outs, List.getD_eq_getElem, List.length_ofFn, j.2,
      List.getElem_ofFn] at h2
    exact h2
  have hj_lt : (C.outputs j).toNat < res.1.length := by
    have := Wire.toNat_lt (C.outputs j)
    have hplen : C.program.code.length = C.size := Program.length_code C.program
    simp only [initMap, List.length_range] at hwmlen
    omega
  rw [Circuit.eval_eq_getD C' Monotone.interpretation false x j,
    Circuit.eval_eq_getD C interpretation false x j, hC'_code, hC'_out]
  change (evalCode Monotone.interpretation false (List.ofFn x) res.2).getD
      (res.1.getD (C.outputs j).toNat 0) false =
    (evalCode interpretation false (List.ofFn x) C.program.code).getD (C.outputs j).toNat false
  simpa only [List.nil_append] using hev (List.ofFn x) (by simp) (C.outputs j).toNat hj_lt

end CslibFrontier.Computability.Circuit.Monotone.Unbounded
