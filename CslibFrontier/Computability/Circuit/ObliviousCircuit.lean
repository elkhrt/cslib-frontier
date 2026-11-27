module

public import CslibFrontier.Computability.Circuit.Boolean.Encoding
public import CslibFrontier.Computability.Circuit.Boolean.EvaluationTime
public import CslibFrontier.Computability.Circuit.BlockTape
import CslibFrontier.Computability.Circuit.Boolean.OpValue
import CslibFrontier.Computability.Circuit.Boolean.Tseitin
import CslibFrontier.Computability.Circuit.Encoding.Evaluation
import CslibFrontier.Foundations.Data.Nat.BinarySize
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring

/-!
# Pippenger–Fischer $O(T \log T)$ Oblivious Circuit Construction

This module compiles the pure Pippenger–Fischer block-tape simulation
(`CslibFrontier.Computability.Circuit.BlockTape`) of any deterministic multi-tape Turing
machine (`Turing.MultiTapeTM`) into a De Morgan Boolean circuit
(`Cslib.Circuits.Circuit Cslib.Circuits.Boolean.signature`) of size
$O((T + 1)(\log_2(\max(T, N) + 2) + 1))$.

## Main definitions

* `CslibFrontier.Computability.Circuit.Oblivious.Gates`: reversed gate-list builder with next
  wire index.
* `CslibFrontier.Computability.Circuit.Oblivious.LevelW`, `TapeW`, `StateW`: wire-index
  representations of `BlockLevel`, `BlockTape`, and `ObliviousCfg`.
* `CslibFrontier.Computability.Circuit.Oblivious.buildGates`: full $T$-step oblivious gate
  builder parameterized by arbitrary input wire indices `inputWires`.
* `CslibFrontier.Computability.Circuit.Oblivious.obliviousCircuitWithWires`: resulting
  `Circuit Boolean.signature totalInputs 1` with negated-output option.

## Main results

* `CslibFrontier.Computability.Circuit.Oblivious.size_obliviousCircuitWithWires_le`: the
  circuit has $O((T + 1)(\log_2(\max(T, N) + 2) + 1))$ gates, independent of
  `totalInputs`.
* `CslibFrontier.Computability.Circuit.Oblivious.eval_obliviousCircuitWithWires`: the circuit
  evaluates to `true` iff the simulated machine produces output `[true]` after `T` steps
  (or its negation when `negateOut = true`).
-/

public section

namespace CslibFrontier.Computability.Circuit.Oblivious

open Turing MultiTapeTM Cslib.Circuits Cslib.Circuits.Boolean

/-! ### Gate-list builder and basic Boolean gadgets -/

/-- Reversed list of De Morgan gates together with the next fresh wire index. -/
abbrev Gates : Type := List (Boolean.Op × List ℕ) × ℕ

namespace Gates

/-- Well-formedness of a gate builder over `N` primary input wires. -/
@[expose] def WF (N : ℕ) (g : Gates) : Prop :=
  Program.IsCodeFrom Boolean.signature N 0 g.1.reverse ∧ g.2 = N + g.1.length

/-- Wire value in `g` on primary input list `x`. -/
@[expose] def val (x : List Bool) (g : Gates) (w : ℕ) : Bool :=
  (evalCode Boolean.interpretation false x g.1.reverse).getD w false

/-- `g'` extends `g` by prepending new gates onto `g.1`. -/
@[expose] def Extends (g g' : Gates) : Prop :=
  ∃ rest : List (Boolean.Op × List ℕ), g'.1 = rest ++ g.1

theorem extends_refl (g : Gates) : Extends g g := ⟨[], rfl⟩

theorem extends_trans {g₁ g₂ g₃ : Gates} (h1 : Extends g₁ g₂) (h2 : Extends g₂ g₃) :
    Extends g₁ g₃ := by
  rcases h1 with ⟨r1, h1⟩
  rcases h2 with ⟨r2, h2⟩
  exact ⟨r2 ++ r1, by rw [h2, h1, List.append_assoc]⟩

theorem val_of_extends {x : List Bool} {g g' : Gates} (hext : Extends g g')
    {w : ℕ} (hw : w < x.length + g.1.length) :
    g'.val x w = g.val x w := by
  rcases hext with ⟨rest, hrest⟩
  simp only [val, hrest, List.reverse_append]
  exact Boolean.getD_evalCode_append_of_lt (by simpa using hw)

theorem val_of_extends_wf {x : List Bool} {g g' : Gates} (hwf : g.WF x.length)
    (hext : Extends g g') {w : ℕ} (hw : w < g.2) :
    g'.val x w = g.val x w :=
  val_of_extends hext (hwf.2 ▸ hw)

/-- Emit a single gate `(op, args)` and return its wire index. -/
@[expose] def emit (g : Gates) (op : Boolean.Op) (args : List ℕ) : Gates × ℕ :=
  (((op, args) :: g.1, g.2 + 1), g.2)

theorem emit_wf {N : ℕ} {g : Gates} {op : Boolean.Op} {args : List ℕ}
    (hg : g.WF N) (hlen : args.length = Boolean.signature.Arity op)
    (hargs : ∀ a ∈ args, a < g.2) :
    (g.emit op args).1.WF N := by
  refine ⟨?_, by simp [emit, hg.2]; omega⟩
  simp only [emit, List.reverse_cons]; rw [Program.isCodeFrom_append, Program.isCodeFrom_cons]
  refine ⟨hg.1, ⟨⟨hlen, fun a ha => ?_⟩, Program.isCodeFrom_nil _⟩⟩
  have := hargs a ha
  simp only [List.length_reverse, hg.2] at this ⊢; omega

theorem emit_extends (g : Gates) (op : Boolean.Op) (args : List ℕ) :
    Extends g (g.emit op args).1 :=
  ⟨[(op, args)], rfl⟩

theorem emit_val_new {x : List Bool} {g : Gates} {op : Boolean.Op} {args : List ℕ}
    (hg : g.WF x.length) (hlen : args.length = Boolean.signature.Arity op)
    (hargs : ∀ a ∈ args, a < g.2) :
    (g.emit op args).1.val x g.2 =
      Boolean.interpretation op fun a => args[a.val]?.elim false (g.val x) := by
  have hwf := emit_wf hg hlen hargs
  have hget : ((g.emit op args).1.1.reverse)[g.1.length]? = some (op, args) := by
    simp [emit]
  have hv := getD_evalCode Boolean.interpretation false x hwf.1 hget
  rw [← hg.2] at hv; dsimp only [val]
  rw [hv]
  congr 1; funext a
  cases ha : args[a.val]? with
  | none => rfl
  | some w =>
    simp only [Option.elim_some]
    exact val_of_extends_wf hg (emit_extends g op args) (hargs w (List.mem_of_getElem? ha))

/-- Initial builder with `false` at wire `N` and `true` at wire `N + 1`. -/
@[expose] def init (N : ℕ) : Gates :=
  ([(.const true, []), (.const false, [])], N + 2)

theorem init_wf (N : ℕ) : (init N).WF N := by
  refine ⟨?_, by simp [init]⟩
  simp only [init, List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append]
  rw [Program.isCodeFrom_cons, Program.isCodeFrom_cons]
  exact ⟨⟨rfl, by simp⟩, ⟨rfl, by simp⟩, Program.isCodeFrom_nil _⟩

theorem init_val_input {x : List Bool} {i : ℕ} (hi : i < x.length) :
    (init x.length).val x i = x[i] := by
  simp only [val]; rw [getD_evalCode_of_lt _ _ _ _ hi, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hi, Option.getD_some]

theorem init_val_fls (x : List Bool) : (init x.length).val x x.length = false := by
  have hwf := init_wf x.length
  have hget : ((init x.length).1.reverse)[0]? = some (.const false, []) := by simp [init]
  have hv := getD_evalCode Boolean.interpretation false x hwf.1 hget
  rw [Nat.add_zero] at hv; dsimp only [val]
  rw [hv]; rfl

theorem init_val_tru (x : List Bool) : (init x.length).val x (x.length + 1) = true := by
  have hwf := init_wf x.length
  have hget : ((init x.length).1.reverse)[1]? = some (.const true, []) := by simp [init]
  have hv := getD_evalCode Boolean.interpretation false x hwf.1 hget
  dsimp only [val]; rw [hv]
  rfl

/-- Emit a `NOT` gate. -/
@[expose] def gNot (g : Gates) (a : ℕ) : Gates × ℕ := g.emit .not [a]

/-- Emit an `AND` gate. -/
@[expose] def gAnd (g : Gates) (a b : ℕ) : Gates × ℕ := g.emit .and [a, b]

/-- Emit an `OR` gate. -/
@[expose] def gOr (g : Gates) (a b : ℕ) : Gates × ℕ := g.emit .or [a, b]

/-- Emit a 3-way `OR`. -/
@[expose] def gOr3 (g : Gates) (a b c : ℕ) : Gates × ℕ :=
  let (g1, w1) := gOr g a b
  gOr g1 w1 c

/-- Emit a 4-way `OR`. -/
@[expose] def gOr4 (g : Gates) (a b c d : ℕ) : Gates × ℕ :=
  let (g1, w1) := gOr g a b
  let (g2, w2) := gOr g1 c d
  gOr g2 w1 w2

/-- Emit a 2-way multiplexer `if sel then a else b` (4 gates). -/
@[expose] def gMux (g : Gates) (sel a b : ℕ) : Gates × ℕ :=
  let (g1, ns) := gNot g sel
  let (g2, w1) := gAnd g1 sel a
  let (g3, w2) := gAnd g2 ns b
  gOr g3 w1 w2

/-- Emit a 3-way one-hot selector `(s0 ∧ a0) ∨ (s1 ∧ a1) ∨ (s2 ∧ a2)` (5 gates). -/
@[expose] def gMux3 (g : Gates) (s0 a0 s1 a1 s2 a2 : ℕ) : Gates × ℕ :=
  let (g1, w0) := gAnd g s0 a0
  let (g2, w1) := gAnd g1 s1 a1
  let (g3, w2) := gAnd g2 s2 a2
  gOr3 g3 w0 w1 w2

/-- Emit a 4-way one-hot selector (7 gates). -/
@[expose] def gMux4 (g : Gates) (s0 a0 s1 a1 s2 a2 s3 a3 : ℕ) : Gates × ℕ :=
  let (g1, w0) := gAnd g s0 a0
  let (g2, w1) := gAnd g1 s1 a1
  let (g3, w2) := gAnd g2 s2 a2
  let (g4, w3) := gAnd g3 s3 a3
  gOr4 g4 w0 w1 w2 w3

/-- Emit an `OR` over a list of wires (using `fls` for empty list). -/
@[expose] def gOrList (g : Gates) (fls : ℕ) (ws : List ℕ) : Gates × ℕ :=
  ws.foldl (fun acc w => gOr acc.1 acc.2 w) (g, fls)

/-- Emit an `AND` over a list of wires (using `tru` for empty list). -/
@[expose] def gAndList (g : Gates) (tru : ℕ) (ws : List ℕ) : Gates × ℕ :=
  ws.foldl (fun acc w => gAnd acc.1 acc.2 w) (g, tru)

theorem gNot_spec {x : List Bool} {g : Gates} {a : ℕ} (hg : g.WF x.length) (ha : a < g.2) :
    let r := gNot g a
    r.1.WF x.length ∧ Extends g r.1 ∧ r.2 < r.1.2 ∧ r.1.1.length = g.1.length + 1 ∧
      r.1.val x r.2 = !(g.val x a) := by
  refine ⟨emit_wf hg rfl (by simp [ha]), emit_extends _ _ _, by simp [gNot, emit],
    by simp [gNot, emit], ?_⟩
  have hv := emit_val_new hg (op := .not) (args := [a]) rfl (by simp [ha])
  exact hv

theorem gAnd_spec {x : List Bool} {g : Gates} {a b : ℕ} (hg : g.WF x.length)
    (ha : a < g.2) (hb : b < g.2) :
    let r := gAnd g a b
    r.1.WF x.length ∧ Extends g r.1 ∧ r.2 < r.1.2 ∧ r.1.1.length = g.1.length + 1 ∧
      r.1.val x r.2 = (g.val x a && g.val x b) := by
  refine ⟨emit_wf hg rfl (by simp [ha, hb]), emit_extends _ _ _, by simp [gAnd, emit],
    by simp [gAnd, emit], ?_⟩
  exact emit_val_new hg (op := .and) (args := [a, b]) rfl (by simp [ha, hb])

theorem gOr_spec {x : List Bool} {g : Gates} {a b : ℕ} (hg : g.WF x.length)
    (ha : a < g.2) (hb : b < g.2) :
    let r := gOr g a b
    r.1.WF x.length ∧ Extends g r.1 ∧ r.2 < r.1.2 ∧ r.1.1.length = g.1.length + 1 ∧
      r.1.val x r.2 = (g.val x a || g.val x b) := by
  refine ⟨emit_wf hg rfl (by simp [ha, hb]), emit_extends _ _ _, by simp [gOr, emit],
    by simp [gOr, emit], ?_⟩
  exact emit_val_new hg (op := .or) (args := [a, b]) rfl (by simp [ha, hb])

theorem gOr3_spec {x : List Bool} {g : Gates} {a b c : ℕ} (hg : g.WF x.length)
    (ha : a < g.2) (hb : b < g.2) (hc : c < g.2) :
    let r := gOr3 g a b c
    r.1.WF x.length ∧ Extends g r.1 ∧ r.2 < r.1.2 ∧ r.1.1.length = g.1.length + 2 ∧
      r.1.val x r.2 = (g.val x a || g.val x b || g.val x c) := by
  dsimp only [gOr3]
  have h1 := gOr_spec hg ha hb
  have h2 := gOr_spec h1.1 h1.2.2.1 (lt_trans hc (by rw [h1.1.2, hg.2, h1.2.2.2.1]; omega))
  refine ⟨h2.1, extends_trans h1.2.1 h2.2.1, h2.2.2.1, by omega, ?_⟩
  rw [h2.2.2.2.2, h1.2.2.2.2, val_of_extends_wf hg h1.2.1 hc]

theorem gOr4_spec {x : List Bool} {g : Gates} {a b c d : ℕ} (hg : g.WF x.length)
    (ha : a < g.2) (hb : b < g.2) (hc : c < g.2) (hd : d < g.2) :
    let r := gOr4 g a b c d
    r.1.WF x.length ∧ Extends g r.1 ∧ r.2 < r.1.2 ∧ r.1.1.length = g.1.length + 3 ∧
      r.1.val x r.2 = ((g.val x a || g.val x b) || (g.val x c || g.val x d)) := by
  dsimp only [gOr4]
  have h1 := gOr_spec hg ha hb
  have hc1 : c < (gOr g a b).1.2 := lt_trans hc (by rw [h1.1.2, hg.2, h1.2.2.2.1]; omega)
  have hd1 : d < (gOr g a b).1.2 := lt_trans hd (by rw [h1.1.2, hg.2, h1.2.2.2.1]; omega)
  have h2 := gOr_spec h1.1 hc1 hd1
  have hw1 : (gOr g a b).2 < (gOr (gOr g a b).1 c d).1.2 :=
    lt_trans h1.2.2.1 (by rw [h2.1.2, h1.1.2, h2.2.2.2.1]; omega)
  have h3 := gOr_spec h2.1 hw1 h2.2.2.1
  refine ⟨h3.1, extends_trans (extends_trans h1.2.1 h2.2.1) h3.2.1, h3.2.2.1, by omega, ?_⟩
  rw [h3.2.2.2.2, val_of_extends_wf h1.1 h2.2.1 h1.2.2.1, h1.2.2.2.2, h2.2.2.2.2,
    val_of_extends_wf hg h1.2.1 hc, val_of_extends_wf hg h1.2.1 hd]

theorem gMux3_spec {x : List Bool} {g : Gates} {s0 a0 s1 a1 s2 a2 : ℕ} (hg : g.WF x.length)
    (hs0 : s0 < g.2) (ha0 : a0 < g.2) (hs1 : s1 < g.2) (ha1 : a1 < g.2)
    (hs2 : s2 < g.2) (ha2 : a2 < g.2) :
    let r := gMux3 g s0 a0 s1 a1 s2 a2
    r.1.WF x.length ∧ Extends g r.1 ∧ r.2 < r.1.2 ∧ r.1.1.length = g.1.length + 5 ∧
      r.1.val x r.2 =
        ((g.val x s0 && g.val x a0) || (g.val x s1 && g.val x a1) ||
          (g.val x s2 && g.val x a2)) := by
  dsimp only [gMux3]
  have h1 := gAnd_spec hg hs0 ha0
  have hlt1 : g.2 < (gAnd g s0 a0).1.2 := by rw [h1.1.2, hg.2, h1.2.2.2.1]; omega
  have h2 := gAnd_spec h1.1 (lt_trans hs1 hlt1) (lt_trans ha1 hlt1)
  have hlt2 : (gAnd g s0 a0).1.2 < (gAnd (gAnd g s0 a0).1 s1 a1).1.2 := by
    rw [h2.1.2, h1.1.2, h2.2.2.2.1]; omega
  have h3 := gAnd_spec h2.1 (lt_trans (lt_trans hs2 hlt1) hlt2) (lt_trans (lt_trans ha2 hlt1) hlt2)
  have hlt3 : (gAnd (gAnd g s0 a0).1 s1 a1).1.2 <
      (gAnd (gAnd (gAnd g s0 a0).1 s1 a1).1 s2 a2).1.2 := by
    rw [h3.1.2, h2.1.2, h3.2.2.2.1]; omega
  have h4 := gOr3_spec h3.1 (lt_trans (lt_trans h1.2.2.1 hlt2) hlt3)
    (lt_trans h2.2.2.1 hlt3) h3.2.2.1
  have he12 := extends_trans h1.2.1 h2.2.1
  have he13 := extends_trans he12 h3.2.1
  refine ⟨h4.1, extends_trans he13 h4.2.1, h4.2.2.1, by omega, ?_⟩
  rw [h4.2.2.2.2, val_of_extends_wf h1.1 (extends_trans h2.2.1 h3.2.1) h1.2.2.1, h1.2.2.2.2,
    val_of_extends_wf h2.1 h3.2.1 h2.2.2.1, h2.2.2.2.2,
    val_of_extends_wf hg h1.2.1 hs1, val_of_extends_wf hg h1.2.1 ha1,
    h3.2.2.2.2, val_of_extends_wf hg he12 hs2, val_of_extends_wf hg he12 ha2]

theorem gMux4_spec {x : List Bool} {g : Gates} {s0 a0 s1 a1 s2 a2 s3 a3 : ℕ} (hg : g.WF x.length)
    (hs0 : s0 < g.2) (ha0 : a0 < g.2) (hs1 : s1 < g.2) (ha1 : a1 < g.2)
    (hs2 : s2 < g.2) (ha2 : a2 < g.2) (hs3 : s3 < g.2) (ha3 : a3 < g.2) :
    let r := gMux4 g s0 a0 s1 a1 s2 a2 s3 a3
    r.1.WF x.length ∧ Extends g r.1 ∧ r.2 < r.1.2 ∧ r.1.1.length = g.1.length + 7 ∧
      r.1.val x r.2 =
        (((g.val x s0 && g.val x a0) || (g.val x s1 && g.val x a1)) ||
          ((g.val x s2 && g.val x a2) || (g.val x s3 && g.val x a3))) := by
  dsimp only [gMux4]
  have h1 := gAnd_spec hg hs0 ha0
  have hlt1 : g.2 < (gAnd g s0 a0).1.2 := by rw [h1.1.2, hg.2, h1.2.2.2.1]; omega
  have h2 := gAnd_spec h1.1 (lt_trans hs1 hlt1) (lt_trans ha1 hlt1)
  have hlt2 : (gAnd g s0 a0).1.2 < (gAnd (gAnd g s0 a0).1 s1 a1).1.2 := by
    rw [h2.1.2, h1.1.2, h2.2.2.2.1]; omega
  have h3 := gAnd_spec h2.1 (lt_trans (lt_trans hs2 hlt1) hlt2) (lt_trans (lt_trans ha2 hlt1) hlt2)
  have hlt3 : (gAnd (gAnd g s0 a0).1 s1 a1).1.2 <
      (gAnd (gAnd (gAnd g s0 a0).1 s1 a1).1 s2 a2).1.2 := by
    rw [h3.1.2, h2.1.2, h3.2.2.2.1]; omega
  have h4 := gAnd_spec h3.1 (lt_trans (lt_trans (lt_trans hs3 hlt1) hlt2) hlt3)
    (lt_trans (lt_trans (lt_trans ha3 hlt1) hlt2) hlt3)
  have hlt4 : (gAnd (gAnd (gAnd g s0 a0).1 s1 a1).1 s2 a2).1.2 <
      (gAnd (gAnd (gAnd (gAnd g s0 a0).1 s1 a1).1 s2 a2).1 s3 a3).1.2 := by
    rw [h4.1.2, h3.1.2, h4.2.2.2.1]; omega
  have h5 := gOr4_spec h4.1
    (lt_trans (lt_trans (lt_trans h1.2.2.1 hlt2) hlt3) hlt4)
    (lt_trans (lt_trans h2.2.2.1 hlt3) hlt4)
    (lt_trans h3.2.2.1 hlt4) h4.2.2.1
  have he12 := extends_trans h1.2.1 h2.2.1
  have he13 := extends_trans he12 h3.2.1
  have he14 := extends_trans he13 h4.2.1
  refine ⟨h5.1, extends_trans he14 h5.2.1, h5.2.2.1, by omega, ?_⟩
  rw [h5.2.2.2.2, val_of_extends_wf h1.1 (extends_trans (extends_trans h2.2.1 h3.2.1) h4.2.1)
      h1.2.2.1, h1.2.2.2.2,
    val_of_extends_wf h2.1 (extends_trans h3.2.1 h4.2.1) h2.2.2.1, h2.2.2.2.2,
    val_of_extends_wf hg h1.2.1 hs1, val_of_extends_wf hg h1.2.1 ha1,
    val_of_extends_wf h3.1 h4.2.1 h3.2.2.1, h3.2.2.2.2,
    val_of_extends_wf hg he12 hs2, val_of_extends_wf hg he12 ha2,
    h4.2.2.2.2, val_of_extends_wf hg he13 hs3, val_of_extends_wf hg he13 ha3]

theorem gOrList_spec {x : List Bool} {g : Gates} {fls : ℕ} {ws : List ℕ}
    (hg : g.WF x.length) (hfls : fls < g.2) (hws : ∀ w ∈ ws, w < g.2) :
    let r := gOrList g fls ws
    r.1.WF x.length ∧ Extends g r.1 ∧ r.2 < r.1.2 ∧ r.1.1.length = g.1.length + ws.length ∧
      r.1.val x r.2 = (g.val x fls || ws.any (g.val x)) := by
  induction ws generalizing g fls with
  | nil =>
    exact ⟨hg, extends_refl g, hfls, rfl, by simp [gOrList]⟩
  | cons w tl ih =>
    simp only [gOrList, List.foldl_cons]
    have hw : w < g.2 := hws w List.mem_cons_self
    have h1 := gOr_spec hg hfls hw
    have hlt1 : g.2 < (gOr g fls w).1.2 := by rw [h1.1.2, hg.2, h1.2.2.2.1]; omega
    have h2 := ih h1.1 h1.2.2.1 (fun u hu => lt_trans (hws u (List.mem_cons_of_mem w hu)) hlt1)
    dsimp only [gOrList] at h2
    refine ⟨h2.1, extends_trans h1.2.1 h2.2.1, h2.2.2.1,
      by rw [h2.2.2.2.1, h1.2.2.2.1, List.length_cons]; omega, ?_⟩
    rw [h2.2.2.2.2, h1.2.2.2.2]
    have hany : tl.any ((gOr g fls w).1.val x) = tl.any (g.val x) := by
      rw [Bool.eq_iff_iff]; simp only [List.any_eq_true]
      exact exists_congr fun u => and_congr_right fun hu => by
        rw [val_of_extends_wf hg h1.2.1 (hws u (List.mem_cons_of_mem w hu))]
    rw [hany]; simp [Bool.or_assoc]

@[simp] theorem init_fst (N : ℕ) : (init N).1 = [(.const true, []), (.const false, [])] := rfl

@[simp] theorem init_snd (N : ℕ) : (init N).2 = N + 2 := rfl

theorem emit_eq (g : Gates) (op : Boolean.Op) (args : List ℕ) :
    emit g op args = (((op, args) :: g.1, g.2 + 1), g.2) := rfl

theorem init_eq (N : ℕ) :
    init N = ([(.const true, []), (.const false, [])], N + 2) := rfl

theorem gNot_eq (g : Gates) (a : ℕ) :
    gNot g a = g.emit .not [a] := rfl

theorem gAnd_eq (g : Gates) (a b : ℕ) :
    gAnd g a b = g.emit .and [a, b] := rfl

theorem gOr_eq (g : Gates) (a b : ℕ) :
    gOr g a b = g.emit .or [a, b] := rfl

theorem gOr3_eq (g : Gates) (a b c : ℕ) :
    gOr3 g a b c =
      let (g1, w1) := gOr g a b
      gOr g1 w1 c := rfl

theorem gOr4_eq (g : Gates) (a b c d : ℕ) :
    gOr4 g a b c d =
      let (g1, w1) := gOr g a b
      let (g2, w2) := gOr g1 c d
      gOr g2 w1 w2 := rfl

theorem gMux_eq (g : Gates) (sel a b : ℕ) :
    gMux g sel a b =
      let (g1, nsel) := g.gNot sel
      let (g2, w1) := g1.gAnd sel a
      let (g3, w2) := g2.gAnd nsel b
      g3.gOr w1 w2 := rfl

theorem gMux3_eq (g : Gates) (s0 a0 s1 a1 s2 a2 : ℕ) :
    gMux3 g s0 a0 s1 a1 s2 a2 =
      let (g1, w0) := gAnd g s0 a0
      let (g2, w1) := gAnd g1 s1 a1
      let (g3, w2) := gAnd g2 s2 a2
      gOr3 g3 w0 w1 w2 := rfl

theorem gMux4_eq (g : Gates) (s0 a0 s1 a1 s2 a2 s3 a3 : ℕ) :
    gMux4 g s0 a0 s1 a1 s2 a2 s3 a3 =
      let (g1, w0) := gAnd g s0 a0
      let (g2, w1) := gAnd g1 s1 a1
      let (g3, w2) := gAnd g2 s2 a2
      let (g4, w3) := gAnd g3 s3 a3
      gOr4 g4 w0 w1 w2 w3 := rfl

theorem gOrList_eq (g : Gates) (fls : ℕ) (ws : List ℕ) :
    gOrList g fls ws = ws.foldl (fun acc w => gOr acc.1 acc.2 w) (g, fls) := rfl

theorem gAndList_eq (g : Gates) (tru : ℕ) (ws : List ℕ) :
    gAndList g tru ws = ws.foldl (fun acc w => gAnd acc.1 acc.2 w) (g, tru) := rfl

end Gates

/-! ### Wire representations of `BlockLevel`, `BlockTape`, and `ObliviousCfg` -/

/-- Wire representation of a `BlockLevel i`: 6 one-hot count wires and `2 ^ i` cell rows,
each cell row containing `10` wires (5 slots × 2 bits). -/
abbrev LevelW : Type := List ℕ × List (List ℕ)

/-- Wire representation of an `L`-level `BlockHalfTape`: list of `L` `LevelW`s. -/
abbrev HalfW : Type := List LevelW

/-- Wire representation of a `BlockTape`: `(headCell, (left, right))`. -/
abbrev TapeW : Type := (ℕ × ℕ) × (HalfW × HalfW)

/-- Wire representation of `ObliviousCfg`: `((stateW, outW), (inputTape, workTapes))`. -/
abbrev StateW : Type := (List ℕ × List ℕ) × (TapeW × List TapeW)

/-- Wire validity predicate for `LevelW`. -/
@[expose] def LevelW.Valid (W : ℕ) (i : ℕ) (lw : LevelW) : Prop :=
  lw.1.length = 6 ∧ (∀ w ∈ lw.1, w < W) ∧
  lw.2.length = 2 ^ i ∧ ∀ row ∈ lw.2, row.length = 10 ∧ ∀ w ∈ row, w < W

theorem LevelW.Valid.mono {W W' i : ℕ} {lw : LevelW} (h : lw.Valid W i) (hle : W ≤ W') :
    lw.Valid W' i :=
  ⟨h.1, fun w hw => lt_of_lt_of_le (h.2.1 w hw) hle,
   h.2.2.1, fun row hrow => ⟨(h.2.2.2 row hrow).1, fun w hw =>
     lt_of_lt_of_le ((h.2.2.2 row hrow).2 w hw) hle⟩⟩

theorem LevelW.Valid.getD_cnt {W i : ℕ} {lw : LevelW} (h : lw.Valid W i) {c : ℕ} (hc : c < 6) :
    lw.1.getD c 0 < W := by
  have hl := h.1
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
  exact h.2.1 _ (List.getElem_mem _)

theorem LevelW.Valid.getD_cell {W i : ℕ} {lw : LevelW} (h : lw.Valid W i) {j k : ℕ}
    (hj : j < 2 ^ i) (hk : k < 10) :
    (lw.2.getD j []).getD k 0 < W := by
  have hl2 := h.2.2.1
  have hj' : j < lw.2.length := by omega
  have hrow := h.2.2.2 (lw.2[j]) (List.getElem_mem hj')
  have hrl := hrow.1
  have hrow_eq : lw.2.getD j [] = lw.2[j] := by simp [List.getD, hj']
  rw [hrow_eq, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
  exact hrow.2 _ (List.getElem_mem _)

/-- Semantics: `lw` encodes `lvl : BlockLevel i` under gate builder `g` and input `x`. -/
@[expose] def LevelW.Encodes (g : Gates) (x : List Bool) {i : ℕ} (lw : LevelW) (lvl : BlockLevel i)
  : Prop :=
  lw.Valid g.2 i ∧
  (∀ c : Fin 6, g.val x (lw.1.getD c.val 0) = decide (lvl.cnt = c.val)) ∧
  (∀ (j : Fin (2 ^ i)) (s : Fin 5),
    let row := lw.2.getD j.val []
    (g.val x (row.getD (2 * s.val) 0), g.val x (row.getD (2 * s.val + 1) 0)) = lvl.slots s j)

theorem LevelW.Encodes.of_extends {x : List Bool} {g g' : Gates} {i : ℕ}
    {lw : LevelW} {lvl : BlockLevel i} (hg : g.WF x.length) (hext : Gates.Extends g g')
    (hle : g.2 ≤ g'.2) (henc : lw.Encodes g x lvl) :
    lw.Encodes g' x lvl := by
  refine ⟨henc.1.mono hle, fun c => ?_, fun j s => ?_⟩
  · rw [Gates.val_of_extends_wf hg hext (henc.1.getD_cnt c.isLt)]; exact henc.2.1 c
  · dsimp only
    rw [Gates.val_of_extends_wf hg hext (henc.1.getD_cell j.isLt (by omega)),
      Gates.val_of_extends_wf hg hext (henc.1.getD_cell j.isLt (by omega))]
    exact henc.2.2 j s

/-- Wire validity and encoding for `HalfW`. -/
@[expose] def HalfW.Encodes (g : Gates) (x : List Bool) {L : ℕ} (hw : HalfW) (ht : BlockHalfTape L)
  : Prop :=
  hw.length = L ∧ ∀ i : Fin L, (hw.getD i.val ([], [])).Encodes g x (ht i)

theorem HalfW.Encodes.of_extends {x : List Bool} {g g' : Gates} {L : ℕ}
    {hw : HalfW} {ht : BlockHalfTape L} (hg : g.WF x.length) (hext : Gates.Extends g g')
    (hle : g.2 ≤ g'.2) (henc : hw.Encodes g x ht) :
    hw.Encodes g' x ht :=
  ⟨henc.1, fun i => (henc.2 i).of_extends hg hext hle⟩

/-- Wire validity and encoding for `TapeW`. -/
@[expose] def TapeW.Encodes (g : Gates) (x : List Bool) {L : ℕ} (tw : TapeW) (bt : BlockTape L)
  : Prop :=
  tw.1.1 < g.2 ∧ tw.1.2 < g.2 ∧
  (g.val x tw.1.1, g.val x tw.1.2) = bt.head ∧
  tw.2.1.Encodes g x bt.left ∧ tw.2.2.Encodes g x bt.right

theorem TapeW.Encodes.of_extends {x : List Bool} {g g' : Gates} {L : ℕ}
    {tw : TapeW} {bt : BlockTape L} (hg : g.WF x.length) (hext : Gates.Extends g g')
    (hle : g.2 ≤ g'.2) (henc : tw.Encodes g x bt) :
    tw.Encodes g' x bt :=
  ⟨lt_of_lt_of_le henc.1 hle, lt_of_lt_of_le henc.2.1 hle,
   by rw [Gates.val_of_extends_wf hg hext henc.1, Gates.val_of_extends_wf hg hext henc.2.1];
      exact henc.2.2.1,
   henc.2.2.2.1.of_extends hg hext hle, henc.2.2.2.2.of_extends hg hext hle⟩

/-! ### Generic list-emission combinator `emitMap` -/

/-- Emit one wire per element of `xs` using `f`, preserving wire order. -/
@[expose] def emitMap {α : Type} (g : Gates) (f : Gates → α → Gates × ℕ) (xs : List α) :
    Gates × List ℕ :=
  let res := xs.foldl (fun acc a =>
    let (g', w) := f acc.1 a
    (g', w :: acc.2)) (g, [])
  (res.1, res.2.reverse)

private lemma emitMap_foldl_append {α : Type} (f : Gates → α → Gates × ℕ) (l : List α)
    (g₀ : Gates) (acc : List ℕ) :
    let res := l.foldl (fun p a => let q := f p.1 a; (q.1, q.2 :: p.2)) (g₀, acc)
    let res0 := l.foldl (fun p a => let q := f p.1 a; (q.1, q.2 :: p.2)) (g₀, [])
    res.1 = res0.1 ∧ res.2 = res0.2 ++ acc := by
  induction l generalizing g₀ acc with
  | nil => simp
  | cons a tl ih =>
    simp only [List.foldl_cons]
    have h1 := ih (f g₀ a).1 ((f g₀ a).2 :: acc)
    have h2 := ih (f g₀ a).1 [(f g₀ a).2]
    refine ⟨h1.1.trans h2.1.symm, ?_⟩
    rw [h1.2, h2.2, List.append_assoc, List.singleton_append]

/-- Master specification for `emitMap`: simultaneously establishes well-formedness, extension,
wire bounds, exact gate count, and wire values for all emitted wires. -/
theorem emitMap_spec {α : Type} {x : List Bool} {g : Gates} {f : Gates → α → Gates × ℕ}
    {xs : List α} {K : ℕ} {spec : α → Bool}
    (hg : g.WF x.length)
    (hf : ∀ (g₀ : Gates) (a : α), a ∈ xs → g₀.WF x.length → Gates.Extends g g₀ →
      let r := f g₀ a
      r.1.WF x.length ∧ Gates.Extends g₀ r.1 ∧ r.2 < r.1.2 ∧
        r.1.1.length = g₀.1.length + K ∧ r.1.val x r.2 = spec a) :
    let r := emitMap g f xs
    r.1.WF x.length ∧ Gates.Extends g r.1 ∧ r.2.length = xs.length ∧
    r.1.1.length = g.1.length + K * xs.length ∧
    (∀ w ∈ r.2, w < r.1.2) ∧
    (∀ (i : ℕ) (hi : i < xs.length), r.1.val x (r.2.getD i 0) = spec xs[i]) := by
  suffices h : ∀ (l : List α), (∀ a ∈ l, a ∈ xs) → ∀ (g₀ : Gates),
      g₀.WF x.length → Gates.Extends g g₀ →
      let r := emitMap g₀ f l
      r.1.WF x.length ∧ Gates.Extends g₀ r.1 ∧ r.2.length = l.length ∧
      r.1.1.length = g₀.1.length + K * l.length ∧
      (∀ w ∈ r.2, w < r.1.2) ∧
      (∀ (i : ℕ) (hi : i < l.length), r.1.val x (r.2.getD i 0) = spec l[i]) by
    exact h xs (fun _ ha => ha) g hg (Gates.extends_refl g)
  intro l
  induction l with
  | nil =>
    intro _ g₀ hg₀ _
    exact ⟨hg₀, Gates.extends_refl g₀, rfl, by simp [emitMap], by simp [emitMap],
      fun _ hi => by simp at hi⟩
  | cons a tl ih =>
    intro hsub g₀ hg₀ hext₀
    have ha : a ∈ xs := hsub a List.mem_cons_self
    have hstep := hf g₀ a ha hg₀ hext₀
    set p := f g₀ a
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ :=
      ih (fun b hb => hsub b (List.mem_cons_of_mem a hb)) p.1 hstep.1
        (Gates.extends_trans hext₀ hstep.2.1)
    have hfold := emitMap_foldl_append f tl p.1 [p.2]
    have hge : p.1.2 ≤ (emitMap p.1 f tl).1.2 := by
      rcases h2 with ⟨r, hr⟩
      rw [h1.2, hstep.1.2, hr, List.length_append]; omega
    have hrev : (emitMap g₀ f (a :: tl)).1 = (emitMap p.1 f tl).1 ∧
        (emitMap g₀ f (a :: tl)).2 = p.2 :: (emitMap p.1 f tl).2 := by
      refine ⟨hfold.1, ?_⟩
      dsimp only [emitMap, List.foldl_cons]; rw [hfold.2]; simp
    dsimp only
    rw [hrev.1, hrev.2]
    refine ⟨h1, Gates.extends_trans hstep.2.1 h2, by simp [h3],
      by rw [h4, hstep.2.2.2.1, List.length_cons]; ring, ?_, ?_⟩
    · intro w hw
      simp only [List.mem_cons] at hw
      rcases hw with rfl | hw
      · exact lt_of_lt_of_le hstep.2.2.1 hge
      · exact h5 w hw
    · intro i hi
      cases i with
      | zero =>
        simp only [List.getD_cons_zero, List.getElem_cons_zero]
        rw [Gates.val_of_extends_wf hstep.1 h2 hstep.2.2.1, hstep.2.2.2.2]
      | succ i' =>
        simp only [List.getD_cons_succ, List.getElem_cons_succ]
        exact h6 i' (by simp at hi; omega)

/-! ### Level-0 shift and level-`i` rebalance gadgets via `emitMap` -/

/-- Update a level-`0` `LevelW` under 3 one-hot wires `(sPop, sKeep, sPush)` and pushed cell
wires `(w0, w1)`. Emits `80` gates (`16 × 5`). -/
@[expose] def emitShiftLevel0 (g : Gates) (fls : ℕ) (sPop sKeep sPush w0 w1 : ℕ)
    (lw : LevelW) : Gates × LevelW :=
  let c := fun k => lw.1.getD k 0
  let r := fun k => (lw.2.getD 0 []).getD k 0
  let cntSpec : List (ℕ × ℕ × ℕ) :=
    [(c 1, c 0, fls), (c 2, c 1, c 0), (c 3, c 2, c 1),
     (c 4, c 3, c 2), (c 5, c 4, c 3), (fls, c 5, c 4)]
  let rowSpec : List (ℕ × ℕ × ℕ) :=
    [(r 2, r 0, w0), (r 3, r 1, w1), (r 4, r 2, r 0), (r 5, r 3, r 1),
     (r 6, r 4, r 2), (r 7, r 5, r 3), (r 8, r 6, r 4), (r 9, r 7, r 5),
     (r 8, r 8, r 6), (r 9, r 9, r 7)]
  let (g1, ncnt) := emitMap g (fun g₀ t => Gates.gMux3 g₀ sPop t.1 sKeep t.2.1 sPush t.2.2) cntSpec
  let (g2, nrow) := emitMap g1 (fun g₀ t => Gates.gMux3 g₀ sPop t.1 sKeep t.2.1 sPush t.2.2) rowSpec
  (g2, (ncnt, [nrow]))

/-- Count-rebalance gadget: computes `(borrow, noop, carry)` and `(lowCnt', hiCnt')`.
Emits `37` gates. -/
@[expose] def emitCntRebalance (g : Gates) (fls : ℕ) (lowCnt hiCnt : List ℕ) :
    Gates × ((ℕ × ℕ × ℕ) × (List ℕ × List ℕ)) :=
  let c := fun k => lowCnt.getD k 0
  let h := fun k => hiCnt.getD k 0
  let (g, borrow) := Gates.gOr g (c 0) (c 1)
  let (g, noop) := Gates.gOr g (c 2) (c 3)
  let (g, carry) := Gates.gOr g (c 4) (c 5)
  let (g, lc2) := Gates.gOr3 g (c 0) (c 2) (c 4)
  let (g, lc3) := Gates.gOr3 g (c 1) (c 3) (c 5)
  let hiSpec : List (ℕ × ℕ × ℕ) :=
    [(h 1, h 0, fls), (h 2, h 1, h 0), (h 3, h 2, h 1),
     (h 4, h 3, h 2), (h 5, h 4, h 3), (fls, h 5, h 4)]
  let (g, nh) := emitMap g (fun g₀ t => Gates.gMux3 g₀ borrow t.1 noop t.2.1 carry t.2.2) hiSpec
  (g, ((borrow, noop, carry), ([fls, fls, lc2, lc3, fls, fls], nh)))

/-- Cell-rebalance gadget using uniform `gMux4` over `emitMap`: `30 × 7 = 210` gates. -/
@[expose] def emitCellRebalance (g : Gates) (c0 c1 c4 c5 borrow noop carry : ℕ)
    (L H0 H1 : List ℕ) : Gates × (List ℕ × List ℕ × List ℕ) :=
  let l := fun k => L.getD k 0
  let a := fun k => H0.getD k 0
  let b := fun k => H1.getD k 0
  let lSpec : List (ℕ × ℕ × ℕ × ℕ) :=
    [(a 0, l 0, l 0, l 0), (a 1, l 1, l 1, l 1),
     (b 0, a 0, l 2, l 2), (b 1, a 1, l 3, l 3),
     (l 4, b 0, l 4, l 4), (l 5, b 1, l 5, l 5),
     (l 6, l 6, l 6, l 6), (l 7, l 7, l 7, l 7),
     (l 8, l 8, l 8, l 8), (l 9, l 9, l 9, l 9)]
  let h0Spec : List (ℕ × ℕ × ℕ × ℕ) :=
    [(a 2, a 0, l 4, l 6), (a 3, a 1, l 5, l 7),
     (a 4, a 2, a 0, a 0), (a 5, a 3, a 1, a 1),
     (a 6, a 4, a 2, a 2), (a 7, a 5, a 3, a 3),
     (a 8, a 6, a 4, a 4), (a 9, a 7, a 5, a 5),
     (a 8, a 8, a 6, a 6), (a 9, a 9, a 7, a 7)]
  let h1Spec : List (ℕ × ℕ × ℕ × ℕ) :=
    [(b 2, b 0, l 6, l 8), (b 3, b 1, l 7, l 9),
     (b 4, b 2, b 0, b 0), (b 5, b 3, b 1, b 1),
     (b 6, b 4, b 2, b 2), (b 7, b 5, b 3, b 3),
     (b 8, b 6, b 4, b 4), (b 9, b 7, b 5, b 5),
     (b 8, b 8, b 6, b 6), (b 9, b 9, b 7, b 7)]
  let (g1, nL) := emitMap g (fun g₀ t =>
    Gates.gMux4 g₀ c0 t.1 c1 t.2.1 noop t.2.2.1 carry t.2.2.2) lSpec
  let (g2, nH0) := emitMap g1 (fun g₀ t =>
    Gates.gMux4 g₀ borrow t.1 noop t.2.1 c4 t.2.2.1 c5 t.2.2.2) h0Spec
  let (g3, nH1) := emitMap g2 (fun g₀ t =>
    Gates.gMux4 g₀ borrow t.1 noop t.2.1 c4 t.2.2.1 c5 t.2.2.2) h1Spec
  (g3, (nL, nH0, nH1))

/-- Rebalance adjacent levels `low` (level `i`) and `hi` (level `i + 1`). -/
@[expose] def emitRebalanceLevel (g : Gates) (fls : ℕ) (low hi : LevelW) :
    Gates × (LevelW × LevelW) :=
  let (g1, (borrow, noop, carry), (lowCnt', hiCnt')) := emitCntRebalance g fls low.1 hi.1
  let c0 := low.1.getD 0 0; let c1 := low.1.getD 1 0
  let c4 := low.1.getD 4 0; let c5 := low.1.getD 5 0
  let B := low.2.length
  let res := (List.range B).foldl (fun acc j =>
    let (gc, (rL, rH0, rH1)) := acc
    let (gc', (nL, nH0, nH1)) := emitCellRebalance gc c0 c1 c4 c5 borrow noop carry
      (low.2.getD j []) (hi.2.getD j []) (hi.2.getD (B + j) [])
    (gc', (nL :: rL, nH0 :: rH0, nH1 :: rH1))) (g1, ([], [], []))
  (res.1, ((lowCnt', res.2.1.reverse), (hiCnt', res.2.2.1.reverse ++ res.2.2.2.reverse)))

/-- Rebalance level `lvl` and `lvl + 1` inside a half-tape wire list `hw`. -/
@[expose] def emitRebalanceHalfTape (g : Gates) (fls : ℕ) (hw : HalfW) (lvl : ℕ) :
    Gates × HalfW :=
  let (g', (low', hi')) := emitRebalanceLevel g fls (hw.getD lvl ([], []))
    (hw.getD (lvl + 1) ([], []))
  (g', hw.take lvl ++ [low', hi'] ++ hw.drop (lvl + 2))

/-- Update `headCell`, `left[0]`, and `right[0]` of a `TapeW` given 3 one-hot move wires
`(mNeg, mZero, mPos)` and 2 write-cell wires `(w0, w1)`. Emits `170` gates. -/
@[expose] def emitTapeStep0 (g : Gates) (fls : ℕ) (mNeg mZero mPos w0 w1 : ℕ) (tw : TapeW) :
    Gates × TapeW :=
  let l0 := tw.2.1.getD 0 ([], [])
  let r0 := tw.2.2.getD 0 ([], [])
  let lh0 := (l0.2.getD 0 []).getD 0 0; let lh1 := (l0.2.getD 0 []).getD 1 0
  let rh0 := (r0.2.getD 0 []).getD 0 0; let rh1 := (r0.2.getD 0 []).getD 1 0
  let (g, nh0) := Gates.gMux3 g mNeg lh0 mZero w0 mPos rh0
  let (g, nh1) := Gates.gMux3 g mNeg lh1 mZero w1 mPos rh1
  let (g, nl0) := emitShiftLevel0 g fls mNeg mZero mPos w0 w1 l0
  let (g, nr0) := emitShiftLevel0 g fls mPos mZero mNeg w0 w1 r0
  (g, ((nh0, nh1), (nl0 :: tw.2.1.drop 1, nr0 :: tw.2.2.drop 1)))

/-! ### Correctness and gate-count bounds for rebalance and tape steps -/

private theorem getD_append_left {α : Type} (l₁ l₂ : List α) (j : ℕ) (d : α) (h : j < l₁.length) :
    (l₁ ++ l₂).getD j d = l₁.getD j d := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left h, ← List.getD_eq_getElem?_getD]

private theorem getD_append_right {α : Type} (l₁ l₂ : List α) (j : ℕ) (d : α) (h : l₁.length ≤ j) :
    (l₁ ++ l₂).getD j d = l₂.getD (j - l₁.length) d := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right h, ← List.getD_eq_getElem?_getD]

private theorem getD_append_singleton_self {α : Type} (l : List α) (a d : α) :
    (l ++ [a]).getD l.length d = a := by
  rw [getD_append_right l [a] l.length d le_rfl]; simp

private theorem getD_append_singleton_eq {α : Type} (l : List α) (a d : α) {j : ℕ}
    (hj : l.length = j) : (l ++ [a]).getD j d = a := by
  subst hj; exact getD_append_singleton_self l a d

private theorem getD_mem_of_lt {α : Type} {l : List α} {k : ℕ} {d : α} (hk : k < l.length) :
    l.getD k d ∈ l := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]; exact List.getElem_mem hk

private theorem cnt_rebalance_hi_eq (cL cH : ℕ) (hcL : cL ≤ 5) (hcH1 : 1 ≤ cH) (hcH2 : cH ≤ 4)
    (c : Fin 6) :
    (if cL ≤ 1 then if c.val = 5 then false else decide (cH = c.val + 1)
     else if cL ≤ 3 then decide (cH = c.val)
     else if c.val = 0 then false else decide (cH = c.val - 1)) =
    decide ((if cL ≤ 1 then cH - 1 else if cL ≤ 3 then cH else cH + 1) = c.val) := by
  interval_cases cL <;> interval_cases cH <;> fin_cases c <;> rfl

private theorem cellRebalance_low_eq {i : ℕ} {j : Fin (2 ^ i)} (lvlL : BlockLevel i)
    (lvlH : BlockLevel (i + 1)) (hcL : lvlL.cnt ≤ 5) (s : Fin 5) (l h0 h1 : ℕ → Bool)
    (hl : ∀ q : Fin 5, (l (2 * q.val), l (2 * q.val + 1)) = lvlL.slots q j)
    (hh0 : (h0 0, h0 1) = lvlH.slots 0 ⟨j.val, by rw [pow_succ]; omega⟩)
    (hh1 : (h1 0, h1 1) = lvlH.slots 0 ⟨2 ^ i + j.val, by rw [pow_succ]; omega⟩) :
    let spec : List (Bool × Bool × Bool × Bool) :=
      [(h0 0, l 0, l 0, l 0), (h0 1, l 1, l 1, l 1), (h1 0, h0 0, l 2, l 2),
       (h1 1, h0 1, l 3, l 3), (l 4, h1 0, l 4, l 4), (l 5, h1 1, l 5, l 5),
       (l 6, l 6, l 6, l 6), (l 7, l 7, l 7, l 7), (l 8, l 8, l 8, l 8), (l 9, l 9, l 9, l 9)]
    let pick := fun t : Bool × Bool × Bool × Bool =>
      if lvlL.cnt = 0 then t.1 else if lvlL.cnt = 1 then t.2.1
      else if lvlL.cnt ≤ 3 then t.2.2.1 else t.2.2.2
    (pick (spec.getD (2 * s.val) (false, false, false, false)),
     pick (spec.getD (2 * s.val + 1) (false, false, false, false))) =
      (BlockLevel.rebalance lvlL lvlH).1.slots s j := by
  rcases lvlL with ⟨cL, sL⟩
  have hl0 := hl ⟨0, by decide⟩; have hl1 := hl ⟨1, by decide⟩; have hl2 := hl ⟨2, by decide⟩
  have hl3 := hl ⟨3, by decide⟩; have hl4 := hl ⟨4, by decide⟩
  dsimp only at hcL hl0 hl1 hl2 hl3 hl4 hh0 hh1 ⊢
  interval_cases cL <;> fin_cases s <;>
    dsimp only [BlockLevel.rebalance_eq, BlockLevel.splitBlock_eq, List.getD_cons_zero,
      List.getD_cons_succ] <;>
    first | exact hl0 | exact hl1 | exact hl2 | exact hl3 | exact hl4 | exact hh0 | exact hh1

private theorem cellRebalance_hi0_eq {i : ℕ} {j : Fin (2 ^ i)} (lvlL : BlockLevel i)
    (lvlH : BlockLevel (i + 1)) (hcL : lvlL.cnt ≤ 5) (s : Fin 5) (l h0 : ℕ → Bool)
    (hl : ∀ q : Fin 5, (l (2 * q.val), l (2 * q.val + 1)) = lvlL.slots q j)
    (hh0 : ∀ q : Fin 5, (h0 (2 * q.val), h0 (2 * q.val + 1)) =
      lvlH.slots q ⟨j.val, by rw [pow_succ]; omega⟩) :
    let spec : List (Bool × Bool × Bool × Bool) :=
      [(h0 2, h0 0, l 4, l 6), (h0 3, h0 1, l 5, l 7), (h0 4, h0 2, h0 0, h0 0),
       (h0 5, h0 3, h0 1, h0 1), (h0 6, h0 4, h0 2, h0 2), (h0 7, h0 5, h0 3, h0 3),
       (h0 8, h0 6, h0 4, h0 4), (h0 9, h0 7, h0 5, h0 5), (h0 8, h0 8, h0 6, h0 6),
       (h0 9, h0 9, h0 7, h0 7)]
    let pick := fun t : Bool × Bool × Bool × Bool =>
      if lvlL.cnt ≤ 1 then t.1 else if lvlL.cnt ≤ 3 then t.2.1
      else if lvlL.cnt = 4 then t.2.2.1 else t.2.2.2
    (pick (spec.getD (2 * s.val) (false, false, false, false)),
     pick (spec.getD (2 * s.val + 1) (false, false, false, false))) =
      (BlockLevel.rebalance lvlL lvlH).2.slots s ⟨j.val, by rw [pow_succ]; omega⟩ := by
  rcases lvlL with ⟨cL, sL⟩
  have hl2 := hl ⟨2, by decide⟩; have hl3 := hl ⟨3, by decide⟩
  have hh0_0 := hh0 ⟨0, by decide⟩; have hh0_1 := hh0 ⟨1, by decide⟩; have hh0_2 :=
    hh0 ⟨2, by decide⟩
  have hh0_3 := hh0 ⟨3, by decide⟩; have hh0_4 := hh0 ⟨4, by decide⟩
  dsimp only at hcL hl2 hl3 hh0_0 hh0_1 hh0_2 hh0_3 hh0_4 ⊢
  interval_cases cL <;> fin_cases s <;>
    simp only [BlockLevel.rebalance_eq, BlockLevel.mergeBlock_eq, j.isLt, ↓reduceDIte, ↓reduceIte,
      List.getD_cons_zero, List.getD_cons_succ, Nat.reduceEqDiff, Nat.le_refl,
      show (0 : ℕ) ≤ 1 by decide, show (2 : ℕ) ≤ 3 by decide, show ¬(2 ≤ 1) by decide,
      show ¬(3 ≤ 1) by decide, show ¬(4 ≤ 1) by decide, show ¬(4 ≤ 3) by decide,
      show ¬(5 ≤ 1) by decide, show ¬(5 ≤ 3) by decide] <;>
    (first
      | exact hl2 | exact hl3 | exact hh0_0 | exact hh0_1 | exact hh0_2 | exact hh0_3 | exact hh0_4)

private theorem cellRebalance_hi1_eq {i : ℕ} {j : Fin (2 ^ i)} (lvlL : BlockLevel i)
    (lvlH : BlockLevel (i + 1)) (hcL : lvlL.cnt ≤ 5) (s : Fin 5) (l h1 : ℕ → Bool)
    (hl : ∀ q : Fin 5, (l (2 * q.val), l (2 * q.val + 1)) = lvlL.slots q j)
    (hh1 : ∀ q : Fin 5, (h1 (2 * q.val), h1 (2 * q.val + 1)) =
      lvlH.slots q ⟨2 ^ i + j.val, by rw [pow_succ]; omega⟩) :
    let spec : List (Bool × Bool × Bool × Bool) :=
      [(h1 2, h1 0, l 6, l 8), (h1 3, h1 1, l 7, l 9), (h1 4, h1 2, h1 0, h1 0),
       (h1 5, h1 3, h1 1, h1 1), (h1 6, h1 4, h1 2, h1 2), (h1 7, h1 5, h1 3, h1 3),
       (h1 8, h1 6, h1 4, h1 4), (h1 9, h1 7, h1 5, h1 5), (h1 8, h1 8, h1 6, h1 6),
       (h1 9, h1 9, h1 7, h1 7)]
    let pick := fun t : Bool × Bool × Bool × Bool =>
      if lvlL.cnt ≤ 1 then t.1 else if lvlL.cnt ≤ 3 then t.2.1
      else if lvlL.cnt = 4 then t.2.2.1 else t.2.2.2
    (pick (spec.getD (2 * s.val) (false, false, false, false)),
     pick (spec.getD (2 * s.val + 1) (false, false, false, false))) =
      (BlockLevel.rebalance lvlL lvlH).2.slots s ⟨2 ^ i + j.val, by rw [pow_succ]; omega⟩ := by
  rcases lvlL with ⟨cL, sL⟩
  have hl3 := hl ⟨3, by decide⟩; have hl4 := hl ⟨4, by decide⟩
  have hh1_0 := hh1 ⟨0, by decide⟩; have hh1_1 := hh1 ⟨1, by decide⟩; have hh1_2 :=
    hh1 ⟨2, by decide⟩
  have hh1_3 := hh1 ⟨3, by decide⟩; have hh1_4 := hh1 ⟨4, by decide⟩
  dsimp only at hcL hl3 hl4 hh1_0 hh1_1 hh1_2 hh1_3 hh1_4 ⊢
  have hnot : ¬ (2 ^ i + j.val < 2 ^ i) := by omega
  have hsub : 2 ^ i + j.val - 2 ^ i = j.val := by omega
  interval_cases cL <;> fin_cases s <;>
    simp only [BlockLevel.rebalance_eq, BlockLevel.mergeBlock_eq, hnot, hsub, ↓reduceDIte,
      ↓reduceIte,
      List.getD_cons_zero, List.getD_cons_succ, Nat.reduceEqDiff, Nat.le_refl,
      show (0 : ℕ) ≤ 1 by decide, show (2 : ℕ) ≤ 3 by decide, show ¬(2 ≤ 1) by decide,
      show ¬(3 ≤ 1) by decide, show ¬(4 ≤ 1) by decide, show ¬(4 ≤ 3) by decide,
      show ¬(5 ≤ 1) by decide, show ¬(5 ≤ 3) by decide] <;>
    (first
      | exact hl3 | exact hl4 | exact hh1_0 | exact hh1_1 | exact hh1_2 | exact hh1_3 | exact hh1_4)

private theorem emitCellRebalance_spec {x : List Bool} {g g₀ : Gates} {i j : ℕ}
    {wBorrow wNoop wCarry : ℕ} {low hi : LevelW}
    {lvlL : BlockLevel i} {lvlH : BlockLevel (i + 1)}
    (hg : g.WF x.length) (hg₀ : g₀.WF x.length) (hextG : Gates.Extends g g₀)
    (hlow : low.Encodes g x lvlL) (hhi : hi.Encodes g x lvlH) (hcL : lvlL.cnt ≤ 5)
    (hBor_lt : wBorrow < g₀.2) (hNoop_lt : wNoop < g₀.2) (hCar_lt : wCarry < g₀.2)
    (hBor_v : g₀.val x wBorrow = decide (lvlL.cnt = 0 ∨ lvlL.cnt = 1))
    (hNoop_v : g₀.val x wNoop = decide (lvlL.cnt = 2 ∨ lvlL.cnt = 3))
    (hCar_v : g₀.val x wCarry = decide (lvlL.cnt = 4 ∨ lvlL.cnt = 5))
    (hj : j < 2 ^ i) :
    let r := emitCellRebalance g₀ (low.1.getD 0 0) (low.1.getD 1 0) (low.1.getD 4 0)
      (low.1.getD 5 0) wBorrow wNoop wCarry
      (low.2.getD j []) (hi.2.getD j []) (hi.2.getD (low.2.length + j) [])
    r.1.WF x.length ∧ Gates.Extends g₀ r.1 ∧ r.1.1.length = g₀.1.length + 210 ∧
    r.2.1.length = 10 ∧ (∀ w ∈ r.2.1, w < r.1.2) ∧
    r.2.2.1.length = 10 ∧ (∀ w ∈ r.2.2.1, w < r.1.2) ∧
    r.2.2.2.length = 10 ∧ (∀ w ∈ r.2.2.2, w < r.1.2) ∧
    (∀ s : Fin 5,
      (r.1.val x (r.2.1.getD (2 * s.val) 0), r.1.val x (r.2.1.getD (2 * s.val + 1) 0)) =
        (BlockLevel.rebalance lvlL lvlH).1.slots s ⟨j, hj⟩) ∧
    (∀ s : Fin 5,
      (r.1.val x (r.2.2.1.getD (2 * s.val) 0), r.1.val x (r.2.2.1.getD (2 * s.val + 1) 0)) =
        (BlockLevel.rebalance lvlL lvlH).2.slots s ⟨j, by rw [pow_succ]; omega⟩) ∧
    (∀ s : Fin 5,
      (r.1.val x (r.2.2.2.getD (2 * s.val) 0), r.1.val x (r.2.2.2.getD (2 * s.val + 1) 0)) =
        (BlockLevel.rebalance lvlL lvlH).2.slots s ⟨2 ^ i + j, by rw [pow_succ]; omega⟩) := by
  dsimp only [emitCellRebalance]
  have hB : low.2.length = 2 ^ i := hlow.1.2.2.1
  have hcL_w := fun k (hk : k < 6) => hlow.1.getD_cnt hk
  have hLj := fun k (hk : k < 10) => hlow.1.getD_cell hj hk
  have hH0j := fun k (hk : k < 10) => hhi.1.getD_cell (show j < 2 ^ (i +
    1) by rw [pow_succ]; omega) hk
  have hH1j := fun k (hk : k < 10) => hhi.1.getD_cell
    (show low.2.length + j < 2 ^ (i + 1) by rw [hB, pow_succ]; omega) hk
  have hleG : g.2 ≤ g₀.2 := by
    rcases hextG with ⟨rr, hrr⟩; rw [hg.2, hg₀.2, hrr, List.length_append]; omega
  let lRow := low.2.getD j []
  let h0Row := hi.2.getD j []
  let h1Row := hi.2.getD (low.2.length + j) []
  let lowSpec : List (ℕ × ℕ × ℕ × ℕ) :=
    [(h0Row.getD 0 0, lRow.getD 0 0, lRow.getD 0 0, lRow.getD 0 0),
     (h0Row.getD 1 0, lRow.getD 1 0, lRow.getD 1 0, lRow.getD 1 0),
     (h1Row.getD 0 0, h0Row.getD 0 0, lRow.getD 2 0, lRow.getD 2 0),
     (h1Row.getD 1 0, h0Row.getD 1 0, lRow.getD 3 0, lRow.getD 3 0),
     (lRow.getD 4 0, h1Row.getD 0 0, lRow.getD 4 0, lRow.getD 4 0),
     (lRow.getD 5 0, h1Row.getD 1 0, lRow.getD 5 0, lRow.getD 5 0),
     (lRow.getD 6 0, lRow.getD 6 0, lRow.getD 6 0, lRow.getD 6 0),
     (lRow.getD 7 0, lRow.getD 7 0, lRow.getD 7 0, lRow.getD 7 0),
     (lRow.getD 8 0, lRow.getD 8 0, lRow.getD 8 0, lRow.getD 8 0),
     (lRow.getD 9 0, lRow.getD 9 0, lRow.getD 9 0, lRow.getD 9 0)]
  have hmL := emitMap_spec (x := x) (K := 7) (xs := lowSpec)
    (f := fun gc t => Gates.gMux4 gc (low.1.getD 0 0) t.1 (low.1.getD 1 0) t.2.1
      wNoop t.2.2.1 wCarry t.2.2.2)
    (spec := fun t : ℕ × ℕ × ℕ × ℕ =>
      if lvlL.cnt = 0 then g.val x t.1
      else if lvlL.cnt = 1 then g.val x t.2.1
      else if lvlL.cnt ≤ 3 then g.val x t.2.2.1
      else g.val x t.2.2.2)
    hg₀ (fun gc t ht hgc hextc => by
      have hextC := Gates.extends_trans hextG hextc
      have hleC : g₀.2 ≤ gc.2 := by
        rcases hextc with ⟨rr, hrr⟩; rw [hg₀.2, hgc.2, hrr, List.length_append]; omega
      have hti : t.1 < g.2 ∧ t.2.1 < g.2 ∧ t.2.2.1 < g.2 ∧ t.2.2.2 < g.2 := by
        simp only [lowSpec, lRow, h0Row, h1Row, List.mem_cons, List.not_mem_nil, or_false] at ht
        rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          exact ⟨by (first | exact hLj _ (by omega) | exact hH0j _ (by omega)
                           | exact hH1j _ (by omega)),
                 by (first | exact hLj _ (by omega) | exact hH0j _ (by omega)
                           | exact hH1j _ (by omega)),
                 hLj _ (by omega), hLj _ (by omega)⟩
      have hm := Gates.gMux4_spec hgc
        (lt_of_lt_of_le (hcL_w 0 (by omega)) (hleG.trans hleC))
          (lt_of_lt_of_le hti.1 (hleG.trans hleC))
        (lt_of_lt_of_le (hcL_w 1 (by omega)) (hleG.trans hleC))
          (lt_of_lt_of_le hti.2.1 (hleG.trans hleC))
        (lt_of_lt_of_le hNoop_lt hleC) (lt_of_lt_of_le hti.2.2.1 (hleG.trans hleC))
        (lt_of_lt_of_le hCar_lt hleC) (lt_of_lt_of_le hti.2.2.2 (hleG.trans hleC))
      refine ⟨hm.1, hm.2.1, hm.2.2.1, hm.2.2.2.1, ?_⟩
      have hlc0 := hlow.2.1 ⟨0, by decide⟩; have hlc1 := hlow.2.1 ⟨1, by decide⟩
      dsimp only at hlc0 hlc1
      rw [hm.2.2.2.2,
        Gates.val_of_extends_wf hg hextC (hcL_w 0 (by omega)),
        Gates.val_of_extends_wf hg hextC (hcL_w 1 (by omega)),
        Gates.val_of_extends_wf hg₀ hextc hNoop_lt,
        Gates.val_of_extends_wf hg₀ hextc hCar_lt,
        Gates.val_of_extends_wf hg hextC hti.1, Gates.val_of_extends_wf hg hextC hti.2.1,
        Gates.val_of_extends_wf hg hextC hti.2.2.1, Gates.val_of_extends_wf hg hextC hti.2.2.2,
        hlc0, hlc1, hNoop_v, hCar_v]
      rcases lvlL with ⟨cL, _⟩; dsimp only at hcL ⊢; interval_cases cL <;> simp)
  have hH_mux : ∀ {gBase : Gates} (hgB : gBase.WF x.length) (hextB : Gates.Extends g₀ gBase)
      (xs : List (ℕ × ℕ × ℕ × ℕ))
      (hxs : ∀ t ∈ xs, t.1 < g.2 ∧ t.2.1 < g.2 ∧ t.2.2.1 < g.2 ∧ t.2.2.2 < g.2),
      let m := emitMap gBase (fun gc t =>
        Gates.gMux4 gc wBorrow t.1 wNoop t.2.1 (low.1.getD 4 0) t.2.2.1 (low.1.getD 5 0) t.2.2.2) xs
      m.1.WF x.length ∧ Gates.Extends gBase m.1 ∧ m.2.length = xs.length ∧
      m.1.1.length = gBase.1.length + 7 * xs.length ∧ (∀ w ∈ m.2, w < m.1.2) ∧
      (∀ (k : ℕ) (hk : k < xs.length),
        m.1.val x (m.2.getD k 0) =
          if lvlL.cnt ≤ 1 then g.val x xs[k].1
          else if lvlL.cnt ≤ 3 then g.val x xs[k].2.1
          else if lvlL.cnt = 4 then g.val x xs[k].2.2.1
          else g.val x xs[k].2.2.2) := by
    intro gBase hgB hextB xs hxs
    refine emitMap_spec (K := 7)
      (spec := fun t : ℕ × ℕ × ℕ × ℕ =>
        if lvlL.cnt ≤ 1 then g.val x t.1
        else if lvlL.cnt ≤ 3 then g.val x t.2.1
        else if lvlL.cnt = 4 then g.val x t.2.2.1
        else g.val x t.2.2.2)
      hgB fun gc t ht hgc hextc => ?_
    have hextB0 := Gates.extends_trans hextB hextc
    have hextC := Gates.extends_trans hextG hextB0
    have hleC : g₀.2 ≤ gc.2 := by
      rcases hextB0 with ⟨rr, hrr⟩; rw [hg₀.2, hgc.2, hrr, List.length_append]; omega
    have hti := hxs t ht
    have hm := Gates.gMux4_spec hgc
      (lt_of_lt_of_le hBor_lt hleC) (lt_of_lt_of_le hti.1 (hleG.trans hleC))
      (lt_of_lt_of_le hNoop_lt hleC) (lt_of_lt_of_le hti.2.1 (hleG.trans hleC))
      (lt_of_lt_of_le (hcL_w 4 (by omega)) (hleG.trans hleC))
        (lt_of_lt_of_le hti.2.2.1 (hleG.trans hleC))
      (lt_of_lt_of_le (hcL_w 5 (by omega)) (hleG.trans hleC))
        (lt_of_lt_of_le hti.2.2.2 (hleG.trans hleC))
    refine ⟨hm.1, hm.2.1, hm.2.2.1, hm.2.2.2.1, ?_⟩
    have hlc4 := hlow.2.1 ⟨4, by decide⟩; have hlc5 := hlow.2.1 ⟨5, by decide⟩
    dsimp only at hlc4 hlc5
    rw [hm.2.2.2.2,
      Gates.val_of_extends_wf hg₀ hextB0 hBor_lt,
      Gates.val_of_extends_wf hg₀ hextB0 hNoop_lt,
      Gates.val_of_extends_wf hg hextC (hcL_w 4 (by omega)),
      Gates.val_of_extends_wf hg hextC (hcL_w 5 (by omega)),
      Gates.val_of_extends_wf hg hextC hti.1, Gates.val_of_extends_wf hg hextC hti.2.1,
      Gates.val_of_extends_wf hg hextC hti.2.2.1, Gates.val_of_extends_wf hg hextC hti.2.2.2,
      hBor_v, hNoop_v, hlc4, hlc5]
    rcases lvlL with ⟨cL, _⟩; dsimp only at hcL ⊢; interval_cases cL <;> simp
  let hi0Spec : List (ℕ × ℕ × ℕ × ℕ) :=
    [(h0Row.getD 2 0, h0Row.getD 0 0, lRow.getD 4 0, lRow.getD 6 0),
     (h0Row.getD 3 0, h0Row.getD 1 0, lRow.getD 5 0, lRow.getD 7 0),
     (h0Row.getD 4 0, h0Row.getD 2 0, h0Row.getD 0 0, h0Row.getD 0 0),
     (h0Row.getD 5 0, h0Row.getD 3 0, h0Row.getD 1 0, h0Row.getD 1 0),
     (h0Row.getD 6 0, h0Row.getD 4 0, h0Row.getD 2 0, h0Row.getD 2 0),
     (h0Row.getD 7 0, h0Row.getD 5 0, h0Row.getD 3 0, h0Row.getD 3 0),
     (h0Row.getD 8 0, h0Row.getD 6 0, h0Row.getD 4 0, h0Row.getD 4 0),
     (h0Row.getD 9 0, h0Row.getD 7 0, h0Row.getD 5 0, h0Row.getD 5 0),
     (h0Row.getD 8 0, h0Row.getD 8 0, h0Row.getD 6 0, h0Row.getD 6 0),
     (h0Row.getD 9 0, h0Row.getD 9 0, h0Row.getD 7 0, h0Row.getD 7 0)]
  let hi1Spec : List (ℕ × ℕ × ℕ × ℕ) :=
    [(h1Row.getD 2 0, h1Row.getD 0 0, lRow.getD 6 0, lRow.getD 8 0),
     (h1Row.getD 3 0, h1Row.getD 1 0, lRow.getD 7 0, lRow.getD 9 0),
     (h1Row.getD 4 0, h1Row.getD 2 0, h1Row.getD 0 0, h1Row.getD 0 0),
     (h1Row.getD 5 0, h1Row.getD 3 0, h1Row.getD 1 0, h1Row.getD 1 0),
     (h1Row.getD 6 0, h1Row.getD 4 0, h1Row.getD 2 0, h1Row.getD 2 0),
     (h1Row.getD 7 0, h1Row.getD 5 0, h1Row.getD 3 0, h1Row.getD 3 0),
     (h1Row.getD 8 0, h1Row.getD 6 0, h1Row.getD 4 0, h1Row.getD 4 0),
     (h1Row.getD 9 0, h1Row.getD 7 0, h1Row.getD 5 0, h1Row.getD 5 0),
     (h1Row.getD 8 0, h1Row.getD 8 0, h1Row.getD 6 0, h1Row.getD 6 0),
     (h1Row.getD 9 0, h1Row.getD 9 0, h1Row.getD 7 0, h1Row.getD 7 0)]
  have hmH0 := hH_mux hmL.1 hmL.2.1 hi0Spec (by
    intro t ht; simp only [hi0Spec, lRow, h0Row, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact ⟨hH0j _ (by omega), hH0j _ (by omega),
             by first | exact hLj _ (by omega) | exact hH0j _ (by omega),
             by first | exact hLj _ (by omega) | exact hH0j _ (by omega)⟩)
  have hmH1 := hH_mux hmH0.1 (Gates.extends_trans hmL.2.1 hmH0.2.1) hi1Spec (by
    intro t ht; simp only [hi1Spec, lRow, h1Row, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact ⟨hH1j _ (by omega), hH1j _ (by omega),
             by first | exact hLj _ (by omega) | exact hH1j _ (by omega),
             by first | exact hLj _ (by omega) | exact hH1j _ (by omega)⟩)
  set rL := emitMap g₀ (fun gc t => Gates.gMux4 gc (low.1.getD 0 0) t.1 (low.1.getD 1 0) t.2.1
    wNoop t.2.2.1 wCarry t.2.2.2) lowSpec
  set rH0 := emitMap rL.1 (fun gc t =>
    Gates.gMux4 gc wBorrow t.1 wNoop t.2.1 (low.1.getD 4 0) t.2.2.1
      (low.1.getD 5 0) t.2.2.2) hi0Spec
  set rH1 := emitMap rH0.1 (fun gc t =>
    Gates.gMux4 gc wBorrow t.1 wNoop t.2.1 (low.1.getD 4 0) t.2.2.1
      (low.1.getD 5 0) t.2.2.2) hi1Spec
  have hge1 : rL.1.2 ≤ rH1.1.2 := by
    rcases Gates.extends_trans hmH0.2.1 hmH1.2.1 with ⟨rr, hrr⟩
    rw [hmL.1.2, hmH1.1.2, hrr, List.length_append]; omega
  have hge2 : rH0.1.2 ≤ rH1.1.2 := by
    rcases hmH1.2.1 with ⟨rr, hrr⟩; rw [hmH0.1.2, hmH1.1.2, hrr, List.length_append]; omega
  have hlenL := hmL.2.2.2.1; have hlenH0 := hmH0.2.2.2.1; have hlenH1 := hmH1.2.2.2.1
  dsimp only [lowSpec, hi0Spec, hi1Spec, List.length_cons, List.length_nil] at hlenL hlenH0 hlenH1
  refine ⟨hmH1.1, Gates.extends_trans hmL.2.1 (Gates.extends_trans hmH0.2.1 hmH1.2.1),
    by omega,
    hmL.2.2.1, fun w hw => lt_of_lt_of_le (hmL.2.2.2.2.1 w hw) hge1,
    hmH0.2.2.1, fun w hw => lt_of_lt_of_le (hmH0.2.2.2.2.1 w hw) hge2,
    hmH1.2.2.1, hmH1.2.2.2.2.1, ?_, ?_, ?_⟩
  · intro s
    have he0 := hmL.2.2.2.2.2 (2 * s.val) (by simp [lowSpec]; omega)
    have he1' := hmL.2.2.2.2.2 (2 * s.val + 1) (by simp [lowSpec]; omega)
    rw [Gates.val_of_extends_wf hmL.1 (Gates.extends_trans hmH0.2.1 hmH1.2.1)
        (hmL.2.2.2.2.1 _ (getD_mem_of_lt (by rw [hmL.2.2.1]; omega))),
      Gates.val_of_extends_wf hmL.1 (Gates.extends_trans hmH0.2.1 hmH1.2.1)
        (hmL.2.2.2.2.1 _ (getD_mem_of_lt (by rw [hmL.2.2.1]; omega))),
      he0, he1']
    have hEq := cellRebalance_low_eq (j := ⟨j, hj⟩) lvlL lvlH hcL s
      (fun k => g.val x (lRow.getD k 0)) (fun k => g.val x (h0Row.getD k 0))
      (fun k => g.val x (h1Row.getD k 0)) (fun q => hlow.2.2 ⟨j, hj⟩ q)
      (by simpa [h0Row] using hhi.2.2 ⟨j, by rw [pow_succ]; omega⟩ 0)
      (by simpa [h1Row, hB] using hhi.2.2 ⟨2 ^ i + j, by rw [pow_succ]; omega⟩ 0)
    rw [← hEq]; dsimp only [lowSpec]
    fin_cases s <;> rfl
  · intro s
    have he0 := hmH0.2.2.2.2.2 (2 * s.val) (by simp [hi0Spec]; omega)
    have he1' := hmH0.2.2.2.2.2 (2 * s.val + 1) (by simp [hi0Spec]; omega)
    rw [Gates.val_of_extends_wf hmH0.1 hmH1.2.1
        (hmH0.2.2.2.2.1 _ (getD_mem_of_lt (by rw [hmH0.2.2.1]; omega))),
      Gates.val_of_extends_wf hmH0.1 hmH1.2.1
        (hmH0.2.2.2.2.1 _ (getD_mem_of_lt (by rw [hmH0.2.2.1]; omega))),
      he0, he1']
    have hEq := cellRebalance_hi0_eq (j := ⟨j, hj⟩) lvlL lvlH hcL s
      (fun k => g.val x (lRow.getD k 0)) (fun k => g.val x (h0Row.getD k 0))
      (fun q => hlow.2.2 ⟨j, hj⟩ q)
      (fun q => hhi.2.2 ⟨j, by rw [pow_succ]; omega⟩ q)
    rw [← hEq]; dsimp only [hi0Spec]
    fin_cases s <;> rfl
  · intro s
    have he0 := hmH1.2.2.2.2.2 (2 * s.val) (by simp [hi1Spec]; omega)
    have he1' := hmH1.2.2.2.2.2 (2 * s.val + 1) (by simp [hi1Spec]; omega)
    rw [he0, he1']
    have hEq := cellRebalance_hi1_eq (j := ⟨j, hj⟩) lvlL lvlH hcL s
      (fun k => g.val x (lRow.getD k 0)) (fun k => g.val x (h1Row.getD k 0))
      (fun q => hlow.2.2 ⟨j, hj⟩ q)
      (fun q => by simpa [h1Row, hB] using hhi.2.2 ⟨2 ^ i + j, by rw [pow_succ]; omega⟩ q)
    rw [← hEq]; dsimp only [hi1Spec]
    fin_cases s <;> rfl

theorem emitRebalanceLevel_spec {x : List Bool} {g : Gates} {fls i : ℕ}
    {low hi : LevelW} {lvlL : BlockLevel i} {lvlH : BlockLevel (i + 1)}
    (hg : g.WF x.length) (hfls : fls < g.2) (hflsV : g.val x fls = false)
    (hlow : low.Encodes g x lvlL) (hhi : hi.Encodes g x lvlH)
    (hcL : lvlL.cnt ≤ 5) (hcH1 : 1 ≤ lvlH.cnt) (hcH2 : lvlH.cnt ≤ 4) :
    let res := emitRebalanceLevel g fls low hi
    res.1.WF x.length ∧ Gates.Extends g res.1 ∧
    res.1.1.length = g.1.length + 37 + 210 * 2 ^ i ∧
    res.2.1.Encodes res.1 x (BlockLevel.rebalance lvlL lvlH).1 ∧
    res.2.2.Encodes res.1 x (BlockLevel.rebalance lvlL lvlH).2 := by
  dsimp only [emitRebalanceLevel]
  -- Step 1: `emitCntRebalance` correctness and exact gate count `37`.
  have hcL_w := fun k (hk : k < 6) => hlow.1.getD_cnt hk
  have hcH_w := fun k (hk : k < 6) => hhi.1.getD_cnt hk
  dsimp only [emitCntRebalance]
  have hb1 := Gates.gOr_spec hg (hcL_w 0 (by omega)) (hcL_w 1 (by omega))
  set gB := (Gates.gOr g (low.1.getD 0 0) (low.1.getD 1 0)).1
  set wBorrow := (Gates.gOr g (low.1.getD 0 0) (low.1.getD 1 0)).2
  have hlt1 : g.2 ≤ gB.2 := by rw [hg.2, hb1.1.2, hb1.2.2.2.1]; omega
  have hb2 := Gates.gOr_spec hb1.1 (lt_of_lt_of_le (hcL_w 2 (by omega)) hlt1)
    (lt_of_lt_of_le (hcL_w 3 (by omega)) hlt1)
  set gN := (Gates.gOr gB (low.1.getD 2 0) (low.1.getD 3 0)).1
  set wNoop := (Gates.gOr gB (low.1.getD 2 0) (low.1.getD 3 0)).2
  have hlt2 : gB.2 ≤ gN.2 := by rw [hb1.1.2, hb2.1.2, hb2.2.2.2.1]; omega
  have hb3 := Gates.gOr_spec hb2.1 (lt_of_lt_of_le (hcL_w 4 (by omega)) (hlt1.trans hlt2))
    (lt_of_lt_of_le (hcL_w 5 (by omega)) (hlt1.trans hlt2))
  set gC := (Gates.gOr gN (low.1.getD 4 0) (low.1.getD 5 0)).1
  set wCarry := (Gates.gOr gN (low.1.getD 4 0) (low.1.getD 5 0)).2
  have hlt3 : gN.2 ≤ gC.2 := by rw [hb2.1.2, hb3.1.2, hb3.2.2.2.1]; omega
  have hb4 := Gates.gOr3_spec hb3.1
    (lt_of_lt_of_le (hcL_w 0 (by omega)) (hlt1.trans (hlt2.trans hlt3)))
    (lt_of_lt_of_le (hcL_w 2 (by omega)) (hlt1.trans (hlt2.trans hlt3)))
    (lt_of_lt_of_le (hcL_w 4 (by omega)) (hlt1.trans (hlt2.trans hlt3)))
  set gL2 := (Gates.gOr3 gC (low.1.getD 0 0) (low.1.getD 2 0) (low.1.getD 4 0)).1
  set wL2 := (Gates.gOr3 gC (low.1.getD 0 0) (low.1.getD 2 0) (low.1.getD 4 0)).2
  have hlt4 : gC.2 ≤ gL2.2 := by rw [hb3.1.2, hb4.1.2, hb4.2.2.2.1]; omega
  have hb5 := Gates.gOr3_spec hb4.1
    (lt_of_lt_of_le (hcL_w 1 (by omega)) (hlt1.trans (hlt2.trans (hlt3.trans hlt4))))
    (lt_of_lt_of_le (hcL_w 3 (by omega)) (hlt1.trans (hlt2.trans (hlt3.trans hlt4))))
    (lt_of_lt_of_le (hcL_w 5 (by omega)) (hlt1.trans (hlt2.trans (hlt3.trans hlt4))))
  set gL3 := (Gates.gOr3 gL2 (low.1.getD 1 0) (low.1.getD 3 0) (low.1.getD 5 0)).1
  set wL3 := (Gates.gOr3 gL2 (low.1.getD 1 0) (low.1.getD 3 0) (low.1.getD 5 0)).2
  have hlt5 : gL2.2 ≤ gL3.2 := by rw [hb4.1.2, hb5.1.2, hb5.2.2.2.1]; omega
  have he12 := Gates.extends_trans hb1.2.1 hb2.2.1
  have he13 := Gates.extends_trans he12 hb3.2.1
  have he14 := Gates.extends_trans he13 hb4.2.1
  have he15 := Gates.extends_trans he14 hb5.2.1
  have hle5 : g.2 ≤ gL3.2 := hlt1.trans (hlt2.trans (hlt3.trans (hlt4.trans hlt5)))
  have hBor_lt : wBorrow < gL3.2 :=
    lt_of_lt_of_le hb1.2.2.1 (hlt2.trans (hlt3.trans (hlt4.trans hlt5)))
  have hNoop_lt : wNoop < gL3.2 := lt_of_lt_of_le hb2.2.2.1 (hlt3.trans (hlt4.trans hlt5))
  have hCar_lt : wCarry < gL3.2 := lt_of_lt_of_le hb3.2.2.1 (hlt4.trans hlt5)
  have hBor_v : gL3.val x wBorrow = decide (lvlL.cnt = 0 ∨ lvlL.cnt = 1) := by
    rw [Gates.val_of_extends_wf hb1.1 (Gates.extends_trans hb2.2.1 (Gates.extends_trans hb3.2.1
      (Gates.extends_trans hb4.2.1 hb5.2.1))) hb1.2.2.1, hb1.2.2.2.2]
    have h0 := hlow.2.1 ⟨0, by decide⟩; have h1 := hlow.2.1 ⟨1, by decide⟩
    dsimp only at h0 h1; rw [h0, h1]; simp
  have hNoop_v : gL3.val x wNoop = decide (lvlL.cnt = 2 ∨ lvlL.cnt = 3) := by
    rw [Gates.val_of_extends_wf hb2.1 (Gates.extends_trans hb3.2.1
      (Gates.extends_trans hb4.2.1 hb5.2.1)) hb2.2.2.1, hb2.2.2.2.2,
      Gates.val_of_extends_wf hg hb1.2.1 (hcL_w 2 (by omega)),
      Gates.val_of_extends_wf hg hb1.2.1 (hcL_w 3 (by omega))]
    have h2 := hlow.2.1 ⟨2, by decide⟩; have h3 := hlow.2.1 ⟨3, by decide⟩
    dsimp only at h2 h3; rw [h2, h3]; simp
  have hCar_v : gL3.val x wCarry = decide (lvlL.cnt = 4 ∨ lvlL.cnt = 5) := by
    rw [Gates.val_of_extends_wf hb3.1 (Gates.extends_trans hb4.2.1 hb5.2.1) hb3.2.2.1,
      hb3.2.2.2.2, Gates.val_of_extends_wf hg he12 (hcL_w 4 (by omega)),
      Gates.val_of_extends_wf hg he12 (hcL_w 5 (by omega))]
    have h4 := hlow.2.1 ⟨4, by decide⟩; have h5 := hlow.2.1 ⟨5, by decide⟩
    dsimp only at h4 h5; rw [h4, h5]; simp
  have hL2_v : gL3.val x wL2 = decide (lvlL.cnt = 0 ∨ lvlL.cnt = 2 ∨ lvlL.cnt = 4) := by
    rw [Gates.val_of_extends_wf hb4.1 hb5.2.1 hb4.2.2.1, hb4.2.2.2.2,
      Gates.val_of_extends_wf hg he13 (hcL_w 0 (by omega)),
      Gates.val_of_extends_wf hg he13 (hcL_w 2 (by omega)),
      Gates.val_of_extends_wf hg he13 (hcL_w 4 (by omega))]
    have h0 := hlow.2.1 ⟨0, by decide⟩; have h2 := hlow.2.1 ⟨2, by decide⟩
    have h4 := hlow.2.1 ⟨4, by decide⟩
    dsimp only at h0 h2 h4; rw [h0, h2, h4]; simp [Bool.or_assoc]
  have hL3_v : gL3.val x wL3 = decide (lvlL.cnt = 1 ∨ lvlL.cnt = 3 ∨ lvlL.cnt = 5) := by
    rw [hb5.2.2.2.2, Gates.val_of_extends_wf hg he14 (hcL_w 1 (by omega)),
      Gates.val_of_extends_wf hg he14 (hcL_w 3 (by omega)),
      Gates.val_of_extends_wf hg he14 (hcL_w 5 (by omega))]
    have h1 := hlow.2.1 ⟨1, by decide⟩; have h3 := hlow.2.1 ⟨3, by decide⟩
    have h5 := hlow.2.1 ⟨5, by decide⟩
    dsimp only at h1 h3 h5; rw [h1, h3, h5]; simp [Bool.or_assoc]
  let hiCntSpec : List (ℕ × ℕ × ℕ) :=
    [(hi.1.getD 1 0, hi.1.getD 0 0, fls), (hi.1.getD 2 0, hi.1.getD 1 0, hi.1.getD 0 0),
     (hi.1.getD 3 0, hi.1.getD 2 0, hi.1.getD 1 0), (hi.1.getD 4 0, hi.1.getD 3 0, hi.1.getD 2 0),
     (hi.1.getD 5 0, hi.1.getD 4 0, hi.1.getD 3 0), (fls, hi.1.getD 5 0, hi.1.getD 4 0)]
  have hhiCnt := emitMap_spec (x := x) (K := 5) (xs := hiCntSpec)
    (f := fun g₀ t => Gates.gMux3 g₀ wBorrow t.1 wNoop t.2.1 wCarry t.2.2)
    (spec := fun t : ℕ × ℕ × ℕ =>
      if lvlL.cnt ≤ 1 then g.val x t.1
      else if lvlL.cnt ≤ 3 then g.val x t.2.1
      else g.val x t.2.2)
    hb5.1 (fun g₀ t ht hg₀ hext₀ => by
      have hext := Gates.extends_trans he15 hext₀
      have hle0 : gL3.2 ≤ g₀.2 := by
        rcases hext₀ with ⟨rr, hrr⟩; rw [hb5.1.2, hg₀.2, hrr, List.length_append]; omega
      have hti : t.1 < g.2 ∧ t.2.1 < g.2 ∧ t.2.2 < g.2 := by
        simp only [hiCntSpec, List.mem_cons, List.not_mem_nil, or_false] at ht
        rcases ht with rfl | rfl | rfl | rfl | rfl | rfl <;>
          exact ⟨by first | exact hfls | exact hcH_w _ (by omega),
                 hcH_w _ (by omega),
                 by first | exact hfls | exact hcH_w _ (by omega)⟩
      have hm := Gates.gMux3_spec hg₀ (lt_of_lt_of_le hBor_lt hle0)
        (lt_of_lt_of_le hti.1 (hle5.trans hle0))
        (lt_of_lt_of_le hNoop_lt hle0) (lt_of_lt_of_le hti.2.1 (hle5.trans hle0))
        (lt_of_lt_of_le hCar_lt hle0) (lt_of_lt_of_le hti.2.2 (hle5.trans hle0))
      refine ⟨hm.1, hm.2.1, hm.2.2.1, hm.2.2.2.1, ?_⟩
      rw [hm.2.2.2.2,
        Gates.val_of_extends_wf hb5.1 hext₀ hBor_lt,
        Gates.val_of_extends_wf hb5.1 hext₀ hNoop_lt,
        Gates.val_of_extends_wf hb5.1 hext₀ hCar_lt,
        Gates.val_of_extends_wf hg hext hti.1,
        Gates.val_of_extends_wf hg hext hti.2.1,
        Gates.val_of_extends_wf hg hext hti.2.2, hBor_v, hNoop_v, hCar_v]
      rcases lvlL with ⟨cL, sL⟩; dsimp only at hcL ⊢; interval_cases cL <;> simp)
  set g1 :=
    (emitMap gL3 (fun g₀ t => Gates.gMux3 g₀ wBorrow t.1 wNoop t.2.1 wCarry t.2.2) hiCntSpec).1
  set hiCnt' :=
    (emitMap gL3 (fun g₀ t => Gates.gMux3 g₀ wBorrow t.1 wNoop t.2.1 wCarry t.2.2) hiCntSpec).2
  have he1 := Gates.extends_trans he15 hhiCnt.2.1
  have hle_g1 : gL3.2 ≤ g1.2 := by
    rcases hhiCnt.2.1 with ⟨rr, hrr⟩; rw [hb5.1.2, hhiCnt.1.2, hrr, List.length_append]; omega
  -- Step 2: fold over `j ∈ List.range (2 ^ i)` using `emitCellRebalance_spec` (210 gates per step).
  have hB : low.2.length = 2 ^ i := hlow.1.2.2.1
  have hcell_step : ∀ (g₀ : Gates) (j : ℕ) (hj : j < 2 ^ i), g₀.WF x.length → Gates.Extends g1 g₀ →
      let r := emitCellRebalance g₀ (low.1.getD 0 0) (low.1.getD 1 0) (low.1.getD 4 0)
        (low.1.getD 5 0) wBorrow wNoop wCarry
        (low.2.getD j []) (hi.2.getD j []) (hi.2.getD (low.2.length + j) [])
      r.1.WF x.length ∧ Gates.Extends g₀ r.1 ∧ r.1.1.length = g₀.1.length + 210 ∧
      r.2.1.length = 10 ∧ (∀ w ∈ r.2.1, w < r.1.2) ∧
      r.2.2.1.length = 10 ∧ (∀ w ∈ r.2.2.1, w < r.1.2) ∧
      r.2.2.2.length = 10 ∧ (∀ w ∈ r.2.2.2, w < r.1.2) ∧
      (∀ s : Fin 5,
        (r.1.val x (r.2.1.getD (2 * s.val) 0), r.1.val x (r.2.1.getD (2 * s.val + 1) 0)) =
          (BlockLevel.rebalance lvlL lvlH).1.slots s ⟨j, hj⟩) ∧
      (∀ s : Fin 5,
        (r.1.val x (r.2.2.1.getD (2 * s.val) 0), r.1.val x (r.2.2.1.getD (2 * s.val + 1) 0)) =
          (BlockLevel.rebalance lvlL lvlH).2.slots s ⟨j, by rw [pow_succ]; omega⟩) ∧
      (∀ s : Fin 5,
        (r.1.val x (r.2.2.2.getD (2 * s.val) 0), r.1.val x (r.2.2.2.getD (2 * s.val + 1) 0)) =
          (BlockLevel.rebalance lvlL lvlH).2.slots s ⟨2 ^ i + j, by rw [pow_succ]; omega⟩) := by
    intro g₀ j hj hg₀ hext₀
    have hextL3 := Gates.extends_trans hhiCnt.2.1 hext₀
    have hleL3 : gL3.2 ≤ g₀.2 := by
      rcases hextL3 with ⟨rr, hrr⟩; rw [hb5.1.2, hg₀.2, hrr, List.length_append]; omega
    exact emitCellRebalance_spec hg hg₀ (Gates.extends_trans he1 hext₀) hlow hhi hcL
      (lt_of_lt_of_le hBor_lt hleL3) (lt_of_lt_of_le hNoop_lt hleL3) (lt_of_lt_of_le hCar_lt hleL3)
      (by rw [Gates.val_of_extends_wf hb5.1 hextL3 hBor_lt, hBor_v])
      (by rw [Gates.val_of_extends_wf hb5.1 hextL3 hNoop_lt, hNoop_v])
      (by rw [Gates.val_of_extends_wf hb5.1 hextL3 hCar_lt, hCar_v]) hj
  -- Fold induction over `List.range m` for `m ≤ 2 ^ i`:
  have hfold : ∀ (m : ℕ) (hm : m ≤ 2 ^ i),
      let res := (List.range m).foldl (fun acc j =>
        let (gc, (rL, rH0, rH1)) := acc
        let (gc', (nL, nH0, nH1)) := emitCellRebalance gc (low.1.getD 0 0) (low.1.getD 1 0)
          (low.1.getD 4 0) (low.1.getD 5 0) wBorrow wNoop wCarry
          (low.2.getD j []) (hi.2.getD j []) (hi.2.getD (low.2.length + j) [])
        (gc', (nL :: rL, nH0 :: rH0, nH1 :: rH1))) (g1, ([], [], []))
      res.1.WF x.length ∧ Gates.Extends g1 res.1 ∧ res.1.1.length = g1.1.length + 210 * m ∧
      res.2.1.length = m ∧ res.2.2.1.length = m ∧ res.2.2.2.length = m ∧
      (∀ row ∈ res.2.1, row.length = 10 ∧ ∀ w ∈ row, w < res.1.2) ∧
      (∀ row ∈ res.2.2.1, row.length = 10 ∧ ∀ w ∈ row, w < res.1.2) ∧
      (∀ row ∈ res.2.2.2, row.length = 10 ∧ ∀ w ∈ row, w < res.1.2) ∧
      (∀ j (hj : j < m) (s : Fin 5),
        let row := res.2.1.reverse.getD j []
        (res.1.val x (row.getD (2 * s.val) 0), res.1.val x (row.getD (2 * s.val + 1) 0)) =
          (BlockLevel.rebalance lvlL lvlH).1.slots s ⟨j, by omega⟩) ∧
      (∀ j (hj : j < m) (s : Fin 5),
        let row := res.2.2.1.reverse.getD j []
        (res.1.val x (row.getD (2 * s.val) 0), res.1.val x (row.getD (2 * s.val + 1) 0)) =
          (BlockLevel.rebalance lvlL lvlH).2.slots s ⟨j, by rw [pow_succ]; omega⟩) ∧
      (∀ j (hj : j < m) (s : Fin 5),
        let row := res.2.2.2.reverse.getD j []
        (res.1.val x (row.getD (2 * s.val) 0), res.1.val x (row.getD (2 * s.val + 1) 0)) =
          (BlockLevel.rebalance lvlL lvlH).2.slots s ⟨2 ^ i + j, by rw [pow_succ]; omega⟩) := by
    intro m
    induction m with
    | zero =>
      intro _; exact ⟨hhiCnt.1, Gates.extends_refl g1, by simp, rfl, rfl, rfl,
        by simp, by simp, by simp, fun _ h => by omega, fun _ h => by omega, fun _ h => by omega⟩
    | succ m ih =>
      intro hm
      obtain ⟨hW, hE, hG, hLlen, hH0len, hH1len, hLrow, hH0row, hH1row, hLval, hH0val, hH1val⟩ :=
        ih (by omega)
      dsimp only
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      revert hW hE hG hLlen hH0len hH1len hLrow hH0row hH1row hLval hH0val hH1val
      generalize (List.range m).foldl (fun acc j =>
        let (gc, (rL, rH0, rH1)) := acc
        let (gc', (nL, nH0, nH1)) := emitCellRebalance gc (low.1.getD 0 0) (low.1.getD 1 0)
          (low.1.getD 4 0) (low.1.getD 5 0) wBorrow wNoop wCarry
          (low.2.getD j []) (hi.2.getD j []) (hi.2.getD (low.2.length + j) [])
        (gc', (nL :: rL, nH0 :: rH0, nH1 :: rH1))) (g1, ([], [], [])) = prev
      intro hW hE hG hLlen hH0len hH1len hLrow hH0row hH1row hLval hH0val hH1val
      dsimp only
      have hst := hcell_step prev.1 m (by omega) hW hE
      have hgeM : ∀ {ga gb : Gates}, ga.WF x.length → gb.WF x.length → Gates.Extends ga gb →
          ga.2 ≤ gb.2 := fun hw1 hw2 ⟨rr, hrr⟩ => by
        rw [hw1.2, hw2.2, hrr, List.length_append]; omega
      have hle_m := hgeM hW hst.1 hst.2.1
      refine ⟨hst.1, Gates.extends_trans hE hst.2.1, by rw [hst.2.2.1, hG]; omega,
        by rw [List.length_cons, hLlen], by rw [List.length_cons, hH0len],
        by rw [List.length_cons, hH1len],
        ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro row hr; simp only [List.mem_cons] at hr; rcases hr with rfl | hr
        · exact ⟨hst.2.2.2.1, hst.2.2.2.2.1⟩
        · exact ⟨(hLrow row hr).1, fun w hw => lt_of_lt_of_le ((hLrow row hr).2 w hw) hle_m⟩
      · intro row hr; simp only [List.mem_cons] at hr; rcases hr with rfl | hr
        · exact ⟨hst.2.2.2.2.2.1, hst.2.2.2.2.2.2.1⟩
        · exact ⟨(hH0row row hr).1, fun w hw => lt_of_lt_of_le ((hH0row row hr).2 w hw) hle_m⟩
      · intro row hr; simp only [List.mem_cons] at hr; rcases hr with rfl | hr
        · exact ⟨hst.2.2.2.2.2.2.2.1, hst.2.2.2.2.2.2.2.2.1⟩
        · exact ⟨(hH1row row hr).1, fun w hw => lt_of_lt_of_le ((hH1row row hr).2 w hw) hle_m⟩
      · intro j hj s
        simp only [List.reverse_cons]
        by_cases hjm : j < m
        · rw [getD_append_left _ _ _ _ (by rw [List.length_reverse, hLlen]; exact hjm)]
          have hmem : prev.2.1.reverse.getD j [] ∈ prev.2.1 :=
            List.mem_reverse.mp (getD_mem_of_lt (by rw [List.length_reverse, hLlen]; exact hjm))
          rw [Gates.val_of_extends_wf hW hst.2.1
              ((hLrow _ hmem).2 _ (getD_mem_of_lt (by rw [(hLrow _ hmem).1]; omega))),
            Gates.val_of_extends_wf hW hst.2.1
              ((hLrow _ hmem).2 _ (getD_mem_of_lt (by rw [(hLrow _ hmem).1]; omega)))]
          exact hLval j hjm s
        · have hjeq : j = m := by omega
          subst hjeq; rw [getD_append_singleton_eq _ _ _ (by rw [List.length_reverse, hLlen])]
          exact hst.2.2.2.2.2.2.2.2.2.1 s
      · intro j hj s
        simp only [List.reverse_cons]
        by_cases hjm : j < m
        · rw [getD_append_left _ _ _ _ (by rw [List.length_reverse, hH0len]; exact hjm)]
          have hmem : prev.2.2.1.reverse.getD j [] ∈ prev.2.2.1 :=
            List.mem_reverse.mp (getD_mem_of_lt (by rw [List.length_reverse, hH0len]; exact hjm))
          rw [Gates.val_of_extends_wf hW hst.2.1
              ((hH0row _ hmem).2 _ (getD_mem_of_lt (by rw [(hH0row _ hmem).1]; omega))),
            Gates.val_of_extends_wf hW hst.2.1
              ((hH0row _ hmem).2 _ (getD_mem_of_lt (by rw [(hH0row _ hmem).1]; omega)))]
          exact hH0val j hjm s
        · have hjeq : j = m := by omega
          subst hjeq; rw [getD_append_singleton_eq _ _ _ (by rw [List.length_reverse, hH0len])]
          exact hst.2.2.2.2.2.2.2.2.2.2.1 s
      · intro j hj s
        simp only [List.reverse_cons]
        by_cases hjm : j < m
        · rw [getD_append_left _ _ _ _ (by rw [List.length_reverse, hH1len]; exact hjm)]
          have hmem : prev.2.2.2.reverse.getD j [] ∈ prev.2.2.2 :=
            List.mem_reverse.mp (getD_mem_of_lt (by rw [List.length_reverse, hH1len]; exact hjm))
          rw [Gates.val_of_extends_wf hW hst.2.1
              ((hH1row _ hmem).2 _ (getD_mem_of_lt (by rw [(hH1row _ hmem).1]; omega))),
            Gates.val_of_extends_wf hW hst.2.1
              ((hH1row _ hmem).2 _ (getD_mem_of_lt (by rw [(hH1row _ hmem).1]; omega)))]
          exact hH1val j hjm s
        · have hjeq : j = m := by omega
          subst hjeq; rw [getD_append_singleton_eq _ _ _ (by rw [List.length_reverse, hH1len])]
          exact hst.2.2.2.2.2.2.2.2.2.2.2 s
  obtain ⟨hW, hE, hG, hLlen, hH0len, hH1len, hLrow, hH0row, hH1row, hLval, hH0val, hH1val⟩ :=
    hfold (2 ^ i) le_rfl
  rw [hB] at hW hE hG hLlen hH0len hH1len hLrow hH0row hH1row hLval hH0val hH1val ⊢
  revert hW hE hG hLlen hH0len hH1len hLrow hH0row hH1row hLval hH0val hH1val
  generalize (List.range (2 ^ i)).foldl (fun acc j =>
    let (gc, (rL, rH0, rH1)) := acc
    let (gc', (nL, nH0, nH1)) := emitCellRebalance gc (low.1.getD 0 0) (low.1.getD 1 0)
      (low.1.getD 4 0) (low.1.getD 5 0) wBorrow wNoop wCarry
      (low.2.getD j []) (hi.2.getD j []) (hi.2.getD (2 ^ i + j) [])
    (gc', (nL :: rL, nH0 :: rH0, nH1 :: rH1))) (g1, ([], [], [])) = fin
  intro hW hE hG hLlen hH0len hH1len hLrow hH0row hH1row hLval hH0val hH1val
  have hle_fin : g1.2 ≤ fin.1.2 := by
    have hg1 : g1.2 = x.length + g1.1.length := hhiCnt.1.2
    rw [hg1, hW.2, hG]; omega
  have hle_gL3 : gL3.2 ≤ fin.1.2 := hle_g1.trans hle_fin
  have hle_g : g.2 ≤ fin.1.2 := hle5.trans hle_gL3
  refine ⟨hW, Gates.extends_trans he1 hE,
    by have hlen : hiCntSpec.length = 6 := rfl
       have hg1l : g1.1.length = gL3.1.length + 5 * hiCntSpec.length := hhiCnt.2.2.2.1
       rw [hG, hg1l, hlen, hb5.2.2.2.1, hb4.2.2.2.1, hb3.2.2.2.1, hb2.2.2.2.1, hb1.2.2.2.1],
    ?_, ?_⟩
  · refine ⟨⟨by simp, ?_, by rw [List.length_reverse, hLlen],
        fun row hr => hLrow row (List.mem_reverse.mp hr)⟩,
      fun c => ?_, fun j s => hLval j.val j.isLt s⟩
    · intro w hw; simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl | rfl | rfl | rfl <;>
        (first
          | exact lt_of_lt_of_le hfls hle_g
          | exact lt_of_lt_of_le (lt_of_lt_of_le hb4.2.2.1 hlt5) hle_gL3
          | exact lt_of_lt_of_le hb5.2.2.1 hle_gL3)
    · rw [Gates.val_of_extends_wf hb5.1 (Gates.extends_trans hhiCnt.2.1 hE) (by
        fin_cases c <;> dsimp only <;> simp only [List.getD_cons_zero, List.getD_cons_succ] <;>
          (first | exact lt_of_lt_of_le hfls hle5
                 | exact lt_of_lt_of_le hb4.2.2.1 hlt5 | exact hb5.2.2.1))]
      have hflsL3 : gL3.val x fls = false := by rw [Gates.val_of_extends_wf hg he15 hfls, hflsV]
      rcases lvlL with ⟨cL, sL⟩; dsimp only at hcL hL2_v hL3_v ⊢
      fin_cases c
      · dsimp only; rw [List.getD_cons_zero, hflsL3]; interval_cases cL <;> rfl
      · dsimp only; rw [List.getD_cons_succ, List.getD_cons_zero, hflsL3]; interval_cases cL <;> rfl
      · dsimp only; rw [List.getD_cons_succ, List.getD_cons_succ, List.getD_cons_zero,
        hL2_v]; interval_cases cL <;> rfl
      · dsimp only; rw [List.getD_cons_succ, List.getD_cons_succ, List.getD_cons_succ,
        List.getD_cons_zero, hL3_v]; interval_cases cL <;> rfl
      · dsimp only; rw [List.getD_cons_succ, List.getD_cons_succ, List.getD_cons_succ,
        List.getD_cons_succ, List.getD_cons_zero, hflsL3]; interval_cases cL <;> rfl
      · dsimp only; rw [List.getD_cons_succ, List.getD_cons_succ, List.getD_cons_succ,
        List.getD_cons_succ, List.getD_cons_succ, List.getD_cons_zero,
          hflsL3]; interval_cases cL <;> rfl
  · refine ⟨⟨hhiCnt.2.2.1, fun w hw => lt_of_lt_of_le (hhiCnt.2.2.2.2.1 w hw) hle_fin,
      by rw [List.length_append, List.length_reverse, List.length_reverse, hH0len, hH1len,
        pow_succ]; omega,
      fun row hr => ?_⟩,
      fun c => ?_, fun j s => ?_⟩
    · rcases List.mem_append.mp hr with hr | hr
      · exact hH0row row (List.mem_reverse.mp hr)
      · exact hH1row row (List.mem_reverse.mp hr)
    · rw [Gates.val_of_extends_wf hhiCnt.1 hE
        (hhiCnt.2.2.2.2.1 _ (getD_mem_of_lt (by rw [hhiCnt.2.2.1]; exact c.isLt)))]
      rw [hhiCnt.2.2.2.2.2 c.val (by simp [hiCntSpec])]
      have hcH_eq := fun q : Fin 6 => hhi.2.1 q
      have hh0 := hcH_eq ⟨0, by decide⟩; have hh1 := hcH_eq ⟨1, by decide⟩
      have hh2 := hcH_eq ⟨2, by decide⟩; have hh3 := hcH_eq ⟨3, by decide⟩
      have hh4 := hcH_eq ⟨4, by decide⟩; have hh5 := hcH_eq ⟨5, by decide⟩
      dsimp only at hh0 hh1 hh2 hh3 hh4 hh5
      have hcntEq : (BlockLevel.rebalance lvlL lvlH).2.cnt =
          if lvlL.cnt ≤ 1 then lvlH.cnt - 1
          else if lvlL.cnt ≤ 3 then lvlH.cnt else lvlH.cnt + 1 := by
        rcases lvlL with ⟨cL, _⟩; dsimp only at hcL ⊢; interval_cases cL <;> rfl
      rw [hcntEq, ← cnt_rebalance_hi_eq lvlL.cnt lvlH.cnt hcL hcH1 hcH2 c]
      fin_cases c <;>
        dsimp only [hiCntSpec, List.getElem_cons_zero, List.getElem_cons_succ] <;>
        simp only [hflsV, hh0, hh1, hh2, hh3, hh4, hh5, ↓reduceIte, Nat.reduceEqDiff]
    · dsimp only
      by_cases hj : j.val < 2 ^ i
      · rw [getD_append_left _ _ _ _ (by rw [List.length_reverse, hH0len]; exact hj)]
        exact hH0val j.val hj s
      · rw [getD_append_right _ _ _ _ (by rw [List.length_reverse, hH0len]; omega)]
        rw [List.length_reverse, hH0len]
        have hp : 2 ^ (i + 1) = 2 ^ i * 2 := pow_succ 2 i
        have hlt2 : j.val - 2 ^ i < 2 ^ i := by have := j.isLt; omega
        have heq : (⟨2 ^ i + (j.val - 2 ^ i), by omega⟩ : Fin (2 ^ (i + 1))) = j := by
          apply Fin.ext; dsimp; omega
        simpa only [heq] using hH1val (j.val - 2 ^ i) hlt2 s

theorem emitMap_eq {α : Type} (g : Gates) (f : Gates → α → Gates × ℕ) (xs : List α) :
    emitMap g f xs =
      let res := xs.foldl (fun acc a =>
        let (g', w) := f acc.1 a
        (g', w :: acc.2)) (g, [])
      (res.1, res.2.reverse) := rfl

theorem emitShiftLevel0_eq (g : Gates) (fls : ℕ) (sPop sKeep sPush w0 w1 : ℕ)
    (lw : LevelW) :
    emitShiftLevel0 g fls sPop sKeep sPush w0 w1 lw =
      let c := fun k => lw.1.getD k 0
      let r := fun k => (lw.2.getD 0 []).getD k 0
      let cntSpec : List (ℕ × ℕ × ℕ) :=
        [(c 1, c 0, fls), (c 2, c 1, c 0), (c 3, c 2, c 1),
         (c 4, c 3, c 2), (c 5, c 4, c 3), (fls, c 5, c 4)]
      let rowSpec : List (ℕ × ℕ × ℕ) :=
        [(r 2, r 0, w0), (r 3, r 1, w1), (r 4, r 2, r 0), (r 5, r 3, r 1),
         (r 6, r 4, r 2), (r 7, r 5, r 3), (r 8, r 6, r 4), (r 9, r 7, r 5),
         (r 8, r 8, r 6), (r 9, r 9, r 7)]
      let (g1, ncnt) := emitMap g
        (fun g₀ t => Gates.gMux3 g₀ sPop t.1 sKeep t.2.1 sPush t.2.2) cntSpec
      let (g2, nrow) := emitMap g1
        (fun g₀ t => Gates.gMux3 g₀ sPop t.1 sKeep t.2.1 sPush t.2.2) rowSpec
      (g2, (ncnt, [nrow])) := rfl

theorem emitCntRebalance_eq (g : Gates) (fls : ℕ) (lowCnt hiCnt : List ℕ) :
    emitCntRebalance g fls lowCnt hiCnt =
      let c := fun k => lowCnt.getD k 0
      let h := fun k => hiCnt.getD k 0
      let (g, borrow) := Gates.gOr g (c 0) (c 1)
      let (g, noop) := Gates.gOr g (c 2) (c 3)
      let (g, carry) := Gates.gOr g (c 4) (c 5)
      let (g, lc2) := Gates.gOr3 g (c 0) (c 2) (c 4)
      let (g, lc3) := Gates.gOr3 g (c 1) (c 3) (c 5)
      let hiSpec : List (ℕ × ℕ × ℕ) :=
        [(h 1, h 0, fls), (h 2, h 1, h 0), (h 3, h 2, h 1),
         (h 4, h 3, h 2), (h 5, h 4, h 3), (fls, h 5, h 4)]
      let (g, nh) := emitMap g (fun g₀ t => Gates.gMux3 g₀ borrow t.1 noop t.2.1 carry t.2.2) hiSpec
      (g, ((borrow, noop, carry), ([fls, fls, lc2, lc3, fls, fls], nh))) := rfl

theorem emitCellRebalance_eq (g : Gates) (c0 c1 c4 c5 borrow noop carry : ℕ)
    (L H0 H1 : List ℕ) :
    emitCellRebalance g c0 c1 c4 c5 borrow noop carry L H0 H1 =
      let l := fun k => L.getD k 0
      let a := fun k => H0.getD k 0
      let b := fun k => H1.getD k 0
      let lSpec : List (ℕ × ℕ × ℕ × ℕ) :=
        [(a 0, l 0, l 0, l 0), (a 1, l 1, l 1, l 1),
         (b 0, a 0, l 2, l 2), (b 1, a 1, l 3, l 3),
         (l 4, b 0, l 4, l 4), (l 5, b 1, l 5, l 5),
         (l 6, l 6, l 6, l 6), (l 7, l 7, l 7, l 7),
         (l 8, l 8, l 8, l 8), (l 9, l 9, l 9, l 9)]
      let h0Spec : List (ℕ × ℕ × ℕ × ℕ) :=
        [(a 2, a 0, l 4, l 6), (a 3, a 1, l 5, l 7),
         (a 4, a 2, a 0, a 0), (a 5, a 3, a 1, a 1),
         (a 6, a 4, a 2, a 2), (a 7, a 5, a 3, a 3),
         (a 8, a 6, a 4, a 4), (a 9, a 7, a 5, a 5),
         (a 8, a 8, a 6, a 6), (a 9, a 9, a 7, a 7)]
      let h1Spec : List (ℕ × ℕ × ℕ × ℕ) :=
        [(b 2, b 0, l 6, l 8), (b 3, b 1, l 7, l 9),
         (b 4, b 2, b 0, b 0), (b 5, b 3, b 1, b 1),
         (b 6, b 4, b 2, b 2), (b 7, b 5, b 3, b 3),
         (b 8, b 6, b 4, b 4), (b 9, b 7, b 5, b 5),
         (b 8, b 8, b 6, b 6), (b 9, b 9, b 7, b 7)]
      let (g1, nL) := emitMap g (fun g₀ t =>
        Gates.gMux4 g₀ c0 t.1 c1 t.2.1 noop t.2.2.1 carry t.2.2.2) lSpec
      let (g2, nH0) := emitMap g1 (fun g₀ t =>
        Gates.gMux4 g₀ borrow t.1 noop t.2.1 c4 t.2.2.1 c5 t.2.2.2) h0Spec
      let (g3, nH1) := emitMap g2 (fun g₀ t =>
        Gates.gMux4 g₀ borrow t.1 noop t.2.1 c4 t.2.2.1 c5 t.2.2.2) h1Spec
      (g3, (nL, nH0, nH1)) := rfl

theorem emitRebalanceLevel_eq (g : Gates) (fls : ℕ) (low hi : LevelW) :
    emitRebalanceLevel g fls low hi =
      let (g1, (borrow, noop, carry), (lowCnt', hiCnt')) := emitCntRebalance g fls low.1 hi.1
      let c0 := low.1.getD 0 0; let c1 := low.1.getD 1 0
      let c4 := low.1.getD 4 0; let c5 := low.1.getD 5 0
      let B := low.2.length
      let res := (List.range B).foldl (fun acc j =>
        let (gc, (rL, rH0, rH1)) := acc
        let (gc', (nL, nH0, nH1)) := emitCellRebalance gc c0 c1 c4 c5 borrow noop carry
          (low.2.getD j []) (hi.2.getD j []) (hi.2.getD (B + j) [])
        (gc', (nL :: rL, nH0 :: rH0, nH1 :: rH1))) (g1, ([], [], []))
      (res.1, ((lowCnt', res.2.1.reverse), (hiCnt', res.2.2.1.reverse ++ res.2.2.2.reverse))) := rfl

theorem emitRebalanceHalfTape_eq (g : Gates) (fls : ℕ) (hw : HalfW) (lvl : ℕ) :
    emitRebalanceHalfTape g fls hw lvl =
      let (g', (low', hi')) := emitRebalanceLevel g fls (hw.getD lvl ([], []))
        (hw.getD (lvl + 1) ([], []))
      (g', hw.take lvl ++ [low', hi'] ++ hw.drop (lvl + 2)) := rfl

theorem emitTapeStep0_eq (g : Gates) (fls : ℕ) (mNeg mZero mPos w0 w1 : ℕ) (tw : TapeW) :
    emitTapeStep0 g fls mNeg mZero mPos w0 w1 tw =
      let l0 := tw.2.1.getD 0 ([], [])
      let r0 := tw.2.2.getD 0 ([], [])
      let lh0 := (l0.2.getD 0 []).getD 0 0; let lh1 := (l0.2.getD 0 []).getD 1 0
      let rh0 := (r0.2.getD 0 []).getD 0 0; let rh1 := (r0.2.getD 0 []).getD 1 0
      let (g, nh0) := Gates.gMux3 g mNeg lh0 mZero w0 mPos rh0
      let (g, nh1) := Gates.gMux3 g mNeg lh1 mZero w1 mPos rh1
      let (g, nl0) := emitShiftLevel0 g fls mNeg mZero mPos w0 w1 l0
      let (g, nr0) := emitShiftLevel0 g fls mPos mZero mNeg w0 w1 r0
      (g, ((nh0, nh1), (nl0 :: tw.2.1.drop 1, nr0 :: tw.2.2.drop 1))) := rfl

end CslibFrontier.Computability.Circuit.Oblivious

